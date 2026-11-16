import Theorems.StepWrites

/-!
# From power-on to the press of Start on the title screen

`TitleStart` proves the run from the press of Start on the title to frame 0 of the route, from one condition on the machine after the frame of the press (`Press`: the idle
loop, the bytes `K` of a reference machine, and a nonzero timer-load flag). Here that condition is proved for a class of runs from power-on: no Start and no Select on the frames before the press, the press
is Start with A or without it and no other button, and the press comes in a window of frames (`Ctx.first`, `Ctx.last`: from the first menu frame, before the demo
starts).

The machine at power-on is one state (`PowerOn`): the registers and the place in the frame of the reference power-on, and a RAM that is not known. Either its byte `W`
is not the game's mark of a warm boot (then the reset code clears the RAM), or its bytes `Z` are 0 (the two bytes that a warm boot keeps and that change the game started
from the title). The first frame is the reset code's wait for the picture: it reads no RAM, so a tracked run of the reference decides it for every RAM
(`PipeTransitionAll`), and no step of it stores to RAM, so the RAM stays (`frame_keeps`, with `StepWrites`). From there an abstract machine (`TaintRun`, with the walk across
the frame's end of `SideChangeEnd`) follows every machine, one row of states for each frame (`Row`). The reset code clears the RAM, so that after a few frames the states
know all bytes but the stack's old bytes and the bytes that a warm boot keeps. A row's frame with no Start and no Select ends in the next row (`linkOK`); a row's frame
with the press ends in the condition (`pressOK`, `finPress`).

`Menu.Run` permits Start before the first frame that leaves the title. Each row either stays on the title or leaves it with `Press`. Select is absent; the first input has no Start.

`TitleStart.Begin` takes a `Start`: the original run from power-on (`Run`), the first-exit run (`Menu.Run`), or the condition itself for a run outside these classes. All give `Press` (`Start.cond`).

The search for the rows is no part of the proof (`rowsOf`): `check` walks every state of every row and of its tables. There is no game data in this file.
Page: `1-1/0-5-4-TitleBoot.md`.
-/

namespace Smbrta.TitleBoot

open PipeTransition (frame)
open PipeTransitionAll (go go_bind plain Rel RelF Bad track readsIn notIn SameCore ruf_rel ruf_mono)
open PipeEntryRule (trace nxt trace_stop run_trace frame_trace)
open StepWrites (stepLocs wOf Wr ramIdx trace_ram)
open TaintRun
open SideChangeEnd (xwalk xsearch nextStates finOf ExitCond)
open SideChangeBound (knOf)

/-! ## The context and the pads -/

/-- what the check is told -/
structure Ctx where
  /-- the environment of the title's frames: the ROM, and a pad that is not known -/
  E : Env
  sy : Syms
  /-- the bytes that the search keeps apart -/
  keep : List Nat
  /-- the machine after the press of the reference run, the bytes known of it, the pause's status byte -/
  x : Machine
  K : List Nat
  gps : Nat
  /-- the reference machine at power-on -/
  P : Machine
  /-- the bytes that are 0 in a RAM at power-on with the mark of a warm boot -/
  Z : List Nat
  /-- the byte of the mark of a warm boot: the mark is its value in `x` -/
  W : Nat
  /-- the byte of the flag that makes the game load the timer when the player enters: it is not 0 after the press, and `K` does not hold it -/
  T : Nat
  /-- the frames of the press that the check covers: `first ≤ kp ≤ last` -/
  first : Nat
  last : Nat
  laterFirst : Nat := 1
  laterLast : Nat := 0

/-- the names of the bytes `Z`: the two bytes that a warm boot keeps and that change the game started from the title (the world selection, the world of a continue) -/
def zeroNames : List String := ["WorldSelectEnableFlag", "ContinueWorld"]

/-- the name of the byte `W` -/
def markName : String := "WarmBootValidation"

/-- the name of the byte `T`. The menu changes it on the frame of the press. Its first frame can leave a different nonzero value, before the game core has cleared it.
The game only tests whether it is zero. -/
def flagName : String := "FetchNewGameTimerFlag"

/-- the pad of a frame before the press: no Start and no Select -/
def quietPad : AB := ⟨0, 0x0C⟩
/-- no Start and no Select in the input of a frame (game layout) -/
def noSS (i : UInt8) : Bool := smbToPad i &&& 0x0C == 0

/-- the pad of the press: Start, with A or not, and no other button -/
def startPad : AB := ⟨0x08, 0xFE⟩
/-- the input is Start, or A with Start (game layout) -/
def onlyStart (i : UInt8) : Bool := smbToPad i &&& 0xFE == 0x08

/-- the byte of the buttons read is taken in pieces by the bit of A, so that the menu's two tests of it (Start, A with Start) agree -/
def padSplits (b : Ctx) : List (Nat × UInt8) := b.E.splits ++ [((b.sy.SavedJoypadBits &&& 0x7FF).toNat, 0x80)]

/-- the pieces of that byte stay apart in the frame of the press -/
def keepS (b : Ctx) : List Nat := b.keep ++ [(b.sy.SavedJoypadBits &&& 0x7FF).toNat]

def envQ (b : Ctx) : Env := { b.E with pad := quietPad }
def envS (b : Ctx) : Env := { ({ b.E with splits := padSplits b } : Env) with pad := startPad }

/-! ## Rows -/

/-- the states when a frame begins, the table of their frames with no Start and no Select, and the table of their frames with the press -/
structure Row where
  R : List AS
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  tp : Array AS
  idxp : Std.HashMap Nat (List Nat)
  cutp : ByteArray
  deriving Inhabited

def cfgQ (b : Ctx) (r : Row) : Cfg :=
  { E := envQ b, ops := (aRows (envQ b)).toArray, sy := b.sy, K := 1, keep := b.keep, t := r.t, idx := r.idx, cut := r.cut }

def cfgS (b : Ctx) (r : Row) : Cfg :=
  { E := envS b, ops := (aRows (envS b)).toArray, sy := b.sy, K := 1, keep := keepS b, t := r.tp, idx := r.idxp, cut := r.cutp }

/-- a state that starts a frame: a state of the table covers it, or its walk succeeds -/
def startOK (C : Cfg) (fin : AS → Bool) (S : AS) : Bool := S.k == 0 && !S.rk && (coverIn C S || xwalk C fin walkFuel S)

/-- a frame with no Start and no Select from a state of `r` ends in a state of `r'` -/
def linkOK (b : Ctx) (r r' : Row) : Bool :=
  r.t.all (xwalk (cfgQ b r) (finOf r'.R) walkFuel) && r.R.all (startOK (cfgQ b r) (finOf r'.R))

/-- the end of the frame of the press: the idle loop of the reference, the next NMI to come or pending, the bytes `K` of the reference, and the byte `T` is not 0 -/
def finPress (b : Ctx) (B : AS) : Bool :=
  B.pc == b.x.pc && B.s == b.x.s && decide (B.hi < 10) &&
  ((B.hi == 0 && !B.vb && !B.nmi) || (decide (1 ≤ B.lo) && B.vb && B.nmi)) &&
  B.ppuCtrl.k &&& 0x80 == 0x80 && B.ppuCtrl.v &&& 0x80 == 0x80 && !B.strobe && b.K.all (fun i => knownIs B (i, b.x.ram.get! i)) &&
  (B.getK b.T).isZero == some false

/-- **The condition after the frame of the press** (`Press` in the pages): the condition of `SideChangeEnd` on the idle loop and the bytes `K` of the reference, and the
byte `T` is not 0. All other bytes are free. -/
structure Press (b : Ctx) (m : Machine) : Prop where
  exit : ExitCond b.E b.x b.K b.gps m
  timer : m.ram.get! b.T ≠ 0

/-- `Press` as a check, for a program -/
def meets (b : Ctx) (m : Machine) : Bool := SideChangeEnd.exitOK b.E b.x b.K b.gps m && m.ram.get! b.T != 0

/-- a frame with the press from a state of `r` ends in the condition -/
def pressOK (b : Ctx) (r : Row) : Bool :=
  r.tp.all (xwalk (cfgS b r) (finPress b) walkFuel) && r.R.all (startOK (cfgS b r) (finPress b))

/-! ## The first frame -/

/-- a byte is in the known bits -/
def memB (v : AB) (x : UInt8) : Bool := x &&& v.k == v.v &&& v.k

/-- the state covers every machine with the registers, the PPU and the place in the frame of `y`, whose RAM has the bytes `Z` of `y` -/
def coreIn (E : Env) (Z : List Nat) (S : AS) (y : Machine) : Bool :=
  memB S.a y.a && memB S.x y.x && memB S.y y.y && memB S.p y.p && y.s == S.s && y.pc == S.pc && decide (y.prg.data = E.prg.data) && y.prgMask == E.mask &&
  memB S.ppuCtrl y.ppuCtrl && memB S.ppuMask y.ppuMask && y.vblank == S.vb && y.nmiPending == S.nmi && y.sprite0 == s0f y.fdot &&
  decide (S.lo ≤ y.fdot) && decide (y.fdot ≤ S.hi) && decide (S.hi < dotsPerFrame) && memB S.padShift y.padShift && y.padStrobe == S.strobe && !y.halted &&
  !S.dg && S.ram.size == 2048 && S.kn.size == 2048 && S.k == 0 && !S.rk &&
  (List.range 2048).all (fun j => S.kn.get! j == 0 || (Z.contains j && memB (S.getK j) (y.ram.get! j)))

/-- the abstract state of a machine: the registers are known, of the RAM only the bytes `Z` -/
def stateOf (y : Machine) (Z : List Nat) : AS :=
  { a := AB.known y.a, x := AB.known y.x, y := AB.known y.y, s := y.s, p := AB.known y.p, pc := y.pc, ram := y.ram, kn := knOf Z,
    ppuCtrl := AB.known y.ppuCtrl, ppuMask := AB.known y.ppuMask, vb := y.vblank, nmi := y.nmiPending, lo := y.fdot, hi := y.fdot,
    padShift := AB.known y.padShift, strobe := y.padStrobe, dg := false, k := 0, rk := false, spent := false }

/-- the states after the first frame: nothing is known of the RAM, but the bytes `Z` are 0; or but one bit of the byte `W`, which is not that of the mark -/
def firstStates (b : Ctx) : List AS :=
  let S := stateOf (frame b.P 0) []
  SideChangeEnd.refine (b.Z.map (·, 0)) S :: bitList.map fun bit => S.setK b.W ⟨~~~(b.x.ram.get! b.W) &&& bit, bit⟩

/-- an opcode or an operand in the ROM -/
theorem fetch_rom (m : Machine) (h : 0x8000 ≤ m.pc.toNat) : go fetch m = (m.prg.get! (m.pc &&& m.prgMask).toNat, { m with pc := m.pc + 1 }) := by
  have h1 : ¬ m.pc < 0x2000 := fun hlt => by
    have := UInt16.lt_iff_toNat_lt.1 hlt
    have e : (0x2000 : UInt16).toNat = 0x2000 := rfl
    omega
  have h2 : m.pc ≥ 0x8000 := UInt16.le_iff_toNat_le.2 (by have e : (0x8000 : UInt16).toNat = 0x8000 := rfl; omega)
  show go (rd m.pc) { m with pc := m.pc + 1 } = _
  rw [rd_rom _ h1 h2]

/-- the address in the two bytes after the opcode -/
def adr (m : Machine) : UInt16 :=
  (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 ||| ((m.prg.get! ((m.pc + 1 + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)

/-- the kind of an opcode that does not store -/
def isNo : Wr → Bool
  | .no => true
  | _ => false

/-- the next step writes no RAM, and the RAM does not decide it: no NMI is pending; the machine has halted, or its opcode and the two bytes after it are in the ROM, and
the opcode does not store, or it is `STA abs` at an address that is not in the RAM -/
def quietStep (y : Machine) : Bool :=
  !y.nmiPending && (y.halted ||
    (decide (0x8000 ≤ y.pc.toNat) && decide (y.pc.toNat + 2 < 65536) &&
      (isNo (wOf (y.prg.get! (y.pc &&& y.prgMask).toNat)) || (y.prg.get! (y.pc &&& y.prgMask).toNat == 0x8D && ramIdx (adr y) == []))))

theorem stepLocs_quiet (m : Machine) (h : quietStep m = true) : stepLocs m = [] := by
  simp only [quietStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hn, h⟩ := h
  unfold stepLocs
  rw [if_neg (by simp [hn])]
  by_cases hh : m.halted = true
  · rw [if_pos hh]
  · rw [if_neg hh]
    rcases h with h | ⟨⟨hp, hp2⟩, h⟩
    · exact absurd h hh
    · rw [fetch_rom m hp]
      rcases h with h | ⟨h8, ha⟩
      · show (wOf (m.prg.get! (m.pc &&& m.prgMask).toNat)).locs _ = []
        generalize wOf (m.prg.get! (m.pc &&& m.prgMask).toNat) = w at h
        cases w with
        | no => rfl
        | md c a => cases h
        | st k => cases h
      · show (wOf (m.prg.get! (m.pc &&& m.prgMask).toNat)).locs _ = []
        rw [h8]
        show ramIdx (go fetch16 { m with pc := m.pc + 1 }).1 = []
        have e1 : (m.pc + 1).toNat = m.pc.toNat + 1 := by
          rw [UInt16.toNat_add]
          have : (1 : UInt16).toNat = 1 := rfl
          omega
        have f1 := fetch_rom { m with pc := m.pc + 1 } (by show 0x8000 ≤ (m.pc + 1).toNat; omega)
        have e2 : (m.pc + 1 + 1).toNat = m.pc.toNat + 2 := by
          rw [UInt16.toNat_add, e1]
          have : (1 : UInt16).toNat = 1 := rfl
          omega
        have f2 := fetch_rom { m with pc := m.pc + 1 + 1 } (by show 0x8000 ≤ (m.pc + 1 + 1).toNat; omega)
        have e3 : (go fetch16 { m with pc := m.pc + 1 }).1 = adr m := by
          show ((go fetch { m with pc := m.pc + 1 }).1.toUInt16 ||| ((go fetch (go fetch { m with pc := m.pc + 1 }).2).1.toUInt16 <<< 8)) = _
          rw [f1]
          show (_ ||| ((go fetch { m with pc := m.pc + 1 + 1 }).1.toUInt16 <<< 8)) = _
          rw [f2]
          rfl
        rw [e3]
        simpa using ha

/-- `quietStep`, with a table of the opcodes that do not store -/
def quietTab (tab : ByteArray) (y : Machine) : Bool :=
  !y.nmiPending && (y.halted ||
    (decide (0x8000 ≤ y.pc.toNat) && decide (y.pc.toNat + 2 < 65536) &&
      (tab.get! (y.prg.get! (y.pc &&& y.prgMask).toNat).toNat != 0 || (y.prg.get! (y.pc &&& y.prgMask).toNat == 0x8D && ramIdx (adr y) == []))))

/-- every opcode that the table marks does not store -/
def tabOK (tab : ByteArray) : Bool := (List.range 256).all fun n => tab.get! n == 0 || isNo (wOf n.toUInt8)

/-- the table of the opcodes that do not store -/
def noTab : ByteArray := ByteArray.mk ((Array.range 256).map fun n => if isNo (wOf n.toUInt8) then 1 else 0)

theorem quiet_of_tab {tab : ByteArray} (ht : tabOK tab = true) {y : Machine} (h : quietTab tab y = true) : quietStep y = true := by
  simp only [quietTab, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  simp only [quietStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq]
  refine ⟨h.1, ?_⟩
  rcases h.2 with hh | ⟨hp, hk⟩
  · exact Or.inl hh
  · refine Or.inr ⟨hp, ?_⟩
    rcases hk with hk | hk
    · left
      simp only [tabOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht _ (UInt8.toNat_lt (y.prg.get! (y.pc &&& y.prgMask).toNat)) with h0 | h1
      · exact absurd h0 hk
      · rw [show (y.prg.get! (y.pc &&& y.prgMask).toNat).toNat.toUInt8 = y.prg.get! (y.pc &&& y.prgMask).toNat from by simp] at h1
        exact h1
    · exact Or.inr hk

/-- the machine at the end of its frame, after at most `n` steps, if `chk` holds on the machine and on the machines of these steps -/
def stepsEnd (t : Nat) (chk : Machine → Bool) : Nat → Machine → Option Machine
  | 0, m => some m
  | n + 1, m => if chk m then (if decide (m.frame ≥ t) || m.halted then some m else stepsEnd t chk n (nxt t m)) else none

theorem stepsEnd_trace {y : Machine} {i : UInt8} {chk : Machine → Bool} {z : Machine} :
    ∀ (n j : Nat), stepsEnd (y.frame + 1) chk n (trace y i j) = some z → z = trace y i (j + n) ∧ ∀ k, k < n → chk (trace y i (j + k)) = true
  | 0, _, h => ⟨(Option.some.inj h).symm, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1, j, h => by
    simp only [stepsEnd] at h
    split at h
    · rename_i h1
      split at h
      · rename_i h2
        have e := trace_stop (m := y) (i := i) (j := j) (by simpa using h2)
        refine ⟨by rw [e]; exact (Option.some.inj h).symm, fun k _ => by rw [e]; exact h1⟩
      · obtain ⟨g1, g2⟩ := stepsEnd_trace n (j + 1) h
        refine ⟨by rw [g1]; congr 1; omega, fun k hk => ?_⟩
        cases k with
        | zero => exact h1
        | succ k =>
          rw [show j + (k + 1) = j + 1 + k by omega]
          exact g2 k (by omega)
    · cases h

/-- **A frame whose steps write no RAM keeps the RAM**, for every machine that the tracked run of `ref` stands for -/
theorem frame_keeps {U : Nat → Bool} {ref M : Machine} {i : UInt8} (hrel : RelF U 0 0 (track ref) M)
    (hq : ∀ k, k < fuelPerFrame → quietStep (trace (track ref) i k) = true) (hnb : ¬ Bad U (frame (track ref) i)) (j : Nat) :
    (frame M i).ram.get! j = M.ram.get! j := by
  rw [frame_trace M i]
  apply trace_ram fuelPerFrame
  intro k hk
  have h0 : Rel U 0 0 (trace (track ref) i 0) (trace M i 0) := hrel (smbToPad i)
  have hfr : M.frame = ref.frame := by
    obtain ⟨r, tr, tw, ti, hm⟩ := h0.emb
    have := congrArg Machine.frame hm
    exact this
  have e1 := run_trace (track ref) i k 0
  have e2 := run_trace M i k 0
  rw [Nat.zero_add] at e1 e2
  have hstep := ruf_rel k ((track ref).frame + 1) _ _ h0
  rw [e1] at hstep
  have e3 : (track ref).frame + 1 + 0 = M.frame + 1 := by
    show ref.frame + 1 + 0 = M.frame + 1
    omega
  rw [e3, e2] at hstep
  rcases hstep with hb | hr
  · exfalso
    apply hnb
    rw [frame_trace (track ref) i]
    have e4 := run_trace (track ref) i (fuelPerFrame - k) k
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at e4
    rw [← e4]
    exact ruf_mono _ _ _ hb
  · obtain ⟨r, tr, tw, ti, hm⟩ := hr.emb
    rw [hm]
    have hq2 : quietStep (trace (track ref) i k) = true := hq k hk
    rw [stepLocs_quiet _ (show quietStep (plain ⟨r, tr, tw, ti, 0, 0⟩ (trace (track ref) i k)) = true from hq2)]
    exact List.not_mem_nil

/-- the first frame from power-on, with each input that has no Start and no Select: no step of the tracked run of the reference stores to RAM, the run reads no RAM,
and its end is the state after the first frame, of which the row has the states `firstStates` -/
def bootOK (b : Ctx) (r : Row) : Bool :=
  b.P.ram.size == 2048 && !b.P.trk && tabOK noTab &&
  (List.range 256).all (fun n => !noSS n.toUInt8 ||
    match stepsEnd (b.P.frame + 1) (quietTab noTab) fuelPerFrame (trace (track b.P) n.toUInt8 0) with
    | some y => readsIn [] y && coreIn b.E [] (stateOf (frame b.P 0) []) y
    | none => false) &&
  (firstStates b).all fun S => r.R.any fun D => S.le D

/-! ## The search: no part of the proof -/

/-- the candidates by key and the program counters of a table -/
def tableOf (E : Env) (keep : List Nat) (t : Array AS) : Std.HashMap Nat (List Nat) × ByteArray :=
  let P := t.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  (P.1, P.2.1)

/-- the order of the keys of the search -/
def cmp3 (a b : UInt64 × UInt64 × UInt64) : Ordering := (compare a.1 b.1).then ((compare a.2.1 b.2.1).then (compare a.2.2 b.2.2))

/-- a small key for the search: the parts of `keyOf`, in the same order (the frame, the stack pointer, the program counter; `x` and `y`; a hash of the rest) -/
def hkey (E : Env) (keep : List Nat) (A : AS) : UInt64 × UInt64 × UInt64 :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let idle := isIdle E A.pc op
  let num := fun (v : AB) => if idle then (0 : UInt64) else v.k.toUInt64 * 256 + (v.v &&& v.k).toUInt64
  let useA := op == 0x29 || op == 0xD0 || op == 0xF0
  let mix := fun (h x : UInt64) => (h ^^^ x) * 0x100000001B3
  let h := mix 0xCBF29CE484222325 (if useA then num A.a else 0)
  let h := mix h ((if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0))
  let h := keep.foldl (fun h i => mix h ((A.getK i).k.toUInt64 * 256 + ((A.getK i).v &&& (A.getK i).k).toUInt64)) h
  let h := E.D.foldl (fun h i => mix h (if op == 0x0D || op == 0xF0 then (A.getK i).k.toUInt64 else 0)) h
  ((A.k.toUInt64 <<< 24) ||| (A.s.toUInt64 <<< 16) ||| A.pc.toUInt64, (num A.x <<< 16) ||| num A.y, mix h (stackHash A).toUInt64)

/-- the search with chains of `TaintRun` and `SideChangeEnd`, with small keys and a small table -/
structure Fast where
  /-- the states that wait, with the number of paths that came into each -/
  pending : Std.TreeMap (UInt64 × UInt64 × UInt64) (AS × Nat) cmp3 := {}
  done : Std.HashMap (UInt64 × UInt64 × UInt64) AS := {}
  /-- the program counters where a state has waited -/
  leaders : ByteArray := ByteArray.mk (Array.replicate 65536 0)
  out : Array AS := #[]
  ends : Array AS := #[]
  steps : Nat := 0
  fails : Nat := 0

/-- a new state waits: it is joined with a state that waits with the same key -/
def Fast.route (E : Env) (keep : List Nat) (X : Fast) (B : AS) : Fast :=
  let K := hkey E keep B
  match X.pending[K]? with
  | some (P, n) => { X with pending := X.pending.insert K (P.join B, n + 1) }
  | none =>
    if isSpin E B then
      match X.done[K]? with
      | some D =>
        if B.le D then X else
        let J := widen (D.join B)
        { X with pending := X.pending.insert K (J, 2), done := X.done.insert K J }
      | none => { X with pending := X.pending.insert K (B, 2), done := X.done.insert K B }
    else { X with pending := X.pending.insert K (B, 1) }

/-- follow one waiting state as far as no other path can join -/
partial def Fast.chain (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (X0 : Fast) (A0 : AS) : Fast := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := SideChangeEnd.xsuccs E ops cur
    X := { X with steps := X.steps + rs.length }
    if rs.any (·.isNone) then X := { X with fails := X.fails + 1 }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && X.leaders.get! b.pc.toNat == 0 && run < 128 &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.set! b.pc.toNat 1 }
        X := X.route E keep b
    break
  return X

/-- how often one path of a frame comes to each program counter (at most 255): the first successor of each step -/
def visitsOf (E : Env) (ops : Array (AM Unit)) (S : AS) (limit : Nat) : ByteArray := Id.run do
  let mut cnt := ByteArray.mk (Array.replicate 65536 0)
  let mut cur := S
  for _ in [0:limit] do
    match SideChangeEnd.xsuccs E ops cur with
    | some b :: _ =>
      if b.k != cur.k then break
      let c := cnt.get! b.pc.toNat
      if c < 255 then cnt := cnt.set! b.pc.toNat (c + 1)
      cur := b
    | _ => break
  return cnt

/-- the search: the table gets only the states that two paths come into, and a state after `every` steps without one, at a program counter that a path comes to
at most 8 times (a state in a loop would make the walk look at the table on each turn) -/
partial def searchF (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (every limit : Nat) (visits : ByteArray) (starts : List AS) : Fast := Id.run do
  let mut X : Fast := starts.foldl (Fast.route E keep) {}
  let mut last := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, (A, n)) =>
      X := { X with pending := X.pending.erase key }
      if n ≥ 2 || (X.steps ≥ last + every && visits.get! A.pc.toNat ≤ 8) then
        X := { X with out := X.out.push A }
        last := X.steps
      if isSpin E A then X := { X with done := X.done.insert key A }
      X := X.chain E ops keep A
  return X

/-- the search of one frame: its table and its ends. From few states the search with a small table (a frame from the idle loop is short: no state but where paths
meet; another frame may be long: a state after 4000 steps, outside the loops), from many states that of `SideChangeEnd`. -/
def searchOf (E : Env) (keep : List Nat) (idle : Bool) (starts : List AS) : Array AS × Array AS :=
  if starts.length > 32 then
    let X := xsearch E (aRows E).toArray keep starts
    (X.out, X.ends)
  else
    let ops := (aRows E).toArray
    let visits := if idle then ByteArray.mk (Array.replicate 65536 0) else visitsOf E ops (starts.headD default) 200000
    let X := searchF E ops keep (if idle then 1000000 else 4000) 2000000 visits starts
    (X.out, X.ends)

/-- the states without those that another state covers -/
def prune (l : List AS) : List AS :=
  let a := l.toArray
  (List.range a.size).filterMap fun i =>
    if (List.range a.size).any (fun j => j != i && a[i]!.le a[j]! && (j < i || !a[j]!.le a[i]!)) then none else some a[i]!

/-- a row from its states. When the states are in the idle loop, the search starts from those after dot 0, and they go into the table: the state at dot 0 comes to them
in one step. `press` asks for the table of the frame of the press. -/
def rowOf (b : Ctx) (R : List AS) (press : Bool) : Row × List AS :=
  let eQ := envQ b
  let eS := envS b
  let idle := R.all fun S => isIdle b.E S.pc (b.E.prg.get! (S.pc &&& b.E.mask).toNat)
  let late := if idle then R.filter (·.lo != 0) else []
  let starts := if idle then late else R
  let X := searchOf eQ b.keep idle starts
  let t := X.1 ++ late.toArray
  let T := tableOf eQ b.keep t
  let tp := if press then (searchOf eS (keepS b) idle starts).1 ++ late.toArray else #[]
  let Tp := tableOf eS (keepS b) tp
  ({ R, t, idx := T.1, cut := T.2, tp, idxp := Tp.1, cutp := Tp.2 }, prune (nextStates b.E false X.2.toList))

/-- the rows of the frames `1..last`: row `j` has the states when frame `j + 1` begins -/
def rowsOf (b : Ctx) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  if b.last < b.first then return rows
  let mut R : List AS := firstStates b
  for j in [0:b.last] do
    let (r, R') := rowOf b R (decide (b.first ≤ j + 1))
    rows := rows.push r
    R := R'
  return rows

/-- the frames of the press for which the rows close, up to `cap`: the first frame whose row ends in the condition with the press, and the last frame before a row fails.
`(0, 0)` if there is none. -/
def windowOf (b : Ctx) (cap : Nat) : Nat × Nat := Id.run do
  let b1 : Ctx := { b with first := 1, last := cap }
  let mut R : List AS := firstStates b
  let mut prev : Option Row := none
  let mut first := 0
  let mut last := 0
  for j in [0:cap] do
    let (r, R') := rowOf b1 R true
    let linked := match prev with
      | some q => linkOK b1 q r
      | none => bootOK b1 r
    if !linked then break
    let ok := pressOK b1 r
    if first == 0 then
      if ok then
        first := j + 1
        last := j + 1
    else if ok then last := j + 1
    else break
    prev := some r
    R := R'
  return (first, last)

/-! ## The check -/

/-- A later continuous window after `skip`. The search crosses failed press frames, but every preceding link must close. -/
def windowAfter (b : Ctx) (skip cap : Nat) : Nat × Nat := Id.run do
  let b1 : Ctx := { b with first := 1, last := cap }
  let mut R := firstStates b
  let mut prev : Option Row := none
  let mut first := 0
  let mut last := 0
  for j in [0:cap] do
    let (r, R') := rowOf b1 R (decide (skip ≤ j + 1))
    let linked := match prev with
      | none => bootOK b1 r
      | some q => linkOK b1 q r
    if !linked then break
    if skip ≤ j + 1 then
      let ok := pressOK b1 r
      if ok then
        if first == 0 then first := j + 1
        last := j + 1
      else if first != 0 then break
    prev := some r
    R := R'
  return (first, last)

/-- The optional later window uses the same condition on the machine after the exit. -/
def later (b : Ctx) : Ctx := { b with first := b.laterFirst, last := b.laterLast }

/-- **The check**, for given rows: the first frame ends in the first row; each row's frame with no Start and no Select ends in the next row; from `first` on, each row's
frame with the press ends in the condition. -/
def checkOf (b : Ctx) (rows : Array Row) : Bool :=
  decide (b.last < b.first) ||
  (decide (1 ≤ b.first) && b.K.contains b.gps && b.x.ram.get! b.gps &&& 1 == 0 && decide (b.T < 2048) && bootOK b rows[0]! &&
    (List.range (b.last - 1)).all (fun j => linkOK b rows[j]! rows[j + 1]!) &&
    (List.range b.last).all (fun j => decide (j + 1 < b.first) || pressOK b rows[j]!))

/-- **The check**, with the rows that the search finds -/
def check (b : Ctx) : Bool := checkOf b (rowsOf b)

/-! ## What the check gives -/

section
variable {b : Ctx}

open SideChangeEnd (sim_pad sim_unpad two_le cover_xlive xframe_run xframe_of_walk sim_splits sim_splits')

/-- **One frame from a start state.** The state covers the machine with this frame's pad; the frame ends in a state that `fin` accepts. -/
theorem frame_of_start {C : Cfg} {fin : AS → Bool} (ht : C.t.all (xwalk C fin walkFuel) = true) (hops : C.ops = (aRows C.E).toArray)
    {S : AS} {m : Machine} {i : UInt8} (hS : startOK C fin S = true) (hs : Sim C.E (m.frame, 2) S { m with pad := smbToPad i }) :
    ∃ B, fin B = true ∧ Sim C.E (m.frame, 2) B (frame m i) := by
  simp only [startOK, Bool.and_eq_true, Bool.or_eq_true] at hS
  rcases hS.2 with hS | hS
  · obtain ⟨D, hD, _⟩ := cover_xlive (F := (m.frame, 2)) ht hs hS
    rw [PipeTransitionAll.frame_eq]
    have hf : dotsPerFrame ≤ ({ m with pad := smbToPad i } : Machine).fdot + 3 * fuelPerFrame := by
      have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
      omega
    obtain ⟨_, B, h1, _, h2⟩ := xframe_run ht hops two_le (f := m.frame) fuelPerFrame D _ hD rfl hf
    exact ⟨B, h1, h2⟩
  · obtain ⟨_, B, h1, _, h2⟩ := xframe_of_walk ht hops two_le hS hs
    exact ⟨B, h1, h2⟩

theorem noSS_mem {i : UInt8} (h : noSS i = true) : quietPad.mem (smbToPad i) := by
  have e : smbToPad i &&& 0x0C = 0 := by simpa [noSS] using h
  show smbToPad i &&& 0x0C = 0 &&& 0x0C
  rw [e]
  rfl

theorem onlyStart_mem {i : UInt8} (h : onlyStart i = true) : startPad.mem (smbToPad i) := by
  have e : smbToPad i &&& 0xFE = 0x08 := by simpa [onlyStart] using h
  show smbToPad i &&& 0xFE = 0x08 &&& 0xFE
  rw [e]
  rfl

/-- a machine is in a state of the row, when its frame begins -/
def Covered (b : Ctx) (r : Row) (m : Machine) : Prop := ∃ S ∈ r.R, Sim b.E (m.frame, 2) S m

/-- the end of a frame, as the start of the next -/
theorem next_start {E : Env} {B D : AS} {f : Nat} {m' : Machine} (hb : Sim E (f, 2) B m') (hr : B.rk = false) (hle : ({ B with k := 0 } : AS).le D = true) :
    Sim E (m'.frame, 2) D m' := by
  have hbase : Sim E (m'.frame, 2) ({ B with k := 0 } : AS) m' := by
    refine { hb with fr := ?_, rkv := ?_ }
    · show m'.frame = m'.frame + 0
      rfl
    · intro hr2
      have : B.rk = true := hr2
      rw [hr] at this
      cases this
  exact sim_le hle hbase

/-- **A frame with no Start and no Select** from a row ends in the next row -/
theorem link_frame (hE : b.E.pad = AB.top) {r r' : Row} (h : linkOK b r r' = true) {m : Machine} (hc : Covered b r m) {i : UInt8} (hq : noSS i = true) :
    Covered b r' (frame m i) := by
  obtain ⟨S, hS, hs⟩ := hc
  simp only [linkOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hs1 : Sim (cfgQ b r).E (m.frame, 2) S { m with pad := smbToPad i } := sim_pad hs (noSS_mem hq)
  obtain ⟨B, hf, hb⟩ := frame_of_start (C := cfgQ b r) h1 rfl (List.all_eq_true.1 h2 S hS) hs1
  have hb' : Sim b.E (m.frame, 2) B (frame m i) := sim_unpad hE hb
  simp only [finOf, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hf
  obtain ⟨hr, D, hD, hle⟩ := hf
  exact ⟨D, hD, next_start hb' hr hle⟩

/-- a byte that the state knows not to be 0 -/
theorem ne_zero_of_sim {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim E F B m) {i : Nat} (hi : i < 2048) (h : (B.getK i).isZero = some false) :
    m.ram.get! i ≠ 0 := by
  rcases TR_isZero (hs.ram i hi) with h0 | h0
  · rw [h] at h0
    cases h0
  · rw [h] at h0
    intro he
    rw [he] at h0
    cases h0

/-- an end of a frame that `finPress` accepts meets the condition -/
theorem press_of_fin (hg : b.K.contains b.gps = true) (hp : b.x.ram.get! b.gps &&& 1 = 0) (hT : b.T < 2048) {B : AS} (hf : finPress b B = true) {F : Nat × UInt8}
    {m' : Machine} (hb' : Sim b.E F B m') : Press b m' := by
  simp only [finPress, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, f7⟩, f8⟩, f9⟩ := hf
  have hhi := hb'.hi
  have hlo := hb'.lo
  have hbytes : ∀ j ∈ b.K, m'.ram.get! j = b.x.ram.get! j := fun j hj => sim_known hb' (f8 j hj)
  refine ⟨⟨by omega, ?_, ?_, ?_, hb'.strobe.trans f7, hb'.halted, hb'.trk, hb'.prg, hb'.mask, hb'.size, hb'.pc.trans f1, hb'.s.trans f2, hbytes, ?_⟩, ne_zero_of_sim hb' hT f9⟩
  · rcases f4 with ⟨⟨a1, a2⟩, a3⟩ | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl ⟨by omega, hb'.vb.trans a2, hb'.nmi.trans a3⟩
    · exact Or.inr ⟨by omega, hb'.vb.trans a2, hb'.nmi.trans a3⟩
  · rw [hb'.s0]
    exact s0f_small (by omega)
  · rw [bit_eq hb'.ppuCtrl f5, f6]
  · rw [hbytes b.gps (List.contains_iff_mem.1 hg)]
    exact hp

/-- **The frame of the press** from a row ends in the condition of `TitleStart` -/
theorem press_frame (hE : b.E.pad = AB.top) (hg : b.K.contains b.gps = true) (hp : b.x.ram.get! b.gps &&& 1 = 0) (hT : b.T < 2048) {r : Row} (h : pressOK b r = true)
    {m : Machine} (hc : Covered b r m) {i : UInt8} (hq : onlyStart i = true) : Press b (frame m i) := by
  obtain ⟨S, hS, hs⟩ := hc
  simp only [pressOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hs1 : Sim (cfgS b r).E (m.frame, 2) S { m with pad := smbToPad i } := sim_pad (sim_splits' hs) (onlyStart_mem hq)
  obtain ⟨B, hf, hb⟩ := frame_of_start (C := cfgS b r) h1 rfl (List.all_eq_true.1 h2 S hS) hs1
  have hE' : ({ b.E with splits := padSplits b } : Env).pad = AB.top := hE
  have hb' : Sim b.E (m.frame, 2) B (frame m i) := sim_splits (sim_unpad hE' hb)
  exact press_of_fin hg hp hT hf hb'

theorem memB_ok {v : AB} {x : UInt8} (h : memB v x = true) : v.mem x := by
  simpa [memB, AB.mem] using h

/-- **The machine at power-on**: the registers, the PPU and the place in the frame of the reference `P`. Its RAM is not known: the bytes `Z` are 0, or the byte `W`
is not the mark of a warm boot (its value in `x`). -/
def PowerOn (b : Ctx) (m : Machine) : Prop :=
  ∃ r : ByteArray, r.size = 2048 ∧ ((∀ i ∈ b.Z, r.get! i = 0) ∨ r.get! b.W ≠ b.x.ram.get! b.W) ∧ m = { b.P with ram := r }

theorem mask_at : ∀ j : Fin 8, ∃ b ∈ bitList, ∀ i : Fin 8, bt b i.1 = decide (i.1 = j.1) := by decide

/-- a byte that is not `y` differs from it in one bit -/
theorem mask_of_ne {x y : UInt8} (h : x ≠ y) : ∃ b ∈ bitList, (⟨~~~y &&& b, b⟩ : AB).mem x := by
  have h2 : ∃ j : Fin 8, bt x j.1 ≠ bt y j.1 := by
    refine Classical.byContradiction fun hno => h (bt_ext fun i hi => ?_)
    exact Classical.byContradiction fun hne => hno ⟨⟨i, hi⟩, hne⟩
  obtain ⟨j, hj⟩ := h2
  obtain ⟨b, hb, hbt⟩ := mask_at j
  refine ⟨b, hb, mem_iff.2 fun t ht => ?_⟩
  show (bt x t && bt b t) = (bt (~~~y &&& b) t && bt b t)
  rw [bt_and, bt_not _ _ ht, hbt ⟨t, ht⟩]
  by_cases htj : t = j.1
  · subst htj
    simp only [decide_true, Bool.and_true]
    cases hx : bt x j.1 <;> cases hy : bt y j.1 <;> simp_all
  · simp [htj]

/-- **The first frame**, with no Start and no Select: it ends in the first row -/
theorem boot_frame (hE : b.E.pad = AB.top) {r : Row} (h : bootOK b r = true) {m : Machine} (hp : PowerOn b m) {i : UInt8} (hi : noSS i = true) :
    Covered b r (frame m i) := by
  obtain ⟨ram, hsz, hcase, rfl⟩ := hp
  simp only [bootOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true, List.mem_range, List.any_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, htab⟩, h4⟩, h7⟩ := h
  have h5 := h4 i.toNat (UInt8.toNat_lt i)
  rw [show i.toNat.toUInt8 = i from by simp] at h5
  rcases h5 with h5 | h5
  · rw [hi] at h5
    cases h5
  cases hse : stepsEnd (b.P.frame + 1) (quietTab noTab) fuelPerFrame (trace (track b.P) i 0) with
  | none =>
    rw [hse] at h5
    cases h5
  | some y0 =>
  rw [hse] at h5
  obtain ⟨hy0, hq0⟩ := stepsEnd_trace (y := track b.P) fuelPerFrame 0 hse
  rw [Nat.zero_add, ← frame_trace] at hy0
  subst hy0
  have hq : ∀ k, k < fuelPerFrame → quietStep (trace (track b.P) i k) = true := fun k hk => by
    have := hq0 k hk
    rw [Nat.zero_add] at this
    exact quiet_of_tab htab this
  simp only [Bool.and_eq_true] at h5
  obtain ⟨h6, hc⟩ := h5
  have hs : SameCore b.P ({ b.P with ram := ram } : Machine) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, by simp, Nat.le_refl _, by simp, h2, hsz⟩
  have hrel0 := PipeTransitionAll.relF_track (R := []) hs h1 (fun j hj _ => absurd hj List.not_mem_nil)
  have ec : ({ b.P with ram := ram } : Machine).cyc - b.P.cyc = 0 := Nat.sub_self _
  have ef : ({ b.P with ram := ram } : Machine).frame - b.P.frame = 0 := Nat.sub_self _
  rw [ec, ef] at hrel0
  have hnb := PipeTransitionAll.not_bad h6
  have hkeep : ∀ j, (frame ({ b.P with ram := ram } : Machine) i).ram.get! j = ram.get! j := fun j => frame_keeps hrel0 hq hnb j
  rcases PipeTransitionAll.frame_rel i hrel0 with hbad | hr
  · exact absurd hbad hnb
  · have hsize := hr.szP
    obtain ⟨rr, tr, tw, ti, he⟩ := hr.emb
    generalize frame (track b.P) i = y at he hc
    generalize frame ({ b.P with ram := ram } : Machine) i = m' at he hsize hkeep ⊢
    -- the state that knows nothing of the RAM
    have hS0 : Sim b.E (m'.frame, 2) (stateOf (frame b.P 0) []) m' := by
      generalize stateOf (frame b.P 0) [] = S at hc ⊢
      simp only [coreIn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true, List.mem_range, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, c22⟩, c23⟩, c24⟩, c25⟩ := hc
      have ebase : ∀ {α : Type} (f : Machine → α), (∀ e z, f (PipeTransitionAll.plain e z) = f z) → f m' = f y := fun f hf => by rw [he]; exact hf _ _
      have eprg : m'.prg = b.E.prg := by
        rw [ebase (·.prg) (fun _ _ => rfl)]
        have : ∀ a c : ByteArray, a.data = c.data → a = c := by
          intro a c hac
          cases a
          cases c
          simp_all
        exact this _ _ c7
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, eprg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c16, ?_, ?_, ?_, ?_, ?_, hsize, ?_, ?_, c21, c22, ?_, ?_⟩
      · rw [ebase (·.a) (fun _ _ => rfl)]; exact memB_ok c1
      · rw [ebase (·.x) (fun _ _ => rfl)]; exact memB_ok c2
      · rw [ebase (·.y) (fun _ _ => rfl)]; exact memB_ok c3
      · rw [ebase (·.p) (fun _ _ => rfl)]; exact memB_ok c4
      · rw [ebase (·.s) (fun _ _ => rfl)]; exact c5
      · rw [ebase (·.pc) (fun _ _ => rfl)]; exact c6
      · rw [ebase (·.prgMask) (fun _ _ => rfl)]; exact c8
      · rw [ebase (·.ppuCtrl) (fun _ _ => rfl)]; exact memB_ok c9
      · rw [ebase (·.ppuMask) (fun _ _ => rfl)]; exact memB_ok c10
      · rw [ebase (·.vblank) (fun _ _ => rfl)]; exact c11
      · rw [ebase (·.nmiPending) (fun _ _ => rfl)]; exact c12
      · rw [ebase (·.sprite0) (fun _ _ => rfl), ebase (·.fdot) (fun _ _ => rfl)]; exact c13
      · rw [ebase (·.fdot) (fun _ _ => rfl)]; exact c14
      · rw [ebase (·.fdot) (fun _ _ => rfl)]; exact c15
      · rw [hE]; exact mem_top _
      · rw [ebase (·.padShift) (fun _ _ => rfl)]; exact memB_ok c17
      · rw [ebase (·.padStrobe) (fun _ _ => rfl)]; exact c18
      · rw [ebase (·.halted) (fun _ _ => rfl)]; exact c19
      · rw [he]; rfl
      · intro j hj
        rcases c25 j hj with h0 | ⟨hz1, _⟩
        · show m'.ram.get! j &&& S.kn.get! j = S.ram.get! j &&& S.kn.get! j
          rw [h0]
          simp
        · exact absurd hz1 (by simp)
      · intro hd
        rw [c20] at hd
        cases hd
      · show m'.frame = m'.frame + S.k
        rw [c23]
        rfl
      · intro hrk
        rw [c24] at hrk
        cases hrk
    -- what is known of the RAM at power-on is known after the first frame
    have hfirst : ∃ S ∈ firstStates b, Sim b.E (m'.frame, 2) S m' := by
      rcases hcase with hz | hw
      · refine ⟨_, List.mem_cons_self, SideChangeEnd.sim_refines (fun q hq => ?_) hS0⟩
        obtain ⟨z, hz1, rfl⟩ := List.mem_map.1 hq
        show m'.ram.get! z = 0
        rw [hkeep z, hz z hz1]
      · obtain ⟨bit, hbit, hmem⟩ := mask_of_ne hw
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨bit, hbit, rfl⟩), SideChangeEnd.sim_refine hS0 ?_⟩
        rw [hkeep b.W]
        exact hmem
    obtain ⟨S, hS, hsim⟩ := hfirst
    obtain ⟨D, hD, hle⟩ := h7 S hS
    exact ⟨D, hD, sim_le hle hsim⟩

/-- **The run from power-on to the press of Start.** `m` is the machine after the frame of the press. -/
structure Run (b : Ctx) (m : Machine) where
  /-- the frame of the press, counted from power-on -/
  kp : Nat
  pm : Nat → Machine
  pi : Nat → UInt8
  next : ∀ n, pm (n + 1) = frame (pm n) (pi n)
  /-- **one state**: the machine at power-on -/
  power : PowerOn b (pm 0)
  /-- no Start and no Select on the frames before the press -/
  quiet : ∀ n, n < kp → noSS (pi n) = true
  /-- the press: Start, with A or without it, and no other button -/
  start : onlyStart (pi kp) = true
  /-- the press comes in the window of frames that the check covers -/
  lo : b.first ≤ kp
  hi : kp ≤ b.last
  after : m = pm (kp + 1)

variable {m : Machine}

/-- every machine before the press is in its row -/
theorem Run.covered (hE : b.E.pad = AB.top) {rows : Array Row} (hb : bootOK b rows[0]! = true)
    (hl : ∀ j, j < b.last - 1 → linkOK b rows[j]! rows[j + 1]! = true) (R : Run b m) : ∀ n, n < R.kp → Covered b rows[n]! (R.pm (n + 1))
  | 0, h => by
    rw [R.next]
    exact boot_frame hE hb R.power (R.quiet 0 h)
  | n + 1, h => by
    rw [R.next]
    exact link_frame hE (hl n (by have := R.hi; omega)) (Run.covered hE hb hl R n (by omega)) (R.quiet (n + 1) h)

/-- **The condition of `TitleStart` at the press**, from the machine at power-on and the inputs -/
theorem Run.press_of (hE : b.E.pad = AB.top) {rows : Array Row} (h : checkOf b rows = true) (R : Run b m) : Press b m := by
  have hlo := R.lo
  have hhi := R.hi
  simp only [checkOf, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rcases h with h | ⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, hT⟩, h5⟩, h6⟩, h7⟩
  · omega
  · obtain ⟨k, hk⟩ : ∃ k, R.kp = k + 1 := ⟨R.kp - 1, by omega⟩
    have hc := R.covered hE h5 h6 k (by omega)
    have e : m = frame (R.pm (k + 1)) (R.pi (k + 1)) := by
      have h8 := R.after
      rw [hk] at h8
      exact h8.trans (R.next (k + 1))
    rw [e]
    rcases h7 k (by omega) with hp | hp
    · omega
    · exact press_frame hE h3 h4 hT hp hc (by rw [← hk]; exact R.start)

/-- **The condition at the press**, from the check -/
theorem Run.press (hE : b.E.pad = AB.top) (h : check b = true) (R : Run b m) : Press b m := R.press_of hE h

/-! ## The first frame that leaves the title, with Start allowed before it -/

namespace Menu
open TaintRun
open SideChangeEnd (xwalk finOf xframe_of_walk sim_pad sim_unpad sim_splits sim_splits')

/-- Start may be held before the frame that leaves the title. Select is absent. -/
def pad : AB := ⟨0, 0x04⟩
def noSelect (i : UInt8) : Bool := smbToPad i &&& 0x04 == 0
def mode (b : Ctx) : Nat := (b.sy.OperMode &&& 0x7FF).toNat
def env (b : Ctx) : Env := { ({ b.E with splits := b.E.splits ++ [((b.sy.SavedJoypadBits &&& 0x7FF).toNat, 0x90)] } : Env) with pad := pad }
def cfg (b : Ctx) (r : Row) : Cfg :=
  { E := env b, ops := (aRows (env b)).toArray, sy := b.sy, K := 1, keep := keepS b, t := r.t, idx := r.idx, cut := r.cut }
/-- Every end either stays on the title, or meets the condition after leaving it. -/
def fin (b : Ctx) (R : List AS) (B : AS) : Bool :=
  (knownIs B (mode b, 0) && finOf R B) || (finPress b B && (B.getK (mode b)).isZero == some false)
def link (b : Ctx) (r r' : Row) : Bool :=
  r.t.all (xwalk (cfg b r) (fin b r'.R) walkFuel) && r.R.all (startOK (cfg b r) (fin b r'.R))

def row (b : Ctx) (R : List AS) : Row × List AS :=
  let E := env b
  let idle := R.all fun S => isIdle b.E S.pc (b.E.prg.get! (S.pc &&& b.E.mask).toNat)
  let late := if idle then R.filter (·.lo != 0) else []
  let starts := if idle then late else R
  let X := searchOf E (keepS b) idle starts
  let t := X.1 ++ late.toArray
  let T := tableOf E (keepS b) t
  let ends := X.2.toList.filter (fun S => knownIs S (mode b, 0))
  ({ R, t, idx := T.1, cut := T.2, tp := #[], idxp := {}, cutp := ByteArray.empty }, prune (SideChangeEnd.nextStates b.E false ends))

def rows (b : Ctx) : Array Row := Id.run do
  let mut rs := #[]
  let mut R := firstStates b
  for _ in [0:b.last + 1] do
    let (r, R') := row b R
    rs := rs.push r
    R := R'
  return rs

def checkOf (b : Ctx) (rs : Array Row) : Bool :=
  decide (b.last < b.first) || (decide (1 ≤ b.first) && decide (b.T < 2048) && decide (mode b < 2048) &&
  b.K.contains b.gps && b.x.ram.get! b.gps &&& 1 == 0 && bootOK b rs[0]! &&
  (List.range b.last).all (fun j => link b rs[j]! rs[j + 1]!))
def check (b : Ctx) : Bool := checkOf b (rows b)
theorem pad_mem {i : UInt8} (h : noSelect i = true) : pad.mem (smbToPad i) := by
  simpa [noSelect, pad, AB.mem] using h

/-- A frame either stays on the title or leaves it with Press. -/
theorem link_frame (hE : b.E.pad = AB.top) (hg : b.K.contains b.gps = true)
    (hp : b.x.ram.get! b.gps &&& 1 = 0) (hT : b.T < 2048) (hM : mode b < 2048)
    {r r' : Row} (h : link b r r' = true) {m : Machine} (hc : Covered b r m)
    {i : UInt8} (hi : noSelect i = true) :
    (Covered b r' (PipeTransition.frame m i) ∧ (PipeTransition.frame m i).ram.get! (mode b) = 0) ∨
    (Press b (PipeTransition.frame m i) ∧ (PipeTransition.frame m i).ram.get! (mode b) ≠ 0) := by
  obtain ⟨S, hS, hs⟩ := hc
  simp only [link, Bool.and_eq_true] at h
  have hs1 : Sim (cfg b r).E (m.frame, 2) S { m with pad := smbToPad i } :=
    sim_pad (sim_splits' hs) (pad_mem hi)
  obtain ⟨B, hf, hb⟩ := frame_of_start (C := cfg b r) h.1 rfl (List.all_eq_true.1 h.2 S hS) hs1
  have hE' : ({ b.E with splits := b.E.splits ++ [((b.sy.SavedJoypadBits &&& 0x7FF).toNat, 0x90)] } : Env).pad = AB.top := hE
  have hb' : Sim b.E (m.frame, 2) B (PipeTransition.frame m i) := sim_splits (sim_unpad hE' hb)
  simp only [fin, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
  rcases hf with ⟨h0, hf⟩ | ⟨hf, hn⟩
  · have hm := sim_known hb' h0
    simp only [finOf, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at hf
    obtain ⟨hr, D, hD, hle⟩ := hf
    exact Or.inl ⟨⟨D, hD, next_start hb' hr hle⟩, hm⟩
  · exact Or.inr ⟨press_of_fin hg hp hT hf hb', ne_zero_of_sim hb' hM hn⟩

/-- A run is indexed by its first exit from the title, rather than by the first input with Start. -/
structure Run (b : Ctx) (m : Machine) where
  kp : Nat
  pm : Nat → Machine
  pi : Nat → UInt8
  next : ∀ n, pm (n + 1) = PipeTransition.frame (pm n) (pi n)
  power : PowerOn b (pm 0)
  bootInput : noSS (pi 0) = true
  quiet : ∀ n, n ≤ kp → noSelect (pi n) = true
  stays : ∀ n, 2 ≤ n → n ≤ kp → (pm n).ram.get! (mode b) = 0
  left : m.ram.get! (mode b) ≠ 0
  lo : b.first ≤ kp
  hi : kp ≤ b.last
  after : m = pm (kp + 1)

variable {m : Machine}

theorem Run.press_of {rs : Array Row} (hE : b.E.pad = AB.top) (h : checkOf b rs = true) (R : Run b m) : Press b m := by
  simp only [checkOf, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  rcases h with hempty | h
  · have := R.lo; have := R.hi; omega
  obtain ⟨⟨⟨⟨⟨⟨hfirst, hT⟩, hM⟩, hg⟩, hp⟩, hboot⟩, hlinks⟩ := h
  have hc : ∀ n, n < R.kp → Covered b rs[n]! (R.pm (n + 1)) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [R.next]
      exact boot_frame hE hboot R.power R.bootInput
    | succ n ih =>
      intro hn
      rw [R.next]
      rcases link_frame hE hg hp hT hM (hlinks n (by have := R.hi; omega)) (ih (by omega)) (R.quiet (n + 1) (by omega)) with hstay | hleft
      · exact hstay.1
      · have he := R.stays (n + 2) (by omega) (by omega)
        rw [R.next] at he
        exact False.elim (hleft.2 he)
  have hk : 1 ≤ R.kp := by have := R.lo; omega
  have hcov := hc (R.kp - 1) (by omega)
  have he : R.kp - 1 + 1 = R.kp := by omega
  rw [he] at hcov
  rcases link_frame hE hg hp hT hM (hlinks (R.kp - 1) (by have := R.hi; omega)) hcov (R.quiet R.kp (Nat.le_refl _)) with hstay | hleft
  · have hz := hstay.2
    rw [← R.next, ← R.after] at hz
    exact False.elim (R.left hz)
  · rw [← R.next, ← R.after] at hleft
    exact hleft.1

theorem Run.press (hE : b.E.pad = AB.top) (h : check b = true) (R : Run b m) : Press b m :=
  R.press_of hE h

/-- A small native probe before committing to a larger ROM check. -/
def probe (b : Ctx) : IO Unit := do
  let mut R := firstStates b
  let mut prev : Option Row := none
  for j in [0:b.last + 1] do
    let (r, R') := row b R
    let ok := match prev with
      | none => bootOK b r
      | some q => link b q r
    if j % 20 == 0 || !ok then
      IO.println s!"menu row {j + 1}: states {R.length}, table {r.t.size}, next {R'.length}, link {ok}"
      (← IO.getStdout).flush
    if !ok then return
    prev := some r
    R := R'
end Menu

/-- **How the machine after the press is known**: by the run from power-on (`power`: one state and conditions on single inputs), or by the condition itself (`press`:
one state, as before, for a run that is not in the class of `Run`) -/
inductive Start (b : Ctx) (m : Machine) where
  | power (R : Run b m)
  | menu (R : Menu.Run b m)
  | later (R : Run (later b) m)
  | press (h : Press b m)

/-- **The condition at the press**, in all cases -/
theorem Start.cond (hE : b.E.pad = AB.top) (h : check b = true) (hm : Menu.check b = true) (hl : check (TitleBoot.later b) = true) : Start b m → Press b m
  | .power R => R.press hE h
  | .menu R => R.press hE hm
  | .later R => let h := Run.press (b := TitleBoot.later b) hE hl R; ⟨h.exit, h.timer⟩
  | .press h' => h'

end

end Smbrta.TitleBoot
