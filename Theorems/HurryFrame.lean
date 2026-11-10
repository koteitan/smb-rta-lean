import Theorems.FrameKeep
import Theorems.CastleToLevel

/-!
# The frame that starts the hurry-up music

`HurryMusic.Run` asked of the frame that starts the hurry-up music that the timer shows `u` or less when it begins (`music`). Here a walk of that one frame in control replaces it.
`PipeWrites` follows a whole frame in control with the abstract machine of `TaintRun`, and asks one condition on each instruction (`Clean`). The same walk here starts with the music
bits off: the bit of the hurry-up music in the event music queue and in its buffer, and the tempo's adder 0. Every path of the frame ends with these bits off, or with the timer's
three digits known and their value at most `u`. So a frame in control that ends with the music has the timer at `u` or less when it ends (`frame_music`).

The game queues the music in its timer routine, after it has read the digits; the routine then lowers them. A byte of the walk has known bits, and the digits are not known when the frame
starts. So at the timer routine's load of the first digit the walk splits it into its values, and at its load of the second digit it splits the second and the third into 0 or their lowest
bit 1 (`digitP`). Where the queue gets the music, the digits are then known.

The search is no part of the proof: `check` walks every state of its table. There is no game data in this file: the places come from the names of the disassembly and the symbols.
Page: `1-1/0-6-4-2-1-HurryFrame.md`.
-/

namespace Smbrta.HurryFrame

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace trace_stop findOp splitAll)
open PipeWrites (Guard Clean FrameStart gsucc capT jumpP startG keepKn leK joinK knownOf SG)
open FrameKeep (Watch watchOK Watched startK xPieces)

/-! ## The places -/

/-- a RAM index of a name -/
def adI (nm : Names) (n : String) : Nat := ((nm.ad n) &&& 0x7FF).toNat

/-- the timer's digits, the music bytes, the music's number, and the timer routine's loads of the first and the second digit -/
structure Places where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  queue : Nat
  buffer : Nat
  adder : Nat
  tro : UInt8
  /-- the load of the first digit into `Y` -/
  ldy : UInt16
  /-- the load of the second digit into `A`, after it -/
  lda : UInt16
  /-- other loads into a register, and the byte each loads: the walk splits the byte there into 0 or its lowest bit 1 -/
  loads : List (UInt16 × Nat)
  /-- the digits routine (no part of the proof: the search keeps its registers apart) -/
  dmr : UInt16
  /-- the bytes that the digits routine adds to the digits (`DigitModifier`): as many as its loop's count, read from the ROM -/
  mods : List Nat
  /-- the stores through an index into the digits or the bytes it adds: there a store with a target not known may change these bytes -/
  dset : List UInt16
  deriving Inhabited

/-- the places in the ROM of the instruction `op` with the absolute operand `a` -/
def findAbs (m0 : Machine) (op : UInt8) (a : UInt16) : List UInt16 :=
  (List.range 32765).filterMap fun i =>
    let p := (0x8000 + i).toUInt16
    if romByte m0 p == op && romByte m0 (p + 1) == a.toUInt8 && romByte m0 (p + 2) == (a >>> 8).toUInt8 then some p else none

/-- the places, from the names and the ROM. The other loads: the player's status into `X` and the flag of the death music into `Y`; on a death the game queues one more than
the register. -/
def placesOf (sy : Syms) (nm : Names) (m0 : Machine) : Places :=
  let a := nm.ad "GameTimerDisplay"
  let ldy := findOp m0 sy.RunGameTimer 0xAC 64
  let ps := nm.ad "PlayerStatus"
  let dm := nm.ad "DeathMusicLoaded"
  let lda := findOp m0 (ldy + 3) 0xAD 8
  let j := findOp m0 lda 0x20 32
  let dd := nm.ad "DisplayDigits"
  let mo := nm.ad "DigitModifier"
  let dmr := (romByte m0 (j + 1)).toUInt16 ||| ((romByte m0 (j + 2)).toUInt16 <<< 8)
  let nmods := (romByte m0 (findOp m0 dmr 0xA2 16 + 1)).toNat + 1
  { d0 := (a &&& 0x7FF).toNat, d1 := ((a + 1) &&& 0x7FF).toNat, d2 := ((a + 2) &&& 0x7FF).toNat,
    queue := adI nm "EventMusicQueue", buffer := adI nm "EventMusicBuffer", adder := adI nm "NoteLengthTblAdder",
    tro := nm.vl "TimeRunningOutMusic", ldy, lda,
    loads := (findAbs m0 0xAE ps).map (·, (ps &&& 0x7FF).toNat) ++ (findAbs m0 0xAC dm).map (·, (dm &&& 0x7FF).toNat),
    dmr,
    mods := (List.range nmods).map fun i => ((mo + i.toUInt16) &&& 0x7FF).toNat,
    dset := (findAbs m0 0x99 dd ++ findAbs m0 0x9D (mo - 1) ++ findAbs m0 0xDE (mo - 1) ++ findAbs m0 0xFE (mo - 1)).filter (fun p => decide (dmr ≤ p) && decide (p ≤ dmr + 64)) ++
      findAbs m0 0x9D mo }

/-- the music bits: the music's bit of the queue and of its buffer, and the tempo's adder -/
def watchOf (P : Places) : List Watch := [(P.queue, P.tro, 0), (P.buffer, P.tro, 0), (P.adder, 0xFF, 0)]

/-- the guard of `PipeWrites`, with the bytes of `Places.mods` known to be 0 when the frame starts (the game sets them just before it calls the digits routine, and the routine
clears them), and these, the music bytes and the digits among the bytes that a store with a target not known does not touch -/
def guardOf (sy : Syms) (nm : Names) (m0 : Machine) : Guard :=
  let G := PipeWrites.guardOf sy m0
  let P := placesOf sy nm m0
  { G with
    known := G.known ++ P.mods.map (·, 0)
    prot := P.queue :: P.buffer :: P.adder :: P.d0 :: P.d1 :: P.d2 :: P.mods ++ G.prot }

/-- the guard with the routine of the player's entrance known when the frame starts, in place of control: such a frame comes to control before the timer routine -/
def guardE (sy : Syms) (G : Guard) : Guard :=
  { G with known := G.known.map fun p => if p.1 == (sy.GameEngineSubroutine &&& 0x7FF).toNat then (p.1, sy.Eng_PlayerEntrance.toUInt8) else p }

/-- the bytes of `prot` but the digits and the bytes of `mods`: at the stores of `dset` a store with a target not known may change those -/
def protD (P : Places) (G : Guard) : List Nat := G.prot.filter fun i => !([P.d0, P.d1, P.d2] ++ P.mods).contains i

/-- the guard at the stores of `dset` -/
def guardD (P : Places) (G : Guard) : Guard := { G with prot := protD P G }

/-- one step: at the stores of `dset` with the guard of `guardD`, elsewhere with `G` -/
def mstep (G GD : Guard) (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if P.dset.contains A.pc then gsucc GD E ops A else gsucc G E ops A

/-! ## The pieces -/

/-- a byte that is not known: 0, or its lowest bit 1 at `b` -/
def lowP (d : Nat) (A : AS) : List AS := if (A.getK d).isK then [A] else xPieces.map fun p => A.setK d p

/-- at the load of the first digit: its values. At the load of the second: the second and the third, 0 or not. At the other loads: the byte, 0 or not. -/
def digitP (P : Places) (A : AS) : List AS :=
  if A.nmi then [A]
  else if A.pc == P.ldy then splitAll P.d0 A
  else if A.pc == P.lda then (lowP P.d1 A).flatMap fun B => if (B.getK P.d1).isK && (B.getK P.d1).v == 0 then lowP P.d2 B else [B]
  else match P.loads.find? (fun l => l.1 == A.pc) with
    | some l => lowP l.2 A
    | none => [A]

/-- the pieces before a step: the time, the jump's table, the digits -/
def preM (G : Guard) (P : Places) (A : AS) : List AS := (jumpP G (capT G A)).flatMap (digitP P)

/-! ## The walk -/

/-- the digits are known, and their value is at most `u` -/
def lowTimer (P : Places) (u : Nat) (B : AS) : Bool :=
  (B.getK P.d0).isK && (B.getK P.d1).isK && (B.getK P.d2).isK &&
    decide (100 * (B.getK P.d0).v.toNat + 10 * (B.getK P.d1).v.toNat + (B.getK P.d2).v.toNat ≤ u)

/-- the frame's end: the music bits off, or the timer at `u` or less -/
def finM (P : Places) (u : Nat) (B : AS) : Bool := watchOK (watchOf P) B || lowTimer P u B

/-- the bytes that the digits routine adds, watched: all bits 0 -/
def modsW (P : Places) : List Watch := P.mods.map fun i => (i, 0xFF, 0)

/-- the queue knows a bit of the music set -/
def queuedOn (P : Places) (B : AS) : Bool := (B.getK P.queue).v &&& (B.getK P.queue).k &&& P.tro != 0

/-- the frame's end as the walk checks it: `finM`, and either the music is queued, or the next frame starts as a frame in control asks (`FrameKeep.endOK`) with the bytes
that the digits routine adds 0 and the music bits off -/
def finS (G : Guard) (P : Places) (u : Nat) (B : AS) : Bool :=
  finM P u B && (queuedOn P B || (FrameKeep.endOK G B && watchOK (modsW P ++ watchOf P) B))

/-- the table -/
structure CfgM where
  E : Env
  ops : Array (AM Unit)
  G : Guard
  GD : Guard
  P : Places
  u : Nat
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  /-- the table's key of a state: no part of the proof -/
  key : AS → Nat

def coverM (C : CfgM) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end with `finS` -/
def walkM (C : CfgM) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preM C.G C.P A).all fun A₁ => (mstep C.G C.GD C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverM C B) || walkM C n B
      else B.k == A.k + 1 && finS C.G C.P C.u B

/-! ## Finding the table: a search, no part of the proof -/

/-- in the timer routine, from its start to the load of the second digit and a little after: the search keeps the registers and the digits apart there -/
def inTimer (sy : Syms) (P : Places) (pc : UInt16) : Bool := decide (sy.RunGameTimer ≤ pc) && decide (pc ≤ P.lda + 16)

/-- in the digits routine: the search keeps its registers apart there -/
def inDigits (P : Places) (pc : UInt16) : Bool := decide (P.dmr ≤ pc) && decide (pc ≤ P.dmr + 64)

/-- a little after one of the other loads: the search keeps the registers apart there -/
def nearLoad (P : Places) (pc : UInt16) : Bool := P.loads.any fun l => decide (l.1 ≤ pc) && decide (pc ≤ l.1 + 12)

/-- what the search forgets: the bytes outside `prot` and the free stack; near the jump routine and in the timer routine nothing -/
def normM (sy : Syms) (G : Guard) (P : Places) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if (G.je ≤ A.pc && A.pc ≤ G.je + 18) || inTimer sy P A.pc || nearLoad P A.pc || inDigits P A.pc then A else
  let B := PipeWrites.AS.forgetW G.prot A
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
  { B with kn }

/-- the queue knows the music's bit set -/
def troOn (P : Places) (A : AS) : Bool := (A.getK P.queue).k &&& P.tro != 0 && (A.getK P.queue).v &&& P.tro != 0

/-- a watched byte, by its watched bits: known with the value, known with another value, or not known -/
def wstat (A : AS) (w : Watch) : Nat :=
  let b := A.getK w.1
  if b.k &&& w.2.1 == w.2.1 then (if b.v &&& w.2.1 == w.2.2 &&& w.2.1 then 1 else 2) else 0

/-- the key: states with the same key are joined -/
def keyM (sy : Syms) (G : Guard) (P : Places) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := num (A.getK G.rtI)
  let n := (watchOf P).foldl (fun n w => n * 3 + wstat A w) n
  let n := if troOn P A || inTimer sy P A.pc then [P.d0, P.d1, P.d2].foldl (fun n i => n * 65536 + num (A.getK i)) n else n
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0)
  let n := if G.je ≤ A.pc && A.pc ≤ G.je + 18 then (n * 65536 + num A.a) * 65536 + num A.y else n
  let n := if inTimer sy P A.pc then ((n * 65536 + num A.a) * 65536 + num A.y) * 256 + num A.p else n
  let n := if nearLoad P A.pc || inDigits P A.pc then (((n * 65536 + num A.x) * 65536 + num A.y) * 65536 + num A.a) * 256 + num A.p else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

def routeM (sy : Syms) (G : Guard) (P : Places) (X : SG) (B0 : AS) : SG :=
  let B := normM sy G P B0
  let K := keyM sy G P B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runM (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preM G P cur).flatMap (mstep G GD P E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !finS G P u B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != P.ldy && b.pc != P.lda &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeM sy G P X b
    break
  return X

partial def searchM (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runM sy G GD E P u ops X A
  return X

/-- the abstract states when the frame starts: in control or in the entrance, just before or just after the frame's first event -/
def startsM (sy : Syms) (G : Guard) (P : Places) : List AS :=
  [startK G (watchOf P) false, startK G (watchOf P) true, startK (guardE sy G) (watchOf P) false, startK (guardE sy G) (watchOf P) true]

def searchOfM (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) : SG :=
  let ops := (aRows E).toArray
  searchM sy G GD E P u ops ((startsM sy G P).foldl (routeM sy G P) {})

/-- the table, from the search: every state that was reached more than once -/
def tableOfM (sy : Syms) (G : Guard) (P : Places) (X : SG) : Array AS × Std.HashMap Nat (List Nat) × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat (List Nat) := {}
  let mut cut := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (keyM sy G P A) (t.size :: idx.getD (keyM sy G P A) [])
      cut := cut.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, cut)

def cfgOfM (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) : CfgM :=
  let q := tableOfM sy G P (searchOfM sy G GD E P u)
  { E, ops := (aRows E).toArray, G, GD, P, u, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key := keyM sy G P }

/-- the fuel of a walk -/
def fuelM : Nat := 20000

/-- **The check.** -/
def musicCheck (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) : Bool :=
  let C := cfgOfM sy G GD E P u
  decide (G.late < dotsPerFrame) && decide (P.d0 < 2048) && decide (P.d1 < 2048) && decide (P.d2 < 2048) && decide (P.queue < 2048) &&
    C.t.all (walkM C fuelM) && (startsM sy G P).all (walkM C fuelM)

/-- the check on the ROM -/
def checkOf (sy : Syms) (nm : Names) (m0 : Machine) (u : Nat) : Bool :=
  let P := placesOf sy nm m0
  let G := guardOf sy nm m0
  musicCheck sy G (guardD P G) (PipeEntryRule.envOf m0) P u

/-! ## The condition on one instruction -/

/-- **What stays assumed of one instruction**: `PipeWrites.Clean`, but at the stores of `D` a store through an index is `Plain` for `pd` only: there it may change the bytes of
`G.prot` that are not in `pd` (the digits and the bytes of `Places.mods`). -/
structure CleanM (G : Guard) (pd : List Nat) (D : List UInt16) (m : Machine) : Prop where
  /-- a store through an index or a pointer is `Plain`, for `pd` at the stores of `D` -/
  store : ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → PipeWrites.Plain (if D.contains m.pc then pd else G.prot) t
  /-- `LDA (zp),Y` does not read a register -/
  read : PipeWrites.opAt m = 0xB1 → PipeWrites.rTarget m < 0x2000 ∨ 0x8000 ≤ PipeWrites.rTarget m
  /-- the index of the jump is in its table -/
  jump : m.pc = G.je → ∀ n, G.jumps.lookup (PipeWrites.tableOf m).toNat = some n → m.a.toNat < n
  /-- the time -/
  time : m.pc ≠ G.idle → m.fdot ≤ G.late

section
variable {G : Guard} {pd : List Nat} {D : List UInt16} {m : Machine}

theorem clean_G (h : CleanM G pd D m) (hd : D.contains m.pc = false) : Clean G m :=
  ⟨fun t ht => by
    have h1 := h.store t ht
    rw [hd] at h1
    exact h1, h.read, h.jump, h.time⟩

theorem clean_D (h : CleanM G pd D m) (hd : D.contains m.pc = true) : Clean { G with prot := pd } m :=
  ⟨fun t ht => by
    have h1 := h.store t ht
    rw [hd] at h1
    exact h1, h.read, h.jump, h.time⟩

end

/-! ## The steps follow the machine -/

section
variable {E : Env} {F : Nat × UInt8}

set_option maxRecDepth 100000 in
/-- **A step of the machine**: with the guard of `D` at its stores, else with `G` -/
theorem s_mstep {G : Guard} {pd : List Nat} {P : Places} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (hc : CleanM G pd P.dset m) (hs : Sim E F A m) :
    ∃ r ∈ mstep G { G with prot := pd } P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold mstep
  by_cases h : P.dset.contains A.pc = true
  · rw [if_pos h]
    exact PipeWrites.s_gsucc hops hT (clean_D hc (by rw [hs.pc]; exact h)) hs
  · rw [if_neg h]
    exact PipeWrites.s_gsucc hops hT (clean_G hc (by rw [hs.pc]; simpa using h)) hs

theorem sim_capM {G : Guard} {pd : List Nat} {D : List UInt16} {A : AS} {m : Machine} (hc : CleanM G pd D m) (hs : Sim E F A m) : Sim E F (capT G A) m := by
  unfold capT
  by_cases h : (A.pc != G.idle && decide (G.late < A.hi)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hl := hs.lim
    exact { hs with
      hi := hc.time (by rw [hs.pc]; exact h1)
      lim := by
        show G.late < dotsPerFrame
        omega }
  · rw [if_neg h]
    exact hs

theorem cov_jumpM {G : Guard} {pd : List Nat} {D : List UInt16} {A : AS} {m : Machine} (hc : CleanM G pd D m) (hs : Sim E F A m) : ∃ B ∈ jumpP G A, Sim E F B m := by
  unfold jumpP
  by_cases h : (A.pc == G.je && !A.a.isK) = true
  · rw [if_pos h]
    have hpc : m.pc = G.je := by
      rw [hs.pc]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    cases hp : ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
    | some r =>
      simp only
      cases hl : G.jumps.lookup (r + 1).toNat with
      | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      | some n =>
        simp only
        have hsz : A.s.toNat < 256 := A.s.toNat_lt
        have e1 := hs.ram (0x100 + A.s.toNat + 1) (by omega)
        have e2 := hs.ram (0x100 + A.s.toNat + 2) (by omega)
        have e3 := TaintRun.ptrOf_ok hp e1 e2
        have ht : PipeWrites.tableOf m = r + 1 := by
          unfold PipeWrites.tableOf
          rw [hs.s, e3]
        have hlt := hc.jump hpc n (by rw [ht]; exact hl)
        refine ⟨_, List.mem_map.2 ⟨m.a.toNat, List.mem_range.2 hlt, rfl⟩, ?_⟩
        refine { hs with a := ?_ }
        have e4 : m.a.toNat.toUInt8 = m.a := by simp
        show (AB.known m.a.toNat.toUInt8).mem m.a
        rw [e4]
        exact mem_known_self _
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

/-- a byte that is not known: 0 or its lowest bit 1 -/
theorem cov_lowP (d : Nat) : Cov E F (lowP d) := by
  intro A m hs
  unfold lowP
  split
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · obtain ⟨p, hp, hm⟩ := FrameKeep.xPieces_cover (m.ram.get! d)
    exact ⟨A.setK d p, List.mem_map.2 ⟨p, hp, rfl⟩, PipeEntryRule.sim_setK' hs hm, rfl⟩

/-- the pieces of the digits cover the machine -/
theorem cov_digitP {P : Places} (hd : P.d0 < 2048) : Cov E F (digitP P) := by
  intro A m hs
  unfold digitP
  split
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · split
    · exact PipeEntryRule.cov_all hd A m hs
    · split
      · obtain ⟨B, hB, h1, h2⟩ := cov_lowP P.d1 A m hs
        have h3 : ∃ C ∈ (if ((B.getK P.d1).isK && (B.getK P.d1).v == 0) = true then lowP P.d2 B else [B]), Sim E F C m ∧ C.k = A.k := by
          split
          · obtain ⟨C, hC, g1, g2⟩ := cov_lowP P.d2 B m h1
            exact ⟨C, hC, g1, g2.trans h2⟩
          · exact ⟨B, List.mem_singleton.2 rfl, h1, h2⟩
        obtain ⟨C, hC, g1, g2⟩ := h3
        exact ⟨C, List.mem_flatMap.2 ⟨B, hB, hC⟩, g1, g2⟩
      · split
        · exact cov_lowP _ A m hs
        · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- **The pieces cover the machine** -/
theorem cov_preM {G : Guard} {pd : List Nat} {D : List UInt16} {P : Places} (hd : P.d0 < 2048) {A : AS} {m : Machine} (hc : CleanM G pd D m) (hs : Sim E F A m) :
    ∃ B ∈ preM G P A, Sim E F B m ∧ B.k = A.k := by
  have h1 := sim_capM hc hs
  obtain ⟨B, hB, h2⟩ := cov_jumpM hc h1
  obtain ⟨C, hC, h3, h4⟩ := cov_digitP hd B m h2
  exact ⟨C, List.mem_flatMap.2 ⟨B, hB, hC⟩, h3, h4.trans (FrameKeep.k_of_sim hs h2)⟩

end

/-! ## The walk covers the frame -/

section
variable {C : CfgM} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveM (C : CfgM) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkM C n A = true

theorem cover_liveM (ht : C.t.all (walkM C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverM C B = true) :
    ∃ D, LiveM C F D m ∧ D.k = B.k := by
  unfold coverM at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepM {pd : List Nat} (hGD : C.GD = { C.G with prot := pd }) (hd : C.P.d0 < 2048) (ht : C.t.all (walkM C Fu) = true) (hkl : C.kl = C.t.map knownOf)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveM C F A m) (hh : CleanM C.G pd C.P.dset m) :
    (∃ A', LiveM C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, finS C.G C.P C.u B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkM] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preM hd hh hs
    obtain ⟨r, hr, hB⟩ := s_mstep (P := C.P) hops hT hh hs1
    rw [← hGD] at hr
    simp only [walkM, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveM ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `CleanM`. -/
theorem frame_of_walkM {pd : List Nat} (hGD : C.GD = { C.G with prot := pd }) (hd : C.P.d0 < 2048) (ht : C.t.all (walkM C Fu) = true) (hkl : C.kl = C.t.map knownOf)
    (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkM C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, CleanM C.G pd C.P.dset (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, finS C.G C.P C.u B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveM C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, finS C.G C.P C.u B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        rcases live_stepM hGD hd ht hkl hops hT h1 (hk j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h3, h4⟩

end

/-! ## The frame -/

/-- the value of the timer's three digits, as the timer is read (`CastleToLevel.timerOf`) -/
def timerAt (P : Places) (m : Machine) : Nat := 100 * (m.ram.get! P.d0).toNat + 10 * (m.ram.get! P.d1).toNat + (m.ram.get! P.d2).toNat

section
variable {E : Env} {F : Nat × UInt8}

/-- the frame's end: the music bits off, or the timer at `u` or less -/
theorem fin_ok {P : Places} {u : Nat} {B : AS} {m : Machine} (h1 : P.d1 < 2048) (h2 : P.d2 < 2048) (hd : P.d0 < 2048) (hf : finM P u B = true) (hs : Sim E F B m) :
    Watched (watchOf P) m ∨ timerAt P m ≤ u := by
  unfold finM at hf
  simp only [Bool.or_eq_true] at hf
  rcases hf with h | h
  · exact Or.inl (FrameKeep.watched_of h hs)
  · right
    unfold lowTimer at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨k0, k1⟩, k2⟩, hle⟩ := h
    have e0 := isK_eq k0 (hs.ram P.d0 hd)
    have e1 := isK_eq k1 (hs.ram P.d1 h1)
    have e2 := isK_eq k2 (hs.ram P.d2 h2)
    unfold timerAt
    rw [e0, e1, e2]
    exact hle

/-- a queue that knows a bit of the music set: the music bits are not off -/
theorem not_watched_of_queued {P : Places} {B : AS} {m : Machine} (hq : P.queue < 2048) (h : queuedOn P B = true) (hs : Sim E F B m) :
    ¬ Watched (watchOf P) m := by
  intro hw
  have h1 : m.ram.get! P.queue &&& P.tro = 0 &&& P.tro := hw _ List.mem_cons_self
  rw [UInt8.zero_and] at h1
  have h2 : m.ram.get! P.queue &&& (B.getK P.queue).k = (B.getK P.queue).v &&& (B.getK P.queue).k := hs.ram P.queue hq
  unfold queuedOn at h
  simp only [bne_iff_ne, ne_eq] at h
  apply h
  rw [← h2, UInt8.and_assoc, UInt8.and_comm (B.getK P.queue).k P.tro, ← UInt8.and_assoc, h1, UInt8.zero_and]

end

/-- what the check says -/
structure MusicOK (sy : Syms) (G GD : Guard) (E : Env) (P : Places) (u : Nat) : Prop where
  late : G.late < dotsPerFrame
  d0 : P.d0 < 2048
  d1 : P.d1 < 2048
  d2 : P.d2 < 2048
  queue : P.queue < 2048
  table : (cfgOfM sy G GD E P u).t.all (walkM (cfgOfM sy G GD E P u) fuelM) = true
  starts : (startsM sy G P).all (walkM (cfgOfM sy G GD E P u) fuelM) = true

theorem musicOK_of_check {sy : Syms} {G GD : Guard} {E : Env} {P : Places} {u : Nat} (h : musicCheck sy G GD E P u = true) : MusicOK sy G GD E P u := by
  simp only [musicCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h7⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h7, h5, h6⟩

/-- **One frame in control or in the entrance, as the walk ends it.** A frame that starts in the idle loop with the routine of control or of the entrance and the bytes of the
digits routine 0 (`FrameStart`), with the music bits off, and whose every instruction meets `CleanM`, ends in a state of `finS`. -/
theorem frame_end_of {sy : Syms} {G : Guard} {pd : List Nat} {E : Env} {P : Places} {u : Nat} (hc : musicCheck sy G { G with prot := pd } E P u = true)
    (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m ∨ FrameStart (guardE sy G) E m) (hw : Watched (watchOf P) m)
    (hk : ∀ j, CleanM G pd P.dset (trace m i j)) : ∃ B, finS G P u B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  have hC := musicOK_of_check hc
  have hS : ∃ S ∈ startsM sy G P, Sim E (m.frame, 2) S m := by
    rcases h0 with h | h
    · obtain ⟨b, hs⟩ := FrameKeep.sim_startK hE h hw
      cases b with
      | false => exact ⟨_, by simp [startsM], hs⟩
      | true => exact ⟨_, by simp [startsM], hs⟩
    · obtain ⟨b, hs⟩ := FrameKeep.sim_startK hE h hw
      cases b with
      | false => exact ⟨_, by simp [startsM], hs⟩
      | true => exact ⟨_, by simp [startsM], hs⟩
  obtain ⟨S, hSm, hs⟩ := hS
  have hw0 := List.all_eq_true.1 hC.starts S hSm
  obtain ⟨_, B, h1, _, h2⟩ := frame_of_walkM (C := cfgOfM sy G { G with prot := pd } E P u) (F := (m.frame, 2)) (pd := pd) rfl hC.d0 hC.table rfl rfl
    (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs hk
  exact ⟨B, h1, h2⟩

/-- **One frame in control or in the entrance.** A frame that starts in the idle loop with the routine of control or of the entrance and the bytes of the digits routine 0
(`FrameStart`), with the music bits off, and whose every instruction meets `CleanM`, ends with the music bits off, or with the timer at `u` or less. -/
theorem frame_music_of {sy : Syms} {G : Guard} {pd : List Nat} {E : Env} {P : Places} {u : Nat} (hc : musicCheck sy G { G with prot := pd } E P u = true)
    (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m ∨ FrameStart (guardE sy G) E m) (hw : Watched (watchOf P) m)
    (hk : ∀ j, CleanM G pd P.dset (trace m i j)) : Watched (watchOf P) (frame m i) ∨ timerAt P (frame m i) ≤ u := by
  have hC := musicOK_of_check hc
  obtain ⟨B, h1, h2⟩ := frame_end_of hc hE h0 hw hk
  unfold finS at h1
  rw [Bool.and_eq_true] at h1
  exact fin_ok hC.d1 hC.d2 hC.d0 h1.1 h2

/-! ## On the ROM -/

/-- the timer of `CastleToLevel` is the value of the digits of the places -/
theorem timer_eq (sy : Syms) (nm : Names) (m0 m : Machine) : CastleToLevel.timerOf nm m = timerAt (placesOf sy nm m0) m := rfl

/-- **The frame starts** in the idle loop, with the routine of control or of the entrance, and the bytes of `Places.mods` 0: `FrameStart` with the guard of the ROM -/
def Start (sy : Syms) (nm : Names) (m0 m : Machine) : Prop :=
  FrameStart (guardOf sy nm m0) (PipeEntryRule.envOf m0) m ∨ FrameStart (guardE sy (guardOf sy nm m0)) (PipeEntryRule.envOf m0) m

/-- **The condition on one instruction**, with the guard of the ROM: `CleanM` -/
def CleanAt (sy : Syms) (nm : Names) (m0 m : Machine) : Prop :=
  CleanM (guardOf sy nm m0) (protD (placesOf sy nm m0) (guardOf sy nm m0)) (placesOf sy nm m0).dset m

/-- **The frame that starts the hurry-up music, on the ROM.** `hc` is the walk's check. -/
theorem frame_music {sy : Syms} {nm : Names} {m0 : Machine} {u : Nat} (hc : checkOf sy nm m0 u = true) {m : Machine} {i : UInt8}
    (h0 : Start sy nm m0 m) (hw : Watched (watchOf (placesOf sy nm m0)) m) (hk : ∀ j, CleanAt sy nm m0 (trace m i j)) :
    Watched (watchOf (placesOf sy nm m0)) (frame m i) ∨ CastleToLevel.timerOf nm (frame m i) ≤ u :=
  frame_music_of hc rfl h0 hw hk

/-- the known bytes of the guard of the ROM, on a machine with control and the bytes of `Places.mods` 0 -/
theorem known_of {sy : Syms} {nm : Names} {m0 m : Machine} (hc : controllable sy m = true) (hm : Watched (modsW (placesOf sy nm m0)) m) :
    ∀ p ∈ (guardOf sy nm m0).known, m.ram.get! p.1 = p.2 := by
  intro p hp
  have e : (guardOf sy nm m0).known = (FrameKeep.guardK sy m0).known ++ (placesOf sy nm m0).mods.map (fun i => (i, (0 : UInt8))) := rfl
  rw [e, List.mem_append] at hp
  rcases hp with hp | hp
  · exact FrameKeep.known_of_ctl hc p hp
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have h1 : m.ram.get! i &&& 0xFF = (0 : UInt8) &&& 0xFF := hm (i, 0xFF, 0) (List.mem_map.2 ⟨i, hi, rfl⟩)
    rw [FrameKeep.and_ff, FrameKeep.and_ff] at h1
    exact h1

/-- **A frame in control or in the entrance that ends with control, on the ROM.** From the music bits off, it ends with the music in the queue, or at the start of a frame in
control (`Start`) with the music bits off: the same walk as `frame_music`, whose ends know the start of the next frame and the bytes of `Places.mods`. `hc` is the walk's check. -/
theorem frame_start {sy : Syms} {nm : Names} {m0 : Machine} {u : Nat} (hc : checkOf sy nm m0 u = true) {m : Machine} {i : UInt8}
    (h0 : Start sy nm m0 m) (hw : Watched (watchOf (placesOf sy nm m0)) m) (hk : ∀ j, CleanAt sy nm m0 (trace m i j)) (hctl : controllable sy (frame m i) = true) :
    ¬ Watched (watchOf (placesOf sy nm m0)) (frame m i) ∨ (Start sy nm m0 (frame m i) ∧ Watched (watchOf (placesOf sy nm m0)) (frame m i)) := by
  obtain ⟨B, h1, h2⟩ := frame_end_of hc rfl h0 hw hk
  have hC := musicOK_of_check hc
  unfold finS at h1
  rw [Bool.and_eq_true, Bool.or_eq_true] at h1
  rcases h1.2 with h | h
  · exact Or.inl (not_watched_of_queued hC.queue h h2)
  · rw [Bool.and_eq_true] at h
    have hw2 := FrameKeep.watched_of h.2 h2
    have hm : Watched (modsW (placesOf sy nm m0)) (frame m i) := fun w hw' => hw2 w (List.mem_append_left _ hw')
    have hwm : Watched (watchOf (placesOf sy nm m0)) (frame m i) := fun w hw' => hw2 w (List.mem_append_right _ hw')
    exact Or.inr ⟨Or.inl (FrameKeep.start_of_sim h2 h.1 rfl rfl (known_of hctl hm)), hwm⟩

end Smbrta.HurryFrame
