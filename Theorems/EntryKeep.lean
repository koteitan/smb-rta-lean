import Theorems.TitleStart
import Theorems.FrameKeep
import Theorems.PipeChangeEnd

/-!
# The state at the vertical pipe's entry, from the press of Start on the title

`PipeChangeEnd.Entry` is the condition on the state at the end of the frame that enters the vertical pipe: the frame has ended in the idle loop, and some bytes have the values of
the reference entry, some of them under a mask. Here most of these bytes are proved from the press of Start on the title (`TitleStart.Begin`), and from the frames from control to
the entry:

* frame 0 (the frame before control) begins in a state of `TitleStart`'s set. A walk of that frame shows that it ends with the kept bytes (`kept`) at the entry's values (`nearCheck`);
* each frame from control to the entry starts in the idle loop in control (`PipeWrites.FrameStart`), and each of its instructions meets `PipeWrites.Clean` with the kept bytes among the
  bytes that a store through an index or a pointer does not touch (`guardOf`). A walk of one whole frame (as in `FrameKeep`, with every byte not known but the kept ones) shows that such
  a frame ends with the kept bytes at their values when the routine at its end is the player's, and with the bytes `atEntry` at the entry's values when it is the pipe's (`keepCheck`).

The frame of the entry ends in the idle loop (`IdleAt`): the walk shows this too. What stays assumed at the entry is `Rest`: the condition of `Entry` on the bytes of
`restNames` only, and the pipe's timer. The bytes of `restNames` are those that differ at control or that the walk does not know there; those that change on the way on real runs;
those that a frame may write when nothing on the screen is known (a new object, the music of an event, a new area); those that real frames write through an index; and two that
the frame of a warp pipe writes. The walk knows the timer only by some of its bits at some ends of the entry frame, where the side pipe's code has also run.

The searches are no part of the proof: the checks walk every state of their tables. There is no game data in this file. Page: `1-1/b-3-4-EntryKeep.md`.
-/

namespace Smbrta.EntryKeep

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace nxt frame_trace)
open PipeWrites (Guard Clean FrameStart SG leK joinK knownOf)
open FrameKeep (Watch watchOK Watched Spot CleanK kstep preK normK keyK startK)

/-! ## The bytes -/

/-- **The bytes of the condition at the entry that are not proved here**: a name, an offset, a number of bytes.
* not known at control, or other values there: the buttons up and down, the routine, the enemies' page, the screen's timer and the demo's, three bytes after the world's number in the
  menu, the byte after the mode, the pause's bits, the saved song;
* other values on the way on real runs: the first block's state, the first misc object, the first scores, Mario's state, the first two enemies' states, the sound effects;
* written by a frame where nothing on the screen is known: the buttons left and right, the slots of the power-up and others, the music and the noise, the flagpole's number, the vine,
  the first cannon, the frenzy, the duplicate, the warp zone, the colours, the loop, the next area, the star;
* written through an index on real frames: the second block's state, the second enemy, the third enemy's state, two scores;
* written by the frame of a warp pipe: the world and the flag of a new game timer. -/
def restNames : List (String × Nat × Nat) :=
  [("Up_Down_Buttons", 0, 1), ("GameEngineSubroutine", 0, 1), ("EnemyObjectPageLoc", 0, 1), ("EnemyObjectPageSel", 0, 1), ("ScreenTimer", 0, 1), ("DemoTimer", 0, 1),
   ("WorldSelectNumber", 2, 3), ("OperMode", 1, 1), ("GamePauseStatus", 0, 1), ("AreaMusicBuffer_Alt", 0, 1),
   ("Block_State", 0, 2), ("Block_RepFlag", 0, 2), ("Misc_State", 8, 1), ("Misc_Y_Position", 8, 1), ("FloateyNum_Control", 0, 3), ("FloateyNum_Control", 5, 1),
   ("Player_State", 0, 1), ("Enemy_State", 0, 3), ("Enemy_State", 5, 1), ("Square1SoundQueue", 0, 1), ("Square2SoundQueue", 0, 1),
   ("Left_Right_Buttons", 0, 1), ("Enemy_Flag", 4, 2), ("Enemy_ID", 0, 3), ("Enemy_ID", 4, 2), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1),
   ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("FlagpoleFNum_Y_Pos", 0, 1), ("VineFlagOffset", 0, 1), ("VineHeight", 0, 1),
   ("Cannon_Offset", 0, 1), ("Cannon_PageLoc", 0, 1), ("Cannon_X_Position", 0, 1), ("Cannon_Y_Position", 0, 1), ("EnemyFrenzyBuffer", 0, 1), ("EnemyFrenzyQueue", 0, 1),
   ("DuplicateObj_Offset", 0, 1), ("WarpZoneControl", 0, 1), ("BackgroundColorCtrl", 0, 1), ("LoopCommand", 0, 1), ("AreaPointer", 0, 1), ("EntrancePage", 0, 1),
   ("StarInvincibleTimer", 0, 1), ("WorldNumber", 0, 1), ("FetchNewGameTimerFlag", 0, 1)]

/-- these bytes as RAM indices -/
def restIdx (nx : Names) : List Nat := SideChangeBound.bytesOf nx restNames

/-- every byte of the condition at the entry: its index, the bits it asks, the values of the reference entry -/
def entryW (d : PipeChangeEnd.Data) (e : Machine) : List Watch :=
  d.known.map (fun i => (i, (0xFF : UInt8), e.ram.get! i)) ++ d.bits.map (fun b => (b.1, b.2, e.ram.get! b.1))

/-- **the bytes proved at the entry**: all but those of `restNames` -/
def atEntry (d : PipeChangeEnd.Data) (e : Machine) : List Watch := (entryW d e).filter fun w => !(restIdx d.nx).contains w.1

/-- the mode and the task: each frame's start in control gives them -/
def ctlIdx (sy : Syms) : List Nat := [(sy.OperMode &&& 0x7FF).toNat, (sy.OperMode_Task &&& 0x7FF).toNat]

/-- **the bytes the frames keep** from control to the entry: those of `atEntry` but the mode and the task -/
def kept (sy : Syms) (d : PipeChangeEnd.Data) (e : Machine) : List Watch := (atEntry d e).filter fun w => !(ctlIdx sy).contains w.1

/-- **The condition at the entry that stays assumed**: the bytes of `restNames` that `Entry` asks have the reference's values (all bits, or the bits of the mask), and the pipe's
timer is at least its first value. -/
abbrev Rest (d : PipeChangeEnd.Data) (e : Machine) (m : Machine) : Prop :=
  (∀ i ∈ d.known, i ∈ restIdx d.nx → m.ram.get! i = e.ram.get! i) ∧ PipeChangeEnd.timerF ≤ (m.ram.get! (PipeChangeEnd.envOf d e).rkI).toNat ∧
    PipeChangeEnd.BitsAt (d.bits.filter fun b => (restIdx d.nx).contains b.1) e m

/-- **The frame has ended in the idle loop**, as `Entry` asks: just before or just after the frame's first event, with the program counter and the stack of the reference -/
structure IdleAt (E : Env) (e m : Machine) : Prop where
  dot : m.fdot < 10
  flags : (m.fdot = 0 ∧ m.vblank = false ∧ m.nmiPending = false) ∨ (1 ≤ m.fdot ∧ m.vblank = true ∧ m.nmiPending = true)
  s0 : m.sprite0 = true
  ctrl : m.ppuCtrl &&& 0x80 = 0x80
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048
  pc : m.pc = e.pc
  s : m.s = e.s

/-- **The guard** of the frames from control to the entry: that of `PipeWrites`, with the kept bytes among the bytes that a store with a target not known does not touch -/
def guardOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Guard :=
  let G := PipeWrites.guardOf sy m0
  { G with prot := (kept sy d e).map (·.1) ++ G.prot }

/-- no store of the move routine is set apart -/
def spot : Spot := { entry := 0, store := 0, temps := [] }

/-! ## The walk of one frame -/

/-- **The frame's end**: the routine is known; if it is the player's, the bytes `W` are known with their values, and `y` (on the ROM: the idle loop as a frame in control
starts, `FrameKeep.endOK`); if it is the pipe's, the bytes `W₃`, and `x` -/
def finE (rtI : Nat) (ctl vp : UInt8) (W W₃ : List Watch) (y x : AS → Bool) (B : AS) : Bool :=
  decide (rtI < 2048) && (B.getK rtI).isK && ((B.getK rtI).v != ctl || (watchOK W B && y B)) && ((B.getK rtI).v != vp || (watchOK W₃ B && x B))

/-- the state is at a frame's start in the idle loop, as `IdleAt` asks: the dots, the flags, the control register's top bit, the strobe, the program counter and the stack of `e` -/
def idleOK (e : Machine) (B : AS) : Bool :=
  decide (B.hi ≤ 9) && ((!B.vb && !B.nmi && B.hi == 0) || (B.vb && B.nmi && decide (1 ≤ B.lo))) && B.ppuCtrl.k &&& 0x80 == 0x80 && B.ppuCtrl.v &&& 0x80 == 0x80 &&
    !B.strobe && B.pc == e.pc && B.s == e.s

/-- the table -/
structure CfgE where
  E : Env
  ops : Array (AM Unit)
  S : Spot
  G : Guard
  fin : AS → Bool
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray
  /-- the table's key of a state: no part of the proof -/
  key : AS → Nat

def coverE (C : CfgE) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end with `fin` -/
def walkE (C : CfgE) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverE C B) || walkE C n B
      else B.k == A.k + 1 && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- the search keeps `A` apart where it is about to be stored as the routine -/
def rtStoreAt (E : Env) (rtI : Nat) (pc : UInt16) : Bool :=
  let op := fun (a : UInt16) => E.prg.get! (a &&& E.mask).toNat
  let isSt := fun (a : UInt16) => (op a == 0x85 && (op (a + 1)).toNat == rtI) || (op a == 0x8D && (op (a + 1)).toNat + 256 * (op (a + 2)).toNat == rtI)
  let isJ := fun (a : UInt16) => op a == 0x20 && isSt ((op (a + 1)).toUInt16 + 256 * (op (a + 2)).toUInt16)
  isSt pc || isJ pc || ((op pc == 0xA0 || op pc == 0xA2) && (isSt (pc + 2) || isJ (pc + 2)))

/-- the key of the search: that of `FrameKeep` with no watched byte, and `A` where it is about to be stored as the routine -/
def keyE (E : Env) (S : Spot) (G : Guard) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  keyK S G [] A + (if rtStoreAt E G.rtI A.pc then (num A.a + 1) * 2 ^ 200 else 0)

def routeE (E : Env) (S : Spot) (G : Guard) (X : SG) (B0 : AS) : SG :=
  let B := normK S G B0
  let K := keyE E S G B
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

partial def runE (S : Spot) (G : Guard) (E : Env) (fin : AS → Bool) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preK S G cur).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !fin B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeE E S G X b
    break
  return X

partial def searchE (S : Spot) (G : Guard) (E : Env) (fin : AS → Bool) (W : List Watch) : SG := Id.run do
  let ops := (aRows E).toArray
  let mut X : SG := [startK G W false, startK G W true].foldl (routeE E S G) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runE S G E fin ops X A
  return X

/-- the table, from the search: every state that was reached more than once -/
def tableOfE (key : AS → Nat) (X : SG) : Array AS × Std.HashMap Nat (List Nat) × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat (List Nat) := {}
  let mut cut := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (key A) (t.size :: idx.getD (key A) [])
      cut := cut.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, cut)

def cfgOfE (S : Spot) (G : Guard) (E : Env) (fin : AS → Bool) (W : List Watch) : CfgE :=
  let q := tableOfE (keyE E S G) (searchE S G E fin W)
  { E, ops := (aRows E).toArray, S, G, fin, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key := keyE E S G }

/-- the fuel of a walk -/
def fuelE : Nat := 20000

/-- the end of a frame on the ROM -/
def finOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : AS → Bool :=
  finE (guardOf sy m0 d e).rtI sy.Eng_PlayerCtrl.toUInt8 (PipeEntryRule.vp sy) (kept sy d e) (atEntry d e) (FrameKeep.endOK (guardOf sy m0 d e)) (idleOK e)

/-- the table on the ROM -/
def cfgOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : CfgE :=
  cfgOfE spot (guardOf sy m0 d e) (PipeEntryRule.envOf m0) (finOf sy m0 d e) (kept sy d e)

/-- **The check of the frames.** The bytes and the guard's indices are in RAM, the player's routine is not the pipe's, the guard knows the player's routine when the frame starts,
the program is that of the entry's condition, and every walk of the table and of the two start states succeeds. -/
def keepCheck (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  let G := guardOf sy m0 d e
  let C := cfgOf sy m0 d e
  let W := kept sy d e
  decide (G.late < dotsPerFrame) && W.all (fun w => decide (w.1 < 2048)) && (atEntry d e).all (fun w => decide (w.1 < 2048)) &&
    sy.Eng_PlayerCtrl.toUInt8 != PipeEntryRule.vp sy && G.known.contains (G.rtI, sy.Eng_PlayerCtrl.toUInt8) &&
    decide ((PipeEntryRule.envOf m0).prg.data = (PipeChangeEnd.envOf d e).prg.data) && (PipeEntryRule.envOf m0).mask == (PipeChangeEnd.envOf d e).mask &&
    C.t.all (walkE C fuelE) && walkE C fuelE (startK G W false) && walkE C fuelE (startK G W true)

/-- **The check of frame 0**: the title's program is that of the frames from control; from each state of `TitleStart`'s near group, the frame ends with control and the speed 0,
with the kept bytes at their values, and in the idle loop as a frame in control starts (`FrameKeep.endOK`) -/
def nearCheck (sy : Syms) (m0 : Machine) (c : TitleStart.Ctx) (W : List Watch) : Bool :=
  decide (c.E.prg.data = (PipeEntryRule.envOf m0).prg.data) && c.E.mask == (PipeEntryRule.envOf m0).mask &&
    TitleStart.grpOK sy c (TitleStart.setsOf sy c).near (fun B => TitleStart.finNear sy B && watchOK W B && FrameKeep.endOK (PipeWrites.guardOf sy m0) B)

/-- **The check of the lists**: the names of `restNames` are known; the reference entry has the pipe's routine and lists it among the bytes of `Rest`; the masks are in RAM -/
def listCheck (sy : Syms) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  let rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat
  restNames.all (fun p => (d.nx.lookup p.1).isSome) && d.known.contains rtI && (restIdx d.nx).contains rtI && e.ram.get! rtI == PipeEntryRule.vp sy &&
    d.bits.all (fun b => decide (b.1 < 2048))

/-- what the checks on the ROM give -/
structure Checks (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (c : TitleStart.Ctx) : Prop where
  near : nearCheck sy m0 c (kept sy d (PipeTransition.entry m0)) = true
  keep : keepCheck sy m0 d (PipeTransition.entry m0) = true
  lists : listCheck sy d (PipeTransition.entry m0) = true

/-! ## The walk covers the frame -/

section
variable {C : CfgE} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveE (C : CfgE) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkE C n A = true

theorem cover_liveE (ht : C.t.all (walkE C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverE C B = true) :
    ∃ D, LiveE C F D m ∧ D.k = B.k := by
  unfold coverE at h
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

theorem live_stepE (ht : C.t.all (walkE C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveE C F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A', LiveE C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkE] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkE, List.all_eq_true] at hw
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
        · obtain ⟨D, hD, hk⟩ := cover_liveE ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, for every input, if each instruction meets `CleanK`: it ends in a state with `fin`. -/
theorem frame_of_walkE (ht : C.t.all (walkE C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkE C Fu S = true) (hs : Sim C.E F S m) (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveE C F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j)) := by
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
        rcases live_stepE ht hkl hops hT h1 (hk j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
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

/-! ## One frame from control -/

section
variable {sy : Syms} {m0 : Machine} {d : PipeChangeEnd.Data} {e : Machine}

/-- what the check of the frames says -/
structure KeepOK (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Prop where
  late : (guardOf sy m0 d e).late < dotsPerFrame
  ne : sy.Eng_PlayerCtrl.toUInt8 ≠ PipeEntryRule.vp sy
  known : ((guardOf sy m0 d e).rtI, sy.Eng_PlayerCtrl.toUInt8) ∈ (guardOf sy m0 d e).known
  prg : (PipeEntryRule.envOf m0).prg = (PipeChangeEnd.envOf d e).prg
  mask : (PipeEntryRule.envOf m0).mask = (PipeChangeEnd.envOf d e).mask
  table : (cfgOf sy m0 d e).t.all (walkE (cfgOf sy m0 d e) fuelE) = true
  s0 : walkE (cfgOf sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) false) = true
  s1 : walkE (cfgOf sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) true) = true

theorem keepOK_of_check (h : keepCheck sy m0 d e = true) : KeepOK sy m0 d e := by
  simp only [keepCheck, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, h5⟩, h9⟩, h10⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h4, h5, SideTransition.byteArray_eq h9, beq_iff_eq.1 h10, h6, h7, h8⟩

/-- `Clean` is `CleanK` with no store set apart -/
theorem cleanK_of {G : Guard} {m : Machine} (h : Clean G m) : CleanK G spot.store m :=
  ⟨fun t ht _ => h.store t ht, h.read, h.jump, h.time⟩

/-- a frame start of `PipeWrites` is one of this guard: the guards differ only in the bytes a store does not touch -/
theorem start_of {m : Machine} (h : FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) m) : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- the routine of a state with a known routine -/
theorem rt_of {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} {rtI : Nat} (hs : Sim E F B m) (h1 : rtI < 2048) (h2 : (B.getK rtI).isK = true) :
    m.ram.get! rtI = (B.getK rtI).v :=
  sim_known (p := (rtI, (B.getK rtI).v)) hs (by simp [knownIs, h1, h2])

/-- the top bit of a byte known by a mask -/
theorem top_of_mem {b : AB} {x : UInt8} (hk : b.k &&& 0x80 = 0x80) (hv : b.v &&& 0x80 = 0x80) (h : b.mem x) : x &&& 0x80 = 0x80 := by
  calc x &&& 0x80 = x &&& (b.k &&& 0x80) := by rw [hk]
    _ = (x &&& b.k) &&& 0x80 := by rw [UInt8.and_assoc]
    _ = (b.v &&& b.k) &&& 0x80 := by rw [show x &&& b.k = b.v &&& b.k from h]
    _ = b.v &&& (b.k &&& 0x80) := by rw [UInt8.and_assoc]
    _ = b.v &&& 0x80 := by rw [hk]
    _ = 0x80 := hv

/-- a frame's end that `idleOK` accepts is in the idle loop as `IdleAt` asks -/
theorem idle_of {F : Nat × UInt8} {B : AS} {m : Machine} (hC : KeepOK sy m0 d e) (hs : Sim (PipeEntryRule.envOf m0) F B m) (h : idleOK e B = true) :
    IdleAt (PipeChangeEnd.envOf d e) e m := by
  simp only [idleOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hd : m.fdot ≤ 9 := Nat.le_trans hs.hi h1
  refine ⟨by omega, ?_, ?_, top_of_mem h3 h4 hs.ppuCtrl, hs.strobe.trans h5, hs.halted, hs.trk, hs.prg.trans hC.prg, hs.mask.trans hC.mask, hs.size, hs.pc.trans h6,
    hs.s.trans h7⟩
  · rcases h2 with ⟨⟨a1, a2⟩, a3⟩ | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl ⟨by have := hs.hi; omega, hs.vb.trans a1, hs.nmi.trans a2⟩
    · exact Or.inr ⟨Nat.le_trans a3 hs.lo, hs.vb.trans a1, hs.nmi.trans a2⟩
  · rw [hs.s0]
    simp only [s0f, Bool.or_eq_true, decide_eq_true_eq]
    left
    have : (9 : Nat) < dotVblClr := by decide
    omega

/-- **The walk of one frame from control**: a frame that starts in the idle loop in control with the kept bytes at their values, and whose every instruction is `Clean` for
the guard, ends in a state that `finOf` accepts -/
theorem fin_frame (hc : keepCheck sy m0 d e = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) (hw : Watched (kept sy d e) m)
    (hk : ∀ j, Clean (guardOf sy m0 d e) (trace m i j)) :
    ∃ B, finOf sy m0 d e B = true ∧ Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (frame m i) := by
  have hC := keepOK_of_check hc
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (W := kept sy d e) rfl h0 hw
  have hw0 : walkE (cfgOf sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) b) = true := by
    cases b with
    | false => exact hC.s0
    | true => exact hC.s1
  obtain ⟨_, B, h1, _, h2⟩ := frame_of_walkE (C := cfgOf sy m0 d e) (F := (m.frame, 2)) hC.table rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) rfl hw0 hs
    (fun j => cleanK_of (hk j))
  exact ⟨B, h1, h2⟩

/-- **One frame from control.** A frame that starts in the idle loop in control with the kept bytes at their values, and whose every instruction is `Clean` for the guard, ends with the
kept bytes at their values if it ends with the player's routine, and with the bytes `atEntry` at their values if it ends with the pipe's. -/
theorem keep_frame (hc : keepCheck sy m0 d e = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) (hw : Watched (kept sy d e) m)
    (hk : ∀ j, Clean (guardOf sy m0 d e) (trace m i j)) :
    ((frame m i).ram.get! (guardOf sy m0 d e).rtI = sy.Eng_PlayerCtrl.toUInt8 → Watched (kept sy d e) (frame m i)) ∧
    ((frame m i).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy → Watched (atEntry d e) (frame m i) ∧ IdleAt (PipeChangeEnd.envOf d e) e (frame m i)) := by
  have hC := keepOK_of_check hc
  obtain ⟨B, h1, h2⟩ := fin_frame hc h0 hw hk
  have hf : finOf sy m0 d e B = true := h1
  simp only [finOf, finE, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hf
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hf
  have er := rt_of h2 a1 a2
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rcases a3 with a3 | ⟨a3, _⟩
    · exact absurd (er.symm.trans hr) a3
    · exact FrameKeep.watched_of a3 h2
  · rcases a4 with a4 | ⟨a4, a5⟩
    · exact absurd (er.symm.trans hr) a4
    · exact ⟨FrameKeep.watched_of a4 h2, idle_of hC h2 a5⟩

/-- **One frame from control that ends in control ends at the start of a frame in control** (`FrameStart`), with the kept bytes at their values: the walk gives the idle loop,
and control gives the routine, the mode and the task -/
theorem keep_start (hc : keepCheck sy m0 d e = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) (hw : Watched (kept sy d e) m)
    (hk : ∀ j, Clean (guardOf sy m0 d e) (trace m i j)) (hr : controllable sy (frame m i) = true) :
    FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) (frame m i) ∧ Watched (kept sy d e) (frame m i) := by
  obtain ⟨B, h1, h2⟩ := fin_frame hc h0 hw hk
  have hf : finOf sy m0 d e B = true := h1
  simp only [finOf, finE, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hf
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, _⟩ := hf
  have er := rt_of h2 a1 a2
  have hkn : ∀ p ∈ (guardOf sy m0 d e).known, (frame m i).ram.get! p.1 = p.2 := FrameKeep.known_of_ctl (m0 := m0) hr
  have hrt : (frame m i).ram.get! (guardOf sy m0 d e).rtI = sy.Eng_PlayerCtrl.toUInt8 := hkn _ (keepOK_of_check hc).known
  rcases a3 with a3 | ⟨a3, a5⟩
  · exact absurd (er.symm.trans hrt) a3
  · exact ⟨FrameKeep.start_of_sim h2 a5 rfl rfl hkn, FrameKeep.watched_of a3 h2⟩

/-- a frame start of this guard is one of `PipeWrites`: the guards differ only in the bytes a store does not touch -/
theorem start_to {m : Machine} (h : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) : FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

end

/-! ## Frame 0 -/

section
variable {sy : Syms} {c : TitleStart.Ctx} {t0 : Nat} {seq : Nat → Machine} {inp : Nat → UInt8}

/-- **Frame 1 starts in the idle loop in control, with the bytes `W` at their values**: frame 0 begins in a near state of `TitleStart` (from the press of Start, `Begin`), and the
walk of its frame ends with them, in the idle loop as `FrameStart` asks. Control at frame 1 gives the routine, the mode and the task. -/
theorem Begin.start {m0 : Machine} {W : List Watch} (hB : TitleStart.check sy c t0 = true) (hN : nearCheck sy m0 c W = true) (B : TitleStart.Begin sy c seq inp)
    (hn : seq 1 = frame (seq 0) (inp 0)) : FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq 1) ∧ Watched W (seq 1) := by
  have P : TitleStart.Parts sy c t0 (TitleStart.setsOf sy c) := TitleStart.parts_of_check hB
  obtain ⟨⟨S, hS, hs⟩, _⟩ := B.near P hn
  have hi : TitleStart.inCore sy (seq 0) = true → SideChangeEnd.noStart (inp 0) = true := by
    intro h
    have := B.noPause B.pre (Nat.le_refl _)
    rw [B.atZero.1, B.atZero.2] at this
    exact this h
  unfold nearCheck at hN
  rw [Bool.and_eq_true, Bool.and_eq_true] at hN
  obtain ⟨⟨hp, hm⟩, hN'⟩ := hN
  obtain ⟨B', h1, h2⟩ := TitleStart.grp_frame hN' hS hs (TitleStart.grp_pad hN' hS hs hi)
  simp only [Bool.and_eq_true] at h1
  have hk : ∀ p ∈ (PipeWrites.guardOf sy m0).known, (seq 1).ram.get! p.1 = p.2 := FrameKeep.known_of_ctl (m0 := m0) B.ctl
  rw [hn] at hk ⊢
  exact ⟨FrameKeep.start_of_sim h2 h1.2 (SideTransition.byteArray_eq (of_decide_eq_true hp)) (beq_iff_eq.1 hm) hk, FrameKeep.watched_of h1.1.2 h2⟩

/-- **The machine at control has the bytes `W` at their values**: frame 0 begins in a near state of `TitleStart` (from the press of Start, `Begin`), and the walk of its frame ends
with them -/
theorem Begin.watched {m0 : Machine} {W : List Watch} (hB : TitleStart.check sy c t0 = true) (hN : nearCheck sy m0 c W = true) (B : TitleStart.Begin sy c seq inp)
    (hn : seq 1 = frame (seq 0) (inp 0)) : Watched W (seq 1) :=
  (Begin.start hB hN B hn).2

end

/-! ## From control to the entry -/

section
variable {sy : Syms} {m0 : Machine} {d : PipeChangeEnd.Data} {e : Machine} {seq : Nat → Machine} {inp : Nat → UInt8}

/-- **Every frame from control keeps the kept bytes**, up to the entry: frame `n`, for `1 ≤ n < a`, starts in control and its instructions are `Clean` -/
theorem watched_up (hc : keepCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat}
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1 : Watched (kept sy d e) (seq 1)) : ∀ n, 1 ≤ n → n < a → Watched (kept sy d e) (seq n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro ha hb
    by_cases hk : k = 0
    · subst hk
      exact h1
    · have hw := ih (by omega) (by omega)
      have hf := keep_frame hc (start_of (start k (by omega) (by omega))) hw (clean k (by omega) (by omega))
      have hs := (start (k + 1) ha hb).known _ (keepOK_of_check hc).known
      rw [next k] at hs ⊢
      exact hf.1 hs

/-- **The bytes `atEntry` at the entry, in the idle loop**: the frame before `a` ends with the pipe's routine -/
theorem watched_entry (hc : keepCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat} (ha : 2 ≤ a)
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1 : Watched (kept sy d e) (seq 1)) (hr : (seq a).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy) :
    Watched (atEntry d e) (seq a) ∧ IdleAt (PipeChangeEnd.envOf d e) e (seq a) := by
  have hw := watched_up hc next start clean h1 (a - 1) (by omega) (by omega)
  have hf := keep_frame hc (start_of (start (a - 1) (by omega) (by omega))) hw (clean (a - 1) (by omega) (by omega))
  have e1 : seq a = frame (seq (a - 1)) (inp (a - 1)) := by
    have := next (a - 1)
    rwa [Nat.sub_add_cancel (by omega)] at this
  rw [e1] at hr ⊢
  exact hf.2 hr

/-- **The condition at the entry**, from the idle loop, the bytes `atEntry` and `Rest` -/
theorem entry_of_rest (hl : listCheck sy d e = true) {m : Machine} (hi1 : IdleAt (PipeChangeEnd.envOf d e) e m) (hw : Watched (atEntry d e) m) (hr : Rest d e m) :
    PipeChangeEnd.Entry d e m := by
  obtain ⟨hb, ht, h2⟩ := hr
  simp only [listCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hl
  have hbits := hl.2
  refine ⟨⟨hi1.dot, hi1.flags, hi1.s0, hi1.ctrl, hi1.strobe, hi1.halted, hi1.trk, hi1.prg, hi1.mask, hi1.size, ⟨(e, d.known), List.mem_singleton.2 rfl, hi1.pc, hi1.s, fun i hi => ?_⟩,
    ht⟩, fun b hb' => ?_⟩
  · by_cases hR : (restIdx d.nx).contains i = true
    · exact hb i hi (by simpa using hR)
    · have hm : (i, (0xFF : UInt8), e.ram.get! i) ∈ atEntry d e :=
        List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_map.2 ⟨i, hi, rfl⟩), by simpa using hR⟩
      have h3 := hw _ hm
      simp only [FrameKeep.and_ff] at h3
      exact h3
  · by_cases hR : (restIdx d.nx).contains b.1 = true
    · exact h2 b (List.mem_filter.2 ⟨hb', hR⟩)
    · have hm : (b.1, b.2, e.ram.get! b.1) ∈ atEntry d e :=
        List.mem_filter.2 ⟨List.mem_append_right _ (List.mem_map.2 ⟨b, hb', rfl⟩), by simpa using hR⟩
      exact ⟨hbits b hb', hw _ hm⟩

theorem u8_of_u16 {x : UInt8} {y : UInt16} (h : x.toUInt16 = y) : x = y.toUInt8 := by
  subst h
  simp

/-- **Each frame from control to the entry starts in the idle loop in control**, with the kept bytes at their values: by induction from frame 1. Frame `n`, for `1 ≤ n < a`,
has `Clean` instructions, and its machine has control when it begins. -/
theorem start_up (hc : keepCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat}
    (stay : ∀ n, 1 ≤ n → n < a → controllable sy (seq n) = true)
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1s : FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq 1)) (h1 : Watched (kept sy d e) (seq 1)) :
    ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n) ∧ Watched (kept sy d e) (seq n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro ha hb
    by_cases hk : k = 0
    · subst hk
      exact ⟨h1s, h1⟩
    · obtain ⟨s1, w1⟩ := ih (by omega) (by omega)
      have hr := stay (k + 1) ha hb
      rw [next k] at hr ⊢
      obtain ⟨s2, w2⟩ := keep_start hc (start_of s1) w1 (clean k (by omega) (by omega)) hr
      exact ⟨start_to s2, w2⟩

/-- **Each frame from control to the entry starts in the idle loop in control** (`FrameStart`), from the press of Start on the title: frame `n`, for `1 ≤ n < a`, has `Clean`
instructions, and its machine has control when it begins. -/
theorem starts_of_title {c : TitleStart.Ctx} {t0 : Nat} (hB : TitleStart.check sy c t0 = true) (hK : Checks sy m0 d c)
    (T : TitleStart.Begin sy c seq inp) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat}
    (stay : ∀ n, 1 ≤ n → n < a → controllable sy (seq n) = true)
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d (PipeTransition.entry m0)) (trace (seq n) (inp n) j)) :
    ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n) := by
  have h1 := Begin.start hB hK.near T (next 0)
  exact fun n ha hb => (start_up hK.keep next stay clean h1.1 h1.2 n ha hb).1

/-- **The condition at the entry, from the press of Start on the title.** Frame 0 begins as `Begin` says; each frame from control to the entry starts in control and its instructions
are `Clean` for the guard; at the entry `Rest` holds. Then `Entry` holds. -/
theorem entry_of_title {c : TitleStart.Ctx} {t0 : Nat} (hB : TitleStart.check sy c t0 = true) (hK : Checks sy m0 d c)
    (T : TitleStart.Begin sy c seq inp) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat} (ha : 1 ≤ a)
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d (PipeTransition.entry m0)) (trace (seq n) (inp n) j))
    (rest : Rest d (PipeTransition.entry m0) (seq a)) : PipeChangeEnd.Entry d (PipeTransition.entry m0) (seq a) := by
  have hl := hK.lists
  have hC := keepOK_of_check hK.keep
  have hr : (seq a).ram.get! (guardOf sy m0 d (PipeTransition.entry m0)).rtI = PipeEntryRule.vp sy := by
    simp only [listCheck, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hl
    obtain ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, _⟩ := hl
    exact (rest.1 _ h2 h3).trans h4
  have h1 := Begin.watched hB hK.near T (next 0)
  by_cases h2 : 2 ≤ a
  · have hw := watched_entry hK.keep next h2 start clean h1 hr
    exact entry_of_rest hl hw.2 hw.1 rest
  · exfalso
    have e1 : a = 1 := by omega
    subst e1
    have hc := T.ctl
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    have e2 : peek (seq 1) sy.GameEngineSubroutine = PipeEntryRule.vp sy := hr
    rw [e2] at hc
    exact hC.ne (u8_of_u16 hc.2).symm

end

/-! ## For a program -/

/-- `Rest` as a check, for a program -/
def restOK (d : PipeChangeEnd.Data) (e m : Machine) : Bool :=
  (d.known.all fun i => !(restIdx d.nx).contains i || m.ram.get! i == e.ram.get! i) && decide (PipeChangeEnd.timerF ≤ (m.ram.get! (PipeChangeEnd.envOf d e).rkI).toNat) &&
    (d.bits.filter fun b => (restIdx d.nx).contains b.1).all fun b => decide (b.1 < 2048) && (m.ram.get! b.1 &&& b.2) == (e.ram.get! b.1 &&& b.2)

/-- `IdleAt` as a check, for a program -/
def idleB (E : Env) (e m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
    m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
    m.pc == e.pc && m.s == e.s

end Smbrta.EntryKeep
