import Theorems.TitleStart
import Theorems.FrameKeep
import Theorems.CtrlKeep
import Theorems.PipeChangeEnd

/-!
# The state at the vertical pipe's entry, from the press of Start on the title

`PipeChangeEnd.Entry` is the condition on the state at the end of the frame that enters the vertical pipe: the frame has ended in the idle loop, and some bytes have the values of
the reference entry, some of them under a mask. Here most of these bytes are proved from the press of Start on the title (`TitleStart.Begin`), and from the frames from control to
the entry:

* frame 0 (the frame before control) begins in a state of `TitleStart`'s set. A walk of that frame shows that it ends with the kept bytes (`kept`) at the entry's values (`nearCheck`);
* each frame from control to the entry starts in the idle loop in control (`PipeWrites.FrameStart`), and each of its instructions meets `PipeWrites.Clean` with the bytes of `held` (the kept
  bytes and those of `endNames`) among the bytes that a store through an index or a pointer does not touch (`guardOf`). A walk of one whole frame (as in `FrameKeep`, with every byte not known but the kept ones) shows that such
  a frame ends with the kept bytes at their values when the routine at its end is the player's, and with the bytes `atEntry` at the entry's values when it is the pipe's (`keepCheck`).

The frame of the entry ends in the idle loop (`IdleAt`) with the pipe's timer at least its first value (`timerOK`): the walk shows this too. The bytes of `endNames` are not kept,
but the walk of the entry frame knows them at its end. What stays assumed at the entry is `Rest`: the condition of `Entry` on the bytes of `restNames` only. The bytes of
`restNames` are those that change on the way on real runs; those that frame 0 does not know; those that a frame may write when nothing on the screen is known (a new object, the
music of an event, a new area, a warp pipe); and those that real frames store to through an index. The walks of the pipe's frames need each of them
(`PipeChangeEnd.entryDropped` lists the bytes that left `Entry` in round 12, because they do not).

Round 15: the level's number (`AreaNumber`) is a byte of `Entry` (`PipeChangeEnd.entryNames`) and not of `restNames`, so it is one of the kept bytes: the condition at
the press on the title knows it (`TitleStart.areaNames`), frame 0 ends with it, the walk of a frame from control does not store to it, and the guard protects it from the
stores through an index or a pointer. With it `Route.Run.area₁` is a theorem. The checks (`Checks`) also have the check of the store of the move routine (`qCheck`), so
that the condition on the frames' instructions is a plain `CleanK` of the union guard of `UpClean`.

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

/-- **The bytes of the condition at the entry that are not proved here**: a name, an offset, a number of bytes. Each byte was measured alone. The walks of the pipe's frames
need each of them (with the byte not known at the entry, `PipeChangeEnd.zcheck` and `pcheck` fail, or for the two music queues the search does not end in 10 minutes:
`entry-need`), except the first square's effect queue, which is now removed from Entry: the larger pipe-frame tables are accepted. Each fails one of these:
* another value on some real frame from control to the entry: the routine, the enemies' page select, the states and flags of blocks 0 and 1, misc object 8's state, scores 0 to 2,
  the states of enemy slots 0 to 2, the flag and the kind of enemy slot 5 (the power-up's);
* not known at frame 0 (no near state of `TitleStart` knows them): the saved song;
* written by the walk of a frame that ends with the player's routine, since it knows nothing of the objects, the area's data or the sound: the flag of enemy slot 4, the music
  and the noise, the vine's flag offset, the frenzy, the warp zone, the next area (2), the star, the world;
* stored through an index on real frames: the kinds of enemy slots 0 to 2, score 5.
The pause byte's bits 1 to 6 left in round 11: the near states of `TitleStart` know the pause byte, and the frames keep these bits. In round 12 the 19 bytes of
`PipeChangeEnd.entryDropped` left: the pipe's frames do not need them, so `Entry` no longer asks them. -/
def restNames : List (String × Nat × Nat) :=
  [("GameEngineSubroutine", 0, 1), ("EnemyObjectPageSel", 0, 1), ("AreaMusicBuffer_Alt", 0, 1),
   ("Block_State", 0, 2), ("Block_RepFlag", 0, 2), ("Misc_State", 8, 1), ("FloateyNum_Control", 0, 3), ("FloateyNum_Control", 5, 1),
   ("Enemy_State", 0, 3),
   ("Enemy_Flag", 4, 2), ("Enemy_ID", 0, 3), ("Enemy_ID", 5, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1),
   ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("VineFlagOffset", 0, 1),
   ("EnemyFrenzyBuffer", 0, 1), ("EnemyFrenzyQueue", 0, 1), ("WarpZoneControl", 0, 1), ("AreaPointer", 0, 1), ("EntrancePage", 0, 1),
   ("StarInvincibleTimer", 0, 1), ("WorldNumber", 0, 1)]

/-- these bytes as RAM indices -/
def restIdx (nx : Names) : List Nat := SideChangeBound.bytesOf nx restNames

/-- **the bytes proved at the entry that the frames do not keep**: the frame of the entry writes them, whatever they were when it began (the buttons left and right) -/
def endNames : List (String × Nat × Nat) := [("Left_Right_Buttons", 0, 1)]

/-- these bytes as RAM indices -/
def endIdx (nx : Names) : List Nat := SideChangeBound.bytesOf nx endNames

/-- every byte of the condition at the entry: its index, the bits it asks, the values of the reference entry -/
def entryW (d : PipeChangeEnd.Data) (e : Machine) : List Watch :=
  d.known.map (fun i => (i, (0xFF : UInt8), e.ram.get! i)) ++ d.bits.map (fun b => (b.1, b.2, e.ram.get! b.1))

/-- **the bytes proved at the entry**: all but those of `restNames` -/
def atEntry (d : PipeChangeEnd.Data) (e : Machine) : List Watch := (entryW d e).filter fun w => !(restIdx d.nx).contains w.1

/-- the mode and the task: each frame's start in control gives them -/
def ctlIdx (sy : Syms) : List Nat := [(sy.OperMode &&& 0x7FF).toNat, (sy.OperMode_Task &&& 0x7FF).toNat]

/-- the bytes of `atEntry` but the mode and the task: a store with a target not known does not touch them -/
def held (sy : Syms) (d : PipeChangeEnd.Data) (e : Machine) : List Watch := (atEntry d e).filter fun w => !(ctlIdx sy).contains w.1

/-- **the bytes the frames keep** from control to the entry: those of `atEntry` but the mode and the task, and but those of `endNames` -/
def kept (sy : Syms) (d : PipeChangeEnd.Data) (e : Machine) : List Watch := (held sy d e).filter fun w => !(endIdx d.nx).contains w.1

/-- **The condition at the entry that stays assumed**: the bytes of `restNames` that `Entry` asks have the reference's values (all bits, or the bits of the mask). The pipe's
timer is no longer assumed: the walk of the entry frame gives it. -/
abbrev Rest (d : PipeChangeEnd.Data) (e : Machine) (m : Machine) : Prop :=
  (∀ i ∈ d.known, i ∈ restIdx d.nx → m.ram.get! i = e.ram.get! i) ∧ PipeChangeEnd.BitsAt (d.bits.filter fun b => (restIdx d.nx).contains b.1) e m

/-- the pipe's timer as a RAM index -/
def timerI (d : PipeChangeEnd.Data) (e : Machine) : Nat := (PipeChangeEnd.envOf d e).rkI

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

/-- the six bytes of the pause: the queue, the buffer, the flag and the counter of the pause sound, the pause timer, the pause byte -/
def pauseSix (d : PipeChangeEnd.Data) : List Nat :=
  let ix := PipeChangeEnd.pauseIx d.nx
  [ix.q, ix.b, ix.f, ix.c, PipeChangeEnd.pauseTI d, PipeChangeEnd.pauseI d]

/-- **The guard** of the frames from control to the entry: that of `PipeWrites`, with the kept bytes, those of `endNames`, the pipe's timer and the six bytes of the pause
among the bytes that a store with a target not known does not touch -/
def guardOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Guard :=
  let G := PipeWrites.guardOf sy m0
  { G with prot := (held sy d e).map (·.1) ++ timerI d e :: pauseSix d ++ G.prot }

/-- no store of the move routine is set apart -/
def spot : Spot := { entry := 0, store := 0, temps := [] }

/-! ## The store of the move routine

The move routine stores the fraction of the player's position with `STA abs,X`, the index 0 for the player. A store through an index is asked to miss the guard's bytes
(`PipeWrites.Clean`), but the fraction is not one of them. `qCheck` reads this from the ROM. With it the one condition on the frames from control to the entry
(`Route.ChangesBase.upCleanU`, `CleanK` of the union guard of `UpClean`, which sets this store apart) gives `Clean` of this file's guard (`UpClean.cleanE₁_of_U`). -/

/-- the store of the move routine (`FrameKeep.spotOf`) -/
abbrev qOf (sy : Syms) (m0 : Machine) : UInt16 := (FrameKeep.spotOf sy m0).store

/-- the operand of the instruction at `q`: with `STA abs,X` and the index 0, its target -/
def tq (sy : Syms) (m0 : Machine) : UInt16 :=
  (romByte m0 (qOf sy m0 + 1)).toUInt16 ||| ((romByte m0 (qOf sy m0 + 2)).toUInt16 <<< 8)

/-- **The check of the store of the move routine**: the instruction at `q` is `STA abs,X` (opcode 157) in the program's part of memory, its target with the index 0 is a
byte of RAM, the guard does not protect it, and it is not the pause byte that the NMI tests (`CtrlKeep.pauseI`) -/
def qCheck (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  romByte m0 (qOf sy m0) == 0x9D && decide (0x8000 ≤ qOf sy m0) && decide (0x8000 ≤ qOf sy m0 + 1) && decide (0x8000 ≤ qOf sy m0 + 2) &&
    decide (tq sy m0 < 0x2000) && !((guardOf sy m0 d e).prot.contains (tq sy m0 &&& 0x7FF).toNat) &&
    (tq sy m0 &&& 0x7FF).toNat != CtrlKeep.pauseI sy m0

/-! ## The walk of one frame -/

/-- **The frame's end**: the routine is known; if it is the player's, the bytes `W` are known with their values, and `y` (on the ROM: the idle loop as a frame in control
starts, `FrameKeep.endOK`); if it is the pipe's, the bytes `W₃`, and `x` -/
def finE (rtI : Nat) (ctl vp : UInt8) (W W₃ : List Watch) (y x : AS → Bool) (B : AS) : Bool :=
  decide (rtI < 2048) && (B.getK rtI).isK && ((B.getK rtI).v != ctl || (watchOK W B && y B)) && ((B.getK rtI).v != vp || (watchOK W₃ B && x B))

/-- the state is at a frame's start in the idle loop, as `IdleAt` asks: the dots, the flags, the control register's top bit, the strobe, the program counter and the stack of `e` -/
def idleOK (e : Machine) (B : AS) : Bool :=
  decide (B.hi ≤ 9) && ((!B.vb && !B.nmi && B.hi == 0) || (B.vb && B.nmi && decide (1 ≤ B.lo))) && B.ppuCtrl.k &&& 0x80 == 0x80 && B.ppuCtrl.v &&& 0x80 == 0x80 &&
    !B.strobe && B.pc == e.pc && B.s == e.s

/-- the pipe's timer is at least its first value: the bits known of it, with the others 0, make at least that value -/
def timerOK (tI : Nat) (B : AS) : Bool :=
  decide (tI < 2048) && decide (PipeChangeEnd.timerF ≤ ((B.getK tI).v &&& (B.getK tI).k).toNat)

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

/-- the search keeps `Y` apart where a table is about to be read by `Y` (`LDA abs,Y`) and stored as the pipe's timer: the side pipe's code picks one of two values -/
def tmrReadAt (E : Env) (tI : Nat) (pc : UInt16) : Bool :=
  let op := fun (a : UInt16) => E.prg.get! (a &&& E.mask).toNat
  op pc == 0xB9 && ((op (pc + 3) == 0x85 && (op (pc + 4)).toNat == tI) || (op (pc + 3) == 0x8D && (op (pc + 4)).toNat + 256 * (op (pc + 5)).toNat == tI))

/-- the key of the search: that of `FrameKeep` with no watched byte, `A` where it is about to be stored as the routine, what is known of the pipe's timer when the routine is known
to be the pipe's, and `Y` where a table is about to be read for the timer -/
def keyE (E : Env) (S : Spot) (G : Guard) (tI : Nat) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let r := A.getK G.rtI
  keyK S G [] A + (if rtStoreAt E G.rtI A.pc then (num A.a + 1) * 2 ^ 200 else 0) + (if r.k == 0xFF && r.v == G.ev then (num (A.getK tI) + 1) * 2 ^ 220 else 0) +
    (if tmrReadAt E tI A.pc then (num A.y + 1) * 2 ^ 240 else 0)

def routeE (E : Env) (S : Spot) (G : Guard) (tI : Nat) (X : SG) (B0 : AS) : SG :=
  let B := normK S G B0
  let K := keyE E S G tI B
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

partial def runE (S : Spot) (G : Guard) (E : Env) (tI : Nat) (fin : AS → Bool) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
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
      X := routeE E S G tI X b
    break
  return X

partial def searchE (S : Spot) (G : Guard) (E : Env) (tI : Nat) (fin : AS → Bool) (W : List Watch) : SG := Id.run do
  let ops := (aRows E).toArray
  let mut X : SG := [startK G W false, startK G W true].foldl (routeE E S G tI) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runE S G E tI fin ops X A
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

def cfgOfE (S : Spot) (G : Guard) (E : Env) (tI : Nat) (fin : AS → Bool) (W : List Watch) : CfgE :=
  let q := tableOfE (keyE E S G tI) (searchE S G E tI fin W)
  { E, ops := (aRows E).toArray, S, G, fin, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key := keyE E S G tI }

/-- the fuel of a walk -/
def fuelE : Nat := 20000

/-- the end of a frame on the ROM: at the pipe's routine also the pipe's timer -/
def finOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : AS → Bool :=
  finE (guardOf sy m0 d e).rtI sy.Eng_PlayerCtrl.toUInt8 (PipeEntryRule.vp sy) (kept sy d e) (atEntry d e) (FrameKeep.endOK (guardOf sy m0 d e))
    (fun B => idleOK e B && timerOK (timerI d e) B)

/-- the table on the ROM -/
def cfgOf (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : CfgE :=
  cfgOfE spot (guardOf sy m0 d e) (PipeEntryRule.envOf m0) (timerI d e) (finOf sy m0 d e) (kept sy d e)

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
    TitleStart.frame0Check sy c (fun B => TitleStart.finNear sy B && watchOK W B && FrameKeep.endOK (PipeWrites.guardOf sy m0) B)

/-- **The check of the lists**: the names of `restNames` and `endNames` are known; the reference entry has the pipe's routine and lists it among the bytes of `Rest`; the masks are in RAM -/
def listCheck (sy : Syms) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  let rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat
  (restNames ++ endNames).all (fun p => (d.nx.lookup p.1).isSome) && d.known.contains rtI && (restIdx d.nx).contains rtI && e.ram.get! rtI == PipeEntryRule.vp sy &&
    d.bits.all (fun b => decide (b.1 < 2048))

/-! ## The pause, with the class beside the walk

Start may be pressed on the frames from control to the entry. The six bytes of the pause (`pauseSix`) are then in one of the 88 classes of `PipeChangeEnd.classesV`
at each frame's end. The walk above knows none of them, so the class is carried beside it, as `PipeChangeEnd.pwalk` carries it beside the walk of the pipe's frames:
from the call of the sound routine in the frame's interrupt to the return after the pause routine (`PipeChangeEnd.inR`) the walk knows the six bytes, split by the
classes at the call; at the return they must be in a class and are forgotten, but for bits 0 to 6 of the pause byte. Outside, a step must keep them: its store does not
reach them (`StepWrites.keepOK`), or, for each class that agrees with the state, the step of the state with the class's bytes still knows them (`outOK`). The second
case is a store through an index or a pointer: it forgets every byte but the guard's, and the six bytes are in the guard. -/

open PipeChangeEnd (PR inR pret classesV)
open StepWrites (SState SIn soundLe)

/-- a step outside the routine keeps the six bytes: the store does not reach them, or for each class that agrees with the state, every step of the state with the bytes
of the class knows them as the class says -/
def outOK (S : Spot) (G : Guard) (E : Env) (ops : Array (AM Unit)) (R : PR) (T : List SState) (A : AS) : Bool :=
  StepWrites.keepOK E (fun i => R.SB.contains i) A ||
    T.all fun t => !StepWrites.agrees t A || (kstep S G E ops (StepWrites.refineAll t A)).all fun o =>
      match o with
      | some B => soundLe B t
      | none => false

/-- **The step with the class beside the walk.** In the routine: the step of the walk, and at the return the check and the forgetting of `PipeChangeEnd.pret`; at the
call of the pause routine the state is split by bit 7 of the pause byte. At the first call: one piece for each class that agrees with the state. Elsewhere: the step,
which must keep the six bytes (`outOK`). -/
def vsuccs (S : Spot) (G : Guard) (E : Env) (ops : Array (AM Unit)) (R : PR) (T : List SState) (A : AS) : List (Option AS) :=
  if inR R A then
    (if A.pc == R.call + 6 then TaintRun.splitBit R.g 0x80 A else [A]).flatMap fun A' =>
      (preK S G A').flatMap fun A₁ => (kstep S G E ops A₁).map fun o => o.bind (pret R T A₁)
  else if A.pc == R.call then
    if StepWrites.keepOK E (fun i => R.SB.contains i) A then
      T.flatMap fun t => if StepWrites.agrees t A then (preK S G (StepWrites.refineAll t A)).flatMap (kstep S G E ops) else []
    else [none]
  else (preK S G A).flatMap fun A₁ => (kstep S G E ops A₁).map fun o => o.bind fun B => if outOK S G E ops R T A₁ then some B else none

/-- the table has a state that covers `B`, both in the routine or both outside -/
def coverV (C : CfgE) (R : PR) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l && inR R B == inR R D
    | _, _ => false

/-- `walkE` with `vsuccs`; the frame's end is outside the routine and meets `fin` -/
def walkV (C : CfgE) (R : PR) (T : List SState) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (vsuccs C.S C.G C.E C.ops R T A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverV C R B) || walkV C R T fin n B
      else B.k == A.k + 1 && fin B && !inR R B

/-! ### The search for the table with the class beside the walk: no part of the proof -/

/-- the key: that of `keyE`, what the state knows of the pause byte, and in the routine what it knows of the six bytes -/
def keyV (E : Env) (S : Spot) (G : Guard) (tI : Nat) (R : PR) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  keyE E S G tI A + (num (A.getK R.g) + 1) * 2 ^ 260 +
    (if inR R A then (R.SB.foldl (fun n i => n * 65536 + num (A.getK i)) 1) * 2 ^ 280 else 0)

/-- `routeE` with the key `keyV` -/
def routeV (E : Env) (S : Spot) (G : Guard) (tI : Nat) (R : PR) (X : SG) (B0 : AS) : SG :=
  let B := normK S G B0
  let K := keyV E S G tI R B
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

/-- `runE` with `vsuccs` -/
partial def runV (S : Spot) (G : Guard) (E : Env) (tI : Nat) (R : PR) (T : List SState) (fin : AS → Bool) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := vsuccs S G E ops R T cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && (!fin B || inR R B)
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && inR R b == inR R cur &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeV E S G tI R X b
    break
  return X

/-- the search from the two start states -/
partial def searchV (S : Spot) (G : Guard) (E : Env) (tI : Nat) (R : PR) (T : List SState) (fin : AS → Bool) (W : List Watch) : SG := Id.run do
  let ops := (aRows E).toArray
  let mut X : SG := [startK G W false, startK G W true].foldl (routeV E S G tI R) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runV S G E tI R T fin ops X A
  return X

/-- at the frame's end: as `finOf`, and if the routine is the pipe's, the state knows that the game is not paused -/
def finV (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) (B : AS) : Bool :=
  finOf sy m0 d e B && ((B.getK (guardOf sy m0 d e).rtI).v != PipeEntryRule.vp sy || PipeChangeEnd.notPausedK (PipeChangeEnd.pauseI d) B)

/-- the table with the class beside the walk, on the ROM -/
def cfgV (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : CfgE :=
  let G := guardOf sy m0 d e
  let E := PipeEntryRule.envOf m0
  let R := PipeChangeEnd.prOf sy d e
  let key := keyV E spot G (timerI d e) R
  let q := tableOfE key (searchV spot G E (timerI d e) R (classesV sy d) (finV sy m0 d e) (kept sy d e))
  { E, ops := (aRows E).toArray, S := spot, G, fin := finV sy m0 d e, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key }

/-- **The check of the frames with the class beside the walk.** The pause byte is in RAM, the classes name only the six bytes, the length of the pause sound is below
255, the start states are outside the routine, and every walk of the table and of the two start states succeeds. -/
def pauseCheck (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  let G := guardOf sy m0 d e
  let R := PipeChangeEnd.prOf sy d e
  let T := classesV sy d
  let C := cfgV sy m0 d e
  let W := kept sy d e
  let fin := finV sy m0 d e
  decide (R.g < 2048) && StepWrites.tabOK R.SB T && decide (sy.PauseSfxLength.toNat + 1 < 256) && !inR R (startK G W false) && !inR R (startK G W true) &&
    C.t.all (walkV C R T fin fuelE) && walkV C R T fin fuelE (startK G W false) && walkV C R T fin fuelE (startK G W true)

/-- **The check of frame 0 for the pause**: from each near or held state of `TitleStart`, any input, each end of frame 0 with control knows the six bytes as one of
the classes says -/
def nearPauseCheck (sy : Syms) (c : TitleStart.Ctx) (d : PipeChangeEnd.Data) : Bool :=
  TitleStart.frame0Check sy c (fun B => (classesV sy d).any (soundLe B))

/-- what the checks on the ROM give -/
structure Checks (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (c : TitleStart.Ctx) : Prop where
  near : nearCheck sy m0 c (kept sy d (PipeTransition.entry m0)) = true
  keep : keepCheck sy m0 d (PipeTransition.entry m0) = true
  lists : listCheck sy d (PipeTransition.entry m0) = true
  /-- frame 0 ends with the six bytes of the pause in a class -/
  pauseNear : nearPauseCheck sy c d = true
  /-- the frames from control with the class beside the walk -/
  pause : pauseCheck sy m0 d (PipeTransition.entry m0) = true
  /-- the store of the move routine with the index 0 goes to a byte of RAM that the guard does not protect (round 15: with it `Route.ChangesBase.upCleanU` is a plain
  `CleanK`, and the theorems that take these checks have the ROM fact that `UpClean` needs) -/
  q : qCheck sy m0 d (PipeTransition.entry m0) = true

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

/-! ## The walk with the class beside it covers the frame -/

section
variable {E : Env} {F : Nat × UInt8} {S : Spot} {G : Guard} {ops : Array (AM Unit)} {R : PR} {T : List SState}

open PipeChangeEnd (Ph)

/-- the classes name only the six bytes, in RAM -/
theorem tab_of (h0 : StepWrites.tabOK R.SB T = true) : ∀ t ∈ T, ∀ p ∈ t, R.SB.contains p.1 = true ∧ p.1 < 2048 := by
  intro t ht p hp
  simp only [StepWrites.tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0
  exact h0 t ht p hp

/-- **A step outside the routine keeps the class**: by `keepOK`, or by the step of the state with the class's bytes -/
theorem keep_of_outOK (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (h0 : StepWrites.tabOK R.SB T = true) {A : AS} {m : Machine}
    (ho : outOK S G E ops R T A = true) (hs : Sim E F A m) (hc : CleanK G S.store m) {t : SState} (ht : t ∈ T) (htm : SIn t m) : SIn t (go step m).2 := by
  have tab := tab_of h0
  unfold outOK at ho
  rw [Bool.or_eq_true] at ho
  rcases ho with hk | ho
  · exact StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (StepWrites.keep_step hs hk)
  · have hag : StepWrites.agrees t A = true := StepWrites.agrees_of hs (fun p hp => (tab t ht p hp).2) htm
    have h1 := List.all_eq_true.1 ho t ht
    rw [hag, Bool.not_true, Bool.false_or] at h1
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hc (StepWrites.sim_refineAll t hs htm)
    have h2 := List.all_eq_true.1 h1 r hr
    cases r with
    | none => cases h2
    | some B => exact StepWrites.sIn_of_le (hB B rfl).1 h2

/-- **One step**: `vsuccs` follows the machine, when its instruction meets `CleanK`, and the class beside the walk goes on -/
theorem s_vsuccs (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hg : R.g < 2048) (h0 : StepWrites.tabOK R.SB T = true)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hph : Ph R T A m) (hc : CleanK G S.store m) :
    ∃ r ∈ vsuccs S G E ops R T A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 ∧ Ph R T B (go step m).2 := by
  have tab := tab_of h0
  unfold vsuccs
  by_cases hin : inR R A = true
  · rw [if_pos hin]
    obtain ⟨A', hA', s', k'⟩ : ∃ A' ∈ (if A.pc == R.call + 6 then TaintRun.splitBit R.g 0x80 A else [A]), Sim E F A' m ∧ A'.k = A.k := by
      split
      · exact TaintRun.cov_bit hg (by decide) A m hs
      · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
    obtain ⟨A₁, hA₁, s1, k1⟩ := FrameKeep.cov_preK hc s'
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hc s1
    refine ⟨r.bind (pret R T A₁), List.mem_flatMap.2 ⟨A', hA', List.mem_flatMap.2 ⟨A₁, hA₁, List.mem_map.2 ⟨r, hr, rfl⟩⟩⟩, fun B hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B0 =>
      obtain ⟨g1, g2⟩ := hB B0 rfl
      have g2' : StepRel A B0 m (go step m).2 := StepWrites.stepRel_k (k1.trans k').symm rfl g2
      have hB2 : pret R T A₁ B0 = some B := hB'
      unfold pret at hB2
      split at hB2
      · split at hB2
        · rename_i _ hT1
          simp only [Option.some.injEq] at hB2
          subst hB2
          obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 hT1
          exact ⟨PipeChangeEnd.sim_forgetP R hg g1, StepWrites.stepRel_k rfl (PipeChangeEnd.forgetP_k R B0) g2', Or.inr ⟨t, ht, StepWrites.sIn_of_le g1 hle⟩⟩
        · cases hB2
      · split at hB2
        · rename_i _ hin2
          simp only [Option.some.injEq] at hB2
          subst hB2
          exact ⟨g1, g2', Or.inl hin2⟩
        · cases hB2
  · rw [if_neg hin]
    have hgh : ∃ t ∈ T, SIn t m := by
      rcases hph with h | h
      · exact absurd h hin
      · exact h
    by_cases hcl : (A.pc == R.call) = true
    · rw [if_pos hcl]
      by_cases hk : StepWrites.keepOK E (fun i => R.SB.contains i) A = true
      · rw [if_pos hk]
        obtain ⟨t, ht, htm⟩ := hgh
        have hag : StepWrites.agrees t A = true := StepWrites.agrees_of hs (fun p hp => (tab t ht p hp).2) htm
        obtain ⟨A₁, hA₁, s1, k1⟩ := FrameKeep.cov_preK hc (StepWrites.sim_refineAll t hs htm)
        obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hc s1
        refine ⟨r, List.mem_flatMap.2 ⟨t, ht, by rw [if_pos hag]; exact List.mem_flatMap.2 ⟨A₁, hA₁, hr⟩⟩, fun B hB' => ?_⟩
        obtain ⟨g1, g2⟩ := hB B hB'
        exact ⟨g1, StepWrites.stepRel_k (k1.trans (StepWrites.refineAll_k t A)).symm rfl g2,
          Or.inr ⟨t, ht, StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (StepWrites.keep_step hs hk)⟩⟩
      · rw [if_neg hk]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    · rw [if_neg hcl]
      obtain ⟨A₁, hA₁, s1, k1⟩ := FrameKeep.cov_preK hc hs
      obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hc s1
      refine ⟨r.bind fun B => if outOK S G E ops R T A₁ then some B else none, List.mem_flatMap.2 ⟨A₁, hA₁, List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
      cases r with
      | none => cases hB'
      | some B0 =>
        obtain ⟨g1, g2⟩ := hB B0 rfl
        have hB2 : (if outOK S G E ops R T A₁ = true then some B0 else none) = some B := hB'
        split at hB2
        · rename_i ho
          simp only [Option.some.injEq] at hB2
          subst hB2
          obtain ⟨t, ht, htm⟩ := hgh
          exact ⟨g1, StepWrites.stepRel_k k1.symm rfl g2, Or.inr ⟨t, ht, keep_of_outOK hops hT h0 ho s1 hc ht htm⟩⟩
        · cases hB2

end

section
variable {C : CfgE} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool} {R : PR} {T : List SState}

open PipeChangeEnd (Ph)

/-- a state of the walk: it covers the machine, the class beside it holds, and the walk from it succeeds -/
def LiveV (C : CfgE) (R : PR) (T : List SState) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph R T A m ∧ ∃ n, walkV C R T fin n A = true

theorem cover_liveV (ht : C.t.all (walkV C R T fin Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph R T B m)
    (h : coverV C R B = true) : ∃ D, LiveV C R T fin F D m ∧ D.k = B.k := by
  unfold coverV at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have h3 : leK B D (knownOf D) = true ∧ inR R B = inR R D := by simpa only [Bool.and_eq_true, beq_iff_eq] using h2
    have hle := PipeWrites.leK_le h3.1
    have hp' : Ph R T D m := by
      rcases hp with h4 | h4
      · exact Or.inl (h3.2 ▸ h4)
      · exact Or.inr h4
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, hp', Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepV (ht : C.t.all (walkV C R T fin Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hg : R.g < 2048) (h0 : StepWrites.tabOK R.SB T = true) {A : AS} {m : Machine} (hl : LiveV C R T fin F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A', LiveV C R T fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ inR R B = false ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph R T B (go step m).2) := by
  obtain ⟨hs, hph, n, hw⟩ := hl
  cases n with
  | zero => simp [walkV] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_vsuccs hops hT hg h0 hs hph hh
    simp only [walkV, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2, h3⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h4⟩ | h4
        · obtain ⟨D, hD, hk⟩ := cover_liveV ht hkl h1 h3 h4
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, h3, n, h4⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, h1, h3⟩

/-- **One frame, with the class beside the walk.** A walk from `S` that succeeds covers the frame of every machine of `S` whose six bytes are in a class, for every
input, if each instruction meets `CleanK`: it ends in a state with `fin`, and the six bytes are in a class again. -/
theorem frame_of_walkV (ht : C.t.all (walkV C R T fin Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) (hg : R.g < 2048) (h0 : StepWrites.tabOK R.SB T = true)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkV C R T fin Fu S = true) (hs : Sim C.E F S m) (hph : Ph R T S m) (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) ∧ ∃ t ∈ T, SIn t (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph R T S { m with pad := smbToPad i } := hph
  have key : ∀ j, (∃ A, LiveV C R T fin F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ inR R B = false ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ Ph R T B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        rcases live_stepV ht hkl hops hT hg h0 h1 (hk j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4, h5⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h5⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · refine ⟨h1, B, h2, h3, h4, ?_⟩
    rcases h5 with h5 | h5
    · rw [h2'] at h5
      cases h5
    · exact h5

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
  · rcases a4 with a4 | ⟨a4, a5, _⟩
    · exact absurd (er.symm.trans hr) a4
    · exact ⟨FrameKeep.watched_of a4 h2, idle_of hC h2 a5⟩

/-- the pipe's timer of a state that `timerOK` accepts: the known bits make at least its first value, and the other bits only add -/
theorem timer_of {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} {tI : Nat} (hs : Sim E F B m) (h : timerOK tI B = true) :
    PipeChangeEnd.timerF ≤ (m.ram.get! tI).toNat := by
  simp only [timerOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have e : m.ram.get! tI &&& (B.getK tI).k = (B.getK tI).v &&& (B.getK tI).k := hs.ram tI h1
  rw [← e, UInt8.toNat_and] at h2
  exact Nat.le_trans h2 Nat.and_le_left

/-- **The end of the frame of the entry.** A frame that starts in the idle loop in control with the kept bytes at their values, whose every instruction is `Clean` for the guard,
and that ends with the pipe's routine, ends with the bytes `atEntry` at their values, in the idle loop, and with the pipe's timer at least its first value. -/
theorem pipe_end (hc : keepCheck sy m0 d e = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) (hw : Watched (kept sy d e) m)
    (hk : ∀ j, Clean (guardOf sy m0 d e) (trace m i j)) (hr : (frame m i).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy) :
    Watched (atEntry d e) (frame m i) ∧ IdleAt (PipeChangeEnd.envOf d e) e (frame m i) ∧ PipeChangeEnd.timerF ≤ ((frame m i).ram.get! (timerI d e)).toNat := by
  have hC := keepOK_of_check hc
  obtain ⟨B, h1, h2⟩ := fin_frame hc h0 hw hk
  have hf : finOf sy m0 d e B = true := h1
  simp only [finOf, finE, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hf
  obtain ⟨⟨⟨a1, a2⟩, _⟩, a4⟩ := hf
  have er := rt_of h2 a1 a2
  rcases a4 with a4 | ⟨a4, a5, a6⟩
  · exact absurd (er.symm.trans hr) a4
  · exact ⟨FrameKeep.watched_of a4 h2, idle_of hC h2 a5, timer_of h2 a6⟩

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
  unfold nearCheck at hN
  rw [Bool.and_eq_true, Bool.and_eq_true] at hN
  obtain ⟨⟨hp, hm⟩, hN'⟩ := hN
  obtain ⟨B', h1, h2⟩ := B.frame0 hB hN' hn
  simp only [Bool.and_eq_true] at h1
  have hk : ∀ p ∈ (PipeWrites.guardOf sy m0).known, (seq 1).ram.get! p.1 = p.2 := FrameKeep.known_of_ctl (m0 := m0) B.ctl
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

/-- **The bytes `atEntry` at the entry, in the idle loop, and the pipe's timer**: the frame before `a` ends with the pipe's routine -/
theorem watched_entryT (hc : keepCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat} (ha : 2 ≤ a)
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1 : Watched (kept sy d e) (seq 1)) (hr : (seq a).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy) :
    Watched (atEntry d e) (seq a) ∧ IdleAt (PipeChangeEnd.envOf d e) e (seq a) ∧ PipeChangeEnd.timerF ≤ ((seq a).ram.get! (timerI d e)).toNat := by
  have hw := watched_up hc next start clean h1 (a - 1) (by omega) (by omega)
  have e1 : seq a = frame (seq (a - 1)) (inp (a - 1)) := by
    have := next (a - 1)
    rwa [Nat.sub_add_cancel (by omega)] at this
  rw [e1] at hr ⊢
  exact pipe_end hc (start_of (start (a - 1) (by omega) (by omega))) hw (clean (a - 1) (by omega) (by omega)) hr

/-- **The condition at the entry**, from the idle loop, the bytes `atEntry`, the pipe's timer and `Rest` -/
theorem entry_of_rest (hl : listCheck sy d e = true) {m : Machine} (hi1 : IdleAt (PipeChangeEnd.envOf d e) e m) (hw : Watched (atEntry d e) m)
    (ht : PipeChangeEnd.timerF ≤ (m.ram.get! (timerI d e)).toNat) (hr : Rest d e m) :
    PipeChangeEnd.Entry d e m := by
  obtain ⟨hb, h2⟩ := hr
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
  · have hw := watched_entryT hK.keep next h2 start clean h1 hr
    exact entry_of_rest hl hw.2.1 hw.1 hw.2.2 rest
  · exfalso
    have e1 : a = 1 := by omega
    subst e1
    have hc := T.ctl
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    have e2 : peek (seq 1) sy.GameEngineSubroutine = PipeEntryRule.vp sy := hr
    rw [e2] at hc
    exact hC.ne (u8_of_u16 hc.2).symm

end

/-! ## The pause at the entry -/

section
variable {sy : Syms} {m0 : Machine} {d : PipeChangeEnd.Data} {e : Machine} {seq : Nat → Machine} {inp : Nat → UInt8}

open PipeChangeEnd (Ph PauseV pauseI pauseIx pauseTI eq_of_knownV toNat_of_toUInt8V)

/-- what the check of the frames with the class beside the walk says -/
structure PauseOK (sy : Syms) (m0 : Machine) (d : PipeChangeEnd.Data) (e : Machine) : Prop where
  g : (PipeChangeEnd.prOf sy d e).g < 2048
  tab : StepWrites.tabOK (PipeChangeEnd.prOf sy d e).SB (classesV sy d) = true
  len : sy.PauseSfxLength.toNat + 1 < 256
  out0 : inR (PipeChangeEnd.prOf sy d e) (startK (guardOf sy m0 d e) (kept sy d e) false) = false
  out1 : inR (PipeChangeEnd.prOf sy d e) (startK (guardOf sy m0 d e) (kept sy d e) true) = false
  table : (cfgV sy m0 d e).t.all (walkV (cfgV sy m0 d e) (PipeChangeEnd.prOf sy d e) (classesV sy d) (finV sy m0 d e) fuelE) = true
  s0 : walkV (cfgV sy m0 d e) (PipeChangeEnd.prOf sy d e) (classesV sy d) (finV sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) false) = true
  s1 : walkV (cfgV sy m0 d e) (PipeChangeEnd.prOf sy d e) (classesV sy d) (finV sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) true) = true

theorem pauseOK_of_check (h : pauseCheck sy m0 d e = true) : PauseOK sy m0 d e := by
  simp only [pauseCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **One frame from control with the pause in a class.** A frame that starts in the idle loop in control with the kept bytes at their values, whose every instruction
is `Clean` for the guard, and whose six bytes of the pause are in a class, ends with them in a class; if it ends with the pipe's routine, it is not paused. -/
theorem pause_frame (hc : pauseCheck sy m0 d e = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0 d e) (PipeEntryRule.envOf m0) m) (hw : Watched (kept sy d e) m)
    (hk : ∀ j, Clean (guardOf sy m0 d e) (trace m i j)) (hp : ∃ t ∈ classesV sy d, SIn t m) :
    (∃ t ∈ classesV sy d, SIn t (frame m i)) ∧
      ((frame m i).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy → (frame m i).ram.get! (pauseI d) &&& 1 ≠ 1) := by
  have hC := pauseOK_of_check hc
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (W := kept sy d e) rfl h0 hw
  have hw0 : walkV (cfgV sy m0 d e) (PipeChangeEnd.prOf sy d e) (classesV sy d) (finV sy m0 d e) fuelE (startK (guardOf sy m0 d e) (kept sy d e) b) = true := by
    cases b with
    | false => exact hC.s0
    | true => exact hC.s1
  obtain ⟨_, B, h1, _, h2, h3⟩ := frame_of_walkV (C := cfgV sy m0 d e) (F := (m.frame, 2)) hC.table rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) rfl hC.g hC.tab
    hw0 hs (Or.inr hp) (fun j => cleanK_of (hk j))
  refine ⟨h3, fun hr => ?_⟩
  have hf : finV sy m0 d e B = true := h1
  unfold finV at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨hf1, hf2⟩ := hf
  have hf1' : finOf sy m0 d e B = true := hf1
  simp only [finOf, finE, Bool.and_eq_true, decide_eq_true_eq] at hf1'
  obtain ⟨⟨⟨a1, a2⟩, _⟩, _⟩ := hf1'
  have er := rt_of h2 a1 a2
  rw [Bool.or_eq_true, bne_iff_ne, ne_eq] at hf2
  rcases hf2 with hf2 | hf2
  · exact absurd (er.symm.trans hr) hf2
  · exact PipeChangeEnd.not_paused_of h2 hf2

set_option maxRecDepth 100000 in
theorem low7_all : ((List.range 256).all fun n => n.toUInt8 &&& 0x7F != 0 || n.toUInt8 == 0 || n.toUInt8 == 0x80) = true := by decide

/-- a byte with bits 0 to 6 clear is 0 or `0x80` -/
theorem low7_cases (x : UInt8) (h : x &&& 0x7F = 0) : x = 0 ∨ x = 0x80 := by
  have h2 := List.all_eq_true.1 low7_all x.toNat (List.mem_range.2 x.toNat_lt)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e, h] at h2
  simpa using h2

/-- **A machine that is not paused, with the bytes of a class, has the pause as `PauseV` says** (the length of the sound and one more are below 256): the classes that
are not paused are the three kinds of `PauseV` -/
theorem pauseV_of_class (hL : sy.PauseSfxLength.toNat + 1 < 256) {t : SState} (ht : t ∈ classesV sy d) {m : Machine} (hm : SIn t m)
    (hnp : m.ram.get! (pauseI d) &&& 1 ≠ 1) : PauseV sy d m := by
  have paused : ∀ v : UInt8, v &&& 1 = 1 → (pauseI d, AB.known v) ∈ t → False := fun v hv hin => by
    have := eq_of_knownV (hm _ hin)
    rw [this] at hnp
    exact hnp hv
  unfold classesV at ht
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at ht
  rcases ht with (((((rfl | ⟨j, hj, rfl⟩) | rfl) | rfl) | ⟨j, hj, rfl⟩) | (rfl | rfl | rfl))
  · have hg : m.ram.get! (pauseI d) &&& 0x7F = (0 : UInt8) &&& 0x7F := hm (pauseI d, ⟨0, 0x7F⟩) (by simp)
    exact Or.inl ⟨low7_cases _ (hg.trans (by decide)), eq_of_knownV (hm ((pauseIx d.nx).q, AB.known 0) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).b, AB.known 0) (by simp)), eq_of_knownV (hm ((pauseIx d.nx).f, AB.known 0) (by simp))⟩
  · have hc : m.ram.get! (pauseIx d.nx).c = (j + 1).toUInt8 := eq_of_knownV (hm ((pauseIx d.nx).c, AB.known (j + 1).toUInt8) (by simp))
    have hc' := toNat_of_toUInt8V hc (by omega)
    have hti : m.ram.get! (pauseTI d) = (j + 2).toUInt8 := eq_of_knownV (hm (pauseTI d, AB.known (j + 2).toUInt8) (by simp))
    have hti' := toNat_of_toUInt8V hti (by omega)
    exact Or.inr (Or.inl ⟨eq_of_knownV (hm (pauseI d, AB.known 0x80) (by simp)), eq_of_knownV (hm ((pauseIx d.nx).q, AB.known 0) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).b, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).f, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)), by omega, by omega, by omega⟩)
  · have hti : m.ram.get! (pauseTI d) = (sy.PauseSfxLength.toNat + 1).toUInt8 :=
      eq_of_knownV (hm (pauseTI d, AB.known (sy.PauseSfxLength.toNat + 1).toUInt8) (by simp))
    exact Or.inr (Or.inr ⟨eq_of_knownV (hm (pauseI d, AB.known 0x80) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).q, AB.known sy.UnpauseSfxValue.toUInt8) (by simp)), eq_of_knownV (hm ((pauseIx d.nx).b, AB.known 0) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).f, AB.known sy.PauseSfxValue.toUInt8) (by simp)), toNat_of_toUInt8V hti hL⟩)
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 1 (by decide) (by simp)).elim

/-- **At control the six bytes of the pause are in a class**: frame 0 begins in a near or held state of `TitleStart`, and the walk of its frame ends with control
with the six bytes as a class says (`nearPauseCheck`) -/
theorem Begin.pauseClass {c : TitleStart.Ctx} {t0 : Nat} (hB : TitleStart.check sy c t0 = true) (hN : nearPauseCheck sy c d = true) (B : TitleStart.Begin sy c seq inp)
    (hn : seq 1 = frame (seq 0) (inp 0)) : ∃ t ∈ classesV sy d, SIn t (seq 1) := by
  obtain ⟨B', h1, h2⟩ := B.frame0 hB hN hn
  have h1' : (classesV sy d).any (soundLe B') = true := h1
  obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 h1'
  exact ⟨t, ht, StepWrites.sIn_of_le h2 hle⟩

/-- **Every frame from control keeps the pause in a class**, up to the entry: frame `n`, for `1 ≤ n < a`, starts in control with the kept bytes and its instructions
are `Clean` -/
theorem class_up (hc : pauseCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat}
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n) ∧ Watched (kept sy d e) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1 : ∃ t ∈ classesV sy d, SIn t (seq 1)) : ∀ n, 1 ≤ n → n ≤ a → ∃ t ∈ classesV sy d, SIn t (seq n) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro ha hb
    by_cases hk : k = 0
    · subst hk
      exact h1
    · have hp := ih (by omega) (by omega)
      obtain ⟨s1, w1⟩ := start k (by omega) (by omega)
      have h := (pause_frame hc (start_of s1) w1 (clean k (by omega) (by omega)) hp).1
      rw [next k]
      exact h

/-- **The pause at the entry**: the frame before `a` ends with the pipe's routine, so it is not paused, and the class at its end is one of `PauseV` -/
theorem pause_entry (hc : pauseCheck sy m0 d e = true) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat} (ha : 2 ≤ a)
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n) ∧ Watched (kept sy d e) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d e) (trace (seq n) (inp n) j))
    (h1 : ∃ t ∈ classesV sy d, SIn t (seq 1)) (hr : (seq a).ram.get! (guardOf sy m0 d e).rtI = PipeEntryRule.vp sy) : PauseV sy d (seq a) := by
  have hp := class_up hc next start clean h1 (a - 1) (by omega) (by omega)
  obtain ⟨s1, w1⟩ := start (a - 1) (by omega) (by omega)
  have hf := pause_frame hc (start_of s1) w1 (clean (a - 1) (by omega) (by omega)) hp
  have e1 : seq a = frame (seq (a - 1)) (inp (a - 1)) := by
    have := next (a - 1)
    rwa [Nat.sub_add_cancel (by omega)] at this
  rw [e1] at hr ⊢
  obtain ⟨t, ht, htm⟩ := hf.1
  exact pauseV_of_class (pauseOK_of_check hc).len ht htm (hf.2 hr)

/-- **The condition at the entry with the pause, from the press of Start on the title.** As `entry_of_title`; the six bytes of the pause are in a class at control
(`Begin.pauseClass`), every frame from control keeps them in a class (`class_up`), and the frame of the entry is not paused (`pause_entry`). Start may be pressed on
any of these frames. -/
theorem entryV_of_title {c : TitleStart.Ctx} {t0 : Nat} (hB : TitleStart.check sy c t0 = true) (hK : Checks sy m0 d c)
    (T : TitleStart.Begin sy c seq inp) (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {a : Nat} (ha : 1 ≤ a)
    (start : ∀ n, 1 ≤ n → n < a → FrameStart (PipeWrites.guardOf sy m0) (PipeEntryRule.envOf m0) (seq n))
    (clean : ∀ n, 1 ≤ n → n < a → ∀ j, Clean (guardOf sy m0 d (PipeTransition.entry m0)) (trace (seq n) (inp n) j))
    (rest : Rest d (PipeTransition.entry m0) (seq a)) : PipeChangeEnd.EntryV sy d (PipeTransition.entry m0) (seq a) := by
  have he := entry_of_title hB hK T next ha start clean rest
  have hl := hK.lists
  have hr : (seq a).ram.get! (guardOf sy m0 d (PipeTransition.entry m0)).rtI = PipeEntryRule.vp sy := by
    simp only [listCheck, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hl
    obtain ⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, _⟩ := hl
    exact (rest.1 _ h2 h3).trans h4
  have h1w := Begin.watched hB hK.near T (next 0)
  have hw := watched_up hK.keep next start clean h1w
  have hp1 := Begin.pauseClass (d := d) hB hK.pauseNear T (next 0)
  by_cases h2 : 2 ≤ a
  · exact ⟨he, pause_entry hK.pause next h2 (fun n h1 h3 => ⟨start n h1 h3, hw n h1 h3⟩) clean hp1 hr⟩
  · exfalso
    have hC := keepOK_of_check hK.keep
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
  (d.known.all fun i => !(restIdx d.nx).contains i || m.ram.get! i == e.ram.get! i) &&
    (d.bits.filter fun b => (restIdx d.nx).contains b.1).all fun b => decide (b.1 < 2048) && (m.ram.get! b.1 &&& b.2) == (e.ram.get! b.1 &&& b.2)

/-- `IdleAt` as a check, for a program -/
def idleB (E : Env) (e m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
    m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
    m.pc == e.pc && m.s == e.s

end Smbrta.EntryKeep
