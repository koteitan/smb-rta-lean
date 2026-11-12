import Theorems.LagFrames
import Theorems.FrameKeep
import Theorems.FrameModel

/-!
# A frame in control, up to the player's routine

A frame that starts in the idle loop in control (`FrameKeep.StartK`) runs the screen, the sound, the pad, the pause and the timers, then the mode's routine, which
calls the player's routine. Here the abstract machine of `TaintRun` follows the frame from its start to the first time it comes to the player's routine (the cut),
as `LagFrames` follows a frame to the call of the mode's routine. One byte is followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on any write to it.
At the cut the walk asks that the byte is still followed, so it has the value it had at the frame's start. There is one walk for each byte of `keepI`.
At the cut the walk also asks the stack pointer of the player's routine, no NMI pending, the NMI off in the PPU, and the routine byte of control.

The condition on each instruction before the cut is `FrameKeep.CleanK` (the condition of `PipeWrites.Clean`, but the move routine's store): the walk asks that no state
before the cut is at that store. A store with a target not known makes the walk forget the followed byte, so the walk fails if one comes before the cut.

On the paths that do not come to the cut (the paused frames: the NMI skips the mode's routine) the walk goes on to the frame's end, and asks there that the byte is still
followed (`endR`). One more walk follows the low bit of the pause byte (`pauseA`, the byte the NMI tests before the call of the mode's routine): it starts with the bit known,
and asks that it is known to be 1 at the end of a frame that did not come to the cut. So (`cut_or_end`):
* `arrive_of`, `arrive_at`: a frame in control that ends with the game not paused comes to the player's routine, a first time at `arrAt`;
* `keep_of_noCut`: a frame in control that does not come to the player's routine keeps the bytes of `keepA`.

At the cut the walk of the pause bit can go on (`CfgR.after`): a walk of `FrameKeep` follows the frame from the player's routine to its end (`afterCheck`), with four more
protected bytes (`spareI`: the pause byte, the area's type, the swimming flag, the change of size). The condition on each instruction is then `CleanK` and `Spare`. So
(`area_end`): a frame in control keeps the area's type, the swimming flag and the change of size, and a frame that comes to the player's routine ends not paused; so a frame
that ends paused does not come there (`noCut_of_paused`).

The searches are no part of the proof: the check walks every state of its table. There is no game data in this file. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.CtrlKeep

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites
open PipeEntryRule (trace)
open LagFrames (preL opOf startL)

/-- the key: the `pc`, the stack, the flags of the frame, the counter, both index registers, the pause byte `pz` if `pw`, and `A` and `Y` near the jump routine -/
def keyR (G : Guard) (pz : Nat) (pw : Bool) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0) + (if A.rk then 16 else 0) + (if A.spent then 32 else 0)
  let n := (n * 65536 + num A.x) * 65536 + num A.y
  let n := if pw then n * 65536 + num (A.getK pz) else n
  let n := if G.je ≤ A.pc && A.pc ≤ G.je + 18 then n * 65536 + num A.a else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

/-! ## The walk -/

/-- the table, and what the walk asks at the cut -/
structure CfgR where
  E : Env
  ops : Array (AM Unit)
  G : Guard
  /-- the walk stops at this `pc`: the player's routine -/
  cut : UInt16
  /-- the move routine's store: no state before the cut is there -/
  q : UInt16
  /-- the stack pointer at the cut -/
  S : UInt8
  /-- the routine byte, and its value at the cut -/
  engI : Nat
  eng : UInt8
  /-- the pause byte; if `pw`, the walk asks that its low bit is known to be 1 where the frame ends before the cut -/
  pz : Nat
  pw : Bool
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  /-- the `pc` of the states of the table -/
  tc : ByteArray
  /-- what the walk asks besides `atCut` at the cut: for the pause bit, that the walk from the cut to the frame's end succeeds (`CtrlKeep.after`) -/
  after : AS → Bool := fun _ => true

/-- what the walk asks at the cut: the byte still followed and not decremented, the stack pointer, no NMI pending, the NMI off, the routine byte -/
def atCut (C : CfgR) (B : AS) : Bool :=
  B.rk && !B.spent && B.s == C.S && !B.nmi && B.ppuCtrl.bit 0x80 == some false && (B.getK C.engI).isK && (B.getK C.engI).v == C.eng

/-- what the walk asks at the frame's end, if the frame did not come to the cut: the byte still followed and not decremented, and if `pw` the low bit of the pause
byte known to be 1 -/
def endR (C : CfgR) (B : AS) : Bool := B.rk && !B.spent && (!C.pw || (B.getK C.pz).bit 0x01 == some true)

def coverR (C : CfgR) (B : AS) : Bool :=
  match C.idx[keyR C.G C.pz C.pw B]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path comes to the cut with `atCut`, ends the frame with `endR`, or reaches a state of the table. No state is at the move
routine's store, and no step is `DEC abs` of the byte. -/
def walkR (C : CfgR) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => A.pc != C.q && (preL C.G A).all fun A₁ => !isRkDec C.E A₁.pc (opOf C.E A₁) && (gsucc C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        (if B.pc == C.cut then atCut C B && C.after B else (C.tc.get! B.pc.toNat != 0 && coverR C B) || walkR C n B)
      else B.k == A.k + 1 && endR C B

/-- the state when the frame starts, with the byte followed and the low bit of the pause byte known: `b` -/
def startP (G : Guard) (pz : Nat) (late b : Bool) : AS := (startL G late).setK pz ⟨if b then 1 else 0, 1⟩

/-- **The check of one byte.** -/
def ctrlCheck1 (C : CfgR) : Bool :=
  decide (C.G.late < dotsPerFrame) && C.cut != C.G.idle && C.t.all (walkR C fuelG) &&
    walkR C fuelG (startP C.G C.pz false false) && walkR C fuelG (startP C.G C.pz false true) &&
    walkR C fuelG (startP C.G C.pz true false) && walkR C fuelG (startP C.G C.pz true true)

/-! ## On the ROM -/

/-- **The bytes that a frame in control keeps up to the player's routine**: the horizontal state and the position (`FrameModel.hBytes`), the collision bits, the stored
speed, the area's type, the jumpspring, the swimming flag, the change of size, the vertical bytes and the jump's halt value (`SurfaceFrames.vKeep`), A and B, and A and B
of the frame before. -/
def keepA (sy : Syms) : List UInt16 :=
  [sy.Player_X_Speed, sy.Player_X_MoveForce, sy.PlayerFacingDir, sy.Player_MovingDir, sy.RunningSpeed, sy.Player_X_Position, sy.Player_PageLoc, sy.SprObject_X_MoveForce,
   sy.Player_CollisionBits, sy.Player_XSpeedAbsolute, sy.AreaType, sy.JumpspringAnimCtrl, sy.SwimmingFlag, sy.PlayerChangeSizeFlag,
   sy.Player_Y_Position, sy.Player_Y_MoveForce, sy.Player_Y_Speed, sy.Player_YMF_Dummy, sy.VerticalForce, sy.VerticalForceDown, sy.JumpOrigin_Y_Position,
   sy.Player_State, sy.DiffToHaltJump, sy.A_B_Buttons, sy.PreviousA_B_Buttons]

def keepI (sy : Syms) : List Nat := (keepA sy).map fun a => (a &&& 0x7FF).toNat

/-- **The pause byte**: the operand of the load just before the NMI's call of the mode's routine (`lda` of the byte, `lsr`, `bcs` over the call). Its low bit is 1 while
the game is paused, and a paused frame does not call the mode's routine. -/
def pauseA (sy : Syms) (m0 : Machine) : UInt16 :=
  (romByte m0 (LagFrames.modeCall sy - 5)).toUInt16 ||| ((romByte m0 (LagFrames.modeCall sy - 4)).toUInt16 <<< 8)

def pauseI (sy : Syms) (m0 : Machine) : Nat := (pauseA sy m0 &&& 0x7FF).toNat

/-- **The game is not paused** on the machine `m`: the low bit of the pause byte is 0 -/
def Unpaused (sy : Syms) (m0 m : Machine) : Prop := m.ram.get! (pauseI sy m0) &&& 1 = 0

/-- `Unpaused`, for a program -/
def unpausedB (sy : Syms) (m0 m : Machine) : Bool := m.ram.get! (pauseI sy m0) &&& 1 == 0

/-- the machine of the walk, with the byte `b` followed -/
def envR (m0 : Machine) (b : Nat) : Env := { PipeEntryRule.envOf m0 with rkI := b }

/-! ## Finding the table: a search, no part of the proof

As the search of `LagFrames`, but it forgets no byte of RAM, and the index registers are in the key: the loops before the player's routine store through an index
(the timers, the random bits, the top score), and the check knows the target of such a store only if the index is known. -/

/-- what the search forgets: the stack below the stack pointer -/
def normR (G : Guard) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) A.kn
  { A with kn }

def routeR (G : Guard) (pz : Nat) (pw : Bool) (X : LagFrames.SL) (B0 : AS) : LagFrames.SL :=
  let B := normR G B0
  let K := keyR G pz pw B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runR (G : Guard) (E : Env) (ops : Array (AM Unit)) (cut : UInt16) (pz : Nat) (pw : Bool) (X0 : LagFrames.SL) (A0 : AS) : LagFrames.SL := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preL G cur).flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (fun r => r.isNone) then X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let same := (rs.filterMap id).filter fun b => b.k == cur.k
    X := { X with cuts := X.cuts + (same.filter fun b => b.pc == cut).length, ends := X.ends + ((rs.filterMap id).filter fun b => b.k != cur.k).length }
    let good := same.filter fun b => b.pc != cut
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeR G pz pw X b
    break
  return X

partial def searchR (G : Guard) (E : Env) (cut : UInt16) (pz : Nat) (pw : Bool) : LagFrames.SL := Id.run do
  let ops := (aRows E).toArray
  let mut X : LagFrames.SL := [startP G pz false false, startP G pz false true, startP G pz true false, startP G pz true true].foldl (routeR G pz pw) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runR G E ops cut pz pw X A
  return X

/-- the table, from the search -/
def tableOfR (G : Guard) (pz : Nat) (pw : Bool) (X : LagFrames.SL) : Array AS × Std.HashMap Nat Nat × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat Nat := {}
  let mut tc := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (keyR G pz pw A) t.size
      tc := tc.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, tc)

/-- the table: one search serves every byte, since no step before the cut stores through a target not known. With `pw` the states with other values of the
pause byte are not joined. -/
abbrev Table := Array AS × Std.HashMap Nat Nat × ByteArray

def cutTable (sy : Syms) (m0 : Machine) (pw : Bool) : Table :=
  let G := FrameKeep.guardK sy m0
  tableOfR G (pauseI sy m0) pw (searchR G (envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) sy.PlayerCtrlRoutine (pauseI sy m0) pw)

/-- the walk of the byte `b`, with the table `q`; with `pw` it asks the pause bit at the frame's end -/
def cfgOf (sy : Syms) (m0 : Machine) (q : Table) (b : Nat) (pw : Bool) : CfgR :=
  { E := envR m0 b, ops := (aRows (envR m0 b)).toArray, G := FrameKeep.guardK sy m0, cut := sy.PlayerCtrlRoutine, q := (FrameKeep.spotOf sy m0).store,
    S := FrameModel.ctrlStack sy m0, engI := (sy.GameEngineSubroutine &&& 0x7FF).toNat, eng := sy.Eng_PlayerCtrl.toUInt8, pz := pauseI sy m0, pw, t := q.1,
    kl := q.1.map knownOf, idx := q.2.1, tc := q.2.2 }

/-- the walk of the byte `b`, as the program runs it -/
def cfgR (sy : Syms) (m0 : Machine) (b : Nat) (pw : Bool) : CfgR := cfgOf sy m0 (cutTable sy m0 pw) b pw

/-- **The check**: for every byte of `keepI` a walk, and one walk that asks the pause bit -/
def ctrlCheck (sy : Syms) (m0 : Machine) : Bool :=
  (let q := cutTable sy m0 false
   (keepI sy).all fun b => ctrlCheck1 (cfgOf sy m0 q b false)) &&
  ctrlCheck1 (cfgOf sy m0 (cutTable sy m0 true) (sy.Player_X_Speed &&& 0x7FF).toNat true)

/-! ## From the cut to the frame's end

At the cut the walk of the pause bit can hand over to a walk of `FrameKeep` (`FrameKeep.walkK`): it follows the frame from the player's routine to its end, forgets the
bytes outside the guard's protected bytes as `FrameKeep` does, and asks at the frame's end the watched bits (`FrameKeep.Watch`). Its guard protects more bytes (`guardP`):
a store through an index or a pointer does not write them. -/

/-- the guard of `FrameKeep`, with the bytes `l` protected too -/
def guardP (sy : Syms) (m0 : Machine) (l : List Nat) : Guard := { FrameKeep.guardK sy m0 with prot := l ++ (FrameKeep.guardK sy m0).prot }

/-- the state at the cut, for the walk after it: the byte is no longer followed, of the bytes of `W` only the watched bits are kept, and the bits of `V` are set to
their values -/
def toA (W V : List FrameKeep.Watch) (B : AS) : AS :=
  let B := W.foldl (fun A w => A.setK w.1 ⟨(A.getK w.1).v &&& w.2.1, (A.getK w.1).k &&& w.2.1⟩) B
  { V.foldl (fun A w => A.setK w.1 ⟨w.2.2 &&& w.2.1, w.2.1⟩) B with rk := false, spent := false }

/-- the states at the cut that a walk reaches: for the search after the cut, no part of the proof -/
def cutsR (C : CfgR) : Nat → AS → List AS
  | 0, _ => []
  | n + 1, A => (preL C.G A).flatMap fun A₁ => (gsucc C.G C.E C.ops A₁).flatMap fun r =>
    match r with
    | none => []
    | some B =>
      if B.k == A.k then (if B.pc == C.cut then [B] else if C.tc.get! B.pc.toNat != 0 && coverR C B then [] else cutsR C n B) else []

/-- every state at the cut that the walk of `C` reaches, from the table and the frame's start -/
def cutsOf (C : CfgR) : List AS :=
  (C.t.toList ++ [startP C.G C.pz false false, startP C.G C.pz false true, startP C.G C.pz true false, startP C.G C.pz true true]).flatMap (cutsR C fuelG)

/-- the search after the cut, from the states `starts`: no part of the proof -/
def afterSearch (sy : Syms) (m0 : Machine) (l : List Nat) (W V : List FrameKeep.Watch) (starts : List AS) : SG :=
  let S := FrameKeep.spotOf sy m0
  let G := guardP sy m0 l
  let E := PipeEntryRule.envOf m0
  let key := FrameKeep.keyK S G W
  FrameKeep.searchKW S G E W key (aRows E).toArray ((starts.map (toA W V)).foldl (FrameKeep.routeKW S G key) {})

/-- the table of the walk after the cut -/
def afterCfg (sy : Syms) (m0 : Machine) (l : List Nat) (W V : List FrameKeep.Watch) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardP sy m0 l
  let E := PipeEntryRule.envOf m0
  let key := FrameKeep.keyK S G W
  let q := FrameKeep.tableOfKW key (afterSearch sy m0 l W V starts)
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the pause bit, watched 0 -/
def pauseW (sy : Syms) (m0 : Machine) : List FrameKeep.Watch := [(pauseI sy m0, 0x01, 0)]

/-- **The bytes that the walk after the cut protects** besides those of `FrameKeep.guardK`: the pause byte, the area's type, the swimming flag, the change of size -/
def spareI (sy : Syms) (m0 : Machine) : List Nat :=
  [pauseI sy m0, (sy.AreaType &&& 0x7FF).toNat, (sy.SwimmingFlag &&& 0x7FF).toNat, (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat]

/-- **A store through an index or a pointer does not write the bytes of `spareI`** (one instruction). With `FrameKeep.CleanK` it is `CleanK` of the guard that protects
them too (`cleanP_of`). -/
def Spare (sy : Syms) (m0 m : Machine) : Prop := ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ spareI sy m0

/-- `Spare`, for a program -/
def spareB (sy : Syms) (m0 m : Machine) : Bool :=
  match wTarget (opAt m) m with
  | some t => !(decide (t < 0x2000) && (spareI sy m0).contains (t &&& 0x7FF).toNat)
  | none => true

/-- **The area's type is `v`, the swimming flag is 0 and no change of size is going on** on the machine `m` -/
def AreaOK (sy : Syms) (v : UInt8) (m : Machine) : Prop := peek m sy.AreaType = v ∧ peek m sy.SwimmingFlag = 0 ∧ peek m sy.PlayerChangeSizeFlag = 0

/-- the area's type `v`, the swimming flag 0, the change of size 0: set at the cut, and watched at the frame's end -/
def valA (sy : Syms) (v : UInt8) : List FrameKeep.Watch :=
  [((sy.AreaType &&& 0x7FF).toNat, 0xFF, v), ((sy.SwimmingFlag &&& 0x7FF).toNat, 0xFF, 0), ((sy.PlayerChangeSizeFlag &&& 0x7FF).toNat, 0xFF, 0)]

/-- what the walk after the cut watches: the pause bit 0, the area's type `v`, the swimming flag 0, the change of size 0 -/
def watchA (sy : Syms) (m0 : Machine) (v : UInt8) : List FrameKeep.Watch := pauseW sy m0 ++ valA sy v

/-- the walk of the pause bit with the table `q` -/
abbrev cfgPz (sy : Syms) (m0 : Machine) (q : Table) : CfgR := cfgOf sy m0 q (sy.Player_X_Speed &&& 0x7FF).toNat true

/-- the table of the walk after the cut, from the states at the cut of the walk of the pause bit -/
def afterOf (sy : Syms) (m0 : Machine) (v : UInt8) (q : Table) : FrameKeep.CfgK :=
  afterCfg sy m0 (spareI sy m0) (watchA sy m0 v) (valA sy v) (cutsOf (cfgPz sy m0 q))

/-- the walk of the pause bit that asks at the cut that the walk `CA` from there to the frame's end succeeds -/
def cfgPA (sy : Syms) (m0 : Machine) (v : UInt8) (q : Table) (CA : FrameKeep.CfgK) : CfgR :=
  { cfgPz sy m0 q with after := fun B => FrameKeep.walkK CA FrameKeep.fuelK (toA (watchA sy m0 v) (valA sy v) B) }

/-- **The check of the whole frame**: the walk of the pause bit up to the cut, and from there the walk after the cut, with the pause byte, the area's type, the swimming flag
and the change of size protected; it asks at the frame's end the pause bit 0, the area's type `v`, the swimming flag 0, the change of size 0 -/
def afterCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := cutTable sy m0 true
  let CA := afterOf sy m0 v q
  ctrlCheck1 (cfgPA sy m0 v q CA) && CA.t.all (FrameKeep.walkK CA FrameKeep.fuelK)

/-! ## The walk covers the frame up to the cut -/

section
variable {C : CfgR} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveR (C : CfgR) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkR C n A = true

theorem cover_liveR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverR C B = true) : ∃ D, LiveR C F D m := by
  unfold coverR at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := le_k hle
        omega
      exact ⟨D, sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

/-- one step: the walk goes on, or the machine comes to the cut with `atCut`, or the frame ends with `endR` -/
theorem live_stepR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveR C F A m) (hc : FrameKeep.CleanK C.G C.q m) :
    (∃ A', LiveR C F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ (go step m).2.pc ≠ C.cut ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = C.cut ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧
      ∃ B, atCut C B = true ∧ C.after B = true ∧ Sim C.E F B (go step m).2) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, endR C B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkR] at hw
  | succ n =>
    simp only [walkR, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hw
    obtain ⟨hq, hw⟩ := hw
    have hc' : Clean C.G m := FrameKeep.clean_of hc (fun h => hq (hs.pc ▸ h.1))
    obtain ⟨A₁, hA, hs1, hk1⟩ := LagFrames.cov_preL hc' hs
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    have hd' : isRkDec C.E A₁.pc (opOf C.E A₁) = false := by simpa using hd
    obtain ⟨r, hr1, hB⟩ := LagFrames.s_gsuccL hops hd' hc' hs1
    have hw3 := hw2 r hr1
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [if_pos (by simp [k1, hk1])] at hw3
        by_cases hcut : B.pc = C.cut
        · rw [if_pos (by simp [hcut]), Bool.and_eq_true] at hw3
          exact Or.inr (Or.inl ⟨k2, by rw [h1.pc]; exact hcut, k3, B, hw3.1, hw3.2, h1⟩)
        · rw [if_neg (by simp [hcut])] at hw3
          have hcut' : (go step m).2.pc ≠ C.cut := by rw [h1.pc]; exact hcut
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
          rcases hw3 with ⟨_, h4⟩ | h4
          · obtain ⟨D, hD⟩ := cover_liveR ht hkl h1 (by omega) h4
            exact Or.inl ⟨D, hD, k2, hcut', k3⟩
          · exact Or.inl ⟨B, ⟨h1, by omega, n, h4⟩, k2, hcut', k3⟩
      · rw [if_neg (by simp [k1, hk1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact Or.inr (Or.inr ⟨k2, B, hw3.2, h1⟩)

/-- the instructions of the frame up to its first arrival at the cut -/
theorem frame_runR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) {M : Machine} {i : UInt8}
    (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace M i n)) {k : Nat} (hk : (trace M i k).pc = C.cut) (hf : (trace M i k).frame = M.frame)
    (hfirst : ∀ j, j < k → (trace M i j).pc ≠ C.cut) :
    ∀ (d j : Nat) (A : AS), j + d = k → LiveR C F A (trace M i j) → (trace M i j).frame = M.frame → (trace M i j).pc ≠ C.cut →
      ∃ B, atCut C B = true ∧ Sim C.E F B (trace M i k) := by
  intro d
  induction d with
  | zero =>
    intro j A hj _ _ hp
    rw [Nat.add_zero] at hj
    rw [hj] at hp
    exact absurd hk hp
  | succ d ih =>
    intro j A hj hl hfj _
    have hh := hl.1.halted
    have e : trace M i (j + 1) = (go step (trace M i j)).2 := by
      show PipeEntryRule.nxt (M.frame + 1) (trace M i j) = _
      have hn : ¬ ((trace M i j).frame ≥ M.frame + 1 || (trace M i j).halted) = true := by simp [hfj, hh]
      simp only [PipeEntryRule.nxt, if_neg hn]
    rcases live_stepR ht hkl hops hl (hcl j) with ⟨A', h1, h2, h3, _⟩ | ⟨h1, h2, _, B, h3, _, h4⟩ | ⟨h1, _⟩
    · rw [← e] at h1 h2 h3
      exact ih (j + 1) A' (by omega) h1 (h2.trans hfj) h3
    · rw [← e] at h1 h2 h4
      have hjk : j + 1 = k := by
        by_cases h5 : j + 1 < k
        · exact absurd h2 (hfirst (j + 1) h5)
        · omega
      rw [← hjk]
      exact ⟨B, h3, h4⟩
    · rw [← e] at h1
      exfalso
      have hst : ((trace M i (j + 1)).frame ≥ M.frame + 1 || (trace M i (j + 1)).halted) = true := by simp [h1, hfj]
      have e2 := PipeEntryRule.trace_stop hst d
      rw [show j + 1 + d = k by omega] at e2
      rw [e2, h1, hfj] at hf
      omega

/-- what the check of one byte says -/
structure OKR (C : CfgR) : Prop where
  late : C.G.late < dotsPerFrame
  cutIdle : C.cut ≠ C.G.idle
  table : C.t.all (walkR C fuelG) = true
  s00 : walkR C fuelG (startP C.G C.pz false false) = true
  s01 : walkR C fuelG (startP C.G C.pz false true) = true
  s10 : walkR C fuelG (startP C.G C.pz true false) = true
  s11 : walkR C fuelG (startP C.G C.pz true true) = true

theorem okR_of_check (h : ctrlCheck1 C = true) : OKR C := by
  simp only [ctrlCheck1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem low_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 1 = (if (UInt8.ofNat n.val &&& 1 != 0) = true then (1 : UInt8) else 0) &&& 1 := by decide +kernel

/-- the low bit of a byte -/
theorem low_mem (x : UInt8) : (⟨if (x &&& 1 != 0) = true then 1 else 0, 1⟩ : AB).mem x := by
  have h := low_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

/-- the walk starts: the state of the frame's start, with the byte followed and the low bit of the pause byte -/
theorem start_liveR (hO : ctrlCheck1 C = true) (hE : C.E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) :
    ∃ A, LiveR C (m.frame, m.ram.get! C.E.rkI) A (trace m i 0) := by
  have H := okR_of_check hO
  obtain ⟨b, hs⟩ := sim_startG hE h0
  have hs2 := LagFrames.sim_rk hs rfl
  have hs3 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := { hs2 with pad := by rw [hE]; exact mem_top _ }
  have hs4 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startP C.G C.pz b (m.ram.get! C.pz &&& 1 != 0)) (trace m i 0) :=
    PipeEntryRule.sim_setK' hs3 (low_mem (m.ram.get! C.pz))
  generalize (m.ram.get! C.pz &&& 1 != 0) = p at hs4
  refine ⟨_, hs4, rfl, fuelG, ?_⟩
  cases b <;> cases p
  · exact H.s00
  · exact H.s01
  · exact H.s10
  · exact H.s11

/-- **One byte.** A frame from the idle loop in control whose instructions meet `CleanK` comes to the cut, the first time, in a state that the walk covers with `atCut`:
the followed byte is as it began. -/
theorem at_cut (hO : ctrlCheck1 C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n))
    {k : Nat} (hk : (trace m i k).pc = C.cut) (hf : (trace m i k).frame = m.frame) (hfirst : ∀ j, j < k → (trace m i j).pc ≠ C.cut) :
    ∃ B, atCut C B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i k) := by
  have H := okR_of_check hO
  obtain ⟨A, hl⟩ := start_liveR hO hE h0 (i := i)
  have hp0 : (trace m i 0).pc ≠ C.cut := by
    show m.pc ≠ C.cut
    rw [h0.pc]
    exact fun h => H.cutIdle h.symm
  exact frame_runR H.table hkl hops hcl hk hf hfirst k 0 A (by omega) hl rfl hp0

/-- **One byte, the whole frame.** A frame from the idle loop in control whose instructions meet `CleanK` either comes to the cut (a first time, before its end), or
it ends in a state that the walk covers with `endR`: the followed byte as it began, and the low bit of the pause byte 1. -/
theorem cut_or_end2 (hO : ctrlCheck1 C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n)) :
    (∃ k, (trace m i k).pc = C.cut ∧ (trace m i k).frame = m.frame ∧ k ≤ fuelPerFrame ∧ (∀ j, j < k → (trace m i j).pc ≠ C.cut) ∧
      m.fdot + 3 * k ≤ (trace m i k).fdot ∧ ∃ B, atCut C B = true ∧ C.after B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i k)) ∨
    ((∀ j, (trace m i j).frame = m.frame → (trace m i j).pc ≠ C.cut) ∧ ∃ B, endR C B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (frame m i)) := by
  have H := okR_of_check hO
  obtain ⟨A0, hl0⟩ := start_liveR hO hE h0 (i := i)
  have hp0 : (trace m i 0).pc ≠ C.cut := by
    show m.pc ≠ C.cut
    rw [h0.pc]
    exact fun h => H.cutIdle h.symm
  have key : ∀ j, (∃ A, LiveR C (m.frame, m.ram.get! C.E.rkI) A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot ∧
        ∀ j', j' ≤ j → (trace m i j').pc ≠ C.cut) ∨
      (∃ k, k ≤ j ∧ (trace m i k).pc = C.cut ∧ (trace m i k).frame = m.frame ∧ (∀ j', j' < k → (trace m i j').pc ≠ C.cut) ∧
        m.fdot + 3 * k ≤ (trace m i k).fdot ∧ ∃ B, atCut C B = true ∧ C.after B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i k)) ∨
      ((trace m i j).frame = m.frame + 1 ∧ (∀ j', (trace m i j').frame = m.frame → (trace m i j').pc ≠ C.cut) ∧
        ∃ B, endR C B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i j)) := by
    intro j
    induction j with
    | zero =>
      refine Or.inl ⟨A0, hl0, rfl, ?_, fun j' hj' => ?_⟩
      · show m.fdot + 3 * 0 ≤ m.fdot
        omega
      · rw [show j' = 0 by omega]
        exact hp0
    | succ j ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨k, hk1, hk2, hk3, hk4, hk5, hk6⟩ | ⟨h1, h1', B, h2, h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [h2, hh]
        have e : trace m i (j + 1) = (go step (trace m i j)).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i j) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepR H.table hkl hops h1 (hcl j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b2, b3⟩ | ⟨a1, B, a2, a3⟩
        · rw [← e] at a1 a2 a3 a4
          refine Or.inl ⟨A', a1, a2.trans h2, by omega, fun j' hj' => ?_⟩
          by_cases h5 : j' ≤ j
          · exact h4 j' h5
          · rw [show j' = j + 1 by omega]
            exact a3
        · rw [← e] at a1 a2 a3 b3
          exact Or.inr (Or.inl ⟨j + 1, Nat.le_refl _, a2, a1.trans h2, fun j' hj' => h4 j' (by omega), by omega, B, b1, b2, b3⟩)
        · rw [← e] at a1 a3
          have hf1 : (trace m i (j + 1)).frame = m.frame + 1 := by rw [a1, h2]
          refine Or.inr (Or.inr ⟨hf1, fun j' hj' => ?_, B, a2, a3⟩)
          by_cases h5 : j' ≤ j
          · exact h4 j' h5
          · exfalso
            have hst : ((trace m i (j + 1)).frame ≥ m.frame + 1 || (trace m i (j + 1)).halted) = true := by simp [hf1]
            have e2 := PipeEntryRule.trace_stop hst (j' - (j + 1))
            rw [show j + 1 + (j' - (j + 1)) = j' by omega] at e2
            rw [e2, hf1] at hj'
            omega
      · exact Or.inr (Or.inl ⟨k, by omega, hk2, hk3, hk4, hk5, hk6⟩)
      · have hst : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [h1]
        rw [PipeEntryRule.trace_stop hst 1]
        exact Or.inr (Or.inr ⟨h1, h1', B, h2, h3⟩)
  rcases key fuelPerFrame with ⟨A, h1, _, h3, _⟩ | ⟨k, hk1, hk2, hk3, hk4, hk5, hk6⟩ | ⟨_, h1', B, h2, h3⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact Or.inl ⟨k, hk2, hk3, hk1, hk4, hk5, hk6⟩
  · right
    rw [PipeEntryRule.frame_trace]
    exact ⟨h1', B, h2, h3⟩

/-- **One byte, the whole frame.** A frame from the idle loop in control whose instructions meet `CleanK` either comes to the cut (a first time, before its end), or
it ends in a state that the walk covers with `endR`: the followed byte as it began, and the low bit of the pause byte 1. -/
theorem cut_or_end (hO : ctrlCheck1 C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n)) :
    (∃ k, (trace m i k).pc = C.cut ∧ (trace m i k).frame = m.frame ∧ k ≤ fuelPerFrame ∧ ∀ j, j < k → (trace m i j).pc ≠ C.cut) ∨
    ∃ B, endR C B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (frame m i) := by
  rcases cut_or_end2 hO hkl hops hE h0 hcl with ⟨k, h1, h2, h3, h4, _⟩ | ⟨_, h⟩
  · exact Or.inl ⟨k, h1, h2, h3, h4⟩
  · exact Or.inr h

/-- **From the cut to the frame's end**, by a walk of `FrameKeep` (`CA`): the machine `k` instructions into the frame of `m`, covered by a state from which the walk
succeeds, comes to the frame's end in a state with the watched bits of `CA`. Each instruction meets `CleanK` of the guard of `CA`. -/
theorem after_end {CA : FrameKeep.CfgK} {Fu Fu' : Nat} {F : Nat × UInt8} (ht : CA.t.all (FrameKeep.walkK CA Fu) = true) (hkl : CA.kl = CA.t.map knownOf)
    (hops : CA.ops = (aRows CA.E).toArray) (hT : 2 ≤ F.2.toNat) {m : Machine} {i : UInt8} {k : Nat} {A : AS}
    (hw : FrameKeep.walkK CA Fu' A = true) (hs : Sim CA.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK CA.G CA.S.store (trace m i j)) :
    ∃ B, FrameKeep.watchOK CA.W B = true ∧ Sim CA.E F B (frame m i) := by
  have key : ∀ d, (∃ A, FrameKeep.LiveK CA F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK CA.W B = true ∧ Sim CA.E F B (trace m i (k + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases FrameKeep.live_stepK ht hkl hops hT h1 (hcl (k + d)) with ⟨A', a1, _, a3, a4⟩ | ⟨a1, B, a2, _, _, _, a3⟩
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · exact Or.inr ⟨by rw [a1, h2], B, a2, a3⟩
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr ⟨h1, B, h2, h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h3⟩

end

/-! ## The first arrival -/

/-- the first `k < n` with `f k`, or `n` if there is none -/
def firstUpTo (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if firstUpTo f n < n then firstUpTo f n else if f n then n else n + 1

theorem firstUpTo_spec (f : Nat → Bool) : ∀ n, firstUpTo f n ≤ n ∧ (∀ j, j < firstUpTo f n → f j = false) ∧ (firstUpTo f n < n → f (firstUpTo f n) = true) := by
  intro n
  induction n with
  | zero => exact ⟨Nat.le_refl _, fun j h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ n ih =>
    obtain ⟨a1, a2, a3⟩ := ih
    by_cases h : firstUpTo f n < n
    · have e : firstUpTo f (n + 1) = firstUpTo f n := by simp only [firstUpTo, if_pos h]
      rw [e]
      exact ⟨by omega, a2, fun _ => a3 h⟩
    · have e1 : firstUpTo f n = n := by omega
      by_cases hf : f n = true
      · have e : firstUpTo f (n + 1) = n := by simp only [firstUpTo, if_neg h, if_pos hf]
        rw [e]
        exact ⟨by omega, fun j hj => a2 j (by omega), fun _ => hf⟩
      · have e : firstUpTo f (n + 1) = n + 1 := by simp only [firstUpTo, if_neg h, if_neg hf]
        rw [e]
        refine ⟨Nat.le_refl _, fun j hj => ?_, fun h2 => absurd h2 (Nat.lt_irrefl _)⟩
        by_cases hj2 : j < n
        · exact a2 j (by omega)
        · rw [show j = n by omega]
          simpa using hf

/-- the first `k` with `f k` is `firstUpTo f n`, for any `n` after it -/
theorem firstUpTo_eq {f : Nat → Bool} {k n : Nat} (hk : f k = true) (hb : ∀ j, j < k → f j = false) (hn : k < n) : firstUpTo f n = k := by
  obtain ⟨a1, a2, a3⟩ := firstUpTo_spec f n
  by_cases h1 : firstUpTo f n < k
  · have := hb _ h1
    rw [a3 (by omega)] at this
    cases this
  · by_cases h2 : k < firstUpTo f n
    · have := a2 k h2
      rw [hk] at this
      cases this
    · omega

/-- **The instruction at which the frame of `M` with the input `i` first comes to the player's routine** (if it does before `fuelPerFrame + 1` instructions) -/
def arrAt (sy : Syms) (M : Machine) (i : UInt8) : Nat := firstUpTo (fun n => (trace M i n).pc == sy.PlayerCtrlRoutine) (fuelPerFrame + 1)

/-! ## On the ROM -/

section
variable {sy : Syms} {m0 : Machine}

theorem bit80_false_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0x80 != 0) = false → UInt8.ofNat n.val &&& 0x80 = 0 := by decide +kernel

/-- a known bit 7 that is 0 -/
theorem nmi_off_of {b : AB} {x : UInt8} (h : (b.bit 0x80 == some false) = true) (hm : b.mem x) : x &&& 0x80 = 0 := by
  unfold AB.bit at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq, Option.some.injEq] at h hk
    have e : (x &&& b.k) &&& 0x80 = (b.v &&& b.k) &&& 0x80 := by rw [show x &&& b.k = b.v &&& b.k from hm]
    rw [UInt8.and_assoc, UInt8.and_assoc, hk] at e
    rw [e]
    have h1 := bit80_false_all ⟨b.v.toNat, b.v.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h1
    exact h1 (by rw [h])
  · simp at h

/-- a known byte -/
theorem eq_of_known {b : AB} {x : UInt8} (hk : b.isK = true) (hm : b.mem x) : x = b.v := by
  have e : b.k = 0xFF := by simpa [AB.isK] using hk
  have h1 : x &&& b.k = b.v &&& b.k := hm
  rw [e, FrameKeep.and_ff, FrameKeep.and_ff] at h1
  exact h1

/-- **The machine when a frame in control first comes to the player's routine**: it has the bytes of `keepA` of the frame's start, the stack pointer of the player's
routine, no NMI pending and the NMI off, and the routine byte of control. -/
structure AtCut (sy : Syms) (m0 m R : Machine) : Prop where
  keep : ∀ x ∈ keepA sy, peek R x = peek m x
  s : R.s = FrameModel.ctrlStack sy m0
  good : FrameModel.Good (FrameModel.Rom.of m0) R
  eng : peek R sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8

theorem cfg_start (q : Table) (b : Nat) (pw : Bool) {m : Machine} (h0 : FrameKeep.StartK sy m0 m) : FrameStart (cfgOf sy m0 q b pw).G (cfgOf sy m0 q b pw).E m :=
  ⟨h0.pc, h0.s, h0.dot, h0.ctrl, h0.s0, h0.strobe, h0.halted, h0.trk, h0.prg, h0.mask, h0.size, h0.known⟩

/-- **A frame in control, up to the player's routine.** The frame starts in the idle loop in control (`FrameKeep.StartK`) and each instruction meets `FrameKeep.CleanK`.
The first time it comes to the player's routine, in the same frame, it has the bytes of `keepA` it began with, and the state of `FrameModel.AtCtrl0` but the values.
`hc` is the check on the ROM. -/
theorem ctrl_keep (hc : ctrlCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) : AtCut sy m0 m (trace m i k) := by
  unfold ctrlCheck at hc
  generalize cutTable sy m0 false = q at hc
  rw [Bool.and_eq_true] at hc
  have one : ∀ b ∈ keepI sy, ∃ B, atCut (cfgOf sy m0 q b false) B = true ∧ Sim (envR m0 b) (m.frame, m.ram.get! b) B (trace m i k) := by
    intro b hb
    exact at_cut (C := cfgOf sy m0 q b false) ((List.all_eq_true.1 hc.1) b hb) rfl rfl rfl (cfg_start q b false h0) hcl hk hf hfirst
  have hx : (sy.Player_X_Speed &&& 0x7FF).toNat ∈ keepI sy := List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩
  obtain ⟨B, hB, hs⟩ := one _ hx
  simp only [atCut, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hS⟩, hn⟩, hctl⟩, hek⟩, hev⟩ := hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxm
    obtain ⟨B', hB', hs'⟩ := one _ (List.mem_map.2 ⟨x, hxm, rfl⟩)
    simp only [atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB'
    have h1 := hs'.rkv hB'.1.1.1.1.1.1
    rw [if_neg (by simp [hB'.1.1.1.1.1.2])] at h1
    exact h1
  · rw [hs.s]
    exact hS
  · exact ⟨hs.prg, hs.mask, by rw [hs.nmi]; exact hn, hs.halted, hs.trk, hs.size, nmi_off_of (by rw [hctl]; rfl) hs.ppuCtrl⟩
  · have hlt : (sy.GameEngineSubroutine &&& 0x7FF).toNat < 2048 := PipeTransitionAll.mask_lt _
    have h1 := hs.ram _ hlt
    have h2 := eq_of_known hek h1
    show (trace m i k).ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = _
    rw [h2]
    exact hev

theorem low1_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0x01 != 0) = true → UInt8.ofNat n.val &&& 1 = 1 := by decide +kernel

/-- a known low bit that is 1 -/
theorem low_of_bit {b : AB} {x : UInt8} (h : (b.bit 0x01 == some true) = true) (hm : b.mem x) : x &&& 1 = 1 := by
  unfold AB.bit at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq, Option.some.injEq] at h hk
    have e : (x &&& b.k) &&& 0x01 = (b.v &&& b.k) &&& 0x01 := by rw [show x &&& b.k = b.v &&& b.k from hm]
    rw [UInt8.and_assoc, UInt8.and_assoc, hk] at e
    rw [e]
    have h1 := low1_all ⟨b.v.toNat, b.v.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h1
    exact h1 (by rw [h])
  · simp at h

theorem pauseI_lt (sy : Syms) (m0 : Machine) : pauseI sy m0 < 2048 := PipeTransitionAll.mask_lt _

/-- **A frame in control that ends with the game not paused comes to the player's routine.** The frame starts in the idle loop in control and each instruction meets
`CleanK`; if it ends with the low bit of the pause byte 0, it comes to the player's routine before its end, a first time at the instruction `k`. `hc` is the check on the ROM:
every path that does not come to the routine ends with that bit 1. -/
theorem arrive_of (hc : ctrlCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hu : Unpaused sy m0 (frame m i)) :
    ∃ k, (trace m i k).pc = sy.PlayerCtrlRoutine ∧ (trace m i k).frame = m.frame ∧ k ≤ fuelPerFrame ∧
      ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine := by
  unfold ctrlCheck at hc
  generalize cutTable sy m0 true = q at hc
  rw [Bool.and_eq_true] at hc
  rcases cut_or_end (C := cfgOf sy m0 q _ true) hc.2 rfl rfl rfl (cfg_start q _ true h0) hcl with h | ⟨B, hB, hs⟩
  · exact h
  · exfalso
    simp only [endR, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hB
    have hB2 : ((B.getK (pauseI sy m0)).bit 0x01 == some true) = true := by
      rcases hB.2 with h | h
      · cases h
      · exact h
    have h1 : (frame m i).ram.get! (pauseI sy m0) &&& 1 = 1 := low_of_bit hB2 (hs.ram _ (pauseI_lt sy m0))
    have h2 : (frame m i).ram.get! (pauseI sy m0) &&& 1 = 0 := hu
    rw [h1] at h2
    cases h2

/-- the first arrival is `arrAt` -/
theorem arrAt_eq {M : Machine} {i : UInt8} {k : Nat} (hk : (trace M i k).pc = sy.PlayerCtrlRoutine) (hb : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine)
    (hn : k ≤ fuelPerFrame) : arrAt sy M i = k :=
  firstUpTo_eq (by simp [hk]) (fun j hj => by simp [hb j hj]) (by omega)

/-- **The first arrival, at `arrAt`**: a frame in control that ends with the game not paused comes to the player's routine at `arrAt` the first time, before its end -/
theorem arrive_at (hc : ctrlCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hu : Unpaused sy m0 (frame m i)) :
    (trace m i (arrAt sy m i)).pc = sy.PlayerCtrlRoutine ∧ (trace m i (arrAt sy m i)).frame = m.frame ∧
      ∀ j, j < arrAt sy m i → (trace m i j).pc ≠ sy.PlayerCtrlRoutine := by
  obtain ⟨k, h1, h2, h3, h4⟩ := arrive_of hc h0 hcl hu
  rw [arrAt_eq h1 h4 h3]
  exact ⟨h1, h2, h4⟩

/-- **A frame in control that does not come to the player's routine keeps the bytes of `keepA`.** The frame starts in the idle loop in control and each instruction meets
`CleanK`. `hc` is the check on the ROM: on every path that does not come to the routine no instruction writes the followed byte. -/
theorem keep_of_noCut (hc : ctrlCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ keepA sy, peek (frame m i) x = peek m x := by
  unfold ctrlCheck at hc
  generalize cutTable sy m0 false = q at hc
  rw [Bool.and_eq_true] at hc
  intro x hx
  have hb : (x &&& 0x7FF).toNat ∈ keepI sy := List.mem_map.2 ⟨x, hx, rfl⟩
  rcases cut_or_end (C := cfgOf sy m0 q _ false) ((List.all_eq_true.1 hc.1) _ hb) rfl rfl rfl (cfg_start q _ false h0) hcl with ⟨k, h1, h2, _, _⟩ | ⟨B, hB, hs⟩
  · exact absurd h1 (hn k h2)
  · simp only [endR, Bool.and_eq_true, Bool.not_eq_true'] at hB
    have h1 := hs.rkv hB.1.1
    rw [if_neg (by simp [hB.1.2])] at h1
    exact h1

/-! ### The whole frame: from the cut to the frame's end -/

/-- fewer known bits -/
theorem mem_weak {b : AB} {x : UInt8} (w : UInt8) (h : b.mem x) : (⟨b.v &&& w, b.k &&& w⟩ : AB).mem x := by
  show x &&& (b.k &&& w) = (b.v &&& w) &&& (b.k &&& w)
  have h' : x &&& b.k = b.v &&& b.k := h
  rw [← UInt8.and_assoc, h', UInt8.and_assoc, UInt8.and_assoc, UInt8.and_comm w (b.k &&& w), UInt8.and_assoc, UInt8.and_self]

/-- of the bytes of `W`, only the watched bits stay known -/
theorem sim_weakW {E : Env} {F : Nat × UInt8} {m : Machine} : ∀ (W : List FrameKeep.Watch) (A : AS), (∀ w ∈ W, w.1 < 2048) → Sim E F A m →
    Sim E F (W.foldl (fun A w => A.setK w.1 ⟨(A.getK w.1).v &&& w.2.1, (A.getK w.1).k &&& w.2.1⟩) A) m
  | [], _, _, hs => hs
  | w :: W, A, hW, hs => by
    simp only [List.foldl_cons]
    exact sim_weakW W _ (fun x hx => hW x (List.mem_cons_of_mem _ hx)) (PipeEntryRule.sim_setK' hs (mem_weak _ (hs.ram w.1 (hW w List.mem_cons_self))))

/-- the byte is no longer followed: the machine of `FrameKeep` -/
theorem sim_env {b : Nat} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim (envR m0 b) F A m) :
    Sim (PipeEntryRule.envOf m0) (F.1, 2) { A with rk := false, spent := false } m :=
  { hs with rkv := fun h => by cases h }

/-- **The state at the cut, for the walk after it**, covers the machine if the bits of `V` have their values -/
theorem sim_toA {W V : List FrameKeep.Watch} {b : Nat} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim (envR m0 b) F B m) (hW : ∀ w ∈ W, w.1 < 2048)
    (hV : FrameKeep.Watched V m) : Sim (PipeEntryRule.envOf m0) (F.1, 2) (toA W V B) m :=
  sim_env (FrameKeep.sim_watch hV V (fun _ h => h) _ (sim_weakW W B hW hs))

/-- `CleanK` with the bytes `l` protected too -/
theorem cleanK_prot {G : Guard} {l : List Nat} {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK G q m)
    (hs : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ l) : FrameKeep.CleanK { G with prot := l ++ G.prot } q m := by
  refine ⟨fun t ht hq => ?_, hc.read, hc.jump, hc.time⟩
  rcases hc.store t ht hq with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, fun h => (List.mem_append.1 h).elim (hs t ht h1) h2⟩
  · exact Or.inr h1

/-- **`CleanK` with the bytes of `spareI` protected**: `CleanK` and `Spare` -/
theorem cleanP_of {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK (FrameKeep.guardK sy m0) q m) (hs : Spare sy m0 m) :
    FrameKeep.CleanK (guardP sy m0 (spareI sy m0)) q m :=
  cleanK_prot hc hs

theorem watchA_lt (v : UInt8) : ∀ w ∈ watchA sy m0 v, w.1 < 2048 := by
  intro w hw
  simp only [watchA, pauseW, valA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact pauseI_lt sy m0
  · exact PipeTransitionAll.mask_lt _
  · exact PipeTransitionAll.mask_lt _
  · exact PipeTransitionAll.mask_lt _

theorem afterCheck_parts {v : UInt8} (h : afterCheck sy m0 v = true) :
    ctrlCheck1 (cfgPA sy m0 v (cutTable sy m0 true) (afterOf sy m0 v (cutTable sy m0 true))) = true ∧
    (afterOf sy m0 v (cutTable sy m0 true)).t.all (FrameKeep.walkK (afterOf sy m0 v (cutTable sy m0 true)) FrameKeep.fuelK) = true :=
  Eq.mp (Bool.and_eq_true (ctrlCheck1 (cfgPA sy m0 v (cutTable sy m0 true) (afterOf sy m0 v (cutTable sy m0 true))))
    ((afterOf sy m0 v (cutTable sy m0 true)).t.all (FrameKeep.walkK (afterOf sy m0 v (cutTable sy m0 true)) FrameKeep.fuelK))) h

/-- **A frame in control keeps the area's type, the swimming flag and the change of size, and if it comes to the player's routine it ends with the game not paused.** The
frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction meets `CleanK` and `Spare` (no store through an index or a pointer writes the bytes of
`spareI`), and `AreaOK`: the area's type is `v`, the swimming flag 0, the change of size 0. `hc`, `ha` are the checks on the ROM: up to the player's routine the walks
of `ctrlCheck`; from there to the frame's end the walk after the cut, which watches the four bytes. -/
theorem area_end (hc : ctrlCheck sy m0 = true) {v : UInt8} (ha : afterCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsp : ∀ n, Spare sy m0 (trace m i n))
    (hv : AreaOK sy v m) :
    AreaOK sy v (frame m i) ∧ ((∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = sy.PlayerCtrlRoutine) → Unpaused sy m0 (frame m i)) := by
  obtain ⟨ha1, ha2⟩ := afterCheck_parts ha
  generalize cutTable sy m0 true = q at ha1 ha2
  rcases cut_or_end2 (C := cfgPA sy m0 v q (afterOf sy m0 v q)) ha1 rfl rfl rfl (cfg_start q _ true h0) hcl with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hw : FrameKeep.walkK (afterOf sy m0 v q) FrameKeep.fuelK (toA (watchA sy m0 v) (valA sy v) B) = true := hB2
    have A := ctrl_keep hc h0 hcl h1 h2 h4
    have hV : FrameKeep.Watched (valA sy v) (trace m i k) := by
      intro w hw
      simp only [valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [keepA])).trans hv.1
      · show (trace m i k).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [keepA])).trans hv.2.1
      · show (trace m i k).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [keepA])).trans hv.2.2
    have hsA := sim_toA (W := watchA sy m0 v) hs (watchA_lt v) hV
    have hclA : ∀ j, FrameKeep.CleanK (guardP sy m0 (spareI sy m0)) (FrameKeep.spotOf sy m0).store (trace m i j) := fun j => cleanP_of (hcl j) (hsp j)
    obtain ⟨B', hB', hs'⟩ := after_end (CA := afterOf sy m0 v q) (F := (m.frame, 2)) ha2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclA
    have hW := FrameKeep.watched_of hB' hs'
    have e1 := hW _ (List.mem_append_left _ (List.mem_singleton.2 rfl))
    have e2 := hW _ (List.mem_append_right _ (List.mem_cons_self (a := ((sy.AreaType &&& 0x7FF).toNat, (0xFF : UInt8), v))))
    have e3 := hW _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := ((sy.SwimmingFlag &&& 0x7FF).toNat, (0xFF : UInt8), (0 : UInt8))))))
    have e4 := hW _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))))
    simp only [FrameKeep.and_ff] at e2 e3 e4
    refine ⟨⟨e2, e3, e4⟩, fun _ => ?_⟩
    have e1' : (frame m i).ram.get! (pauseI sy m0) &&& 1 = (0 : UInt8) &&& 1 := e1
    exact e1'.trans rfl
  · refine ⟨⟨?_, ?_, ?_⟩, fun ⟨k, hk1, hk2⟩ => absurd hk2 (hno k hk1)⟩
    · rw [keep_of_noCut hc h0 hcl hno _ (by simp [keepA])]
      exact hv.1
    · rw [keep_of_noCut hc h0 hcl hno _ (by simp [keepA])]
      exact hv.2.1
    · rw [keep_of_noCut hc h0 hcl hno _ (by simp [keepA])]
      exact hv.2.2

/-- **A frame in control that ends paused does not come to the player's routine**, under the conditions of `area_end` -/
theorem noCut_of_paused (hc : ctrlCheck sy m0 = true) {v : UInt8} (ha : afterCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsp : ∀ n, Spare sy m0 (trace m i n))
    (hv : AreaOK sy v m) (hp : ¬ Unpaused sy m0 (frame m i)) : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine :=
  fun k h1 h2 => hp ((area_end hc ha h0 hcl hsp hv).2 ⟨k, h1, h2⟩)

end

/-! ## A program: where the walk fails, no part of the proof -/

/-- the walk of `walkR`, returning where it fails first -/
def whyR (C : CfgR) : Nat → AS → Option (String × Nat)
  | 0, A => some ("fuel", A.pc.toNat)
  | n + 1, A => Id.run do
    if A.pc == C.q then return some ("store", A.pc.toNat)
    for A₁ in preL C.G A do
      if isRkDec C.E A₁.pc (opOf C.E A₁) then return some ("dec", A₁.pc.toNat)
      for r in gsucc C.G C.E C.ops A₁ do
        match r with
        | none => return some ("step", A₁.pc.toNat)
        | some B =>
          if A₁.rk && !B.rk then return some (s!"rkdrop x {A₁.x.v}/{A₁.x.k} y {A₁.y.v}/{A₁.y.k}", A₁.pc.toNat)
          if A₁.ppuCtrl.bit 0x80 != none && B.ppuCtrl.bit 0x80 == none then return some ("ctldrop", A₁.pc.toNat)
          if B.k == A.k then
            if B.pc == C.cut then
              if !atCut C B then
                return some (s!"cut rk {B.rk} spent {B.spent} s {B.s}/{C.S} nmi {B.nmi} ctl {B.ppuCtrl.v}/{B.ppuCtrl.k} eng {(B.getK C.engI).v}/{(B.getK C.engI).k}", A₁.pc.toNat)
            else if C.tc.get! B.pc.toNat != 0 && coverR C B then pure ()
            else
              match whyR C n B with
              | some w => return some w
              | none => pure ()
          else if B.k != A.k + 1 then return some ("end", A₁.pc.toNat)
          else if !endR C B then return some (s!"end rk {B.rk} spent {B.spent} pause {(B.getK C.pz).v}/{(B.getK C.pz).k}", A₁.pc.toNat)
    return none

end Smbrta.CtrlKeep
