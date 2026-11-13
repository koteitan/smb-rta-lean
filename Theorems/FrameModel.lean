import Theorems.FrameWalk
import Theorems.Potential
import Theorems.PipeEntryRule

/-!
# A real frame and the horizontal model

`RoomJoin.Follow` and `TopSpeed.Frame` speak of numbers with no link to machines. Here the horizontal state and the position are read from a real machine.

* `move_model`: the run from the player's routine to the scroll handler is `Potential.hstep`, and the move is `P' = P + 16·v'` modulo the size of the position. It is proved for every value of the bytes, by the walks of `FrameWalk.lean`:
  `modelOK` checks them on the ROM, in each case of the buttons and the state.
* `move_masked`: the same with the side he presses masked by a block of Left (`AtCtrl0`): the run is `hstep`, or it leaves the speed 0. `maskOK` checks it on the ROM.
* `clean_frame`: a whole frame `frame M i`, under `Clean`, conditions on that one frame: the state at the player's routine; nothing writes the horizontal bytes before it, or after the scroll handler.
* `frame_read`: a frame is a `TopSpeed.Frame`, under `ReadFrame`, with the same conditions but for the stored speed and the mask, and with `Collide` for the part after the scroll handler.

There is no game data in this file. Page: `0-0/0-3-2-FrameModel.md`.
-/

namespace Smbrta.FrameModel

open Potential (HS HIn hstep hstepN norm)
open TopSpeed (absB)
open TaintRun (AB bt)
open PipeTransition (frame)
open PipeEntryRule (trace trace_stop nxt)

/-- `InFrameN.add` along a machine named by an equation -/
theorem InFrameN.add' {E : Rom} {m m' : Machine} {k1 k2 : Nat} (h1 : InFrameN E m k1) (e : stepN k1 m = m') (h2 : InFrameN E m' k2) : InFrameN E m (k1 + k2) :=
  InFrameN.add h1 (by rw [e]; exact h2)

/-- the RAM index of a byte -/
def I (a : UInt16) : Nat := (a &&& 0x7FF).toNat

/-! ## What a machine says -/

/-- the horizontal state, read from a machine -/
def readHS (sy : Syms) (m : Machine) : HS :=
  { v := peek m sy.Player_X_Speed, f := peek m sy.Player_X_MoveForce, fd := peek m sy.PlayerFacingDir, md := peek m sy.Player_MovingDir,
    rs := if peek m sy.RunningSpeed == 0 then 0 else sy.RunSpeedMin.toUInt8 }

/-- the buttons: B, Up, Down, Left, Right. Select and Start count only as "a button", as Up does -/
def joyOf (raw : UInt8) : UInt8 := (raw &&& 0x4F) ||| (if raw &&& 0x30 != 0 then 8 else 0)

/-- the input of a frame, read from the machine when it comes to the player's routine -/
def readIn (sy : Syms) (m : Machine) : HIn :=
  { st := if peek m sy.Player_State == 0 then 0 else 1,
    jump := peek m sy.Player_State == 0 && peek m sy.SavedJoypadBits &&& 0x80 != 0 && peek m sy.PreviousA_B_Buttons &&& 0x80 == 0,
    joy := joyOf (peek m sy.SavedJoypadBits),
    rt := if peek m sy.RunningTimer == 0 then 0 else 1 }

/-- Left/Right in the model -/
def lrOf (i : HIn) : UInt8 :=
  let lr0 := i.joy &&& 3
  if i.joy &&& 4 != 0 && i.st == 0 && lr0 != 0 then 0 else lr0

/-- `Player_State` in the model -/
def stOf (i : HIn) : UInt8 := if i.st == 0 && i.jump then 1 else i.st

/-- the state `hstep` needs at the player's routine -/
structure AtCtrl (sy : Syms) (E : Rom) (S : UInt8) (m : Machine) : Prop where
  good : Good E m
  pc : m.pc = sy.PlayerCtrlRoutine
  s : m.s = S
  eng : peek m sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8
  area : peek m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  st : peek m sy.Player_State ∈ [(0 : UInt8), 1, 2]
  spring : peek m sy.JumpspringAnimCtrl = 0
  swim : peek m sy.SwimmingFlag = 0
  size : peek m sy.PlayerChangeSizeFlag = 0
  /-- the stored speed is that of the speed: not so right after a hit -/
  abs : peek m sy.Player_XSpeedAbsolute = absB (peek m sy.Player_X_Speed)
  /-- the side he presses is not masked: not so right after a hit -/
  coll : peek m sy.Player_CollisionBits &&& lrOf (norm (readIn sy m)) = lrOf (norm (readIn sy m))

/-- `AtCtrl` but the mask: the side he presses may be masked -/
structure AtCtrl0 (sy : Syms) (E : Rom) (S : UInt8) (m : Machine) : Prop where
  good : Good E m
  pc : m.pc = sy.PlayerCtrlRoutine
  s : m.s = S
  eng : peek m sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8
  area : peek m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  st : peek m sy.Player_State ∈ [(0 : UInt8), 1, 2]
  spring : peek m sy.JumpspringAnimCtrl = 0
  swim : peek m sy.SwimmingFlag = 0
  size : peek m sy.PlayerChangeSizeFlag = 0
  abs : peek m sy.Player_XSpeedAbsolute = absB (peek m sy.Player_X_Speed)

theorem AtCtrl.to0 {sy : Syms} {E : Rom} {S : UInt8} {m : Machine} (h : AtCtrl sy E S m) : AtCtrl0 sy E S m :=
  ⟨h.good, h.pc, h.s, h.eng, h.area, h.st, h.spring, h.swim, h.size, h.abs⟩

/-- with the side he presses not masked, the state is `AtCtrl` -/
theorem AtCtrl0.mk1 {sy : Syms} {E : Rom} {S : UInt8} {m : Machine} (h : AtCtrl0 sy E S m)
    (hc : peek m sy.Player_CollisionBits &&& lrOf (norm (readIn sy m)) = lrOf (norm (readIn sy m))) : AtCtrl sy E S m :=
  ⟨h.good, h.pc, h.s, h.eng, h.area, h.st, h.spring, h.swim, h.size, h.abs, hc⟩

/-! ## The cases -/

/-- what decides the path through the glue -/
structure Case where
  st : UInt8
  raw : UInt8
  prevA : Bool
  area : UInt8
  deriving Inhabited, BEq

def Case.inp (c : Case) (rt : UInt8) : HIn :=
  { st := if c.st == 0 then 0 else 1, jump := c.st == 0 && c.raw &&& 0x80 != 0 && !c.prevA, joy := joyOf c.raw, rt }

/-- the input the model runs on -/
def Case.n (c : Case) : HIn := norm (c.inp 0)

/-! ## The walks of a case -/

/-- the fuel of a long walk, and of a short one. They bound the instructions from the player's routine to the scroll handler -/
def fuelW : Nat := 100
def fuelS : Nat := 48

/-- along the first path, up to `stop` -/
def firstEnd (E : Rom) (stop : UInt16) : Nat → TS → Option TS
  | 0, _ => none
  | f + 1, Q =>
    if Q.pc == stop then some Q
    else
      match tstep E Q with
      | some (q :: _) => firstEnd E stop f q
      | _ => none

/-- along the first path, up to a return -/
def firstRts (E : Rom) : Nat → TS → UInt16
  | 0, _ => 0
  | f + 1, Q =>
    if E.b Q.pc == 0x60 then Q.pc
    else
      match tstep E Q with
      | some (q :: _) => firstRts E f q
      | _ => 0

/-- the live stack, as RAM indices -/
def liveStack (s : UInt8) : List Nat := (List.range (255 - s.toNat)).map fun j => stkI (s + 1 + j.toUInt8)

/-- what is known at the end of the first path, of the listed bytes and the live stack -/
def cutOf (ids : List Nat) (useA useX : Bool) (Q : TS) : Cut :=
  let s := Q.s.getD 0
  { pc := Q.pc, s, K := (ids ++ liveStack s).filterMap (fun i => (Q.ram i).same.map (i, ·)),
    ra := if useA then Q.a.same else none, x := if useX then Q.x.same else none }

/-- the next cut, found by following one path; `pieceOK` checks it on all -/
def nextCut (E : Rom) (ids : List Nat) (useA useX : Bool) (c : Cut) (stop : UInt16) : Cut :=
  match firstEnd E stop fuelW (startQ c) with
  | some Q => cutOf ids useA useX Q
  | none => default

/-- the same cut, after a return address is on the stack and a routine has run to its return -/
def afterLeaf (c : Cut) (r : UInt16) : Cut := { pc := r, s := c.s, K := c.K }

/-- the bytes the glue keeps known -/
def idsG (sy : Syms) : List Nat :=
  [I sy.GameEngineSubroutine, I sy.AreaType, I sy.Player_State, I sy.SavedJoypadBits, I sy.Left_Right_Buttons, I sy.A_B_Buttons,
   I sy.JumpspringAnimCtrl, I sy.SwimmingFlag, I sy.PlayerChangeSizeFlag]

/-- the bytes the glue keeps known at the mover: not those of the case -/
def idsM (sy : Syms) : List Nat := [I sy.GameEngineSubroutine, I sy.JumpspringAnimCtrl, I sy.SwimmingFlag, I sy.PlayerChangeSizeFlag]

/-- the bytes of the horizontal state, the stored speed, the position -/
def watchH (sy : Syms) : List Nat :=
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_XSpeedAbsolute,
   I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce]

/-- the caps and the adder -/
def capsL (sy : Syms) : List Nat := [I sy.MaximumRightSpeed, I sy.MaximumLeftSpeed, I sy.FrictionAdderLow, I sy.FrictionAdderHigh]

/-- the known bytes of a cut, as indices -/
def Cut.ids (c : Cut) : List Nat := c.K.map (·.1)

def Case.c0 (sy : Syms) (S : UInt8) (c : Case) : Cut :=
  { pc := sy.PlayerCtrlRoutine, s := S,
    K := [(I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8), (I sy.AreaType, c.area), (I sy.Player_State, c.st), (I sy.SavedJoypadBits, c.raw),
          (I sy.JumpspringAnimCtrl, 0), (I sy.SwimmingFlag, 0), (I sy.PlayerChangeSizeFlag, 0)],
    B := [(I sy.PreviousA_B_Buttons, ⟨if c.prevA then 0x80 else 0, 0x80⟩)] }

/-- the walks of a case -/
structure Plan where
  c1 : Cut
  r1 : UInt16
  c2 : Cut
  r2 : UInt16
  c3 : Cut
  r3 : UInt16
  c4 : Cut

/-- the state after the glue before `X_Physics`, on the real machine -/
def Case.rst (c : Case) : UInt8 := if c.n.jump then 1 else c.st

/-- the buttons A and B, on the real machine -/
def Case.rab (c : Case) : UInt8 := c.raw &&& 0xC0

/-- the same in the model -/
def habOf (n : HIn) : UInt8 := (n.joy &&& 0x40) ||| (if n.jump then 0x80 else 0)
def hsvOf (n : HIn) : UInt8 := n.joy ||| (if n.jump then 0x80 else 0)

/-- on the ground with no jump and no B, `X_Physics` may read the running timer -/
def Case.gb (c : Case) : Bool := c.st == 0 && !(c.inp 0).jump && (c.inp 0).joy &&& 0x40 == 0

/-- what a walk over a routine needs: the tags -/
def tagsPhys (sy : Syms) (m0 : Machine) (c : Case) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_XSpeedAbsolute, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.GameEngineSubroutine, Tag.kn sy.Eng_PlayerCtrl.toUInt8 sy.Eng_PlayerCtrl.toUInt8), (I sy.AreaType, Tag.kn c.area (peek m0 sy.AreaType)),
   (I sy.Player_State, Tag.kn c.rst (stOf c.n)), (I sy.Left_Right_Buttons, Tag.kn (lrOf c.n) (lrOf c.n)), (I sy.A_B_Buttons, Tag.kn c.rab (habOf c.n)),
   (I sy.RunningTimer, if c.gb then .nz else .any)]

def outPhys (sy : Syms) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_XSpeedAbsolute, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.MaximumRightSpeed, .eq), (I sy.MaximumLeftSpeed, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq)]

def tagsAnim (sy : Syms) (c : Case) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_XSpeedAbsolute, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.MaximumRightSpeed, .eq), (I sy.MaximumLeftSpeed, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq),
   (I sy.SavedJoypadBits, Tag.kn c.raw (hsvOf c.n))]

def outAnim (sy : Syms) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.MaximumRightSpeed, .eq), (I sy.MaximumLeftSpeed, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq)]

def tagsFric (sy : Syms) (m0 : Machine) (lr : UInt8) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.MaximumRightSpeed, .eq), (I sy.MaximumLeftSpeed, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq),
   (I sy.Player_CollisionBits, .ab ⟨lr, lr⟩ (AB.known (peek m0 sy.Player_CollisionBits)))]

def outFric (sy : Syms) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz)]

/-- the place where the next routine is entered -/
def stop2 (sy : Syms) (c : Case) : UInt16 :=
  if stOf c.n == 0 then sy.GetPlayerAnimSpeed else if lrOf c.n != 0 then sy.ImposeFriction else sy.MoveObjectHorizontally

def planOf (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Plan :=
  let E : Rom := { prg := m0.prg, mask := m0.prgMask }
  let c1 := nextCut E (idsG sy) false false (c.c0 sy S) sy.X_Physics
  let r1 := firstRts E fuelW (leafQ sy.X_Physics .any (tagsPhys sy m0 c))
  let st2 := stop2 sy c
  let c2 := nextCut E (if st2 == sy.MoveObjectHorizontally then idsM sy else idsG sy) (st2 == sy.ImposeFriction) (st2 == sy.MoveObjectHorizontally) (afterLeaf c1 r1) st2
  let r2 := firstRts E fuelW (leafQ sy.GetPlayerAnimSpeed .any (tagsAnim sy c))
  let c3 := if st2 == sy.GetPlayerAnimSpeed then nextCut E (I sy.PlayerFacingDir :: idsG sy) true false (afterLeaf c2 r2) sy.ImposeFriction else c2
  let r3 := firstRts E fuelW (leafQ sy.ImposeFriction (Tag.kn (lrOf c.n) (lrOf c.n)) (tagsFric sy m0 (lrOf c.n)))
  let c4 := if st2 == sy.MoveObjectHorizontally then c2 else nextCut E (idsM sy) false true (afterLeaf c3 r3) sy.MoveObjectHorizontally
  { c1, r1, c2, r2, c3, r3, c4 }

/-! ## The checks of a case -/

def Rom.of (m : Machine) : Rom := { prg := m.prg, mask := m.prgMask }

/-- a return that the walk can stop at -/
def isRts (E : Rom) (r : UInt16) : Bool := decide (0x8000 ≤ r) && E.b r == 0x60 && !idleAt E r

/-- the indices of a list are bytes of the RAM, and not those of the stack of the model -/
def tagsOK (sp : UInt8) (L : List (Nat × Tag)) : Bool :=
  L.all fun p => decide (p.1 < 2048) && p.1 != stkI sp && p.1 != stkI (sp - 1)

/-- the two bytes of the stack of `runSub` -/
def hStack (sp : UInt8) : List Nat := [stkI sp, stkI (sp - 1)]

/-- the walk over a routine, with what `leaf_spec` asks -/
def leafAll (E : Rom) (sp : UInt8) (entry r : UInt16) (a : Tag) (L Lo : List (Nat × Tag)) (watch : List Nat) : Bool :=
  isRts E r && tagsOK sp L && leafOK E entry r a L Lo (hStack sp ++ watch) fuelS

/-- bytes the glue from `X_Physics` to the next routine keeps -/
def watchA (sy : Syms) : List Nat := I sy.SavedJoypadBits :: (watchH sy ++ capsL sy)

/-- the list of bytes after `Friction`'s return -/
def watchM (sy : Syms) : List Nat :=
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce]

/-- what the walks of the ground need -/
def groundOK (sy : Syms) (m0 : Machine) (c : Case) (P : Plan) : Bool :=
  let E := Rom.of m0
  let lr := lrOf c.n
  P.c2.pc == sy.GetPlayerAnimSpeed && pieceOK E (afterLeaf P.c1 P.r1) P.c2 (watchA sy) fuelS &&
  leafAll E m0.s sy.GetPlayerAnimSpeed P.r2 .any (tagsAnim sy c) (outAnim sy)
    ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy ++ P.c2.ids) &&
  pieceOK E (afterLeaf P.c2 P.r2) P.c3
    ([I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy ++
      (if lr != 0 then [] else [I sy.PlayerFacingDir])) fuelS &&
  (lr == 0 || P.c3.K.contains (I sy.PlayerFacingDir, lr))

/-- the walks of `ImposeFriction`, and on to the mover -/
def fricOK (sy : Syms) (m0 : Machine) (c : Case) (P : Plan) : Bool :=
  let E := Rom.of m0
  let lr := lrOf c.n
  P.c3.ra == some lr && P.c3.pc == sy.ImposeFriction &&
  leafAll E m0.s sy.ImposeFriction P.r3 (Tag.kn lr lr) (tagsFric sy m0 lr) (outFric sy)
    ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ P.c3.ids) &&
  pieceOK E (afterLeaf P.c3 P.r3) P.c4 (watchM sy) fuelS

/-- a case with its walks. Which walks depends on the path of the case: on the ground, in the air with Left or Right, in the air with neither -/
def caseOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  let E := Rom.of m0
  let P := planOf sy m0 S c
  let lr := lrOf c.n
  -- the player's routine to `X_Physics`
  pieceOK E (c.c0 sy S) P.c1 (I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy) fuelW &&
  P.c1.pc == sy.X_Physics && P.c1.K.contains (I sy.Player_State, c.rst) && P.c1.K.contains (I sy.Left_Right_Buttons, lr) && P.c1.K.contains (I sy.A_B_Buttons, c.rab) &&
  P.c1.K.contains (I sy.AreaType, c.area) && P.c1.K.contains (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) &&
  -- `X_Physics`
  leafAll E m0.s sy.X_Physics P.r1 .any (tagsPhys sy m0 c) (outPhys sy) (I sy.SavedJoypadBits :: (watchH sy ++ P.c1.ids)) &&
  (if stOf c.n == 0 then groundOK sy m0 c P && fricOK sy m0 c P
   else if lr != 0 then pieceOK E (afterLeaf P.c1 P.r1) P.c3 (watchA sy) fuelS && fricOK sy m0 c P
   else pieceOK E (afterLeaf P.c1 P.r1) P.c4 (watchA sy) fuelS) &&
  P.c4.pc == sy.MoveObjectHorizontally && P.c4.x == some 0

/-- the cases -/
def allCases : List Case :=
  [(0 : UInt8), 1, 2].flatMap fun st => [(1 : UInt8), 2, 3].flatMap fun area => [false, true].flatMap fun prevA =>
    (List.range 256).map fun r => { st, raw := r.toUInt8, prevA, area }

/-! ## The move -/

/-- the first address from `a` on, within `n` bytes, where the bytes `pat` are -/
def findPat (E : Rom) (a : UInt16) (pat : List UInt8) : Nat → UInt16
  | 0 => a
  | n + 1 =>
    if ((List.range pat.length).all fun j => E.b (a + j.toUInt16) == pat.getD j 0) then a else findPat E (a + 1) pat n

/-- the places in the mover: the load of the fraction, of the position, of the page; the place after them; and where the moving direction is set -/
structure MoveSites where
  sF : UInt16
  sX : UInt16
  sP : UInt16
  sD : UInt16
  sV : UInt16
  /-- the temporary bytes with the three digits of `16·v` -/
  iL : Nat
  iD : Nat
  iE : Nat
  deriving Inhabited

def sitesOf (sy : Syms) (E : Rom) : MoveSites :=
  let lo := sy.SprObject_X_MoveForce.toUInt8
  let hi := (sy.SprObject_X_MoveForce >>> 8).toUInt8
  let sF := findPat E sy.MoveObjectHorizontally [0xBD, lo, hi] 64
  let sX := findPat E sF [0xB5, sy.Player_X_Position.toUInt8] 32
  let sP := findPat E sX [0xB5, sy.Player_PageLoc.toUInt8] 32
  let sV := findPat E sy.PlayerCtrlRoutine [0xA4, sy.Player_X_Speed.toUInt8] 128 - 2
  { sF, sX, sP, sD := sP + 6, sV, iL := (E.b (sF + 5)).toNat, iD := (E.b (sX + 3)).toNat, iE := (E.b (sP + 3)).toNat }

/-- the three digits of `16·v` -/
def lOf (v : UInt8) : UInt8 := v <<< 4
def dOf (v : UInt8) : UInt8 := if v < 0x80 then v >>> 4 else (v >>> 4) ||| 0xF0
def eOf (v : UInt8) : UInt8 := if v < 0x80 then 0 else 0xFF

/-- the digits are those of `16·v`, modulo the size of the position -/
def digitsOK : Bool :=
  TopSpeed.bytes.all fun v => ((lOf v).toNat + 256 * (dOf v).toNat + 65536 * (eOf v).toNat - 16 * sbyte v) % 0x1000000 == 0

/-- the bytes that the mover keeps -/
def keepM (sy : Syms) (c4 : Cut) : List Nat :=
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed] ++ c4.ids

/-- the cut before the moving direction is set -/
def cutV (sy : Syms) (E : Rom) (c4 : Cut) : Cut :=
  let M := sitesOf sy E
  let c := nextCut E [] false false { pc := M.sD, s := c4.s - 1, K := c4.K } M.sV
  { pc := c.pc, s := c.s, K := [] }

/-- the walks of the mover, for every value of the bytes it reads, and from it to the scroll handler -/
def tailOK (sy : Syms) (E : Rom) (c4 : Cut) : Bool :=
  let M := sitesOf sy E
  let bs := TopSpeed.bytes
  let v := I sy.Player_X_Speed
  let mf := I sy.SprObject_X_MoveForce
  let xI := I sy.Player_X_Position
  let pI := I sy.Player_PageLoc
  let keep := keepM sy c4
  let s1 := c4.s - 1
  let cv := cutV sy E c4
  decide (M.iL < 2048) && decide (M.iD < 2048) && decide (M.iE < 2048) && decide (mf < 2048) && decide (xI < 2048) && decide (pI < 2048) &&
  c4.x == some 0 && c4.B.isEmpty && c4.K.all (fun p => decide (p.1 < 2048)) && M.iL != M.iD && M.iL != M.iE && M.iD != M.iE &&
  bs.all (fun b => pieceOK E { c4 with K := (v, b) :: c4.K } { pc := M.sF, s := c4.s, K := (M.iL, lOf b) :: (M.iD, dOf b) :: (M.iE, eOf b) :: c4.K, x := some 0 } (mf :: xI :: pI :: keep) fuelS) &&
  bs.all (fun f => bs.all fun l =>
    pieceOK E { pc := M.sF, s := c4.s, K := [(mf, f), (M.iL, l)], x := some 0 }
      { pc := M.sX, s := s1, K := [(mf, (adcC f l false).1)], x := some 0, cf := some (adcC f l false).2 } (M.iD :: M.iE :: xI :: pI :: keep) fuelS) &&
  bs.all (fun x => bs.all fun d => [false, true].all fun c =>
    pieceOK E { pc := M.sX, s := s1, K := [(xI, x), (M.iD, d)], x := some 0, cf := some c }
      { pc := M.sP, s := s1, K := [(xI, (adcC x d c).1)], x := some 0, cf := some (adcC x d c).2 } (mf :: M.iE :: pI :: keep) fuelS) &&
  bs.all (fun p => bs.all fun e => [false, true].all fun c =>
    pieceOK E { pc := M.sP, s := s1, K := [(pI, p), (M.iE, e)], x := some 0, cf := some c }
      { pc := M.sD, s := s1, K := [(pI, (adcC p e c).1)] } (mf :: xI :: keep) fuelS) &&
  pieceOK E { pc := M.sD, s := s1, K := c4.K } cv [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, mf, xI, pI] fuelW &&
  bs.all (fun b =>
    pieceOK E { pc := cv.pc, s := cv.s, K := [(v, b)] }
      { pc := sy.PlayerSubs, s := cv.s, K := if b == 0 then [] else [(I sy.Player_MovingDir, if b < 0x80 then 1 else 2)] }
      ([I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.RunningSpeed, mf, xI, pI] ++ if b == 0 then [I sy.Player_MovingDir] else []) fuelS)

theorem adcC_nat (a v : UInt8) (c : Bool) : (adcC a v c).1.toNat + 256 * (if (adcC a v c).2 then 1 else 0) = a.toNat + v.toNat + (if c then 1 else 0) := by
  have h1 := a.toNat_lt
  have h2 := v.toNat_lt
  have hs : (a.toUInt16 + v.toUInt16 + (cB c).toUInt16).toNat = a.toNat + v.toNat + (if c then 1 else 0) := by
    simp only [UInt16.toNat_add, UInt8.toNat_toUInt16]
    cases c
    · simp only [Bool.false_eq_true, if_false]
      show ((a.toNat + v.toNat) % 2 ^ 16 + (0 : UInt8).toNat) % 2 ^ 16 = _
      simp
      omega
    · simp only [if_true]
      show ((a.toNat + v.toNat) % 2 ^ 16 + (1 : UInt8).toNat) % 2 ^ 16 = _
      simp
      omega
  have e1 : (adcC a v c).1 = (a.toUInt16 + v.toUInt16 + (cB c).toUInt16).toUInt8 := rfl
  have e2 : (adcC a v c).2 = decide (a.toUInt16 + v.toUInt16 + (cB c).toUInt16 > 0xFF) := rfl
  rw [e1, e2]
  generalize a.toUInt16 + v.toUInt16 + (cB c).toUInt16 = s at hs
  have h3 : s.toUInt8.toNat = s.toNat % 256 := by simp
  have h4 : (s > 0xFF) ↔ 255 < s.toNat := by
    constructor
    · intro h
      exact UInt16.lt_iff_toNat_lt.1 h
    · intro h
      exact UInt16.lt_iff_toNat_lt.2 h
  rw [h3]
  have hc : (if c = true then 1 else 0 : Nat) ≤ 1 := by split <;> omega
  generalize (if c = true then 1 else 0 : Nat) = u at hs hc ⊢
  by_cases h5 : 255 < s.toNat
  · have h6 : decide (s > 0xFF) = true := decide_eq_true (h4.2 h5)
    rw [h6]
    simp only [if_true]
    omega
  · have h6 : decide (s > 0xFF) = false := decide_eq_false (fun h => h5 (h4.1 h))
    rw [h6]
    simp only [Bool.false_eq_true, if_false]
    omega

/-! ### The mover, on a real machine -/

section tail
variable {sy : Syms} {E : Rom}

/-- the position, as digits -/
def posOf (p x f : UInt8) : Int := ((p.toNat : Int) * 256 + (x.toNat : Int)) * 256 + (f.toNat : Int)

theorem posP_eq (sy : Syms) (m : Machine) : posP sy m = posOf (peek m sy.Player_PageLoc) (peek m sy.Player_X_Position) (peek m sy.SprObject_X_MoveForce) := rfl

theorem I_lt (a : UInt16) : I a < 2048 := PipeTransitionAll.mask_lt a

/-- a change of `P` by digits -/
theorem pos_digits {p x f l d e : UInt8} {b1 b2 : Bool} {f' x' p' : UInt8} {sv : Int}
    (h1 : (adcC f l false).1 = f') (h2 : (adcC f l false).2 = b1) (h3 : (adcC x d b1).1 = x') (h4 : (adcC x d b1).2 = b2) (h5 : (adcC p e b2).1 = p')
    (hd : (l.toNat + 256 * d.toNat + 65536 * e.toNat - sv) % 0x1000000 = 0) : (posOf p' x' f' - posOf p x f - sv) % 0x1000000 = 0 := by
  have n1 := adcC_nat f l false
  have n2 := adcC_nat x d b1
  have n3 := adcC_nat p e b2
  rw [h1, h2] at n1
  rw [h3, h4] at n2
  rw [h5] at n3
  simp only [Bool.false_eq_true, if_false] at n1
  generalize (if b1 = true then 1 else 0) = u1 at n1 n2
  generalize (if b2 = true then 1 else 0) = u2 at n2 n3
  generalize (if (adcC p e b2).2 = true then 1 else 0) = u3 at n3
  unfold posOf
  omega

/-- the mover and the glue after it, on a real machine -/
theorem tail_spec {c4 : Cut} {R : Machine} (hc : tailOK sy E c4 = true) (hd : digitsOK = true) (h : At E c4 R) :
    ∃ k, k ≤ fuelW + 5 * fuelS ∧ Good E (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧
      (stepN k R).ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) ∧
      (stepN k R).ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) ∧
      (stepN k R).ram.get! (I sy.PlayerFacingDir) = R.ram.get! (I sy.PlayerFacingDir) ∧
      (stepN k R).ram.get! (I sy.RunningSpeed) = R.ram.get! (I sy.RunningSpeed) ∧
      (stepN k R).ram.get! (I sy.Player_MovingDir) =
        (if R.ram.get! (I sy.Player_X_Speed) == 0 then R.ram.get! (I sy.Player_MovingDir) else if R.ram.get! (I sy.Player_X_Speed) < 0x80 then 1 else 2) ∧
      (posP sy (stepN k R) - posP sy R - 16 * sbyte (R.ram.get! (I sy.Player_X_Speed))) % 0x1000000 = 0 ∧ InFrameN E R k := by
  simp only [tailOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hiL, hiD⟩, hiE⟩, hmf⟩, hxI⟩, hpI⟩, hx0⟩, _⟩, hK⟩, _⟩, _⟩, _⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := hc
  have hb := fun (b : UInt8) => Potential.mem_bytes b
  generalize hM : sitesOf sy E = M at a7 a8 a9 a10 a11 a12 hiL hiD hiE
  have hcv : cutV sy E c4 = cutV sy E c4 := rfl
  generalize cutV sy E c4 = cv at a11 a12 hcv
  generalize hb0 : R.ram.get! (I sy.Player_X_Speed) = b
  -- the digits
  have hA1 : At E { c4 with K := (I sy.Player_X_Speed, b) :: c4.K } R := by
    refine ⟨h.good, h.pc, h.s, ?_, h.B, h.ra, h.x, h.cf⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hb0
    · exact h.K p hp
  obtain ⟨k1, f1, A1, W1, _, C1⟩ := piece_spec (a7 b (hb b)) hA1
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have hWk1 : ∀ i ∈ keepM sy c4, i < 2048 → R1.ram.get! i = R.ram.get! i := fun i hi hl =>
    W1 i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))) hl
  have hL : R1.ram.get! M.iL = lOf b := A1.K (M.iL, lOf b) List.mem_cons_self
  have hD1 : R1.ram.get! M.iD = dOf b := A1.K (M.iD, dOf b) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hE1 : R1.ram.get! M.iE = eOf b := A1.K (M.iE, eOf b) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hC1 : ∀ p ∈ c4.K, R1.ram.get! p.1 = p.2 := fun p hp => A1.K p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
  have hmf1 : R1.ram.get! (I sy.SprObject_X_MoveForce) = R.ram.get! (I sy.SprObject_X_MoveForce) := W1 _ List.mem_cons_self (I_lt _)
  have hx1 : R1.ram.get! (I sy.Player_X_Position) = R.ram.get! (I sy.Player_X_Position) := W1 _ (List.mem_cons_of_mem _ List.mem_cons_self) (I_lt _)
  have hp1 : R1.ram.get! (I sy.Player_PageLoc) = R.ram.get! (I sy.Player_PageLoc) := W1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (I_lt _)
  generalize hf0 : R.ram.get! (I sy.SprObject_X_MoveForce) = f0 at hmf1
  generalize hx0' : R.ram.get! (I sy.Player_X_Position) = x0 at hx1
  generalize hp0 : R.ram.get! (I sy.Player_PageLoc) = p0 at hp1
  -- the fraction
  have hA2 : At E { pc := M.sF, s := c4.s, K := [(I sy.SprObject_X_MoveForce, f0), (M.iL, lOf b)], x := some 0 } R1 := by
    refine ⟨A1.good, A1.pc, A1.s, ?_, ?_, ?_, A1.x, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hmf1
      · rcases List.mem_singleton.1 hp with rfl
        exact hL
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      cases hv
  obtain ⟨k2, f2, A2, W2, _, C2⟩ := piece_spec (a8 f0 (hb f0) (lOf b) (hb _)) hA2
  generalize hR2 : stepN k2 R1 = R2 at A2 W2
  have hWk2 : ∀ i ∈ keepM sy c4, i < 2048 → R2.ram.get! i = R1.ram.get! i := fun i hi hl =>
    W2 i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)))) hl
  have hmf2 : R2.ram.get! (I sy.SprObject_X_MoveForce) = (adcC f0 (lOf b) false).1 := A2.K _ List.mem_cons_self
  have hD2 : R2.ram.get! M.iD = dOf b := by rw [W2 _ List.mem_cons_self hiD]; exact hD1
  have hE2 : R2.ram.get! M.iE = eOf b := by rw [W2 _ (List.mem_cons_of_mem _ List.mem_cons_self) hiE]; exact hE1
  have hx2 : R2.ram.get! (I sy.Player_X_Position) = x0 := by
    rw [W2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (I_lt _)]
    exact hx1
  have hp2 : R2.ram.get! (I sy.Player_PageLoc) = p0 := by
    rw [W2 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (I_lt _)]
    exact hp1
  have hc1 : bt R2.p 0 = (adcC f0 (lOf b) false).2 := A2.cf _ rfl
  -- the position
  have hA3 : At E { pc := M.sX, s := c4.s - 1, K := [(I sy.Player_X_Position, x0), (M.iD, dOf b)], x := some 0, cf := some (adcC f0 (lOf b) false).2 } R2 := by
    refine ⟨A2.good, A2.pc, A2.s, ?_, ?_, ?_, A2.x, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hx2
      · rcases List.mem_singleton.1 hp with rfl
        exact hD2
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      have e := Option.some.inj hv
      rw [← e]
      exact hc1
  obtain ⟨k3, f3, A3, W3, _, C3⟩ := piece_spec (a9 x0 (hb x0) (dOf b) (hb _) (adcC f0 (lOf b) false).2 (by cases (adcC f0 (lOf b) false).2 <;> simp)) hA3
  generalize hR3 : stepN k3 R2 = R3 at A3 W3
  have hWk3 : ∀ i ∈ keepM sy c4, i < 2048 → R3.ram.get! i = R2.ram.get! i := fun i hi hl =>
    W3 i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))) hl
  have hmf3 : R3.ram.get! (I sy.SprObject_X_MoveForce) = (adcC f0 (lOf b) false).1 := by
    rw [W3 _ List.mem_cons_self (I_lt _)]
    exact hmf2
  have hE3 : R3.ram.get! M.iE = eOf b := by rw [W3 _ (List.mem_cons_of_mem _ List.mem_cons_self) hiE]; exact hE2
  have hp3 : R3.ram.get! (I sy.Player_PageLoc) = p0 := by
    rw [W3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (I_lt _)]
    exact hp2
  have hx3 : R3.ram.get! (I sy.Player_X_Position) = (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).1 := A3.K _ List.mem_cons_self
  have hc2 : bt R3.p 0 = (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).2 := A3.cf _ rfl
  -- the page
  have hA4 : At E { pc := M.sP, s := c4.s - 1, K := [(I sy.Player_PageLoc, p0), (M.iE, eOf b)], x := some 0, cf := some (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).2 } R3 := by
    refine ⟨A3.good, A3.pc, A3.s, ?_, ?_, ?_, A3.x, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hp3
      · rcases List.mem_singleton.1 hp with rfl
        exact hE3
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      have e := Option.some.inj hv
      rw [← e]
      exact hc2
  obtain ⟨k4, f4, A4, W4, _, C4⟩ := piece_spec (a10 p0 (hb p0) (eOf b) (hb _) (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).2 (by cases (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).2 <;> simp)) hA4
  generalize hR4 : stepN k4 R3 = R4 at A4 W4
  have hWk4 : ∀ i ∈ keepM sy c4, i < 2048 → R4.ram.get! i = R3.ram.get! i := fun i hi hl =>
    W4 i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)) hl
  have hmf4 : R4.ram.get! (I sy.SprObject_X_MoveForce) = (adcC f0 (lOf b) false).1 := by
    rw [W4 _ List.mem_cons_self (I_lt _)]
    exact hmf3
  have hx4 : R4.ram.get! (I sy.Player_X_Position) = (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).1 := by
    rw [W4 _ (List.mem_cons_of_mem _ List.mem_cons_self) (I_lt _)]
    exact hx3
  have hp4 : R4.ram.get! (I sy.Player_PageLoc) = (adcC p0 (eOf b) (adcC x0 (dOf b) (adcC f0 (lOf b) false).2).2).1 := A4.K _ List.mem_cons_self
  have chain : ∀ i ∈ keepM sy c4, i < 2048 → R4.ram.get! i = R1.ram.get! i := fun i hi hl => by
    rw [hWk4 i hi hl, hWk3 i hi hl, hWk2 i hi hl]
  -- to where the moving direction is set
  have hA5 : At E { pc := M.sD, s := c4.s - 1, K := c4.K } R4 := by
    refine ⟨A4.good, A4.pc, A4.s, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rw [chain p.1 (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK p hp)]
      exact hC1 p hp
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      cases hv
    · intro v hv
      cases hv
  obtain ⟨k5, f5, A5, W5, _, C5⟩ := piece_spec a11 hA5
  generalize hR5 : stepN k5 R4 = R5 at A5 W5
  have hk : ∀ i ∈ keepM sy c4, i < 2048 → R4.ram.get! i = R.ram.get! i := fun i hi hl => by
    rw [chain i hi hl, hWk1 i hi hl]
  have hvk : I sy.Player_X_Speed ∈ keepM sy c4 := by simp [keepM]
  have hfk : I sy.Player_X_MoveForce ∈ keepM sy c4 := by simp [keepM]
  have hdk : I sy.PlayerFacingDir ∈ keepM sy c4 := by simp [keepM]
  have hmk : I sy.Player_MovingDir ∈ keepM sy c4 := by simp [keepM]
  have hrk : I sy.RunningSpeed ∈ keepM sy c4 := by simp [keepM]
  have hv5 : R5.ram.get! (I sy.Player_X_Speed) = b := by
    rw [W5 _ (by simp) (I_lt _), hk _ hvk (I_lt _)]
    exact hb0
  -- the moving direction
  have hA6 : At E { pc := cv.pc, s := cv.s, K := [(I sy.Player_X_Speed, b)] } R5 := by
    refine ⟨A5.good, A5.pc, A5.s, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_singleton.1 hp with rfl
      exact hv5
    · intro p hp
      cases hp
    · intro v hv
      cases hv
    · intro v hv
      cases hv
    · intro v hv
      cases hv
  obtain ⟨k6, f6, A6, W6, _, C6⟩ := piece_spec (a12 b (hb b)) hA6
  generalize hR6 : stepN k6 R5 = R6 at A6 W6
  have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = R6 := by
    rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5, hR6]
  have w6 : ∀ i, i ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.RunningSpeed, I sy.SprObject_X_MoveForce, I sy.Player_X_Position, I sy.Player_PageLoc] → i < 2048 → R6.ram.get! i = R5.ram.get! i :=
    fun i hi hl => W6 i (List.mem_append_left _ hi) hl
  have w5 : ∀ i, i ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.SprObject_X_MoveForce, I sy.Player_X_Position, I sy.Player_PageLoc] → i < 2048 → R5.ram.get! i = R4.ram.get! i :=
    fun i hi hl => W5 i hi hl
  have hdig := hd
  simp only [digitsOK, List.all_eq_true, beq_iff_eq] at hdig
  refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 (InFrameN.add' C4 hR4 (InFrameN.add' C5 hR5 C6))))⟩
  · omega
  · rw [hfin]
    exact A6.good
  · rw [hfin]
    exact A6.pc
  · rw [hfin, w6 _ (by simp) (I_lt _), hv5]
  · rw [hfin, w6 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), hk _ hfk (I_lt _)]
  · rw [hfin, w6 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), hk _ hdk (I_lt _)]
  · rw [hfin, w6 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), hk _ hrk (I_lt _)]
  · rw [hfin]
    by_cases hb1 : b = 0
    · have hb2 : (b == 0) = true := beq_iff_eq.2 hb1
      have e6 : R6.ram.get! (I sy.Player_MovingDir) = R5.ram.get! (I sy.Player_MovingDir) := by
        refine W6 _ (List.mem_append_right _ ?_) (I_lt _)
        rw [if_pos hb1]
        exact List.mem_cons_self
      rw [e6, w5 _ (by simp) (I_lt _), hk _ hmk (I_lt _), if_pos hb2]
    · have hb2 : ¬ (b == 0) = true := fun e => hb1 (beq_iff_eq.1 e)
      have e6 := A6.K (I sy.Player_MovingDir, if b < 0x80 then 1 else 2) (by
        show _ ∈ (if b = 0 then [] else [_])
        rw [if_neg hb1]
        exact List.mem_cons_self)
      rw [e6, if_neg hb2]
  · rw [hfin, posP_eq, posP_eq]
    show (posOf (R6.ram.get! (I sy.Player_PageLoc)) (R6.ram.get! (I sy.Player_X_Position)) (R6.ram.get! (I sy.SprObject_X_MoveForce)) -
      posOf (R.ram.get! (I sy.Player_PageLoc)) (R.ram.get! (I sy.Player_X_Position)) (R.ram.get! (I sy.SprObject_X_MoveForce)) - 16 * sbyte b) % 0x1000000 = 0
    rw [w6 _ (by simp) (I_lt _), w6 _ (by simp) (I_lt _), w6 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), w5 _ (by simp) (I_lt _), hp4, hx4, hmf4, hf0, hx0', hp0]
    exact pos_digits rfl rfl rfl rfl rfl (hdig b (hb b))

end tail

/-! ## The model, unfolded -/

/-- the pokes of `hstepN`, in its order -/
def hsL (sy : Syms) (s : HS) (i : HIn) : List (UInt16 × UInt8) :=
  [(sy.Player_State, stOf i), (sy.Player_X_Speed, s.v), (sy.Player_X_MoveForce, s.f), (sy.Player_XSpeedAbsolute, absB s.v), (sy.PlayerFacingDir, s.fd),
   (sy.Player_MovingDir, s.md), (sy.RunningSpeed, s.rs), (sy.RunningTimer, i.rt), (sy.Left_Right_Buttons, lrOf i),
   (sy.A_B_Buttons, habOf i), (sy.SavedJoypadBits, hsvOf i), (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8)]

/-- the indices of the pokes -/
def pokeIdx (sy : Syms) : List Nat :=
  [I sy.Player_State, I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_XSpeedAbsolute, I sy.PlayerFacingDir,
   I sy.Player_MovingDir, I sy.RunningSpeed, I sy.RunningTimer, I sy.Left_Right_Buttons, I sy.A_B_Buttons, I sy.SavedJoypadBits, I sy.GameEngineSubroutine]

def pokeL (m : Machine) : List (UInt16 × UInt8) → Machine
  | [] => m
  | p :: l => pokeL (poke m p.1 p.2) l

/-- `hstepN` up to its last reads -/
def midH (sy : Syms) (m0 : Machine) (s : HS) (i : HIn) : Machine :=
  let A := runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0
  if stOf i == 0 then
    let B := runSub A sy.GetPlayerAnimSpeed 0 0 0
    runSub (if lrOf i != 0 then poke B sy.PlayerFacingDir (lrOf i) else B) sy.ImposeFriction (lrOf i) 0 0
  else if lrOf i != 0 then runSub A sy.ImposeFriction (lrOf i) 0 0 else A

/-- the last reads of `hstepN` -/
def finishH (sy : Syms) (m : Machine) : HS :=
  { v := peek m sy.Player_X_Speed, f := peek m sy.Player_X_MoveForce, fd := peek m sy.PlayerFacingDir,
    md := if peek m sy.Player_X_Speed == 0 then peek m sy.Player_MovingDir else if peek m sy.Player_X_Speed < 0x80 then 1 else 2,
    rs := if peek m sy.RunningSpeed == 0 then 0 else sy.RunSpeedMin.toUInt8 }

theorem poke_eq (m : Machine) (a : UInt16) (v : UInt8) : poke m a v = { m with ram := m.ram.set! (I a) v } := rfl

theorem hstepN_eq (sy : Syms) (m0 : Machine) (s : HS) (i : HIn) : hstepN sy m0 s i = finishH sy (midH sy m0 s i) := by
  simp only [hstepN, finishH, midH, lrOf, stOf, hsL, pokeL, habOf, hsvOf]

theorem poke_get_self {m : Machine} (a : UInt16) (v : UInt8) (h : m.ram.size = 2048) : (poke m a v).ram.get! (I a) = v := by
  rw [poke_eq]
  exact PipeTransitionAll.ba_get_set_self _ _ _ (by rw [h]; exact I_lt a)

theorem poke_get_ne (m : Machine) (a : UInt16) (v : UInt8) {i : Nat} (h : I a ≠ i) : (poke m a v).ram.get! i = m.ram.get! i := by
  rw [poke_eq]
  exact PipeTransitionAll.ba_get_set_ne _ _ _ _ h

theorem poke_good {E : Rom} {m : Machine} (a : UInt16) (v : UInt8) (g : GoodH E m) : GoodH E (poke m a v) := by
  rw [poke_eq]
  refine ⟨g.prg, g.mask, g.halted, g.trk, ?_⟩
  show (m.ram.set! _ _).size = 2048
  rw [PipeTransitionAll.ba_size_set]
  exact g.size

theorem poke_s (m : Machine) (a : UInt16) (v : UInt8) : (poke m a v).s = m.s := rfl

theorem pokeL_good {E : Rom} : ∀ (l : List (UInt16 × UInt8)) {m : Machine}, GoodH E m → GoodH E (pokeL m l)
  | [], _, g => g
  | p :: l, _, g => pokeL_good l (poke_good p.1 p.2 g)

theorem pokeL_s : ∀ (l : List (UInt16 × UInt8)) (m : Machine), (pokeL m l).s = m.s
  | [], _ => rfl
  | p :: l, m => by
    show (pokeL (poke m p.1 p.2) l).s = _
    rw [pokeL_s l]
    rfl

theorem pokeL_out {i : Nat} : ∀ (l : List (UInt16 × UInt8)) (m : Machine), (∀ p ∈ l, I p.1 ≠ i) → (pokeL m l).ram.get! i = m.ram.get! i
  | [], _, _ => rfl
  | p :: l, m, h => by
    show (pokeL (poke m p.1 p.2) l).ram.get! i = _
    rw [pokeL_out l _ (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    exact poke_get_ne _ _ _ (h p List.mem_cons_self)

/-- no index twice -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: l => !l.contains x && nodupB l

theorem pokeL_get {E : Rom} : ∀ (l : List (UInt16 × UInt8)) (m : Machine), GoodH E m → nodupB (l.map fun p => I p.1) = true →
    ∀ p ∈ l, (pokeL m l).ram.get! (I p.1) = p.2
  | [], _, _, _, _, hp => by cases hp
  | q :: l, m, g, hd, p, hp => by
    simp only [List.map_cons, nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map, not_exists, not_and] at hd
    show (pokeL (poke m q.1 q.2) l).ram.get! _ = _
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [pokeL_out l _ (fun r hr => hd.1 r hr)]
      exact poke_get_self _ _ g.size
    · exact pokeL_get l _ (poke_good _ _ g) hd.2 p hp

/-- what `m0` must be -/
def baseOK (m0 : Machine) : Bool := !m0.halted && !m0.trk && m0.ram.size == 2048

theorem base_good {m0 : Machine} (h : baseOK m0 = true) : GoodH (Rom.of m0) m0 := by
  simp only [baseOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨rfl, rfl, h.1.1, h.1.2, h.2⟩

set_option maxRecDepth 100000 in
theorem lookup_rts : lookupOp 0x60 insList = some .rts := rfl

section chain
variable {sy : Syms} {E : Rom}

/-- a routine, from what the check says -/
theorem leaf_app {sp : UInt8} {entry r : UInt16} {a : Tag} {ain : UInt8} {L Lo : List (Nat × Tag)} {watch : List Nat} {R H : Machine}
    (hc : leafAll E sp entry r a L Lo watch = true) (gR : Good E R) (pcR : R.pc = entry) (ha : a.R R.a ain) (gH : GoodH E H) (hs : H.s = sp)
    (hL : ∀ p ∈ L, p.2.R (R.ram.get! p.1) (H.ram.get! p.1)) :
    ∃ k, k ≤ fuelS ∧ Good E (stepN k R) ∧ (stepN k R).pc = r ∧ (stepN k R).s = R.s ∧
      (∀ p ∈ Lo, p.2.R ((stepN k R).ram.get! p.1) ((runSub H entry ain 0 0).ram.get! p.1)) ∧
      (∀ i ∈ watch, i < 2048 → (stepN k R).ram.get! i = R.ram.get! i) ∧
      (∀ i ∈ watch, i < 2048 → i ≠ stkI sp → i ≠ stkI (sp - 1) → (runSub H entry ain 0 0).ram.get! i = H.ram.get! i) ∧
      GoodH E (runSub H entry ain 0 0) ∧ (runSub H entry ain 0 0).s = sp ∧ InFrameN E R k := by
  subst hs
  simp only [leafAll, isRts, tagsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true', List.all_eq_true, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  obtain ⟨k, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := leaf_spec (fuel := fuelS) h5 (by decide) h1 (by rw [h2]; exact lookup_rts) h3 gR pcR ha gH
    (fun p hp => ⟨(h4 p hp).1.1, (h4 p hp).1.2, (h4 p hp).2, hL p hp⟩) (List.mem_cons_self) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨k, h6, h7, h8, h9, h10, fun i hi hl => h11 i (List.mem_append_right _ hi) hl,
    fun i hi hl h15 h16 => h12 i (List.mem_append_right _ hi) hl h15 h16, h13, h14, h15⟩

/-- `R` and the model agree on the horizontal state -/
structure Rel5 (sy : Syms) (a b : Machine) : Prop where
  v : a.ram.get! (I sy.Player_X_Speed) = b.ram.get! (I sy.Player_X_Speed)
  f : a.ram.get! (I sy.Player_X_MoveForce) = b.ram.get! (I sy.Player_X_MoveForce)
  fd : a.ram.get! (I sy.PlayerFacingDir) = b.ram.get! (I sy.PlayerFacingDir)
  md : a.ram.get! (I sy.Player_MovingDir) = b.ram.get! (I sy.Player_MovingDir)
  rs : a.ram.get! (I sy.RunningSpeed) = 0 ↔ b.ram.get! (I sy.RunningSpeed) = 0

/-- the bytes of the position -/
def Same3 (sy : Syms) (a b : Machine) : Prop :=
  a.ram.get! (I sy.Player_X_Position) = b.ram.get! (I sy.Player_X_Position) ∧ a.ram.get! (I sy.Player_PageLoc) = b.ram.get! (I sy.Player_PageLoc) ∧
    a.ram.get! (I sy.SprObject_X_MoveForce) = b.ram.get! (I sy.SprObject_X_MoveForce)

/-- a cut after a return, on a real machine -/
theorem at_after {c : Cut} {r : UInt16} {R R' : Machine} (h : At E c R) (hg : Good E R') (hpc : R'.pc = r) (hs : R'.s = R.s)
    (hK : ∀ p ∈ c.K, R'.ram.get! p.1 = R.ram.get! p.1) : At E (afterLeaf c r) R' := by
  refine ⟨hg, hpc, by rw [hs]; exact h.s, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hK p hp]
    exact h.K p hp
  · intro p hp
    cases hp
  · intro v hv
    cases hv
  · intro v hv
    cases hv
  · intro v hv
    cases hv

/-- the stage of `ImposeFriction`, from its entry to the mover -/
theorem fric_stage {sp : UInt8} {c3 c4 : Cut} {r3 : UInt16} {lr : UInt8} {R C : Machine} {L : List (Nat × Tag)}
    (h1 : leafAll E sp sy.ImposeFriction r3 (Tag.kn lr lr) L (outFric sy)
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ c3.ids) = true)
    (h2 : pieceOK E (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction)
    (hA : At E c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048) (gC : GoodH E C) (hs : C.s = sp) (hrel : ∀ p ∈ L, p.2.R (R.ram.get! p.1) (C.ram.get! p.1)) :
    ∃ k, k ≤ 2 * fuelS ∧ At E c4 (stepN k R) ∧ Rel5 sy (stepN k R) (runSub C sy.ImposeFriction lr 0 0) ∧ Same3 sy (stepN k R) R ∧ InFrameN E R k := by
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, f1, g1, p1, s1, o1, w1, _, _, _, C1⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) gC hs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK3 p hp))
  obtain ⟨k2, f2, A2, W2, _, C2⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have w1' : ∀ i, i ∈ [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] → i < 2048 → (stepN k1 R).ram.get! i = R.ram.get! i :=
    fun i hi hl => w1 i (List.mem_append_left _ hi) hl
  have oV := o1 (I sy.Player_X_Speed, .eq) (by simp [outFric])
  have oF := o1 (I sy.Player_X_MoveForce, .eq) (by simp [outFric])
  have oM := o1 (I sy.Player_MovingDir, .eq) (by simp [outFric])
  have oD := o1 (I sy.PlayerFacingDir, .eq) (by simp [outFric])
  have oR := o1 (I sy.RunningSpeed, .nz) (by simp [outFric])
  refine ⟨k1 + k2, by omega, by rw [e]; exact A2, ?_, ?_, InFrameN.add C1 C2⟩
  · rw [e]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oV
    · rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oF
    · rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oD
    · rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oM
    · rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oR
  · rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp) (I_lt _)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp) (I_lt _)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp) (I_lt _)]

/-- the bytes the model pokes, and two more bytes, are apart -/
def apartOK (sy : Syms) (m0 : Machine) : Bool :=
  nodupB (pokeIdx sy) && !(pokeIdx sy).contains (I sy.AreaType) && !(pokeIdx sy).contains (I sy.Player_CollisionBits) && sy.RunSpeedMin.toUInt8 != 0 &&
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.MaximumRightSpeed, I sy.MaximumLeftSpeed, I sy.FrictionAdderLow, I sy.FrictionAdderHigh, I sy.Player_CollisionBits].all (· != I sy.PlayerFacingDir) &&
  (I sy.SavedJoypadBits :: I sy.Player_CollisionBits :: pokeIdx sy).all (fun i => i != stkI m0.s && i != stkI (m0.s - 1))

/-- the input of the frame, from the case -/
theorem norm_fields (c : Case) (rt : UInt8) :
    (norm (c.inp rt)).joy = c.n.joy ∧ (norm (c.inp rt)).st = c.n.st ∧ (norm (c.inp rt)).jump = c.n.jump ∧ (norm (c.inp rt)).rt = if c.gb then rt else 0 := by
  unfold Case.n Case.gb norm Case.inp
  by_cases h1 : c.st = 0 <;> by_cases h2 : (c.raw &&& 0x80 != 0 && !c.prevA) = true <;> by_cases h3 : (joyOf c.raw &&& 0x40) = 0 <;> simp [h1, h2, h3]

theorem lr_of {i j : HIn} (h1 : i.joy = j.joy) (h2 : i.st = j.st) : lrOf i = lrOf j := by
  simp only [lrOf, h1, h2]
theorem st_of {i j : HIn} (h1 : i.st = j.st) (h2 : i.jump = j.jump) : stOf i = stOf j := by
  simp only [stOf, h1, h2]
theorem hab_of {i j : HIn} (h1 : i.joy = j.joy) (h2 : i.jump = j.jump) : habOf i = habOf j := by
  simp only [habOf, h1, h2]
theorem hsv_of {i j : HIn} (h1 : i.joy = j.joy) (h2 : i.jump = j.jump) : hsvOf i = hsvOf j := by
  simp only [hsvOf, h1, h2]

/-- the state read: the running speed is known only as zero or not -/
theorem rs_nz (sy : Syms) (hmin : sy.RunSpeedMin.toUInt8 ≠ 0) (x : UInt8) : (x = 0 ↔ (if x == 0 then (0 : UInt8) else sy.RunSpeedMin.toUInt8) = 0) := by
  by_cases h : x = 0
  · subst h
    simp
  · have h2 : (x == 0) = false := beq_eq_false_iff_ne.2 h
    simp [h, h2, hmin]

/-- the running timer in the model -/
theorem rt_nz (x : UInt8) : (x = 0 ↔ (if x == 0 then (0 : UInt8) else 1) = 0) := by
  by_cases h : x = 0
  · subst h
    simp
  · have h2 : (x == 0) = false := beq_eq_false_iff_ne.2 h
    simp [h, h2]

/-- the facts of `apartOK` -/
structure Apart (sy : Syms) (m0 : Machine) : Prop where
  nd : nodupB (pokeIdx sy) = true
  area : ∀ p ∈ pokeIdx sy, p ≠ I sy.AreaType
  coll : ∀ p ∈ pokeIdx sy, p ≠ I sy.Player_CollisionBits
  rmin : sy.RunSpeedMin.toUInt8 ≠ 0
  fd : ∀ i ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.MaximumRightSpeed, I sy.MaximumLeftSpeed, I sy.FrictionAdderLow, I sy.FrictionAdderHigh, I sy.Player_CollisionBits], I sy.PlayerFacingDir ≠ i
  st : ∀ i ∈ I sy.SavedJoypadBits :: I sy.Player_CollisionBits :: pokeIdx sy, i ≠ stkI m0.s ∧ i ≠ stkI (m0.s - 1)

theorem apart_of {m0 : Machine} (h : apartOK sy m0 = true) : Apart sy m0 := by
  simp only [apartOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, ?_, ?_, h4, fun i hi e => h5 i hi e.symm, h6⟩
  · intro p hp e
    subst e
    rw [List.contains_iff_mem.2 hp] at h2
    cases h2
  · intro p hp e
    subst e
    rw [List.contains_iff_mem.2 hp] at h3
    cases h3

/-- from the player's routine through `X_Physics` -/
theorem phase1 {m0 : Machine} {S : UInt8} {c : Case} {c1 : Cut} {r1 : UInt16} {R : Machine} {s : HS} {i : HIn}
    (hb : GoodH E m0) (hap : Apart sy m0)
    (h1 : pieceOK E (c.c0 sy S) c1 (I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy) fuelW = true) (hpc1 : c1.pc = sy.X_Physics)
    (hst : (I sy.Player_State, c.rst) ∈ c1.K) (hlr : (I sy.Left_Right_Buttons, lrOf c.n) ∈ c1.K) (hab : (I sy.A_B_Buttons, c.rab) ∈ c1.K)
    (har : (I sy.AreaType, c.area) ∈ c1.K) (hen : (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) ∈ c1.K)
    (h2 : leafAll E m0.s sy.X_Physics r1 .any (tagsPhys sy m0 c) (outPhys sy) (I sy.SavedJoypadBits :: (watchH sy ++ c1.ids)) = true)
    (hA : At E (c.c0 sy S) R)
    (hv : s.v = R.ram.get! (I sy.Player_X_Speed)) (hf : s.f = R.ram.get! (I sy.Player_X_MoveForce)) (hfd : s.fd = R.ram.get! (I sy.PlayerFacingDir))
    (hmd : s.md = R.ram.get! (I sy.Player_MovingDir)) (hrs : R.ram.get! (I sy.RunningSpeed) = 0 ↔ s.rs = 0)
    (habs : R.ram.get! (I sy.Player_XSpeedAbsolute) = absB (R.ram.get! (I sy.Player_X_Speed)))
    (hilr : lrOf i = lrOf c.n) (hist : stOf i = stOf c.n) (hiab : habOf i = habOf c.n)
    (hirt : c.gb = true → (R.ram.get! (I sy.RunningTimer) = 0 ↔ i.rt = 0)) :
    ∃ k, k ≤ fuelW + fuelS ∧ At E (afterLeaf c1 r1) (stepN k R) ∧
      (∀ p ∈ outPhys sy, p.2.R ((stepN k R).ram.get! p.1) ((runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0).ram.get! p.1)) ∧
      (∀ j ∈ I sy.SavedJoypadBits :: watchH sy, (stepN k R).ram.get! j = R.ram.get! j) ∧
      (∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j ≠ stkI m0.s → j ≠ stkI (m0.s - 1) → (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0).ram.get! j = (pokeL m0 (hsL sy s i)).ram.get! j) ∧
      GoodH E (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0) ∧ (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0).s = m0.s ∧ InFrameN E R k := by
  obtain ⟨k1, f1, A1, W1, B1, C1⟩ := piece_spec h1 hA
  have hH : GoodH E (pokeL m0 (hsL sy s i)) := pokeL_good _ hb
  have hHs : (pokeL m0 (hsL sy s i)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ hsL sy s i, (pokeL m0 (hsL sy s i)).ram.get! (I q.1) = q.2 := pokeL_get _ _ hb hap.nd
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → (stepN k1 R).ram.get! j = R.ram.get! j := W1
  have hR : ∀ p ∈ tagsPhys sy m0 c, p.2.R ((stepN k1 R).ram.get! p.1) ((pokeL m0 (hsL sy s i)).ram.get! p.1) := by
    intro p hp
    simp only [tagsPhys, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show _ = _
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.Player_X_Speed, s.v) (by simp [hsL])]
      exact hv.symm
    · show _ = _
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.Player_X_MoveForce, s.f) (by simp [hsL])]
      exact hf.symm
    · show _ = _
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.Player_XSpeedAbsolute, absB s.v) (by simp [hsL]), habs, hv]
    · show _ = _
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.Player_MovingDir, s.md) (by simp [hsL])]
      exact hmd.symm
    · show _ = _
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.PlayerFacingDir, s.fd) (by simp [hsL])]
      exact hfd.symm
    · show (_ = 0 ↔ _ = 0)
      rw [wG _ (by simp [watchH]) (I_lt _), hget (sy.RunningSpeed, s.rs) (by simp [hsL])]
      exact hrs
    · have e1 := A1.K _ hen
      have e2 := hget (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (by simp [hsL])
      simp only at e1 e2 ⊢
      rw [e1, e2]
      exact Tag.R_kn _ _
    · have e1 := A1.K _ har
      have e2 : (pokeL m0 (hsL sy s i)).ram.get! (I sy.AreaType) = m0.ram.get! (I sy.AreaType) :=
        pokeL_out _ _ (fun q hq => hap.area _ (by
          have e3 : (hsL sy s i).map (fun p => I p.1) = pokeIdx sy := rfl
          rw [← e3]
          exact List.mem_map.2 ⟨q, hq, rfl⟩))
      simp only at e1 ⊢
      rw [e1, e2]
      exact Tag.R_kn _ _
    · have e1 := A1.K _ hst
      have e2 := hget (sy.Player_State, stOf i) (by simp [hsL])
      simp only at e1 e2 ⊢
      rw [e1, e2, hist]
      exact Tag.R_kn _ _
    · have e1 := A1.K _ hlr
      have e2 := hget (sy.Left_Right_Buttons, lrOf i) (by simp [hsL])
      simp only at e1 e2 ⊢
      rw [e1, e2, hilr]
      exact Tag.R_kn _ _
    · have e1 := A1.K _ hab
      have e2 := hget (sy.A_B_Buttons, habOf i) (by simp [hsL])
      simp only at e1 e2 ⊢
      rw [e1, e2, hiab]
      exact Tag.R_kn _ _
    · simp only
      split
      · rename_i hg
        show (_ = 0 ↔ _ = 0)
        rw [wG _ (by simp) (I_lt _), hget (sy.RunningTimer, i.rt) (by simp [hsL])]
        exact hirt hg
      · trivial
  obtain ⟨k2, f2, g2, p2, s2, o2, w2, w3, g3, s3, C2⟩ := leaf_app h2 A1.good (by rw [A1.pc, hpc1]) trivial hH hHs hR
  have hK : ∀ p ∈ c1.K, (stepN k2 (stepN k1 R)).ram.get! p.1 = (stepN k1 R).ram.get! p.1 := fun p hp =>
    w2 _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))) (B1 p hp)
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  refine ⟨k1 + k2, by omega, ?_, ?_, ?_, ?_, g3, ?_, InFrameN.add C1 C2⟩
  · rw [e]
    exact at_after A1 g2 p2 s2 hK
  · rw [e]
    exact o2
  · intro j hj
    have hl : j < 2048 := by
      simp only [watchH, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact I_lt _
    rw [e, w2 j (by
      rcases List.mem_cons.1 hj with rfl | h3
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h3)) hl, wG j (List.mem_cons_of_mem _ hj) hl]
  · intro j hj h3 h4
    have hl : j < 2048 := by
      simp only [watchH, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact I_lt _
    exact w3 j (by
      rcases List.mem_cons.1 hj with rfl | h5
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h5)) hl h3 h4
  · exact s3


/-- the tags of the friction, but the collision bits -/
def tagsFric0 (sy : Syms) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.Player_MovingDir, .eq), (I sy.PlayerFacingDir, .eq), (I sy.RunningSpeed, .nz),
   (I sy.MaximumRightSpeed, .eq), (I sy.MaximumLeftSpeed, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq)]

/-- the speed of the model's machine `C` at the friction: the speed of the state, or what `GetPlayerAnimSpeed` leaves of it -/
def SpeedFrom (sy : Syms) (m0 : Machine) (v : UInt8) (C : Machine) : Prop :=
  C.ram.get! (I sy.Player_X_Speed) = v ∨ ∃ A, GoodH (Rom.of m0) A ∧ A.s = m0.s ∧ A.ram.get! (I sy.Player_X_Speed) = v ∧
    C.ram.get! (I sy.Player_X_Speed) = (runSub A sy.GetPlayerAnimSpeed 0 0 0).ram.get! (I sy.Player_X_Speed)

/-- what the friction stage gives: from the real machine `R5` at `ImposeFriction` and the model's machine `C` there, the cut of the mover, and `Out` of the two -/
def FricStage (sy : Syms) (m0 : Machine) (c4 : Cut) (lr : UInt8) (Out : Machine → Machine → Prop) (R5 C : Machine) : Prop :=
  ∃ k, k ≤ 2 * fuelS ∧ At (Rom.of m0) c4 (stepN k R5) ∧ Out (stepN k R5) (runSub C sy.ImposeFriction lr 0 0) ∧ Same3 sy (stepN k R5) R5 ∧ InFrameN (Rom.of m0) R5 k

/-- **From the player's routine to the mover**, with the friction stage as a hypothesis (`hfric`): it is given the machines at `ImposeFriction`, the real one and
the model's, their tags but the collision bits, where the collision bits come from, and the speed of the model's machine. -/
theorem to_moverG {m0 : Machine} {S : UInt8} {c : Case} {R : Machine} {s : HS} {i : HIn} {Out : Machine → Machine → Prop}
    (hb : GoodH (Rom.of m0) m0) (hap : Apart sy m0) (hc : caseOK sy m0 S c = true) (hA : At (Rom.of m0) (c.c0 sy S) R)
    (hv : s.v = R.ram.get! (I sy.Player_X_Speed)) (hf : s.f = R.ram.get! (I sy.Player_X_MoveForce)) (hfd : s.fd = R.ram.get! (I sy.PlayerFacingDir))
    (hmd : s.md = R.ram.get! (I sy.Player_MovingDir)) (hrs : R.ram.get! (I sy.RunningSpeed) = 0 ↔ s.rs = 0)
    (habs : R.ram.get! (I sy.Player_XSpeedAbsolute) = absB (R.ram.get! (I sy.Player_X_Speed)))
    (hsv : R.ram.get! (I sy.SavedJoypadBits) = c.raw)
    (hilr : lrOf i = lrOf c.n) (hist : stOf i = stOf c.n) (hiab : habOf i = habOf c.n) (hisv : hsvOf i = hsvOf c.n)
    (hirt : c.gb = true → (R.ram.get! (I sy.RunningTimer) = 0 ↔ i.rt = 0))
    (hOut : ∀ x y, Rel5 sy x y → Out x y)
    (hfric : stOf c.n = 0 ∨ lrOf c.n ≠ 0 → ∀ {R5 C : Machine}, At (Rom.of m0) (planOf sy m0 S c).c3 R5 → (∀ p ∈ (planOf sy m0 S c).c3.K, p.1 < 2048) →
      GoodH (Rom.of m0) C → C.s = m0.s → (∀ p ∈ tagsFric0 sy, p.2.R (R5.ram.get! p.1) (C.ram.get! p.1)) →
      R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) → C.ram.get! (I sy.Player_CollisionBits) = m0.ram.get! (I sy.Player_CollisionBits) →
      SpeedFrom sy m0 s.v C → FricStage sy m0 (planOf sy m0 S c).c4 (lrOf c.n) Out R5 C) :
    ∃ k, k ≤ fuelW + 6 * fuelS ∧ At (Rom.of m0) (planOf sy m0 S c).c4 (stepN k R) ∧ Out (stepN k R) (midH sy m0 s i) ∧ Same3 sy (stepN k R) R ∧
      InFrameN (Rom.of m0) R k := by
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  generalize planOf sy m0 S c = P at hc hfric ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨k1, f1, AF, oP, wR, wH, gA, sA, C1⟩ := phase1 hb hap a1 a2 (List.contains_iff_mem.1 a3) (List.contains_iff_mem.1 a4) (List.contains_iff_mem.1 a5)
    (List.contains_iff_mem.1 a6) (List.contains_iff_mem.1 a7) a8 hA hv hf hfd hmd hrs habs hilr hist hiab hirt
  have hmid : midH sy m0 s i = if stOf c.n == 0 then
      runSub (if lrOf c.n != 0 then poke (runSub (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0) sy.GetPlayerAnimSpeed 0 0 0) sy.PlayerFacingDir (lrOf c.n)
        else runSub (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0) sy.GetPlayerAnimSpeed 0 0 0) sy.ImposeFriction (lrOf c.n) 0 0
    else if lrOf c.n != 0 then runSub (runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0) sy.ImposeFriction (lrOf c.n) 0 0 else runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0 := by
    simp only [midH, hist, hilr]
  have hHsv : (pokeL m0 (hsL sy s i)).ram.get! (I sy.SavedJoypadBits) = hsvOf c.n := by
    rw [← hisv]
    exact pokeL_get (E := Rom.of m0) (hsL sy s i) m0 hb hap.nd (sy.SavedJoypadBits, hsvOf i) (by simp [hsL])
  have hHcoll : (pokeL m0 (hsL sy s i)).ram.get! (I sy.Player_CollisionBits) = m0.ram.get! (I sy.Player_CollisionBits) :=
    pokeL_out _ _ (fun q hq => hap.coll _ (by
      have e3 : (hsL sy s i).map (fun p => I p.1) = pokeIdx sy := rfl
      rw [← e3]
      exact List.mem_map.2 ⟨q, hq, rfl⟩))
  have hst1 := hap.st (I sy.Player_CollisionBits) (by simp)
  have hst2 := hap.st (I sy.SavedJoypadBits) (by simp)
  generalize hR2 : stepN k1 R = R2 at AF oP wR
  generalize hAe : runSub (pokeL m0 (hsL sy s i)) sy.X_Physics 0 0 0 = A at oP wH gA sA hmid
  have hAcoll : A.ram.get! (I sy.Player_CollisionBits) = m0.ram.get! (I sy.Player_CollisionBits) := by
    rw [wH _ (by simp [watchH]) hst1.1 hst1.2, hHcoll]
  have hAsv : A.ram.get! (I sy.SavedJoypadBits) = hsvOf c.n := by
    rw [wH _ (by simp) hst2.1 hst2.2, hHsv]
  have hRcoll : R2.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := wR _ (by simp [watchH])
  have hstv := hap.st (I sy.Player_X_Speed) (by simp [pokeIdx])
  have hAv : A.ram.get! (I sy.Player_X_Speed) = s.v := by
    rw [wH _ (by simp [watchH]) hstv.1 hstv.2]
    exact pokeL_get (E := Rom.of m0) (hsL sy s i) m0 hb hap.nd (sy.Player_X_Speed, s.v) (by simp [hsL])
  have hRsv : R2.ram.get! (I sy.SavedJoypadBits) = c.raw := by
    rw [wR _ (by simp)]
    exact hsv
  have hS3 : Same3 sy R2 R := ⟨wR _ (by simp [watchH]), wR _ (by simp [watchH]), wR _ (by simp [watchH])⟩
  -- what `X_Physics` leaves, kept by the glue after it
  have carry : ∀ {R3 : Machine}, (∀ j ∈ watchA sy, j < 2048 → R3.ram.get! j = R2.ram.get! j) → ∀ p ∈ outPhys sy, p.2.R (R3.ram.get! p.1) (A.ram.get! p.1) := by
    intro R3 hw p hp
    have hl : p.1 ∈ watchA sy ∧ p.1 < 2048 := by
      simp only [outPhys, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp [watchA, watchH, capsL], I_lt _⟩
    rw [hw _ hl.1 hl.2]
    exact oP p hp
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    have hb0 : (stOf c.n == 0) = true := beq_iff_eq.2 h0
    rw [if_pos hb0] at hmid
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, d3⟩, d4⟩ := fc
    obtain ⟨k2, f2, A3, W3, B3, C2⟩ := piece_spec b2 AF
    generalize hR3 : stepN k2 R2 = R3 at A3 W3
    have c3 := carry W3
    have hrelA : ∀ p ∈ tagsAnim sy c, p.2.R (R3.ram.get! p.1) (A.ram.get! p.1) := by
      intro p hp
      simp only [tagsAnim, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · exact c3 _ (by simp [outPhys])
      · simp only
        rw [W3 _ (by simp [watchA]) (I_lt _), hRsv, hAsv]
        exact Tag.R_kn _ _
    obtain ⟨k3, f3, g4, p4, s4, o4, w4, wH4, gB, sB, C3⟩ := leaf_app b3 A3.good (by rw [A3.pc, b1]) trivial gA sA hrelA
    generalize hR4 : stepN k3 R3 = R4 at g4 p4 s4 o4 w4
    generalize hBe : runSub A sy.GetPlayerAnimSpeed 0 0 0 = B at o4 wH4 gB sB hmid
    have AF4 := at_after (r := P.r2) A3 g4 p4 s4 (fun p hp => w4 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (B3 p hp))
    obtain ⟨k4, f4, A5, W5, B5, C4⟩ := piece_spec b4 AF4
    generalize hR5 : stepN k4 R4 = R5 at A5 W5
    -- the machine of the model before `ImposeFriction`
    generalize hCe : (if lrOf c.n != 0 then poke B sy.PlayerFacingDir (lrOf c.n) else B) = C at hmid
    have gC : GoodH (Rom.of m0) C := by
      rw [← hCe]
      split
      · exact poke_good _ _ gB
      · exact gB
    have sC : C.s = m0.s := by
      rw [← hCe]
      split
      · exact (poke_s _ _ _).trans sB
      · exact sB
    have hCo : ∀ j, I sy.PlayerFacingDir ≠ j → C.ram.get! j = B.ram.get! j := by
      intro j hj
      rw [← hCe]
      split
      · exact poke_get_ne _ _ _ hj
      · rfl
    have wf : ∀ j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy,
        j < 2048 → R5.ram.get! j = R4.ram.get! j := fun j hj hl => W5 j (List.mem_append_left _ hj) hl
    have hrelF : ∀ p ∈ tagsFric0 sy, p.2.R (R5.ram.get! p.1) (C.ram.get! p.1) := by
      intro p hp
      have hO : ∀ {j : Nat} {t : Tag}, (j, t) ∈ outAnim sy → j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy →
          j < 2048 → I sy.PlayerFacingDir ≠ j → t.R (R5.ram.get! j) (C.ram.get! j) := by
        intro j t h1 h2 h3 h4
        rw [wf j h2 h3, hCo j h4]
        exact o4 _ h1
      simp only [tagsFric0, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hO (by simp [outAnim]) (by simp) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp) (I_lt _) (hap.fd _ (by simp))
      · -- the facing direction
        show R5.ram.get! (I sy.PlayerFacingDir) = C.ram.get! (I sy.PlayerFacingDir)
        by_cases hl : lrOf c.n = 0
        · have hl2 : (lrOf c.n != 0) = false := by simp [hl]
          have e1 : C = B := by
            rw [← hCe, if_neg (by rw [hl2]; decide)]
          have e2 : R5.ram.get! (I sy.PlayerFacingDir) = R4.ram.get! (I sy.PlayerFacingDir) := by
            refine W5 _ (List.mem_append_right _ ?_) (I_lt _)
            rw [hl2]
            simp
          rw [e2, e1]
          exact o4 (I sy.PlayerFacingDir, .eq) (by simp [outAnim])
        · have hl2 : (lrOf c.n != 0) = true := by simpa using hl
          have e1 : C = poke B sy.PlayerFacingDir (lrOf c.n) := by
            rw [← hCe, if_pos hl2]
          have e2 : (I sy.PlayerFacingDir, lrOf c.n) ∈ P.c3.K := by
            rcases b5 with b5 | b5
            · exact absurd b5 hl
            · exact List.contains_iff_mem.1 b5
          rw [A5.K _ e2, e1, poke_get_self _ _ gB.size]
      · exact hO (by simp [outAnim]) (by simp) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp [capsL]) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp [capsL]) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp [capsL]) (I_lt _) (hap.fd _ (by simp))
      · exact hO (by simp [outAnim]) (by simp [capsL]) (I_lt _) (hap.fd _ (by simp))
    have hbR : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
      rw [wf _ (by simp) (I_lt _), w4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _)]
      exact hRcoll
    have hbC : C.ram.get! (I sy.Player_CollisionBits) = m0.ram.get! (I sy.Player_CollisionBits) := by
      rw [hCo _ (hap.fd _ (by simp)), wH4 _ (by simp) (I_lt _) hst1.1 hst1.2]
      exact hAcoll
    have hCv : SpeedFrom sy m0 s.v C := Or.inr ⟨A, gA, sA, hAv, by rw [hCo _ (hap.fd _ (by simp)), ← hBe]⟩
    obtain ⟨k5, f5, A7, R7, S7, C5⟩ := hfric (Or.inl h0) A5 B5 gC sC hrelF hbR hbC hCv
    rw [← hmid] at R7
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + k5)))) R = stepN k5 R5 := by
      rw [stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + k5))), by omega, by rw [hfin]; exact A7, by rw [hfin]; exact R7, ?_,
      InFrameN.add' C1 hR2 (InFrameN.add' C2 hR3 (InFrameN.add' C3 hR4 (InFrameN.add' C4 hR5 C5)))⟩
    rw [hfin]
    obtain ⟨s1, s2, s3⟩ := S7
    obtain ⟨t1, t2, t3⟩ := hS3
    refine ⟨?_, ?_, ?_⟩
    · rw [s1, wf _ (by simp) (I_lt _), w4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
    · rw [s2, wf _ (by simp) (I_lt _), w4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
    · rw [s3, wf _ (by simp) (I_lt _), w4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
  · have hb0 : ¬ (stOf c.n == 0) = true := fun e => h0 (beq_iff_eq.1 e)
    rw [if_neg hb0] at hmid
    simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at hmid a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, d3⟩, d4⟩ := fc
      obtain ⟨k2, f2, A3, W3, B3, C2⟩ := piece_spec g AF
      generalize hR3 : stepN k2 R2 = R3 at A3 W3
      have c3 := carry W3
      have hrelF : ∀ p ∈ tagsFric0 sy, p.2.R (R3.ram.get! p.1) (A.ram.get! p.1) := by
        intro p hp
        simp only [tagsFric0, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
        · exact c3 _ (by simp [outPhys])
      have hbR : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _)]
        exact hRcoll
      obtain ⟨k5, f5, A7, R7, S7, C5⟩ := hfric (Or.inr (by simpa using hl)) A3 B3 gA sA hrelF hbR hAcoll (Or.inl hAv)
      rw [← hmid] at R7
      have hfin : stepN (k1 + (k2 + k5)) R = stepN k5 R3 := by
        rw [stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + k5), by omega, by rw [hfin]; exact A7, by rw [hfin]; exact R7, ?_, InFrameN.add' C1 hR2 (InFrameN.add' C2 hR3 C5)⟩
      rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S7
      obtain ⟨t1, t2, t3⟩ := hS3
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
    · -- in the air, with neither
      rw [if_neg hl] at hmid a9
      obtain ⟨k2, f2, A3, W3, _, C2⟩ := piece_spec a9 AF
      generalize hR3 : stepN k2 R2 = R3 at A3 W3
      have c3 := carry W3
      have hfin : stepN (k1 + k2) R = R3 := by
        rw [stepN_add, hR2, hR3]
      refine ⟨k1 + k2, by omega, by rw [hfin]; exact A3, ?_, ?_, InFrameN.add' C1 hR2 C2⟩
      · rw [hfin, hmid]
        refine hOut _ _ ⟨c3 (I sy.Player_X_Speed, .eq) (by simp [outPhys]), c3 (I sy.Player_X_MoveForce, .eq) (by simp [outPhys]), c3 (I sy.PlayerFacingDir, .eq) (by simp [outPhys]),
          c3 (I sy.Player_MovingDir, .eq) (by simp [outPhys]), c3 (I sy.RunningSpeed, .nz) (by simp [outPhys])⟩
      · rw [hfin]
        obtain ⟨t1, t2, t3⟩ := hS3
        refine ⟨?_, ?_, ?_⟩
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t3]


/-- the friction's walks of a case with friction -/
theorem fricOK_of {m0 : Machine} {S : UInt8} {c : Case} (hc : caseOK sy m0 S c = true) (h : stOf c.n = 0 ∨ lrOf c.n ≠ 0) :
    fricOK sy m0 c (planOf sy m0 S c) = true := by
  simp only [caseOK, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  by_cases h0 : stOf c.n = 0
  · simp only [if_pos (beq_iff_eq.2 h0), Bool.and_eq_true] at a9
    exact a9.2
  · have hb0 : (stOf c.n == 0) = false := by simpa using h0
    have hl : (lrOf c.n != 0) = true := by simpa using h.resolve_left h0
    simp only [hb0, hl, if_true, Bool.false_eq_true, if_false, Bool.and_eq_true] at a9
    exact a9.2

/-- the tag of the collision bits in `tagsFric`, on a real machine whose pressed side is not masked -/
theorem collTag {m0 : Machine} {lr x y : UInt8} (h1 : x &&& lr = lr) (h2 : y = m0.ram.get! (I sy.Player_CollisionBits)) :
    (Tag.ab ⟨lr, lr⟩ (AB.known (peek m0 sy.Player_CollisionBits))).R x y := by
  refine ⟨?_, ?_⟩
  · show x &&& lr = lr &&& lr
    rw [h1, UInt8.and_self]
  · rw [h2]
    exact TaintRun.mem_known_self _

/-- from the player's routine to the mover -/
theorem to_mover {m0 : Machine} {S : UInt8} {c : Case} {R : Machine} {s : HS} {i : HIn}
    (hb : GoodH (Rom.of m0) m0) (hap : Apart sy m0) (hc : caseOK sy m0 S c = true) (hA : At (Rom.of m0) (c.c0 sy S) R)
    (hv : s.v = R.ram.get! (I sy.Player_X_Speed)) (hf : s.f = R.ram.get! (I sy.Player_X_MoveForce)) (hfd : s.fd = R.ram.get! (I sy.PlayerFacingDir))
    (hmd : s.md = R.ram.get! (I sy.Player_MovingDir)) (hrs : R.ram.get! (I sy.RunningSpeed) = 0 ↔ s.rs = 0)
    (habs : R.ram.get! (I sy.Player_XSpeedAbsolute) = absB (R.ram.get! (I sy.Player_X_Speed)))
    (hcoll : R.ram.get! (I sy.Player_CollisionBits) &&& lrOf c.n = lrOf c.n) (hsv : R.ram.get! (I sy.SavedJoypadBits) = c.raw)
    (hilr : lrOf i = lrOf c.n) (hist : stOf i = stOf c.n) (hiab : habOf i = habOf c.n) (hisv : hsvOf i = hsvOf c.n)
    (hirt : c.gb = true → (R.ram.get! (I sy.RunningTimer) = 0 ↔ i.rt = 0)) :
    ∃ k, k ≤ fuelW + 6 * fuelS ∧ At (Rom.of m0) (planOf sy m0 S c).c4 (stepN k R) ∧ Rel5 sy (stepN k R) (midH sy m0 s i) ∧ Same3 sy (stepN k R) R ∧
      InFrameN (Rom.of m0) R k := by
  refine to_moverG hb hap hc hA hv hf hfd hmd hrs habs hsv hilr hist hiab hisv hirt (fun _ _ h => h) ?_
  intro hfr R5 C hA5 hK hC hCs hrel hbR hbC _
  have fc := fricOK_of hc hfr
  simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, d4⟩ := fc
  refine fric_stage d3 d4 d1 d2 hA5 hK hC hCs ?_
  intro p hp
  simp only [tagsFric, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · exact hrel _ (by simp [tagsFric0])
  · refine collTag ?_ hbC
    rw [hbR]
    exact hcoll

/-- the two machines of a cut are the same -/
def cutSame (a b : Cut) : Bool :=
  a.pc == b.pc && a.s == b.s && a.K == b.K && a.B.isEmpty && b.B.isEmpty && a.ra == b.ra && a.x == b.x && a.cf == b.cf

theorem cutSame_eq {a b : Cut} (h : cutSame a b = true) : a = b := by
  simp only [cutSame, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases a
  cases b
  simp_all

/-- the different cuts at the mover -/
def tailsOf (sy : Syms) (m0 : Machine) (S : UInt8) : List Cut :=
  allCases.foldl (fun l c =>
    let t := (planOf sy m0 S c).c4
    if l.any (cutSame · t) then l else t :: l) []

/-! ## `TopSpeed.Frame` on real machines: the checks -/

/-- the caps and the adder are entries of the tables -/
def capsGood (sy : Syms) (m0 : Machine) (Q : TS) : Bool :=
  match (Q.ram (I sy.MaximumRightSpeed)).same, (Q.ram (I sy.MaximumLeftSpeed)).same, (Q.ram (I sy.FrictionAdderLow)).same, (Q.ram (I sy.FrictionAdderHigh)).same with
  | some mr, some ml, some lo, some hi => (maxRs sy m0).contains mr && (maxLs sy m0).contains ml && (adders sy m0).contains (lo, hi)
  | _, _, _, _ => false

/-- the speed and its fraction are not written, or are both 0 -/
def animGood (sy : Syms) (Q : TS) : Bool :=
  (!Q.w (I sy.Player_X_Speed) && !Q.w (I sy.Player_X_MoveForce)) ||
    ((Q.ram (I sy.Player_X_Speed)).same == some 0 && (Q.ram (I sy.Player_X_MoveForce)).same == some 0)

/-- the bytes of `frictionCheck`, in its order -/
def fricL (sy : Syms) (v f lo hi mr ml cb : UInt8) : List (UInt16 × UInt8) :=
  [(sy.Player_X_Speed, v), (sy.Player_X_MoveForce, f), (sy.FrictionAdderLow, lo), (sy.FrictionAdderHigh, hi), (sy.MaximumRightSpeed, mr), (sy.MaximumLeftSpeed, ml), (sy.Player_CollisionBits, cb)]

def fricIdx (sy : Syms) : List Nat :=
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.FrictionAdderLow, I sy.FrictionAdderHigh, I sy.MaximumRightSpeed, I sy.MaximumLeftSpeed, I sy.Player_CollisionBits]

def tagsFr (sy : Syms) : List (Nat × Tag) := (fricIdx sy).map (·, .eq)

/-- the walks of a case for `TopSpeed.Frame`: `X_Physics` with the stored speed free, `GetPlayerAnimSpeed` on one machine, `ImposeFriction` next to `frictionCheck` -/
def frameCaseOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  let E := Rom.of m0
  let P := planOf sy m0 S c
  let lr := lrOf c.n
  (TopSpeed.upTo 3).contains lr &&
  walkT E (fun Q => Q.pc == P.r1) (fun Q => goalC (afterLeaf P.c1 P.r1) (I sy.SavedJoypadBits :: watchH sy) Q && capsGood sy m0 Q) fuelS (startQ P.c1) &&
  (stOf c.n != 0 ||
    walkT E (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2)) &&
  ((stOf c.n != 0 && lr == 0) ||
    leafAll E m0.s sy.ImposeFriction P.r3 (Tag.kn lr lr) (tagsFr sy) [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq)]
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ P.c3.ids))

/-- every value of the buttons gives an input of the model -/
def joyOK : Bool := TopSpeed.bytes.all fun r => groundInputs.contains (joyOf r)

/-- **The check on the ROM.** All the cases, and the mover from each cut. -/
def modelOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  joyOK && baseOK m0 && apartOK sy m0 && digitsOK && decide (16 ≤ TopSpeed.top sy) &&
  allCases.all (fun c => caseOK sy m0 S c && frameCaseOK sy m0 S c) && nodupB (fricIdx sy) &&
  TopSpeed.bytes.all (fun v => !TopSpeed.inSpeed sy v || (TopSpeed.speedsB sy).contains v) &&
  (TopSpeed.speedsB sy).contains 0 &&
  (let ts := tailsOf sy m0 S
   ts.all (tailOK sy (Rom.of m0)) && allCases.all fun c => ts.any (cutSame · (planOf sy m0 S c).c4))

/-- what the check on the ROM says -/
structure ModelFacts (sy : Syms) (m0 : Machine) (S : UInt8) : Prop where
  joy : joyOK = true
  base : baseOK m0 = true
  apart : apartOK sy m0 = true
  digits : digitsOK = true
  top16 : 16 ≤ TopSpeed.top sy
  cases : ∀ c ∈ allCases, caseOK sy m0 S c = true ∧ frameCaseOK sy m0 S c = true
  fnd : nodupB (fricIdx sy) = true
  scomp : ∀ v ∈ TopSpeed.bytes, (!TopSpeed.inSpeed sy v || (TopSpeed.speedsB sy).contains v) = true
  s0 : (TopSpeed.speedsB sy).contains 0 = true
  tails : ∀ t ∈ tailsOf sy m0 S, tailOK sy (Rom.of m0) t = true
  anyT : ∀ c ∈ allCases, ∃ t ∈ tailsOf sy m0 S, cutSame t (planOf sy m0 S c).c4 = true

theorem facts_of {sy : Syms} {m0 : Machine} {S : UInt8} (h : modelOK sy m0 S = true) : ModelFacts sy m0 S := by
  simp only [modelOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h0⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h0, h5, h6, h7, h8, h9, h10⟩

/-- the case of a machine -/
def caseOf (sy : Syms) (m : Machine) : Case :=
  { st := peek m sy.Player_State, raw := peek m sy.SavedJoypadBits, prevA := peek m sy.PreviousA_B_Buttons &&& 0x80 != 0, area := peek m sy.AreaType }

theorem caseOf_mem {sy : Syms} {E : Rom} {S : UInt8} {R : Machine} (h : AtCtrl0 sy E S R) : caseOf sy R ∈ allCases := by
  refine List.mem_flatMap.2 ⟨_, h.st, List.mem_flatMap.2 ⟨_, h.area, List.mem_flatMap.2 ⟨peek R sy.PreviousA_B_Buttons &&& 0x80 != 0, by cases (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) <;> simp, ?_⟩⟩⟩
  refine List.mem_map.2 ⟨(peek R sy.SavedJoypadBits).toNat, List.mem_range.2 (peek R sy.SavedJoypadBits).toNat_lt, ?_⟩
  simp [caseOf]

/-- the known bit of a byte -/
theorem and80_mem (x : UInt8) : AB.mem ⟨if (x &&& 0x80 != 0) = true then 0x80 else 0, 0x80⟩ x := by
  show x &&& 0x80 = _ &&& 0x80
  rw [and80]
  cases h : bt x 7
  · simp only [Bool.false_eq_true, if_false]
    apply TaintRun.bt_ext
    intro j hj
    rw [TaintRun.bt_and, TaintRun.bt_and, (bit_lits ⟨j, hj⟩).2.2]
    by_cases e : j = 7
    · subst e
      simp [h, TaintRun.bt_zero]
    · simp [e]
  · simp only [if_true]
    apply TaintRun.bt_ext
    intro j hj
    rw [TaintRun.bt_and, TaintRun.bt_and, (bit_lits ⟨j, hj⟩).2.2]
    by_cases e : j = 7
    · subst e
      simp [h]
    · simp [e]

theorem at_start {E : Rom} {S : UInt8} {R : Machine} (h : AtCtrl0 sy E S R) : At E ((caseOf sy R).c0 sy S) R := by
  refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eng
    · rfl
    · rfl
    · rfl
    · exact h.spring
    · exact h.swim
    · exact h.size
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact and80_mem _
  · intro v hv
    cases hv
  · intro v hv
    cases hv
  · intro v hv
    cases hv

theorem readIn_eq (sy : Syms) (R : Machine) : readIn sy R = (caseOf sy R).inp (if peek R sy.RunningTimer == 0 then 0 else 1) := by
  simp only [readIn, Case.inp, caseOf, not_ne]

theorem readHS_of {r b : Machine} (hv : r.ram.get! (I sy.Player_X_Speed) = b.ram.get! (I sy.Player_X_Speed)) (hf : r.ram.get! (I sy.Player_X_MoveForce) = b.ram.get! (I sy.Player_X_MoveForce))
    (hfd : r.ram.get! (I sy.PlayerFacingDir) = b.ram.get! (I sy.PlayerFacingDir)) (hrs : r.ram.get! (I sy.RunningSpeed) = 0 ↔ b.ram.get! (I sy.RunningSpeed) = 0)
    (hmd : r.ram.get! (I sy.Player_MovingDir) = (if b.ram.get! (I sy.Player_X_Speed) == 0 then b.ram.get! (I sy.Player_MovingDir) else if b.ram.get! (I sy.Player_X_Speed) < 0x80 then 1 else 2)) :
    readHS sy r = finishH sy b := by
  have e1 : peek r sy.Player_X_Speed = peek b sy.Player_X_Speed := hv
  have e2 : peek r sy.Player_X_MoveForce = peek b sy.Player_X_MoveForce := hf
  have e3 : peek r sy.PlayerFacingDir = peek b sy.PlayerFacingDir := hfd
  have e4 : peek r sy.Player_MovingDir = (if peek b sy.Player_X_Speed == 0 then peek b sy.Player_MovingDir else if peek b sy.Player_X_Speed < 0x80 then 1 else 2) := hmd
  have e5 : (peek r sy.RunningSpeed == 0) = (peek b sy.RunningSpeed == 0) := by
    have h : peek r sy.RunningSpeed = 0 ↔ peek b sy.RunningSpeed = 0 := hrs
    cases h1 : peek r sy.RunningSpeed == 0 <;> cases h2 : peek b sy.RunningSpeed == 0
    · rfl
    · exact absurd (h.2 (beq_iff_eq.1 h2)) (by simpa using h1)
    · exact absurd (h.1 (beq_iff_eq.1 h1)) (by simpa using h2)
    · rfl
  simp only [readHS, finishH, e1, e2, e3, e4, e5]

/-- **The movement of a real frame.** From the player's routine to the scroll handler, the horizontal state read from the machine follows `hstep`, on the input read from the machine, and `P` moves by `16·v'`,
modulo the size of the position. -/
theorem move_model {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (h : AtCtrl sy (Rom.of m0) S R) :
    ∃ k, k ≤ 2 * fuelW + 11 * fuelS ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧
      readHS sy (stepN k R) = hstep sy m0 (readHS sy R) (readIn sy R) ∧
      (posP sy (stepN k R) - posP sy R - 16 * sbyte (readHS sy (stepN k R)).v) % 0x1000000 = 0 ∧ InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  have hap := apart_of hF.apart
  have hmem := caseOf_mem h.to0
  generalize hc : caseOf sy R = c at hmem
  have hA := at_start h.to0
  rw [hc] at hA
  generalize hrt : (if peek R sy.RunningTimer == 0 then (0 : UInt8) else 1) = rtb
  have hI : readIn sy R = c.inp rtb := by
    rw [readIn_eq, hc, hrt]
  obtain ⟨n1, n2, n3, n4⟩ := norm_fields c rtb
  have hcollC : R.ram.get! (I sy.Player_CollisionBits) &&& lrOf c.n = lrOf c.n := by
    have e := h.coll
    rw [hI, lr_of n1 n2] at e
    exact e
  have hN : hstep sy m0 (readHS sy R) (readIn sy R) = finishH sy (midH sy m0 (readHS sy R) (norm (c.inp rtb))) := by
    rw [hI]
    exact hstepN_eq _ _ _ _
  obtain ⟨k1, f1, A1, R1, S1, C1⟩ := to_mover (i := norm (c.inp rtb)) (s := readHS sy R) hb hap (hF.cases c hmem).1 hA rfl rfl rfl rfl
    (rs_nz sy hap.rmin _) h.abs hcollC (by rw [← hc]; rfl)
    (lr_of n1 n2) (st_of n2 n3) (hab_of n1 n3) (hsv_of n1 n3)
    (fun hg => by
      rw [n4, if_pos hg, ← hrt]
      exact rt_nz _)
  obtain ⟨t, ht, hte⟩ := hF.anyT c hmem
  have e4 : t = (planOf sy m0 S c).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, f2, g2, p2, v2, ff2, d2, r2, m2, q2, C2⟩ := tail_spec htl hF.digits A1
  generalize hR : stepN k1 R = R1' at A1 R1 S1 v2 ff2 d2 r2 m2 q2 g2 p2 C2
  have hfin : stepN (k1 + k2) R = stepN k2 R1' := by rw [stepN_add, hR]
  refine ⟨k1 + k2, by omega, by rw [hfin]; exact g2, by rw [hfin]; exact p2, ?_, ?_, InFrameN.add' C1 hR C2⟩
  · rw [hfin, hN]
    refine readHS_of (v2.trans R1.v) (ff2.trans R1.f) (d2.trans R1.fd) (by rw [r2]; exact R1.rs) ?_
    rw [m2, R1.v, R1.md]
  · rw [hfin]
    obtain ⟨s1, s2, s3⟩ := S1
    have e : posP sy R1' = posP sy R := by
      rw [posP_eq, posP_eq]
      show posOf (R1'.ram.get! (I sy.Player_PageLoc)) (R1'.ram.get! (I sy.Player_X_Position)) (R1'.ram.get! (I sy.SprObject_X_MoveForce)) =
        posOf (R.ram.get! (I sy.Player_PageLoc)) (R.ram.get! (I sy.Player_X_Position)) (R.ram.get! (I sy.SprObject_X_MoveForce))
      rw [s1, s2, s3]
    have e2 : (readHS sy (stepN k2 R1')).v = R1'.ram.get! (I sy.Player_X_Speed) := v2
    rw [e2, ← e]
    exact q2

/-! ## A frame with the pressed side masked

`hstep` runs `ImposeFriction` with the collision bits of the machine `m0`, the real frame with those of a block of Left. `ImposeFriction` first masks the buttons
with the bits. With Left and Right the two take the same way. With Left alone the real routine reads the speed: at a speed that is not 0 it comes to `RghtFrict` by another
way, at the speed 0 it leaves the speed 0. The proof compares the real machine with the model's machine with the real bits (`fric_stage`, a walk of two machines), and
that machine's `runSub` with the model's (`runSub2`: a walk with a detour for Left alone, one walk for each speed). The speed at the friction is that of the state, or 0:
`GetPlayerAnimSpeed` writes only 0 to it (`gpasOK`). -/

/-- the side `lr` is masked by the bits of a block of Left -/
def maskedLr (sy : Syms) (lr : UInt8) : Bool := sy.noLeft &&& lr != lr

/-- the friction's tags, with the bits of a block of Left on both machines -/
def tagsFricN (sy : Syms) : List (Nat × Tag) := tagsFric0 sy ++ [(I sy.Player_CollisionBits, Tag.kn sy.noLeft sy.noLeft)]

/-- the walk of `ImposeFriction` of a masked case: the real machine and the model's machine with the real bits -/
def maskCaseOK (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  !maskedLr sy (lrOf c.n) ||
    leafAll (Rom.of m0) m0.s sy.ImposeFriction (planOf sy m0 S c).r3 (Tag.kn (lrOf c.n) (lrOf c.n)) (tagsFricN sy) (outFric sy)
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ (planOf sy m0 S c).c3.ids)

/-- the collision bits of `m0` -/
def bits0 (sy : Syms) (m0 : Machine) : UInt8 := peek m0 sy.Player_CollisionBits

/-- the stack pointer in the model's routines -/
def spM (m0 : Machine) : UInt8 := m0.s - 2

/-- where a walk of two machines of `runSub` stops: at the return `r`, with the stack pointer of the call -/
def mStop (r : UInt16) (sp : UInt8) (Q : TS) : Bool := Q.pc == r && Q.s == some sp

/-- the bytes of `runSub`'s return address are not written -/
def stkKept (m0 : Machine) (Q : TS) : Bool := !Q.w (stkI m0.s) && !Q.w (stkI (m0.s - 1))

/-- the two results agree on the speed and its fraction, and nothing wrote the directions and the running speed -/
def mGoal (sy : Syms) (m0 : Machine) (Q : TS) : Bool :=
  tagImp (Q.ram (I sy.Player_X_Speed)) .eq && tagImp (Q.ram (I sy.Player_X_MoveForce)) .eq &&
    !Q.w (I sy.PlayerFacingDir) && !Q.w (I sy.Player_MovingDir) && !Q.w (I sy.RunningSpeed) && stkKept m0 Q

/-- the return of `ImposeFriction` -/
def fricRet (sy : Syms) (m0 : Machine) : UInt16 := firstRtsS (Rom.of m0) (spM m0) fuelW (leafQD sy.ImposeFriction (spM m0) (Tag.kn 3 3) .eq [])

/-- the return of `GetPlayerAnimSpeed` -/
def gpasRet (sy : Syms) (m0 : Machine) : UInt16 := firstRtsS (Rom.of m0) (spM m0) fuelW (leafQD sy.GetPlayerAnimSpeed (spM m0) (Tag.kn 0 0) .eq [])

/-- Left alone at the speed `v` (not 0, moving right): each machine, the first with the bits of a block of Left and the second with those of `m0`,
comes to `RghtFrict` and writes nothing on the way -/
def leftDetour (sy : Syms) (m0 : Machine) (lr v : UInt8) : Detour :=
  { c := { pc := sy.ImposeFriction, s := spM m0, K := [(I sy.Player_X_Speed, v), (I sy.Player_CollisionBits, sy.noLeft)], ra := some lr },
    c₂ := some { pc := sy.ImposeFriction, s := spM m0, K := [(I sy.Player_X_Speed, v), (I sy.Player_CollisionBits, bits0 sy m0)], ra := some lr },
    c' := { pc := sy.RghtFrict, s := spM m0, K := [(I sy.Player_X_Speed, v)] },
    keep := [I sy.Player_X_MoveForce, I sy.FrictionAdderLow, I sy.FrictionAdderHigh, I sy.MaximumRightSpeed, I sy.MaximumLeftSpeed,
             I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, stkI m0.s, stkI (m0.s - 1)],
    fuel := 16 }

/-- the start of the model's walk of `ImposeFriction` -/
def fricQ (sy : Syms) (m0 : Machine) (lr : UInt8) (L : List (Nat × Tag)) : TS := leafQD sy.ImposeFriction (spM m0) (Tag.kn lr lr) .eq L

/-- the model's `ImposeFriction` with the real bits and with those of `m0`, for a masked `lr`: the same speed and fraction, or the speed 0 with the real bits -/
def maskModelOK (sy : Syms) (m0 : Machine) (lr : UInt8) : Bool :=
  let E := Rom.of m0
  let st := mStop (fricRet sy m0) (spM m0)
  let bT := (I sy.Player_CollisionBits, Tag.kn sy.noLeft (bits0 sy m0))
  !maskedLr sy lr ||
  (if sy.noLeft &&& lr != 0 then walkD E [] st (mGoal sy m0) fuelS (fricQ sy m0 lr [bT])
   else
     (List.range 127).all (fun j =>
       (leftDetour sy m0 lr (j + 1).toUInt8).ok E &&
       walkD E [leftDetour sy m0 lr (j + 1).toUInt8] st (mGoal sy m0) fuelS (fricQ sy m0 lr [(I sy.Player_X_Speed, Tag.kn (j + 1).toUInt8 (j + 1).toUInt8), bT])) &&
     walkD E [] st (fun Q => (Q.ram (I sy.Player_X_Speed)).same == some 0 && stkKept m0 Q) fuelS
       (fricQ sy m0 lr [(I sy.Player_X_Speed, Tag.kn 0 0), (I sy.Player_CollisionBits, Tag.kn sy.noLeft sy.noLeft)]))

/-- `GetPlayerAnimSpeed` on the model writes 0 to the speed, or does not write it -/
def gpasOK (sy : Syms) (m0 : Machine) : Bool :=
  walkD (Rom.of m0) [] (mStop (gpasRet sy m0) (spM m0))
    (fun Q => (!Q.w (I sy.Player_X_Speed) || (Q.ram (I sy.Player_X_Speed)).same == some 0) && stkKept m0 Q) fuelS
    (leafQD sy.GetPlayerAnimSpeed (spM m0) (Tag.kn 0 0) .eq [])

/-- **The check of the masked frames on the ROM.** -/
def maskOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  isRts (Rom.of m0) (fricRet sy m0) && isRts (Rom.of m0) (gpasRet sy m0) &&
  [I sy.Player_X_Speed, I sy.Player_CollisionBits].all (fun i => i != stkI m0.s && i != stkI (m0.s - 1)) &&
  (tagsFric0 sy).all (fun p => p.1 != I sy.Player_CollisionBits) &&
  gpasOK sy m0 && [(0 : UInt8), 1, 2, 3].all (maskModelOK sy m0) && allCases.all (maskCaseOK sy m0 S)

/-- what the check says -/
structure MaskFacts (sy : Syms) (m0 : Machine) (S : UInt8) : Prop where
  fret : isRts (Rom.of m0) (fricRet sy m0) = true
  gret : isRts (Rom.of m0) (gpasRet sy m0) = true
  stk : ∀ i ∈ [I sy.Player_X_Speed, I sy.Player_CollisionBits], i ≠ stkI m0.s ∧ i ≠ stkI (m0.s - 1)
  apart : ∀ p ∈ tagsFric0 sy, p.1 ≠ I sy.Player_CollisionBits
  gpas : gpasOK sy m0 = true
  model : ∀ lr ∈ [(0 : UInt8), 1, 2, 3], maskModelOK sy m0 lr = true
  cases : ∀ c ∈ allCases, maskCaseOK sy m0 S c = true

theorem mfacts_of {sy : Syms} {m0 : Machine} {S : UInt8} (h : maskOK sy m0 S = true) : MaskFacts sy m0 S := by
  simp only [maskOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, fun i hi => ⟨(h3 i hi).1, (h3 i hi).2⟩, h4, h5, h6, h7⟩

theorem and3_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 3 = 0 ∨ UInt8.ofNat n.val &&& 3 = 1 ∨ UInt8.ofNat n.val &&& 3 = 2 ∨ UInt8.ofNat n.val &&& 3 = 3) := by
  decide +kernel

/-- Left/Right in the model is one of four values -/
theorem lrOf_cases (i : HIn) : lrOf i = 0 ∨ lrOf i = 1 ∨ lrOf i = 2 ∨ lrOf i = 3 := by
  have h : i.joy &&& 3 = 0 ∨ i.joy &&& 3 = 1 ∨ i.joy &&& 3 = 2 ∨ i.joy &&& 3 = 3 := by
    have h0 := and3_all ⟨i.joy.toNat, i.joy.toNat_lt⟩
    simpa using h0
  simp only [lrOf]
  split
  · exact Or.inl rfl
  · exact h

theorem lrOf_mem (i : HIn) : lrOf i ∈ [(0 : UInt8), 1, 2, 3] := by
  rcases lrOf_cases i with h | h | h | h <;> rw [h] <;> simp

theorem Rel5.trans {a b d : Machine} (h1 : Rel5 sy a b) (h2 : Rel5 sy b d) : Rel5 sy a d :=
  ⟨h1.v.trans h2.v, h1.f.trans h2.f, h1.fd.trans h2.fd, h1.md.trans h2.md, h1.rs.trans h2.rs⟩

/-- a byte that a list does not tag is not in it -/
theorem lookN_none {α : Type} {i : Nat} : ∀ {L : List (Nat × α)}, lookN i L = none → ∀ p ∈ L, p.1 ≠ i
  | [], _, _, hp => by cases hp
  | q :: L, h, p, hp => by
    unfold lookN at h
    split at h
    · cases h
    · rename_i h1
      rcases List.mem_cons.1 hp with rfl | hp
      · intro e
        exact h1 (by rw [e]; exact beq_self_eq_true _)
      · exact lookN_none h p hp

/-- where the walks of two machines of `runSub` stop -/
theorem mstop_spec {E : Rom} {r : UInt16} {sp : UInt8} (h : isRts E r = true) :
    ∀ Q, mStop r sp Q = true → 0x8000 ≤ Q.pc ∧ lookupOp (E.b Q.pc) insList = some .rts ∧ idleAt E Q.pc = false ∧ Q.s = some sp := by
  intro Q hQ
  simp only [mStop, Bool.and_eq_true, beq_iff_eq] at hQ
  simp only [isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [hQ.1]
  exact ⟨h1, by rw [h2]; exact lookup_rts, h3, hQ.2⟩

theorem stkKept_spec {m0 H : Machine} {Q : TS} (h : stkKept m0 Q = true) (hs : H.s = m0.s) : Q.w (stkI H.s) = false ∧ Q.w (stkI (H.s - 1)) = false := by
  simp only [stkKept, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hs]
  exact h

/-- **The model's friction on two machines** that differ in a few bytes: the same speed, fraction, directions and running speed after it -/
theorem rel_runSub {m0 : Machine} {ds : List Detour} (hds : ∀ d ∈ ds, d.ok (Rom.of m0) = true) {lr : UInt8} {L : List (Nat × Tag)} {r : UInt16} {H₁ H₂ : Machine}
    (hc : walkD (Rom.of m0) ds (mStop r (spM m0)) (mGoal sy m0) fuelS (fricQ sy m0 lr L) = true) (hr : isRts (Rom.of m0) r = true)
    (g1 : GoodH (Rom.of m0) H₁) (g2 : GoodH (Rom.of m0) H₂) (s1 : H₁.s = m0.s) (s2 : H₂.s = m0.s)
    (hL : ∀ p ∈ L, p.1 < 2048 ∧ p.1 ≠ stkI m0.s ∧ p.1 ≠ stkI (m0.s - 1) ∧ p.2.R (H₁.ram.get! p.1) (H₂.ram.get! p.1))
    (hd : ∀ i, lookN i L = none → H₁.ram.get! i = H₂.ram.get! i)
    (hdir : ∀ i ∈ [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed], i ≠ stkI m0.s ∧ i ≠ stkI (m0.s - 1) ∧ H₁.ram.get! i = H₂.ram.get! i) :
    Rel5 sy (runSub H₁ sy.ImposeFriction lr 0 0) (runSub H₂ sy.ImposeFriction lr 0 0) := by
  have hgoal : ∀ Q, mGoal sy m0 Q = true → Q.w (stkI H₁.s) = false ∧ Q.w (stkI (H₁.s - 1)) = false := by
    intro Q hQ
    simp only [mGoal, Bool.and_eq_true] at hQ
    exact stkKept_spec hQ.2 s1
  obtain ⟨Q, _, hg, hR, hW⟩ := runSub2 hds hc (by decide) (mstop_spec hr) hgoal g1 g2 (by rw [s1]; rfl) (by rw [s2, s1]) (Tag.R_kn lr lr) rfl
    (fun p hp => by rw [s1]; exact hL p hp) (fun i _ _ _ hn => hd i hn)
  simp only [mGoal, Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨⟨gv, gf⟩, gfd⟩, gmd⟩, grs⟩, _⟩ := hg
  have e : ∀ i ∈ [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed], Q.w i = false →
      (runSub H₁ sy.ImposeFriction lr 0 0).ram.get! i = (runSub H₂ sy.ImposeFriction lr 0 0).ram.get! i := by
    intro i hi hw
    have hl : i < 2048 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> exact I_lt _
    obtain ⟨n1, n2, n3⟩ := hdir i hi
    obtain ⟨w1, w2⟩ := hW i hl hw (by rw [s1]; exact n1) (by rw [s1]; exact n2)
    rw [w1, w2, n3]
  exact ⟨tagImp_R gv (hR _ (I_lt _)), tagImp_R gf (hR _ (I_lt _)), e _ (by simp) gfd, e _ (by simp) gmd, by rw [e _ (by simp) grs]⟩

/-- the model's friction with the real bits at the speed 0 leaves the speed 0 -/
theorem zero_runSub {m0 : Machine} {lr : UInt8} {r : UInt16} {H : Machine}
    (hc : walkD (Rom.of m0) [] (mStop r (spM m0)) (fun Q => (Q.ram (I sy.Player_X_Speed)).same == some 0 && stkKept m0 Q) fuelS
      (fricQ sy m0 lr [(I sy.Player_X_Speed, Tag.kn 0 0), (I sy.Player_CollisionBits, Tag.kn sy.noLeft sy.noLeft)]) = true)
    (hr : isRts (Rom.of m0) r = true) (gH : GoodH (Rom.of m0) H) (sH : H.s = m0.s)
    (hst : ∀ i ∈ [I sy.Player_X_Speed, I sy.Player_CollisionBits], i ≠ stkI m0.s ∧ i ≠ stkI (m0.s - 1))
    (hv : H.ram.get! (I sy.Player_X_Speed) = 0) (hb : H.ram.get! (I sy.Player_CollisionBits) = sy.noLeft) :
    (runSub H sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) = 0 := by
  have hgoal : ∀ Q, ((Q.ram (I sy.Player_X_Speed)).same == some 0 && stkKept m0 Q) = true → Q.w (stkI H.s) = false ∧ Q.w (stkI (H.s - 1)) = false := by
    intro Q hQ
    simp only [Bool.and_eq_true] at hQ
    exact stkKept_spec hQ.2 sH
  obtain ⟨Q, _, hg, hR, _⟩ := runSub2 (ds := []) (by simp) hc (by decide) (mstop_spec hr) hgoal gH gH (by rw [sH]; rfl) rfl (Tag.R_kn lr lr) rfl
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · obtain ⟨n1, n2⟩ := hst (I sy.Player_X_Speed) (by simp)
        refine ⟨I_lt _, by rw [sH]; exact n1, by rw [sH]; exact n2, ?_⟩
        show (Tag.kn 0 0).R _ _
        rw [hv]
        exact Tag.R_kn 0 0
      · obtain ⟨n1, n2⟩ := hst (I sy.Player_CollisionBits) (by simp)
        refine ⟨I_lt _, by rw [sH]; exact n1, by rw [sH]; exact n2, ?_⟩
        show (Tag.kn sy.noLeft sy.noLeft).R _ _
        rw [hb]
        exact Tag.R_kn _ _)
    (fun _ _ _ _ _ => rfl)
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  exact (Tag.same_spec hg.1 (hR _ (I_lt _))).1

/-- `GetPlayerAnimSpeed` on a machine of the model writes 0 to the speed, or leaves it -/
theorem gpas_v {m0 A : Machine} {S : UInt8} (hm : MaskFacts sy m0 S) (gA : GoodH (Rom.of m0) A) (sA : A.s = m0.s) :
    (runSub A sy.GetPlayerAnimSpeed 0 0 0).ram.get! (I sy.Player_X_Speed) = A.ram.get! (I sy.Player_X_Speed) ∨
      (runSub A sy.GetPlayerAnimSpeed 0 0 0).ram.get! (I sy.Player_X_Speed) = 0 := by
  have hc := hm.gpas
  unfold gpasOK at hc
  have hgoal : ∀ Q, ((!Q.w (I sy.Player_X_Speed) || (Q.ram (I sy.Player_X_Speed)).same == some 0) && stkKept m0 Q) = true →
      Q.w (stkI A.s) = false ∧ Q.w (stkI (A.s - 1)) = false := by
    intro Q hQ
    simp only [Bool.and_eq_true] at hQ
    exact stkKept_spec hQ.2 sA
  obtain ⟨Q, _, hg, hR, hW⟩ := runSub2 (ds := []) (by simp) hc (by decide) (mstop_spec hm.gret) hgoal gA gA (by rw [sA]; rfl) rfl (Tag.R_kn 0 0) rfl
    (fun p hp => by cases hp) (fun _ _ _ _ _ => rfl)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
  obtain ⟨n1, n2⟩ := hm.stk (I sy.Player_X_Speed) (by simp)
  rcases hg.1 with h | h
  · exact Or.inl (hW _ (I_lt _) h (by rw [sA]; exact n1) (by rw [sA]; exact n2)).1
  · exact Or.inr (Tag.same_spec h (hR _ (I_lt _))).1

/-- what the friction of a masked frame leaves on the real machine: the model's result, or the speed 0 -/
def OutM (sy : Syms) (x y : Machine) : Prop := Rel5 sy x y ∨ x.ram.get! (I sy.Player_X_Speed) = 0

/-- **The friction of a masked frame.** The real machine at `ImposeFriction` with the bits of a block of Left, the model's machine with those of `m0`: the real friction gives
the model's result, or the speed 0. The model's speed there is the state's speed `v0`, moving right, or what `GetPlayerAnimSpeed` leaves of it. -/
theorem fric_masked {m0 : Machine} {S : UInt8} {c : Case} {R R5 C : Machine} {v0 : UInt8}
    (hm : MaskFacts sy m0 S) (hap : Apart sy m0) (hc : caseOK sy m0 S c = true) (hmem : c ∈ allCases)
    (hml : maskedLr sy (lrOf c.n) = true) (hRb : R.ram.get! (I sy.Player_CollisionBits) = sy.noLeft) (hv1 : v0 ≠ 0) (hv2 : v0 < 0x80)
    (hA5 : At (Rom.of m0) (planOf sy m0 S c).c3 R5) (hK : ∀ p ∈ (planOf sy m0 S c).c3.K, p.1 < 2048)
    (gC : GoodH (Rom.of m0) C) (sC : C.s = m0.s) (hrel : ∀ p ∈ tagsFric0 sy, p.2.R (R5.ram.get! p.1) (C.ram.get! p.1))
    (hbR : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits))
    (hbC : C.ram.get! (I sy.Player_CollisionBits) = m0.ram.get! (I sy.Player_CollisionBits))
    (hCv : SpeedFrom sy m0 v0 C) :
    FricStage sy m0 (planOf sy m0 S c).c4 (lrOf c.n) (OutM sy) R5 C := by
  have hl0 : lrOf c.n ≠ 0 := by
    intro e
    rw [e] at hml
    simp [maskedLr] at hml
  have fc := fricOK_of hc (Or.inr hl0)
  simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
  obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
  have hN := hm.cases c hmem
  simp only [maskCaseOK, hml, Bool.not_true, Bool.false_or] at hN
  -- the model's machine with the real bits
  generalize hNe : poke C sy.Player_CollisionBits sy.noLeft = N
  have gN : GoodH (Rom.of m0) N := by rw [← hNe]; exact poke_good _ _ gC
  have sN : N.s = m0.s := by rw [← hNe]; exact (poke_s _ _ _).trans sC
  have hNo : ∀ j, I sy.Player_CollisionBits ≠ j → N.ram.get! j = C.ram.get! j := fun j hj => by
    rw [← hNe]
    exact poke_get_ne _ _ _ hj
  have hNb : N.ram.get! (I sy.Player_CollisionBits) = sy.noLeft := by rw [← hNe]; exact poke_get_self _ _ gC.size
  have hap0 : ∀ p ∈ tagsFric0 sy, I sy.Player_CollisionBits ≠ p.1 := fun p hp e => hm.apart p hp e.symm
  have hrelN : ∀ p ∈ tagsFricN sy, p.2.R (R5.ram.get! p.1) (N.ram.get! p.1) := by
    intro p hp
    simp only [tagsFricN, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · rw [hNo _ (hap0 p hp)]
      exact hrel p hp
    · show (Tag.kn sy.noLeft sy.noLeft).R _ _
      rw [hbR, hRb, hNb]
      exact Tag.R_kn _ _
  obtain ⟨k, hk, A4, R1, S1, C1⟩ := fric_stage hN d4 d1 d2 hA5 hK gN sN hrelN
  refine ⟨k, hk, A4, ?_, S1, C1⟩
  -- the model's friction with the real bits next to the model's
  have hvb : I sy.Player_CollisionBits ≠ I sy.Player_X_Speed := hap0 (I sy.Player_X_Speed, .eq) (by simp [tagsFric0])
  have hstv := hap.st (I sy.Player_X_Speed) (by simp [pokeIdx])
  have hstb := hap.st (I sy.Player_CollisionBits) (by simp)
  have hdir : ∀ i ∈ [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed], i ≠ stkI m0.s ∧ i ≠ stkI (m0.s - 1) ∧ N.ram.get! i = C.ram.get! i := by
    intro i hi
    have h1 : i ∈ pokeIdx sy := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simp [pokeIdx]
    have h2 : I sy.Player_CollisionBits ≠ i := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hap0 (I sy.PlayerFacingDir, .eq) (by simp [tagsFric0])
      · exact hap0 (I sy.Player_MovingDir, .eq) (by simp [tagsFric0])
      · exact hap0 (I sy.RunningSpeed, .nz) (by simp [tagsFric0])
    obtain ⟨n1, n2⟩ := hap.st i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1))
    exact ⟨n1, n2, hNo i h2⟩
  have hbT : (Tag.kn sy.noLeft (bits0 sy m0)).R (N.ram.get! (I sy.Player_CollisionBits)) (C.ram.get! (I sy.Player_CollisionBits)) := by
    rw [hNb, hbC]
    exact Tag.R_kn _ _
  have hmod := hm.model (lrOf c.n) (lrOf_mem _)
  simp only [maskModelOK, hml, Bool.not_true, Bool.false_or] at hmod
  by_cases hlr3 : (sy.noLeft &&& lrOf c.n != 0) = true
  · -- Left and Right: the two take the same way
    rw [if_pos hlr3] at hmod
    have e := rel_runSub (H₁ := N) (H₂ := C) (ds := []) (by simp) hmod hm.fret gN gC sN sC
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨I_lt _, hstb.1, hstb.2, hbT⟩)
      (fun i hn => hNo i (lookN_none hn _ (List.mem_cons_self)))
      hdir
    exact Or.inl (R1.trans e)
  · rw [if_neg hlr3] at hmod
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hmod
    obtain ⟨hall, hzero⟩ := hmod
    have hCv' : C.ram.get! (I sy.Player_X_Speed) = v0 ∨ C.ram.get! (I sy.Player_X_Speed) = 0 := by
      rcases hCv with h | ⟨A, gA, sA, hAv, hCA⟩
      · exact Or.inl h
      · rcases gpas_v hm gA sA with h | h
        · left
          rw [hCA, h, hAv]
        · right
          rw [hCA, h]
    rcases hCv' with hv | hv
    · -- Left alone, moving right: the detour to `RghtFrict`
      have hv3 : v0.toNat < 128 := UInt8.lt_iff_toNat_lt.1 hv2
      have hv4 : v0.toNat ≠ 0 := fun e => hv1 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      have hj : v0.toNat - 1 < 127 := by omega
      have ev : (v0.toNat - 1 + 1).toUInt8 = v0 := by
        rw [Nat.sub_add_cancel (by omega)]
        exact UInt8.toNat_inj.1 (by simp)
      obtain ⟨hdok, hw⟩ := hall _ hj
      rw [ev] at hdok hw
      have e := rel_runSub (H₁ := N) (H₂ := C) (ds := [leftDetour sy m0 (lrOf c.n) v0])
        (fun d hd => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          subst hd
          exact hdok) hw hm.fret gN gC sN sC
        (fun p hp => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · refine ⟨I_lt _, hstv.1, hstv.2, ?_⟩
            show (Tag.kn v0 v0).R _ _
            rw [hNo _ hvb, hv]
            exact Tag.R_kn _ _
          · exact ⟨I_lt _, hstb.1, hstb.2, hbT⟩)
        (fun i hn => hNo i (lookN_none hn _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        hdir
      exact Or.inl (R1.trans e)
    · -- the speed 0: the real friction leaves it 0
      have e := zero_runSub (lr := lrOf c.n) hzero hm.fret gN sN hm.stk (by rw [hNo _ hvb, hv]) hNb
      exact Or.inr (R1.v.trans e)

/-- **The movement of a real frame with the pressed side masked.** From the player's routine to the scroll handler the frame follows `hstep`, or it leaves the speed 0;
the position moves by `16·v'`, modulo the size of the position. The state at the player's routine is `AtCtrl` but the mask; it has the bits of a block of Left,
the side he presses is masked, and he moves right. `hmk` is the check on the ROM of the masked frames. -/
theorem move_masked {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (hmk : maskOK sy m0 S = true) (h : AtCtrl0 sy (Rom.of m0) S R)
    (hRb : peek R sy.Player_CollisionBits = sy.noLeft) (hml : maskedLr sy (lrOf (norm (readIn sy R))) = true)
    (hv1 : peek R sy.Player_X_Speed ≠ 0) (hv2 : peek R sy.Player_X_Speed < 0x80) :
    ∃ k, k ≤ 2 * fuelW + 11 * fuelS ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧
      (readHS sy (stepN k R) = hstep sy m0 (readHS sy R) (readIn sy R) ∨ peek (stepN k R) sy.Player_X_Speed = 0) ∧
      (posP sy (stepN k R) - posP sy R - 16 * sbyte (readHS sy (stepN k R)).v) % 0x1000000 = 0 ∧ InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hm := mfacts_of hmk
  have hb := base_good hF.base
  have hap := apart_of hF.apart
  have hmem := caseOf_mem h
  generalize hc : caseOf sy R = c at hmem
  have hA := at_start h
  rw [hc] at hA
  generalize hrt : (if peek R sy.RunningTimer == 0 then (0 : UInt8) else 1) = rtb
  have hI : readIn sy R = c.inp rtb := by
    rw [readIn_eq, hc, hrt]
  obtain ⟨n1, n2, n3, n4⟩ := norm_fields c rtb
  have hmlC : maskedLr sy (lrOf c.n) = true := by
    rw [hI, lr_of n1 n2] at hml
    exact hml
  have hN : hstep sy m0 (readHS sy R) (readIn sy R) = finishH sy (midH sy m0 (readHS sy R) (norm (c.inp rtb))) := by
    rw [hI]
    exact hstepN_eq _ _ _ _
  obtain ⟨k1, f1, A1, R1, S1, C1⟩ := to_moverG (Out := OutM sy) (i := norm (c.inp rtb)) (s := readHS sy R) hb hap (hF.cases c hmem).1 hA rfl rfl rfl rfl
    (rs_nz sy hap.rmin _) h.abs (by rw [← hc]; rfl)
    (lr_of n1 n2) (st_of n2 n3) (hab_of n1 n3) (hsv_of n1 n3)
    (fun hg => by
      rw [n4, if_pos hg, ← hrt]
      exact rt_nz _)
    (fun _ _ h => Or.inl h)
    (fun _ _ _ hA5 hK gC sC hrel hbR hbC hCv => fric_masked hm hap (hF.cases c hmem).1 hmem hmlC hRb hv1 hv2 hA5 hK gC sC hrel hbR hbC hCv)
  obtain ⟨t, ht, hte⟩ := hF.anyT c hmem
  have e4 : t = (planOf sy m0 S c).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, f2, g2, p2, v2, ff2, d2, r2, m2, q2, C2⟩ := tail_spec htl hF.digits A1
  generalize hR : stepN k1 R = R1' at A1 R1 S1 v2 ff2 d2 r2 m2 q2 g2 p2 C2
  have hfin : stepN (k1 + k2) R = stepN k2 R1' := by rw [stepN_add, hR]
  refine ⟨k1 + k2, by omega, by rw [hfin]; exact g2, by rw [hfin]; exact p2, ?_, ?_, InFrameN.add' C1 hR C2⟩
  · rw [hfin]
    rcases R1 with R1 | R1
    · left
      rw [hN]
      refine readHS_of (v2.trans R1.v) (ff2.trans R1.f) (d2.trans R1.fd) (by rw [r2]; exact R1.rs) ?_
      rw [m2, R1.v, R1.md]
    · right
      show (stepN k2 R1').ram.get! (I sy.Player_X_Speed) = 0
      rw [v2]
      exact R1
  · rw [hfin]
    obtain ⟨s1, s2, s3⟩ := S1
    have e : posP sy R1' = posP sy R := by
      rw [posP_eq, posP_eq]
      show posOf (R1'.ram.get! (I sy.Player_PageLoc)) (R1'.ram.get! (I sy.Player_X_Position)) (R1'.ram.get! (I sy.SprObject_X_MoveForce)) =
        posOf (R.ram.get! (I sy.Player_PageLoc)) (R.ram.get! (I sy.Player_X_Position)) (R.ram.get! (I sy.SprObject_X_MoveForce))
      rw [s1, s2, s3]
    have e2 : (readHS sy (stepN k2 R1')).v = R1'.ram.get! (I sy.Player_X_Speed) := v2
    rw [e2, ← e]
    exact q2


/-! ## A frame -/

/-- the instructions from the player's routine to the scroll handler, at most -/
def moveLen : Nat := 2 * fuelW + 11 * fuelS

/-- the stack pointer at the player's routine -/
def ctrlStack (sy : Syms) (m0 : Machine) : UInt8 :=
  match PipeEntryRule.firstAt sy.PlayerCtrlRoutine 100000 { m0 with pad := 0x01 } with
  | some m => m.s
  | none => 0

/-- the bytes of the horizontal state and of the position -/
def hBytes (sy : Syms) : List UInt16 :=
  [sy.Player_X_Speed, sy.Player_X_MoveForce, sy.PlayerFacingDir, sy.Player_MovingDir, sy.RunningSpeed, sy.Player_X_Position, sy.Player_PageLoc, sy.SprObject_X_MoveForce]

/-- **A frame that follows the model**, on one frame: the frame of `M` with the input `i`, which comes to the player's routine at the instruction `n₀`. -/
structure Clean (sy : Syms) (E : Rom) (S : UInt8) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  /-- it comes to the player's routine in the state `AtCtrl` -/
  at_ctrl : AtCtrl sy E S (trace M i n₀)
  /-- until then nothing wrote the horizontal bytes -/
  before : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a
  /-- the frame does not end during the movement -/
  longer : ((trace M i (n₀ + moveLen)).frame ≥ M.frame + 1 || (trace M i (n₀ + moveLen)).halted) = false
  /-- from the scroll handler on, nothing writes them: the collision routine does not stop him -/
  after : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → ∀ a ∈ hBytes sy, peek (frame M i) a = peek (trace M i j) a
  /-- the position is away from both ends of its range -/
  far : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000

theorem trace_steps {M : Machine} {i : UInt8} {n₀ K : Nat} (h : ((trace M i (n₀ + K)).frame ≥ M.frame + 1 || (trace M i (n₀ + K)).halted) = false) :
    ∀ k, k ≤ K → trace M i (n₀ + k) = stepN k (trace M i n₀) := by
  intro k
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : ((trace M i (n₀ + k)).frame ≥ M.frame + 1 || (trace M i (n₀ + k)).halted) = false := by
      cases h3 : ((trace M i (n₀ + k)).frame ≥ M.frame + 1 || (trace M i (n₀ + k)).halted) with
      | false => rfl
      | true =>
        have e := trace_stop h3 (K - k)
        have e2 : n₀ + k + (K - k) = n₀ + K := by omega
        rw [e2] at e
        rw [e, h3] at h
        cases h
    rw [stepN_succ, ← h1]
    show nxt (M.frame + 1) (trace M i (n₀ + k)) = _
    unfold nxt
    rw [if_neg (by rw [h2]; decide)]

/-- **The frame does not end during a walked run.** The machines of the next `k` steps from the machine `R` at the instruction `n₀` of the frame meet `InFrame` (`InFrameN`, from the
walks), and each instruction of the frame that is not at the idle loop runs at a dot at least 64 before the frame's end (`ht`: the condition `time` of `FrameKeep.CleanK`). The idle
loop is a `JMP` to itself. Then the frame does not end in these `k` steps, and they are the steps of the frame. -/
theorem trace_inFrame {E : Rom} {M : Machine} {i : UInt8} {n₀ k : Nat} {idle : UInt16} (hidle : idleAt E idle = true)
    (hR : (trace M i n₀).frame = M.frame) (hc : InFrameN E (trace M i n₀) k)
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64) :
    ∀ j, j ≤ k → trace M i (n₀ + j) = stepN j (trace M i n₀) ∧ (trace M i (n₀ + j)).frame = M.frame := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, hR⟩
  | succ j ih =>
    intro hj
    obtain ⟨e1, e2⟩ := ih (by omega)
    have C := hc j (by omega)
    have hne : (stepN j (trace M i n₀)).pc ≠ idle := by
      intro e
      have h1 := C.idle
      rw [e, hidle] at h1
      cases h1
    have hfr : (stepN j (trace M i n₀)).frame = M.frame := by rw [← e1]; exact e2
    have hf : (stepN j (trace M i n₀)).fdot + 64 ≤ dotsPerFrame := by
      have h1 := ht (n₀ + j) (by rw [e1]; exact hne)
      rw [e1] at h1
      have h2 : 64 ≤ dotsPerFrame := by decide
      omega
    have e3 := C.frame hf
    have e4 : trace M i (n₀ + (j + 1)) = (PipeTransitionAll.go step (stepN j (trace M i n₀))).2 := by
      show nxt (M.frame + 1) (trace M i (n₀ + j)) = _
      rw [e1]
      unfold nxt
      rw [if_neg (by rw [hfr, C.halted]; simp)]
    refine ⟨by rw [e4, stepN_succ], ?_⟩
    rw [e4, e3, hfr]

theorem readHS_congr {x y : Machine} (h : ∀ a ∈ hBytes sy, peek x a = peek y a) : readHS sy x = readHS sy y := by
  simp only [readHS, h _ (show sy.Player_X_Speed ∈ hBytes sy by simp [hBytes]), h _ (show sy.Player_X_MoveForce ∈ hBytes sy by simp [hBytes]),
    h _ (show sy.PlayerFacingDir ∈ hBytes sy by simp [hBytes]), h _ (show sy.Player_MovingDir ∈ hBytes sy by simp [hBytes]), h _ (show sy.RunningSpeed ∈ hBytes sy by simp [hBytes])]

theorem posP_congr {x y : Machine} (h : ∀ a ∈ hBytes sy, peek x a = peek y a) : posP sy x = posP sy y := by
  rw [posP_eq, posP_eq, h _ (show sy.Player_PageLoc ∈ hBytes sy by simp [hBytes]), h _ (show sy.Player_X_Position ∈ hBytes sy by simp [hBytes]), h _ (show sy.SprObject_X_MoveForce ∈ hBytes sy by simp [hBytes])]

theorem posOf_range (p x f : UInt8) : 0 ≤ posOf p x f ∧ posOf p x f < 0x1000000 := by
  have h1 := p.toNat_lt
  have h2 := x.toNat_lt
  have h3 := f.toNat_lt
  unfold posOf
  omega

theorem sbyte_range (v : UInt8) : -128 ≤ sbyte v ∧ sbyte v ≤ 127 := by
  unfold sbyte
  have h1 := v.toNat_lt
  split
  · rename_i h
    have h2 : v.toNat < (0x80 : UInt8).toNat := UInt8.lt_iff_toNat_lt.1 h
    have h3 : (0x80 : UInt8).toNat = 128 := rfl
    omega
  · rename_i h
    have h2 : ¬ v.toNat < (0x80 : UInt8).toNat := fun e => h (UInt8.lt_iff_toNat_lt.2 e)
    have h3 : (0x80 : UInt8).toNat = 128 := rfl
    omega

/-- **A real frame follows the model.** -/
theorem clean_frame {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (hOK : modelOK sy m0 S = true) (h : Clean sy (Rom.of m0) S M i n₀) :
    readHS sy (frame M i) = hstep sy m0 (readHS sy M) (readIn sy (trace M i n₀)) ∧
      posP sy (frame M i) = posP sy M + 16 * sbyte (readHS sy (frame M i)).v := by
  obtain ⟨k, hk, _, hpc, h1, h2, _⟩ := move_model hOK h.at_ctrl
  have e0 := trace_steps h.longer k hk
  have e1 := h.after (n₀ + k) (by omega) (by rw [e0]; exact hpc)
  rw [e0] at e1
  have e2 : readHS sy (trace M i n₀) = readHS sy M := readHS_congr h.before
  have e3 : posP sy (trace M i n₀) = posP sy M := posP_congr h.before
  have e4 := readHS_congr (sy := sy) e1
  have e5 := posP_congr (sy := sy) e1
  rw [e2] at h1
  rw [e3] at h2
  rw [← e4] at h1 h2
  rw [← e5] at h2
  refine ⟨h1, ?_⟩
  obtain ⟨a1, a2⟩ := posOf_range (peek (frame M i) sy.Player_PageLoc) (peek (frame M i) sy.Player_X_Position) (peek (frame M i) sy.SprObject_X_MoveForce)
  have a3 := sbyte_range (readHS sy (frame M i)).v
  have a4 := h.far
  rw [← posP_eq] at a1 a2
  omega

theorem readIn_mem (hj : joyOK = true) (m : Machine) : readIn sy m ∈ Potential.inputs := by
  simp only [joyOK, List.all_eq_true, List.contains_iff_mem] at hj
  have h1 := hj _ (Potential.mem_bytes (peek m sy.SavedJoypadBits))
  have h2 : (if peek m sy.RunningTimer == 0 then (0 : UInt8) else 1) ∈ [(0 : UInt8), 1] := by
    split <;> simp
  by_cases h0 : (peek m sy.Player_State == 0) = true
  · have e : readIn sy m = { st := 0, jump := peek m sy.SavedJoypadBits &&& 0x80 != 0 && peek m sy.PreviousA_B_Buttons &&& 0x80 == 0, joy := joyOf (peek m sy.SavedJoypadBits), rt := if peek m sy.RunningTimer == 0 then 0 else 1 } := by
      simp only [readIn, h0, if_true, Bool.true_and]
    rw [e]
    refine List.mem_flatMap.2 ⟨((0 : UInt8), peek m sy.SavedJoypadBits &&& 0x80 != 0 && peek m sy.PreviousA_B_Buttons &&& 0x80 == 0), ?_, List.mem_flatMap.2 ⟨_, h1, List.mem_map.2 ⟨_, h2, rfl⟩⟩⟩
    cases (peek m sy.SavedJoypadBits &&& 0x80 != 0 && peek m sy.PreviousA_B_Buttons &&& 0x80 == 0) <;> simp
  · have h3 : (peek m sy.Player_State == 0) = false := by simpa using h0
    have e : readIn sy m = { st := 1, jump := false, joy := joyOf (peek m sy.SavedJoypadBits), rt := if peek m sy.RunningTimer == 0 then 0 else 1 } := by
      simp only [readIn, h3, Bool.false_and, Bool.false_eq_true, if_false]
    rw [e]
    exact List.mem_flatMap.2 ⟨((1 : UInt8), false), by simp, List.mem_flatMap.2 ⟨_, h1, List.mem_map.2 ⟨_, h2, rfl⟩⟩⟩

theorem joy_of_model {m0 : Machine} {S : UInt8} (h : modelOK sy m0 S = true) : joyOK = true := (facts_of h).joy

end chain

/-! ## `TopSpeed.Frame` on real machines -/

section frames
variable {sy : Syms} {E : Rom}

theorem foldl_mem : ∀ (l : List Int) (a x : Int), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by cases h
  | y :: l, a, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · have h1 := FastAccel.foldl_max_ge l (max a x)
      simp only [List.foldl_cons]
      omega
    · exact foldl_mem l _ _ h

theorem adder_le {m : Machine} {lo hi : UInt8} (h : (lo, hi) ∈ adders sy m) : (256 * hi.toNat + lo.toNat : Int) ≤ amax sy m :=
  foldl_mem _ _ _ (List.mem_map.2 ⟨(lo, hi), h, rfl⟩)

theorem capsGood_spec {m0 : Machine} {Q : TS} {r r' : Machine} {m₀ n₀ : Machine} (he : capsGood sy m0 Q = true) (h : Lk E m₀ n₀ Q r r') :
    ∃ mr ml lo hi, r.ram.get! (I sy.MaximumRightSpeed) = mr ∧ r.ram.get! (I sy.MaximumLeftSpeed) = ml ∧ r.ram.get! (I sy.FrictionAdderLow) = lo ∧
      r.ram.get! (I sy.FrictionAdderHigh) = hi ∧ mr ∈ maxRs sy m0 ∧ ml ∈ maxLs sy m0 ∧ (lo, hi) ∈ adders sy m0 := by
  unfold capsGood at he
  split at he
  · rename_i mr ml lo hi h1 h2 h3 h4
    simp only [Bool.and_eq_true, List.contains_iff_mem] at he
    exact ⟨mr, ml, lo, hi, (Tag.same_spec h1 (h.ram _ (I_lt _))).1, (Tag.same_spec h2 (h.ram _ (I_lt _))).1, (Tag.same_spec h3 (h.ram _ (I_lt _))).1,
      (Tag.same_spec h4 (h.ram _ (I_lt _))).1, he.1.1, he.1.2, he.2⟩
  · cases he

theorem animGood_spec {Q : TS} {m r : Machine} (he : animGood sy Q = true) (h : Lk E m m Q r r) :
    (r.ram.get! (I sy.Player_X_Speed) = m.ram.get! (I sy.Player_X_Speed) ∧ r.ram.get! (I sy.Player_X_MoveForce) = m.ram.get! (I sy.Player_X_MoveForce)) ∨
      (r.ram.get! (I sy.Player_X_Speed) = 0 ∧ r.ram.get! (I sy.Player_X_MoveForce) = 0) := by
  simp only [animGood, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at he
  rcases he with he | he
  · exact Or.inl ⟨h.fixl _ (I_lt _) he.1, h.fixl _ (I_lt _) he.2⟩
  · exact Or.inr ⟨(Tag.same_spec he.1 (h.ram _ (I_lt _))).1, (Tag.same_spec he.2 (h.ram _ (I_lt _))).1⟩

/-- the speed is in the range, and the fraction a byte -/
def gainOK (sy : Syms) (m0 r : Machine) (v₁ f₁ : UInt8) : Prop :=
  TopSpeed.inSpeed sy (r.ram.get! (I sy.Player_X_Speed)) = true ∧
    256 * sbyte (r.ram.get! (I sy.Player_X_Speed)) + ((r.ram.get! (I sy.Player_X_MoveForce)).toNat : Int) ≤ max (256 * sbyte v₁ + (f₁.toNat : Int)) 0 + amax sy m0

/-- the stage of `ImposeFriction` next to `frictionCheck` -/
theorem fric_read {m0 : Machine} {c3 c4 : Cut} {r3 : UInt16} {lr : UInt8} {R : Machine} {mr ml lo hi : UInt8}
    (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hnd : nodupB (fricIdx sy) = true) (hsp : (TopSpeed.speedsB sy).contains (R.ram.get! (I sy.Player_X_Speed)) = true)
    (h1 : leafAll (Rom.of m0) m0.s sy.ImposeFriction r3 (Tag.kn lr lr) (tagsFr sy) [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq)]
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ c3.ids) = true)
    (h2 : pieceOK (Rom.of m0) (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction) (hlr : (TopSpeed.upTo 3).contains lr = true)
    (hA : At (Rom.of m0) c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048)
    (e1 : R.ram.get! (I sy.MaximumRightSpeed) = mr) (e2 : R.ram.get! (I sy.MaximumLeftSpeed) = ml) (e3 : R.ram.get! (I sy.FrictionAdderLow) = lo) (e4 : R.ram.get! (I sy.FrictionAdderHigh) = hi)
    (m1 : mr ∈ maxRs sy m0) (m2 : ml ∈ maxLs sy m0) (m3 : (lo, hi) ∈ adders sy m0) (hcb : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy) :
    ∃ k, k ≤ 2 * fuelS ∧ At (Rom.of m0) c4 (stepN k R) ∧ gainOK sy m0 (stepN k R) (R.ram.get! (I sy.Player_X_Speed)) (R.ram.get! (I sy.Player_X_MoveForce)) ∧ Same3 sy (stepN k R) R := by
  generalize hv0 : R.ram.get! (I sy.Player_X_Speed) = v at hsp
  generalize hf0 : R.ram.get! (I sy.Player_X_MoveForce) = f
  generalize hc0 : R.ram.get! (I sy.Player_CollisionBits) = cb at hcb
  have hH := pokeL_good (fricL sy v f lo hi mr ml cb) hb
  have hHs : (pokeL m0 (fricL sy v f lo hi mr ml cb)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ fricL sy v f lo hi mr ml cb, (pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! (I q.1) = q.2 := pokeL_get _ _ hb hnd
  have hrel : ∀ p ∈ tagsFr sy, p.2.R (R.ram.get! p.1) ((pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! p.1) := by
    intro p hp
    simp only [tagsFr, fricIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show _ = _
      rw [hget (sy.Player_X_Speed, v) (by simp [fricL])]
      exact hv0
    · show _ = _
      rw [hget (sy.Player_X_MoveForce, f) (by simp [fricL])]
      exact hf0
    · show _ = _
      rw [hget (sy.FrictionAdderLow, lo) (by simp [fricL])]
      exact e3
    · show _ = _
      rw [hget (sy.FrictionAdderHigh, hi) (by simp [fricL])]
      exact e4
    · show _ = _
      rw [hget (sy.MaximumRightSpeed, mr) (by simp [fricL])]
      exact e1
    · show _ = _
      rw [hget (sy.MaximumLeftSpeed, ml) (by simp [fricL])]
      exact e2
    · show _ = _
      rw [hget (sy.Player_CollisionBits, cb) (by simp [fricL])]
      exact hc0
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, f1, g1, p1, s1, o1, w1, _, _, _⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) hH hHs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK3 p hp))
  obtain ⟨k2, f2, A2, W2, _⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have oV : (stepN k1 R).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := o1 (I sy.Player_X_Speed, .eq) (by simp)
  have oF : (stepN k1 R).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := o1 (I sy.Player_X_MoveForce, .eq) (by simp)
  -- what `frictionCheck` says
  have hC := hfr
  simp only [TopSpeed.frictionCheck, List.all_eq_true] at hC
  have hq := hC v (List.contains_iff_mem.1 hsp) f (Potential.mem_bytes f) (lo, hi) m3 mr m1 ml m2 lr (List.contains_iff_mem.1 hlr) cb hcb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have hk : pokeL m0 (fricL sy v f lo hi mr ml cb) = poke (poke (poke (poke (poke (poke (poke m0 sy.Player_X_Speed v) sy.Player_X_MoveForce f) sy.FrictionAdderLow lo) sy.FrictionAdderHigh hi) sy.MaximumRightSpeed mr) sy.MaximumLeftSpeed ml) sy.Player_CollisionBits cb := by
    simp only [fricL, pokeL]
  rw [← hk] at hq
  have hal := adder_le m3
  have w1' : ∀ i, i ∈ [I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] → (stepN k1 R).ram.get! i = R.ram.get! i := by
    intro i hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
  refine ⟨k1 + k2, by omega, by rw [e]; exact A2, ?_, ?_⟩
  · rw [e]
    have e5 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := by
      rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oV
    have e6 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := by
      rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oF
    refine ⟨?_, ?_⟩
    · rw [e5]
      exact hq.1.1
    · rw [e5, e6]
      have h7 := hq.2
      have h8 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := rfl
      have h9 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := rfl
      rw [h8, h9] at h7
      omega
  · rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]

/-- the state at the player's routine that a `TopSpeed.Frame` needs: nothing about the stored speed; the mask and the speed as `TopSpeed`'s checks have them -/
structure AtFrame (sy : Syms) (E : Rom) (S : UInt8) (m : Machine) : Prop where
  good : Good E m
  pc : m.pc = sy.PlayerCtrlRoutine
  s : m.s = S
  eng : peek m sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8
  area : peek m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  st : peek m sy.Player_State ∈ [(0 : UInt8), 1, 2]
  spring : peek m sy.JumpspringAnimCtrl = 0
  swim : peek m sy.SwimmingFlag = 0
  size : peek m sy.PlayerChangeSizeFlag = 0
  coll : peek m sy.Player_CollisionBits ∈ TopSpeed.collBits sy
  speed : TopSpeed.inSpeed sy (peek m sy.Player_X_Speed) = true

theorem at_startF {S : UInt8} {R : Machine} (h : AtFrame sy E S R) : At E ((caseOf sy R).c0 sy S) R := by
  refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.eng
    · rfl
    · rfl
    · rfl
    · exact h.spring
    · exact h.swim
    · exact h.size
  · intro p hp
    simp only [Case.c0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact and80_mem _
  · intro v hv
    cases hv
  · intro v hv
    cases hv
  · intro v hv
    cases hv

theorem caseOf_memF {S : UInt8} {R : Machine} (h : AtFrame sy E S R) : caseOf sy R ∈ allCases := by
  refine List.mem_flatMap.2 ⟨_, h.st, List.mem_flatMap.2 ⟨_, h.area, List.mem_flatMap.2 ⟨peek R sy.PreviousA_B_Buttons &&& 0x80 != 0, by cases (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) <;> simp, ?_⟩⟩⟩
  refine List.mem_map.2 ⟨(peek R sy.SavedJoypadBits).toNat, List.mem_range.2 (peek R sy.SavedJoypadBits).toNat_lt, ?_⟩
  simp [caseOf]

theorem speed_list (hF : ∀ v ∈ TopSpeed.bytes, (!TopSpeed.inSpeed sy v || (TopSpeed.speedsB sy).contains v) = true) {v : UInt8} (h : TopSpeed.inSpeed sy v = true) :
    (TopSpeed.speedsB sy).contains v = true := by
  have e := hF v (Potential.mem_bytes v)
  rw [h] at e
  simpa using e

/-- from the player's routine to the mover, for `TopSpeed.Frame` -/
theorem frame_path {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k v₁ f₁, k ≤ fuelW + 6 * fuelS ∧ At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      ((v₁ = R.ram.get! (I sy.Player_X_Speed) ∧ f₁ = R.ram.get! (I sy.Player_X_MoveForce)) ∨ (v₁ = 0 ∧ f₁ = 0)) ∧
      gainOK sy m0 (stepN k R) v₁ f₁ ∧ Same3 sy (stepN k R) R := by
  have hmem := caseOf_memF h
  have hA := at_startF h
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  generalize hcc : caseOf sy R = c at hmem hA hc hc2 ⊢
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  generalize planOf sy m0 S c = P at hc hc2 ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨hlr, x1⟩, x2⟩, x3⟩ := hc2
  have hzero : TopSpeed.inSpeed sy (0 : UInt8) = true := by
    simp only [TopSpeed.inSpeed, decide_eq_true_eq]
    show ((0 : Int)).natAbs ≤ _
    simp
  have hsp : TopSpeed.inSpeed sy (R.ram.get! (I sy.Player_X_Speed)) = true := h.speed
  have hco : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy := h.coll
  obtain ⟨k1, f1, A1, W1, B1, _⟩ := piece_spec a1 hA
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  obtain ⟨k2, Q2, f2, A2, W2, _, cg, L2, _⟩ := piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
  generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
  obtain ⟨mr, ml, lo, hi, c1, c2, c3, c4, m1, m2, m3⟩ := capsGood_spec cg L2
  have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
  have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl => by
    rw [wX j (List.mem_cons_of_mem _ hj) hl, wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl]
  have hS2 : Same3 sy R2 R := ⟨hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)⟩
  have spL := fun {v : UInt8} (e : TopSpeed.inSpeed sy v = true) => speed_list hF.scomp e
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨b1, b2⟩, _⟩, b4⟩, b5⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, f3, A3, W3, B3, _⟩ := piece_spec b2 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have x2' : walkT (Rom.of m0) (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2) = true := by
      rcases x2 with x2 | x2
      · exact absurd h0 x2
      · exact x2
    obtain ⟨k4, Q4, f4, A4, W4, _, ag, L4, _⟩ := piece_specX (c' := afterLeaf P.c2 P.r2) (extra := animGood sy) x2' A3
    generalize hR4 : stepN k4 R3 = R4 at A4 W4 L4
    have an := animGood_spec ag L4
    obtain ⟨k5, f5, A5, W5, B5, _⟩ := piece_spec b4 A4
    generalize hR5 : stepN k5 R4 = R5 at A5 W5
    have wf : ∀ j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy,
        j < 2048 → R5.ram.get! j = R4.ram.get! j := fun j hj hl => W5 j (List.mem_append_left _ hj) hl
    have hCaps : ∀ j ∈ capsL sy, R5.ram.get! j = R2.ram.get! j := fun j hj => by
      have hl : j < 2048 := by
        simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
      rw [wf j (List.mem_append_right _ hj) hl, W4 j (List.mem_append_right _ hj) hl, W3 j (by
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl]
    have hcoll5 : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
      rw [wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hsp5 : TopSpeed.inSpeed sy (R5.ram.get! (I sy.Player_X_Speed)) = true := by
      rw [wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · rw [an.1, W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact hsp
      · rw [an.1]
        exact hzero
    obtain ⟨k6, f6, A6, G6, S6⟩ := fric_read hb hfr hF.fnd (spL hsp5) (x3.resolve_left (fun e => e.1 h0)) d4 d1 d2 hlr A5 B5
      (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
      m1 m2 m3 (by rw [hcoll5]; exact hco)
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = stepN k6 R5 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), R5.ram.get! (I sy.Player_X_Speed), R5.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, ?_, by rw [hfin]; exact G6, ?_⟩
    · rw [wf _ (by simp) (I_lt _), wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · left
        rw [an.1, an.2, W3 _ (by simp [watchA, watchH]) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact ⟨rfl, rfl⟩
      · exact Or.inr an
    · rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
  · simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
      obtain ⟨k3, f3, A3, W3, B3, _⟩ := piece_spec g A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
        have hl : j < 2048 := by
          simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
        exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e3 : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hne : lrOf c.n ≠ 0 := by simpa using hl
      obtain ⟨k6, f6, A6, G6, S6⟩ := fric_read hb hfr hF.fnd (spL (by rw [e1]; exact hsp)) (x3.resolve_left (fun e => hne e.2)) d4 d1 d2 hlr A3 B3
        (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
        m1 m2 m3 (by rw [e3]; exact hco)
      have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + (k3 + k6)), R3.ram.get! (I sy.Player_X_Speed), R3.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, Or.inl ⟨e1, e2⟩, by rw [hfin]; exact G6, ?_⟩
      rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
    · -- in the air, with neither
      rw [if_neg hl] at a9
      obtain ⟨k3, f3, A3, W3, _⟩ := piece_spec a9 A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, hR3]
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      refine ⟨k1 + (k2 + k3), R.ram.get! (I sy.Player_X_Speed), R.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A3, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
      · rw [hfin]
        refine ⟨by rw [e1]; exact hsp, ?_⟩
        rw [e1, e2]
        have := FastAccel.amax_nonneg sy m0
        omega
      · rw [hfin]
        obtain ⟨t1, t2, t3⟩ := hS2
        refine ⟨?_, ?_, ?_⟩
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t3]

/-- what the collision routine and the rest of the frame do: `B` is the machine at the scroll handler, `F` at the frame's end -/
structure Collide (sy : Syms) (B F : Machine) : Prop where
  v : peek F sy.Player_X_Speed = peek B sy.Player_X_Speed ∨ peek F sy.Player_X_Speed = 0
  f : peek F sy.Player_X_MoveForce = peek B sy.Player_X_MoveForce
  P : posP sy F = posP sy B ∨ posP sy F = posP sy B - 256 ∨ (posP sy F = posP sy B + 256 ∧ sbyte (peek B sy.Player_X_Speed) ≤ 0)

/-- **A frame that is a `TopSpeed.Frame`**, on one frame -/
structure ReadFrame (sy : Syms) (E : Rom) (S : UInt8) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  at_frame : AtFrame sy E S (trace M i n₀)
  before : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a
  longer : ((trace M i (n₀ + moveLen)).frame ≥ M.frame + 1 || (trace M i (n₀ + moveLen)).halted) = false
  collide : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → Collide sy (trace M i j) (frame M i)
  far : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000

theorem speed_int {v : UInt8} (h : TopSpeed.inSpeed sy v = true) : -(TopSpeed.top sy : Int) ≤ sbyte v ∧ sbyte v ≤ (TopSpeed.top sy : Int) := by
  simp only [TopSpeed.inSpeed, decide_eq_true_eq] at h
  omega

/-- **A real frame is a `TopSpeed.Frame`.** -/
theorem frame_read {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} (hOK : modelOK sy m0 S = true) (hfr : TopSpeed.frictionCheck sy m0 = true) (h : ReadFrame sy (Rom.of m0) S M i n₀) :
    ∃ f : TopSpeed.Frame (TopSpeed.top sy : Int) (amax sy m0), f.v = sbyte (peek M sy.Player_X_Speed) ∧ f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ f.f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧ f.P' = posP sy (frame M i) := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, S1⟩ := frame_path hb hfr hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 S (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, _⟩ := tail_spec htl hF.digits A1
  have hk : k1 + k2 ≤ moveLen := by
    show k1 + k2 ≤ 2 * fuelW + 11 * fuelS
    omega
  have e0 := trace_steps h.longer (k1 + k2) hk
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have hco := h.collide (n₀ + (k1 + k2)) (by omega) (by rw [e0]; exact p2)
  rw [e0] at hco
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek M sy.Player_X_Speed := h.before _ (by simp [hBytes])
  have ef : peek (trace M i n₀) sy.Player_X_MoveForce = peek M sy.Player_X_MoveForce := h.before _ (by simp [hBytes])
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr h.before
  have hsp : TopSpeed.inSpeed sy (peek (trace M i n₀) sy.Player_X_Speed) = true := h.at_frame.speed
  obtain ⟨g1, g2'⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hf2 : B.ram.get! (I sy.Player_X_MoveForce) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce) := ff2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := h.far
    rw [ePk, eP] at q2
    omega
  have hfr1 := ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce)).toNat_lt
  refine ⟨{ v := sbyte (peek M sy.Player_X_Speed), f := ((peek M sy.Player_X_MoveForce).toNat : Int), P := posP sy M,
            v₁ := sbyte v₁, f₁ := (f₁.toNat : Int),
            v₂ := sbyte (B.ram.get! (I sy.Player_X_Speed)), f₂ := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P₂ := posP sy B,
            v' := sbyte (peek (frame M i) sy.Player_X_Speed), f' := ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int), P' := posP sy (frame M i),
            anim := ?_, friction := ?_, friction_gain := ?_, frac := ?_, move := hmove, impedeV := ?_, impedeF := ?_, impedeP := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rcases an with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [a1]
        exact congrArg sbyte ev
      · rw [a2]
        exact congrArg (fun x : UInt8 => (x.toNat : Int)) ef
    · right
      rw [a1, a2]
      exact ⟨rfl, rfl⟩
  · intro _
    rw [hv2]
    exact hr1
  · rw [hv2, hf2]
    exact g2'
  · rw [hf2]
    omega
  · rcases hco.v with e | e
    · left
      rw [e]
      rfl
    · right
      rw [e]
      rfl
  · rw [hco.f]
    rfl
  · have e := hco.P
    rcases e with e | e | ⟨e, e2⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · -- the third case of `impedeP` is stated from the frame's start: a push of 1 px after a move left or none
      refine Or.inr (Or.inr ⟨?_, e2⟩)
      have hm := hmove
      have e3 : sbyte (B.ram.get! (I sy.Player_X_Speed)) ≤ 0 := e2
      omega

end frames

/-! ## On real frames: a program, no part of the proof -/

/-- what is wrong with the state at the player's routine, as a list of names -/
def atFails (sy : Syms) (S : UInt8) (m : Machine) : List String :=
  let lr := lrOf (norm (readIn sy m))
  [("pc", m.pc == sy.PlayerCtrlRoutine), ("stack", m.s == S), ("routine", peek m sy.GameEngineSubroutine == sy.Eng_PlayerCtrl.toUInt8),
   ("area", [(1 : UInt8), 2, 3].contains (peek m sy.AreaType)), ("state", [(0 : UInt8), 1, 2].contains (peek m sy.Player_State)),
   ("spring", peek m sy.JumpspringAnimCtrl == 0), ("swim", peek m sy.SwimmingFlag == 0), ("size", peek m sy.PlayerChangeSizeFlag == 0),
   ("stored speed", peek m sy.Player_XSpeedAbsolute == absB (peek m sy.Player_X_Speed)), ("mask", peek m sy.Player_CollisionBits &&& lr == lr),
   ("nmi", !m.nmiPending && m.ppuCtrl &&& 0x80 == 0)].filterMap fun p => if p.2 then none else some p.1

/-- one real frame -/
structure FrameScan where
  /-- the conditions of `Clean` that fail -/
  fails : List String
  /-- the machine at the player's routine -/
  atC : Machine
  /-- at the frame's end -/
  next : Machine
  /-- the program counters of the writes to the horizontal bytes after the scroll handler -/
  writers : List UInt16
  /-- the instructions from the player's routine to the scroll handler, and to the frame's end -/
  len : Nat
  rest : Nat
  /-- the conditions of `ReadFrame` that fail -/
  rfails : List String
  deriving Inhabited

/-- run one real frame, instruction by instruction, and look at the conditions of `Clean` -/
def scanFrame (sy : Syms) (S : UInt8) (m : Machine) (i : UInt8) : FrameScan := Id.run do
  let same := fun (a b : Machine) => (hBytes sy).all fun x => peek a x == peek b x
  let t := m.frame + 1
  let mut c : Machine := { m with pad := smbToPad i }
  let mut n := 0
  let mut arr : Option (Nat × Machine) := none
  let mut sub : Option Nat := none
  let mut subM : Machine := m
  let mut wr : List UInt16 := []
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if arr.isNone && c.pc == sy.PlayerCtrlRoutine then arr := some (n, c)
    if arr.isSome && sub.isNone && c.pc == sy.PlayerSubs then
      sub := some n
      subM := c
    let before := c
    c := (PipeTransitionAll.go step c).2
    if sub.isSome && !same before c then wr := before.pc :: wr
    n := n + 1
  match arr with
  | none => return { fails := ["no arrival"], atC := m, next := c, writers := [], len := 0, rest := 0, rfails := ["no arrival"] }
  | some (n0, a) =>
    let mut f := atFails sy S a
    if !same m a then f := "before" :: f
    if n ≤ n0 + moveLen then f := "short" :: f
    if !wr.isEmpty then f := "after" :: f
    if !(decide (2048 ≤ posP sy m) && decide (posP sy m + 2048 < 0x1000000)) then f := "far" :: f
    if sub.isNone then f := "no scroll handler" :: f
    let at0 := (atFails sy S a).filter fun w => w != "stored speed" && w != "mask"
    let mut rf := at0
    if !(TopSpeed.collBits sy).contains (peek a sy.Player_CollisionBits) then rf := "mask" :: rf
    if !TopSpeed.inSpeed sy (peek a sy.Player_X_Speed) then rf := "speed" :: rf
    if !same m a then rf := "before" :: rf
    if n ≤ n0 + moveLen then rf := "short" :: rf
    if !(decide (2048 ≤ posP sy m) && decide (posP sy m + 2048 < 0x1000000)) then rf := "far" :: rf
    if sub.isNone then rf := "no scroll handler" :: rf
    let vok := peek c sy.Player_X_Speed == peek subM sy.Player_X_Speed || peek c sy.Player_X_Speed == 0
    let fok := peek c sy.Player_X_MoveForce == peek subM sy.Player_X_MoveForce
    let d := posP sy c - posP sy subM
    let pok := d == 0 || d == -256 || (d == 256 && decide (sbyte (peek subM sy.Player_X_Speed) ≤ 0))
    if !(vok && fok && pok) then rf := "collide" :: rf
    return { fails := f, atC := a, next := c, writers := wr, len := (sub.getD n0) - n0, rest := n - n0, rfails := rf }

/-- on a frame with no failing condition, the real frame is the model. The theorem says so: this checks the theorem's statement on a real frame -/
def agrees (sy : Syms) (m0 m : Machine) (r : FrameScan) : Bool :=
  readHS sy r.next == hstep sy m0 (readHS sy m) (readIn sy r.atC) && posP sy r.next == posP sy m + 16 * sbyte (readHS sy r.next).v

end Smbrta.FrameModel
