import Theorems.OpenWalk
import Theorems.OpenJump
import Theorems.OpenVert
import Theorems.RoomVert

/-!
# A frame of the opening in the air, or at a takeoff

A counted frame of the opening that begins in the air (the state 1 or 2) or on the ground with a jump: one walk of `OpenWalk` follows it from the player's routine
(the cut of `CtrlKeep`) to its end. The phase of a state (`AS.log`):

| phase | meaning |
|---|---|
| `[]` | before the scroll handler `Q` (in the air) |
| `[1, 1]`, `[1]` | from `Q` to the collision routine `cE`: no step writes the bytes of `pAll`, no second arrival at `Q` |
| `[2, 1]`, `[2]` | from `cE` on, not landing: the height known below `y₀`, or near the ground and rising; no step writes the bytes of `pAll` |
| `[3, 1]`, `[3]` | from `cE` on, landing: near the ground and falling, the state known 1 or 2; no step writes the bytes of `pRest` |
| `[9, 1]`, `[9]` | from `cE` on, the other states: no second arrival at `Q` |
| `[4]` | after the return `cR` of the collision routine, from `[2]`, `[3]` or `[9]`: the checks at `cR` held, and no step comes to `Q` again |
| `[5, u]` | a takeoff with the stored speed `u`, before `cR`: every vertical byte is known on the way, and at `cR` they are the model's |
| `[7]` | after `cR`, from `[5, u]` |
| `[99]` | a check at `cR` failed: the walk fails |

The mark `1` is the phase's first step (at `Q` or at `cE`). At `cE` a state of the phase `[1]` is split into the pieces of `piecesQ` (the exact heights below
`y₀ + LandDepth` with the high byte 1, and near the ground by bit 7 of the vertical speed and by the state), marked `[2, 1]`, `[3, 1]` or `[9, 1]`. At `cR` each phase is
checked and moved on. The frame's end must be in `[4]` or `[7]`.

There is no game data in this file. Page: `1-1/a-5-7-2-OpenAir.md`.
-/

namespace Smbrta.OpenAir

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard knownOf SG)
open FrameKeep (Watch CfgK Spot CleanK)
open PipeEntryRule (trace)
open OpenWalk (PhK walkP)

/-- a byte's RAM index -/
abbrev I (a : UInt16) : Nat := (a &&& 0x7FF).toNat

/-! ## The bytes -/

/-- the bytes that no step writes from `Q` to the return when he does not land: the vertical bytes of `vstep`, the state, A and B, the high byte of the height, the
jump's halt value -/
def pAll (sy : Syms) : List Nat :=
  [I sy.Player_Y_Position, I sy.Player_Y_MoveForce, I sy.Player_Y_Speed, I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position,
   I sy.Player_State, I sy.A_B_Buttons, I sy.Player_Y_HighPos, I sy.DiffToHaltJump]

/-- the bytes that no step writes from `Q` to the return when he lands: `pAll` but the height, the vertical speed and its fraction and the state -/
def pRest (sy : Syms) : List Nat :=
  [I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.A_B_Buttons, I sy.Player_Y_HighPos, I sy.DiffToHaltJump]

/-! ## What the walk asks -/

/-- the byte is known to be `v` -/
def knIs (b : AB) (v : UInt8) : Bool := b.isK && b.v == v

/-- **the halt relation, known**: the state known not to be 1, or the jump's halt value known to be 1 -/
def haltK (sy : Syms) (A : AS) : Bool :=
  ((A.getK (I sy.Player_State)).isK && (A.getK (I sy.Player_State)).v != 1) || knIs (A.getK (I sy.DiffToHaltJump)) 1

/-- **landed at `y0`**: the height `y0`, the vertical speed and its fraction 0, the state 0 -/
def landedK (sy : Syms) (y0 : UInt8) (A : AS) : Bool :=
  knIs (A.getK (I sy.Player_Y_Position)) y0 && knIs (A.getK (I sy.Player_Y_Speed)) 0 && knIs (A.getK (I sy.Player_Y_MoveForce)) 0 &&
    knIs (A.getK (I sy.Player_State)) 0

/-- **the vertical bytes known to be `s`**, bit 7 of A and B known to be A of `s`, the high byte known 1 and the halt value known 1 -/
def vsK (sy : Syms) (s : Jump.VS) (A : AS) : Bool :=
  knIs (A.getK (I sy.Player_Y_Position)) s.y && knIs (A.getK (I sy.Player_Y_MoveForce)) s.mf && knIs (A.getK (I sy.Player_Y_Speed)) s.vy &&
    knIs (A.getK (I sy.Player_YMF_Dummy)) s.dummy && knIs (A.getK (I sy.VerticalForce)) s.vf && knIs (A.getK (I sy.VerticalForceDown)) s.vfd &&
    knIs (A.getK (I sy.JumpOrigin_Y_Position)) s.origin && knIs (A.getK (I sy.Player_State)) s.st &&
    (A.getK (I sy.A_B_Buttons)).bit 0x80 == some s.prevA && knIs (A.getK (I sy.Player_Y_HighPos)) 1 && knIs (A.getK (I sy.DiffToHaltJump)) 1

/-- the takeoff's state of the model at the end of the frame, for the stored speed `v` -/
def expT (sy : Syms) (m0 : Machine) (v : Nat) : Jump.VS :=
  OpenJump.vstepO sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position) (OpenJump.ground0 (peek m0 sy.Player_Y_Position)) true v.toUInt8

/-! ## The pieces at the scroll handler -/

open RoomVert (canBe canBit withBit)

/-- the state with the height `y` and the high byte 1 known -/
def atY (sy : Syms) (A : AS) (y : UInt8) : AS := (A.setK (I sy.Player_Y_Position) (AB.known y)).setK (I sy.Player_Y_HighPos) (AB.known 1)

/-- **the pieces at `Q`**: each height below `y0` with the high byte 1 (`[2, 1]`); each height from `y0` below `y0 + d`, rising (`[2, 1]`), or falling in the state 1
or 2 (`[3, 1]`); and the state itself (`[9, 1]`) -/
def piecesQ (sy : Syms) (y0 d : UInt8) (A : AS) : List AS :=
  let hy := A.getK (I sy.Player_Y_Position)
  let hh := A.getK (I sy.Player_Y_HighPos)
  let vy := A.getK (I sy.Player_Y_Speed)
  let st := A.getK (I sy.Player_State)
  let low := (List.range y0.toNat).filterMap fun y =>
    if canBe hy y.toUInt8 && canBe hh 1 then some { atY sy A y.toUInt8 with log := [2, 1] } else none
  let near := (List.range d.toNat).flatMap fun j =>
    let y := (y0.toNat + j).toUInt8
    if canBe hy y && canBe hh 1 then
      (if canBit vy 0x80 true then [{ (atY sy A y).setK (I sy.Player_Y_Speed) (withBit vy 0x80 true) with log := [2, 1] }] else []) ++
      ([(1 : UInt8), 2].filterMap fun c => if canBit vy 0x80 false && canBe st c then
        some { ((atY sy A y).setK (I sy.Player_Y_Speed) (withBit vy 0x80 false)).setK (I sy.Player_State) (AB.known c) with log := [3, 1] } else none)
    else []
  low ++ near ++ [{ A with log := [9, 1] }]

/-! ## The phases -/

/-- the state with the bytes of `pAll` forgotten: after the return they are no longer needed, and the states of all heights and speeds join -/
def forgetV (sy : Syms) (A : AS) : AS := (pAll sy).foldl (fun A i => A.setK i AB.top) A

/-- what the walk reads from the ROM and from `m0`, computed once -/
structure Ctx where
  /-- the move routine's spot, the guard, the watched bits at the frame's end -/
  S : Spot
  G : Guard
  W : List Watch
  /-- the bounding box routine and the routine of the buffer's address (for the search's key) -/
  bb : UInt16
  gb : UInt16
  /-- the read of the block buffer routine -/
  R : OpenFlat.Rd1
  /-- the return of the collision routine, and the collision routine (the target of the call before the return) -/
  cR : UInt16
  cE : UInt16
  /-- the ground's height and `LandDepth` -/
  y0 : UInt8
  d : UInt8
  /-- the flag that disables the collision routine, as a RAM index: the operand of the routine's first load -/
  dI : Nat

/-- the context of the opening's machine `m0` and the area's type `v` -/
def ctxOf (sy : Syms) (m0 : Machine) (v : UInt8) : Ctx :=
  { S := FrameKeep.spotOf sy m0, G := OpenFlat.guardQ sy m0, W := OpenFlat.watchF sy m0 v, bb := OpenFlat.bboxOf sy m0, gb := OpenFlat.gbOf sy m0,
    R := OpenFlat.rdOf sy m0, cR := OpenFlat.collRet sy m0,
    cE := (romByte m0 (OpenFlat.collRet sy m0 - 2)).toUInt16 ||| ((romByte m0 (OpenFlat.collRet sy m0 - 1)).toUInt16 <<< 8),
    y0 := peek m0 sy.Player_Y_Position, d := sy.LandDepth.toUInt8, dI := OpenMap.dcdI sy m0 }

/-- **The phases**, read from the list `AS.log` of a state -/
inductive Phase where
  /-- in the air, before `Q` -/
  | pre
  /-- from `Q` on, up to the collision routine: at the step at `Q`, and after it -/
  | q1 | q
  /-- from `Q` on, not landing: at the step at `Q`, and after it -/
  | k1 | k
  /-- from `Q` on, landing -/
  | l1 | l
  /-- from `Q` on, the other heights -/
  | n1 | n
  /-- after the return, from the air -/
  | aft
  /-- a takeoff with the stored speed `u` before the return, and after it -/
  | tk (u : Nat) | tkd
  /-- a failed check, or a list that is no phase -/
  | bad
  deriving DecidableEq

/-- the phase of a list -/
def decode (l : List Nat) : Phase :=
  match l with
  | [] => .pre
  | [1, 1] => .q1
  | [1] => .q
  | [2, 1] => .k1
  | [2] => .k
  | [3, 1] => .l1
  | [3] => .l
  | [9, 1] => .n1
  | [9] => .n
  | [4] => .aft
  | [5, u] => .tk u
  | [7] => .tkd
  | _ => .bad

/-- **The pieces before a step**: at `Q` in the phase `pre` the phase `q1`; after a marked step the phase without its mark; at the collision routine `cE` in the
phase `q` the pieces of `piecesQ`; at its return `cR` the check of each phase and the next phase (`[99]` if the check fails, or if `cR` comes before `cE`), with the
bytes of `pAll` forgotten. `ex u` is the model's takeoff for the speed `u`. -/
def zoneA (sy : Syms) (K : Ctx) (ex : Nat → Jump.VS) (A : AS) : List AS :=
  match decode A.log with
  | .pre => if A.pc == sy.PlayerSubs then [{ A with log := [1, 1] }] else [A]
  | .q1 => [{ A with log := if A.pc == K.cR then [99] else [1] }]
  | .q => if A.pc == K.cE then piecesQ sy K.y0 K.d A else if A.pc == K.cR then [{ A with log := [99] }] else [A]
  | .k1 => [{ A with log := if A.pc == K.cR then [99] else [2] }]
  | .l1 => [{ A with log := if A.pc == K.cR then [99] else [3] }]
  | .n1 => [{ A with log := if A.pc == K.cR then [99] else [9] }]
  | .k => if A.pc == K.cR then [{ forgetV sy A with log := if haltK sy A then [4] else [99] }] else [A]
  | .l => if A.pc == K.cR then [{ forgetV sy A with log := if landedK sy K.y0 A && haltK sy A then [4] else [99] }] else [A]
  | .n => if A.pc == K.cR then [{ forgetV sy A with log := [4] }] else [A]
  | .tk u => if A.pc == K.cR then [{ forgetV sy A with log := if vsK sy (ex u) A then [7] else [99] }] else [A]
  | _ => [A]

/-- **What each piece meets**: from `Q` to the return, no write to `pAll` (not landing) or to `pRest` (landing), and no second arrival at `Q`; after the return from
the air, no arrival at `Q`; `bad` fails -/
def okA (sy : Syms) (K : Ctx) (E : Env) (A : AS) : Bool :=
  match decode A.log with
  | .bad => false
  | .q1 => StepWrites.keepOK E (fun i => (pAll sy).contains i) A
  | .q => A.pc != sy.PlayerSubs && StepWrites.keepOK E (fun i => (pAll sy).contains i) A
  | .k1 => A.pc != sy.PlayerSubs && A.pc != K.cR && StepWrites.keepOK E (fun i => (pAll sy).contains i) A
  | .l1 => A.pc != sy.PlayerSubs && A.pc != K.cR && StepWrites.keepOK E (fun i => (pRest sy).contains i) A
  | .n1 => A.pc != sy.PlayerSubs && A.pc != K.cR
  | .k => A.pc != sy.PlayerSubs && StepWrites.keepOK E (fun i => (pAll sy).contains i) A
  | .l => A.pc != sy.PlayerSubs && StepWrites.keepOK E (fun i => (pRest sy).contains i) A
  | .n => A.pc != sy.PlayerSubs
  | .aft => A.pc != sy.PlayerSubs
  | _ => true

/-- the phases -/
def phA (sy : Syms) (K : Ctx) (ex : Nat → Jump.VS) (E : Env) : PhK := { zone := zoneA sy K ex, ok := okA sy K E }

/-- the phases after the return of the collision routine -/
def afterRet (l : List Nat) : Bool :=
  match decode l with
  | .aft | .tkd => true
  | _ => false

/-- the frame's end: after the return of the collision routine -/
def finA (B : AS) : Bool := afterRet B.log

/-! ## The starts at the cut -/

/-- the states at the cut: in the air in the state 1 with the halt value 1, in the state 2; a takeoff of any speed (A pressed, not on the frame before); a takeoff on
the ground at `y0` for each stored speed up to the top -/
def startsA (sy : Syms) (K : Ctx) (v : UInt8) (B : AS) : List AS :=
  let sp : Watch := (I sy.JumpspringAnimCtrl, 0xFF, 0)
  let dc : Watch := (K.dI, 0xFF, 0)
  let jA : List Watch := [(I sy.SavedJoypadBits, 0x80, 0x80), (I sy.PreviousA_B_Buttons, 0x80, 0)]
  [{ CtrlKeep.toA K.W (CtrlKeep.valA sy v ++ [(I sy.Player_State, 0xFF, 1), (I sy.DiffToHaltJump, 0xFF, 1), sp, dc]) B with log := [] },
   { CtrlKeep.toA K.W (CtrlKeep.valA sy v ++ [(I sy.Player_State, 0xFF, 2), sp, dc]) B with log := [] }] ++
  (List.range (TopSpeed.top sy + 1)).map fun u =>
    { CtrlKeep.toA K.W (CtrlKeep.valA sy v ++ OpenFlat.groundW sy K.y0 ++ [sp, dc, (I sy.Player_XSpeedAbsolute, 0xFF, u.toUInt8)] ++ jA) B with log := [5, u] }

/-! ## The check on the ROM -/

/-- the phase as a number: the search's key keeps the phases apart -/
def logCode (l : List Nat) : Nat := l.foldl (fun n x => n * 256 + x + 1) 0

/-- the search's key, with the phase: before the return that of `OpenFlat`, after it that of `FrameKeep` -/
def keyA (sy : Syms) (K : Ctx) (A : AS) : Nat :=
  (if afterRet A.log then FrameKeep.keyK K.S K.G K.W A else OpenFlat.keyF sy K.S K.G K.bb K.gb A) * 16777216 + logCode A.log

/-- the search's step into the table: before the return it keeps every byte of the RAM (as `OpenFlat.searchB`); after it, the step of `FrameKeep`. No part of the
proof. -/
def routeA (sy : Syms) (K : Ctx) (X : SG) (B : AS) : SG :=
  if afterRet B.log then FrameKeep.routeKW K.S K.G (keyA sy K) X B
  else OpenWalk.routeP (OpenMap.inColl sy) OpenMap.tempsC (List.range 2048) K.S K.G (keyA sy K) X B

/-- the search of the walk from the states `starts` at the cut: its table. No part of the proof. -/
def searchFrom (sy : Syms) (m0 : Machine) (K : Ctx) (starts : List AS) : SG :=
  let E := PipeEntryRule.envOf m0
  OpenWalk.searchP K.R (phA sy K (expT sy m0) E) (routeA sy K) K.S K.G E K.W (TaintRun.aRows E).toArray finA (starts.foldl (routeA sy K) {})

/-- the cut states of the walk of the pause bit -/
def cutsA (sy : Syms) (m0 : Machine) : List AS := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true))

/-- the search of the walk from the states at the cut. No part of the proof. -/
def searchA (sy : Syms) (m0 : Machine) (v : UInt8) : SG :=
  let K := ctxOf sy m0 v
  searchFrom sy m0 K ((cutsA sy m0).flatMap (startsA sy K v))

/-- the walk, with the table of the search `X` -/
def cfgAOf (sy : Syms) (m0 : Machine) (K : Ctx) (X : SG) : CfgK :=
  let E := PipeEntryRule.envOf m0
  let q := FrameKeep.tableOfKW (keyA sy K) X
  { E := E, ops := (TaintRun.aRows E).toArray, S := K.S, G := K.G, W := K.W, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key := keyA sy K,
    fin := finA }

/-- what the walk of the pause bit asks at the player's routine: the walk from each state of `startsA` -/
@[irreducible] def hookA (sy : Syms) (m0 : Machine) (K : Ctx) (v : UInt8) (C : CfgK) (B : AS) : Bool :=
  (startsA sy K v B).all (walkP K.R (phA sy K (expT sy m0) C.E) C FrameKeep.fuelK)

/-- the walk of the pause bit of `CtrlKeep` up to the player's routine, with `hookA` there -/
def cfgPA (sy : Syms) (m0 : Machine) (K : Ctx) (v : UInt8) (C : CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true) with after := hookA sy m0 K v C }

/-- the check with the context `K` and the walk `C` -/
def airCheckWith (sy : Syms) (m0 : Machine) (K : Ctx) (v : UInt8) (C : CfgK) : Bool :=
  CtrlKeep.ctrlCheck1 (cfgPA sy m0 K v C) && C.t.all (walkP K.R (phA sy K (expT sy m0) C.E) C FrameKeep.fuelK)

/-- **The check on the ROM**: the walk of the pause bit up to the player's routine, which asks there that the walk of the frame succeeds from each start -/
def airCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let K := ctxOf sy m0 v
  airCheckWith sy m0 K v (cfgAOf sy m0 K (searchA sy m0 v))

end Smbrta.OpenAir
