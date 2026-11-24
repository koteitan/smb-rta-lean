import Theorems.SurfaceRun
import Theorems.SideChangeEnd
import Theorems.FrameModel
import Theorems.VertModel
import Theorems.CtrlKeep
import Theorems.AfterKeep
import Theorems.GuardE
import Theorems.CollKeep
import Theorems.CollideKeep
import Theorems.VertKeep
import Theorems.FaceKeep
import Theorems.SurfaceRead
import Theorems.SideLoop
import Theorems.SideAcross
import Theorems.ImpedePosition
import Theorems.PositionKeep
import Theorems.EdgeStep
import Theorems.MoveScroll
import Theorems.SideTimer
import Theorems.ClampSide
import Theorems.RightEdge
import Theorems.PushTimer
import Theorems.StopEdge
import Theorems.StopClamp

/-!
# Above ground: the frames from control, one by one

`PoleJoin.Run` used to assume statements about a whole run: `model` (up to the first hit the position is `hdist`), `hit`, `stop`, and `box`, `off` (no hit before frame `J`). Here they are
theorems. What stays is about one frame, read from the machines: `seq j` is the machine at the end of the counted frame `j`, so `seq 0` is the machine at control. `lag` frames are not counted (`Route.Run.clock`):
they can come between `seq j` and the frame `j + 1`, and they change none of the bytes read here (measured).

* The model's input of a frame is the one the player's routine reads (`inAt`); it is always in `Potential.inputs`. `readIn` reads it from the machines around the frame,
  for the programs.
* `Clean` is a condition on one state: the stored speed is `|v|`, and the collision bits block nothing, or only Left while he moves right.
* `OneFrame`: from a clean state, the frame is `hstep` up to the collision routine (`Pre`), and the routine leaves one of three things (`Coll`): nothing, a block of Left, or a hit;
  or the frame is a hit with no `Pre` (a frame that ends with the speed 0 can have another facing than `hstep` gives).
  A hit (`Hit`) leaves a speed of at most 0, and `P` at most `P₂ − 256` or at most `B + 256`, where the base `B` (`SurfaceRead.baseOf`) is the larger of `P` and the
  screen's left edge (round 24: it was `P + 256`, false on a real frame that starts 1 px left of the edge). The screen's left edge is a hit of the second kind.
* `one_of_moves`: a real frame is a `OneFrame`. The movement, from the player's routine to the scroll handler, is `FrameModel.move_model`, proved. The state at the player's routine
  (`FrameModel.AtCtrl0`, and that nothing writes the horizontal bytes before it) is a theorem too (`Moves.toAt`): the walk of `CtrlKeep` from the frame's start in control.
  So are the first arrival at the routine (`OnFrames.arrive`: the counted frame ends with the game not paused, by the definition of the counted frames in `FrameKeep.Frames`)
  and that the frames not counted keep the bytes (`OnFrames.lagKeep`, from `OnFrames.lagNo`: they do not come to the routine). That they do not is a theorem too: they end
  paused (`FrameKeep.Frames.down`), and the walk of the whole frame (`area_endF`) shows that every frame keeps the area's type, the swimming flag and the change of size
  (`OnFrames.areaAll`), and that a frame that comes to the routine ends not paused; its condition on each instruction is `CleanK` of `FrameKeep.guardF`, from the field
  `cleanE` of `FrameKeep.Frames`. Every frame also keeps bit 7 of A of the frame before equal to that of A (`OnFrames.prevAll`, the walk of `PrevKeep`), and the moving
  direction, the running speed and the stored speed from the scroll handler to its end (`AfterKeep.keepH`); their condition on each instruction is `CleanK` of
  `FrameKeep.guardE`, the field `cleanE` (`GuardE.prev_endE`, `GuardE.keepHE`: the field `spareE` is gone). At the scroll
  handler the stored speed is `|v|` (`storedQ_of`: the walks of `FrameModel.stored_path`, and the frame comes there once, `GuardE.subs_onceE`). What is assumed is
  the rest of the state at the end of the frame before (`OnFrames.state`) and the rest of what the frame does from the scroll handler on: the position
  (`OnFrames.collide`, and `AfterP` for the frames that move right there: `After.of`). Of `collide`, the speed's part is a theorem (`OnFrames.collideAt`: the walk of
  `CollideKeep`, with the condition `cleanE` on each instruction, which protects the speed; the old field `spareV`), and so is the subspeed on every frame that does
  not end with the speed 0 and the subspeed 0 (the walk of `FaceKeep`), so the field is `CollideS`: the position, and the subspeed on the frames that end so. The
  facing is a theorem on every frame that does not end so (`FaceKeep.keepZ_end`; such a frame is a hit, and a hit needs no facing), but on the frames before `J`,
  which must follow `hstep`: there the field `faceJ` asks it. The collision bits of a frame that moves right at the scroll handler are a theorem
  (`FaceKeep.bits_end`). So `AfterR`, which asked the facing and the collision bits, is now `AfterP`.
  A frame with the pressed side masked (`Masked`) is a `OneFrame` too: `FrameModel.move_masked` follows `hstep`, or leaves the speed 0 (`MaskStop`).
* `BoxRun`: the frames before `J` run the collision routine as on the machine at control, from the machine at the scroll handler, on its pixel and the height of `vstep`. The height comes from
  `vert_of`, one frame of `Jump.vstep` (the movement routine by `VertModel.vert_model`, the part before it by the walk of `CtrlKeep` (`vBefore`), the part after it by `OnFrames.vAfter` for five bytes, by the walk of `VertKeep` for four others, `OnFrames.kAt`, and by the walk of `FaceKeep` for the vertical force, `OnFrames.vfAt`: it stays, or the frame ends on the ground with the value of a jumpspring's landing, which `VStep` allows), and a small search (`vCheck`).
  The pixel comes from the distance bound (`dist_abs`).
* `frOf`: the frames as `TopSpeed.Frame`s are a definition on the machines: a frame before the touch is `SurfaceRead.frameE` of the real frame, the touch's frame
  `SurfaceRead.frameH`. From conditions on one frame or one machine (`OnFrames.state`, `collide`) each one is read from its machines
  (`OnFrames.reads`: `Reads`, the old field `reads`), so they follow each other by the definition (`next_of_reads`). The collision bits are one of the four values of
  `TopSpeed.collBits` at each frame's start (`OnFrames.collAll`: the walk of `CollKeep`, with the condition `cleanE` on each instruction, which protects the
  collision bits; the old fields `coll` and `spareC`). The
  position is away from the ends of its range on the first `farN` frames (`OnFrames.readAll`), so these theorems ask that the touch is not later (`g ≤ farN`); a later
  touch is a case of its own of the route (`SurfaceLate`), so the old field `farLate` is gone.
* The frames are those of `FrameKeep.Frames` (the field `keep` of `PoleJoin.Run`): `OnFrames` takes their starts, inputs and ends from it.

`surface_of_frames` derives `model`, `hit`, `stop`, and that no hit comes before `J`, from these, with no search: it is the arithmetic of `go` and `hdist`.

The start: `SideChangeEnd` proves rows of states up to the frame of control. In its last row the machine at control has the horizontal state and the position of the machine of the private proof
(`startCheck`, `start_of_rows`, `EndRun.start`), and the area's type, the swimming flag and the change of size of it. So `startP`, `startV` are theorems on real machines, under the conditions of the change and the condition that `left` is not 0 before control.
No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.PoleJoin

open Potential (HIn inputs hdist startHS)
open TopSpeed (top Frame)
open SurfaceRun (noHitCheck noHitAt someSpeeds vyStates)

variable {sy : Syms} {m0 : Machine} {tp am : Int}

/-- What the private proof fixes about the map above ground: the machine at control, how far around its position `SurfaceRun.noHitCheck` looked, and the highest row above the
ground that he stands on near the flag. -/
structure Box where
  m : Machine
  dx : Nat
  dy : Nat
  rows : Nat

/-- the collision routine, as `SurfaceRun.noHitAt` runs it -/
def noHitRun (sy : Syms) (m : Machine) (x y v vy st : UInt8) : Machine :=
  let m1 := poke m sy.Player_X_Position x
  let m1 := poke m1 sy.Player_Y_Position y
  let m1 := poke m1 sy.Player_X_Speed v
  let m1 := poke m1 sy.Player_MovingDir (if v < 0x80 then 1 else 2)
  let m1 := poke m1 sy.Player_Y_Speed vy
  let m1 := poke m1 sy.Player_State st
  runSub m1 sy.PlayerBGCollision 0 0 0

/-- the height and the fall of the box of `noHitCheck`: on the ground at the height of the machine, or in the air up to `dy` above it -/
def BoxV (sy : Syms) (B : Box) (y vy st : UInt8) : Prop :=
  (y = (peek B.m sy.Player_Y_Position).toNat.toUInt8 ∧ vy = 0 ∧ st = 0) ∨
    ∃ b, b < B.dy + 1 ∧ y = ((peek B.m sy.Player_Y_Position).toNat - b).toUInt8 ∧ (vy, st) ∈ vyStates sy

/-- a state of the box of `noHitCheck` -/
def InBox (sy : Syms) (B : Box) (x y v vy st : UInt8) : Prop :=
  (∃ a, a < 2 * B.dx + 1 ∧ x = ((peek B.m sy.Player_X_Position).toNat + a - B.dx).toUInt8) ∧ v ∈ someSpeeds ∧ BoxV sy B y vy st

/-- The real frame runs the collision routine as on the state `x y v vy st` of the machine `B.m`, `v` standing for the speed's sign: what it does to the position's pixel and to the speed, and the
collision bits it leaves, are the routine's. `Q` is the machine when the frame comes to the scroll handler, `b` the machine at the frame's end. -/
def RunsAs (sy : Syms) (B : Box) (Q b : Machine) (x y v vy st : UInt8) : Prop :=
  (∃ base : Int, posP sy Q = base + 256 * (x.toNat : Int) ∧
      posP sy b = base + 256 * ((peek (noHitRun sy B.m x y v vy st) sy.Player_X_Position).toNat : Int)) ∧
    sbyte (peek b sy.Player_X_Speed) - sbyte (peek Q sy.Player_X_Speed) = sbyte (peek (noHitRun sy B.m x y v vy st) sy.Player_X_Speed) - sbyte v ∧
    peek b sy.Player_CollisionBits = peek (noHitRun sy B.m x y v vy st) sy.Player_CollisionBits

/-- The real frame from `Q` to `b` runs the collision routine as on a state of the box. -/
def BoxFrame (sy : Syms) (B : Box) (Q b : Machine) : Prop :=
  ∃ x y v vy st : UInt8, InBox sy B x y v vy st ∧ RunsAs sy B Q b x y v vy st

/-- From the scroll handler `Q` to the frame's end `b`, the collision routine did nothing. -/
def Quiet (sy : Syms) (Q b : Machine) : Prop :=
  posP sy b = posP sy Q ∧ sbyte (peek b sy.Player_X_Speed) = sbyte (peek Q sy.Player_X_Speed) ∧ peek b sy.Player_CollisionBits = 0xFF

/-- `noHitCheck` on the frames: a frame in the box is quiet -/
theorem quiet_of_box {B : Box} (hc : noHitCheck sy B.m B.dx B.dy = true) {Q b : Machine} (h : BoxFrame sy B Q b) : Quiet sy Q b := by
  obtain ⟨x, y, v, vy, st, ⟨⟨a, ha, hx⟩, hv, hy⟩, ⟨base, h1, h2⟩, h3, h4⟩ := h
  have hat : noHitAt sy B.m x y v vy st = true := by
    simp only [noHitCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
    have h5 := hc a ha
    rw [← hx] at h5
    rcases hy with ⟨hy, hvy, hst⟩ | ⟨b, hb, hy, hvs⟩
    · rw [hy, hvy, hst]
      exact h5.1 v hv
    · rw [hy]
      exact h5.2 b hb v hv (vy, st) hvs
  simp only [noHitAt, Bool.and_eq_true, beq_iff_eq] at hat
  obtain ⟨⟨h5, h6⟩, h7⟩ := hat
  have e5 : peek (noHitRun sy B.m x y v vy st) sy.Player_X_Position = x := h5
  have e6 : peek (noHitRun sy B.m x y v vy st) sy.Player_X_Speed = v := h6
  have e7 : peek (noHitRun sy B.m x y v vy st) sy.Player_CollisionBits = 0xFF := h7
  rw [e5] at h2
  rw [e6] at h3
  rw [e7] at h4
  exact ⟨by omega, by omega, h4⟩

/-- What a real run gives from control above ground (position `PA`, frame `fr 1` the first frame after control) up to frame `T`, in the model of `SurfaceRun`: `w` are the model's inputs, and the
frames before the first hit `h` move as `hdist` says. A first hit is one of the kinds of `SurfaceRun.hit_bound`, and it leaves a speed of at most 0. No hit comes before `J`.
If he hits nothing up to `T` before the touch `g`, `h` is past `T`. This is a theorem now: `SurfaceFrames.surface_of_frames`. -/
structure Surface (sy : Syms) (m0 : Machine) (PA : Int) (T J g : Nat) (fr : Nat → Frame (top sy) (amax sy m0) true)
    (w : List HIn) (h : Nat) : Prop where
  mem : ∀ i ∈ w, i ∈ inputs
  long : T ≤ w.length
  /-- a first hit up to `T` comes before the touch -/
  range : h ≤ T → h < g
  /-- no hit before `J`: the frames before it stay in the box of `SurfaceRun.noHitCheck` -/
  first : J ≤ h
  model : ∀ j, 1 ≤ j → j < h → j ≤ T → j < g → (fr j).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take j)
  /-- the first hit ends 1 px behind the model's move, or at most 1 px past the model's position at some frame before it: the frame's base (`SurfaceRead.baseOf`) is
  its start or the screen's left edge, and the edge is behind a position he had before (round 24: it was `w.take (h − 1)`, the frame's start) -/
  hit : h ≤ T → (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take h) - 256 ∨
    ∃ s, s < h ∧ (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take s) + 256
  stop : h ≤ T → (fr h).v' ≤ 0
  /-- the base of the frame after the first hit is its start, or at most the model's position at a frame before the hit -/
  base : h ≤ T → (fr (h + 1)).B ≤ (fr h).P' ∨ ∃ s, s < h ∧ (fr (h + 1)).B ≤ PA + hdist sy m0 (startHS sy m0) (w.take s)
  /-- the bases of the frames follow each other (`TopSpeed.ChainB`) -/
  links : ∀ t, 1 ≤ t → t < g → (fr (t + 1)).B ≤ max (max (fr t).P (fr t).B) (fr (t + 1)).P
  /-- the base of the first frame is the position at control (round 25: asked when there is a frame before the touch) -/
  base₁ : 1 ≤ g → (fr 1).B ≤ PA

/-- No hit before `J`. `surface_of_frames` proves it from the box (`SurfaceFrames.quiet_upto`); the arguments stay for the callers. -/
theorem first_of_surface {PA : Int} {m : Machine} {dx dy T J g : Nat} {fr : Nat → Frame (top sy) (amax sy m0) true} {w : List HIn} {h : Nat}
    (_hc : noHitCheck sy m dx dy = true) (_hJT : J ≤ T) (R : Surface sy m0 PA T J g fr w h) : J ≤ h :=
  R.first

end Smbrta.PoleJoin

namespace Smbrta.SurfaceFrames

open Potential (HS HIn inputs hstep hdist startHS inD phi nxt J Facts step_J phi_ge)
open TopSpeed (top absB Frame)
open FastTakeoff (go adv TFacts)
open SurfaceRun (noHitCheck someSpeeds)
open PoleJoin (Box BoxV InBox RunsAs BoxFrame Quiet Surface quiet_of_box)
open PoleGrab (Next)

/-! ## What is read from a machine -/

/-- the speed -/
def vOf (sy : Syms) (m : Machine) : Int := sbyte (peek m sy.Player_X_Speed)
/-- the subspeed -/
def fOf (sy : Syms) (m : Machine) : Int := ((peek m sy.Player_X_MoveForce).toNat : Int)
/-- the collision bits -/
def bitsOf (sy : Syms) (m : Machine) : UInt8 := peek m sy.Player_CollisionBits

/-- The buttons as `HIn` has them. A frame reads Select and Start only in `GetPlayerAnimSpeed`'s test for any button other than A, as it reads Up. -/
def joyOf (saved : UInt8) : UInt8 := (saved &&& 0x4F) ||| (if saved &&& 0x30 != 0 then 0x08 else 0)

/-- The input of the frame from `a` to `b`. `RunningTimer` counts down before `X_Physics` reads it, so a value of 1 is read as 0. -/
def readIn (sy : Syms) (a b : Machine) : HIn :=
  { st := if peek a sy.Player_State == 0 then 0 else 1
    jump := peek a sy.Player_State == 0 && peek b sy.Player_State == 1
    joy := joyOf (peek b sy.SavedJoypadBits)
    rt := if (peek a sy.RunningTimer).toNat ≤ 1 then 0 else 1 }

theorem joyOf_all : ∀ n : Fin 256, joyOf (UInt8.ofNat n.val) ∈ groundInputs := by decide +kernel

theorem joyOf_mem (x : UInt8) : joyOf x ∈ groundInputs := by
  have h := joyOf_all ⟨x.toNat, x.toNat_lt⟩
  simpa using h

/-- every frame's input is an input of the model -/
theorem readIn_mem (sy : Syms) (a b : Machine) : readIn sy a b ∈ inputs := by
  have hj := joyOf_mem (peek b sy.SavedJoypadBits)
  have hr : (if (peek a sy.RunningTimer).toNat ≤ 1 then (0 : UInt8) else 1) ∈ [(0 : UInt8), 1] := by
    split <;> simp
  simp only [readIn, inputs, List.mem_flatMap, List.mem_map]
  by_cases h0 : peek a sy.Player_State == 0
  · by_cases h1 : peek b sy.Player_State == 1
    · refine ⟨(0, true), by simp, joyOf (peek b sy.SavedJoypadBits), hj, _, hr, ?_⟩
      simp [h0, h1]
    · refine ⟨(0, false), by simp, joyOf (peek b sy.SavedJoypadBits), hj, _, hr, ?_⟩
      simp [h0, h1]
  · refine ⟨(1, false), by simp, joyOf (peek b sy.SavedJoypadBits), hj, _, hr, ?_⟩
    simp [h0]

/-! ## One frame -/

/-- **The state that the model covers.** The horizontal state is in the domain, the stored speed is `|v|`, and the collision bits block nothing, or only Left while he moves right. A hit can leave
the stored speed stale (`X_Physics` reads it), and after a block of Right the frame is not `hstep`: these are not clean, and no field speaks of the frames after them. -/
def Clean (sy : Syms) (m : Machine) : Prop :=
  inD sy (startHS sy m) = true ∧ peek m sy.Player_XSpeedAbsolute = absB (peek m sy.Player_X_Speed) ∧
    (bitsOf sy m = 0xFF ∨ (bitsOf sy m = sy.noLeft ∧ 0 < vOf sy m))

/-- what `hstep` says of the frame from `a` on the input `i` -/
def modelS (sy : Syms) (m0 a : Machine) (i : HIn) : HS := hstep sy m0 (startHS sy a) i

/-- the frame from `a` to `b` on the input `i` follows `hstep` in the open area: the form of `RoomJoin.Follow`, with `fr.hs n = startHS (seq n)`, `fr.P n = posP (seq n)` -/
def Follow (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  i ∈ inputs ∧ startHS sy b = modelS sy m0 a i ∧ posP sy b = posP sy a + 16 * sbyte (startHS sy b).v

/-- Before the collision routine the frame is `hstep`: the routine can change only the speed. -/
def Pre (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  ({ startHS sy b with v := (modelS sy m0 a i).v } : HS) = modelS sy m0 a i ∧
    peek b sy.Player_XSpeedAbsolute = absB (modelS sy m0 a i).v

/-- **A hit, on one frame.** The speed ends at most 0, and `P` ends 1 px behind the frame's move, or at most 1 px past the base at its start (`SurfaceRead.baseOf`:
the larger of the position and the screen's left edge). The second kind is also the screen's left edge: the clamp puts him on the edge's pixel, and a push of 1 px
can follow. -/
def Hit (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy a + 16 * sbyte (modelS sy m0 a i).v - 256 ∨ posP sy b ≤ SurfaceRead.baseOf sy a + 256)

/-- What the collision routine leaves on a frame that is `hstep` before it: nothing; or the block of Left on a frame moving right, which changes nothing else; or a hit. -/
def Coll (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  (posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a i).v ∧ vOf sy b = sbyte (modelS sy m0 a i).v ∧ bitsOf sy b = 0xFF) ∨
  (0 < sbyte (modelS sy m0 a i).v ∧ posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a i).v ∧ vOf sy b = sbyte (modelS sy m0 a i).v ∧ bitsOf sy b = sy.noLeft) ∨
  Hit sy m0 i a b

/-- With Left blocked, a frame moving right can stop him: Left on the ground at a low speed stops a skid, and the blocked Left does not start him moving left. -/
def MaskStop (sy : Syms) (a b : Machine) : Prop :=
  bitsOf sy a = sy.noLeft ∧ vOf sy b ≤ 0 ∧ posP sy b ≤ SurfaceRead.baseOf sy a + 256

/-- **One frame from a clean state**, on the input `i`: a stop with Left blocked; or the frame of `hstep` up to the collision routine and what that routine leaves;
or a hit. A hit needs no `Pre`: a frame that ends with the speed 0 can have another facing than `hstep` gives (a climbing tile turns him), and the run leaves the
model at a hit anyway (`step_of_one`). -/
def OneFrame (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  MaskStop sy a b ∨ (Pre sy m0 i a b ∧ Coll sy m0 i a b) ∨ Hit sy m0 i a b

/-- the frame's own pixel -/
def pix (P : Int) : UInt8 := (P / 256).toNat.toUInt8

/-- the vertical bytes of a machine, as `Jump.vstep` has them -/
def vsOf (sy : Syms) (m : Machine) : Jump.VS :=
  { y := peek m sy.Player_Y_Position, mf := peek m sy.Player_Y_MoveForce, vy := peek m sy.Player_Y_Speed, dummy := peek m sy.Player_YMF_Dummy, vf := peek m sy.VerticalForce,
    vfd := peek m sy.VerticalForceDown, origin := peek m sy.JumpOrigin_Y_Position, st := peek m sy.Player_State, prevA := (peek m sy.A_B_Buttons &&& 0x80) != 0 }

/-- what `Jump.vstep` says of the frame from `a` to `b`, on the machine `VertModel.vmach` (the stack pointer of the player's routine, the jump's halt value 1):
A is the one `b` holds, the stored speed is that of `a` -/
def vNext (sy : Syms) (m0 a b : Machine) : Jump.VS :=
  VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy a) (vsOf sy b).prevA (peek a sy.Player_XSpeedAbsolute)

theorem vsOf_eq (sy : Syms) (m : Machine) : vsOf sy m = VertModel.vsOf sy m := rfl

/-- the bytes of the vertical state but A, and the jump's halt value -/
def vKeep (sy : Syms) : List UInt16 :=
  [sy.Player_Y_Position, sy.Player_Y_MoveForce, sy.Player_Y_Speed, sy.Player_YMF_Dummy, sy.VerticalForce, sy.VerticalForceDown, sy.JumpOrigin_Y_Position,
   sy.Player_State, sy.DiffToHaltJump]

/-- **the bytes of `vKeep` that `OnFrames.vAfter` asks**: the height, its fraction, the vertical speed, the fraction counter, the state. Three others (the vertical
force down, the jump's origin, the jump's halt value) and A are kept by a walk (`VertKeep.keep_end`, `OnFrames.kAt`). The vertical force is kept by a walk too, or the
frame ends on the ground with the vertical force of a jumpspring (`FaceKeep.vf_end`, `OnFrames.vfAt`); the vertical model allows that (`VStep`, `vVar`). -/
def vHard (sy : Syms) : List UInt16 :=
  [sy.Player_Y_Position, sy.Player_Y_MoveForce, sy.Player_Y_Speed, sy.Player_YMF_Dummy, sy.Player_State]

/-- **One vertical step of a real frame**, from `a` to `b`: the vertical bytes of `b` are those of `vNext`, or `vNext` ends on the ground (the state 0) and they are
those of `vNext` with the vertical force `cv` (the landing on a jumpspring stores it; on the ground no step reads it) -/
def VStep (sy : Syms) (m0 : Machine) (cv : UInt8) (a b : Machine) : Prop :=
  vsOf sy b = vNext sy m0 a b ∨ ((vNext sy m0 a b).st = 0 ∧ vsOf sy b = { vNext sy m0 a b with vf := cv })

/-- in a jump the jump's halt value is 1 -/
def HaltOK (sy : Syms) (m : Machine) : Prop := peek m sy.Player_State = 1 → peek m sy.DiffToHaltJump = 1

instance (sy : Syms) (m : Machine) : Decidable (HaltOK sy m) := by unfold HaltOK; infer_instance

/-- The frame runs the collision routine as on the machine at control, from the machine `Q` at the scroll handler: on the pixel of `Q` and the height that `vstep` gives, `v` standing for the
speed's sign. -/
def BoxRun (sy : Syms) (m0 : Machine) (B : Box) (a Q b : Machine) : Prop :=
  ∃ v : UInt8, v ∈ someSpeeds ∧ RunsAs sy B Q b (pix (posP sy Q)) (vNext sy m0 a b).y v (vNext sy m0 a b).vy (vNext sy m0 a b).st

instance (sy : Syms) (m : Machine) : Decidable (Clean sy m) := by unfold Clean; infer_instance
instance (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Decidable (Pre sy m0 i a b) := by unfold Pre; infer_instance
instance (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Decidable (Hit sy m0 i a b) := by unfold Hit; infer_instance
instance (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Decidable (Coll sy m0 i a b) := by unfold Coll; infer_instance
instance (sy : Syms) (a b : Machine) : Decidable (MaskStop sy a b) := by unfold MaskStop; infer_instance
instance (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Decidable (OneFrame sy m0 i a b) := by unfold OneFrame; infer_instance

/-- **The frames are read from the machines.** `fr j` begins with the bytes of `seq (j − 1)`, and it ends with those of `seq j` if it is before the touch: the touch moves him, and that is not a `Frame`. -/
structure Reads (sy : Syms) (g : Nat) (seq : Nat → Machine) {tp am : Int} {wd : Bool} (fr : Nat → Frame tp am wd) : Prop where
  v : ∀ j, 1 ≤ j → j ≤ g → (fr j).v = vOf sy (seq (j - 1))
  f : ∀ j, 1 ≤ j → j ≤ g → (fr j).f = fOf sy (seq (j - 1))
  P : ∀ j, 1 ≤ j → j ≤ g → (fr j).P = posP sy (seq (j - 1))
  v' : ∀ j, 1 ≤ j → j < g → (fr j).v' = vOf sy (seq j)
  f' : ∀ j, 1 ≤ j → j < g → (fr j).f' = fOf sy (seq j)
  P' : ∀ j, 1 ≤ j → j < g → (fr j).P' = posP sy (seq j)

/-- The frames follow each other by the definition: both ends are read from the same machine. -/
theorem next_of_reads {g : Nat} {seq : Nat → Machine} {tp am : Int} {wd : Bool} {fr : Nat → Frame tp am wd} (R : Reads sy g seq fr) :
    ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1)) := by
  intro j h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [R.v (j + 1) (by omega) (by omega), R.v' j h1 h2, Nat.add_sub_cancel]
  · rw [R.f (j + 1) (by omega) (by omega), R.f' j h1 h2, Nat.add_sub_cancel]
  · rw [R.P (j + 1) (by omega) (by omega), R.P' j h1 h2, Nat.add_sub_cancel]

/-- **The state at control**: the horizontal state, the position, the stored speed, the collision bits, the vertical bytes, the area's type, the swimming flag and the
change of size of the machine `B.m`. -/
structure Start (sy : Syms) (B : Box) (m : Machine) : Prop where
  hs : startHS sy m = startHS sy B.m
  P : posP sy m = posP sy B.m
  stored : peek m sy.Player_XSpeedAbsolute = peek B.m sy.Player_XSpeedAbsolute
  bits : peek m sy.Player_CollisionBits = peek B.m sy.Player_CollisionBits
  vs : vsOf sy m = vsOf sy B.m
  area : peek m sy.AreaType = peek B.m sy.AreaType
  swim : peek m sy.SwimmingFlag = peek B.m sy.SwimmingFlag
  size : peek m sy.PlayerChangeSizeFlag = peek B.m sy.PlayerChangeSizeFlag
  /-- A and B, and A and B of the frame before -/
  ab : peek m sy.A_B_Buttons = peek B.m sy.A_B_Buttons
  prev : peek m sy.PreviousA_B_Buttons = peek B.m sy.PreviousA_B_Buttons
  /-- round 25: the two bytes of the screen's left edge (`SurfaceRead.edgeOf`), at the clamp's operands found in the program of `B.m` (`ScreenClamp.places`) -/
  edgeX : peek m (ScreenClamp.places sy B.m).edgeX = peek B.m (ScreenClamp.places sy B.m).edgeX
  edgeP : peek m (ScreenClamp.places sy B.m).edgeP = peek B.m (ScreenClamp.places sy B.m).edgeP
  /-- round 27: the platforms' force on the scroll (`EdgeStep.platI`) -/
  plat : peek m sy.Platform_X_Scroll = peek B.m sy.Platform_X_Scroll
  /-- round 31: the two bytes of the screen's right edge, one byte after the left edge's (`RightEdge`) -/
  rightX : peek m ((ScreenClamp.places sy B.m).edgeX + 1) = peek B.m ((ScreenClamp.places sy B.m).edgeX + 1)
  rightP : peek m ((ScreenClamp.places sy B.m).edgeP + 1) = peek B.m ((ScreenClamp.places sy B.m).edgeP + 1)

/-! ## The numbers -/

/-- how far the frames from `Φ ≤ p` move, either way. Moving left the speed's byte can be 1 below the bound on `V`. -/
def dl (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * (nxt sy m p / 256 + 1) + dl sy m (nxt sy m p) n

/-- the height and the fall of the box, as a check -/
def boxVB (sy : Syms) (B : Box) (t : Jump.VS) : Bool :=
  (t.y == (peek B.m sy.Player_Y_Position).toNat.toUInt8 && t.vy == 0 && t.st == 0) ||
    ((List.range (B.dy + 1)).any fun b => t.y == ((peek B.m sy.Player_Y_Position).toNat - b).toUInt8) && (SurfaceRun.vyStates sy).contains (t.vy, t.st)

/-- a state of the vertical bytes, and on the ground (the state 0) also the same state with the vertical force `cv` -/
def vVar (cv : UInt8) (w : Jump.VS) : List Jump.VS := if w.st == 0 then [w, { w with vf := cv }] else [w]

theorem mem_vVar_self (cv : UInt8) (w : Jump.VS) : w ∈ vVar cv w := by
  unfold vVar
  split <;> simp

theorem mem_vVar_c (cv : UInt8) {w : Jump.VS} (h : w.st = 0) : { w with vf := cv } ∈ vVar cv w := by
  unfold vVar
  simp [h]

/-- the next frames of the vertical bytes: A pressed or not, and every stored speed up to the top; a frame that ends on the ground also with the vertical force `cv` -/
def vNextAll (sy : Syms) (m0 : Machine) (cv : UInt8) (l : List Jump.VS) : List Jump.VS :=
  (l.flatMap fun s => [true, false].flatMap fun a => (List.range (top sy + 1)).flatMap fun ab =>
    vVar cv (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) s a ab.toUInt8)).eraseDups

/-- `n` more frames from the states `l` stay in the box's height -/
def vCheck (sy : Syms) (m0 : Machine) (B : Box) (cv : UInt8) : Nat → List Jump.VS → Bool
  | 0, _ => true
  | n + 1, l => (vNextAll sy m0 cv l).all (boxVB sy B) && vCheck sy m0 B cv n (vNextAll sy m0 cv l)

/-- **The frames that the position's range covers**, from the machine `m`: each frame read from the machines moves him at most `16·top` right and `16·top + 256` left
(`OnFrames.readAll`), so for the first `farN` frames from `m` the position stays at least 8 px from both ends of its range. With the machine at control, 745 frames. -/
def farN (sy : Syms) (m : Machine) : Nat :=
  min ((posP sy m - 2048) / (16 * (top sy : Int) + 256)).toNat ((0x1000000 - 2049 - posP sy m) / (16 * (top sy : Int))).toNat

/-- `farN` reads only the position -/
theorem farN_congr {a b : Machine} (h : posP sy a = posP sy b) : farN sy a = farN sy b := by
  unfold farN
  rw [h]

/-- the machine at control is stopped, clean, not in a jump, and the frames before `J` stay within `dx` px and in the box's height; and the checks on the ROM of `FrameModel`
and `VertModel`, for the movement -/
def numbersCheck (sy : Syms) (m0 : Machine) (B : Box) (J : Nat) : Bool :=
  let c := B.m
  FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) && VertModel.vertOK sy m0 (FrameModel.ctrlStack sy m0) && FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) &&
    CtrlKeep.ctrlCheck sy m0 && peek c sy.Player_State != 1 &&
    inD sy (startHS sy m0) && decide (startHS sy c = startHS sy m0) && decide (sbyte (peek c sy.Player_X_Speed) = 0) &&
    peek c sy.Player_XSpeedAbsolute == absB (peek c sy.Player_X_Speed) && peek c sy.Player_CollisionBits == 0xFF && sy.noLeft != 0xFF &&
    decide (B.dx ≤ (peek c sy.Player_X_Position).toNat) &&
    ((List.range J).all fun j => decide (dl sy m0 (Opening.pOf sy m0 (startHS sy m0)) j ≤ 256 * (B.dx : Int))) &&
    vCheck sy m0 B (FaceKeep.vfC sy m0 (peek c sy.AreaType)) (J - 1) [vsOf sy c] &&
    CtrlKeep.afterCheck sy m0 (peek c sy.AreaType) && [(1 : UInt8), 2, 3].contains (peek c sy.AreaType) && peek c sy.SwimmingFlag == 0 &&
    peek c sy.PlayerChangeSizeFlag == 0 && FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop &&
    PrevKeep.prevCheck sy m0 (peek c sy.AreaType) && PrevKeep.prevOKB sy c && AfterKeep.hCheck sy m0 (peek c sy.AreaType) &&
    FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) && CollKeep.collCheckAll sy m0 (peek c sy.AreaType) && CollideKeep.vCheck sy m0 (peek c sy.AreaType) &&
    VertKeep.kCheck sy m0 (peek c sy.AreaType) && FaceKeep.zCheck sy m0 (peek c sy.AreaType) && FaceKeep.bCheck sy m0 (peek c sy.AreaType) &&
    FaceKeep.vfCheck sy m0 (peek c sy.AreaType) (FaceKeep.vfC sy m0 (peek c sy.AreaType)) && PositionKeep.pCheck sy m0 (peek c sy.AreaType) &&
    decide (c.prg = m0.prg) && decide (c.prgMask = m0.prgMask) && decide (SurfaceRead.edgeOf sy c ≤ posP sy c) &&
    EdgeStep.qCheck sy m0 (peek c sy.AreaType) && EdgeStep.rCheck sy m0 (peek c sy.AreaType) && ScrollRule.check sy m0 &&
    peek c sy.Platform_X_Scroll == 0 && (ScrollRule.places sy m0).plat == EdgeStep.platI sy && PlaceKeep.placeCheck sy m0 (peek c sy.AreaType) &&
    MoveScroll.xsCheck sy m0 && SideTimer.sideCheck sy m0 && SideTimer.keepCheck sy m0 && decide (SurfaceRead.edgeOf sy c + 257 ≤ posP sy c) &&
    ClampSide.checkAll sy m0 && decide (2 ≤ (ScrollRule.places sy m0).thr1) && RightEdge.check sy m0 &&
    decide (ClampSide.edge16 (ClampSide.places sy m0) 1 c % 65536 = (ClampSide.edge16 (ClampSide.places sy m0) 0 c + 255) % 65536) &&
    decide (posP sy c + 16 * (top sy : Int) * (farN sy c : Int) < 65280 * 256) && PushTimer.sCheck sy m0 (peek c sy.AreaType) &&
    SideAcross.check sy m0 (peek c sy.AreaType)

/-- what `numbersCheck` says -/
structure Numbers (sy : Syms) (m0 : Machine) (B : Box) (J : Nat) : Prop where
  model : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true
  vmodel : VertModel.vertOK sy m0 (FrameModel.ctrlStack sy m0) = true
  /-- the check of the frames with the pressed side masked -/
  mask : FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) = true
  /-- the walk of a frame in control up to the player's routine -/
  ctrl : CtrlKeep.ctrlCheck sy m0 = true
  st1 : peek B.m sy.Player_State ≠ 1
  hD : inD sy (startHS sy m0) = true
  hs : startHS sy B.m = startHS sy m0
  v0 : sbyte (peek B.m sy.Player_X_Speed) = 0
  stored : peek B.m sy.Player_XSpeedAbsolute = absB (peek B.m sy.Player_X_Speed)
  bits : peek B.m sy.Player_CollisionBits = 0xFF
  noLeft : sy.noLeft ≠ 0xFF
  dx : B.dx ≤ (peek B.m sy.Player_X_Position).toNat
  dist : ∀ j, j < J → dl sy m0 (Opening.pOf sy m0 (startHS sy m0)) j ≤ 256 * (B.dx : Int)
  vert : vCheck sy m0 B (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (J - 1) [vsOf sy B.m] = true
  /-- the walk of the whole frame (`CtrlKeep.area_end`), with the area's type of `B.m` -/
  after : CtrlKeep.afterCheck sy m0 (peek B.m sy.AreaType) = true
  area3 : peek B.m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  swim0 : peek B.m sy.SwimmingFlag = 0
  size0 : peek B.m sy.PlayerChangeSizeFlag = 0
  /-- the idle loop is a `JMP` to itself -/
  idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true
  /-- the walk of the whole frame for A and B of the frame before (`PrevKeep.prev_end`), with the area's type of `B.m` -/
  prev : PrevKeep.prevCheck sy m0 (peek B.m sy.AreaType) = true
  /-- at control bit 7 of A and B of the frame before is that of A and B -/
  prev0 : PrevKeep.PrevOK sy B.m
  /-- the walks from the scroll handler to the frame's end (`AfterKeep.keepH`), with the area's type of `B.m` -/
  keepH : AfterKeep.hCheck sy m0 (peek B.m sy.AreaType) = true
  /-- the walks of the stored speed up to the scroll handler (`FrameModel.stored_path`) -/
  storedW : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true
  /-- the walk of the whole frame for the collision bits (`CollKeep.coll_end`), with the area's type of `B.m`, and that the bytes under the mask `FC` are the four values -/
  coll : CollKeep.collCheckAll sy m0 (peek B.m sy.AreaType) = true
  /-- the walk of the speed from the scroll handler to the frame's end (`CollideKeep.speed_end`), with the area's type of `B.m` -/
  vkeep : CollideKeep.vCheck sy m0 (peek B.m sy.AreaType) = true
  /-- the walks of four vertical bytes from the scroll handler to the frame's end (`VertKeep.keep_end`), with the area's type of `B.m` -/
  vk : VertKeep.kCheck sy m0 (peek B.m sy.AreaType) = true
  /-- the walks of the facing and of the subspeed from the scroll handler to the frame's end (`FaceKeep.keepZ_end`), with the area's type of `B.m` -/
  zk : FaceKeep.zCheck sy m0 (peek B.m sy.AreaType) = true
  /-- the walks of the collision bits on a frame that moves right at the scroll handler (`FaceKeep.bits_end`), with the area's type of `B.m` -/
  bk : FaceKeep.bCheck sy m0 (peek B.m sy.AreaType) = true
  /-- the walk of the vertical force from the scroll handler to the frame's end (`FaceKeep.vf_end`), with the area's type of `B.m` and the value `FaceKeep.vfC` -/
  vfk : FaceKeep.vfCheck sy m0 (peek B.m sy.AreaType) (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) = true
  /-- the checks of `PositionKeep.keep_frame` (the walk of the position's writers from the scroll handler to the frame's end, the push, the clamp), with the area's
  type of `B.m` -/
  pk : PositionKeep.pCheck sy m0 (peek B.m sy.AreaType) = true
  /-- round 25: `B.m` has the program of `m0` -/
  prgB : B.m.prg = m0.prg
  maskB : B.m.prgMask = m0.prgMask
  /-- round 25: on `B.m` the screen's left edge is behind him -/
  edgeB : SurfaceRead.edgeOf sy B.m ≤ posP sy B.m
  /-- round 26: the walks of the edge's two bytes up to the scroll handler (`EdgeStep.keep_q`, `EdgeStep.keep_noCut`), with the area's type of `B.m` -/
  edgeQ : EdgeStep.qCheck sy m0 (peek B.m sy.AreaType) = true
  /-- round 26: the walks of the edge's two bytes from the instruction after the scroll handler's call (`EdgeStep.keep_r`), with the area's type of `B.m` -/
  edgeR : EdgeStep.rCheck sy m0 (peek B.m sy.AreaType) = true
  /-- round 26: the check of the scroll's rule (`ScrollRule.scroll_edge`) -/
  scroll : ScrollRule.check sy m0 = true
  /-- round 27: on `B.m` the platforms' force on the scroll is 0 -/
  platB : peek B.m sy.Platform_X_Scroll = 0
  /-- round 27: the byte that the scroll handler adds to the byte the move stores is `EdgeStep.platI` -/
  platP : (ScrollRule.places sy m0).plat = EdgeStep.platI sy
  /-- round 28: the walks of the scroll's three bytes and the edge's two from the player's routine to the scroll handler (`PlaceKeep.keep_place`) -/
  place : PlaceKeep.placeCheck sy m0 (peek B.m sy.AreaType) = true
  /-- round 28: the walks of the byte the move stores (`MoveScroll.move_xs`) -/
  xs : MoveScroll.xsCheck sy m0 = true
  /-- round 29: the walk of the side collision's timer from the frame's start to the player's routine (`SideTimer.side_at`) -/
  side : SideTimer.sideCheck sy m0 = true
  /-- round 29: the walks of the place byte, the scroll lock and the edge's two bytes from the frame's start to the player's routine (`SideTimer.keep_at`) -/
  keepS : SideTimer.keepCheck sy m0 = true
  /-- round 29: on `B.m` he is at least 2 px (and a fraction step) right of the screen's left edge -/
  nearB : SurfaceRead.edgeOf sy B.m + 257 ≤ posP sy B.m
  /-- round 30: the pieces of the clamp's choice at the screen's edge (`ClampSide.left_after`) -/
  clampS : ClampSide.checkAll sy m0 = true
  /-- round 30: the scroll's first threshold of his place on the screen is at least 2 px -/
  thr2 : 2 ≤ (ScrollRule.places sy m0).thr1
  /-- round 31: the pieces of the scroll handler up to the routine of the offscreen bits that follow the right edge (`RightEdge.scroll_rel`) -/
  rightC : RightEdge.check sy m0 = true
  /-- round 31: on `B.m` the right edge is the left edge plus 255 px, modulo 2¹⁶ -/
  relB : RightEdge.Rel (ClampSide.places sy m0) B.m
  /-- round 31: in the first `farN` frames from control the base stays below the page 255 of the screen's left edge -/
  pageB : posP sy B.m + 16 * (top sy : Int) * (farN sy B.m : Int) < 65280 * 256
  /-- round 32: the walks of his pixel and his page after the scroll handler's call (`PushTimer.pix_end`; round 33: and his speed) -/
  pushC : PushTimer.sCheck sy m0 (peek B.m sy.AreaType) = true
  /-- round 36: the walk of `SideAcross.near_sideA` with the block buffer's column and the block objects' offset, and the walks of the two bytes from the frame's
  start to the scroll handler's call -/
  acrossC : SideAcross.check sy m0 (peek B.m sy.AreaType) = true

theorem numbers_of_check {B : Box} {J : Nat} (h : numbersCheck sy m0 B J = true) : Numbers sy m0 B J := by
  simp only [numbersCheck, PrevKeep.prevOKB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, ha⟩, hm⟩, hk⟩, hb⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩,
    h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩, h43⟩, h44⟩, h45⟩ := h
  exact ⟨h0, ha, hm, hk, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, List.contains_iff_mem.1 h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25,
    h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45⟩

/-- **At control the screen's left edge is behind him** (round 25; the old field `edge₀` of `OnFrames`): a machine with the state of `B.m` (`Start`: with the two bytes of
the edge) that starts a frame in control (so it has the program of `m0`, which `B.m` has too) has the edge of `B.m`, and on `B.m` the edge is behind him (`numbersCheck`) -/
theorem edge_zero {B : Box} {J : Nat} {m : Machine} (Nm : Numbers sy m0 B J) (st : Start sy B m) (h0 : FrameKeep.StartK sy m0 m) :
    SurfaceRead.edgeOf sy m ≤ posP sy m := by
  have hp : m.prg = B.m.prg := h0.prg.trans Nm.prgB.symm
  have hk : m.prgMask = B.m.prgMask := h0.mask.trans Nm.maskB.symm
  have e : ScreenClamp.places sy m = ScreenClamp.places sy B.m := SurfaceRead.places_congr hp hk
  have h := Nm.edgeB
  unfold SurfaceRead.edgeOf at h ⊢
  rw [e, st.edgeX, st.edgeP, st.P]
  exact h

/-- the bytes of the two edges are in `EdgeStep.eI` (round 31) -/
theorem eI_lx : ClampSide.eX (ClampSide.places sy m0) 0 ∈ EdgeStep.eI sy m0 := by
  rw [ClampSide.eX_zero]; exact List.mem_cons_self
theorem eI_lp : ClampSide.eP (ClampSide.places sy m0) 0 ∈ EdgeStep.eI sy m0 := by
  rw [ClampSide.eP_zero]; exact List.mem_cons_of_mem _ List.mem_cons_self
theorem eI_rx : ClampSide.eX (ClampSide.places sy m0) 1 ∈ EdgeStep.eI sy m0 := by
  rw [RightEdge.eX_one]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem eI_rp : ClampSide.eP (ClampSide.places sy m0) 1 ∈ EdgeStep.eI sy m0 := by
  rw [RightEdge.eP_one]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- the right edge's relation is read from the bytes of `EdgeStep.eI` (round 31) -/
theorem rel_congr {a b : Machine} (h : ∀ x ∈ EdgeStep.eI sy m0, a.ram.get! x = b.ram.get! x) (hr : RightEdge.Rel (ClampSide.places sy m0) b) :
    RightEdge.Rel (ClampSide.places sy m0) a := by
  unfold RightEdge.Rel ClampSide.edge16 at hr ⊢
  rw [h _ eI_lx, h _ eI_lp, h _ eI_rx, h _ eI_rp]
  exact hr

/-- **round 31: at control the right edge is the left edge plus 255 px**, modulo 2¹⁶: a machine with the state of `B.m` (`Start`: with the four bytes of the edges)
has the edges of `B.m`, and on `B.m` the relation holds (`numbersCheck`) -/
theorem rel_zero {B : Box} {J : Nat} {m : Machine} (Nm : Numbers sy m0 B J) (st : Start sy B m) : RightEdge.Rel (ClampSide.places sy m0) m := by
  have e : ScreenClamp.places sy B.m = ScreenClamp.places sy m0 := SurfaceRead.places_congr Nm.prgB Nm.maskB
  have h := Nm.relB
  have ex := st.edgeX
  have ep := st.edgeP
  have rx := st.rightX
  have rp := st.rightP
  rw [e] at ex ep rx rp
  unfold peek at ex ep rx rp
  unfold RightEdge.Rel ClampSide.edge16 at h ⊢
  rw [ClampSide.eX_zero, ClampSide.eP_zero, RightEdge.eX_one, RightEdge.eP_one] at h ⊢
  have c1 : (ClampSide.places sy m0).edgeX = (ScreenClamp.places sy m0).edgeX := rfl
  have c2 : (ClampSide.places sy m0).edgeP = (ScreenClamp.places sy m0).edgeP := rfl
  rw [c1, c2] at h ⊢
  unfold FrameModel.I at h ⊢
  rw [ex, ep, rx, rp]
  exact h

/-- **At control `SideTimer.NearM` holds** (round 29): a machine with the state of `B.m` (`Start`: with the two bytes of the edge and the position) that starts a
frame in control is as far right of the edge as `B.m`, at least 2 px (`numbersCheck`), so `NearM` holds whatever its timer, lock and place byte -/
theorem near_zero {B : Box} {J : Nat} {m : Machine} (Nm : Numbers sy m0 B J) (st : Start sy B m) (h0 : FrameKeep.StartK sy m0 m) :
    SideTimer.NearM sy (ScrollRule.places sy m0) m := by
  have hp : m.prg = B.m.prg := h0.prg.trans Nm.prgB.symm
  have hk : m.prgMask = B.m.prgMask := h0.mask.trans Nm.maskB.symm
  have e : ScreenClamp.places sy m = ScreenClamp.places sy B.m := SurfaceRead.places_congr hp hk
  have h := Nm.nearB
  have h2 : SurfaceRead.edgeOf sy m + 257 ≤ posP sy m := by
    unfold SurfaceRead.edgeOf at h ⊢
    rw [e, st.edgeX, st.edgeP, st.P]
    exact h
  exact SideTimer.nearM_of_edge h0.prg h0.mask h2

theorem absB_natAbs (v : UInt8) : (absB v).toNat = (sbyte v).natAbs := by
  have h1 := v.toNat_lt
  simp only [absB, sbyte]
  by_cases h : v < 0x80
  · rw [if_pos h, if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    have h2 : ¬ v.toNat < 128 := fun h3 => h (UInt8.lt_iff_toNat_lt.2 h3)
    rw [UInt8.toNat_sub, show (0 : UInt8).toNat = 0 from rfl]
    omega

/-- what the check says of a state in the box -/
theorem boxV_of_B {B : Box} {t : Jump.VS} (h : boxVB sy B t = true) : BoxV sy B t.y t.vy t.st := by
  simp only [boxVB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, List.contains_iff_mem] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨b, hb, h1⟩, h2⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨b, hb, h1, h2⟩

/-- **The search of the height.** Frames that are steps of `vstep`, with a stored speed up to the top, from a state of `l`, stay in the box. -/
theorem vCheck_spec {B : Box} {cv : UInt8} : ∀ (n : Nat) (l : List Jump.VS), vCheck sy m0 B cv n l = true → ∀ (u : Nat → Jump.VS) (a : Nat → Bool) (ab : Nat → UInt8), u 0 ∈ l →
    ∀ k, 1 ≤ k → k ≤ n → (∀ i, i < k → (ab i).toNat ≤ top sy ∧ u (i + 1) ∈ vVar cv (VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u i) (a i) (ab i))) →
      boxVB sy B (u k) = true
  | 0, _, _, _, _, _, _, _, h1, h2, _ => by omega
  | n + 1, l, h, u, a, ab, h0, k, h1, h2, hs => by
    simp only [vCheck, Bool.and_eq_true, List.all_eq_true] at h
    have hm : u 1 ∈ vNextAll sy m0 cv l := by
      obtain ⟨h3, h4⟩ := hs 0 (by omega)
      unfold vNextAll
      refine List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨u 0, h0, List.mem_flatMap.2 ⟨a 0, ?_, List.mem_flatMap.2 ⟨(ab 0).toNat, List.mem_range.2 (by omega), ?_⟩⟩⟩)
      · cases a 0 <;> simp
      · have e : (ab 0).toNat.toUInt8 = ab 0 := by simp
        rw [e]
        exact h4
    by_cases hi : k = 1
    · subst hi
      exact h.1 _ hm
    · obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 + 1 := ⟨k - 2, by omega⟩
      exact vCheck_spec n _ h.2 (fun k => u (k + 1)) (fun k => a (k + 1)) (fun k => ab (k + 1)) hm (d + 1) (by omega) (by omega) (fun k hk => hs (k + 1) (by omega))

/-- the distance of any inputs, either way -/
theorem dist_abs {m : Machine} (F : Facts sy m) :
    ∀ (is : List HIn) (s : HS) (p : Int), J sy m s p → (∀ i ∈ is, i ∈ inputs) →
      -dl sy m p is.length ≤ hdist sy m s is ∧ hdist sy m s is ≤ dl sy m p is.length
  | [], _, _, _, _ => by simp [hdist, dl]
  | i :: rest, s, p, hJ, his => by
    obtain ⟨hJ', h256, _⟩ := step_J F hJ (his i (by simp))
    have ih := dist_abs F rest _ _ hJ' (fun j hj => his j (by simp [hj]))
    have h1 := phi_ge F (hstep sy m s i)
    have h2 := hJ'.2.1
    have h3 : (Potential.V (hstep sy m s i)) = 256 * sbyte (hstep sy m s i).v + ((hstep sy m s i).f.toNat : Int) := rfl
    have h4 := (hstep sy m s i).f.toNat_lt
    simp only [hdist, dl, List.length_cons]
    omega

/-! ## Reading a byte back -/

theorem sbyte_inj {x y : UInt8} (h : sbyte x = sbyte y) : x = y := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold sbyte at h
  have e : x.toNat = y.toNat := by
    by_cases h1 : x < 0x80 <;> by_cases h2 : y < 0x80 <;> simp only [h1, h2, if_true, if_false] at h
    · omega
    · have : x.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h1
      have : ¬ y.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h2
      omega
    · have : ¬ x.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h1
      have : y.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h2
      omega
    · omega
  exact UInt8.toNat_inj.1 e

theorem hs_v (sy : Syms) (m : Machine) : (startHS sy m).v = peek m sy.Player_X_Speed := rfl

theorem with_v {s : HS} {v : UInt8} (h : s.v = v) : ({ s with v := v } : HS) = s := by
  cases s
  simp_all

section Step

variable {a b : Machine} {i : HIn}

/-- a frame that is `hstep` before the collision routine and that the routine leaves the speed of -/
theorem follow_of_pre (hi : i ∈ inputs) (hP : Pre sy m0 i a b) (hv : vOf sy b = sbyte (modelS sy m0 a i).v) (hp : posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a i).v) :
    Follow sy m0 i a b := by
  have e : peek b sy.Player_X_Speed = (modelS sy m0 a i).v := sbyte_inj hv
  have h1 : startHS sy b = modelS sy m0 a i := by
    have h2 := hP.1
    rwa [with_v (s := startHS sy b) (by rw [hs_v]; exact e)] at h2
  refine ⟨hi, h1, ?_⟩
  rw [hp, h1]

/-- a frame that follows `hstep` from a clean state leaves a clean state, if its bits are -/
theorem clean_of_follow (F : Facts sy m0) (hc : Clean sy a) (hf : Follow sy m0 i a b) (hP : Pre sy m0 i a b)
    (hb : bitsOf sy b = 0xFF ∨ (bitsOf sy b = sy.noLeft ∧ 0 < vOf sy b)) : Clean sy b := by
  have h1 := hf.2.1
  refine ⟨?_, ?_, hb⟩
  · rw [h1]
    exact (FastTakeoff.step_facts F hc.1 hf.1).1
  · have e : peek b sy.Player_X_Speed = (modelS sy m0 a i).v := by
      rw [← hs_v, h1]
    rw [e]
    exact hP.2

/-- **One frame from a clean state**: it follows `hstep` and leaves a clean state, or it is a hit. -/
theorem step_of_one (F : Facts sy m0) (hi : i ∈ inputs) (hc : Clean sy a) (h : OneFrame sy m0 i a b) :
    (Follow sy m0 i a b ∧ Clean sy b) ∨ Hit sy m0 i a b := by
  rcases h with ⟨_, h1, h2⟩ | ⟨hP, hq | ⟨h0, hq⟩ | hH⟩ | hH
  · exact Or.inr ⟨h1, Or.inr h2⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hi hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inl h3)⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hi hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inr ⟨h3, by rw [h2]; exact h0⟩)⟩
  · exact Or.inr hH
  · exact Or.inr hH

end Step

/-! ## One frame on the real machine

`FrameModel.move_model` proves the movement of a real frame: from the player's routine to the scroll handler the horizontal state follows `hstep` and `P` moves by `16·v₂`. What is left of
`OneFrame` is the frame outside the movement: up to the player's routine (`Moves`), and from the scroll handler to the frame's end (`After`). -/

section Real

open FrameModel (AtCtrl AtCtrl0 hBytes moveLen lrOf stepN)
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {a M : Machine} {i : UInt8} {n₀ : Nat}

/-- On the input `i`, the side he presses is masked in the state `a`. Then the routine of the friction reads the mask and `hstep` does not (`FrameModel.move_masked`). -/
def Masked (sy : Syms) (i : HIn) (a : Machine) : Prop :=
  bitsOf sy a &&& lrOf (Potential.norm i) ≠ lrOf (Potential.norm i)

instance (sy : Syms) (i : HIn) (a : Machine) : Decidable (Masked sy i a) := by unfold Masked; infer_instance

/-- the input of a frame, as the player's routine reads it: at the instruction `n` of the frame of `M` with the input `i`, where the frame comes to the routine -/
def inAt (sy : Syms) (M : Machine) (i : UInt8) (n : Nat) : HIn := FrameModel.readIn sy (trace M i n)

/-- that input is an input of the model -/
theorem inAt_mem (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (M : Machine) (i : UInt8) (n : Nat) : inAt sy M i n ∈ inputs :=
  FrameModel.readIn_mem (FrameModel.joy_of_model hOK) _

theorem ff_and_all : ∀ n : Fin 256, (0xFF : UInt8) &&& UInt8.ofNat n.val = UInt8.ofNat n.val := by decide +kernel

theorem ff_and (x : UInt8) : (0xFF : UInt8) &&& x = x := by
  have h := ff_and_all ⟨x.toNat, x.toNat_lt⟩
  simpa using h

/-- **The frame from the scroll handler to its end.** `a` is the machine at the frame's start, `Q` when the frame comes to the scroll handler, `b` at the frame's end. The rest of the frame
does not change the subspeed; it keeps the facing, or the frame ends with the speed 0 and the subspeed 0; and the screen's edge and the collision routine leave one of three things:
nothing, a block of Left moving right, or a hit. The moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler: that is
proved (`AfterKeep.keepH`, `AfterK`). The stored speed at the scroll handler is that of the speed there: proved too (`MovesAt.stored`, by `FrameModel.stored_path`).
The facing is proved too (`MovesAt.face`, by `FaceKeep.keepZ_end`): the field `fd` used to ask that it stays on every frame, which a walk cannot give (a climbing
tile near the screen's left edge turns him and sets the speed and the subspeed to 0). -/
structure After (sy : Syms) (a Q b : Machine) : Prop where
  f : peek b sy.Player_X_MoveForce = peek Q sy.Player_X_MoveForce
  fd : peek b sy.PlayerFacingDir = peek Q sy.PlayerFacingDir ∨ (peek b sy.Player_X_Speed = 0 ∧ peek b sy.Player_X_MoveForce = 0)
  coll : (posP sy b = posP sy Q ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∧ bitsOf sy b = 0xFF) ∨
    (0 < vOf sy Q ∧ posP sy b = posP sy Q ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∧ bitsOf sy b = sy.noLeft) ∨
    (vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy Q - 256 ∨ posP sy b ≤ SurfaceRead.baseOf sy a + 256))

/-- **What `After` still asks of a frame that moves right at the scroll handler** (the field `after` of `Moves`): the position. If the speed stays, the position
stays. If the speed ends 0, the position ends 1 px behind the move, or at most 1 px past the frame's start (the screen's left edge, where he stops only at a low
speed). The other parts of `After` are theorems: the speed stays or ends 0 (`CollideKeep.speed_end`), the facing stays or the speed ends 0 (`FaceKeep.keepZ_end`), the
collision bits end `FF` or those of a block of Left or the speed ends 0 (`FaceKeep.bits_end`), and when he moves left or not at all there, `CollideE` and the move
give `After.coll` (`After.of`). This was `AfterR`, which asked the facing and the collision bits too. -/
structure AfterP (sy : Syms) (a Q b : Machine) : Prop where
  keep : 0 < vOf sy Q → peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed → posP sy b = posP sy Q
  stop : 0 < vOf sy Q → peek b sy.Player_X_Speed = 0 → posP sy b ≤ posP sy Q - 256 ∨ posP sy b ≤ posP sy a + 256

/-- A single ImpedePlayerMove call satisfies the local `AfterP` relation.
This does not identify the call entry with the scroll-handler machine or prove
that the rest of a frame preserves position. -/
theorem AfterP.impede_return {a R : Machine}
    (hc : ImpedePosition.check sy m0 = true)
    (hg : FrameModel.Good (FrameModel.Rom.of m0) R) (hpc : R.pc = sy.ImpedePlayerMove)
    (hl : 256 ≤ posP sy R) (hr : posP sy R + 256 < 0x1000000) :
    ∃ k, k ≤ 65 ∧ (FrameModel.stepN k R).pc = ImpedePosition.returnPc R ∧
      (FrameModel.stepN k R).s = R.s + 1 + 1 ∧ AfterP sy a R (FrameModel.stepN k R) := by
  obtain ⟨k,hk,_,pc,sp,vel,_,_,hm,_⟩ := ImpedePosition.routine_return hc hg hpc
  have ep := ImpedePosition.exact_of_mod hl hr hm
  refine ⟨k,hk,pc,sp,?_⟩
  constructor
  · intro hv same
    exact (ImpedePosition.positive_effect hv vel ep).1 same
  · intro hv zero
    have hp := (ImpedePosition.positive_effect hv vel ep).2 zero
    exact Or.inl (by omega)

/-- **`After` from `AfterP`, `CollideE`, the facing and the collision bits**, at a machine `Q` at the scroll handler that the move put at `P(a) + 16·v(Q)`. `hfd` is
what `FaceKeep.keepZ_end` proves of the facing, `hbits` what `FaceKeep.bits_end` proves of the collision bits. -/
theorem After.of {a Q b : Machine} (h : AfterP sy a Q b) (c : SurfaceRead.CollideE sy (SurfaceRead.baseOf sy a) Q b)
    (hfd : peek b sy.PlayerFacingDir = peek Q sy.PlayerFacingDir ∨ (peek b sy.Player_X_Speed = 0 ∧ peek b sy.Player_X_MoveForce = 0))
    (hbits : 0 < vOf sy Q → (bitsOf sy b = 0xFF ∨ bitsOf sy b = sy.noLeft) ∨ peek b sy.Player_X_Speed = 0)
    (hP : posP sy Q = posP sy a + 16 * vOf sy Q) : After sy a Q b := by
  refine ⟨c.f, hfd, ?_⟩
  have hba := SurfaceRead.le_baseOf (sy := sy) a
  have hz0 : sbyte (0 : UInt8) = 0 := by decide
  by_cases hv : 0 < vOf sy Q
  · rcases c.v with e | e
    · have hp := h.keep hv e
      rcases hbits hv with (b1 | b1) | z
      · exact Or.inl ⟨hp, e, b1⟩
      · exact Or.inr (Or.inl ⟨hv, hp, e, b1⟩)
      · exfalso
        have e1 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
        rw [← e, z] at e1
        omega
    · refine Or.inr (Or.inr ⟨?_, (h.stop hv e).imp id (fun x => by omega)⟩)
      show sbyte (peek b sy.Player_X_Speed) ≤ 0
      rw [e]
      decide
  · have hv' : sbyte (peek Q sy.Player_X_Speed) ≤ 0 := by
      have : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
      omega
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · show sbyte (peek b sy.Player_X_Speed) ≤ 0
      rcases c.v with e | e
      · rw [e]
        exact hv'
      · rw [e]
        decide
    · have : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
      rcases c.P with e | e | ⟨_, e2, _⟩ <;> omega

/-- **What the field `collide` asks of a frame before the touch, from the scroll handler `Q` to its end `b`** (`M` the machine at the end of the frame before): the
position as in `SurfaceRead.CollideE`; and of the subspeed only this: a frame that ends with the speed 0 and the subspeed 0 has the subspeed 0 at the scroll handler.
Every other frame keeps the subspeed, by a walk (`FaceKeep.keepZ_end`). This was `SurfaceRead.CollideR`, which asked that the subspeed stays on every frame. -/
structure CollideS (sy : Syms) (M Q b : Machine) (calls : Prop) : Prop where
  f : peek b sy.Player_X_Speed = 0 → peek b sy.Player_X_MoveForce = 0 → peek Q sy.Player_X_MoveForce = 0
  /-- the position, on a frame that calls the push or the clamp after the scroll handler (`calls`), and does not move right at the scroll handler and keep that
  speed to its end (on the other frames the position stays: theorems, `PositionKeep.still_frame`, `PositionKeep.keep_frame`) -/
  P : calls → ¬ (0 < sbyte (peek Q sy.Player_X_Speed) ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed) →
    (posP sy b = posP sy Q ∨ posP sy b = posP sy Q - 256 ∨
      (posP sy Q ≤ posP sy b ∧ posP sy b ≤ SurfaceRead.baseOf sy M + 256 ∧ sbyte (peek Q sy.Player_X_Speed) ≤ 0))

/-- `CollideS`, what the walk of the subspeed proves, the position on a frame that keeps a speed to the right (`hk`, `PositionKeep.keep_frame`) and on a frame
that makes no call (`hs`, `PositionKeep.still_frame`) give `SurfaceRead.CollideR` -/
theorem CollideS.toR {M Q b : Machine} {calls : Prop} (h : CollideS sy M Q b calls)
    (hf : peek b sy.Player_X_MoveForce = peek Q sy.Player_X_MoveForce ∨ (peek b sy.Player_X_Speed = 0 ∧ peek b sy.Player_X_MoveForce = 0))
    (hk : 0 < sbyte (peek Q sy.Player_X_Speed) → peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed → posP sy b = posP sy Q)
    (hs : ¬ calls → posP sy b = posP sy Q) :
    SurfaceRead.CollideR sy (SurfaceRead.baseOf sy M) Q b := by
  refine ⟨?_, ?_⟩
  · rcases hf with e | ⟨e1, e2⟩
    · exact e
    · rw [e2, h.f e1 e2]
  · rcases Classical.em calls with c | c
    · rcases Classical.em (0 < sbyte (peek Q sy.Player_X_Speed) ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed) with e | e
      · exact Or.inl (hk e.1 e.2)
      · exact h.P c e
    · exact Or.inl (hs c)

/-- **The frame of `M` with the input `i` calls the push or the clamp at the screen's edge from the instruction `k` on**, in the frame -/
def Calls (sy : Syms) (m0 M : Machine) (i : UInt8) (k : Nat) : Prop :=
  ∃ n, k ≤ n ∧ (PipeEntryRule.trace M i n).frame = M.frame ∧
    ((PipeEntryRule.trace M i n).pc = sy.ImpedePlayerMove ∨ (PipeEntryRule.trace M i n).pc = (ScreenClamp.places sy m0).entry)

/-- **A real frame from the state `a`, at the player's routine**: the frame of `M` with the input `i`, which comes to the player's routine at the instruction `n₀`. `M` is `a`, or later
by `lag` frames. The input of the model is the one the routine reads there (`inAt`), so it is no condition. The fields `at_ctrl`, `before`, `bits` are a theorem (`Moves.toAt`)
from the walk of `CtrlKeep` and the conditions of `Moves` at the frame's ends. -/
structure MovesAt (sy : Syms) (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  /-- at the player's routine, the state that `hstep` needs, but the mask (`FrameModel.AtCtrl0`) -/
  at_ctrl : AtCtrl0 sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀)
  /-- from `a` to there, nothing writes the horizontal bytes -/
  before : ∀ x ∈ hBytes sy, peek (trace M i n₀) x = peek a x
  /-- nor the collision bits -/
  bits : bitsOf sy (trace M i n₀) = bitsOf sy a
  /-- the routine comes in the frame of `M` -/
  start : (trace M i n₀).frame = M.frame
  /-- each instruction of the frame but the idle loop runs at least 64 dots before the frame's end (`FrameKeep.CleanK.time`) -/
  time : ∀ n, (trace M i n).pc ≠ sy.EndlessLoop → (trace M i n).fdot ≤ dotsPerFrame - 64
  /-- the idle loop is a `JMP` to itself -/
  idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true
  /-- the position is away from both ends of its range -/
  far : 2048 ≤ posP sy a ∧ posP sy a + 2048 < 0x1000000
  /-- the rest of the frame, from the scroll handler: what `After` asks of the position when he moves right there -/
  after : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → AfterP sy a (trace M i k) (frame M i)
  /-- and `CollideE` there (the field `collide` of `OnFrames`, with the walks of the speed and of the subspeed) -/
  collide : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → SurfaceRead.CollideE sy (SurfaceRead.baseOf sy a) (trace M i k) (frame M i)
  /-- the moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler (`AfterKeep.keepH`) -/
  keepH : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → ∀ x ∈ AfterKeep.hI sy, (frame M i).ram.get! x = (trace M i k).ram.get! x
  /-- at the scroll handler the stored speed is that of the speed (`storedQ_of`, from `FrameModel.stored_path` and `AfterKeep.subs_once`) -/
  stored : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → peek (trace M i k) sy.Player_XSpeedAbsolute = absB (peek (trace M i k) sy.Player_X_Speed)
  /-- the facing at the frame's end is that at the scroll handler, or the frame ends with the speed 0 and the subspeed 0 (`FaceKeep.keepZ_end`) -/
  face : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs →
    peek (frame M i) sy.PlayerFacingDir = peek (trace M i k) sy.PlayerFacingDir ∨
      (peek (frame M i) sy.Player_X_Speed = 0 ∧ peek (frame M i) sy.Player_X_MoveForce = 0)
  /-- a frame that moves right at the scroll handler ends with the collision bits `FF` or those of a block of Left, or with the speed 0 (`FaceKeep.bits_end`) -/
  bitsR : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) →
    (bitsOf sy (frame M i) = 0xFF ∨ bitsOf sy (frame M i) = sy.noLeft) ∨ peek (frame M i) sy.Player_X_Speed = 0

/-- **The frame from the scroll handler to its end**, as the movement needs it: `After`, the three bytes of `AfterKeep.hI` at the frame's end are those of `Q`, and the
stored speed at `Q` is that of the speed there -/
structure AfterK (sy : Syms) (a Q b : Machine) : Prop where
  after : After sy a Q b
  keep : ∀ x ∈ AfterKeep.hI sy, b.ram.get! x = Q.ram.get! x
  storedQ : peek Q sy.Player_XSpeedAbsolute = absB (peek Q sy.Player_X_Speed)

theorem AfterK.md {a Q b : Machine} (h : AfterK sy a Q b) : peek b sy.Player_MovingDir = peek Q sy.Player_MovingDir := h.keep _ (by simp [AfterKeep.hI])

theorem AfterK.rs {a Q b : Machine} (h : AfterK sy a Q b) : peek b sy.RunningSpeed = peek Q sy.RunningSpeed := h.keep _ (by simp [AfterKeep.hI])

theorem AfterK.stored {a Q b : Machine} (h : AfterK sy a Q b) : peek b sy.Player_XSpeedAbsolute = absB (peek Q sy.Player_X_Speed) :=
  (h.keep (sy.Player_XSpeedAbsolute &&& 0x7FF).toNat (by simp [AfterKeep.hI])).trans h.storedQ

theorem readHS_eq (sy : Syms) (m : Machine) : FrameModel.readHS sy m = startHS sy m := rfl

/-- **The movement of the real frame.** The frame comes to the scroll handler at a machine `Q` that has the horizontal state of `hstep` and the position moved by `16·v₂`, and the rest of the
frame is `After`. `hOK` is the check on the ROM of `FrameModel`. -/
theorem at_subs (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (h : MovesAt sy m0 a M i n₀) (hm : ¬ Masked sy (inAt sy M i n₀) a) :
    ∃ k, n₀ ≤ k ∧ (trace M i k).pc = sy.PlayerSubs ∧ startHS sy (trace M i k) = modelS sy m0 a (inAt sy M i n₀) ∧
      posP sy (trace M i k) = posP sy a + 16 * vOf sy (trace M i k) ∧ AfterK sy a (trace M i k) (frame M i) := by
  have hc : peek (trace M i n₀) sy.Player_CollisionBits &&& lrOf (Potential.norm (FrameModel.readIn sy (trace M i n₀))) =
      lrOf (Potential.norm (FrameModel.readIn sy (trace M i n₀))) := by
    have e : bitsOf sy (trace M i n₀) = bitsOf sy a := h.bits
    unfold Masked at hm
    unfold bitsOf at e hm
    rw [e]
    by_cases e2 : peek a sy.Player_CollisionBits &&& lrOf (Potential.norm (inAt sy M i n₀)) = lrOf (Potential.norm (inAt sy M i n₀))
    · exact e2
    · exact absurd e2 hm
  obtain ⟨k, hk, _, hpc, h1, h2, hC⟩ := FrameModel.move_model hOK (h.at_ctrl.mk1 hc)
  have e0 := (FrameModel.trace_inFrame h.idle h.start hC h.time k (Nat.le_refl k)).1
  have e2 : FrameModel.readHS sy (trace M i n₀) = FrameModel.readHS sy a := FrameModel.readHS_congr h.before
  have e3 : posP sy (trace M i n₀) = posP sy a := FrameModel.posP_congr h.before
  rw [e2] at h1
  rw [e3] at h2
  rw [← e0] at h1 h2 hpc
  have hmove : posP sy (trace M i (n₀ + k)) = posP sy a + 16 * vOf sy (trace M i (n₀ + k)) := by
    have ev : sbyte (FrameModel.readHS sy (trace M i (n₀ + k))).v = vOf sy (trace M i (n₀ + k)) := rfl
    rw [ev] at h2
    obtain ⟨a1, a2⟩ := FrameModel.posOf_range (peek (trace M i (n₀ + k)) sy.Player_PageLoc) (peek (trace M i (n₀ + k)) sy.Player_X_Position)
      (peek (trace M i (n₀ + k)) sy.SprObject_X_MoveForce)
    rw [← FrameModel.posP_eq] at a1 a2
    have a3 := FrameModel.sbyte_range (peek (trace M i (n₀ + k)) sy.Player_X_Speed)
    have a4 := h.far
    have ev2 : vOf sy (trace M i (n₀ + k)) = sbyte (peek (trace M i (n₀ + k)) sy.Player_X_Speed) := rfl
    omega
  exact ⟨n₀ + k, by omega, hpc, h1, hmove, After.of (h.after (n₀ + k) (by omega) hpc) (h.collide (n₀ + k) (by omega) hpc) (h.face (n₀ + k) (by omega) hpc)
    (h.bitsR (n₀ + k) (by omega) hpc) hmove, h.keepH (n₀ + k) (by omega) hpc, h.stored (n₀ + k) (by omega) hpc⟩

/-- **A frame that ends with the speed 0 is a hit**, if the rest of the frame is `After` and the move put `Q` at `P(a) + 16·v(Q)`: the collision routine or the
screen's edge stopped him, or he did not move at all. -/
theorem hit_of_stop {Q b : Machine} {u : HIn} (A : After sy a Q b) (hz : peek b sy.Player_X_Speed = 0) (ev : (modelS sy m0 a u).v = peek Q sy.Player_X_Speed)
    (hP : posP sy Q = posP sy a + 16 * vOf sy Q) : Hit sy m0 u a b := by
  have hba := SurfaceRead.le_baseOf (sy := sy) a
  have ev2 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
  have hz0 : sbyte (0 : UInt8) = 0 := by decide
  have hb0 : vOf sy b = 0 := by
    show sbyte (peek b sy.Player_X_Speed) = 0
    rw [hz]
    exact hz0
  unfold Hit
  rw [ev]
  rcases A.coll with ⟨c1, c2, _⟩ | ⟨c0, _, c2, _⟩ | ⟨c1, c2⟩
  · have e : sbyte (peek Q sy.Player_X_Speed) = 0 := by rw [← c2, hz]; exact hz0
    exact ⟨by omega, Or.inr (by omega)⟩
  · have e : sbyte (peek Q sy.Player_X_Speed) = 0 := by rw [← c2, hz]; exact hz0
    omega
  · exact ⟨c1, by omega⟩

/-- **`Pre` from the movement and the rest of the frame**, when the facing at the frame's end is that at the scroll handler -/
theorem pre_of_after {Q b : Machine} {u : HIn} (h1 : startHS sy Q = modelS sy m0 a u) (A : AfterK sy a Q b)
    (hfd : peek b sy.PlayerFacingDir = peek Q sy.PlayerFacingDir) : Pre sy m0 u a b := by
  have ev : (modelS sy m0 a u).v = peek Q sy.Player_X_Speed := by rw [← h1]; rfl
  refine ⟨?_, ?_⟩
  · rw [← h1]
    simp only [startHS, PState.read, A.after.f, hfd, A.md, A.rs]
    rfl
  · rw [ev]
    exact A.stored

/-- **A real frame is a `OneFrame`.** From the movement, proved, and the rest of the frame, `Moves`: it is `hstep` up to the collision routine and what the routine
leaves, or (when the facing is not that of the scroll handler, so the frame ends with the speed 0) a hit. -/
theorem one_of_moves (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (h : MovesAt sy m0 a M i n₀) (hm : ¬ Masked sy (inAt sy M i n₀) a) :
    (Pre sy m0 (inAt sy M i n₀) a (frame M i) ∧ Coll sy m0 (inAt sy M i n₀) a (frame M i)) ∨ Hit sy m0 (inAt sy M i n₀) a (frame M i) := by
  obtain ⟨k, _, _, h1, h2, A⟩ := at_subs hOK h hm
  generalize trace M i k = Q at h1 h2 A
  generalize frame M i = b at h1 h2 A ⊢
  generalize inAt sy M i n₀ = u at h1 ⊢
  have ev : (modelS sy m0 a u).v = peek Q sy.Player_X_Speed := by rw [← h1]; rfl
  have ev2 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
  rcases A.after.fd with hfd | ⟨hz, _⟩
  · refine Or.inl ⟨pre_of_after h1 A hfd, ?_⟩
    unfold Coll Hit
    rw [ev]
    rcases A.after.coll with ⟨c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c1, c2⟩
    · refine Or.inl ⟨by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩
    · refine Or.inr (Or.inl ⟨by omega, by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩)
    · exact Or.inr (Or.inr ⟨c1, by omega⟩)
  · exact Or.inr (hit_of_stop A.after hz ev h2)

/-- a clean state with the pressed side masked has the bits of a block of Left and moves right -/
theorem masked_clean {i : HIn} (hc : Clean sy a) (hm : Masked sy i a) : bitsOf sy a = sy.noLeft ∧ 0 < vOf sy a := by
  rcases hc.2.2 with e | e
  · unfold Masked at hm
    rw [e, ff_and] at hm
    exact absurd rfl hm
  · exact e

theorem pos_of_v {v : UInt8} (h : 0 < sbyte v) : v ≠ 0 ∧ v < 0x80 := by
  unfold sbyte at h
  split at h
  · rename_i h1
    refine ⟨fun e => ?_, h1⟩
    rw [e] at h
    exact absurd h (by decide)
  · rename_i h1
    have h2 := v.toNat_lt
    exfalso
    omega

theorem lt80_all : ∀ n : Fin 256, n.val < 128 → UInt8.ofNat n.val &&& 0x80 = 0 := by decide +kernel

/-- a speed to the right has the sign bit 0 -/
theorem sign_of_pos {v : UInt8} (h : 0 < sbyte v) : v &&& 0x80 = 0 := by
  have h1 := (pos_of_v h).2
  have h2 := lt80_all ⟨v.toNat, v.toNat_lt⟩ (by
    have := UInt8.lt_iff_toNat_lt.1 h1
    simpa using this)
  simpa using h2

/-- **The movement of a real frame with the pressed side masked.** The frame comes to the scroll handler at a machine `Q` that follows `hstep`, or has the speed 0,
and the position moved by `16·v(Q)`. `hmk` is the check on the ROM of the masked frames. -/
theorem at_subsM (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hmk : FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (h : MovesAt sy m0 a M i n₀) (hc : Clean sy a) (hm : Masked sy (inAt sy M i n₀) a) :
    ∃ k, n₀ ≤ k ∧ (trace M i k).pc = sy.PlayerSubs ∧ (startHS sy (trace M i k) = modelS sy m0 a (inAt sy M i n₀) ∨ vOf sy (trace M i k) = 0) ∧
      posP sy (trace M i k) = posP sy a + 16 * vOf sy (trace M i k) ∧ AfterK sy a (trace M i k) (frame M i) := by
  obtain ⟨hb, hv⟩ := masked_clean hc hm
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek a sy.Player_X_Speed := h.before _ (.head _)
  obtain ⟨hv1, hv2⟩ := pos_of_v hv
  have hRb : peek (trace M i n₀) sy.Player_CollisionBits = sy.noLeft := by
    have e : bitsOf sy (trace M i n₀) = bitsOf sy a := h.bits
    rw [← hb]
    exact e
  have hml : FrameModel.maskedLr sy (lrOf (Potential.norm (FrameModel.readIn sy (trace M i n₀)))) = true := by
    unfold Masked inAt at hm
    unfold FrameModel.maskedLr
    have e : bitsOf sy a = sy.noLeft := hb
    rw [e] at hm
    simpa using hm
  obtain ⟨k, hk, _, hpc, h1, h2, hC⟩ := FrameModel.move_masked hOK hmk h.at_ctrl hRb hml (by rw [ev]; exact hv1) (by rw [ev]; exact hv2)
  have e0 := (FrameModel.trace_inFrame h.idle h.start hC h.time k (Nat.le_refl k)).1
  have e2 : FrameModel.readHS sy (trace M i n₀) = FrameModel.readHS sy a := FrameModel.readHS_congr h.before
  have e3 : posP sy (trace M i n₀) = posP sy a := FrameModel.posP_congr h.before
  rw [e2] at h1
  rw [e3] at h2
  rw [← e0] at h1 h2 hpc
  have hmove : posP sy (trace M i (n₀ + k)) = posP sy a + 16 * vOf sy (trace M i (n₀ + k)) := by
    have ev2 : sbyte (FrameModel.readHS sy (trace M i (n₀ + k))).v = vOf sy (trace M i (n₀ + k)) := rfl
    rw [ev2] at h2
    obtain ⟨a1, a2⟩ := FrameModel.posOf_range (peek (trace M i (n₀ + k)) sy.Player_PageLoc) (peek (trace M i (n₀ + k)) sy.Player_X_Position)
      (peek (trace M i (n₀ + k)) sy.SprObject_X_MoveForce)
    rw [← FrameModel.posP_eq] at a1 a2
    have a3 := FrameModel.sbyte_range (peek (trace M i (n₀ + k)) sy.Player_X_Speed)
    have a4 := h.far
    have ev3 : vOf sy (trace M i (n₀ + k)) = sbyte (peek (trace M i (n₀ + k)) sy.Player_X_Speed) := rfl
    omega
  refine ⟨n₀ + k, by omega, hpc, ?_, hmove, ⟨After.of (h.after (n₀ + k) (by omega) hpc) (h.collide (n₀ + k) (by omega) hpc) (h.face (n₀ + k) (by omega) hpc)
    (h.bitsR (n₀ + k) (by omega) hpc) hmove, h.keepH (n₀ + k) (by omega) hpc, h.stored (n₀ + k) (by omega) hpc⟩⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · right
    show sbyte (peek (trace M i (n₀ + k)) sy.Player_X_Speed) = 0
    rw [h1]
    rfl

/-- **A real frame with the pressed side masked is a `OneFrame`**: it follows `hstep`, or it stops (`MaskStop`). -/
theorem one_of_movesM (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hmk : FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (h : MovesAt sy m0 a M i n₀) (hc : Clean sy a) (hm : Masked sy (inAt sy M i n₀) a) : OneFrame sy m0 (inAt sy M i n₀) a (frame M i) := by
  obtain ⟨k, _, _, h1, h2, A⟩ := at_subsM hOK hmk h hc hm
  generalize trace M i k = Q at h1 h2 A
  generalize frame M i = b at A ⊢
  unfold OneFrame
  rcases h1 with h1 | h1
  · right
    generalize inAt sy M i n₀ = u at h1 ⊢
    have ev : (modelS sy m0 a u).v = peek Q sy.Player_X_Speed := by rw [← h1]; rfl
    rcases A.after.fd with hfd | ⟨hz, _⟩
    · refine Or.inl ⟨pre_of_after h1 A hfd, ?_⟩
      unfold Coll Hit
      rw [ev]
      have ev2 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
      rcases A.after.coll with ⟨c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c1, c2⟩
      · refine Or.inl ⟨by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩
      · refine Or.inr (Or.inl ⟨by omega, by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩)
      · exact Or.inr (Or.inr ⟨c1, by omega⟩)
    · exact Or.inr (hit_of_stop A.after hz ev h2)
  · left
    have hba := SurfaceRead.le_baseOf (sy := sy) a
    obtain ⟨hb, _⟩ := masked_clean hc hm
    rw [h1] at h2
    refine ⟨hb, ?_, ?_⟩
    · rcases A.after.coll with ⟨_, c2, _⟩ | ⟨c0, _, _, _⟩ | ⟨c1, _⟩
      · show sbyte (peek b sy.Player_X_Speed) ≤ 0
        rw [c2]
        have : sbyte (peek Q sy.Player_X_Speed) = 0 := h1
        omega
      · rw [h1] at c0
        exact absurd c0 (by decide)
      · exact c1
    · rcases A.after.coll with ⟨c1, _, _⟩ | ⟨c0, _, _, _⟩ | ⟨_, c2⟩
      · omega
      · rw [h1] at c0
        exact absurd c0 (by decide)
      · omega

/-! ### The frame up to the player's routine, from the walk of `CtrlKeep` -/

/-- **The values that the player's routine needs, at the end of the frame before**: the player's state, no jumpspring. The area's type, the swimming flag and the change
of size are not here: every frame keeps them (`OnFrames.areaAll`); nor is bit 7 of A of the frame before: every frame keeps it equal to that of A (`OnFrames.prevAll`). -/
structure CtlState (sy : Syms) (m : Machine) : Prop where
  st : peek m sy.Player_State ∈ [(0 : UInt8), 1, 2]
  spring : peek m sy.JumpspringAnimCtrl = 0

/-- `CtlState` as a check, for a program; with the area's type one of 1, 2, 3, the swimming flag 0, the change of size 0, and bit 7 of A of the frame before that of A -/
def ctlStateB (sy : Syms) (m : Machine) : Bool :=
  [(1 : UInt8), 2, 3].contains (peek m sy.AreaType) && [(0 : UInt8), 1, 2].contains (peek m sy.Player_State) && peek m sy.JumpspringAnimCtrl == 0 &&
    peek m sy.SwimmingFlag == 0 && peek m sy.PlayerChangeSizeFlag == 0 && PrevKeep.prevOKB sy m

/-- **A real frame from the state `a`**: the frame of `M` with the input `i`, which comes to the player's routine at the instruction `n₀`. `M` is `a`, or later by `lag` frames.
The state at the player's routine is a theorem (`Moves.toAt`, by the walk of `CtrlKeep`), and so are the first arrival at the routine and that the `lag` frames keep the
bytes (`OnFrames.arrive`, `OnFrames.lagKeep`); what is assumed is the rest of the frame. The state at the end of the frame before (`CtlState`) is the field `state` of
`OnFrames`, on every frame (it was the field `Moves.state`). That the position is away from both ends of its range is not a field: on the frames where it is needed it
comes from the frames before, which follow `hstep` (`far_of_follow`). -/
structure Moves (sy : Syms) (m0 a M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  /-- the rest of the frame, from the scroll handler: on a frame that moves right there and ends with the speed 0, where the position ends (`AfterP.stop`). That the
  position stays when the speed stays (`AfterP.keep`) is a theorem (`PositionKeep.keep_frame`, from the fields `posW` and `clampR` of `OnFrames`). The facing and
  the collision bits are theorems (`FaceKeep.keepZ_end`, `FaceKeep.bits_end`); the position on the other frames is in the field `collide` of `OnFrames`. Round 28:
  asked only of a frame that ends at the position of the scroll handler: on such a frame that moves right there, `CollideE` leaves the position there or 1 px
  behind it, and 1 px behind is the first case of `AfterP.stop` (`StopAt.stopP`). So what is left is a frame that sets the speed to 0 and leaves the position as it
  is after the move (two pushes that cancel, a call that sets the speed to 0 without a push). Round 32: asked only of a frame where at the scroll handler he is
  right of the screen's left edge, or that starts left of it. On the other frames (at the scroll handler at or left of the edge, at the start at or right of it) the
  frame keeps the edge up to the scroll handler, so his pixel there is at most that of the start: `OnFrames.stopAt` (the old field is `StopAt`). Round 33: where
  he is right of the edge at the scroll handler, asked only of a frame that ends with the side collision's timer at the value the push stores
  (`PushTimer.pushT`: a push on this frame). A frame that ends with the timer at another value ends at the left edge (`OnFrames.stopRight`: the speed 0 at the end comes from the clamp, and it is the left clamp), and then, right of the edge at
  the scroll handler, the edge moved there on this frame, which the scroll's rule and `EdgeStep.NearX` exclude (`OnFrames.noStopRight`). And where the frame
  starts left of the edge, asked only when the frame before ended with the timer at the push's value: a counted frame that ends with the timer at another value ends at or
  right of the edge (`OnFrames.leftEnd`), and so does the machine at control (`AreaRun.edge₀`). So the field is asked only on a frame with a push: the timer at
  the push's value at the end of this frame or of the frame before. -/
  stop : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) → peek (frame M i) sy.Player_X_Speed = 0 →
    posP sy (frame M i) = posP sy (trace M i k) →
    ((ScrollRule.left16 (ScrollRule.places sy m0) (trace M i k) < EdgeStep.pixel16 sy (trace M i k) ∧
        (frame M i).ram.get! (ScrollRule.places sy m0).sideB = PushTimer.pushT sy m0) ∨
      (EdgeStep.pixel16 sy a < ScrollRule.left16 (ScrollRule.places sy m0) a ∧ a.ram.get! (ScrollRule.places sy m0).sideB = PushTimer.pushT sy m0)) →
    posP sy (trace M i k) ≤ posP sy a + 256

/-- **The old field `Moves.stop`** (round 32: a theorem, `OnFrames.stopAt`, from the narrowed field): on a frame that moves right at the scroll handler, ends with
the speed 0 and ends at the position there, the position there is at most 1 px past that of `a` -/
def StopAt (sy : Syms) (a M : Machine) (i : UInt8) (n₀ : Nat) : Prop :=
  ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) → peek (frame M i) sy.Player_X_Speed = 0 →
    posP sy (frame M i) = posP sy (trace M i k) → posP sy (trace M i k) ≤ posP sy a + 256

/-- **`AfterP.stop` from `StopAt` and `CollideE`** (round 28): on a frame that moves right at the scroll handler and ends with the speed 0, `CollideE` leaves the
position there or 1 px behind it (its third case needs the speed at most 0 there); 1 px behind is the first case, and there `StopAt` gives the second. -/
theorem StopAt.stopP (h : StopAt sy a M i n₀)
    (hco : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → SurfaceRead.CollideE sy (SurfaceRead.baseOf sy a) (trace M i k) (frame M i)) :
    ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) → peek (frame M i) sy.Player_X_Speed = 0 →
      posP sy (frame M i) ≤ posP sy (trace M i k) - 256 ∨ posP sy (frame M i) ≤ posP sy a + 256 := by
  intro k hk hpc hv h0
  rcases (hco k hk hpc).P with e | e | ⟨_, _, e3⟩
  · exact Or.inr (by rw [e]; exact h k hk hpc hv h0 e)
  · exact Or.inl (by omega)
  · exfalso
    have e4 : vOf sy (trace M i k) = sbyte (peek (trace M i k) sy.Player_X_Speed) := rfl
    omega

theorem keepA_mem {x : UInt16} (h : x ∈ FrameModel.hBytes sy ∨ x ∈ vKeep sy ∨ x = sy.Player_CollisionBits ∨ x = sy.Player_XSpeedAbsolute ∨ x = sy.AreaType ∨
    x = sy.JumpspringAnimCtrl ∨ x = sy.SwimmingFlag ∨ x = sy.PlayerChangeSizeFlag ∨ x = sy.A_B_Buttons ∨ x = sy.PreviousA_B_Buttons) : x ∈ CtrlKeep.keepA sy := by
  unfold CtrlKeep.keepA
  simp only [FrameModel.hBytes, vKeep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h
  · rcases h with h | h | h | h | h | h | h | h <;> simp [h]
  · rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]
  all_goals simp [h]

/-- the frame of `M` with the input `i` comes to the player's routine at the instruction `n₀`, the first time, before its end -/
def Arrive (sy : Syms) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop :=
  (trace M i n₀).pc = sy.PlayerCtrlRoutine ∧ (trace M i n₀).frame = M.frame ∧ ∀ n, n < n₀ → (trace M i n).pc ≠ sy.PlayerCtrlRoutine

/-- **The stored speed at the scroll handler is that of the speed.** At the player's routine `R` (`AtCtrl0`, so the stored speed is `|v|` there), the speed and the
collision bits are those of a clean state `a`. The walks of `FrameModel.stored_path` come to the scroll handler with the stored speed `|v|` (`hOK`, `hfr`, `hso` are
the checks on the ROM), and the frame comes to the scroll handler once after the player's routine (`honce`, `AfterKeep.subs_once`). -/
theorem storedQ_of (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hat : AtCtrl0 sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀))
    (hc : Clean sy a) (hv : peek (trace M i n₀) sy.Player_X_Speed = peek a sy.Player_X_Speed) (hb : bitsOf sy (trace M i n₀) = bitsOf sy a)
    (hstart : (trace M i n₀).frame = M.frame) (htime : ∀ n, (trace M i n).pc ≠ sy.EndlessLoop → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace M i k).pc = sy.PlayerSubs → (trace M i k').pc = sy.PlayerSubs → k = k') :
    ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → peek (trace M i k) sy.Player_XSpeedAbsolute = absB (peek (trace M i k) sy.Player_X_Speed) := by
  have hcoll : peek (trace M i n₀) sy.Player_CollisionBits ∈ TopSpeed.collBits sy := by
    have e : peek (trace M i n₀) sy.Player_CollisionBits = bitsOf sy a := hb
    rw [e]
    rcases hc.2.2 with e2 | ⟨e2, _⟩ <;> rw [e2] <;> simp [TopSpeed.collBits]
  have hsp : TopSpeed.inSpeed sy (peek (trace M i n₀) sy.Player_X_Speed) = true := by
    rw [hv]
    have h1 := hc.1
    simp only [inD, Bool.and_eq_true] at h1
    exact h1.1.1.1
  have hF : FrameModel.AtFrame sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀) :=
    ⟨hat.good, hat.pc, hat.s, hat.eng, hat.area, hat.st, hat.spring, hat.swim, hat.size, hcoll, hsp⟩
  obtain ⟨k₁, hpc, hst, hC⟩ := FrameModel.stored_path hOK hfr hso hF hat.abs
  have e0 := (FrameModel.trace_inFrame hidle hstart hC htime k₁ (Nat.le_refl k₁)).1
  intro k hk hpck
  have e1 : k = n₀ + k₁ := honce k (n₀ + k₁) hk (by omega) hpck (by rw [e0]; exact hpc)
  rw [e1, e0]
  exact hst

/-- **The state at the player's routine, from the frame's start.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each of its instructions meets
`FrameKeep.CleanK`, and `ctrlCheck` is the walk's check on the ROM. It comes to the player's routine at `n₀` (`harr`), and the `lag` frames before it keep the bytes of
`CtrlKeep.keepA` (`hlag`). The area's type is one of 1, 2, 3, the swimming flag 0 and the change of size 0 at the end of the frame before (`harea`, `hswim`, `hsize`:
`OnFrames.areaAll`). The position is away from both ends of its range (`hfar`).
Then the state at the end of the frame before (`hs`) and the rest of the frame (`StopAt`, round 32: from the field `Moves.stop` by `OnFrames.stopAt`) give the
state at the player's routine (`MovesAt`). -/
theorem Moves.toAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true) (h0 : FrameKeep.StartK sy m0 M)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace M i n)) (hc : Clean sy a) (harr : Arrive sy M i n₀)
    (hlag : ∀ x ∈ CtrlKeep.keepA sy, peek M x = peek a x) (harea : peek a sy.AreaType ∈ [(1 : UInt8), 2, 3]) (hswim : peek a sy.SwimmingFlag = 0)
    (hsize : peek a sy.PlayerChangeSizeFlag = 0) (hfar : 2048 ≤ posP sy a ∧ posP sy a + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (hkh : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → ∀ x ∈ AfterKeep.hI sy, (frame M i).ram.get! x = (trace M i k).ram.get! x)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace M i k).pc = sy.PlayerSubs → (trace M i k').pc = sy.PlayerSubs → k = k')
    (hs : CtlState sy a) (hco : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → SurfaceRead.CollideE sy (SurfaceRead.baseOf sy a) (trace M i k) (frame M i))
    (hface : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs →
      peek (frame M i) sy.PlayerFacingDir = peek (trace M i k) sy.PlayerFacingDir ∨
        (peek (frame M i) sy.Player_X_Speed = 0 ∧ peek (frame M i) sy.Player_X_MoveForce = 0))
    (hbitsR : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) →
      (bitsOf sy (frame M i) = 0xFF ∨ bitsOf sy (frame M i) = sy.noLeft) ∨ peek (frame M i) sy.Player_X_Speed = 0)
    (hkeep : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → 0 < vOf sy (trace M i k) →
      peek (frame M i) sy.Player_X_Speed = peek (trace M i k) sy.Player_X_Speed → posP sy (frame M i) = posP sy (trace M i k))
    (h : StopAt sy a M i n₀) : MovesAt sy m0 a M i n₀ := by
  have A := CtrlKeep.ctrl_keep hck h0 hcl harr.1 harr.2.1 harr.2.2
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace M i n₀) x = peek a x := fun x hx => (A.keep x hx).trans (hlag x hx)
  have S := hs
  have hat : AtCtrl0 sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i n₀) := by
    refine ⟨A.good, harr.1, A.s, A.eng, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kp _ (keepA_mem (by simp))]
      exact harea
    · rw [kp _ (keepA_mem (by simp [vKeep]))]
      exact S.st
    · rw [kp _ (keepA_mem (by simp))]
      exact S.spring
    · rw [kp _ (keepA_mem (by simp))]
      exact hswim
    · rw [kp _ (keepA_mem (by simp))]
      exact hsize
    · rw [kp _ (keepA_mem (by simp)), kp _ (keepA_mem (by simp [FrameModel.hBytes]))]
      exact hc.2.1
  have hbits : bitsOf sy (trace M i n₀) = bitsOf sy a := kp _ (keepA_mem (by simp))
  have htime : ∀ n, (trace M i n).pc ≠ sy.EndlessLoop → (trace M i n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hcl n).time hn
  exact ⟨hat, fun x hx => kp x (keepA_mem (Or.inl hx)), hbits, harr.2.1, htime, hidle, hfar, fun k hk hpc => ⟨hkeep k hk hpc, h.stopP hco k hk hpc⟩, hco, hkh,
    storedQ_of hOK hfr hso hat hc (kp _ (keepA_mem (Or.inl (by simp [FrameModel.hBytes])))) hbits harr.2.1 htime hidle honce, hface, hbitsR⟩

/-- **The vertical bytes at the player's routine**, from the frame's start, as `Moves.toAt`: the vertical bytes and A are those of `a`, and bit 7 of A of the frame before
is that of A, if it is so on `a` (`hprev`, every frame keeps it: `OnFrames.prevAll`). -/
theorem vBefore (hck : CtrlKeep.ctrlCheck sy m0 = true) (h0 : FrameKeep.StartK sy m0 M)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace M i n)) (harr : Arrive sy M i n₀)
    (hlag : ∀ x ∈ CtrlKeep.keepA sy, peek M x = peek a x) (hprev : PrevKeep.PrevOK sy a) :
    (∀ x ∈ vKeep sy, peek (trace M i n₀) x = peek a x) ∧
    peek (trace M i n₀) sy.A_B_Buttons &&& 0x80 = peek a sy.A_B_Buttons &&& 0x80 ∧
    peek (trace M i n₀) sy.PreviousA_B_Buttons &&& 0x80 = peek (trace M i n₀) sy.A_B_Buttons &&& 0x80 := by
  have A := CtrlKeep.ctrl_keep hck h0 hcl harr.1 harr.2.1 harr.2.2
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace M i n₀) x = peek a x := fun x hx => (A.keep x hx).trans (hlag x hx)
  have eA := kp _ (keepA_mem (x := sy.A_B_Buttons) (by simp))
  have eP := kp _ (keepA_mem (x := sy.PreviousA_B_Buttons) (by simp))
  refine ⟨fun x hx => kp x (keepA_mem (Or.inr (Or.inl hx))), by rw [eA], ?_⟩
  rw [eA, eP]
  exact hprev

end Real

/-- round 30: **the frame's end** `b` (round 32: the place byte only, a condition on the one state `b`): when the frame ends with the side collision's timer at
most 1, the scroll lock 0 and his place on the screen at least the scroll's threshold, his place byte at `b` is his pixel minus the left edge modulo 256 (the
drawing writes it). Rounds 30 and 31 also asked here that his pixel at `b` is that of the scroll handler's return instruction on a frame that calls the push or
the clamp; round 32: that is a theorem whenever the timer at `b` is at most 1 (`PushTimer.pix_end`, with the field `sideW`; round 37: the theorem `OnFrames.sideWAt`). That the left edge at `b` is that
of the return instruction is a theorem too (the walk of `EdgeStep.keep_r`). -/
def EndKeep (sy : Syms) (m0 : Machine) (b : Machine) : Prop :=
  b.ram.get! (ScrollRule.places sy m0).sideB ≤ 1 → b.ram.get! (ScrollRule.places sy m0).lockB = 0 →
    (ScrollRule.places sy m0).thr1 ≤ b.ram.get! (ScrollRule.places sy m0).pfs →
    (b.ram.get! (ScrollRule.places sy m0).pfs).toNat =
      (ClampSide.pix16 (ClampSide.places sy m0) b + 65536 - ClampSide.edge16 (ClampSide.places sy m0) 0 b) % 256

/-- round 30: **the right edge's relation** at a machine: the right edge is the left edge plus 255 px (modulo 2¹⁶), and the left edge's page is not 255 -/
def RightRel (P : ClampSide.Places) (R : Machine) : Prop :=
  ClampSide.edge16 P 1 R % 65536 = (ClampSide.edge16 P 0 R + 255) % 65536 ∧ R.ram.get! (ClampSide.eP P 0) ≠ 255

/-- the two bytes of a 16-bit number, put together again -/
theorem bytes16_eq (v : UInt16) : v.toUInt8.toUInt16 ||| ((v >>> 8).toUInt8.toUInt16 <<< 8) = v := by
  apply UInt16.toNat_inj.1
  have hv := v.toNat_lt
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  have h8 : (8 : UInt16).toNat % 16 = 8 := rfl
  rw [h8]
  have hb : v.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have hs : (v.toNat >>> 8 % 2 ^ 8) <<< 8 % 2 ^ 16 = (v.toNat >>> 8 % 2 ^ 8) <<< 8 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  rw [hs, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- round 30: **the scroll handler's return**: from its return instruction (`ClampSide.places.ret`, an `RTS` by `ScreenClamp.check`) with the call's return address
on the stack, one step goes to the instruction after the call (`PlayerSubs + 3`) and keeps the RAM -/
theorem ret_step (hcC : ScreenClamp.check sy m0 = true) {R : Machine} (hg : FrameModel.Good (FrameModel.Rom.of m0) R)
    (hpc : R.pc = (ClampSide.places sy m0).ret) (hlo : R.ram.get! (FrameModel.stkI (R.s + 1)) = (sy.PlayerSubs + 2).toUInt8)
    (hhi : R.ram.get! (FrameModel.stkI (R.s + 1 + 1)) = ((sy.PlayerSubs + 2) >>> 8).toUInt8) :
    FrameModel.Good (FrameModel.Rom.of m0) (FrameModel.stepN 1 R) ∧ (FrameModel.stepN 1 R).pc = sy.PlayerSubs + 3 ∧
      (FrameModel.stepN 1 R).ram = R.ram ∧ FrameModel.InFrameN (FrameModel.Rom.of m0) R 1 := by
  have F := ScreenClamp.facts_of_check hcC
  have hr1 : 0x8000 ≤ R.pc := by rw [hpc]; exact F.ret.1
  have hr2 : FrameModel.lookupOp ((FrameModel.Rom.of m0).b R.pc) FrameModel.insList = some .rts := by rw [hpc]; exact F.ret.2.1
  have hr3 : FrameModel.idleAt (FrameModel.Rom.of m0) R.pc = false := by rw [hpc]; exact F.ret.2.2
  obtain ⟨rp, _, rm, rg⟩ := FrameModel.step_rts hg hr1 hr2 hr3
  rw [← FrameModel.stepN_one] at rp rm rg
  refine ⟨rg, ?_, rm, fun j hj => ?_⟩
  · rw [rp, hlo, hhi, bytes16_eq, UInt16.add_assoc]
    rfl
  · have e : j = 0 := by omega
    subst e
    exact FrameModel.inFrame_rts hg hr1 hr2 hr3

/-- equal positions have the same pixel and page -/
theorem pix16_of_posP {a b : Machine} (h : posP sy a = posP sy b) :
    ClampSide.pix16 (ClampSide.places sy m0) a = ClampSide.pix16 (ClampSide.places sy m0) b := by
  have e1 : ClampSide.pix16 (ClampSide.places sy m0) a = (peek a sy.Player_PageLoc).toNat * 256 + (peek a sy.Player_X_Position).toNat := rfl
  have e2 : ClampSide.pix16 (ClampSide.places sy m0) b = (peek b sy.Player_PageLoc).toNat * 256 + (peek b sy.Player_X_Position).toNat := rfl
  rw [e1, e2]
  rw [FrameModel.posP_eq, FrameModel.posP_eq] at h
  unfold FrameModel.posOf at h
  have := (peek a sy.SprObject_X_MoveForce).toNat_lt; have := (peek b sy.SprObject_X_MoveForce).toNat_lt
  have := (peek a sy.Player_X_Position).toNat_lt; have := (peek b sy.Player_X_Position).toNat_lt
  omega

/-- round 30: `EndKeep` and the clamp's result (`ClampSide.left_after`: at `Rt` his pixel is at most 255 px right of the left edge `e0`, modulo 2¹⁶, and not left of
it) give `SideTimer.NearM` at the frame's end, when the left edge's page is not 255, the scroll's threshold is at least 2 px and his pixel at `b` is that at `Rt`
when the frame ends with the side collision's timer at most 1, the scroll lock 0 and his place on the screen at least the scroll's threshold (`hpix`, round 32:
`PushTimer.pix_end`) -/
theorem nearM_of_end {Rt b : Machine} {e0 : Nat} (hE : EndKeep sy m0 b)
    (hpix : b.ram.get! (ScrollRule.places sy m0).sideB ≤ 1 → b.ram.get! (ScrollRule.places sy m0).lockB = 0 →
      (ScrollRule.places sy m0).thr1 ≤ b.ram.get! (ScrollRule.places sy m0).pfs →
      ClampSide.pix16 (ClampSide.places sy m0) b = ClampSide.pix16 (ClampSide.places sy m0) Rt)
    (hL : (ClampSide.pix16 (ClampSide.places sy m0) Rt + 65536 - e0) % 65536 < 256) (he : ClampSide.edge16 (ClampSide.places sy m0) 0 Rt = e0)
    (p2 : ClampSide.edge16 (ClampSide.places sy m0) 0 b = ClampSide.edge16 (ClampSide.places sy m0) 0 Rt)
    (hlt : e0 < 65280) (ht : 2 ≤ (ScrollRule.places sy m0).thr1) : SideTimer.NearM sy (ScrollRule.places sy m0) b := by
  intro h1 h2 h3
  have p3 := hE h1 h2 h3
  have p1 := hpix h1 h2 h3
  have t1 : (2 : UInt8).toNat ≤ ((ScrollRule.places sy m0).thr1).toNat := UInt8.le_iff_toNat_le.1 ht
  have t2 : ((ScrollRule.places sy m0).thr1).toNat ≤ (b.ram.get! (ScrollRule.places sy m0).pfs).toNat := UInt8.le_iff_toNat_le.1 h3
  have t0 : (2 : UInt8).toNat = 2 := rfl
  have eL : ScrollRule.left16 (ScrollRule.places sy m0) b = ClampSide.edge16 (ClampSide.places sy m0) 0 b := by
    unfold ScrollRule.left16 ClampSide.edge16
    rw [ClampSide.eX_zero, ClampSide.eP_zero]
    rfl
  have eP : EdgeStep.pixel16 sy b = ClampSide.pix16 (ClampSide.places sy m0) b := rfl
  rw [eL, eP]
  have := ClampSide.pix16_lt (ClampSide.places sy m0) b
  have := ClampSide.pix16_lt (ClampSide.places sy m0) Rt
  omega

/-- **What the run assumes of its frames above ground, frame by frame.** The frames are those of `K` (`FrameKeep.Frames`, the field `keep` of `PoleJoin.Run`): `K.fm j`,
`K.pad j` are where the counted frame `j` begins on the real machine, the machine (`seq (j − 1)`, or later by `lag` frames) and the input, and `K.ends` says that it ends at
`seq j`. `CtrlKeep.arrAt` is the instruction at which it first comes to the player's routine: it does so, since it ends with the game not paused (`OnFrames.arrive`): a frame
is counted when it ends not paused (`FrameKeep.Frames`). The frames not counted end paused (`FrameKeep.Frames.down`), so they do not come to the player's routine
(`OnFrames.lagNo`, by the walk of the whole frame `area_endF`), and they keep the bytes the routine needs (`OnFrames.lagKeep`). Every frame keeps the area's type, the
swimming flag and the change of size (`OnFrames.areaAll`).
The frames as `TopSpeed.Frame`s are a definition on these machines (`frOf`), no longer data with a field `reads`: from `state` and `collide` each frame up to the
touch is read from its machines (`OnFrames.reads`), when the touch is not later than `farN` frames after control. The collision bits at each frame's start come from
the walk of `CollKeep` with `FrameKeep.Frames.cleanE` (`OnFrames.collAll`; the field `spareC` is gone). The speed at the end of a frame is that of the scroll handler,
or 0, by the walk of `CollideKeep` with `cleanE` too (`OnFrames.collideAt`; the field `spareV` is gone). The facing and the subspeed at the end of a frame are
those of the scroll handler, or the frame ends with the speed 0 and the subspeed 0, by the walks of `FaceKeep` (`FaceKeep.keepZ_end`); so `collide` asks the subspeed
only on a frame that ends so (`CollideS`), and the facing is asked only on such a frame before `J` (`faceJ`). The collision bits of a frame that moves right at the
scroll handler come from a walk too (`FaceKeep.bits_end`), so `moves` asks the position only (`AfterP`). -/
structure OnFrames (sy : Syms) (m0 : Machine) (B : Box) (T J g : Nat) (seq : Nat → Machine)
    {S : FrameKeep.RealRun} {a : Nat} (K : FrameKeep.Frames sy m0 S a g seq) where
  /-- the values at the end of the frame before, on every frame up to the touch: the player's state is 0, 1 or 2, and no jumpspring (the old `Moves.state`, which was
  asked on the frames from a clean state up to `T`) -/
  state : ∀ j, 1 ≤ j → j ≤ g → CtlState sy (seq (j - 1))
  /-- each counted frame before the touch, from the scroll handler on: the collision routine and the rest of the frame keep the position, take 1 px off it, or push
  him right but not past 1 px right of the base at the end of the frame before (`SurfaceRead.baseOf`: the larger of the position and the screen's left edge; round
  24: it was the frame's start, false on a real frame) when he moves left or not at all; and a frame that ends with the speed 0 and the subspeed 0 has the subspeed
  0 at the scroll handler (`CollideS`). That they keep the speed or set it to 0 is a theorem (the walk of `CollideKeep`), and so is that every other frame keeps the
  subspeed (the walk of `FaceKeep`); with them this is `SurfaceRead.CollideE` (`OnFrames.collideAt`). The position is asked only of a frame that calls the push or
  the clamp after the scroll handler (`Calls`) and does not keep a speed to the right: on the other frames it is a theorem (`OnFrames.stillAt`, `OnFrames.keepAt`). -/
  collide : ∀ j, 1 ≤ j → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    CollideS sy (seq (j - 1)) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (seq j) (Calls sy m0 (K.fm j) (K.pad j) k)
  /-- round 30: at the end of each counted frame before the last one before the touch, `EndKeep` (round 32: a condition on that one state): when the frame ends
  with the side collision's timer at most 1, the scroll lock 0 and his place on the screen at least the scroll's threshold, his place byte is his pixel minus the
  left edge modulo 256. Rounds 30 and 31 also asked that his pixel is that of the scroll handler's return instruction (`ClampSide.places.ret`) on a frame that
  calls the push or the clamp; round 32: that is a theorem whenever the timer is at most 1 (`PushTimer.pix_end`, with the field `posW` and `OnFrames.sideWAt`, round 37's theorem in place of the old field `sideW`). The left edge
  at the frame's end is that of the return instruction (the walk of `EdgeStep.keep_r`). With the right edge's relation (`OnFrames.relAll`,
  `RightEdge.scroll_rel`), the left edge's page (`OnFrames.pageAll`) and `ClampSide.left_after` this gives `SideTimer.NearM` at the frame's end
  (`OnFrames.nearStepAt`, the old field `nearStep`, now without `NearM` at the frame's start). At control `NearM` holds (`AreaRun.near₀`), and the frames not
  counted keep its bytes (`OnFrames.nearLag`), so every counted frame before the touch starts with `NearM` (`OnFrames.nearMAll`). Up to the player's routine the
  timer falls by one at most (`SideTimer.side_at`) and the frame keeps the other bytes (`SideTimer.keep_at`), so this gives `MoveScroll.NearA` there
  (`OnFrames.nearAAt`). The walks of `PlaceKeep.keep_place` carry the three bytes and the edge to the scroll handler, and there his pixel is that of the arrival
  plus the byte the move stores (`MoveScroll.move_xs`), so this gives the old field `near` (`EdgeStep.NearX` at the scroll handler: `OnFrames.nearAt`). With the
  walks of `EdgeStep`, the scroll's rule and `collide` this gives the old field `edge` of round 24 (`OnFrames.edgeAt`). -/
  endKeep : ∀ j, 1 ≤ j → j + 1 < g → EndKeep sy m0 (seq j)
  /-- round 36 (in place of the old field `sideW` at the castle's loop of rows, on the frames where `sideW` asked it): each counted frame before the touch that does
  not end with the side collision's timer at the push's value, from the scroll handler on: at the head of the castle's loop of rows the row is at most 10
  (`SideAcross.CastleRow`). The loop stores the rows from there up to 10; a start row of 11 or more would run it over the whole page (and reach the timer).
  The old field `sideW` (rounds 32 to 36: a store through an index or a pointer after the scroll handler does not write the side collision's timer,
  `PushTimer.SideW`, at the stores that may reach it) is gone in round 37: it was asked only on a frame without `SideAcross.FactsAt`, and every frame of the
  route has it (`AreaRun.facts`, from part f's fields: `SideAcross.Run.factsK`); the theorem is `OnFrames.sideWAt` -/
  castleRow : ∀ j, 1 ≤ j → j < g → (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 →
    ∀ k n, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → k ≤ n → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    (PipeEntryRule.trace (K.fm j) (K.pad j) n).frame = (K.fm j).frame → SideAcross.CastleRow sy (PipeEntryRule.trace (K.fm j) (K.pad j) n)
  /-- each counted frame before the touch, from the scroll handler to its end, at each instruction: a store of a byte of the position by its address is inside the
  push or the clamp at the screen's edge, and outside them a store through an index or a pointer writes no byte of the position (`PositionKeep.PosW`). With
  `clampR` this gives the position on a frame that keeps a speed to the right (`PositionKeep.keep_frame`: the field `AfterP.keep` and a part of `collide`) -/
  posW : ∀ j, 1 ≤ j → j < g → ∀ k n, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → k ≤ n → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    (PipeEntryRule.trace (K.fm j) (K.pad j) n).frame = (K.fm j).frame → PositionKeep.PosW sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n)
  /-- each counted frame before the touch that moves right at the scroll handler and ends with the speed there, from the scroll handler to its end: at the clamp's
  entry, when he moves right there, the clamp's target is his position (`PositionKeep.ClampR`). Round 23: asked only on these frames, where `keep_frame` uses it -/
  clampR : ∀ j, 1 ≤ j → j < g → ∀ k n, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → k ≤ n → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    0 < sbyte (peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_X_Speed) →
    peek (seq j) sy.Player_X_Speed = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_X_Speed →
    (PipeEntryRule.trace (K.fm j) (K.pad j) n).frame = (K.fm j).frame → PositionKeep.ClampR sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n)
  /-- a frame from a clean state: the parts outside the movement -/
  moves : ∀ j, 1 ≤ j → j ≤ T → j < g → Clean sy (seq (j - 1)) → Moves sy m0 (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))
  /-- the frames before `J`, from the scroll handler on: the rest of the frame leaves the bytes of `vHard` as they are there (the height, its fraction, the vertical speed,
  the fraction counter, the state); he does not land on these frames. Three other bytes of `vKeep` and A are a theorem (`OnFrames.kAt`), and so is the vertical force
  (`OnFrames.vfAt`). -/
  vAfter : ∀ j, 1 ≤ j → j < J → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    ∀ x ∈ vHard sy, peek (seq j) x = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) x
  /-- the frames before `J` that end with the speed 0 and the subspeed 0 have the facing of the scroll handler at their end. On every other frame the facing is
  that of the scroll handler by a walk (`FaceKeep.keepZ_end`); here he stands still, and a walk does not know whether a climbing tile turned him. This is what is left
  of the old `AfterR.fd`, which asked the facing on every frame from a clean state up to `T`. -/
  faceJ : ∀ j, 1 ≤ j → j < J → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    peek (seq j) sy.Player_X_Speed = 0 → peek (seq j) sy.Player_X_MoveForce = 0 →
    peek (seq j) sy.PlayerFacingDir = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.PlayerFacingDir
  /-- the frames before `J` run the collision routine as on the machine at control, from the scroll handler on -/
  box : ∀ j, 1 ≤ j → j < J → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    BoxRun sy m0 B (seq (j - 1)) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (seq j)

/-- **The area's type, the swimming flag and the change of size on the frames of `K`**: `v` is one of 1, 2, 3, and every frame before the touch's frame starts with the
area's type `v`, the swimming flag 0 and the change of size 0 (a theorem: `OnFrames.areaAll`). `after` is the check of the walk of the whole frame (`CtrlKeep.area_end`). -/
structure AreaRun (sy : Syms) (m0 : Machine) {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq) (v : UInt8) : Prop where
  after : CtrlKeep.afterCheck sy m0 v = true
  v3 : v ∈ [(1 : UInt8), 2, 3]
  all : ∀ n, n < K.ix g → CtrlKeep.AreaOK sy v (K.all n)
  /-- the check of the walks from the scroll handler to the frame's end (`AfterKeep.keepH`) -/
  keep : AfterKeep.hCheck sy m0 v = true
  /-- every frame up to the touch's frame starts with the collision bits under the mask `FC` (a theorem: `OnFrames.collAll`) -/
  bits : ∀ n, n < K.ix g → CollKeep.CollOK sy (K.all n)
  /-- the bytes under the mask `FC` are the four values of `TopSpeed.collBits` -/
  cb : CollKeep.collBitsOK sy = true
  /-- the check of the walk of the speed from the scroll handler to the frame's end (`CollideKeep.speed_end`) -/
  vkeep : CollideKeep.vCheck sy m0 v = true
  /-- the check of the walks of four vertical bytes from the scroll handler to the frame's end (`VertKeep.keep_end`) -/
  kv : VertKeep.kCheck sy m0 v = true
  /-- the check of the walks of the facing and of the subspeed from the scroll handler to the frame's end (`FaceKeep.keepZ_end`) -/
  zk : FaceKeep.zCheck sy m0 v = true
  /-- the check of the walks of the collision bits on a frame that moves right at the scroll handler (`FaceKeep.bits_end`) -/
  bk : FaceKeep.bCheck sy m0 v = true
  /-- the check of the walk of the vertical force from the scroll handler to the frame's end (`FaceKeep.vf_end`), with the value `FaceKeep.vfC` -/
  vfk : FaceKeep.vfCheck sy m0 v (FaceKeep.vfC sy m0 v) = true
  /-- the checks of `PositionKeep.keep_frame`: the walk of the position's writers from the scroll handler to the frame's end, the push, the clamp -/
  pk : PositionKeep.pCheck sy m0 v = true
  /-- at control the screen's left edge is behind him (a theorem: `edge_zero`; the old field `edge₀` of `OnFrames`, round 25) -/
  edge₀ : 0 < g → SurfaceRead.edgeOf sy (seq 0) ≤ posP sy (seq 0)
  /-- round 26: the checks of the walks of the edge's two bytes (`EdgeStep.keep_q`, `EdgeStep.keep_noCut`, `EdgeStep.keep_r`) and of the scroll's rule -/
  eq : EdgeStep.qCheck sy m0 v = true
  er : EdgeStep.rCheck sy m0 v = true
  sr : ScrollRule.check sy m0 = true
  /-- round 27: at control the platforms' force on the scroll is 0 (a theorem: `Start` and `numbersCheck`), and it is the byte that the scroll handler adds -/
  plat₀ : (seq 0).ram.get! (EdgeStep.platI sy) = 0
  platP : (ScrollRule.places sy m0).plat = EdgeStep.platI sy
  /-- round 28: the checks of the walks of `PlaceKeep.keep_place` and of the byte the move stores (`MoveScroll.move_xs`) -/
  pl : PlaceKeep.placeCheck sy m0 v = true
  xs : MoveScroll.xsCheck sy m0 = true
  /-- round 29: the checks of the walks from the frame's start to the player's routine of the side collision's timer (`SideTimer.side_at`) and of the place byte,
  the scroll lock and the edge's two bytes (`SideTimer.keep_at`) -/
  side : SideTimer.sideCheck sy m0 = true
  keepS : SideTimer.keepCheck sy m0 = true
  /-- round 29: at control `SideTimer.NearM` holds (a theorem: `near_zero`): he is at least 2 px right of the screen's left edge there -/
  near₀ : 0 < g → SideTimer.NearM sy (ScrollRule.places sy m0) (seq 0)
  /-- round 30: the pieces of the clamp's choice (`ClampSide.left_after`) and the scroll's first threshold at least 2 px -/
  clampS : ClampSide.checkAll sy m0 = true
  thr2 : 2 ≤ (ScrollRule.places sy m0).thr1
  /-- round 31: the pieces of the scroll handler that follow the right edge (`RightEdge.scroll_rel`), and at control the right edge is the left edge plus 255 px
  modulo 2¹⁶ (a theorem: `rel_zero`) -/
  rc : RightEdge.check sy m0 = true
  rel₀ : 0 < g → RightEdge.Rel (ClampSide.places sy m0) (seq 0)
  /-- round 31: in the first `farN` frames from control the base stays below the page 255 of the screen's left edge (`numbersCheck`, with the position of control) -/
  pageB : 0 < g → posP sy (seq 0) + 16 * (top sy : Int) * (farN sy (seq 0) : Int) < 65280 * 256
  /-- round 32: the walks of his pixel and his page after the scroll handler's call (`PushTimer.pix_end`; round 33: and his speed) -/
  pt : PushTimer.sCheck sy m0 v = true
  /-- round 36: the walks of `SideAcross.near_sideA` and of the two bytes up to the scroll handler's call -/
  ac : SideAcross.check sy m0 v = true
  /-- round 37: every frame up to the touch's frame meets `SideAcross.FactsAt` (it starts with the block buffer's column below 32 and the block objects' offset 0 or
  1, and no store of it through an index or a pointer writes them). A theorem on the route from part f's fields (`SideAcross.Run.factsK`); with it the old field
  `OnFrames.sideW` is gone (`OnFrames.sideWAt`) -/
  facts : ∀ n, n < K.ix g → SideAcross.FactsAt sy (K.all n) (K.inp n)

/-- **`CtrlKeep.area_end` on the frames of a run**: a frame in control keeps the area's type, the swimming flag and the change of size, and if it comes to the player's
routine it ends not paused. The condition on each instruction is `CleanK` of `FrameKeep.guardF` (the field `cleanF` of `FrameKeep.Frames`): it holds `CtrlKeep.Spare`
but at the player's own store of the fraction, where the walk after the cut does not ask it. The proof is that of `CtrlKeep.area_end`. -/
theorem area_endF (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (ha : CtrlKeep.afterCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace m i n)) (hv : CtrlKeep.AreaOK sy v m) :
    CtrlKeep.AreaOK sy v (PipeTransition.frame m i) ∧
      ((∃ k, (PipeEntryRule.trace m i k).frame = m.frame ∧ (PipeEntryRule.trace m i k).pc = sy.PlayerCtrlRoutine) → CtrlKeep.Unpaused sy m0 (PipeTransition.frame m i)) := by
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hclA : ∀ j, FrameKeep.CleanK (CtrlKeep.guardP sy m0 (CtrlKeep.spareI sy m0)) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace m i j) := hcl
  obtain ⟨ha1, ha2⟩ := CtrlKeep.afterCheck_parts ha
  generalize CtrlKeep.cutTable sy m0 true = q at ha1 ha2
  rcases CtrlKeep.cut_or_end2 (C := CtrlKeep.cfgPA sy m0 v q (CtrlKeep.afterOf sy m0 v q)) ha1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hw : FrameKeep.walkK (CtrlKeep.afterOf sy m0 v q) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (PipeEntryRule.trace m i k) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (PipeEntryRule.trace m i k).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (PipeEntryRule.trace m i k).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (PipeEntryRule.trace m i k).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    obtain ⟨B', hB', hs'⟩ := CtrlKeep.after_end (CA := CtrlKeep.afterOf sy m0 v q) (F := (m.frame, 2)) ha2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclA
    have hW := FrameKeep.watched_of hB' hs'
    have e1 := hW _ (List.mem_append_left _ (List.mem_singleton.2 rfl))
    have e2 := hW _ (List.mem_append_right _ (List.mem_cons_self (a := ((sy.AreaType &&& 0x7FF).toNat, (0xFF : UInt8), v))))
    have e3 := hW _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self (a := ((sy.SwimmingFlag &&& 0x7FF).toNat, (0xFF : UInt8), (0 : UInt8))))))
    have e4 := hW _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))))
    simp only [FrameKeep.and_ff] at e2 e3 e4
    refine ⟨⟨e2, e3, e4⟩, fun _ => ?_⟩
    have e1' : (PipeTransition.frame m i).ram.get! (CtrlKeep.pauseI sy m0) &&& 1 = (0 : UInt8) &&& 1 := e1
    exact e1'.trans rfl
  · refine ⟨⟨?_, ?_, ?_⟩, fun ⟨k, hk1, hk2⟩ => absurd hk2 (hno k hk1)⟩
    · rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
      exact hv.1
    · rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
      exact hv.2.1
    · rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
      exact hv.2.2

/-- **A frame in control that ends paused does not come to the player's routine**, under the conditions of `area_endF` (`CtrlKeep.noCut_of_paused`) -/
theorem noCut_of_pausedF (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (ha : CtrlKeep.afterCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace m i n)) (hv : CtrlKeep.AreaOK sy v m)
    (hp : ¬ CtrlKeep.Unpaused sy m0 (PipeTransition.frame m i)) :
    ∀ k, (PipeEntryRule.trace m i k).frame = m.frame → (PipeEntryRule.trace m i k).pc ≠ sy.PlayerCtrlRoutine :=
  fun k h1 h2 => hp ((area_endF hc ha h0 hcl hv).2 ⟨k, h1, h2⟩)

section Frames
variable {B : Box} {T J g : Nat} {seq : Nat → Machine} {Sr : FrameKeep.RealRun} {ar : Nat} {K : FrameKeep.Frames sy m0 Sr ar g seq}

/-- the machine when the counted frame `j` begins: that of `K` -/
abbrev OnFrames.fm (_ : OnFrames sy m0 B T J g seq K) : Nat → Machine := K.fm

/-- the input of the counted frame `j`: that of `K` -/
abbrev OnFrames.pad (_ : OnFrames sy m0 B T J g seq K) : Nat → UInt8 := K.pad

/-- the frame ends at `seq j`: the field `ends` of before, now `K.ends` -/
theorem OnFrames.ends (O : OnFrames sy m0 B T J g seq K) : ∀ j, 1 ≤ j → j ≤ T → j < g → seq j = PipeTransition.frame (O.fm j) (O.pad j) :=
  fun j h1 _ h3 => K.ends j h1 (by omega)

/-- the instruction at which the counted frame `j` first comes to the player's routine: `CtrlKeep.arrAt` (a field before, now a definition) -/
abbrev OnFrames.arr (_ : OnFrames sy m0 B T J g seq K) (j : Nat) : Nat := CtrlKeep.arrAt sy (K.fm j) (K.pad j)

/-- the input of the counted frame `j`, as its player's routine reads it -/
def OnFrames.inp (O : OnFrames sy m0 B T J g seq K) (j : Nat) : HIn :=
  inAt sy (O.fm j) (O.pad j) (O.arr j)

/-- the counted frame `j` begins in the idle loop in control: from `hst`, on every frame of `K` -/
theorem start_fm (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : FrameKeep.StartK sy m0 (K.fm j) := by
  have a := K.ix_mono j g h3 (Nat.le_refl g)
  have b := K.one_le_ix h1 h3
  exact hst _ (by omega)

/-- **The counted frame `j` comes to the player's routine at `arr j`, the first time, before its end**: it ends with the game not paused (`FrameKeep.Frames.up`: the
counted frames are the frames that end not paused), and the walk of `CtrlKeep` shows that a frame in control that does not come to the routine ends paused
(`CtrlKeep.arrive_at`). -/
theorem OnFrames.arrive (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : Arrive sy (O.fm j) (O.pad j) (O.arr j) := by
  have hu : CtrlKeep.Unpaused sy m0 (seq j) := K.up h1 (by omega)
  rw [K.ends j h1 (by omega)] at hu
  exact CtrlKeep.arrive_at hck (start_fm hst h1 (by omega)) (K.cleanAt j h1 (by omega)) hu

/-- **Every frame before the touch's frame starts with the area's type `v`, the swimming flag 0 and the change of size 0**, counted or not, from the machine at control:
each frame keeps them
(`area_endF`: up to the player's routine the walks of `ctrlCheck`, from there the walk after the cut, with `FrameKeep.Frames.cleanF`). -/
theorem OnFrames.areaAll (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (ha : CtrlKeep.afterCheck sy m0 v = true) (O : OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (h0 : CtrlKeep.AreaOK sy v (seq 0)) : ∀ n, n < K.ix g → CtrlKeep.AreaOK sy v (K.all n) := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : K.all 0 = seq 0 := K.seq0.symm
    rw [e]
    exact h0
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    rw [K.next n]
    exact (area_endF hck ha (hst n (by omega)) (K.cleanF n (by show n < K.ix g; omega)) h1).1

/-- **A frame not counted does not come to the player's routine** (the field `lagNo` of before): it ends paused (`FrameKeep.Frames.down`), and by the walk of the whole
frame a frame that comes to the routine ends not paused (`noCut_of_pausedF`). -/
theorem OnFrames.lagNo (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (Ar : AreaRun sy m0 K v) (O : OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) :
    ∀ j, 1 ≤ j → j ≤ g → ∀ n, K.ix (j - 1) ≤ n → n + 1 < K.ix j →
      ∀ k, (PipeEntryRule.trace (K.all n) (K.inp n) k).frame = (K.all n).frame → (PipeEntryRule.trace (K.all n) (K.inp n) k).pc ≠ sy.PlayerCtrlRoutine := by
  intro j h1 h3 n hn1 hn2
  have hg := K.ix_mono j g (by omega) (Nat.le_refl g)
  have hp := K.down h1 (by omega) hn1 hn2
  rw [K.next n] at hp
  exact noCut_of_pausedF hck Ar.after (hst n (by omega)) (K.cleanF n (by show n < K.ix g; omega)) (Ar.all n (by omega)) hp

/-- **Every frame before the touch's frame starts with bit 7 of A and B of the frame before equal to that of A and B**, counted or not, from the machine at control:
each frame keeps it (`PrevKeep.prev_end`: the walk after the player's routine with the stores to the routine, the mode and the task cut, `FrameKeep.Frames.noStore`;
its condition on each instruction is `FrameKeep.Frames.cleanE`, `GuardE.prev_endE`). -/
theorem OnFrames.prevAll (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : PrevKeep.prevCheck sy m0 v = true) (Ar : AreaRun sy m0 K v)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (h0 : PrevKeep.PrevOK sy (seq 0)) :
    ∀ n, n < K.ix g → PrevKeep.PrevOK sy (K.all n) := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : K.all 0 = seq 0 := K.seq0.symm
    rw [e]
    exact h0
  | succ n ih =>
    intro hn
    rw [K.next n]
    exact GuardE.prev_endE hck hp (hst n (by omega)) (K.cleanE n (by show n < K.ix g; omega)) (K.noStore n hn) (Ar.all n (by omega)) (ih (by omega))

/-- **Every frame up to the touch's frame starts with the collision bits under the mask `FC`**, counted or not, from the machine at control: each frame keeps them
(`CollKeep.coll_end`: the walk after the player's routine with `X` split at `ImpedePlayerMove` and the stores to the routine, the mode and the task cut,
`FrameKeep.Frames.noStore`; its condition on each instruction is `FrameKeep.Frames.cleanE`, which protects the collision bits). It was the field `coll`; the field
`spareC` is gone. -/
theorem OnFrames.collAll (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : CollKeep.collCheck sy m0 v = true) (hA : ∀ n, n < K.ix g → CtrlKeep.AreaOK sy v (K.all n))
    (_O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (h0 : CollKeep.CollOK sy (seq 0)) :
    ∀ n, n < K.ix g → CollKeep.CollOK sy (K.all n) := by
  intro n
  induction n with
  | zero =>
    intro _
    have e : K.all 0 = seq 0 := K.seq0.symm
    rw [e]
    exact h0
  | succ n ih =>
    intro hn
    rw [K.next n]
    exact CollKeep.coll_end hck hp (hst n (by omega)) (K.cleanE n (by show n < K.ix g; omega)) (K.noStore n hn) (hA n (by omega)) (ih (by omega))

theorem collCheckAll_parts {v : UInt8} (h : CollKeep.collCheckAll sy m0 v = true) : CollKeep.collCheck sy m0 v = true ∧ CollKeep.collBitsOK sy = true := by
  unfold CollKeep.collCheckAll at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- **The facts of the area's values and of the collision bits on the frames of `K`**, from the numbers of the machine at control (`Numbers`) and the state of the real
machine there (`Start`): `OnFrames.areaAll` and `OnFrames.collAll` -/
theorem OnFrames.areaRun {J' : Nat} (Nm : Numbers sy m0 B J') (O : OnFrames sy m0 B T J g seq K) (st : Start sy B (seq 0))
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (hF : ∀ n, n < K.ix g → SideAcross.FactsAt sy (K.all n) (K.inp n)) :
    AreaRun sy m0 K (peek B.m sy.AreaType) := by
  have hall := O.areaAll Nm.ctrl Nm.after hst ⟨st.area, st.swim.trans Nm.swim0, st.size.trans Nm.size0⟩
  obtain ⟨hcc, hcb⟩ := collCheckAll_parts Nm.coll
  have h0 : CollKeep.CollOK sy (seq 0) := by
    unfold CollKeep.CollOK
    rw [st.bits, Nm.bits]
    rfl
  have he0 : 0 < g → SurfaceRead.edgeOf sy (seq 0) ≤ posP sy (seq 0) := by
    intro hg
    have h1 := K.order 0 hg
    rw [K.ix0] at h1
    have h2 := K.ix_mono 1 g hg (Nat.le_refl g)
    have hs0 : FrameKeep.StartK sy m0 (K.all 0) := hst 0 (by simp only [Nat.zero_add] at h1; omega)
    have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
    rw [e0] at st ⊢
    exact edge_zero Nm st hs0
  have hp0 : (seq 0).ram.get! (EdgeStep.platI sy) = 0 := st.plat.trans Nm.platB
  have hn0 : 0 < g → SideTimer.NearM sy (ScrollRule.places sy m0) (seq 0) := by
    intro hg
    have h1 := K.order 0 hg
    rw [K.ix0] at h1
    have h2 := K.ix_mono 1 g hg (Nat.le_refl g)
    have hs0 : FrameKeep.StartK sy m0 (K.all 0) := hst 0 (by simp only [Nat.zero_add] at h1; omega)
    have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
    rw [e0] at st ⊢
    exact near_zero Nm st hs0
  exact ⟨Nm.after, Nm.area3, hall, Nm.keepH, O.collAll Nm.ctrl hcc hall hst h0, hcb, Nm.vkeep, Nm.vk, Nm.zk, Nm.bk, Nm.vfk, Nm.pk, he0, Nm.edgeQ, Nm.edgeR, Nm.scroll,
    hp0, Nm.platP, Nm.place, Nm.xs, Nm.side, Nm.keepS, hn0, Nm.clampS, Nm.thr2, Nm.rightC, fun _ => rel_zero Nm st,
    fun _ => by rw [farN_congr st.P, st.P]; exact Nm.pageB, Nm.pushC, Nm.acrossC, hF⟩

/-- **A counted frame before the touch that moves right at the scroll handler and keeps that speed to its end keeps the position from there**
(`PositionKeep.keep_frame` on the frames of `K`, with `posW` and `clampR`): the field `AfterP.keep` and a part of `collide` -/
theorem OnFrames.keepAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      0 < sbyte (peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_X_Speed) →
      peek (PipeTransition.frame (K.fm j) (K.pad j)) sy.Player_X_Speed = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_X_Speed →
      posP sy (PipeTransition.frame (K.fm j) (K.pad j)) = posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  exact PositionKeep.keep_frame hck Ar.pk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
    (fun n hn => (K.cleanAt j h1 (by omega) n).time hn) (O.posW j h1 h3)
    (fun k n hk hkn hpc hpos hsame => O.clampR j h1 h3 k n hk hkn hpc hpos (by rw [K.ends j h1 (by omega)]; exact hsame))

/-- **A counted frame before the touch that makes no call after the scroll handler keeps the position from there** (`PositionKeep.still_frame` on the frames of
`K`, with `posW`): a part of `collide` -/
theorem OnFrames.stillAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      ¬ Calls sy m0 (K.fm j) (K.pad j) k →
      posP sy (PipeTransition.frame (K.fm j) (K.pad j)) = posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  intro k hk hpc hnc
  refine PositionKeep.still_frame hck Ar.pk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
    (fun n hn => (K.cleanAt j h1 (by omega) n).time hn) (O.posW j h1 h3) k hk hpc (fun n hn hf => ⟨fun e => hnc ⟨n, hn, hf, Or.inl e⟩, fun e => hnc ⟨n, hn, hf, Or.inr e⟩⟩)

/-- **What a counted frame before the touch does from the scroll handler on** (`SurfaceRead.CollideE`): the field `collide` (`SurfaceRead.CollideR`), and that the
speed at the frame's end is that of the scroll handler, or 0 (`CollideKeep.speed_end`: the walk from the player's routine, through the first walk of `AfterKeep`, and
from the scroll handler on with the speed followed; its condition on each instruction is `FrameKeep.Frames.cleanE`, which protects the speed (the old field `spareV`),
and it cuts the paths at a store to the
routine, the mode or the task, `FrameKeep.Frames.noStore`); on a frame that keeps a speed to the right, the position from `OnFrames.keepAt`, and on a frame that makes no call, from `OnFrames.stillAt` -/
theorem OnFrames.collideAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      SurfaceRead.CollideE sy (SurfaceRead.baseOf sy (seq (j - 1))) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (PipeTransition.frame (K.fm j) (K.pad j)) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have hsv := CollideKeep.speed_end hck Ar.vkeep (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have hz := FaceKeep.keepZ_end hck Ar.zk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  intro k hk hpc
  have c := O.collide j h1 h3 k hk hpc
  rw [K.ends j h1 (by omega)] at c
  exact (c.toR (hz k hk hpc (CollideKeep.sfI sy) (by simp [FaceKeep.zI])) (O.keepAt hck hst Ar h1 h3 k hk hpc)
    (O.stillAt hck hst Ar h1 h3 k hk hpc)).toE (hsv k hk hpc)

/-- **Four vertical bytes of a counted frame before the touch, from the scroll handler on**: the vertical force down, the jump's origin, the jump's halt value and A and B
at the frame's end are those at the scroll handler (`VertKeep.keep_end`: the walk from the player's routine, through the first walk of `AfterKeep`, and from the scroll
handler on with each byte followed; its condition on each instruction is `FrameKeep.Frames.cleanE`, which protects the four bytes, and it cuts the paths at a store to the
routine, the mode or the task, `FrameKeep.Frames.noStore`). They were a part of the field `vAfter`. -/
theorem OnFrames.kAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      ∀ x ∈ VertKeep.kI sy, (seq j).ram.get! x = (PipeEntryRule.trace (K.fm j) (K.pad j) k).ram.get! x := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have hk := VertKeep.keep_end hck Ar.kv (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  intro k hk' hpc x hx
  rw [K.ends j h1 (by omega)]
  exact hk k hk' hpc x hx

/-- **The vertical force of a counted frame before the touch, from the scroll handler on**: at the frame's end it is that at the scroll handler, or the frame ends on
the ground (the player's state 0) with the vertical force `FaceKeep.vfC` (`FaceKeep.vf_end`: the walk that follows the vertical force, with the player's state
protected; the state 3 at the frame's end is excluded by the field `state`). It was a part of the field `vAfter`. -/
theorem OnFrames.vfAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      peek (seq j) sy.VerticalForce = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.VerticalForce ∨
      (peek (seq j) sy.VerticalForce = FaceKeep.vfC sy m0 v ∧ peek (seq j) sy.Player_State = 0) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have hk := FaceKeep.vf_end hck Ar.vfk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have hs3 : peek (seq j) sy.Player_State ≠ 3 := by
    have hs := (O.state (j + 1) (by omega) (by omega)).st
    rw [show j + 1 - 1 = j by omega] at hs
    intro e
    rw [e] at hs
    exact absurd hs (by decide)
  intro k hk' hpc
  have e : peek (seq j) sy.VerticalForce = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.VerticalForce ∨
      (peek (seq j) sy.VerticalForce = FaceKeep.vfC sy m0 v ∧ (peek (seq j) sy.Player_State = 0 ∨ peek (seq j) sy.Player_State = 3)) := by
    rw [K.ends j h1 (by omega)]
    exact hk k hk' hpc
  rcases e with e | ⟨e1, e2 | e2⟩
  · exact Or.inl e
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd e2 hs3

/-- **The frames not counted before the counted frame `j` keep the bytes of `CtrlKeep.keepA`**: each starts in control and does not come to the player's routine
(`OnFrames.lagNo`), and the walk of `CtrlKeep` shows that such a frame writes none of these bytes (`CtrlKeep.keep_of_noCut`). -/
theorem OnFrames.lagKeep (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : ∀ x ∈ CtrlKeep.keepA sy, peek (O.fm j) x = peek (seq (j - 1)) x := by
  have ho := K.order (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at ho
  have hg := K.ix_mono j g (by omega) (Nat.le_refl g)
  have step : ∀ d, K.ix (j - 1) + d + 1 ≤ K.ix j → ∀ x ∈ CtrlKeep.keepA sy, peek (K.all (K.ix (j - 1) + d)) x = peek (K.all (K.ix (j - 1))) x := by
    intro d
    induction d with
    | zero => exact fun _ _ _ => rfl
    | succ d ih =>
      intro hd x hx
      have hn := K.next (K.ix (j - 1) + d)
      rw [show K.ix (j - 1) + (d + 1) = K.ix (j - 1) + d + 1 by omega, hn]
      rw [CtrlKeep.keep_of_noCut hck (hst _ (by omega)) (K.clean _ (by omega)) (O.lagNo hck Ar hst j h1 h3 _ (by omega) (by omega)) x hx]
      exact ih (by omega) x hx
  intro x hx
  have e := step (K.ix j - 1 - K.ix (j - 1)) (by omega) x hx
  rw [show K.ix (j - 1) + (K.ix j - 1 - K.ix (j - 1)) = K.ix j - 1 by omega] at e
  rw [K.at_ix (j - 1) (by omega)]
  exact e

/-- **The frames not counted before the counted frame `j` keep the edge's two bytes** (round 26): each starts in control and does not come to the player's routine
(`OnFrames.lagNo`), and the walk of `EdgeStep` shows that such a frame writes neither byte (`EdgeStep.keep_noCut`) -/
theorem OnFrames.edgeLag (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : ∀ x ∈ EdgeStep.eI sy m0, (O.fm j).ram.get! x = (seq (j - 1)).ram.get! x := by
  have ho := K.order (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at ho
  have hg := K.ix_mono j g (by omega) (Nat.le_refl g)
  have step : ∀ d, K.ix (j - 1) + d + 1 ≤ K.ix j → ∀ x ∈ EdgeStep.eI sy m0, (K.all (K.ix (j - 1) + d)).ram.get! x = (K.all (K.ix (j - 1))).ram.get! x := by
    intro d
    induction d with
    | zero => exact fun _ _ _ => rfl
    | succ d ih =>
      intro hd x hx
      have hn := K.next (K.ix (j - 1) + d)
      rw [show K.ix (j - 1) + (d + 1) = K.ix (j - 1) + d + 1 by omega, hn]
      rw [EdgeStep.keep_noCut Ar.eq (hst _ (by omega)) (K.clean _ (by omega)) (O.lagNo hck Ar hst j h1 h3 _ (by omega) (by omega)) x hx]
      exact ih (by omega) x hx
  intro x hx
  have e := step (K.ix j - 1 - K.ix (j - 1)) (by omega) x hx
  rw [show K.ix (j - 1) + (K.ix j - 1 - K.ix (j - 1)) = K.ix j - 1 by omega] at e
  rw [K.at_ix (j - 1) (by omega)]
  exact e

/-- **The counted frame `j` at its scroll handler and after it** (round 27: the first part of the old proof of `edgeAt`, now also used by `platEnd`). The frame comes to
the scroll handler at `kq` (the walk of `EdgeStep.keep_r`); there the machine is `Good` and has the bytes of `EdgeStep.eI` of the frame's start (`EdgeStep.keep_q`), which
are those of the end of the frame before (`OnFrames.edgeLag`): the edge's two bytes and the platforms' force on the scroll. The scroll's rule (`EdgeStep.edge_frame`)
gives the instruction `R` after the call, `n` instructions later; from there to the frame's end the bytes of `eI` are kept (`EdgeStep.keep_r`, with `posW`), and at `R`
the platforms' force is 0 (the check of `EdgeStep.rCheck`), so it is 0 at the frame's end. -/
theorem OnFrames.scrollAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∃ kq n, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ kq ∧ (PipeEntryRule.trace (K.fm j) (K.pad j) kq).pc = sy.PlayerSubs ∧
      (∀ j', CtrlKeep.arrAt sy (K.fm j) (K.pad j) < j' → j' < kq → (PipeEntryRule.trace (K.fm j) (K.pad j) j').pc ≠ sy.PlayerSubs) ∧
      SurfaceRead.edgeOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = SurfaceRead.edgeOf sy (seq (j - 1)) ∧
      SurfaceRead.edgeOf sy (seq j) = SurfaceRead.edgeOf sy (FrameModel.stepN n (PipeEntryRule.trace (K.fm j) (K.pad j) kq)) ∧
      (PipeEntryRule.trace (K.fm j) (K.pad j) kq).ram.get! (EdgeStep.platI sy) = (seq (j - 1)).ram.get! (EdgeStep.platI sy) ∧
      (seq j).ram.get! (EdgeStep.platI sy) = 0 ∧
      ∀ M b : Machine, SurfaceRead.edgeOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = SurfaceRead.edgeOf sy M →
        EdgeStep.Near sy (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) →
        posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) kq) - 256 ≤ posP sy b →
        SurfaceRead.edgeOf sy b = SurfaceRead.edgeOf sy (FrameModel.stepN n (PipeEntryRule.trace (K.fm j) (K.pad j) kq)) →
        SurfaceRead.edgeOf sy b ≤ max (SurfaceRead.baseOf sy M) (posP sy b) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hpj : (seq (j - 1)).prg = m0.prg ∧ (seq (j - 1)).prgMask = m0.prgMask := by
    have s := hst (K.ix (j - 1)) (by omega)
    rw [K.at_ix (j - 1) (by omega)]
    exact ⟨s.prg, s.mask⟩
  have hpe : (seq j).prg = m0.prg ∧ (seq j).prgMask = m0.prgMask := by
    have s := hst (K.ix j) (by omega)
    rw [K.at_ix j (by omega)]
    exact ⟨s.prg, s.mask⟩
  have eQ : SurfaceRead.edgeOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = SurfaceRead.edgeOf sy (seq (j - 1)) :=
    EdgeStep.edgeOf_eq hgQ.prg hgQ.mask hpj.1 hpj.2 fun x hx => (HQ x hx).2.trans (O.edgeLag hck hst Ar h1 (by omega) x hx)
  obtain ⟨n, gR, pcR, _, ifr, H⟩ := EdgeStep.edge_frame Ar.sr hgQ hqq
  have hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := by
    have h := Ar.pk
    simp only [PositionKeep.pCheck, Bool.and_eq_true] at h
    exact h.2
  have eq := FrameModel.trace_inFrame hidle hfq ifr (fun n hn => (K.cleanAt j h1 (by omega) n).time hn) n (Nat.le_refl _)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with e | e
    · exfalso
      subst e
      have e2 : (FrameModel.stepN 0 (PipeEntryRule.trace (K.fm j) (K.pad j) kq)).pc = sy.PlayerSubs := hqq
      rw [pcR] at e2
      have e3 := congrArg UInt16.toNat e2
      simp only [UInt16.toNat_add] at e3
      have e4 : (3 : UInt16).toNat = 3 := rfl
      rw [e4] at e3
      have := sy.PlayerSubs.toNat_lt
      omega
    · exact e
  have hp : ∀ n', kq ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 h3 kq n' (Nat.le_of_lt hkq) hn' hqq hf').1
    have hpg := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  have eR := HR hp (kq + n) (by omega) (by rw [eq.1]; exact pcR)
  have e2 : SurfaceRead.edgeOf sy (seq j) = SurfaceRead.edgeOf sy (FrameModel.stepN n (PipeEntryRule.trace (K.fm j) (K.pad j) kq)) := by
    refine EdgeStep.edgeOf_eq hpe.1 hpe.2 gR.prg gR.mask fun x hx => ?_
    rw [K.ends j h1 (by omega), ← eq.1]
    exact eR.1 x hx
  have ep : (seq j).ram.get! (EdgeStep.platI sy) = 0 := by
    rw [K.ends j h1 (by omega)]
    exact (eR.1 _ EdgeStep.platI_mem).trans eR.2
  exact ⟨kq, n, Nat.le_of_lt hkq, hqq, hbq, eQ, e2, (HQ _ EdgeStep.platI_mem).2.trans (O.edgeLag hck hst Ar h1 (by omega) _ EdgeStep.platI_mem), ep, H⟩

/-- **The platforms' force on the scroll is 0 at the end of each counted frame before the touch** (round 27): `OnFrames.scrollAt` -/
theorem OnFrames.platEnd (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) : (seq j).ram.get! (EdgeStep.platI sy) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hp, _⟩ := O.scrollAt hck hst Ar h1 h3
  exact hp

/-- **and at the end of the frame before each counted frame before the touch**: at control it is 0 (`AreaRun.plat₀`), else `OnFrames.platEnd` -/
theorem OnFrames.platPrev (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) : (seq (j - 1)).ram.get! (EdgeStep.platI sy) = 0 := by
  rcases Nat.eq_or_lt_of_le h1 with e | e
  · subst e
    exact Ar.plat₀
  · exact O.platEnd hck hst Ar (j := j - 1) (by omega) (by omega)

/-- **The platforms' force on the scroll is 0 at the scroll handler of each counted frame before the touch** (round 27): the frame comes to the scroll handler at `kq`
with the force of the end of the frame before (`OnFrames.scrollAt`), which is 0 (`OnFrames.platPrev`). So there the scroll's amount `X` is the byte the move stores. -/
theorem OnFrames.platQ (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ∃ kq, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ kq ∧ (PipeEntryRule.trace (K.fm j) (K.pad j) kq).pc = sy.PlayerSubs ∧
      (PipeEntryRule.trace (K.fm j) (K.pad j) kq).ram.get! (ScrollRule.places sy m0).plat = 0 := by
  obtain ⟨kq, _, hk, hqq, _, _, _, hpq, _, _⟩ := O.scrollAt hck hst Ar h1 h3
  refine ⟨kq, hk, hqq, ?_⟩
  rw [Ar.platP, hpq]
  exact O.platPrev hck hst Ar h1 h3

/-- **round 31: one counted frame keeps the right edge's relation.** The frame comes to the scroll handler `Q` (`EdgeStep.keep_r`, `EdgeStep.keep_q`: a `Good`
machine in the frame with the four bytes of the edges of the frame's start, which are those of the end of the frame before, `OnFrames.edgeLag`); the scroll's part of
the scroll handler keeps the relation (`RightEdge.scroll_rel`: the right edge's routine sets it after a scroll); the clamp keeps both edges (`ClampSide.clamp_end`);
the scroll handler's return keeps the RAM (`ret_step`); and from the instruction after the call to the frame's end the walks of `EdgeStep.keep_r` keep the four bytes
(with `posW`). -/
theorem OnFrames.relStep (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (hr : RightEdge.Rel (ClampSide.places sy m0) (seq (j - 1))) :
    RightEdge.Rel (ClampSide.places sy m0) (seq j) := by
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  have a4 := K.ix_mono (j + 1) g (by omega) (Nat.le_refl g)
  have a5 := K.ix_mono 0 j (by omega) (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hp : ∀ n', kq ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 h3 kq n' (Nat.le_of_lt hkq) hn' hqq hf').1
    have hpg := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  have hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := (PositionKeep.pCheck_parts Ar.pk).2.2.2.2
  have hscc : ScreenClamp.check sy m0 = true := (PositionKeep.pCheck_parts Ar.pk).2.2.1
  have rQ : RightEdge.Rel (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) :=
    rel_congr (fun x hx => (HQ x hx).2.trans (O.edgeLag hck hst Ar h1 (by omega) x hx)) hr
  obtain ⟨k2, g2, pc2, s2, hi2, lo2, _, _, C2, rel2⟩ := RightEdge.scroll_rel Ar.rc hgQ hqq
  have hck2 := K.cleanAt j h1 (by omega)
  have ht : ∀ n, (PipeEntryRule.trace (K.fm j) (K.pad j) n).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hck2 n).time hn
  obtain ⟨k3, g3, pc3, s3, we3, _, up3, _, _, C3⟩ := ClampSide.clamp_end Ar.clampS hscc g2 pc2
  have C23 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3) := FrameModel.InFrameN.add' C2 rfl C3
  have r2 := rel2 rQ
  generalize hQ2 : FrameModel.stepN k2 (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = Q2 at g2 pc2 s2 hi2 lo2 r2 we3 up3 C3 g3 pc3 s3
  generalize hQ3 : FrameModel.stepN k3 Q2 = Q3 at we3 up3 g3 pc3 s3
  have lo3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1)) = (sy.PlayerSubs + 2).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add1]
    exact lo2
  have hi3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1 + 1)) = ((sy.PlayerSubs + 2) >>> 8).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add2]
    exact hi2
  obtain ⟨_, pc4, rm4, C4⟩ := ret_step hscc g3 pc3 lo3 hi3
  have C234 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3 + 1) := by
    refine FrameModel.InFrameN.add' C23 ?_ C4
    rw [FrameModel.stepN_add, hQ2, hQ3]
  have tr4 := FrameModel.trace_inFrame hidle hfq C234 ht (k2 + k3 + 1) (Nat.le_refl _)
  rw [FrameModel.stepN_add, FrameModel.stepN_add, hQ2, hQ3] at tr4
  have eR := HR hp (kq + (k2 + k3 + 1)) (by omega) (by rw [tr4.1]; exact pc4)
  have r3 : RightEdge.Rel (ClampSide.places sy m0) Q3 := by
    unfold RightEdge.Rel ClampSide.edge16 at r2 ⊢
    rw [we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW])]
    exact r2
  refine rel_congr (fun x hx => ?_) r3
  rw [K.ends j h1 (by omega), ← rm4, ← tr4.1]
  exact eR.1 x hx

/-- **round 31: every counted frame before the touch ends with the right edge's relation** (and so does the machine at control: `AreaRun.rel₀`), by
`OnFrames.relStep`. It is the first half of the old field `rightRel`. -/
theorem OnFrames.relAll (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) : ∀ j, j < g → RightEdge.Rel (ClampSide.places sy m0) (seq j) := by
  intro j
  induction j with
  | zero => exact fun h => Ar.rel₀ h
  | succ j ih =>
    intro h3
    exact O.relStep hck hst Ar (j := j + 1) (by omega) h3 (by rw [show j + 1 - 1 = j by omega]; exact ih (by omega))

/-- round 34: **the old field `sideW`** (round 33's form: at every store that may reach the side collision's timer, `PushTimer.NearW`), from the narrowed field
(the stores of `SideRange.Resid`) and the walk of `SideRange.near_side` (the other stores); round 35: from the field at the stores of `SideLoop.Resid`
and the walk of `SideLoop.near_side`; round 36: on a frame with `SideAcross.FactsAt` by the walk of `SideAcross.near_sideA` (with the field `castleRow`);
round 37: every frame has `FactsAt` (`AreaRun.facts`), so the field `sideW` is gone -/
theorem OnFrames.sideWAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (j : Nat) (h1 : 1 ≤ j) (h3 : j < g) (hside : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0) :
    ∀ k n, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → k ≤ n → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).frame = (K.fm j).frame → PushTimer.NearW sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n) →
      PushTimer.SideW sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n) := by
  intro k n hk hkn hpc hfn hn
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  have a4 := K.ix_mono (j + 1) g (by omega) (Nat.le_refl g)
  have a5 := K.ix_mono 0 j (by omega) (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have honce := GuardE.subs_onceE hck Ar.keep h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  have hF : SideAcross.FactsAt sy (K.fm j) (K.pad j) := Ar.facts (K.ix j - 1) (by omega)
  -- the walk of `SideAcross.near_sideA` (with the field `castleRow`) at every store
  obtain ⟨hca, hcb⟩ := SideAcross.check_parts Ar.ac
  obtain ⟨kq', hkq', hqq', _, _, H'⟩ := SideAcross.near_sideA hca hcb h0 hclE hxs hck hAf hF harr.1 harr.2.1 harr.2.2
    (fun k' n' hk' hkn' hpc' hfn' => O.castleRow j h1 h3 hside k' n' hk' hkn' hpc' hfn')
  have hkk' : k = kq' := honce k kq' hk (Nat.le_of_lt hkq') hpc hqq'
  subst hkk'
  exact H' n hkn hfn hn

/-- round 33: **A counted frame that moves right at the scroll handler and ends there with the speed 0 ends at the screen's left edge, when it ends with the side
collision's timer not at the push's value (`PushTimer.pushT`)** (`OnFrames.stopAt`). The frame comes to the scroll handler `Q` once after the arrival (`EdgeStep.keep_r`, `GuardE.subs_onceE`); the
scroll's part keeps his position and his speed up to the routine of the offscreen bits (`RightEdge.scroll_rel`), where the right edge is the left edge plus
255 px (`OnFrames.relAll`); the routine and the clamp bring him to the scroll handler's return instruction with his pixel that of the choice (`ClampSide.pixAfter`),
the edges kept, and his speed kept when nothing is chosen (`ClampSide.clamp_end`); the return keeps the RAM (`ret_step`); and from the instruction after the call
to the frame's end his pixel, his page and his speed are kept (`PushTimer.pix_end`, with the field `posW` and `OnFrames.sideWAt`, round 37's theorem in place of the old field `sideW`), and the left edge too (`EdgeStep.keep_r`).
So with the speed 0 at the end a clamp was chosen. The right clamp leaves him at the right edge minus its amount, and there the choice would not be the right
clamp (`ClampSide.rightAmt`); but his pixel at the end is that of `Q`, so the choice at `Q`'s pixel would be that place: a contradiction. So it is the left
clamp, which leaves him at the left edge. -/
theorem OnFrames.stopRight (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) {k : Nat} (hk : CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k)
    (hpc : (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs) (hv : 0 < vOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) k))
    (hz : peek (seq j) sy.Player_X_Speed = 0) (he : posP sy (seq j) = posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) k))
    (hside : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0) :
    EdgeStep.pixel16 sy (seq j) = ScrollRule.left16 (ScrollRule.places sy m0) (seq j) := by
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  have a4 := K.ix_mono (j + 1) g (by omega) (Nat.le_refl g)
  have a5 := K.ix_mono 0 j (by omega) (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  -- `Q` is the frame's only scroll handler after the arrival
  have honce := GuardE.subs_onceE hck Ar.keep h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  have hkk : k = kq := honce k kq hk (Nat.le_of_lt hkq) hpc hqq
  subst hkk
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hp : ∀ n', k ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 h3 k n' hk hn' hqq hf').1
    have hpg := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  have hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := (PositionKeep.pCheck_parts Ar.pk).2.2.2.2
  have hscc : ScreenClamp.check sy m0 = true := (PositionKeep.pCheck_parts Ar.pk).2.2.1
  -- the scroll's part of the scroll handler, up to the routine of the offscreen bits, with the right edge's relation
  have rQ : RightEdge.Rel (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) :=
    rel_congr (fun x hx => (HQ x hx).2.trans (O.edgeLag hck hst Ar h1 (by omega) x hx)) (O.relAll hck hst Ar (j - 1) (by omega))
  obtain ⟨k2, g2, pc2, s2, hi2, lo2, pw2, sp2, C2, rel2⟩ := RightEdge.scroll_rel Ar.rc hgQ hqq
  have hR1 := rel2 rQ
  -- the routine of the offscreen bits and the clamp
  have hck2 := K.cleanAt j h1 (by omega)
  have ht : ∀ n, (PipeEntryRule.trace (K.fm j) (K.pad j) n).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hck2 n).time hn
  obtain ⟨k3, g3, pc3, s3, we3, _, up3, hp3, hv3, C3⟩ := ClampSide.clamp_end Ar.clampS hscc g2 pc2
  have C23 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (k2 + k3) := FrameModel.InFrameN.add' C2 rfl C3
  have tr3 := FrameModel.trace_inFrame hidle hfq C23 ht (k2 + k3) (Nat.le_refl _)
  rw [FrameModel.stepN_add] at tr3
  generalize hQ2 : FrameModel.stepN k2 (PipeEntryRule.trace (K.fm j) (K.pad j) k) = Q2 at g2 pc2 s2 hi2 lo2 pw2 sp2 hR1 we3 up3 hp3 hv3 C3 tr3 g3 pc3 s3
  generalize hQ3 : FrameModel.stepN k3 Q2 = Q3 at we3 up3 hp3 hv3 tr3 g3 pc3 s3
  have lo3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1)) = (sy.PlayerSubs + 2).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add1]
    exact lo2
  have hi3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1 + 1)) = ((sy.PlayerSubs + 2) >>> 8).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add2]
    exact hi2
  obtain ⟨_, pc4, rm4, C4⟩ := ret_step hscc g3 pc3 lo3 hi3
  have C234 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (k2 + k3 + 1) := by
    refine FrameModel.InFrameN.add' C23 ?_ C4
    rw [FrameModel.stepN_add, hQ2, hQ3]
  have tr4 := FrameModel.trace_inFrame hidle hfq C234 ht (k2 + k3 + 1) (Nat.le_refl _)
  rw [FrameModel.stepN_add, FrameModel.stepN_add, hQ2, hQ3] at tr4
  have pcR : (PipeEntryRule.trace (K.fm j) (K.pad j) (k + (k2 + k3 + 1))).pc = EdgeStep.rPc sy := by rw [tr4.1]; exact pc4
  have eR := HR hp (k + (k2 + k3 + 1)) (by omega) pcR
  -- his pixel, his page and his speed from the instruction after the call to the frame's end (`PushTimer.pix_end`)
  have hoff := (PositionWriters.wCheck_facts (PositionKeep.pCheck_parts Ar.pk).1).2.2
  obtain ⟨kq', hkq'', hqq', _, hbq', HP⟩ := PushTimer.pix_end hck Ar.pt hoff h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  have hkk : kq' = k := by
    rcases Nat.lt_trichotomy kq' k with h | h | h
    · exact absurd hqq' (hbq kq' hkq'' h)
    · exact h
    · exact absurd hqq (hbq' k hkq h)
  rw [hkk] at HP
  have hs' : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 := by
    rw [← K.ends j h1 (by omega)]; exact hside
  have E := HP (fun n' hn' hf' => ⟨O.posW j h1 h3 k n' hk hn' hqq hf', O.sideWAt hck hst Ar j h1 h3 hside k n' hk hn' hqq hf'⟩) (k + (k2 + k3 + 1)) (by omega) pcR hs'
  have ex : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).x =
      (PipeEntryRule.trace (K.fm j) (K.pad j) (k + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).x := E _ PushTimer.pvI_x
  have ep : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).page =
      (PipeEntryRule.trace (K.fm j) (K.pad j) (k + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).page := E _ PushTimer.pvI_page
  have ev : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat =
      (PipeEntryRule.trace (K.fm j) (K.pad j) (k + (k2 + k3 + 1))).ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat := E _ PushTimer.pvI_speed
  rw [tr4.1, rm4, ← K.ends j h1 (by omega)] at ex ep ev
  have eRb : ∀ x ∈ EdgeStep.eI sy m0, (seq j).ram.get! x = Q3.ram.get! x := by
    intro x hx
    rw [K.ends j h1 (by omega), ← rm4, ← tr4.1]
    exact eR.1 x hx
  -- the pixels: at the end, at the return instruction, at the routine of the offscreen bits, at `Q`
  have m1 : (ClampSide.places sy m0).x = (ScrollRule.places sy m0).x := rfl
  have m2 : (ClampSide.places sy m0).page = (ScrollRule.places sy m0).page := rfl
  have pb3 : ClampSide.pix16 (ClampSide.places sy m0) (seq j) = ClampSide.pix16 (ClampSide.places sy m0) Q3 := by
    unfold ClampSide.pix16
    rw [m1, m2, ex, ep]
  have pq2 : ClampSide.pix16 (ClampSide.places sy m0) Q2 = ClampSide.pix16 (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) := by
    unfold ClampSide.pix16
    rw [m1, m2, pw2 _ (by simp [ScrollRule.posW]), pw2 _ (by simp [ScrollRule.posW])]
  have pbq : ClampSide.pix16 (ClampSide.places sy m0) (seq j) = ClampSide.pix16 (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) := pix16_of_posP he
  -- the left edge at the end is that of the routine of the offscreen bits
  have hed : ClampSide.edge16 (ClampSide.places sy m0) 0 (seq j) = ClampSide.edge16 (ClampSide.places sy m0) 0 Q2 := by
    have ex0 : (seq j).ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) := by
      rw [ClampSide.eX_zero]; exact eRb _ hx0
    have ep0 : (seq j).ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) := by
      rw [ClampSide.eP_zero]; exact eRb _ (List.mem_cons_of_mem _ List.mem_cons_self)
    unfold ClampSide.edge16
    rw [ex0, ep0, we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW])]
  have eL : ScrollRule.left16 (ScrollRule.places sy m0) (seq j) = ClampSide.edge16 (ClampSide.places sy m0) 0 (seq j) := by
    unfold ScrollRule.left16 ClampSide.edge16
    rw [ClampSide.eX_zero, ClampSide.eP_zero]
    rfl
  have eP : EdgeStep.pixel16 sy (seq j) = ClampSide.pix16 (ClampSide.places sy m0) (seq j) := rfl
  rw [eP, eL]
  -- the speed at the end (0) is not that of the routine of the offscreen bits (that of `Q`, above 0)
  have hvb : (seq j).ram.get! (ClampSide.places sy m0).speed = Q3.ram.get! (ClampSide.places sy m0).speed := ev
  have hne : (seq j).ram.get! (ClampSide.places sy m0).speed ≠ Q2.ram.get! (ClampSide.places sy m0).speed := by
    intro e0
    have e1 : peek (seq j) sy.Player_X_Speed = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_X_Speed := e0.trans sp2
    unfold vOf at hv
    rw [← e1, hz] at hv
    exact absurd hv (by decide)
  exact StopClamp.stop_clamp Ar.clampS hR1 hp3 hv3 pb3 hvb (pq2.trans pbq.symm) hed hne

/-! ### The frames as `TopSpeed.Frame`s, read from the machines -/

/-- **Frame `j` from control above ground, read from the machines** (it was the data `fr` of `PoleJoin.Run`, tied to the machines by the field `reads`). It starts with
the speed, the subspeed and the position of `seq (j − 1)`, by the definition. A frame before the touch is `SurfaceRead.frameE` of the real frame of `K`: the
`TopSpeed.Frame` of the real frame, which ends at `seq j`, when the frame meets `SurfaceRead.ReadE` (`OnFrames.reads` shows that it does). The touch's frame is
`SurfaceRead.frameH`: the real frame up to the scroll handler. -/
noncomputable def frOf (sy : Syms) (m0 : Machine) {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq) (j : Nat) :
    Frame (top sy) (amax sy m0) true :=
  if j < g then SurfaceRead.frameE sy m0 (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))
  else SurfaceRead.frameH sy m0 (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))

theorem frOf_v (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : (frOf sy m0 K j).v = vOf sy (seq (j - 1)) := by
  unfold frOf
  split
  · exact SurfaceRead.frameE_v _ _ _ _ _
  · exact SurfaceRead.frameH_v _ _ _ _ _

theorem frOf_f (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : (frOf sy m0 K j).f = fOf sy (seq (j - 1)) := by
  unfold frOf
  split
  · exact SurfaceRead.frameE_f _ _ _ _ _
  · exact SurfaceRead.frameH_f _ _ _ _ _

theorem frOf_P (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : (frOf sy m0 K j).P = posP sy (seq (j - 1)) := by
  unfold frOf
  split
  · exact SurfaceRead.frameE_P _ _ _ _ _
  · exact SurfaceRead.frameH_P _ _ _ _ _

theorem frOf_B (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : (frOf sy m0 K j).B = SurfaceRead.baseOf sy (seq (j - 1)) := by
  unfold frOf
  split
  · exact SurfaceRead.frameE_B _ _ _ _ _
  · exact SurfaceRead.frameH_B _ _ _ _ _

/-- **The counted frame `j` up to the scroll handler meets `SurfaceRead.ReadH`**, and its start has the horizontal bytes of `seq (j − 1)`, when the speed at
`seq (j − 1)` is at most the top and the position is away from the ends of its range. The state at the player's routine is the walk of `CtrlKeep` (`ctrl_keep`) with
`state` and `coll` at `seq (j − 1)`, the area's values (`Ar`), and the `lag` frames before it (`OnFrames.lagKeep`); the frame's time is `CleanK` (`K.cleanAt`). -/
theorem OnFrames.readH (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g)
    (hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true) (hfar : SurfaceRead.Far sy (seq (j - 1))) :
    SurfaceRead.ReadH sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) ∧ SurfaceRead.Same sy (seq (j - 1)) (K.fm j) := by
  have harr := O.arrive hck hst h1 h3
  have A := CtrlKeep.ctrl_keep hck (start_fm hst h1 h3) (K.cleanAt j h1 h3) harr.1 harr.2.1 harr.2.2
  have hlag := O.lagKeep hck hst Ar h1 h3
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (PipeEntryRule.trace (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))) x = peek (seq (j - 1)) x :=
    fun x hx => (A.keep x hx).trans (hlag x hx)
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g h3 (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have hA : CtrlKeep.AreaOK sy v (seq (j - 1)) := by
    rw [K.at_ix (j - 1) (by omega)]
    exact Ar.all _ (by omega)
  have hS : SurfaceRead.Same sy (seq (j - 1)) (K.fm j) := fun x hx => hlag x (keepA_mem (Or.inl hx))
  have hc : bitsOf sy (seq (j - 1)) ∈ TopSpeed.collBits sy := by
    rw [K.at_ix (j - 1) (by omega)]
    exact CollKeep.mem_of_collOK Ar.cb (Ar.bits _ (by omega))
  have hs := O.state j h1 h3
  refine ⟨⟨hOK, hfr, ⟨A.good, harr.1, A.s, A.eng, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => A.keep x (keepA_mem (Or.inl hx)),
    ⟨hidle, harr.2.1, fun n hn => (K.cleanAt j h1 h3 n).time hn⟩, ⟨by rw [hS.P]; exact hfar.1, by rw [hS.P]; exact hfar.2⟩⟩, hS⟩
  · rw [kp _ (keepA_mem (by simp)), hA.1]
    exact Ar.v3
  · rw [kp _ (keepA_mem (by simp [vKeep]))]
    exact hs.st
  · rw [kp _ (keepA_mem (by simp))]
    exact hs.spring
  · rw [kp _ (keepA_mem (by simp))]
    exact hA.2.1
  · rw [kp _ (keepA_mem (by simp))]
    exact hA.2.2
  · rw [kp _ (keepA_mem (by simp))]
    exact hc
  · rw [kp _ (keepA_mem (by simp [FrameModel.hBytes]))]
    exact hsp

/-- **A counted frame before the touch meets `SurfaceRead.ReadE`**: `OnFrames.readH` and `collide`, with `seq j` the frame's end (`K.ends`) -/
theorem OnFrames.readE (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g)
    (hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true) (hfar : SurfaceRead.Far sy (seq (j - 1))) :
    SurfaceRead.ReadE sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) (SurfaceRead.baseOf sy (seq (j - 1))) ∧ SurfaceRead.Same sy (seq (j - 1)) (K.fm j) := by
  obtain ⟨hR, hS⟩ := O.readH hck hOK hfr hidle hst Ar h1 (by omega) hsp hfar
  exact ⟨{ toReadH := hR, collide := fun k hk hpc => O.collideAt hck hst Ar h1 h3 k hk hpc }, hS⟩

/-- the speed of a byte between `−top` and `top` -/
theorem inSpeed_of {v : UInt8} (h : -(top sy : Int) ≤ sbyte v ∧ sbyte v ≤ (top sy : Int)) : TopSpeed.inSpeed sy v = true := by
  simp only [TopSpeed.inSpeed, decide_eq_true_eq]
  omega

/-- **The position's range covers the first `farN` frames**: within `(16·top + 256)·d` left and `16·top·d` right of `P₀`, with `d < farN`, the position is at least 8 px
from both ends of its range -/
theorem far_of_range {P0 Pm : Int} {t d : Nat}
    (hd : d < min ((P0 - 2048) / (16 * (t : Int) + 256)).toNat ((0x1000000 - 2049 - P0) / (16 * (t : Int))).toNat)
    (hr : P0 - (16 * (t : Int) + 256) * (d : Int) ≤ Pm ∧ Pm ≤ P0 + 16 * (t : Int) * (d : Int)) : 2048 ≤ Pm ∧ Pm + 2048 < 0x1000000 := by
  have h1 : d + 1 ≤ ((P0 - 2048) / (16 * (t : Int) + 256)).toNat := by omega
  have h2 : d + 1 ≤ ((0x1000000 - 2049 - P0) / (16 * (t : Int))).toNat := by omega
  have hy : (0 : Int) < 16 * (t : Int) + 256 := by omega
  have hz : (0 : Int) < 16 * (t : Int) := by
    rcases Nat.eq_zero_or_pos t with e | e
    · subst e
      simp at h2
    · omega
  have q1 := Int.ediv_mul_le (P0 - 2048) (b := 16 * (t : Int) + 256) (by omega)
  have q2 := Int.ediv_mul_le (0x1000000 - 2049 - P0) (b := 16 * (t : Int)) (by omega)
  generalize (P0 - 2048) / (16 * (t : Int) + 256) = a at h1 q1
  generalize (0x1000000 - 2049 - P0) / (16 * (t : Int)) = b at h2 q2
  generalize hY : 16 * (t : Int) + 256 = Y at hy q1 hr
  generalize hZ : 16 * (t : Int) = Z at hz q2 hr hY
  have ha : (d : Int) + 1 ≤ a := by omega
  have hb : (d : Int) + 1 ≤ b := by omega
  have m1 := Int.mul_le_mul_of_nonneg_right ha (Int.le_of_lt hy)
  have m2 := Int.mul_le_mul_of_nonneg_right hb (Int.le_of_lt hz)
  rw [Int.add_mul, Int.one_mul] at m1 m2
  rw [Int.mul_comm Y] at hr
  rw [Int.mul_comm Z] at hr
  omega

/-- **The frames not counted before the counted frame `j` keep the bytes of `SideTimer.NearM`** (round 29): each starts in control and does not come to the player's
routine (`OnFrames.lagNo`), and the walks of `SideTimer` show that such a frame writes none of the timer, the place byte, the lock and the edge's two bytes
(`SideTimer.side_noCut`, `SideTimer.keep_noCut`) -/
theorem OnFrames.nearLag (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : ∀ x ∈ SideTimer.nearI sy m0, (O.fm j).ram.get! x = (seq (j - 1)).ram.get! x := by
  have ho := K.order (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at ho
  have hg := K.ix_mono j g (by omega) (Nat.le_refl g)
  have step : ∀ d, K.ix (j - 1) + d + 1 ≤ K.ix j → ∀ x ∈ SideTimer.nearI sy m0, (K.all (K.ix (j - 1) + d)).ram.get! x = (K.all (K.ix (j - 1))).ram.get! x := by
    intro d
    induction d with
    | zero => exact fun _ _ _ => rfl
    | succ d ih =>
      intro hd x hx
      have hn := K.next (K.ix (j - 1) + d)
      rw [show K.ix (j - 1) + (d + 1) = K.ix (j - 1) + d + 1 by omega, hn]
      have hno := O.lagNo hck Ar hst j h1 h3 (K.ix (j - 1) + d) (by omega) (by omega)
      have hkx : (PipeTransition.frame (K.all (K.ix (j - 1) + d)) (K.inp (K.ix (j - 1) + d))).ram.get! x = (K.all (K.ix (j - 1) + d)).ram.get! x := by
        simp only [SideTimer.nearI, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact SideTimer.side_noCut Ar.side (hst _ (by omega)) (K.clean _ (by omega)) hno
        · exact SideTimer.keep_noCut Ar.keepS (hst _ (by omega)) (K.clean _ (by omega)) hno x hx
      rw [hkx]
      exact ih (by omega) x hx
  intro x hx
  have e := step (K.ix j - 1 - K.ix (j - 1)) (by omega) x hx
  rw [show K.ix (j - 1) + (K.ix j - 1 - K.ix (j - 1)) = K.ix j - 1 by omega] at e
  rw [K.at_ix (j - 1) (by omega)]
  exact e

/-- round 31: **the left edge's page is not 255** at a machine (the second half of the old field `rightRel`) -/
def PageOK (sy : Syms) (m0 m : Machine) : Prop := m.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) ≠ 255

/-- round 31: **a base below the bound of `AreaRun.pageB` has the left edge's page not 255**: the edge is at most the base, and a page 255 puts the edge at
`65280·256` or more -/
theorem page_of_base {v : UInt8} (Ar : AreaRun sy m0 K v) {m : Machine} (hp : m.prg = m0.prg) (hk : m.prgMask = m0.prgMask) (hg0 : 0 < g) {d : Nat}
    (hd : d ≤ farN sy (seq 0)) (hb : SurfaceRead.baseOf sy m ≤ posP sy (seq 0) + 16 * (top sy : Int) * (d : Int)) : PageOK sy m0 m := by
  have h1 := Ar.pageB hg0
  have ht : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  have hd' : 16 * (top sy : Int) * (d : Int) ≤ 16 * (top sy : Int) * (farN sy (seq 0) : Int) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hd) ht
  have he : SurfaceRead.edgeOf sy m ≤ SurfaceRead.baseOf sy m := Int.le_max_right _ _
  have e : ScreenClamp.places sy m = ScreenClamp.places sy m0 := SurfaceRead.places_congr hp hk
  intro hpg
  unfold SurfaceRead.edgeOf at he
  rw [e] at he
  have q : peek m (ScreenClamp.places sy m0).edgeP = 255 := by
    have i : ClampSide.eP (ClampSide.places sy m0) 0 = ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat := by rw [ClampSide.eP_zero]; rfl
    unfold peek
    rw [← i]
    exact hpg
  rw [q] at he
  have t : (255 : UInt8).toNat = 255 := rfl
  rw [t] at he
  omega

/-- **The old field `nearStep`, a theorem (round 30)**: each counted frame before the last one before the touch ends with `SideTimer.NearM`. The frame comes to the
scroll handler `Q` (`EdgeStep.keep_r`, `EdgeStep.keep_q`: a `Good` machine in the frame); the scroll's part of the scroll handler (round 31: `RightEdge.scroll_rel`;
round 30: `ScrollRule.jsrCheck`, `ScrollRule.scroll_of_facts`) brings it to the routine of the offscreen bits, where the right edge's relation holds (round 31:
`OnFrames.relAll` at the end of the frame before, `OnFrames.edgeLag`, `EdgeStep.keep_q` and `RightEdge.scroll_rel`; round 30: the field `rightRel`) and the left
edge's page is that of the frame's end, not 255 (`OnFrames.pageAll` at the frames before; a premise here); the routine and the clamp (`ClampSide.left_after`) bring it to the scroll handler's return
instruction with his pixel at most 255 px right of the left edge and not left of it, and the edge kept; and from there to the frame's end `EndKeep` holds (the field
`endKeep`). `NearM` at the frame's start is not needed. -/
theorem OnFrames.nearStepAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j + 1 < g) (hpj : PageOK sy m0 (seq j)) :
    SideTimer.NearM sy (ScrollRule.places sy m0) (seq j) := by
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hkq' : CtrlKeep.arrAt sy (K.fm j) (K.pad j) < kq := hkq
  have hp : ∀ n', kq ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 (by omega) kq n' (Nat.le_of_lt hkq) hn' hqq hf').1
    have hpg := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  have hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := (PositionKeep.pCheck_parts Ar.pk).2.2.2.2
  have hscc : ScreenClamp.check sy m0 = true := (PositionKeep.pCheck_parts Ar.pk).2.2.1
  -- the scroll's part of the scroll handler, up to the routine of the offscreen bits, with the right edge's relation (round 31)
  have rQ : RightEdge.Rel (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) :=
    rel_congr (fun x hx => (HQ x hx).2.trans (O.edgeLag hck hst Ar h1 (by omega) x hx)) (O.relAll hck hst Ar (j - 1) (by omega))
  obtain ⟨k2, g2, pc2, s2, hi2, lo2, pw2, sp2, C2, rel2⟩ := RightEdge.scroll_rel Ar.rc hgQ hqq
  have hR1 := rel2 rQ
  -- the routine of the offscreen bits and the clamp
  have hck2 := K.cleanAt j h1 (by omega)
  have ht : ∀ n, (PipeEntryRule.trace (K.fm j) (K.pad j) n).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hck2 n).time hn
  obtain ⟨k3, g3, pc3, s3, we3, _, up3, hp3, _, C3⟩ := ClampSide.clamp_end Ar.clampS hscc g2 pc2
  have hl3 := ClampSide.left_of Ar.clampS hR1 hp3
  have C23 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3) := FrameModel.InFrameN.add' C2 rfl C3
  have tr3 := FrameModel.trace_inFrame hidle hfq C23 ht (k2 + k3) (Nat.le_refl _)
  rw [FrameModel.stepN_add] at tr3
  have hE := O.endKeep j h1 h3
  -- the scroll handler's return, and the left edge from there to the frame's end (`EdgeStep.keep_r`)
  generalize hQ2 : FrameModel.stepN k2 (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = Q2 at g2 pc2 s2 hi2 lo2 pw2 sp2 hR1 we3 up3 hp3 hl3 C3 tr3 g3 pc3 s3
  generalize hQ3 : FrameModel.stepN k3 Q2 = Q3 at we3 up3 hp3 hl3 tr3 g3 pc3 s3
  have lo3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1)) = (sy.PlayerSubs + 2).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add1]
    exact lo2
  have hi3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1 + 1)) = ((sy.PlayerSubs + 2) >>> 8).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add2]
    exact hi2
  obtain ⟨_, pc4, rm4, C4⟩ := ret_step hscc g3 pc3 lo3 hi3
  have C234 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3 + 1) := by
    refine FrameModel.InFrameN.add' C23 ?_ C4
    rw [FrameModel.stepN_add, hQ2, hQ3]
  have tr4 := FrameModel.trace_inFrame hidle hfq C234 ht (k2 + k3 + 1) (Nat.le_refl _)
  rw [FrameModel.stepN_add, FrameModel.stepN_add, hQ2, hQ3] at tr4
  have eR := HR hp (kq + (k2 + k3 + 1)) (by omega) (by rw [tr4.1]; exact pc4)
  have ex : (seq j).ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) := by
    rw [ClampSide.eX_zero, K.ends j h1 (by omega), ← rm4, ← tr4.1]
    exact (eR.1 _ List.mem_cons_self)
  have ep : (seq j).ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) := by
    rw [ClampSide.eP_zero, K.ends j h1 (by omega), ← rm4, ← tr4.1]
    exact (eR.1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hed : ClampSide.edge16 (ClampSide.places sy m0) 0 (seq j) = ClampSide.edge16 (ClampSide.places sy m0) 0 Q3 := by
    unfold ClampSide.edge16
    rw [ex, ep]
  -- the left edge at the return instruction, and its page
  have hw : ClampSide.edge16 (ClampSide.places sy m0) 0 Q3 = ClampSide.edge16 (ClampSide.places sy m0) 0 Q2 := by
    unfold ClampSide.edge16
    rw [we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW])]
  have hlt : ClampSide.edge16 (ClampSide.places sy m0) 0 Q2 < 65280 := by
    have h : Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) ≠ 255 := by
      rw [← we3 _ (by simp [ClampSide.EW]), ← ep]
      exact hpj
    unfold ClampSide.edge16
    have h' := Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) |>.toNat_lt
    have h2 := Q2.ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) |>.toNat_lt
    have h3' : (Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0)).toNat ≠ 255 := by
      intro e
      apply h
      exact UInt8.toNat_inj.1 (by rw [e]; rfl)
    omega
  -- round 32: when the frame ends with the side collision's timer at most 1, the lock 0 and the place byte at least the threshold, his pixel and his page there
  -- are those of the instruction after the scroll handler's call (`PushTimer.pix_end`, with the field `posW` and `OnFrames.sideWAt`, round 37's theorem in place of the old field `sideW`), and so those of the return instruction
  have hpix : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≤ 1 → (seq j).ram.get! (ScrollRule.places sy m0).lockB = 0 →
      (ScrollRule.places sy m0).thr1 ≤ (seq j).ram.get! (ScrollRule.places sy m0).pfs →
      ClampSide.pix16 (ClampSide.places sy m0) (seq j) = ClampSide.pix16 (ClampSide.places sy m0) Q3 := by
    intro hside hlock hthr
    have hoff := (PositionWriters.wCheck_facts (PositionKeep.pCheck_parts Ar.pk).1).2.2
    obtain ⟨kq', hkq'', hqq', _, hbq', HP⟩ := PushTimer.pix_end hck Ar.pt hoff h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
    have hkk : kq' = kq := by
      rcases Nat.lt_trichotomy kq' kq with h | h | h
      · exact absurd hqq' (hbq kq' hkq'' h)
      · exact h
      · exact absurd hqq (hbq' kq hkq h)
    rw [hkk] at HP
    have hs' : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 := by
      rw [← K.ends j h1 (by omega)]; exact PushTimer.pushT_ne Ar.pt hside
    have pcR : (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).pc = EdgeStep.rPc sy := by rw [tr4.1]; exact pc4
    have E := HP (fun n' hn' hf' => ⟨O.posW j h1 (by omega) kq n' (Nat.le_of_lt hkq') hn' hqq hf', O.sideWAt hck hst Ar j h1 (by omega) (PushTimer.pushT_ne Ar.pt hside) kq n' (Nat.le_of_lt hkq') hn' hqq hf'⟩)
      (kq + (k2 + k3 + 1)) (by omega) pcR hs'
    have ex : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).x =
        (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).x := E _ List.mem_cons_self
    have ep : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).page =
        (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).page := E _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [tr4.1, rm4] at ex ep
    have m1 : (ClampSide.places sy m0).x = (ScrollRule.places sy m0).x := rfl
    have m2 : (ClampSide.places sy m0).page = (ScrollRule.places sy m0).page := rfl
    unfold ClampSide.pix16
    rw [m1, m2, K.ends j h1 (by omega), ex, ep]
  exact nearM_of_end hE hpix hl3 hw hed hlt Ar.thr2

/-- round 33: **A counted frame that does not end with the side collision's timer at the push's value ends at or right of the screen's left edge** (`OnFrames.stopAt`), when the
left edge's page there is not 255: as `OnFrames.nearStepAt`, the clamp leaves him at the left edge or at most 255 px right of it (`ClampSide.left_of`), and to the
frame's end his pixel and the edge are kept (`PushTimer.pix_end`, `EdgeStep.keep_r`). -/
theorem OnFrames.leftEnd (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (hpj : PageOK sy m0 (seq j))
    (hside : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0) :
    ScrollRule.left16 (ScrollRule.places sy m0) (seq j) ≤ EdgeStep.pixel16 sy (seq j) := by
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j (by omega)
  have a4 := K.ix_mono (j + 1) g (by omega) (Nat.le_refl g)
  have a5 := K.ix_mono 0 j (by omega) (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hkq' : CtrlKeep.arrAt sy (K.fm j) (K.pad j) < kq := hkq
  have hp : ∀ n', kq ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 (by omega) kq n' (Nat.le_of_lt hkq) hn' hqq hf').1
    have hpg := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  have hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := (PositionKeep.pCheck_parts Ar.pk).2.2.2.2
  have hscc : ScreenClamp.check sy m0 = true := (PositionKeep.pCheck_parts Ar.pk).2.2.1
  -- the scroll's part of the scroll handler, up to the routine of the offscreen bits, with the right edge's relation (round 31)
  have rQ : RightEdge.Rel (ClampSide.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) :=
    rel_congr (fun x hx => (HQ x hx).2.trans (O.edgeLag hck hst Ar h1 (by omega) x hx)) (O.relAll hck hst Ar (j - 1) (by omega))
  obtain ⟨k2, g2, pc2, s2, hi2, lo2, pw2, sp2, C2, rel2⟩ := RightEdge.scroll_rel Ar.rc hgQ hqq
  have hR1 := rel2 rQ
  -- the routine of the offscreen bits and the clamp
  have hck2 := K.cleanAt j h1 (by omega)
  have ht : ∀ n, (PipeEntryRule.trace (K.fm j) (K.pad j) n).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hck2 n).time hn
  obtain ⟨k3, g3, pc3, s3, we3, _, up3, hp3, _, C3⟩ := ClampSide.clamp_end Ar.clampS hscc g2 pc2
  have hl3 := ClampSide.left_of Ar.clampS hR1 hp3
  have C23 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3) := FrameModel.InFrameN.add' C2 rfl C3
  have tr3 := FrameModel.trace_inFrame hidle hfq C23 ht (k2 + k3) (Nat.le_refl _)
  rw [FrameModel.stepN_add] at tr3
  -- the scroll handler's return, and the left edge from there to the frame's end (`EdgeStep.keep_r`)
  generalize hQ2 : FrameModel.stepN k2 (PipeEntryRule.trace (K.fm j) (K.pad j) kq) = Q2 at g2 pc2 s2 hi2 lo2 pw2 sp2 hR1 we3 up3 hp3 hl3 C3 tr3 g3 pc3 s3
  generalize hQ3 : FrameModel.stepN k3 Q2 = Q3 at we3 up3 hp3 hl3 tr3 g3 pc3 s3
  have lo3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1)) = (sy.PlayerSubs + 2).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add1]
    exact lo2
  have hi3 : Q3.ram.get! (FrameModel.stkI (Q3.s + 1 + 1)) = ((sy.PlayerSubs + 2) >>> 8).toUInt8 := by
    rw [s3, up3 _ (by simp), s2, ScrollRule.sub2_add2]
    exact hi2
  obtain ⟨_, pc4, rm4, C4⟩ := ret_step hscc g3 pc3 lo3 hi3
  have C234 : FrameModel.InFrameN (FrameModel.Rom.of m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) (k2 + k3 + 1) := by
    refine FrameModel.InFrameN.add' C23 ?_ C4
    rw [FrameModel.stepN_add, hQ2, hQ3]
  have tr4 := FrameModel.trace_inFrame hidle hfq C234 ht (k2 + k3 + 1) (Nat.le_refl _)
  rw [FrameModel.stepN_add, FrameModel.stepN_add, hQ2, hQ3] at tr4
  have eR := HR hp (kq + (k2 + k3 + 1)) (by omega) (by rw [tr4.1]; exact pc4)
  have ex : (seq j).ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) := by
    rw [ClampSide.eX_zero, K.ends j h1 (by omega), ← rm4, ← tr4.1]
    exact (eR.1 _ List.mem_cons_self)
  have ep : (seq j).ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) = Q3.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) := by
    rw [ClampSide.eP_zero, K.ends j h1 (by omega), ← rm4, ← tr4.1]
    exact (eR.1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hed : ClampSide.edge16 (ClampSide.places sy m0) 0 (seq j) = ClampSide.edge16 (ClampSide.places sy m0) 0 Q3 := by
    unfold ClampSide.edge16
    rw [ex, ep]
  -- the left edge at the return instruction, and its page
  have hw : ClampSide.edge16 (ClampSide.places sy m0) 0 Q3 = ClampSide.edge16 (ClampSide.places sy m0) 0 Q2 := by
    unfold ClampSide.edge16
    rw [we3 _ (by simp [ClampSide.EW]), we3 _ (by simp [ClampSide.EW])]
  have hlt : ClampSide.edge16 (ClampSide.places sy m0) 0 Q2 < 65280 := by
    have h : Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) ≠ 255 := by
      rw [← we3 _ (by simp [ClampSide.EW]), ← ep]
      exact hpj
    unfold ClampSide.edge16
    have h' := Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) |>.toNat_lt
    have h2 := Q2.ram.get! (ClampSide.eX (ClampSide.places sy m0) 0) |>.toNat_lt
    have h3' : (Q2.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0)).toNat ≠ 255 := by
      intro e
      apply h
      exact UInt8.toNat_inj.1 (by rw [e]; rfl)
    omega
  -- when the frame does not end with the side collision's timer at the push's value, his pixel and his page there
  -- are those of the instruction after the scroll handler's call (`PushTimer.pix_end`, with the field `posW` and `OnFrames.sideWAt`, round 37's theorem in place of the old field `sideW`), and so those of the return instruction
  have hpix : ClampSide.pix16 (ClampSide.places sy m0) (seq j) = ClampSide.pix16 (ClampSide.places sy m0) Q3 := by
    have hoff := (PositionWriters.wCheck_facts (PositionKeep.pCheck_parts Ar.pk).1).2.2
    obtain ⟨kq', hkq'', hqq', _, hbq', HP⟩ := PushTimer.pix_end hck Ar.pt hoff h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
    have hkk : kq' = kq := by
      rcases Nat.lt_trichotomy kq' kq with h | h | h
      · exact absurd hqq' (hbq kq' hkq'' h)
      · exact h
      · exact absurd hqq (hbq' kq hkq h)
    rw [hkk] at HP
    have hs' : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 := by
      rw [← K.ends j h1 (by omega)]; exact hside
    have pcR : (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).pc = EdgeStep.rPc sy := by rw [tr4.1]; exact pc4
    have E := HP (fun n' hn' hf' => ⟨O.posW j h1 (by omega) kq n' (Nat.le_of_lt hkq') hn' hqq hf', O.sideWAt hck hst Ar j h1 (by omega) hside kq n' (Nat.le_of_lt hkq') hn' hqq hf'⟩)
      (kq + (k2 + k3 + 1)) (by omega) pcR hs'
    have ex : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).x =
        (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).x := E _ List.mem_cons_self
    have ep : (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).page =
        (PipeEntryRule.trace (K.fm j) (K.pad j) (kq + (k2 + k3 + 1))).ram.get! (ScrollRule.places sy m0).page := E _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [tr4.1, rm4] at ex ep
    have m1 : (ClampSide.places sy m0).x = (ScrollRule.places sy m0).x := rfl
    have m2 : (ClampSide.places sy m0).page = (ScrollRule.places sy m0).page := rfl
    unfold ClampSide.pix16
    rw [m1, m2, K.ends j h1 (by omega), ex, ep]
  -- his pixel at the return instruction is the left edge's or at most 255 px right of it (`ClampSide.left_of`), and the edge's page is not 255
  have eL : ScrollRule.left16 (ScrollRule.places sy m0) (seq j) = ClampSide.edge16 (ClampSide.places sy m0) 0 (seq j) := by
    unfold ScrollRule.left16 ClampSide.edge16
    rw [ClampSide.eX_zero, ClampSide.eP_zero]
    rfl
  have eP : EdgeStep.pixel16 sy (seq j) = ClampSide.pix16 (ClampSide.places sy m0) (seq j) := rfl
  rw [eL, eP, hpix, hed, hw]
  have := ClampSide.pix16_lt (ClampSide.places sy m0) Q3
  omega

/-- **Every counted frame before the touch starts with `SideTimer.NearM`** (round 29): at control it holds (`AreaRun.near₀`), each counted frame ends with it
(round 30: `OnFrames.nearStepAt`, from the fields `rightRel` and `endKeep`; round 31: from the field `endKeep` and the left edge's page at the earlier frames,
`PageOK`, which `OnFrames.readAllP` gives; round 29: the field `nearStep`), and the frames not counted keep its bytes (`OnFrames.nearLag`) and the position (`OnFrames.lagKeep`) -/
theorem OnFrames.nearMAll (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) :
    ∀ j, 1 ≤ j → j < g → (∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) → SideTimer.NearM sy (ScrollRule.places sy m0) (K.fm j) := by
  have lag : ∀ j, 1 ≤ j → j < g → SideTimer.NearM sy (ScrollRule.places sy m0) (seq (j - 1)) → SideTimer.NearM sy (ScrollRule.places sy m0) (K.fm j) := by
    intro j h1 h3 h
    have kl := O.lagKeep hck hst Ar h1 (by omega)
    exact SideTimer.nearM_congr (O.nearLag hck hst Ar h1 (by omega)) (kl _ (by simp [CtrlKeep.keepA])) (kl _ (by simp [CtrlKeep.keepA])) h
  intro j h1 h3 hpg
  by_cases hj : j = 1
  · subst hj
    exact lag 1 (Nat.le_refl 1) h3 (Ar.near₀ (by omega))
  · exact lag j h1 h3 (O.nearStepAt hck hst Ar (j := j - 1) (by omega) (by omega) (hpg (j - 1) (by omega) (by omega)))

/-- **The old field `nearA`, a theorem (round 29)**: where each counted frame before the touch first comes to the player's routine, `MoveScroll.NearA`. The frame
starts in control (`hst`) and comes to the routine (`OnFrames.arrive`); up to there the side collision's timer falls by one at most and the frame keeps the place
byte, the lock, the edge and the position (`SideTimer.nearA_of_M`, with the walks of `SideTimer.sideCheck`, `SideTimer.keepCheck`, `CtrlKeep.ctrlCheck`), and the
frame starts with `SideTimer.NearM` (`OnFrames.nearMAll`, from `OnFrames.nearStepAt`). -/
theorem OnFrames.nearAAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    MoveScroll.NearA sy (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))) := by
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  have harr := O.arrive hck hst h1 (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_F (FrameKeep.cleanK_of_E (hclE n))
  exact SideTimer.nearA_of_M Ar.side Ar.keepS hck h0 hclK harr.1 harr.2.1 harr.2.2 (O.nearMAll hck hst Ar j h1 h3 hpg)

/-- **The old field `near`, a theorem (round 28)**: at the first scroll handler `Q` of each counted frame before the touch, `EdgeStep.NearX`. The frame is read up
to `Q` (`OnFrames.readH`, with the speed and the position of the frame before), so there his pixel is that of the first arrival at the player's routine plus the byte
the move stores, when that byte is from 1 to 128 (`MoveScroll.move_xs`, and the frame comes to the scroll handler once: `GuardE.subs_onceE`); the walks of
`PlaceKeep.keep_place` carry the scroll's three bytes and the edge from the arrival to `Q`; the platforms' force is 0 at `Q` (`hp0`); and `MoveScroll.NearA` (the old field `nearA`) is the
condition at the arrival (`MoveScroll.nearX_of_a`; round 29: a theorem, `OnFrames.nearAAt`, from `SideTimer.NearM` at the frame's start, `OnFrames.nearMAll`). -/
theorem OnFrames.nearAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g)
    (hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true) (hfar : SurfaceRead.Far sy (seq (j - 1))) {kq : Nat}
    (hk : CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ kq) (hqq : (PipeEntryRule.trace (K.fm j) (K.pad j) kq).pc = sy.PlayerSubs)
    (hbq : ∀ j', CtrlKeep.arrAt sy (K.fm j) (K.pad j) < j' → j' < kq → (PipeEntryRule.trace (K.fm j) (K.pad j) j').pc ≠ sy.PlayerSubs)
    (hp0 : (PipeEntryRule.trace (K.fm j) (K.pad j) kq).ram.get! (ScrollRule.places sy m0).plat = 0) (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    EdgeStep.NearX sy (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hkp := PlaceKeep.keep_place hck Ar.pl h0 hclF hxs hAf harr.1 harr.2.1 harr.2.2 hk hqq hbq
  have honce := GuardE.subs_onceE hck Ar.keep h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  obtain ⟨hR, _⟩ := O.readH hck hOK hfr hidle hst Ar h1 (by omega) hsp hfar
  obtain ⟨k, hk0, hpk, hmv⟩ := MoveScroll.move_xs hR Ar.xs honce
  have ek : k = kq := honce k kq hk0 hk hpk hqq
  subst ek
  exact MoveScroll.nearX_of_a (O.nearAAt hck hst Ar h1 h3 hpg) hkp hp0 hmv

/-- round 33: **No counted frame that moves right at the scroll handler, right of the screen's left edge there, ends with the speed 0 at the position there and
with the side collision's timer not at the push's value** (`OnFrames.stopAt`). Such a frame ends at the left edge (`OnFrames.stopRight`), so his pixel at the scroll handler `Q`
is the left edge at the frame's end. From `Q` to the instruction after the call the edge is kept, or the scroll is allowed and the edge moves at most the
scroll's amount, which is the byte the move stores (the platforms' force is 0 at `Q`: `OnFrames.platQ`) (`ScrollRule.scroll_edge`); from there to the frame's
end it is kept (`EdgeStep.keep_r`). Without a scroll the edge at the end is that of `Q`, left of his pixel there. With a scroll `EdgeStep.NearX` at `Q`
(`OnFrames.nearAt`) puts his pixel at least 2 px right of the edge plus that byte. Both contradict. `hsp`, `hfar`, `hpg` are what `nearAt` needs: the speed and
the position of the frame before, and the left edge's page on the frames before. -/
theorem OnFrames.noStopRight (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j)
    (h3 : j < g) (hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true) (hfar : SurfaceRead.Far sy (seq (j - 1)))
    (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) {k : Nat} (hk : CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k)
    (hpc : (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs) (hv : 0 < vOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) k))
    (hz : peek (seq j) sy.Player_X_Speed = 0) (he : posP sy (seq j) = posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) k))
    (hside : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0)
    (hl : ScrollRule.left16 (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) <
      EdgeStep.pixel16 sy (PipeEntryRule.trace (K.fm j) (K.pad j) k)) : False := by
  have hlb := O.stopRight hck hst Ar h1 h3 hk hpc hv hz he hside
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  have a3 := K.order j h3
  have a4 := K.ix_mono (j + 1) g (by omega) (Nat.le_refl g)
  have a5 := K.ix_mono 0 j (by omega) (by omega)
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have h0 := start_fm hst h1 (by omega)
  have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
  have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun n => FrameKeep.cleanK_of_E (hclE n)
  have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
    fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
  obtain ⟨kq, hkq, hqq, hfq, hbq, HR⟩ := EdgeStep.keep_r hck Ar.er h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2
  have honce := GuardE.subs_onceE hck Ar.keep h0 hclE hxs hAf harr.1 harr.2.1 harr.2.2
  have hkk : k = kq := honce k kq hk (Nat.le_of_lt hkq) hpc hqq
  subst hkk
  have HQ := EdgeStep.keep_q hck Ar.eq h0 hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 (Nat.le_of_lt hkq) hqq hbq
  have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
  have hgQ := (HQ _ hx0).1
  have hp : ∀ n', k ≤ n' → (PipeEntryRule.trace (K.fm j) (K.pad j) n').frame = (K.fm j).frame →
      EdgeStep.cutPos sy m0 (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc = false := by
    intro n' hn' hf'
    have W := (O.posW j h1 h3 k n' hk hn' hqq hf').1
    have hpg' := StepPrg.trace_prg (K.fm j) (K.pad j) n'
    have e1 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prg = m0.prg := hpg'.1.trans h0.prg
    have e2 : (PipeEntryRule.trace (K.fm j) (K.pad j) n').prgMask = m0.prgMask := hpg'.2.trans h0.mask
    rw [e1, e2] at W
    unfold EdgeStep.cutPos
    cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (PipeEntryRule.trace (K.fm j) (K.pad j) n').pc with
    | false => rfl
    | true => rw [W hs]; rfl
  -- `NearX` at `Q`
  obtain ⟨kq2, hk2, hq2, hp02⟩ := O.platQ hck hst Ar h1 h3
  have hkk2 : kq2 = k := honce kq2 k hk2 hk hq2 hqq
  subst hkk2
  have hNX := O.nearAt hck hOK hfr hidle hst Ar h1 h3 hsp hfar hk hqq hbq hp02 hpg
  -- the scroll handler's call, with the edge
  have hck2 := K.cleanAt j h1 (by omega)
  have ht : ∀ n, (PipeEntryRule.trace (K.fm j) (K.pad j) n).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace (K.fm j) (K.pad j) n).fdot ≤ dotsPerFrame - 64 := fun n hn => (hck2 n).time hn
  obtain ⟨k', g', pc', _, hedge, C'⟩ := ScrollRule.scroll_edge Ar.sr hgQ hqq
  have tr := FrameModel.trace_inFrame hidle hfq C' ht k' (Nat.le_refl _)
  have hk' : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with e0 | e0
    · exfalso
      subst e0
      have e2 : (FrameModel.stepN 0 (PipeEntryRule.trace (K.fm j) (K.pad j) kq2)).pc = sy.PlayerSubs := hqq
      rw [pc'] at e2
      have e3 := congrArg UInt16.toNat e2
      simp only [UInt16.toNat_add] at e3
      have e4 : (3 : UInt16).toNat = 3 := rfl
      rw [e4] at e3
      have := sy.PlayerSubs.toNat_lt
      omega
    · exact e0
  have pcR : (PipeEntryRule.trace (K.fm j) (K.pad j) (kq2 + k')).pc = EdgeStep.rPc sy := by rw [tr.1]; exact pc'
  have eR := HR hp (kq2 + k') (by omega) pcR
  have hpe : (seq j).prg = m0.prg ∧ (seq j).prgMask = m0.prgMask := by
    have s := hst (K.ix j) (by omega)
    rw [K.at_ix j (by omega)]
    exact ⟨s.prg, s.mask⟩
  have eb : SurfaceRead.edgeOf sy (seq j) = SurfaceRead.edgeOf sy (FrameModel.stepN k' (PipeEntryRule.trace (K.fm j) (K.pad j) kq2)) := by
    refine EdgeStep.edgeOf_eq hpe.1 hpe.2 g'.prg g'.mask fun x hx => ?_
    rw [K.ends j h1 (by omega), ← tr.1]
    exact eR.1 x hx
  rw [ScrollRule.edgeOf_left16 hpe.1 hpe.2, ScrollRule.edgeOf_left16 g'.prg g'.mask] at eb
  rw [ScrollRule.edgeOf_left16 g'.prg g'.mask, ScrollRule.edgeOf_left16 hgQ.prg hgQ.mask] at hedge
  -- his pixel at `Q` is that of the frame's end, which is the left edge there
  have pq : EdgeStep.pixel16 sy (seq j) = EdgeStep.pixel16 sy (PipeEntryRule.trace (K.fm j) (K.pad j) kq2) := pix16_of_posP (m0 := m0) he
  have ham : (ScrollRule.amountOf (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) kq2)).toNat =
      ((PipeEntryRule.trace (K.fm j) (K.pad j) kq2).ram.get! (ScrollRule.places sy m0).xs).toNat := by
    unfold ScrollRule.amountOf
    rw [hp02, UInt8.add_zero]
  rcases hedge with h | ⟨ha, Y, hY, hle⟩
  · omega
  · have := hNX ha
    omega

/-- **The old field `Moves.stop` (`StopAt`) on every counted frame from a clean state** (round 32). The field asks it only where at the scroll handler `Q` he is right
of the screen's left edge, or the frame starts left of it. On the other frames he is at or left of the edge at `Q` and the frame starts at or right of it. The frame
keeps the edge's two bytes from its start to `Q` (`EdgeStep.keep_q`; `Q` is the only scroll handler after the arrival: `GuardE.subs_onceE`), and the frames not
counted keep them from the end of the frame before (`OnFrames.edgeLag`). So pixel(Q) ≤ left(Q) = left(a) ≤ pixel(a), and P(Q) ≤ P(a) + 255
(`StopEdge.stop_of_edge`). Round 33: a frame right of the edge at `Q` that does not end with the side collision's timer at the push's value does not exist (`OnFrames.noStopRight`),
and a frame that starts left of the edge after a frame that did not end with the timer at that value does not exist (`OnFrames.leftEnd`; at control `AreaRun.edge₀`); so
the field asks only the frames near a push. `hfar` and `hpg` (the position of `a`, the left edge's page on the frames before) are for `OnFrames.nearAt`. -/
theorem OnFrames.stopAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ T) (h3 : j < g) (hc : Clean sy (seq (j - 1)))
    (hfar : SurfaceRead.Far sy (seq (j - 1))) (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    StopAt sy (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) := by
  intro k hk hpc hv h0 e
  by_cases hA : (ScrollRule.left16 (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) <
      EdgeStep.pixel16 sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) ∧
        (PipeTransition.frame (K.fm j) (K.pad j)).ram.get! (ScrollRule.places sy m0).sideB = PushTimer.pushT sy m0) ∨
      (EdgeStep.pixel16 sy (seq (j - 1)) < ScrollRule.left16 (ScrollRule.places sy m0) (seq (j - 1)) ∧
        (seq (j - 1)).ram.get! (ScrollRule.places sy m0).sideB = PushTimer.pushT sy m0)
  · exact (O.moves j h1 h2 h3 hc).stop k hk hpc hv h0 e hA
  -- round 33: the frame does not start left of the edge, when the frame before did not end with the side collision's timer at the push's value (`OnFrames.leftEnd`)
  have hstart : EdgeStep.pixel16 sy (seq (j - 1)) < ScrollRule.left16 (ScrollRule.places sy m0) (seq (j - 1)) → False := by
    intro ha
    have hsa : (seq (j - 1)).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 := fun h => hA (Or.inr ⟨ha, h⟩)
    rcases Nat.lt_or_ge 1 j with hj | hj
    · have := O.leftEnd hck hst Ar (j := j - 1) (by omega) (by omega) (hpg (j - 1) (by omega) (by omega)) hsa
      omega
    · -- `j = 1`: the machine at control
      have hj1 : j - 1 = 0 := by omega
      rw [hj1] at ha
      have e0 := Ar.edge₀ (by omega)
      have hp0 : (seq 0).prg = m0.prg ∧ (seq 0).prgMask = m0.prgMask := by
        have s := hst (K.ix 0) (by have := K.ix_mono 0 g (by omega) (Nat.le_refl g); omega)
        rw [K.at_ix 0 (by omega)]
        exact ⟨s.prg, s.mask⟩
      rw [ScrollRule.edgeOf_left16 hp0.1 hp0.2] at e0
      have hP : posP sy (seq 0) ≤ 256 * (EdgeStep.pixel16 sy (seq 0) : Int) + 255 := by
        show (((peek (seq 0) sy.Player_PageLoc).toNat * 256 + (peek (seq 0) sy.Player_X_Position).toNat) * 256 +
          (peek (seq 0) sy.SprObject_X_MoveForce).toNat : Int) ≤
          256 * (((peek (seq 0) sy.Player_PageLoc).toNat * 256 + (peek (seq 0) sy.Player_X_Position).toNat : Nat) : Int) + 255
        have := (peek (seq 0) sy.SprObject_X_MoveForce).toNat_lt
        omega
      omega
  by_cases hl : ScrollRule.left16 (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) <
      EdgeStep.pixel16 sy (PipeEntryRule.trace (K.fm j) (K.pad j) k)
  · -- round 33: right of the left edge at `Q`, with the side collision's timer not at the push's value at the end: no such frame (`OnFrames.noStopRight`)
    exfalso
    have hz : peek (seq j) sy.Player_X_Speed = 0 := by rw [K.ends j h1 (Nat.le_of_lt h3)]; exact h0
    have he : posP sy (seq j) = posP sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) := by rw [K.ends j h1 (Nat.le_of_lt h3)]; exact e
    have hs : (seq j).ram.get! (ScrollRule.places sy m0).sideB ≠ PushTimer.pushT sy m0 := by
      rw [K.ends j h1 (Nat.le_of_lt h3)]
      exact fun h => hA (Or.inl ⟨hl, h⟩)
    have hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true := by
      have h := hc.1
      simp only [inD, Bool.and_eq_true] at h
      exact h.1.1.1
    exact O.noStopRight hck hOK hfr hidle hst Ar h1 h3 hsp hfar hpg hk hpc hv hz he hs hl
  · have hcase : ¬ (ScrollRule.left16 (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) <
        EdgeStep.pixel16 sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) ∨
        EdgeStep.pixel16 sy (seq (j - 1)) < ScrollRule.left16 (ScrollRule.places sy m0) (seq (j - 1))) := by
      rintro (h | h)
      · exact hl h
      · exact hstart h
    have a1 := K.order (j - 1) (by omega)
    have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
    rw [show j - 1 + 1 = j by omega] at a1
    have harr := O.arrive hck hst h1 (by omega)
    have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
    have h0' := start_fm hst h1 (by omega)
    have hclE := K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega)
    have hxs := K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)
    have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
      fun n => FrameKeep.cleanK_of_E (hclE n)
    have hH : ∀ x ∈ EdgeStep.eI sy m0, ∀ n, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (PipeEntryRule.trace (K.fm j) (K.pad j) n) :=
      fun x hx n => EdgeStep.cleanH_of_E hx (hclE n)
    have honce := GuardE.subs_onceE hck Ar.keep h0' hclE hxs hAf harr.1 harr.2.1 harr.2.2
    have hb : ∀ j', CtrlKeep.arrAt sy (K.fm j) (K.pad j) < j' → j' < k → (PipeEntryRule.trace (K.fm j) (K.pad j) j').pc ≠ sy.PlayerSubs := by
      intro j' hj1 hj2 hpj
      have := honce j' k (Nat.le_of_lt hj1) hk hpj hpc
      omega
    have HQ := EdgeStep.keep_q hck Ar.eq h0' hclF hH hxs hAf harr.1 harr.2.1 harr.2.2 hk hpc hb
    have hx0 : ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_self
    have hp0 : ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat ∈ EdgeStep.eI sy m0 := List.mem_cons_of_mem _ List.mem_cons_self
    have elx : (ScrollRule.places sy m0).lx = ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat := rfl
    have elp : (ScrollRule.places sy m0).lp = ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat := rfl
    have ex : (PipeEntryRule.trace (K.fm j) (K.pad j) k).ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat =
        (seq (j - 1)).ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat := (HQ _ hx0).2.trans (O.edgeLag hck hst Ar h1 (by omega) _ hx0)
    have ep : (PipeEntryRule.trace (K.fm j) (K.pad j) k).ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat =
        (seq (j - 1)).ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat := (HQ _ hp0).2.trans (O.edgeLag hck hst Ar h1 (by omega) _ hp0)
    have eL : ScrollRule.left16 (ScrollRule.places sy m0) (PipeEntryRule.trace (K.fm j) (K.pad j) k) =
        ScrollRule.left16 (ScrollRule.places sy m0) (seq (j - 1)) := by
      unfold ScrollRule.left16
      rw [elx, elp, ex, ep]
    have := StopEdge.stop_of_edge sy (ScrollRule.places sy m0) (a := seq (j - 1)) (Q := PipeEntryRule.trace (K.fm j) (K.pad j) k) (by omega) (by omega) eL
    omega

/-- the state at the player's routine of the counted frame `j`, from a clean state: `Moves.toAt` with the frame's start in control (`hst`), `K.cleanAt`, `OnFrames.arrive`
and `OnFrames.lagKeep` -/
theorem OnFrames.movesAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ T) (h3 : j < g) (hc : Clean sy (seq (j - 1)))
    (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    MovesAt sy m0 (seq (j - 1)) (O.fm j) (O.pad j) (O.arr j) := by
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have hA : CtrlKeep.AreaOK sy v (seq (j - 1)) := by
    rw [K.at_ix (j - 1) (by omega)]
    exact Ar.all _ (by omega)
  have harea : peek (seq (j - 1)) sy.AreaType ∈ [(1 : UInt8), 2, 3] := by
    rw [hA.1]
    exact Ar.v3
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have hkh := GuardE.keepHE hck Ar.keep (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have honce := GuardE.subs_onceE hck Ar.keep (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have hz := FaceKeep.keepZ_end hck Ar.zk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have hlag := O.lagKeep hck hst Ar h1 (by omega)
  have hbits0 : peek (O.fm j) sy.Player_CollisionBits &&& sy.noLeft = sy.noLeft := by
    rw [hlag _ (keepA_mem (by simp))]
    rcases hc.2.2 with e | ⟨e, _⟩
    · have e' : peek (seq (j - 1)) sy.Player_CollisionBits = 0xFF := e
      rw [e', ff_and]
    · have e' : peek (seq (j - 1)) sy.Player_CollisionBits = sy.noLeft := e
      rw [e', UInt8.and_self]
  have hb := FaceKeep.bits_end hck Ar.bk (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf hbits0 harr.1 harr.2.1 harr.2.2 honce
  exact Moves.toAt hck hOK hfr hso (start_fm hst h1 (by omega)) (K.cleanAt j h1 (by omega)) hc harr hlag
    harea hA.2.1 hA.2.2 hfar hidle hkh honce (O.state j h1 (by omega))
    (O.collideAt hck hst Ar h1 h3)
    (fun k hk hpc => hz k hk hpc (FaceKeep.fdI sy) (by simp [FaceKeep.zI]))
    (fun k hk hpc hv => hb k hk hpc (sign_of_pos hv)) (O.keepAt hck hst Ar h1 h3) (O.stopAt hck hOK hfr hidle hst Ar h1 h2 h3 hc hfar hpg)

/-- **Each frame from a clean state is a `OneFrame`**, by the movement: `one_of_moves`, or with the side he presses masked `one_of_movesM`. -/
theorem one_of_frames (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hmk : FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ T) (h3 : j < g)
    (hc : Clean sy (seq (j - 1))) (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    OneFrame sy m0 (O.inp j) (seq (j - 1)) (seq j) := by
  have hmv := O.movesAt hck hOK hfr hso hst Ar h1 h2 h3 hc hfar hidle hpg
  by_cases hm : Masked sy (O.inp j) (seq (j - 1))
  · have e := one_of_movesM hOK hmk hmv hc hm
    rw [← O.ends j h1 h2 h3] at e
    exact e
  · have e := one_of_moves hOK hmv hm
    rw [← O.ends j h1 h2 h3] at e
    exact Or.inr e

/-- **The vertical step of a frame before `J`**: from the vertical model (`VertModel.vert_model`, proved), the state at the player's routine (`moves`, and the walk of
`CtrlKeep` for the vertical bytes up to there: `vBefore`, and bit 7 of A of the frame before: `OnFrames.prevAll`), and the frame's part from the scroll handler on
(`vAfter` for five bytes, the walk of `VertKeep` for four others: `OnFrames.kAt`, the walk of `FaceKeep` for the vertical force: `OnFrames.vfAt`). The step is
`VStep`: that of `vNext`, or on the ground that of `vNext` with the vertical force of a jumpspring's landing. In a jump the jump's halt value is 1 at the frame's
start, and so at its end. -/
theorem vert_of (hv : VertModel.vertOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hck : CtrlKeep.ctrlCheck sy m0 = true)
    (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true) (O : OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j < J) (hT : j ≤ T) (h3 : j < g)
    (hc : Clean sy (seq (j - 1))) (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hh : HaltOK sy (seq (j - 1))) (hpv : PrevKeep.PrevOK sy (seq (j - 1)))
    (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    VStep sy m0 (FaceKeep.vfC sy m0 v) (seq (j - 1)) (seq j) ∧ HaltOK sy (seq j) := by
  have hmv := O.movesAt hck hOK hfr hso hst Ar h1 hT h3 hc hfar hidle hpg
  have hv0 : peek (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j)) sy.Player_X_Speed = peek (seq (j - 1)) sy.Player_X_Speed := hmv.before _ (.head _)
  have hat := hmv.at_ctrl
  obtain ⟨vb1, vb2, vb3⟩ := vBefore hck (start_fm hst h1 (by omega)) (K.cleanAt j h1 (by omega)) (O.arrive hck hst h1 (by omega)) (O.lagKeep hck hst Ar h1 (by omega)) hpv
  change (∀ x ∈ vKeep sy, peek (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j)) x = peek (seq (j - 1)) x) at vb1
  change peek (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j)) sy.A_B_Buttons &&& 0x80 = _ at vb2
  change peek (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j)) sy.PreviousA_B_Buttons &&& 0x80 =
    peek (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j)) sy.A_B_Buttons &&& 0x80 at vb3
  generalize hR : PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j) = R at vb1 vb2 vb3 hv0 hat
  have hd : peek R sy.Player_State = 1 → peek R sy.DiffToHaltJump = 1 := by
    intro e
    rw [vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))]
    rw [vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))] at e
    exact hh e
  obtain ⟨k, hk, _, hpc, _, hvs, hhk, hC⟩ := VertModel.vert_model hv hat hd vb3
  have e0 : PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j + k) = FrameModel.stepN k R := by
    have e1 := (FrameModel.trace_inFrame hmv.idle hmv.start (by rw [hR]; exact hC) hmv.time k (Nat.le_refl k)).1
    rw [hR] at e1
    exact e1
  have hpc' : (PipeEntryRule.trace (O.fm j) (O.pad j) (O.arr j + k)).pc = sy.PlayerSubs := by rw [e0]; exact hpc
  have va0 := O.vAfter j h1 h2 h3 (O.arr j + k) (Nat.le_add_right _ _) hpc'
  have vk := O.kAt hck hst Ar h1 h3 (O.arr j + k) (Nat.le_add_right _ _) hpc'
  have vf0 := O.vfAt hck hst Ar h1 h3 (O.arr j + k) (Nat.le_add_right _ _) hpc'
  have va1 : ∀ x ∈ vHard sy, peek (seq j) x = peek (FrameModel.stepN k R) x := by
    intro x hx
    rw [← e0]
    exact va0 x hx
  have vk1 : ∀ x ∈ VertKeep.kI sy, (seq j).ram.get! x = (FrameModel.stepN k R).ram.get! x := by
    intro x hx
    rw [← e0]
    exact vk x hx
  have vf1 : peek (seq j) sy.VerticalForce = peek (FrameModel.stepN k R) sy.VerticalForce ∨
      (peek (seq j) sy.VerticalForce = FaceKeep.vfC sy m0 v ∧ peek (seq j) sy.Player_State = 0) := by
    rw [← e0]
    exact vf0
  have y1 : peek (seq j) sy.Player_Y_Position = peek (FrameModel.stepN k R) sy.Player_Y_Position := va1 _ (by simp [vHard])
  have y2 : peek (seq j) sy.Player_Y_MoveForce = peek (FrameModel.stepN k R) sy.Player_Y_MoveForce := va1 _ (by simp [vHard])
  have y3 : peek (seq j) sy.Player_Y_Speed = peek (FrameModel.stepN k R) sy.Player_Y_Speed := va1 _ (by simp [vHard])
  have y4 : peek (seq j) sy.Player_YMF_Dummy = peek (FrameModel.stepN k R) sy.Player_YMF_Dummy := va1 _ (by simp [vHard])
  have y6 : peek (seq j) sy.VerticalForceDown = peek (FrameModel.stepN k R) sy.VerticalForceDown := vk1 _ (by simp [VertKeep.kI])
  have y7 : peek (seq j) sy.JumpOrigin_Y_Position = peek (FrameModel.stepN k R) sy.JumpOrigin_Y_Position := vk1 _ (by simp [VertKeep.kI])
  have y8 : peek (seq j) sy.Player_State = peek (FrameModel.stepN k R) sy.Player_State := va1 _ (by simp [vHard])
  have y9 : peek (seq j) sy.DiffToHaltJump = peek (FrameModel.stepN k R) sy.DiffToHaltJump := vk1 _ (by simp [VertKeep.kI])
  have yA : peek (seq j) sy.A_B_Buttons = peek (FrameModel.stepN k R) sy.A_B_Buttons := vk1 _ (by simp [VertKeep.kI])
  -- the vertical bytes at the frame's end are those at the scroll handler, but the vertical force
  have eb : vsOf sy (seq j) = { VertModel.vsOf sy (FrameModel.stepN k R) with vf := peek (seq j) sy.VerticalForce } := by
    unfold vsOf VertModel.vsOf
    rw [y1, y2, y3, y4, y6, y7, y8, yA]
  have ea : VertModel.vsOf sy R = vsOf sy (seq (j - 1)) := by
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = Jump.VS.mk _ _ _ _ _ _ _ _ _
    rw [vb1 _ (.head _), vb1 _ (.tail _ (.head _)), vb1 _ (.tail _ (.tail _ (.head _))), vb1 _ (.tail _ (.tail _ (.tail _ (.head _)))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), vb2]
  have eab : peek R sy.Player_XSpeedAbsolute = peek (seq (j - 1)) sy.Player_XSpeedAbsolute := by
    rw [hat.abs, hc.2.1, hv0]
  rw [ea, eab] at hvs
  have ePA : (vsOf sy (seq j)).prevA = (VertModel.vsOf sy (FrameModel.stepN k R)).prevA := by
    show (peek (seq j) sy.A_B_Buttons &&& 0x80 != 0) = (peek (FrameModel.stepN k R) sy.A_B_Buttons &&& 0x80 != 0)
    rw [yA]
  have eXA : (VertModel.vsOf sy (FrameModel.stepN k R)).prevA = (peek R sy.SavedJoypadBits &&& 0x80 != 0) := by
    rw [hvs, VertModel.vstepV_eq]
  have eQ : VertModel.vsOf sy (FrameModel.stepN k R) = vNext sy m0 (seq (j - 1)) (seq j) := by
    unfold vNext
    rw [ePA, eXA]
    exact hvs
  refine ⟨?_, ?_⟩
  · rcases vf1 with e | ⟨e1, e2⟩
    · left
      rw [eb, e, ← eQ]
      rfl
    · right
      refine ⟨?_, by rw [eb, e1, eQ]⟩
      rw [← eQ]
      show peek (FrameModel.stepN k R) sy.Player_State = 0
      rw [← y8]
      exact e2
  · intro e
    show peek (seq j) sy.DiffToHaltJump = 1
    rw [y9]
    rw [y8] at e
    exact hhk e

/-- **The old field `edge`, a theorem (round 26)**: each counted frame before the touch moves the screen's left edge only behind him: at its end the edge is at most
the larger of the base at the end of the frame before and the position at its end. `OnFrames.scrollAt` gives the scroll handler `Q`, with the edge of the end of the
frame before, the instruction `R` after the call, with the edge of the frame's end, and the scroll's rule between them. `collide` gives P(Q) − 256 ≤ P
(`OnFrames.collideAt`), and `EdgeStep.NearX` is the condition at `Q` (round 27: it gives `EdgeStep.Near` as the platforms' force is 0 there; round 28: a theorem,
`OnFrames.nearAt`, from the field `nearA`, with the speed `hsp` and the position `hfar` of the frame before; round 29: `nearA` is a theorem, `OnFrames.nearAAt`). -/
theorem OnFrames.edgeAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g)
    (hsp : TopSpeed.inSpeed sy (peek (seq (j - 1)) sy.Player_X_Speed) = true) (hfar : SurfaceRead.Far sy (seq (j - 1)))
    (hpg : ∀ i, 1 ≤ i → i < j → PageOK sy m0 (seq i)) :
    SurfaceRead.edgeOf sy (seq j) ≤ max (SurfaceRead.baseOf sy (seq (j - 1))) (posP sy (seq j)) := by
  obtain ⟨kq, n, hk, hqq, hbq, eQ, e2, hpq, _, H⟩ := O.scrollAt hck hst Ar h1 h3
  have hp0 : (PipeEntryRule.trace (K.fm j) (K.pad j) kq).ram.get! (ScrollRule.places sy m0).plat = 0 := by
    rw [Ar.platP, hpq]
    exact O.platPrev hck hst Ar h1 h3
  have c := O.collideAt hck hst Ar h1 h3 kq hk hqq
  rw [← K.ends j h1 (by omega)] at c
  exact H _ _ eQ (EdgeStep.near_of_x (O.nearAt hck hOK hfr hidle hst Ar h1 h3 hsp hfar hk hqq hbq hp0 hpg) hp0) (EdgeStep.collideE_lower c) e2

/-- **Each frame before the touch starts with a speed of at most the top**, and within the first `farN` frames the position stays within `(16·top + 256)·d` left and
`16·top·d` right of the machine at control: each frame before it is read as a `TopSpeed.Frame` (`OnFrames.readE`, `SurfaceRead.frameE_end`), which keeps the speed at most
the top (`Frame.bound`), moves him at most `16·top` right, and at most `16·top + 256` left (the move and `CollideE`). `hg`: the touch is not later than `farN` frames
after control, so every frame before it is one of the first `farN` (a later touch is `SurfaceLate`). `hv0`, `hP0`: the speed 0 and the position of `B.m` at control. -/
theorem OnFrames.readAllP (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ d, d < g → TopSpeed.inSpeed sy (peek (seq d) sy.Player_X_Speed) = true ∧
      (d < farN sy B.m → posP sy B.m - (16 * (top sy : Int) + 256) * (d : Int) ≤ posP sy (seq d) ∧
        SurfaceRead.baseOf sy (seq d) ≤ posP sy B.m + 16 * (top sy : Int) * (d : Int)) ∧
      (∀ i, 1 ≤ i → i ≤ d → PageOK sy m0 (seq i)) := by
  have h16 : (16 : Int) ≤ (top sy : Int) := by
    have := (FrameModel.facts_of hOK).top16
    show (16 : Int) ≤ (TopSpeed.top sy : Int)
    omega
  intro d
  induction d with
  | zero =>
    intro hg0
    refine ⟨inSpeed_of (by have e : sbyte (peek (seq 0) sy.Player_X_Speed) = 0 := hv0; rw [e]; omega), fun _ => ?_, fun i h1 h2 => absurd h2 (by omega)⟩
    have e0 := Ar.edge₀ hg0
    have hb0 : SurfaceRead.baseOf sy (seq 0) = posP sy (seq 0) := by unfold SurfaceRead.baseOf; omega
    rw [hb0, hP0]
    simp
  | succ d ih =>
    intro hd
    obtain ⟨hsp, hr, hpg⟩ := ih (by omega)
    have hn : d < farN sy B.m := by omega
    have hfar : SurfaceRead.Far sy (seq d) := far_of_range hn ⟨(hr hn).1, Int.le_trans (SurfaceRead.le_baseOf _) (hr hn).2⟩
    obtain ⟨hR, hS⟩ := O.readE hck hOK hfr hidle hst Ar (j := d + 1) (by omega) hd (by simpa using hsp) (by simpa using hfar)
    have ev := SurfaceRead.frameE_v (sy := sy) m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1)))
    have eP := SurfaceRead.frameE_P (sy := sy) m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1)))
    have eB := SurfaceRead.frameE_B (sy := sy) m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1)))
    obtain ⟨e1, _, e3, e4⟩ := SurfaceRead.frameE_end hR hS
    have hend := K.ends (d + 1) (by omega) (by omega)
    generalize SurfaceRead.frameE sy m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1))) = c at ev eP eB e1 e3 e4
    rw [← hend] at e1 e3
    have e0 : d + 1 - 1 = d := rfl
    rw [e0] at ev eP eB
    have hv : -(top sy : Int) ≤ c.v ∧ c.v ≤ (top sy : Int) := by rw [ev]; exact FrameModel.speed_int hsp
    have hsv := c.speed hv
    have hpb := c.posB h16 hv
    have hv1 : -(top sy : Int) ≤ c.v₁ ∧ c.v₁ ≤ (top sy : Int) := by
      rcases c.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
    have hv2 := c.friction hv1
    have hm := c.move
    have hB : d + 1 < farN sy B.m → posP sy B.m - (16 * (top sy : Int) + 256) * ((d + 1 : Nat) : Int) ≤ posP sy (seq (d + 1)) ∧
        SurfaceRead.baseOf sy (seq (d + 1)) ≤ posP sy B.m + 16 * (top sy : Int) * ((d + 1 : Nat) : Int) := by
      intro hn
      obtain ⟨r1, r2⟩ := hr (by omega)
      have hed := O.edgeAt hck hOK hfr hidle hst Ar (j := d + 1) (by omega) hd (by simpa using hsp) (by simpa using hfar) (fun i h1 h2 => hpg i h1 (by omega))
      rw [e0] at hed
      have hba := SurfaceRead.le_baseOf (sy := sy) (seq d)
      have hmv : -16 * (top sy : Int) ≤ 16 * c.v₂ ∧ 16 * c.v₂ ≤ 16 * (top sy : Int) := by omega
      have c1 : ((d + 1 : Nat) : Int) = (d : Int) + 1 := by push_cast; rfl
      rw [c1, Int.mul_add, Int.mul_one, Int.mul_add, Int.mul_one]
      have hbe : SurfaceRead.baseOf sy (seq (d + 1)) = max (posP sy (seq (d + 1))) (SurfaceRead.edgeOf sy (seq (d + 1))) := rfl
      rw [hbe, ← e3]
      rw [← e3] at hed
      rw [eP] at hm hpb
      rw [eB] at hpb
      omega
    refine ⟨inSpeed_of ⟨by rw [← e1]; exact hsv.1, by rw [← e1]; exact hsv.2⟩, hB, fun i h1 h2 => ?_⟩
    by_cases hi : i ≤ d
    · exact hpg i h1 hi
    · have e : i = d + 1 := by omega
      subst e
      have hn1 : d + 1 < farN sy B.m := by omega
      have a3 := K.order (d + 1) hd
      have a2 := K.ix_mono (d + 1 + 1) g (by omega) (Nat.le_refl g)
      have s0 := hst (K.ix (d + 1)) (by omega)
      have hpe : (seq (d + 1)).prg = m0.prg ∧ (seq (d + 1)).prgMask = m0.prgMask := by
        rw [K.at_ix (d + 1) (by omega)]
        exact ⟨s0.prg, s0.mask⟩
      exact page_of_base Ar hpe.1 hpe.2 (d := d + 1) (by omega) (by rw [farN_congr hP0]; omega) (by rw [hP0]; exact (hB hn1).2)

/-- **Each frame before the touch starts with a speed of at most the top**, and within the first `farN` frames the position stays within `(16·top + 256)·d` left and
`16·top·d` right of the machine at control (`OnFrames.readAllP`) -/
theorem OnFrames.readAllB (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ d, d < g → TopSpeed.inSpeed sy (peek (seq d) sy.Player_X_Speed) = true ∧
      (d < farN sy B.m → posP sy B.m - (16 * (top sy : Int) + 256) * (d : Int) ≤ posP sy (seq d) ∧
        SurfaceRead.baseOf sy (seq d) ≤ posP sy B.m + 16 * (top sy : Int) * (d : Int)) :=
  fun d hd => have h := O.readAllP hck hOK hfr hidle hst Ar hv0 hP0 hg d hd; ⟨h.1, h.2.1⟩

/-- **round 31: the left edge's page is not 255 at the end of every counted frame before the touch** (the second half of the old field `rightRel`): the base
there is at most `posP(B.m) + 16·top·d` (`OnFrames.readAllP`), and `numbersCheck` puts that below the page 255 (`AreaRun.pageB`) -/
theorem OnFrames.pageAll (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ i, 1 ≤ i → i < g → PageOK sy m0 (seq i) :=
  fun i h1 h3 => (O.readAllP hck hOK hfr hidle hst Ar hv0 hP0 hg i h3).2.2 i h1 (Nat.le_refl i)

/-- `readAllB` with the position in place of the base -/
theorem OnFrames.readAll (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ d, d < g → TopSpeed.inSpeed sy (peek (seq d) sy.Player_X_Speed) = true ∧
      (d < farN sy B.m → posP sy B.m - (16 * (top sy : Int) + 256) * (d : Int) ≤ posP sy (seq d) ∧ posP sy (seq d) ≤ posP sy B.m + 16 * (top sy : Int) * (d : Int)) :=
  fun d hd =>
    have h := O.readAllB hck hOK hfr hidle hst Ar hv0 hP0 hg d hd
    ⟨h.1, fun hn => ⟨(h.2 hn).1, Int.le_trans (SurfaceRead.le_baseOf _) (h.2 hn).2⟩⟩

/-- **The screen's left edge stays behind a position he had** (round 24): at the end of each counted frame before the touch the edge is at most his position at the end
of that frame or of one before it (`OnFrames.edgeAt`: round 26, and at control `AreaRun.edge₀`: round 25) -/
theorem OnFrames.edge_behind (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ t, t < g → ∃ s, s ≤ t ∧ SurfaceRead.edgeOf sy (seq t) ≤ posP sy (seq s)
  | 0, h => ⟨0, Nat.le_refl 0, Ar.edge₀ h⟩
  | t + 1, h => by
    obtain ⟨s, hs, e⟩ := OnFrames.edge_behind hck hOK hfr hidle O hst Ar hv0 hP0 hg t (by omega)
    obtain ⟨hsp, hr⟩ := O.readAll hck hOK hfr hidle hst Ar hv0 hP0 hg t (by omega)
    have hn : t < farN sy B.m := by omega
    have hed := O.edgeAt hck hOK hfr hidle hst Ar (j := t + 1) (by omega) h (by simpa using hsp) (by simpa using far_of_range hn (hr hn))
      (fun i h1 h2 => O.pageAll hck hOK hfr hidle hst Ar hv0 hP0 hg i h1 (by omega))
    rw [show t + 1 - 1 = t by omega] at hed
    have hb : SurfaceRead.baseOf sy (seq t) = max (posP sy (seq t)) (SurfaceRead.edgeOf sy (seq t)) := rfl
    rw [hb] at hed
    by_cases h1 : SurfaceRead.edgeOf sy (seq (t + 1)) ≤ posP sy (seq (t + 1))
    · exact ⟨t + 1, Nat.le_refl _, h1⟩
    · by_cases h2 : SurfaceRead.edgeOf sy (seq (t + 1)) ≤ posP sy (seq t)
      · exact ⟨t, by omega, h2⟩
      · exact ⟨s, by omega, by omega⟩

/-- **A counted frame before the touch is read** (`SurfaceRead.ReadE`): the speed at its start is at most the top and its position away from the ends of its range
(`OnFrames.readAll`, with the touch not later than `farN` frames after control) -/
theorem OnFrames.readE_at (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) :
    SurfaceRead.ReadH sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) ∧ SurfaceRead.Same sy (seq (j - 1)) (K.fm j) ∧
      (j < g → SurfaceRead.ReadE sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) (SurfaceRead.baseOf sy (seq (j - 1)))) := by
  obtain ⟨hsp, hr⟩ := O.readAll hck hOK hfr hidle hst Ar hv0 hP0 hg (j - 1) (by omega)
  have hn : j - 1 < farN sy B.m := by omega
  have hfar : SurfaceRead.Far sy (seq (j - 1)) := far_of_range hn (hr hn)
  obtain ⟨hR, hS⟩ := O.readH hck hOK hfr hidle hst Ar h1 h3 hsp hfar
  exact ⟨hR, hS, fun hj => (O.readE hck hOK hfr hidle hst Ar h1 hj hsp hfar).1⟩

/-- **The frames are read from the machines** (`Reads`, the old field `reads`): `frOf` starts with the bytes of `seq (j − 1)` by its definition, and a frame before the touch
ends with those of `seq j` (`OnFrames.readE_at`, `SurfaceRead.frameE_end`, `K.ends`) -/
theorem OnFrames.reads (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) : Reads sy g seq (frOf sy m0 K) := by
  have hend : ∀ j, 1 ≤ j → j < g → (frOf sy m0 K j).v' = vOf sy (seq j) ∧ (frOf sy m0 K j).f' = fOf sy (seq j) ∧ (frOf sy m0 K j).P' = posP sy (seq j) := by
    intro j h1 h3
    obtain ⟨_, hS, hE⟩ := O.readE_at hck hOK hfr hidle hst Ar hv0 hP0 hg h1 (by omega)
    obtain ⟨e1, e2, e3, _⟩ := SurfaceRead.frameE_end (hE h3) hS
    have he := K.ends j h1 (by omega)
    unfold frOf
    rw [if_pos h3, he]
    exact ⟨e1, e2, e3⟩
  exact ⟨fun j _ _ => frOf_v K j, fun j _ _ => frOf_f K j, fun j _ _ => frOf_P K j, fun j h1 h3 => (hend j h1 h3).1, fun j h1 h3 => (hend j h1 h3).2.1,
    fun j h1 h3 => (hend j h1 h3).2.2⟩

/-- **The touch's frame up to the scroll handler**: `P₂` and `v₂` of `frOf g` are the position and the speed at an arrival of the touch's frame at the scroll handler -/
theorem OnFrames.touchMove (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hgN : g ≤ farN sy B.m) (hg : 1 ≤ g) :
    ∃ k, CtrlKeep.arrAt sy (K.fm g) (K.pad g) ≤ k ∧ (PipeEntryRule.trace (K.fm g) (K.pad g) k).pc = sy.PlayerSubs ∧
      (frOf sy m0 K g).P₂ = posP sy (PipeEntryRule.trace (K.fm g) (K.pad g) k) ∧ (frOf sy m0 K g).v₂ = vOf sy (PipeEntryRule.trace (K.fm g) (K.pad g) k) := by
  obtain ⟨hR, hS, _⟩ := O.readE_at hck hOK hfr hidle hst Ar hv0 hP0 hgN hg (Nat.le_refl g)
  obtain ⟨k, hk, hpc, e1, e2⟩ := SurfaceRead.frameH_move hR hS
  refine ⟨k, hk, hpc, ?_, ?_⟩
  · unfold frOf
    rw [if_neg (Nat.lt_irrefl g)]
    exact e1
  · unfold frOf
    rw [if_neg (Nat.lt_irrefl g)]
    exact e2

end Frames

/-! ## From the frames to the whole run -/

section Run

variable {B : Box} {T Jn g : Nat} {seq : Nat → Machine} {inp : Nat → HIn} {Sr : FrameKeep.RealRun} {ar : Nat} {K : FrameKeep.Frames sy m0 Sr ar g seq}

/-- the inputs of the first `n` frames: `inp j` is the input of the counted frame `j` -/
def wlist (inp : Nat → HIn) (n : Nat) : List HIn := (List.range n).map fun k => inp (k + 1)

theorem wlist_succ (n : Nat) : wlist inp (n + 1) = wlist inp n ++ [inp (n + 1)] := by
  simp [wlist, List.range_succ]

theorem wlist_length (n : Nat) : (wlist inp n).length = n := by simp [wlist]

theorem wlist_mem (hm : ∀ j, inp j ∈ inputs) (n : Nat) : ∀ i ∈ wlist inp n, i ∈ inputs := by
  intro i hi
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hi
  exact hm _

theorem wlist_take {n j : Nat} (h : j ≤ n) : (wlist inp n).take j = wlist inp j := by
  unfold wlist
  rw [← List.map_take, List.take_range]
  rw [Nat.min_eq_left h]

/-- following `hstep`, the state and the position are those of `go` -/
theorem go_wlist : ∀ n, (∀ i, i < n → Follow sy m0 (inp (i + 1)) (seq i) (seq (i + 1))) →
    go sy m0 (startHS sy (seq 0), posP sy (seq 0)) (wlist inp n) = (startHS sy (seq n), posP sy (seq n))
  | 0, _ => rfl
  | n + 1, h => by
    have ih := go_wlist n (fun i hi => h i (by omega))
    have hf := h n (by omega)
    rw [wlist_succ, FastTakeoff.go_append, ih]
    show adv sy m0 (startHS sy (seq n), posP sy (seq n)) (inp (n + 1)) = _
    unfold adv
    simp only
    have e : hstep sy m0 (startHS sy (seq n)) (inp (n + 1)) = startHS sy (seq (n + 1)) := hf.2.1.symm
    rw [e, hf.2.2]

/-- the position after frames that follow `hstep` -/
theorem pos_wlist (n : Nat) (h : ∀ i, i < n → Follow sy m0 (inp (i + 1)) (seq i) (seq (i + 1))) :
    posP sy (seq n) = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist inp n) := by
  have h1 := go_wlist (m0 := m0) (seq := seq) n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m0) (wlist inp n) (startHS sy (seq 0), posP sy (seq 0))
  rw [h1] at h2
  exact h2

/-- the frame after frames that follow `hstep`: its move is the next step of the distance -/
theorem pos_next (n : Nat) (h : ∀ i, i < n → Follow sy m0 (inp (i + 1)) (seq i) (seq (i + 1))) :
    posP sy (seq n) + 16 * sbyte (modelS sy m0 (seq n) (inp (n + 1))).v = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist inp (n + 1)) := by
  have h1 := go_wlist (m0 := m0) (seq := seq) n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m0) (wlist inp (n + 1)) (startHS sy (seq 0), posP sy (seq 0))
  rw [wlist_succ, FastTakeoff.go_append, h1] at h2
  rw [wlist_succ]
  exact h2

/-- the model moves at most `16·top` per frame, either way -/
theorem hdist_abs (F : Facts sy m0) : ∀ (is : List HIn) (s : HS), inD sy s = true → (∀ i ∈ is, i ∈ inputs) →
    -(16 * (top sy : Int) * (is.length : Int)) ≤ hdist sy m0 s is ∧ hdist sy m0 s is ≤ 16 * (top sy : Int) * (is.length : Int)
  | [], _, _, _ => by simp [hdist]
  | i :: r, s, hD, his => by
    obtain ⟨h1, _⟩ := FastTakeoff.step_facts F hD (his i (by simp))
    have ih := hdist_abs F r _ h1 (fun j hj => his j (by simp [hj]))
    have hv : -(top sy : Int) ≤ sbyte (hstep sy m0 s i).v ∧ sbyte (hstep sy m0 s i).v ≤ (top sy : Int) := by
      have := h1
      simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    simp only [hdist, List.length_cons]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-- **The position is away from both ends of its range** after `d ≤ T` frames that follow `hstep` from control: each moves at most `16·top`, and the position at
control is away from the ends by more than `T` such frames (`hfar`, a check of `SurfaceRun.allCheck`). This was the field `Moves.far`. -/
theorem far_of_follow (F : Facts sy m0) (Nm : Numbers sy m0 B Jn) (st : Start sy B (seq 0))
    (hfar : 2048 + 16 * (top sy : Int) * (T : Int) ≤ posP sy B.m ∧ posP sy B.m + 16 * (top sy : Int) * (T : Int) + 2048 < 0x1000000)
    (hin : ∀ j, inp j ∈ inputs) {d : Nat} (hd : d ≤ T) (hf : ∀ i, i < d → Follow sy m0 (inp (i + 1)) (seq i) (seq (i + 1))) :
    2048 ≤ posP sy (seq d) ∧ posP sy (seq d) + 2048 < 0x1000000 := by
  have e1 := pos_wlist (m0 := m0) (seq := seq) d hf
  have hd0 : startHS sy (seq 0) = startHS sy m0 := by rw [st.hs, Nm.hs]
  rw [hd0, st.P] at e1
  have h2 := hdist_abs F (wlist inp d) (startHS sy m0) Nm.hD (wlist_mem hin d)
  rw [wlist_length] at h2
  have h3 : 16 * (top sy : Int) * (d : Int) ≤ 16 * (top sy : Int) * (T : Int) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  rw [e1]
  omega

/-- the state at control is clean -/
theorem clean_start (Nm : Numbers sy m0 B Jn) (st : Start sy B (seq 0)) : Clean sy (seq 0) := by
  have e : peek (seq 0) sy.Player_X_Speed = peek B.m sy.Player_X_Speed := by
    rw [← hs_v, ← hs_v, st.hs]
  refine ⟨by rw [st.hs, Nm.hs]; exact Nm.hD, by rw [st.stored, e]; exact Nm.stored, Or.inl ?_⟩
  show peek (seq 0) sy.Player_CollisionBits = 0xFF
  rw [st.bits, Nm.bits]

/-- what `pix` gives on a position near `256·X` -/
theorem pix_near {X : Nat} {x0 pg dx : Nat} {P : Int} (hX : X = 256 * pg + x0) (hdx : dx ≤ x0)
    (h1 : 256 * ((X : Int) - dx) ≤ P) (h2 : P < 256 * ((X : Int) + dx + 1)) :
    ∃ a, a < 2 * dx + 1 ∧ pix P = (x0 + a - dx).toUInt8 := by
  have hq1 : (X : Int) - dx ≤ P / 256 := by omega
  have hq2 : P / 256 ≤ (X : Int) + dx := by omega
  refine ⟨(P / 256 - ((X : Int) - dx)).toNat, by omega, ?_⟩
  have e : (P / 256).toNat = 256 * pg + (x0 + (P / 256 - ((X : Int) - dx)).toNat - dx) := by omega
  unfold pix
  rw [e]
  apply UInt8.toNat_inj.1
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/-- the stored speed of a clean state is at most the top -/
theorem stored_le {m : Machine} (h : Clean sy m) : (peek m sy.Player_XSpeedAbsolute).toNat ≤ top sy := by
  rw [h.2.1, absB_natAbs]
  have h1 := h.1
  simp only [inD, Bool.and_eq_true, TopSpeed.inSpeed, decide_eq_true_eq] at h1
  exact h1.1.1.1

/-- **The frames before `J` are quiet**, and they follow `hstep`: each is a real frame (`moves`) that comes to the scroll handler at the model's state, near the start, and in the box's height
(`vert`, `vCheck`), and there the collision routine does what it does on the machine at control (`box`), which is nothing (`noHitCheck`). -/
theorem quiet_upto (F : TFacts sy m0) (hc : noHitCheck sy B.m B.dx B.dy = true) (Nm : Numbers sy m0 B Jn) (hfr : TopSpeed.frictionCheck sy m0 = true) (hJT : Jn ≤ T + 1)
    (O : OnFrames sy m0 B T Jn g seq K)
    (st : Start sy B (seq 0)) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (hF : ∀ n, n < K.ix g → SideAcross.FactsAt sy (K.all n) (K.inp n))
    (hfar : 2048 + 16 * (top sy : Int) * (T : Int) ≤ posP sy B.m ∧ posP sy B.m + 16 * (top sy : Int) * (T : Int) + 2048 < 0x1000000)
    (hpg : ∀ i, 1 ≤ i → i < g → PageOK sy m0 (seq i)) :
    ∀ d, d + 1 < Jn → d + 1 < g → (∀ i, i ≤ d → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1))) ∧
      (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF ∧
      (∀ i, i ≤ d → VStep sy m0 (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → HaltOK sy (seq i)) := by
  have hb0 : bitsOf sy (seq 0) = 0xFF := by
    show peek (seq 0) sy.Player_CollisionBits = 0xFF
    rw [st.bits, Nm.bits]
  have hh0 : HaltOK sy (seq 0) := by
    intro e
    have e1 : peek (seq 0) sy.Player_State = peek B.m sy.Player_State := congrArg Jump.VS.st st.vs
    rw [e1] at e
    exact absurd e Nm.st1
  intro d
  induction d with
  | zero =>
    intro h1 h2
    exact one_frame 0 h1 h2 (fun i hi => by omega) (fun i hi => by rw [show i = 0 by omega]; exact clean_start Nm st) hb0 (fun i hi => by omega)
      (fun i hi => by rw [show i = 0 by omega]; exact hh0)
  | succ d ih =>
    intro h1 h2
    obtain ⟨h3, h4, h5, h6, h7⟩ := ih (by omega) (by omega)
    exact one_frame (d + 1) h1 h2 (fun i hi => h3 i (by omega)) h4 h5 (fun i hi => h6 i (by omega)) h7
where
  one_frame (d : Nat) (h1 : d + 1 < Jn) (h2 : d + 1 < g) (hf : ∀ i, i < d → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1))) (hcl : ∀ i, i ≤ d → Clean sy (seq i))
      (hb : bitsOf sy (seq d) = 0xFF) (hvt : ∀ i, i < d → VStep sy m0 (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (seq i) (seq (i + 1)))
      (hho : ∀ i, i ≤ d → HaltOK sy (seq i)) :
      (∀ i, i ≤ d → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF ∧
      (∀ i, i ≤ d → VStep sy m0 (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → HaltOK sy (seq i)) := by
    have hc' : Clean sy (seq (d + 1 - 1)) := by simpa using hcl d (Nat.le_refl d)
    have hnm : ¬ Masked sy (inAt sy (O.fm (d + 1)) (O.pad (d + 1)) (O.arr (d + 1))) (seq (d + 1 - 1)) := by
      have hb' : bitsOf sy (seq (d + 1 - 1)) = 0xFF := by simpa using hb
      unfold Masked
      rw [hb', ff_and]
      exact fun h => h rfl
    have Ar : AreaRun sy m0 K (peek B.m sy.AreaType) := O.areaRun Nm st hst hF
    have hfd : 2048 ≤ posP sy (seq (d + 1 - 1)) ∧ posP sy (seq (d + 1 - 1)) + 2048 < 0x1000000 := by
      simpa using far_of_follow F.pot Nm st hfar (fun j => inAt_mem Nm.model _ _ _) (d := d) (by omega) hf
    have hmv := O.movesAt Nm.ctrl Nm.model hfr Nm.storedW hst Ar (j := d + 1) (by omega) (by omega) h2 hc' hfd Nm.idle (fun i hi1 hi2 => hpg i hi1 (by omega))
    have hpv : PrevKeep.PrevOK sy (seq (d + 1 - 1)) := by
      have h0 : PrevKeep.PrevOK sy (seq 0) := by
        unfold PrevKeep.PrevOK
        rw [st.prev, st.ab]
        exact Nm.prev0
      have a1 := K.ix_mono d g (by omega) (Nat.le_refl g)
      rw [show d + 1 - 1 = d by omega, K.at_ix d (by omega)]
      exact O.prevAll Nm.ctrl Nm.prev Ar hst h0 (K.ix d) (by omega)
    have hvd := vert_of Nm.vmodel Nm.ctrl Nm.model hfr Nm.storedW O hst Ar (j := d + 1) (by omega) h1 (by omega) h2 hc' hfd Nm.idle (by simpa using hho d (Nat.le_refl d)) hpv
      (fun i hi1 hi2 => hpg i hi1 (by omega))
    simp only [Nat.add_sub_cancel] at hvd
    obtain ⟨hvd, hhd⟩ := hvd
    have hvt' : ∀ i, i ≤ d → VStep sy m0 (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (seq i) (seq (i + 1)) := by
      intro i hi
      by_cases hid : i < d
      · exact hvt i hid
      · have : i = d := by omega
        subst this
        exact hvd
    have hend := O.ends (d + 1) (by omega) (by omega) h2
    obtain ⟨k, hk, hpc, h3, h4, Ak⟩ := at_subs Nm.model hmv hnm
    have hfdJ : peek (PipeTransition.frame (O.fm (d + 1)) (O.pad (d + 1))) sy.PlayerFacingDir =
        peek (PipeEntryRule.trace (O.fm (d + 1)) (O.pad (d + 1)) k) sy.PlayerFacingDir := by
      rcases Ak.after.fd with e | ⟨z1, z2⟩
      · exact e
      · have hj := O.faceJ (d + 1) (by omega) h1 h2 k hk hpc
        rw [hend] at hj
        exact hj z1 z2
    have hP := pre_of_after h3 Ak hfdJ
    rw [← hend] at hP
    have hbr := O.box (d + 1) (by omega) h1 h2 k hk hpc
    simp only [Nat.add_sub_cancel] at hc' hP h3 h4 hbr
    generalize PipeEntryRule.trace (O.fm (d + 1)) (O.pad (d + 1)) k = Q at h3 h4 hbr
    have h3' : startHS sy Q = modelS sy m0 (seq d) (O.inp (d + 1)) := h3
    have hP' : Pre sy m0 (O.inp (d + 1)) (seq d) (seq (d + 1)) := hP
    have ev : sbyte (modelS sy m0 (seq d) (O.inp (d + 1))).v = vOf sy Q := by rw [← h3']; rfl
    -- the pixel at the scroll handler is near the start
    have hQ : posP sy Q = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist O.inp (d + 1)) := by
      rw [h4, ← ev]
      exact pos_next d hf
    have hd0 : startHS sy (seq 0) = startHS sy m0 := by rw [st.hs, Nm.hs]
    have hdist1 := dist_abs F.pot (wlist O.inp (d + 1)) (startHS sy m0) (Opening.pOf sy m0 (startHS sy m0)) (Opening.J_pOf Nm.hD) (wlist_mem (fun j => inAt_mem Nm.model _ _ _) _)
    rw [wlist_length] at hdist1
    have hdl := Nm.dist (d + 1) h1
    rw [hd0] at hQ
    -- the height is in the box
    have hvs : boxVB sy B (vsOf sy (seq (d + 1))) = true := by
      refine vCheck_spec (Jn - 1) [vsOf sy B.m] Nm.vert (fun i => vsOf sy (seq i)) (fun i => (vsOf sy (seq (i + 1))).prevA) (fun i => peek (seq i) sy.Player_XSpeedAbsolute)
        (by simp only [List.mem_singleton]; exact st.vs) (d + 1) (by omega) (by omega) (fun i hi => ?_)
      refine ⟨stored_le (hcl i (by omega)), ?_⟩
      rcases hvt' i (by omega) with e | ⟨e0, e⟩
      · exact (congrArg (· ∈ vVar (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (vNext sy m0 (seq i) (seq (i + 1)))) e).mpr (mem_vVar_self _ _)
      · exact (congrArg (· ∈ vVar (FaceKeep.vfC sy m0 (peek B.m sy.AreaType)) (vNext sy m0 (seq i) (seq (i + 1)))) e).mpr (mem_vVar_c _ e0)
    have hy3 : (vNext sy m0 (seq d) (seq (d + 1))).y = (vsOf sy (seq (d + 1))).y ∧ (vNext sy m0 (seq d) (seq (d + 1))).vy = (vsOf sy (seq (d + 1))).vy ∧
        (vNext sy m0 (seq d) (seq (d + 1))).st = (vsOf sy (seq (d + 1))).st := by
      rcases hvd with e | ⟨_, e⟩
      · exact ⟨congrArg Jump.VS.y e.symm, congrArg Jump.VS.vy e.symm, congrArg Jump.VS.st e.symm⟩
      · exact ⟨by rw [e], by rw [e], by rw [e]⟩
    obtain ⟨v, hv, hr⟩ := hbr
    rw [hy3.1, hy3.2.1, hy3.2.2] at hr
    have hy := boxV_of_B hvs
    have hx0 : (peek B.m sy.Player_X_Position).toNat < 256 := (peek B.m sy.Player_X_Position).toNat_lt
    have hmf := (peek B.m sy.SprObject_X_MoveForce).toNat_lt
    have hPA : posP sy (seq 0) = 256 * ((((peek B.m sy.Player_PageLoc).toNat * 256 + (peek B.m sy.Player_X_Position).toNat : Nat)) : Int) + ((peek B.m sy.SprObject_X_MoveForce).toNat : Int) := by
      rw [st.P]
      unfold posP
      omega
    obtain ⟨a, ha, hpx⟩ := pix_near (X := (peek B.m sy.Player_PageLoc).toNat * 256 + (peek B.m sy.Player_X_Position).toNat) (x0 := (peek B.m sy.Player_X_Position).toNat)
      (pg := (peek B.m sy.Player_PageLoc).toNat) (dx := B.dx) (P := posP sy Q) (by omega) Nm.dx (by rw [hQ, hPA]; omega) (by rw [hQ, hPA]; omega)
    have hq := quiet_of_box hc ⟨pix (posP sy Q), _, v, _, _, ⟨⟨a, ha, hpx⟩, hv, hy⟩, hr⟩
    obtain ⟨q1, q2, q3⟩ := hq
    -- so the frame follows `hstep`
    have hf1 : Follow sy m0 (O.inp (d + 1)) (seq d) (seq (d + 1)) := by
      refine follow_of_pre (inAt_mem Nm.model _ _ _) hP' ?_ ?_
      · show sbyte (peek (seq (d + 1)) sy.Player_X_Speed) = _
        rw [q2, ev]
        rfl
      · rw [q1, h4, ev]
    have hc1 := clean_of_follow F.pot hc' hf1 hP' (Or.inl q3)
    refine ⟨fun i hi => ?_, fun i hi => ?_, q3, hvt', fun i hi => ?_⟩
    · by_cases hid : i < d
      · exact hf i hid
      · have : i = d := by omega
        subst this
        exact hf1
    · by_cases hid : i ≤ d
      · exact hcl i hid
      · have : i = d + 1 := by omega
        subst this
        exact hc1
    · by_cases hid : i ≤ d
      · exact hho i hid
      · have : i = d + 1 := by omega
        subst this
        exact hhd

/-- the first number where a property fails, if there is one up to `n` -/
theorem exists_first (P : Nat → Prop) : ∀ n, (∀ j, 1 ≤ j → j ≤ n → P j) ∨ ∃ h, 1 ≤ h ∧ h ≤ n ∧ ¬ P h ∧ ∀ j, 1 ≤ j → j < h → P j
  | 0 => Or.inl fun j h1 h2 => by omega
  | n + 1 => by
    rcases exists_first P n with h | h
    · by_cases hp : P (n + 1)
      · left
        intro j h1 h2
        by_cases hj : j ≤ n
        · exact h j h1 hj
        · have : j = n + 1 := by omega
          rw [this]
          exact hp
      · exact Or.inr ⟨n + 1, by omega, by omega, hp, fun j h1 h2 => h j h1 (by omega)⟩
    · obtain ⟨h0, h1, h2, h3, h4⟩ := h
      exact Or.inr ⟨h0, h1, by omega, h3, h4⟩

/-- the speed at control is 0 -/
theorem start_v0 (hn : numbersCheck sy m0 B Jn = true) (st : Start sy B (seq 0)) : vOf sy (seq 0) = 0 := by
  have Nm := numbers_of_check hn
  show sbyte (peek (seq 0) sy.Player_X_Speed) = 0
  rw [← hs_v, st.hs, hs_v]
  exact Nm.v0

/-- **The statements about the whole run follow from the frames.** `model`, `hit`, `stop`, and no hit before `J`, with no search. `h` is the first frame up to `T` before the touch that does not
follow `hstep` into a clean state. -/
theorem surface_of_frames (F : TFacts sy m0) (hc : noHitCheck sy B.m B.dx B.dy = true) (hn : numbersCheck sy m0 B Jn = true) (hfr : TopSpeed.frictionCheck sy m0 = true) (hJT : Jn ≤ T)
    (hfar : 2048 + 16 * (top sy : Int) * (T : Int) ≤ posP sy B.m ∧ posP sy B.m + 16 * (top sy : Int) * (T : Int) + 2048 < 0x1000000)
    (O : OnFrames sy m0 B T Jn g seq K) (st : Start sy B (seq 0)) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    (hF : ∀ n, n < K.ix g → SideAcross.FactsAt sy (K.all n) (K.inp n)) (hg : g ≤ farN sy B.m) :
    ∃ w h, Surface sy m0 (posP sy B.m) T Jn g (frOf sy m0 K) w h := by
  have Nm := numbers_of_check hn
  have Ar : AreaRun sy m0 K (peek B.m sy.AreaType) := O.areaRun Nm st hst hF
  have Rd := O.reads Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg
  -- round 33: the left edge's page on every counted frame before the touch (`OnFrames.stopAt` uses it, through `OnFrames.nearAt`)
  have hpgA := O.pageAll Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg
  have hd0 : startHS sy (seq 0) = startHS sy m0 := by rw [st.hs, Nm.hs]
  have hin : ∀ j, O.inp j ∈ inputs := fun j => inAt_mem Nm.model _ _ _
  let FC : Nat → Prop := fun j => Follow sy m0 (O.inp j) (seq (j - 1)) (seq j) ∧ Clean sy (seq j)
  -- the first frame that fails, or a frame past `T`
  have hfirst : ∃ h, (∀ j, 1 ≤ j → j < h → j ≤ T → j < g → FC j) ∧ (h ≤ T → 1 ≤ h ∧ h < g ∧ ¬ FC h) := by
    rcases exists_first FC (min T (g - 1)) with h | ⟨h0, h1, h2, h3, h4⟩
    · exact ⟨T + 1, fun j h1 _ h3 h5 => h j h1 (by omega), fun h1 => by omega⟩
    · exact ⟨h0, fun j h5 h6 _ _ => h4 j h5 h6, fun _ => ⟨h1, by omega, h3⟩⟩
  obtain ⟨h, H1, H2⟩ := hfirst
  have hfol : ∀ n, n < h → n ≤ T → n < g → ∀ i, i < n → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1)) := by
    intro n h1 h2 h3 i hi
    have := (H1 (i + 1) (by omega) (by omega) (by omega) (by omega)).1
    simpa using this
  -- the state before the first failure is clean
  have hclean : h ≤ T → Clean sy (seq (h - 1)) := by
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    by_cases h0 : h = 1
    · subst h0
      exact clean_start Nm st
    · exact (H1 (h - 1) (by omega) (by omega) (by omega) (by omega)).2
  have hhit : h ≤ T → Hit sy m0 (O.inp h) (seq (h - 1)) (seq h) := by
    intro hT
    obtain ⟨h1, h2, h3⟩ := H2 hT
    have hfh := far_of_follow F.pot Nm st hfar hin (d := h - 1) (by omega) (hfol (h - 1) (by omega) (by omega) (by omega))
    have ho := one_of_frames Nm.model Nm.mask hfr Nm.storedW Nm.ctrl O hst Ar h1 hT h2 (hclean hT) hfh Nm.idle (fun i hi1 hi2 => hpgA i hi1 (by omega))
    rcases step_of_one F.pot (hin h) (hclean hT) ho with h4 | h4
    · exact absurd h4 h3
    · exact h4
  have hposn : h ≤ T → posP sy (seq (h - 1)) = posP sy B.m + hdist sy m0 (startHS sy m0) (wlist O.inp (h - 1)) ∧
      posP sy (seq (h - 1)) + 16 * sbyte (modelS sy m0 (seq (h - 1)) (O.inp h)).v = posP sy B.m + hdist sy m0 (startHS sy m0) (wlist O.inp h) := by
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    have hf : ∀ i, i < h - 1 → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1)) := hfol (h - 1) (by omega) (by omega) (by omega)
    have e1 := pos_wlist (m0 := m0) (seq := seq) (h - 1) hf
    have e2 := pos_next (m0 := m0) (seq := seq) (h - 1) hf
    rw [hd0, st.P] at e1 e2
    rw [show h - 1 + 1 = h by omega] at e2
    exact ⟨e1, e2⟩
  have hposs : ∀ s, s ≤ h - 1 → h ≤ T → posP sy (seq s) = posP sy B.m + hdist sy m0 (startHS sy m0) (wlist O.inp s) := by
    intro s hs hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    have hf : ∀ i, i < s → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1)) :=
      fun i hi => hfol (h - 1) (by omega) (by omega) (by omega) i (by omega)
    have e1 := pos_wlist (m0 := m0) (seq := seq) s hf
    rw [hd0, st.P] at e1
    exact e1
  have hbo : ∀ x, SurfaceRead.baseOf sy x = max (posP sy x) (SurfaceRead.edgeOf sy x) := fun _ => rfl
  refine ⟨wlist O.inp T, h, wlist_mem hin T, by rw [wlist_length]; omega, fun hT => (H2 hT).2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- no hit before `J`: the frames before it follow `hstep` into a clean state
    by_cases hT : h ≤ T
    · obtain ⟨h1, h2, h3⟩ := H2 hT
      by_cases hJ : Jn ≤ h
      · exact hJ
      · exfalso
        obtain ⟨d, rfl⟩ : ∃ d, h = d + 1 := ⟨h - 1, by omega⟩
        obtain ⟨hf, hcl, _⟩ := quiet_upto F hc Nm hfr (by omega) O st hst hF hfar hpgA d (by omega) h2
        exact h3 ⟨by simpa using hf d (Nat.le_refl d), hcl (d + 1) (Nat.le_refl _)⟩
    · omega
  · -- `model`
    intro j h1 h2 h3 h4
    have hf := hfol j h2 h3 h4
    have e1 := pos_wlist (m0 := m0) (seq := seq) j hf
    rw [hd0, st.P] at e1
    rw [wlist_take h3, Rd.P' j h1 h4, e1]
    omega
  · -- `hit`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    obtain ⟨_, h3⟩ := hhit hT
    obtain ⟨e1, e2⟩ := hposn hT
    rw [wlist_take hT, Rd.P' h h1 h2]
    rcases h3 with h3 | h3
    · exact Or.inl (by omega)
    · right
      obtain ⟨s, hs, es⟩ := O.edge_behind Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg (h - 1) (by omega)
      have ps := hposs s hs hT
      rw [hbo] at h3
      by_cases hc : SurfaceRead.edgeOf sy (seq (h - 1)) ≤ posP sy (seq (h - 1))
      · exact ⟨h - 1, by omega, by rw [wlist_take (by omega)]; omega⟩
      · exact ⟨s, by omega, by rw [wlist_take (by omega)]; omega⟩
  · -- `stop`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    rw [Rd.v' h h1 h2]
    exact (hhit hT).1
  · -- `base`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    rw [frOf_B, Rd.P' h h1 h2, show h + 1 - 1 = h by omega]
    obtain ⟨s, hs, es⟩ := O.edge_behind Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg h h2
    rw [hbo]
    by_cases hc : SurfaceRead.edgeOf sy (seq h) ≤ posP sy (seq h)
    · exact Or.inl (by omega)
    · right
      have hsh : s < h := by
        rcases Nat.lt_or_ge s h with x | x
        · exact x
        · have e : s = h := by omega
          rw [e] at es
          exact absurd es hc
      have ps := hposs s (by omega) hT
      exact ⟨s, hsh, by rw [wlist_take (by omega)]; omega⟩
  · -- `links`
    intro t h1 h2
    rw [frOf_B, frOf_B, frOf_P, frOf_P, show t + 1 - 1 = t by omega]
    obtain ⟨hsp, hr⟩ := O.readAll Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg (t - 1) (by omega)
    have hn1 : t - 1 < farN sy B.m := by omega
    have hed := O.edgeAt Nm.ctrl Nm.model hfr Nm.idle hst Ar h1 h2 hsp (far_of_range hn1 (hr hn1))
      (fun i h1' h2' => O.pageAll Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg i h1' (by omega))
    rw [hbo (seq t)]
    omega
  · -- `base₁`
    intro hg1
    rw [frOf_B]
    show SurfaceRead.baseOf sy (seq 0) ≤ posP sy B.m
    have e := Ar.edge₀ hg1
    have p := st.P
    rw [hbo]
    omega

/-- at control he is stopped at the machine's position: `frOf` starts with the bytes of the machine at control -/
theorem start_P (K : FrameKeep.Frames sy m0 Sr ar g seq) (st : Start sy B (seq 0)) : (frOf sy m0 K 1).P = posP sy B.m := by
  rw [frOf_P]
  exact st.P

theorem start_v (hn : numbersCheck sy m0 B Jn = true) (K : FrameKeep.Frames sy m0 Sr ar g seq) (st : Start sy B (seq 0)) : (frOf sy m0 K 1).v = 0 := by
  rw [frOf_v]
  exact start_v0 hn st

end Run

/-! ## The start, from the rows of `SideChangeEnd` -/

section Rows

open SideChangeBound
open SideChangeEnd
open PipeChangeBound (inPipe)
open PipeTransitionAll (Names)
open PipeTransition (run zeros frame)

/-- the bytes that say whether a machine has control -/
def ctlBytes (sy : Syms) : List UInt16 := [sy.OperMode, sy.OperMode_Task, sy.GameEngineSubroutine]

/-- the bytes of `Start` -/
def startBytes (sy : Syms) : List UInt16 :=
  [sy.Player_X_Speed, sy.Player_X_MoveForce, sy.PlayerFacingDir, sy.Player_MovingDir, sy.RunningSpeed, sy.Player_PageLoc, sy.Player_X_Position, sy.SprObject_X_MoveForce,
   sy.Player_XSpeedAbsolute, sy.Player_CollisionBits, sy.Player_Y_Position, sy.Player_Y_MoveForce, sy.Player_Y_Speed, sy.Player_YMF_Dummy, sy.VerticalForce, sy.VerticalForceDown,
   sy.JumpOrigin_Y_Position, sy.Player_State, sy.A_B_Buttons, sy.AreaType, sy.SwimmingFlag, sy.PlayerChangeSizeFlag, sy.PreviousA_B_Buttons]

/-- the two bytes of the screen's left edge, at the clamp's operands found in the program of `c` (round 25), the platforms' force on the scroll (round 27), and the
two bytes of the screen's right edge, one byte after the left edge's (round 31) -/
def edgeBytes (sy : Syms) (c : Machine) : List UInt16 :=
  [(ScreenClamp.places sy c).edgeX, (ScreenClamp.places sy c).edgeP, sy.Platform_X_Scroll, (ScreenClamp.places sy c).edgeX + 1, (ScreenClamp.places sy c).edgeP + 1]

/-- a state of a row: it says whether it has control, and if it has, it knows the bytes of `Start`, with the values of the machine `c` -/
def rowStart (sy : Syms) (c : Machine) (S : AS) : Bool :=
  (ctlBytes sy).all (knowsAd S) && (!controllable sy (mOf S) || ((startBytes sy).all fun a => knowsAd S a && peek (mOf S) a == peek c a) &&
    (edgeBytes sy c).all fun a => knowsAd S a && peek (mOf S) a == peek c a)

/-- every state of the rows -/
def rowsStart (sy : Syms) (c : Machine) (l : List Row) : Bool := l.all fun r => r.R.all (rowStart sy c)

/-- the check on the ROM: the state at control in the rows is that of `c`. Also what says that a machine in the pipe's frames has no control. -/
def startCheck (sy : Syms) (nm nx : Names) (e : Machine) (A B : Nat) (c : Box) : Bool :=
  let x := run e (zeros A)
  rowsStart sy c.m (rows0 (rowCtx sy nm nx e A B) nx e A B) && rowsStart sy c.m (rows1 (rowCtx sy nm nx e A B) nx e A B) &&
    leftCheck (sideEnv nm e) sy nm sy.EngSidePipe (tableFrom sy nm B x) B (startsOf (refsOf nm e)) x

variable {nm nx : Names} {e : Machine} {c : Box} {A B : Nat} {es : List Machine}

theorem controllable_of_known {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hk : (ctlBytes sy).all (knowsAd S) = true)
    (h : controllable sy m = true) : controllable sy (mOf S) = true := by
  simp only [ctlBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hk
  obtain ⟨h1, h2, h3⟩ := hk
  unfold controllable at h ⊢
  rw [← peek_of_known hs h1, ← peek_of_known hs h2, ← peek_of_known hs h3]
  exact h

/-- a covered machine with control has the bytes of `c.m` -/
theorem start_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowStart sy c.m S = true) (h : controllable sy m = true) : Start sy c m := by
  simp only [rowStart, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · obtain ⟨h1, h2⟩ := h1
    simp only [edgeBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨⟨kx, ex⟩, ⟨kp, ep⟩, ⟨kl, el⟩, ⟨krx, erx⟩, ⟨krp, erp⟩⟩ := h2
    simp only [startBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨k1, e1⟩, ⟨k2, e2⟩, ⟨k3, e3⟩, ⟨k4, e4⟩, ⟨k5, e5⟩, ⟨k6, e6⟩, ⟨k7, e7⟩, ⟨k8, e8⟩, ⟨k9, e9⟩, ⟨k10, e10⟩, ⟨k11, e11⟩, ⟨k12, e12⟩, ⟨k13, e13⟩, ⟨k14, e14⟩, ⟨k15, e15⟩, ⟨k16, e16⟩, ⟨k17, e17⟩, ⟨k18, e18⟩, ⟨k19, e19⟩,
      ⟨k20, e20⟩, ⟨k21, e21⟩, ⟨k22, e22⟩, ⟨k23, e23⟩⟩ := h1
    have g1 := (peek_of_known hs k1).trans e1
    have g2 := (peek_of_known hs k2).trans e2
    have g3 := (peek_of_known hs k3).trans e3
    have g4 := (peek_of_known hs k4).trans e4
    have g5 := (peek_of_known hs k5).trans e5
    have g6 := (peek_of_known hs k6).trans e6
    have g7 := (peek_of_known hs k7).trans e7
    have g8 := (peek_of_known hs k8).trans e8
    have g9 := (peek_of_known hs k9).trans e9
    have g10 := (peek_of_known hs k10).trans e10
    have g11 := (peek_of_known hs k11).trans e11
    have g12 := (peek_of_known hs k12).trans e12
    have g13 := (peek_of_known hs k13).trans e13
    have g14 := (peek_of_known hs k14).trans e14
    have g15 := (peek_of_known hs k15).trans e15
    have g16 := (peek_of_known hs k16).trans e16
    have g17 := (peek_of_known hs k17).trans e17
    have g18 := (peek_of_known hs k18).trans e18
    have g19 := (peek_of_known hs k19).trans e19
    have g20 := (peek_of_known hs k20).trans e20
    have g21 := (peek_of_known hs k21).trans e21
    have g22 := (peek_of_known hs k22).trans e22
    have g23 := (peek_of_known hs k23).trans e23
    refine ⟨?_, ?_, g9, g10, ?_, g20, g21, g22, g19, g23, (peek_of_known hs kx).trans ex, (peek_of_known hs kp).trans ep, (peek_of_known hs kl).trans el,
      (peek_of_known hs krx).trans erx, (peek_of_known hs krp).trans erp⟩
    · have e5 : (peek m sy.RunningSpeed == 0) = (peek c.m sy.RunningSpeed == 0) := by rw [g5]
      simp only [startHS, PState.read, g1, g2, g3, g4, e5]
      congr
    · unfold posP
      rw [g6, g7, g8]
    · simp only [vsOf, g11, g12, g13, g14, g15, g16, g17, g18, g19]

theorem start_of_invL {C : Ctx} : ∀ {l : List Row}, rowsStart sy c.m l = true → ∀ {m : Machine}, InvL C l m → controllable sy m = true → Start sy c m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsStart, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact start_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact start_of_invL hl.2 h hc

/-- **A machine in the rows that has control has the state of `c.m`.** -/
theorem start_of_rows (hc : startCheck sy nm nx e A B c = true) {m : Machine} (h : InRows sy nm nx e A B m) (hm : controllable sy m = true) : Start sy c m := by
  simp only [startCheck, Bool.and_eq_true] at hc
  rcases h with h | h
  · exact start_of_invL hc.1.1 h hm
  · exact start_of_invL hc.1.2 h hm

/-- no machine in the pipe's frames has control -/
theorem no_ctl_during (hc : startCheck sy nm nx e A B c = true) {m : Machine} (h : During nm e m) : controllable sy m = false := by
  simp only [startCheck, Bool.and_eq_true] at hc
  have hl := leftOK_of_check hc.2
  have hp := inPipe_of_inv hl h
  simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at hp
  have hk := hl.keys
  simp only [PipeChangeBound.keysOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  cases hc2 : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc2
    exact hk.1 (hp.2.symm.trans hc2.2)

/-- **The state at control, on a real run**, from the conditions of the change: the condition at the entry, no Start on the game core's frames, the sound's pause bytes at the exit, and `left` not
0 before control. In the rows `left` is 0 only on the last row: there he has control, or the time is up. -/
theorem EndRun.start (S : Statement sy nm e es A B) (T : EndStatement sy nm nx e A B) (hc : startCheck sy nm nx e A B c = true) (R : EndRun sy nm nx e A B)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≠ 0) : Start sy c (R.seq R.b) := by
  have key : ∀ d, R.a + d ≤ R.b → St sy nm nx e A B (R.seq (R.a + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => Or.inl (T.during _ R.entry)
    | succ d ih =>
      intro hd
      have e1 : R.a + (d + 1) = R.a + d + 1 := rfl
      rw [e1, R.next (R.a + d)]
      have h1 := ih (by omega)
      have hn := R.next (R.a + d)
      have hq : ExitAt (exitBytes sy nm (refExit e A)) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) → SideChangeEnd.Quiet (quietBytes nx e A) (frame (R.seq (R.a + d)) (R.inp (R.a + d))) := by
        intro hx
        rw [← hn] at hx ⊢
        exact R.quiet _ (by omega) (by omega) hx
      rcases st_step S T h1 (R.noStart (R.a + d) (by omega) (by omega)) hq with g | ⟨g1, _⟩
      · exact absurd g (hf _ (by omega) (by omega))
      · exact g1
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := key (R.b - R.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · have := no_ctl_during hc (T.toDuring _ h)
    rw [R.atCtl] at this
    cases this
  · exact start_of_rows hc h R.atCtl

end Rows

/-! ## On real frames: a program, no part of the proof -/

/-- what `After` says, as a check (the three bytes that `AfterKeep.keepH` proves are checked by `keepHB`) -/
def afterB (sy : Syms) (a Q b : Machine) : Bool :=
  peek b sy.Player_X_MoveForce == peek Q sy.Player_X_MoveForce && peek b sy.PlayerFacingDir == peek Q sy.PlayerFacingDir &&
  peek Q sy.Player_XSpeedAbsolute == absB (peek Q sy.Player_X_Speed) &&
  ((posP sy b == posP sy Q && peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed && bitsOf sy b == 0xFF) ||
   (decide (0 < vOf sy Q) && posP sy b == posP sy Q && peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed && bitsOf sy b == sy.noLeft) ||
   (decide (vOf sy b ≤ 0) && (decide (posP sy b ≤ posP sy Q - 256) || decide (posP sy b ≤ SurfaceRead.baseOf sy a + 256))))

/-- what `AfterP` says, as a check -/
def afterPB (sy : Syms) (a Q b : Machine) : Bool :=
  !decide (0 < vOf sy Q) ||
    ((peek b sy.Player_X_Speed != peek Q sy.Player_X_Speed || posP sy b == posP sy Q) &&
     (peek b sy.Player_X_Speed != 0 || decide (posP sy b ≤ posP sy Q - 256) || decide (posP sy b ≤ posP sy a + 256)))

/-- round 28: the field `Moves.stop` as a check: a frame that moves right at the scroll handler, ends with the speed 0 and ends at the position there ends at most
1 px past `a` (`AfterP.stop` is the theorem `StopAt.stopP`; `afterPB` checks it); round 32: asked only when he is right of the screen's left edge at `Q`
or `a` is left of it (`OnFrames.stopAt`); round 33: and the side collision's timer is at least 2 at `b` (right of the edge at `Q`) or at `a` (`a` left of
it); `stopAtB` is the old field, a theorem -/
def stopB (sy : Syms) (m0 a Q b : Machine) : Bool :=
  !(decide (0 < vOf sy Q) && peek b sy.Player_X_Speed == 0 && posP sy b == posP sy Q &&
    -- round 33: right of the left edge at the scroll handler with the side collision's timer at the push's value at the end, or the start left of the edge
    -- with the timer at that value there
    ((decide (ScrollRule.left16 (ScrollRule.places sy m0) Q < EdgeStep.pixel16 sy Q) && b.ram.get! (ScrollRule.places sy m0).sideB == PushTimer.pushT sy m0) ||
      (decide (EdgeStep.pixel16 sy a < ScrollRule.left16 (ScrollRule.places sy m0) a) && a.ram.get! (ScrollRule.places sy m0).sideB == PushTimer.pushT sy m0))) ||
  decide (posP sy Q ≤ posP sy a + 256)

/-- round 33: what `OnFrames.stopRight` proves, as a check: a frame that moves right at the scroll handler, ends with the speed 0 at the position there and
with the side collision's timer not at the push's value, ends at the screen's left edge -/
def stopRightB (sy : Syms) (m0 Q b : Machine) : Bool :=
  !(decide (0 < vOf sy Q) && peek b sy.Player_X_Speed == 0 && posP sy b == posP sy Q && b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0) ||
  decide (EdgeStep.pixel16 sy b = ScrollRule.left16 (ScrollRule.places sy m0) b)

/-- round 33: what `OnFrames.leftEnd` proves, as a check: a frame that does not end with the side collision's timer at the push's value (and the left edge's page not 255) ends at
or right of the screen's left edge -/
def leftEndB (sy : Syms) (m0 b : Machine) : Bool :=
  !(b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0 && b.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) != 255) ||
  decide (ScrollRule.left16 (ScrollRule.places sy m0) b ≤ EdgeStep.pixel16 sy b)

/-- round 33: what `OnFrames.noStopRight` proves, as a check: no such frame is right of the left edge at the scroll handler -/
def noStopRightB (sy : Syms) (m0 Q b : Machine) : Bool :=
  !(decide (0 < vOf sy Q) && peek b sy.Player_X_Speed == 0 && posP sy b == posP sy Q && b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0 &&
    decide (ScrollRule.left16 (ScrollRule.places sy m0) Q < EdgeStep.pixel16 sy Q))

/-- round 32: the old field `Moves.stop` (`StopAt`, now the theorem `OnFrames.stopAt`) as a check -/
def stopAtB (sy : Syms) (a Q b : Machine) : Bool :=
  !(decide (0 < vOf sy Q) && peek b sy.Player_X_Speed == 0 && posP sy b == posP sy Q) || decide (posP sy Q ≤ posP sy a + 256)

/-- what `CollideS` says, as a check -/
def collideSB (sy : Syms) (M Q b : Machine) (calls : Bool) : Bool :=
  (peek b sy.Player_X_Speed != 0 || peek b sy.Player_X_MoveForce != 0 || peek Q sy.Player_X_MoveForce == 0) &&
  (!calls || decide (0 < sbyte (peek Q sy.Player_X_Speed)) && peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed ||
   posP sy b == posP sy Q || posP sy b == posP sy Q - 256 ||
    (decide (posP sy Q ≤ posP sy b) && decide (posP sy b ≤ SurfaceRead.baseOf sy M + 256) && decide (sbyte (peek Q sy.Player_X_Speed) ≤ 0)))

/-- what the old field `edge` of `OnFrames` (a theorem since round 26: `OnFrames.edgeAt`) says of the frame from `M` (the end of the frame before) to `b`, as a check -/
def edgeB (sy : Syms) (M b : Machine) : Bool :=
  decide (SurfaceRead.edgeOf sy b ≤ max (SurfaceRead.baseOf sy M) (posP sy b))

/-- the old field `near` at the scroll handler `Q` (`EdgeStep.NearX`, round 27; round 26: `EdgeStep.Near`; round 28: a theorem, `OnFrames.nearAt`), as a check -/
def nearB (sy : Syms) (m0 Q : Machine) : Bool :=
  let P := ScrollRule.places sy m0
  !(Q.ram.get! P.lockB == 0 && decide (P.thr1 ≤ Q.ram.get! P.pfs) && Q.ram.get! P.sideB == 0 && ScrollRule.xOK (ScrollRule.amountOf P Q)) ||
    decide (ScrollRule.left16 P Q + (Q.ram.get! P.xs).toNat + 2 ≤ EdgeStep.pixel16 sy Q)

/-- round 28: the field `nearA` at the first arrival at the player's routine `R` (`MoveScroll.NearA`; round 29: a theorem, `OnFrames.nearAAt`), as a check: when the side collision's timer and the scroll
lock are 0 and his place on the screen is at least the scroll's threshold, he is at least 2 px right of the screen's left edge -/
def nearAB (sy : Syms) (m0 R : Machine) : Bool :=
  let P := ScrollRule.places sy m0
  !(R.ram.get! P.sideB == 0 && R.ram.get! P.lockB == 0 && decide (P.thr1 ≤ R.ram.get! P.pfs)) ||
    decide (ScrollRule.left16 P R + 2 ≤ EdgeStep.pixel16 sy R)

/-- round 29: `SideTimer.NearM` on a machine (at the frame's start `M`, a theorem: `OnFrames.nearMAll`; round 30: at the frame's end too, `OnFrames.nearStepAt`; round 29: the field `nearStep` asked it at the frame's end when it held at
the start), as a check: when the side collision's timer is at most 1, the scroll lock is 0 and
his place on the screen is at least the scroll's threshold, he is at least 2 px right of the screen's left edge -/
def nearMB (sy : Syms) (m0 M : Machine) : Bool :=
  let P := ScrollRule.places sy m0
  !(decide (M.ram.get! P.sideB ≤ 1) && M.ram.get! P.lockB == 0 && decide (P.thr1 ≤ M.ram.get! P.pfs)) ||
    decide (ScrollRule.left16 P M + 2 ≤ EdgeStep.pixel16 sy M)

/-- round 30: the fields `rightRel` and `endKeep` as checks (round 31: `rightRel` is `RightEdge.Rel`, a theorem, and the page is `OnFrames.pageAll`; this check is no longer used) -/
def rightRelB (sy : Syms) (m0 R : Machine) : Bool :=
  let P := ClampSide.places sy m0
  ClampSide.edge16 P 1 R % 65536 == (ClampSide.edge16 P 0 R + 255) % 65536 && R.ram.get! (ClampSide.eP P 0) != 255
/-- round 31: `RightEdge.Rel` (a theorem: `OnFrames.relAll`, `RightEdge.scroll_rel`) and the left edge's page (a theorem: `OnFrames.pageAll`), as checks -/
def relB (sy : Syms) (m0 R : Machine) : Bool :=
  let P := ClampSide.places sy m0
  ClampSide.edge16 P 1 R % 65536 == (ClampSide.edge16 P 0 R + 255) % 65536
def leftPageB (sy : Syms) (m0 b : Machine) : Bool := b.ram.get! (ClampSide.eP (ClampSide.places sy m0) 0) != 255
def endKeepB (sy : Syms) (m0 : Machine) (b : Machine) : Bool :=
  let S := ScrollRule.places sy m0
  let P := ClampSide.places sy m0
  !(decide (b.ram.get! S.sideB ≤ 1) && b.ram.get! S.lockB == 0 && decide (S.thr1 ≤ b.ram.get! S.pfs)) ||
    (b.ram.get! S.pfs).toNat == (ClampSide.pix16 P b + 65536 - ClampSide.edge16 P 0 b) % 256
/-- round 32: what `PushTimer.pix_end` proves, as a check: when the frame ends at `b` with the side collision's timer at most 1, his pixel and his page there are
those of the scroll handler's return instruction `Rt` -/
def pixEndB (sy : Syms) (m0 : Machine) (Rt b : Machine) : Bool :=
  let S := ScrollRule.places sy m0
  !(decide (b.ram.get! S.sideB ≤ 1)) || ClampSide.pix16 (ClampSide.places sy m0) b == ClampSide.pix16 (ClampSide.places sy m0) Rt

/-- round 29: what `SideTimer.side_at` and `SideTimer.keep_at` prove, as a check: at the arrival `R` the side collision's timer is that of the frame's start `M`
or one less, and the place byte, the lock and the edge's two bytes are those of `M` -/
def sideAtB (sy : Syms) (m0 M R : Machine) : Bool :=
  let i := SideTimer.sideI sy m0
  (R.ram.get! i == M.ram.get! i || R.ram.get! i == M.ram.get! i - 1) && (SideTimer.startI sy m0).all fun x => R.ram.get! x == M.ram.get! x

/-- round 28: what `MoveScroll.move_xs` proves, as a check: at the scroll handler `Q`, when the byte the move stores is from 1 to 128, his pixel is that of the
arrival `R` plus that byte -/
def moveXsB (sy : Syms) (m0 R Q : Machine) : Bool :=
  let P := ScrollRule.places sy m0
  !ScrollRule.xOK (Q.ram.get! P.xs) || EdgeStep.pixel16 sy Q == EdgeStep.pixel16 sy R + (Q.ram.get! P.xs).toNat

/-- what `FaceKeep.keepZ_end` proves, as a check: the facing and the subspeed at the frame's end are those at the scroll handler, or the frame ends with the speed 0
and the subspeed 0 -/
def keepZB (sy : Syms) (Q b : Machine) : Bool :=
  (FaceKeep.zI sy).all fun x => b.ram.get! x == Q.ram.get! x || (peek b sy.Player_X_Speed == 0 && peek b sy.Player_X_MoveForce == 0)

/-- what `FaceKeep.bits_end` proves, as a check, on a frame from a clean state: if the speed's sign bit is 0 at the scroll handler, the frame ends with the collision
bits `FF` or those of a block of Left, or with the speed 0 -/
def bitsEndB (sy : Syms) (Q b : Machine) : Bool :=
  peek Q sy.Player_X_Speed &&& 0x80 != 0 || bitsOf sy b == 0xFF || bitsOf sy b == sy.noLeft || peek b sy.Player_X_Speed == 0

/-- what `AfterKeep.keepH` proves, as a check: the moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler -/
def keepHB (sy : Syms) (Q b : Machine) : Bool := (AfterKeep.hI sy).all fun x => b.ram.get! x == Q.ram.get! x

/-- what `BoxRun` says, as a check -/
def boxRunB (sy : Syms) (m0 : Machine) (B : Box) (a Q b : Machine) : Bool :=
  let u := vNext sy m0 a b
  let x := pix (posP sy Q)
  someSpeeds.any fun v =>
    let r := PoleJoin.noHitRun sy B.m x u.y v u.vy u.st
    decide (posP sy b - posP sy Q = 256 * ((peek r sy.Player_X_Position).toNat : Int) - 256 * (x.toNat : Int)) &&
      decide (sbyte (peek b sy.Player_X_Speed) - sbyte (peek Q sy.Player_X_Speed) = sbyte (peek r sy.Player_X_Speed) - sbyte v) &&
      peek b sy.Player_CollisionBits == peek r sy.Player_CollisionBits

/-- one real frame on the conditions of `OnFrames` -/
structure MovesScan where
  /-- the conditions of `Moves` that fail -/
  fails : List String
  /-- the condition of `box` if it fails -/
  boxFails : List String
  /-- the frame's end -/
  next : Machine
  /-- how often the frame comes to the scroll handler -/
  subs : Nat
  /-- the input the player's routine reads, if the frame comes to it -/
  inp : Option HIn := none
  /-- after the first scroll handler a byte of `vKeep` takes another value, at some instruction -/
  vMid : Bool := false
  /-- round 29, measured: `SideTimer.NearM` at the frame's start asks the bound and `MoveScroll.NearA` at the arrival does not (the timer at most 1 there, not 0) -/
  nearMore : Bool := false
  /-- round 35, measured: the frame comes to a store of `SideLoop.Resid` (from the scroll handler on) -/
  residAt : Bool := false
  /-- round 36, measured: the frame does not meet `SideAcross.FactsAt` (the two bytes at its start, or a store through an index or a pointer to one of them) -/
  factsBad : Bool := false
  /-- round 37, measured: the frame starts with the scroll lock not 0, and with the timers' control not 0 -/
  lockBad : Bool := false
  timerBad : Bool := false
  deriving Inhabited

/-- run the frame of `M` with the input `i` instruction by instruction, `a` the machine at the end of the counted frame before, and look at `Moves`, and at `box` if `box` -/
def movesScan (sy : Syms) (m0 : Machine) (B : Box) (a M : Machine) (i : UInt8) (box : Bool) : MovesScan := Id.run do
  let S := FrameModel.ctrlStack sy m0
  let t := M.frame + 1
  let mut c : Machine := { M with pad := smbToPad i }
  let mut n := 0
  let mut arr : Option (Nat × Machine) := none
  let mut subs : List Machine := []
  let mut vq : Option (List UInt8) := none
  let mut vMid := false
  let Pc := ScreenClamp.places sy m0
  let idxP := PositionWriters.posI sy
  let mut posWBad := false
  let mut sideWBad := false
  let mut sideWNearBad := false
  let mut sideWResBad := false
  let mut residAt := false
  let mut residBytes := false
  let mut castleBad := false
  let mut missBad := false
  let mut clampRBad := false
  let mut calls := false
  let CP := ClampSide.places sy m0
  let mut chks : List Machine := []
  let mut rets : List Machine := []
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if arr.isNone && c.pc == sy.PlayerCtrlRoutine then arr := some (n, c)
    -- round 36: `SideAcross.MissB` at each instruction of the frame
    if !SideAcross.missBB sy c then missBad := true
    if arr.isSome && c.pc == sy.PlayerSubs then
      subs := c :: subs
      if vq.isNone then vq := some ((vKeep sy).map (peek c ·))
    -- the fields `posW` and `clampR` of `OnFrames` at each instruction from the scroll handler on (`posW` as the stronger: no byte of the position written outside
    -- the push and the clamp)
    if !subs.isEmpty then
      if !PositionWriters.innerP sy m0 c.pc && idxP.any ((StepWrites.stepLocs c).contains ·) then posWBad := true
      -- round 32: the field `sideW`
      if !PushTimer.sideWB sy m0 c then sideWBad := true
      -- round 33: the field asks it only at the stores that may reach the timer
      if PushTimer.nearWB sy m0 c && !PushTimer.sideWB sy m0 c then sideWNearBad := true
      -- round 34: the field asks it only at the stores of `SideRange.Resid`; round 35: of `SideLoop.Resid`
      -- round 36: only on a frame without `SideAcross.FactsAt`; at the castle's loop's head the field `castleRow`
      if PushTimer.nearWB sy m0 c && SideLoop.residB sy c.pc (PipeWrites.opAt c) && !PushTimer.sideWB sy m0 c then sideWResBad := true
      if c.pc == sy.CRendLoop && decide (10 < c.x.toNat) then castleBad := true
      -- round 35, measured only: at the stores of `SideLoop.Resid`, the block buffer's column below 32, the control of the block objects' offset 0 or 1, and in
      -- the castle's loop of rows the row at most 10
      if PushTimer.nearWB sy m0 c && SideLoop.residB sy c.pc (PipeWrites.opAt c) then
        residAt := true
        if decide (32 ≤ peek c sy.BlockBufferColumnPos) || decide (2 ≤ peek c sy.SprDataOffset_Ctrl) ||
            (decide (sy.CRendLoop ≤ c.pc) && decide (c.pc < sy.ChkCFloor) && decide (10 < c.x)) then residBytes := true
      if c.pc == Pc.entry && decide (0 < sbyte (peek c sy.Player_X_Speed)) &&
          ScreenClamp.target (FrameModel.Rom.of m0) Pc c c.y != posP sy c then clampRBad := true
      if c.pc == sy.ImpedePlayerMove || c.pc == Pc.entry then calls := true
    if arr.isSome && c.pc == CP.chk then chks := c :: chks
    if arr.isSome && c.pc == CP.ret then rets := c :: rets
    if box then
      match vq with
      | some l => if (vKeep sy).map (peek c ·) != l then vMid := true
      | none => pure ()
    c := (PipeTransitionAll.go step c).2
    n := n + 1
  let b := c
  if arr.isSome && b.pc == sy.PlayerSubs then subs := b :: subs
  match arr with
  | none => return { fails := ["no arrival"], boxFails := [], next := b, subs := 0 }
  | some (n0, R) =>
    let mut f := (FrameModel.atFails sy S R).filter (· != "mask")
    if peek R sy.Player_CollisionBits != peek a sy.Player_CollisionBits then f := "bits" :: f
    if !(R.prg.data == m0.prg.data && R.prgMask == m0.prgMask && !R.halted && !R.trk && R.ram.size == 2048) then f := "good" :: f
    if !(FrameModel.hBytes sy).all (fun x => peek R x == peek a x) then f := "before" :: f
    if n ≤ n0 + FrameModel.moveLen then f := "longer" :: f
    if !(decide (2048 ≤ posP sy a) && decide (posP sy a + 2048 < 0x1000000)) then f := "far" :: f
    if subs.isEmpty then f := "no scroll handler" :: f
    if !subs.all (fun Q => afterB sy a Q b) then f := "after" :: f
    if !subs.all (fun Q => keepHB sy Q b) then f := "keepH" :: f
    if !subs.all (fun Q => afterPB sy a Q b) then f := "afterP" :: f
    if !subs.all (fun Q => stopB sy m0 a Q b) then f := "stop" :: f
    if !subs.all (fun Q => stopAtB sy a Q b) then f := "stopAt (a theorem)" :: f
    if !subs.all (fun Q => stopRightB sy m0 Q b) then f := "stopRight (a theorem)" :: f
    if !subs.all (fun Q => noStopRightB sy m0 Q b) then f := "noStopRight (a theorem)" :: f
    if !leftEndB sy m0 b then f := "leftEnd (a theorem)" :: f
    if posWBad then f := "posW" :: f
    let factsOK := SideAcross.invBB sy M && !missBad
    -- round 37: the old field `sideW` (gone: every frame of the route has `FactsAt`, from part f's fields), measured as before
    if sideWResBad && !factsOK && b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0 then f := "sideW" :: f
    if castleBad && b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0 then f := "castleRow" :: f
    if residBytes then f := "SideLoop's bytes (measured only)" :: f
    -- round 34: round 33's field, a theorem (`OnFrames.sideWAt`)
    if sideWNearBad && b.ram.get! (ScrollRule.places sy m0).sideB != PushTimer.pushT sy m0 then f := "sideWAt (a theorem)" :: f
    -- round 32: `SideW` on every frame (more than the field asks), for the page
    if sideWBad then f := "sideW on every frame (measured only)" :: f
    if clampRBad && subs.any (fun Q => decide (0 < sbyte (peek Q sy.Player_X_Speed)) && peek b sy.Player_X_Speed == peek Q sy.Player_X_Speed) then f := "clampR" :: f
    if !subs.all (fun Q => collideSB sy a Q b calls) then f := "collideS" :: f
    if !edgeB sy a b then f := "edge" :: f
    if !subs.all (fun Q => nearB sy m0 Q) then f := "near" :: f
    if !nearAB sy m0 R then f := "nearA (a theorem)" :: f
    if !nearMB sy m0 M then f := "nearM at the start (a theorem)" :: f
    if !nearMB sy m0 b then f := "nearStep (a theorem)" :: f
    if !(relB sy m0 M && chks.all (fun r => relB sy m0 r) && relB sy m0 b) then f := "right edge (a theorem)" :: f
    if !leftPageB sy m0 b then f := "leftPage (a theorem)" :: f
    if !endKeepB sy m0 b then f := "endKeep" :: f
    if !rets.all (fun r => pixEndB sy m0 r b) then f := "pix_end (a theorem)" :: f
    if !sideAtB sy m0 M R then f := "side timer (a theorem)" :: f
    if !subs.all (fun Q => moveXsB sy m0 R Q) then f := "move xs (a theorem)" :: f
    if !subs.all (fun Q => keepZB sy Q b) then f := "keepZ (a theorem)" :: f
    if !subs.all (fun Q => bitsEndB sy Q b) then f := "bits_end (a theorem)" :: f
    -- `Moves.state`, and what the walk of `CtrlKeep` proves: the `lag` frames keep `keepA` (`OnFrames.lagKeep`), the bytes at the routine
    if !(CtrlKeep.keepA sy).all (fun x => peek M x == peek a x) then f := "lag" :: f
    if !ctlStateB sy a then f := "state" :: f
    if !(CtrlKeep.keepA sy).all (fun x => peek R x == peek M x) then f := "walk: keepA at the routine" :: f
    let mut bf : List String := []
    if box then
      if subs.isEmpty then bf := ["no scroll handler"]
      if !subs.all (fun Q => boxRunB sy m0 B a Q b) then bf := "box" :: bf
      if !((vKeep sy).all (fun x => peek R x == peek a x) && (peek R sy.A_B_Buttons &&& 0x80) == (peek a sy.A_B_Buttons &&& 0x80) &&
          (peek R sy.PreviousA_B_Buttons &&& 0x80) == (peek R sy.A_B_Buttons &&& 0x80)) then bf := "vBefore" :: bf
      if !subs.all (fun Q => (vHard sy).all (fun x => peek b x == peek Q x)) then bf := "vAfter" :: bf
      if !subs.all (fun Q => (VertKeep.kI sy).all (fun x => b.ram.get! x == Q.ram.get! x)) then bf := "kAt (a theorem)" :: bf
      if !(decide (HaltOK sy a) && decide (HaltOK sy b)) then bf := "halt" :: bf
      if !subs.all (fun Q => peek b sy.Player_X_Speed != 0 || peek b sy.Player_X_MoveForce != 0 || peek b sy.PlayerFacingDir == peek Q sy.PlayerFacingDir) then
        bf := "faceJ" :: bf
    let P := ScrollRule.places sy m0
    let nearMore := decide (M.ram.get! P.sideB ≤ 1) && M.ram.get! P.lockB == 0 && decide (P.thr1 ≤ M.ram.get! P.pfs) && R.ram.get! P.sideB != 0
    -- round 37, measured: the scroll lock and the timers' control at the frame's start
    let lockBad := M.ram.get! P.lockB != 0
    let timerBad := peek M sy.TimerControl != 0
    return { fails := f, boxFails := bf, next := b, subs := subs.length, inp := some (FrameModel.readIn sy R), vMid, nearMore, residAt, factsBad := !factsOK, lockBad, timerBad }

end Smbrta.SurfaceFrames
