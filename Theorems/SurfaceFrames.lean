import Theorems.SurfaceRun
import Theorems.SideChangeEnd
import Theorems.FrameModel
import Theorems.VertModel
import Theorems.CtrlKeep
import Theorems.AfterKeep
import Theorems.GuardE
import Theorems.CollKeep
import Theorems.SurfaceRead

/-!
# Above ground: the frames from control, one by one

`PoleJoin.Run` used to assume statements about a whole run: `model` (up to the first hit the position is `hdist`), `hit`, `stop`, and `box`, `off` (no hit before frame `J`). Here they are
theorems. What stays is about one frame, read from the machines: `seq j` is the machine at the end of the counted frame `j`, so `seq 0` is the machine at control. `lag` frames are not counted (`Route.Run.clock`):
they can come between `seq j` and the frame `j + 1`, and they change none of the bytes read here (measured).

* The model's input of a frame is the one the player's routine reads (`inAt`); it is always in `Potential.inputs`. `readIn` reads it from the machines around the frame,
  for the programs.
* `Clean` is a condition on one state: the stored speed is `|v|`, and the collision bits block nothing, or only Left while he moves right.
* `OneFrame`: from a clean state, the frame is `hstep` up to the collision routine (`Pre`), and the routine leaves one of three things (`Coll`): nothing, a block of Left, or a hit.
  A hit (`Hit`) leaves a speed of at most 0, and `P` at most `P₂ − 256` or at most `P + 256`. The screen's left edge is a hit of the second kind.
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
  the rest of the state at the end of the frame before (`OnFrames.state`) and the rest of what the frame does from the scroll handler on (`OnFrames.collide`, and
  `AfterR` for the frames that move right there: `After.of`).
  A frame with the pressed side masked (`Masked`) is a `OneFrame` too: `FrameModel.move_masked` follows `hstep`, or leaves the speed 0 (`MaskStop`).
* `BoxRun`: the frames before `J` run the collision routine as on the machine at control, from the machine at the scroll handler, on its pixel and the height of `vstep`. The height comes from
  `vert_of`, one frame of `Jump.vstep` (the movement routine by `VertModel.vert_model`, the part before it by the walk of `CtrlKeep` (`vBefore`), the part after it by `OnFrames.vAfter`), and a small search (`vCheck`).
  The pixel comes from the distance bound (`dist_abs`).
* `frOf`: the frames as `TopSpeed.Frame`s are a definition on the machines: a frame before the touch is `SurfaceRead.frameE` of the real frame, the touch's frame
  `SurfaceRead.frameH`. From conditions on one frame or one machine (`OnFrames.state`, `collide`) each one is read from its machines
  (`OnFrames.reads`: `Reads`, the old field `reads`), so they follow each other by the definition (`next_of_reads`). The collision bits are one of the four values of
  `TopSpeed.collBits` at each frame's start (`OnFrames.collAll`: the walk of `CollKeep`, with the condition `spareC` on each instruction; the old field `coll`). The
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
structure Surface (sy : Syms) (m0 : Machine) (PA : Int) (T J g : Nat) (fr : Nat → Frame (top sy) (amax sy m0))
    (w : List HIn) (h : Nat) : Prop where
  mem : ∀ i ∈ w, i ∈ inputs
  long : T ≤ w.length
  /-- a first hit up to `T` comes before the touch -/
  range : h ≤ T → h < g
  /-- no hit before `J`: the frames before it stay in the box of `SurfaceRun.noHitCheck` -/
  first : J ≤ h
  model : ∀ j, 1 ≤ j → j < h → j ≤ T → j < g → (fr j).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take j)
  hit : h ≤ T → (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take h) - 256 ∨
    (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take (h - 1)) + 256
  stop : h ≤ T → (fr h).v' ≤ 0

/-- No hit before `J`. `surface_of_frames` proves it from the box (`SurfaceFrames.quiet_upto`); the arguments stay for the callers. -/
theorem first_of_surface {PA : Int} {m : Machine} {dx dy T J g : Nat} {fr : Nat → Frame (top sy) (amax sy m0)} {w : List HIn} {h : Nat}
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

/-- **A hit, on one frame.** The speed ends at most 0, and `P` ends 1 px behind the frame's move, or at most 1 px past where it began. The second kind is also the screen's left edge: he stops there
and `P` does not rise by more than a pixel's fraction. -/
def Hit (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy a + 16 * sbyte (modelS sy m0 a i).v - 256 ∨ posP sy b ≤ posP sy a + 256)

/-- What the collision routine leaves on a frame that is `hstep` before it: nothing; or the block of Left on a frame moving right, which changes nothing else; or a hit. -/
def Coll (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  (posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a i).v ∧ vOf sy b = sbyte (modelS sy m0 a i).v ∧ bitsOf sy b = 0xFF) ∨
  (0 < sbyte (modelS sy m0 a i).v ∧ posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a i).v ∧ vOf sy b = sbyte (modelS sy m0 a i).v ∧ bitsOf sy b = sy.noLeft) ∨
  Hit sy m0 i a b

/-- With Left blocked, a frame moving right can stop him: Left on the ground at a low speed stops a skid, and the blocked Left does not start him moving left. -/
def MaskStop (sy : Syms) (a b : Machine) : Prop :=
  bitsOf sy a = sy.noLeft ∧ vOf sy b ≤ 0 ∧ posP sy b ≤ posP sy a + 256

/-- **One frame from a clean state**, on the input `i`. -/
def OneFrame (sy : Syms) (m0 : Machine) (i : HIn) (a b : Machine) : Prop :=
  MaskStop sy a b ∨ (Pre sy m0 i a b ∧ Coll sy m0 i a b)

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
structure Reads (sy : Syms) (g : Nat) (seq : Nat → Machine) {tp am : Int} (fr : Nat → Frame tp am) : Prop where
  v : ∀ j, 1 ≤ j → j ≤ g → (fr j).v = vOf sy (seq (j - 1))
  f : ∀ j, 1 ≤ j → j ≤ g → (fr j).f = fOf sy (seq (j - 1))
  P : ∀ j, 1 ≤ j → j ≤ g → (fr j).P = posP sy (seq (j - 1))
  v' : ∀ j, 1 ≤ j → j < g → (fr j).v' = vOf sy (seq j)
  f' : ∀ j, 1 ≤ j → j < g → (fr j).f' = fOf sy (seq j)
  P' : ∀ j, 1 ≤ j → j < g → (fr j).P' = posP sy (seq j)

/-- The frames follow each other by the definition: both ends are read from the same machine. -/
theorem next_of_reads {g : Nat} {seq : Nat → Machine} {tp am : Int} {fr : Nat → Frame tp am} (R : Reads sy g seq fr) :
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

/-! ## The numbers -/

/-- how far the frames from `Φ ≤ p` move, either way. Moving left the speed's byte can be 1 below the bound on `V`. -/
def dl (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * (nxt sy m p / 256 + 1) + dl sy m (nxt sy m p) n

/-- the height and the fall of the box, as a check -/
def boxVB (sy : Syms) (B : Box) (t : Jump.VS) : Bool :=
  (t.y == (peek B.m sy.Player_Y_Position).toNat.toUInt8 && t.vy == 0 && t.st == 0) ||
    ((List.range (B.dy + 1)).any fun b => t.y == ((peek B.m sy.Player_Y_Position).toNat - b).toUInt8) && (SurfaceRun.vyStates sy).contains (t.vy, t.st)

/-- the next frames of the vertical bytes: A pressed or not, and every stored speed up to the top -/
def vNextAll (sy : Syms) (m0 : Machine) (l : List Jump.VS) : List Jump.VS :=
  (l.flatMap fun s => [true, false].flatMap fun a => (List.range (top sy + 1)).map fun ab => VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) s a ab.toUInt8).eraseDups

/-- `n` more frames from the states `l` stay in the box's height -/
def vCheck (sy : Syms) (m0 : Machine) (B : Box) : Nat → List Jump.VS → Bool
  | 0, _ => true
  | n + 1, l => (vNextAll sy m0 l).all (boxVB sy B) && vCheck sy m0 B n (vNextAll sy m0 l)

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
    vCheck sy m0 B (J - 1) [vsOf sy c] &&
    CtrlKeep.afterCheck sy m0 (peek c sy.AreaType) && [(1 : UInt8), 2, 3].contains (peek c sy.AreaType) && peek c sy.SwimmingFlag == 0 &&
    peek c sy.PlayerChangeSizeFlag == 0 && FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop &&
    PrevKeep.prevCheck sy m0 (peek c sy.AreaType) && PrevKeep.prevOKB sy c && AfterKeep.hCheck sy m0 (peek c sy.AreaType) &&
    FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) && CollKeep.collCheckAll sy m0 (peek c sy.AreaType)

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
  vert : vCheck sy m0 B (J - 1) [vsOf sy B.m] = true
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

theorem numbers_of_check {B : Box} {J : Nat} (h : numbersCheck sy m0 B J = true) : Numbers sy m0 B J := by
  simp only [numbersCheck, PrevKeep.prevOKB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, ha⟩, hm⟩, hk⟩, hb⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩ := h
  exact ⟨h0, ha, hm, hk, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, List.contains_iff_mem.1 h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

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
theorem vCheck_spec {B : Box} : ∀ (n : Nat) (l : List Jump.VS), vCheck sy m0 B n l = true → ∀ (u : Nat → Jump.VS) (a : Nat → Bool) (ab : Nat → UInt8), u 0 ∈ l →
    ∀ k, 1 ≤ k → k ≤ n → (∀ i, i < k → (ab i).toNat ≤ top sy ∧ u (i + 1) = VertModel.vstepV sy m0 (FrameModel.ctrlStack sy m0) (u i) (a i) (ab i)) →
      boxVB sy B (u k) = true
  | 0, _, _, _, _, _, _, _, h1, h2, _ => by omega
  | n + 1, l, h, u, a, ab, h0, k, h1, h2, hs => by
    simp only [vCheck, Bool.and_eq_true, List.all_eq_true] at h
    have hm : u 1 ∈ vNextAll sy m0 l := by
      obtain ⟨h3, h4⟩ := hs 0 (by omega)
      unfold vNextAll
      refine List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨u 0, h0, List.mem_flatMap.2 ⟨a 0, ?_, List.mem_map.2 ⟨(ab 0).toNat, List.mem_range.2 (by omega), ?_⟩⟩⟩)
      · cases a 0 <;> simp
      · rw [h4]
        simp
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
  rcases h with ⟨_, h1, h2⟩ | ⟨hP, hq | ⟨h0, hq⟩ | hH⟩
  · exact Or.inr ⟨h1, Or.inr h2⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hi hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inl h3)⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hi hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inr ⟨h3, by rw [h2]; exact h0⟩)⟩
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
changes neither the subspeed nor the facing, and the screen's edge and the collision routine leave one of three things: nothing, a block of Left moving right, or a hit. The
moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler: that is proved (`AfterKeep.keepH`, `AfterK`), no longer a
field here (`md`, `rs` are gone). The stored speed at the scroll handler is that of the speed there: proved too (`MovesAt.stored`, by `FrameModel.stored_path`), so the
field `storedQ` is gone. -/
structure After (sy : Syms) (a Q b : Machine) : Prop where
  f : peek b sy.Player_X_MoveForce = peek Q sy.Player_X_MoveForce
  fd : peek b sy.PlayerFacingDir = peek Q sy.PlayerFacingDir
  coll : (posP sy b = posP sy Q ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∧ bitsOf sy b = 0xFF) ∨
    (0 < vOf sy Q ∧ posP sy b = posP sy Q ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∧ bitsOf sy b = sy.noLeft) ∨
    (vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy Q - 256 ∨ posP sy b ≤ posP sy a + 256))

/-- **What `After` asks beyond `SurfaceRead.CollideE`** (the field `collide` of `OnFrames`, on every frame before the touch): the facing stays, and when he moves right at
the scroll handler, the screen's edge and the collision routine leave nothing, the block of Left, or a hit. When he moves left or not at all there, `CollideE` and the
move give `After.coll`; the subspeed is `CollideE.f` (`After.of`). This is the field `after` of `Moves` now: `After.f` and the half of `After.coll` for a speed of at most 0
are gone from it. -/
structure AfterR (sy : Syms) (a Q b : Machine) : Prop where
  fd : peek b sy.PlayerFacingDir = peek Q sy.PlayerFacingDir
  coll : 0 < vOf sy Q → (posP sy b = posP sy Q ∧ peek b sy.Player_X_Speed = peek Q sy.Player_X_Speed ∧ (bitsOf sy b = 0xFF ∨ bitsOf sy b = sy.noLeft)) ∨
    (vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy Q - 256 ∨ posP sy b ≤ posP sy a + 256))

/-- **`After` from `AfterR` and `CollideE`**, at a machine `Q` at the scroll handler that the move put at `P(a) + 16·v(Q)` -/
theorem After.of {a Q b : Machine} (h : AfterR sy a Q b) (c : SurfaceRead.CollideE sy a Q b) (hP : posP sy Q = posP sy a + 16 * vOf sy Q) : After sy a Q b := by
  refine ⟨c.f, h.fd, ?_⟩
  by_cases hv : 0 < vOf sy Q
  · rcases h.coll hv with ⟨e1, e2, e3 | e3⟩ | e
    · exact Or.inl ⟨e1, e2, e3⟩
    · exact Or.inr (Or.inl ⟨hv, e1, e2, e3⟩)
    · exact Or.inr (Or.inr e)
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
  /-- the rest of the frame, from the scroll handler: what `After` asks beyond `CollideE` -/
  after : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → AfterR sy a (trace M i k) (frame M i)
  /-- and `CollideE` there (the field `collide` of `OnFrames`) -/
  collide : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → SurfaceRead.CollideE sy a (trace M i k) (frame M i)
  /-- the moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler (`AfterKeep.keepH`) -/
  keepH : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → ∀ x ∈ AfterKeep.hI sy, (frame M i).ram.get! x = (trace M i k).ram.get! x
  /-- at the scroll handler the stored speed is that of the speed (`storedQ_of`, from `FrameModel.stored_path` and `AfterKeep.subs_once`) -/
  stored : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → peek (trace M i k) sy.Player_XSpeedAbsolute = absB (peek (trace M i k) sy.Player_X_Speed)

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
  exact ⟨n₀ + k, by omega, hpc, h1, hmove, After.of (h.after (n₀ + k) (by omega) hpc) (h.collide (n₀ + k) (by omega) hpc) hmove,
    h.keepH (n₀ + k) (by omega) hpc, h.stored (n₀ + k) (by omega) hpc⟩

/-- **A real frame is a `OneFrame`.** From the movement, proved, and the rest of the frame, `Moves`. -/
theorem one_of_moves (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (h : MovesAt sy m0 a M i n₀) (hm : ¬ Masked sy (inAt sy M i n₀) a) :
    Pre sy m0 (inAt sy M i n₀) a (frame M i) ∧ Coll sy m0 (inAt sy M i n₀) a (frame M i) := by
  obtain ⟨k, _, _, h1, h2, A⟩ := at_subs hOK h hm
  generalize trace M i k = Q at h1 h2 A
  generalize frame M i = b at h1 h2 A ⊢
  generalize inAt sy M i n₀ = u at h1 ⊢
  have ev : (modelS sy m0 a u).v = peek Q sy.Player_X_Speed := by rw [← h1]; rfl
  have ev2 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← h1]
    simp only [startHS, PState.read, A.after.f, A.after.fd, A.md, A.rs]
    rfl
  · rw [ev]
    exact A.stored
  · unfold Coll Hit
    rw [ev]
    rcases A.after.coll with ⟨c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c1, c2⟩
    · refine Or.inl ⟨by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩
    · refine Or.inr (Or.inl ⟨by omega, by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩)
    · exact Or.inr (Or.inr ⟨c1, by omega⟩)

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
  refine ⟨n₀ + k, by omega, hpc, ?_, hmove, ⟨After.of (h.after (n₀ + k) (by omega) hpc) (h.collide (n₀ + k) (by omega) hpc) hmove,
    h.keepH (n₀ + k) (by omega) hpc, h.stored (n₀ + k) (by omega) hpc⟩⟩
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
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← h1]
      simp only [startHS, PState.read, A.after.f, A.after.fd, A.md, A.rs]
      rfl
    · rw [ev]
      exact A.stored
    · unfold Coll Hit
      rw [ev]
      have ev2 : vOf sy Q = sbyte (peek Q sy.Player_X_Speed) := rfl
      rcases A.after.coll with ⟨c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c1, c2⟩
      · refine Or.inl ⟨by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩
      · refine Or.inr (Or.inl ⟨by omega, by omega, by show sbyte (peek b sy.Player_X_Speed) = _; rw [c2], c3⟩)
      · exact Or.inr (Or.inr ⟨c1, by omega⟩)
  · left
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
  /-- the rest of the frame, from the scroll handler: what `After` asks beyond `CollideE` (the subspeed and a speed of at most 0 are in the field `collide` of `OnFrames`) -/
  after : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → AfterR sy a (trace M i k) (frame M i)

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
Then the state at the end of the frame before (`hs`) and the rest of the frame (`Moves`) give the state at the player's routine (`MovesAt`). -/
theorem Moves.toAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true) (h0 : FrameKeep.StartK sy m0 M)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace M i n)) (hc : Clean sy a) (harr : Arrive sy M i n₀)
    (hlag : ∀ x ∈ CtrlKeep.keepA sy, peek M x = peek a x) (harea : peek a sy.AreaType ∈ [(1 : UInt8), 2, 3]) (hswim : peek a sy.SwimmingFlag = 0)
    (hsize : peek a sy.PlayerChangeSizeFlag = 0) (hfar : 2048 ≤ posP sy a ∧ posP sy a + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (hkh : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → ∀ x ∈ AfterKeep.hI sy, (frame M i).ram.get! x = (trace M i k).ram.get! x)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace M i k).pc = sy.PlayerSubs → (trace M i k').pc = sy.PlayerSubs → k = k')
    (hs : CtlState sy a) (hco : ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs → SurfaceRead.CollideE sy a (trace M i k) (frame M i))
    (h : Moves sy m0 a M i n₀) : MovesAt sy m0 a M i n₀ := by
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
  exact ⟨hat, fun x hx => kp x (keepA_mem (Or.inl hx)), hbits, harr.2.1, htime, hidle, hfar, h.after, hco, hkh,
    storedQ_of hOK hfr hso hat hc (kp _ (keepA_mem (Or.inl (by simp [FrameModel.hBytes])))) hbits harr.2.1 htime hidle honce⟩

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

/-- **The frames that the position's range covers**, from the machine `m`: each frame read from the machines moves him at most `16·top` right and `16·top + 256` left
(`OnFrames.readAll`), so for the first `farN` frames from `m` the position stays at least 8 px from both ends of its range. With the machine at control, 745 frames. -/
def farN (sy : Syms) (m : Machine) : Nat :=
  min ((posP sy m - 2048) / (16 * (top sy : Int) + 256)).toNat ((0x1000000 - 2049 - posP sy m) / (16 * (top sy : Int))).toNat

/-- **What the run assumes of its frames above ground, frame by frame.** The frames are those of `K` (`FrameKeep.Frames`, the field `keep` of `PoleJoin.Run`): `K.fm j`,
`K.pad j` are where the counted frame `j` begins on the real machine, the machine (`seq (j − 1)`, or later by `lag` frames) and the input, and `K.ends` says that it ends at
`seq j`. `CtrlKeep.arrAt` is the instruction at which it first comes to the player's routine: it does so, since it ends with the game not paused (`OnFrames.arrive`): a frame
is counted when it ends not paused (`FrameKeep.Frames`). The frames not counted end paused (`FrameKeep.Frames.down`), so they do not come to the player's routine
(`OnFrames.lagNo`, by the walk of the whole frame `area_endF`), and they keep the bytes the routine needs (`OnFrames.lagKeep`). Every frame keeps the area's type, the
swimming flag and the change of size (`OnFrames.areaAll`).
The frames as `TopSpeed.Frame`s are a definition on these machines (`frOf`), no longer data with a field `reads`: from `state`, `spareC` and `collide` each
frame up to the touch is read from its machines (`OnFrames.reads`), when the touch is not later than `farN` frames after control. -/
structure OnFrames (sy : Syms) (m0 : Machine) (B : Box) (T J g : Nat) (seq : Nat → Machine)
    {S : FrameKeep.RealRun} {a : Nat} (K : FrameKeep.Frames sy m0 S a g seq) where
  /-- the values at the end of the frame before, on every frame up to the touch: the player's state is 0, 1 or 2, and no jumpspring (the old `Moves.state`, which was
  asked on the frames from a clean state up to `T`) -/
  state : ∀ j, 1 ≤ j → j ≤ g → CtlState sy (seq (j - 1))
  /-- each instruction of each frame before the touch's frame, counted or not, meets `CollKeep.SpareC`: no store through an index or a pointer writes the collision
  bits. With it the collision bits at the end of each frame are one of the four values of `TopSpeed.collBits` (`OnFrames.collAll`; the old field `coll`). -/
  spareC : ∀ n, n + 1 < K.ix g → ∀ k, CollKeep.SpareC sy (PipeEntryRule.trace (K.all n) (K.inp n) k)
  /-- each frame before the touch, from the scroll handler on: the collision routine and the rest of the frame keep the subspeed, keep the speed or set it to 0, and keep
  the position, take 1 px off it, or push him right but not past 1 px right of the frame's start when he moves left or not at all (`SurfaceRead.CollideE`) -/
  collide : ∀ j, 1 ≤ j → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    SurfaceRead.CollideE sy (seq (j - 1)) (PipeEntryRule.trace (K.fm j) (K.pad j) k) (seq j)
  /-- a frame from a clean state: the parts outside the movement -/
  moves : ∀ j, 1 ≤ j → j ≤ T → j < g → Clean sy (seq (j - 1)) → Moves sy m0 (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))
  /-- the frames before `J`, from the scroll handler on: the rest of the frame leaves these bytes as they are there; he does not land on these frames -/
  vAfter : ∀ j, 1 ≤ j → j < J → j < g → ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k → (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    (∀ x ∈ vKeep sy, peek (seq j) x = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) x) ∧
    peek (seq j) sy.A_B_Buttons &&& 0x80 = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.A_B_Buttons &&& 0x80
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
`FrameKeep.Frames.noStore`; its condition on each instruction is `FrameKeep.Frames.cleanE` and `spareC`). It was the field `coll`. -/
theorem OnFrames.collAll (hck : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : CollKeep.collCheck sy m0 v = true) (hA : ∀ n, n < K.ix g → CtrlKeep.AreaOK sy v (K.all n))
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (h0 : CollKeep.CollOK sy (seq 0)) :
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
    exact CollKeep.coll_end hck hp (hst n (by omega)) (K.cleanE n (by show n < K.ix g; omega)) (O.spareC n hn) (K.noStore n hn) (hA n (by omega)) (ih (by omega))

theorem collCheckAll_parts {v : UInt8} (h : CollKeep.collCheckAll sy m0 v = true) : CollKeep.collCheck sy m0 v = true ∧ CollKeep.collBitsOK sy = true := by
  unfold CollKeep.collCheckAll at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- **The facts of the area's values and of the collision bits on the frames of `K`**, from the numbers of the machine at control (`Numbers`) and the state of the real
machine there (`Start`): `OnFrames.areaAll` and `OnFrames.collAll` -/
theorem OnFrames.areaRun {J' : Nat} (Nm : Numbers sy m0 B J') (O : OnFrames sy m0 B T J g seq K) (st : Start sy B (seq 0))
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) : AreaRun sy m0 K (peek B.m sy.AreaType) := by
  have hall := O.areaAll Nm.ctrl Nm.after hst ⟨st.area, st.swim.trans Nm.swim0, st.size.trans Nm.size0⟩
  obtain ⟨hcc, hcb⟩ := collCheckAll_parts Nm.coll
  have h0 : CollKeep.CollOK sy (seq 0) := by
    unfold CollKeep.CollOK
    rw [st.bits, Nm.bits]
    rfl
  exact ⟨Nm.after, Nm.area3, hall, Nm.keepH, O.collAll Nm.ctrl hcc hall hst h0, hcb⟩

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

/-- the state at the player's routine of the counted frame `j`, from a clean state: `Moves.toAt` with the frame's start in control (`hst`), `K.cleanAt`, `OnFrames.arrive`
and `OnFrames.lagKeep` -/
theorem OnFrames.movesAt (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ T) (h3 : j < g) (hc : Clean sy (seq (j - 1)))
    (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) :
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
  exact (O.moves j h1 h2 h3 hc).toAt hck hOK hfr hso (start_fm hst h1 (by omega)) (K.cleanAt j h1 (by omega)) hc harr (O.lagKeep hck hst Ar h1 (by omega))
    harea hA.2.1 hA.2.2 hfar hidle hkh honce (O.state j h1 (by omega))
    (fun k hk hpc => by have c := O.collide j h1 h3 k hk hpc; rwa [K.ends j h1 (by omega)] at c)

/-- **Each frame from a clean state is a `OneFrame`**, by the movement: `one_of_moves`, or with the side he presses masked `one_of_movesM`. -/
theorem one_of_frames (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hmk : FrameModel.maskOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ T) (h3 : j < g)
    (hc : Clean sy (seq (j - 1))) (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) :
    OneFrame sy m0 (O.inp j) (seq (j - 1)) (seq j) := by
  have hmv := O.movesAt hck hOK hfr hso hst Ar h1 h2 h3 hc hfar hidle
  by_cases hm : Masked sy (O.inp j) (seq (j - 1))
  · have e := one_of_movesM hOK hmk hmv hc hm
    rw [← O.ends j h1 h2 h3] at e
    exact e
  · have e := one_of_moves hOK hmv hm
    rw [← O.ends j h1 h2 h3] at e
    exact Or.inr e

/-- **The vertical step of a frame before `J`**: from the vertical model (`VertModel.vert_model`, proved), the state at the player's routine (`moves`, and the walk of
`CtrlKeep` for the vertical bytes up to there: `vBefore`, and bit 7 of A of the frame before: `OnFrames.prevAll`), and the frame's part from the scroll handler on (`vAfter`). In a jump the jump's halt value is 1 at the
frame's start, and so at its end. -/
theorem vert_of (hv : VertModel.vertOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hck : CtrlKeep.ctrlCheck sy m0 = true)
    (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (hso : FrameModel.storedOK sy m0 (FrameModel.ctrlStack sy m0) = true) (O : OnFrames sy m0 B T J g seq K)
    (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h2 : j < J) (hT : j ≤ T) (h3 : j < g)
    (hc : Clean sy (seq (j - 1))) (hfar : 2048 ≤ posP sy (seq (j - 1)) ∧ posP sy (seq (j - 1)) + 2048 < 0x1000000)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hh : HaltOK sy (seq (j - 1))) (hpv : PrevKeep.PrevOK sy (seq (j - 1))) :
    vsOf sy (seq j) = vNext sy m0 (seq (j - 1)) (seq j) ∧ HaltOK sy (seq j) := by
  have hmv := O.movesAt hck hOK hfr hso hst Ar h1 hT h3 hc hfar hidle
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
  obtain ⟨va1, va2⟩ := O.vAfter j h1 h2 h3 (O.arr j + k) (Nat.le_add_right _ _) hpc'
  rw [e0] at va1 va2
  have eb : vsOf sy (seq j) = VertModel.vsOf sy (FrameModel.stepN k R) := by
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = Jump.VS.mk _ _ _ _ _ _ _ _ _
    rw [va1 _ (.head _), va1 _ (.tail _ (.head _)), va1 _ (.tail _ (.tail _ (.head _))), va1 _ (.tail _ (.tail _ (.tail _ (.head _)))), va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), va2]
  have ea : VertModel.vsOf sy R = vsOf sy (seq (j - 1)) := by
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = Jump.VS.mk _ _ _ _ _ _ _ _ _
    rw [vb1 _ (.head _), vb1 _ (.tail _ (.head _)), vb1 _ (.tail _ (.tail _ (.head _))), vb1 _ (.tail _ (.tail _ (.tail _ (.head _)))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), vb1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), vb2]
  have eab : peek R sy.Player_XSpeedAbsolute = peek (seq (j - 1)) sy.Player_XSpeedAbsolute := by
    rw [hat.abs, hc.2.1, hv0]
  rw [ea, eab] at hvs
  refine ⟨?_, ?_⟩
  · have eA : (vsOf sy (seq j)).prevA = (peek R sy.SavedJoypadBits &&& 0x80 != 0) := by
      rw [eb, hvs, VertModel.vstepV_eq]
    unfold vNext
    rw [eA, eb, hvs]
  · intro e
    show peek (seq j) sy.DiffToHaltJump = 1
    rw [va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))]
    rw [va1 _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))] at e
    exact hhk e

/-! ### The frames as `TopSpeed.Frame`s, read from the machines -/

/-- **Frame `j` from control above ground, read from the machines** (it was the data `fr` of `PoleJoin.Run`, tied to the machines by the field `reads`). It starts with
the speed, the subspeed and the position of `seq (j − 1)`, by the definition. A frame before the touch is `SurfaceRead.frameE` of the real frame of `K`: the
`TopSpeed.Frame` of the real frame, which ends at `seq j`, when the frame meets `SurfaceRead.ReadE` (`OnFrames.reads` shows that it does). The touch's frame is
`SurfaceRead.frameH`: the real frame up to the scroll handler. -/
noncomputable def frOf (sy : Syms) (m0 : Machine) {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq) (j : Nat) :
    Frame (top sy) (amax sy m0) :=
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
    SurfaceRead.ReadE sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) ∧ SurfaceRead.Same sy (seq (j - 1)) (K.fm j) := by
  obtain ⟨hR, hS⟩ := O.readH hck hOK hfr hidle hst Ar h1 (by omega) hsp hfar
  refine ⟨{ toReadH := hR, collide := fun k hk hpc => ?_ }, hS⟩
  have c := O.collide j h1 h3 k hk hpc
  rw [K.ends j h1 (by omega)] at c
  exact c.ofP hS.P.symm

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

/-- **Each frame before the touch starts with a speed of at most the top**, and within the first `farN` frames the position stays within `(16·top + 256)·d` left and
`16·top·d` right of the machine at control: each frame before it is read as a `TopSpeed.Frame` (`OnFrames.readE`, `SurfaceRead.frameE_end`), which keeps the speed at most
the top (`Frame.bound`), moves him at most `16·top` right, and at most `16·top + 256` left (the move and `CollideE`). `hg`: the touch is not later than `farN` frames
after control, so every frame before it is one of the first `farN` (a later touch is `SurfaceLate`). `hv0`, `hP0`: the speed 0 and the position of `B.m` at control. -/
theorem OnFrames.readAll (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) :
    ∀ d, d < g → TopSpeed.inSpeed sy (peek (seq d) sy.Player_X_Speed) = true ∧
      (d < farN sy B.m → posP sy B.m - (16 * (top sy : Int) + 256) * (d : Int) ≤ posP sy (seq d) ∧ posP sy (seq d) ≤ posP sy B.m + 16 * (top sy : Int) * (d : Int)) := by
  have h16 : (16 : Int) ≤ (top sy : Int) := by
    have := (FrameModel.facts_of hOK).top16
    show (16 : Int) ≤ (TopSpeed.top sy : Int)
    omega
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨inSpeed_of (by have e : sbyte (peek (seq 0) sy.Player_X_Speed) = 0 := hv0; rw [e]; omega), fun _ => ?_⟩
    rw [hP0]
    simp
  | succ d ih =>
    intro hd
    obtain ⟨hsp, hr⟩ := ih (by omega)
    have hn : d < farN sy B.m := by omega
    have hfar : SurfaceRead.Far sy (seq d) := far_of_range hn (hr hn)
    obtain ⟨hR, hS⟩ := O.readE hck hOK hfr hidle hst Ar (j := d + 1) (by omega) hd (by simpa using hsp) (by simpa using hfar)
    have ev := SurfaceRead.frameE_v (sy := sy) m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1)))
    have eP := SurfaceRead.frameE_P (sy := sy) m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1)))
    obtain ⟨e1, _, e3, e4⟩ := SurfaceRead.frameE_end hR hS
    have hend := K.ends (d + 1) (by omega) (by omega)
    generalize SurfaceRead.frameE sy m0 (seq (d + 1 - 1)) (K.fm (d + 1)) (K.pad (d + 1)) (CtrlKeep.arrAt sy (K.fm (d + 1)) (K.pad (d + 1))) = c at ev eP e1 e3 e4
    rw [← hend] at e1 e3
    have e0 : d + 1 - 1 = d := rfl
    rw [e0] at ev eP
    have hv : -(top sy : Int) ≤ c.v ∧ c.v ≤ (top sy : Int) := by rw [ev]; exact FrameModel.speed_int hsp
    have hb := c.bound h16 hv
    have hv1 : -(top sy : Int) ≤ c.v₁ ∧ c.v₁ ≤ (top sy : Int) := by
      rcases c.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
    have hv2 := c.friction hv1
    have hm := c.move
    refine ⟨inSpeed_of ⟨by rw [← e1]; exact hb.1.1, by rw [← e1]; exact hb.1.2⟩, fun hn => ?_⟩
    obtain ⟨r1, r2⟩ := hr (by omega)
    have hmv : -16 * (top sy : Int) ≤ 16 * c.v₂ ∧ 16 * c.v₂ ≤ 16 * (top sy : Int) := by omega
    have c1 : ((d + 1 : Nat) : Int) = (d : Int) + 1 := by push_cast; rfl
    rw [c1, Int.mul_add, Int.mul_one, Int.mul_add, Int.mul_one]
    rw [← e3]
    rw [eP] at hm hb
    omega

/-- **A counted frame before the touch is read** (`SurfaceRead.ReadE`): the speed at its start is at most the top and its position away from the ends of its range
(`OnFrames.readAll`, with the touch not later than `farN` frames after control) -/
theorem OnFrames.readE_at (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) :
    SurfaceRead.ReadH sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) ∧ SurfaceRead.Same sy (seq (j - 1)) (K.fm j) ∧
      (j < g → SurfaceRead.ReadE sy m0 (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))) := by
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
    (st : Start sy B (seq 0)) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    (hfar : 2048 + 16 * (top sy : Int) * (T : Int) ≤ posP sy B.m ∧ posP sy B.m + 16 * (top sy : Int) * (T : Int) + 2048 < 0x1000000) :
    ∀ d, d + 1 < Jn → d + 1 < g → (∀ i, i ≤ d → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1))) ∧
      (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF ∧
      (∀ i, i ≤ d → vsOf sy (seq (i + 1)) = vNext sy m0 (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → HaltOK sy (seq i)) := by
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
      (hb : bitsOf sy (seq d) = 0xFF) (hvt : ∀ i, i < d → vsOf sy (seq (i + 1)) = vNext sy m0 (seq i) (seq (i + 1))) (hho : ∀ i, i ≤ d → HaltOK sy (seq i)) :
      (∀ i, i ≤ d → Follow sy m0 (O.inp (i + 1)) (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF ∧
      (∀ i, i ≤ d → vsOf sy (seq (i + 1)) = vNext sy m0 (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → HaltOK sy (seq i)) := by
    have hc' : Clean sy (seq (d + 1 - 1)) := by simpa using hcl d (Nat.le_refl d)
    have hnm : ¬ Masked sy (inAt sy (O.fm (d + 1)) (O.pad (d + 1)) (O.arr (d + 1))) (seq (d + 1 - 1)) := by
      have hb' : bitsOf sy (seq (d + 1 - 1)) = 0xFF := by simpa using hb
      unfold Masked
      rw [hb', ff_and]
      exact fun h => h rfl
    have Ar : AreaRun sy m0 K (peek B.m sy.AreaType) := O.areaRun Nm st hst
    have hfd : 2048 ≤ posP sy (seq (d + 1 - 1)) ∧ posP sy (seq (d + 1 - 1)) + 2048 < 0x1000000 := by
      simpa using far_of_follow F.pot Nm st hfar (fun j => inAt_mem Nm.model _ _ _) (d := d) (by omega) hf
    have hmv := O.movesAt Nm.ctrl Nm.model hfr Nm.storedW hst Ar (j := d + 1) (by omega) (by omega) h2 hc' hfd Nm.idle
    have hpv : PrevKeep.PrevOK sy (seq (d + 1 - 1)) := by
      have h0 : PrevKeep.PrevOK sy (seq 0) := by
        unfold PrevKeep.PrevOK
        rw [st.prev, st.ab]
        exact Nm.prev0
      have a1 := K.ix_mono d g (by omega) (Nat.le_refl g)
      rw [show d + 1 - 1 = d by omega, K.at_ix d (by omega)]
      exact O.prevAll Nm.ctrl Nm.prev Ar hst h0 (K.ix d) (by omega)
    have hvd := vert_of Nm.vmodel Nm.ctrl Nm.model hfr Nm.storedW O hst Ar (j := d + 1) (by omega) h1 (by omega) h2 hc' hfd Nm.idle (by simpa using hho d (Nat.le_refl d)) hpv
    simp only [Nat.add_sub_cancel] at hvd
    obtain ⟨hvd, hhd⟩ := hvd
    have hvt' : ∀ i, i ≤ d → vsOf sy (seq (i + 1)) = vNext sy m0 (seq i) (seq (i + 1)) := by
      intro i hi
      by_cases hid : i < d
      · exact hvt i hid
      · have : i = d := by omega
        subst this
        exact hvd
    have hend := O.ends (d + 1) (by omega) (by omega) h2
    have hP := (one_of_moves Nm.model hmv hnm).1
    rw [← hend] at hP
    obtain ⟨k, hk, hpc, h3, h4, _⟩ := at_subs Nm.model hmv hnm
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
      exact ⟨stored_le (hcl i (by omega)), hvt' i (by omega)⟩
    have hnext : vsOf sy (seq (d + 1)) = vNext sy m0 (seq d) (seq (d + 1)) := hvd
    obtain ⟨v, hv, hr⟩ := hbr
    rw [← hnext] at hr
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
    (O : OnFrames sy m0 B T Jn g seq K) (st : Start sy B (seq 0)) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) (hg : g ≤ farN sy B.m) :
    ∃ w h, Surface sy m0 (posP sy B.m) T Jn g (frOf sy m0 K) w h := by
  have Nm := numbers_of_check hn
  have Ar : AreaRun sy m0 K (peek B.m sy.AreaType) := O.areaRun Nm st hst
  have Rd := O.reads Nm.ctrl Nm.model hfr Nm.idle hst Ar (start_v0 hn st) st.P hg
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
    have ho := one_of_frames Nm.model Nm.mask hfr Nm.storedW Nm.ctrl O hst Ar h1 hT h2 (hclean hT) hfh Nm.idle
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
  refine ⟨wlist O.inp T, h, wlist_mem hin T, by rw [wlist_length]; omega, fun hT => (H2 hT).2.1, ?_, ?_, ?_, ?_⟩
  · -- no hit before `J`: the frames before it follow `hstep` into a clean state
    by_cases hT : h ≤ T
    · obtain ⟨h1, h2, h3⟩ := H2 hT
      by_cases hJ : Jn ≤ h
      · exact hJ
      · exfalso
        obtain ⟨d, rfl⟩ : ∃ d, h = d + 1 := ⟨h - 1, by omega⟩
        obtain ⟨hf, hcl, _⟩ := quiet_upto F hc Nm hfr (by omega) O st hst hfar d (by omega) h2
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
    rw [wlist_take hT, wlist_take (by omega), Rd.P' h h1 h2]
    rcases h3 with h3 | h3
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · -- `stop`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    rw [Rd.v' h h1 h2]
    exact (hhit hT).1

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

/-- a state of a row: it says whether it has control, and if it has, it knows the bytes of `Start`, with the values of the machine `c` -/
def rowStart (sy : Syms) (c : Machine) (S : AS) : Bool :=
  (ctlBytes sy).all (knowsAd S) && (!controllable sy (mOf S) || (startBytes sy).all fun a => knowsAd S a && peek (mOf S) a == peek c a)

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
  · simp only [startBytes, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h1
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
    refine ⟨?_, ?_, g9, g10, ?_, g20, g21, g22, g19, g23⟩
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
   (decide (vOf sy b ≤ 0) && (decide (posP sy b ≤ posP sy Q - 256) || decide (posP sy b ≤ posP sy a + 256))))

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
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if arr.isNone && c.pc == sy.PlayerCtrlRoutine then arr := some (n, c)
    if arr.isSome && c.pc == sy.PlayerSubs then
      subs := c :: subs
      if vq.isNone then vq := some ((vKeep sy).map (peek c ·))
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
      if !subs.all (fun Q => (vKeep sy).all (fun x => peek b x == peek Q x) && (peek b sy.A_B_Buttons &&& 0x80) == (peek Q sy.A_B_Buttons &&& 0x80)) then
        bf := "vAfter" :: bf
      if !(decide (HaltOK sy a) && decide (HaltOK sy b)) then bf := "halt" :: bf
    return { fails := f, boxFails := bf, next := b, subs := subs.length, inp := some (FrameModel.readIn sy R), vMid }

end Smbrta.SurfaceFrames
