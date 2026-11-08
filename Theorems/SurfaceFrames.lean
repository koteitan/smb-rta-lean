import Theorems.SurfaceRun
import Theorems.SideChangeEnd

/-!
# Above ground: the frames from control, one by one

`PoleJoin.Run` used to assume statements about a whole run: `model` (up to the first hit the position is `hdist`), `hit`, `stop`, and `box`, `off` (no hit before frame `J`). Here they are
theorems. What stays is about one frame, read from the machines: `seq j` is the machine at the end of the counted frame `j`, so `seq 0` is the machine at control. `lag` frames are not counted (`Route.Run.clock`):
they can come between `seq j` and the frame `j + 1`, and they change none of the bytes read here (measured).

* `readIn` reads the input of a frame from the machines around it, and it is always in `Potential.inputs`.
* `Clean` is a condition on one state: the stored speed is `|v|`, and the collision bits block nothing, or only Left while he moves right.
* `OneFrame`: from a clean state, the frame is `hstep` up to the collision routine (`Pre`), and the routine leaves one of three things (`Coll`): nothing, a block of Left, or a hit.
  A hit (`Hit`) leaves a speed of at most 0, and `P` at most `P₂ − 256` or at most `P + 256`. The screen's left edge is a hit of the second kind.
* `BoxRun`: the frames before `J` run the collision routine as on the machine at control, on the frame's own pixel and height. The height comes from `OnFrames.vert`, one frame of `Jump.vstep`, and a small
  search (`vCheck`). The pixel comes from the distance bound (`dist_abs`).
* `Reads`: the frames `fr` are read from the machines, so they follow each other by the definition (`next_of_reads`).

`surface_of_frames` derives `model`, `hit`, `stop`, `box`, `off` from these, with no search: it is the arithmetic of `go` and `hdist`.

The start: `SideChangeEnd` proves rows of states up to the frame of control. In its last row the machine at control has the horizontal state and the position of the machine of the private proof
(`startCheck`, `start_of_rows`, `EndRun.start`). So `startP`, `startV` are theorems on real machines, under the conditions of the change and the condition that `left` is not 0 before control.
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

/-- The frame `f` runs the collision routine as on the state `x y v vy st` of the machine `B.m`, `v` standing for the speed's sign: what it does to the position's pixel and to the speed, and
the collision bits `bit` it leaves, are the routine's. -/
def RunsAs (sy : Syms) (B : Box) (f : Frame tp am) (bit : UInt8) (x y v vy st : UInt8) : Prop :=
  (∃ base : Int, f.P₂ = base + 256 * (x.toNat : Int) ∧
      f.P' = base + 256 * ((peek (noHitRun sy B.m x y v vy st) sy.Player_X_Position).toNat : Int)) ∧
    f.v' - f.v₂ = sbyte (peek (noHitRun sy B.m x y v vy st) sy.Player_X_Speed) - sbyte v ∧
    bit = peek (noHitRun sy B.m x y v vy st) sy.Player_CollisionBits

/-- The real frame `f` runs the collision routine as on a state of the box. -/
def BoxFrame (sy : Syms) (B : Box) (f : Frame tp am) (bit : UInt8) : Prop :=
  ∃ x y v vy st : UInt8, InBox sy B x y v vy st ∧ RunsAs sy B f bit x y v vy st

/-- the collision routine did nothing on this frame: `bit` are the collision bits it leaves -/
def Quiet (f : Frame tp am) (bit : UInt8) : Prop := f.P' = f.P₂ ∧ f.v' = f.v₂ ∧ bit = 0xFF

/-- `noHitCheck` on the frames: a frame in the box is quiet -/
theorem quiet_of_box {B : Box} (hc : noHitCheck sy B.m B.dx B.dy = true) {f : Frame tp am} {bit : UInt8} (h : BoxFrame sy B f bit) :
    Quiet f bit := by
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
frames before the first hit `h` move as `hdist` says. A first hit is one of the kinds of `SurfaceRun.hit_bound`, and it leaves a speed of at most 0. `bits j` are the collision bits frame `j` leaves.
If he hits nothing up to `T` before the touch `g`, `h` is past `T`. This is a theorem now: `SurfaceFrames.surface_of_frames`. -/
structure Surface (sy : Syms) (m0 : Machine) (PA : Int) (B : Box) (T J g : Nat) (fr : Nat → Frame (top sy) (amax sy m0))
    (w : List HIn) (h : Nat) (bits : Nat → UInt8) : Prop where
  mem : ∀ i ∈ w, i ∈ inputs
  long : T ≤ w.length
  /-- a first hit up to `T` comes before the touch -/
  range : h ≤ T → h < g
  /-- the frames before `J` stay in the box of `SurfaceRun.noHitCheck` -/
  box : ∀ j, 1 ≤ j → j < J → j < g → BoxFrame sy B (fr j) (bits j)
  /-- he leaves the model because of the collision routine: it did something on a frame up to `h` -/
  off : h ≤ T → ∃ j, 1 ≤ j ∧ j ≤ h ∧ ¬ Quiet (fr j) (bits j)
  model : ∀ j, 1 ≤ j → j < h → j ≤ T → j < g → (fr j).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take j)
  hit : h ≤ T → (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take h) - 256 ∨
    (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take (h - 1)) + 256
  stop : h ≤ T → (fr h).v' ≤ 0

/-- No hit before `J`: the frames before it are in the box, and `noHitCheck` says nothing happens there. -/
theorem first_of_surface {PA : Int} {B : Box} {T J g : Nat} {fr : Nat → Frame (top sy) (amax sy m0)} {w : List HIn} {h : Nat} {bits : Nat → UInt8}
    (hc : noHitCheck sy B.m B.dx B.dy = true) (hJT : J ≤ T) (R : Surface sy m0 PA B T J g fr w h bits) : J ≤ h := by
  by_cases hT : h ≤ T
  · by_cases hJ : J ≤ h
    · exact hJ
    · exfalso
      obtain ⟨j, h1, h2, h3⟩ := R.off hT
      have := R.range hT
      exact h3 (quiet_of_box hc (R.box j h1 (by omega) (by omega)))
  · omega

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

/-- what `hstep` says of the frame from `a` to `b` -/
def modelS (sy : Syms) (m0 a b : Machine) : HS := hstep sy m0 (startHS sy a) (readIn sy a b)

/-- the frame from `a` to `b` follows `hstep` in the open area: the form of `RoomJoin.Follow`, with `fr.hs n = startHS (seq n)`, `fr.P n = posP (seq n)` and the input read -/
def Follow (sy : Syms) (m0 a b : Machine) : Prop :=
  readIn sy a b ∈ inputs ∧ startHS sy b = modelS sy m0 a b ∧ posP sy b = posP sy a + 16 * sbyte (startHS sy b).v

/-- Before the collision routine the frame is `hstep`: the routine can change only the speed. -/
def Pre (sy : Syms) (m0 a b : Machine) : Prop :=
  ({ startHS sy b with v := (modelS sy m0 a b).v } : HS) = modelS sy m0 a b ∧
    peek b sy.Player_XSpeedAbsolute = absB (modelS sy m0 a b).v

/-- **A hit, on one frame.** The speed ends at most 0, and `P` ends 1 px behind the frame's move, or at most 1 px past where it began. The second kind is also the screen's left edge: he stops there
and `P` does not rise by more than a pixel's fraction. -/
def Hit (sy : Syms) (m0 a b : Machine) : Prop :=
  vOf sy b ≤ 0 ∧ (posP sy b ≤ posP sy a + 16 * sbyte (modelS sy m0 a b).v - 256 ∨ posP sy b ≤ posP sy a + 256)

/-- What the collision routine leaves on a frame that is `hstep` before it: nothing; or the block of Left on a frame moving right, which changes nothing else; or a hit. -/
def Coll (sy : Syms) (m0 a b : Machine) : Prop :=
  (posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a b).v ∧ vOf sy b = sbyte (modelS sy m0 a b).v ∧ bitsOf sy b = 0xFF) ∨
  (0 < sbyte (modelS sy m0 a b).v ∧ posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a b).v ∧ vOf sy b = sbyte (modelS sy m0 a b).v ∧ bitsOf sy b = sy.noLeft) ∨
  Hit sy m0 a b

/-- With Left blocked, a frame moving right can stop him: Left on the ground at a low speed stops a skid, and the blocked Left does not start him moving left. -/
def MaskStop (sy : Syms) (a b : Machine) : Prop :=
  bitsOf sy a = sy.noLeft ∧ vOf sy b ≤ 0 ∧ posP sy b ≤ posP sy a + 256

/-- **One frame from a clean state.** -/
def OneFrame (sy : Syms) (m0 a b : Machine) : Prop :=
  MaskStop sy a b ∨ (Pre sy m0 a b ∧ Coll sy m0 a b)

/-- the frame's own pixel -/
def pix (P : Int) : UInt8 := (P / 256).toNat.toUInt8

/-- the vertical bytes of a machine, as `Jump.vstep` has them -/
def vsOf (sy : Syms) (m : Machine) : Jump.VS :=
  { y := peek m sy.Player_Y_Position, mf := peek m sy.Player_Y_MoveForce, vy := peek m sy.Player_Y_Speed, dummy := peek m sy.Player_YMF_Dummy, vf := peek m sy.VerticalForce,
    vfd := peek m sy.VerticalForceDown, origin := peek m sy.JumpOrigin_Y_Position, st := peek m sy.Player_State, prevA := (peek m sy.A_B_Buttons &&& 0x80) != 0 }

/-- what `Jump.vstep` says of the frame from `a` to `b`: A is read from `b`, the stored speed from `a` -/
def vNext (sy : Syms) (m0 a b : Machine) : Jump.VS :=
  Jump.vstep sy m0 (vsOf sy a) ((peek b sy.SavedJoypadBits &&& 0x80) != 0) (peek a sy.Player_XSpeedAbsolute)

/-- The frame runs the collision routine as on the machine at control, on its own pixel and the height that `vstep` gives, `v` standing for the speed's sign. -/
def BoxRun (sy : Syms) (m0 : Machine) (B : Box) (a b : Machine) {tp am : Int} (f : Frame tp am) : Prop :=
  ∃ v : UInt8, v ∈ someSpeeds ∧ RunsAs sy B f (bitsOf sy b) (pix f.P₂) (vNext sy m0 a b).y v (vNext sy m0 a b).vy (vNext sy m0 a b).st

instance (sy : Syms) (m : Machine) : Decidable (Clean sy m) := by unfold Clean; infer_instance
instance (sy : Syms) (m0 a b : Machine) : Decidable (Pre sy m0 a b) := by unfold Pre; infer_instance
instance (sy : Syms) (m0 a b : Machine) : Decidable (Hit sy m0 a b) := by unfold Hit; infer_instance
instance (sy : Syms) (m0 a b : Machine) : Decidable (Coll sy m0 a b) := by unfold Coll; infer_instance
instance (sy : Syms) (a b : Machine) : Decidable (MaskStop sy a b) := by unfold MaskStop; infer_instance
instance (sy : Syms) (m0 a b : Machine) : Decidable (OneFrame sy m0 a b) := by unfold OneFrame; infer_instance

/-- **The frames are read from the machines.** `fr j` begins with the bytes of `seq (j − 1)`, and it ends with those of `seq j` if it is before the touch: the touch moves him, and that is not a `Frame`. On a
clean frame with nothing blocked, its speed at the move is `hstep`'s. -/
structure Reads (sy : Syms) (m0 : Machine) (g : Nat) (seq : Nat → Machine) {tp am : Int} (fr : Nat → Frame tp am) : Prop where
  v : ∀ j, 1 ≤ j → j ≤ g → (fr j).v = vOf sy (seq (j - 1))
  f : ∀ j, 1 ≤ j → j ≤ g → (fr j).f = fOf sy (seq (j - 1))
  P : ∀ j, 1 ≤ j → j ≤ g → (fr j).P = posP sy (seq (j - 1))
  v' : ∀ j, 1 ≤ j → j < g → (fr j).v' = vOf sy (seq j)
  f' : ∀ j, 1 ≤ j → j < g → (fr j).f' = fOf sy (seq j)
  P' : ∀ j, 1 ≤ j → j < g → (fr j).P' = posP sy (seq j)
  mid : ∀ j, 1 ≤ j → j < g → Clean sy (seq (j - 1)) → bitsOf sy (seq (j - 1)) = 0xFF → (fr j).v₂ = sbyte (modelS sy m0 (seq (j - 1)) (seq j)).v

/-- The frames follow each other by the definition: both ends are read from the same machine. -/
theorem next_of_reads {g : Nat} {seq : Nat → Machine} {tp am : Int} {fr : Nat → Frame tp am} (R : Reads sy m0 g seq fr) :
    ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1)) := by
  intro j h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [R.v (j + 1) (by omega) (by omega), R.v' j h1 h2, Nat.add_sub_cancel]
  · rw [R.f (j + 1) (by omega) (by omega), R.f' j h1 h2, Nat.add_sub_cancel]
  · rw [R.P (j + 1) (by omega) (by omega), R.P' j h1 h2, Nat.add_sub_cancel]

/-- **What the run assumes of its frames above ground, frame by frame.** -/
structure OnFrames (sy : Syms) (m0 : Machine) (B : Box) (T J g : Nat) (seq : Nat → Machine) (fr : Nat → Frame (top sy) (amax sy m0)) : Prop where
  reads : Reads sy m0 g seq fr
  /-- each frame from a clean state -/
  step : ∀ j, 1 ≤ j → j ≤ T → j < g → Clean sy (seq (j - 1)) → OneFrame sy m0 (seq (j - 1)) (seq j)
  /-- the frames before `J` are one step of `vstep`: he does not land on these frames -/
  vert : ∀ j, 1 ≤ j → j < J → j < g → vsOf sy (seq j) = vNext sy m0 (seq (j - 1)) (seq j)
  /-- the frames before `J` run the collision routine as on the machine at control -/
  box : ∀ j, 1 ≤ j → j < J → j < g → BoxRun sy m0 B (seq (j - 1)) (seq j) (fr j)

/-- **The state at control**: the horizontal state, the position, the stored speed, the collision bits and the vertical bytes of the machine `B.m`. -/
structure Start (sy : Syms) (B : Box) (m : Machine) : Prop where
  hs : startHS sy m = startHS sy B.m
  P : posP sy m = posP sy B.m
  stored : peek m sy.Player_XSpeedAbsolute = peek B.m sy.Player_XSpeedAbsolute
  bits : peek m sy.Player_CollisionBits = peek B.m sy.Player_CollisionBits
  vs : vsOf sy m = vsOf sy B.m

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
  (l.flatMap fun s => [true, false].flatMap fun a => (List.range (top sy + 1)).map fun ab => Jump.vstep sy m0 s a ab.toUInt8).eraseDups

/-- `n` more frames from the states `l` stay in the box's height -/
def vCheck (sy : Syms) (m0 : Machine) (B : Box) : Nat → List Jump.VS → Bool
  | 0, _ => true
  | n + 1, l => (vNextAll sy m0 l).all (boxVB sy B) && vCheck sy m0 B n (vNextAll sy m0 l)

/-- the machine at control is stopped, clean, and the frames before `J` stay within `dx` px and in the box's height -/
def numbersCheck (sy : Syms) (m0 : Machine) (B : Box) (J : Nat) : Bool :=
  let c := B.m
  inD sy (startHS sy m0) && decide (startHS sy c = startHS sy m0) && decide (sbyte (peek c sy.Player_X_Speed) = 0) &&
    peek c sy.Player_XSpeedAbsolute == absB (peek c sy.Player_X_Speed) && peek c sy.Player_CollisionBits == 0xFF && sy.noLeft != 0xFF &&
    decide (B.dx ≤ (peek c sy.Player_X_Position).toNat) &&
    ((List.range J).all fun j => decide (dl sy m0 (Opening.pOf sy m0 (startHS sy m0)) j ≤ 256 * (B.dx : Int))) &&
    vCheck sy m0 B (J - 1) [vsOf sy c]

/-- what `numbersCheck` says -/
structure Numbers (sy : Syms) (m0 : Machine) (B : Box) (J : Nat) : Prop where
  hD : inD sy (startHS sy m0) = true
  hs : startHS sy B.m = startHS sy m0
  v0 : sbyte (peek B.m sy.Player_X_Speed) = 0
  stored : peek B.m sy.Player_XSpeedAbsolute = absB (peek B.m sy.Player_X_Speed)
  bits : peek B.m sy.Player_CollisionBits = 0xFF
  noLeft : sy.noLeft ≠ 0xFF
  dx : B.dx ≤ (peek B.m sy.Player_X_Position).toNat
  dist : ∀ j, j < J → dl sy m0 (Opening.pOf sy m0 (startHS sy m0)) j ≤ 256 * (B.dx : Int)
  vert : vCheck sy m0 B (J - 1) [vsOf sy B.m] = true

theorem numbers_of_check {B : Box} {J : Nat} (h : numbersCheck sy m0 B J = true) : Numbers sy m0 B J := by
  simp only [numbersCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

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
    ∀ k, 1 ≤ k → k ≤ n → (∀ i, i < k → (ab i).toNat ≤ top sy ∧ u (i + 1) = Jump.vstep sy m0 (u i) (a i) (ab i)) → boxVB sy B (u k) = true
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

variable {a b : Machine}

/-- a frame that is `hstep` before the collision routine and that the routine leaves the speed of -/
theorem follow_of_pre (hP : Pre sy m0 a b) (hv : vOf sy b = sbyte (modelS sy m0 a b).v) (hp : posP sy b = posP sy a + 16 * sbyte (modelS sy m0 a b).v) : Follow sy m0 a b := by
  have e : peek b sy.Player_X_Speed = (modelS sy m0 a b).v := sbyte_inj hv
  have h1 : startHS sy b = modelS sy m0 a b := by
    have h2 := hP.1
    rwa [with_v (s := startHS sy b) (by rw [hs_v]; exact e)] at h2
  refine ⟨readIn_mem sy a b, h1, ?_⟩
  rw [hp, h1]

/-- a frame that follows `hstep` from a clean state leaves a clean state, if its bits are -/
theorem clean_of_follow (F : Facts sy m0) (hc : Clean sy a) (hf : Follow sy m0 a b) (hP : Pre sy m0 a b)
    (hb : bitsOf sy b = 0xFF ∨ (bitsOf sy b = sy.noLeft ∧ 0 < vOf sy b)) : Clean sy b := by
  have h1 := hf.2.1
  refine ⟨?_, ?_, hb⟩
  · rw [h1]
    exact (FastTakeoff.step_facts F hc.1 hf.1).1
  · have e : peek b sy.Player_X_Speed = (modelS sy m0 a b).v := by
      rw [← hs_v, h1]
    rw [e]
    exact hP.2

/-- **One frame from a clean state**: it follows `hstep` and leaves a clean state, or it is a hit. -/
theorem step_of_one (F : Facts sy m0) (hc : Clean sy a) (h : OneFrame sy m0 a b) :
    (Follow sy m0 a b ∧ Clean sy b) ∨ Hit sy m0 a b := by
  rcases h with ⟨_, h1, h2⟩ | ⟨hP, hq | ⟨h0, hq⟩ | hH⟩
  · exact Or.inr ⟨h1, Or.inr h2⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inl h3)⟩
  · obtain ⟨h1, h2, h3⟩ := hq
    have hf := follow_of_pre hP h2 h1
    exact Or.inl ⟨hf, clean_of_follow F hc hf hP (Or.inr ⟨h3, by rw [h2]; exact h0⟩)⟩
  · exact Or.inr hH

end Step

/-! ## From the frames to the whole run -/

section Run

variable {B : Box} {T Jn g : Nat} {seq : Nat → Machine} {fr : Nat → Frame (top sy) (amax sy m0)}

/-- the inputs of the first `n` frames -/
def wlist (sy : Syms) (seq : Nat → Machine) (n : Nat) : List HIn := (List.range n).map fun k => readIn sy (seq k) (seq (k + 1))

theorem wlist_succ (n : Nat) : wlist sy seq (n + 1) = wlist sy seq n ++ [readIn sy (seq n) (seq (n + 1))] := by
  simp [wlist, List.range_succ]

theorem wlist_length (n : Nat) : (wlist sy seq n).length = n := by simp [wlist]

theorem wlist_mem (n : Nat) : ∀ i ∈ wlist sy seq n, i ∈ inputs := by
  intro i hi
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hi
  exact readIn_mem sy _ _

theorem wlist_take {n j : Nat} (h : j ≤ n) : (wlist sy seq n).take j = wlist sy seq j := by
  unfold wlist
  rw [← List.map_take, List.take_range]
  rw [Nat.min_eq_left h]

/-- following `hstep`, the state and the position are those of `go` -/
theorem go_wlist : ∀ n, (∀ i, i < n → Follow sy m0 (seq i) (seq (i + 1))) →
    go sy m0 (startHS sy (seq 0), posP sy (seq 0)) (wlist sy seq n) = (startHS sy (seq n), posP sy (seq n))
  | 0, _ => rfl
  | n + 1, h => by
    have ih := go_wlist n (fun i hi => h i (by omega))
    have hf := h n (by omega)
    rw [wlist_succ, FastTakeoff.go_append, ih]
    show adv sy m0 (startHS sy (seq n), posP sy (seq n)) (readIn sy (seq n) (seq (n + 1))) = _
    unfold adv
    simp only
    have e : hstep sy m0 (startHS sy (seq n)) (readIn sy (seq n) (seq (n + 1))) = startHS sy (seq (n + 1)) := hf.2.1.symm
    rw [e, hf.2.2]

/-- the position after frames that follow `hstep` -/
theorem pos_wlist (n : Nat) (h : ∀ i, i < n → Follow sy m0 (seq i) (seq (i + 1))) :
    posP sy (seq n) = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist sy seq n) := by
  have h1 := go_wlist (m0 := m0) (seq := seq) n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m0) (wlist sy seq n) (startHS sy (seq 0), posP sy (seq 0))
  rw [h1] at h2
  exact h2

/-- the frame after frames that follow `hstep`: its move is the next step of the distance -/
theorem pos_next (n : Nat) (h : ∀ i, i < n → Follow sy m0 (seq i) (seq (i + 1))) :
    posP sy (seq n) + 16 * sbyte (modelS sy m0 (seq n) (seq (n + 1))).v = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist sy seq (n + 1)) := by
  have h1 := go_wlist (m0 := m0) (seq := seq) n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m0) (wlist sy seq (n + 1)) (startHS sy (seq 0), posP sy (seq 0))
  rw [wlist_succ, FastTakeoff.go_append, h1] at h2
  rw [wlist_succ]
  exact h2

/-- the state at control is clean -/
theorem clean_start (Nm : Numbers sy m0 B Jn) (st : Start sy B (seq 0)) : Clean sy (seq 0) := by
  have e : peek (seq 0) sy.Player_X_Speed = peek B.m sy.Player_X_Speed := by
    rw [← hs_v, ← hs_v, st.hs]
  refine ⟨by rw [st.hs, Nm.hs]; exact Nm.hD, by rw [st.stored, e]; exact Nm.stored, Or.inl ?_⟩
  show peek (seq 0) sy.Player_CollisionBits = 0xFF
  rw [st.bits, Nm.bits]

/-- a quiet frame from a clean state with nothing blocked follows `hstep`, and leaves a clean state with nothing blocked -/
theorem fc_of_quiet (F : Facts sy m0) (hN : sy.noLeft ≠ 0xFF) (O : Reads sy m0 g seq fr) {j : Nat} (h1 : 1 ≤ j) (h2 : j < g)
    (hc : Clean sy (seq (j - 1))) (hb : bitsOf sy (seq (j - 1)) = 0xFF) (ho : OneFrame sy m0 (seq (j - 1)) (seq j))
    (hq : Quiet (fr j) (bitsOf sy (seq j))) : Follow sy m0 (seq (j - 1)) (seq j) ∧ Clean sy (seq j) := by
  have hP : Pre sy m0 (seq (j - 1)) (seq j) := by
    rcases ho with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact absurd (h3.symm.trans hb) hN
    · exact h3
  have hm := O.mid j h1 h2 hc hb
  have hv : vOf sy (seq j) = sbyte (modelS sy m0 (seq (j - 1)) (seq j)).v := by
    rw [← O.v' j h1 h2, hq.2.1, hm]
  have hp : posP sy (seq j) = posP sy (seq (j - 1)) + 16 * sbyte (modelS sy m0 (seq (j - 1)) (seq j)).v := by
    rw [← O.P' j h1 h2, hq.1, (fr j).move, O.P j h1 (by omega), hm]
  have hf := follow_of_pre hP hv hp
  exact ⟨hf, clean_of_follow F hc hf hP (Or.inl hq.2.2)⟩

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

/-- The frames before `J` are quiet, and they follow `hstep`. -/
theorem quiet_upto (F : TFacts sy m0) (hc : noHitCheck sy B.m B.dx B.dy = true) (Nm : Numbers sy m0 B Jn) (hJT : Jn ≤ T + 1) (O : OnFrames sy m0 B T Jn g seq fr)
    (st : Start sy B (seq 0)) :
    ∀ d, d + 1 < Jn → d + 1 < g → BoxFrame sy B (fr (d + 1)) (bitsOf sy (seq (d + 1))) ∧ (∀ i, i ≤ d → Follow sy m0 (seq i) (seq (i + 1))) ∧
      (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF := by
  have hb0 : bitsOf sy (seq 0) = 0xFF := by
    show peek (seq 0) sy.Player_CollisionBits = 0xFF
    rw [st.bits, Nm.bits]
  intro d
  induction d with
  | zero =>
    intro h1 h2
    exact one_frame 0 h1 h2 (fun i hi => by omega) (fun i hi => by rw [show i = 0 by omega]; exact clean_start Nm st) hb0
  | succ d ih =>
    intro h1 h2
    obtain ⟨_, h3, h4, h5⟩ := ih (by omega) (by omega)
    exact one_frame (d + 1) h1 h2 (fun i hi => h3 i (by omega)) h4 h5
where
  one_frame (d : Nat) (h1 : d + 1 < Jn) (h2 : d + 1 < g) (hf : ∀ i, i < d → Follow sy m0 (seq i) (seq (i + 1))) (hcl : ∀ i, i ≤ d → Clean sy (seq i)) (hb : bitsOf sy (seq d) = 0xFF) :
      BoxFrame sy B (fr (d + 1)) (bitsOf sy (seq (d + 1))) ∧ (∀ i, i ≤ d → Follow sy m0 (seq i) (seq (i + 1))) ∧ (∀ i, i ≤ d + 1 → Clean sy (seq i)) ∧ bitsOf sy (seq (d + 1)) = 0xFF := by
    have hc' : Clean sy (seq (d + 1 - 1)) := by simpa using hcl d (Nat.le_refl d)
    have hb' : bitsOf sy (seq (d + 1 - 1)) = 0xFF := by simpa using hb
    have ho := O.step (d + 1) (by omega) (by omega) h2 hc'
    -- the frame's pixel is near the start
    have hm := O.reads.mid (d + 1) (by omega) h2 hc' hb'
    have hP₂ : (fr (d + 1)).P₂ = posP sy (seq 0) + hdist sy m0 (startHS sy (seq 0)) (wlist sy seq (d + 1)) := by
      rw [(fr (d + 1)).move, O.reads.P (d + 1) (by omega) (by omega), hm]
      simp only [Nat.add_sub_cancel]
      exact pos_next d hf
    have hd0 : startHS sy (seq 0) = startHS sy m0 := by rw [st.hs, Nm.hs]
    have hdist1 := dist_abs F.pot (wlist sy seq (d + 1)) (startHS sy m0) (Opening.pOf sy m0 (startHS sy m0)) (Opening.J_pOf Nm.hD) (wlist_mem _)
    rw [wlist_length] at hdist1
    have hdl := Nm.dist (d + 1) h1
    rw [hd0] at hP₂
    -- the height is in the box
    have hvs : boxVB sy B (vsOf sy (seq (d + 1))) = true := by
      refine vCheck_spec (Jn - 1) [vsOf sy B.m] Nm.vert (fun i => vsOf sy (seq i)) (fun i => (peek (seq (i + 1)) sy.SavedJoypadBits &&& 0x80) != 0) (fun i => peek (seq i) sy.Player_XSpeedAbsolute)
        (by simp only [List.mem_singleton]; exact st.vs) (d + 1) (by omega) (by omega) (fun i hi => ?_)
      refine ⟨stored_le (hcl i (by omega)), ?_⟩
      have := O.vert (i + 1) (by omega) (by omega) (by omega)
      simpa [vNext] using this
    have hnext : vsOf sy (seq (d + 1)) = vNext sy m0 (seq (d + 1 - 1)) (seq (d + 1)) := O.vert (d + 1) (by omega) h1 h2
    obtain ⟨v, hv, hr⟩ := O.box (d + 1) (by omega) h1 h2
    rw [← hnext] at hr
    have hy := boxV_of_B hvs
    have hx0 : (peek B.m sy.Player_X_Position).toNat < 256 := (peek B.m sy.Player_X_Position).toNat_lt
    have hmf := (peek B.m sy.SprObject_X_MoveForce).toNat_lt
    have hPA : posP sy (seq 0) = 256 * ((((peek B.m sy.Player_PageLoc).toNat * 256 + (peek B.m sy.Player_X_Position).toNat : Nat)) : Int) + ((peek B.m sy.SprObject_X_MoveForce).toNat : Int) := by
      rw [st.P]
      unfold posP
      omega
    obtain ⟨a, ha, hpx⟩ := pix_near (X := (peek B.m sy.Player_PageLoc).toNat * 256 + (peek B.m sy.Player_X_Position).toNat) (x0 := (peek B.m sy.Player_X_Position).toNat)
      (pg := (peek B.m sy.Player_PageLoc).toNat) (dx := B.dx) (P := (fr (d + 1)).P₂) (by omega) Nm.dx (by rw [hP₂, hPA]; omega) (by rw [hP₂, hPA]; omega)
    have hbf : BoxFrame sy B (fr (d + 1)) (bitsOf sy (seq (d + 1))) :=
      ⟨pix (fr (d + 1)).P₂, _, v, _, _, ⟨⟨a, ha, hpx⟩, hv, hy⟩, hr⟩
    have hq := quiet_of_box hc hbf
    obtain ⟨h5, h6⟩ := fc_of_quiet F.pot Nm.noLeft O.reads (j := d + 1) (by omega) h2 hc' hb' ho hq
    refine ⟨hbf, fun i hi => ?_, fun i hi => ?_, hq.2.2⟩
    · by_cases hid : i < d
      · exact hf i hid
      · have : i = d := by omega
        subst this
        simpa using h5
    · by_cases hid : i ≤ d
      · exact hcl i hid
      · have : i = d + 1 := by omega
        subst this
        exact h6

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

/-- **The statements about the whole run follow from the frames.** `model`, `hit`, `stop`, `box`, `off`, with no search. `h` is the first frame up to `T` before the touch that does not follow `hstep`
into a clean state. -/
theorem surface_of_frames (F : TFacts sy m0) (hc : noHitCheck sy B.m B.dx B.dy = true) (hn : numbersCheck sy m0 B Jn = true) (hJT : Jn ≤ T)
    (O : OnFrames sy m0 B T Jn g seq fr) (st : Start sy B (seq 0)) :
    ∃ w h, Surface sy m0 (posP sy B.m) B T Jn g fr w h fun j => bitsOf sy (seq j) := by
  have Nm := numbers_of_check hn
  have hd0 : startHS sy (seq 0) = startHS sy m0 := by rw [st.hs, Nm.hs]
  let FC : Nat → Prop := fun j => Follow sy m0 (seq (j - 1)) (seq j) ∧ Clean sy (seq j)
  -- the first frame that fails, or a frame past `T`
  have hfirst : ∃ h, (∀ j, 1 ≤ j → j < h → j ≤ T → j < g → FC j) ∧ (h ≤ T → 1 ≤ h ∧ h < g ∧ ¬ FC h) := by
    rcases exists_first FC (min T (g - 1)) with h | ⟨h0, h1, h2, h3, h4⟩
    · exact ⟨T + 1, fun j h1 _ h3 h5 => h j h1 (by omega), fun h1 => by omega⟩
    · exact ⟨h0, fun j h5 h6 _ _ => h4 j h5 h6, fun _ => ⟨h1, by omega, h3⟩⟩
  obtain ⟨h, H1, H2⟩ := hfirst
  have hfol : ∀ n, n < h → n ≤ T → n < g → ∀ i, i < n → Follow sy m0 (seq i) (seq (i + 1)) := by
    intro n h1 h2 h3 i hi
    have := (H1 (i + 1) (by omega) (by omega) (by omega) (by omega)).1
    simpa using this
  have hbox : ∀ j, 1 ≤ j → j < Jn → j < g → BoxFrame sy B (fr j) (bitsOf sy (seq j)) := by
    intro j h1 h2 h3
    obtain ⟨d, rfl⟩ : ∃ d, j = d + 1 := ⟨j - 1, by omega⟩
    exact (quiet_upto F hc Nm (by omega) O st d h2 h3).1
  -- the state before the first failure is clean
  have hclean : h ≤ T → Clean sy (seq (h - 1)) := by
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    by_cases h0 : h = 1
    · subst h0
      exact clean_start Nm st
    · exact (H1 (h - 1) (by omega) (by omega) (by omega) (by omega)).2
  have hhit : h ≤ T → Hit sy m0 (seq (h - 1)) (seq h) := by
    intro hT
    obtain ⟨h1, h2, h3⟩ := H2 hT
    have ho := O.step h h1 hT h2 (hclean hT)
    rcases step_of_one F.pot (hclean hT) ho with h4 | h4
    · exact absurd h4 h3
    · exact h4
  have hposn : h ≤ T → posP sy (seq (h - 1)) = posP sy B.m + hdist sy m0 (startHS sy m0) (wlist sy seq (h - 1)) ∧
      posP sy (seq (h - 1)) + 16 * sbyte (modelS sy m0 (seq (h - 1)) (seq h)).v = posP sy B.m + hdist sy m0 (startHS sy m0) (wlist sy seq h) := by
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    have hf : ∀ i, i < h - 1 → Follow sy m0 (seq i) (seq (i + 1)) := hfol (h - 1) (by omega) (by omega) (by omega)
    have e1 := pos_wlist (m0 := m0) (seq := seq) (h - 1) hf
    have e2 := pos_next (m0 := m0) (seq := seq) (h - 1) hf
    rw [hd0, st.P] at e1 e2
    rw [show h - 1 + 1 = h by omega] at e2
    exact ⟨e1, e2⟩
  refine ⟨wlist sy seq T, h, wlist_mem T, by rw [wlist_length]; omega, fun hT => (H2 hT).2.1, hbox, ?_, ?_, ?_, ?_⟩
  · -- `off`
    intro hT
    obtain ⟨h1, h2, h3⟩ := H2 hT
    by_cases hq : Quiet (fr h) (bitsOf sy (seq h))
    · -- the frame before it left a block, or the frame itself is not quiet
      by_cases h0 : h = 1
      · subst h0
        exfalso
        apply h3
        exact fc_of_quiet F.pot Nm.noLeft O.reads (by omega) h2 (clean_start Nm st) (by show peek (seq 0) sy.Player_CollisionBits = 0xFF; rw [st.bits, Nm.bits])
          (O.step 1 (by omega) hT h2 (clean_start Nm st)) hq
      · by_cases hb : bitsOf sy (seq (h - 1)) = 0xFF
        · exfalso
          apply h3
          exact fc_of_quiet F.pot Nm.noLeft O.reads h1 h2 (hclean hT) hb (O.step h h1 hT h2 (hclean hT)) hq
        · exact ⟨h - 1, by omega, by omega, fun hq2 => hb hq2.2.2⟩
    · exact ⟨h, h1, by omega, hq⟩
  · -- `model`
    intro j h1 h2 h3 h4
    have hf := hfol j h2 h3 h4
    have e1 := pos_wlist (m0 := m0) (seq := seq) j hf
    rw [hd0, st.P] at e1
    rw [wlist_take h3, O.reads.P' j h1 h4, e1]
    omega
  · -- `hit`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    obtain ⟨_, h3⟩ := hhit hT
    obtain ⟨e1, e2⟩ := hposn hT
    rw [wlist_take hT, wlist_take (by omega), O.reads.P' h h1 h2]
    rcases h3 with h3 | h3
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · -- `stop`
    intro hT
    obtain ⟨h1, h2, _⟩ := H2 hT
    rw [O.reads.v' h h1 h2]
    exact (hhit hT).1

/-- at control he is stopped at the machine's position -/
theorem start_P (O : OnFrames sy m0 B T Jn g seq fr) (hg : 1 ≤ g) (st : Start sy B (seq 0)) : (fr 1).P = posP sy B.m := by
  rw [O.reads.P 1 (by omega) hg]
  exact st.P

theorem start_v (hn : numbersCheck sy m0 B Jn = true) (O : OnFrames sy m0 B T Jn g seq fr) (hg : 1 ≤ g) (st : Start sy B (seq 0)) : (fr 1).v = 0 := by
  have Nm := numbers_of_check hn
  rw [O.reads.v 1 (by omega) hg]
  show sbyte (peek (seq 0) sy.Player_X_Speed) = 0
  rw [← hs_v, st.hs, hs_v]
  exact Nm.v0

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
   sy.JumpOrigin_Y_Position, sy.Player_State, sy.A_B_Buttons]

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
    obtain ⟨⟨k1, e1⟩, ⟨k2, e2⟩, ⟨k3, e3⟩, ⟨k4, e4⟩, ⟨k5, e5⟩, ⟨k6, e6⟩, ⟨k7, e7⟩, ⟨k8, e8⟩, ⟨k9, e9⟩, ⟨k10, e10⟩, ⟨k11, e11⟩, ⟨k12, e12⟩, ⟨k13, e13⟩, ⟨k14, e14⟩, ⟨k15, e15⟩, ⟨k16, e16⟩, ⟨k17, e17⟩, ⟨k18, e18⟩, ⟨k19, e19⟩⟩ := h1
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
    refine ⟨?_, ?_, g9, g10, ?_⟩
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

end Smbrta.SurfaceFrames
