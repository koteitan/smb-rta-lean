import Theorems.FastTakeoff
import Theorems.AirCap
import Theorems.SidePipe
import Theorems.FrameModel

/-!
# Joining the bonus room

`RoomRun` is what a real run in the room gives: real machines, frames of which `FrameModel.clean_frame` proves that they follow `hstep`, or that leave him stopped, the takeoff before the first frame
past the block's right end, the jump's frames in the vertical routine, how he leaves the block, and the entry frame. `entry_ge`
proves, from it and the checks of the earlier theorems, that the entry comes at least `goalF + aboveF` frames after first control.
Page: `1-1/c-5-RoomJoin.md`.

The arcs are hypotheses: that real frames follow `vstep` is not proved. What follows from them is proved
here, with the theorems of `AirCap`, `FastTakeoff` and `Jump`. Most fields are about one frame: the input and the height of a frame, standing, what the
left wall does to a frame, the stored speed, the entry. From these and small checks: before `hitF` he is left of the corner (`corner_late`), his feet are
low by the earliest jump (`low_by`), with no wall hit he stays on the floor up to an early takeoff (`floor_low`), `RunningSpeed` is 0 at a stop by `runF` or
he is far back (`run_short`), the entry is at the mouth (`mouth_at`).

The case split, all by `cases` and `by_cases`:
* over the block in one jump (no landing): impossible, `no_landing`;
* onto the block, with a stop from `hitF` on (a hit at the corner on the floor or in the air, a fast jump with a stale speed after a
  hit, a jump from the side of the block): short of the goal, `stop_short`;
* with no such stop, after a wall hit before `hitF`: short of the goal, whatever he does, `wall_short`. It looks at no jump, so a run that stands on the wall
  and never touches the floor is in it;
* with no such stop and no wall hit, onto the block: a takeoff after the last one searched (top speed), or a slow takeoff (air speed cap), or a fast
  takeoff (the search of `FastTakeoff`), `landed_short`;
* then off the block by a fast jump, a slow jump or stepping off, `entry_ge`.
-/

namespace Smbrta.RoomJoin

open Potential
open TopSpeed (top speedsB bytes)
open FastTakeoff (Room bonusRoom cornerP goalP roomCheck rightOk leftOk Takeoff AirIn GndIn JmpIn TFacts Pos Ent Cov Low go adv airI)
open AirCap (capped isAir CFacts capDist step_cap landing_bound landing_later)
open Jump (Arc VS vstep arcStart arcSucc arcCheck arc_spec arc_k arcStart_k groundY standY cornerY windowOk dropOk walkOk walkFrames
  forces falling arcFrames)

/-! ## The numbers -/

/-- the numbers of a room, in frames from first control -/
structure Nums where
  /-- the fall: this many air frames, the last one lands on the floor -/
  fall : Nat
  /-- the search of `FastTakeoff` covers takeoffs up to this many ground frames after the fall -/
  lastG : Nat
  /-- the frames after the takeoff frame with the feet low, in every jump from the floor -/
  rise : Nat
  /-- the frame at which he must be past the block's right end for an earlier entry -/
  goalF : Nat
  /-- before this frame he is not at the corner -/
  hitF : Nat
  /-- `RunningSpeed` is 0 up to this frame -/
  runF : Nat
  /-- what a frame that does not follow `hstep` leaves: the bound on `Φ`, and how far past the corner `P` can be -/
  stopPhi : Int
  stopSlack : Int
  /-- how far past the corner `P` can be while his feet are low -/
  lowSlack : Int
  /-- rows of the block above the floor -/
  h : Nat
  /-- the heights a jump can start from below the block's top: the floor, and the side of the block -/
  heights : List Nat
  /-- onto the block: (last low frame, frame on it), from the takeoff frame -/
  slow : List (Nat × Nat)
  fast : List (Nat × Nat)
  /-- off the block: frames to the floor after the last frame above it, slow and fast; air frames of a slow jump; stepping off -/
  aboveS : Nat
  aboveF : Nat
  airS : Nat
  walk : Nat
  /-- the longest jump from the floor, slow and fast; from any of those heights; from the block -/
  lenS : Nat
  lenF : Nat
  lenA : Nat
  lenB : Nat
  /-- a frame stopped at the left wall starts and ends at or left of `wallP`; the state after the first one is at or after frame `wallF` -/
  wallP : Int
  wallF : Nat
  /-- at the end of the fall, a state with `Φ ≤ safeP` does not reach the running threshold by frame `runF - 1` -/
  safeP : Int
  /-- frames counted back from the end of the fall, when he moves left fast then -/
  backK : Nat
  /-- with `RunningSpeed` not 0 at a stop by frame `runF`, the position is at most this -/
  backP : Int
  /-- after a wall hit, from the last frame stopped by the wall: from frame `wallD` on, the potential alone is enough. Before it, at the end of
  the fall: `Φ ≤ fastQ`, or he moves left and `wallK` air frames took him back -/
  wallD : Nat
  fastQ : Int
  wallK : Nat
  /-- the frames about standing are stated up to here -/
  standF : Nat
  /-- two stands in the fall are at least this many frames apart: before a stand he moves left at `standV` or more, and he is at or left of `standP` -/
  gapF : Nat
  standV : Int
  standP : Int
  /-- at first control: the height and the downward speed are at most these, and the force of the fall -/
  startY : Int
  startW : Int
  fallF : Nat
  /-- `(j, k)`: after a stand on frame `j` with no jump, he is not on the floor for `k` more frames -/
  gaps : List (Nat × Nat)
  deriving Repr, Inhabited

/-- the room of `FastTakeoff`, with these numbers -/
def room (sy : Syms) (N : Nums) : Room := bonusRoom sy N.fall N.lastG N.rise (N.goalF - N.fall)

/-! ## The frames of a run -/

/-- position, horizontal state and input by frame: `inp (n + 1)` is the input of frame `n + 1`, and `hs (n + 1)`, `P (n + 1)` are
the state and the position at its end -/
structure Frames where
  hs : Nat → HS
  inp : Nat → HIn
  P : Nat → Int
  /-- the vertical state at the end of frame `n`, and A on frame `n` -/
  vs : Nat → VS
  a : Nat → Bool
  /-- `Player_XSpeedAbsolute` at the end of frame `n`: the stored speed, which a jump reads -/
  ab : Nat → Nat

/-- frame `n + 1` follows `hstep` in the open area -/
def Follow (sy : Syms) (m : Machine) (fr : Frames) (n : Nat) : Prop :=
  fr.inp (n + 1) ∈ inputs ∧ fr.hs (n + 1) = hstep sy m (fr.hs n) (fr.inp (n + 1)) ∧
    fr.P (n + 1) = fr.P n + 16 * sbyte (fr.hs (n + 1)).v

/-- at the end of frame `n` he is slow, and not far past the corner. This is what a hit leaves (the speed is 0), and also the
frames right after a hit that do not follow `hstep`: the stored speed is stale, or the side is masked -/
def Stop (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop :=
  inD sy (fr.hs n) = true ∧ phi sy m (fr.hs n) ≤ N.stopPhi ∧ fr.P n ≤ cornerP sy + N.stopSlack

/-- what the collision routine gives at a frame with the feet low: not far past the corner; and he is stopped, or left of the corner,
or moving left (then the routine does not stop him) -/
def LowAt (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop :=
  fr.P n ≤ cornerP sy + N.lowSlack ∧ (Stop sy m N fr n ∨ fr.P n < cornerP sy ∨ sbyte (fr.hs n).v < 0)

/-- frame `i + 1` of a slow jump that does not follow `hstep`: he still moves at most the air speed. A hit from the block's right
side pushes him 1 px, only if he is moving left or stopped -/
def Moved (sy : Syms) (fr : Frames) (i : Nat) : Prop :=
  capped sy (fr.hs (i + 1)) = true ∧ inD sy (fr.hs (i + 1)) = true ∧
    fr.P (i + 1) ≤ fr.P i + 16 * ((sy.AirFastSpeed.toNat : Int) - 1)

/-- how he gets past the block's right end at frame `t0`, ending on the floor at frame `F` if nothing stops him. A stop or a landing
on the way only delays the floor, so `F` is at or before the entry frame `E` -/
inductive Off (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 E : Nat) : Type where
  /-- a jump from the block: frame `T1 + 1` is the takeoff frame, `n` frames later he reaches the floor. At `t0 - 1` he is above
  the block, or standing on it right before the jump -/
  | jump (T1 n F : Nat) (x u : Arc)
      (T1_ge : C ≤ T1)
      (x_mem : x ∈ arcStart sy m (standY sy N.h) N.h)
      (reach : Cert.Reach (arcSucc sy m N.h) x n u)
      (floor : falling u.s = true ∧ groundY sy ≤ u.s.y.toNat)
      (hF : F = T1 + 1 + n)
      (F_le : F ≤ E)
      (above : t0 + u.above ≤ F + 1)
      (slowJ : x.fast = false → F = E → capped sy (fr.hs T1) = true ∧
        ∀ i, T1 ≤ i → i < F → (Follow sy m fr i ∧ isAir (fr.inp (i + 1)) = true) ∨ Moved sy fr i) :
      Off sy m N fr C t0 E
  /-- stepping off: `t0` is the frame that walks past the end; then he falls with the fall force `f` and the carried fraction `d` -/
  | step (F : Nat) (f d : UInt8)
      (f_mem : f ∈ forces sy m)
      (hF : t0 + walkFrames sy m N.h f d ≤ F)
      (F_le : F ≤ E) :
      Off sy m N fr C t0 E

/-- he passes over the block in one jump, from the floor or from the side of the block: the jump still runs at frame `t0` -/
structure Over (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 : Nat) : Type where
  /-- the takeoff frame is `T1 + 1` -/
  T1 : Nat
  y0 : Nat
  x : Arc
  u : Arc
  T1_ge : C ≤ T1
  T1_lt : T1 < t0
  y0_mem : y0 ∈ N.heights
  x_mem : x ∈ arcStart sy m y0 N.h
  reach : Cert.Reach (arcSucc sy m N.h) x (t0 - (T1 + 1)) u
  /-- he stays in the air, except for stops -/
  air : ∀ n, T1 ≤ n → n < t0 → isAir (fr.inp (n + 1)) = true ∨ Stop sy m N fr (n + 1)
  /-- a slow jump reads a stored speed below the threshold, and the stored speed is at least `|v|` -/
  slowC : x.fast = false → capped sy (fr.hs T1) = true
  /-- at the takeoff he is not far past the corner -/
  start : fr.P T1 ≤ cornerP sy + N.stopSlack
  /-- at the threshold or more he took off from the floor: his feet stay low -/
  low : capped sy (fr.hs T1) = false → y0 = groundY sy ∧
    ∀ n, T1 + 1 ≤ n → n ≤ T1 + 1 + N.rise → n ≤ t0 → fr.P n ≤ cornerP sy + N.lowSlack

/-- he stands on the floor -/
def OnFloor (sy : Syms) (s : VS) : Prop := s.st = 0 ∧ s.y.toNat = groundY sy

/-- no frame before `hitF` is stopped -/
def NoWall (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C : Nat) : Prop :=
  ∀ n, C ≤ n → n + 1 < C + N.hitF → Follow sy m fr n

/-- frame `n + 1` is stopped at the left wall: he is near it before and after the frame, and `RunningSpeed` is 0 -/
structure WallAt (N : Nums) (fr : Frames) (n : Nat) : Prop where
  before : fr.P n ≤ N.wallP
  after : fr.P (n + 1) ≤ N.wallP
  run : (fr.hs (n + 1)).rs = 0

/-- the height with its fraction -/
def VY (s : VS) : Int := 256 * (s.y.toNat : Int) + (s.dummy.toNat : Int)
/-- the downward speed with its fraction -/
def VW (s : VS) : Int := 256 * (s.vy.toNat : Int) + (s.mf.toNat : Int)

/-- what a frame with no jump does to the height, from a state that is not in a jump: the speed is added to the height, the force to the
speed. A landing only lowers them -/
structure VDrop (s t : VS) : Prop where
  st : t.st ≠ 1
  y_le : VY t ≤ VY s + VW s
  w_le : VW t ≤ VW s + (s.vfd.toNat : Int)
  vfd : t.vfd = s.vfd

/-- what frame `n + 1` does to the height. Standing on the floor he stays or takes off; in the air, the frame is the vertical routine's,
unless he is falling (then it may land). The last case is standing anywhere else -/
inductive VFrame (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (n : Nat) : Prop where
  | stay (h1 : OnFloor sy (fr.vs n)) (h2 : OnFloor sy (fr.vs (n + 1))) (hi : GndIn (fr.inp (n + 1))) : VFrame sy m N fr n
  | takeoff (h1 : OnFloor sy (fr.vs n)) (x : Arc) (hx : x ∈ arcStart sy m (groundY sy) N.h) (h2 : fr.vs (n + 1) = x.s)
      (hi : JmpIn (fr.inp (n + 1))) : VFrame sy m N fr n
  | air (h1 : (fr.vs n).st ≠ 0) (h2 : fr.vs (n + 1) = vstep sy m (fr.vs n) (fr.a (n + 1)) 0) (hi : AirIn (fr.inp (n + 1))) :
      VFrame sy m N fr n
  | fall (h1 : (fr.vs n).st ≠ 0) (h2 : falling (vstep sy m (fr.vs n) (fr.a (n + 1)) 0) = true) : VFrame sy m N fr n
  | other (h1 : ¬OnFloor sy (fr.vs n)) (h2 : (fr.vs n).st = 0) : VFrame sy m N fr n

/-- a fast takeoff by the last frame searched, with no wall hit: the frames up to it are those of `FastTakeoff`. `early_of` proves it -/
structure Early (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C T1 : Nat) : Prop where
  /-- no frame before `hitF` is stopped -/
  follow : ∀ n, C ≤ n → n + 1 < C + N.hitF → Follow sy m fr n
  fall_in : ∀ n, C ≤ n → n < C + N.fall → AirIn (fr.inp (n + 1))
  gnd_in : ∀ n, C + N.fall ≤ n → n < T1 → GndIn (fr.inp (n + 1))
  jump_in : JmpIn (fr.inp (T1 + 1))
  air_in : ∀ n, T1 + 1 ≤ n → n < T1 + 1 + N.rise → AirIn (fr.inp (n + 1))

/-- with no wall hit, no stop from `hitF` on, and a landing on the block before `t0`: the last takeoff from the floor and its landing -/
structure Approach (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 : Nat) : Type where
  /-- the takeoff frame is `T1 + 1`. A takeoff needs the floor, so it comes after the fall -/
  T1 : Nat
  T1_ge : C + N.fall ≤ T1
  T1_lt : T1 < t0
  T1_floor : OnFloor sy (fr.vs T1)
  /-- its first frame in the vertical routine; `x.fast` says whether the stored speed is at the threshold -/
  x : Arc
  x_mem : x ∈ arcStart sy m (groundY sy) N.h
  x_vs : fr.vs (T1 + 1) = x.s
  /-- the jump reads the stored speed -/
  x_ab : x.fast = decide (sy.AirFastSpeed.toNat ≤ fr.ab T1)
  /-- he lands on the block on frame `L`, at the arc's state `u`. Frame `T1 + 1 + u.low` is the last low frame -/
  L : Nat
  u : Arc
  L_gt : T1 < L
  L_le : L ≤ t0
  reach : Cert.Reach (arcSucc sy m N.h) x (L - (T1 + 1)) u
  window : falling u.s = true ∧ standY sy N.h ≤ u.s.y.toNat ∧ u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat
  air : ∀ n, T1 ≤ n → n < L → isAir (fr.inp (n + 1)) = true
  low : ∀ n, T1 + 1 ≤ n → n ≤ T1 + 1 + u.low → LowAt sy m N fr n

/-- over the block in one jump, or onto it and off it. Only a run with no wall hit and no stop needs its takeoff from the floor -/
inductive Way (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C t0 E : Nat) : Type where
  | over (o : Over sy m N fr C t0) : Way sy m N fr C t0 E
  | onto (a : NoWall sy m N fr C → (∀ n, C + N.hitF ≤ n → n ≤ t0 → ¬Stop sy m N fr n) → Approach sy m N fr C t0)
      (off : Off sy m N fr C t0 E) : Way sy m N fr C t0 E

/-- what a real run in the room gives, apart from the frames' link to `hstep` -/
structure RoomFields (sy : Syms) (m : Machine) (N : Nums) where
  fr : Frames
  /-- first control -/
  C : Nat
  /-- the state at first control -/
  start : fr.hs C = (room sy N).s0
  startP0 : (room sy N).P0 ≤ fr.P C
  startP1 : fr.P C ≤ (room sy N).P1
  /-- the entry frame: the collision routine enters the side pipe on a state of the domain of `SidePipe.sideCheck`, with the frame's `x` -/
  E : Nat
  entry : SidePipe.Case
  entry_mem : entry ∈ SidePipe.cases sy
  entered : SidePipe.enters sy (SidePipe.withPipe sy m) entry = true
  entry_P : ∃ f : Int, 0 ≤ f ∧ fr.P E = 256 * (256 * ((0 : Nat) : Int) + (entry.x.toNat : Int)) + f
  /-- the first frame past the block's right end -/
  t0 : Nat
  t0_ge : C ≤ t0
  past : goalP sy ≤ fr.P t0
  first : ∀ n, C ≤ n → n < t0 → fr.P n < goalP sy
  /-- a frame before `hitF` that does not follow `hstep` is stopped by the left wall -/
  wall : ∀ n, C ≤ n → n + 1 < C + N.hitF → ¬Follow sy m fr n → WallAt N fr n
  /-- from `hitF` to `runF + 1`, by the left wall, or he is at the corner -/
  late : ∀ n, C + N.hitF ≤ n + 1 → n ≤ C + N.runF → ¬Follow sy m fr n →
    WallAt N fr n ∨ cornerP sy ≤ fr.P n + 16 * (top sy : Int)
  /-- a frame by `runF` that does not follow `hstep` leaves `RunningSpeed` 0 -/
  stop_run : ∀ n, C ≤ n → n < C + N.runF → ¬Follow sy m fr n → (fr.hs (n + 1)).rs = 0
  /-- he starts in the air -/
  v_start : (fr.vs C).st = 2 ∧ VY (fr.vs C) ≤ N.startY ∧ VW (fr.vs C) ≤ N.startW ∧ (fr.vs C).vfd.toNat = N.fallF
  /-- a frame that starts in the air has an air input -/
  air_in : ∀ n, C ≤ n → n < C + N.standF → (fr.vs n).st ≠ 0 → AirIn (fr.inp (n + 1))
  /-- he stands away from the floor only at the end of a frame that does not follow `hstep`: a side stops him on that frame -/
  stand_wall : ∀ n, C ≤ n → n + 1 < C + N.standF → (fr.vs (n + 1)).st = 0 → ¬OnFloor sy (fr.vs (n + 1)) → ¬Follow sy m fr n
  /-- he is not on the floor during the fall -/
  fall_long : ∀ n, C ≤ n → n < C + N.fall → ¬OnFloor sy (fr.vs n)
  /-- a frame in the air and a jump frame keep the facing direction -/
  facing : ∀ n, C ≤ n → n < C + N.fall → (fr.inp (n + 1)).st ≠ 0 ∨ (fr.inp (n + 1)).jump = true → (fr.hs (n + 1)).fd = (fr.hs n).fd
  /-- before a stand in the fall he moves left fast, and he is near the wall -/
  stand_fast : ∀ n, C ≤ n → n + 1 < C + N.fall → (fr.vs (n + 1)).st = 0 → N.standV ≤ -V (fr.hs n)
  stand_P : ∀ n, C ≤ n → n + 1 < C + N.fall → (fr.vs (n + 1)).st = 0 → fr.P n ≤ N.standP
  /-- landing: on a whole row, with no speed -/
  stand_row : ∀ n, C ≤ n → n + 1 < C + N.standF → (fr.vs n).st ≠ 0 → (fr.vs (n + 1)).st = 0 →
    (fr.vs (n + 1)).y.toNat % 16 = 0 ∧ VW (fr.vs (n + 1)) = 0
  /-- a frame with no jump, from a state that is not in a jump -/
  vfall : ∀ n, C ≤ n → n + 1 < C + N.standF → (fr.vs n).st ≠ 1 → (fr.inp (n + 1)).jump = false → VDrop (fr.vs n) (fr.vs (n + 1))
  /-- with no wall, the fall ends on the floor -/
  floor_at : NoWall sy m N fr C → OnFloor sy (fr.vs (C + N.fall))
  /-- with no wall, the heights of the frames after the fall -/
  vframes : NoWall sy m N fr C → ∀ n, C + N.fall ≤ n → n < C + N.fall + N.lastG + 1 + N.rise → VFrame sy m N fr n
  /-- what the collision routine gives with the feet at or below the corner -/
  low_at : ∀ n, C + N.hitF ≤ n → n ≤ C + N.fall + 1 + N.rise → n ≤ t0 → cornerY sy N.h ≤ (fr.vs n).y.toNat → LowAt sy m N fr n
  /-- the stored speed is 0 at first control, and at least `|v|` -/
  ab_start : fr.ab C = 0
  ab_ge : ∀ n, C ≤ n → n ≤ t0 → (sbyte (fr.hs n).v).natAbs ≤ fr.ab n
  /-- a frame that follows `hstep` stores `|v|`, or changes neither -/
  ab_follow : ∀ n, C ≤ n → n < t0 → Follow sy m fr n →
    fr.ab (n + 1) = (sbyte (fr.hs (n + 1)).v).natAbs ∨ (fr.ab (n + 1) = fr.ab n ∧ (fr.hs (n + 1)).v = (fr.hs n).v)
  way : Way sy m N fr C t0 E

/-- the frames as numbers: what the theorems below use. `RoomRun.toCore` makes them from real machines -/
structure RoomCore (sy : Syms) (m : Machine) (N : Nums) extends RoomFields sy m N where
  /-- every frame up to `t0` follows `hstep` or leaves him stopped -/
  frames : ∀ n, C ≤ n → n < t0 → Follow sy m fr n ∨ Stop sy m N fr (n + 1)
  /-- every frame moves him at most the top speed -/
  move_top : ∀ n, C ≤ n → n < t0 → fr.P (n + 1) ≤ fr.P n + 16 * (top sy : Int)

/-- what a real run in the room gives, on real machines -/
structure RoomRun (sy : Syms) (m : Machine) (N : Nums) extends RoomFields sy m N where
  /-- `fm n` is the machine at the end of frame `n`, `pad n` the input of frame `n` -/
  fm : Nat → Machine
  pad : Nat → UInt8
  /-- the instruction at which frame `n + 1` comes to the player's routine -/
  arr : Nat → Nat
  next : ∀ n, C ≤ n → n < t0 → fm (n + 1) = PipeTransition.frame (fm n) (pad (n + 1))
  /-- the state and the position are those of the machine -/
  read_hs : ∀ n, C ≤ n → n ≤ t0 → fr.hs n = FrameModel.readHS sy (fm n)
  read_P : ∀ n, C ≤ n → n ≤ t0 → fr.P n = posP sy (fm n)
  /-- a frame that follows the model has the input read from the machine -/
  read_in : ∀ n, C ≤ n → n < t0 → FrameModel.Clean sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (fm n) (pad (n + 1)) (arr n) →
    fr.inp (n + 1) = FrameModel.readIn sy (PipeEntryRule.trace (fm n) (pad (n + 1)) (arr n))
  /-- each frame up to `t0` is one that follows the model; or it leaves him stopped, and it is a `TopSpeed.Frame` -/
  clean : ∀ n, C ≤ n → n < t0 → FrameModel.Clean sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (fm n) (pad (n + 1)) (arr n) ∨
    (Stop sy m N fr (n + 1) ∧ FrameModel.ReadFrame sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (fm n) (pad (n + 1)) (arr n))

/-! ## What the computation provides -/

/-- the bound on the distance from `Φ ≤ p`, with `g_fast` on every frame: it needs no condition on the running speed -/
def fastDist (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * min (top sy : Int) ((p + gFast sy m) / 256) + fastDist sy m (p + gFast sy m) n

/-- on every frame of an arc, its length is at most the given number -/
def lenOk (ks kf : Nat) (x : Arc) : Bool := decide (x.k ≤ if x.fast then kf else ks)

/-- a jump from the floor: on the first `low` frames after the takeoff frame the feet are low, he is rising and in the air state, and a jump
that comes back to the floor lasts at least `hop` frames -/
def floorArcOk (sy : Syms) (h low hop : Nat) (x : Arc) : Bool :=
  (decide (low < x.k) || (decide (Jump.cornerY sy h ≤ x.s.y.toNat) && !falling x.s && x.s.st != 0)) &&
    (!(falling x.s && decide (groundY sy ≤ x.s.y.toNat)) || decide (hop ≤ x.k))

/-- `Φ` counted only to the right: on an air frame facing right it grows by at most `a₁`. Moving left, the adder is doubled, so a state just
below 0 is worth what its reversal gives: the three cases are one, one and two more frames of the doubled adder -/
def psiP (sy : Syms) (m : Machine) (s : HS) : Int :=
  if 0 ≤ V s then V s + w sy m s
  else max 0 (if 256 - gSlow sy m ≤ V s then V s + a1 sy m
    else if -gSlow sy m ≤ V s then V s + gSlow sy m
    else if -gSlow sy m - a1 sy m ≤ V s then V s + gSlow sy m + a1 sy m else 0)

/-- on an air frame facing right: the facing stays, `Ψ` grows by at most `a₁`, `V` falls by at most `g_slow` -/
def airOk (sy : Syms) (m : Machine) (s : HS) (i : HIn) : Bool :=
  let t := hstep sy m s i
  t.fd == s.fd && decide (psiP sy m t ≤ psiP sy m s + a1 sy m) && decide (V s - V t ≤ gSlow sy m)

/-- the states of the fall: below the air threshold, facing right, `RunningSpeed` 0 -/
def fallStates (sy : Syms) : List HS :=
  ((speedsB sy).filter fun v => decide ((sbyte v).natAbs < sy.AirFastSpeed.toNat)).flatMap fun v =>
    bytes.flatMap fun f => (mds v).map fun md => { v, f, fd := 1, md, rs := 0 }

def airCheck (sy : Syms) (m : Machine) : Bool := (fallStates sy).all fun s => airI.all (airOk sy m s)

/-- how far an air frame after `j` frames moves him at most, from `Ψ ≤ p` -/
def airDist (sy : Syms) (m : Machine) (p : Int) : Nat → Int
  | 0 => 0
  | j + 1 => airDist sy m p j + 16 * ((p + a1 sy m * ((j + 1 : Nat) : Int)) / 256)

/-- how far he moves left at least, when `-V` is at least `u` at the end of `k` air frames -/
def backD (sy : Syms) (m : Machine) (u : Int) : Nat → Int
  | 0 => 0
  | k + 1 => 16 * (u / 256) + backD sy m (u - gSlow sy m) k

/-- how far he moves left at most, from `Φ ≤ p` -/
def leftDist (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * ((nxt sy m p + 255) / 256) + leftDist sy m (nxt sy m p) n

/-- below this `|V|` the speed is below the running threshold -/
def runTheta (sy : Syms) : Int := 256 * (sy.RunSpeedMin.toNat : Int) - 255

/-- for `k` more frames `|v|` stays below the running threshold. Most states are decided by the bound on `Φ` -/
def safeFrom (sy : Syms) (m : Machine) : Nat → HS → Bool
  | 0, s => decide ((sbyte s.v).natAbs < sy.RunSpeedMin.toNat)
  | k + 1, s => decide ((sbyte s.v).natAbs < sy.RunSpeedMin.toNat) &&
      (decide (iterN sy m (phi sy m s) (k + 1) < runTheta sy) || inputsN.all fun i => safeFrom sy m k (hstep sy m s i))

/-- moving right at the end of the fall, with `Φ ≤ p` -/
def safeStates (sy : Syms) : List HS :=
  ((speedsB sy).filter fun v => decide (0 ≤ sbyte v) && decide ((sbyte v).natAbs < sy.AirFastSpeed.toNat)).flatMap fun v =>
    bytes.flatMap fun f => (mds v).map fun md => { v, f, fd := 1, md, rs := 0 }

def safeCheck (sy : Syms) (m : Machine) (p : Int) (k : Nat) : Bool :=
  (safeStates sy).all fun s => !decide (phi sy m s ≤ p) || safeFrom sy m k s

/-- the height added in `n` frames, from the speed `w` and the force `f` -/
def fallSum (w f : Int) : Nat → Int
  | 0 => 0
  | n + 1 => fallSum w f n + w + f * (n : Int)

/-- the height with its fraction on a stand `j` frames after first control, at most: a whole row -/
def standB (N : Nums) (j : Nat) : Int := 4096 * ((N.startY + fallSum N.startW (N.fallF : Int) j) / 4096) + 255

/-- how far he moves at most from `Φ ≤ p` in `n` frames below the air threshold -/
def capRamp (sy : Syms) (m : Machine) : Int → Nat → Int
  | _, 0 => 0
  | p, n + 1 => 16 * min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) + capRamp sy m (nxt sy m p) n

/-- the numbers fit together -/
structure NumFacts (sy : Syms) (m : Machine) (N : Nums) : Prop where
  air_pos : 1 ≤ sy.AirFastSpeed.toNat
  stop_small : N.stopPhi + 255 < 256 * (sy.AirFastSpeed.toNat : Int)
  stop_nonneg : 0 ≤ N.stopPhi
  low_nonneg : 0 ≤ N.lowSlack
  hit_ge : N.fall + 1 ≤ N.hitF
  hit_rise : N.hitF ≤ N.fall + 2 + N.rise
  run_le : N.runF ≤ N.fall + 1 + N.rise
  /-- the slow pairs, with the frame on the block and the air speed, then `capDist`, are short of the goal -/
  slow_pairs : N.slow.all (fun q => decide (N.rise ≤ q.1) && decide (N.fall + 1 + q.2 ≤ N.goalF) && decide (q.1 ≤ q.2) &&
      decide (cornerP sy - 1 + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((q.2 - q.1 : Nat) : Int) +
        capDist sy m (N.goalF - (N.fall + 1 + q.2)) < goalP sy)) = true
  fast_pairs : N.fast.all (fun q => decide (N.rise ≤ q.1)) = true
  /-- a stop with `RunningSpeed` 0 while his feet are low -/
  hit_J : cornerP sy + N.lowSlack + dbound sy m N.stopPhi (N.goalF - N.hitF) < goalP sy
  /-- a stop with any `RunningSpeed` while his feet are low -/
  hit_F : cornerP sy + N.lowSlack + fastDist sy m N.stopPhi (N.goalF - (N.runF + 1)) < goalP sy
  /-- a stop later: at most the top speed after the low frames, and not far past the corner -/
  hit_late : (List.range (N.goalF + 1)).all (fun j => decide (j ≤ N.fall + 1 + N.rise) ||
      decide (min (cornerP sy + N.lowSlack + 16 * (top sy : Int) * ((j - (N.fall + 1 + N.rise) : Nat) : Int))
        (cornerP sy + N.stopSlack) + fastDist sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a takeoff after the last one searched: the top speed from the end of the low frames -/
  late : cornerP sy + N.lowSlack + 16 * (top sy : Int) * ((N.goalF - (N.fall + N.lastG + 2 + N.rise) : Nat) : Int) < goalP sy
  /-- over the block in one jump: below the threshold, the air speed all the way -/
  over_capped : cornerP sy + N.stopSlack + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((N.lenA + 1 : Nat) : Int) < goalP sy
  /-- at the threshold or more, the top speed after the low frames -/
  over_top : cornerP sy + N.lowSlack + 16 * (top sy : Int) * ((N.lenF - N.rise : Nat) : Int) < goalP sy
  /-- or a stop on the way -/
  over_stop : cornerP sy + N.stopSlack + fastDist sy m N.stopPhi (N.lenF - N.rise) < goalP sy
  len_ok : N.lenS < arcFrames ∧ N.lenF < arcFrames ∧ N.lenB < arcFrames ∧ N.lenA < arcFrames
  /-- off the block: a fast jump gives the bound; the others are not shorter, or are short of the mouth -/
  above_le : N.aboveF ≤ N.aboveS + 1
  walk_le : N.aboveF ≤ N.walk + 1
  air_ge : N.aboveS ≤ N.airS + 1
  slow_mouth : goalP sy + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (N.aboveS : Int) ≤ SidePipe.mouthP sy 0
  /-- the order of the frames -/
  rise_lt : N.rise < arcFrames
  corner_le : cornerY sy N.h ≤ groundY sy
  corner_goal : cornerP sy ≤ goalP sy
  last_le : N.lastG ≤ N.rise
  hit_run : N.hitF ≤ N.runF
  run_ge : N.fall + 1 ≤ N.runF
  goal_ge : N.runF + 1 ≤ N.goalF
  fall_wall : N.wallF + 1 + N.wallK ≤ N.fall
  back_le : N.backK ≤ N.fall
  wall_two : 2 ≤ N.wallF
  gs_le : gSlow sy m ≤ gFast sy m
  gs_stop : gSlow sy m ≤ N.stopPhi
  a1_nonneg : 0 ≤ a1 sy m
  /-- with no wall he is left of the corner before `hitF` -/
  corner_open : (room sy N).P1 + airDist sy m (phi sy m (room sy N).s0) N.fall + capDist sy m (N.hitF - 1 - N.fall) < cornerP sy
  /-- the wall is too far for the frames before `wallF - 1` -/
  wall_far : N.wallP < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) (N.wallF - 2)
  /-- after a wall hit he stays left of the corner: before `hitF`, at the corner stops, on the floor, on the low frames -/
  wall_corner : N.wallP + dbound sy m N.stopPhi (N.hitF - 1 - N.wallF) < cornerP sy
  wall_late : N.wallP + dbound sy m N.stopPhi (N.runF - N.wallF) + 16 * (top sy : Int) < cornerP sy
  wall_low : N.wallP + dbound sy m N.stopPhi (N.runF + 1 - N.wallF) +
    16 * (top sy : Int) * ((N.fall + 1 + N.rise - (N.runF + 1) : Nat) : Int) ≤ cornerP sy + N.lowSlack
  /-- a stop by `runF` with `RunningSpeed` not 0, after a wall hit -/
  wall_stops : (List.range (N.goalF + 1)).all (fun j => decide (j < N.hitF) || decide (N.runF < j) ||
    decide (N.wallP + dbound sy m N.stopPhi (j - N.wallF) + fastDist sy m N.stopPhi (N.goalF - j) < goalP sy)) = true
  /-- a wall hit by frame `wallD` or later -/
  wall_near : N.wallP + dbound sy m N.stopPhi (N.goalF - N.wallD) < goalP sy
  wallD_le : N.wallD ≤ N.fall
  /-- facing right after a wall hit before `wallD`: one frame of any kind, then air frames to the end of the fall -/
  wall_phi : nxt sy m N.stopPhi < theta sy
  wall_Q : nxt sy m N.stopPhi + a1 sy m * ((N.fall - N.wallF - 1 : Nat) : Int) ≤ N.fastQ
  wall_open : N.wallP + 16 * (nxt sy m N.stopPhi / 256) + airDist sy m (nxt sy m N.stopPhi) (N.fall - N.wallF - 1) +
    dbound sy m N.fastQ (N.goalF - N.fall) < goalP sy
  wall_u : nxt sy m N.stopPhi < N.fastQ + 1 - 2 * c sy m - gSlow sy m * ((N.wallK - 1 : Nat) : Int)
  wall_k : 1 ≤ N.wallK
  wall_back : N.wallP + 16 * (nxt sy m N.stopPhi / 256) + airDist sy m (nxt sy m N.stopPhi) (N.fall - N.wallK - N.wallF - 1) -
    backD sy m (N.fastQ + 1 - 2 * c sy m) N.wallK + capDist sy m (N.goalF - N.fall) < goalP sy
  /-- turned away after a wall hit before `wallD`: he falls, below the air threshold, until the floor -/
  fall_le : N.fall ≤ N.standF
  gap_D : N.wallD ≤ N.wallF + N.gapF
  gap_two : 2 ≤ N.gapF
  gap_V : iterN sy m N.stopPhi (N.gapF - 2) < N.standV
  stand_far : N.standP < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) (N.wallF - 1)
  gaps_all : (List.range N.wallD).all (fun j => decide (j ≤ N.wallF) || N.gaps.any (fun q => q.1 == j)) = true
  gaps_ok : N.gaps.all (fun q => decide (N.wallD ≤ q.1 + q.2) && decide (q.1 + q.2 + 2 ≤ N.standF) && decide (q.1 + q.2 + 1 ≤ N.goalF) &&
    decide (standB N q.1 + fallSum 0 (N.fallF : Int) q.2 < 256 * (groundY sy : Int)) &&
    decide (N.wallP + capRamp sy m N.stopPhi (q.2 + 1) + capDist sy m (N.goalF - (q.1 + q.2 + 1)) < goalP sy)) = true
  /-- `RunningSpeed` by `runF` with no wall -/
  safe_bound : iterN sy m N.safeP (N.runF - N.fall - 1) < runTheta sy
  stop_safe : iterN sy m N.stopPhi (N.runF - N.fall - 1) < runTheta sy
  back_ok : (room sy N).P1 + airDist sy m (phi sy m (room sy N).s0) (N.fall - N.backK) -
    backD sy m (N.safeP + 1 - 2 * c sy m) N.backK + 16 * (top sy : Int) * ((N.runF - N.fall : Nat) : Int) ≤ N.backP
  hit_B : N.backP + fastDist sy m N.stopPhi (N.goalF - N.hitF) < goalP sy

/-- the checks of the earlier theorems -/
structure Checks (sy : Syms) (m : Machine) (N : Nums) : Prop where
  air : CFacts sy m
  normI : normIdem = true
  roomOk : roomCheck sy m (room sy N) = true
  window : arcCheck sy m (groundY sy) N.h (windowOk sy N.h N.slow N.fast) = true
  drop : arcCheck sy m (standY sy N.h) N.h (dropOk sy N.aboveS N.aboveF N.airS) = true
  walk : walkOk sy m N.h N.walk = true
  lenG : arcCheck sy m (groundY sy) N.h (lenOk N.lenS N.lenF) = true
  lenY : N.heights.all (fun y0 => arcCheck sy m y0 N.h (lenOk N.lenA N.lenA)) = true
  lenB : arcCheck sy m (standY sy N.h) N.h (lenOk N.lenB N.lenB) = true
  /-- every jump from the floor -/
  floor : ∃ hop, arcCheck sy m (groundY sy) N.h (floorArcOk sy N.h N.rise hop) = true
  /-- the entry -/
  side : SidePipe.sideCheck sy m = true
  /-- the frames of the fall -/
  fall : airCheck sy m = true
  safe : safeCheck sy m (phi sy m (room sy N).s0 + a1 sy m * (N.fall : Int)) (N.runF - N.fall - 1) = true
  /-- a real frame follows the model -/
  model : FrameModel.modelOK sy m (FrameModel.ctrlStack sy m) = true
  /-- the routine of the friction, for `TopSpeed.Frame` -/
  fric : TopSpeed.frictionCheck sy m = true
  nums : NumFacts sy m N

/-! ## Lists of frames -/

/-- the inputs of frames `u + 1 .. u + n` -/
def seg (inp : Nat → HIn) : Nat → Nat → List HIn
  | _, 0 => []
  | u, n + 1 => inp (u + 1) :: seg inp (u + 1) n

theorem length_seg (inp : Nat → HIn) : ∀ u n, (seg inp u n).length = n
  | _, 0 => rfl
  | u, n + 1 => by simp [seg, length_seg inp (u + 1) n]

theorem seg_add (inp : Nat → HIn) : ∀ u a b, seg inp u (a + b) = seg inp u a ++ seg inp (u + a) b
  | _, 0, b => by simp [seg]
  | u, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [seg, List.cons_append]
    rw [seg_add inp (u + 1) a b, show u + 1 + a = u + (a + 1) by omega]

theorem mem_seg {inp : Nat → HIn} {P : HIn → Prop} : ∀ {u n}, (∀ j, u ≤ j → j < u + n → P (inp (j + 1))) → ∀ i ∈ seg inp u n, P i
  | _, 0, _, i, hi => by simp [seg] at hi
  | u, n + 1, h, i, hi => by
    simp only [seg, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact h u (by omega) (by omega)
    · exact mem_seg (u := u + 1) (n := n) (fun j h1 h2 => h j (by omega) (by omega)) i hi

variable {sy : Syms} {m : Machine} {N : Nums}

/-- following `hstep`, the position and state are those of `go` -/
theorem go_seg {fr : Frames} : ∀ u n, (∀ j, u ≤ j → j < u + n → Follow sy m fr j) →
    go sy m (fr.hs u, fr.P u) (seg fr.inp u n) = (fr.hs (u + n), fr.P (u + n))
  | _, 0, _ => rfl
  | u, n + 1, h => by
    have h0 := h u (by omega) (by omega)
    simp only [seg, go]
    have h1 : adv sy m (fr.hs u, fr.P u) (fr.inp (u + 1)) = (fr.hs (u + 1), fr.P (u + 1)) := by
      unfold adv
      simp only
      rw [← h0.2.1, h0.2.2]
    rw [h1, go_seg (u + 1) n (fun j h2 h3 => h j (by omega) (by omega)),
      show u + 1 + n = u + (n + 1) by omega]

theorem hdist_seg {fr : Frames} (u n : Nat) (h : ∀ j, u ≤ j → j < u + n → Follow sy m fr j) :
    fr.P (u + n) = fr.P u + hdist sy m (fr.hs u) (seg fr.inp u n) := by
  have h1 := go_seg u n h
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m) (seg fr.inp u n) (fr.hs u, fr.P u)
  rw [h1] at h2
  exact h2

theorem inputs_seg {fr : Frames} (u n : Nat) (h : ∀ j, u ≤ j → j < u + n → Follow sy m fr j) :
    ∀ i ∈ seg fr.inp u n, i ∈ inputs :=
  mem_seg (fun j h1 h2 => (h j h1 h2).1)

/-- `P` left of the corner on the frames gives `Low` -/
theorem low_seg {fr : Frames} {cp : Int} : ∀ u n, (∀ j, u ≤ j → j < u + n → Follow sy m fr j) →
    (∀ j, u ≤ j → j < u + n → fr.P (j + 1) < cp) → Low sy m cp (fr.hs u, fr.P u) (seg fr.inp u n)
  | _, 0, _, _ => trivial
  | u, n + 1, h, hl => by
    have h0 := h u (by omega) (by omega)
    have h1 : adv sy m (fr.hs u, fr.P u) (fr.inp (u + 1)) = (fr.hs (u + 1), fr.P (u + 1)) := by
      unfold adv
      simp only
      rw [← h0.2.1, h0.2.2]
    refine ⟨by rw [h1]; exact hl u (by omega) (by omega), ?_⟩
    rw [h1]
    exact low_seg (u + 1) n (fun j h2 h3 => h j (by omega) (by omega)) (fun j h2 h3 => hl j (by omega) (by omega))

/-! ## Bounds on `hdist` -/

theorem fastDist_nonneg (hg : 0 ≤ gFast sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ fastDist sy m p n
  | 0, _, _ => by simp [fastDist]
  | n + 1, p, hp => by
    have ih := fastDist_nonneg hg n (p + gFast sy m) (by omega)
    simp only [fastDist]
    omega

theorem fastDist_mono (hg : 0 ≤ gFast sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → fastDist sy m p n ≤ fastDist sy m p (n + k)
  | 0, k, p, hp => by
    have := fastDist_nonneg hg k p hp
    simpa [fastDist] using this
  | n + 1, k, p, hp => by
    have ih := fastDist_mono hg n k (p + gFast sy m) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [fastDist]
    omega

theorem fast_dist_le (F : Facts sy m) : ∀ (is : List HIn) (s : HS) (p : Int), inD sy s = true → phi sy m s ≤ p →
    (∀ i ∈ is, i ∈ inputs) → hdist sy m s is ≤ fastDist sy m p is.length
  | [], _, _, _, _, _ => by simp [hdist, fastDist]
  | i :: rest, s, p, hD, hp, his => by
    obtain ⟨h1, h2⟩ := FastTakeoff.step_facts F hD (his i (by simp))
    have ih := fast_dist_le F rest _ (p + gFast sy m) h1 (by omega) (fun j hj => his j (by simp [hj]))
    have hpt := phi_ge F (hstep sy m s i)
    generalize ht : hstep sy m s i = t at *
    have hVt : 256 * sbyte t.v ≤ ((V t).natAbs : Int) := by
      have : (0 : Int) ≤ (t.f.toNat : Int) := by omega
      unfold V; omega
    have htop : sbyte t.v ≤ (top sy : Int) := by
      simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at h1
      omega
    have h3 : sbyte t.v ≤ (p + gFast sy m) / 256 := by omega
    simp only [hdist, fastDist, ht]
    omega

theorem dbound_nonneg (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ dbound sy m p n
  | 0, _, _ => by simp [dbound]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_nonneg F n (nxt sy m p) (by omega)
    simp only [dbound]
    omega

theorem dbound_mono (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → dbound sy m p n ≤ dbound sy m p (n + k)
  | 0, k, p, hp => by
    have := dbound_nonneg F k p hp
    simpa [dbound] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_mono F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [dbound]
    omega

/-- `capDist` grows with the frames -/
theorem cap_mono (hA : 1 ≤ sy.AirFastSpeed.toNat) (n k : Nat) : capDist sy m n ≤ capDist sy m (n + k) := by
  have h := landing_later (sy := sy) (m := m) 0 n k
  rw [Int.zero_add, Int.mul_zero, Int.zero_add] at h
  have h0 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by omega
  have h1 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (k : Int) := Int.mul_nonneg h0 (by omega)
  omega

/-- the same as `FastTakeoff.left_spec`, for any number of frames up to `D` -/
theorem left_spec_le (F : Facts sy m) {D : Nat} {goal : Int} {es : List Ent} {y : Pos}
    (hl : leftOk sy m D goal es = true) (hc : Cov es y)
    (hv : sbyte y.1.v ≤ -(sy.AirFastSpeed.toNat : Int)) {rest : List HIn} (hin : ∀ i ∈ rest, i ∈ inputs)
    (hlen : rest.length ≤ D) : (go sy m y rest).2 < goal := by
  simp only [leftOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hl
  obtain ⟨hall, hgoal⟩ := hl
  obtain ⟨a, b, h1, h2, h3⟩ := FastTakeoff.cov_filter (f := fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int)))
    hc (fun _ _ => by simp only [decide_eq_true_eq]; exact hv)
  obtain ⟨⟨h4, h5⟩, h6⟩ := hall _ h1
  simp only at h4 h5 h6
  generalize hH : List.foldl (fun b (e : Ent) => max b e.2.2) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = H at hgoal h5
  generalize hQ : List.foldl (fun b (e : Ent) => max b (Opening.pOf sy m e.1)) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = Q at hgoal h6
  obtain ⟨hJ1, hJ2, hJ3⟩ := Opening.J_pOf (sy := sy) (m := m) h4
  have hJ : J sy m y.1 Q := ⟨hJ1, by omega, fun h => by have := hJ3 h; omega⟩
  have h7 := dist_le F rest y.1 Q hJ hin
  have hQ0 : 0 ≤ Q := by
    have h8 := phi_ge F y.1
    have h9 := hJ.2.1
    omega
  obtain ⟨k, hk⟩ : ∃ k, D = rest.length + k := ⟨D - rest.length, by omega⟩
  have h10 := dbound_mono F rest.length k Q hQ0
  rw [← hk] at h10
  rw [FastTakeoff.go_snd]
  omega

/-! ## Arcs -/

theorem arcStart_low {sy : Syms} {m : Machine} {y0 h : Nat} {x : Arc} (hx : x ∈ arcStart sy m y0 h) : x.low = 0 := by
  unfold arcStart at hx
  obtain ⟨_, _, h2⟩ := List.mem_map.1 (List.mem_eraseDups.1 hx)
  rw [← h2]

/-- the last low frame is not after the frame -/
theorem arc_low {h : Nat} : ∀ {x u : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → x.low ≤ x.k → u.low ≤ u.k
  | _, _, _, .refl _, h0 => h0
  | x, _, _, @Cert.Reach.step _ _ _ y _ _ h1 h2, h0 => by
    refine arc_low h2 ?_
    unfold arcSucc at h1
    split at h1
    · simp at h1
    · simp only [List.mem_map] at h1
      obtain ⟨_, _, h3⟩ := h1
      rw [← h3]
      simp only
      split <;> omega

/-- every arc of a check of `lenOk` ends in time -/
theorem arc_len {y0 h ks kf : Nat} (hc : arcCheck sy m y0 h (lenOk ks kf) = true) {x u : Arc} (hx : x ∈ arcStart sy m y0 h)
    {n : Nat} (hr : Cert.Reach (arcSucc sy m h) x n u) (hs : ks < arcFrames) (hf : kf < arcFrames) :
    n ≤ if x.fast then kf else ks := by
  have hspec := arc_spec hc x hx
  have hK : (if x.fast then kf else ks) < arcFrames := by split <;> assumption
  generalize hK2 : (if x.fast then kf else ks) = K at hK ⊢
  by_cases hn : n ≤ K
  · exact hn
  · exfalso
    have hsp : n = (K + 1) + (n - (K + 1)) := by omega
    rw [hsp] at hr
    obtain ⟨y, h1, _⟩ := Cert.Reach.split (K + 1) (n - (K + 1)) hr
    have h2 := hspec (K + 1) y (by omega) h1
    obtain ⟨h3, h4⟩ := arc_k h1
    have h5 := arcStart_k hx
    simp only [lenOk, decide_eq_true_eq] at h2
    rw [h4, hK2] at h2
    omega


/-! ## The air frames of the fall -/

/-- below the air threshold, facing right, `RunningSpeed` 0 -/
structure FallSt (sy : Syms) (s : HS) : Prop where
  dom : inD sy s = true
  cap : capped sy s = true
  fd : s.fd = 1
  rs : s.rs = 0

theorem psiP_eq_phi {s : HS} (h : 0 ≤ V s) : phi sy m s = psiP sy m s := by
  unfold psiP phi
  rw [if_pos h]
  omega

/-- `Ψ` is at most `Φ`, or the doubled adder -/
theorem psiP_le (ha : 0 ≤ a1 sy m) {s : HS} {p : Int} (h1 : phi sy m s ≤ p) (h2 : gSlow sy m ≤ p) : psiP sy m s ≤ p := by
  by_cases h : 0 ≤ V s
  · rw [← psiP_eq_phi h]
    exact h1
  · have h3 : gSlow sy m = 2 * a1 sy m := rfl
    unfold psiP
    rw [if_neg h]
    split <;> (try split) <;> (try split) <;> omega

theorem v_le_psiP (F : Facts sy m) (s : HS) : 256 * sbyte s.v ≤ psiP sy m s := by
  have h1 := w_nonneg F s
  have h2 : (0 : Int) ≤ (s.f.toNat : Int) := by omega
  unfold psiP
  split
  · unfold V at *
    omega
  · have h3 : 256 * sbyte s.v ≤ V s := by
      unfold V
      omega
    have h4 := Int.le_max_left 0 (if 256 - gSlow sy m ≤ V s then V s + a1 sy m
      else if -gSlow sy m ≤ V s then V s + gSlow sy m
      else if -gSlow sy m - a1 sy m ≤ V s then V s + gSlow sy m + a1 sy m else 0)
    omega

/-- one air frame -/
theorem air_step (H : Checks sy m N) {s : HS} (hs : FallSt sy s) {i : HIn} (hi : AirIn i) :
    FallSt sy (hstep sy m s i) ∧ psiP sy m (hstep sy m s i) ≤ psiP sy m s + a1 sy m ∧ V s - V (hstep sy m s i) ≤ gSlow sy m := by
  have F := H.air.pot
  obtain ⟨hD, hc, hfd, hrs⟩ := hs
  have hD0 := hD
  have hc0 := hc
  obtain ⟨v, f, fd, md, rs⟩ := s
  simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD
  obtain ⟨⟨⟨hv, _⟩, hmd⟩, _⟩ := hD
  simp only at hfd hrs
  subst hfd
  subst hrs
  have hvs : v ∈ speedsB sy := by
    have hsp := H.air.speeds
    simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_iff_mem] at hsp
    rcases hsp v (mem_bytes v) with h | h
    · rw [h] at hv; exact absurd hv (by decide)
    · exact h
  have hcv : (sbyte v).natAbs < sy.AirFastSpeed.toNat := by
    simpa only [capped, decide_eq_true_eq] using hc
  have hmem : ({ v, f, fd := 1, md, rs := 0 } : HS) ∈ fallStates sy :=
    List.mem_flatMap.2 ⟨v, List.mem_filter.2 ⟨hvs, by simpa only [decide_eq_true_eq] using hcv⟩,
      List.mem_flatMap.2 ⟨f, mem_bytes f, List.mem_map.2 ⟨md, hmd, rfl⟩⟩⟩
  have hall := H.fall
  simp only [airCheck, List.all_eq_true] at hall
  have h := hall _ hmem _ (FastTakeoff.mem_airI hi)
  rw [show airOk sy m _ (norm i) = airOk sy m _ i by
    unfold airOk
    rw [FastTakeoff.hstep_norm H.normI hi.1]] at h
  simp only [airOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨(FastTakeoff.step_facts F hD0 hi.1).1, ?_, h1, ?_⟩, h2, h3⟩
  · rcases step_cap H.air hD0 hc0 hi.1 with h4 | ⟨h4, _⟩
    · exact h4
    · have : isAir i = true := by simp [isAir, hi.2.1]
      rw [this] at h4
      exact absurd h4 (by decide)
  · have h4 := F.check _ hD0 i hi.1
    have har := F.air_le_run
    simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
      bne_iff_ne, ne_eq] at h4
    rcases h4.2 with (h5 | h5) | h5
    · exact h5
    · exact absurd trivial h5
    · omega

theorem airDist_mono {p : Int} (hp : 0 ≤ p) (ha : 0 ≤ a1 sy m) (n k : Nat) : airDist sy m p n ≤ airDist sy m p (n + k) := by
  induction k with
  | zero => exact Int.le_refl _
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    simp only [airDist]
    have h1 : 0 ≤ a1 sy m * ((n + k + 1 : Nat) : Int) := Int.mul_nonneg ha (by omega)
    have h2 : 0 ≤ (p + a1 sy m * ((n + k + 1 : Nat) : Int)) / 256 := by omega
    omega

theorem leftDist_nonneg (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ leftDist sy m p n
  | 0, _, _ => by simp [leftDist]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := leftDist_nonneg F n (nxt sy m p) (by omega)
    simp only [leftDist]
    omega

theorem leftDist_mono (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → leftDist sy m p n ≤ leftDist sy m p (n + k)
  | 0, k, p, hp => by
    have := leftDist_nonneg F k p hp
    simpa [leftDist] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := leftDist_mono F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [leftDist]
    omega

/-- moving left is bounded by `Φ` too -/
theorem left_dist_le (F : Facts sy m) : ∀ (is : List HIn) (s : HS) (p : Int), J sy m s p → (∀ i ∈ is, i ∈ inputs) →
    -hdist sy m s is ≤ leftDist sy m p is.length
  | [], _, _, _, _ => by simp [hdist, leftDist]
  | i :: rest, s, p, hJ, his => by
    obtain ⟨hJ', _, _⟩ := step_J F hJ (his i (by simp))
    have ih := left_dist_le F rest _ _ hJ' (fun j hj => his j (by simp [hj]))
    have h1 := hJ'.2.1
    have h2 := phi_ge F (hstep sy m s i)
    simp only [hdist, leftDist]
    generalize hstep sy m s i = t at *
    have hf : t.f.toNat < 256 := t.f.toNat_lt
    have h3 : -(256 * sbyte t.v) ≤ ((V t).natAbs : Int) + 255 := by
      unfold V
      omega
    omega

/-! ## The bound on `Φ` over frames -/

theorem iterN_le (F : Facts sy m) : ∀ (k : Nat) (p : Int), p ≤ iterN sy m p k
  | 0, _ => by simp [iterN]
  | k + 1, p => by
    have h1 := le_nxt F p
    have h2 := iterN_le F k (nxt sy m p)
    simp only [iterN]
    omega

theorem nxt_mono (hg : gSlow sy m ≤ gFast sy m) {p q : Int} (h : p ≤ q) : nxt sy m p ≤ nxt sy m q := by
  unfold nxt
  split <;> split <;> omega

theorem iterN_mono (hg : gSlow sy m ≤ gFast sy m) : ∀ (k : Nat) {p q : Int}, p ≤ q → iterN sy m p k ≤ iterN sy m q k
  | 0, _, _, h => by simpa [iterN] using h
  | k + 1, _, _, h => by
    simp only [iterN]
    exact iterN_mono hg k (nxt_mono hg h)

theorem iterN_succ (F : Facts sy m) : ∀ (c : Nat) (p : Int), iterN sy m p c ≤ iterN sy m p (c + 1)
  | 0, p => by simpa [iterN] using le_nxt F p
  | c + 1, p => by
    simp only [iterN]
    exact iterN_succ F c (nxt sy m p)

theorem iterN_count (F : Facts sy m) : ∀ (k j : Nat) (p : Int), iterN sy m p k ≤ iterN sy m p (k + j)
  | k, 0, _ => Int.le_refl _
  | k, j + 1, p => by
    have h1 := iterN_count F k j p
    have h2 := iterN_succ F (k + j) p
    rw [show k + (j + 1) = k + j + 1 by omega]
    omega

/-- below `runTheta`, the speed is below the running threshold -/
theorem speed_lt_of_phi (F : Facts sy m) {s : HS} (h : phi sy m s < runTheta sy) :
    (sbyte s.v).natAbs < sy.RunSpeedMin.toNat := by
  have h1 := phi_ge F s
  have hf : s.f.toNat < 256 := s.f.toNat_lt
  unfold runTheta at h
  unfold V at h1
  omega

/-- a state with a bound that stays below `runTheta` passes `safeFrom` -/
theorem safe_of_bound (F : Facts sy m) (hg : gSlow sy m ≤ gFast sy m) :
    ∀ (k : Nat) {s : HS} {p : Int}, phi sy m s ≤ p → iterN sy m p k < runTheta sy → safeFrom sy m k s = true
  | k, s, p, h1, h2 => by
    have h3 := iterN_le F k p
    have h4 := speed_lt_of_phi F (s := s) (by omega)
    cases k with
    | zero => simpa only [safeFrom, decide_eq_true_eq] using h4
    | succ k =>
      have h5 := iterN_mono hg (k + 1) h1
      simp only [safeFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨h4, Or.inl (by omega)⟩

/-- one frame: `safeFrom` goes on, and `RunningSpeed` stays 0 -/
theorem safe_step (F : Facts sy m) (hg : gSlow sy m ≤ gFast sy m) (hn : normIdem = true) {k : Nat} {s : HS} (hD : inD sy s = true)
    (hrs : s.rs = 0) (hsafe : safeFrom sy m (k + 1) s = true) {i : HIn} (hi : i ∈ inputs) :
    safeFrom sy m k (hstep sy m s i) = true ∧ (hstep sy m s i).rs = 0 := by
  simp only [safeFrom, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨h1, h2⟩ := hsafe
  constructor
  · rcases h2 with h2 | h2
    · have hJ : J sy m s (phi sy m s) := ⟨hD, Int.le_refl _, fun h => absurd hrs h⟩
      obtain ⟨hJ', _, _⟩ := step_J F hJ hi
      exact safe_of_bound F hg k hJ'.2.1 (by simpa only [iterN] using h2)
    · have h3 := h2 (norm i) (FastTakeoff.norm_mem hi)
      rwa [FastTakeoff.hstep_norm hn hi] at h3
  · have h4 := F.check s hD i hi
    simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
      bne_iff_ne, ne_eq] at h4
    rcases h4.2 with (h5 | h5) | h5
    · exact h5
    · exact absurd hrs h5
    · omega

/-! ## Jumps from the floor -/

/-- frame `n` is in a jump from the floor with the takeoff frame `T + 1` -/
def OnArc (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (T n : Nat) : Prop :=
  T + 1 ≤ n ∧ ∃ x u, x ∈ arcStart sy m (groundY sy) N.h ∧ Cert.Reach (arcSucc sy m N.h) x (n - (T + 1)) u ∧ fr.vs n = u.s

theorem reach_snoc {h : Nat} : ∀ {x u y : Arc} {n : Nat}, Cert.Reach (arcSucc sy m h) x n u → y ∈ arcSucc sy m h u →
    Cert.Reach (arcSucc sy m h) x (n + 1) y
  | _, _, _, _, .refl _, hy => .step hy (.refl _)
  | _, _, _, _, .step h1 h2, hy => .step h1 (reach_snoc h2 hy)

/-- on the first frames of a jump the feet are low, he is rising and in the air state -/
theorem arc_facts (H : Checks sy m N) {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hk : n - (T + 1) ≤ N.rise) :
    cornerY sy N.h ≤ (fr.vs n).y.toNat ∧ falling (fr.vs n) = false ∧ (fr.vs n).st ≠ 0 := by
  obtain ⟨hop, hf⟩ := H.floor
  obtain ⟨_, x, u, hx, hr, hv⟩ := h
  have h1 := arc_spec hf x hx _ u (by have := H.nums.rise_lt; omega) hr
  obtain ⟨h2, _⟩ := arc_k hr
  have h3 := arcStart_k hx
  have h4 : ¬N.rise < u.k := by omega
  simp only [floorArcOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, h4, false_or, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at h1
  rw [hv]
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2⟩

/-- the next frame of a jump, before its low frames are over -/
theorem arc_next (H : Checks sy m N) {fr : Frames} {T n : Nat} (h : OnArc sy m N fr T n) (hk : n + 1 - (T + 1) ≤ N.rise)
    (hv : VFrame sy m N fr n) : OnArc sy m N fr T (n + 1) ∧ AirIn (fr.inp (n + 1)) := by
  have hT := h.1
  obtain ⟨_, hfall, hst⟩ := arc_facts H h (by omega)
  obtain ⟨_, x, u, hx, hr, hu⟩ := h
  -- the arc's next state, with the frame's A
  let y : Arc :=
    { s := vstep sy m u.s (fr.a (n + 1)) 0, k := u.k + 1,
      low := if cornerY sy N.h ≤ (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat then u.k + 1 else u.low,
      above := if (vstep sy m u.s (fr.a (n + 1)) 0).y.toNat < standY sy N.h then 0 else u.above + 1, fast := u.fast }
  have hy : y ∈ arcSucc sy m N.h u := by
    unfold arcSucc
    rw [← hu, hfall]
    simp only [Bool.false_and, if_false, Bool.false_eq_true]
    rw [hu]
    cases ha : fr.a (n + 1) with
    | true => simp [y, ha]
    | false => simp [y, ha]
  have hr' : Cert.Reach (arcSucc sy m N.h) x (n + 1 - (T + 1)) y := by
    rw [show n + 1 - (T + 1) = n - (T + 1) + 1 by omega]
    exact reach_snoc hr hy
  cases hv with
  | stay h1 _ _ => exact absurd h1.1 hst
  | takeoff h1 _ _ _ _ => exact absurd h1.1 hst
  | other _ h2 => exact absurd h2 hst
  | air _ h2 hi =>
    refine ⟨⟨by omega, x, y, hx, hr', ?_⟩, hi⟩
    rw [h2, hu]
  | fall _ h2 =>
    exfalso
    obtain ⟨_, h3, _⟩ := arc_facts H (fr := { fr with vs := fun j => if j = n + 1 then y.s else fr.vs j }) (T := T) (n := n + 1)
      ⟨by omega, x, y, hx, hr', by simp⟩ hk
    simp only [if_true] at h3
    simp only [y] at h3
    rw [hu] at h2
    rw [h2] at h3
    exact absurd h3 (by decide)

/-! ## The run -/

namespace RoomCore

variable (r : RoomCore sy m N)

theorem inD_start (H : Checks sy m N) : inD sy (r.fr.hs r.C) = true := by
  have h := H.roomOk
  simp only [roomCheck, Bool.and_eq_true] at h
  rw [r.start]
  exact h.1.1

/-- every frame up to `t0` is in the domain -/
theorem inD_all (H : Checks sy m N) : ∀ d, r.C + d ≤ r.t0 → inD sy (r.fr.hs (r.C + d)) = true
  | 0, _ => r.inD_start H
  | d + 1, h => by
    have ih := inD_all H d (by omega)
    rcases r.frames (r.C + d) (by omega) (by omega) with h1 | h1
    · rw [show r.C + (d + 1) = r.C + d + 1 by omega, h1.2.1]
      exact (FastTakeoff.step_facts H.air.pot ih h1.1).1
    · exact h1.1

theorem inD_at (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n ≤ r.t0) : inD sy (r.fr.hs n) = true := by
  have := inD_all r H (n - r.C) (by omega)
  rwa [show r.C + (n - r.C) = n by omega] at this

/-- a frame that does not stop him follows `hstep` -/
theorem follow_of (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {n : Nat} (h1 : r.C + N.hitF ≤ n + 1)
    (h2 : n < r.t0) (hC : r.C ≤ n) : Follow sy m r.fr n := by
  rcases r.frames n hC h2 with h | h
  · exact h
  · exact absurd h (hs (n + 1) h1 (by omega))

/-- the last stop -/
theorem last_stop {a : Nat} : ∀ w, a ≤ w → (∃ h, a ≤ h ∧ h ≤ w ∧ Stop sy m N r.fr h) →
    ∃ h, a ≤ h ∧ h ≤ w ∧ Stop sy m N r.fr h ∧ ∀ n, h < n → n ≤ w → ¬Stop sy m N r.fr n
  | w, hw, ⟨h, h1, h2, h3⟩ => by
    induction w with
    | zero =>
      have : h = 0 := by omega
      subst this
      exact ⟨0, h1, h2, h3, fun n h4 h5 => by omega⟩
    | succ w ih =>
      by_cases hs : Stop sy m N r.fr (w + 1)
      · exact ⟨w + 1, by omega, by omega, hs, fun n h4 h5 => by omega⟩
      · have hne : h ≠ w + 1 := fun he => hs (he ▸ h3)
        obtain ⟨h', h4, h5, h6, h7⟩ := ih (by omega) (by omega)
        refine ⟨h', h4, by omega, h6, fun n h8 h9 => ?_⟩
        by_cases hn : n = w + 1
        · rw [hn]; exact hs
        · exact h7 n h8 (by omega)

/-- `μ` per frame, or not past `B` -/
theorem reach_le {P : Nat → Int} {u : Nat} {B μ : Int} (hB : P u ≤ B) (hμ : 0 ≤ μ) {w : Nat}
    (hstep : ∀ n, u ≤ n → n < w → P (n + 1) ≤ P n + μ ∨ P (n + 1) ≤ B) :
    ∀ d, u + d ≤ w → P (u + d) ≤ B + μ * (d : Int)
  | 0, _ => by simpa using hB
  | d + 1, h => by
    have ih := reach_le hB hμ hstep d (by omega)
    have hm : μ * ((d + 1 : Nat) : Int) = μ * (d : Int) + μ := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    have hd : 0 ≤ μ * (d : Int) := Int.mul_nonneg hμ (by omega)
    rw [show u + (d + 1) = u + d + 1 by omega, hm]
    rcases hstep (u + d) (by omega) (by omega) with h1 | h1 <;> omega

/-- **After a stop, what remains is bounded by the speed near 0**: the position at `t0`, from the last stop -/
theorem after_stop {a : Nat} (ha : r.C ≤ a) (h2 : a ≤ r.t0) (hs : ∃ h, a ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h) :
    ∃ h, a ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h ∧ r.fr.P r.t0 = r.fr.P h + hdist sy m (r.fr.hs h) (seg r.fr.inp h (r.t0 - h)) ∧
      ∀ i ∈ seg r.fr.inp h (r.t0 - h), i ∈ inputs := by
  obtain ⟨h', h3, h4, h5, h6⟩ := last_stop r (a := a) r.t0 h2 hs
  have hfol : ∀ j, h' ≤ j → j < h' + (r.t0 - h') → Follow sy m r.fr j := fun j h7 h8 => by
    rcases r.frames j (by omega) (by omega) with h9 | h9
    · exact h9
    · exact absurd h9 (h6 (j + 1) (by omega) (by omega))
  have h7 := hdist_seg h' (r.t0 - h') hfol
  rw [show h' + (r.t0 - h') = r.t0 by omega] at h7
  exact ⟨h', h3, h4, h5, h7, inputs_seg h' (r.t0 - h') hfol⟩

/-- a stopped state is below the air threshold -/
theorem capped_of_stop (H : Checks sy m N) {n : Nat} (hs : Stop sy m N r.fr n) : capped sy (r.fr.hs n) = true := by
  have h1 := phi_ge H.air.pot (r.fr.hs n)
  have h2 := hs.2.1
  have h3 := H.nums.stop_small
  have h4 : (r.fr.hs n).f.toNat < 256 := (r.fr.hs n).f.toNat_lt
  simp only [capped, decide_eq_true_eq]
  unfold V at h1
  omega

/-- air frames or stops keep the speed below the threshold -/
theorem capped_along (H : Checks sy m N) {u w : Nat} (hu : r.C ≤ u) (hw : w ≤ r.t0) (hc : capped sy (r.fr.hs u) = true)
    (hair : ∀ n, u ≤ n → n < w → isAir (r.fr.inp (n + 1)) = true ∨ Stop sy m N r.fr (n + 1)) :
    ∀ d, u + d ≤ w → capped sy (r.fr.hs (u + d)) = true
  | 0, _ => hc
  | d + 1, h => by
    have ih := capped_along H hu hw hc hair d (by omega)
    rw [show u + (d + 1) = u + d + 1 by omega]
    rcases r.frames (u + d) (by omega) (by omega) with h1 | h1
    · rcases hair (u + d) (by omega) (by omega) with h2 | h2
      · rw [h1.2.1]
        rcases step_cap H.air (inD_at r H (by omega) (by omega)) ih h1.1 with h3 | ⟨h3, _⟩
        · exact h3
        · rw [h2] at h3
          exact absurd h3 (by decide)
      · exact capped_of_stop r H h2
    · exact capped_of_stop r H h1

/-! ### The fall -/

/-- the state at first control -/
theorem start_fall (H : Checks sy m N) : FallSt sy (r.fr.hs r.C) := by
  have h := H.nums.air_pos
  rw [r.start]
  refine ⟨?_, ?_, rfl, rfl⟩
  · have h1 := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h1
    exact h1.1.1
  · show capped sy { v := 0, f := 0, fd := 1, md := 0, rs := 0 } = true
    simp only [capped, decide_eq_true_eq]
    have h2 : (sbyte (0 : UInt8)).natAbs = 0 := by decide
    rw [h2]
    omega

theorem psiP_start : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := by
  rw [r.start]
  have h : (0 : Int) ≤ V (room sy N).s0 := by
    have h1 : (room sy N).s0 = { v := 0, f := 0, fd := 1, md := 0, rs := 0 } := rfl
    rw [h1]
    unfold V
    have h2 : sbyte (0 : UInt8) = 0 := by decide
    rw [h2]
    omega
  rw [← psiP_eq_phi h]
  exact Int.le_refl _

theorem phi0_nonneg (H : Checks sy m N) : 0 ≤ phi sy m (room sy N).s0 := by
  have := phi_ge H.air.pot (room sy N).s0
  omega

/-- air frames from `a` -/
theorem fall_run (H : Checks sy m N) {a : Nat} {p : Int} (hst : FallSt sy (r.fr.hs a)) (hp : psiP sy m (r.fr.hs a) ≤ p) :
    ∀ j, (∀ i, a ≤ i → i < a + j → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      FallSt sy (r.fr.hs (a + j)) ∧ psiP sy m (r.fr.hs (a + j)) ≤ p + a1 sy m * (j : Int) ∧
        r.fr.P (a + j) ≤ r.fr.P a + airDist sy m p j
  | 0, _ => by simpa [airDist] using And.intro hst hp
  | j + 1, h => by
    obtain ⟨h1, h2, h3⟩ := fall_run H hst hp j (fun i h4 h5 => h i h4 (by omega))
    obtain ⟨h4, h5⟩ := h (a + j) (by omega) (by omega)
    obtain ⟨h6, h7, h8⟩ := air_step H h1 h5
    have h9 := v_le_psiP H.air.pot (hstep sy m (r.fr.hs (a + j)) (r.fr.inp (a + j + 1)))
    rw [show a + (j + 1) = a + j + 1 by omega, h4.2.1]
    have h10 := h4.2.2
    rw [h4.2.1] at h10
    have hm : a1 sy m * ((j + 1 : Nat) : Int) = a1 sy m * (j : Int) + a1 sy m := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    refine ⟨h6, by rw [hm]; omega, ?_⟩
    simp only [airDist]
    rw [hm]
    omega

/-- moving left at the end of air frames: how far he has moved -/
theorem back_run (H : Checks sy m N) {b : Nat} :
    ∀ (k : Nat) (u : Int), (∀ i, b ≤ i → i < b + k → FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      u ≤ -V (r.fr.hs (b + k)) → r.fr.P (b + k) ≤ r.fr.P b - backD sy m u k
  | 0, _, _, _ => by simp [backD]
  | k + 1, u, h, hu => by
    obtain ⟨h1, h2, h3⟩ := h (b + k) (by omega) (by omega)
    obtain ⟨_, _, h4⟩ := air_step H h1 h3
    rw [show b + (k + 1) = b + k + 1 by omega] at hu ⊢
    have h5 := h2.2.2
    rw [h2.2.1] at hu h5
    have ih := back_run H k (u - gSlow sy m) (fun i h6 h7 => h i h6 (by omega)) (by omega)
    generalize hstep sy m (r.fr.hs (b + k)) (r.fr.inp (b + k + 1)) = t at *
    have hf : (0 : Int) ≤ (t.f.toNat : Int) := by omega
    have h6 : 256 * sbyte t.v ≤ -u := by
      unfold V at hu
      omega
    simp only [backD]
    omega

theorem back_speed (H : Checks sy m N) {b : Nat} :
    ∀ (k : Nat) (u : Int), (∀ i, b ≤ i → i < b + k → FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1))) →
      u ≤ -V (r.fr.hs (b + k)) → u - gSlow sy m * (k : Int) ≤ -V (r.fr.hs b)
  | 0, _, _, hu => by simpa using hu
  | k + 1, u, h, hu => by
    obtain ⟨h1, h2, h3⟩ := h (b + k) (by omega) (by omega)
    obtain ⟨_, _, h4⟩ := air_step H h1 h3
    rw [show b + (k + 1) = b + k + 1 by omega, h2.2.1] at hu
    have ih := back_speed H k (u - gSlow sy m) (fun i h6 h7 => h i h6 (by omega)) (by omega)
    have hm : gSlow sy m * ((k + 1 : Nat) : Int) = gSlow sy m * (k : Int) + gSlow sy m := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [hm]
    omega

/-- with no wall hit, the states of the fall -/
theorem fall_states (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (hair : ∀ n, r.C ≤ n → n < r.C + N.fall → AirIn (r.fr.inp (n + 1))) :
    ∀ d, d ≤ N.fall → r.C + d ≤ r.t0 → FallSt sy (r.fr.hs (r.C + d))
  | 0, _, _ => start_fall r H
  | d + 1, h1, h2 => by
    have ih := fall_states H hw hair d (by omega) (by omega)
    have h3 := hair (r.C + d) (by omega) (by omega)
    have hg := H.nums.hit_ge
    have hf : Follow sy m r.fr (r.C + d) := hw _ (by omega) (by omega)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega, hf.2.1]
    exact (air_step H ih h3).1

/-! ### Standing -/

/-- with `Follow` on the frame, off the floor he is not standing at its end -/
theorem st_ne {n : Nat} (hn : r.C ≤ n) (h1 : n + 1 < r.C + N.standF) (hf : Follow sy m r.fr n) (h2 : ¬OnFloor sy (r.fr.vs (n + 1))) :
    (r.fr.vs (n + 1)).st ≠ 0 :=
  fun h3 => r.stand_wall n hn h1 h3 h2 hf

/-- as long as he has touched nothing, the frames of the fall are air frames -/
theorem fall_air (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n < r.C + N.fall) (hall : ∀ j, r.C ≤ j → j < n → Follow sy m r.fr j) :
    AirIn (r.fr.inp (n + 1)) := by
  have hle := H.nums.fall_le
  apply r.air_in n h1 (by omega)
  by_cases he : n = r.C
  · rw [he, r.v_start.1]
    decide
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact st_ne r (by omega) (by omega) (hall n' (by omega) (by omega)) (r.fall_long _ h1 h2)

/-! ### The left wall -/

/-- the first frame that does not follow `hstep` -/
theorem first_hit {fr : Frames} {C : Nat} : ∀ n, (¬∀ j, C ≤ j → j < n → Follow sy m fr j) →
    ∃ h, C ≤ h ∧ h < n ∧ ¬Follow sy m fr h ∧ ∀ j, C ≤ j → j < h → Follow sy m fr j
  | 0, hn => absurd (fun j _ h2 => absurd h2 (by omega)) hn
  | n + 1, hn => by
    by_cases h : ∀ j, C ≤ j → j < n → Follow sy m fr j
    · by_cases hc : C ≤ n ∧ ¬Follow sy m fr n
      · exact ⟨n, hc.1, by omega, hc.2, h⟩
      · exfalso
        apply hn
        intro j h1 h2
        by_cases h3 : j < n
        · exact h j h1 h3
        · have h4 : j = n := by omega
          subst h4
          by_cases h5 : Follow sy m fr j
          · exact h5
          · exact absurd ⟨h1, h5⟩ hc
    · obtain ⟨k, h1, h2, h3, h4⟩ := first_hit n h
      exact ⟨k, h1, by omega, h3, h4⟩

/-- the last frame stopped at the wall, up to `w`, and the frames from it on -/
structure Anchor (sy : Syms) (m : Machine) (N : Nums) (fr : Frames) (C w a : Nat) : Prop where
  ge : C + N.wallF ≤ a
  le : a ≤ w
  P_le : fr.P a ≤ N.wallP
  J' : J sy m (fr.hs a) N.stopPhi
  rs : (fr.hs a).rs = 0
  fol : ∀ i, a ≤ i → i < w → Follow sy m fr i

theorem anchor_P (H : Checks sy m N) {w a : Nat} (ha : Anchor sy m N r.fr r.C w a) :
    r.fr.P w ≤ N.wallP + dbound sy m N.stopPhi (w - (r.C + N.wallF)) := by
  have hF := H.air.pot
  have hfol : ∀ j, a ≤ j → j < a + (w - a) → Follow sy m r.fr j := fun j h1 h2 => ha.fol j h1 (by have := ha.le; omega)
  have h1 := hdist_seg a (w - a) hfol
  have h2 := dist_le hF _ _ _ ha.J' (inputs_seg a (w - a) hfol)
  rw [length_seg] at h2
  have hle := ha.le
  have hge := ha.ge
  rw [show a + (w - a) = w by omega] at h1
  obtain ⟨k, hk⟩ : ∃ k, w - (r.C + N.wallF) = (w - a) + k := ⟨a - (r.C + N.wallF), by omega⟩
  have h3 := dbound_mono hF (w - a) k N.stopPhi H.nums.stop_nonneg
  rw [← hk] at h3
  have h4 := ha.P_le
  omega

/-- with no hit before `h`, a position at `X`, far from the start, is late -/
theorem left_far (H : Checks sy m N) {h K : Nat} {X : Int} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ X) (hf : X < (room sy N).P0 - leftDist sy m (phi sy m (room sy N).s0) K) : r.C + K < h := by
  by_cases hc : r.C + K < h
  · exact hc
  · exfalso
    have hF := H.air.pot
    have hfol : ∀ j, r.C ≤ j → j < r.C + (h - r.C) → Follow sy m r.fr j := fun j h3 h4 => h2 j h3 (by omega)
    have h3 := hdist_seg r.C (h - r.C) hfol
    rw [show r.C + (h - r.C) = h by omega] at h3
    have hJ : J sy m (r.fr.hs r.C) (phi sy m (room sy N).s0) := by
      refine ⟨(start_fall r H).dom, by rw [r.start]; exact Int.le_refl _, fun h4 => absurd (start_fall r H).rs h4⟩
    have h4 := left_dist_le hF _ _ _ hJ (inputs_seg r.C (h - r.C) hfol)
    rw [length_seg] at h4
    obtain ⟨k, hk⟩ : ∃ k, K = (h - r.C) + k := ⟨K - (h - r.C), by omega⟩
    have h5 := leftDist_mono hF (h - r.C) k _ (phi0_nonneg H)
    rw [← hk] at h5
    have h7 := r.startP0
    omega

/-- the first wall frame is late: the wall is far from the start -/
theorem wall_first (H : Checks sy m N) {h : Nat} (h1 : r.C ≤ h) (h2 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j)
    (hP : r.fr.P h ≤ N.wallP) : r.C + N.wallF ≤ h + 1 := by
  have h3 := left_far r H h1 h2 hP H.nums.wall_far
  have h4 := H.nums.wall_two
  omega

/-- from the first wall frame on, up to `runF + 1`, there is a last wall frame -/
theorem anchor_at (H : Checks sy m N) {h : Nat} (h1 : r.C ≤ h) (h2 : h + 1 < r.C + N.hitF) (h3 : ¬Follow sy m r.fr h)
    (h4 : ∀ j, r.C ≤ j → j < h → Follow sy m r.fr j) (ht : h < r.t0) :
    ∀ d, h + 1 + d ≤ r.C + N.runF + 1 → h + 1 + d ≤ r.t0 → ∃ a, Anchor sy m N r.fr r.C (h + 1 + d) a
  | 0, _, _ => by
    have hw := r.wall h h1 h2 h3
    have hs := (r.frames h h1 ht).resolve_left h3
    exact ⟨h + 1, wall_first r H h1 h4 hw.before, by omega, hw.after, ⟨hs.1, hs.2.1, fun h5 => absurd hw.run h5⟩, hw.run,
      fun i h5 h6 => by omega⟩
  | d + 1, h5, h6 => by
    obtain ⟨a, ha⟩ := anchor_at H h1 h2 h3 h4 ht d (by omega) (by omega)
    rw [show h + 1 + (d + 1) = h + 1 + d + 1 by omega] at h6 ⊢
    have hC : r.C ≤ h + 1 + d := by omega
    by_cases hf : Follow sy m r.fr (h + 1 + d)
    · refine ⟨a, ha.ge, by have := ha.le; omega, ha.P_le, ha.J', ha.rs, fun i h7 h8 => ?_⟩
      by_cases h9 : i < h + 1 + d
      · exact ha.fol i h7 h9
      · rw [show i = h + 1 + d by omega]
        exact hf
    · have hw : WallAt N r.fr (h + 1 + d) := by
        by_cases h7 : h + 1 + d + 1 < r.C + N.hitF
        · exact r.wall _ hC h7 hf
        · rcases r.late _ (by omega) (by omega) hf with h8 | h8
          · exact h8
          · exfalso
            have hn := H.nums
            have h9 := anchor_P r H ha
            have hge := ha.ge
            obtain ⟨k, hk⟩ : ∃ k, N.runF - N.wallF = (h + 1 + d - (r.C + N.wallF)) + k :=
              ⟨N.runF - N.wallF - (h + 1 + d - (r.C + N.wallF)), by omega⟩
            have h10 := dbound_mono H.air.pot (h + 1 + d - (r.C + N.wallF)) k N.stopPhi hn.stop_nonneg
            rw [← hk] at h10
            have h11 := hn.wall_late
            omega
      have hs := (r.frames _ hC (by omega)).resolve_left hf
      exact ⟨h + 1 + d + 1, by have := ha.ge; have := ha.le; omega, by omega, hw.after,
        ⟨hs.1, hs.2.1, fun h7 => absurd hw.run h7⟩, hw.run, fun i h7 h8 => by omega⟩

/-- with a wall hit before `hitF`: the anchor of any frame from `hitF - 1` to `runF + 1` -/
theorem anchor_of_wall (H : Checks sy m N) (hw : ¬NoWall sy m N r.fr r.C) {w : Nat} (h1 : r.C + N.hitF - 1 ≤ w)
    (h2 : w ≤ r.C + N.runF + 1) (h3 : w ≤ r.t0) : ∃ a, Anchor sy m N r.fr r.C w a := by
  have hg := H.nums.hit_ge
  have hn : ¬∀ j, r.C ≤ j → j < r.C + N.hitF - 1 → Follow sy m r.fr j := fun h4 => hw fun n h5 h6 => h4 n h5 (by omega)
  obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hn
  obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (w - (h + 1)) (by omega) (by omega)
  rw [show h + 1 + (w - (h + 1)) = w by omega] at ha
  exact ⟨a, ha⟩

/-! ### Before `hitF` he is not at the corner -/

/-- **`corner_late`**: before `hitF` he is left of the corner. With no hit, the air frames of the fall and two more frames. With a hit, the
potential from the wall -/
theorem corner_late (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n < r.C + N.hitF) (h3 : n ≤ r.t0) : r.fr.P n < cornerP sy := by
  have hN := H.nums
  have hg := hN.hit_ge
  have hA := hN.air_pos
  by_cases hall : ∀ j, r.C ≤ j → j < n → Follow sy m r.fr j
  · have hair : ∀ i, r.C ≤ i → i < n → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h4 h5 h6 =>
      ⟨hall i h4 h5, fall_air r H h4 h6 (fun j h7 h8 => hall j h7 (by omega))⟩
    have hp : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := psiP_start r
    have hp0 := phi0_nonneg H
    have hcap0 : 0 ≤ capDist sy m (N.hitF - 1 - N.fall) := by
      have := cap_mono (m := m) hA 0 (N.hitF - 1 - N.fall)
      simpa [capDist] using this
    have hc := hN.corner_open
    have hP1 := r.startP1
    by_cases hn : n ≤ r.C + N.fall
    · obtain ⟨_, _, h4⟩ := fall_run r H (start_fall r H) hp (n - r.C) (fun i h5 h6 => hair i h5 (by omega) (by omega))
      rw [show r.C + (n - r.C) = n by omega] at h4
      obtain ⟨k, hk⟩ : ∃ k, N.fall = (n - r.C) + k := ⟨N.fall - (n - r.C), by omega⟩
      have h5 := airDist_mono (sy := sy) (m := m) hp0 hN.a1_nonneg (n - r.C) k
      rw [← hk] at h5
      omega
    · obtain ⟨h4, _, h5⟩ := fall_run r H (start_fall r H) hp N.fall (fun i h5 h6 => hair i h5 (by omega) (by omega))
      have hfol : ∀ j, r.C + N.fall ≤ j → j < r.C + N.fall + (n - (r.C + N.fall)) → Follow sy m r.fr j := fun j h6 h7 =>
        hall j (by omega) (by omega)
      have h6 := hdist_seg (r.C + N.fall) (n - (r.C + N.fall)) hfol
      rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at h6
      have h7 := AirCap.dist_capped H.air _ _ h4.dom h4.cap (inputs_seg (r.C + N.fall) (n - (r.C + N.fall)) hfol)
      rw [length_seg] at h7
      obtain ⟨k, hk⟩ : ∃ k, N.hitF - 1 - N.fall = (n - (r.C + N.fall)) + k := ⟨N.hitF - 1 - N.fall - (n - (r.C + N.fall)), by omega⟩
      have h8 := cap_mono (m := m) hA (n - (r.C + N.fall)) k
      rw [← hk] at h8
      omega
  · obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hall
    obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (n - (h + 1)) (by have := hN.hit_run; omega) (by omega)
    rw [show h + 1 + (n - (h + 1)) = n by omega] at ha
    have h8 := anchor_P r H ha
    have hge := ha.ge
    have hle := ha.le
    obtain ⟨k, hk⟩ : ∃ k, N.hitF - 1 - N.wallF = (n - (r.C + N.wallF)) + k := ⟨N.hitF - 1 - N.wallF - (n - (r.C + N.wallF)), by omega⟩
    have h9 := dbound_mono H.air.pot (n - (r.C + N.wallF)) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h9
    have h10 := hN.wall_corner
    omega

/-- he is not past the block's right end before `hitF` -/
theorem t0_late (H : Checks sy m N) : r.C + N.hitF ≤ r.t0 := by
  by_cases h : r.C + N.hitF ≤ r.t0
  · exact h
  · exfalso
    have h1 := corner_late r H r.t0_ge (by omega) (Nat.le_refl _)
    have h2 := r.past
    have h3 := H.nums.corner_goal
    omega

/-! ### The heights after the fall -/

/-- with no wall: from the fall on, he is on the floor or in the first frames of a jump from the floor -/
theorem v_chain (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) :
    ∀ d, d ≤ 1 + N.rise → OnFloor sy (r.fr.vs (r.C + N.fall + d)) ∨
      ∃ T, r.C + N.fall ≤ T ∧ T < r.C + N.fall + d ∧ OnArc sy m N r.fr T (r.C + N.fall + d)
  | 0, _ => Or.inl (r.floor_at hw)
  | d + 1, h1 => by
    have ih := v_chain H hw d (by omega)
    have hv := r.vframes hw (r.C + N.fall + d) (by omega) (by omega)
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega]
    rcases ih with hf | ⟨T, h2, h3, ha⟩
    · cases hv with
      | stay _ h2 _ => exact Or.inl h2
      | takeoff _ x hx h2 _ =>
        refine Or.inr ⟨r.C + N.fall + d, by omega, by omega, by omega, x, x, hx, ?_, h2⟩
        rw [show r.C + N.fall + d + 1 - (r.C + N.fall + d + 1) = 0 by omega]
        exact .refl _
      | air h2 _ _ => exact absurd hf.1 h2
      | fall h2 _ => exact absurd hf.1 h2
      | other h2 _ => exact absurd hf h2
    · exact Or.inr ⟨T, h2, by omega, (arc_next H ha (by omega) hv).1⟩

/-- **`low_by`**: through the low frames of the earliest jump he is not far past the corner. With no wall, the heights and the collision
routine; with a wall hit, the potential from the wall -/
theorem low_by (H : Checks sy m N) {n : Nat} (h1 : r.C ≤ n) (h2 : n ≤ r.C + N.fall + 1 + N.rise) (h3 : n ≤ r.t0) :
    r.fr.P n ≤ cornerP sy + N.lowSlack := by
  have hN := H.nums
  have hl := hN.low_nonneg
  by_cases hn : n < r.C + N.hitF
  · have := corner_late r H h1 hn h3
    omega
  by_cases hw : NoWall sy m N r.fr r.C
  · refine (r.low_at n (by omega) h2 h3 ?_).1
    rcases v_chain r H hw (n - (r.C + N.fall)) (by omega) with hf | ⟨T, h4, h5, ha⟩
    · rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by have := hN.hit_ge; omega] at hf
      rw [hf.2]
      exact hN.corner_le
    · rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by have := hN.hit_ge; omega] at h5 ha
      exact (arc_facts H ha (by omega)).1
  · have hg := hN.hit_run
    have hmin : min n (r.C + N.runF + 1) ≤ r.t0 := by omega
    obtain ⟨a, ha⟩ := anchor_of_wall r H hw (w := min n (r.C + N.runF + 1)) (by omega) (by omega) hmin
    have h4 := anchor_P r H ha
    have hge := ha.ge
    have hle := ha.le
    obtain ⟨k, hk⟩ : ∃ k, N.runF + 1 - N.wallF = (min n (r.C + N.runF + 1) - (r.C + N.wallF)) + k :=
      ⟨N.runF + 1 - N.wallF - (min n (r.C + N.runF + 1) - (r.C + N.wallF)), by omega⟩
    have h5 := dbound_mono H.air.pot (min n (r.C + N.runF + 1) - (r.C + N.wallF)) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h5
    have h6 := hN.wall_low
    have ht : (0 : Int) ≤ 16 * (top sy : Int) := by omega
    have h7 := reach_le (P := r.fr.P) (u := min n (r.C + N.runF + 1)) (B := r.fr.P (min n (r.C + N.runF + 1))) (μ := 16 * (top sy : Int))
      (w := r.t0) (Int.le_refl _) ht (fun j h8 h9 => Or.inl (r.move_top j (by omega) h9)) (n - min n (r.C + N.runF + 1)) (by omega)
    rw [show min n (r.C + N.runF + 1) + (n - min n (r.C + N.runF + 1)) = n by omega] at h7
    have h8 : 16 * (top sy : Int) * ((n - min n (r.C + N.runF + 1) : Nat) : Int) ≤
        16 * (top sy : Int) * ((N.fall + 1 + N.rise - (N.runF + 1) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) ht
    omega

/-! ### `RunningSpeed` by `runF` -/

theorem rs_step (F : Facts sy m) {s : HS} (hD : inD sy s = true) (hrs : s.rs = 0) (hv : (sbyte s.v).natAbs < sy.RunSpeedMin.toNat)
    {i : HIn} (hi : i ∈ inputs) : (hstep sy m s i).rs = 0 := by
  have h4 := F.check s hD i hi
  simp only [stepOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h4
  rcases h4.2 with (h5 | h5) | h5
  · exact h5
  · exact absurd hrs h5
  · omega

/-- from a state that passes `safeFrom` at the end of the fall, `RunningSpeed` stays 0 through `runF` -/
theorem rs_of_safe (H : Checks sy m N) (h0 : (r.fr.hs (r.C + N.fall)).rs = 0)
    (hs : safeFrom sy m (N.runF - N.fall - 1) (r.fr.hs (r.C + N.fall)) = true) :
    ∀ d, d ≤ N.runF - N.fall - 1 → r.C + N.fall + d ≤ r.t0 →
      (r.fr.hs (r.C + N.fall + d)).rs = 0 ∧ safeFrom sy m (N.runF - N.fall - 1 - d) (r.fr.hs (r.C + N.fall + d)) = true
  | 0, _, _ => ⟨h0, hs⟩
  | d + 1, h1, h2 => by
    obtain ⟨h3, h4⟩ := rs_of_safe H h0 hs d (by omega) (by omega)
    have hN := H.nums
    have hge := hN.run_ge
    rw [show r.C + N.fall + (d + 1) = r.C + N.fall + d + 1 by omega]
    rw [show N.runF - N.fall - 1 - d = (N.runF - N.fall - 1 - (d + 1)) + 1 by omega] at h4
    by_cases hf : Follow sy m r.fr (r.C + N.fall + d)
    · rw [hf.2.1]
      have hD := inD_at r H (n := r.C + N.fall + d) (by omega) (by omega)
      have h5 := safe_step H.air.pot hN.gs_le H.normI hD h3 h4 hf.1
      exact ⟨h5.2, h5.1⟩
    · have hs2 := (r.frames (r.C + N.fall + d) (by omega) (by omega)).resolve_left hf
      refine ⟨r.stop_run _ (by omega) (by omega) hf, ?_⟩
      refine safe_of_bound H.air.pot hN.gs_le _ hs2.2.1 ?_
      obtain ⟨k, hk⟩ : ∃ k, N.runF - N.fall - 1 = (N.runF - N.fall - 1 - (d + 1)) + k := ⟨d + 1, by omega⟩
      have h5 := iterN_count H.air.pot (N.runF - N.fall - 1 - (d + 1)) k N.stopPhi
      rw [← hk] at h5
      have h6 := hN.stop_safe
      omega

/-- **`RunningSpeed` not 0 at a stop by `runF`, with no wall**: he moved left fast at the end of the fall, so he is far back. Moving right, or
slower, `safeFrom` shows `RunningSpeed` is 0 -/
theorem no_wall_back (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) {h' : Nat} (hc : r.C + N.hitF ≤ h') (hr : h' ≤ r.C + N.runF)
    (ht : h' ≤ r.t0) (hrs : (r.fr.hs h').rs ≠ 0) : r.fr.P h' ≤ N.backP := by
  have hN := H.nums
  have hg := hN.hit_ge
  have hge := hN.run_ge
  have F := H.air.pot
  have hair : ∀ i, r.C ≤ i → i < r.C + N.fall → AirIn (r.fr.inp (i + 1)) := fun i h1 h2 =>
    fall_air r H h1 h2 (fun j h3 h4 => hw j h3 (by omega))
  have hp : psiP sy m (r.fr.hs r.C) ≤ phi sy m (room sy N).s0 := psiP_start r
  have hrun : ∀ i, r.C ≤ i → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 =>
    ⟨hw i h1 (by omega), hair i h1 h2⟩
  obtain ⟨hst, hpsi, hP⟩ := fall_run r H (start_fall r H) hp N.fall (fun i h1 h2 => hrun i h1 h2)
  -- `safeFrom` at the end of the fall gives `RunningSpeed` 0 at `h'`
  have hno : safeFrom sy m (N.runF - N.fall - 1) (r.fr.hs (r.C + N.fall)) = true → False := fun hs => by
    by_cases hlast : h' ≤ r.C + N.fall + (N.runF - N.fall - 1)
    · obtain ⟨h1, _⟩ := rs_of_safe r H hst.rs hs (h' - (r.C + N.fall)) (by omega) (by omega)
      rw [show r.C + N.fall + (h' - (r.C + N.fall)) = h' by omega] at h1
      exact hrs h1
    · have hh : h' = r.C + N.fall + (N.runF - N.fall - 1) + 1 := by omega
      obtain ⟨h1, h2⟩ := rs_of_safe r H hst.rs hs (N.runF - N.fall - 1) (Nat.le_refl _) (by omega)
      rw [show N.runF - N.fall - 1 - (N.runF - N.fall - 1) = 0 by omega] at h2
      simp only [safeFrom, decide_eq_true_eq] at h2
      apply hrs
      rw [hh]
      by_cases hf : Follow sy m r.fr (r.C + N.fall + (N.runF - N.fall - 1))
      · rw [hf.2.1]
        exact rs_step F (inD_at r H (by omega) (by omega)) h1 h2 hf.1
      · exact r.stop_run _ (by omega) (by omega) hf
  by_cases hV : 0 ≤ V (r.fr.hs (r.C + N.fall))
  · exfalso
    apply hno
    -- moving right: the check
    have hphi := psiP_eq_phi (sy := sy) (m := m) hV
    obtain ⟨hD, hcap, hfd, hrs0⟩ := hst
    generalize r.fr.hs (r.C + N.fall) = s at *
    obtain ⟨v, f, fd, md, rs⟩ := s
    simp only at hfd hrs0
    subst hfd
    subst hrs0
    have hD' := hD
    simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD'
    obtain ⟨⟨⟨hv, _⟩, hmd⟩, _⟩ := hD'
    have hvs : v ∈ speedsB sy := by
      have hsp := H.air.speeds
      simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.contains_iff_mem] at hsp
      rcases hsp v (mem_bytes v) with h | h
      · rw [h] at hv; exact absurd hv (by decide)
      · exact h
    have hcv : (sbyte v).natAbs < sy.AirFastSpeed.toNat := by
      simpa only [capped, decide_eq_true_eq] using hcap
    have hfr : f.toNat < 256 := f.toNat_lt
    have hv0 : 0 ≤ sbyte v := by
      unfold V at hV
      simp only at hV
      omega
    have hmem : ({ v, f, fd := 1, md, rs := 0 } : HS) ∈ safeStates sy :=
      List.mem_flatMap.2 ⟨v, List.mem_filter.2 ⟨hvs, by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hv0, hcv⟩⟩,
        List.mem_flatMap.2 ⟨f, mem_bytes f, List.mem_map.2 ⟨md, hmd, rfl⟩⟩⟩
    have hall := H.safe
    simp only [safeCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hall
    rcases hall _ hmem with h1 | h1
    · exact absurd (by rw [hphi]; exact hpsi) h1
    · exact h1
  · by_cases hq : phi sy m (r.fr.hs (r.C + N.fall)) ≤ N.safeP
    · exfalso
      exact hno (safe_of_bound F hN.gs_le _ hq hN.safe_bound)
    · -- moving left fast: he is far back
      have hle := hN.back_le
      have hb : r.C + N.fall - N.backK + N.backK = r.C + N.fall := by omega
      have hu : N.safeP + 1 - 2 * c sy m ≤ -V (r.fr.hs (r.C + N.fall)) := by
        have h1 := AirCap.w_le F (r.fr.hs (r.C + N.fall))
        unfold phi at hq
        omega
      rw [← hb] at hu
      have hst2 : ∀ i, r.C + N.fall - N.backK ≤ i → i < r.C + N.fall - N.backK + N.backK →
          FallSt sy (r.fr.hs i) ∧ Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 => by
        have h3 := fall_states r H hw hair (i - r.C) (by omega) (by omega)
        rw [show r.C + (i - r.C) = i by omega] at h3
        exact ⟨h3, hrun i (by omega) (by omega)⟩
      have h1 := back_run r H N.backK _ hst2 hu
      rw [hb] at h1
      obtain ⟨_, _, h2⟩ := fall_run r H (start_fall r H) hp (N.fall - N.backK) (fun i h3 h4 => hrun i h3 (by omega))
      rw [show r.C + (N.fall - N.backK) = r.C + N.fall - N.backK by omega] at h2
      have htop : (0 : Int) ≤ 16 * (top sy : Int) := by omega
      have h3 := reach_le (P := r.fr.P) (u := r.C + N.fall) (B := r.fr.P (r.C + N.fall)) (μ := 16 * (top sy : Int)) (w := r.t0)
        (Int.le_refl _) htop (fun j h4 h5 => Or.inl (r.move_top j (by omega) h5)) (h' - (r.C + N.fall)) (by omega)
      rw [show r.C + N.fall + (h' - (r.C + N.fall)) = h' by omega] at h3
      have h4 : 16 * (top sy : Int) * ((h' - (r.C + N.fall) : Nat) : Int) ≤ 16 * (top sy : Int) * ((N.runF - N.fall : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) htop
      have h5 := hN.back_ok
      have h6 := r.startP1
      omega

/-- a stop by `runF` with `RunningSpeed` not 0 is short of the goal -/
theorem run_short (H : Checks sy m N) {h' : Nat} (hs : Stop sy m N r.fr h') (hc : r.C + N.hitF ≤ h') (hr : h' ≤ r.C + N.runF)
    (h4 : h' ≤ r.t0) (hrs : (r.fr.hs h').rs ≠ 0) (ht : r.t0 ≤ r.C + N.goalF)
    (hin : ∀ i ∈ seg r.fr.inp h' (r.t0 - h'), i ∈ inputs)
    (h7 : r.fr.P r.t0 = r.fr.P h' + hdist sy m (r.fr.hs h') (seg r.fr.inp h' (r.t0 - h'))) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have h8 := fast_dist_le F _ _ _ hs.1 hs.2.1 hin
  rw [length_seg] at h8
  by_cases hw : NoWall sy m N r.fr r.C
  · have h1 := no_wall_back r H hw hc hr h4 hrs
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.hitF = (r.t0 - h') + k := ⟨N.goalF - N.hitF - (r.t0 - h'), by omega⟩
    have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hN.stop_nonneg
    rw [← hk] at h9
    have h10 := hN.hit_B
    omega
  · obtain ⟨a, ha⟩ := anchor_of_wall r H hw (w := h') (by omega) (by omega) h4
    have h1 := anchor_P r H ha
    have h9 := hN.wall_stops
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h9
    rcases h9 (h' - r.C) (List.mem_range.2 (by have := hN.goal_ge; omega)) with (h10 | h10) | h10
    · omega
    · omega
    · rw [show h' - r.C - N.wallF = h' - (r.C + N.wallF) by omega] at h10
      obtain ⟨k, hk⟩ : ∃ k, N.goalF - (h' - r.C) = (r.t0 - h') + k := ⟨N.goalF - (h' - r.C) - (r.t0 - h'), by omega⟩
      have h11 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hN.stop_nonneg
      rw [← hk] at h11
      omega

/-- **A stop from `hitF` on is short of the goal**, whatever he does after it: the speed is near 0, and the potential bounds the
rest. This covers a hit at the corner on the floor or in the air, a jump with a stale stored speed after it, and a jump from the
side of the block. -/
theorem stop_short (H : Checks sy m N) {h : Nat} (h1 : r.C + N.hitF ≤ h) (h2 : h ≤ r.t0) (hs : Stop sy m N r.fr h)
    (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  obtain ⟨h', h3, h4, h5, h7, hin⟩ := after_stop r (a := r.C + N.hitF) (by omega) (by omega) ⟨h, h1, h2, hs⟩
  have F := H.air.pot
  have hn := H.nums
  have hrl := hn.run_le
  have hl0 := hn.low_nonneg
  by_cases hrun : h' ≤ r.C + N.runF
  · by_cases hz : (r.fr.hs h').rs = 0
    · have hJ : J sy m (r.fr.hs h') N.stopPhi := ⟨h5.1, h5.2.1, fun hne => absurd hz hne⟩
      have h8 := dist_le F _ _ _ hJ hin
      rw [length_seg] at h8
      obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.hitF = (r.t0 - h') + k := ⟨N.goalF - N.hitF - (r.t0 - h'), by omega⟩
      have h9 := dbound_mono F (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.hit_J
      have h11 := low_by r H (n := h') (by omega) (by omega) h4
      omega
    · exact run_short r H h5 h3 hrun h4 hz ht hin h7
  · have h8 := fast_dist_le F _ _ _ h5.1 h5.2.1 hin
    rw [length_seg] at h8
    by_cases hlow : h' ≤ r.C + N.fall + 1 + N.rise
    · obtain ⟨k, hk⟩ : ∃ k, N.goalF - (N.runF + 1) = (r.t0 - h') + k := ⟨N.goalF - (N.runF + 1) - (r.t0 - h'), by omega⟩
      have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.hit_F
      have h11 := low_by r H (n := h') (by omega) hlow h4
      omega
    · -- later: at most the top speed after the low frames, and not far past the corner
      let j := h' - r.C
      have h9 := hn.hit_late
      simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h9
      rcases h9 j (List.mem_range.2 (by omega)) with h10 | h10
      · omega
      · obtain ⟨k, hk⟩ : ∃ k, N.goalF - j = (r.t0 - h') + k := ⟨N.goalF - j - (r.t0 - h'), by omega⟩
        have h11 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
        rw [← hk] at h11
        have h12 := h5.2.2
        let u0 := r.C + N.fall + 1 + N.rise
        have h13 := reach_le (P := r.fr.P) (u := u0) (B := cornerP sy + N.lowSlack) (μ := 16 * (top sy : Int)) (w := r.t0)
          (low_by r H (n := u0) (by omega) (by omega) (by omega)) (by omega)
          (fun n h14 h15 => Or.inl (r.move_top n (by omega) h15)) (h' - u0) (by omega)
        rw [show u0 + (h' - u0) = h' by omega] at h13
        have h14 : ((j - (N.fall + 1 + N.rise) : Nat) : Int) = ((h' - u0 : Nat) : Int) := by
          congr 1
          omega
        rw [h14] at h10
        omega

/-- no stop from `hitF` on: on the low frames he is left of the corner -/
theorem left_of_corner (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {w : Nat}
    (hw : w ≤ r.t0) (hlow : ∀ n, r.C + N.hitF ≤ n → n ≤ w → LowAt sy m N r.fr n) :
    ∀ d, r.C + N.hitF + d ≤ w + 1 → d = 0 ∨ r.fr.P (r.C + N.hitF + d - 1) < cornerP sy
  | 0, _ => Or.inl rfl
  | d + 1, h => by
    right
    rw [show r.C + N.hitF + (d + 1) - 1 = r.C + N.hitF + d by omega]
    have hprev : r.fr.P (r.C + N.hitF + d - 1) < cornerP sy := by
      rcases left_of_corner H hs hw hlow d (by omega) with h0 | h0
      · subst h0
        have hF := H.nums.hit_ge
        exact corner_late r H (by omega) (by omega) (by omega)
      · exact h0
    obtain ⟨_, h1⟩ := hlow (r.C + N.hitF + d) (by omega) (by omega)
    rcases h1 with h1 | h1 | h1
    · exact absurd h1 (hs _ (by omega) (by omega))
    · exact h1
    · have hF := H.nums.hit_ge
      have h2 : Follow sy m r.fr (r.C + N.hitF + d - 1) :=
        follow_of r hs (by omega) (by omega) (by omega)
      have h3 := h2.2.2
      rw [show r.C + N.hitF + d - 1 + 1 = r.C + N.hitF + d by omega] at h3
      omega

theorem left_at (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) {w : Nat}
    (hw : w ≤ r.t0) (hlow : ∀ n, r.C + N.hitF ≤ n → n ≤ w → LowAt sy m N r.fr n) {n : Nat} (hC : r.C ≤ n) (hn : n ≤ w) :
    r.fr.P n < cornerP sy := by
  by_cases h1 : n < r.C + N.hitF
  · exact corner_late r H hC h1 (by omega)
  · rcases left_of_corner r H hs hw hlow (n + 1 - (r.C + N.hitF)) (by omega) with h2 | h2
    · omega
    · rwa [show r.C + N.hitF + (n + 1 - (r.C + N.hitF)) - 1 = n by omega] at h2

/-! ### Over the block in one jump -/

/-- **No landing on the block**: he does not pass over the whole block in one jump, from the floor or from its side -/
theorem no_landing (H : Checks sy m N) (o : Over sy m N r.fr r.C r.t0) : False := by
  have hn := H.nums
  have hy := H.lenY
  simp only [List.all_eq_true] at hy
  have hlenA := arc_len (hy o.y0 o.y0_mem) o.x_mem o.reach hn.len_ok.2.2.2 hn.len_ok.2.2.2
  simp only [ite_self] at hlenA
  have hT1 := o.T1_ge
  have hT2 := o.T1_lt
  have hpast := r.past
  have hA := hn.air_pos
  have hl0 := hn.low_nonneg
  have F := H.air.pot
  cases hcap : capped sy (r.fr.hs o.T1) with
  | true =>
    -- below the threshold: the air speed all the way
    have hc := capped_along r H (u := o.T1) (w := r.t0) hT1 (by omega) hcap o.air
    have h1 := reach_le (P := r.fr.P) (u := o.T1) (B := cornerP sy + N.stopSlack)
      (μ := 16 * ((sy.AirFastSpeed.toNat : Int) - 1)) (w := r.t0) o.start (by omega) (fun n h3 h4 => by
        rcases r.frames n (by omega) h4 with h5 | h5
        · left
          have h6 := hc (n + 1 - o.T1) (by omega)
          rw [show o.T1 + (n + 1 - o.T1) = n + 1 by omega] at h6
          simp only [capped, decide_eq_true_eq] at h6
          have h7 := h5.2.2
          omega
        · right
          exact h5.2.2) (r.t0 - o.T1) (by omega)
    rw [show o.T1 + (r.t0 - o.T1) = r.t0 by omega] at h1
    have h2 := hn.over_capped
    have h3 : r.t0 - o.T1 ≤ N.lenA + 1 := by omega
    have h4 : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((r.t0 - o.T1 : Nat) : Int) ≤
        16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((N.lenA + 1 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  | false =>
    -- at the threshold or more: it is a fast jump from the floor
    have hf : o.x.fast = true := by
      cases hf : o.x.fast with
      | true => rfl
      | false =>
        have := o.slowC hf
        rw [hcap] at this
        exact absurd this (by decide)
    obtain ⟨hg, hlowf⟩ := o.low hcap
    have hxm := o.x_mem
    rw [hg] at hxm
    have hlen := arc_len H.lenG hxm o.reach hn.len_ok.1 hn.len_ok.2.1
    rw [hf] at hlen
    simp only [if_true] at hlen
    let u0 := min (o.T1 + 1 + N.rise) r.t0
    have hu0 := hlowf u0 (by omega) (by omega) (by omega)
    by_cases hstop : ∃ h, u0 ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h
    · obtain ⟨h', h3, h4, h5, h7, hin⟩ := after_stop r (a := u0) (by omega) (by omega) hstop
      have h8 := fast_dist_le F _ _ _ h5.1 h5.2.1 hin
      rw [length_seg] at h8
      obtain ⟨k, hk⟩ : ∃ k, N.lenF - N.rise = (r.t0 - h') + k := ⟨N.lenF - N.rise - (r.t0 - h'), by omega⟩
      have h9 := fastDist_mono F.gf_nonneg (r.t0 - h') k N.stopPhi hn.stop_nonneg
      rw [← hk] at h9
      have h10 := hn.over_stop
      have h11 := h5.2.2
      omega
    · have h1 := reach_le (P := r.fr.P) (u := u0) (B := cornerP sy + N.lowSlack) (μ := 16 * (top sy : Int)) (w := r.t0)
        hu0 (by omega) (fun n h3 h4 => Or.inl (r.move_top n (by omega) h4)) (r.t0 - u0) (by omega)
      rw [show u0 + (r.t0 - u0) = r.t0 by omega] at h1
      have h2 := hn.over_top
      have h3 : 16 * (top sy : Int) * ((r.t0 - u0 : Nat) : Int) ≤ 16 * (top sy : Int) * ((N.lenF - N.rise : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega

/-! ### Landing on the block -/

/-- the pair of the jump table for this landing -/
theorem window_pair (H : Checks sy m N) {x u : Arc} {n : Nat} (hx : x ∈ arcStart sy m (groundY sy) N.h)
    (hreach : Cert.Reach (arcSucc sy m N.h) x n u)
    (hw : falling u.s = true ∧ standY sy N.h ≤ u.s.y.toNat ∧ u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat) :
    u.k = n ∧ ∃ q ∈ (if x.fast then N.fast else N.slow), q.1 ≤ u.low ∧ q.2 ≤ u.k := by
  have hn := H.nums
  have hlen := arc_len H.lenG hx hreach hn.len_ok.1 hn.len_ok.2.1
  have hle : n ≤ arcFrames := by
    have h1 := hn.len_ok.1
    have h2 := hn.len_ok.2.1
    split at hlen <;> omega
  have h1 := arc_spec H.window x hx n u hle hreach
  obtain ⟨h2, h3⟩ := arc_k hreach
  have h4 := arcStart_k hx
  refine ⟨by omega, ?_⟩
  have hw' : (falling u.s && decide (standY sy N.h ≤ u.s.y.toNat) &&
      decide (u.s.y.toNat < standY sy N.h + sy.LandDepth.toNat)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  unfold windowOk at h1
  rw [hw', h3] at h1
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

/-- the slow bound, moved to the earliest frames of the pair: landing later never raises it -/
theorem pair_bound (hA : 1 ≤ sy.AirFastSpeed.toNat) {q1 q2 S0 L0 s L t G : Nat} (h1 : S0 + q2 = L0 + q1) (hq : q1 ≤ q2)
    (hs : S0 ≤ s) (hL : L0 ≤ L) (hsL : s ≤ L) (hLt : L ≤ t) (htG : t ≤ G) :
    16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((L - s : Nat) : Int) + capDist sy m (t - L) ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((q2 - q1 : Nat) : Int) + capDist sy m (G - L0) := by
  have h0 : (0 : Int) ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by omega
  have h2 := landing_later (sy := sy) (m := m) ((q2 - q1 : Nat) : Int) (t - L) (L - L0)
  have h3 : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((L - s : Nat) : Int) ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (((q2 - q1 : Nat) : Int) + ((L - L0 : Nat) : Int)) :=
    Int.mul_le_mul_of_nonneg_left (by omega) h0
  have h4 := cap_mono (m := m) hA (t - L + (L - L0)) (G - t)
  rw [show t - L + (L - L0) + (G - t) = G - L0 by omega] at h4
  omega

/-! ### The floor up to the takeoff -/

/-- **`floor_low`**, with no wall: up to a takeoff by the last frame searched he has stayed on the floor. An earlier jump would still be in its
low frames -/
theorem floor_all (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0)
    (hearly : a.T1 ≤ r.C + N.fall + N.lastG) {n : Nat} (h1 : r.C + N.fall ≤ n) (h2 : n ≤ a.T1) : OnFloor sy (r.fr.vs n) := by
  have hN := H.nums
  have hl := hN.last_le
  rcases v_chain r H hw (n - (r.C + N.fall)) (by omega) with hf | ⟨T, h3, h4, ha⟩
  · rwa [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at hf
  · exfalso
    rw [show r.C + N.fall + (n - (r.C + N.fall)) = n by omega] at h4 ha
    have hgo : ∀ e, n + e ≤ a.T1 → OnArc sy m N r.fr T (n + e) := by
      intro e
      induction e with
      | zero => exact fun _ => ha
      | succ e ih =>
        intro h5
        have h6 := ih (by omega)
        rw [show n + (e + 1) = n + e + 1 by omega]
        exact (arc_next H h6 (by omega) (r.vframes hw (n + e) (by omega) (by omega))).1
    have h7 := hgo (a.T1 - n) (by omega)
    rw [show n + (a.T1 - n) = a.T1 by omega] at h7
    exact (arc_facts H h7 (by omega)).2.2 a.T1_floor.1

/-- the frames of the jump's low frames -/
theorem arc_from (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0)
    (hearly : a.T1 ≤ r.C + N.fall + N.lastG) : ∀ e, e ≤ N.rise → OnArc sy m N r.fr a.T1 (a.T1 + 1 + e)
  | 0, _ => by
    refine ⟨by omega, a.x, a.x, a.x_mem, ?_, a.x_vs⟩
    rw [show a.T1 + 1 + 0 - (a.T1 + 1) = 0 by omega]
    exact .refl _
  | e + 1, h1 => by
    have h2 := arc_from H hw a hearly e (by omega)
    have hT := a.T1_ge
    rw [show a.T1 + 1 + (e + 1) = a.T1 + 1 + e + 1 by omega]
    exact (arc_next H h2 (by omega) (r.vframes hw _ (by omega) (by omega))).1

/-- **`floor_low`**: the frames from `hitF` to a takeoff by the last frame searched are low -/
theorem floor_low (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (a : Approach sy m N r.fr r.C r.t0) (hearly : a.T1 ≤ r.C + N.fall + N.lastG)
    {n : Nat} (h1 : r.C + N.hitF ≤ n) (h2 : n ≤ a.T1) : LowAt sy m N r.fr n := by
  have hN := H.nums
  have hT := a.T1_lt
  have hl := hN.last_le
  have hg := hN.hit_ge
  have h3 := floor_all r H hw a hearly (n := n) (by omega) h2
  refine r.low_at n h1 (by omega) (by omega) ?_
  rw [h3.2]
  exact hN.corner_le

/-- **`early`**, with no wall: a fast takeoff by the last frame searched has the frames of `FastTakeoff` -/
theorem early_of (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C)
    (a : Approach sy m N r.fr r.C r.t0) (hearly : a.T1 ≤ r.C + N.fall + N.lastG) : Early sy m N r.fr r.C a.T1 := by
  have hN := H.nums
  have hT := a.T1_ge
  have hl := hN.last_le
  have harc0 : (r.fr.vs (a.T1 + 1)).st ≠ 0 := (arc_facts H (arc_from r H hw a hearly 0 (by omega)) (by omega)).2.2
  have hhg := hN.hit_ge
  refine ⟨hw, fun n h1 h2 => fall_air r H h1 h2 (fun j h3 h4 => hw j h3 (by omega)), ?_, ?_, ?_⟩
  · intro n h1 h2
    have h3 := floor_all r H hw a hearly h1 (by omega)
    have h4 := floor_all r H hw a hearly (n := n + 1) (by omega) (by omega)
    cases r.vframes hw n h1 (by omega) with
    | stay _ _ hi => exact hi
    | takeoff _ x hx h5 _ =>
      exfalso
      have h6 : OnArc sy m N r.fr n (n + 1) := by
        refine ⟨by omega, x, x, hx, ?_, h5⟩
        rw [show n + 1 - (n + 1) = 0 by omega]
        exact .refl _
      exact (arc_facts H h6 (by omega)).2.2 h4.1
    | air h5 _ _ => exact absurd h3.1 h5
    | fall h5 _ => exact absurd h3.1 h5
    | other h5 _ => exact absurd h3 h5
  · cases r.vframes hw a.T1 hT (by omega) with
    | stay _ h2 _ => exact absurd h2.1 harc0
    | takeoff _ _ _ _ hi => exact hi
    | air h1 _ _ => exact absurd a.T1_floor.1 h1
    | fall h1 _ => exact absurd a.T1_floor.1 h1
    | other h1 _ => exact absurd a.T1_floor h1
  · intro n h1 h2
    have h3 := arc_from r H hw a hearly (n - (a.T1 + 1)) (by omega)
    rw [show a.T1 + 1 + (n - (a.T1 + 1)) = n by omega] at h3
    exact (arc_next H h3 (by omega) (r.vframes hw n (by omega) (by omega))).2

/-- with no wall hit and no stop from `hitF` on, the stored speed is `|v|`, or below the threshold. So a fast jump reads `|v|` -/
theorem ab_or (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) :
    ∀ d, r.C + d ≤ r.t0 → r.fr.ab (r.C + d) = (sbyte (r.fr.hs (r.C + d)).v).natAbs ∨ r.fr.ab (r.C + d) < sy.AirFastSpeed.toNat
  | 0, _ => by
    have h1 := r.ab_start
    have h2 := H.nums.air_pos
    exact Or.inr (by simpa using (by omega : r.fr.ab r.C < sy.AirFastSpeed.toNat))
  | d + 1, h => by
    have ih := ab_or H hw hs d (by omega)
    rw [show r.C + (d + 1) = r.C + d + 1 by omega]
    by_cases hf : Follow sy m r.fr (r.C + d)
    · rcases r.ab_follow (r.C + d) (by omega) (by omega) hf with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · rw [h1, h2]
        exact ih
    · by_cases h1 : r.C + d + 1 < r.C + N.hitF
      · exact absurd (hw _ (by omega) h1) hf
      · exact absurd ((r.frames _ (by omega) (by omega)).resolve_left hf) (hs _ (by omega) (by omega))

/-! ### A wall hit: short of the goal with no jump analysis -/

/-- the distance to `t0` from a frame, with every frame following `hstep` -/
theorem dist_from (H : Checks sy m N) {u : Nat} {p : Int} (hJ : J sy m (r.fr.hs u) p) (hu : u ≤ r.t0)
    (hfol : ∀ i, u ≤ i → i < r.t0 → Follow sy m r.fr i) : r.fr.P r.t0 ≤ r.fr.P u + dbound sy m p (r.t0 - u) := by
  have hf : ∀ i, u ≤ i → i < u + (r.t0 - u) → Follow sy m r.fr i := fun i h1 h2 => hfol i h1 (by omega)
  have h1 := hdist_seg u (r.t0 - u) hf
  rw [show u + (r.t0 - u) = r.t0 by omega] at h1
  have h2 := dist_le H.air.pot _ _ _ hJ (inputs_seg u (r.t0 - u) hf)
  rw [length_seg] at h2
  omega

/-- `J` along frames that follow `hstep` -/
theorem J_run (F : Facts sy m) : ∀ (d u : Nat) (p : Int), J sy m (r.fr.hs u) p → (∀ i, u ≤ i → i < u + d → Follow sy m r.fr i) →
    J sy m (r.fr.hs (u + d)) (iterN sy m p d)
  | 0, _, _, h, _ => h
  | d + 1, u, p, h, hf => by
    have h1 := hf u (Nat.le_refl _) (by omega)
    have h2 := (step_J F h h1.1).1
    rw [← h1.2.1] at h2
    have h3 := J_run F d (u + 1) _ h2 (fun i h4 h5 => hf i (by omega) (by omega))
    rwa [show u + 1 + d = u + (d + 1) by omega] at h3

/-- two stands in the fall are apart: from a stand, a frame stopped by the wall, he needs speed to stand again -/
theorem stand_gap (H : Checks sy m N) {i j : Nat} (hi : r.C ≤ i) (hij : i < j) (hj : j < r.C + N.fall) (h1 : (r.fr.vs i).st = 0)
    (h2 : (r.fr.vs j).st = 0) : i + N.gapF ≤ j := by
  have hN := H.nums
  have F := H.air.pot
  have hle := hN.fall_le
  have hg := hN.hit_ge
  have hhr := hN.hit_run
  have hlate := t0_late r H
  have h2' := hN.gap_two
  have hiC : i ≠ r.C := fun h3 => by
    rw [h3, r.v_start.1] at h1
    exact absurd h1 (by decide)
  obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
  have h3 := r.stand_wall l (by omega) (by omega) h1 (r.fall_long _ hi (by omega))
  have hn : ¬∀ k, r.C ≤ k → k < l + 1 → Follow sy m r.fr k := fun h4 => h3 (h4 l (by omega) (by omega))
  obtain ⟨h, h4, h5, h6, h7⟩ := first_hit _ hn
  obtain ⟨a, ha⟩ := anchor_at r H h4 (by omega) h6 h7 (by omega) (j - 1 - (h + 1)) (by omega) (by omega)
  rw [show h + 1 + (j - 1 - (h + 1)) = j - 1 by omega] at ha
  have hal : l + 1 ≤ a := by
    by_cases h8 : l + 1 ≤ a
    · exact h8
    · exact absurd (ha.fol l (by omega) (by omega)) h3
  have hle2 := ha.le
  have h9 := J_run r F (j - 1 - a) a N.stopPhi ha.J' (fun k h10 h11 => ha.fol k h10 (by omega))
  rw [show a + (j - 1 - a) = j - 1 by omega] at h9
  have h10 := phi_ge F (r.fr.hs (j - 1))
  have h11 := h9.2.1
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h12 := r.stand_fast j' (by omega) (by omega) (by rw [← hj']; exact h2)
  rw [show j' = j - 1 by omega] at h12
  by_cases h13 : l + 1 + N.gapF ≤ j
  · exact h13
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, N.gapF - 2 = (j - 1 - a) + k := ⟨N.gapF - 2 - (j - 1 - a), by omega⟩
    have h14 := iterN_count F (j - 1 - a) k N.stopPhi
    rw [← hk] at h14
    have h15 := hN.gap_V
    omega

/-- the frame after the last wall frame: in `J` with `nxt`, below the threshold, and not far -/
theorem wall_next (H : Checks sy m N) {b : Nat} (hP : r.fr.P b ≤ N.wallP) (hJ : J sy m (r.fr.hs b) N.stopPhi) (hf : Follow sy m r.fr b) :
    J sy m (r.fr.hs (b + 1)) (nxt sy m N.stopPhi) ∧ capped sy (r.fr.hs (b + 1)) = true ∧ (r.fr.hs (b + 1)).rs = 0 ∧
      r.fr.P (b + 1) ≤ N.wallP + 16 * (nxt sy m N.stopPhi / 256) := by
  have F := H.air.pot
  have hN := H.nums
  obtain ⟨hJ1, h256, _⟩ := step_J F hJ hf.1
  rw [← hf.2.1] at hJ1 h256
  have h1 := phi_ge F (r.fr.hs (b + 1))
  have h2 := hJ1.2.1
  have h3 := hN.wall_phi
  have h4 : (r.fr.hs (b + 1)).f.toNat < 256 := (r.fr.hs (b + 1)).f.toNat_lt
  have h5 := hf.2.2
  refine ⟨hJ1, ?_, ?_, ?_⟩
  · simp only [capped, decide_eq_true_eq]
    unfold V at h1
    unfold theta at h3
    omega
  · by_cases h6 : (r.fr.hs (b + 1)).rs = 0
    · exact h6
    · have := hJ1.2.2 h6
      omega
  · omega

/-- **After a wall hit before `wallD`, facing right.** One frame of any kind, then air frames to the end of the fall: `Ψ` is small. Moving right
at the end of the fall, or with `Φ ≤ fastQ`, the potential gives the bound. Moving left fast, he has gone back -/
theorem wall_right (H : Checks sy m N) {b : Nat} (hge : r.C + N.wallF ≤ b) (hP : r.fr.P b ≤ N.wallP) (hJ : J sy m (r.fr.hs b) N.stopPhi)
    (hb : b + 1 ≤ r.C + N.fall) (hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i) (hb0 : b < r.t0) (hfall : r.C + N.fall ≤ r.t0)
    (hfd : (r.fr.hs (b + 1)).fd = 1) (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have ha1 := hN.a1_nonneg
  have hgs := F.gs_nonneg
  have hle := hN.fall_le
  have hfw := hN.fall_wall
  have hwk := hN.wall_k
  obtain ⟨hJ1, hc1, hrs1, hP1⟩ := wall_next r H hP hJ (hfol b (Nat.le_refl _) hb0)
  have hst1 : FallSt sy (r.fr.hs (b + 1)) := ⟨hJ1.1, hc1, hfd, hrs1⟩
  have hs0 := hN.stop_nonneg
  have hle1 := le_nxt F N.stopPhi
  have hgn : gSlow sy m ≤ nxt sy m N.stopPhi := by
    have := hN.gs_stop
    omega
  have hpn : 0 ≤ nxt sy m N.stopPhi := by omega
  have hpsi1 : psiP sy m (r.fr.hs (b + 1)) ≤ nxt sy m N.stopPhi := psiP_le ha1 hJ1.2.1 hgn
  -- the air frames
  have hrun : ∀ i, b + 1 ≤ i → i < r.C + N.fall → Follow sy m r.fr i ∧ AirIn (r.fr.inp (i + 1)) := fun i h1 h2 => by
    refine ⟨hfol i (by omega) (by omega), r.air_in i (by omega) (by omega) ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', i = n' + 1 := ⟨i - 1, by omega⟩
    exact st_ne r (by omega) (by omega) (hfol n' (by omega) (by omega)) (r.fall_long _ (by omega) h2)
  have hd : b + 1 + (r.C + N.fall - (b + 1)) = r.C + N.fall := by omega
  obtain ⟨hst34, hpsi, hP34⟩ := fall_run r H hst1 hpsi1 (r.C + N.fall - (b + 1)) (fun i h1 h2 => hrun i h1 (by omega))
  rw [hd] at hst34 hpsi hP34
  have hfol34 : ∀ i, r.C + N.fall ≤ i → i < r.t0 → Follow sy m r.fr i := fun i h1 h2 => hfol i (by omega) h2
  have ha : a1 sy m * ((r.C + N.fall - (b + 1) : Nat) : Int) ≤ a1 sy m * ((N.fall - N.wallF - 1 : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) ha1
  have hQ0 := hN.wall_Q
  by_cases hQ : phi sy m (r.fr.hs (r.C + N.fall)) ≤ N.fastQ
  · -- the potential from the end of the fall
    have hJ34 : J sy m (r.fr.hs (r.C + N.fall)) N.fastQ := ⟨hst34.dom, hQ, fun h1 => absurd hst34.rs h1⟩
    have h1 := dist_from r H hJ34 hfall hfol34
    have hq0 : 0 ≤ N.fastQ := by
      have := phi_ge F (r.fr.hs (r.C + N.fall))
      omega
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.fall = (r.t0 - (r.C + N.fall)) + k := ⟨N.goalF - N.fall - (r.t0 - (r.C + N.fall)), by omega⟩
    have h2 := dbound_mono F (r.t0 - (r.C + N.fall)) k N.fastQ hq0
    rw [← hk] at h2
    obtain ⟨k2, hk2⟩ : ∃ k, N.fall - N.wallF - 1 = (r.C + N.fall - (b + 1)) + k := ⟨N.fall - N.wallF - 1 - (r.C + N.fall - (b + 1)), by omega⟩
    have h3 := airDist_mono (sy := sy) (m := m) hpn ha1 (r.C + N.fall - (b + 1)) k2
    rw [← hk2] at h3
    have h4 := hN.wall_open
    omega
  · -- moving left at the end of the fall
    have hV : V (r.fr.hs (r.C + N.fall)) < 0 := by
      by_cases h1 : V (r.fr.hs (r.C + N.fall)) < 0
      · exact h1
      · exfalso
        apply hQ
        rw [psiP_eq_phi (by omega)]
        omega
    have hu : N.fastQ + 1 - 2 * c sy m ≤ -V (r.fr.hs (r.C + N.fall)) := by
      have h1 := AirCap.w_le F (r.fr.hs (r.C + N.fall))
      unfold phi at hQ
      omega
    have hst : ∀ i, b + 1 ≤ i → i ≤ r.C + N.fall → FallSt sy (r.fr.hs i) := fun i h1 h2 => by
      obtain ⟨h3, _, _⟩ := fall_run r H hst1 hpsi1 (i - (b + 1)) (fun j h3 h4 => hrun j h3 (by omega))
      rwa [show b + 1 + (i - (b + 1)) = i by omega] at h3
    have hbk : b + 1 ≤ r.C + N.fall - N.wallK := by
      by_cases h1 : b + 1 ≤ r.C + N.fall - N.wallK
      · exact h1
      · exfalso
        have hu2 := hu
        rw [← hd] at hu2
        have h3 := back_speed r H (b := b + 1) (r.C + N.fall - (b + 1)) _ (fun i h3 h4 => by
          have h5 := hrun i h3 (by omega)
          exact ⟨hst i (by omega) (by omega), h5.1, h5.2⟩) hu2
        have h4 : gSlow sy m * ((r.C + N.fall - (b + 1) : Nat) : Int) ≤ gSlow sy m * ((N.wallK - 1 : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left (by omega) hgs
        have h5 := hN.wall_u
        have h6 := phi_ge F (r.fr.hs (b + 1))
        have h7 := hJ1.2.1
        omega
    have hb2 : r.C + N.fall - N.wallK + N.wallK = r.C + N.fall := by omega
    have hu3 := hu
    rw [← hb2] at hu3
    have h1 := back_run r H (b := r.C + N.fall - N.wallK) N.wallK _ (fun i h3 h4 => by
      have h5 := hrun i (by omega) (by omega)
      exact ⟨hst i (by omega) (by omega), h5.1, h5.2⟩) hu3
    rw [hb2] at h1
    obtain ⟨_, _, h2⟩ := fall_run r H hst1 hpsi1 (r.C + N.fall - N.wallK - (b + 1)) (fun i h3 h4 => hrun i h3 (by omega))
    rw [show b + 1 + (r.C + N.fall - N.wallK - (b + 1)) = r.C + N.fall - N.wallK by omega] at h2
    obtain ⟨k, hk⟩ : ∃ k, N.fall - N.wallK - N.wallF - 1 = (r.C + N.fall - N.wallK - (b + 1)) + k :=
      ⟨N.fall - N.wallK - N.wallF - 1 - (r.C + N.fall - N.wallK - (b + 1)), by omega⟩
    have h3 := airDist_mono (sy := sy) (m := m) hpn ha1 (r.C + N.fall - N.wallK - (b + 1)) k
    rw [← hk] at h3
    have hfol2 : ∀ j, r.C + N.fall ≤ j → j < r.C + N.fall + (r.t0 - (r.C + N.fall)) → Follow sy m r.fr j := fun j h4 h5 =>
      hfol34 j h4 (by omega)
    have h4 := hdist_seg (r.C + N.fall) (r.t0 - (r.C + N.fall)) hfol2
    rw [show r.C + N.fall + (r.t0 - (r.C + N.fall)) = r.t0 by omega] at h4
    have h5 := AirCap.dist_capped H.air _ _ hst34.dom hst34.cap (inputs_seg _ _ hfol2)
    rw [length_seg] at h5
    obtain ⟨k2, hk2⟩ : ∃ k, N.goalF - N.fall = (r.t0 - (r.C + N.fall)) + k := ⟨N.goalF - N.fall - (r.t0 - (r.C + N.fall)), by omega⟩
    have h6 := cap_mono (m := m) hN.air_pos (r.t0 - (r.C + N.fall)) k2
    rw [← hk2] at h6
    have h7 := hN.wall_back
    omega

/-- frames with no jump: the height and the speed from a frame -/
theorem drop_run {u : Nat} {w0 : Int} (hu : r.C ≤ u) (h1 : (r.fr.vs u).st ≠ 1) (h2 : (r.fr.vs u).vfd.toNat = N.fallF) (h3 : VW (r.fr.vs u) ≤ w0) :
    ∀ e, u + e < r.C + N.standF → (∀ j, u ≤ j → j < u + e → (r.fr.inp (j + 1)).jump = false) →
      (r.fr.vs (u + e)).st ≠ 1 ∧ (r.fr.vs (u + e)).vfd.toNat = N.fallF ∧ VW (r.fr.vs (u + e)) ≤ w0 + (N.fallF : Int) * (e : Int) ∧
        VY (r.fr.vs (u + e)) ≤ VY (r.fr.vs u) + fallSum w0 (N.fallF : Int) e
  | 0, _, _ => by simpa [fallSum] using And.intro h1 (And.intro h2 h3)
  | e + 1, h4, h5 => by
    obtain ⟨h6, h7, h8, h9⟩ := drop_run hu h1 h2 h3 e (by omega) (fun j h10 h11 => h5 j h10 (by omega))
    have hv := r.vfall (u + e) (by omega) (by omega) h6 (h5 _ (by omega) (by omega))
    have hm : (N.fallF : Int) * ((e + 1 : Nat) : Int) = (N.fallF : Int) * (e : Int) + (N.fallF : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [show u + (e + 1) = u + e + 1 by omega, hm]
    simp only [fallSum]
    have h10 := hv.y_le
    have h11 := hv.w_le
    rw [show (u + e + 1) = u + e + 1 from rfl] at *
    refine ⟨hv.st, by rw [hv.vfd]; exact h7, by omega, by omega⟩

theorem capRamp_nonneg (hA : 1 ≤ sy.AirFastSpeed.toNat) (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ capRamp sy m p n
  | 0, _, _ => by simp [capRamp]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := capRamp_nonneg hA F n (nxt sy m p) (by omega)
    simp only [capRamp]
    have h2 : 0 ≤ min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) := Int.le_min.2 ⟨by omega, by omega⟩
    omega

theorem capRamp_mono (hA : 1 ≤ sy.AirFastSpeed.toNat) (F : Facts sy m) : ∀ (n k : Nat) (p : Int), 0 ≤ p → capRamp sy m p n ≤ capRamp sy m p (n + k)
  | 0, k, p, hp => by
    have := capRamp_nonneg hA F k p hp
    simpa [capRamp] using this
  | n + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := capRamp_mono hA F n k (nxt sy m p) (by omega)
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [capRamp]
    omega

/-- frames below the threshold: at most the air speed, and at most the potential -/
theorem ramp_run (F : Facts sy m) : ∀ (d u : Nat) (p : Int), J sy m (r.fr.hs u) p →
    (∀ i, u ≤ i → i < u + d → Follow sy m r.fr i) → (∀ i, u < i → i ≤ u + d → capped sy (r.fr.hs i) = true) →
      r.fr.P (u + d) ≤ r.fr.P u + capRamp sy m p d
  | 0, _, _, _, _, _ => by simp [capRamp]
  | d + 1, u, p, hJ, h1, h2 => by
    have hf := h1 u (Nat.le_refl _) (by omega)
    obtain ⟨hJ1, h256, _⟩ := step_J F hJ hf.1
    rw [← hf.2.1] at hJ1 h256
    have ih := ramp_run F d (u + 1) _ hJ1 (fun i h3 h4 => h1 i (by omega) (by omega)) (fun i h3 h4 => h2 i (by omega) (by omega))
    have hc := h2 (u + 1) (by omega) (by omega)
    simp only [capped, decide_eq_true_eq] at hc
    have h5 := hf.2.2
    rw [show u + 1 + d = u + (d + 1) by omega] at ih
    simp only [capRamp]
    have h6 : sbyte (r.fr.hs (u + 1)).v ≤ min ((sy.AirFastSpeed.toNat : Int) - 1) (nxt sy m p / 256) := Int.le_min.2 ⟨by omega, by omega⟩
    omega

/-- **After a wall hit before `wallD`, turned away from the right.** That needs a ground frame with no jump, on a stand in the fall, and it is
the only stand so far. He falls with the first force, so he is not on the floor for `k` frames after the stand, and all those frames are air frames:
below the threshold. After them, any frames -/
theorem wall_turn (H : Checks sy m N) {b : Nat} (hge : r.C + N.wallF ≤ b) (hbD : b < r.C + N.wallD) (hP : r.fr.P b ≤ N.wallP)
    (hJ : J sy m (r.fr.hs b) N.stopPhi) (hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i) (hb0 : b < r.t0)
    (hfd : (r.fr.hs (b + 1)).fd ≠ 1) (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have hle := hN.fall_le
  have hwD := hN.wallD_le
  have hgap := hN.gap_D
  have hg := hN.hit_ge
  have hA := hN.air_pos
  have hbF : b < r.C + N.fall := by omega
  obtain ⟨hst0, hY0, hW0, hf0⟩ := r.v_start
  -- a ground frame with no jump, up to `b + 1`
  have hex : ∃ i, r.C ≤ i ∧ i ≤ b ∧ (r.fr.inp (i + 1)).st = 0 ∧ (r.fr.inp (i + 1)).jump = false := by
    by_cases hc : ∃ i, r.C ≤ i ∧ i ≤ b ∧ (r.fr.inp (i + 1)).st = 0 ∧ (r.fr.inp (i + 1)).jump = false
    · exact hc
    · exfalso
      have hchain : ∀ d, r.C + d ≤ b + 1 → (r.fr.hs (r.C + d)).fd = 1 := by
        intro d
        induction d with
        | zero => exact fun _ => (start_fall r H).fd
        | succ d ih =>
          intro h1
          have h2 := ih (by omega)
          have h3 : (r.fr.inp (r.C + d + 1)).st ≠ 0 ∨ (r.fr.inp (r.C + d + 1)).jump = true := by
            by_cases h4 : (r.fr.inp (r.C + d + 1)).st = 0
            · right
              by_cases h5 : (r.fr.inp (r.C + d + 1)).jump = true
              · exact h5
              · exact absurd ⟨r.C + d, by omega, by omega, h4, by simpa using h5⟩ hc
            · exact Or.inl h4
          rw [show r.C + (d + 1) = r.C + d + 1 by omega, r.facing (r.C + d) (by omega) (by omega) h3]
          exact h2
      have h1 := hchain (b + 1 - r.C) (by omega)
      rw [show r.C + (b + 1 - r.C) = b + 1 by omega] at h1
      exact hfd h1
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hex
  -- it starts on a stand
  have hst : (r.fr.vs i).st = 0 := by
    by_cases h1 : (r.fr.vs i).st = 0
    · exact h1
    · have h2 := (r.air_in i hi1 (by omega) h1).2.1
      rw [hi3] at h2
      exact absurd h2 (by decide)
  have hiC : i ≠ r.C := fun h1 => by
    rw [h1, hst0] at hst
    exact absurd hst (by decide)
  -- no stand before it
  have hfirst : ∀ l, r.C ≤ l → l < i → (r.fr.vs l).st ≠ 0 := fun l h1 h2 h3 => by
    have h4 := stand_gap r H h1 h2 (by omega) h3 hst
    have hlC : l ≠ r.C := fun h5 => by
      rw [h5, hst0] at h3
      exact absurd h3 (by decide)
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h5 := r.stand_wall l' (by omega) (by omega) h3 (r.fall_long _ h1 (by omega))
    have hn : ¬∀ j, r.C ≤ j → j < l' + 1 → Follow sy m r.fr j := fun h6 => h5 (h6 l' (by omega) (by omega))
    obtain ⟨h', h6, h7, h8, h9⟩ := first_hit _ hn
    have h10 := wall_first r H h6 h9 (r.wall h' h6 (by omega) h8).before
    omega
  -- it is not on the frame `wallF + 1` or before
  have hlate : r.C + N.wallF + 1 ≤ i := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have h5 := r.stand_wall i' (by omega) (by omega) hst (r.fall_long _ hi1 (by omega))
    have hn : ¬∀ j, r.C ≤ j → j < i' + 1 → Follow sy m r.fr j := fun h6 => h5 (h6 i' (by omega) (by omega))
    obtain ⟨h', h6, h7, h8, h9⟩ := first_hit _ hn
    by_cases h10 : h' = i'
    · subst h10
      have h11 := left_far r H h6 h9 (r.stand_P h' h6 (by omega) hst) hN.stand_far
      omega
    · have h11 := wall_first r H h6 h9 (r.wall h' h6 (by omega) h8).before
      omega
  -- the height on the stand
  have hjump0 : ∀ j, r.C ≤ j → j < i → (r.fr.inp (j + 1)).jump = false := fun j h1 h2 =>
    (r.air_in j h1 (by omega) (hfirst j h1 h2)).2.2
  obtain ⟨h1, h2, h3, h4⟩ := drop_run r (u := r.C) (Nat.le_refl _) (by rw [hst0]; decide) hf0 hW0 (i - r.C) (by omega)
    (fun j h5 h6 => hjump0 j h5 (by omega))
  rw [show r.C + (i - r.C) = i by omega] at h1 h2 h3 h4
  obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hrow := r.stand_row i' (by omega) (by omega) (hfirst i' (by omega) (by omega)) (by rw [← hi']; exact hst)
  rw [← hi'] at hrow
  obtain ⟨hr1, hr2⟩ := hrow
  have hYi : VY (r.fr.vs i) ≤ standB N (i - r.C) := by
    unfold standB
    generalize fallSum N.startW (N.fallF : Int) (i - r.C) = S at h4
    have hd : (r.fr.vs i).dummy.toNat < 256 := (r.fr.vs i).dummy.toNat_lt
    have h5 : VY (r.fr.vs i) ≤ N.startY + S := by omega
    unfold VY at h5 ⊢
    omega
  -- the pair of numbers
  have hany : N.gaps.any (fun q => q.1 == i - r.C) = true := by
    have h5 := hN.gaps_all
    simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h5
    rcases h5 (i - r.C) (List.mem_range.2 (by omega)) with h6 | h6
    · omega
    · exact h6
  obtain ⟨q, hq, hq1⟩ := List.any_eq_true.1 hany
  have hq2 : q.1 = i - r.C := by simpa using hq1
  have hok := hN.gaps_ok
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hq3, hq4⟩, hq5⟩, hq6⟩, hq7⟩ := hok q hq
  rw [hq2] at hq3 hq4 hq5 hq6 hq7
  generalize q.2 = k at hq3 hq4 hq5 hq6 hq7
  -- not on the floor for `k` frames
  have hsum : ∀ e, e ≤ k → fallSum 0 (N.fallF : Int) e ≤ fallSum 0 (N.fallF : Int) k := by
    intro e he
    obtain ⟨c, hc⟩ : ∃ c, k = e + c := ⟨k - e, by omega⟩
    rw [hc]
    clear hc
    induction c with
    | zero => exact Int.le_refl _
    | succ c ih =>
      rw [show e + (c + 1) = e + c + 1 by omega]
      simp only [fallSum]
      have : (0 : Int) ≤ (N.fallF : Int) * ((e + c : Nat) : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
  have hw0 : VW (r.fr.vs i) ≤ 0 := by omega
  have hnoj : ∀ e, e ≤ k → i + e ≤ r.t0 → ∀ j, i ≤ j → j < i + e → (r.fr.inp (j + 1)).jump = false := by
    intro e
    induction e with
    | zero => exact fun _ _ j h5 h6 => by omega
    | succ e ih =>
      intro h5 h6 j h7 h8
      by_cases h9 : j < i + e
      · exact ih (by omega) (by omega) j h7 h9
      · have hj : j = i + e := by omega
        subst hj
        by_cases he : e = 0
        · subst he
          exact hi4
        · obtain ⟨_, _, _, h10⟩ := drop_run r (u := i) hi1 (by rw [hst]; decide) h2 hw0 e (by omega) (ih (by omega) (by omega))
          have h11 := hsum e (by omega)
          have hnf : ¬OnFloor sy (r.fr.vs (i + e)) := fun h12 => by
            have h13 := h12.2
            have hd : (0 : Int) ≤ ((r.fr.vs (i + e)).dummy.toNat : Int) := by omega
            unfold VY at h10
            rw [h13] at h10
            unfold VY at hYi
            unfold standB at hq6 hYi
            omega
          refine (r.air_in (i + e) (by omega) (by omega) ?_).2.2
          by_cases h12 : i + e ≤ b
          · intro h13
            have h14 := stand_gap r H hi1 (by omega) (by omega) hst h13
            omega
          · obtain ⟨n', hn'⟩ : ∃ n', i + e = n' + 1 := ⟨i + e - 1, by omega⟩
            rw [hn']
            exact st_ne r (by omega) (by omega) (hfol n' (by omega) (by omega)) (by rw [← hn']; exact hnf)
  -- so every frame after `b` up to there is an air frame
  let n2 := min r.t0 (i + k + 1)
  have hn2 : b + 1 ≤ n2 := by
    simp only [n2]
    omega
  have hairF : ∀ n, b + 1 ≤ n → n < n2 → isAir (r.fr.inp (n + 1)) = true ∨ Stop sy m N r.fr (n + 1) := fun n h5 h6 => by
    left
    simp only [n2] at h6
    have h7 := hnoj (n - i) (by omega) (by omega)
    obtain ⟨_, _, _, h10⟩ := drop_run r (u := i) hi1 (by rw [hst]; decide) h2 hw0 (n - i) (by omega) h7
    rw [show i + (n - i) = n by omega] at h10
    have h11 := hsum (n - i) (by omega)
    have hnf : ¬OnFloor sy (r.fr.vs n) := fun h12 => by
      have h13 := h12.2
      have hd : (0 : Int) ≤ ((r.fr.vs n).dummy.toNat : Int) := by omega
      unfold VY at h10
      rw [h13] at h10
      unfold VY at hYi
      unfold standB at hq6 hYi
      omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h12 := r.air_in (n' + 1) (by omega) (by omega) (st_ne r (by omega) (by omega) (hfol n' (by omega) (by omega)) hnf)
    simp [isAir, h12.2.1]
  obtain ⟨hJ1, hc1, _, _⟩ := wall_next r H hP hJ (hfol b (Nat.le_refl _) hb0)
  have hcap := capped_along r H (u := b + 1) (w := n2) (by omega) (by simp only [n2]; omega) hc1 hairF
  have hcap' : ∀ j, b < j → j ≤ n2 → capped sy (r.fr.hs j) = true := fun j h5 h6 => by
    have h7 := hcap (j - (b + 1)) (by omega)
    rwa [show b + 1 + (j - (b + 1)) = j by omega] at h7
  have hP2 := ramp_run r F (n2 - b) b N.stopPhi hJ (fun j h5 h6 => hfol j h5 (by simp only [n2] at h6; omega))
    (fun j h5 h6 => hcap' j h5 (by omega))
  rw [show b + (n2 - b) = n2 by omega] at hP2
  obtain ⟨c1, hc1'⟩ : ∃ c, k + 1 = (n2 - b) + c := ⟨k + 1 - (n2 - b), by
    simp only [n2]
    omega⟩
  have hP3 := capRamp_mono hA F (n2 - b) c1 N.stopPhi hN.stop_nonneg
  rw [← hc1'] at hP3
  -- then any frames
  have hfol2 : ∀ j, n2 ≤ j → j < n2 + (r.t0 - n2) → Follow sy m r.fr j := fun j h5 h6 => hfol j (by omega) (by simp only [n2] at h6 ⊢; omega)
  have h5 := hdist_seg n2 (r.t0 - n2) hfol2
  rw [show n2 + (r.t0 - n2) = r.t0 by simp only [n2]; omega] at h5
  have h6 := AirCap.dist_capped H.air _ _ (inD_at r H (n := n2) (by omega) (by simp only [n2]; omega)) (hcap' n2 (by omega) (Nat.le_refl _))
    (inputs_seg _ _ hfol2)
  rw [length_seg] at h6
  obtain ⟨c2, hc2⟩ : ∃ c, N.goalF - (i - r.C + k + 1) = (r.t0 - n2) + c := ⟨N.goalF - (i - r.C + k + 1) - (r.t0 - n2), by
    simp only [n2]
    omega⟩
  have h7 := cap_mono (m := m) hA (r.t0 - n2) c2
  rw [← hc2] at h7
  omega

/-- **A wall hit before `hitF`, and no stop from `hitF` on: he is short of the goal**, whatever he does: there is no need to look at a jump -/
theorem wall_short (H : Checks sy m N) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n) (hw : ¬NoWall sy m N r.fr r.C)
    (ht : r.t0 ≤ r.C + N.goalF) : r.fr.P r.t0 < goalP sy := by
  have hN := H.nums
  have F := H.air.pot
  have hg := hN.hit_ge
  have hhr := hN.hit_run
  have hlate := t0_late r H
  have hwD := hN.wallD_le
  have hfA : ∀ j, r.C + N.hitF ≤ j + 1 → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 => follow_of r hs h1 h2 (by omega)
  obtain ⟨b, hb⟩ := anchor_of_wall r H hw (w := r.C + N.hitF - 1) (by omega) (by omega) (by omega)
  have hle := hb.le
  have hge := hb.ge
  have hfol : ∀ i, b ≤ i → i < r.t0 → Follow sy m r.fr i := fun i h1 h2 => by
    by_cases h3 : i < r.C + N.hitF - 1
    · exact hb.fol i h1 h3
    · exact hfA i (by omega) h2
  by_cases hnear : r.C + N.wallD ≤ b
  · have h1 := dist_from r H hb.J' (by omega) hfol
    obtain ⟨k, hk⟩ : ∃ k, N.goalF - N.wallD = (r.t0 - b) + k := ⟨N.goalF - N.wallD - (r.t0 - b), by omega⟩
    have h2 := dbound_mono F (r.t0 - b) k N.stopPhi hN.stop_nonneg
    rw [← hk] at h2
    have h3 := hN.wall_near
    have h4 := hb.P_le
    omega
  · by_cases hfd : (r.fr.hs (b + 1)).fd = 1
    · exact wall_right r H hge hb.P_le hb.J' (by omega) hfol (by omega) (by omega) hfd ht
    · exact wall_turn r H hge (by omega) hb.P_le hb.J' hfol (by omega) hfd ht

/-- with no stop from `hitF` on, a landing on the block is short of the goal in time: the case split on the takeoff -/
theorem landed_short (H : Checks sy m N) (hw : NoWall sy m N r.fr r.C) (hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n)
    (a : Approach sy m N r.fr r.C r.t0) (ht : r.t0 ≤ r.C + N.goalF) : False := by
  have hn := H.nums
  have hpast := r.past
  have hT1 := a.T1_ge
  have hT2 := a.T1_lt
  have hT := a.L_gt
  have hLt := a.L_le
  have hl0 := hn.low_nonneg
  have hA := hn.air_pos
  obtain ⟨hk, q, hq, hq1, hq2⟩ := window_pair H a.x_mem a.reach a.window
  -- the last low frame is not after the landing
  have hlowk : a.u.low ≤ a.u.k := arc_low a.reach (by rw [arcStart_low a.x_mem, arcStart_k a.x_mem]; omega)
  -- the pair has at least the low frames of every jump
  have hrq : N.rise ≤ q.1 := by
    have h1 := hn.slow_pairs
    have h2 := hn.fast_pairs
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    cases hf : a.x.fast with
    | false =>
      rw [hf] at hq
      exact (h1 q (by simpa using hq)).1.1.1
    | true =>
      rw [hf] at hq
      exact h2 q (by simpa using hq)
  have hfol : ∀ j, r.C + N.hitF ≤ j + 1 → r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 h3 =>
    follow_of r hs h1 h3 h2
  have hhr := hn.hit_rise
  have hhg := hn.hit_ge
  -- a takeoff after the last one searched: the top speed
  by_cases hlate : r.C + N.fall + N.lastG < a.T1
  · let u0 := a.T1 + 1 + N.rise
    have hu0 := (a.low u0 (by omega) (by omega)).1
    have h1 := reach_le (P := r.fr.P) (u := u0) (B := cornerP sy + N.lowSlack) (μ := 16 * (top sy : Int)) (w := r.t0) hu0
      (by omega) (fun n h3 h4 => Or.inl (r.move_top n (by omega) h4)) (r.t0 - u0) (by omega)
    rw [show u0 + (r.t0 - u0) = r.t0 by omega] at h1
    have h2 := hn.late
    have h3 : 16 * (top sy : Int) * ((r.t0 - u0 : Nat) : Int) ≤
        16 * (top sy : Int) * ((N.goalF - (N.fall + N.lastG + 2 + N.rise) : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hearly : a.T1 ≤ r.C + N.fall + N.lastG := by omega
  -- every low frame is left of the corner
  let s := a.T1 + 1 + a.u.low
  have hsL : s ≤ a.L := by omega
  have hlowall : ∀ n, r.C + N.hitF ≤ n → n ≤ s → LowAt sy m N r.fr n := fun n h1 h2 => by
    by_cases h3 : n ≤ a.T1
    · exact floor_low r H hw a hearly h1 h3
    · exact a.low n (by omega) h2
  have hleft : ∀ n, r.C ≤ n → n ≤ s → r.fr.P n < cornerP sy := fun n h1 h2 =>
    left_at r H hs (w := s) (by omega) hlowall h1 h2
  cases hf : a.x.fast with
  | false =>
    -- a slow takeoff: the air speed cap from the last low frame
    rw [hf] at hq
    simp only [Bool.false_eq_true, if_false] at hq
    have hc0 : capped sy (r.fr.hs a.T1) = true := by
      have h1 := a.x_ab
      rw [hf] at h1
      have h2 := r.ab_ge a.T1 (by omega) (by omega)
      have h3 : ¬sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
      simp only [capped, decide_eq_true_eq]
      omega
    have hcap := capped_along r H (u := a.T1) (w := a.L) (by omega) hLt hc0 (fun n h1 h2 => Or.inl (a.air n h1 h2))
      (s - a.T1) (by omega)
    rw [show a.T1 + (s - a.T1) = s by omega] at hcap
    have hD := inD_at r H (n := s) (by omega) (by omega)
    have hF : ∀ j, s ≤ j → j < s + (r.t0 - s) → Follow sy m r.fr j := fun j h1 h2 =>
      hfol j (by omega) (by omega) (by omega)
    have h1 := hdist_seg s (r.t0 - s) hF
    rw [show s + (r.t0 - s) = r.t0 by omega] at h1
    have hsplit : seg r.fr.inp s (r.t0 - s) = seg r.fr.inp s (a.L - s) ++ seg r.fr.inp a.L (r.t0 - a.L) := by
      rw [show r.t0 - s = (a.L - s) + (r.t0 - a.L) by omega, seg_add, show s + (a.L - s) = a.L by omega]
    rw [hsplit] at h1
    have h2 := landing_bound H.air (r.fr.hs s) hD hcap (seg r.fr.inp s (a.L - s)) (seg r.fr.inp a.L (r.t0 - a.L))
      (mem_seg (P := fun i => i ∈ inputs ∧ isAir i = true) fun j h3 h4 =>
        ⟨(hF j h3 (by omega)).1, a.air j (by omega) (by omega)⟩)
      (mem_seg (P := fun i => i ∈ inputs) fun j h3 h4 => (hF j (by omega) (by omega)).1)
    rw [length_seg, length_seg] at h2
    have hp := hn.slow_pairs
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨_, hq3⟩, hq4⟩, hq5⟩ := hp q hq
    have h3 := pair_bound (sy := sy) (m := m) hA (q1 := q.1) (q2 := q.2) (S0 := r.C + N.fall + 1 + q.1)
      (L0 := r.C + N.fall + 1 + q.2) (s := s) (L := a.L) (t := r.t0) (G := r.C + N.goalF) (by omega) hq4 (by omega) (by omega)
      hsL hLt ht
    rw [show r.C + N.goalF - (r.C + N.fall + 1 + q.2) = N.goalF - (N.fall + 1 + q.2) by omega] at h3
    have h4 := hleft s (by omega) (Nat.le_refl s)
    omega
  | true =>
    -- a fast takeoff: the speed is at the threshold, and the search of `FastTakeoff`
    have hth : sy.AirFastSpeed.toNat ≤ (sbyte (r.fr.hs a.T1).v).natAbs := by
      have h1 := a.x_ab
      rw [hf] at h1
      have h2 : sy.AirFastSpeed.toNat ≤ r.fr.ab a.T1 := by simpa using h1.symm
      have h3 := ab_or r H hw hs (a.T1 - r.C) (by omega)
      rw [show r.C + (a.T1 - r.C) = a.T1 by omega] at h3
      omega
    have E := early_of r H hw a hearly
    have hF : ∀ j, r.C ≤ j → j < r.t0 → Follow sy m r.fr j := fun j h1 h2 => by
      by_cases h3 : j + 1 < r.C + N.hitF
      · exact E.follow j h1 h3
      · exact hfol j (by omega) h1 h2
    let R := room sy N
    have hg0 : a.T1 - (r.C + N.fall) ≤ N.lastG := by omega
    let fa := seg r.fr.inp r.C N.fall
    let g := seg r.fr.inp (r.C + N.fall) (a.T1 - (r.C + N.fall))
    let k := seg r.fr.inp (a.T1 + 1) N.rise
    have hTk : Takeoff R fa g (r.fr.inp (a.T1 + 1)) k :=
      { fall_in := mem_seg (P := AirIn) fun j h1 h2 => E.fall_in j h1 h2
        fall_len := length_seg _ _ _
        gnd_in := mem_seg (P := GndIn) fun j h1 h2 => E.gnd_in j h1 (by omega)
        jump_in := E.jump_in
        air_in := mem_seg (P := AirIn) fun j h1 h2 => E.air_in j h1 h2
        air_len := length_seg _ _ _ }
    have hgo1 : go sy m (R.s0, r.fr.P r.C) fa = (r.fr.hs (r.C + N.fall), r.fr.P (r.C + N.fall)) := by
      have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) r.C N.fall (fun j h2 h3 => hF j h2 (by omega))
      rw [r.start] at h1
      exact h1
    have hgo2 : go sy m (R.s0, r.fr.P r.C) (fa ++ g) = (r.fr.hs a.T1, r.fr.P a.T1) := by
      rw [FastTakeoff.go_append, hgo1]
      have h1 := go_seg (fr := r.fr) (sy := sy) (m := m) (r.C + N.fall) (a.T1 - (r.C + N.fall))
        (fun j h2 h3 => hF j (by omega) (by omega))
      rw [show r.C + N.fall + (a.T1 - (r.C + N.fall)) = a.T1 by omega] at h1
      exact h1
    have hlow0 : Low sy m R.cp (go sy m (R.s0, r.fr.P r.C) fa) (g ++ r.fr.inp (a.T1 + 1) :: k) := by
      rw [hgo1]
      have h1 : g ++ r.fr.inp (a.T1 + 1) :: k = seg r.fr.inp (r.C + N.fall) (a.T1 - (r.C + N.fall) + (1 + N.rise)) := by
        rw [seg_add, show r.C + N.fall + (a.T1 - (r.C + N.fall)) = a.T1 by omega, Nat.add_comm 1 N.rise]
        simp only [g, k, seg]
      rw [h1]
      exact low_seg _ _ (fun j h2 h3 => hF j (by omega) (by omega)) (fun j h2 h3 => hleft (j + 1) (by omega) (by omega))
    have hp0 := r.startP0
    have hp1 := r.startP1
    have FT : TFacts sy m := ⟨H.air.pot, H.normI⟩
    by_cases hv : (sy.AirFastSpeed.toNat : Int) ≤ sbyte (r.fr.hs a.T1).v
    · -- moving right: he does not stay left of the corner
      refine FastTakeoff.no_right_takeoff FT H.roomOk hp0 hp1 hTk (by rw [length_seg]; exact hg0) ?_ hlow0
      rw [hgo2]
      exact hv
    · -- moving left: he is too far back
      have hv2 : sbyte (r.fr.hs a.T1).v ≤ -(sy.AirFastSpeed.toNat : Int) := by omega
      have hlowg : Low sy m R.cp (go sy m (R.s0, r.fr.P r.C) fa) g := (FastTakeoff.low_append g _ _ hlow0).1
      obtain ⟨es, _, h2, h3⟩ := FastTakeoff.layer_of FT H.roomOk hp0 hp1 hTk.fall_in hTk.fall_len hTk.gnd_in
        (by rw [length_seg]; exact hg0) (by rw [hgo2]; exact hth) hlowg
      rw [hgo2] at h3
      have hrest : ∀ j, a.T1 ≤ j → j < a.T1 + (r.t0 - a.T1) → Follow sy m r.fr j := fun j h4 h5 =>
        hF j (by omega) (by omega)
      have h5 := left_spec_le H.air.pot h2 h3 hv2 (rest := seg r.fr.inp a.T1 (r.t0 - a.T1)) (inputs_seg _ _ hrest)
        (by
          rw [length_seg, length_seg]
          show r.t0 - a.T1 ≤ N.goalF - N.fall - (a.T1 - (r.C + N.fall))
          omega)
      rw [go_seg a.T1 (r.t0 - a.T1) hrest, show a.T1 + (r.t0 - a.T1) = r.t0 by omega] at h5
      have h6 : (room sy N).goal = goalP sy := rfl
      simp only [h6] at h5
      omega

/-- he is not past the block's right end by frame `C + goalF` -/
theorem past_late (H : Checks sy m N) : r.C + N.goalF < r.t0 := by
  by_cases ht : r.t0 ≤ r.C + N.goalF
  · exfalso
    cases hw : r.way with
    | over o => exact no_landing r H o
    | onto a _ =>
      by_cases hstop : ∃ h, r.C + N.hitF ≤ h ∧ h ≤ r.t0 ∧ Stop sy m N r.fr h
      · obtain ⟨h, h1, h2, h3⟩ := hstop
        have h4 := stop_short r H h1 h2 h3 ht
        have h5 := r.past
        omega
      · have hs : ∀ n, r.C + N.hitF ≤ n → n ≤ r.t0 → ¬Stop sy m N r.fr n := fun n h1 h2 h3 => hstop ⟨n, h1, h2, h3⟩
        by_cases hnw : NoWall sy m N r.fr r.C
        · exact landed_short r H hnw hs (a hnw hs) ht
        · have h4 := wall_short r H hs hnw ht
          have h5 := r.past
          omega
  · omega

/-! ### Off the block -/

/-- a slow jump: at most the air speed on every frame -/
theorem slow_move (H : Checks sy m N) {u F : Nat} (hc : capped sy (r.fr.hs u) = true) (hD : inD sy (r.fr.hs u) = true)
    (hfr : ∀ i, u ≤ i → i < F → (Follow sy m r.fr i ∧ isAir (r.fr.inp (i + 1)) = true) ∨ Moved sy r.fr i) :
    ∀ d, u + d ≤ F → capped sy (r.fr.hs (u + d)) = true ∧ inD sy (r.fr.hs (u + d)) = true ∧
      r.fr.P (u + d) ≤ r.fr.P u + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (d : Int)
  | 0, _ => ⟨hc, hD, by simp⟩
  | d + 1, h => by
    obtain ⟨h1, h2, h3⟩ := slow_move H hc hD hfr d (by omega)
    have hm : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((d + 1 : Nat) : Int) =
        16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (d : Int) + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [show u + (d + 1) = u + d + 1 by omega, hm]
    rcases hfr (u + d) (by omega) (by omega) with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩
    · obtain ⟨h7, h8, h9⟩ := h4
      have h10 : capped sy (r.fr.hs (u + d + 1)) = true := by
        rw [h8]
        rcases step_cap H.air h2 h1 h7 with h11 | ⟨h11, _⟩
        · exact h11
        · rw [h5] at h11
          exact absurd h11 (by decide)
      refine ⟨h10, ?_, ?_⟩
      · rw [h8]
        exact (FastTakeoff.step_facts H.air.pot h2 h7).1
      · simp only [capped, decide_eq_true_eq] at h10
        omega
    · exact ⟨h4, h5, by omega⟩

/-- **`mouth`**: on the entry frame he is at the mouth, or past its left end -/
theorem mouth_at (H : Checks sy m N) : SidePipe.mouthP sy 0 ≤ r.fr.P r.E := by
  obtain ⟨f, h1, h2⟩ := r.entry_P
  have h3 := (SidePipe.mouth_of_enters H.side r.entry_mem r.entered).1
  rw [h2]
  simp only [SidePipe.mouthP]
  omega

/-- the entry frame lands on the ground, or stands on it. This is the reason why the fall of `Off` ends by `E` -/
theorem entry_ground (H : Checks sy m N) : SidePipe.onGround sy r.entry = true :=
  SidePipe.ground_of_enters H.side r.entry_mem r.entered

/-- **The bonus room.** From a run and the checks: the entry comes at least `goalF + aboveF` frames after first control -/
theorem entry_ge (H : Checks sy m N) : r.C + N.goalF + N.aboveF ≤ r.E := by
  have hN := past_late r H
  have hn := H.nums
  cases hw : r.way with
  | over o => exact (no_landing r H o).elim
  | onto _ off =>
    cases off with
    | jump T1 n F x u T1_ge x_mem reach floor hF F_le above slowJ =>
      have hlen := arc_len H.lenB x_mem reach hn.len_ok.2.2.1 hn.len_ok.2.2.1
      simp only [ite_self] at hlen
      have hle : n ≤ arcFrames := by
        have := hn.len_ok.2.2.1
        omega
      have h1 := arc_spec H.drop x x_mem n u hle reach
      obtain ⟨h2, h3⟩ := arc_k reach
      have h4 := arcStart_k x_mem
      have hfl : (falling u.s && decide (groundY sy ≤ u.s.y.toNat)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact floor
      unfold dropOk at h1
      rw [hfl, h3] at h1
      simp only [Bool.not_true, Bool.false_or] at h1
      cases hf : x.fast with
      | true =>
        rw [hf] at h1
        simp only [if_true, decide_eq_true_eq] at h1
        omega
      | false =>
        rw [hf] at h1
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at h1
        by_cases hE : r.C + N.goalF + N.aboveF ≤ r.E
        · exact hE
        · exfalso
          have hab := hn.above_le
          have hag := hn.air_ge
          have hFE : F = r.E := by omega
          have hFv : F = r.C + N.goalF + N.aboveS := by omega
          have hT1 : T1 ≤ r.C + N.goalF := by omega
          obtain ⟨hc, hfr⟩ := slowJ hf hFE
          have hD := inD_at r H T1_ge (by omega)
          obtain ⟨h5, h6, _⟩ := slow_move r H hc hD hfr (r.C + N.goalF - T1) (by omega)
          rw [show T1 + (r.C + N.goalF - T1) = r.C + N.goalF by omega] at h5 h6
          obtain ⟨_, _, h7⟩ := slow_move r H h5 h6 (F := F) (fun i h8 h9 => hfr i (by omega) h9) N.aboveS (by omega)
          rw [← hFv, hFE] at h7
          have h8 := r.first (r.C + N.goalF) (by omega) hN
          have h9 := mouth_at r H
          have h10 := hn.slow_mouth
          omega
    | step F f d f_mem hF F_le =>
      have hw2 := H.walk
      simp only [walkOk, List.all_eq_true, decide_eq_true_eq] at hw2
      have h1 := hw2 f f_mem d (mem_bytes d)
      have h3 := hn.walk_le
      omega

end RoomCore

namespace RoomRun

variable (r : RoomRun sy m N)

/-- a frame that follows the model follows `hstep`: `FrameModel.clean_frame` -/
theorem follow_of_clean (H : Checks sy m N) {n : Nat} (hC : r.C ≤ n) (h2 : n < r.t0)
    (hc : FrameModel.Clean sy (FrameModel.Rom.of m) (FrameModel.ctrlStack sy m) (r.fm n) (r.pad (n + 1)) (r.arr n)) : Follow sy m r.fr n := by
  obtain ⟨h1, h3⟩ := FrameModel.clean_frame H.model hc
  rw [← r.next n hC h2] at h1 h3
  have e0 := r.read_hs n hC (by omega)
  have e1 := r.read_hs (n + 1) (by omega) (by omega)
  have p0 := r.read_P n hC (by omega)
  have p1 := r.read_P (n + 1) (by omega) (by omega)
  have e2 := r.read_in n hC h2 hc
  refine ⟨?_, ?_, ?_⟩
  · rw [e2]
    exact FrameModel.readIn_mem (FrameModel.joy_of_model H.model) _
  · rw [e1, h1, e0, e2]
  · rw [p1, h3, p0, e1]

/-- each frame follows `hstep` or leaves him stopped -/
theorem frames_of (H : Checks sy m N) : ∀ n, r.C ≤ n → n < r.t0 → Follow sy m r.fr n ∨ Stop sy m N r.fr (n + 1) := by
  intro n h1 h2
  rcases r.clean n h1 h2 with h3 | h3
  · exact Or.inl (r.follow_of_clean H h1 h2 h3)
  · exact Or.inr h3.1

/-- every frame up to `t0` is in the domain -/
theorem inD_of (H : Checks sy m N) : ∀ d, r.C + d ≤ r.t0 → inD sy (r.fr.hs (r.C + d)) = true
  | 0, _ => by
    have h := H.roomOk
    simp only [roomCheck, Bool.and_eq_true] at h
    rw [show r.C + 0 = r.C from rfl, r.start]
    exact h.1.1
  | d + 1, h => by
    have ih := inD_of H d (by omega)
    rcases r.frames_of H (r.C + d) (by omega) (by omega) with h1 | h1
    · rw [show r.C + (d + 1) = r.C + d + 1 by omega, h1.2.1]
      exact (FastTakeoff.step_facts H.air.pot ih h1.1).1
    · exact h1.1

/-- every frame moves him at most the top speed: a frame that follows `hstep` by the bound on its domain -/
theorem move_top_of (H : Checks sy m N) : ∀ n, r.C ≤ n → n < r.t0 → r.fr.P (n + 1) ≤ r.fr.P n + 16 * (top sy : Int) := by
  intro n h1 h2
  rcases r.clean n h1 h2 with h3 | h3
  · have hf := r.follow_of_clean H h1 h2 h3
    have hd := r.inD_of H (n + 1 - r.C) (by omega)
    rw [show r.C + (n + 1 - r.C) = n + 1 by omega] at hd
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h4 := hd.1.1.1
    rw [hf.2.2]
    omega
  · -- a `TopSpeed.Frame`: `Frame.bound`, from the domain
    obtain ⟨f, e1, _, e3, _, _, e6⟩ := FrameModel.frame_read H.model H.fric h3.2
    have hd := r.inD_of H (n - r.C) (by omega)
    rw [show r.C + (n - r.C) = n by omega, r.read_hs n h1 (by omega)] at hd
    simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h4 : (sbyte (peek (r.fm n) sy.Player_X_Speed)).natAbs ≤ top sy := hd.1.1.1
    have h16 : (16 : Int) ≤ (top sy : Int) := by
      have := (FrameModel.facts_of H.model).top16
      show (16 : Int) ≤ (TopSpeed.top sy : Int)
      omega
    have hb := f.bound h16 (by rw [e1]; omega)
    rw [r.read_P (n + 1) (by omega) (by omega), r.read_P n h1 (by omega), r.next n h1 h2, ← e6, ← e3]
    omega

/-- the frames as numbers -/
def toCore (H : Checks sy m N) : RoomCore sy m N :=
  { r.toRoomFields with frames := r.frames_of H, move_top := r.move_top_of H }

/-- **The entry comes at least `goalF + aboveF` frames after first control.** -/
theorem entry_ge (H : Checks sy m N) : r.C + N.goalF + N.aboveF ≤ r.E := (r.toCore H).entry_ge H

end RoomRun

end Smbrta.RoomJoin
