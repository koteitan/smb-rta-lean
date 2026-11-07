import Theorems.PipeTransition
import Theorems.Jump

/-!
# From touching the flagpole to the castle

From the machine at the frame Mario grabs the pole from below, the castle entry (`StarFlagTaskControl` set) comes `N` frames later or
one more, by the fraction of his position, and not earlier. A touch at another height takes longer. The states come from a real run up to
the base block, overwritten at the end. Page: `CastleWalk.md`.
-/

namespace Smbrta.CastleWalk

open PipeTransition (frame run zeros expand inputs gchain GMerge no_input_of_chain first_control
  zero_mem_inputs run_zeros_cons)

/-- the castle entry -/
def castle (sy : Syms) (m : Machine) : Bool := peek m sy.StarFlagTaskControl != 0

/-- from the 1-1 start: the vertical pipe of the other theorem, the bonus room (a few frames of Left, Right to the floor, a jump onto the
block, Right into the side pipe), and above ground Right with B held, A over the pits and up the staircase, down beside the base block -/
def route : List UInt8 :=
  PipeTransition.witness ++ expand [(0x00, 91), (0x02, 3), (0x01, 31), (0x81, 16), (0x01, 119), (0x00, 282),
    (0x41, 51), (0xC1, 35), (0x41, 23), (0xC1, 20), (0x41, 14), (0xC1, 20), (0x41, 10), (0xC1, 20), (0x41, 22), (0xC1, 20), (0x41, 80)]

/-- on the ground beside the base block -/
def beside (m0 : Machine) : Machine := run m0 route

/-- the frames of a jump from the ground before the frame at the height of a direct grab: a slow jump's frame `1`, with A held on or not -/
def beforeGrab (sy : Syms) (m : Machine) : List Jump.VS :=
  (((Jump.arcAll sy m (Jump.groundY sy) 1).filter fun x => x.k == 1 && !x.fast).map (·.s)).eraseDups

/-- `beside`, overwritten: at `x` beside the pole, with the vertical state `s` -/
def atPole (sy : Syms) (m : Machine) (x : UInt8) (fr : UInt8) (s : Jump.VS) : Machine :=
  let m := poke m sy.Player_X_Position x
  let m := poke m sy.SprObject_X_MoveForce fr
  let m := poke m sy.Player_Y_Position s.y
  let m := poke m sy.Player_Y_MoveForce s.mf
  let m := poke m sy.Player_Y_Speed s.vy
  let m := poke m sy.Player_YMF_Dummy s.dummy
  let m := poke m sy.VerticalForce s.vf
  let m := poke m sy.VerticalForceDown s.vfd
  let m := poke m sy.JumpOrigin_Y_Position s.origin
  let m := poke m sy.Player_State s.st
  let m := poke m sy.Player_X_Speed 0
  poke m sy.Player_XSpeedAbsolute 0

/-- the frame of the touch: one frame of no input from `atPole`, on the machine `b` beside the base block -/
def touchAt (sy : Syms) (b : Machine) (x fr : UInt8) (s : Jump.VS) : Machine := frame (atPole sy b x fr s) 0

/-- the routine changed: he touched the pole -/
def touched (sy : Syms) (m : Machine) : Bool := (peek m sy.GameEngineSubroutine).toUInt16 != sy.Eng_PlayerCtrl

/-- the two `x` of a direct grab: further right his head meets the pole first -/
def grabXs (sy : Syms) : List UInt8 := [(PoleGrab.colX sy - 10).toUInt8, (PoleGrab.colX sy - 9).toUInt8]

/-- the fractions a position can have (it moves by `16·v`), and the largest of all -/
def fracs : List UInt8 := (List.range 16).map (fun i => (16 * i).toUInt8) ++ [255]

/-- a fraction with the shorter delay -/
def bigFrac : UInt8 := 240

/-- the heights of other touches: below and above the height of a direct grab's limit -/
def otherYs (sy : Syms) : List UInt8 :=
  [1, 2, 4, 12, 32, 62, 98, 122].map fun d => (sy.FlagGrabY.toNat - d).toUInt8

/-- no castle entry on frames `1..n` of no input -/
def noneBefore (sy : Syms) : Nat → Machine → Bool
  | 0, _ => true
  | n + 1, m => !castle sy (frame m 0) && noneBefore sy n (frame m 0)

theorem noneBefore_spec (sy : Syms) :
    ∀ (n : Nat) (m : Machine), noneBefore sy n m = true → ∀ k, 1 ≤ k → k ≤ n → castle sy (run m (zeros k)) = false
  | 0, _, _, k, h1, h2 => by omega
  | n + 1, m, h, k, h1, h2 => by
    simp only [noneBefore, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [run_zeros_cons]
    cases j with
    | zero => exact h.1
    | succ i => exact noneBefore_spec sy n (frame m 0) h.2 (i + 1) (by omega) (by omega)

/-- the left `x` of a direct grab -/
def firstX (sy : Syms) : UInt8 := (PoleGrab.colX sy - 10).toUInt8

/-- everything the theorem needs, on the machine `b` beside the base block and the jump's states `vs`: `N` the delay, `lo` the frames
another touch takes at least -/
def checkOn (sy : Syms) (b : Machine) (vs : List Jump.VS) (N lo : Nat) : Bool :=
  let v0 := vs.headD default
  let e := touchAt sy b (firstX sy) bigFrac v0
  touched sy e &&
    gchain (castle sy) sy inputs (fun _ => true) N e &&
    vs.all (fun s => (grabXs sy).all fun x => gchain (castle sy) sy [] (fun _ => true) N (touchAt sy b x bigFrac s)) &&
    fracs.all (fun fr =>
      let t := touchAt sy b (firstX sy) fr v0
      touched sy t && noneBefore sy (N - 1) t) &&
    (otherYs sy).all (fun y =>
      let t := touchAt sy b (PoleGrab.colX sy - 9).toUInt8 bigFrac { v0 with y := y + 3 }
      touched sy t && noneBefore sy (lo - 1) t)

/-- the check from the 1-1 start -/
def allCheck (sy : Syms) (m0 : Machine) (N lo : Nat) : Bool := checkOn sy (beside m0) (beforeGrab sy m0) N lo

/-- what the check gives, on the machine `b` beside the base block -/
structure Statement (sy : Syms) (b : Machine) (vs : List Jump.VS) (N lo : Nat) : Prop where
  /-- he has touched the pole -/
  entered : touched sy (touchAt sy b (firstX sy) bigFrac (vs.headD default)) = true
  /-- every input on every frame: the castle on frame `N`, not before. Hypothesis: `GMerge`. -/
  allInputs : GMerge (castle sy) sy inputs N (touchAt sy b (firstX sy) bigFrac (vs.headD default)) →
    ∀ w : List UInt8, (∀ i ∈ w, i ∈ inputs) → w.length = N →
      castle sy (run (touchAt sy b (firstX sy) bigFrac (vs.headD default)) w) = true ∧
        ∀ k, 1 ≤ k → k < N → castle sy (run (touchAt sy b (firstX sy) bigFrac (vs.headD default)) (w.take k)) = false
  /-- no input, other `x` of a direct grab and other jumps: the same frame -/
  otherStates : ∀ s ∈ vs, ∀ x ∈ grabXs sy, ∀ k, 1 ≤ k → k ≤ N →
    castle sy (run (touchAt sy b x bigFrac s) (zeros k)) = decide (k = N)
  /-- no input, every fraction a position can have: not before frame `N` -/
  anyFraction : ∀ fr ∈ fracs, ∀ k, 1 ≤ k → k ≤ N - 1 →
    castle sy (run (touchAt sy b (firstX sy) fr (vs.headD default)) (zeros k)) = false
  /-- no input, a touch at another height: not before frame `lo` -/
  otherTouch : ∀ y ∈ otherYs sy, ∀ k, 1 ≤ k → k ≤ lo - 1 →
    castle sy (run (touchAt sy b (PoleGrab.colX sy - 9).toUInt8 bigFrac { (vs.headD default) with y := y + 3 }) (zeros k)) = false

theorem statement_of_check {sy : Syms} {b : Machine} {vs : List Jump.VS} {N lo : Nat} (hN : 1 ≤ N)
    (h : checkOn sy b vs N lo = true) : Statement sy b vs N lo := by
  simp only [checkOn, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · intro hM w hw hl
    exact first_control h2 zero_mem_inputs hM w hw hl hN
  · intro s hs x hx k hk1 hk2
    exact no_input_of_chain (h3 s hs x hx) k hk1 hk2
  · intro fr hfr k hk1 hk2
    exact noneBefore_spec sy (N - 1) _ (h4 fr hfr).2 k hk1 hk2
  · intro y hy k hk1 hk2
    exact noneBefore_spec sy (lo - 1) _ (h5 y hy).2 k hk1 hk2

/-- frames of no input until the castle entry -/
def framesToCastle (sy : Syms) (m : Machine) (limit : Nat := 400) : Option Nat := Id.run do
  let mut x := m
  for k in [0:limit] do
    x := frame x 0
    if castle sy x then return some (k + 1)
  return none

end Smbrta.CastleWalk
