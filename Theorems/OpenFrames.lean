import Theorems.Opening
import Theorems.PipeFrames

/-!
# The opening on real frames: each of the first `N` frames is a step of the model

`Route.Pipe` assumed the bound of the opening on the real frames: the position at the end of frame `N` is at most `P₀ + D` (`openB`). The bound is proved on a model
(`Opening`: the horizontal frame `hstep` and the measured jump lengths). Here the bound is a theorem, from a condition on each of the first `N` frames: the frame is a step of the
model (`OpenRun.step`). The model's state is read from the machines: the horizontal state (`Potential.startHS`) and the position; the frames left in the air are a sequence of
numbers (`air`), 0 at control.

* `OpenRun.reach`: frame `t` begins in a state that the model reaches in `t − 1` steps from the start, with the distance `P(t) − P(1)`.
* `OpenRun.endB`: with the bound of the model (`Opening.opt_of_check`, a check on the ROM), the position at the end of frame `N` is at most `P(1) + D`.

There is no game data in this file. Page: `1-1/a-5-4-OpenFrames.md`.
-/

namespace Smbrta.OpenFrames

open Potential (HS HIn inputsN hstep startHS)
open Opening (Lens valid modes succ start)

variable {sy : Syms} {m0 : Machine} {lens : Lens} {N E : Nat} {fm : Nat → Machine}

/-- **Each of the first `N` frames is a step of the opening's model.** For each counted frame `t` from 1 to `N`, before the entering frame `E`: an input `i` of the model, valid for
the frames left in the air (`air t`: on the ground when 0, else in the air with no jump start); the frames left in the air after it are those the model allows (on a jump start,
between the lengths of a one-frame press and of a held A for the speed at the takeoff, `Opening.modes`); the horizontal state at the next counted frame is `hstep` of this one on
`i`, and the position has moved by `16·v` (no wall, no edge of the screen). -/
structure OpenRun (sy : Syms) (m0 : Machine) (lens : Lens) (N E : Nat) (fm : Nat → Machine) where
  /-- the frames left in the air, when frame `t` begins -/
  air : Nat → Nat
  /-- on the ground at control -/
  air₁ : air 1 = 0
  /-- the step of each frame -/
  step : ∀ t, 1 ≤ t → t ≤ N → t < E → ∃ i ∈ inputsN, valid (air t) i = true ∧ air (t + 1) ∈ modes lens (startHS sy (fm t)) (air t) i ∧
    startHS sy (fm (t + 1)) = hstep sy m0 (startHS sy (fm t)) i ∧ posP sy (fm (t + 1)) = posP sy (fm t) + 16 * sbyte (startHS sy (fm (t + 1))).v

/-- a path of `Reach` with one step more at its end -/
theorem reach_snoc {σ : Type} {f : σ → List σ} : ∀ {x y z : σ} {k : Nat}, Cert.Reach f x k y → z ∈ f y → Cert.Reach f x (k + 1) z
  | _, _, _, _, .refl _, h => .step h (.refl _)
  | _, _, _, _, .step h1 h2, h => .step h1 (reach_snoc h2 h)

/-- the model's state when the counted frame `t` begins: the horizontal state, the frames left in the air, the distance from control -/
def stOf (O : OpenRun sy m0 lens N E fm) (t : Nat) : Opening.St := ((startHS sy (fm t), O.air t), posP sy (fm t) - posP sy (fm 1))

/-- **Frame `t` begins in a state that the model reaches in `t − 1` steps from the start**, when the horizontal state at control is that of the start (`hs`) -/
theorem OpenRun.reach (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) :
    ∀ k, k ≤ N → 1 + k ≤ E → Cert.Reach (succ sy m0 lens) (start sy m0) k (stOf O (1 + k))
  | 0, _, _ => by
    have e : stOf O 1 = start sy m0 := by
      show ((startHS sy (fm 1), O.air 1), posP sy (fm 1) - posP sy (fm 1)) = ((startHS sy m0, 0), 0)
      rw [hs, O.air₁, Int.sub_self]
    rw [Nat.add_zero, e]
    exact .refl _
  | k + 1, h1, h2 => by
    have ih := O.reach hs k (by omega) (by omega)
    refine reach_snoc ih ?_
    obtain ⟨i, hi, hv, hm, he, hp⟩ := O.step (1 + k) (by omega) (by omega) (by omega)
    unfold succ
    refine List.mem_flatMap.2 ⟨i, List.mem_filter.2 ⟨hi, hv⟩, List.mem_map.2 ⟨O.air (1 + k + 1), hm, ?_⟩⟩
    show ((hstep sy m0 (startHS sy (fm (1 + k))) i, O.air (1 + k + 1)), (posP sy (fm (1 + k)) - posP sy (fm 1)) + 16 * sbyte (hstep sy m0 (startHS sy (fm (1 + k))) i).v) =
      ((startHS sy (fm (1 + (k + 1))), O.air (1 + (k + 1))), posP sy (fm (1 + (k + 1))) - posP sy (fm 1))
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, ← he, hp]
    congr 1
    omega

/-- **The bound of the opening on real frames.** If the model does not get past `D` in `N` steps (`hopt`, the check of `Opening`), the counted frame `N + 1` begins at most `D`
right of control -/
theorem OpenRun.endB (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D) (hN : N < E) : posP sy (fm (N + 1)) ≤ posP sy (fm 1) + D := by
  have h := hopt N _ (Nat.le_refl _) (O.reach hs N (Nat.le_refl _) (by omega))
  have e : (stOf O (1 + N)).2 = posP sy (fm (1 + N)) - posP sy (fm 1) := rfl
  rw [e, show 1 + N = N + 1 by omega] at h
  omega

/-- **The old field `openB`**: the frames are read from the machines (`PipeFrames.Reads`), and the position at control is `P₀` -/
theorem OpenRun.openB {top amax : Int} {fr : Nat → TopSpeed.Frame top amax} (O : OpenRun sy m0 lens N E fm) (hs : startHS sy (fm 1) = startHS sy m0) {D : Int}
    (hopt : ∀ k u, k ≤ N → Cert.Reach (succ sy m0 lens) (start sy m0) k u → u.2 ≤ D) (R : PipeFrames.Reads sy E fm fr) (hP : posP sy (fm 1) = posP sy m0) (h1 : 1 ≤ N) :
    N < E → (fr N).P' ≤ posP sy m0 + D := fun hN => by
  rw [R.P' N h1 hN, ← hP]
  exact O.endB hs hopt hN

end Smbrta.OpenFrames
