import Theorems.Opening
import Theorems.SurfaceFrames

/-!
# The opening: no input gets far to the left

`Opening` bounds how far right the model of the opening gets in `n` frames. Here is the same search to the left: no input of the model gets more than `T` to the left of
the start in `n` frames (`leftCheck`, `low_of_check`). The model is the same (`Opening.succ`: the horizontal frame `hstep` and the measured jump lengths). The search drops a
state that cannot get past `−T` any more: the potential bounds the speed either way (`Potential.step_J`: `|V| ≤ Φ`), and moving left the speed's byte can be 1 below the
bound on `V`, so `n` frames from `Φ ≤ p` move at most `SurfaceFrames.dl p n` to the left.

With `T` the position at control, the position stays at or right of 0 on the first `n` frames: the page is never 255 (`OpenFrames`). There is no game data in this file.
Page: `1-1/a-5-4-3-3-2-OpenLeft.md`.
-/

namespace Smbrta.OpenLeft

open Potential
open Opening (St Lens succ start pOf mem_succ OFacts J_pOf phi_nonneg)
open SurfaceFrames (dl)

variable {sy : Syms} {m : Machine} {lens : Lens}

/-- follow `x` with `r` frames left unless it is in the domain and cannot get past `−T` -/
def keepL (sy : Syms) (m : Machine) (T : Int) (r : Nat) (x : St) : Bool :=
  !inD sy x.1.1 || decide (x.2 - dl sy m (pOf sy m x.1.1) r < -T)

/-- **The search**: from the start, every state of the first `n` frames is at most `T` to the left -/
def leftCheck (sy : Syms) (m : Machine) (lens : Lens) (T : Int) (n : Nat) : Bool :=
  Cert.checkPrunedS (succ sy m lens) (fun x => decide (-T ≤ x.2)) (keepL sy m T) n [start sy m]

theorem dl_nonneg (F : Facts sy m) : ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ dl sy m p n
  | 0, _, _ => by simp [dl]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := dl_nonneg F n (nxt sy m p) (by omega)
    simp only [dl]
    have : 0 ≤ nxt sy m p / 256 := by omega
    omega

theorem dl_mono (F : Facts sy m) : ∀ (a k : Nat) (p : Int), 0 ≤ p → dl sy m p a ≤ dl sy m p (a + k)
  | 0, k, p, hp => by simpa [dl] using dl_nonneg F k p hp
  | a + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := dl_mono F a k (nxt sy m p) (by omega)
    rw [show a + 1 + k = (a + k) + 1 by omega]
    simp only [dl]
    omega

/-- from a state in the domain with `Φ ≤ p`, `k` steps move at most `dl p k` to the left -/
theorem reach_ge (F : OFacts sy m) :
    ∀ {x u : St} {k : Nat} (p : Int), Cert.Reach (succ sy m lens) x k u → J sy m x.1.1 p → x.2 - dl sy m p k ≤ u.2
  | _, _, _, p, .refl _, _ => by simp [dl]
  | x, u, _, p, @Cert.Reach.step _ _ _ y _ k hy hr, hJ => by
    obtain ⟨i, hi, hy1, hy2⟩ := mem_succ hy
    obtain ⟨hJ', _, _⟩ := step_J F.facts hJ (F.inputs_sub i hi)
    have hJy : J sy m y.1.1 (nxt sy m p) := by rw [hy1]; exact hJ'
    have ih := reach_ge F (nxt sy m p) hr hJy
    have h1 := phi_ge F.facts (hstep sy m x.1.1 i)
    have h2 := hJ'.2.1
    have h3 : (Potential.V (hstep sy m x.1.1 i)) = 256 * sbyte (hstep sy m x.1.1 i).v + ((hstep sy m x.1.1 i).f.toNat : Int) := rfl
    have h4 := (hstep sy m x.1.1 i).f.toNat_lt
    simp only [dl]
    omega

/-- **The search proves**: within `n` frames the distance never gets past `−T` to the left -/
theorem low_of_check {T : Int} {n : Nat} (F : OFacts sy m) (h : leftCheck sy m lens T n = true) :
    ∀ k u, k ≤ n → Cert.Reach (succ sy m lens) (start sy m) k u → -T ≤ u.2 := by
  intro k u hk hr
  have := Cert.prunedS_spec (succ sy m lens) (fun x => decide (-T ≤ x.2)) (keepL sy m T) ?_ n [start sy m] h (start sy m) (by simp) k u hk hr
  · simpa using this
  intro r x hx k' u' hk' hr'
  simp only [keepL, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at hx
  obtain ⟨hD, hlt⟩ := hx
  have h1 := reach_ge F (pOf sy m x.1.1) hr' (J_pOf hD)
  have h2 := dl_mono F.facts k' (r - k') (pOf sy m x.1.1) (by
    have := phi_nonneg F.facts x.1.1
    unfold pOf; split <;> omega)
  rw [show k' + (r - k') = r by omega] at h2
  simp only [decide_eq_true_eq]
  omega

end Smbrta.OpenLeft
