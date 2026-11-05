import Theorems.TopSpeed
import Theorems.TasFastAccel

/-!
# Reach: how far Mario can get in `n` frames, counting the acceleration

The frames of `Theorems/TopSpeed.lean` (`Frame`, `Chain`). With `V = 256·v + f` (speed with
subspeed), one frame gives `V' ≤ max(V, 0) + amax` (`Frame.gain`) and moves `P` by at most
`adv(w)` when `max(V, 0) ≤ w` (`Frame.adv_le`). So from a start with `max(V, 0) ≤ w`, `n`
frames move `P` by at most

  `reach(w, n) = adv(w) + adv(w + amax) + … + adv(w + amax·(n-1))`

(`chain_reach`). Once `w + amax·k` reaches `256·top`, each later frame adds exactly `16·top`
(`reach_top`), so `reach(w, K + m) = reach(w, K) + 16·top·m` (`reach_add`). Page: `Reach.md`.
-/

namespace Smbrta.TopSpeed

/-- the most `n` frames can move `P`, from `max(V, 0) ≤ w` -/
def reach (top amax w : Int) : Nat → Int
  | 0 => 0
  | n + 1 => adv top amax w + reach top amax (w + amax) n

/-- `n` chained frames move `P` by at most `reach` -/
theorem chain_reach {top amax : Int} (h16 : 16 ≤ top) (h255 : 255 ≤ amax) :
    ∀ (fs : List (Frame top amax)) (f : Frame top amax) (w : Int), Chain (f :: fs) →
      (-top ≤ f.v ∧ f.v ≤ top) → max (256 * f.v + f.f) 0 ≤ w →
      (fs.getLastD f).P' - f.P ≤ reach top amax w (fs.length + 1)
  | [], f, w, _, hv, hw => by
    have := f.adv_le w hv hw
    simp only [List.getLastD_nil, reach]
    omega
  | g :: rest, f, w, hc, hv, hw => by
    obtain ⟨hgv, hgf, hgP, hrest⟩ := hc
    have hf := f.bound h16 hv
    have hg : -top ≤ g.v ∧ g.v ≤ top := by rw [hgv]; exact hf.1
    have hG := f.gain h255
    have hgw : max (256 * g.v + g.f) 0 ≤ w + amax := by rw [hgv, hgf]; omega
    have ih := chain_reach h16 h255 rest g (w + amax) hrest hg hgw
    have ha := f.adv_le w hv hw
    have hlast : ((g :: rest).getLastD f) = (rest.getLastD g) := List.getLastD_cons
    rw [hlast]
    simp only [reach] at ih ⊢
    omega

/-- after the speed bound reaches the top, each frame adds exactly `16·top` -/
theorem reach_top {top amax : Int} (h16 : 16 ≤ top) (ha : 0 ≤ amax) :
    ∀ (n : Nat) (w : Int), 256 * top ≤ w + amax → reach top amax w n = 16 * top * n
  | 0, w, _ => by simp [reach]
  | n + 1, w, hw => by
    have ih := reach_top h16 ha n (w + amax) (by omega)
    have hq : top ≤ (w + amax) / 256 := by omega
    have hadv : adv top amax w = 16 * top := by unfold adv; omega
    simp only [reach]
    rw [ih, hadv]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-- split `reach` after `k` frames -/
theorem reach_add {top amax : Int} :
    ∀ (k m : Nat) (w : Int), reach top amax w (k + m) = reach top amax w k + reach top amax (w + amax * k) m
  | 0, m, w => by simp [reach]
  | k + 1, m, w => by
    have ih := reach_add (top := top) (amax := amax) k m (w + amax)
    rw [show k + 1 + m = (k + m) + 1 by omega]
    simp only [reach]
    rw [ih]
    have e : w + amax + amax * (k : Int) = w + amax * ((k + 1 : Nat) : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
      omega
    rw [e]
    omega

/-- the closed form: past `K` frames, `reach(w, K + m) = reach(w, K) + 16·top·m` -/
theorem reach_closed {top amax w : Int} (K : Nat) (h16 : 16 ≤ top) (ha : 0 ≤ amax)
    (hK : 256 * top ≤ w + amax * K + amax) (m : Nat) :
    reach top amax w (K + m) = reach top amax w K + 16 * top * m := by
  rw [reach_add, reach_top h16 ha m _ hK]

/-- from a first frame with speed `v0` and subspeed `f0` (`|v0| ≤ top`) -/
theorem reach_from {top amax : Int} (h16 : 16 ≤ top) (h255 : 255 ≤ amax) (v0 f0 : Int)
    (hv : -top ≤ v0 ∧ v0 ≤ top) (fs : List (Frame top amax)) (f : Frame top amax)
    (hc : Chain (f :: fs)) (h0 : f.v = v0 ∧ f.f = f0) :
    (fs.getLastD f).P' - f.P ≤ reach top amax (max (256 * v0 + f0) 0) (fs.length + 1) := by
  obtain ⟨e1, e2⟩ := h0
  exact chain_reach h16 h255 fs f _ hc (by rw [e1]; exact hv) (by rw [e1, e2]; omega)

/-! ## The game's values -/

/-- `max(V, 0)` at the first controllable frame of 1-1 -/
def w0 (sy : Syms) (ctx : Machine) : Int := max (FastAccel.V (FastAccel.start sy ctx)) 0

/-- the bound with the game's top speed and largest adder, from the 1-1 start -/
def reachG (sy : Syms) (ctx : Machine) (n : Nat) : Int := reach (top sy) (amax sy ctx) (w0 sy ctx) n

/-- the first `K` after which every frame adds `16·top` -/
def reachK (sy : Syms) (ctx : Machine) : Nat :=
  (((256 * (top sy : Int) - w0 sy ctx - amax sy ctx) + amax sy ctx - 1) / amax sy ctx).toNat

/-- the distance `P` grows on the full emulator while playing `w` -/
def walkDist (sy : Syms) (ctx : Machine) (w : List UInt8) : Int :=
  posP sy (playFull ctx w) - posP sy ctx

/-- a witness of `n ≥ 32` frames: the TAS fast accel, then Right+B -/
def reachWitness (n : Nat) : List UInt8 := TasFastAccel.witness ++ List.replicate (n - 32) 0x41

end Smbrta.TopSpeed
