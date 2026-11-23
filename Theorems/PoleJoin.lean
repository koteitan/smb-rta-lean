import Theorems.SurfaceFrames
import Theorems.FastHop
import Theorems.PoleEntryRule
import Theorems.FrameKeep
import Theorems.PoleFrame
import Theorems.PoleTileWalk
import Theorems.PoleTileRead
import Theorems.PoleTileHeight
import Theorems.PoleTileFar
import Theorems.PoleTileKeep
import Theorems.PoleKeepFar
import Theorems.PoleSlot
import Theorems.PoleRing
import Theorems.StopRead

/-!
# Above ground: the castle entry from control

Joins the position bound (`SurfaceRun`), the collision rules (`PoleGrab`), the fast hop (`FastHop`), the jump (`Jump`) and the walk to the castle (`CastleWalk`). Frames are
counted from control above ground: `fr j` is frame `j` after control. The theorem is `castle_ge`: from what a real run gives (`Run`, every field a hypothesis), the castle
entry is at least `T + 7 + Nc` frames after control. The case split is in `direct_castle` and `castle_ge`:

* any other touch: not before `T + 1`, and the castle is `Nc + 6` or more frames later (`touch_ge`, `castle_of_other`);
* a direct grab by a fast jump: never (`fast_short`). The stored speed is read from the machines: each frame writes `|v₂|` into it or keeps it (`Run.stop_step`,
  `Run.stored_step`, by the walks of `StopRead`). If no frame since the landing wrote it, every frame in the block pushed him back (`fast_near`); if one did, he was
  left of the block's side there (`fast_late`). The jump need not come on the frame after the landing, and nothing is asked of the frame before it;
* a direct grab by a slow jump: not by `T + 6` (`slow_short`, with `Crossed` and `landing_cases` for every `k`); on `T + 7` and `T + 8` he moved left on the frame before, with the
  fraction below `F` (`slow_tight`), so the castle is `Nc` frames later; after `T + 8` the castle is at least `Nc − 1` frames later. `touch_castle` gives these cases to the timer.
  A fall has at most 3 frames in the base's rows, by a search of every fall (`fallCheck`, `fall_rows`); stepping off the base itself is too late (`base_late`).

The first hit: `first_of_surface` reads `J ≤ h` from `SurfaceRun.noHitCheck`.

`hop_short` is `PoleGrab.hop_le` without its hypothesis that every frame is at the side of the block. Page: `1-1/f-5-PoleJoin.md`.
-/

namespace Smbrta.PoleJoin

open TopSpeed (Frame Chain)
open PoleGrab (Next Side InBlock MaskL Low low_of_side low_of_inBlock side_step grab_le landing_far landing_one landing_left)

section Frames

variable {top amax : Int} {wd : Bool}

theorem v₂_range (h16 : 16 ≤ top) {f : Frame top amax wd} (hv : -top ≤ f.v ∧ f.v ≤ top) :
    -top ≤ f.v₂ ∧ f.v₂ ≤ top := by
  have h1 : -top ≤ f.v₁ ∧ f.v₁ ≤ top := by
    rcases f.anim with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  exact f.friction h1

/-- A frame below the block's top, on the ground or rising: `Side` at the side of the block, not moving left fast; left of it, he stays left of it. -/
def Beside (Ps : Int) (f : Frame top amax wd) : Prop := (Side f ∧ -12 ≤ f.v₂) ∨ (f.P₂ < Ps ∧ f.P' < Ps)

/-- With the feet over the block and inside it, falling: `InBlock`, and he is not moving left fast. -/
def Inside (Pf : Int) (f : Frame top amax wd) : Prop := Pf ≤ f.P₂ ∧ InBlock f ∧ -12 ≤ f.v₂

/-- A frame falling below the block's top: left of where the feet get over the block he stays left of it; with the feet over it, `Inside`. -/
def Falling (Pf : Int) (f : Frame top amax wd) : Prop := (f.P₂ < Pf ∧ f.P' < Pf) ∨ Inside Pf f

/-- where he can be after the landing: pushed back from the landing's position `Z`; or left of the side of the block; or pushed back from there -/
def HopState (Ps Z : Int) (f : Frame top amax wd) : Prop :=
  (Low f ∧ f.P ≤ Z) ∨ f.P < Ps ∨ (Low f ∧ f.P ≤ Ps + 16 * top - 256)

theorem hopState_step (h16 : 16 ≤ top) (hA : amax ≤ 512) {Ps Z : Int} {f g : Frame top amax wd}
    (hv : -top ≤ f.v ∧ f.v ≤ top) (hs : HopState Ps Z f) (hb : Beside Ps f) (hn : Next f g) :
    HopState Ps (Z - 16) g := by
  have hP := hn.2.2
  rcases hb with ⟨hb, _⟩ | ⟨_, h2⟩
  · have hl := low_of_side hb hn
    rcases hs with ⟨h1, h3⟩ | h3 | ⟨h1, h3⟩
    · have := side_step hA h1 hb
      exact Or.inl ⟨hl, by omega⟩
    · have hv2 := v₂_range h16 hv
      have hm := f.move
      refine Or.inr (Or.inr ⟨hl, ?_⟩)
      rcases hb with ⟨_, _, h4⟩ | ⟨_, _, h4⟩ <;> omega
    · have := side_step hA h1 hb
      exact Or.inr (Or.inr ⟨hl, by omega⟩)
  · exact Or.inr (Or.inl (by omega))

theorem hopState_iter (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps Z : Int) (L : Nat)
    (h0 : HopState Ps Z (fr (L + 1))) :
    ∀ m, (∀ j, j < m → -top ≤ (fr (L + j + 1)).v ∧ (fr (L + j + 1)).v ≤ top) →
      (∀ j, j < m → Beside Ps (fr (L + j + 1))) → (∀ j, j < m → Next (fr (L + j + 1)) (fr (L + j + 2))) →
      HopState Ps (Z - 16 * (m : Int)) (fr (L + m + 1))
  | 0, _, _, _ => by simpa using h0
  | m + 1, hv, hb, hn => by
    have ih := hopState_iter h16 hA fr Ps Z L h0 m (fun j hj => hv j (by omega)) (fun j hj => hb j (by omega))
      (fun j hj => hn j (by omega))
    have h := hopState_step h16 hA (hv m (by omega)) ih (hb m (by omega)) (hn m (by omega))
    rw [show L + (m + 1) + 1 = L + m + 2 by omega]
    have e : Z - 16 * ((m + 1 : Nat) : Int) = Z - 16 * (m : Int) - 16 := by push_cast; omega
    rw [e]
    exact h

theorem short_of_state (h16 : 16 ≤ top) (hA : amax ≤ 512) {Ps Z P₀ : Int} {f : Frame top amax wd}
    (hv : -top ≤ f.v ∧ f.v ≤ top) (hs : HopState Ps Z f) (hZ : Z + 32 < P₀) (hPs : Ps + 16 * top < P₀) :
    f.P₂ < P₀ := by
  rcases hs with ⟨h1, h3⟩ | h3 | ⟨h1, h3⟩
  · have := grab_le hA h1
    omega
  · have hv2 := v₂_range h16 hv
    have hm := f.move
    omega
  · have := grab_le hA h1
    omega

/-- After the landing, on the ground and rising: he can leave the side of the block, but he does not get to `P₀`, unless the landing's
position allows it. `PoleGrab.hop_le` is the case in which every frame is at the side. -/
theorem hop_short (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps P₀ : Int) (L m : Nat)
    (hPs : Ps + 16 * top < P₀)
    (hL : Beside Ps (fr L)) (hnL : Next (fr L) (fr (L + 1)))
    (hv : ∀ j, j ≤ m → -top ≤ (fr (L + j + 1)).v ∧ (fr (L + j + 1)).v ≤ top)
    (hb : ∀ j, j < m → Beside Ps (fr (L + j + 1))) (hn : ∀ j, j < m → Next (fr (L + j + 1)) (fr (L + j + 2)))
    (hZ : Side (fr L) → -12 ≤ (fr L).v₂ → (fr L).P' - 16 * (m : Int) + 32 < P₀) :
    (fr (L + m + 1)).P₂ < P₀ := by
  have hP := hnL.2.2
  have hm' : (0 : Int) ≤ m := by omega
  rcases hL with ⟨hL, hL12⟩ | ⟨_, h2⟩
  · have h0 : HopState Ps (fr L).P' (fr (L + 1)) := Or.inl ⟨low_of_side hL hnL, by omega⟩
    have h := hopState_iter h16 hA fr Ps _ L h0 m (fun j hj => hv j (by omega)) hb hn
    exact short_of_state h16 hA (hv m (Nat.le_refl _)) h (hZ hL hL12) hPs
  · have h0 : HopState Ps Ps (fr (L + 1)) := Or.inr (Or.inl (by omega))
    have h := hopState_iter h16 hA fr Ps _ L h0 m (fun j hj => hv j (by omega)) hb hn
    exact short_of_state h16 hA (hv m (Nat.le_refl _)) h (by omega) hPs

/-! ## Before the landing -/

/-- he is left of where the feet get over the block, or he moved over it on frame `e` and his feet have stayed inside since -/
def Crossed (fr : Nat → Frame top amax wd) (Pf : Int) (q j : Nat) : Prop :=
  (fr j).P < Pf ∨ ∃ e, q < e ∧ e < j ∧ (fr e).P < Pf ∧ Inside Pf (fr e) ∧ ∀ i, e < i → i < j → Inside Pf (fr i)

theorem crossed (fr : Nat → Frame top amax wd) (Pf : Int) (q : Nat) (hq : (fr q).P' < Pf) :
    ∀ n, (∀ j, j ≤ n → Next (fr (q + j)) (fr (q + j + 1))) → (∀ j, j < n → Falling Pf (fr (q + j + 1))) →
      Crossed fr Pf q (q + n + 1)
  | 0, hn, _ => Or.inl (by have := (hn 0 (Nat.le_refl _)).2.2; simp only [Nat.add_zero] at this ⊢; omega)
  | n + 1, hn, hf => by
    have ih := crossed fr Pf q hq n (fun j hj => hn j (by omega)) (fun j hj => hf j (by omega))
    have hnx := (hn (n + 1) (Nat.le_refl _)).2.2
    rw [show q + (n + 1) = q + n + 1 by omega] at hnx ⊢
    rcases hf n (Nat.lt_succ_self _) with ⟨_, h2⟩ | h2
    · exact Or.inl (by omega)
    · by_cases h3 : (fr (q + n + 1)).P < Pf
      · refine Or.inr ⟨q + n + 1, by omega, by omega, h3, h2, fun i h4 h5 => by omega⟩
      · rcases ih with h4 | ⟨e, h4, h5, h6, h8, h9⟩
        · exact absurd h4 h3
        · refine Or.inr ⟨e, h4, by omega, h6, h8, fun i h10 h11 => ?_⟩
          by_cases h12 : i = q + n + 1
          · rw [h12]
            exact h2
          · exact h9 i h10 (by omega)

/-! ## A fast jump -/

/-- What a fast jump on the frame after the landing `L` needs from the frames before it. `abs j` is the stored speed after frame `j`; `right j` is the moving
direction being right, at frame `j`'s collision. -/
structure FastLink (fr : Nat → Frame top amax wd) (Pf : Int) (q L A : Nat) (abs : Nat → Nat) (right : Nat → Bool) : Prop where
  /-- a fast jump reads the stored speed of the frame before it -/
  takeoff : A ≤ abs L
  /-- a frame from a stopped Mario writes `|v₂|` into the stored speed, or keeps the stored speed and the moving direction -/
  step : ∀ j, q < j → j ≤ L → (fr j).v = 0 → abs j = (fr j).v₂.natAbs ∨ (abs j = abs (j - 1) ∧ right j = right (j - 1))
  /-- moving right by speed, with the feet over the block: the direction is right -/
  cross : ∀ j, q < j → j < L → Pf ≤ (fr j).P₂ → 1 ≤ (fr j).v₂ → right j = true
  /-- feet inside the block, moving direction right: 1 px back -/
  push : ∀ j, q < j → j < L → Pf ≤ (fr j).P₂ → right j = true → (fr j).P' = (fr j).P₂ - 256

/-- Moved over the block at `e`, the feet inside until the landing `L`, and a fast jump after it: each frame after `e` starts stopped, so `|v₂|` is small there, and a frame that
writes it would leave the stored speed below `A`. So no frame wrote it, the moving direction stayed right, and every frame pushed him back. This gives the hypotheses of `PoleGrab.landing_left`. -/
theorem fast_pushes (hA : amax ≤ 512) {fr : Nat → Frame top amax wd} {Pf : Int} {q L A : Nat} {abs : Nat → Nat} {right : Nat → Bool}
    (K : FastLink fr Pf q L A abs right) (hA13 : 13 ≤ A) {e : Nat} (hqe : q < e) (heL : e < L)
    (hnx : ∀ j, e ≤ j → j < L → Next (fr j) (fr (j + 1))) (he : Inside Pf (fr e)) (hv : 1 ≤ (fr e).v₂)
    (hb : ∀ i, e < i → i < L → Inside Pf (fr i)) (hvL : -12 ≤ (fr L).v₂) :
    ∀ i, e < i → i < L → (fr i).P' = (fr i).P₂ - 256 := by
  have hin : ∀ j, e ≤ j → j < L → Inside Pf (fr j) := by
    intro j h1 h2
    by_cases h3 : j = e
    · rw [h3]; exact he
    · exact hb j (by omega) h2
  -- every frame after `e` starts stopped, with a fraction
  have hlow : ∀ i, e < i → i ≤ L → Low (fr i) := by
    intro i h1 h2
    have h3 := low_of_inBlock (hin (i - 1) (by omega) (by omega)).2.1 (hnx (i - 1) (by omega) (by omega))
    rwa [show i - 1 + 1 = i by omega] at h3
  have hsmall : ∀ i, e < i → i ≤ L → (fr i).v₂.natAbs < A := by
    intro i h1 h2
    have h3 := PoleGrab.speed_le_two hA (hlow i h1 h2)
    have h4 : -12 ≤ (fr i).v₂ := by
      by_cases h5 : i = L
      · rw [h5]; exact hvL
      · exact (hin i (by omega) (by omega)).2.2
    omega
  have hstop : ∀ i, e < i → i ≤ L → (fr i).v = 0 := by
    intro i h1 h2
    have h3 := (hnx (i - 1) (by omega) (by omega)).1
    rw [show i - 1 + 1 = i by omega] at h3
    rw [h3]
    exact (hin (i - 1) (by omega) (by omega)).2.1.1
  -- going back from the landing, each frame kept the stored speed and the moving direction
  have hkept : ∀ i, e < i → i ≤ L → A ≤ abs i → abs i = abs (i - 1) ∧ right i = right (i - 1) := by
    intro i h1 h2 h3
    rcases K.step i (by omega) h2 (hstop i h1 h2) with h4 | h4
    · have := hsmall i h1 h2
      omega
    · exact h4
  have hhigh : ∀ d, e + d < L → A ≤ abs (L - d) := by
    intro d
    induction d with
    | zero => intro _; exact K.takeoff
    | succ d ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := (hkept (L - d) (by omega) (by omega) h1).1
      rw [show L - (d + 1) = L - d - 1 by omega]
      omega
  have hkeep : ∀ i, e < i → i ≤ L → right i = right (i - 1) := by
    intro i h1 h2
    have h3 := hhigh (L - i) (by omega)
    rw [show L - (L - i) = i by omega] at h3
    exact (hkept i h1 h2 h3).2
  have hright : ∀ n, e + n < L → right (e + n) = true := by
    intro n
    induction n with
    | zero => intro _; exact K.cross e hqe heL he.1 hv
    | succ n ih =>
      intro h
      have h1 := hkeep (e + (n + 1)) (by omega) (by omega)
      rw [show e + (n + 1) - 1 = e + n by omega] at h1
      rw [h1]
      exact ih (by omega)
  intro i h1 h2
  have h3 := hright (i - e) (by omega)
  rw [show e + (i - e) = i by omega] at h3
  exact K.push i (by omega) h2 (hb i h1 h2).1 h3

/-! ## The direct grab -/

/-- What a real run gives before a direct grab on frame `g`: `q` is a frame left of where the feet get over the block, from which he stays below the block's
top until he lands on the ground on frame `L`; `T` is the takeoff frame of the jump, `fast` its class; `t` the last frame of the position bound. -/
structure Approach (fr : Nat → Frame top amax wd) (Ps Pf : Int) (t q L T g : Nat) (fast : Bool) : Prop where
  order : q < L ∧ L < T
  /-- left of where the feet get over the block -/
  left : (fr q).P' < Pf
  /-- the frames from there to the landing -/
  air : ∀ j, q < j → j < L → Falling Pf (fr j)
  /-- a push to the right blocks the Left button on the landing's frame -/
  mask : MaskL (fr (L - 1)) (fr L)
  /-- the landing -/
  land : Beside Ps (fr L)
  /-- on the ground and rising, until the grab -/
  hop : ∀ j, L < j → j < g → Beside Ps (fr j)
  /-- a fast jump: it reads a stored speed that nothing has updated since the landing; or a frame after the landing and before the jump wrote its speed, 13 or more
  either way, into the stored speed -/
  fastWay : fast = true →
    (∃ A abs right, 13 ≤ A ∧ FastLink fr Pf q L A abs right) ∨ ∃ j, L < j ∧ j < T ∧ (13 ≤ (fr j).v₂ ∨ (fr j).v₂ ≤ -13)
  /-- a slow jump's approach: a fall through the block's rows, from a frame not after `t + 1`, takes at most three frames -/
  rows : fast = false → ∀ e, q < e → e < L → e ≤ t + 1 → (∀ i, e ≤ i → i < L → Pf ≤ (fr i).P₂) → L ≤ e + 3

/-- What the frames before the landing leave, when the landing is at the side of the block: not past the left of the block by one frame's move, or he moved
over it on `e` at least two frames before and his feet stayed inside. -/
theorem landing_cases (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) {Pf : Int} {q L : Nat}
    (hC : Crossed fr Pf q L) (hsL : Side (fr L)) (hvL : -top ≤ (fr L).v ∧ (fr L).v ≤ top)
    (hnx : ∀ j, q < j → j < L → Next (fr j) (fr (j + 1)))
    (hvs : ∀ j, q < j → j < L → -top ≤ (fr j).v ∧ (fr j).v ≤ top) :
    (fr L).P' < Pf + 16 * top - 256 ∨
      ∃ e n, q < e ∧ L = e + n + 2 ∧ (fr e).P < Pf ∧ Inside Pf (fr e) ∧ (∀ i, e < i → i < L → Inside Pf (fr i)) := by
  rcases hC with hl | ⟨e, hqe, heL, h1, he, hb⟩
  · left
    have hv2 := v₂_range h16 hvL
    have hmv := (fr L).move
    rcases hsL with ⟨_, _, h3⟩ | ⟨h4, _, h3⟩ <;> omega
  · by_cases hk : L = e + 1
    · left
      subst hk
      have hve := v₂_range h16 (hvs e hqe (by omega))
      have hme := (fr e).move
      have h3 := landing_one hA h1 he.1 he.2.1 (hnx e hqe (by omega)) hsL
      omega
    · right
      exact ⟨e, L - e - 2, hqe, by omega, h1, he, hb⟩

/-- A fast jump that reads a stored speed nothing has updated since the landing `L`: `P₂(g) < P₀`, at any time, on any frame `g` after the frames on the ground and
rising that follow the landing. The jump need not be on the frame after the landing. -/
theorem fast_near (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps Pf P₀ : Int) {q L g : Nat}
    (hPs : Ps + 16 * top < P₀) (hfar : Pf + 16 * top ≤ P₀ + 224)
    (hg : L + 2 ≤ g) (hqL : q < L) (hleft : (fr q).P' < Pf)
    (hnx : ∀ j, q ≤ j → j < g → Next (fr j) (fr (j + 1)))
    (hv : ∀ j, q ≤ j → j ≤ g → -top ≤ (fr j).v ∧ (fr j).v ≤ top)
    (hair : ∀ j, q < j → j < L → Falling Pf (fr j))
    (hland : Beside Ps (fr L)) (hhop : ∀ j, L < j → j < g → Beside Ps (fr j))
    (hfl : ∃ A abs right, 13 ≤ A ∧ FastLink fr Pf q L A abs right) :
    (fr g).P₂ < P₀ := by
  obtain ⟨m, hm⟩ : ∃ m, g = L + m + 1 := ⟨g - L - 1, by omega⟩
  subst hm
  have hm1 : (1 : Int) ≤ m := by omega
  have hC : Crossed fr Pf q L := by
    have h := crossed fr Pf q hleft (L - q - 1) (fun j hj => hnx (q + j) (by omega) (by omega))
      (fun j hj => hair (q + j + 1) (by omega) (by omega))
    rwa [show q + (L - q - 1) + 1 = L by omega] at h
  refine hop_short h16 hA fr Ps P₀ L m hPs hland (hnx L (by omega) (by omega))
    (fun j hj => hv _ (by omega) (by omega))
    (fun j hj => hhop _ (by omega) (by omega))
    (fun j hj => hnx (L + j + 1) (by omega) (by omega)) ?_
  intro hsL hsL12
  have hvL := hv L (by omega) (by omega)
  rcases landing_cases h16 hA fr hC hsL hvL (fun j h1 h2 => hnx j (by omega) (by omega))
    (fun j h1 h2 => hv j (by omega) (by omega)) with h | ⟨e, n, hqe, hLe, h1, he, hb⟩
  · omega
  · subst hLe
    obtain ⟨A, abs, right, hA13, K⟩ := hfl
    have h2 := he.1
    have hve := v₂_range h16 (hv e (by omega) (by omega))
    have hme := (fr e).move
    have hpush := fast_pushes hA K hA13 hqe (by omega) (fun j h3 h4 => hnx j (by omega) (by omega)) he (by omega) hb hsL12
    obtain ⟨h3, h4⟩ := landing_left hA fr e h1 h2 he.2.1 (n + 1) (fun j hj => hnx (e + j) (by omega) (by omega))
      (fun j hj => ⟨(hb _ (by omega) (by omega)).2.1, hpush _ (by omega) (by omega)⟩)
    rw [show e + (n + 1) + 1 = e + n + 2 by omega] at h3 h4
    have h5 := side_step hA h3 hsL
    omega

/-- A frame `j` after the landing that ends its move with a speed of 13 or more, either way: the speed comes from running, so he has not been pushed since he was left of
the block's side, and the frames on the ground and rising after it do not bring him to `P₀`, on any later frame `g`. A fast jump after such a frame reads the stored
speed that it wrote; the jump need not be on the next frame. -/
theorem fast_late (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps P₀ : Int) {L j g : Nat}
    (hPs : Ps + 16 * top < P₀) (hLj : L < j) (hjg : j < g)
    (hland : Beside Ps (fr L)) (hnx : ∀ i, L ≤ i → i < g → Next (fr i) (fr (i + 1)))
    (hv : ∀ i, L < i → i ≤ g → -top ≤ (fr i).v ∧ (fr i).v ≤ top)
    (hb : ∀ i, L < i → i < g → Beside Ps (fr i))
    (hfast : 13 ≤ (fr j).v₂ ∨ (fr j).v₂ ≤ -13) :
    (fr g).P₂ < P₀ := by
  obtain ⟨m, hm⟩ : ∃ m, j = L + m + 1 := ⟨j - L - 1, by omega⟩
  subst hm
  obtain ⟨d, hd⟩ : ∃ d, g = L + m + 1 + d + 1 := ⟨g - (L + m + 1) - 1, by omega⟩
  subst hd
  have hnL := hnx L (Nat.le_refl _) (by omega)
  -- the state on the frame `j`
  obtain ⟨Z, h0⟩ : ∃ Z, HopState Ps Z (fr (L + 1)) := by
    rcases hland with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨(fr L).P', Or.inl ⟨low_of_side h1 hnL, by have := hnL.2.2; omega⟩⟩
    · exact ⟨Ps, Or.inr (Or.inl (by have := hnL.2.2; omega))⟩
  have hst := hopState_iter h16 hA fr Ps Z L h0 m (fun i hi => hv _ (by omega) (by omega))
    (fun i hi => hb _ (by omega) (by omega)) (fun i hi => hnx (L + i + 1) (by omega) (by omega))
  have hn1 : Next (fr (L + m + 1)) (fr (L + m + 1 + 1)) := hnx (L + m + 1) (by omega) (by omega)
  have hP1 := hn1.2.2
  -- on the next frame he is left of the block's side, or pushed back from there
  have hW : HopState Ps (Ps + 16 * top - 256) (fr (L + m + 1 + 1)) := by
    rcases hb (L + m + 1) (by omega) (by omega) with ⟨h1, h2⟩ | ⟨_, h2⟩
    · have hl := low_of_side h1 hn1
      have hv1 : 13 ≤ (fr (L + m + 1)).v₂ := by omega
      rcases hst with ⟨h3, _⟩ | h3 | ⟨h3, _⟩
      · have := PoleGrab.speed_le_two hA h3
        omega
      · have hvr := v₂_range h16 (hv (L + m + 1) (by omega) (by omega))
        have hmv := (fr (L + m + 1)).move
        refine Or.inl ⟨hl, ?_⟩
        rcases h1 with ⟨_, _, h4⟩ | ⟨h5, _, _⟩
        · omega
        · omega
      · have := PoleGrab.speed_le_two hA h3
        omega
    · exact Or.inr (Or.inl (by omega))
  -- and so on every later frame
  have hfin := hopState_iter h16 hA fr Ps (Ps + 16 * top - 256) (L + m + 1) hW d (fun i hi => hv _ (by omega) (by omega))
    (fun i hi => hb _ (by omega) (by omega)) (fun i hi => hnx (L + m + 1 + i + 1) (by omega) (by omega))
  have hd0 : (0 : Int) ≤ d := by omega
  exact short_of_state h16 hA (hv (L + m + 1 + d + 1) (by omega) (by omega)) hfin (by omega) hPs

/-- A fast jump: `P₂(g) < P₀` at any time. So a fast jump gives no direct grab at all. The two cases are those of `Approach.fastWay`: no frame since the landing
wrote the stored speed (`fast_near`), or one did (`fast_late`). -/
theorem fast_short (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps Pf P₀ : Int) (t : Nat) {q L T g : Nat}
    (hPs : Ps + 16 * top < P₀) (hfar : Pf + 16 * top ≤ P₀ + 224)
    (hnx : ∀ j, q ≤ j → j < g → Next (fr j) (fr (j + 1)))
    (hv : ∀ j, q ≤ j → j ≤ g → -top ≤ (fr j).v ∧ (fr j).v ≤ top)
    (G : Approach fr Ps Pf t q L T g true) (rise : g = T + 1) :
    (fr g).P₂ < P₀ := by
  obtain ⟨⟨hqL, hLT⟩, hleft, hair, _, hland, hhop, hfw, _⟩ := G
  subst rise
  rcases hfw rfl with hfl | ⟨j, hj1, hj2, hfast⟩
  · exact fast_near h16 hA fr Ps Pf P₀ hPs hfar (by omega) hqL hleft hnx hv hair hland hhop hfl
  · exact fast_late h16 hA fr Ps P₀ hPs hj1 (by omega) hland (fun i h1 h2 => hnx i (by omega) h2)
      (fun i h1 h2 => hv i (by omega) h2) hhop hfast

/-- A slow jump, in time: `P₂(g) < P₀` for `g ≤ t + 6`. `hB` is the position bound. -/
theorem slow_short (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps Pf P₀ B : Int) (t : Nat) {q L T g : Nat}
    (hPs : Ps + 16 * top < P₀) (hfar : Pf + 16 * top ≤ P₀ + 224) (hgap : B + 32 < P₀)
    (hB : ∀ e d : Nat, q < e → e < g → e + d = t → Pf ≤ (fr e).P₂ → (fr e).P₂ + 16 * top * (d : Int) ≤ B)
    (hnx : ∀ j, q ≤ j → j < g → Next (fr j) (fr (j + 1)))
    (hv : ∀ j, q ≤ j → j ≤ g → -top ≤ (fr j).v ∧ (fr j).v ≤ top)
    (G : Approach fr Ps Pf t q L T g false) (rise : g = T + 2) (hg : g ≤ t + 6) :
    (fr g).P₂ < P₀ := by
  obtain ⟨⟨hqL, hLT⟩, hleft, hair, hmask, hland, hhop, _, _⟩ := G
  obtain ⟨m, hm⟩ : ∃ m, g = L + m + 1 := ⟨g - L - 1, by omega⟩
  subst hm
  have hm2 : 2 ≤ m := by omega
  have hm2' : (2 : Int) ≤ m := by omega
  have hC : Crossed fr Pf q L := by
    have h := crossed fr Pf q hleft (L - q - 1) (fun j hj => hnx (q + j) (by omega) (by omega))
      (fun j hj => hair (q + j + 1) (by omega) (by omega))
    rwa [show q + (L - q - 1) + 1 = L by omega] at h
  refine hop_short h16 hA fr Ps P₀ L m hPs hland (hnx L (by omega) (by omega))
    (fun j hj => hv _ (by omega) (by omega)) (fun j hj => hhop _ (by omega) (by omega))
    (fun j hj => hnx (L + j + 1) (by omega) (by omega)) ?_
  intro hsL _
  rcases landing_cases h16 hA fr hC hsL (hv L (by omega) (by omega)) (fun j h1 h2 => hnx j (by omega) (by omega))
    (fun j h1 h2 => hv j (by omega) (by omega)) with h | ⟨e, n, hqe, hLe, h1, he, hb⟩
  · omega
  · subst hLe
    have h2 := he.1
    have hve := v₂_range h16 (hv e (by omega) (by omega))
    have hme := (fr e).move
    have h3 := landing_far hA fr e n h1 h2 he.2.1 (fun j hj => hnx (e + j) (by omega) (by omega))
      (fun j hj => (hb _ (by omega) (by omega)).2.1) hsL
      (by rw [show e + n + 2 - 1 = e + n + 1 by omega] at hmask; exact hmask)
    cases n with
    | zero =>
      push_cast at h3
      omega
    | succ n' =>
      obtain ⟨d, hd⟩ : ∃ d, e + d = t := ⟨t - e, by omega⟩
      have h7 := hB e d hqe (by omega) hd h2
      have hdn : ((n' + 1 : Nat) : Int) ≤ d + 1 := by omega
      have h8 : 256 * (d : Int) ≤ 16 * top * d :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega

/-- A slow jump on the first frame the position bound allows, `g = t + 7`: the landing's position bounds the touch. He has to move left on the two frames before the
touch, or the block pushes him back. So the frame before the touch moves left, and his position at the touch is at most the landing's. -/
theorem slow_tight (h16 : 16 ≤ top) (hA : amax ≤ 512) (fr : Nat → Frame top amax wd) (Ps Pf P₀ F : Int) (t : Nat) {q L T : Nat}
    (hPs : Ps + 16 * top < P₀) (hF : Pf + 16 * top + 32 ≤ P₀ + F) (hF0 : 0 ≤ F) (hF2 : F ≤ 208)
    (hnx : ∀ j, q ≤ j → j < T + 2 → Next (fr j) (fr (j + 1)))
    (hv : ∀ j, q ≤ j → j ≤ T + 2 → -top ≤ (fr j).v ∧ (fr j).v ≤ top)
    (G : Approach fr Ps Pf t q L T (T + 2) false) (hg : T + 2 ≤ t + 8)
    (hin : P₀ ≤ (fr (T + 2)).P₂) :
    (fr (T + 1)).v₂ < 0 ∧ (fr (T + 2)).P₂ < P₀ + F := by
  obtain ⟨⟨hqL, hLT⟩, hleft, hair, hmask, hland, hhop, _, hrows⟩ := G
  have hC : Crossed fr Pf q L := by
    have h := crossed fr Pf q hleft (L - q - 1) (fun j hj => hnx (q + j) (by omega) (by omega))
      (fun j hj => hair (q + j + 1) (by omega) (by omega))
    rwa [show q + (L - q - 1) + 1 = L by omega] at h
  have hnL := hnx L (by omega) (by omega)
  -- the landing's position
  have hZ : Side (fr L) → (fr L).P' < P₀ + F := by
    intro hsL
    rcases landing_cases h16 hA fr hC hsL (hv L (by omega) (by omega)) (fun j h1 h2 => hnx j (by omega) (by omega))
      (fun j h1 h2 => hv j (by omega) (by omega)) with h | ⟨e, n, hqe, hLe, h1, he, hb⟩
    · omega
    · subst hLe
      have h2 := he.1
      have hve := v₂_range h16 (hv e (by omega) (by omega))
      have hme := (fr e).move
      have h3 := landing_far hA fr e n h1 h2 he.2.1 (fun j hj => hnx (e + j) (by omega) (by omega))
        (fun j hj => (hb _ (by omega) (by omega)).2.1) hsL
        (by rw [show e + n + 2 - 1 = e + n + 1 by omega] at hmask; exact hmask)
      have hn1 : n ≤ 1 := by
        by_cases het : e ≤ t + 1
        · have := hrows rfl e hqe (by omega) het (fun i hi1 hi2 => by
            by_cases h9 : i = e
            · rw [h9]; exact he.1
            · exact (hb i (by omega) hi2).1)
          omega
        · omega
      have hn1' : (n : Int) ≤ 1 := by omega
      omega
  -- the state on the takeoff frame
  obtain ⟨Z, hZle, h0⟩ : ∃ Z, Z < P₀ + F ∧ HopState Ps Z (fr (L + 1)) := by
    rcases hland with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨(fr L).P', hZ h1, Or.inl ⟨low_of_side h1 hnL, by have := hnL.2.2; omega⟩⟩
    · exact ⟨Ps, by omega, Or.inr (Or.inl (by have := hnL.2.2; omega))⟩
  obtain ⟨m, hm⟩ : ∃ m, T = L + m + 1 := ⟨T - L - 1, by omega⟩
  subst hm
  have hst := hopState_iter h16 hA fr Ps Z L h0 m (fun j hj => hv _ (by omega) (by omega))
    (fun j hj => hhop _ (by omega) (by omega)) (fun j hj => hnx (L + j + 1) (by omega) (by omega))
  have hm0 : (0 : Int) ≤ m := by omega
  have hnT : Next (fr (L + m + 1)) (fr (L + m + 1 + 1)) := hnx (L + m + 1) (by omega) (by omega)
  have hnT1 : Next (fr (L + m + 1 + 1)) (fr (L + m + 1 + 2)) := hnx (L + m + 1 + 1) (by omega) (by omega)
  have hvT := hv (L + m + 1) (by omega) (by omega)
  have hvT1 := hv (L + m + 1 + 1) (by omega) (by omega)
  have hvg := hv (L + m + 1 + 2) (by omega) (by omega)
  have hbT := hhop (L + m + 1) (by omega) (by omega)
  have hbT1 := hhop (L + m + 1 + 1) (by omega) (by omega)
  -- from a frame left of the side or pushed back from there, the touch is short of `P₀`
  have hshort : HopState Ps (Ps + 16 * top - 256) (fr (L + m + 1 + 1)) → False := by
    intro h1
    have h2 := hopState_step h16 hA hvT1 h1 hbT1 hnT1
    have h3 := short_of_state h16 hA hvg h2 (by omega) hPs
    exact absurd hin (by omega)
  have hP1 := hnT.2.2
  have hP2 := hnT1.2.2
  rcases hst with ⟨hl, hle⟩ | hle | ⟨hl, hle⟩
  · rcases hbT with ⟨hs, _⟩ | ⟨_, h2⟩
    · have hl1 := low_of_side hs hnT
      rcases hbT1 with ⟨hs1, _⟩ | ⟨_, h2⟩
      · have hl2 := low_of_side hs1 hnT1
        have hg2 := grab_le hA hl2
        have hs2 := PoleGrab.speed_le_two hA hl
        have hs3 := PoleGrab.speed_le_two hA hl1
        have hm1 := (fr (L + m + 1)).move
        have hm2 := (fr (L + m + 1 + 1)).move
        rcases hs with ⟨h4, _, h5⟩ | ⟨h4, _, h5⟩ <;> rcases hs1 with ⟨h6, _, h7⟩ | ⟨h6, _, h7⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · exact ⟨h6, by omega⟩
      · exfalso
        have h3 : HopState Ps (Ps + 16 * top - 256) (fr (L + m + 1 + 2)) := Or.inr (Or.inl (by omega))
        have h4 := short_of_state h16 hA hvg h3 (by omega) hPs
        omega
    · exact (hshort (Or.inr (Or.inl (by omega)))).elim
  · exact (hopState_step h16 hA hvT (Or.inr (Or.inl hle) : HopState Ps (Ps + 16 * top - 256 + 16) _) hbT hnT |>
      fun h1 => hshort (by simpa using h1)).elim
  · exact (hopState_step h16 hA hvT (Or.inr (Or.inr ⟨hl, hle⟩) : HopState Ps (Ps + 16 * top - 256 + 16) _) hbT hnT |>
      fun h1 => hshort (by simpa using h1)).elim

/-! ## Lists of consecutive frames -/

/-- the frames `a`, `a + 1`, ... -/
def seg (fr : Nat → Frame top amax wd) : Nat → Nat → List (Frame top amax wd)
  | _, 0 => []
  | a, n + 1 => fr a :: seg fr (a + 1) n

theorem seg_length (fr : Nat → Frame top amax wd) : ∀ n a, (seg fr a n).length = n
  | 0, _ => rfl
  | n + 1, a => by simp [seg, seg_length fr n (a + 1)]

theorem seg_chain (fr : Nat → Frame top amax wd) :
    ∀ n a, (∀ j, a ≤ j → j < a + n → Next (fr j) (fr (j + 1))) → Chain (fr a :: seg fr (a + 1) n)
  | 0, _, _ => trivial
  | n + 1, a, h => by
    obtain ⟨h1, h2, h3⟩ := h a (Nat.le_refl _) (by omega)
    exact ⟨h1, h2, h3, seg_chain fr n (a + 1) (fun j hj hj2 => h j (by omega) (by omega))⟩

theorem seg_last (fr : Nat → Frame top amax wd) :
    ∀ n a, (seg fr (a + 1) n).getLastD (fr a) = fr (a + n)
  | 0, a => rfl
  | n + 1, a => by
    have h := seg_last fr n (a + 1)
    simp only [seg]
    rw [List.getLastD_cons, h]
    congr 1
    omega

end Frames

/-! ## From the position bound: `t`, `B` -/

section Surface

open Potential (HIn inputs hdist startHS)
open TopSpeed (top)
open SurfaceRun (Statement poleP hit_bound noHitCheck)

variable {sy : Syms} {m0 : Machine} {tp am : Int}

theorem speed_range (h16 : 16 ≤ (top sy : Int)) {fr : Nat → Frame (top sy) (amax sy m0) true} {g : Nat}
    (hnx : ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1))) (hv : (fr 1).v = 0) :
    ∀ n, n + 1 ≤ g → -(top sy : Int) ≤ (fr (n + 1)).v ∧ (fr (n + 1)).v ≤ (top sy : Int)
  | 0, _ => by simp only [Nat.zero_add]; rw [hv]; omega
  | n + 1, h => by
    have ih := speed_range h16 hnx hv n (by omega)
    have h1 := (fr (n + 1)).speed ih
    have h2 := (hnx (n + 1) (by omega) (by omega)).1
    rw [h2]
    exact h1

/-- the crude bound, for the first frames: `max(P, B)` grows by at most `16·top` a frame (`TopSpeed.Frame.posB`, and the bases follow each other) -/
theorem early_leB (h16 : 16 ≤ (top sy : Int)) {fr : Nat → Frame (top sy) (amax sy m0) true} {g : Nat} {PA : Int}
    (hnx : ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1))) (hv : (fr 1).v = 0) (hP : (fr 1).P = PA)
    (hlk : ∀ t, 1 ≤ t → t < g → (fr (t + 1)).B ≤ max (max (fr t).P (fr t).B) (fr (t + 1)).P) (hb1 : (fr 1).B ≤ PA) :
    ∀ n, n + 1 ≤ g → max (fr (n + 1)).P (fr (n + 1)).B ≤ PA + 16 * (top sy : Int) * (n : Int)
  | 0, _ => by simp only [Nat.zero_add, Int.natCast_zero, Int.mul_zero]; omega
  | n + 1, h => by
    have ih := early_leB h16 hnx hv hP hlk hb1 n (by omega)
    have h1 := (fr (n + 1)).posB h16 (speed_range h16 hnx hv n (by omega))
    have h2 := (hnx (n + 1) (by omega) (by omega)).2.2
    have h3 := hlk (n + 1) (by omega) (by omega)
    have e : 16 * (top sy : Int) * ((n + 1 : Nat) : Int) = 16 * (top sy : Int) * (n : Int) + 16 * (top sy : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [e]
    rw [h2] at h3 ⊢
    omega

/-- the crude bound, for the first frames -/
theorem early_le (h16 : 16 ≤ (top sy : Int)) {fr : Nat → Frame (top sy) (amax sy m0) true} {g : Nat} {PA : Int}
    (hnx : ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1))) (hv : (fr 1).v = 0) (hP : (fr 1).P = PA)
    (hlk : ∀ t, 1 ≤ t → t < g → (fr (t + 1)).B ≤ max (max (fr t).P (fr t).B) (fr (t + 1)).P) (hb1 : (fr 1).B ≤ PA) :
    ∀ n, n + 1 ≤ g → (fr (n + 1)).P ≤ PA + 16 * (top sy : Int) * (n : Int) := fun n h => by
  have := early_leB h16 hnx hv hP hlk hb1 n h
  omega

/-- the bases of the frames `a`, `a + 1`, ... follow each other -/
theorem seg_chainB {fr : Nat → Frame (top sy) (amax sy m0) true} :
    ∀ n a, (∀ j, a ≤ j → j < a + n → (fr (j + 1)).B ≤ max (max (fr j).P (fr j).B) (fr (j + 1)).P) → TopSpeed.ChainB (fr a :: seg fr (a + 1) n)
  | 0, _, _ => trivial
  | n + 1, a, h => ⟨h a (Nat.le_refl _) (by omega), seg_chainB n (a + 1) (fun j hj hj2 => h j (by omega) (by omega))⟩

theorem take_snoc {α : Type} (w : List α) (k : Nat) (hk : k < w.length) : ∃ i ∈ w, w.take (k + 1) = w.take k ++ [i] := by
  refine ⟨w[k], List.getElem_mem hk, ?_⟩
  simp

/-- The line of the position bound, on a real run, hits included: at frame `j` at most `PA + X + 16·top·(j − N)`. This joins `Statement.after` and `hit_bound`. -/
theorem line {n N E T J dx dy : Nat} {X : Int} (F : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy)
    (h16 : 16 ≤ (top sy : Int)) (h255 : 255 ≤ amax sy m0) (hE : 1 ≤ E) (hJ : 1 ≤ J)
    {PA : Int} {fr : Nat → Frame (top sy) (amax sy m0) true} {w : List HIn} {h g : Nat}
    (R : Surface sy m0 PA T J g fr w h) (hJh : J ≤ h) (hnx : ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1))) (hv : (fr 1).v = 0)
    (j : Nat) (h1 : N + E ≤ j) (h2 : j ≤ T) (h3 : j < g) :
    (fr j).P' ≤ PA + X + 16 * (top sy : Int) * ((j - N : Nat) : Int) := by
  have hs : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  have hd : ∀ a, a ≤ T → N ≤ a → hdist sy m0 (startHS sy m0) (w.take a) ≤ X + 16 * (top sy : Int) * ((a - N : Nat) : Int) := by
    intro a ha1 ha2
    exact S.after (w.take a) (fun i hi => R.mem i (List.mem_of_mem_take hi)) (a - N)
      (by simp; have := R.long; omega)
  have hj1 : 1 ≤ j := by omega
  -- every prefix up to `T`, with `S.within` for those up to `N`
  have hd' : ∀ a, a ≤ T → hdist sy m0 (startHS sy m0) (w.take a) ≤ X + 16 * (top sy : Int) * ((a - N : Nat) : Int) := by
    intro a ha1
    by_cases haN : N ≤ a
    · exact hd a ha1 haN
    · have := S.within (w.take a) (fun i hi => R.mem i (List.mem_of_mem_take hi)) (by simp; omega)
      rw [show a - N = 0 by omega]
      simp only [Int.natCast_zero, Int.mul_zero, Int.add_zero]
      exact this
  have hmono : ∀ a b : Nat, a ≤ b → 16 * (top sy : Int) * (a : Int) ≤ 16 * (top sy : Int) * (b : Int) :=
    fun a b hab => Int.mul_le_mul_of_nonneg_left (by omega) hs
  by_cases hjh : j < h
  · have := R.model j hj1 hjh h2 h3
    have := hd j h2 (by omega)
    omega
  · by_cases hjh2 : j = h
    · subst hjh2
      obtain ⟨a, ha⟩ : ∃ a, j - N = a + 1 := ⟨j - N - 1, by omega⟩
      have e1 : j - 1 - N = a := by omega
      have e2 : 16 * (top sy : Int) * ((a + 1 : Nat) : Int) = 16 * (top sy : Int) * (a : Int) + 16 * (top sy : Int) := by
        push_cast
        rw [Int.mul_add, Int.mul_one]
      rcases R.hit h2 with h4 | ⟨s, hs1, h4⟩
      · have := hd j h2 (by omega)
        omega
      · have h5 := hd' s (by omega)
        have h6 := hmono (s - N) a (by omega)
        rw [ha, e2]
        omega
    · -- after the first hit
      have hhj : h < j := by omega
      have hhT : h ≤ T := by omega
      obtain ⟨p, hp⟩ : ∃ p, h = p + 1 := ⟨h - 1, by omega⟩
      obtain ⟨i, hi, hti⟩ := take_snoc w p (by have := R.long; omega)
      have hmemp : ∀ a ∈ w.take p, a ∈ inputs := fun a ha => R.mem a (List.mem_of_mem_take ha)
      have hnh := hnx h (by omega) (by omega)
      have hlen : (w.take p).length = p := by simp; have := R.long; omega
      have hit : (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) (w.take p ++ [i]) - 256 ∨
          ∃ s, s ≤ (w.take p).length ∧ (fr h).P' ≤ PA + hdist sy m0 (startHS sy m0) ((w.take p).take s) + 256 := by
        rcases R.hit hhT with h4 | ⟨s, hs1, h4⟩
        · left
          rw [hp] at h4 ⊢
          rwa [hti] at h4
        · right
          refine ⟨s, by omega, ?_⟩
          rw [List.take_take, show min s p = s by omega]
          exact h4
      have hB : (fr (h + 1)).B ≤ (fr h).P' ∨
          ∃ s, s ≤ (w.take p).length ∧ (fr (h + 1)).B ≤ PA + hdist sy m0 (startHS sy m0) ((w.take p).take s) := by
        rcases R.base hhT with h4 | ⟨s, hs1, h4⟩
        · exact Or.inl h4
        · right
          refine ⟨s, by omega, ?_⟩
          rw [List.take_take, show min s p = s by omega]
          exact h4
      have hlast := seg_last fr (j - h - 1) (h + 1)
      have hchain := seg_chain fr (j - h - 1) (h + 1) (fun a ha hb => hnx a (by omega) (by omega))
      have hchainB := seg_chainB (fr := fr) (j - h - 1) (h + 1) (fun a ha hb => R.links a (by omega) (by omega))
      have hsp := speed_range h16 hnx hv h (by omega)
      have hstop := R.stop hhT
      have hbd := SurfaceRun.hit_boundB (k := j - N - E) F S.search S.hits h16 h255 hmemp (R.mem i hi)
        (by simp; have := R.long; omega) hit (fr (h + 1)) (seg fr (h + 1 + 1) (j - h - 1)) hchain hchainB
        ⟨hsp.1, by rw [hnh.1]; exact hstop⟩
        (by have h5 := hnh.2.1; have h6 := (fr h).impedeF; have h7 := (fr h).frac; omega) hnh.2.2 hB
        (by rw [seg_length]; simp; have := R.long; omega)
      rw [hlast, show h + 1 + (j - h - 1) = j by omega, show E + (j - N - E) = j - N by omega] at hbd
      exact hbd

/-- `hB` of `grab_short`: on any frame `e` with `Pf ≤ P₂(e)`, `P₂(e) + 16·top·(T − e)` is at most `B = PA + X + 16·top·(T − N)`. -/
theorem hB_of_line {n N E T J dx dy : Nat} {X : Int} (F : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy)
    (h16 : 16 ≤ (top sy : Int)) (h255 : 255 ≤ amax sy m0) (hE : 1 ≤ E) (hJ : 1 ≤ J)
    {PA Pf : Int} {fr : Nat → Frame (top sy) (amax sy m0) true} {w : List HIn} {h g : Nat}
    (R : Surface sy m0 PA T J g fr w h) (hJh : J ≤ h) (hnx : ∀ j, 1 ≤ j → j < g → Next (fr j) (fr (j + 1))) (hv : (fr 1).v = 0)
    (hP : (fr 1).P = PA) (hearly : PA + 16 * (top sy : Int) * ((N + E : Nat) : Int) < Pf)
    (e d : Nat) (he1 : 1 ≤ e) (heg : e ≤ g) (hd : e + d = T) (hPf : Pf ≤ (fr e).P₂) :
    (fr e).P₂ + 16 * (top sy : Int) * (d : Int) ≤ PA + X + 16 * (top sy : Int) * ((T - N : Nat) : Int) := by
  have hs : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  obtain ⟨a, ha⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
  subst ha
  have hsp := speed_range h16 hnx hv a (by omega)
  have hv2 := v₂_range h16 hsp
  have hm := (fr (a + 1)).move
  by_cases hae : a < N + E
  · exfalso
    have h1 := early_le h16 hnx hv hP R.links (R.base₁ (by omega)) a (by omega)
    have h2 : 16 * (top sy : Int) * ((a + 1 : Nat) : Int) ≤ 16 * (top sy : Int) * ((N + E : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hs
    have h3 : 16 * (top sy : Int) * ((a + 1 : Nat) : Int) = 16 * (top sy : Int) * (a : Int) + 16 * (top sy : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    omega
  · have hl := line F S h16 h255 hE hJ R hJh hnx hv a (by omega) (by omega) (by omega)
    have hnxa := (hnx a (by omega) (by omega)).2.2
    have e1 : T - N = (a - N) + 1 + d := by omega
    have e2 : 16 * (top sy : Int) * (((a - N) + 1 + d : Nat) : Int) =
        16 * (top sy : Int) * ((a - N : Nat) : Int) + 16 * (top sy : Int) + 16 * (top sy : Int) * (d : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_add, Int.mul_one]
    rw [e1, e2]
    omega

end Surface

/-! ## From the collision routine to the frames -/

section Rules

open PoleGrab (Case collide ruleOk colX topY)
open TopSpeed (Frame)

variable {top amax : Int} {wd : Bool}

/-- The real frame `f` runs `PlayerBGCollision` as `PoleGrab.collide` does on the case `c`: the speed and the position's pixel before and after are those of the case;
the page and the fraction stay (`base`). -/
structure Collides (sy : Syms) (mp : Machine) (f : Frame top amax wd) (c : Case) : Prop where
  pos : ∃ base : Int, f.P₂ = base + 256 * (c.x.toNat : Int) ∧
    f.P' = base + 256 * ((peek (collide sy mp c) sy.Player_X_Position).toNat : Int)
  v₂ : f.v₂ = sbyte c.v
  v' : f.v' = sbyte (peek (collide sy mp c) sy.Player_X_Speed)

/-- on the ground, or rising with the lower side check at the height of the block -/
def lowCase (sy : Syms) (c : Case) : Bool :=
  if 0 ≤ sbyte c.vy then decide (topY sy + 16 ≤ c.y.toNat + sy.FeetAdderY.toNat)
  else decide (topY sy ≤ c.y.toNat + sy.SideAdderY.toNat)

/-- the right side is at the block -/
def sideCase (sy : Syms) (c : Case) : Bool := decide (colX sy ≤ c.x.toNat + sy.SideAdderX.toNat)

/-- falling with the feet inside the block -/
def inBlockCase (sy : Syms) (c : Case) : Bool :=
  decide (0 ≤ sbyte c.vy) && decide (topY sy + sy.LandDepth.toNat ≤ c.y.toNat + sy.FeetAdderY.toNat) &&
    decide (c.y.toNat + sy.FeetAdderY.toNat < topY sy + 16) && decide (colX sy ≤ c.x.toNat + sy.FeetAdderX.toNat)

theorem sub_one_toNat {x : UInt8} (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 := by
  have := x.toNat_lt
  rw [UInt8.toNat_sub, show (1 : UInt8).toNat = 1 from rfl]
  omega

theorem add_one_toNat {x : UInt8} (h : x.toNat < 255) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt8.toNat_add, show (1 : UInt8).toNat = 1 from rfl]
  omega

theorem sbyte_zero : sbyte 0 = 0 := by decide

/-- pushed back: 1 px back and speed 0 -/
theorem push_back {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd} (hx : 1 ≤ c.x.toNat) (C : Collides sy mp f c)
    (h1 : peek (collide sy mp c) sy.Player_X_Position = c.x - 1) (h2 : peek (collide sy mp c) sy.Player_X_Speed = 0) :
    f.v' = 0 ∧ f.P' = f.P₂ - 256 := by
  obtain ⟨⟨base, h3, h4⟩, _, h6⟩ := C
  rw [h2, sbyte_zero] at h6
  rw [h1, sub_one_toNat hx] at h4
  refine ⟨h6, ?_⟩
  push_cast [Int.natCast_sub hx] at h4
  omega

/-- pushed forward: 1 px forward and speed 0 -/
theorem push_forward {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd} (hx : c.x.toNat < 255) (C : Collides sy mp f c)
    (h1 : peek (collide sy mp c) sy.Player_X_Position = c.x + 1) (h2 : peek (collide sy mp c) sy.Player_X_Speed = 0) :
    f.v' = 0 ∧ f.P' = f.P₂ + 256 := by
  obtain ⟨⟨base, h3, h4⟩, _, h6⟩ := C
  rw [h2, sbyte_zero] at h6
  rw [h1, add_one_toNat hx] at h4
  refine ⟨h6, ?_⟩
  push_cast at h4
  omega

/-- not moved -/
theorem no_push {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd} (C : Collides sy mp f c)
    (h1 : peek (collide sy mp c) sy.Player_X_Position = c.x) (h2 : peek (collide sy mp c) sy.Player_X_Speed = c.v) :
    f.v' = f.v₂ ∧ f.P' = f.P₂ := by
  obtain ⟨⟨base, h3, h4⟩, h5, h6⟩ := C
  rw [h2, ← h5] at h6
  rw [h1] at h4
  exact ⟨h6, by omega⟩

/-- the rule at the side of the block, on frames -/
theorem side_of_sideRule {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd} (hx : 1 ≤ c.x.toNat) (C : Collides sy mp f c)
    (h : (if 0 ≤ sbyte c.v then
        peek (collide sy mp c) sy.Player_X_Position == c.x - 1 && peek (collide sy mp c) sy.Player_X_Speed == 0 &&
          peek (collide sy mp c) sy.Player_CollisionBits == sy.noRight
      else
        peek (collide sy mp c) sy.Player_X_Position == c.x && peek (collide sy mp c) sy.Player_X_Speed == c.v &&
          peek (collide sy mp c) sy.Player_CollisionBits == sy.noRight) = true) :
    PoleGrab.Side f := by
  have hv := C.v₂
  by_cases h0 : 0 ≤ sbyte c.v
  · rw [if_pos h0] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := push_back hx C h.1.1 h.1.2
    exact Or.inl ⟨by omega, h1, h2⟩
  · rw [if_neg h0] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := no_push C h.1.1 h.1.2
    exact Or.inr ⟨by omega, h1, h2⟩

/-- on the ground or rising low, at the side of the block: `Side` -/
theorem side_of_rule {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd}
    (h : ruleOk sy mp c = true) (hl : lowCase sy c = true) (hs : sideCase sy c = true) (hx : 1 ≤ c.x.toNat)
    (hd : sy.LandDepth.toNat ≤ 16) (C : Collides sy mp f c) : PoleGrab.Side f := by
  simp only [lowCase] at hl
  simp only [sideCase, decide_eq_true_eq] at hs
  simp only [ruleOk, Bool.and_eq_true] at h
  have h := h.2
  by_cases hvy : 0 ≤ sbyte c.vy
  · rw [if_pos hvy] at hl h
    simp only [decide_eq_true_eq] at hl h
    rw [if_neg (by omega), if_neg (by omega), if_pos hl] at h
    simp only [Bool.and_eq_true] at h
    rw [if_pos hs] at h
    exact side_of_sideRule hx C h.2
  · rw [if_neg hvy] at hl h
    simp only [decide_eq_true_eq] at hl
    simp only [Bool.and_eq_true] at h
    have h := h.2
    rw [if_pos hl] at h
    simp only [Bool.and_eq_true] at h
    have h := h.2
    rw [if_pos hs] at h
    exact side_of_sideRule hx C h

/-- moving right by speed, the direction is right -/
theorem md_of_right {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd} (hmd : c.md ∈ Potential.mds c.v) (C : Collides sy mp f c)
    (h6 : 1 ≤ f.v₂) : c.md = 1 := by
  have hv := C.v₂
  rw [hv] at h6
  have h7 : c.v < 0x80 ∧ c.v ≠ 0 := by
    simp only [sbyte] at h6
    by_cases h8 : c.v < 0x80
    · rw [if_pos h8] at h6
      refine ⟨h8, fun h9 => ?_⟩
      rw [h9] at h6
      exact absurd h6 (by decide)
    · rw [if_neg h8] at h6
      have := c.v.toNat_lt
      omega
  simp only [Potential.mds] at hmd
  rw [if_neg (by simpa using h7.2), if_pos (by simpa using h7.1)] at hmd
  simpa using hmd

/-- falling with the feet inside the block: `InBlock` -/
theorem inBlock_of_rule {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd}
    (h : ruleOk sy mp c = true) (hb : inBlockCase sy c = true) (hmd : c.md ∈ Potential.mds c.v)
    (hx : 1 ≤ c.x.toNat) (hx2 : c.x.toNat < 255) (C : Collides sy mp f c) : PoleGrab.InBlock f := by
  simp only [inBlockCase, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hvy, h1⟩, h2⟩, h3⟩ := hb
  simp only [ruleOk, Bool.and_eq_true] at h
  have h := h.2
  rw [if_pos hvy, if_pos (by simp only [decide_eq_true_eq]; omega)] at h
  simp only [Bool.and_eq_true] at h
  have h := h.1.1.1
  have hv := C.v₂
  by_cases hm : (c.md == 1) = true
  · rw [if_pos hm] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h4, h5⟩ := push_back hx C h.1.1 h.1.2
    refine ⟨h4, ?_⟩
    by_cases h6 : 1 ≤ f.v₂
    · exact Or.inl ⟨h6, h5⟩
    · exact Or.inr ⟨by omega, Or.inl h5⟩
  · rw [if_neg hm] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h4, h5⟩ := push_forward hx2 C h.1.1 h.1.2
    refine ⟨h4, Or.inr ⟨?_, Or.inr h5⟩⟩
    by_cases h6 : 1 ≤ f.v₂
    · exact absurd (by simp [md_of_right hmd C h6]) hm
    · omega

/-- falling with the feet inside the block, moving direction right: 1 px back -/
theorem push_of_rule {sy : Syms} {mp : Machine} {c : Case} {f : Frame top amax wd}
    (h : ruleOk sy mp c = true) (hb : inBlockCase sy c = true) (hd : c.md = 1)
    (hx : 1 ≤ c.x.toNat) (C : Collides sy mp f c) : f.P' = f.P₂ - 256 := by
  simp only [inBlockCase, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hvy, h1⟩, h2⟩, h3⟩ := hb
  simp only [ruleOk, Bool.and_eq_true] at h
  have h := h.2
  rw [if_pos hvy, if_pos (by simp only [decide_eq_true_eq]; omega)] at h
  simp only [Bool.and_eq_true] at h
  have h := h.1.1.1
  rw [if_pos (by simp [hd])] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact (push_back hx C h.1.1 h.1.2).2

theorem mem_cases {sy : Syms} {c : Case} (h : c ∈ PoleGrab.cases sy) :
    c.x ∈ PoleGrab.caseXs sy ∧ c.md ∈ Potential.mds c.v ∧ -12 ≤ sbyte c.v := by
  simp only [PoleGrab.cases, List.mem_flatMap, List.mem_map] at h
  obtain ⟨x, hx, y, _, v, hv, md, hmd, _, _, fd, _, rfl⟩ := h
  simp only [PoleGrab.caseVs, List.mem_filter, decide_eq_true_eq] at hv
  exact ⟨hx, hmd, hv.2⟩

end Rules

/-! ## The whole statement -/

section Whole

open Potential (HS HIn inputsN hstep facings rsVals)
open TopSpeed (top bytes speedsB upTo collBits absB frictionCheck)
open SurfaceRun (Statement poleP polePage above)
open PoleGrab (cases caseXs colX poleCheck maskCheck withPole)
open CastleWalk (castle touchAt firstX fracs bigFrac otherYs grabXs)
open PipeTransition (run zeros)

variable {sy : Syms} {m0 : Machine} {tp am : Int} {wd : Bool}

/-- where his right side reaches the column of the pole, on the pole's page -/
def sideP (sy : Syms) (m0 : Machine) : Int :=
  256 * (256 * (polePage sy m0 : Int) + ((colX sy - sy.SideAdderX.toNat : Nat) : Int))

/-- where his feet get over the base block -/
def feetP (sy : Syms) (m0 : Machine) : Int :=
  256 * (256 * (polePage sy m0 : Int) + ((colX sy - sy.FeetAdderX.toNat : Nat) : Int))

/-- `Beside`, with `Side` read from the routine: left of the side of the block he stays left of it; otherwise the frame runs the collision routine on a
case with the height of the rule for the side -/
def BesideCase (sy : Syms) (m0 : Machine) (Ps : Int) (f : Frame tp am wd) : Prop :=
  (f.P₂ < Ps ∧ f.P' < Ps) ∨ ∃ c ∈ cases sy, Collides sy (withPole sy m0) f c ∧ lowCase sy c = true

/-- `Falling`, with `InBlock` read from the routine, on a case with the moving direction `d` and the height and fall speed of the vertical state `s` -/
def FallingCase (sy : Syms) (m0 : Machine) (Pf : Int) (d : UInt8) (s : Jump.VS) (f : Frame tp am wd) : Prop :=
  (f.P₂ < Pf ∧ f.P' < Pf) ∨
    (Pf ≤ f.P₂ ∧ ∃ c ∈ cases sy, Collides sy (withPole sy m0) f c ∧ inBlockCase sy c = true ∧ c.md = d ∧ c.y = s.y ∧ c.vy = s.vy)

/-- After a push to the right, the next frame's speed comes from `hstep` in the air, from speed 0, with the Left button blocked. -/
def MaskStep (sy : Syms) (m0 : Machine) (f g : Frame tp am wd) : Prop :=
  f.P' = f.P₂ + 256 → ∃ (s : HS) (i : HIn), s.v = 0 ∧ s.f ∈ bytes ∧ s.fd ∈ facings ∧ s.md ∈ ([0, 1, 2, 3] : List UInt8) ∧
    s.rs ∈ rsVals sy ∧ i ∈ inputsN ∧ i.st = 1 ∧ i.jump = false ∧
    g.v₂ = sbyte (hstep sy (poke m0 sy.Player_CollisionBits sy.noLeft) s i).v

theorem maskL_of_step (hm : maskCheck sy m0 = true) {f g : Frame tp am wd} (h : MaskStep sy m0 f g) : MaskL f g := by
  intro hp
  obtain ⟨s, i, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h hp
  simp only [maskCheck, List.all_eq_true, decide_eq_true_eq, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hm
  have h10 := hm s.f h2 s.fd h3 s.md h4 s.rs h5 i ⟨h6, h7, h8⟩
  have h11 : ({ v := 0, f := s.f, fd := s.fd, md := s.md, rs := s.rs } : HS) = s := by
    cases s
    simp only at h1
    rw [h1]
  rw [h11] at h10
  rw [h9]
  exact h10

/-! ### The stored speed -/

/-- `TopSpeed.frictionCheck`'s machine after `ImposeFriction` -/
def frictionRun (sy : Syms) (m0 : Machine) (v fr lo hi mr ml a cb : UInt8) : Machine :=
  let m := poke m0 sy.Player_X_Speed v
  let m := poke m sy.Player_X_MoveForce fr
  let m := poke m sy.FrictionAdderLow lo
  let m := poke m sy.FrictionAdderHigh hi
  let m := poke m sy.MaximumRightSpeed mr
  let m := poke m sy.MaximumLeftSpeed ml
  let m := poke m sy.Player_CollisionBits cb
  runSub m sy.ImposeFriction a 0 0

/-! ### The fall -/

section Fall

open Jump (VS vstep falling groundY standY arcStart forces)
open PoleGrab (topY)

/-- falling with the feet inside the rows of the base block -/
def insideRows (sy : Syms) (s : VS) : Bool :=
  falling s && decide (topY sy + sy.LandDepth.toNat ≤ s.y.toNat + sy.FeetAdderY.toNat) && decide (s.y.toNat + sy.FeetAdderY.toNat < topY sy + 16)

/-- the next frames of a fall, without a block: with A pressed or not while he rises (falling, the routine does not read A). It ends at the ground; a height past the
ground by more than a frame's fall is above the screen. -/
def fallNext (sy : Syms) (m : Machine) (s : VS) : List VS :=
  if falling s then
    if decide (groundY sy ≤ s.y.toNat) && decide (s.y.toNat < groundY sy + 8) then [] else [vstep sy m s false 0]
  else [vstep sy m s true 0, vstep sy m s false 0]

/-- a vertical state, and the frames in a row with the feet inside the rows -/
abbrev FallS := VS × Nat

def fallSucc (sy : Syms) (m : Machine) (x : FallS) : List FallS :=
  (fallNext sy m x.1).map fun t => (t, if insideRows sy t then x.2 + 1 else 0)

/-- stepping off a block `r` rows up: the fall force left from the last jump, and any carried fraction -/
def stepOffs (sy : Syms) (m : Machine) (r : Nat) : List VS :=
  (forces sy m).flatMap fun f => bytes.map fun d =>
    { y := (standY sy r).toUInt8, mf := 0, vy := 0, dummy := d, vf := f, vfd := f, origin := 0, st := 2, prevA := false }

/-- where a fall begins: a jump from the ground or from a block up to `rows` rows up; stepping off a block from 2 to `rows` rows up -/
def fallStarts (sy : Syms) (m : Machine) (rows : Nat) : List VS :=
  ((List.range (rows + 1)).flatMap fun r => (arcStart sy m (standY sy r) 1).map (·.s)) ++
    (List.range (rows - 1)).flatMap fun r => stepOffs sy m (r + 2)

/-- every frame of every fall: at most 3 frames in a row inside the rows; after `r` frames every fall is over -/
def fallLayers (sy : Syms) (m : Machine) : Nat → List FallS → Bool
  | 0, L => L.isEmpty
  | r + 1, L => L.all (fun x => decide (x.2 ≤ 3)) && fallLayers sy m r (Cert.nextS (fallSucc sy m) L)

/-- how many frames a fall can last, more than any fall takes -/
def fallFrames : Nat := 120

def fallCheck (sy : Syms) (m : Machine) (rows : Nat) : Bool :=
  fallLayers sy m fallFrames ((fallStarts sy m rows).map fun s => (s, if insideRows sy s then 1 else 0))

theorem fallLayers_spec {sy : Syms} {m : Machine} :
    ∀ (r : Nat) (L : List FallS), fallLayers sy m r L = true → ∀ (u : Nat → VS) (w n c e0 : Nat), (u w, c) ∈ L →
      (∀ e, e0 ≤ e → e ≤ w → (∀ i, e ≤ i → i ≤ w → insideRows sy (u i) = true) → w + 1 ≤ e + c) →
      (∀ j, w ≤ j → j < w + n → u (j + 1) ∈ fallNext sy m (u j)) →
      ∀ e, e0 ≤ e → e ≤ w + n → (∀ i, e ≤ i → i ≤ w + n → insideRows sy (u i) = true) → w + n + 1 ≤ e + 3
  | 0, L, h, _, _, _, c, _, hm, _, _, _, _, _, _ => by
    simp only [fallLayers, List.isEmpty_iff] at h
    rw [h] at hm
    simp at hm
  | r + 1, L, h, u, w, n, c, e0, hm, hinv, hp, e, he0, he, hin => by
    simp only [fallLayers, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have hc := h.1 _ hm
    simp only at hc
    cases n with
    | zero =>
      have := hinv e he0 (by omega) (fun i h1 h2 => hin i h1 (by omega))
      omega
    | succ n =>
      have hu := hp w (Nat.le_refl _) (by omega)
      have hnext : (u (w + 1), if insideRows sy (u (w + 1)) then c + 1 else 0) ∈ Cert.nextS (fallSucc sy m) L :=
        Cert.mem_nextS _ L hm (List.mem_map.2 ⟨_, hu, rfl⟩)
      have hinv' : ∀ e', e0 ≤ e' → e' ≤ w + 1 → (∀ i, e' ≤ i → i ≤ w + 1 → insideRows sy (u i) = true) →
          w + 1 + 1 ≤ e' + (if insideRows sy (u (w + 1)) then c + 1 else 0) := by
        intro e' h1 h2 h3
        rw [if_pos (h3 (w + 1) h2 (Nat.le_refl _))]
        by_cases h5 : e' = w + 1
        · omega
        · have := hinv e' h1 (by omega) (fun i h6 h7 => h3 i h6 (by omega))
          omega
      have := fallLayers_spec r _ h.2 u (w + 1) n _ e0 hnext hinv' (fun j h1 h2 => hp j (by omega) (by omega)) e he0 (by omega)
        (fun i h1 h2 => hin i h1 (by omega))
      omega

/-- A fall from one of the starts has at most 3 frames in a row inside the rows. -/
theorem fall_rows {sy : Syms} {m : Machine} {rows : Nat} (hc : fallCheck sy m rows = true) {u : Nat → VS} {w L e : Nat} (hs : u w ∈ fallStarts sy m rows)
    (hp : ∀ j, w ≤ j → j + 1 < L → u (j + 1) ∈ fallNext sy m (u j)) (hwe : w ≤ e) (heL : e < L)
    (hin : ∀ i, e ≤ i → i < L → insideRows sy (u i) = true) : L ≤ e + 3 := by
  have h := fallLayers_spec fallFrames _ hc u w (L - 1 - w) (if insideRows sy (u w) then 1 else 0) w
    (List.mem_map.2 ⟨u w, hs, rfl⟩) (fun e' h1 h2 h3 => by
      have h4 : e' = w := by omega
      subst h4
      rw [if_pos (h3 e' (Nat.le_refl _) (Nat.le_refl _))]
      omega)
    (fun j h1 h2 => hp j h1 (by omega)) e hwe (by omega) (fun i h1 h2 => hin i h1 (by omega))
  omega

end Fall

/-- What a real run has per frame, besides `Frame`. -/
structure Track where
  /-- the stored speed after frame `j` -/
  abs : Nat → Nat
  /-- the moving direction after frame `j`: that of frame `j`'s collision (`AfterKeep.keepH`) -/
  md : Nat → UInt8
  /-- the vertical state at frame `j`'s collision, in the model of `fallNext` -/
  u : Nat → Jump.VS

/-- **The track of a real run**: the stored speed and the moving direction at the end of the counted frame `j` (`seq j`), read from the machines; only the vertical
state `u` is given -/
def trackOf (sy : Syms) {m0 : Machine} {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (_K : FrameKeep.Frames sy m0 S a g seq) (u : Nat → Jump.VS) : Track :=
  { abs := fun j => (peek (seq j) sy.Player_XSpeedAbsolute).toNat, md := fun j => peek (seq j) sy.Player_MovingDir, u }

/-- `Approach`, with the rules read from the routines -/
structure ApproachCases (sy : Syms) (m0 : Machine) (rows : Nat) (fr : Nat → Frame tp am wd) (t q L T g : Nat) (fast : Bool) (tk : Track) : Prop where
  order : q < L ∧ L < T
  /-- left of where the feet get over the block -/
  left : (fr q).P' < feetP sy m0
  /-- from there to the landing he falls below the block's top -/
  air : ∀ j, q < j → j < L → FallingCase sy m0 (feetP sy m0) (tk.md j) (tk.u j) (fr j)
  /-- a push to the right blocks the Left button on the landing's frame -/
  mask : MaskStep sy m0 (fr (L - 1)) (fr L)
  /-- the landing on the ground -/
  land : BesideCase sy m0 (sideP sy m0) (fr L)
  /-- on the ground and rising, until the grab -/
  hop : ∀ j, L < j → j < g → BesideCase sy m0 (sideP sy m0) (fr j)
  /-- a fast jump reads the stored speed of the frame before it. This is the only link from the class of the model's jump to the machines. The old fields
  `stopped`, `onGround` and `ground` are gone: every frame writes `|v₂|` into the stored speed or keeps it (`Run.stop_step`, `Run.stored_step`), and both cases
  are closed (`approach_of_cases`). -/
  reads : fast = true → sy.AirFastSpeed.toNat ≤ tk.abs (T - 1)
  /-- a slow jump: the fall began on a frame `w`, by a jump or by stepping off a block (`fallStarts`), and followed `fallNext`: no block above stopped it. If he stepped off a
  block one row up, it was the base: he stood with his feet over it on the frame before -/
  fall : fast = false → ∃ w, w ≤ q ∧ (∀ j, w ≤ j → j + 1 < L → tk.u (j + 1) ∈ fallNext sy m0 (tk.u j)) ∧
    (tk.u w ∈ fallStarts sy m0 rows ∨ (tk.u w ∈ stepOffs sy m0 1 ∧ 2 ≤ w ∧ feetP sy m0 ≤ (fr (w - 1)).P₂))

/-- the numbers of the case `c` are in the ranges of the proof -/
def domainOk (sy : Syms) : Bool :=
  decide (sy.LandDepth.toNat ≤ 16) && decide (13 ≤ sy.AirFastSpeed.toNat) && (caseXs sy).all fun x =>
    decide (1 ≤ x.toNat) && decide (x.toNat < 255) && decide (colX sy ≤ x.toNat + sy.SideAdderX.toNat)

theorem beside_of_case (hp : poleCheck sy m0 = true) (hd : domainOk sy = true) {Ps : Int} {f : Frame tp am wd}
    (h : BesideCase sy m0 Ps f) : Beside Ps f := by
  rcases h with h | ⟨c, hc, hC, hl⟩
  · exact Or.inr h
  · simp only [domainOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
    simp only [poleCheck, List.all_eq_true] at hp
    obtain ⟨h1, _, h6⟩ := mem_cases hc
    obtain ⟨⟨h2, _⟩, h3⟩ := hd.2 c.x h1
    have h4 := hC.v₂
    exact Or.inl ⟨side_of_rule (hp c hc) hl (by simpa [sideCase] using h3) h2 hd.1.1 hC, by omega⟩

theorem falling_of_case (hp : poleCheck sy m0 = true) (hd : domainOk sy = true) {Pf : Int} {d : UInt8} {s : Jump.VS} {f : Frame tp am wd}
    (h : FallingCase sy m0 Pf d s f) : Falling Pf f := by
  rcases h with h | ⟨h0, c, hc, hC, hl, _⟩
  · exact Or.inl h
  · simp only [domainOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
    simp only [poleCheck, List.all_eq_true] at hp
    obtain ⟨h1, h4, h6⟩ := mem_cases hc
    obtain ⟨⟨h2, h5⟩, _⟩ := hd.2 c.x h1
    have h7 := hC.v₂
    exact Or.inr ⟨h0, inBlock_of_rule (hp c hc) hl h4 h2 h5 hC, by omega⟩

/-- `FastLink` from the cases, with `htake`: the stored speed at the landing's end is at the air threshold or more; and `hstop`: a frame from a stopped Mario
writes `|v₂|` into the stored speed, or keeps the stored speed and the moving direction (`Run.stop_step` on a real run) -/
theorem fastLink_of_cases (hp : poleCheck sy m0 = true) (hd : domainOk sy = true)
    {rows : Nat} {fr : Nat → Frame tp am wd} {t q L T g : Nat} {tk : Track} (A : ApproachCases sy m0 rows fr t q L T g true tk)
    (htake : sy.AirFastSpeed.toNat ≤ tk.abs L)
    (hstop : ∀ j, q < j → j ≤ L → (fr j).v = 0 → tk.abs j = (fr j).v₂.natAbs ∨ (tk.abs j = tk.abs (j - 1) ∧ tk.md j = tk.md (j - 1))) :
    FastLink fr (feetP sy m0) q L sy.AirFastSpeed.toNat tk.abs (fun j => tk.md j == 1) := by
  have hrule : ∀ j, q < j → j < L → feetP sy m0 ≤ (fr j).P₂ →
      ∃ c ∈ cases sy, Collides sy (withPole sy m0) (fr j) c ∧ inBlockCase sy c = true ∧ c.md = tk.md j := by
    intro j h1 h2 h3
    rcases A.air j h1 h2 with ⟨h4, _⟩ | ⟨_, c, hc, hC, hl, hm, _⟩
    · omega
    · exact ⟨c, hc, hC, hl, hm⟩
  refine ⟨htake, ?_, ?_, ?_⟩
  · intro j h1 h2 h3
    rcases hstop j h1 h2 h3 with h4 | ⟨h4, h5⟩
    · exact Or.inl h4
    · exact Or.inr ⟨h4, by simp only [h5]⟩
  · intro j h1 h2 h3 h4
    obtain ⟨c, hc, hC, _, hm⟩ := hrule j h1 h2 h3
    rw [← hm, md_of_right (mem_cases hc).2.1 hC h4]
    rfl
  · intro j h1 h2 h3 h4
    obtain ⟨c, hc, hC, hl, hm⟩ := hrule j h1 h2 h3
    simp only [domainOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
    simp only [poleCheck, List.all_eq_true] at hp
    have h5 : c.md = 1 := by
      rw [hm]
      simpa using h4
    exact push_of_rule (hp c hc) hl h5 (hd.2 c.x (mem_cases hc).1).1.1 hC

theorem rows_of_cases {rows : Nat} (hr : fallCheck sy m0 rows = true) {fr : Nat → Frame tp am wd} {t q L T g : Nat} {tk : Track}
    (A : ApproachCases sy m0 rows fr t q L T g false tk)
    (hbase : ∀ w, 2 ≤ w → w ≤ q → feetP sy m0 ≤ (fr (w - 1)).P₂ → t + 1 ≤ w)
    (e : Nat) (hqe : q < e) (heL : e < L) (het : e ≤ t + 1) (hin : ∀ i, e ≤ i → i < L → feetP sy m0 ≤ (fr i).P₂) : L ≤ e + 3 := by
  obtain ⟨w, hw, hp, hs⟩ := A.fall rfl
  rcases hs with hs | ⟨_, h2, h3⟩
  · refine fall_rows hr hs hp (by omega) heL fun i h1 h2 => ?_
    rcases A.air i (by omega) h2 with ⟨h4, _⟩ | ⟨_, c, _, _, hl, _, hy, hvy⟩
    · have := hin i h1 h2
      omega
    · simp only [inBlockCase, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨⟨⟨h4, h5⟩, h6⟩, _⟩ := hl
      simp only [insideRows, Jump.falling, Bool.and_eq_true, decide_eq_true_eq]
      rw [← hy, ← hvy]
      refine ⟨⟨?_, h5⟩, h6⟩
      simp only [sbyte] at h4
      by_cases h7 : c.vy < 0x80
      · simpa using h7
      · rw [if_neg h7] at h4
        have := c.vy.toNat_lt
        omega
  · have := hbase w h2 hw h3
    omega

/-- `Approach` from the cases. `hstop` and `hkeep` are the stored speed of the real frames (`Run.stop_step`, `Run.stored_step`): a frame from a stopped Mario
writes `|v₂|` into the stored speed or keeps the stored speed and the moving direction, and every frame writes `|v₂|` or keeps the stored speed.

A fast jump reads a stored speed at the air threshold or more (`reads`). Going back from the takeoff to the landing, each frame wrote it or kept it. So either a frame
after the landing wrote it, with `|v₂|` at the threshold or more; or no frame did, and the stored speed at the landing's end is at the threshold or more (`FastLink`).
The frame before the takeoff need not start on the ground: the old field `ground` is gone. -/
theorem approach_of_cases (hp : poleCheck sy m0 = true) (hm : maskCheck sy m0 = true) (hd : domainOk sy = true)
    {rows : Nat} (hr : fallCheck sy m0 rows = true)
    {fr : Nat → Frame tp am wd} {t q L T g : Nat} {fast : Bool} {tk : Track} (A : ApproachCases sy m0 rows fr t q L T g fast tk)
    (hbase : ∀ w, 2 ≤ w → w ≤ q → feetP sy m0 ≤ (fr (w - 1)).P₂ → t + 1 ≤ w)
    (hstop : fast = true → ∀ j, q < j → j ≤ L → (fr j).v = 0 →
      tk.abs j = (fr j).v₂.natAbs ∨ (tk.abs j = tk.abs (j - 1) ∧ tk.md j = tk.md (j - 1)))
    (hkeep : fast = true → ∀ j, L < j → j < T → tk.abs j = (fr j).v₂.natAbs ∨ tk.abs j = tk.abs (j - 1)) :
    Approach fr (sideP sy m0) (feetP sy m0) t q L T g fast := by
  have hair : (13 : Nat) ≤ sy.AirFastSpeed.toNat := by
    simp only [domainOk, Bool.and_eq_true, decide_eq_true_eq] at hd
    exact hd.1.2
  refine ⟨A.order, A.left, fun j h1 h2 => falling_of_case hp hd (A.air j h1 h2), maskL_of_step hm A.mask,
    beside_of_case hp hd A.land, fun j h1 h2 => beside_of_case hp hd (A.hop j h1 h2), ?_, ?_⟩
  · intro h1
    subst h1
    have hLT := A.order.2
    -- going back from the takeoff: the stored speed is still at the threshold or more, or a frame wrote it
    have hback : ∀ d, L + d < T → sy.AirFastSpeed.toNat ≤ tk.abs (T - 1 - d) ∨
        ∃ j, L < j ∧ j < T ∧ sy.AirFastSpeed.toNat ≤ (fr j).v₂.natAbs := by
      intro d
      induction d with
      | zero => exact fun _ => Or.inl (A.reads rfl)
      | succ d ih =>
        intro h
        rcases ih (by omega) with h1 | h1
        · rcases hkeep rfl (T - 1 - d) (by omega) (by omega) with h2 | h2
          · exact Or.inr ⟨T - 1 - d, by omega, by omega, by omega⟩
          · left
            rw [show T - 1 - (d + 1) = T - 1 - d - 1 by omega]
            omega
        · exact Or.inr h1
    rcases hback (T - 1 - L) (by omega) with h1 | ⟨j, h1, h2, h3⟩
    · rw [show T - 1 - (T - 1 - L) = L by omega] at h1
      exact Or.inl ⟨_, _, _, hair, fastLink_of_cases hp hd A h1 (hstop rfl)⟩
    · exact Or.inr ⟨j, h1, h2, by omega⟩
  · intro h1
    subst h1
    exact rows_of_cases hr A hbase

/-! ### The jump -/

/-- The vertical state of the frames `T .. g` is a path of `Jump.arcSucc` from a takeoff off the ground. -/
structure JumpPath (sy : Syms) (m0 : Machine) (T g : Nat) (a : Nat → Jump.Arc) : Prop where
  before : T ≤ g
  start : a T ∈ Jump.arcStart sy m0 (Jump.groundY sy) 1
  step : ∀ j, T ≤ j → j < g → a (j + 1) ∈ Jump.arcSucc sy m0 1 (a j)
  short : g ≤ T + Jump.arcFrames

theorem path_reach {T g : Nat} {a : Nat → Jump.Arc} (P : JumpPath sy m0 T g a) :
    ∀ n j, j + n = g → T ≤ j → Cert.Reach (Jump.arcSucc sy m0 1) (a j) n (a g)
  | 0, j, h, _ => by
    have : j = g := by omega
    rw [this]
    exact Cert.Reach.refl _
  | n + 1, j, h, h2 => Cert.Reach.step (P.step j h2 (by omega)) (path_reach P n (j + 1) (by omega) (by omega))

/-- Rising at the height of a direct grab comes only on the frame of `Jump.jump_grab`. -/
theorem grab_frame (hj : Jump.arcCheck sy m0 (Jump.groundY sy) 1 (Jump.riseOk sy 1 2 1) = true) {T g : Nat} {a : Nat → Jump.Arc}
    (P : JumpPath sy m0 T g a) (hr : Jump.falling (a g).s = false) (h1 : sy.FlagGrabY.toNat ≤ (a g).s.y.toNat)
    (h2 : (a g).s.y.toNat < Jump.cornerY sy 1) : g = T + (if (a T).fast then 1 else 2) := by
  have hR := path_reach P (g - T) T (by have := P.before; omega) (Nat.le_refl _)
  have h3 := Jump.arc_spec hj (a T) P.start (g - T) (a g) (by have := P.short; omega) hR
  obtain ⟨h4, h5⟩ := Jump.arc_k hR
  have h6 := Jump.arcStart_k P.start
  simp only [Jump.riseOk, hr, h1, h2, Bool.or_eq_true, Bool.false_eq_true, false_or, Bool.not_eq_true', decide_true,
    Bool.and_true, Bool.true_eq_false, beq_iff_eq, h5] at h3
  have := P.before
  omega

/-! ### The touch and the castle -/

/-- The castle flag of the real run after the touch `g` is the flag of the machine `E` of `CastleWalk`, frame by frame, for `n` frames, up to the castle entry `c`. -/
def FollowsTouch (sy : Syms) (flag : Nat → Bool) (g c : Nat) (E : Machine) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → g + k ≤ c → flag (g + k) = castle sy (run E (zeros k))

theorem castle_after {flag : Nat → Bool} {g c n : Nat} {E : Machine}
    (hE : ∀ k, 1 ≤ k → k ≤ n → castle sy (run E (zeros k)) = false) (H : FollowsTouch sy flag g c E n)
    (hc : flag c = true) (hgc : g < c) : g + n + 1 ≤ c := by
  by_cases h : c ≤ g + n
  · exfalso
    have h1 := H (c - g) (by omega) (by omega) (by omega)
    rw [show g + (c - g) = c by omega, hc, hE _ (by omega) (by omega)] at h1
    exact Bool.noConfusion h1
  · omega

/-- the fraction of a position, as the byte `CastleWalk.atPole` writes -/
def fracOf (P : Int) : UInt8 := (P % 256).toNat.toUInt8

/-- a fraction that is a multiple of 1/16 px is one of `CastleWalk.fracs` -/
theorem fracOf_mem {P : Int} (h : P % 16 = 0) : fracOf P ∈ fracs := by
  obtain ⟨k, hk, hr⟩ : ∃ k : Nat, k < 16 ∧ P % 256 = 16 * (k : Int) :=
    ⟨((P % 256) / 16).toNat, by omega, by omega⟩
  have e : fracOf P = (16 * k).toUInt8 := by
    unfold fracOf
    rw [hr]
    rfl
  rw [e]
  have : ∀ i : Fin 16, (16 * i.val).toUInt8 ∈ fracs := by decide
  exact this ⟨k, hk⟩

/-- for `n` frames after the touch, up to the castle entry `c`, a direct grab behaves as a checked direct grab: with the touch's own fraction `u`
(`CastleWalk.Statement.anyFraction`), or `otherStates` -/
def DirectFlag (sy : Syms) (b : Machine) (vs : List Jump.VS) (flag : Nat → Bool) (g c n : Nat) (u : UInt8) : Prop :=
  FollowsTouch sy flag g c (touchAt sy b (firstX sy) u (vs.headD default)) n ∨
    ∃ s ∈ vs, ∃ x ∈ grabXs sy, FollowsTouch sy flag g c (touchAt sy b x bigFrac s) n

/-- for `n` frames after the touch, up to the castle entry `c`, any other touch behaves as a checked touch at another height: `CastleWalk.Statement.otherTouch` -/
def OtherFlag (sy : Syms) (b : Machine) (vs : List Jump.VS) (flag : Nat → Bool) (g c n : Nat) : Prop :=
  ∃ y ∈ otherYs sy, FollowsTouch sy flag g c
    (touchAt sy b (colX sy - 9).toUInt8 bigFrac { (vs.headD default) with y := y + 3 }) n

theorem castle_of_direct {b : Machine} {vs : List Jump.VS} {Nc lo : Nat} (C : CastleWalk.Statement sy b vs Nc lo)
    {flag : Nat → Bool} {g c n : Nat} {u : UInt8} (hu : u ∈ fracs) (hn : n + 1 ≤ Nc) (H : DirectFlag sy b vs flag g c n u) (hc : flag c = true) (hgc : g < c) :
    g + n + 1 ≤ c := by
  rcases H with H | ⟨s, hs, x, hx, H⟩
  · exact castle_after (fun k h1 h2 => C.anyFraction u hu k h1 (by omega)) H hc hgc
  · exact castle_after (fun k h1 h2 => by
      rw [C.otherStates s hs x hx k h1 (by omega)]
      simp
      omega) H hc hgc

theorem castle_of_other {b : Machine} {vs : List Jump.VS} {Nc lo : Nat} (C : CastleWalk.Statement sy b vs Nc lo)
    {flag : Nat → Bool} {g c n : Nat} (hn : n + 1 ≤ lo) (H : OtherFlag sy b vs flag g c n) (hc : flag c = true) (hgc : g < c) :
    g + n + 1 ≤ c := by
  obtain ⟨y, hy, H⟩ := H
  exact castle_after (fun k h1 h2 => C.otherTouch y hy k h1 (by omega)) H hc hgc

/-! ### A real run -/

/-- Rising, at the height of a direct grab -/
def IsDirect (sy : Syms) (y : UInt8) (rising : Bool) : Prop :=
  rising = true ∧ sy.FlagGrabY.toNat ≤ y.toNat ∧ y.toNat < Jump.cornerY sy 1

/-- What a direct grab on frame `g` gives: the jump, the frames before it, and the castle flag after it. -/
structure DirectWay (sy : Syms) (m0 b : Machine) (vs : List Jump.VS) (rows : Nat) (fr : Nat → Frame tp am wd) (flag : Nat → Bool)
    (t Nc : Nat) (F : Int) (g c : Nat) (y : UInt8) (rising : Bool) (q L T : Nat) (a : Nat → Jump.Arc) (tk : Track) : Prop where
  one_le : 1 ≤ q
  path : JumpPath sy m0 T g a
  atY : (a g).s.y = y
  atRising : Jump.falling (a g).s = !rising
  /-- the frames before the grab, needed for a fast jump at any time and for a slow jump up to frame `t + 8` -/
  approach : ((a T).fast = true ∨ g ≤ t + 8) → ApproachCases sy m0 rows fr t q L T g (a T).fast tk
  /-- a slow jump's grab: no castle before `Nc − 1` frames after it. The checked touch has the fraction of `P₂(g)`. Only the frames up to the castle entry `c` are asked. -/
  flagAny : (a T).fast = false → DirectFlag sy b vs flag g c (Nc - 2) (fracOf (fr g).P₂)
  /-- a slow jump's grab, moving left on the frame before it, with the fraction below `F`: no castle before `Nc` frames after it -/
  flagTight : (a T).fast = false → (fr (g - 1)).v₂ < 0 → (fr g).P₂ < SurfaceRun.poleP sy m0 + F → DirectFlag sy b vs flag g c (Nc - 1) (fracOf (fr g).P₂)

/-- the castle flag of the machines, frame by frame -/
def flagOf (sy : Syms) (seq : Nat → Machine) (j : Nat) : Bool := castle sy (seq j)

/-- **The area parser's column**, 16 columns a page, from its two bytes (`FrameKeep.parE`, round 29): it is `PoleParser.colOf` (`PoleParserRun.parCol_eq`) -/
def parColOf (sy : Syms) (m0 : Machine) (m : Machine) : Nat :=
  (peek m (FrameKeep.romWE m0 (FrameKeep.parRt sy m0 + 0x0E))).toNat * 16 + (peek m (FrameKeep.romWE m0 (FrameKeep.parRt sy m0 + 1))).toNat

/-- **The scroll counter of 32 px** (`FrameKeep.parE`, round 29) -/
def parSOf (sy : Syms) (m0 : Machine) (m : Machine) : Nat := (peek m (FrameKeep.romWE m0 (sy.UpdScrollVar + 13))).toNat

/-- **The screen buffers' control byte** (round 31): the operand of the first load of `UpdScrollVar` (`PoleParser.places`) -/
def parCtlOf (sy : Syms) (m0 : Machine) (m : Machine) : UInt8 := peek m (FrameKeep.romWE m0 (sy.UpdScrollVar + 1))

/-- **The area parser's tasks left** (round 32): the operand of the load of the task count in `UpdScrollVar` (`PoleParser.places`) -/
def parNOf (sy : Syms) (m0 : Machine) (m : Machine) : Nat := (peek m (FrameKeep.romWE m0 (sy.UpdScrollVar + 8))).toNat

/-- **No wrap of the scroll counter** from the frame's start `m` to `UpdScrollVar` (`u`), round 29: if the screen's left edge moved by `Y`, the counter of 32 px plus `Y` is
below 256. With the edge below 65,280 − 384 px it gives `PoleParser.NoWrap` (`PoleParserRun.noWrap_of`). -/
def NoWrapP (sy : Syms) (m0 : Machine) (m u : Machine) : Prop :=
  ∀ Y : UInt8, ScrollRule.left16 (ScrollRule.places sy m0) u = (ScrollRule.left16 (ScrollRule.places sy m0) m + Y.toNat) % 65536 → parSOf sy m0 m + Y.toNat < 256

/-- What a real run gives, with frames counted from control above ground: `fr j` is frame `j` after control (`fr 1` the first frame), read from the machines `seq`: `seq j` is the machine at the end
of the counted frame `j`, so `seq 0` is the machine at control. `seq` is not a field: it is the real run `S` at the end of the `j`-th frame from frame `a` on that ends not paused,
on every frame, before the touch and after it (`Run.seq`, `FrameKeep.Keep.seq`). `g` is the frame he touches the pole, `c` the frame of the castle entry. The castle flag is read from the machines (`flagOf`). On frame `g` only the
fields of `fr g` up to `P₂` are the real frame's: the touch moves him, and that is not a `Frame`. `B.m` is the machine of the private proof at control. Every field is a hypothesis of the theorem:
none is proved here. What the machine at control is, is not a field: it comes from the rows of the change (`SurfaceFrames.Start`). That he is in the pole's range at the touch is a theorem from `touches`, `posKeep`, `keepB`, `bufAll`, `tilesCol`, `edge` and `keep`, with the map and the two bytes at control (`PoleTileCtl.colMap₀`, `PoleTileCtl.watch₀`), by the walk of the whole frame of the touch (`PoleFrame`, `PoleTileWalk`, `PoleTileRead`, `PoleTileHeight`, `PoleTileFar`, `PoleTileKeep`, `Run.inRange`); that `P₂(g)` is the position at the end of the move is a theorem too (`Run.moved`, by `SubsOnce`).
That the fraction of `P₂(g)` is a multiple of 1/16 px is a theorem from `keep`, the walk of one whole frame in control (`FrameKeep`), and the check on the ROM (`Run.frac`). That no machine up to the touch
has the castle flag is a theorem from the machine at control, `keep` and the check (`Run.noCastle_of`); so the castle entry is after the touch (`Run.afterTouch`).
The frames up to the touch are those of the real run `S` from frame `a` on (`keep`), so the machine at control is `S.seq a` (`Run.seq0`). -/
structure Run (sy : Syms) (m0 b : Machine) (vs : List Jump.VS) (B : Box) (T J Nc : Nat) (F : Int) (S : FrameKeep.RealRun) (a : Nat) where
  g : Nat
  c : Nat
  touchY : UInt8
  touchRising : Bool
  one_le : 1 ≤ g
  /-- the frames up to the touch on the real machine, counted or not, as the walk of one whole frame in control needs them: the frames of `S` from frame `a` on; a frame is
  counted when it ends with the game not paused, and the counted frame `j` ends at `keep.seq j`, by definition; no frame before the touch's frame writes the routine, the mode or the task by its
  address; each instruction meets `FrameKeep.CleanK` of `FrameKeep.guardE` (`cleanE`: no store through an index or a pointer writes the protected
  bytes, among them those of the old field `spareE` of `frames`). That each frame starts in the idle loop in control, that the frames before the touch's frame end
  in control, and that the `lag` frames keep the castle flag and the fraction's low 4 bits, are theorems (`FrameKeep.Frames.all_start`, `FrameKeep.Frames.ctlAll`,
  `FrameKeep.Frames.start`, on `keep.toFrames`). -/
  keep : FrameKeep.Keep sy m0 S a g
  /-- the frames: they are the frames of `keep`, read from the machines (`Run.fr`, `SurfaceFrames.frOf`); each one from a clean state follows `hstep`, up to a hit; the ones
  before `J` run the collision routine as on the machine at control -/
  frames : SurfaceFrames.OnFrames sy m0 B T J g keep.seq keep.toFrames
  /-- frame `g` of `keep` is a touch on real machines -/
  touches : PoleEntryRule.Touches sy (keep.fm g) (keep.pad g)
  /-- each instruction of each frame up to the touch's frame, counted or not: a store through an index or a pointer writes a pole's tile into the block buffers
  only in the pole's column. With the map at control (`PoleTileCtl.colMap₀`, from the rows of the change) the map holds at the start of the touch's frame
  (`Run.tilesStart`); the old field `tiles` is a theorem from that, this, `keepB` and `tilesCol` (`PoleTileKeep.no_write_frameZ`).
  Round 26: asked only of a store that `PoleKeepFar.farBuf` does not settle, and of an `STA` through an absolute address and an index or through a pointer
  only when A holds one of the pole's two tiles (`PoleKeepFar.BufV`): not of a store through an absolute address and an index from whose base no index reaches the
  block buffers, nor of a store through the zero page and `X`, nor of an `STA` of another byte (`PoleKeepFar.bufAt_of_V`).
  Round 33 (`1-1/f-6-17-14-PoleSlot.md`): at the same stores, a pole's tile goes into the block buffers only when the area parser's column at the frame's start
  has come to the pole's (`PoleSlot.BufVS`, `PoleSlot.bufC_of_VS`); this replaces the part (`slot`) of `tilesCol`. It is not weaker than the round 26 field: it
  asks more at the stores of a pole's tile. Round 34 (`1-1/f-6-17-16-PoleRing.md`): at those stores, the parser's column of the frame's start has come to the
  pole's, or the store is in the column of the ring of the block buffers that the parser's column has (`PoleRing.BufVM`, `PoleRing.NoTileM`); the rest is proved
  (`PoleRing.noTileC_of_M`, with the parser's column at control less than 32 columns before the pole's, `PoleParserRun.low₀`). It asks less than the round 33
  field (`PoleRing.bufVM_of_VS`) -/
  bufAll : ∀ n, n < FrameKeep.ixOf sy m0 S a keep.top g → ∀ k,
    PoleRing.BufVM (PoleFrame.spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k)
  /-- round 25: each instruction of each frame up to the touch's frame, counted or not: a store through an index or a pointer writes neither of the two bytes that
  `PoleTileKeep` watches, the block objects' offset and the player's number (`PoleTileKeep.KeepB`). With their values at control (`PoleTileCtl.watch₀`) every
  frame keeps them (`PoleTileKeep.frames_keepY`), and the walk of the touch's frame tests each store inside the collision routine against the height
  (`PoleTileKeep.zoneTest`): the old field `yKeep` (inside the collision routine no such store writes the height) is a theorem (`PoleTileKeep.no_write_frameZ`).
  Round 26: asked only of a store that `PoleKeepFar.farStore` does not settle (`PoleKeepFar.KeepR`): not of a store through an absolute address and an index from
  whose base no index reaches either byte, nor of a store through the zero page and `X` (`PoleKeepFar.keepB_of_R`) -/
  keepB : ∀ n, n < FrameKeep.ixOf sy m0 S a keep.top g → ∀ k, PoleKeepFar.KeepR sy m0 (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k)
  /-- round 29 (in place of the old `tilesCol`, which asked `PoleTileFar.TileCol`: right after such a read, at the pole's column, the byte read is not one of the pole's
  tiles): up to the routine's write, right after a read of the side check with the page two or more before the pole's, at the pole's column, if the byte read is one
  of the pole's tiles then the area parser's column of the frame's start had come to the pole's; he is at most 112 px left of the screen's left edge of the frame's
  start; and the read is in the column of his pixel plus less than 16 px, mod 32 (`PoleTileFar.TileSlot`). With the parser's invariant at the start of the touch's
  frame (`PoleParserRun.inv_run`: the parser's column is at most 384 px past the edge) this gives `TileCol` (`PoleParserRun.tilesCol_run`). It is not weaker than the old field: at every such read it also asks the last two parts, where
  the old field asked nothing unless a pole's tile was read. Round 30: the last part (the column of the read) is asked only when his page is exactly two before the
  pole's (`PoleTileFar.tileSlot_of_R`: the round 29 form gives this one; `1-1/f-6-17-11-PoleWrap.md`). Round 33 (`1-1/f-6-17-14-PoleSlot.md`): the first part
  (`slot`) is gone: the walk of the touch's frame proves it from the slot's map, which `bufAll` keeps from control on; and the other two parts are needed only
  where the parser's column of the frame's start has come to the pole's, so the field asks only that it has not, at such a read (`PoleSlot.TileSlotC`). With the
  parser's invariant at the touch's frame (`PoleParserRun.inv_run`) the round 30 parts give it (`PoleSlot.tileSlotC_of_N`): the field asks less than before -/
  tilesCol : ∀ n, PoleEntryRule.WriteStep sy (keep.fm g) (keep.pad g) n → ∀ j, j ≤ n →
    PoleSlot.TileSlotC (PoleFrame.spotsF sy m0) (parColOf sy m0 (keep.fm g)) (PipeEntryRule.trace (keep.fm g) (keep.pad g) j)
  /-- round 31 (in place of the old field `parWrap`, which asked `NoWrapP` there: the scroll counter of 32 px of the frame's start plus the edge's move below 256):
  on each frame before the touch's frame that comes to the player's routine, at each `UpdScrollVar` of it, the screen buffers' control byte is not 6. The code sets
  it to 6 when he takes a coin. With the scroll's amount at most 3 (`PoleParserRun.amount_run`, from part e's reading of each counted frame) and `JV` at control
  (`PoleStrict.jv₀`, from the rows of the change) the frames follow the strict rule and keep
  `JV` (`PoleStrict.invJ_onFrames`), which is what the parser's invariant used the old field for. It is not weaker than the old field: it asks something the old
  field did not ask (`1-1/f-6-17-12-PoleStrict.md`). Round 32 (`1-1/f-6-17-13-PoleLate.md`): asked only when the parser is late there, that is, when the counter
  of 32 px plus 3 times the tasks left is 32 or more: else a frame with the control byte 6 keeps `JV` too (`PoleStrict.step_strict`). Round 33
  (`1-1/f-6-17-15-PoleLag.md`): the frames carry the weaker `PoleLag.JY` (the counter plus 3 times the tasks left below 157), which is all the parser's invariant
  needs, so the field asks the control byte not 6 only where that lag is 157 or more there -/
  ctlU : ∀ n, n + 1 < FrameKeep.ixOf sy m0 S a keep.top g →
    ∀ n₀, (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) n₀).pc = sy.PlayerCtrlRoutine →
      (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) n₀).frame = (S.seq (a + n)).frame →
    ∀ k, (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k).pc = sy.UpdScrollVar →
    (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k).frame = (S.seq (a + n)).frame →
    parCtlOf sy m0 (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k) ≠ 6 ∨
      parSOf sy m0 (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k) + 3 * parNOf sy m0 (PipeEntryRule.trace (S.seq (a + n)) (S.inp (a + n)) k) < 157
  /-- up to the write, a store through an index or a pointer that writes the position's pixel or page is one of the move routine's stores of them, with the index 0 -/
  posKeep : ∀ n, PoleEntryRule.WriteStep sy (keep.fm g) (keep.pad g) n → ∀ j, j ≤ n → PoleFrame.PosKeep sy m0 (PipeEntryRule.trace (keep.fm g) (keep.pad g) j)
  /-- up to the write, the scroll handler's store of the position at the screen's edges does not bring him into the pole's range: if he is in it right after that store
  (`PoleFrame.again`), he was in it at the end of the move -/
  edge : ∀ n, PoleEntryRule.WriteStep sy (keep.fm g) (keep.pad g) n → ∀ j, j ≤ n → (PipeEntryRule.trace (keep.fm g) (keep.pad g) j).pc ∈ PoleFrame.again sy m0 →
    (PoleFrame.spotsF sy m0).left ≤ PoleEntryRule.px (PoleFrame.spotsF sy m0) (PipeEntryRule.trace (keep.fm g) (keep.pad g) j) →
    ∃ k, k ≤ n ∧ (PipeEntryRule.trace (keep.fm g) (keep.pad g) k).pc = sy.PlayerSubs ∧
      (PoleFrame.spotsF sy m0).left ≤ PoleEntryRule.px (PoleFrame.spotsF sy m0) (PipeEntryRule.trace (keep.fm g) (keep.pad g) k)
  /-- `c` frames end not paused by the end of frame `keep.top`: the frames up to the castle entry are counted frames of the run, so `keep.seq j` is the end of the `j`-th
  of them for every `j ≤ c` (`FrameKeep.Keep.up_at`, `FrameKeep.Keep.ends_at`) -/
  toCastle : c ≤ FrameKeep.upTo (FrameKeep.upAt sy m0 S a) keep.top
  /-- the castle entry: the machine at the end of the counted frame `c` has the castle flag -/
  atCastle : castle sy (keep.seq c) = true
  /-- a direct grab -/
  direct : IsDirect sy touchY touchRising →
    ∃ q L T' a u, DirectWay sy m0 b vs B.rows (SurfaceFrames.frOf sy m0 keep.toFrames) (flagOf sy keep.seq) T Nc F g c touchY touchRising q L T' a (trackOf sy keep.toFrames u)
  /-- any other touch: no castle for the frames that could matter, up to the castle entry -/
  other : ¬ IsDirect sy touchY touchRising → OtherFlag sy b vs (flagOf sy keep.seq) g c (Nc + 5)

/-- **The machine at the end of the counted frame `j`**: the real run `S` at the end of the `j`-th frame from frame `a` on that ends not paused (`FrameKeep.Keep.seq`). A definition;
it was the field `seq`, tied to the run only up to the touch (`seqAt`). -/
abbrev Run.seq {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar) :
    Nat → Machine := R.keep.seq

/-- **Frame `j` from control above ground**: read from the machines of `keep` (`SurfaceFrames.frOf`). It was the field `fr`, tied to the machines by the field
`frames.reads`. -/
noncomputable abbrev Run.fr {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar) :
    Nat → Frame (top sy) (amax sy m0) true := SurfaceFrames.frOf sy m0 R.keep.toFrames

/-- **The machine at control is the real run's frame `a`**: by the definition of the frames of `keep` (the old link `Route.Run.atCtl`) -/
theorem Run.seq0 {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar) :
    R.seq 0 = Sr.seq ar :=
  R.keep.seq0

/-- at control he is stopped at the position of the machine `B.m` -/
theorem Run.startP {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) : (R.fr 1).P = posP sy B.m :=
  SurfaceFrames.start_P R.keep.toFrames st

theorem Run.startV {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (st : SurfaceFrames.Start sy B (R.seq 0)) : (R.fr 1).v = 0 :=
  SurfaceFrames.start_v hN R.keep.toFrames st

/-- the fraction of the position at control is a multiple of 1/16 px -/
def fracCheck (sy : Syms) (m : Machine) : Bool := decide (posP sy m % 16 = 0)

/-- the machine at control has the castle flag down and the fraction a multiple of 1/16 px: the watched bits of `FrameKeep` -/
theorem Run.watched₀ {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (h0 : castle sy (R.seq 0) = false) : FrameKeep.Watched (FrameKeep.watchOf sy) (R.seq 0) := by
  have h1 : posP sy B.m % 16 = 0 := by simpa [fracCheck] using hq
  exact FrameKeep.watched_of_parts h0 (by rw [st.P]; exact h1)

/-- **The frames are read from the machines** (the old field `frames.reads`): `SurfaceFrames.OnFrames.reads` on the frames of `keep`, which start in control
(`FrameKeep.Frames.all_start`). `hN` are the numbers of the machine at control, `hfr` the check of the friction, `hk` the walk's check of `FrameKeep`, `hg` that the touch
is not later than `SurfaceFrames.farN` frames after control (a later touch is `SurfaceLate`). -/
theorem Run.reads {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m) : SurfaceFrames.Reads sy R.g R.seq R.fr := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start (R.watched₀ st hq hc0.castle) n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst
  exact R.frames.reads Nm.ctrl Nm.model hfr Nm.idle hst Ar (SurfaceFrames.start_v0 hN st) st.P hg

/-- the frames up to the touch follow each other: they are read from the machines (`Run.reads`) -/
theorem Run.next {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m) :
    ∀ j, 1 ≤ j → j < R.g → Next (R.fr j) (R.fr (j + 1)) :=
  SurfaceFrames.next_of_reads (R.reads hN hfr st hq hk hc0 hg)

/-- **The fraction is a multiple of 1/16 px** on each frame up to the touch: it is one at control (`fracCheck` on the machine `B.m`, `Start.P`), and each frame keeps it: the walk of one
whole frame in control (`FrameKeep.keep_frame`, on the frames of `keep`). `hk` is the walk's check on the ROM. -/
theorem Run.fracP {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) :
    ∀ j, 1 ≤ j → j ≤ R.g → (R.fr j).P % 16 = 0 := by
  have h0 := R.watched₀ st hq hc0.castle
  intro j h1 h2
  rw [SurfaceFrames.frOf_P]
  exact R.keep.toFrames.frac hk hc0.start h0 (j - 1) (by omega)

/-- at the touch, `P₂` too: the move adds `16·v₂` -/
theorem Run.frac {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) :
    (R.fr R.g).P₂ % 16 = 0 := by
  have h1 := R.fracP st hq hk hc0 R.g R.one_le (Nat.le_refl _)
  have h2 := (R.fr R.g).move
  omega

/-- so the checked touch with the fraction of `P₂(g)` is one of `CastleWalk.fracs` -/
theorem Run.frac_mem {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) :
    fracOf (R.fr R.g).P₂ ∈ fracs :=
  fracOf_mem (R.frac st hq hk hc0)

/-- **No castle flag up to the touch**: with the castle flag down at control, the walk keeps it down on every frame up to the touch (`keep`). `hk` is the walk's check on the ROM.
The machine at control (`hc0`: the start of a frame in control, the castle flag down) comes from the rows of the change (`ControlStart.EndRun.atCtl`). The old field `noCastle`. -/
theorem Run.noCastle_of {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) :
    ∀ j, j ≤ R.g → castle sy (R.seq j) = false :=
  R.keep.toFrames.noCastle hk hc0.start (R.watched₀ st hq hc0.castle)

/-- **The castle entry comes after the touch**: up to the touch no machine has the castle flag (`Run.noCastle_of`). `hc0` is the machine at control, `hk` the walk's check on the ROM. -/
theorem Run.afterTouch {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) : R.g < R.c := by
  by_cases h : R.c ≤ R.g
  · have h1 := R.noCastle_of st hq hk hc0 R.c h
    rw [R.atCastle] at h1
    exact absurd h1 (by decide)
  · omega

/-- **`P₂(g)` is the position at the end of the move** (the old field `moved`): `P₂` of the touch's frame is the position at an arrival of the frame at the end of the
move (`SurfaceFrames.OnFrames.touchMove`), and the frame comes there at one instruction at most (`SubsOnce.subs_once`: the two walks of the whole frame, which do not cut
the write of the pole's routine). So at every instruction of the frame at the end of the move the position is `P₂(g)`. The frame starts in control (`FrameKeep.Frames.start`)
and each instruction is `CleanK` (`keep.clean`). `hs` is the check of `SubsOnce` on the ROM; `hN`, `hfr`, `st`, `hq`, `hk`, `hc0`, `hg` are as in `Run.reads`. -/
theorem Run.moved {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (hs : SubsOnce.subsCheck sy m0 = true)
    (R : Run sy m0 b vs B T J Nc F Sr ar) (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0))
    (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m) :
    ∀ j, (PipeEntryRule.trace (R.keep.fm R.g) (R.keep.pad R.g) j).pc = sy.PlayerSubs → (R.fr R.g).P₂ = posP sy (PipeEntryRule.trace (R.keep.fm R.g) (R.keep.pad R.g) j) := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start (R.watched₀ st hq hc0.castle) n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst
  obtain ⟨k, _, hpc, hP, _⟩ := R.frames.touchMove Nm.ctrl Nm.model hfr Nm.idle hst Ar (SurfaceFrames.start_v0 hN st) st.P hg R.one_le
  intro j hj
  have e := SubsOnce.subs_once hs (R.keep.toFrames.start hk hc0.start (R.watched₀ st hq hc0.castle) R.g R.one_le (Nat.le_refl _))
    (R.keep.toFrames.cleanAt R.g R.one_le (Nat.le_refl _)) j k hj hpc
  rw [e]
  exact hP

/-- **A frame from a stopped Mario** (the old field `stopped` of `ApproachCases`): a counted frame before the touch that starts with the speed 0 ends with the stored
speed `|v₂|`, or with the stored speed and the moving direction of the frame before. `StopRead.stop_step` on the frames of `keep`: the walks from the player's routine to
the scroll handler (`StopRead.stored_subs`), and `GuardE.keepHE` from there to the frame's end. `hN`, `hfr`, `st`, `hq`, `hk`, `hc0`, `hg` are as in `Run.reads`. -/
theorem Run.stop_step {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < R.g)
    (h0 : (R.fr j).v = 0) :
    (peek (R.seq j) sy.Player_XSpeedAbsolute).toNat = (R.fr j).v₂.natAbs ∨
      (peek (R.seq j) sy.Player_XSpeedAbsolute = peek (R.seq (j - 1)) sy.Player_XSpeedAbsolute ∧
        peek (R.seq j) sy.Player_MovingDir = peek (R.seq (j - 1)) sy.Player_MovingDir) := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start (R.watched₀ st hq hc0.castle) n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst
  exact StopRead.stop_step Nm.ctrl Nm.model hfr Nm.storedW Nm.idle R.frames hst Ar (SurfaceFrames.start_v0 hN st) st.P hg h1 h3 h0

/-- **A frame writes the stored speed or keeps it**: a counted frame before the touch ends with the stored speed `|v₂|`, or with the stored speed of the frame
before (`StopRead.stored_step` on the frames of `keep`). Nothing is asked of the frame's speed, state or jump. It closes the frames between the landing and a fast
jump (`approach_of_cases`), where the old fields `onGround` and `ground` of `ApproachCases` were asked. The hypotheses are as in `Run.stop_step`. -/
theorem Run.stored_step {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < R.g) :
    (peek (R.seq j) sy.Player_XSpeedAbsolute).toNat = (R.fr j).v₂.natAbs ∨
      peek (R.seq j) sy.Player_XSpeedAbsolute = peek (R.seq (j - 1)) sy.Player_XSpeedAbsolute := by
  have Nm := SurfaceFrames.numbers_of_check hN
  have hst : ∀ n, n < R.keep.toFrames.ix R.g → FrameKeep.StartK sy m0 (R.keep.toFrames.all n) :=
    fun n hn => (R.keep.toFrames.all_start hk hc0.start (R.watched₀ st hq hc0.castle) n hn).1
  have Ar : SurfaceFrames.AreaRun sy m0 R.keep.toFrames (peek B.m sy.AreaType) := R.frames.areaRun Nm st hst
  exact StopRead.stored_step Nm.ctrl Nm.model hfr Nm.storedW Nm.idle R.frames hst Ar (SurfaceFrames.start_v0 hN st) st.P hg h1 h3

/-- **The map and the two bytes at the start of the touch's frame**: the map and the two bytes at control (`hmap`: `PoleTileCtl.colMap₀`, `hwb`:
`PoleTileCtl.watch₀`), and every frame before the touch's frame keeps them (`bufAll`, `keepB`, the walk of the frames with the test `okSK` and the two bytes
watched: `PoleTileKeep.frames_keepY`) -/
theorem Run.tilesStart {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) :
    PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.keep.fm R.g) ∧ FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.keep.fm R.g) := by
  have h1 := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact PoleTileKeep.frames_keepY hk (PoleTileKeep.keepY_of_Z hc) R.keep.toFrames hc0.start (R.watched₀ st hq hc0.castle) hwb hmap
    (fun n hn k => PoleKeepFar.keepB_of_R (R.keepB n (by omega) k)) (fun n hn k => PoleRing.bufAt_of_VM (R.bufAll n (by omega) k)) (R.keep.toFrames.ix R.g - 1) (by omega)

/-- the touch's frame meets `KeepB` on each instruction: `keepB` on its frame, with `PoleKeepFar.keepB_of_R` -/
theorem Run.keepB₁ {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (j : Nat) : PoleTileKeep.KeepB sy m0 (PipeEntryRule.trace (R.keep.fm R.g) (R.keep.pad R.g) j) := by
  have b := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact PoleKeepFar.keepB_of_R (R.keepB (R.keep.toFrames.ix R.g - 1) (by omega) j)

/-- the touch's frame meets `BufAt` on each instruction: `bufAll` on its frame, with `PoleRing.bufAt_of_VM` -/
theorem Run.bufAt₁ {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (j : Nat) : PoleTileWalk.BufAt (PoleFrame.spotsF sy m0) (PipeEntryRule.trace (R.keep.fm R.g) (R.keep.pad R.g) j) := by
  have b := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact PoleRing.bufAt_of_VM (R.bufAll (R.keep.toFrames.ix R.g - 1) (by omega) j)

/-- **What the touch's frame needs of the area parser** (round 33; the name is from round 29, when it was `TileCol` on each instruction of the touch's frame up to
the write): the parser's column not going back from a frame's start to the next one up to the touch's frame; and at control the slot's map (`PoleSlot.SlotMap`: the parser's column has come to the pole's, or no byte of the
block buffers holds a pole's tile). Round 34: also the parser's column at control less than 32 columns before the pole's, and that each byte of the pole's
column is in the ring's column of the pole's column (`PoleRing.RingOK`). All are theorems from the parser's rule, the rows of the change and a check on the places
(`PoleParserRun.tilesCol_run`, after this file: the parser's invariant needs the rows of the change). With them, `bufAll` (`PoleSlot.frames_slot`) and the field
`tilesCol`, the walk of the touch's frame proves `TileCol` right after each far read (`PoleSlot.no_write_frameZS`). -/
abbrev Run.TileColAll {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar) : Prop :=
  (∀ n, n + 1 < R.keep.toFrames.ix R.g → parColOf sy m0 (R.keep.toFrames.all n) ≤ parColOf sy m0 (R.keep.toFrames.all (n + 1))) ∧
  PoleSlot.SlotMap (PoleFrame.spotsF sy m0) (parColOf sy m0 (R.keep.toFrames.all 0)) (R.keep.toFrames.all 0) ∧
  PoleSlot.colP (PoleFrame.spotsF sy m0) < parColOf sy m0 (R.keep.toFrames.all 0) + 32 ∧ PoleRing.RingOK (PoleFrame.spotsF sy m0)

/-- round 34: at each frame's start up to the touch's frame the parser's column is less than 32 columns before the pole's: at control (`TileColAll`, from the rows
of the change), and the column does not go back -/
theorem Run.low {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hT : R.TileColAll) : ∀ n, n < R.keep.toFrames.ix R.g → PoleSlot.colP (PoleFrame.spotsF sy m0) < parColOf sy m0 (R.keep.toFrames.all n) + 32 :=
  PoleRing.low_mono (c := fun n => parColOf sy m0 (R.keep.toFrames.all n)) hT.2.2.1 hT.1

/-- round 33: the touch's frame meets `PoleSlot.BufC` on each instruction, for the parser's column at its start: `bufAll` on its frame, with
`PoleRing.bufC_of_VM` (round 34: with the ring's facts and the bound of `Run.low`) -/
theorem Run.bufC₁ {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hT : R.TileColAll) (j : Nat) :
    PoleSlot.BufC (PoleFrame.spotsF sy m0) (parColOf sy m0 (R.keep.fm R.g)) (PipeEntryRule.trace (R.keep.fm R.g) (R.keep.pad R.g) j) := by
  have b := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact PoleRing.bufC_of_VM (R.bufAll (R.keep.toFrames.ix R.g - 1) (by omega) j) hT.2.2.2 (R.low hT (R.keep.toFrames.ix R.g - 1) (by omega))

/-- **The slot's map at the start of the touch's frame** (round 33): from the slot's map at control and the parser's column not going back (`hT`), every frame
before the touch's frame keeps it (`bufAll`: `PoleRing.bufC_of_VM` from round 34; the walk of the frames of `PoleTileKeep`: `PoleSlot.frames_slot`) -/
theorem Run.slotStart {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true)
    (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hT : R.TileColAll) :
    PoleSlot.SlotMap (PoleFrame.spotsF sy m0) (parColOf sy m0 (R.keep.fm R.g)) (R.keep.fm R.g) := by
  have h1 := R.keep.toFrames.one_le_ix R.one_le (Nat.le_refl _)
  have e : R.keep.toFrames.ix R.g = FrameKeep.ixOf sy m0 Sr ar R.keep.top R.g := rfl
  exact PoleSlot.frames_slot hk (PoleTileKeep.keepY_of_Z hc) R.keep.toFrames hc0.start (R.watched₀ st hq hc0.castle) hwb hmap
    (fun n hn k => PoleKeepFar.keepB_of_R (R.keepB n (by omega) k)) (fun n hn k => PoleRing.bufAt_of_VM (R.bufAll n (by omega) k))
    (fun n => parColOf sy m0 (R.keep.toFrames.all n)) hT.1 (fun n hn k => PoleRing.bufC_of_VM (R.bufAll n (by omega) k) hT.2.2.2 (R.low hT n (by omega))) hT.2.1
    (R.keep.toFrames.ix R.g - 1) (by omega)

/-- **A touch needs his position in the pole's range**: the walk of the whole frame of the touch (`PoleSlot.inRange_of_frameZS`, the walk of `PoleFrame` with more
splits and more tests) on frame `g` of `keep`. The frame starts in control (`FrameKeep.Frames.start`, from the machine at control) with the two bytes' values
(`Run.tilesStart`), each instruction is `CleanK` (`keep.clean`) and meets `KeepB` (`keepB`), and up to the write each instruction meets `PosKeep` (`posKeep`), `BufAt`
and `PoleSlot.BufC` (`bufAll`: `Run.bufAt₁`, `Run.bufC₁`) and `PoleSlot.TileSlotC` (`tilesCol`); the frame starts with the map (`Run.tilesStart`) and the slot's
map (`Run.slotStart`, round 33).
`P₂(g)` is the position at the end of the move (`Run.moved`). `hc` is the walk's check on the ROM, `hk` that of `FrameKeep`; `hN`, `hfr`, `hg` are as in `Run.reads`. -/
theorem Run.inRange {b : Machine} {vs : List Jump.VS} {B : Box} {T J Nc : Nat} {F : Int} {Sr : FrameKeep.RealRun} {ar : Nat} (hc : PoleTileKeep.poleCheckZ sy m0 = true) (R : Run sy m0 b vs B T J Nc F Sr ar)
    (hN : SurfaceFrames.numbersCheck sy m0 B J = true) (hfr : frictionCheck sy m0 = true)
    (st : SurfaceFrames.Start sy B (R.seq 0)) (hq : fracCheck sy B.m = true) (hk : FrameKeep.keepCheckOf sy m0 = true) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0)) (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hg : R.g ≤ SurfaceFrames.farN sy B.m)
    (hT : R.TileColAll) :
    poleP sy m0 ≤ (R.fr R.g).P₂ :=
  have hs := R.tilesStart hc hk st hq hc0 hmap hwb
  PoleSlot.inRange_of_frameZS hc R.touches (R.keep.toFrames.start hk hc0.start (R.watched₀ st hq hc0.castle) R.g R.one_le (Nat.le_refl _)) hs.2
    (fun j => PoleTileKeep.cleanK_GK (R.keep.toFrames.cleanAt R.g R.one_le (Nat.le_refl _) j) (R.keepB₁ j)) R.posKeep hs.1
    (R.slotStart hc hk st hq hc0 hmap hwb hT) (fun _ _ j _ => R.bufAt₁ j) (fun _ _ j _ => R.bufC₁ hT j) R.tilesCol R.edge
    (fun _ j _ _ hj => R.moved (PoleTileKeep.subs_of_Z hc) hN hfr st hq hk hc0 hg j hj)

/-- the numbers the join needs -/
def joinCheck (sy : Syms) (m0 : Machine) (X : Int) (N E T J Nc lo : Nat) (F : Int) : Bool :=
  let s := 16 * (top sy : Int)
  decide (16 ≤ (top sy : Int)) && decide (255 ≤ amax sy m0) && decide (amax sy m0 ≤ 512) && decide (1 ≤ E) && decide (1 ≤ J) &&
    decide (sideP sy m0 + s < poleP sy m0) && decide (feetP sy m0 + s ≤ poleP sy m0 + 224) &&
    decide (s * ((N + E : Nat) : Int) + (poleP sy m0 - feetP sy m0) ≤ X + s * ((T - N : Nat) : Int) + 32) &&
    decide (2 ≤ Nc) && decide (Nc + 6 ≤ lo) && domainOk sy &&
    decide (feetP sy m0 + s + 32 ≤ poleP sy m0 + F) && decide (0 ≤ F) && decide (F ≤ 208) &&
    decide (J ≤ T) && decide (poleP sy m0 ≤ feetP sy m0 + s + 32)

/-- what `joinCheck` says, one fact per field -/
structure Numbers (sy : Syms) (m0 : Machine) (X : Int) (N E T J Nc lo : Nat) (F : Int) : Prop where
  h16 : 16 ≤ (top sy : Int)
  h255 : 255 ≤ amax sy m0
  hA : amax sy m0 ≤ 512
  hE : 1 ≤ E
  hJ : 1 ≤ J
  hPs : sideP sy m0 + 16 * (top sy : Int) < poleP sy m0
  hfar : feetP sy m0 + 16 * (top sy : Int) ≤ poleP sy m0 + 224
  hearly : 16 * (top sy : Int) * ((N + E : Nat) : Int) + (poleP sy m0 - feetP sy m0) ≤
    X + 16 * (top sy : Int) * ((T - N : Nat) : Int) + 32
  hN : 2 ≤ Nc
  hNlo : Nc + 6 ≤ lo
  hd : domainOk sy = true
  hF : feetP sy m0 + 16 * (top sy : Int) + 32 ≤ poleP sy m0 + F
  hF0 : 0 ≤ F
  hF2 : F ≤ 208
  hJT : J ≤ T
  hfeet : poleP sy m0 ≤ feetP sy m0 + 16 * (top sy : Int) + 32

theorem numbers_of_check {X F : Int} {N E T J Nc lo : Nat} (h : joinCheck sy m0 X N E T J Nc lo F = true) :
    Numbers sy m0 X N E T J Nc lo F := by
  simp only [joinCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

section Join

variable {b : Machine} {vs : List Jump.VS} {n : Nat} {X F : Int} {N E T J dx dy rows Nc lo : Nat} {Sr : FrameKeep.RealRun} {ar : Nat}

/-- what the machine at control gives: `hN` the numbers of the machine of the private proof, `st` the state of the real machine at control -/
abbrev AtControl (sy : Syms) (m0 : Machine) (n dx dy rows J : Nat) (m : Machine) : Prop :=
  SurfaceFrames.numbersCheck sy m0 ⟨above m0 n, dx, dy, rows⟩ J = true ∧ SurfaceFrames.Start sy ⟨above m0 n, dx, dy, rows⟩ m

/-- `hB` of `slow_short` on a run, with `B = PA + X + 16·top·(T − N)` and `PA` the position of `SurfaceRun.above` -/
theorem hB_run (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (H : Numbers sy m0 X N E T J Nc lo F)
    (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true)
    (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0)) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hg : R.g ≤ SurfaceFrames.farN sy (above m0 n)) (e d : Nat) (he1 : 1 ≤ e) (heg : e ≤ R.g) (hd : e + d = T)
    (hPf : feetP sy m0 ≤ (R.fr e).P₂) :
    (R.fr e).P₂ + 16 * (top sy : Int) * (d : Int) ≤
      posP sy (above m0 n) + X + 16 * (top sy : Int) * ((T - N : Nat) : Int) := by
  have hgap := S.gap
  have hearly := H.hearly
  obtain ⟨w, h, Rs⟩ := SurfaceFrames.surface_of_frames Fa S.noHit A.1 S.fric H.hJT S.far R.frames A.2 (fun n hn => (R.keep.toFrames.all_start hkc hc0.start (R.watched₀ A.2 hfq hc0.castle) n hn).1) hg
  exact hB_of_line (PA := posP sy (above m0 n)) Fa S H.h16 H.h255 H.hE H.hJ Rs (first_of_surface S.noHit H.hJT Rs) (R.next A.1 S.fric A.2 hfq hkc hc0 hg) (R.startV A.1 A.2) (R.startP A.2)
    (by omega) e d he1 heg hd hPf

/-- The position bound forbids standing on the base by frame `T`: with his feet over it on frame `w − 1`, `w` is past `T`. -/
theorem base_late (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (H : Numbers sy m0 X N E T J Nc lo F)
    (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true)
    (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0)) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))
    (hgN : R.g ≤ SurfaceFrames.farN sy (above m0 n)) (w : Nat) (h2 : 2 ≤ w) (hg : w ≤ R.g) (hPf : feetP sy m0 ≤ (R.fr (w - 1)).P₂) :
    T + 1 ≤ w := by
  by_cases hw : T + 1 ≤ w
  · exact hw
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d, (w - 1) + (d + 1) = T := ⟨T - w, by omega⟩
    have h1 := hB_run Fa S H hfq hkc R A hc0 hgN (w - 1) (d + 1) (by omega) (by omega) hd hPf
    have h3 := S.gap
    have h4 := H.hfeet
    have h16 := H.h16
    have h5 : 16 * (top sy : Int) * ((d + 1 : Nat) : Int) = 16 * (top sy : Int) * (d : Int) + 16 * (top sy : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    have h6 : 0 ≤ 16 * (top sy : Int) * (d : Int) := Int.mul_nonneg (by omega) (by omega)
    omega

/-- No touch up to frame `T`: this is `P₂(g) < P₀` from the position bound, hits included. -/
theorem touch_ge (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (hn : joinCheck sy m0 X N E T J Nc lo F = true)
    (hc : PoleTileKeep.poleCheckZ sy m0 = true) (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true)
    (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0)) (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0))
    (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hgN : R.g ≤ SurfaceFrames.farN sy (above m0 n))
    (hT : R.TileColAll) : T + 1 ≤ R.g := by
  have H := numbers_of_check hn
  by_cases hgT : R.g ≤ T
  · exfalso
    have hgap := S.gap
    have hr := R.inRange hc A.1 S.fric A.2 hfq hkc hc0 hmap hwb hgN hT
    have h16 := H.h16
    have hfar := H.hfar
    by_cases hPf : feetP sy m0 ≤ (R.fr R.g).P₂
    · have h1 := hB_run Fa S H hfq hkc R A hc0 hgN R.g (T - R.g) R.one_le (Nat.le_refl _) (by omega) hPf
      have h2 : 0 ≤ 16 * (top sy : Int) * ((T - R.g : Nat) : Int) := Int.mul_nonneg (by omega) (by omega)
      omega
    · omega
  · omega

/-- A direct grab: the jump is slow and the grab is not before frame `T + 7`; the castle follows. The case split: a fast jump never gets there (`fast_short`); a slow jump
not by `T + 6` (`slow_short`); on `T + 7` and `T + 8` he moved left on the frame before, with the fraction below `F` (`slow_tight`), so the castle is `Nc` frames later;
later than that, `Nc − 1` frames are enough. -/
theorem direct_castle (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (C : CastleWalk.Statement sy b vs Nc lo)
    (hj : Jump.arcCheck sy m0 (Jump.groundY sy) 1 (Jump.riseOk sy 1 2 1) = true)
    (hp : poleCheck sy m0 = true) (hm : maskCheck sy m0 = true) (hn : joinCheck sy m0 X N E T J Nc lo F = true)
    (hf : frictionCheck sy m0 = true) (hr' : fallCheck sy m0 rows = true) (hc : PoleTileKeep.poleCheckZ sy m0 = true)
    (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true) (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0))
    (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0)) (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hgN : R.g ≤ SurfaceFrames.farN sy (above m0 n))
    (hT : R.TileColAll) (hd : IsDirect sy R.touchY R.touchRising) :
    T + 7 ≤ R.g ∧ (R.g ≤ T + 8 → R.g + Nc ≤ R.c) ∧ R.g + Nc ≤ R.c + 1 := by
  have H := numbers_of_check hn
  obtain ⟨q, L, T', a, u, W⟩ := R.direct hd
  have hrise := grab_frame hj W.path (by rw [W.atRising, hd.1]; rfl) (by rw [W.atY]; exact hd.2.1) (by rw [W.atY]; exact hd.2.2)
  have hq := W.one_le
  have hnx : ∀ j, q ≤ j → j < R.g → Next (R.fr j) (R.fr (j + 1)) := fun j h1 h2 => R.next A.1 S.fric A.2 hfq hkc hc0 hgN j (by omega) h2
  have hv : ∀ j, q ≤ j → j ≤ R.g → -(top sy : Int) ≤ (R.fr j).v ∧ (R.fr j).v ≤ (top sy : Int) := fun j h1 h2 => by
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    subst hi
    exact speed_range H.h16 (R.next A.1 S.fric A.2 hfq hkc hc0 hgN) (R.startV A.1 A.2) i h2
  have hin := R.inRange hc A.1 S.fric A.2 hfq hkc hc0 hmap hwb hgN hT
  have hgap := S.gap
  have hN := H.hN
  have hTg := W.path.before
  have hbase : q < L → L < T' → ∀ w, 2 ≤ w → w ≤ q → feetP sy m0 ≤ (R.fr (w - 1)).P₂ → T + 1 ≤ w :=
    fun h1 h2 w h3 h4 h5 => base_late Fa S H hfq hkc R A hc0 hgN w h3 (by omega) h5
  -- the stored speed of the frames before the jump, read from the machines
  have hstop : ∀ j, 1 ≤ j → j < R.g → (R.fr j).v = 0 →
      (trackOf sy R.keep.toFrames u).abs j = (R.fr j).v₂.natAbs ∨
        ((trackOf sy R.keep.toFrames u).abs j = (trackOf sy R.keep.toFrames u).abs (j - 1) ∧
          (trackOf sy R.keep.toFrames u).md j = (trackOf sy R.keep.toFrames u).md (j - 1)) := by
    intro j h1 h2 h0
    rcases R.stop_step A.1 hf A.2 hfq hkc hc0 hgN (j := j) h1 h2 h0 with e | ⟨e1, e2⟩
    · exact Or.inl e
    · exact Or.inr ⟨congrArg UInt8.toNat e1, e2⟩
  have hkeep : ∀ j, 1 ≤ j → j < R.g →
      (trackOf sy R.keep.toFrames u).abs j = (R.fr j).v₂.natAbs ∨
        (trackOf sy R.keep.toFrames u).abs j = (trackOf sy R.keep.toFrames u).abs (j - 1) := by
    intro j h1 h2
    rcases R.stored_step A.1 hf A.2 hfq hkc hc0 hgN (j := j) h1 h2 with e | e
    · exact Or.inl e
    · exact Or.inr (congrArg UInt8.toNat e)
  cases hfa : (a T').fast with
  | true =>
    exfalso
    have hA0 := W.approach (Or.inl hfa)
    have ho := hA0.order
    have hA := approach_of_cases hp hm H.hd hr' hA0 (hbase hA0.order.1 hA0.order.2) (fun _ j h1 h2 h0 => hstop j (by omega) (by omega) h0)
      (fun _ j h1 h2 => hkeep j (by omega) (by omega))
    rw [hfa] at hA
    have hr : R.g = T' + 1 := by simpa [hfa] using hrise
    have := fast_short H.h16 H.hA R.fr (sideP sy m0) (feetP sy m0) (poleP sy m0) T H.hPs H.hfar hnx hv hA hr
    omega
  | false =>
    have hr : R.g = T' + 2 := by simpa [hfa] using hrise
    by_cases hg : R.g ≤ T + 6
    · exfalso
      have hA0 := W.approach (Or.inr (by omega))
      have ho := hA0.order
      have hA := approach_of_cases hp hm H.hd hr' hA0 (hbase hA0.order.1 hA0.order.2) (fun _ j h1 h2 h0 => hstop j (by omega) (by omega) h0)
        (fun _ j h1 h2 => hkeep j (by omega) (by omega))
      rw [hfa] at hA
      have := slow_short H.h16 H.hA R.fr (sideP sy m0) (feetP sy m0) (poleP sy m0)
        (posP sy (above m0 n) + X + 16 * (top sy : Int) * ((T - N : Nat) : Int)) T H.hPs H.hfar (by omega)
        (fun e d h1 h2 h3 h4 => hB_run Fa S H hfq hkc R A hc0 hgN e d (by omega) (by omega) h3 h4) hnx hv hA hr hg
      omega
    · have hu := R.frac_mem A.2 hfq hkc hc0
      have h0 := castle_of_direct C (n := Nc - 2) hu (by omega) (W.flagAny hfa) R.atCastle (R.afterTouch A.2 hfq hkc hc0)
      refine ⟨by omega, fun hg8 => ?_, by omega⟩
      have hA0 := W.approach (Or.inr hg8)
      have ho := hA0.order
      have hA := approach_of_cases hp hm H.hd hr' hA0 (hbase hA0.order.1 hA0.order.2) (fun _ j h1 h2 h0 => hstop j (by omega) (by omega) h0)
        (fun _ j h1 h2 => hkeep j (by omega) (by omega))
      rw [hfa] at hA
      have hA' : Approach R.fr (sideP sy m0) (feetP sy m0) T q L T' (T' + 2) false := hr ▸ hA
      have hin' : poleP sy m0 ≤ (R.fr (T' + 2)).P₂ := hr ▸ hin
      obtain ⟨h1, h2⟩ := slow_tight H.h16 H.hA R.fr (sideP sy m0) (feetP sy m0) (poleP sy m0) F T H.hPs H.hF H.hF0 H.hF2
        (fun j h3 h4 => hnx j h3 (by omega)) (fun j h3 h4 => hv j h3 (by omega)) hA' (by omega) hin'
      have e1 : R.g - 1 = T' + 1 := by omega
      have e2 : R.fr R.g = R.fr (T' + 2) := congrArg R.fr hr
      have h3 := W.flagTight hfa (by rw [e1]; exact h1) (by rw [← e2] at h2; exact h2)
      have h4 := castle_of_direct C (n := Nc - 1) hu (by omega) h3 R.atCastle (R.afterTouch A.2 hfq hkc hc0)
      omega

/-- **The castle entry is at least `T + 7 + Nc` frames after control above ground.** With the numbers of the private proof, `366 ≤ c`. `A` and `hc0` are the machine at
control: its numbers and state, and the start of a frame in control with the castle flag down (`ControlStart.EndRun.atCtl` on a real run). -/
theorem castle_ge (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (C : CastleWalk.Statement sy b vs Nc lo)
    (hj : Jump.arcCheck sy m0 (Jump.groundY sy) 1 (Jump.riseOk sy 1 2 1) = true)
    (hp : poleCheck sy m0 = true) (hm : maskCheck sy m0 = true) (hn : joinCheck sy m0 X N E T J Nc lo F = true)
    (hf : frictionCheck sy m0 = true) (hr : fallCheck sy m0 rows = true) (hc : PoleTileKeep.poleCheckZ sy m0 = true)
    (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true) (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0))
    (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0)) (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hgN : R.g ≤ SurfaceFrames.farN sy (above m0 n))
    (hT : R.TileColAll) : T + 7 + Nc ≤ R.c := by
  have H := numbers_of_check hn
  by_cases hd : IsDirect sy R.touchY R.touchRising
  · obtain ⟨h1, h2, h3⟩ := direct_castle Fa S C hj hp hm hn hf hr hc hfq hkc R A hc0 hmap hwb hgN hT hd
    by_cases hg : R.g ≤ T + 8
    · have := h2 hg
      omega
    · omega
  · have h1 := touch_ge Fa S hn hc hfq hkc R A hc0 hmap hwb hgN hT
    have h2 := castle_of_other C (n := Nc + 5) (by have := H.hNlo; omega) (R.other hd) R.atCastle (R.afterTouch A.2 hfq hkc hc0)
    omega

/-- **The touch and the castle together**, for the timer: another touch, not before `T + 1` with the castle at least `Nc + 6` frames later; a direct grab on `T + 7` or
`T + 8` with the castle at least `Nc` frames later; a direct grab from `T + 9` on with the castle at least `Nc − 1` frames later. -/
theorem touch_castle (Fa : FastTakeoff.TFacts sy m0) (S : Statement sy m0 n X N E T J dx dy) (C : CastleWalk.Statement sy b vs Nc lo)
    (hj : Jump.arcCheck sy m0 (Jump.groundY sy) 1 (Jump.riseOk sy 1 2 1) = true)
    (hp : poleCheck sy m0 = true) (hm : maskCheck sy m0 = true) (hn : joinCheck sy m0 X N E T J Nc lo F = true)
    (hf : frictionCheck sy m0 = true) (hr : fallCheck sy m0 rows = true) (hc : PoleTileKeep.poleCheckZ sy m0 = true)
    (hfq : fracCheck sy (above m0 n) = true) (hkc : FrameKeep.keepCheckOf sy m0 = true) (R : Run sy m0 b vs ⟨above m0 n, dx, dy, rows⟩ T J Nc F Sr ar) (A : AtControl sy m0 n dx dy rows J (R.seq 0))
    (hc0 : FrameKeep.AtCtl sy m0 (R.seq 0)) (hmap : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (R.seq 0)) (hwb : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (R.seq 0)) (hgN : R.g ≤ SurfaceFrames.farN sy (above m0 n))
    (hT : R.TileColAll) :
    (T + 1 ≤ R.g ∧ R.g + Nc + 6 ≤ R.c) ∨ (T + 7 ≤ R.g ∧ R.g ≤ T + 8 ∧ R.g + Nc ≤ R.c) ∨ (T + 9 ≤ R.g ∧ R.g + Nc ≤ R.c + 1) := by
  have H := numbers_of_check hn
  by_cases hd : IsDirect sy R.touchY R.touchRising
  · obtain ⟨h1, h2, h3⟩ := direct_castle Fa S C hj hp hm hn hf hr hc hfq hkc R A hc0 hmap hwb hgN hT hd
    by_cases hg : R.g ≤ T + 8
    · exact Or.inr (Or.inl ⟨h1, hg, h2 hg⟩)
    · exact Or.inr (Or.inr ⟨by omega, h3⟩)
  · have h1 := touch_ge Fa S hn hc hfq hkc R A hc0 hmap hwb hgN hT
    have h2 := castle_of_other C (n := Nc + 5) (by have := H.hNlo; omega) (R.other hd) R.atCastle (R.afterTouch A.2 hfq hkc hc0)
    exact Or.inl ⟨h1, by omega⟩

end Join

end Whole

end Smbrta.PoleJoin
