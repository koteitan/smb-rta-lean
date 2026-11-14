import Theorems.VertModel
import Theorems.Opening

/-!
# The jumps of the opening on the vertical model

The vertical bytes of a frame in the air follow `vstep` up to the scroll handler (`VertModel.vert_model` at the takeoff, `VertAir.vert_air` in the air, with the stored speed
0). On the opening's flat ground the collision routine then only lands him: falling, at or below the ground's height `y0`, he lands at `y0` with no vertical speed and no
fraction, in the state 0 (`land`). `vstepO` is the frame of this model: `vstep` on the machine of `VertModel.vstepV`, then `land`.

* `arcCheck`: a search on the ROM of every jump of the model from the ground at `y0`, for every takeoff speed up to the top and every A on every frame: in the air the frame
  count stays below the longest length `L_hold` of the takeoff speed (`Opening.jumpLens`), and the landing frame is at least the shortest length `L_tap`; the height just
  before the landing is in the window of `LandDepth` px below `y0` (where the game lands him too); in the air the height stays in `[32, y0)` or he rises.
* `lands`: a sequence of vertical states that follows the model from a takeoff lands within the two lengths, at `y0` with no vertical speed. `OpenFrames.Real.jumpV` uses it
  for the length of a jump (the old field `jump` of `OpenFrames.Real`) and `OpenFrames.Real.ground_all` for the ground's height after the landing (the old field `ground`).

What is not here: that the real frames of the opening follow `vstepO` (the field `vert` of `OpenFrames.Real`). There is no game data in this file. Page:
`1-1/a-5-7-OpenJump.md`.
-/

namespace Smbrta.OpenJump

open Jump (VS)
open Opening (Lens)

/-! ## The model -/

/-- **The landing on the opening's ground** at the height `y0`: in the air, falling (the vertical speed not negative), at or below `y0`, he lands at `y0` with no vertical
speed and no fraction, in the state 0 -/
def land (y0 : UInt8) (s : VS) : VS :=
  if s.st != 0 && s.vy < 0x80 && decide (y0 ≤ s.y) then { s with y := y0, vy := 0, mf := 0, st := 0 } else s

/-- **One frame of the opening's vertical model**: `vstep` on the machine of `VertModel.vstepV` (the stack pointer `S` of the player's routine), with A pressed or not and the
stored speed `abs`, then `land` -/
def vstepO (sy : Syms) (m0 : Machine) (S : UInt8) (y0 : UInt8) (s : VS) (a : Bool) (abs : UInt8) : VS :=
  land y0 (VertModel.vstepV sy m0 S s a abs)

/-- on the ground at `y0` before a takeoff: the bytes that the takeoff overwrites are 0, and A was not pressed on the frame before -/
def ground0 (y0 : UInt8) : VS := { y := y0, mf := 0, vy := 0, dummy := 0, vf := 0, vfd := 0, origin := 0, st := 0, prevA := false }

/-! ## The search of the jumps -/

/-- a jump followed frame by frame: the vertical state, the frames since the takeoff frame began, the two lengths of the takeoff speed, the height before `land` -/
structure Arc where
  s : VS
  k : Nat
  lo : Nat
  hi : Nat
  pre : UInt8
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- every next frame in the air, with A pressed or not and the stored speed 0; none after the landing -/
def arcSucc (sy : Syms) (m0 : Machine) (S y0 : UInt8) (x : Arc) : List Arc :=
  if x.s.st == 0 then []
  else [true, false].map fun a =>
    let r := VertModel.vstepV sy m0 S x.s a 0
    { s := land y0 r, k := x.k + 1, lo := x.lo, hi := x.hi, pre := r.y }

/-- the takeoff frame from the ground at `y0`, for every takeoff speed up to the top: the state when the next frame begins -/
def arcStart (sy : Syms) (m0 : Machine) (S y0 : UInt8) (lens : Lens) : List Arc :=
  ((List.range (TopSpeed.top sy + 1)).map fun v =>
    let r := VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8
    ({ s := land y0 r, k := 1, lo := (lens[v]!).1, hi := (lens[v]!).2, pre := r.y } : Arc)).eraseDups

/-- **What every frame of every jump meets**: in the air, the count below the longest length, the height in `[32, y0)` or rising; landed, the count between the two
lengths, at `y0` with no vertical speed and no fraction, and the height before `land` in the window of `d` px below `y0` -/
def arcOK (y0 d : UInt8) (x : Arc) : Bool :=
  if x.s.st == 0 then decide (x.lo ≤ x.k) && decide (x.k ≤ x.hi) && x.s.y == y0 && x.s.vy == 0 && x.s.mf == 0 && decide (y0 ≤ x.pre) &&
    decide (x.pre.toNat < y0.toNat + d.toNat)
  else decide (x.k < x.hi) && (decide (32 ≤ x.s.y) && decide (x.s.y < y0) || x.s.vy ≥ 0x80)

/-- the depth of the search: above every length -/
def arcDepth : Nat := 80

/-- **The check on the ROM**: `arcOK` on every frame of every jump, and every length below the depth -/
def arcCheck (sy : Syms) (m0 : Machine) (S y0 d : UInt8) (lens : Lens) : Bool :=
  Cert.checkPrunedS (arcSucc sy m0 S y0) (arcOK y0 d) (fun _ _ => true) arcDepth (arcStart sy m0 S y0 lens) &&
    (lens.toList.all fun p => decide (p.2 ≤ arcDepth))

/-- the check for the opening: the stack pointer of the player's routine, the height of `m0`, the window `LandDepth`, the lengths `Opening.jumpLens` -/
def openJumpCheck (sy : Syms) (m0 : Machine) : Bool :=
  arcCheck sy m0 (FrameModel.ctrlStack sy m0) (peek m0 sy.Player_Y_Position) sy.LandDepth.toUInt8 (Opening.jumpLens sy m0)

/-! ## What the search shows -/

section
variable {sy : Syms} {m0 : Machine} {S y0 d : UInt8} {lens : Lens}

theorem arc_spec (hc : arcCheck sy m0 S y0 d lens = true) :
    ∀ x ∈ arcStart sy m0 S y0 lens, ∀ n u, n ≤ arcDepth → Cert.Reach (arcSucc sy m0 S y0) x n u → arcOK y0 d u = true := by
  simp only [arcCheck, Bool.and_eq_true] at hc
  exact Cert.prunedS_spec (arcSucc sy m0 S y0) (arcOK y0 d) (fun _ _ => true) (fun _ _ h0 => by simp at h0) arcDepth _ hc.1

theorem lens_le (hc : arcCheck sy m0 S y0 d lens = true) (v : Nat) : (lens[v]!).2 ≤ arcDepth := by
  simp only [arcCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  by_cases h : v < lens.size
  · rw [getElem!_pos lens v h]
    exact hc.2 _ (Array.mem_toList_iff.2 (Array.getElem_mem h))
  · rw [getElem!_neg lens v h]
    show (0 : Nat) ≤ arcDepth
    omega

/-- the arc of a sequence of states, from the frame `1` -/
def arcOf (u : Nat → VS) (lo hi : Nat) (pre : Nat → UInt8) (d : Nat) : Arc := { s := u d, k := d, lo, hi, pre := pre d }

/-- **A sequence of vertical states that follows the model from a takeoff** reaches its arcs: while in the air, each next state is the model's step, so the arc of frame
`1 + j` is reached from the takeoff's arc in `j` steps -/
theorem reach_arcs {u : Nat → VS} {a : Nat → Bool} {pre : Nat → UInt8} {lo hi : Nat}
    (hstep : ∀ e, 1 ≤ e → e < arcDepth → (∀ e', 1 ≤ e' → e' ≤ e → (u e').st ≠ 0) → pre (e + 1) = (VertModel.vstepV sy m0 S (u e) (a e) 0).y ∧
      u (e + 1) = land y0 (VertModel.vstepV sy m0 S (u e) (a e) 0)) :
    ∀ j, j < arcDepth → (∀ e, 1 ≤ e → e < 1 + j → (u e).st ≠ 0) → Cert.Reach (arcSucc sy m0 S y0) (arcOf u lo hi pre 1) j (arcOf u lo hi pre (1 + j)) := by
  intro j
  induction j with
  | zero => intro _ _; exact .refl _
  | succ j ih =>
    intro hjd hair
    have h1 := ih (by omega) (fun e h1 h2 => hair e h1 (by omega))
    have hj := hair (1 + j) (by omega) (by omega)
    obtain ⟨hp, hu⟩ := hstep (1 + j) (by omega) (by omega) (fun e' h1 h2 => hair e' h1 (by omega))
    have hmem : arcOf u lo hi pre (1 + (j + 1)) ∈ arcSucc sy m0 S y0 (arcOf u lo hi pre (1 + j)) := by
      unfold arcSucc arcOf
      have hne : ((u (1 + j)).st == 0) = false := by simp [hj]
      rw [if_neg (by simp [hne])]
      refine List.mem_map.2 ⟨a (1 + j), by cases a (1 + j) <;> simp, ?_⟩
      rw [show 1 + (j + 1) = 1 + j + 1 by omega, hu, hp]
    exact reach_snoc h1 hmem
where
  reach_snoc {σ : Type} {f : σ → List σ} : ∀ {x y z : σ} {k : Nat}, Cert.Reach f x k y → z ∈ f y → Cert.Reach f x (k + 1) z
    | _, _, _, _, .refl _, h => .step h (.refl _)
    | _, _, _, _, .step h1 h2, h => .step h1 (reach_snoc h2 h)

/-- **The landing of a jump of the model.** A sequence of vertical states whose frame `1` is the takeoff's state for the speed `v` (with the height `pre 1` before `land`), and
whose next state is the model's step (A of the frame `a e`) while every frame from `1` on is in the air, lands within the two lengths of `v`: the frames from `1` to `n − 1` are in the air, and the
frame `n` is on the ground at `y0` with no vertical speed and no fraction. -/
theorem lands (hc : arcCheck sy m0 S y0 d lens = true) {u : Nat → VS} {a : Nat → Bool} {pre : Nat → UInt8} {v : Nat} (hv : v ≤ TopSpeed.top sy)
    (h1 : pre 1 = (VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8).y ∧ u 1 = land y0 (VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8))
    (hstep : ∀ e, 1 ≤ e → e < arcDepth → (∀ e', 1 ≤ e' → e' ≤ e → (u e').st ≠ 0) → pre (e + 1) = (VertModel.vstepV sy m0 S (u e) (a e) 0).y ∧
      u (e + 1) = land y0 (VertModel.vstepV sy m0 S (u e) (a e) 0)) :
    ∃ n, 1 ≤ n ∧ (lens[v]!).1 ≤ n ∧ n ≤ (lens[v]!).2 ∧ (∀ e, 1 ≤ e → e < n → (u e).st ≠ 0) ∧
      (u n).st = 0 ∧ (u n).y = y0 ∧ (u n).vy = 0 ∧ (u n).mf = 0 := by
  have hstart : arcOf u (lens[v]!).1 (lens[v]!).2 pre 1 ∈ arcStart sy m0 S y0 lens := by
    unfold arcStart arcOf
    refine List.mem_eraseDups.2 (List.mem_map.2 ⟨v, List.mem_range.2 (by omega), ?_⟩)
    rw [h1.1, h1.2]
  have hok : ∀ j, j < arcDepth → (∀ e, 1 ≤ e → e < 1 + j → (u e).st ≠ 0) → arcOK y0 d (arcOf u (lens[v]!).1 (lens[v]!).2 pre (1 + j)) = true :=
    fun j hj hair => arc_spec hc _ hstart j _ (Nat.le_of_lt hj) (reach_arcs hstep j hj hair)
  have hL := lens_le hc v
  -- the first frame on the ground, by induction on the frames left below the longest length
  have key : ∀ r j, r = (lens[v]!).2 - (1 + j) → 1 + j ≤ (lens[v]!).2 → (∀ e, 1 ≤ e → e < 1 + j → (u e).st ≠ 0) →
      ∃ n, 1 ≤ n ∧ n ≤ (lens[v]!).2 ∧ (∀ e, 1 ≤ e → e < n → (u e).st ≠ 0) ∧ (u n).st = 0 := by
    intro r
    induction r with
    | zero =>
      intro j hr hj hair
      by_cases hs : (u (1 + j)).st = 0
      · exact ⟨1 + j, by omega, hj, hair, hs⟩
      · exfalso
        have := hok j (by omega) hair
        simp only [arcOK, arcOf] at this
        rw [if_neg (by simp [hs])] at this
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        have := this.1
        omega
    | succ r ih =>
      intro j hr hj hair
      by_cases hs : (u (1 + j)).st = 0
      · exact ⟨1 + j, by omega, hj, hair, hs⟩
      · exact ih (j + 1) (by omega) (by omega) (fun e h1 h2 => by
          by_cases he : e < 1 + j
          · exact hair e h1 he
          · rw [show e = 1 + j by omega]; exact hs)
  -- a landed frame after frames in the air: what `arcOK` says there
  have fin : ∀ n, 1 ≤ n → n ≤ arcDepth → (∀ e, 1 ≤ e → e < n → (u e).st ≠ 0) → (u n).st = 0 →
      (lens[v]!).1 ≤ n ∧ n ≤ (lens[v]!).2 ∧ (u n).y = y0 ∧ (u n).vy = 0 ∧ (u n).mf = 0 := by
    intro n n1 n2 n3 n4
    have hn := hok (n - 1) (by omega) (fun e h1 h2 => n3 e h1 (by omega))
    rw [show 1 + (n - 1) = n by omega] at hn
    simp only [arcOK, arcOf] at hn
    rw [if_pos (by simp [n4])] at hn
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hn
    exact ⟨hn.1.1.1.1.1.1, hn.1.1.1.1.1.2, hn.1.1.1.1.2, hn.1.1.1.2, hn.1.1.2⟩
  by_cases hs1 : (u 1).st = 0
  · obtain ⟨f1, f2, f3, f4, f5⟩ := fin 1 (Nat.le_refl 1) (by unfold arcDepth; omega) (fun e h1 h2 => by omega) hs1
    exact ⟨1, Nat.le_refl 1, f1, f2, fun e h1 h2 => by omega, hs1, f3, f4, f5⟩
  · have h0 := hok 0 (by unfold arcDepth; omega) (fun e h1 h2 => by
      rw [show e = 1 by omega]; exact hs1)
    simp only [arcOK, arcOf] at h0
    rw [if_neg (by simp [hs1])] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    have hlt := h0.1
    obtain ⟨n, n1, n2, n3, n4⟩ := key ((lens[v]!).2 - 1) 0 (by omega) (by omega) (fun e h1 h2 => by omega)
    obtain ⟨f1, f2, f3, f4, f5⟩ := fin n n1 (by omega) n3 n4
    exact ⟨n, n1, f1, f2, n3, n4, f3, f4, f5⟩

end

end Smbrta.OpenJump
