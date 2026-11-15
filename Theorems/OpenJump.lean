import Theorems.VertModel
import Theorems.Opening

/-!
# The jumps of the opening on the vertical model

The vertical bytes of a frame in the air follow `vstep` up to the scroll handler (`VertModel.vert_model` at the takeoff, `VertAir.vert_air` in the air, with the stored speed
0). On the opening's flat ground the collision routine then only lands him: falling, at or below the ground's height `y0`, he lands at `y0` with no vertical speed and no
fraction, in the state 0 (`land`). `vstepO` is the frame of this model: `vstep` on the machine of `VertModel.vstepV`, then `land`.

* `arcCheck`: a search on the ROM of every jump of the model from the ground at `y0`, for every takeoff speed up to the top and every A on every frame: in the air the frame
  count stays below the longest length `L_hold` of the takeoff speed (`Opening.jumpLens`), and the landing frame is at least the shortest length `L_tap`; the height just
  before the landing is in the window of `LandDepth` px below `y0` (where the game lands him too), and the high byte after each step in the air is 1 (`hiAfter`); in the
  air the height stays in `[32, y0)`.
* `lands_by`: a sequence of vertical states that follows the model from a takeoff up to a frame `h` either lands by `h` within the two lengths, at `y0` with no vertical
  speed, or is in the air up to `h` with `h` below `L_hold`. `OpenFrames.Real.jumpV` uses it for the length of a jump (the old field `jump` of `OpenFrames.Real`) and
  `OpenFrames.Real.ground_all` for the ground's height after the landing (the old field `ground`).

That the real frames of the opening follow `vstepO` (the old field `vert` of `OpenFrames.Real`) is `OpenFrames.Real.vertOK`, from the walks of `OpenAir`. There is no
game data in this file. Page:
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

/-- the high byte of the height after the model's step: that of the machine of `vstep` after the movement routine -/
def hiAfter (sy : Syms) (m0 : Machine) (S : UInt8) (s : VS) (a : Bool) (abs : UInt8) : UInt8 :=
  peek (VertModel.vRun sy m0 S s a abs) sy.Player_Y_HighPos

/-- the model's step and the high byte after it, from one run of the routine -/
def stepH (sy : Syms) (m0 : Machine) (S : UInt8) (s : VS) (a : Bool) (abs : UInt8) : VS × UInt8 :=
  let M := VertModel.vRun sy m0 S s a abs
  (Jump.VS.mk (peek M sy.Player_Y_Position) (peek M sy.Player_Y_MoveForce) (peek M sy.Player_Y_Speed) (peek M sy.Player_YMF_Dummy) (peek M sy.VerticalForce)
    (peek M sy.VerticalForceDown) (peek M sy.JumpOrigin_Y_Position) (peek M sy.Player_State) a, peek M sy.Player_Y_HighPos)

theorem stepH_eq (sy : Syms) (m0 : Machine) (S : UInt8) (s : VS) (a : Bool) (abs : UInt8) :
    stepH sy m0 S s a abs = (VertModel.vstepV sy m0 S s a abs, hiAfter sy m0 S s a abs) := rfl

/-- a jump followed frame by frame: the vertical state, the frames since the takeoff frame began, the two lengths of the takeoff speed, the height before `land`, the
high byte after the step -/
structure Arc where
  s : VS
  k : Nat
  lo : Nat
  hi : Nat
  pre : UInt8
  phi : UInt8
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- every next frame in the air, with A pressed or not and the stored speed 0; none after the landing -/
def arcSucc (sy : Syms) (m0 : Machine) (S y0 : UInt8) (x : Arc) : List Arc :=
  if x.s.st == 0 then []
  else [true, false].map fun a =>
    let p := stepH sy m0 S x.s a 0
    { s := land y0 p.1, k := x.k + 1, lo := x.lo, hi := x.hi, pre := p.1.y, phi := p.2 }

/-- the takeoff frame from the ground at `y0`, for every takeoff speed up to the top: the state when the next frame begins -/
def arcStart (sy : Syms) (m0 : Machine) (S y0 : UInt8) (lens : Lens) : List Arc :=
  ((List.range (TopSpeed.top sy + 1)).map fun v =>
    let p := stepH sy m0 S (ground0 y0) true v.toUInt8
    ({ s := land y0 p.1, k := 1, lo := (lens[v]!).1, hi := (lens[v]!).2, pre := p.1.y, phi := p.2 } : Arc)).eraseDups

/-- **What every frame of every jump meets**: in the air, the count below the longest length and the height in `[32, y0)`; landed, the count between the two
lengths, at `y0` with no vertical speed and no fraction, and the height before `land` in the window of `d` px below `y0`; and the high byte after the step 1 -/
def arcOK (y0 d : UInt8) (x : Arc) : Bool :=
  if x.s.st == 0 then decide (x.lo ≤ x.k) && decide (x.k ≤ x.hi) && x.s.y == y0 && x.s.vy == 0 && x.s.mf == 0 && decide (y0 ≤ x.pre) &&
    decide (x.pre.toNat < y0.toNat + d.toNat) && x.phi == 1
  else decide (x.k < x.hi) && decide (32 ≤ x.s.y) && decide (x.s.y < y0) && x.phi == 1

/-- the depth of the search: above every length -/
def arcDepth : Nat := 80

/-- **The check on the ROM**: `arcOK` on every frame of every jump, and every pair of lengths in order and below the depth -/
def arcCheck (sy : Syms) (m0 : Machine) (S y0 d : UInt8) (lens : Lens) : Bool :=
  Cert.checkPrunedS (arcSucc sy m0 S y0) (arcOK y0 d) (fun _ _ => true) arcDepth (arcStart sy m0 S y0 lens) &&
    (lens.toList.all fun p => decide (p.1 ≤ p.2) && decide (p.2 ≤ arcDepth))

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
    exact (hc.2 _ (Array.mem_toList_iff.2 (Array.getElem_mem h))).2
  · rw [getElem!_neg lens v h]
    show (0 : Nat) ≤ arcDepth
    omega

/-- the two lengths are in order -/
theorem lens_ord (hc : arcCheck sy m0 S y0 d lens = true) (v : Nat) : (lens[v]!).1 ≤ (lens[v]!).2 := by
  simp only [arcCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  by_cases h : v < lens.size
  · rw [getElem!_pos lens v h]
    exact (hc.2 _ (Array.mem_toList_iff.2 (Array.getElem_mem h))).1
  · rw [getElem!_neg lens v h]
    show (0 : Nat) ≤ 0
    omega

/-- the arc of a sequence of states, from the frame `1` -/
def arcOf (u : Nat → VS) (lo hi : Nat) (pre ph : Nat → UInt8) (d : Nat) : Arc := { s := u d, k := d, lo, hi, pre := pre d, phi := ph d }

/-- a path of `Reach` with one step more at its end -/
theorem reach_snoc {σ : Type} {f : σ → List σ} : ∀ {x y z : σ} {k : Nat}, Cert.Reach f x k y → z ∈ f y → Cert.Reach f x (k + 1) z
  | _, _, _, _, .refl _, h => .step h (.refl _)
  | _, _, _, _, .step h1 h2, h => .step h1 (reach_snoc h2 h)

/-- `land` that leaves the state in the air leaves everything -/
theorem land_of_air {r : VS} (h : (land y0 r).st ≠ 0) : land y0 r = r := by
  unfold land at h ⊢
  split
  · rename_i hc
    rw [if_pos hc] at h
    exact absurd rfl h
  · rfl

/-- the arc after `x`, with A `a`: the model's step -/
def arcNext (sy : Syms) (m0 : Machine) (S y0 : UInt8) (x : Arc) (a : Bool) : Arc :=
  { s := land y0 (VertModel.vstepV sy m0 S x.s a 0), k := x.k + 1, lo := x.lo, hi := x.hi, pre := (VertModel.vstepV sy m0 S x.s a 0).y,
    phi := hiAfter sy m0 S x.s a 0 }

theorem arcNext_mem {x : Arc} (hx : x.s.st ≠ 0) (a : Bool) : arcNext sy m0 S y0 x a ∈ arcSucc sy m0 S y0 x := by
  unfold arcSucc
  have hne : (x.s.st == 0) = false := by simp [hx]
  rw [if_neg (by simp [hne])]
  refine List.mem_map.2 ⟨a, by cases a <;> simp, ?_⟩
  simp only [stepH_eq]
  rfl

/-- **The model's next height before `land` is in the window**: from a state in the air that the search reaches (at a depth `j` with `j + 1 ≤ arcDepth`), the next
height before `land` is below `y0 + d` and the high byte after the step is 1, for both values of A: `arcOK` of the next arc (landed: in the window; in the air: below
`y0`) -/
theorem next_bound (hc : arcCheck sy m0 S y0 d lens = true) {x0 x : Arc} (h0 : x0 ∈ arcStart sy m0 S y0 lens) {j : Nat} (hj : j + 1 ≤ arcDepth)
    (hr : Cert.Reach (arcSucc sy m0 S y0) x0 j x) (hst : x.s.st ≠ 0) (a : Bool) :
    (VertModel.vstepV sy m0 S x.s a 0).y.toNat < y0.toNat + d.toNat ∧ hiAfter sy m0 S x.s a 0 = 1 := by
  have hok := arc_spec hc x0 h0 (j + 1) _ hj (reach_snoc hr (arcNext_mem hst a))
  generalize hR : VertModel.vstepV sy m0 S x.s a 0 = r at hok ⊢
  unfold arcOK arcNext at hok
  rw [hR] at hok
  by_cases hs : (land y0 r).st = 0
  · rw [if_pos (by simp [hs])] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    exact ⟨hok.1.2, hok.2⟩
  · rw [if_neg (by simp [hs]), land_of_air hs] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    have := UInt8.lt_iff_toNat_lt.1 hok.1.2
    exact ⟨by omega, hok.2⟩

/-- **The takeoff's height before `land` is in the window**: `arcOK` of the takeoff's arc, for a speed up to the top -/
theorem start_bound (hc : arcCheck sy m0 S y0 d lens = true) {v : Nat} (hv : v ≤ TopSpeed.top sy) :
    (VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8).y.toNat < y0.toNat + d.toNat := by
  generalize hR : VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8 = r
  have hmem : ({ s := land y0 r, k := 1, lo := (lens[v]!).1, hi := (lens[v]!).2, pre := r.y, phi := hiAfter sy m0 S (ground0 y0) true v.toUInt8 } : Arc) ∈
      arcStart sy m0 S y0 lens := by
    unfold arcStart
    refine List.mem_eraseDups.2 (List.mem_map.2 ⟨v, List.mem_range.2 (by omega), ?_⟩)
    simp only [stepH_eq]
    rw [hR]
  have hok := arc_spec hc _ hmem 0 _ (by unfold arcDepth; omega) (.refl _)
  unfold arcOK at hok
  by_cases hs : (land y0 r).st = 0
  · rw [if_pos (by simp [hs])] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.2
  · rw [if_neg (by simp [hs]), land_of_air hs] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have := UInt8.lt_iff_toNat_lt.1 hok.1.2
    omega

/-- **The landing of a jump of the model, within a horizon `h`.** A sequence of vertical states whose frame `1` is the takeoff's state for the speed `v` (with the height
`pre 1` before `land`), and whose next state is the model's step (A of the frame `a e`) at each frame `e < h` from which every frame since `1` is in the air, when the
model's next height before `land` is in the window (`hstep`): either it lands by the frame `h`, within the two lengths of `v` (the frames from `1` to `n − 1` in the air,
the frame `n` on the ground at `y0` with no vertical speed and no fraction), or the frames from `1` to `h` are in the air and `h` is below the longest length. -/
theorem lands_by (hc : arcCheck sy m0 S y0 d lens = true) {u : Nat → VS} {a : Nat → Bool} {pre ph : Nat → UInt8} {P : Nat → Prop} {v : Nat}
    (hv : v ≤ TopSpeed.top sy) {h : Nat} (hh : 1 ≤ h)
    (h1 : pre 1 = (VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8).y ∧ ph 1 = hiAfter sy m0 S (ground0 y0) true v.toUInt8 ∧
      u 1 = land y0 (VertModel.vstepV sy m0 S (ground0 y0) true v.toUInt8)) (hP : P 1)
    (hstep : ∀ e, 1 ≤ e → e < h → (∀ e', 1 ≤ e' → e' ≤ e → (u e').st ≠ 0) → P e →
      (VertModel.vstepV sy m0 S (u e) (a e) 0).y.toNat < y0.toNat + d.toNat ∧ hiAfter sy m0 S (u e) (a e) 0 = 1 →
      P (e + 1) ∧ pre (e + 1) = (VertModel.vstepV sy m0 S (u e) (a e) 0).y ∧ ph (e + 1) = hiAfter sy m0 S (u e) (a e) 0 ∧
      u (e + 1) = land y0 (VertModel.vstepV sy m0 S (u e) (a e) 0)) :
    (∃ n, 1 ≤ n ∧ n ≤ h ∧ (lens[v]!).1 ≤ n ∧ n ≤ (lens[v]!).2 ∧ (∀ e, 1 ≤ e → e < n → (u e).st ≠ 0) ∧
      (u n).st = 0 ∧ (u n).y = y0 ∧ (u n).vy = 0 ∧ (u n).mf = 0 ∧ P n) ∨
    ((∀ e, 1 ≤ e → e ≤ h → (u e).st ≠ 0) ∧ h < (lens[v]!).2) := by
  have hstart : arcOf u (lens[v]!).1 (lens[v]!).2 pre ph 1 ∈ arcStart sy m0 S y0 lens := by
    unfold arcStart arcOf
    refine List.mem_eraseDups.2 (List.mem_map.2 ⟨v, List.mem_range.2 (by omega), ?_⟩)
    simp only [stepH_eq]
    rw [h1.1, h1.2.1, h1.2.2]
  have hL := lens_le hc v
  -- what `arcOK` says of a reached arc `1 + j`
  have look : ∀ j, j ≤ arcDepth → Cert.Reach (arcSucc sy m0 S y0) (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph 1) j (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + j)) →
      ((u (1 + j)).st = 0 → (lens[v]!).1 ≤ 1 + j ∧ 1 + j ≤ (lens[v]!).2 ∧ (u (1 + j)).y = y0 ∧ (u (1 + j)).vy = 0 ∧ (u (1 + j)).mf = 0) ∧
      ((u (1 + j)).st ≠ 0 → 1 + j < (lens[v]!).2) := by
    intro j hj hr
    have hok := arc_spec hc _ hstart j _ hj hr
    simp only [arcOK, arcOf] at hok
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [if_pos (by simp [hs])] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      exact ⟨hok.1.1.1.1.1.1.1, hok.1.1.1.1.1.1.2, hok.1.1.1.1.1.2, hok.1.1.1.1.2, hok.1.1.1.2⟩
    · rw [if_neg (by simp [hs])] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.1.1.1
  have key : ∀ j, 1 + j ≤ h →
      (∃ n, 1 ≤ n ∧ n ≤ 1 + j ∧ (lens[v]!).1 ≤ n ∧ n ≤ (lens[v]!).2 ∧ (∀ e, 1 ≤ e → e < n → (u e).st ≠ 0) ∧
        (u n).st = 0 ∧ (u n).y = y0 ∧ (u n).vy = 0 ∧ (u n).mf = 0 ∧ P n) ∨
      ((∀ e, 1 ≤ e → e ≤ 1 + j → (u e).st ≠ 0) ∧ 1 + j < (lens[v]!).2 ∧ P (1 + j) ∧
        Cert.Reach (arcSucc sy m0 S y0) (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph 1) j (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨l1, l2⟩ := look 0 (by unfold arcDepth; omega) (.refl _)
      by_cases hs : (u 1).st = 0
      · obtain ⟨f1, f2, f3, f4, f5⟩ := l1 hs
        exact Or.inl ⟨1, Nat.le_refl 1, Nat.le_refl 1, f1, f2, fun e h1 h2 => by omega, hs, f3, f4, f5, hP⟩
      · exact Or.inr ⟨fun e h1 h2 => by rw [show e = 1 by omega]; exact hs, l2 hs, hP, .refl _⟩
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨n, n1, n2, n3⟩ | ⟨hair, hlt, hPj, hr⟩
      · exact Or.inl ⟨n, n1, by omega, n3⟩
      · have hst : (u (1 + j)).st ≠ 0 := hair (1 + j) (by omega) (Nat.le_refl _)
        have hb := next_bound hc hstart (j := j) (by omega) hr hst (a (1 + j))
        obtain ⟨hP', hp, hph, hu⟩ := hstep (1 + j) (by omega) (by omega) (fun e' a1 a2 => hair e' a1 a2) hPj hb
        have hmem : arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + (j + 1)) ∈ arcSucc sy m0 S y0 (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + j)) := by
          have e : arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + (j + 1)) = arcNext sy m0 S y0 (arcOf u (lens[v]!).1 (lens[v]!).2 pre ph (1 + j)) (a (1 + j)) := by
            unfold arcOf arcNext
            rw [show 1 + (j + 1) = 1 + j + 1 by omega, hu, hp, hph]
          rw [e]
          exact arcNext_mem hst _
        have hr' := reach_snoc hr hmem
        obtain ⟨l1, l2⟩ := look (j + 1) (by omega) hr'
        have hP2 : P (1 + (j + 1)) := by rw [show 1 + (j + 1) = 1 + j + 1 by omega]; exact hP'
        by_cases hs : (u (1 + (j + 1))).st = 0
        · obtain ⟨f1, f2, f3, f4, f5⟩ := l1 hs
          exact Or.inl ⟨1 + (j + 1), by omega, Nat.le_refl _, f1, f2, fun e e1 e2 => hair e e1 (by omega), hs, f3, f4, f5, hP2⟩
        · refine Or.inr ⟨fun e e1 e2 => ?_, l2 hs, hP2, hr'⟩
          by_cases he : e ≤ 1 + j
          · exact hair e e1 he
          · rw [show e = 1 + (j + 1) by omega]; exact hs
  rcases key (h - 1) (by omega) with ⟨n, n1, n2, n3⟩ | ⟨hair, hlt, _, _⟩
  · exact Or.inl ⟨n, n1, by omega, n3⟩
  · refine Or.inr ⟨fun e e1 e2 => hair e e1 (by omega), by omega⟩

end

end Smbrta.OpenJump
