import Theorems.PoleLag
/-!
# The pole's tiles: the strict rule of each frame, and the scroll counter on the run

`PoleJoin.Run.parWrap` (round 29) asked, on each frame before the touch's frame that comes to the player's routine, at `UpdScrollVar`: the scroll counter of 32 px
`S` of the frame's start plus the edge's move `Y` is below 256 (`PoleJoin.NoWrapP`). `S` is a value carried over the whole run, so that field was a fact of the run,
not of one frame. Round 30 (`PoleWrap`) proved it from the strict rule of each frame (`PoleWrap.Strict`), `JV` at control and `Y ≤ 3`.

Here the strict rule is proved on real frames, from two conditions on one state each and the walks of `PoleParserEnd`:

* `PoleParserEnd` splits the walks' states at `UpdScrollVar` by the screen buffers' control byte (`PoleParser.ctlPats`). When that byte is not 6, the frame ends
  with `N − 1` tasks left for `N` = 1 ‥ 8, and for `N` = 0 with the counter in 32 ‥ 159 it ends with 7 tasks and the counter less 32 (`PoleParser.frame_six`).
  With the scroll's rule (`ScrollRule.scroll_call`) at the same call of the scroll handler, the edge moved by 0 at `UpdScrollVar`, or the scroll's amount at the
  player's subroutines' call is in 1 ‥ 128 and the edge moved by at most that amount (`PoleParser.frame_sixA`).
* `step_strict`: a frame in control that comes to the player's routine follows the weak rule, keeps the column below 16 and keeps `JV` (`N ≤ 7 ∧ S + 3·N < 32`),
  when at `UpdScrollVar` the control byte is not 6 and at the player's subroutines' call the amount, when in 1 ‥ 128, is at most 3. (`strict_frame`: the same
  `JV` step from the edge's move of at most 3 px at each `UpdScrollVar`.)
* `invJ_onFrames`: on the frames of a run up to the touch's frame, the parser's invariant, the column below 16 and `JV` hold at every frame's start, by one induction
  (`NoWrap` at the frame's `UpdScrollVar` now comes from `JV` of its start: `noWrap_of_jv`).
* `jv₀`: `JV` at control above ground, from the rows of the change out of the side pipe (the check `jvCheckK`).
* `noWrapP_onFrames`: the statement of the old field `parWrap`, from `JV` and an edge's move of at most 3 px at every `UpdScrollVar`.

What is not proved here: that the control byte is not 6 at `UpdScrollVar` (the code sets it to 6 when he takes a coin, `RemoveCoin_Axe`), and that the scroll's
amount is at most 3 when it is in 1 ‥ 128. The first was the field `PoleJoin.Run.ctlU` (round 35: a theorem, `PoleJoin.Run.ctl6`, by the walk of `PoleCoin`); the second is the theorem `PoleParserRun.amount_run`, from part e's
reading of each counted frame. Measured by `pole-keep parser`. Round 32 (`PoleLate`): `step_strict` and `invJ_onFrames` ask the control byte not 6 only where
the parser is late at `UpdScrollVar` (`S + 3·N ≥ 32`); else a frame with the control byte 6 keeps `JV` too (`PoleLate.jv_weak`). Round 33 (`PoleLag`):
`step_strict`, `invJ_onFrames` and `ruleW_onFrames` carry the weaker `PoleLag.JY` (`N ≤ 7 ∧ S + 3·N < 157`), which is all that no wrap and the strict walks need
(`noWrap_of_jy`), so the control byte is asked not 6 only where `S + 3·N ≥ 157` at `UpdScrollVar`.

There is no game data in this file. Page: `1-1/f-6-17-12-PoleStrict.md`.
-/

namespace Smbrta.PoleStrict

open PoleParser PoleWrap
open TaintRun (AS Sim Env)
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-! ## One frame -/

theorem task_of_col {w : UInt8} (h : vCol.contains w = true) : vTask.contains w = true := by
  have h' : w = 1 ∨ w = 5 := by simpa [vCol] using h
  rcases h' with rfl | rfl <;> decide

theorem task_of_six {w : UInt8} (h : vSix.contains w = true) : vTask.contains w = true := by
  have h' : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by simpa [vSix] using h
  rcases h' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`NoWrap` from `JV` at the frame's start**, when the edge moved by at most 3 px and is below 65,280 px at the start -/
theorem noWrap_of_jv {m u : Machine} (hJ : JV (valsOf (places sy m0) m))
    (hy : ∀ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 → Y.toNat ≤ 3)
    (he : edgeOf (places sy m0) m < 65280) : NoWrap sy m0 m u := by
  intro Y hY
  have h1 := hy Y hY
  have h2 := s_lt hJ
  have es : (valsOf (places sy m0) m).s = (m.ram.get! (placesS sy m0).frac).toNat := rfl
  have el : edgeOf (places sy m0) m = ScrollRule.left16 (placesS sy m0) m := rfl
  exact ⟨by omega, by omega⟩

/-- **`NoWrap` from `JY` at the frame's start** (round 33, `PoleLag`): the counter below 157, the edge moved by at most 3 px, the edge below 65,280 px -/
theorem noWrap_of_jy {m u : Machine} (hJ : PoleLag.JY (valsOf (places sy m0) m))
    (hy : ∀ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 → Y.toNat ≤ 3)
    (he : edgeOf (places sy m0) m < 65280) : NoWrap sy m0 m u := by
  intro Y hY
  have h1 := hy Y hY
  have h2 := PoleLag.s_lt hJ
  have es : (valsOf (places sy m0) m).s = (m.ram.get! (placesS sy m0).frac).toNat := rfl
  have el : edgeOf (places sy m0) m = ScrollRule.left16 (placesS sy m0) m := rfl
  exact ⟨by omega, by omega⟩

/-- **A frame by the strict rule keeps `JV`**: a frame in control that comes to the player's routine, with the conditions of `PoleParser.frame_six`, the control
byte not 6 at `UpdScrollVar` (`hk6`) and the edge moved by at most 3 px there (`hy`), and `JV` at its start -/
theorem strict_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hk6 : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → (trace m i k).ram.get! (kIdx sy m0) ≠ 6)
    (hy : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → ∀ Y : UInt8,
      ScrollRule.left16 (placesS sy m0) (trace m i k) = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 → Y.toNat ≤ 3)
    (hJ : JV (valsOf (places sy m0) m)) :
    JV (valsOf (places sy m0) (frame m i)) := by
  obtain ⟨k₂, hq2, hf2, hK, hS, hSix, hCol, hZero, hT1, hT2⟩ := frame_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  have h6 := hk6 k₂ hq2 hf2
  have hnd := nodup_of_check he
  rw [pE_eq] at hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, _, _, _, _⟩, ⟨s1, s2, _, _⟩, _⟩ := hnd
  have hn : ∀ x : Machine, (valsOf (places sy m0) x).n = (x.ram.get! (nI sy m0)).toNat := fun _ => rfl
  have hsv : ∀ x : Machine, (valsOf (places sy m0) x).s = (x.ram.get! (sIdx sy m0)).toNat := fun _ => rfl
  have esI : (placesS sy m0).frac = sIdx sy m0 := rfl
  obtain ⟨hJ1, hJ2⟩ := hJ
  rw [hn] at hJ1
  rw [hn, hsv] at hJ2
  -- the counter at `UpdScrollVar`: that of the start, plus at most 3
  have hSb : ((m.ram.get! (sIdx sy m0)).toNat ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat) ∧
      (((trace m i k₂).ram.get! (sIdx sy m0)).toNat ≤ (m.ram.get! (sIdx sy m0)).toNat + 3) := by
    rcases hS with ⟨_, h2⟩ | ⟨Y, h1, h2⟩
    · rw [esI] at h2
      rw [h2]
      omega
    · have hY := hy k₂ hq2 hf2 Y h1
      rw [esI] at h2
      rw [h2]
      have : (m.ram.get! (sIdx sy m0)).toNat + Y.toNat < 256 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  have hs8 : ((frame m i).ram.get! (nI sy m0)).toNat ≤ 7 → ((frame m i).ram.get! (sIdx sy m0)).toNat + 3 * ((frame m i).ram.get! (nI sy m0)).toNat < 32 →
      JV (valsOf (places sy m0) (frame m i)) := fun a b => ⟨by rw [hn]; exact a, by rw [hn, hsv]; exact b⟩
  have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hK _ nI_memK
  rcases n_cases (w := m.ram.get! (nI sy m0)) (by omega) with hz | hcol | hsix
  · -- no task left: a new column starts when the counter passed 32
    by_cases h32 : 32 ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat
    · obtain ⟨a1, a2⟩ := hT2 h6 hz h32 (by omega)
      have a3 : ((trace m i k₂).ram.get! (sIdx sy m0) - 32).toNat = ((trace m i k₂).ram.get! (sIdx sy m0)).toNat - 32 :=
        UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.2 (by have : (32 : UInt8).toNat = 32 := rfl; rw [this]; exact h32))
      have hz' : (m.ram.get! (nI sy m0)).toNat = 0 := by rw [hz]; rfl
      refine hs8 (by rw [a1]; decide) ?_
      rw [a1, a2, a3]
      have : (7 : UInt8).toNat = 7 := rfl
      rw [this]
      omega
    · rcases (hZero hz).2 with ⟨a1, a2⟩ | ⟨a1, _⟩
      · refine hs8 (by rw [a1]; decide) ?_
        rw [a1, a2]
        have : (0 : UInt8).toNat = 0 := rfl
        rw [this]
        omega
      · exact absurd a1 h32
  · -- the column's step
    obtain ⟨f1, f2, _⟩ := col_facts hcol
    have a1 := hT1 h6 (task_of_col hcol)
    have a2 : (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) :=
      (hCol hcol).1 _ (by rw [pE_eq]; simp) (Ne.symm n1) s1 s2
    refine hs8 ?_ ?_
    · rw [a1, f2]; omega
    · rw [a1, f2, a2]; omega
  · -- one of the other tasks
    obtain ⟨f1, f2, _⟩ := six_facts hsix
    have a1 := hT1 h6 (task_of_six hsix)
    have a2 : (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) :=
      (hSix hsix).1 _ (by rw [pE_eq]; simp) (Ne.symm n1)
    refine hs8 ?_ ?_
    · rw [a1, f2]; omega
    · rw [a1, f2, a2]; omega

/-- **One frame by the strict rule, with the scroll's amount** (round 31): the conditions of `PoleParser.step_frame` with the check of the scroll's rule (`hsc`), at
`UpdScrollVar` the control byte not 6 or the counter of 32 px plus 3·N below 32 (`hk6`, round 32: before, the control byte not 6), and at the player's subroutines'
call the scroll's amount, when it is in 1 ‥ 128, at most 3 (`hA`); with the
invariant, the column below 16, the edge below `65280 − L` px and `JV` at its start, the frame follows the weak rule, keeps the column below 16 and keeps `JV`.
No wrap is needed only at the `UpdScrollVar` after the scroll handler, where the edge moved by 0 or by at most the amount (`PoleParser.frame_sixA`). Round 33
(`PoleLag`): `PoleLag.JY` (`N ≤ 7 ∧ S + 3·N < 157`) in place of `JV` at the start and at the end, and `hk6` with 157 in place of 32 -/
theorem step_strict (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hP : ∀ j, FrameKeep.CleanK (guardPar sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hk6 : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → (trace m i k).ram.get! (kIdx sy m0) ≠ 6 ∨
      ((trace m i k).ram.get! (sIdx sy m0)).toNat + 3 * ((trace m i k).ram.get! (nI sy m0)).toNat < 157)
    (hA : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → (trace m i k).frame = m.frame →
      ScrollRule.xOK (ScrollRule.amountOf (ScrollRule.places sy m0) (trace m i k)) = true →
      (ScrollRule.amountOf (ScrollRule.places sy m0) (trace m i k)).toNat ≤ 3)
    {L : Nat} (hI : Inv (places sy m0) L m) (hC : ColOK sy m0 m) (hE : edgeOf (places sy m0) m + L < 65280) (hJ : PoleLag.JY (valsOf (places sy m0) m)) :
    (RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) ∧ ColOK sy m0 (frame m i)) ∧ PoleLag.JY (valsOf (places sy m0) (frame m i)) := by
  have hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_weak (hP n)
  have hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j) := fun x hx j => cleanH_of_par hx (hP j)
  have hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j) := fun x hx j => cleanN_of_par hx (hP j)
  obtain ⟨k₂, hq2, hf2, hK, hS, hSix, hCol, hZero, hT1, hT2, kq, hkq0, hkq1, hkq2, hYA⟩ :=
    frame_sixA hc hq hqe he hs hsc hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  have hY3 : ∀ Y : UInt8, ScrollRule.left16 (placesS sy m0) (trace m i k₂) = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 → Y.toNat ≤ 3 := by
    intro Y hY
    rcases hYA Y hY with h | ⟨hx1, hle⟩
    · omega
    · have := hA kq (Nat.le_of_lt hkq0) hkq1 hkq2 hx1
      omega
  have hw : NoWrap sy m0 m (trace m i k₂) := noWrap_of_jy hJ hY3 (by omega)
  have h8 : (m.ram.get! (nI sy m0)).toNat ≤ 8 := hI.1
  have hp255 := page_of_inv hI hE
  have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hK _ nI_memK
  have hcK : (trace m i k₂).ram.get! (cIdx sy m0) = m.ram.get! (cIdx sy m0) :=
    hK _ (List.mem_map.2 ⟨(places sy m0).col, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hgK : (trace m i k₂).ram.get! (gIdx sy m0) = m.ram.get! (gIdx sy m0) :=
    hK _ (List.mem_map.2 ⟨(places sy m0).page, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  have hC' : (m.ram.get! (cIdx sy m0)).toNat < 16 := hC
  have hRule : RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
    rcases n_cases h8 with hz | hcol | hsix
    · obtain ⟨hE1, hE2⟩ := hZero hz
      exact ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS hw, parseW_zero (nodup_of_check he) (by rw [hn2]; exact hz) hE1 hE2⟩
    · obtain ⟨hE1, hE2⟩ := hCol hcol
      exact ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS hw,
        parseW_col (nodup_of_check he) (by rw [hn2]; exact hcol) hE1 (by rw [hcK]; exact hC') (by rw [hgK]; exact hp255) (hE2 hC' hp255)⟩
    · obtain ⟨hE1, hE2⟩ := hSix hsix
      refine ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS hw, parseW_six (nodup_of_check he) (by rw [hn2]; exact hsix) hE1 ?_⟩
      rw [hn2]
      exact hE2
  have hColE := col_frame hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp h8 hC' hp255
  refine ⟨⟨hRule, hColE⟩, ?_⟩
  -- `JV` at the end, as in `strict_frame`, with the move at `k₂` from the amount
  have hnd := nodup_of_check he
  rw [pE_eq] at hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, _, _, _, _⟩, ⟨s1, s2, _, _⟩, _⟩ := hnd
  have hn : ∀ x : Machine, (valsOf (places sy m0) x).n = (x.ram.get! (nI sy m0)).toNat := fun _ => rfl
  have hsv : ∀ x : Machine, (valsOf (places sy m0) x).s = (x.ram.get! (sIdx sy m0)).toNat := fun _ => rfl
  have esI : (placesS sy m0).frac = sIdx sy m0 := rfl
  obtain ⟨hJ1, hJ2⟩ := hJ
  rw [hn] at hJ1
  rw [hn, hsv] at hJ2
  have hSb : ((m.ram.get! (sIdx sy m0)).toNat ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat) ∧
      (((trace m i k₂).ram.get! (sIdx sy m0)).toNat ≤ (m.ram.get! (sIdx sy m0)).toNat + 3) := by
    rcases hS with ⟨_, h2⟩ | ⟨Y, h1, h2⟩
    · rw [esI] at h2
      rw [h2]
      omega
    · have hY := hY3 Y h1
      rw [esI] at h2
      rw [h2]
      have : (m.ram.get! (sIdx sy m0)).toNat + Y.toNat < 256 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  have hs8 : ((frame m i).ram.get! (nI sy m0)).toNat ≤ 7 → ((frame m i).ram.get! (sIdx sy m0)).toNat + 3 * ((frame m i).ram.get! (nI sy m0)).toNat < 157 →
      PoleLag.JY (valsOf (places sy m0) (frame m i)) := fun a b => ⟨by rw [hn]; exact a, by rw [hn, hsv]; exact b⟩
  rcases hk6 k₂ hq2 hf2 with h6 | hlate
  · -- the control byte is not 6: the strict forms
    rcases n_cases (w := m.ram.get! (nI sy m0)) (by omega) with hz | hcol | hsix
    · by_cases h32 : 32 ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat
      · obtain ⟨a1, a2⟩ := hT2 h6 hz h32 (by omega)
        have a3 : ((trace m i k₂).ram.get! (sIdx sy m0) - 32).toNat = ((trace m i k₂).ram.get! (sIdx sy m0)).toNat - 32 :=
          UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.2 (by have : (32 : UInt8).toNat = 32 := rfl; rw [this]; exact h32))
        have hz' : (m.ram.get! (nI sy m0)).toNat = 0 := by rw [hz]; rfl
        refine hs8 (by rw [a1]; decide) ?_
        rw [a1, a2, a3]
        have : (7 : UInt8).toNat = 7 := rfl
        rw [this]
        omega
      · rcases (hZero hz).2 with ⟨a1, a2⟩ | ⟨a1, _⟩
        · refine hs8 (by rw [a1]; decide) ?_
          rw [a1, a2]
          have : (0 : UInt8).toNat = 0 := rfl
          rw [this]
          omega
        · exact absurd a1 h32
    · obtain ⟨f1, f2, _⟩ := col_facts hcol
      have a1 := hT1 h6 (task_of_col hcol)
      have a2 : (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) :=
        (hCol hcol).1 _ (by rw [pE_eq]; simp) (Ne.symm n1) s1 s2
      refine hs8 ?_ ?_
      · rw [a1, f2]; omega
      · rw [a1, f2, a2]; omega
    · obtain ⟨f1, f2, _⟩ := six_facts hsix
      have a1 := hT1 h6 (task_of_six hsix)
      have a2 : (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) :=
        (hSix hsix).1 _ (by rw [pE_eq]; simp) (Ne.symm n1)
      refine hs8 ?_ ?_
      · rw [a1, f2]; omega
      · rw [a1, f2, a2]; omega
  · -- the lag at `UpdScrollVar` below 157 (round 33, `PoleLag`; round 32 had 32, `PoleLate`): the weak forms keep `N` or take one off and keep the counter,
    -- or start a new column, which sets `N` to 7 and takes 32 off the counter
    rw [hn2] at hlate
    by_cases hz0 : m.ram.get! (nI sy m0) = 0
    · rcases (hZero hz0).2 with ⟨a1, a2⟩ | ⟨b1, b2, b3, b4⟩
      · obtain ⟨c1, c2⟩ := PoleLag.jy_weak (n' := ((frame m i).ram.get! (nI sy m0)).toNat) hJ1 hlate (Nat.le_of_eq (by rw [a1, hz0])) (congrArg UInt8.toNat a2)
        exact hs8 c1 c2
      · have a3 : ((trace m i k₂).ram.get! (sIdx sy m0) - 32).toNat = ((trace m i k₂).ram.get! (sIdx sy m0)).toNat - 32 :=
          UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.2 (by have : (32 : UInt8).toNat = 32 := rfl; rw [this]; exact b1))
        obtain ⟨c1, c2⟩ := PoleLag.jy_col (n' := ((frame m i).ram.get! (nI sy m0)).toNat) (s' := ((frame m i).ram.get! (sIdx sy m0)).toNat) b1 b2 (congrArg UInt8.toNat b3) (by rw [b4, a3])
        exact hs8 c1 c2
    · have hw : ((frame m i).ram.get! (nI sy m0)).toNat ≤ (m.ram.get! (nI sy m0)).toNat ∧
          (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) := by
        rcases n_cases (w := m.ram.get! (nI sy m0)) (by omega) with hz | hcol | hsix
        · exact absurd hz hz0
        · obtain ⟨_, f2, _⟩ := col_facts hcol
          have hcu : ((trace m i k₂).ram.get! (cIdx sy m0)).toNat < 16 := by rw [hcK]; exact hC'
          refine ⟨?_, (hCol hcol).1 _ (by rw [pE_eq]; simp) (Ne.symm n1) s1 s2⟩
          rcases PoleLate.colEnd_n ((hCol hcol).2 hC' hp255) hcu with e | e <;> rw [e, hn2]
          · exact Nat.le_refl _
          · rw [f2]; omega
        · obtain ⟨_, f2, _⟩ := six_facts hsix
          refine ⟨?_, (hSix hsix).1 _ (by rw [pE_eq]; simp) (Ne.symm n1)⟩
          rcases (hSix hsix).2 with e | e <;> rw [e]
          · exact Nat.le_refl _
          · rw [f2]; omega
      obtain ⟨a1, a2⟩ := PoleLag.jy_weak hJ1 hlate hw.1 (congrArg UInt8.toNat hw.2)
      exact hs8 a1 a2

/-! ## On the frames of a run -/

/-- **The invariant, the column and `JV` (round 33: `PoleLag.JY`) at every frame's start up to the touch's frame**, on the frames of a run: as `PoleParser.inv_onFrames`, with `JV` at
the first frame (`hJ0`), the check of the scroll's rule (`hsc`), and in place of no wrap on each frame that comes to the player's routine: at `UpdScrollVar` the
control byte not 6 or the counter of 32 px plus 3·N below 32 (`hk6`, round 32), and at the player's subroutines' call the scroll's amount at most 3 when it is in
1 ‥ 128 (`hA`) (`step_strict`) -/
theorem invJ_onFrames {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq)
    (hkc : FrameKeep.keepCheckOf sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (hw0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) {L : Nat}
    (h0 : Inv (places sy m0) L (K.all 0) ∧ ColOK sy m0 (K.all 0)) (hJ0 : PoleLag.JY (valsOf (places sy m0) (K.all 0)))
    (hI : ∀ n, n + 1 < K.ix g → ∀ k, FrameKeep.CleanK (guardPI sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k))
    (hv : ∀ n, n + 1 < K.ix g → CtrlKeep.AreaOK sy v (K.all n))
    (hp : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      (∀ j, j < n₀ → (trace (K.all n) (K.inp n) j).pc ≠ sy.PlayerCtrlRoutine) →
      ∀ k, n₀ ≤ k → (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace (K.all n) (K.inp n) j).frame = (K.all n).frame →
      EdgeStep.cutPos sy m0 (trace (K.all n) (K.inp n) j).pc = false)
    (hk6 : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      (trace (K.all n) (K.inp n) k).ram.get! (kIdx sy m0) ≠ 6 ∨
        ((trace (K.all n) (K.inp n) k).ram.get! (sIdx sy m0)).toNat + 3 * ((trace (K.all n) (K.inp n) k).ram.get! (nI sy m0)).toNat < 157)
    (hA : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, n₀ ≤ k → (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      ScrollRule.xOK (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k)) = true →
      (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k)).toNat ≤ 3)
    (hE : ∀ n, n + 1 < K.ix g → edgeOf (places sy m0) (K.all n) + L < 65280) :
    ∀ n, n < K.ix g → (Inv (places sy m0) L (K.all n) ∧ ColOK sy m0 (K.all n)) ∧ PoleLag.JY (valsOf (places sy m0) (K.all n)) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨h0, hJ0⟩
  | succ n ih =>
    intro hn
    obtain ⟨⟨hIn, hCn⟩, hJn⟩ := ih (by omega)
    have hst := (K.all_start hkc hs0 hw0 n (by omega)).1
    have hix : K.ix g = FrameKeep.ixOf sy m0 S a K.top g := rfl
    have hcE := K.cleanE n (by omega)
    have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
      fun k => FrameKeep.cleanK_of_E (hcE k)
    have hclK : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
      fun k => FrameKeep.cleanK_of_F (hclF k)
    have hP : ∀ k, FrameKeep.CleanK (guardPar sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) := fun k => cleanPar_of (hcE k) (hI n hn k)
    have ht : ∀ k, (trace (K.all n) (K.inp n) k).pc ≠ sy.EndlessLoop → (trace (K.all n) (K.inp n) k).fdot ≤ dotsPerFrame - 64 := fun k hk => (hcE k).time hk
    have hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (AfterKeep.guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) j) :=
      fun x hx j => cleanH_of_par hx (hP j)
    have hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) j) :=
      fun x hx j => cleanN_of_par hx (hP j)
    rw [K.next n]
    rcases arrival_cases hq hst hclK with ⟨n₀, a1, a2, a3⟩ | hno
    · have r := step_strict hc hq hqe he hs hsc hidle hst hP (K.noStore n hn) (hv n hn) a1 a2 a3 ht (hp n hn n₀ a1 a2 a3) (hk6 n hn n₀ a1 a2)
        (hA n hn n₀ a1 a2) hIn hCn (hE n hn) hJn
      exact ⟨⟨(invV_iff (P := places sy m0) (m := frame (K.all n) (K.inp n))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := K.all n)).1 hIn) r.1.1), r.1.2⟩, r.2⟩
    · have r := step_noCut hq hqe hst hclK hno hCn
      refine ⟨⟨(invV_iff (P := places sy m0) (m := frame (K.all n) (K.inp n))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := K.all n)).1 hIn) r.1), r.2⟩, ?_⟩
      have A := keep_noCutP hq hst hclK hno
      have B := EdgeStep.keep_noCut hqe hst hclK hno
      have e : valsOf (places sy m0) (frame (K.all n) (K.inp n)) = valsOf (places sy m0) (K.all n) := by
        refine vals_eq ?_ ?_ ?_ ?_ ?_ ?_
        · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
        · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
        · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
        · exact A _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩)
        · exact B _ List.mem_cons_self
        · exact B _ (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [e]
      exact hJn

/-- the parser's column does not go back over a frame that follows the weak rule -/
theorem col_of_ruleW {a b : Vals} (h : RuleW a b) : a.col ≤ b.col := by
  obtain ⟨c, ⟨y, _, e2, _, _⟩, _, hp⟩ := h
  rcases hp with ⟨_, _, h3⟩ | hst
  · omega
  · unfold Step at hst
    split at hst
    · obtain ⟨_, _, _, _, h3⟩ := hst
      omega
    · obtain ⟨_, _, h3⟩ := hst
      split at h3 <;> omega

/-- **The weak rule on every frame up to the touch's frame** (round 33), under the conditions of `invJ_onFrames`: its frame step, with the invariant, the column
and `JV` of the frame's start that `invJ_onFrames` gives (`step_strict` on a frame that comes to the player's routine, `PoleParser.step_noCut` on the others) -/
theorem ruleW_onFrames {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq)
    (hkc : FrameKeep.keepCheckOf sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (hw0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hsc : ScrollRule.check sy m0 = true)
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) {L : Nat}
    (h0 : Inv (places sy m0) L (K.all 0) ∧ ColOK sy m0 (K.all 0)) (hJ0 : PoleLag.JY (valsOf (places sy m0) (K.all 0)))
    (hI : ∀ n, n + 1 < K.ix g → ∀ k, FrameKeep.CleanK (guardPI sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k))
    (hv : ∀ n, n + 1 < K.ix g → CtrlKeep.AreaOK sy v (K.all n))
    (hp : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      (∀ j, j < n₀ → (trace (K.all n) (K.inp n) j).pc ≠ sy.PlayerCtrlRoutine) →
      ∀ k, n₀ ≤ k → (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace (K.all n) (K.inp n) j).frame = (K.all n).frame →
      EdgeStep.cutPos sy m0 (trace (K.all n) (K.inp n) j).pc = false)
    (hk6 : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      (trace (K.all n) (K.inp n) k).ram.get! (kIdx sy m0) ≠ 6 ∨
        ((trace (K.all n) (K.inp n) k).ram.get! (sIdx sy m0)).toNat + 3 * ((trace (K.all n) (K.inp n) k).ram.get! (nI sy m0)).toNat < 157)
    (hA : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, n₀ ≤ k → (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      ScrollRule.xOK (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k)) = true →
      (ScrollRule.amountOf (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k)).toNat ≤ 3)
    (hE : ∀ n, n + 1 < K.ix g → edgeOf (places sy m0) (K.all n) + L < 65280) :
    ∀ n, n + 1 < K.ix g → RuleW (valsOf (places sy m0) (K.all n)) (valsOf (places sy m0) (K.all (n + 1))) := by
  intro n hn
  obtain ⟨⟨hIn, hCn⟩, hJn⟩ := invJ_onFrames K hkc hs0 hw0 hc hq hqe he hs hsc hidle h0 hJ0 hI hv hp hk6 hA hE n (by omega)
  have hst := (K.all_start hkc hs0 hw0 n (by omega)).1
  have hix : K.ix g = FrameKeep.ixOf sy m0 S a K.top g := rfl
  have hcE := K.cleanE n (by omega)
  have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
    fun k => FrameKeep.cleanK_of_E (hcE k)
  have hclK : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
    fun k => FrameKeep.cleanK_of_F (hclF k)
  have hP : ∀ k, FrameKeep.CleanK (guardPar sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) := fun k => cleanPar_of (hcE k) (hI n hn k)
  have ht : ∀ k, (trace (K.all n) (K.inp n) k).pc ≠ sy.EndlessLoop → (trace (K.all n) (K.inp n) k).fdot ≤ dotsPerFrame - 64 := fun k hk => (hcE k).time hk
  rw [K.next n]
  rcases arrival_cases hq hst hclK with ⟨n₀, a1, a2, a3⟩ | hno
  · exact (step_strict hc hq hqe he hs hsc hidle hst hP (K.noStore n hn) (hv n hn) a1 a2 a3 ht (hp n hn n₀ a1 a2 a3) (hk6 n hn n₀ a1 a2)
      (hA n hn n₀ a1 a2) hIn hCn (hE n hn) hJn).1.1
  · exact (step_noCut hq hqe hst hclK hno hCn).1

/-- **The statement of the old field `parWrap`** on the frames of a run: `JV` at each frame's start (`invJ_onFrames`) and the edge's move of at most 3 px give
`PoleJoin.NoWrapP` (`PoleWrap.noWrapP_of`) -/
theorem noWrapP_onFrames {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq)
    (hJ : ∀ n, n < K.ix g → JV (valsOf (places sy m0) (K.all n)))
    (hy : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      ∀ Y : UInt8, ScrollRule.left16 (ScrollRule.places sy m0) (trace (K.all n) (K.inp n) k) =
        (ScrollRule.left16 (ScrollRule.places sy m0) (K.all n) + Y.toNat) % 65536 → Y.toNat ≤ 3) :
    ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      PoleJoin.NoWrapP sy m0 (K.all n) (trace (K.all n) (K.inp n) k) :=
  fun n hn n₀ a1 a2 k hk hf => noWrapP_of (hJ n (by omega)) (hy n hn n₀ a1 a2 k hk hf)

/-! ## `JV` at control, from the rows of the change -/

/-- a state of a row: it knows the bytes of control, and if it has control, it knows `N` and the counter and they meet `JV` -/
def rowJV (sy : Syms) (P : Places) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) &&
    (!controllable sy (SideChangeEnd.mOf S) || (SideChangeEnd.knowsAd S P.task && SideChangeEnd.knowsAd S P.s32 &&
      decide ((peek (SideChangeEnd.mOf S) P.task).toNat ≤ 7) && decide ((peek (SideChangeEnd.mOf S) P.s32).toNat + 3 * (peek (SideChangeEnd.mOf S) P.task).toNat < 32)))

/-- every state of the rows -/
def rowsJV (sy : Syms) (P : Places) (l : List SideChangeEnd.Row) : Bool := l.all fun r => r.R.all (rowJV sy P)

/-- **The check on the ROM**: in every state with control of the rows of the change out of the side pipe, `JV` holds -/
def jvCheckK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  rowsJV sy (places sy m0) ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row))

theorem jv_of_state {E : Env} {F : Nat × UInt8} {P : Places} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowJV sy P S = true)
    (h : controllable sy m = true) : JV (valsOf P m) := by
  simp only [rowJV, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨⟨⟨k1, k2⟩, h2⟩, h3⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · have e1 := peek_of_known hs k1
    have e2 := peek_of_known hs k2
    simp only [decide_eq_true_eq] at h2 h3
    refine ⟨?_, ?_⟩
    · show (peek m P.task).toNat ≤ 7
      rw [e1]
      exact h2
    · show (peek m P.s32).toNat + 3 * (peek m P.task).toNat < 32
      rw [e1, e2]
      exact h3

theorem jv_of_invL {C : SideChangeEnd.Ctx} {P : Places} :
    ∀ {l : List SideChangeEnd.Row}, rowsJV sy P l = true → ∀ {m : Machine}, SideChangeEnd.InvL C l m → controllable sy m = true → JV (valsOf P m)
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [rowsJV, List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact jv_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact jv_of_invL hl.2 h hc

section
variable {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine}

/-- **The machine at control has `JV`**, on a real run of the change, from the rows of `SideChangeSound` (the run of `SidePause`) -/
theorem EndRunQ.jv (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : jvCheckK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    JV (valsOf (places sy m0) (R'.seq R'.b)) :=
  jv_of_invL hk (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

end

section
open Route

variable {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **`JV` at control above ground**, on the real machines: from the last rows of the change, under the same conditions as `PoleParser.inv₀`. `hm` is the check on
the ROM. -/
theorem jv₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : jvCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    JV (valsOf (places sy m0) (R.pole.seq 0)) := by
  rw [R.atCtl]
  exact EndRunQ.jv hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

end

end Smbrta.PoleStrict
