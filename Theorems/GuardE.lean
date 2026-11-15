import Theorems.AfterKeep

/-!
# The walks after the player's routine under `CleanK` of `FrameKeep.guardE`

Each instruction of the frames of a run meets `CleanK` of `FrameKeep.guardE` (the field `cleanE` of `FrameKeep.Frames`): no store through an index or a pointer writes the
bytes of `FrameKeep.guardF`, nor A and B, A and B of the frame before, the moving direction, the running speed or the stored speed (`FrameKeep.spareE`), nor the
player's collision bits (`FrameKeep.collE`, used by `CollKeep.cleanC_of`), nor the player's speed (`FrameKeep.speedE`, used by `CollideKeep.cleanV_of`), nor three
vertical bytes (`FrameKeep.vertE`, used by `VertKeep.cleanK_of_kI`), but the player's own store of the fraction (`CleanK` does not ask that store: the walks know its
target).

`PrevKeep.prev_end` and `AfterKeep.keepH` ask `CleanK` of `FrameKeep.guardF` and, of every instruction, `SpareAB` or `SpareH`: no store through an index or a pointer
writes these bytes. They use both only to give `CleanK` of the guard of their walks (`PrevKeep.guardAB`, `AfterKeep.guardH`), which does not ask the player's own store
of the fraction either. `CleanK` of `guardE` gives `CleanK` of those guards directly (`cleanAB_of_E`, `cleanH_of_E`). So `prev_endE` and `keepHE` are `prev_end` and
`keepH` with the one condition `CleanK` of `guardE`: the same walks, the same checks on the ROM, the same proofs. The field `spareE` of the frames above ground is gone.

There is no game data in this file. Page: `1-1/f-6-21-GuardE.md`.
-/

namespace Smbrta.GuardE

open TaintRun
open PipeEntryRule (trace)
open PipeTransition (frame)

section
variable {sy : Syms} {m0 : Machine}

/-- `CleanK` of `guardE` gives `CleanK` of the guard of the walk of `PrevKeep`: the bytes of `PrevKeep.abP` are in `FrameKeep.spareE` -/
theorem cleanAB_of_E {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) : FrameKeep.CleanK (PrevKeep.guardAB sy m0) q m := by
  refine FrameKeep.cleanK_sub h (fun x hx => ?_) rfl rfl rfl rfl
  simp only [PrevKeep.guardAB, FrameKeep.guardE, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · left
    simp only [PrevKeep.abP, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [FrameKeep.spareE, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl <;> simp
  · exact Or.inr hx

/-- `CleanK` of `guardE` gives `CleanK` of the guard of the second walk of `AfterKeep` for a byte of `AfterKeep.hI`: these bytes are in `FrameKeep.spareE` -/
theorem cleanH_of_E {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ AfterKeep.hI sy) (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) :
    FrameKeep.CleanK (AfterKeep.guardH sy m0 x) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [AfterKeep.guardH, FrameKeep.guardE, List.mem_append] at hy ⊢
  rcases hy with hy | hy
  · left
    simp only [List.mem_singleton] at hy
    subst hy
    simp only [AfterKeep.hI, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [FrameKeep.spareE, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl <;> simp
  · exact Or.inr hy

/-- **The bytes of `AfterKeep.eI` are those of `FrameKeep.spareE`** -/
theorem eI_eq : AfterKeep.eI sy = FrameKeep.spareE sy := rfl

/-- **`CleanK` of `guardE` gives `AfterKeep.SpareE`** on every instruction but the player's own store of the fraction (the instruction at the store of the move routine
with the index 0), where `CleanK` asks nothing -/
theorem spareE_of {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hq : ¬ (m.pc = q ∧ m.x = 0)) : AfterKeep.SpareE sy m := by
  intro t ht hlt hm
  rcases h.store t ht hq with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (eI_eq (sy := sy) ▸ hm)))))
  · have a1 := UInt16.lt_iff_toNat_lt.1 hlt
    have a2 := UInt16.le_iff_toNat_le.1 h1
    simp at a1 a2
    omega

open PrevKeep in
/-- **A frame in control keeps bit 7 of A and B of the frame before equal to that of A and B** (`PrevKeep.prev_end`), with the one condition `CleanK` of `guardE` on
each instruction. The proof is that of `prev_end`, with the walk's guard from `cleanAB_of_E`. -/
theorem prev_endE (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : prevCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) (h : PrevOK sy m) : PrevOK sy (frame m i) := by
  obtain ⟨hp1, hp2, hp3⟩ := prevCheck_parts hp
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (FrameKeep.cleanK_of_E (hcl n))
  have hclA : ∀ n, FrameKeep.CleanK (guardAB sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => cleanAB_of_E (hcl n)
  rcases CtrlKeep.cut_or_end2 (C := cfgPB sy m0 v q (prevCfg sy m0 v false cuts) (prevCfg sy m0 v true cuts)) hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hB2' : afterPB sy m0 v (prevCfg sy m0 v false cuts) (prevCfg sy m0 v true cuts) B = true := hB2
    simp only [afterPB, Bool.and_eq_true] at hB2'
    replace hB2 := hB2'
    have hA : ∀ b : Bool, (trace m i k).ram.get! (savedI sy) &&& 0x80 = CtrlKeep.bit7 b &&& 0x80 → FrameKeep.Watched (CtrlKeep.valP sy v b) (trace m i k) := by
      intro b hb w hw
      simp only [CtrlKeep.valP, CtrlKeep.valA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · show (trace m i k).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
      · exact hb
    have hb := bit7_eq ((trace m i k).ram.get! (savedI sy))
    generalize ((trace m i k).ram.get! (savedI sy) &&& 0x80 != 0) = b at hb
    have hhs : Sim (CtrlKeep.envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) (m.frame, m.ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat) B (trace m i k) := hs
    have hx' : ∀ j, FrameKeep.CtlStore sy (trace m i j) = false := hx
    cases b with
    | false =>
      obtain ⟨e1, e2⟩ := prev_of_walk hp2 hB2.1 hhs h2 h5 (hA false hb) hclA hx'
      show (frame m i).ram.get! _ &&& 0x80 = (frame m i).ram.get! _ &&& 0x80
      exact e2.trans e1.symm
    | true =>
      obtain ⟨e1, e2⟩ := prev_of_walk hp3 hB2.2 hhs h2 h5 (hA true hb) hclA hx'
      show (frame m i).ram.get! _ &&& 0x80 = (frame m i).ram.get! _ &&& 0x80
      exact e2.trans e1.symm
  · unfold PrevOK
    rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA]), CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
    exact h

open AfterKeep in
/-- **A frame in control keeps the moving direction, the running speed and the stored speed from the scroll handler to its end** (`AfterKeep.keepH`), with the one
condition `CleanK` of `guardE` on each instruction. The proof is that of `keepH`, with the second walk's guard from `cleanH_of_E`. -/
theorem keepHE (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ x ∈ hI sy, (frame m i).ram.get! x = (trace m i k).ram.get! x := by
  simp only [hCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPH sy m0 v q (q1Cfg sy m0 v P) ((hI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy ((hI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ := q1_run (C := q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    intro k hk hpc x hxI
    have hmem : q2Cfg sy m0 x P.stops.toList ∈ (hI sy).map fun b => q2Cfg sy m0 b P.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
    have hw2 := List.all_eq_true.1 hat _ hmem
    have ht2 := List.all_eq_true.1 hp3 _ hmem
    have hs2 : Sim (q2Cfg sy m0 x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := sim_rkOn hs₁
    have hclH : ∀ j, FrameKeep.CleanK (q2Cfg sy m0 x P.stops.toList).G (q2Cfg sy m0 x P.stops.toList).S.store (trace m i j) := fun j => cleanH_of_E hxI (hcl j)
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := endKR (C := q2Cfg sy m0 x P.stops.toList) ht2 rfl rfl hne2 hw2 hs2 hf1 hd1 hclH hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
    subst hkk
    change (B₂.rk && !B₂.spent) = true at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
    have e := hs₂.rkv hfin.1
    rw [if_neg (by simp [hfin.2])] at e
    exact e
  · exact absurd harr (hno n₀ hf0)

end

end Smbrta.GuardE

namespace Smbrta.GuardE
open PipeEntryRule (trace)
variable {sy : Syms} {m0 : Machine}

open AfterKeep in
/-- **The frame comes to the scroll handler once after the player's routine** (`AfterKeep.subs_once`), with the one condition `CleanK` of `guardE` on each instruction:
`AfterKeep.keepH_onceG` with the second walk's guard from `cleanH_of_E` -/
theorem subs_onceE (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace m i k).pc = sy.PlayerSubs → (trace m i k').pc = sy.PlayerSubs → k = k' := by
  intro k k' hk hk' hpc hpc'
  obtain ⟨k₁, H⟩ := keepH_onceG hc hh h0 (fun n => FrameKeep.cleanK_of_E (hcl n)) (fun x hxI j => cleanH_of_E hxI (hcl j)) hx hv harr hf0 hfirst
  have u := (H _ (by simp [hI] : (sy.Player_XSpeedAbsolute &&& 0x7FF).toNat ∈ hI sy)).2
  rw [u k hk hpc, u k' hk' hpc']

end Smbrta.GuardE
