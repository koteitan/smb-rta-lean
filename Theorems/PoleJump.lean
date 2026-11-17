import Theorems.StopRead
import Theorems.VertJump
import Theorems.SubsOnce
import Theorems.PoleJoin

/-!
# Above-ground takeoff and air steps read from the machines

`vert_jumpH` and `vert_airH` export the halt value already required by the existing walks.
The frame lemmas below use the existing `OnFrames` and `FrameKeep` conditions explicitly.
No field of `PoleJoin.Run` is changed here. In particular its arbitrary model arc is not
silently identified with the machine arc. Page: `1-1/f-6-3-PoleJump.md`.
-/

namespace Smbrta.PoleJump

open VertModel
open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)
open VertAir (AtV vTagsA vCasesA goalVA caseOKA vertAirOK)
open VertJump (flat jumpOff vTagsJ jCases goalVJ caseOKJ jumpOK jcase_mem)

/-! ## The movement routine, with the jump's halt value at the scroll handler -/

section proof

variable {sy : Syms} {m0 : Machine}

/-- **`VertJump.vert_jump` with the jump's halt value**: on a frame that starts a jump the halt value at the scroll handler is 1. The same check `jumpOK`: the walk's goal
asks that in a jump the halt value is known and 1 (`VertModel.goalV`). The proof is that of `vert_jump`, with the last step added. -/
theorem vert_jumpH {S : UInt8} {R : Machine} (hV : vertOK sy m0 S = true) (hJ : jumpOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R)
    (hst : peek R sy.Player_State = 0) (ha : peek R sy.SavedJoypadBits &&& 0x80 = 0x80) (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = jumpOff sy m0 S (peek R sy.Player_Y_Position) (peek R sy.Player_XSpeedAbsolute) ∧
      peek (stepN k R) sy.Player_State = 1 ∧ peek (stepN k R) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧ peek (stepN k R) sy.DiffToHaltJump = 1 ∧
      FrameModel.InFrameN (Rom.of m0) R k := by
  have F := vfacts_of hV
  have gB := FrameModel.base_good F.base
  obtain ⟨abm, a80, ab80⟩ := ab_facts (peek R sy.SavedJoypadBits)
  -- the first piece: from the player's routine to the movement routine
  let pc : PCase := { st := peek R sy.Player_State, area := peek R sy.AreaType, raw := peek R sy.SavedJoypadBits, prevA := peek R sy.PreviousA_B_Buttons &&& 0x80 != 0 }
  have hpm : pc ∈ pCases := pcase_mem h.st h.area
  have hA0 : At (Rom.of m0) (pc.c0 sy S) R := by
    refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.eng
      · rfl
      · rfl
      · rfl
      · exact h.spring
      · exact h.swim
      · exact h.size
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact FrameModel.and80_mem _
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
  have hpre := F.pre pc hpm
  simp only [prefixOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨hpiece, hPpc⟩, hPs⟩, hK⟩ := hpre
  obtain ⟨kP, fP, AP, WP, IP⟩ := FrameModel.piece_specI hpiece hA0
  have IP' : FrameModel.InFrameN (Rom.of m0) R kP := fun j hj => (IP j hj).2.2
  have kX : ∀ q ∈ knownP sy (Rom.of m0) S pc, (stepN kP R).ram.get! q.1 = q.2 := fun q hq => AP.K q (List.contains_iff_mem.1 (hK q hq))
  have kmem : ∀ q, q ∈ knownP sy (Rom.of m0) S pc → (stepN kP R).ram.get! q.1 = q.2 := kX
  have wX : ∀ i ∈ watchP sy, i < 2048 → (stepN kP R).ram.get! i = R.ram.get! i := WP
  generalize hX : stepN kP R = X at AP kX kmem wX
  -- the machine of `vstep`: the flat state at the real height, with A and the real stored speed
  let s0 := flat (peek R sy.Player_Y_Position)
  let ab := peek R sy.Player_XSpeedAbsolute
  have gP := FrameModel.poke_good (E := Rom.of m0) sy.DiffToHaltJump 1 gB
  have gV : GoodH (Rom.of m0) (vmach sy m0 S) := ⟨gP.prg, gP.mask, gP.halted, gP.trk, gP.size⟩
  have gH : GoodH (Rom.of m0) (vH sy m0 S s0 true ab) := FrameModel.pokeL_good _ gV
  have hHs : (vH sy m0 S s0 true ab).s = S := by
    show (pokeL (vmach sy m0 S) _).s = S
    rw [FrameModel.pokeL_s]
    rfl
  have hv : ∀ q ∈ vList sy s0 true ab, (vH sy m0 S s0 true ab).ram.get! (I q.1) = q.2 :=
    FrameModel.pokeL_get _ _ gV (by rw [show (vList sy s0 true ab).map (fun q => I q.1) = vIdx sy from rfl]; exact F.idx)
  have hout : ∀ i ∈ outV sy, (vH sy m0 S s0 true ab).ram.get! i = (vmach sy m0 S).ram.get! i := by
    intro i hi
    refine FrameModel.pokeL_out _ _ (fun q hq e => ?_)
    have h1 := F.out i hi
    have h2 : I q.1 ∈ vIdx sy := by
      rw [show vIdx sy = (vList sy s0 true ab).map (fun q => I q.1) from rfl]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e] at h2
    have h3 := List.contains_iff_mem.2 h2
    rw [h1] at h3
    cases h3
  have hV1 : (vmach sy m0 S).ram.get! (I sy.DiffToHaltJump) = 1 := FrameModel.poke_get_self _ _ gB.size
  -- the case of the walk
  have hjm : peek R sy.SavedJoypadBits &&& 0xC0 ∈ jCases := jcase_mem ha
  have hJ' := hJ
  simp only [jumpOK, List.all_eq_true] at hJ'
  have hca := hJ' _ hjm
  simp only [caseOKJ, Bool.and_eq_true] at hca
  have hc := hca.2
  have htags := hca.1
  simp only [FrameModel.tagsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at htags
  have hL : ∀ q ∈ vTagsJ sy (vmach sy m0 S) (peek R sy.SavedJoypadBits &&& 0xC0), q.1 < 2048 ∧ q.1 ≠ stkI (vH sy m0 S s0 true ab).s ∧
      q.1 ≠ stkI ((vH sy m0 S s0 true ab).s - 1) ∧ q.2.R (X.ram.get! q.1) ((vH sy m0 S s0 true ab).ram.get! q.1) := by
    intro q hq
    obtain ⟨⟨t1, t2⟩, t3⟩ := htags q hq
    rw [hHs]
    refine ⟨t1, t2, t3, ?_⟩
    have wv : ∀ u : UInt16, I u ∈ watchP sy → X.ram.get! (I u) = peek R u := fun u hu => wX _ hu (FrameModel.I_lt _)
    have top0 : ∀ (x y : UInt8), y = 0 → (Tag.ab AB.top (AB.known 0)).R x y := fun x y e => by
      rw [e]
      exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
    simp only [vTagsJ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (wv sy.Player_Y_Position (List.mem_append_left _ (.head _))).trans (hv (sy.Player_Y_Position, s0.y) (.head _)).symm
    · exact top0 _ _ (hv (sy.Player_Y_MoveForce, s0.mf) (.tail _ (.head _)))
    · exact top0 _ _ (hv (sy.Player_Y_Speed, s0.vy) (.tail _ (.tail _ (.head _))))
    · exact top0 _ _ (hv (sy.Player_YMF_Dummy, s0.dummy) (.tail _ (.tail _ (.tail _ (.head _)))))
    · exact top0 _ _ (hv (sy.VerticalForce, s0.vf) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    · exact top0 _ _ (hv (sy.VerticalForceDown, s0.vfd) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    · exact top0 _ _ (hv (sy.JumpOrigin_Y_Position, s0.origin) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
    · -- the state
      have e1 : X.ram.get! (I sy.Player_State) = peek R sy.Player_State := kmem (I sy.Player_State, pc.st) (.tail _ (.head _))
      have e2 : (vH sy m0 S s0 true ab).ram.get! (I sy.Player_State) = s0.st := hv (sy.Player_State, s0.st) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
      rw [e1, e2, hst]
      exact FrameModel.Tag.R_kn _ _
    · -- the stored speed: the same on the two machines
      have e2 : (vH sy m0 S s0 true ab).ram.get! (I sy.Player_XSpeedAbsolute) = ab := hv (sy.Player_XSpeedAbsolute, ab) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
      exact (wv sy.Player_XSpeedAbsolute (List.mem_append_right _ (.head _))).trans e2.symm
    · -- A and B
      have e1 : X.ram.get! (I sy.A_B_Buttons) = peek R sy.SavedJoypadBits &&& 0xC0 := kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 true ab).ram.get! (I sy.A_B_Buttons) = 0x80 := hv (sy.A_B_Buttons, if true then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · -- A on the frame before: bit 7 off on the real machine, 0 on the machine of `vstep`
      have e1 : X.ram.get! (I sy.PreviousA_B_Buttons) = peek R sy.PreviousA_B_Buttons := wv sy.PreviousA_B_Buttons (List.mem_append_right _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 true ab).ram.get! (I sy.PreviousA_B_Buttons) = 0 :=
        hv (sy.PreviousA_B_Buttons, if s0.prevA then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
      rw [e1, e2]
      refine ⟨?_, TaintRun.mem_known_self _⟩
      show peek R sy.PreviousA_B_Buttons &&& 0x80 = (0 : UInt8) &&& 0x80
      rw [hp]
      rfl
    · have e1 : X.ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 := kmem (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.head _)
      have e2 : (vH sy m0 S s0 true ab).ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 :=
        hv (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.JumpspringAnimCtrl) = 0 := kmem (I sy.JumpspringAnimCtrl, 0) (.tail _ (.tail _ (.tail _ (.head _))))
      rw [e1, hout (I sy.JumpspringAnimCtrl) (.head _)]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.SwimmingFlag) = 0 := kmem (I sy.SwimmingFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      rw [e1, hout (I sy.SwimmingFlag) (.tail _ (.head _))]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.PlayerChangeSizeFlag) = 0 := kmem (I sy.PlayerChangeSizeFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      rw [e1, hout (I sy.PlayerChangeSizeFlag) (.tail _ (.tail _ (.head _)))]
      exact FrameModel.Tag.R_kn _ _
    · rw [hout (I sy.DiffToHaltJump) (.tail _ (.tail _ (.tail _ (.head _)))), hV1]
      exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
  -- the walk with detours, to the routine's return
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalVJ sy S Q = true → Q.w (stkI (vH sy m0 S s0 true ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 true ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalVJ, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.1.1.2 (stkI S) (.tail _ (.head _)), hQ.1.1.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', rel, fix, IX⟩ :=
    FrameModel.leafD_spec (ain := 0) F.ds hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalVJ, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨_, heq⟩, hw⟩, hdt⟩, hst2⟩, hvy2⟩ := hg
  have veq : ∀ i ∈ I sy.Player_State :: vIds sy, (stepN k X).ram.get! i = (vRun sy m0 S s0 true ab).ram.get! i := by
    intro i hi
    have hi2 : i < 2048 := by
      simp only [vIds, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact FrameModel.I_lt _
    exact FrameModel.tagImp_R (heq i hi) (rel i hi2)
  -- the return, on the real machine
  obtain ⟨p1, p2, p3, _⟩ := hstop Q hs
  obtain ⟨y1, y2, y3, y4⟩ := FrameModel.step_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  rw [← FrameModel.stepN_one] at y1 y2 y3 y4
  obtain ⟨sp1, sp2⟩ := FrameModel.stack_two S
  have r1 : (stepN k X).ram.get! (stkI (S - 1)) = retLo sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI (S - 1)) (.tail _ (.tail _ (.head _))))]
    exact kmem (stkI (S - 1), retLo sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have r2 : (stepN k X).ram.get! (stkI S) = retHi sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI S) (.tail _ (.head _)))]
    exact kmem (stkI S, retHi sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have hYpc : (stepN 1 (stepN k X)).pc = retPc sy (Rom.of m0) S := by
    rw [y1, sX', sp2, sp1, r1, r2]
    rfl
  have hYs : (stepN 1 (stepN k X)).s = S := by rw [y2, sX', sp2]
  -- the last piece, to the scroll handler
  have hAY : At (Rom.of m0) { pc := retPc sy (Rom.of m0) S, s := S, K := [] } (stepN 1 (stepN k X)) :=
    ⟨y4, hYpc, hYs, (fun q hq => by cases hq), (fun q hq => by cases hq), (fun v hv => by cases hv), (fun v hv => by cases hv), (fun v hv => by cases hv)⟩
  obtain ⟨kL, fL, AL, WL, IL⟩ := FrameModel.piece_specI F.last hAY
  have I1 : FrameModel.InFrameN (Rom.of m0) (stepN k X) 1 := fun j hj => by
    rw [show j = 0 by omega]
    show FrameModel.InFrame (Rom.of m0) (stepN k X)
    exact FrameModel.inFrame_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  have IL' : FrameModel.InFrameN (Rom.of m0) (stepN 1 (stepN k X)) kL := fun j hj => (IL j hj).2.2
  have wZ : ∀ i ∈ watchR sy, i < 2048 → (stepN kL (stepN 1 (stepN k X))).ram.get! i = (stepN k X).ram.get! i := by
    intro i hi hl
    rw [WL i hi hl, y3]
  have eZ : stepN (kP + (k + (1 + kL))) R = stepN kL (stepN 1 (stepN k X)) := by
    rw [FrameModel.stepN_add, hX, FrameModel.stepN_add, FrameModel.stepN_add]
  have hfin : vsOf sy (stepN (kP + (k + (1 + kL))) R) = jumpOff sy m0 S (peek R sy.Player_Y_Position) (peek R sy.Player_XSpeedAbsolute) := by
    rw [eZ]
    show _ = vstepV sy m0 S s0 true ab
    rw [vstepV_eq]
    have wv : ∀ u : UInt16, I u ∈ I sy.Player_State :: vIds sy →
        peek (stepN kL (stepN 1 (stepN k X))) u = peek (vRun sy m0 S s0 true ab) u := by
      intro u hu
      rw [peek_I, peek_I, wZ (I u) (by
        simp only [List.mem_cons] at hu
        rcases hu with hu | hu
        · rw [hu]
          exact List.mem_append_right _ (.head _)
        · exact List.mem_append_left _ hu) (FrameModel.I_lt _)]
      exact veq _ hu
    have wab : peek (stepN kL (stepN 1 (stepN k X))) sy.A_B_Buttons = peek R sy.SavedJoypadBits &&& 0xC0 := by
      rw [peek_I, wZ (I sy.A_B_Buttons) (List.mem_append_right _ (.tail _ (.head _))) (FrameModel.I_lt _),
        fix _ (FrameModel.I_lt _) (hw (I sy.A_B_Buttons) (.head _))]
      exact kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
    have hat : ((peek R sy.SavedJoypadBits &&& 0xC0) &&& 0x80 != 0) = true := by
      rw [a80, ha]
      decide
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = _
    rw [wv sy.Player_Y_Position (.tail _ (.head _)), wv sy.Player_Y_MoveForce (.tail _ (.tail _ (.head _))), wv sy.Player_Y_Speed (.tail _ (.tail _ (.tail _ (.head _)))),
      wv sy.Player_YMF_Dummy (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), wv sy.VerticalForce (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), wv sy.VerticalForceDown (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      wv sy.JumpOrigin_Y_Position (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), wv sy.Player_State (.head _), wab, hat]
  -- at the return the state is known and 1, the vertical speed known and negative
  have hst1 : peek (stepN (kP + (k + (1 + kL))) R) sy.Player_State = 1 := by
    rw [eZ, peek_I, wZ (I sy.Player_State) (List.mem_append_right _ (.head _)) (FrameModel.I_lt _)]
    exact (FrameModel.Tag.same_spec hst2 (rel _ (FrameModel.I_lt _))).1
  have hvy1 : peek (stepN (kP + (k + (1 + kL))) R) sy.Player_Y_Speed &&& 0x80 = 0x80 := by
    rw [eZ, peek_I, wZ (I sy.Player_Y_Speed) (List.mem_append_left _ (.tail _ (.tail _ (.head _)))) (FrameModel.I_lt _)]
    cases hq : (Q.ram (I sy.Player_Y_Speed)).same with
    | none =>
      rw [hq] at hvy2
      cases hvy2
    | some v =>
      rw [hq] at hvy2
      rw [(FrameModel.Tag.same_spec hq (rel _ (FrameModel.I_lt _))).1]
      exact beq_iff_eq.1 hvy2
  -- the jump's halt value at the return is known and 1: the goal of the walk asks it in a jump
  have hh1 : peek (stepN (kP + (k + (1 + kL))) R) sy.DiffToHaltJump = 1 := by
    rw [eZ, peek_I, wZ (I sy.DiffToHaltJump) (List.mem_append_right _ (.tail _ (.tail _ (.head _)))) (FrameModel.I_lt _)]
    rw [hst2] at hdt
    simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hdt
    exact (FrameModel.Tag.same_spec hdt (rel _ (FrameModel.I_lt _))).1
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, hfin, hst1, hvy1, hh1, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL'))⟩
  · have e1 : FrameModel.moveLen = 728 := rfl
    have e2 : fuelP = 60 := rfl
    have e3 : fuelV = 600 := rfl
    rw [e1]
    rw [e2] at fP
    rw [e3] at hk
    omega
  · rw [eZ]
    exact AL.good
  · rw [eZ]
    exact AL.pc
  · rw [eZ]
    exact AL.s

/-- **`VertAir.vert_air` with the jump's halt value**: at the scroll handler, in a jump the halt value is 1. The same check `vertAirOK`. The proof is that of `vert_air`,
with the last step added (that of `VertModel.vert_model`). -/
theorem vert_airH {S : UInt8} {R : Machine} (hOK : vertAirOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R)
    (hst : peek R sy.Player_State = 1 ∨ peek R sy.Player_State = 2)
    (hd : peek R sy.Player_State = 1 → peek R sy.DiffToHaltJump = 1)
    (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = peek R sy.A_B_Buttons &&& 0x80) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      ((vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨ (vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) ∧
      (peek (stepN k R) sy.Player_State = 1 → peek (stepN k R) sy.DiffToHaltJump = 1) ∧ FrameModel.InFrameN (Rom.of m0) R k := by
  have hOK' := hOK
  simp only [vertAirOK, Bool.and_eq_true, List.all_eq_true] at hOK'
  have F := vfacts_of hOK'.1
  have gB := FrameModel.base_good F.base
  obtain ⟨abm, a80, ab80⟩ := ab_facts (peek R sy.SavedJoypadBits)
  -- the first piece: from the player's routine to the movement routine
  let pc : PCase := { st := peek R sy.Player_State, area := peek R sy.AreaType, raw := peek R sy.SavedJoypadBits, prevA := peek R sy.PreviousA_B_Buttons &&& 0x80 != 0 }
  have hpm : pc ∈ pCases := pcase_mem h.st h.area
  have hA0 : At (Rom.of m0) (pc.c0 sy S) R := by
    refine ⟨h.good, h.pc, h.s, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.eng
      · rfl
      · rfl
      · rfl
      · exact h.spring
      · exact h.swim
      · exact h.size
    · intro q hq
      simp only [PCase.c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      exact FrameModel.and80_mem _
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
    · intro v hv
      simp [PCase.c0] at hv
  have hpre := F.pre pc hpm
  simp only [prefixOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨hpiece, hPpc⟩, hPs⟩, hK⟩ := hpre
  obtain ⟨kP, fP, AP, WP, IP⟩ := FrameModel.piece_specI hpiece hA0
  have IP' : FrameModel.InFrameN (Rom.of m0) R kP := fun j hj => (IP j hj).2.2
  have kX : ∀ q ∈ knownP sy (Rom.of m0) S pc, (stepN kP R).ram.get! q.1 = q.2 := fun q hq => AP.K q (List.contains_iff_mem.1 (hK q hq))
  have kmem : ∀ q, q ∈ knownP sy (Rom.of m0) S pc → (stepN kP R).ram.get! q.1 = q.2 := kX
  have wX : ∀ i ∈ watchP sy, i < 2048 → (stepN kP R).ram.get! i = R.ram.get! i := WP
  generalize hX : stepN kP R = X at AP kX kmem wX
  -- the machine of `vstep`
  let s0 := vsOf sy R
  let a := peek R sy.SavedJoypadBits &&& 0x80 != 0
  let ab : UInt8 := 0
  have gP := FrameModel.poke_good (E := Rom.of m0) sy.DiffToHaltJump 1 gB
  have gV : GoodH (Rom.of m0) (vmach sy m0 S) := ⟨gP.prg, gP.mask, gP.halted, gP.trk, gP.size⟩
  have gH : GoodH (Rom.of m0) (vH sy m0 S s0 a ab) := FrameModel.pokeL_good _ gV
  have hHs : (vH sy m0 S s0 a ab).s = S := by
    show (pokeL (vmach sy m0 S) _).s = S
    rw [FrameModel.pokeL_s]
    rfl
  have hv : ∀ q ∈ vList sy s0 a ab, (vH sy m0 S s0 a ab).ram.get! (I q.1) = q.2 :=
    FrameModel.pokeL_get _ _ gV (by rw [show (vList sy s0 a ab).map (fun q => I q.1) = vIdx sy from rfl]; exact F.idx)
  have hout : ∀ i ∈ outV sy, (vH sy m0 S s0 a ab).ram.get! i = (vmach sy m0 S).ram.get! i := by
    intro i hi
    refine FrameModel.pokeL_out _ _ (fun q hq e => ?_)
    have h1 := F.out i hi
    have h2 : I q.1 ∈ vIdx sy := by
      rw [show vIdx sy = (vList sy s0 a ab).map (fun q => I q.1) from rfl]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    rw [e] at h2
    have h3 := List.contains_iff_mem.2 h2
    rw [h1] at h3
    cases h3
  have hV1 : (vmach sy m0 S).ram.get! (I sy.DiffToHaltJump) = 1 := FrameModel.poke_get_self _ _ gB.size
  -- the case of the walk
  let vc : VCase := { st := peek R sy.Player_State, ab := peek R sy.SavedJoypadBits &&& 0xC0, prevA := peek R sy.PreviousA_B_Buttons &&& 0x80 != 0 }
  have hvm : vc ∈ vCasesA := by
    simp only [vCasesA, List.mem_filter]
    refine ⟨vcase_mem h.st abm, ?_⟩
    rcases hst with e | e <;> simp [vc, e]
  have hca := hOK'.2 vc hvm
  simp only [caseOKA, Bool.and_eq_true] at hca
  have hc := hca.2
  have htags := hca.1
  simp only [FrameModel.tagsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at htags
  have hpv : vc.pv = (if s0.prevA then 0x80 else 0) := by
    show (if (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) = true then (0x80 : UInt8) else 0) = if ((peek R sy.A_B_Buttons &&& 0x80) != 0) = true then 0x80 else 0
    rw [hp]
  have hL : ∀ q ∈ vTagsA sy (vmach sy m0 S) vc, q.1 < 2048 ∧ q.1 ≠ stkI (vH sy m0 S s0 a ab).s ∧ q.1 ≠ stkI ((vH sy m0 S s0 a ab).s - 1) ∧
      q.2.R (X.ram.get! q.1) ((vH sy m0 S s0 a ab).ram.get! q.1) := by
    intro q hq
    obtain ⟨⟨t1, t2⟩, t3⟩ := htags q hq
    rw [hHs]
    refine ⟨t1, t2, t3, ?_⟩
    have wv : ∀ u : UInt16, I u ∈ watchP sy → X.ram.get! (I u) = peek R u := fun u hu => wX _ hu (FrameModel.I_lt _)
    simp only [vTagsA, vIds, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (wv sy.Player_Y_Position (List.mem_append_left _ (.head _))).trans (hv (sy.Player_Y_Position, s0.y) (.head _)).symm
    · exact (wv sy.Player_Y_MoveForce (List.mem_append_left _ (.tail _ (.head _)))).trans (hv (sy.Player_Y_MoveForce, s0.mf) (.tail _ (.head _))).symm
    · exact (wv sy.Player_Y_Speed (List.mem_append_left _ (.tail _ (.tail _ (.head _))))).trans (hv (sy.Player_Y_Speed, s0.vy) (.tail _ (.tail _ (.head _)))).symm
    · exact (wv sy.Player_YMF_Dummy (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))).trans (hv (sy.Player_YMF_Dummy, s0.dummy) (.tail _ (.tail _ (.tail _ (.head _))))).symm
    · exact (wv sy.VerticalForce (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).trans (hv (sy.VerticalForce, s0.vf) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))).symm
    · exact (wv sy.VerticalForceDown (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).trans (hv (sy.VerticalForceDown, s0.vfd) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))).symm
    · exact (wv sy.JumpOrigin_Y_Position (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))).trans (hv (sy.JumpOrigin_Y_Position, s0.origin) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))).symm
    · -- the state
      have e1 : X.ram.get! (I sy.Player_State) = peek R sy.Player_State := kmem (I sy.Player_State, pc.st) (.tail _ (.head _))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.Player_State) = s0.st := hv (sy.Player_State, s0.st) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · -- the stored speed: not known on the real machine, 0 on the machine of `vstep`
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.Player_XSpeedAbsolute) = ab := hv (sy.Player_XSpeedAbsolute, ab) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
      show (Tag.ab AB.top (AB.known 0)).R (X.ram.get! (I sy.Player_XSpeedAbsolute)) ((vH sy m0 S s0 a ab).ram.get! (I sy.Player_XSpeedAbsolute))
      rw [e2]
      exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
    · -- A and B
      have e1 : X.ram.get! (I sy.A_B_Buttons) = peek R sy.SavedJoypadBits &&& 0xC0 := kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.A_B_Buttons) = if a then 0x80 else 0 := hv (sy.A_B_Buttons, if a then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))
      rw [e1, e2]
      show (FrameModel.Tag.kn _ _).R _ (if (peek R sy.SavedJoypadBits &&& 0x80 != 0) = true then (0x80 : UInt8) else 0)
      rw [ab80]
      exact FrameModel.Tag.R_kn _ _
    · -- A on the frame before
      have e1 : X.ram.get! (I sy.PreviousA_B_Buttons) = peek R sy.PreviousA_B_Buttons := wv sy.PreviousA_B_Buttons (List.mem_append_right _ (.tail _ (.head _)))
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.PreviousA_B_Buttons) = if s0.prevA then 0x80 else 0 :=
        hv (sy.PreviousA_B_Buttons, if s0.prevA then 0x80 else 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))
      rw [e1, e2, ← hpv]
      exact ⟨FrameModel.and80_mem _, TaintRun.mem_known_self _⟩
    · have e1 : X.ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 := kmem (I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.head _)
      have e2 : (vH sy m0 S s0 a ab).ram.get! (I sy.GameEngineSubroutine) = sy.Eng_PlayerCtrl.toUInt8 :=
        hv (sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))
      rw [e1, e2]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.JumpspringAnimCtrl) = 0 := kmem (I sy.JumpspringAnimCtrl, 0) (.tail _ (.tail _ (.tail _ (.head _))))
      rw [e1, hout (I sy.JumpspringAnimCtrl) (.head _)]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.SwimmingFlag) = 0 := kmem (I sy.SwimmingFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      rw [e1, hout (I sy.SwimmingFlag) (.tail _ (.head _))]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.PlayerChangeSizeFlag) = 0 := kmem (I sy.PlayerChangeSizeFlag, 0) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      rw [e1, hout (I sy.PlayerChangeSizeFlag) (.tail _ (.tail _ (.head _)))]
      exact FrameModel.Tag.R_kn _ _
    · have e1 : X.ram.get! (I sy.DiffToHaltJump) = peek R sy.DiffToHaltJump := wv sy.DiffToHaltJump (List.mem_append_right _ (.tail _ (.tail _ (.head _))))
      rw [e1, hout (I sy.DiffToHaltJump) (.tail _ (.tail _ (.tail _ (.head _)))), hV1]
      by_cases h1 : peek R sy.Player_State = 1
      · have e2 : (vc.st == 1) = true := by simp [vc, h1]
        simp only [e2, if_true]
        rw [hd h1]
        exact FrameModel.Tag.R_kn _ _
      · have e2 : (vc.st == 1) = false := by simp [vc, h1]
        simp only [e2, Bool.false_eq_true, if_false]
        exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
  -- the walk with detours, to the routine's return
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalVA sy S Q = true → Q.w (stkI (vH sy m0 S s0 a ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 a ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalVA, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.1.2 (stkI S) (.tail _ (.head _)), hQ.1.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', rel, fix, IX⟩ :=
    FrameModel.leafD_spec (ain := 0) F.ds hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalVA, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨⟨_, heq⟩, hw⟩, hdt⟩, hst2⟩ := hg
  have veq : ∀ i ∈ I sy.Player_State :: vIds sy, (stepN k X).ram.get! i = (vRun sy m0 S s0 a ab).ram.get! i := by
    intro i hi
    have hi2 : i < 2048 := by
      simp only [vIds, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact FrameModel.I_lt _
    exact FrameModel.tagImp_R (heq i hi) (rel i hi2)
  -- the return, on the real machine
  obtain ⟨p1, p2, p3, _⟩ := hstop Q hs
  obtain ⟨y1, y2, y3, y4⟩ := FrameModel.step_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  rw [← FrameModel.stepN_one] at y1 y2 y3 y4
  obtain ⟨sp1, sp2⟩ := FrameModel.stack_two S
  have r1 : (stepN k X).ram.get! (stkI (S - 1)) = retLo sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI (S - 1)) (.tail _ (.tail _ (.head _))))]
    exact kmem (stkI (S - 1), retLo sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have r2 : (stepN k X).ram.get! (stkI S) = retHi sy (Rom.of m0) S := by
    rw [fix _ (FrameModel.mask_stk _) (hw (stkI S) (.tail _ (.head _)))]
    exact kmem (stkI S, retHi sy (Rom.of m0) S) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have hYpc : (stepN 1 (stepN k X)).pc = retPc sy (Rom.of m0) S := by
    rw [y1, sX', sp2, sp1, r1, r2]
    rfl
  have hYs : (stepN 1 (stepN k X)).s = S := by rw [y2, sX', sp2]
  -- the last piece, to the scroll handler
  have hAY : At (Rom.of m0) { pc := retPc sy (Rom.of m0) S, s := S, K := [] } (stepN 1 (stepN k X)) :=
    ⟨y4, hYpc, hYs, (fun q hq => by cases hq), (fun q hq => by cases hq), (fun v hv => by cases hv), (fun v hv => by cases hv), (fun v hv => by cases hv)⟩
  obtain ⟨kL, fL, AL, WL, IL⟩ := FrameModel.piece_specI F.last hAY
  have I1 : FrameModel.InFrameN (Rom.of m0) (stepN k X) 1 := fun j hj => by
    rw [show j = 0 by omega]
    show FrameModel.InFrame (Rom.of m0) (stepN k X)
    exact FrameModel.inFrame_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  have IL' : FrameModel.InFrameN (Rom.of m0) (stepN 1 (stepN k X)) kL := fun j hj => (IL j hj).2.2
  have wZ : ∀ i ∈ watchR sy, i < 2048 → (stepN kL (stepN 1 (stepN k X))).ram.get! i = (stepN k X).ram.get! i := by
    intro i hi hl
    rw [WL i hi hl, y3]
  have eZ : stepN (kP + (k + (1 + kL))) R = stepN kL (stepN 1 (stepN k X)) := by
    rw [FrameModel.stepN_add, hX, FrameModel.stepN_add, FrameModel.stepN_add]
  have hfin : vsOf sy (stepN (kP + (k + (1 + kL))) R) = vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) 0 := by
    rw [eZ, vstepV_eq]
    have wv : ∀ u : UInt16, I u ∈ I sy.Player_State :: vIds sy →
        peek (stepN kL (stepN 1 (stepN k X))) u = peek (vRun sy m0 S s0 a ab) u := by
      intro u hu
      rw [peek_I, peek_I, wZ (I u) (by
        simp only [List.mem_cons] at hu
        rcases hu with hu | hu
        · rw [hu]
          exact List.mem_append_right _ (.head _)
        · exact List.mem_append_left _ hu) (FrameModel.I_lt _)]
      exact veq _ hu
    have wab : peek (stepN kL (stepN 1 (stepN k X))) sy.A_B_Buttons = peek R sy.SavedJoypadBits &&& 0xC0 := by
      rw [peek_I, wZ (I sy.A_B_Buttons) (List.mem_append_right _ (.tail _ (.head _))) (FrameModel.I_lt _),
        fix _ (FrameModel.I_lt _) (hw (I sy.A_B_Buttons) (.head _))]
      exact kmem (I sy.A_B_Buttons, pc.raw &&& 0xC0) (.tail _ (.tail _ (.head _)))
    show Jump.VS.mk _ _ _ _ _ _ _ _ _ = _
    rw [wv sy.Player_Y_Position (.tail _ (.head _)), wv sy.Player_Y_MoveForce (.tail _ (.tail _ (.head _))), wv sy.Player_Y_Speed (.tail _ (.tail _ (.tail _ (.head _)))),
      wv sy.Player_YMF_Dummy (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), wv sy.VerticalForce (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), wv sy.VerticalForceDown (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))),
      wv sy.JumpOrigin_Y_Position (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))), wv sy.Player_State (.head _), wab, a80]
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, hfin, ?_, ?_, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL'))⟩
  · have e1 : FrameModel.moveLen = 728 := rfl
    have e2 : fuelP = 60 := rfl
    have e3 : fuelV = 600 := rfl
    rw [e1]
    rw [e2] at fP
    rw [e3] at hk
    omega
  · rw [eZ]
    exact AL.good
  · rw [eZ]
    exact AL.pc
  · rw [eZ]
    exact AL.s
  · -- the state at the return is known and 1 or 2
    rw [← hfin]
    show peek (stepN (kP + (k + (1 + kL))) R) sy.Player_State = 1 ∨ peek (stepN (kP + (k + (1 + kL))) R) sy.Player_State = 2
    rw [eZ, peek_I, wZ (I sy.Player_State) (List.mem_append_right _ (.head _)) (FrameModel.I_lt _)]
    cases hq : (Q.ram (I sy.Player_State)).same with
    | none =>
      rw [hq] at hst2
      cases hst2
    | some v =>
      rw [hq] at hst2
      rw [(FrameModel.Tag.same_spec hq (rel _ (FrameModel.I_lt _))).1]
      simp only [Bool.or_eq_true, beq_iff_eq] at hst2
      exact hst2
  · -- in a jump the jump's halt value at the return is known and 1: the goal of the walk asks it
    rw [eZ]
    intro hst1
    have e1 : (stepN k X).ram.get! (I sy.Player_State) = 1 := by
      rw [← wZ (I sy.Player_State) (List.mem_append_right _ (.head _)) (FrameModel.I_lt _)]
      exact hst1
    cases hq : (Q.ram (I sy.Player_State)).same with
    | none =>
      rw [hq] at hdt
      cases hdt
    | some v =>
      rw [hq] at hdt
      have e2 := (FrameModel.Tag.same_spec hq (rel _ (FrameModel.I_lt _))).1
      rw [e1] at e2
      subst e2
      simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hdt
      have e3 := (FrameModel.Tag.same_spec hdt (rel _ (FrameModel.I_lt _))).1
      show (stepN kL (stepN 1 (stepN k X))).ram.get! (I sy.DiffToHaltJump) = 1
      rw [wZ (I sy.DiffToHaltJump) (List.mem_append_right _ (.tail _ (.tail _ (.head _)))) (FrameModel.I_lt _)]
      exact e3

end proof


/-- The vertical routine needs a subset of the existing horizontal frame conditions. -/
theorem atV_of_atFrame {sy : Syms} {E : Rom} {S : UInt8} {R : Machine}
    (h : FrameModel.AtFrame sy E S R) : AtV sy E S R :=
  ⟨h.good, h.pc, h.s, h.eng, h.area, h.st, h.spring, h.swim, h.size⟩

/-- A takeoff on a timed real frame reaches the scroll handler with `jumpOff`.
The jump is read at the player's routine; no equality between the input pad and that read is assumed. -/
theorem take_read {sy : Syms} {m0 M : Machine} {i : UInt8} {n : Nat}
    (hV : vertOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hJ : jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (h : SurfaceRead.ReadH sy m0 M i n)
    (hst : peek (PipeEntryRule.trace M i n) sy.Player_State = 0)
    (ha : peek (PipeEntryRule.trace M i n) sy.SavedJoypadBits &&& 0x80 = 0x80)
    (hp : peek (PipeEntryRule.trace M i n) sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    ∃ k, n ≤ k ∧ k ≤ n + FrameModel.moveLen ∧
      (PipeEntryRule.trace M i k).pc = sy.PlayerSubs ∧
      vsOf sy (PipeEntryRule.trace M i k) = jumpOff sy m0 (FrameModel.ctrlStack sy m0)
        (peek (PipeEntryRule.trace M i n) sy.Player_Y_Position) (peek (PipeEntryRule.trace M i n) sy.Player_XSpeedAbsolute) ∧
      peek (PipeEntryRule.trace M i k) sy.Player_State = 1 ∧
      peek (PipeEntryRule.trace M i k) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧
      peek (PipeEntryRule.trace M i k) sy.DiffToHaltJump = 1 := by
  obtain ⟨d, hd, _, pc, _, vs, st, vy, halt, hf⟩ := vert_jumpH hV hJ (atV_of_atFrame h.at_frame) hst ha hp
  have eq := (FrameModel.trace_inFrame h.time.loop h.time.start hf h.time.time d (Nat.le_refl d)).1
  exact ⟨n + d, by omega, by omega, by rw [eq]; exact pc, by rw [eq]; exact vs,
    by rw [eq]; exact st, by rw [eq]; exact vy, by rw [eq]; exact halt⟩

section Frames
open SurfaceFrames (OnFrames AreaRun vOf farN)
variable {sy : Syms} {m0 : Machine} {B : PoleJoin.Box} {T J g : Nat} {seq : Nat → Machine}
    {Sr : FrameKeep.RealRun} {ar : Nat} {K : FrameKeep.Frames sy m0 Sr ar g seq}

/-- A counted takeoff, including the touch frame, reads the height and stored speed
of the end of the preceding counted frame. All frame assumptions are the existing ones of `OnFrames.readE_at`. -/
theorem take_subs (hV : vertOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hJ : jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m)
    (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g)
    (hs : peek (seq (j - 1)) sy.Player_State = 0)
    (ha : peek (StopRead.atR sy K j) sy.SavedJoypadBits &&& 0x80 = 0x80)
    (hp : peek (StopRead.atR sy K j) sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    ∃ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k ∧
      k ≤ CtrlKeep.arrAt sy (K.fm j) (K.pad j) + FrameModel.moveLen ∧
      (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs ∧
      vsOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) = jumpOff sy m0 (FrameModel.ctrlStack sy m0)
        (peek (seq (j - 1)) sy.Player_Y_Position) (peek (seq (j - 1)) sy.Player_XSpeedAbsolute) ∧
      peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 1 ∧
      peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧
      peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.DiffToHaltJump = 1 := by
  have hR := (O.readE_at hck hOK hfr hidle hst Ar hv0 hP0 hg h1 h3).1
  have kp := StopRead.keep_at hck O hst Ar h1 h3
  have st : peek (StopRead.atR sy K j) sy.Player_State = 0 := by
    rw [kp _ (by simp [CtrlKeep.keepA]), hs]
  obtain ⟨k, k1, k2, pc, vs, st1, vy, halt⟩ := take_read hV hJ hR st ha hp
  rw [kp _ (by simp [CtrlKeep.keepA]), kp _ (by simp [CtrlKeep.keepA])] at vs
  exact ⟨k, k1, k2, pc, vs, st1, vy, halt⟩

/-- Exactly the five vertical bytes not already protected above ground.
This is a condition for one frame, not a new field or a consequence of `keep`. -/
def VEnd (sy : Syms) (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : Prop :=
  ∀ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k →
    (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs →
    ∀ x ∈ SurfaceFrames.vHard sy, peek (seq j) x = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) x

/-- With the five hard bytes preserved, all vertical bytes are preserved in the air.
The other bytes and the vertical force use `OnFrames.kAt` and `vfAt`, not extra hypotheses. -/
theorem end_vertical (hck : CtrlKeep.ctrlCheck sy m0 = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (he : VEnd sy K j)
    {k : Nat} (hk : CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k)
    (pc : (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs)
    (hs : peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 1 ∨
      peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 2) :
    vsOf sy (seq j) = vsOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) ∧
      peek (seq j) sy.DiffToHaltJump = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.DiffToHaltJump := by
  have va := he k hk pc
  have vk := O.kAt hck hst Ar h1 h3 k hk pc
  have vf := O.vfAt hck hst Ar h1 h3 k hk pc
  have st := va sy.Player_State (by simp [SurfaceFrames.vHard])
  have force : peek (seq j) sy.VerticalForce = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.VerticalForce := by
    rcases vf with vf | ⟨_, h0⟩
    · exact vf
    · rw [st] at h0
      rcases hs with hs | hs <;> rw [hs] at h0 <;> cases h0
  have keep : ∀ x ∈ [sy.VerticalForceDown, sy.JumpOrigin_Y_Position, sy.DiffToHaltJump, sy.A_B_Buttons],
      peek (seq j) x = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) x := by
    intro x hx
    apply vk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [VertKeep.kI]
  refine ⟨?_, keep _ (by simp)⟩
  unfold vsOf
  rw [va _ (by simp [SurfaceFrames.vHard]), va _ (by simp [SurfaceFrames.vHard]),
    va _ (by simp [SurfaceFrames.vHard]), va _ (by simp [SurfaceFrames.vHard]), force,
    keep _ (by simp), keep _ (by simp), st, keep _ (by simp)]

/-- The takeoff at the end of a counted frame, with exactly `VEnd` left explicit. -/
theorem take_end (hV : vertOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hJ : jumpOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m)
    (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (he : VEnd sy K j)
    (hs : peek (seq (j - 1)) sy.Player_State = 0)
    (ha : peek (StopRead.atR sy K j) sy.SavedJoypadBits &&& 0x80 = 0x80)
    (hp : peek (StopRead.atR sy K j) sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    vsOf sy (seq j) = jumpOff sy m0 (FrameModel.ctrlStack sy m0)
        (peek (seq (j - 1)) sy.Player_Y_Position) (peek (seq (j - 1)) sy.Player_XSpeedAbsolute) ∧
      peek (seq j) sy.Player_State = 1 ∧ peek (seq j) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧
      peek (seq j) sy.DiffToHaltJump = 1 := by
  obtain ⟨k, k1, _, pc, vs, st, vy, halt⟩ :=
    take_subs hV hJ hck hOK hfr hidle O hst Ar hv0 hP0 hg h1 (by omega) hs ha hp
  obtain ⟨ev, eh⟩ := end_vertical hck O hst Ar h1 h3 he k1 pc (Or.inl st)
  have es : peek (seq j) sy.Player_State = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State :=
    congrArg Jump.VS.st ev
  have ey : peek (seq j) sy.Player_Y_Speed = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_Y_Speed :=
    congrArg Jump.VS.vy ev
  exact ⟨ev.trans vs, es.trans st, by rw [ey]; exact vy, eh.trans halt⟩

/-- All nine components of the vertical state occur in the existing pre-control keep list. -/
theorem vs_of_keep {a b : Machine}
    (h : ∀ x ∈ CtrlKeep.keepA sy, peek a x = peek b x) : vsOf sy a = vsOf sy b := by
  unfold vsOf
  rw [h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]),
    h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]),
    h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]),
    h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA]), h _ (by simp [CtrlKeep.keepA])]

/-- A counted air frame reads the preceding machine's vertical state and no stored speed.
`HaltOK` and `PrevOK` are explicit; they are not silently added to the run. -/
theorem air_subs (hA : vertAirOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m)
    (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g)
    (hs : peek (seq (j - 1)) sy.Player_State = 1 ∨ peek (seq (j - 1)) sy.Player_State = 2)
    (hh : SurfaceFrames.HaltOK sy (seq (j - 1))) (hp : PrevKeep.PrevOK sy (seq (j - 1))) :
    ∃ k, CtrlKeep.arrAt sy (K.fm j) (K.pad j) ≤ k ∧
      k ≤ CtrlKeep.arrAt sy (K.fm j) (K.pad j) + FrameModel.moveLen ∧
      (PipeEntryRule.trace (K.fm j) (K.pad j) k).pc = sy.PlayerSubs ∧
      vsOf sy (PipeEntryRule.trace (K.fm j) (K.pad j) k) =
        vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy (seq (j - 1)))
          (peek (StopRead.atR sy K j) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      (peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 1 ∨
       peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 2) ∧
      (peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State = 1 →
       peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.DiffToHaltJump = 1) := by
  have hR := (O.readE_at hck hOK hfr hidle hst Ar hv0 hP0 hg h1 h3).1
  have kp := StopRead.keep_at hck O hst Ar h1 h3
  have st : peek (StopRead.atR sy K j) sy.Player_State = 1 ∨ peek (StopRead.atR sy K j) sy.Player_State = 2 := by
    rw [kp _ (by simp [CtrlKeep.keepA])]; exact hs
  have halt : peek (StopRead.atR sy K j) sy.Player_State = 1 → peek (StopRead.atR sy K j) sy.DiffToHaltJump = 1 := by
    rw [kp _ (by simp [CtrlKeep.keepA]), kp _ (by simp [CtrlKeep.keepA])]; exact hh
  have prev : peek (StopRead.atR sy K j) sy.PreviousA_B_Buttons &&& 0x80 = peek (StopRead.atR sy K j) sy.A_B_Buttons &&& 0x80 := by
    rw [kp _ (by simp [CtrlKeep.keepA]), kp _ (by simp [CtrlKeep.keepA])]; exact hp
  obtain ⟨d, hd, _, pc, _, vs, st2, halt2, hf⟩ := vert_airH hA (atV_of_atFrame hR.at_frame) st halt prev
  have eq := (FrameModel.trace_inFrame hR.time.loop hR.time.start hf hR.time.time d (Nat.le_refl d)).1
  have st3 : peek (stepN d (StopRead.atR sy K j)) sy.Player_State = 1 ∨ peek (stepN d (StopRead.atR sy K j)) sy.Player_State = 2 := by
    change (vsOf sy (stepN d (StopRead.atR sy K j))).st = 1 ∨ (vsOf sy (stepN d (StopRead.atR sy K j))).st = 2
    rw [vs]; exact st2
  rw [vs_of_keep kp] at vs
  exact ⟨CtrlKeep.arrAt sy (K.fm j) (K.pad j) + d, by omega, by omega, by rw [eq]; exact pc, by rw [eq]; exact vs,
    by rw [eq]; exact st3, by rw [eq]; exact halt2⟩

/-- The counted air frame at its end, with the same explicit five-byte condition. -/
theorem air_end (hA : vertAirOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : FrameModel.modelOK sy m0 (FrameModel.ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hidle : FrameModel.idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m)
    (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (he : VEnd sy K j)
    (hs : peek (seq (j - 1)) sy.Player_State = 1 ∨ peek (seq (j - 1)) sy.Player_State = 2)
    (hh : SurfaceFrames.HaltOK sy (seq (j - 1))) (hp : PrevKeep.PrevOK sy (seq (j - 1))) :
    vsOf sy (seq j) = vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy (seq (j - 1)))
      (peek (StopRead.atR sy K j) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
    (peek (seq j) sy.Player_State = 1 ∨ peek (seq j) sy.Player_State = 2) ∧
    SurfaceFrames.HaltOK sy (seq j) := by
  obtain ⟨k, k1, _, pc, vs, st, halt⟩ := air_subs hA hck hOK hfr hidle O hst Ar hv0 hP0 hg h1 (by omega) hs hh hp
  obtain ⟨ev, eh⟩ := end_vertical hck O hst Ar h1 h3 he k1 pc st
  have es : peek (seq j) sy.Player_State = peek (PipeEntryRule.trace (K.fm j) (K.pad j) k) sy.Player_State := congrArg Jump.VS.st ev
  exact ⟨ev.trans vs, by rw [es]; exact st, fun h => eh.trans (halt (es.symm.trans h))⟩

end Frames

/-! ## The arc whose states and takeoff class are read from the machines -/

/-- The first arc state, with the actual takeoff state and stored speed. -/
def initialArc (sy : Syms) (s : Jump.VS) (abs : UInt8) : Jump.Arc :=
  { s := s, k := 0, low := 0, above := if s.y.toNat < Jump.standY sy 1 then 0 else 1,
    fast := decide (sy.AirFastSpeed.toNat ≤ abs.toNat) }

def nextArc (sy : Syms) (s : Jump.VS) (x : Jump.Arc) : Jump.Arc :=
  { s := s, k := x.k + 1, low := if Jump.cornerY sy 1 ≤ s.y.toNat then x.k + 1 else x.low,
    above := if s.y.toNat < Jump.standY sy 1 then 0 else x.above + 1, fast := x.fast }

def arcFrom (sy : Syms) (v : Nat → Jump.VS) (abs : UInt8) (T : Nat) : Nat → Jump.Arc
  | 0 => initialArc sy (v T) abs
  | d + 1 => nextArc sy (v (T + d + 1)) (arcFrom sy v abs T d)

/-- `v` supplies actual machine states, e.g. frame ends before the touch and the
scroll handler at the touch. The stored speed is that read on the takeoff frame.
An arbitrary arc in `Run.direct` is not identified with this definition. -/
def arcM (sy : Syms) (v : Nat → Jump.VS) (abs : UInt8) (T n : Nat) : Jump.Arc := arcFrom sy v abs T (n - T)

theorem arcFrom_s (sy : Syms) (v : Nat → Jump.VS) (abs : UInt8) (T d : Nat) :
    (arcFrom sy v abs T d).s = v (T + d) := by
  cases d <;> simp [arcFrom, initialArc, nextArc, Nat.add_assoc]

theorem arcFrom_fast (sy : Syms) (v : Nat → Jump.VS) (abs : UInt8) (T d : Nat) :
    (arcFrom sy v abs T d).fast = decide (sy.AirFastSpeed.toNat ≤ abs.toNat) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem arcM_s {sy : Syms} {v : Nat → Jump.VS} {abs : UInt8} {T n : Nat} (h : T ≤ n) :
    (arcM sy v abs T n).s = v n := by
  rw [arcM, arcFrom_s, Nat.add_sub_of_le h]

/-- The old `reads` implication for this machine-defined arc needs no further hypothesis. -/
theorem arcM_reads {sy : Syms} {v : Nat → Jump.VS} {abs : UInt8} {T n : Nat}
    (h : (arcM sy v abs T n).fast = true) : sy.AirFastSpeed.toNat ≤ abs.toNat := by
  rw [arcM, arcFrom_fast, decide_eq_true_eq] at h
  exact h

/-- Takeoff membership in the original jump model on `vmach`.
The ground height and the stored-speed range are stated explicitly. -/
theorem arcM_start {sy : Syms} {m0 : Machine} {S : UInt8} {v : Nat → Jump.VS} {abs : UInt8} {T : Nat}
    (h : v T = jumpOff sy m0 S (Jump.groundY sy).toUInt8 abs)
    (hb : abs.toNat ≤ TopSpeed.top sy) :
    arcM sy v abs T T ∈ Jump.arcStart sy (vmach sy m0 S) (Jump.groundY sy) 1 := by
  simp only [Jump.arcStart, List.mem_eraseDups, List.mem_map, List.mem_range]
  refine ⟨abs.toNat, by omega, ?_⟩
  simp [arcM, arcFrom, initialArc, h, jumpOff, vstepV, flat, UInt8.ofNat_toNat]

theorem arcM_succ {sy : Syms} {v : Nat → Jump.VS} {abs : UInt8} {T n : Nat} (h : T ≤ n) :
    arcM sy v abs T (n + 1) = nextArc sy (v (n + 1)) (arcM sy v abs T n) := by
  unfold arcM
  rw [show n + 1 - T = (n - T) + 1 by omega, arcFrom]
  rw [show T + (n - T) + 1 = n + 1 by omega]

/-- One actual vertical step yields one model successor, provided the arc has not stopped. -/
theorem arcM_step {sy : Syms} {m0 : Machine} {v : Nat → Jump.VS} {abs : UInt8} {T n : Nat}
    (hn : T ≤ n) (go : (Jump.falling (v n) && decide (Jump.groundY sy ≤ (v n).y.toNat)) = false)
    (hs : ∃ a : Bool, v (n + 1) = Jump.vstep sy m0 (v n) a 0) :
    arcM sy v abs T (n + 1) ∈ Jump.arcSucc sy m0 1 (arcM sy v abs T n) := by
  obtain ⟨a, ha⟩ := hs
  simp only [Jump.arcSucc, arcM_s hn, go, Bool.false_eq_true, if_false]
  rw [arcM_succ hn]
  apply List.mem_map.2
  refine ⟨a, ?_, ?_⟩
  · cases a <;> simp
  · rw [ha]
    rfl

/-- These are precisely the extra links needed for `path`: actual takeoff, air steps,
no model stop before the touch, and the duration bound. None is asserted as a Run theorem here. -/
theorem path_of_frames {sy : Syms} {m0 : Machine} {S : UInt8} {v : Nat → Jump.VS} {abs : UInt8} {T g : Nat}
    (hg : T ≤ g) (hshort : g ≤ T + Jump.arcFrames)
    (hstart : v T = jumpOff sy m0 S (Jump.groundY sy).toUInt8 abs) (hb : abs.toNat ≤ TopSpeed.top sy)
    (hgo : ∀ j, T ≤ j → j < g → (Jump.falling (v j) && decide (Jump.groundY sy ≤ (v j).y.toNat)) = false)
    (hstep : ∀ j, T ≤ j → j < g → ∃ a : Bool, v (j + 1) = Jump.vstep sy (vmach sy m0 S) (v j) a 0) :
    PoleJoin.JumpPath sy (vmach sy m0 S) T g (arcM sy v abs T) :=
  ⟨hg, arcM_start hstart hb, fun j h1 h2 => arcM_step h1 (hgo j h1 h2) (hstep j h1 h2), hshort⟩

/-- At the touch, the height is the supplied machine state's height. -/
theorem arcM_atY {sy : Syms} {v : Nat → Jump.VS} {abs : UInt8} {T g : Nat} (h : T ≤ g) :
    (arcM sy v abs T g).s.y = (v g).y := by rw [arcM_s h]

/-- At the touch, rising is read from the supplied machine state's vertical speed. -/
theorem arcM_atRising {sy : Syms} {v : Nat → Jump.VS} {abs : UInt8} {T g : Nat} (h : T ≤ g) :
    Jump.falling (arcM sy v abs T g).s = Jump.falling (v g) := by rw [arcM_s h]

/-- The arc with its takeoff class read from the preceding counted machine. -/
def arcOf (sy : Syms) (seq : Nat → Machine) (v : Nat → Jump.VS) (T n : Nat) : Jump.Arc :=
  arcM sy v (peek (seq (T - 1)) sy.Player_XSpeedAbsolute) T n

/-- The exact stored-speed implication formerly assumed for an arbitrary fast arc. -/
theorem reads_of_machine_arc {sy : Syms} {seq : Nat → Machine} {v : Nat → Jump.VS} {T n : Nat}
    (h : (arcOf sy seq v T n).fast = true) :
    sy.AirFastSpeed.toNat ≤ (peek (seq (T - 1)) sy.Player_XSpeedAbsolute).toNat := arcM_reads h

end Smbrta.PoleJump
