import Theorems.OpenVert

/-!
# The movement routine standing, with no new press of A

`OpenVert.vert_airH` follows a real frame in the air from the player's routine to the scroll handler. Here the frame starts standing (the state 0) with no new press of
A: then the routine does not start a jump, and on the ground it moves him only sideways. The same walks of two machines, with the cases standing with no new press
(`vCasesS`), show that it comes to the scroll handler with the stack of the player's routine, and that no step on the way writes the height, the vertical speed and its
fraction, the state and the vertical page (`goalVS`: the walk does not write them, and the first and the last piece keep them). So at the scroll handler these five bytes
are those of the player's routine (`vert_stand`).

There is no game data in this file. Page: `1-1/c-7-5-14-FloorFrames.md`.
-/

namespace Smbrta.VertStand

open VertModel
open VertAir
open OpenVert
open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)

/-- the cases standing with no new press of A: the state 0, and A not pressed or pressed on the frame before -/
def vCasesS : List VCase := vCases.filter fun c => c.st == 0 && (!c.a || c.prevA)

/-- the bytes that the routine does not write, standing: the height, the vertical speed and its fraction, the state, the vertical page -/
def standKeep (sy : Syms) : List Nat :=
  [I sy.Player_Y_Position, I sy.Player_Y_Speed, I sy.Player_Y_MoveForce, I sy.Player_State, I sy.Player_Y_HighPos]

/-- at the return: `VertModel.goalV`, and no step has written the bytes of `standKeep` -/
def goalVS (sy : Syms) (S : UInt8) (Q : TS) : Bool := goalV sy S Q && (standKeep sy).all (fun i => !Q.w i)

/-- a case of the movement routine standing, with the high byte -/
def caseOKS (sy : Syms) (m0 : Machine) (S : UInt8) (c : VCase) : Bool :=
  let E := Rom.of m0
  FrameModel.tagsOK S (vTagsH sy (vmach sy m0 S) c) && walkD E (detoursH sy E S) (stopV E S) (goalVS sy S) fuelV (leafQS sy.PlayerMovementSubs (S - 2) (vTagsH sy (vmach sy m0 S) c))

/-- **The check on the ROM**: the cases standing with no new press. The proof uses `OpenVert.vertAirHOK` too: its first and last pieces and its detours keep the vertical
page -/
def standOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool := vCasesS.all (caseOKS sy m0 S)

section proof

variable {sy : Syms} {m0 : Machine}

theorem vcaseS_mem {c : VCase} (h1 : c ∈ vCases) (h2 : c.st = 0) (h3 : c.a = false ∨ c.prevA = true) : c ∈ vCasesS := by
  simp only [vCasesS, List.mem_filter]
  refine ⟨h1, ?_⟩
  rcases h3 with e | e <;> simp [h2, e]

/-- **The movement routine of a real frame standing with no new press of A.** From the player's routine (`AtV`, the state 0, bit 7 of the joypad's bits 0 or bit 7 of A of
the frame before 1, A on the frame before the A that the machine holds, the vertical page 1), the frame comes to the scroll handler with the stack of the player's
routine, and there the height, the vertical speed and its fraction, the state and the vertical page are those of the player's routine. -/
theorem vert_stand {S : UInt8} {R : Machine} (hHOK : vertAirHOK sy m0 S = true) (hOK : standOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R)
    (hhi : peek R sy.Player_Y_HighPos = 1)
    (hst : peek R sy.Player_State = 0)
    (hn : peek R sy.SavedJoypadBits &&& 0x80 = 0 ∨ peek R sy.PreviousA_B_Buttons &&& 0x80 = 0x80)
    (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = peek R sy.A_B_Buttons &&& 0x80) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      FrameModel.InFrameN (Rom.of m0) R k ∧ ∀ i ∈ standKeep sy, (stepN k R).ram.get! i = R.ram.get! i := by
  have hcaseS := hOK
  simp only [standOK, List.all_eq_true] at hcaseS
  have hH := hHOK
  simp only [vertAirHOK, Bool.and_eq_true, List.all_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨hA, hdsH⟩, hpreH⟩, _⟩, hlastH⟩, hvx⟩ := hH
  have hOK' := hA
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
  have hpre := hpreH pc hpm
  simp only [prefixOKH, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hpre
  obtain ⟨⟨⟨hpiece, hPpc⟩, hPs⟩, hK⟩ := hpre
  obtain ⟨kP, fP, AP, WP, IP⟩ := FrameModel.piece_specI hpiece hA0
  have IP' : FrameModel.InFrameN (Rom.of m0) R kP := fun j hj => (IP j hj).2.2
  have kX : ∀ q ∈ knownP sy (Rom.of m0) S pc, (stepN kP R).ram.get! q.1 = q.2 := fun q hq => AP.K q (List.contains_iff_mem.1 (hK q hq))
  have kmem : ∀ q, q ∈ knownP sy (Rom.of m0) S pc → (stepN kP R).ram.get! q.1 = q.2 := kX
  have wX : ∀ i ∈ watchPH sy, i < 2048 → (stepN kP R).ram.get! i = R.ram.get! i := WP
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
  have hvm : vc ∈ vCasesS := by
    refine vcaseS_mem (vcase_mem h.st abm) hst ?_
    show ((peek R sy.SavedJoypadBits &&& 0xC0) &&& 0x80 != 0) = false ∨ (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) = true
    rw [a80]
    rcases hn with e | e
    · exact Or.inl (by rw [e]; rfl)
    · exact Or.inr (by rw [e]; rfl)
  have hca := hcaseS vc hvm
  simp only [caseOKS, Bool.and_eq_true] at hca
  have hc := hca.2
  have htags := hca.1
  simp only [FrameModel.tagsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at htags
  have hpv : vc.pv = (if s0.prevA then 0x80 else 0) := by
    show (if (peek R sy.PreviousA_B_Buttons &&& 0x80 != 0) = true then (0x80 : UInt8) else 0) = if ((peek R sy.A_B_Buttons &&& 0x80) != 0) = true then 0x80 else 0
    rw [hp]
  have hvH : (vH sy m0 S s0 a ab).ram.get! (I sy.Player_Y_HighPos) = 1 := by
    simp only [beq_iff_eq, Bool.not_eq_true'] at hvx
    rw [show (vH sy m0 S s0 a ab).ram.get! (I sy.Player_Y_HighPos) = (vmach sy m0 S).ram.get! (I sy.Player_Y_HighPos) from
      FrameModel.pokeL_out _ _ (fun q hq e => by
        have h2 : I q.1 ∈ vIdx sy := by
          rw [show vIdx sy = (vList sy s0 a ab).map (fun q => I q.1) from rfl]
          exact List.mem_map.2 ⟨q, hq, rfl⟩
        rw [e] at h2
        have h3 := List.contains_iff_mem.2 h2
        rw [hvx.2] at h3
        cases h3)]
    exact hvx.1
  have hL : ∀ q ∈ vTagsH sy (vmach sy m0 S) vc, q.1 < 2048 ∧ q.1 ≠ stkI (vH sy m0 S s0 a ab).s ∧ q.1 ≠ stkI ((vH sy m0 S s0 a ab).s - 1) ∧
      q.2.R (X.ram.get! q.1) ((vH sy m0 S s0 a ab).ram.get! q.1) := by
    intro q hq
    obtain ⟨⟨t1, t2⟩, t3⟩ := htags q hq
    rw [hHs]
    refine ⟨t1, t2, t3, ?_⟩
    have wv : ∀ u : UInt16, I u ∈ watchPH sy → X.ram.get! (I u) = peek R u := fun u hu => wX _ hu (FrameModel.I_lt _)
    simp only [vTagsH, vTagsA, vIds, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      have e2 : (vc.st == 1) = false := by simp [vc, hst]
      simp only [e2, Bool.false_eq_true, if_false]
      exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
    · -- the high byte of the height: 1 on both machines
      have e1 : X.ram.get! (I sy.Player_Y_HighPos) = peek R sy.Player_Y_HighPos :=
        wv sy.Player_Y_HighPos (List.mem_append_right _ (.tail _ (.tail _ (.tail _ (.head _)))))
      show X.ram.get! (I sy.Player_Y_HighPos) = (vH sy m0 S s0 a ab).ram.get! (I sy.Player_Y_HighPos)
      rw [e1, hhi, hvH]
  -- the walk with detours, to the routine's return
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalVS sy S Q = true → Q.w (stkI (vH sy m0 S s0 a ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 a ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalVS, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.1.2 (stkI S) (.tail _ (.head _)), hQ.1.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', _, fix, IX⟩ :=
    FrameModel.leafD_spec (ain := 0) hdsH hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalVS, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨_, hw⟩, _⟩, hkeep⟩ := hg
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
  obtain ⟨kL, fL, AL, WL, IL⟩ := FrameModel.piece_specI hlastH hAY
  have I1 : FrameModel.InFrameN (Rom.of m0) (stepN k X) 1 := fun j hj => by
    rw [show j = 0 by omega]
    show FrameModel.InFrame (Rom.of m0) (stepN k X)
    exact FrameModel.inFrame_rts gX' (by rw [pcX']; exact p1) (by rw [pcX']; exact p2) (by rw [pcX']; exact p3)
  have IL' : FrameModel.InFrameN (Rom.of m0) (stepN 1 (stepN k X)) kL := fun j hj => (IL j hj).2.2
  have wZ : ∀ i ∈ watchRH sy, i < 2048 → (stepN kL (stepN 1 (stepN k X))).ram.get! i = (stepN k X).ram.get! i := by
    intro i hi hl
    rw [WL i hi hl, y3]
  have eZ : stepN (kP + (k + (1 + kL))) R = stepN kL (stepN 1 (stepN k X)) := by
    rw [FrameModel.stepN_add, hX, FrameModel.stepN_add, FrameModel.stepN_add]
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL')), ?_⟩
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
  · -- the five bytes: kept by the first piece, not written by the walk, kept by the last piece
    intro i hi
    have hX5 : X.ram.get! i = R.ram.get! i := by
      simp only [standKeep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact wX _ (by simp [watchPH, vIds]) (FrameModel.I_lt _)
      · exact wX _ (by simp [watchPH, vIds]) (FrameModel.I_lt _)
      · exact wX _ (by simp [watchPH, vIds]) (FrameModel.I_lt _)
      · exact kmem (I sy.Player_State, pc.st) (.tail _ (.head _))
      · exact wX _ (by simp [watchPH]) (FrameModel.I_lt _)
    have hi2 : i < 2048 := by
      simp only [standKeep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact FrameModel.I_lt _
    have hW : i ∈ watchRH sy := by
      simp only [standKeep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [watchRH, vIds]
    rw [eZ, wZ i hW hi2, fix i hi2 (hkeep i hi), hX5]

end proof

end Smbrta.VertStand
