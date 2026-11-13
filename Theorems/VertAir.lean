import Theorems.VertModel

/-!
# The movement routine in the air reads no stored speed

`VertModel.vert_model` relates the real routine to `vstep` with the real stored speed, and asks at the player's routine that the stored speed is `|v|` (`AtCtrl0`). Its walk does not
use that. In the air (the state 1 or 2) the routine reads the stored speed only in its horizontal part (`X_Physics`, a detour of the walk). So the same walk goes through with the
stored speed of `vstep`'s machine set to 0 and the real one not known (`vTagsA`, `caseOKA`), and with no condition on the stored speed at the player's routine (`AtV`). Then the
vertical bytes follow `vstep` with the stored speed 0 (`vert_air`). The proof is that of `vert_model`, with these two changes.

There is no game data in this file. Page: `1-1/c-7-5-1-RoomVert.md`.
-/

namespace Smbrta.VertAir

open VertModel
open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)

/-- what `vert_model`'s walk needs at the player's routine: `FrameModel.AtCtrl0` without the stored speed -/
structure AtV (sy : Syms) (E : Rom) (S : UInt8) (m : Machine) : Prop where
  good : Good E m
  pc : m.pc = sy.PlayerCtrlRoutine
  s : m.s = S
  eng : peek m sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8
  area : peek m sy.AreaType ∈ [(1 : UInt8), 2, 3]
  st : peek m sy.Player_State ∈ [(0 : UInt8), 1, 2]
  spring : peek m sy.JumpspringAnimCtrl = 0
  swim : peek m sy.SwimmingFlag = 0
  size : peek m sy.PlayerChangeSizeFlag = 0

/-- the tags of `VertModel.vTags`, but the stored speed: not known on the real machine, 0 on the machine of `vstep` -/
def vTagsA (sy : Syms) (m : Machine) (c : VCase) : List (Nat × Tag) :=
  (vIds sy).map (·, .eq) ++
  [(I sy.Player_State, Tag.kn c.st c.st), (I sy.Player_XSpeedAbsolute, .ab AB.top (AB.known 0)), (I sy.A_B_Buttons, Tag.kn c.ab (c.ab &&& 0x80)),
   (I sy.PreviousA_B_Buttons, .ab ⟨c.pv, 0x80⟩ (AB.known c.pv)), (I sy.GameEngineSubroutine, Tag.kn sy.Eng_PlayerCtrl.toUInt8 sy.Eng_PlayerCtrl.toUInt8),
   (I sy.JumpspringAnimCtrl, Tag.kn 0 (peek m sy.JumpspringAnimCtrl)), (I sy.SwimmingFlag, Tag.kn 0 (peek m sy.SwimmingFlag)),
   (I sy.PlayerChangeSizeFlag, Tag.kn 0 (peek m sy.PlayerChangeSizeFlag)),
   (I sy.DiffToHaltJump, if c.st == 1 then Tag.kn 1 1 else .ab AB.top (AB.known 1))]

/-- the cases in the air -/
def vCasesA : List VCase := vCases.filter fun c => c.st == 1 || c.st == 2

/-- a case of the movement routine in the air, on the two machines -/
def caseOKA (sy : Syms) (m0 : Machine) (S : UInt8) (c : VCase) : Bool :=
  let E := Rom.of m0
  FrameModel.tagsOK S (vTagsA sy (vmach sy m0 S) c) && walkD E (detours sy E S) (stopV E S) (goalV sy S) fuelV (leafQS sy.PlayerMovementSubs (S - 2) (vTagsA sy (vmach sy m0 S) c))

/-- **The check on the ROM**: `VertModel.vertOK`, and the cases in the air with the stored speed 0 -/
def vertAirOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool := vertOK sy m0 S && vCasesA.all (caseOKA sy m0 S)

section proof

variable {sy : Syms} {m0 : Machine}

/-- **The vertical movement of a real frame in the air.** From the player's routine to the scroll handler, the vertical bytes read from the machine follow `vstep` on the
machine `vmach`, with A of this frame and the stored speed 0. The conditions at the player's routine are those of `vert_model` but the stored speed. -/
theorem vert_air {S : UInt8} {R : Machine} (hOK : vertAirOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R)
    (hst : peek R sy.Player_State = 1 ∨ peek R sy.Player_State = 2)
    (hd : peek R sy.Player_State = 1 → peek R sy.DiffToHaltJump = 1)
    (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = peek R sy.A_B_Buttons &&& 0x80) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = vstepV sy m0 S (vsOf sy R) (peek R sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧ FrameModel.InFrameN (Rom.of m0) R k := by
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
  have hgoal : ∀ Q, goalV sy S Q = true → Q.w (stkI (vH sy m0 S s0 a ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 a ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.2 (stkI S) (.tail _ (.head _)), hQ.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', rel, fix, IX⟩ :=
    FrameModel.leafD_spec (ain := 0) F.ds hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨⟨_, heq⟩, hw⟩, hdt⟩ := hg
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
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, ?_, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL'))⟩
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
  · rw [eZ, vstepV_eq]
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

end proof

/-! ## The jumps' first frames: the machine of `vstep` does not matter

`RoomJoin`'s jumps run `vstep` on the machine at the start of the level, where the jump's halt value is 0; `vert_air` runs it on `vmach`, where it is 1 and the stack pointer is
the player's routine's. On the states of the jumps from the floor, up to `k` frames after the takeoff, the two give the same, and the state is 1 or 2 (`bridgeOK`). -/

section
open Jump (Arc arcStart arcSucc groundY)

/-- the states `n` steps of `f` after the states of `L` -/
def levels (f : Arc → List Arc) : List Arc → Nat → List Arc
  | L, 0 => L
  | L, n + 1 => levels f (L.flatMap f) n

/-- the states of the jumps from the floor, up to `k` frames after the takeoff -/
def arcSet (sy : Syms) (m : Machine) (h k : Nat) : List Arc :=
  (List.range (k + 1)).flatMap fun n => levels (arcSucc sy m h) (arcStart sy m (groundY sy) h) n

/-- **The check on the ROM**: on these states, `vstep` on `vmach` with the stored speed 0 is `vstep` on `m0`, and the state is 1 or 2 -/
def bridgeOK (sy : Syms) (m0 : Machine) (S : UInt8) (h k : Nat) : Bool :=
  (arcSet sy m0 h k).all fun u => (u.s.st == 1 || u.s.st == 2) &&
    [true, false].all fun a => VertModel.vstepV sy m0 S u.s a 0 == Jump.vstep sy m0 u.s a 0


theorem levels_reach {f : Arc → List Arc} {x u : Arc} {n : Nat} (hr : Cert.Reach f x n u) : ∀ {L : List Arc}, x ∈ L → u ∈ levels f L n := by
  induction hr with
  | refl s => exact fun hx => hx
  | step h1 _ ih => exact fun hx => ih (List.mem_flatMap.2 ⟨_, hx, h1⟩)

/-- a state of a jump from the floor, `n ≤ k` frames after the takeoff, is in `arcSet` -/
theorem mem_arcSet {sy : Syms} {m : Machine} {h k n : Nat} {x u : Arc} (hx : x ∈ arcStart sy m (groundY sy) h) (hr : Cert.Reach (arcSucc sy m h) x n u)
    (hn : n ≤ k) : u ∈ arcSet sy m h k :=
  List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega), levels_reach hr hx⟩

theorem bridge_of {sy : Syms} {m0 : Machine} {S : UInt8} {h k : Nat} (hb : bridgeOK sy m0 S h k = true) {u : Arc} (hu : u ∈ arcSet sy m0 h k) :
    (u.s.st = 1 ∨ u.s.st = 2) ∧ ∀ a, VertModel.vstepV sy m0 S u.s a 0 = Jump.vstep sy m0 u.s a 0 := by
  simp only [bridgeOK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  obtain ⟨h1, h2, h3⟩ := hb u hu
  refine ⟨h1, fun a => ?_⟩
  cases a
  · exact h3
  · exact h2

end


end Smbrta.VertAir
