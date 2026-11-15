import Theorems.VertAir

/-!
# The takeoff frame of a jump from a stand

`VertModel.vert_model` relates the movement routine of a real frame to `vstep` from the vertical bytes of the machine, with the stored speed that the frame reads. On a frame
that starts standing with a new press of A the routine starts a jump: it writes the height's fraction, the vertical speed and its fraction, the two forces, the jump's origin
and the state before it reads them. So the walk of two machines goes through with these six bytes not known on the real machine and 0 on the machine of `vstep` (`vTagsJ`,
`caseOKJ`): the vertical bytes after the routine are those of `vstep` from the state `flat y` (standing at the real height `y`, the other bytes 0) with A and the real stored
speed (`jumpOff`, `vert_jump`). They depend only on the height and the stored speed, and the walk knows at the routine's return that he is in a jump (the state 1) and rising.

There is no game data in this file. Page: `1-1/c-7-5-6-RoomJump.md`.
-/

namespace Smbrta.VertJump

open VertModel
open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)
open VertAir (AtV)

/-- the state a jump from a stand at the height `y` starts from, in the model: standing, the other vertical bytes 0, A not pressed on the frame before -/
def flat (y : UInt8) : Jump.VS := { y := y, mf := 0, vy := 0, dummy := 0, vf := 0, vfd := 0, origin := 0, st := 0, prevA := false }

/-- **The takeoff frame** from a stand at the height `y`, with the stored speed `abs`: `vstep` on `vmach` from `flat y`, with A -/
def jumpOff (sy : Syms) (m0 : Machine) (S : UInt8) (y abs : UInt8) : Jump.VS := vstepV sy m0 S (flat y) true abs

/-- the tags of the two machines when the routine is entered on a frame that starts standing with a new press of A (`ab` is the byte of A and B, with bit 7): the height and
the stored speed are the same; the six other vertical bytes are not known on the real machine and 0 on the machine of `vstep`; A of the frame before has bit 7 off -/
def vTagsJ (sy : Syms) (m : Machine) (ab : UInt8) : List (Nat × Tag) :=
  [(I sy.Player_Y_Position, .eq), (I sy.Player_Y_MoveForce, .ab AB.top (AB.known 0)), (I sy.Player_Y_Speed, .ab AB.top (AB.known 0)),
   (I sy.Player_YMF_Dummy, .ab AB.top (AB.known 0)), (I sy.VerticalForce, .ab AB.top (AB.known 0)), (I sy.VerticalForceDown, .ab AB.top (AB.known 0)),
   (I sy.JumpOrigin_Y_Position, .ab AB.top (AB.known 0)),
   (I sy.Player_State, Tag.kn 0 0), (I sy.Player_XSpeedAbsolute, .eq), (I sy.A_B_Buttons, Tag.kn ab 0x80),
   (I sy.PreviousA_B_Buttons, .ab ⟨0, 0x80⟩ (AB.known 0)), (I sy.GameEngineSubroutine, Tag.kn sy.Eng_PlayerCtrl.toUInt8 sy.Eng_PlayerCtrl.toUInt8),
   (I sy.JumpspringAnimCtrl, Tag.kn 0 (peek m sy.JumpspringAnimCtrl)), (I sy.SwimmingFlag, Tag.kn 0 (peek m sy.SwimmingFlag)),
   (I sy.PlayerChangeSizeFlag, Tag.kn 0 (peek m sy.PlayerChangeSizeFlag)),
   (I sy.DiffToHaltJump, .ab AB.top (AB.known 1))]

/-- the bytes of A and B with A pressed -/
def jCases : List UInt8 := [0x80, 0xC0]

/-- at the return, on a takeoff: `goalV`, and the state is known, the same on the two machines, and 1; the vertical speed is known, the same, and negative -/
def goalVJ (sy : Syms) (S : UInt8) (Q : TS) : Bool :=
  goalV sy S Q && (Q.ram (I sy.Player_State)).same == some 1 &&
    (match (Q.ram (I sy.Player_Y_Speed)).same with
     | some v => v &&& 0x80 == 0x80
     | none => false)

/-- a case of the movement routine on a takeoff, on the two machines -/
def caseOKJ (sy : Syms) (m0 : Machine) (S : UInt8) (ab : UInt8) : Bool :=
  let E := Rom.of m0
  FrameModel.tagsOK S (vTagsJ sy (vmach sy m0 S) ab) &&
    walkD E (detours sy E S) (stopV E S) (goalVJ sy S) fuelV (leafQS sy.PlayerMovementSubs (S - 2) (vTagsJ sy (vmach sy m0 S) ab))

/-- **The check on the ROM**: the two cases of a takeoff -/
def jumpOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool := jCases.all (caseOKJ sy m0 S)

section proof

variable {sy : Syms} {m0 : Machine}

theorem a80_cases : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0x80 → (UInt8.ofNat n.val &&& 0xC0 = 0x80 ∨ UInt8.ofNat n.val &&& 0xC0 = 0xC0) := by decide +kernel

/-- with A pressed the byte of A and B is one of `jCases` -/
theorem jcase_mem {x : UInt8} (h : x &&& 0x80 = 0x80) : x &&& 0xC0 ∈ jCases := by
  have := a80_cases ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  rcases this h with e | e <;> rw [e] <;> simp [jCases]

/-- **The vertical movement of a real frame that starts a jump.** At the player's routine he stands (the state 0), A is pressed and was not on the frame before. Then
from the player's routine to the scroll handler the vertical bytes read from the machine become `jumpOff` of the height and the stored speed there; and there he is in a
jump (the state 1) and rising. The conditions at the player's routine are those of `VertAir.vert_air` but the state. -/
theorem vert_jump {S : UInt8} {R : Machine} (hV : vertOK sy m0 S = true) (hJ : jumpOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R)
    (hst : peek R sy.Player_State = 0) (ha : peek R sy.SavedJoypadBits &&& 0x80 = 0x80) (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = jumpOff sy m0 S (peek R sy.Player_Y_Position) (peek R sy.Player_XSpeedAbsolute) ∧
      peek (stepN k R) sy.Player_State = 1 ∧ peek (stepN k R) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧ FrameModel.InFrameN (Rom.of m0) R k := by
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
  obtain ⟨⟨⟨⟨⟨_, heq⟩, hw⟩, _⟩, hst2⟩, hvy2⟩ := hg
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
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, hfin, hst1, hvy1, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL'))⟩
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

end proof

/-! ## On the ROM: a program, no part of the proof -/

/-- why a case fails -/
def caseWhyJ (sy : Syms) (m0 : Machine) (S : UInt8) (ab : UInt8) : List String :=
  let E := Rom.of m0
  match walkDWhy E (detours sy E S) (stopV E S) (goalVJ sy S) fuelV (leafQS sy.PlayerMovementSubs (S - 2) (vTagsJ sy (vmach sy m0 S) ab)) with
  | some (pc, w) => [s!"walk at {pc}: {w}"]
  | none => []

end Smbrta.VertJump
