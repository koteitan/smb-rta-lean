import Theorems.RoomJump
import Theorems.RoomFall

/-!
# The vertical page through the rising frames of a jump

`VertJump.vert_jump` gives the vertical bytes at the scroll handler of a takeoff frame, but not the vertical page (`Player_Y_HighPos`): the movement routine adds the carry
of the height into it. Here the walk of two machines of `vert_jump` follows it too, as `OpenVert.vert_airH` does for a frame in the air: it is 1 on both machines at the
player's routine (`.eq`), and at the scroll handler it is that of the machine of `vstep` (`vert_jumpH`).

From the scroll handler to the frame's end, when he is in the air and rising there, the walk `walkB` of `RoomVert` keeps the vertical page too (`RoomVert.after_QP`). So on
a takeoff frame (`jump_roomH`) and on a frame in the air that rises at the end of its move (`air_roomH`) the vertical page at the frame's end is the one at the end of its
move, and that is the page of the machine of `vstep`. The checks `offCheck` and `arcCheckH` say that it is 1 on a takeoff from the floor and on the states of a jump's first
frames.

There is no game data in this file. Page: `1-1/c-7-5-18-RoomHigh.md`.
-/

namespace Smbrta.RoomHigh

open VertModel
open VertAir
open VertJump (flat jumpOff vTagsJ goalVJ jCases jcase_mem)
open OpenVert (detoursH prefixOKH lastOKH watchPH watchRH vertAirHOK)
open FrameModel (Rom Cut TS Tag FT Detour detourQ walkD walkDWhy pieceOK goalC I stkI lookN AtCtrl firstEnd cutOf firstRtsS findPat startQ tagImp leafQS isRts
  pokeL nodupB stepN At Good GoodH)
open TaintRun (AB)

/-- the tags of `VertJump.vTagsJ`, and the vertical page the same on the two machines -/
def vTagsJH (sy : Syms) (m : Machine) (ab : UInt8) : List (Nat × Tag) := vTagsJ sy m ab ++ [(I sy.Player_Y_HighPos, .eq)]

/-- at the return, on a takeoff: `VertJump.goalVJ`, and the vertical page the same on the two machines -/
def goalVJH (sy : Syms) (S : UInt8) (Q : TS) : Bool := goalVJ sy S Q && tagImp (Q.ram (I sy.Player_Y_HighPos)) .eq

/-- a case of the movement routine on a takeoff, with the vertical page -/
def caseOKJH (sy : Syms) (m0 : Machine) (S : UInt8) (ab : UInt8) : Bool :=
  let E := Rom.of m0
  FrameModel.tagsOK S (vTagsJH sy (vmach sy m0 S) ab) &&
    walkD E (detoursH sy E S) (stopV E S) (goalVJH sy S) fuelV (leafQS sy.PlayerMovementSubs (S - 2) (vTagsJH sy (vmach sy m0 S) ab))

/-- **The check on the ROM**: `OpenVert.vertAirHOK` (the walks of the routine in the air with the vertical page, and the page 1 on the machine of `vstep`), and the two
cases of a takeoff with the vertical page -/
def jumpHOK (sy : Syms) (m0 : Machine) (S : UInt8) : Bool := vertAirHOK sy m0 S && jCases.all (caseOKJH sy m0 S)

section proof

variable {sy : Syms} {m0 : Machine}

/-- **The vertical movement of a real frame that starts a jump, with the vertical page.** `VertJump.vert_jump`, when the vertical page is 1 at the player's routine; and
the vertical page at the scroll handler is that of the machine of `vstep` after the routine (`VertModel.vRun`) from `flat y` with A and the stored speed. -/
theorem vert_jumpH {S : UInt8} {R : Machine} (hOK : jumpHOK sy m0 S = true) (h : AtV sy (Rom.of m0) S R) (hhi : peek R sy.Player_Y_HighPos = 1)
    (hst : peek R sy.Player_State = 0) (ha : peek R sy.SavedJoypadBits &&& 0x80 = 0x80) (hp : peek R sy.PreviousA_B_Buttons &&& 0x80 = 0) :
    ∃ k, k ≤ FrameModel.moveLen ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = sy.PlayerSubs ∧ (stepN k R).s = S ∧
      vsOf sy (stepN k R) = jumpOff sy m0 S (peek R sy.Player_Y_Position) (peek R sy.Player_XSpeedAbsolute) ∧
      peek (stepN k R) sy.Player_State = 1 ∧ peek (stepN k R) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧ FrameModel.InFrameN (Rom.of m0) R k ∧
      peek (stepN k R) sy.Player_Y_HighPos =
        peek (vRun sy m0 S (flat (peek R sy.Player_Y_Position)) true (peek R sy.Player_XSpeedAbsolute)) sy.Player_Y_HighPos := by
  have hH := hOK
  simp only [jumpHOK, vertAirHOK, Bool.and_eq_true, List.all_eq_true] at hH
  obtain ⟨⟨⟨⟨⟨⟨hA, hdsH⟩, hpreH⟩, _⟩, hlastH⟩, hvx⟩, hJ'⟩ := hH
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
  have hca := hJ' _ hjm
  simp only [caseOKJH, Bool.and_eq_true] at hca
  have hc := hca.2
  have htags := hca.1
  simp only [FrameModel.tagsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at htags
  have hvH : (vH sy m0 S s0 true ab).ram.get! (I sy.Player_Y_HighPos) = 1 := by
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hvx
    rw [show (vH sy m0 S s0 true ab).ram.get! (I sy.Player_Y_HighPos) = (vmach sy m0 S).ram.get! (I sy.Player_Y_HighPos) from
      FrameModel.pokeL_out _ _ (fun q hq e => by
        have h2 : I q.1 ∈ vIdx sy := by
          rw [show vIdx sy = (vList sy s0 true ab).map (fun q => I q.1) from rfl]
          exact List.mem_map.2 ⟨q, hq, rfl⟩
        rw [e] at h2
        have h3 := List.contains_iff_mem.2 h2
        rw [hvx.2] at h3
        cases h3)]
    exact hvx.1
  have hL : ∀ q ∈ vTagsJH sy (vmach sy m0 S) (peek R sy.SavedJoypadBits &&& 0xC0), q.1 < 2048 ∧ q.1 ≠ stkI (vH sy m0 S s0 true ab).s ∧
      q.1 ≠ stkI ((vH sy m0 S s0 true ab).s - 1) ∧ q.2.R (X.ram.get! q.1) ((vH sy m0 S s0 true ab).ram.get! q.1) := by
    intro q hq
    obtain ⟨⟨t1, t2⟩, t3⟩ := htags q hq
    rw [hHs]
    refine ⟨t1, t2, t3, ?_⟩
    have wv : ∀ u : UInt16, I u ∈ watchPH sy → X.ram.get! (I u) = peek R u := fun u hu => wX _ hu (FrameModel.I_lt _)
    have top0 : ∀ (x y : UInt8), y = 0 → (Tag.ab AB.top (AB.known 0)).R x y := fun x y e => by
      rw [e]
      exact ⟨TaintRun.mem_top _, TaintRun.mem_known_self _⟩
    simp only [vTagsJH, vTagsJ, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · -- the high byte of the height: 1 on both machines
      have e1 : X.ram.get! (I sy.Player_Y_HighPos) = peek R sy.Player_Y_HighPos :=
        wv sy.Player_Y_HighPos (List.mem_append_right _ (.tail _ (.tail _ (.tail _ (.head _)))))
      show X.ram.get! (I sy.Player_Y_HighPos) = (vH sy m0 S s0 true ab).ram.get! (I sy.Player_Y_HighPos)
      rw [e1, hhi, hvH]
  -- the walk with detours, to the routine's return
  have hstop : ∀ Q, stopV (Rom.of m0) S Q = true → 0x8000 ≤ Q.pc ∧ FrameModel.lookupOp ((Rom.of m0).b Q.pc) FrameModel.insList = some .rts ∧
      FrameModel.idleAt (Rom.of m0) Q.pc = false ∧ Q.s = some (S - 2) := by
    intro Q hQ
    simp only [stopV, isRts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hQ
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hQ
    exact ⟨h1, by rw [h2]; exact FrameModel.lookup_rts, h3, h4⟩
  have hgoal : ∀ Q, goalVJH sy S Q = true → Q.w (stkI (vH sy m0 S s0 true ab).s) = false ∧ Q.w (stkI ((vH sy m0 S s0 true ab).s - 1)) = false := by
    intro Q hQ
    rw [hHs]
    simp only [goalVJH, goalVJ, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hQ
    exact ⟨hQ.1.1.1.1.2 (stkI S) (.tail _ (.head _)), hQ.1.1.1.1.2 (stkI (S - 1)) (.tail _ (.tail _ (.head _)))⟩
  obtain ⟨k, Q, hk, hs, hg, gX', pcX', sX', rel, fix, IX⟩ :=
    FrameModel.leafD_spec (ain := 0) hdsH hc (by decide) hstop hgoal AP.good (by rw [AP.pc, hPpc]) (by rw [AP.s, hPs]) gH (by rw [hHs]) hL
  simp only [goalVJH, goalVJ, goalV, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨_, heq⟩, hw⟩, _⟩, hst2⟩, hvy2⟩, hhiq⟩ := hg
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
  refine ⟨kP + (k + (1 + kL)), ?_, ?_, ?_, ?_, hfin, hst1, hvy1, FrameModel.InFrameN.add' IP' hX (FrameModel.InFrameN.add' IX rfl (FrameModel.InFrameN.add' I1 rfl IL')), ?_⟩
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
  · -- the high byte of the height: kept by the last piece, the same on the two machines at the return
    show peek (stepN (kP + (k + (1 + kL))) R) sy.Player_Y_HighPos = peek (vRun sy m0 S s0 true ab) sy.Player_Y_HighPos
    rw [eZ, peek_I, peek_I, wZ (I sy.Player_Y_HighPos) (List.mem_append_right _ (.tail _ (.tail _ (.tail _ (.head _))))) (FrameModel.I_lt _)]
    exact FrameModel.tagImp_R hhiq (rel _ (FrameModel.I_lt _))

end proof

/-! ## The frames of the room -/

section room

open PipeTransition (frame)
open PipeEntryRule (trace)
open PipeTransitionAll (Names)
open ScreenPage (Places SiteOK RoomCond)
open TaintRun (Env)
open RoomVert (OKV phA phB finB apartB apartH vKeep vKeepA vKeepH before_R after_QP Rising)

/-- **A frame of the room that starts a jump, with the vertical page.** As `RoomJump.jump_frame`, with the vertical page 1 at the frame's start. The frame comes to the end of
its move `j` once; there he is in the state 1 and rising, with the vertical bytes of `jumpOff` and the vertical page of the machine of `vstep`; and from there to the
frame's end no step writes the bytes of `vKeepH` (the vertical bytes and the vertical page). `j` is a state of the walk: `Good`, with the stack of the player's routine. -/
theorem jump_frameH {sy : Syms} {m0 : Machine} {S S' : UInt8} {pz : Nat} {E : Env} {P : Places} {r : Machine} {K : List (Nat × UInt8)} {CA CB : ScreenPage.CfgS}
    {Fa Fb : Nat} (hpz : pz < 2048) (hA : OKV (phA sy E S' pz) E P r K CA Fa) (hfA : ∀ B, CA.fin B = true → B.pc ≠ sy.PlayerCtrlRoutine)
    (hB : OKV (phB sy E P) E P r K CB Fb) (hfin : CB.fin = finB P r) (hap : apartB sy P = true) (hapH : apartH sy P = true) (hJ : jumpHOK sy m0 S = true)
    {idle : UInt16} (hidle : FrameModel.idleAt (Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond E r K M) (hk : ∀ j, SiteOK P (trace M i j)) (hR : AtV sy (Rom.of m0) S (trace M i k))
    (ht : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true) (hhi : peek M sy.Player_Y_HighPos = 1)
    (hrt : (frame M i).ram.get! P.rtI = r.ram.get! P.rtI) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ Good (Rom.of m0) (trace M i j) ∧ (trace M i j).s = S ∧
      vsOf sy (trace M i j) = jumpOff sy m0 S (peek M sy.Player_Y_Position) (peek (trace M i k) sy.Player_XSpeedAbsolute) ∧
      peek (trace M i j) sy.Player_State = 1 ∧ peek (trace M i j) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧
      peek (trace M i j) sy.Player_Y_HighPos =
        peek (vRun sy m0 S (flat (peek M sy.Player_Y_Position)) true (peek (trace M i k) sy.Player_XSpeedAbsolute)) sy.Player_Y_HighPos ∧
      (∀ x ∈ vKeepH sy, (frame M i).ram.get! x = (trace M i j).ram.get! x) ∧
      (∀ j', k ≤ j' → (trace M i j').pc = sy.PlayerSubs → (trace M i j').frame = M.frame → j' = j) := by
  obtain ⟨a1, a2, _, a4⟩ := before_R hpz hA hfA hm hk
  have hfk : (trace M i k).frame = M.frame := a4 k hR.pc
  have hfirst : ∀ j, j < k → (trace M i j).pc ≠ sy.PlayerCtrlRoutine := fun j hj hR' => a2 j k hj hR' hfk hR.pc
  have hkeep := a1 k hfk hfirst
  have eq : ∀ a : UInt16, RoomVert.I a ∈ vKeepA sy → peek (trace M i k) a = peek M a := fun a ha => hkeep _ ha
  obtain ⟨p1, p2, p3⟩ := RoomJump.press_of hj
  have hhiR : peek (trace M i k) sy.Player_Y_HighPos = 1 := by
    rw [eq sy.Player_Y_HighPos (by simp [vKeepA])]
    exact hhi
  obtain ⟨kk, _, hg, hpc, hs, hv, hs1, hvy, hIn, hhq⟩ := vert_jumpH hJ hR hhiR p1 p2 p3
  rw [eq sy.Player_Y_Position (by simp [vKeepA, vKeep])] at hv hhq
  obtain ⟨htr, hfq⟩ := FrameModel.trace_inFrame hidle hfk hIn ht kk (Nat.le_refl kk)
  rw [← htr] at hpc hv hs1 hvy hg hs hhq
  obtain ⟨uniq, b2⟩ := after_QP hB hfin hap hapH hm hk
  have hrs : Rising sy (trace M i (k + kk)) := ⟨Or.inl hs1, hvy⟩
  refine ⟨k + kk, Nat.le_add_right _ _, hpc, hfq, hg, hs, hv, hs1, hvy, hhq, b2 (k + kk) hpc hfq hrs hrt, fun j' _ hj2 hj3 => ?_⟩
  rcases Nat.lt_trichotomy j' (k + kk) with e | e | e
  · exact absurd hpc (uniq j' (k + kk) e hj2 hfq)
  · exact e
  · exact absurd hj2 (uniq (k + kk) j' e hpc hj3)

/-- **A frame of the room that starts a jump, with the vertical page**, on the room: `jump_frameH` with the checks of `RoomVert` -/
theorem jump_roomH {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk)
    (hJ : jumpHOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hapH : apartH sy (ScreenPage.placesR sy nm m0) = true) {idle : UInt16}
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hj : (FrameModel.readIn sy (trace M i k)).jump = true) (hhi : peek M sy.Player_Y_HighPos = 1)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ Good (Rom.of m0) (trace M i j) ∧
      (trace M i j).s = FrameModel.ctrlStack sy m0 ∧
      vsOf sy (trace M i j) = jumpOff sy m0 (FrameModel.ctrlStack sy m0) (peek M sy.Player_Y_Position) (peek (trace M i k) sy.Player_XSpeedAbsolute) ∧
      peek (trace M i j) sy.Player_State = 1 ∧ peek (trace M i j) sy.Player_Y_Speed &&& 0x80 = 0x80 ∧
      peek (trace M i j) sy.Player_Y_HighPos =
        peek (vRun sy m0 (FrameModel.ctrlStack sy m0) (flat (peek M sy.Player_Y_Position)) true (peek (trace M i k) sy.Player_XSpeedAbsolute)) sy.Player_Y_HighPos ∧
      (∀ x ∈ vKeepH sy, (frame M i).ram.get! x = (trace M i j).ram.get! x) ∧
      (∀ j', k ≤ j' → (trace M i j').pc = sy.PlayerSubs → (trace M i j').frame = M.frame → j' = j) :=
  jump_frameH (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB) (RoomVert.okV_of_check hV.b) rfl hV.apart hapH hJ hidle
    hm hs hR htm hj hhi hrt

/-- **A frame of the room in the air, with the vertical page.** The frame starts in the air with the vertical page 1. It comes to the end of its move `j` once (`Good`, with
the stack of the player's routine), with the vertical bytes of `vstep` on `vmach` and its vertical page (`RoomFall.land_frame`, `RoomFall.high_room`); if there he is in the
air and rising, no step from there to the frame's end writes the bytes of `vKeepH` (`RoomVert.after_QP`) -/
theorem air_roomH {sy : Syms} {nm : Names} {m0 : Machine} {h kk : Nat} (hV : RoomVert.VChecks sy nm m0 h kk) (hF : RoomFall.FChecks sy nm m0 h)
    (hH : OpenVert.vertAirHOK sy m0 (FrameModel.ctrlStack sy m0) = true) (hapH : apartH sy (ScreenPage.placesR sy nm m0) = true) {idle : UInt16}
    (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) idle = true) {M : Machine} {i : UInt8} {k : Nat}
    (hm : RoomCond (ScreenPage.envR sy nm m0) (ScreenPage.refR m0) (RoomMap.knownT sy nm m0) M) (hs : ∀ j, SiteOK (ScreenPage.placesR sy nm m0) (trace M i j))
    (hR : AtV sy (FrameModel.Rom.of m0) (FrameModel.ctrlStack sy m0) (trace M i k))
    (htm : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hst : peek M sy.Player_State = 1 ∨ peek M sy.Player_State = 2)
    (hd : peek M sy.Player_State = 1 → peek M sy.DiffToHaltJump = 1)
    (hp : peek M sy.PreviousA_B_Buttons &&& 0x80 = peek M sy.A_B_Buttons &&& 0x80)
    (hhi : peek M sy.Player_Y_HighPos = 1)
    (hrt : (frame M i).ram.get! (ScreenPage.placesR sy nm m0).rtI = (ScreenPage.refR m0).ram.get! (ScreenPage.placesR sy nm m0).rtI) :
    ∃ j, k ≤ j ∧ (trace M i j).pc = sy.PlayerSubs ∧ (trace M i j).frame = M.frame ∧ Good (Rom.of m0) (trace M i j) ∧
      (trace M i j).s = FrameModel.ctrlStack sy m0 ∧
      vsOf sy (trace M i j) = vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0 ∧
      peek (trace M i j) sy.Player_Y_HighPos =
        peek (vRun sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0) sy.Player_Y_HighPos ∧
      (((vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 1 ∨
        (vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).st = 2) →
        (vstepV sy m0 (FrameModel.ctrlStack sy m0) (vsOf sy M) (peek (trace M i k) sy.SavedJoypadBits &&& 0x80 != 0) 0).vy &&& 0x80 = 0x80 →
        ∀ x ∈ vKeepH sy, (frame M i).ram.get! x = (trace M i j).ram.get! x) ∧
      (∀ j', k ≤ j' → (trace M i j').pc = sy.PlayerSubs → (trace M i j').frame = M.frame → j' = j) := by
  obtain ⟨j, hkj, hq, hf, hg, hs', hv, _⟩ := RoomFall.land_frame (CtrlKeep.pauseI_lt sy m0) (RoomVert.okV_of_check hV.a) (fun B hB => RoomVert.finA_pc hB)
    (RoomVert.okV_of_check hF.c) rfl hF.apart hV.air hidle hm hs hR htm hst hd hp hrt
  have hh := RoomFall.high_room hV hF hH hidle hm hs hR htm hst hd hp hhi
  obtain ⟨uniq, b2⟩ := RoomVert.after_QP (RoomVert.okV_of_check hV.b) RoomVert.cfgOfV_fin hV.apart hapH hm hs
  refine ⟨j, hkj, hq, hf, hg, hs', hv, hh.1 j hkj hq hf, fun h1 h2 => b2 j hq hf ⟨?_, ?_⟩ hrt, fun j' _ hj2 hj3 => ?_⟩
  · have e : (vsOf sy (trace M i j)).st = (trace M i j).ram.get! (RoomVert.I sy.Player_State) := rfl
    rw [← e, hv]
    exact h1
  · have e : (vsOf sy (trace M i j)).vy = (trace M i j).ram.get! (RoomVert.I sy.Player_Y_Speed) := rfl
    rw [← e, hv]
    exact h2
  · rcases Nat.lt_trichotomy j' j with e | e | e
    · exact absurd hq (uniq j' j e hj2 hf)
    · exact e
    · exact absurd hj2 (uniq j j' e hq hj3)

end room

/-! ## The checks on the ROM -/

/-- the takeoff from the floor, for every stored speed: the vertical page 1 after the movement routine on the machine of `vstep`, and the height at the end of the move from
`ylo` to the floor's height -/
def offCheck (sy : Syms) (m0 : Machine) (ylo : Nat) : Bool :=
  (List.range 256).all fun ab =>
    peek (vRun sy m0 (FrameModel.ctrlStack sy m0) (flat (Jump.groundY sy).toUInt8) true ab.toUInt8) sy.Player_Y_HighPos == 1 &&
      decide (ylo ≤ (jumpOff sy m0 (FrameModel.ctrlStack sy m0) (Jump.groundY sy).toUInt8 ab.toUInt8).y.toNat) &&
      decide ((jumpOff sy m0 (FrameModel.ctrlStack sy m0) (Jump.groundY sy).toUInt8 ab.toUInt8).y.toNat ≤ Jump.groundY sy)

/-- the states of a jump's first `k` frames from the floor (`VertAir.arcSet`): the state 1, the height at most the floor's, and the vertical page 1 after the movement routine
on the machine of `vstep`, with A or not -/
def arcCheckH (sy : Syms) (m0 : Machine) (h k : Nat) : Bool :=
  (VertAir.arcSet sy m0 h k).all fun u => u.s.st == 1 && decide (u.s.y.toNat ≤ Jump.groundY sy) &&
    [true, false].all fun a => peek (vRun sy m0 (FrameModel.ctrlStack sy m0) u.s a 0) sy.Player_Y_HighPos == 1

/-- **The checks on the ROM of this file** -/
structure Checks (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) (h k ylo : Nat) : Prop where
  jump : jumpHOK sy m0 (FrameModel.ctrlStack sy m0) = true
  apart : RoomVert.apartH sy (ScreenPage.placesR sy nm m0) = true
  off : offCheck sy m0 ylo = true
  arc : arcCheckH sy m0 h k = true
  ylo_le : ylo ≤ Jump.cornerY sy h + 16

theorem off_spec {sy : Syms} {m0 : Machine} {ylo : Nat} (h : offCheck sy m0 ylo = true) (ab : UInt8) :
    peek (vRun sy m0 (FrameModel.ctrlStack sy m0) (flat (Jump.groundY sy).toUInt8) true ab) sy.Player_Y_HighPos = 1 ∧
      ylo ≤ (jumpOff sy m0 (FrameModel.ctrlStack sy m0) (Jump.groundY sy).toUInt8 ab).y.toNat ∧
      (jumpOff sy m0 (FrameModel.ctrlStack sy m0) (Jump.groundY sy).toUInt8 ab).y.toNat ≤ Jump.groundY sy := by
  unfold offCheck at h
  have := List.all_eq_true.1 h ab.toNat (List.mem_range.2 ab.toNat_lt)
  simp only [UInt8.ofNat_toNat, Nat.toUInt8_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem arc_specH {sy : Syms} {m0 : Machine} {h k : Nat} (hc : arcCheckH sy m0 h k = true) {u : Jump.Arc} (hu : u ∈ VertAir.arcSet sy m0 h k) :
    u.s.st = 1 ∧ u.s.y.toNat ≤ Jump.groundY sy ∧ ∀ a, peek (vRun sy m0 (FrameModel.ctrlStack sy m0) u.s a 0) sy.Player_Y_HighPos = 1 := by
  unfold arcCheckH at hc
  have := List.all_eq_true.1 hc u hu
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_cons, List.all_nil, Bool.and_true] at this
  refine ⟨this.1.1, this.1.2, fun a => ?_⟩
  cases a
  · exact this.2.2
  · exact this.2.1

end Smbrta.RoomHigh
