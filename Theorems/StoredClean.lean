import Theorems.FrameModel

/-! # The stored speed of a frame that follows the model

`FrameModel.stored_path` takes the frame at its player's routine in the state `AtFrame`: the collision bits are one of `TopSpeed.collBits`, because its stage of
`ImposeFriction` is compared with `TopSpeed.frictionCheck`, which runs the routine on those values of the bits. A frame that follows the model comes to its player's
routine in the state `AtCtrl`: the stored speed is `|v|` and the side he presses is not masked (`bits &&& lr = lr`), but nothing is known of the other bits.

`ImposeFriction` reads the bits once, in `and` with the pressed side `lr`. So with `bits &&& lr = lr` it takes the way it takes with the bits `0xFF`. Here the walk of
`ImposeFriction` compares the real machine, whose bits are known only on `lr` (to be 1), with the model's machine with the bits `0xFF` (`tagsFrM`, `storedFricM`); then
`frictionCheck` on the bits `0xFF` gives the stored speed `|v|` at the mover (`fric_absM`). `stored_c4M` and `stored_pathM` are `stored_c4` and `stored_path` on this stage:
a frame at its player's routine in the state `AtCtrl`, with the speed in `TopSpeed`'s range, comes to the scroll handler with the stored speed `|v|`.

There is no game data in this file. Page: `1-1/c-7-4-4-StoredClean.md`.
-/

namespace Smbrta.FrameModel

open Potential (HS HIn hstep hstepN norm)
open TopSpeed (absB)
open TaintRun (AB bt)
open PipeTransition (frame)
open PipeEntryRule (trace trace_stop nxt)

section storedM
variable {sy : Syms} {E : Rom}

/-- the friction's tags of `storedFricOK`, but the collision bits: on the real machine they are known only on the side `lr` (to be 1), on the model's machine they
are `0xFF` -/
def tagsFrM (sy : Syms) (lr : UInt8) : List (Nat × Tag) :=
  [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq), (I sy.FrictionAdderLow, .eq), (I sy.FrictionAdderHigh, .eq), (I sy.MaximumRightSpeed, .eq),
   (I sy.MaximumLeftSpeed, .eq), (I sy.Player_CollisionBits, .ab ⟨lr, lr⟩ (AB.known 0xFF))]

/-- `storedFricOK` with the tags `tagsFrM`: `ImposeFriction` on the real machine with the side `lr` not masked, next to the model's machine with the bits `0xFF`, with
the speed and the stored speed out -/
def storedFricM (sy : Syms) (m0 : Machine) (S : UInt8) (c : Case) : Bool :=
  let P := planOf sy m0 S c
  let lr := lrOf c.n
  (stOf c.n != 0 && lr == 0) ||
    leafAll (Rom.of m0) m0.s sy.ImposeFriction P.r3 (Tag.kn lr lr) (tagsFrM sy lr) [(I sy.Player_X_Speed, .eq), (I sy.Player_XSpeedAbsolute, .eq)] P.c3.ids

/-- **The check on the ROM**: `storedFricM` on every case -/
def storedM (sy : Syms) (m0 : Machine) (S : UInt8) : Bool :=
  allCases.all (storedFricM sy m0 S)

theorem and_self8 (x : UInt8) : x &&& x = x := UInt8.and_self

/-- `fric_abs` with the side `lr` not masked in place of the bits' range: the model's machine has the bits `0xFF` -/
theorem fric_absM {m0 : Machine} {c3 c4 : Cut} {r3 : UInt16} {lr : UInt8} {R : Machine} {mr ml lo hi : UInt8}
    (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hnd : nodupB (fricIdx sy) = true) (hsp : (TopSpeed.speedsB sy).contains (R.ram.get! (I sy.Player_X_Speed)) = true)
    (h1 : leafAll (Rom.of m0) m0.s sy.ImposeFriction r3 (Tag.kn lr lr) (tagsFrM sy lr) [(I sy.Player_X_Speed, .eq), (I sy.Player_XSpeedAbsolute, .eq)] c3.ids = true)
    (h2 : pieceOK (Rom.of m0) (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction) (hlr : (TopSpeed.upTo 3).contains lr = true)
    (hA : At (Rom.of m0) c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048)
    (e1 : R.ram.get! (I sy.MaximumRightSpeed) = mr) (e2 : R.ram.get! (I sy.MaximumLeftSpeed) = ml) (e3 : R.ram.get! (I sy.FrictionAdderLow) = lo) (e4 : R.ram.get! (I sy.FrictionAdderHigh) = hi)
    (m1 : mr ∈ maxRs sy m0) (m2 : ml ∈ maxLs sy m0) (m3 : (lo, hi) ∈ adders sy m0) (hcm : R.ram.get! (I sy.Player_CollisionBits) &&& lr = lr) :
    ∃ k, At (Rom.of m0) c4 (stepN k R) ∧ (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k R).ram.get! (I sy.Player_X_Speed)) ∧
      InFrameN (Rom.of m0) R k := by
  generalize hv0 : R.ram.get! (I sy.Player_X_Speed) = v at hsp
  generalize hf0 : R.ram.get! (I sy.Player_X_MoveForce) = f
  have hH := pokeL_good (fricL sy v f lo hi mr ml 0xFF) hb
  have hHs : (pokeL m0 (fricL sy v f lo hi mr ml 0xFF)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ fricL sy v f lo hi mr ml 0xFF, (pokeL m0 (fricL sy v f lo hi mr ml 0xFF)).ram.get! (I q.1) = q.2 := pokeL_get _ _ hb hnd
  have hrel : ∀ p ∈ tagsFrM sy lr, p.2.R (R.ram.get! p.1) ((pokeL m0 (fricL sy v f lo hi mr ml 0xFF)).ram.get! p.1) := by
    intro p hp
    simp only [tagsFrM, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show _ = _
      rw [hget (sy.Player_X_Speed, v) (by simp [fricL])]
      exact hv0
    · show _ = _
      rw [hget (sy.Player_X_MoveForce, f) (by simp [fricL])]
      exact hf0
    · show _ = _
      rw [hget (sy.FrictionAdderLow, lo) (by simp [fricL])]
      exact e3
    · show _ = _
      rw [hget (sy.FrictionAdderHigh, hi) (by simp [fricL])]
      exact e4
    · show _ = _
      rw [hget (sy.MaximumRightSpeed, mr) (by simp [fricL])]
      exact e1
    · show _ = _
      rw [hget (sy.MaximumLeftSpeed, ml) (by simp [fricL])]
      exact e2
    · refine ⟨?_, ?_⟩
      · show R.ram.get! (I sy.Player_CollisionBits) &&& lr = lr &&& lr
        rw [hcm, and_self8]
      · show (pokeL m0 (fricL sy v f lo hi mr ml 0xFF)).ram.get! (I sy.Player_CollisionBits) &&& 0xFF = 0xFF &&& 0xFF
        rw [hget (sy.Player_CollisionBits, 0xFF) (by simp [fricL])]
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, _, g1, p1, s1, o1, w1, _, _, _, C1⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) hH hHs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_map.2 ⟨p, hp, rfl⟩) (hK3 p hp))
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have oV : (stepN k1 R).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml 0xFF)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) :=
    o1 (I sy.Player_X_Speed, .eq) (by simp)
  have oA : (stepN k1 R).ram.get! (I sy.Player_XSpeedAbsolute) =
      (runSub (pokeL m0 (fricL sy v f lo hi mr ml 0xFF)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_XSpeedAbsolute) :=
    o1 (I sy.Player_XSpeedAbsolute, .eq) (by simp)
  -- what `frictionCheck` says, on the bits `0xFF`
  have hC := hfr
  simp only [TopSpeed.frictionCheck, List.all_eq_true] at hC
  have hq := hC v (List.contains_iff_mem.1 hsp) f (Potential.mem_bytes f) (lo, hi) m3 mr m1 ml m2 lr (List.contains_iff_mem.1 hlr) 0xFF (by simp [TopSpeed.collBits])
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
  have hk : pokeL m0 (fricL sy v f lo hi mr ml 0xFF) = poke (poke (poke (poke (poke (poke (poke m0 sy.Player_X_Speed v) sy.Player_X_MoveForce f) sy.FrictionAdderLow lo) sy.FrictionAdderHigh hi) sy.MaximumRightSpeed mr) sy.MaximumLeftSpeed ml) sy.Player_CollisionBits 0xFF := by
    simp only [fricL, pokeL]
  rw [← hk] at hq
  refine ⟨k1 + k2, by rw [e]; exact A2, ?_, InFrameN.add C1 C2⟩
  rw [e, W2 _ (by simp [watchM]) (I_lt _), W2 _ (by simp [watchM]) (I_lt _), oV, oA]
  exact hq.1.2

/-- `stored_c4` from the state `AtCtrl` with the speed in `TopSpeed`'s range, in place of `AtFrame`: at the mover the stored speed is `|v|` -/
theorem stored_c4M {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (hso : ∀ c ∈ allCases, storedFricM sy m0 S c = true) (h : AtCtrl sy (Rom.of m0) S R)
    (hsp : TopSpeed.inSpeed sy (R.ram.get! (I sy.Player_X_Speed)) = true) :
    ∃ k, At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k R).ram.get! (I sy.Player_X_Speed)) ∧ InFrameN (Rom.of m0) R k := by
  have habs : R.ram.get! (I sy.Player_XSpeedAbsolute) = absB (R.ram.get! (I sy.Player_X_Speed)) := h.abs
  have hmem := caseOf_mem h.to0
  have hA := at_start h.to0
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  have hs3 := hso _ hmem
  -- the side he presses is not masked, on the case's side
  have hco : R.ram.get! (I sy.Player_CollisionBits) &&& lrOf (caseOf sy R).n = lrOf (caseOf sy R).n := by
    have e := h.coll
    obtain ⟨n1, n2, _, _⟩ := norm_fields (caseOf sy R) (if peek R sy.RunningTimer == 0 then 0 else 1)
    rw [readIn_eq, lr_of n1 n2] at e
    exact e
  generalize hcc : caseOf sy R = c at hmem hA hc hc2 hs3 hco ⊢
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  simp only [storedFricM, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hs3
  generalize planOf sy m0 S c = P at hc hc2 hs3 ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨hlr, x1⟩, x2⟩, _⟩ := hc2
  have hzero : TopSpeed.inSpeed sy (0 : UInt8) = true := by
    simp only [TopSpeed.inSpeed, decide_eq_true_eq]
    show ((0 : Int)).natAbs ≤ _
    simp
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec a1 hA
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  obtain ⟨k2, Q2, _, A2, W2, _, cg, L2, C2⟩ := piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
  generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
  obtain ⟨mr, ml, lo, hi, c1, c2, c3, c4, m1, m2, m3⟩ := capsGood_spec cg L2
  have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
  have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl => by
    rw [wX j (List.mem_cons_of_mem _ hj) hl, wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl]
  have spL := fun {v : UInt8} (e : TopSpeed.inSpeed sy v = true) => speed_list hF.scomp e
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨_, b2⟩, _⟩, b4⟩, _⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec b2 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have x2' : walkT (Rom.of m0) (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2) = true := by
      rcases x2 with x2 | x2
      · exact absurd h0 x2
      · exact x2
    obtain ⟨k4, Q4, _, A4, W4, _, ag, L4, C4⟩ := piece_specX (c' := afterLeaf P.c2 P.r2) (extra := animGood sy) x2' A3
    generalize hR4 : stepN k4 R3 = R4 at A4 W4 L4
    have an := animGood_spec ag L4
    obtain ⟨k5, _, A5, W5, B5, C5⟩ := piece_spec b4 A4
    generalize hR5 : stepN k5 R4 = R5 at A5 W5
    have wf : ∀ j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy,
        j < 2048 → R5.ram.get! j = R4.ram.get! j := fun j hj hl => W5 j (List.mem_append_left _ hj) hl
    have hCaps : ∀ j ∈ capsL sy, R5.ram.get! j = R2.ram.get! j := fun j hj => by
      have hl : j < 2048 := by
        simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
      rw [wf j (List.mem_append_right _ hj) hl, W4 j (List.mem_append_right _ hj) hl, W3 j (by
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl]
    have hcoll5 : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
      rw [wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hsp5 : TopSpeed.inSpeed sy (R5.ram.get! (I sy.Player_X_Speed)) = true := by
      rw [wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · rw [an.1, W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact hsp
      · rw [an.1]
        exact hzero
    obtain ⟨k6, A6, G6, C6⟩ := fric_absM hb hfr hF.fnd (spL hsp5) (hs3.resolve_left (fun e => e.1 h0)) d4 d1 d2 hlr A5 B5
      (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
      m1 m2 m3 (by rw [hcoll5]; exact hco)
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = stepN k6 R5 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), by rw [hfin]; exact A6, by rw [hfin]; exact G6, ?_⟩
    exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 (InFrameN.add' C4 hR4 (InFrameN.add' C5 hR5 C6))))
  · simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
      obtain ⟨k3, _, A3, W3, B3, C3⟩ := piece_spec g A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
        have hl : j < 2048 := by
          simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
        exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e3 : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hne : lrOf c.n ≠ 0 := by simpa using hl
      obtain ⟨k6, A6, G6, C6⟩ := fric_absM hb hfr hF.fnd (spL (by rw [e1]; exact hsp)) (hs3.resolve_left (fun e => hne e.2)) d4 d1 d2 hlr A3 B3
        (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
        m1 m2 m3 (by rw [e3]; exact hco)
      have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + (k3 + k6)), by rw [hfin]; exact A6, by rw [hfin]; exact G6, ?_⟩
      exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 C6))
    · -- in the air, with neither: the speed and the stored speed stay
      rw [if_neg hl] at a9
      obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec a9 A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, hR3]
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      refine ⟨k1 + (k2 + k3), by rw [hfin]; exact A3, by rw [hfin, e1, e2]; exact habs, ?_⟩
      exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)

/-- **The stored speed at the scroll handler, from the state `AtCtrl`.** From the player's routine in the state `AtCtrl` (the stored speed `|v|`, the side he presses
not masked), with the speed in `TopSpeed`'s range, the frame comes to the scroll handler with the stored speed `|v|` again. `hso` is the check on the ROM of
`stored_path` (`storedOK`: here only its walks after the mover), `hsm` that of the friction with the bits known only on the side he presses (`storedM`) -/
theorem stored_pathM {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : storedOK sy m0 S = true)
    (hsm : storedM sy m0 S = true) (h : AtCtrl sy (Rom.of m0) S R) (hsp : TopSpeed.inSpeed sy (peek R sy.Player_X_Speed) = true) :
    ∃ k, (stepN k R).pc = sy.PlayerSubs ∧ peek (stepN k R) sy.Player_XSpeedAbsolute = absB (peek (stepN k R) sy.Player_X_Speed) ∧ InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  simp only [storedOK, Bool.and_eq_true, List.all_eq_true] at hso
  simp only [storedM, List.all_eq_true] at hsm
  obtain ⟨k1, A1, G1, C1⟩ := stored_c4M hb hfr hF hsm h hsp
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_mem h.to0)
  have e4 : t = (planOf sy m0 S (caseOf sy R)).c4 := cutSame_eq hte
  have htl := hso.2 t ht
  rw [e4] at htl
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec htl A1
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  refine ⟨k1 + k2, by rw [e]; exact A2.pc, ?_, InFrameN.add C1 C2⟩
  show (stepN (k1 + k2) R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN (k1 + k2) R).ram.get! (I sy.Player_X_Speed))
  rw [e, W2 _ (by simp) (I_lt _), W2 _ (by simp) (I_lt _)]
  exact G1

/-- `stored_c4` with no condition on the stored speed at the player's routine: at the mover the stored speed is `|v|`, or (in the air with neither Left nor Right)
the speed and the stored speed are those of the player's routine -/
theorem stored_c4F {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (hso : ∀ c ∈ allCases, storedFricOK sy m0 S c = true) (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k, At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      ((stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k R).ram.get! (I sy.Player_X_Speed)) ∨
        (stOf (caseOf sy R).n ≠ 0 ∧ lrOf (caseOf sy R).n = 0 ∧ (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) ∧
          (stepN k R).ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed))) ∧ InFrameN (Rom.of m0) R k := by
  have hmem := caseOf_memF h
  have hA := at_startF h
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  have hs3 := hso _ hmem
  generalize hcc : caseOf sy R = c at hmem hA hc hc2 hs3 ⊢
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  simp only [storedFricOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hs3
  generalize planOf sy m0 S c = P at hc hc2 hs3 ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨hlr, x1⟩, x2⟩, _⟩ := hc2
  have hzero : TopSpeed.inSpeed sy (0 : UInt8) = true := by
    simp only [TopSpeed.inSpeed, decide_eq_true_eq]
    show ((0 : Int)).natAbs ≤ _
    simp
  have hsp : TopSpeed.inSpeed sy (R.ram.get! (I sy.Player_X_Speed)) = true := h.speed
  have hco : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy := h.coll
  obtain ⟨k1, _, A1, W1, _, C1⟩ := piece_spec a1 hA
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  obtain ⟨k2, Q2, _, A2, W2, _, cg, L2, C2⟩ := piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
  generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
  obtain ⟨mr, ml, lo, hi, c1, c2, c3, c4, m1, m2, m3⟩ := capsGood_spec cg L2
  have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
  have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl => by
    rw [wX j (List.mem_cons_of_mem _ hj) hl, wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl]
  have spL := fun {v : UInt8} (e : TopSpeed.inSpeed sy v = true) => speed_list hF.scomp e
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨_, b2⟩, _⟩, b4⟩, _⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec b2 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have x2' : walkT (Rom.of m0) (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2) = true := by
      rcases x2 with x2 | x2
      · exact absurd h0 x2
      · exact x2
    obtain ⟨k4, Q4, _, A4, W4, _, ag, L4, C4⟩ := piece_specX (c' := afterLeaf P.c2 P.r2) (extra := animGood sy) x2' A3
    generalize hR4 : stepN k4 R3 = R4 at A4 W4 L4
    have an := animGood_spec ag L4
    obtain ⟨k5, _, A5, W5, B5, C5⟩ := piece_spec b4 A4
    generalize hR5 : stepN k5 R4 = R5 at A5 W5
    have wf : ∀ j ∈ [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy,
        j < 2048 → R5.ram.get! j = R4.ram.get! j := fun j hj hl => W5 j (List.mem_append_left _ hj) hl
    have hCaps : ∀ j ∈ capsL sy, R5.ram.get! j = R2.ram.get! j := fun j hj => by
      have hl : j < 2048 := by
        simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
      rw [wf j (List.mem_append_right _ hj) hl, W4 j (List.mem_append_right _ hj) hl, W3 j (by
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl]
    have hcoll5 : R5.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
      rw [wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
    have hsp5 : TopSpeed.inSpeed sy (R5.ram.get! (I sy.Player_X_Speed)) = true := by
      rw [wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · rw [an.1, W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact hsp
      · rw [an.1]
        exact hzero
    obtain ⟨k6, A6, G6, C6⟩ := fric_abs hb hfr hF.fnd (spL hsp5) (hs3.resolve_left (fun e => e.1 h0)) d4 d1 d2 hlr A5 B5
      (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
      m1 m2 m3 (by rw [hcoll5]; exact hco)
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = stepN k6 R5 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), by rw [hfin]; exact A6, by rw [hfin]; exact Or.inl G6, ?_⟩
    exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 (InFrameN.add' C4 hR4 (InFrameN.add' C5 hR5 C6))))
  · simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
      obtain ⟨k3, _, A3, W3, B3, C3⟩ := piece_spec g A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
        have hl : j < 2048 := by
          simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
        exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e3 : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hne : lrOf c.n ≠ 0 := by simpa using hl
      obtain ⟨k6, A6, G6, C6⟩ := fric_abs hb hfr hF.fnd (spL (by rw [e1]; exact hsp)) (hs3.resolve_left (fun e => hne e.2)) d4 d1 d2 hlr A3 B3
        (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
        m1 m2 m3 (by rw [e3]; exact hco)
      have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + (k3 + k6)), by rw [hfin]; exact A6, by rw [hfin]; exact Or.inl G6, ?_⟩
      exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 C6))
    · -- in the air, with neither: the speed and the stored speed stay
      rw [if_neg hl] at a9
      obtain ⟨k3, _, A3, W3, _, C3⟩ := piece_spec a9 A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, hR3]
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      refine ⟨k1 + (k2 + k3), by rw [hfin]; exact A3, by rw [hfin]; exact Or.inr ⟨h0, by simpa using hl, e2, e1⟩, ?_⟩
      exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)

/-- **The stored speed at the scroll handler, with any stored speed at the player's routine.** From the player's routine (`AtFrame`), the frame comes to the scroll
handler with the stored speed `|v|`, or with the speed and the stored speed of the player's routine (in the air with neither Left nor Right, where `ImposeFriction` does not
run). `stored_path` with no condition on the stored speed; the checks are its own -/
theorem stored_pathF {m0 : Machine} {S : UInt8} {R : Machine} (hOK : modelOK sy m0 S = true) (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : storedOK sy m0 S = true)
    (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k, (stepN k R).pc = sy.PlayerSubs ∧ (peek (stepN k R) sy.Player_XSpeedAbsolute = absB (peek (stepN k R) sy.Player_X_Speed) ∨
      (stOf (caseOf sy R).n ≠ 0 ∧ lrOf (caseOf sy R).n = 0 ∧ peek (stepN k R) sy.Player_XSpeedAbsolute = peek R sy.Player_XSpeedAbsolute ∧
        peek (stepN k R) sy.Player_X_Speed = peek R sy.Player_X_Speed)) ∧
      InFrameN (Rom.of m0) R k := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  simp only [storedOK, Bool.and_eq_true, List.all_eq_true] at hso
  obtain ⟨k1, A1, G1, C1⟩ := stored_c4F hb hfr hF hso.1 h
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h)
  have e4 : t = (planOf sy m0 S (caseOf sy R)).c4 := cutSame_eq hte
  have htl := hso.2 t ht
  rw [e4] at htl
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec htl A1
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  refine ⟨k1 + k2, by rw [e]; exact A2.pc, ?_, InFrameN.add C1 C2⟩
  show (stepN (k1 + k2) R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN (k1 + k2) R).ram.get! (I sy.Player_X_Speed)) ∨
    (stOf (caseOf sy R).n ≠ 0 ∧ lrOf (caseOf sy R).n = 0 ∧ (stepN (k1 + k2) R).ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) ∧
      (stepN (k1 + k2) R).ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed))
  rw [e, W2 _ (by simp) (I_lt _), W2 _ (by simp) (I_lt _)]
  exact G1

end storedM

/-! ## Both sides of the friction in one run (round 33)

`TopSpeed.frictionCheck` (the speed after `ImposeFriction` from above, and the stored speed) and `frictionLowCheck` (from below, round 30) run `ImposeFriction` on the
same machines. `frictionBoth` runs it once on each and asks both; `friction_of_both` gives the two checks from it, so the private proofs run the routine once. -/

section fricBoth

/-- **`ImposeFriction` lowers the speed with its fraction by at most the adder below `min(V, 0)`**, on the machines of `TopSpeed.frictionCheck` (round 30; in this file
since round 33) -/
def frictionLowCheck (sy : Syms) (m0 : Machine) : Bool :=
  (TopSpeed.speedsB sy).all fun v => TopSpeed.bytes.all fun fr => (adders sy m0).all fun (lo, hi) =>
  (maxRs sy m0).all fun mr => (maxLs sy m0).all fun ml => (TopSpeed.upTo 3).all fun a => (TopSpeed.collBits sy).all fun cb =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_X_MoveForce fr
    let m := poke m sy.FrictionAdderLow lo
    let m := poke m sy.FrictionAdderHigh hi
    let m := poke m sy.MaximumRightSpeed mr
    let m := poke m sy.MaximumLeftSpeed ml
    let m := poke m sy.Player_CollisionBits cb
    let m := runSub m sy.ImposeFriction a 0 0
    let V := 256 * sbyte v + fr.toNat
    let V' := 256 * sbyte (peek m sy.Player_X_Speed) + (peek m sy.Player_X_MoveForce).toNat
    decide (min V 0 - (256 * hi.toNat + lo.toNat : Int) ≤ V')

/-- `TopSpeed.frictionCheck` and `frictionLowCheck` in one run of `ImposeFriction` on each of their machines -/
def frictionBoth (sy : Syms) (m0 : Machine) : Bool :=
  (TopSpeed.speedsB sy).all fun v => TopSpeed.bytes.all fun fr => (adders sy m0).all fun (lo, hi) =>
  (maxRs sy m0).all fun mr => (maxLs sy m0).all fun ml => (TopSpeed.upTo 3).all fun a => (TopSpeed.collBits sy).all fun cb =>
    let m := poke m0 sy.Player_X_Speed v
    let m := poke m sy.Player_X_MoveForce fr
    let m := poke m sy.FrictionAdderLow lo
    let m := poke m sy.FrictionAdderHigh hi
    let m := poke m sy.MaximumRightSpeed mr
    let m := poke m sy.MaximumLeftSpeed ml
    let m := poke m sy.Player_CollisionBits cb
    let m := runSub m sy.ImposeFriction a 0 0
    let v' := peek m sy.Player_X_Speed
    let V := 256 * sbyte v + fr.toNat
    let V' := 256 * sbyte v' + (peek m sy.Player_X_MoveForce).toNat
    (TopSpeed.inSpeed sy v' && peek m sy.Player_XSpeedAbsolute == absB v' && decide (V' ≤ max V 0 + (256 * hi.toNat + lo.toNat : Int))) &&
      decide (min V 0 - (256 * hi.toNat + lo.toNat : Int) ≤ V')

/-- **The two checks of the friction from one run** -/
theorem friction_of_both {sy : Syms} {m0 : Machine} (h : frictionBoth sy m0 = true) :
    TopSpeed.frictionCheck sy m0 = true ∧ frictionLowCheck sy m0 = true := by
  unfold frictionBoth at h
  unfold TopSpeed.frictionCheck frictionLowCheck
  simp only [List.all_eq_true] at h ⊢
  constructor
  · intro v hv fr hfr p hp mr hmr ml hml a ha cb hcb
    have e := h v hv fr hfr p hp mr hmr ml hml a ha cb hcb
    obtain ⟨lo, hi⟩ := p
    simp only [Bool.and_eq_true] at e ⊢
    exact e.1
  · intro v hv fr hfr p hp mr hmr ml hml a ha cb hcb
    have e := h v hv fr hfr p hp mr hmr ml hml a ha cb hcb
    obtain ⟨lo, hi⟩ := p
    simp only [Bool.and_eq_true] at e ⊢
    exact e.2

end fricBoth

end Smbrta.FrameModel
