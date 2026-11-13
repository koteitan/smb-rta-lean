import Theorems.FrameModel

/-!
# A frame that follows the model, with the frame's time

`FrameModel.clean_frame` and `FrameModel.frame_read` ask of the frame that it does not end in the `moveLen` instructions after the player's routine (`Clean.longer`,
`ReadFrame.longer`), and that the position is away from both ends of its range (`far`). Here the same theorems take instead:
* the frame comes to the player's routine before its end, and each instruction of it that is not at the idle loop runs at least 64 dots before the frame's end
  (`InTime`). The walks from the player's routine to the scroll handler show that each of their steps keeps the frame then (`InFrameN`), so the frame does not end
  during the movement (`FrameModel.trace_inFrame`, as part e does);
* `far` as a hypothesis of the theorem, not of the frame's structure.

`CleanR` and `ReadR` are `Clean` and `ReadFrame` without `before`, `longer` and `far`; `before` (nothing writes the horizontal bytes before the player's routine) is a
hypothesis of the theorems too. `frame_pathI` and `fric_readI` are `frame_path` and `fric_read` of `FrameModel` with the
steps' `InFrameN` in their conclusions (the walks give it; `FrameModel` drops it); the proofs are those of `FrameModel` with that added. There is no game data in this file.
Page: `1-1/c-7-1-1-FrameTime.md`.
-/

namespace Smbrta.FrameModel
open Potential (HS HIn hstep hstepN norm)
open TopSpeed (absB)
open TaintRun (AB bt)
open PipeTransition (frame)
open PipeEntryRule (trace trace_stop nxt)

/-- **The frame's time**: the frame of `M` with the input `i` comes to the instruction `n₀` before its end, and each of its instructions that is not at the idle loop
`idle` runs at least 64 dots before the frame's end -/
structure InTime (E : Rom) (idle : UInt16) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  loop : idleAt E idle = true
  start : (trace M i n₀).frame = M.frame
  time : ∀ n, (trace M i n).pc ≠ idle → (trace M i n).fdot ≤ dotsPerFrame - 64

/-- **A frame that follows the model**, `Clean` without `before`, `longer` and `far` -/
structure CleanR (sy : Syms) (E : Rom) (S : UInt8) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  /-- it comes to the player's routine in the state `AtCtrl` -/
  at_ctrl : AtCtrl sy E S (trace M i n₀)
  /-- from the scroll handler on, nothing writes them: the collision routine does not stop him -/
  after : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → ∀ a ∈ hBytes sy, peek (frame M i) a = peek (trace M i j) a

/-- **A frame that is a `TopSpeed.Frame`**, `ReadFrame` without `before`, `longer` and `far` -/
structure ReadR (sy : Syms) (E : Rom) (S : UInt8) (M : Machine) (i : UInt8) (n₀ : Nat) : Prop where
  at_frame : AtFrame sy E S (trace M i n₀)
  collide : ∀ j, n₀ ≤ j → (trace M i j).pc = sy.PlayerSubs → Collide sy (trace M i j) (frame M i)

section framesI
variable {sy : Syms} {E : Rom}

/-- **A real frame follows the model**, with the frame's time (`InTime`) in place of `longer` -/
theorem clean_frameR {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} {idle : UInt16} (hOK : modelOK sy m0 S = true) (h : CleanR sy (Rom.of m0) S M i n₀)
    (hbef : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a) (hT : InTime (Rom.of m0) idle M i n₀) (hfar : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000) :
    readHS sy (frame M i) = hstep sy m0 (readHS sy M) (readIn sy (trace M i n₀)) ∧
      posP sy (frame M i) = posP sy M + 16 * sbyte (readHS sy (frame M i)).v := by
  obtain ⟨k, _, _, hpc, h1, h2, hC⟩ := move_model hOK h.at_ctrl
  have e0 := (trace_inFrame hT.loop hT.start hC hT.time k (Nat.le_refl k)).1
  have e1 := h.after (n₀ + k) (by omega) (by rw [e0]; exact hpc)
  rw [e0] at e1
  have e2 : readHS sy (trace M i n₀) = readHS sy M := readHS_congr hbef
  have e3 : posP sy (trace M i n₀) = posP sy M := posP_congr hbef
  have e4 := readHS_congr (sy := sy) e1
  have e5 := posP_congr (sy := sy) e1
  rw [e2] at h1
  rw [e3] at h2
  rw [← e4] at h1 h2
  rw [← e5] at h2
  refine ⟨h1, ?_⟩
  obtain ⟨a1, a2⟩ := posOf_range (peek (frame M i) sy.Player_PageLoc) (peek (frame M i) sy.Player_X_Position) (peek (frame M i) sy.SprObject_X_MoveForce)
  have a3 := sbyte_range (readHS sy (frame M i)).v
  have a4 := hfar
  rw [← posP_eq] at a1 a2
  omega

/-- `FrameModel.fric_read`, with the steps' `InFrameN` -/
theorem fric_readI {m0 : Machine} {c3 c4 : Cut} {r3 : UInt16} {lr : UInt8} {R : Machine} {mr ml lo hi : UInt8}
    (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hnd : nodupB (fricIdx sy) = true) (hsp : (TopSpeed.speedsB sy).contains (R.ram.get! (I sy.Player_X_Speed)) = true)
    (h1 : leafAll (Rom.of m0) m0.s sy.ImposeFriction r3 (Tag.kn lr lr) (tagsFr sy) [(I sy.Player_X_Speed, .eq), (I sy.Player_X_MoveForce, .eq)]
      ([I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ c3.ids) = true)
    (h2 : pieceOK (Rom.of m0) (afterLeaf c3 r3) c4 (watchM sy) fuelS = true) (hra : c3.ra = some lr) (hpc : c3.pc = sy.ImposeFriction) (hlr : (TopSpeed.upTo 3).contains lr = true)
    (hA : At (Rom.of m0) c3 R) (hK3 : ∀ p ∈ c3.K, p.1 < 2048)
    (e1 : R.ram.get! (I sy.MaximumRightSpeed) = mr) (e2 : R.ram.get! (I sy.MaximumLeftSpeed) = ml) (e3 : R.ram.get! (I sy.FrictionAdderLow) = lo) (e4 : R.ram.get! (I sy.FrictionAdderHigh) = hi)
    (m1 : mr ∈ maxRs sy m0) (m2 : ml ∈ maxLs sy m0) (m3 : (lo, hi) ∈ adders sy m0) (hcb : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy) :
    ∃ k, k ≤ 2 * fuelS ∧ At (Rom.of m0) c4 (stepN k R) ∧ gainOK sy m0 (stepN k R) (R.ram.get! (I sy.Player_X_Speed)) (R.ram.get! (I sy.Player_X_MoveForce)) ∧ Same3 sy (stepN k R) R ∧ InFrameN (Rom.of m0) R k := by
  generalize hv0 : R.ram.get! (I sy.Player_X_Speed) = v at hsp
  generalize hf0 : R.ram.get! (I sy.Player_X_MoveForce) = f
  generalize hc0 : R.ram.get! (I sy.Player_CollisionBits) = cb at hcb
  have hH := pokeL_good (fricL sy v f lo hi mr ml cb) hb
  have hHs : (pokeL m0 (fricL sy v f lo hi mr ml cb)).s = m0.s := pokeL_s _ _
  have hget : ∀ q ∈ fricL sy v f lo hi mr ml cb, (pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! (I q.1) = q.2 := pokeL_get _ _ hb hnd
  have hrel : ∀ p ∈ tagsFr sy, p.2.R (R.ram.get! p.1) ((pokeL m0 (fricL sy v f lo hi mr ml cb)).ram.get! p.1) := by
    intro p hp
    simp only [tagsFr, fricIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
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
    · show _ = _
      rw [hget (sy.Player_CollisionBits, cb) (by simp [fricL])]
      exact hc0
  have hae : R.a = lr := hA.ra lr hra
  obtain ⟨k1, f1, g1, p1, s1, o1, w1, _, _, _, I1⟩ := leaf_app h1 hA.good (by rw [hA.pc, hpc]) (by rw [hae]; exact Tag.R_kn _ _) hH hHs hrel
  have hAf := at_after (r := r3) hA g1 p1 s1 (fun p hp => w1 _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)) (hK3 p hp))
  obtain ⟨k2, f2, A2, W2, _, I2⟩ := piece_spec h2 hAf
  have e : stepN (k1 + k2) R = stepN k2 (stepN k1 R) := stepN_add _ _ _
  have oV : (stepN k1 R).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := o1 (I sy.Player_X_Speed, .eq) (by simp)
  have oF : (stepN k1 R).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := o1 (I sy.Player_X_MoveForce, .eq) (by simp)
  -- what `frictionCheck` says
  have hC := hfr
  simp only [TopSpeed.frictionCheck, List.all_eq_true] at hC
  have hq := hC v (List.contains_iff_mem.1 hsp) f (Potential.mem_bytes f) (lo, hi) m3 mr m1 ml m2 lr (List.contains_iff_mem.1 hlr) cb hcb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have hk : pokeL m0 (fricL sy v f lo hi mr ml cb) = poke (poke (poke (poke (poke (poke (poke m0 sy.Player_X_Speed v) sy.Player_X_MoveForce f) sy.FrictionAdderLow lo) sy.FrictionAdderHigh hi) sy.MaximumRightSpeed mr) sy.MaximumLeftSpeed ml) sy.Player_CollisionBits cb := by
    simp only [fricL, pokeL]
  rw [← hk] at hq
  have hal := adder_le m3
  have w1' : ∀ i, i ∈ [I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] → (stepN k1 R).ram.get! i = R.ram.get! i := by
    intro i hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
    · exact w1 _ (by simp) (I_lt _)
  refine ⟨k1 + k2, by omega, by rw [e]; exact A2, ?_, ?_, InFrameN.add' I1 rfl I2⟩
  · rw [e]
    have e5 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := by
      rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oV
    have e6 : (stepN k2 (stepN k1 R)).ram.get! (I sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := by
      rw [W2 _ (by simp [watchM]) (I_lt _)]
      exact oF
    refine ⟨?_, ?_⟩
    · rw [e5]
      exact hq.1.1
    · rw [e5, e6]
      have h7 := hq.2
      have h8 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_Speed) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_Speed) := rfl
      have h9 : (peek (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0) sy.Player_X_MoveForce) = (runSub (pokeL m0 (fricL sy v f lo hi mr ml cb)) sy.ImposeFriction lr 0 0).ram.get! (I sy.Player_X_MoveForce) := rfl
      rw [h8, h9] at h7
      omega
  · rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]
    · rw [W2 _ (by simp [watchM]) (I_lt _), w1' _ (by simp)]

/-- `FrameModel.frame_path`, with the steps' `InFrameN` -/
theorem frame_pathI {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k v₁ f₁, k ≤ fuelW + 6 * fuelS ∧ At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧
      ((v₁ = R.ram.get! (I sy.Player_X_Speed) ∧ f₁ = R.ram.get! (I sy.Player_X_MoveForce)) ∨ (v₁ = 0 ∧ f₁ = 0)) ∧
      gainOK sy m0 (stepN k R) v₁ f₁ ∧ Same3 sy (stepN k R) R ∧ InFrameN (Rom.of m0) R k := by
  have hmem := caseOf_memF h
  have hA := at_startF h
  obtain ⟨hc, hc2⟩ := hF.cases _ hmem
  generalize hcc : caseOf sy R = c at hmem hA hc hc2 ⊢
  simp only [caseOK, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [frameCaseOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hc2
  generalize planOf sy m0 S c = P at hc hc2 ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, a9⟩, _⟩, _⟩ := hc
  obtain ⟨⟨⟨hlr, x1⟩, x2⟩, x3⟩ := hc2
  have hzero : TopSpeed.inSpeed sy (0 : UInt8) = true := by
    simp only [TopSpeed.inSpeed, decide_eq_true_eq]
    show ((0 : Int)).natAbs ≤ _
    simp
  have hsp : TopSpeed.inSpeed sy (R.ram.get! (I sy.Player_X_Speed)) = true := h.speed
  have hco : R.ram.get! (I sy.Player_CollisionBits) ∈ TopSpeed.collBits sy := h.coll
  obtain ⟨k1, f1, A1, W1, B1, I1⟩ := piece_spec a1 hA
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have wG : ∀ j ∈ I sy.RunningTimer :: I sy.SavedJoypadBits :: watchH sy, j < 2048 → R1.ram.get! j = R.ram.get! j := W1
  obtain ⟨k2, Q2, f2, A2, W2, _, cg, L2, I2⟩ := piece_specX (c' := afterLeaf P.c1 P.r1) (watch := I sy.SavedJoypadBits :: watchH sy) (extra := capsGood sy m0) x1 A1
  generalize hR2 : stepN k2 R1 = R2 at A2 W2 L2
  obtain ⟨mr, ml, lo, hi, c1, c2, c3, c4, m1, m2, m3⟩ := capsGood_spec cg L2
  have wX : ∀ j ∈ I sy.SavedJoypadBits :: watchH sy, j < 2048 → R2.ram.get! j = R1.ram.get! j := W2
  have hk : ∀ j ∈ watchH sy, j < 2048 → R2.ram.get! j = R.ram.get! j := fun j hj hl => by
    rw [wX j (List.mem_cons_of_mem _ hj) hl, wG j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hl]
  have hS2 : Same3 sy R2 R := ⟨hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)⟩
  have spL := fun {v : UInt8} (e : TopSpeed.inSpeed sy v = true) => speed_list hF.scomp e
  by_cases h0 : stOf c.n = 0
  · -- on the ground
    simp only [if_pos h0, Bool.and_eq_true] at a9
    obtain ⟨g, fc⟩ := a9
    simp only [groundOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at g
    obtain ⟨⟨⟨⟨b1, b2⟩, _⟩, b4⟩, b5⟩ := g
    simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
    obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
    obtain ⟨k3, f3, A3, W3, B3, I3⟩ := piece_spec b2 A2
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have x2' : walkT (Rom.of m0) (fun Q => Q.pc == P.r2) (fun Q => goalC (afterLeaf P.c2 P.r2) ([I sy.PlayerFacingDir, I sy.Player_CollisionBits, I sy.Player_X_Position, I sy.Player_PageLoc, I sy.SprObject_X_MoveForce] ++ capsL sy) Q && animGood sy Q) fuelS (startQ P.c2) = true := by
      rcases x2 with x2 | x2
      · exact absurd h0 x2
      · exact x2
    obtain ⟨k4, Q4, f4, A4, W4, _, ag, L4, I4⟩ := piece_specX (c' := afterLeaf P.c2 P.r2) (extra := animGood sy) x2' A3
    generalize hR4 : stepN k4 R3 = R4 at A4 W4 L4
    have an := animGood_spec ag L4
    obtain ⟨k5, f5, A5, W5, B5, I5⟩ := piece_spec b4 A4
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
    obtain ⟨k6, f6, A6, G6, S6, I6⟩ := fric_readI hb hfr hF.fnd (spL hsp5) (x3.resolve_left (fun e => e.1 h0)) d4 d1 d2 hlr A5 B5
      (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
      m1 m2 m3 (by rw [hcoll5]; exact hco)
    have hfin : stepN (k1 + (k2 + (k3 + (k4 + (k5 + k6))))) R = stepN k6 R5 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3, stepN_add, hR4, stepN_add, hR5]
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), R5.ram.get! (I sy.Player_X_Speed), R5.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, ?_, by rw [hfin]; exact G6, ?_,
      InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 (InFrameN.add' I3 hR3 (InFrameN.add' I4 hR4 (InFrameN.add' I5 hR5 I6))))⟩
    · rw [wf _ (by simp) (I_lt _), wf _ (by simp) (I_lt _)]
      rcases an with an | an
      · left
        rw [an.1, an.2, W3 _ (by simp [watchA, watchH]) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
        exact ⟨rfl, rfl⟩
      · exact Or.inr an
    · rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, wf _ (by simp) (I_lt _), W4 _ (by simp) (I_lt _), W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
  · simp only [if_neg h0] at a9
    by_cases hl : (lrOf c.n != 0) = true
    · -- in the air, with Left or Right
      rw [if_pos hl] at a9
      simp only [Bool.and_eq_true] at a9
      obtain ⟨g, fc⟩ := a9
      simp only [fricOK, Bool.and_eq_true, beq_iff_eq] at fc
      obtain ⟨⟨⟨d1, d2⟩, _⟩, d4⟩ := fc
      obtain ⟨k3, f3, A3, W3, B3, I3⟩ := piece_spec g A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hCaps : ∀ j ∈ capsL sy, R3.ram.get! j = R2.ram.get! j := fun j hj => by
        have hl : j < 2048 := by
          simp only [capsL, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl <;> exact I_lt _
        exact W3 j (List.mem_cons_of_mem _ (List.mem_append_right _ hj)) hl
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e3 : R3.ram.get! (I sy.Player_CollisionBits) = R.ram.get! (I sy.Player_CollisionBits) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hne : lrOf c.n ≠ 0 := by simpa using hl
      obtain ⟨k6, f6, A6, G6, S6, I6⟩ := fric_readI hb hfr hF.fnd (spL (by rw [e1]; exact hsp)) (x3.resolve_left (fun e => hne e.2)) d4 d1 d2 hlr A3 B3
        (by rw [hCaps _ (by simp [capsL])]; exact c1) (by rw [hCaps _ (by simp [capsL])]; exact c2) (by rw [hCaps _ (by simp [capsL])]; exact c3) (by rw [hCaps _ (by simp [capsL])]; exact c4)
        m1 m2 m3 (by rw [e3]; exact hco)
      have hfin : stepN (k1 + (k2 + (k3 + k6))) R = stepN k6 R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
      refine ⟨k1 + (k2 + (k3 + k6)), R3.ram.get! (I sy.Player_X_Speed), R3.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A6, Or.inl ⟨e1, e2⟩, by rw [hfin]; exact G6, ?_,
        InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 (InFrameN.add' I3 hR3 I6))⟩
      rw [hfin]
      obtain ⟨s1, s2, s3⟩ := S6
      obtain ⟨t1, t2, t3⟩ := hS2
      refine ⟨?_, ?_, ?_⟩
      · rw [s1, W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
      · rw [s2, W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
      · rw [s3, W3 _ (by simp [watchA, watchH]) (I_lt _), t3]
    · -- in the air, with neither
      rw [if_neg hl] at a9
      obtain ⟨k3, f3, A3, W3, _, I3⟩ := piece_spec a9 A2
      generalize hR3 : stepN k3 R2 = R3 at A3 W3
      have hfin : stepN (k1 + (k2 + k3)) R = R3 := by
        rw [stepN_add, hR1, stepN_add, hR2, hR3]
      have e1 : R3.ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have e2 : R3.ram.get! (I sy.Player_X_MoveForce) = R.ram.get! (I sy.Player_X_MoveForce) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      refine ⟨k1 + (k2 + k3), R.ram.get! (I sy.Player_X_Speed), R.ram.get! (I sy.Player_X_MoveForce), by omega, by rw [hfin]; exact A3, Or.inl ⟨rfl, rfl⟩, ?_, ?_,
        InFrameN.add' I1 hR1 (InFrameN.add' I2 hR2 I3)⟩
      · rw [hfin]
        refine ⟨by rw [e1]; exact hsp, ?_⟩
        rw [e1, e2]
        have := FastAccel.amax_nonneg sy m0
        omega
      · rw [hfin]
        obtain ⟨t1, t2, t3⟩ := hS2
        refine ⟨?_, ?_, ?_⟩
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t1]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t2]
        · rw [W3 _ (by simp [watchA, watchH]) (I_lt _), t3]

/-- **A real frame is a `TopSpeed.Frame`**, with the frame's time (`InTime`) in place of `longer` -/
theorem frame_readR {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} {idle : UInt16} (hOK : modelOK sy m0 S = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (h : ReadR sy (Rom.of m0) S M i n₀) (hbef : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a) (hT : InTime (Rom.of m0) idle M i n₀)
    (hfar : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000) :
    ∃ f : TopSpeed.Frame (TopSpeed.top sy : Int) (amax sy m0), f.v = sbyte (peek M sy.Player_X_Speed) ∧ f.f = ((peek M sy.Player_X_MoveForce).toNat : Int) ∧ f.P = posP sy M ∧
      f.v' = sbyte (peek (frame M i) sy.Player_X_Speed) ∧ f.f' = ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int) ∧ f.P' = posP sy (frame M i) := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, S1, I1⟩ := frame_pathI hb hfr hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 S (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, I2⟩ := tail_spec htl hF.digits A1
  have hk : k1 + k2 ≤ moveLen := by
    show k1 + k2 ≤ 2 * fuelW + 11 * fuelS
    omega
  have e0 := (trace_inFrame hT.loop hT.start (InFrameN.add' I1 rfl I2) hT.time (k1 + k2) (Nat.le_refl _)).1
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have hco := h.collide (n₀ + (k1 + k2)) (by omega) (by rw [e0]; exact p2)
  rw [e0] at hco
  have ev : peek (trace M i n₀) sy.Player_X_Speed = peek M sy.Player_X_Speed := hbef _ (by simp [hBytes])
  have ef : peek (trace M i n₀) sy.Player_X_MoveForce = peek M sy.Player_X_MoveForce := hbef _ (by simp [hBytes])
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr hbef
  have hsp : TopSpeed.inSpeed sy (peek (trace M i n₀) sy.Player_X_Speed) = true := h.at_frame.speed
  obtain ⟨g1, g2'⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hf2 : B.ram.get! (I sy.Player_X_MoveForce) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce) := ff2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := hfar
    rw [ePk, eP] at q2
    omega
  have hfr1 := ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_MoveForce)).toNat_lt
  refine ⟨{ v := sbyte (peek M sy.Player_X_Speed), f := ((peek M sy.Player_X_MoveForce).toNat : Int), P := posP sy M,
            v₁ := sbyte v₁, f₁ := (f₁.toNat : Int),
            v₂ := sbyte (B.ram.get! (I sy.Player_X_Speed)), f₂ := ((B.ram.get! (I sy.Player_X_MoveForce)).toNat : Int), P₂ := posP sy B,
            v' := sbyte (peek (frame M i) sy.Player_X_Speed), f' := ((peek (frame M i) sy.Player_X_MoveForce).toNat : Int), P' := posP sy (frame M i),
            anim := ?_, friction := ?_, friction_gain := ?_, frac := ?_, move := hmove, impedeV := ?_, impedeF := ?_, impedeP := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rcases an with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [a1]
        exact congrArg sbyte ev
      · rw [a2]
        exact congrArg (fun x : UInt8 => (x.toNat : Int)) ef
    · right
      rw [a1, a2]
      exact ⟨rfl, rfl⟩
  · intro _
    rw [hv2]
    exact hr1
  · rw [hv2, hf2]
    exact g2'
  · rw [hf2]
    omega
  · rcases hco.v with e | e
    · left
      rw [e]
      rfl
    · right
      rw [e]
      rfl
  · rw [hco.f]
    rfl
  · have e := hco.P
    rcases e with e | e | ⟨e, e2⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · -- the third case of `impedeP` is stated from the frame's start: a push of 1 px after a move left or none
      refine Or.inr (Or.inr ⟨?_, e2⟩)
      have hm := hmove
      have e3 : sbyte (B.ram.get! (I sy.Player_X_Speed)) ≤ 0 := e2
      omega

/-- **A real frame under `ReadR` moves `P` left by at most `16·top + 256`**: the move is `16·v₂` with `|v₂| ≤ top`, and the collision routine and the rest of the frame
take off at most 256 (`Collide.P`). With the same conditions as `frame_readR`. -/
theorem frame_readR_low {m0 : Machine} {S : UInt8} {M : Machine} {i : UInt8} {n₀ : Nat} {idle : UInt16} (hOK : modelOK sy m0 S = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (h : ReadR sy (Rom.of m0) S M i n₀) (hbef : ∀ a ∈ hBytes sy, peek (trace M i n₀) a = peek M a) (hT : InTime (Rom.of m0) idle M i n₀)
    (hfar : 2048 ≤ posP sy M ∧ posP sy M + 2048 < 0x1000000) :
    posP sy M - 16 * (TopSpeed.top sy : Int) - 256 ≤ posP sy (frame M i) := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  obtain ⟨k1, v₁, f₁, b1, A1, an, G1, S1, I1⟩ := frame_pathI hb hfr hF h.at_frame
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h.at_frame)
  have e4 : t = (planOf sy m0 S (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have htl := hF.tails t ht
  rw [e4] at htl
  obtain ⟨k2, b2, g2, p2, v2, ff2, d2, r2, m2, q2, I2⟩ := tail_spec htl hF.digits A1
  have e0 := (trace_inFrame hT.loop hT.start (InFrameN.add' I1 rfl I2) hT.time (k1 + k2) (Nat.le_refl _)).1
  rw [stepN_add] at e0
  generalize hB : stepN k2 (stepN k1 (trace M i n₀)) = B at e0 v2 ff2 q2 p2
  have hco := h.collide (n₀ + (k1 + k2)) (by omega) (by rw [e0]; exact p2)
  rw [e0] at hco
  have eP : posP sy (trace M i n₀) = posP sy M := posP_congr hbef
  obtain ⟨g1, _⟩ := G1
  have ePk : posP sy (stepN k1 (trace M i n₀)) = posP sy (trace M i n₀) := by
    rw [posP_eq, posP_eq]
    obtain ⟨s1, s2, s3⟩ := S1
    show posOf ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_PageLoc)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Position)) ((stepN k1 (trace M i n₀)).ram.get! (I sy.SprObject_X_MoveForce)) =
      posOf ((trace M i n₀).ram.get! (I sy.Player_PageLoc)) ((trace M i n₀).ram.get! (I sy.Player_X_Position)) ((trace M i n₀).ram.get! (I sy.SprObject_X_MoveForce))
    rw [s1, s2, s3]
  have hv2 : B.ram.get! (I sy.Player_X_Speed) = (stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed) := v2
  have hr1 := speed_int g1
  have hmove : posP sy B = posP sy M + 16 * sbyte (B.ram.get! (I sy.Player_X_Speed)) := by
    rw [hv2]
    obtain ⟨a1, a2⟩ := posOf_range (peek B sy.Player_PageLoc) (peek B sy.Player_X_Position) (peek B sy.SprObject_X_MoveForce)
    rw [← posP_eq] at a1 a2
    have a3 := sbyte_range ((stepN k1 (trace M i n₀)).ram.get! (I sy.Player_X_Speed))
    have a4 := hfar
    rw [ePk, eP] at q2
    omega
  rw [hv2] at hmove
  have e := hco.P
  rcases e with e | e | ⟨e, _⟩ <;> omega

end framesI

end Smbrta.FrameModel
