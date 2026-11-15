import Theorems.SurfaceFrames

/-!
# Above ground: the stored speed of the frames before the touch, read from the machines

`PoleJoin.ApproachCases` had two fields on the stored speed of the frames before a fast jump: `stopped` (a frame from a stopped Mario writes `|v₂|` into the stored speed,
or keeps the stored speed and the moving direction) and `onGround` (the frame before the jump runs `ImposeFriction`). Here both are read from the machines of the frames
of `FrameKeep.Frames` (the field `keep` of `PoleJoin.Run`).

* `stored_c4N`: `FrameModel.stored_c4` without its hypothesis that the stored speed is `|v|` at the player's routine. On the ground, and in the air with Left or Right,
  `ImposeFriction` writes `|v|` into the stored speed (the same walks); in the air with neither, the speed, the stored speed and the moving direction stay up to the mover.
* `stored_subs`: on to the scroll handler. The walk of `FrameModel.storedOK` from the mover keeps the speed and the stored speed, and the walk of the mover
  (`FrameModel.tail_spec`) keeps the moving direction when the speed is 0. The frame comes to the scroll handler once (`honce`), so both walks end at the same instruction.
* `OnFrames.stored_end`: on a counted frame before the touch: with `SurfaceRead.frameE_move` (`v₂` is the speed at the scroll handler), the walk of `CtrlKeep` up to the
  player's routine and the `lag` frames before it (`OnFrames.lagKeep`), and `GuardE.keepHE` from the scroll handler to the frame's end (the stored speed and the moving
  direction at the end are those there).
* `OnFrames.stop_step` (the old field `stopped`): a frame from a stopped Mario ends with the stored speed `|v₂|`, or with the stored speed and the moving direction of the
  frame before. `OnFrames.ground_step` (the old field `onGround`): a frame that starts on the ground and reads no jump ends with the stored speed `|v₂|`.

There is no game data in this file. Page: `1-1/f-6-9-1-StopRead.md`.
-/

namespace Smbrta.StopRead

open FrameModel
open TopSpeed (absB)
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms}

/-- **From the player's routine to the mover, without `|v|` there** (`FrameModel.stored_c4` without `habs`): on the ground and in the air with Left or Right, the
stored speed at the mover is `|v|`; in the air with neither, the speed, the stored speed and the moving direction are those of the player's routine. -/
theorem stored_c4N {m0 : Machine} {S : UInt8} {R : Machine} (hb : GoodH (Rom.of m0) m0) (hfr : TopSpeed.frictionCheck sy m0 = true) (hF : ModelFacts sy m0 S)
    (hso : ∀ c ∈ allCases, storedFricOK sy m0 S c = true) (h : AtFrame sy (Rom.of m0) S R) :
    ∃ k, At (Rom.of m0) (planOf sy m0 S (caseOf sy R)).c4 (stepN k R) ∧ InFrameN (Rom.of m0) R k ∧
      ((stOf (caseOf sy R).n = 0 ∨ lrOf (caseOf sy R).n ≠ 0) →
        (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k R).ram.get! (I sy.Player_X_Speed))) ∧
      (stOf (caseOf sy R).n ≠ 0 → lrOf (caseOf sy R).n = 0 →
        (stepN k R).ram.get! (I sy.Player_X_Speed) = R.ram.get! (I sy.Player_X_Speed) ∧
        (stepN k R).ram.get! (I sy.Player_XSpeedAbsolute) = R.ram.get! (I sy.Player_XSpeedAbsolute) ∧
        (stepN k R).ram.get! (I sy.Player_MovingDir) = R.ram.get! (I sy.Player_MovingDir)) := by
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
    refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + k6)))), by rw [hfin]; exact A6, ?_, fun _ => by rw [hfin]; exact G6, fun h1 => absurd h0 h1⟩
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
      refine ⟨k1 + (k2 + (k3 + k6)), by rw [hfin]; exact A6, ?_, fun _ => by rw [hfin]; exact G6, fun _ h2 => absurd h2 hne⟩
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
      have e3 : R3.ram.get! (I sy.Player_MovingDir) = R.ram.get! (I sy.Player_MovingDir) := by
        rw [W3 _ (by simp [watchA, watchH]) (I_lt _), hk _ (by simp [watchH]) (I_lt _)]
      have hl0 : lrOf c.n = 0 := by simpa using hl
      refine ⟨k1 + (k2 + k3), by rw [hfin]; exact A3, ?_, fun h1 => ?_, fun _ _ => by rw [hfin]; exact ⟨e1, e2, e3⟩⟩
      · exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)
      · rcases h1 with h1 | h1
        · exact absurd h1 h0
        · exact absurd hl0 h1


/-- **At the scroll handler, without `|v|` at the player's routine.** The frame of `M` with the input `i` comes to the player's routine at `n₀` (`AtFrame`), and to the
scroll handler once after it (`honce`). On the ground and in the air with Left or Right, the stored speed at the scroll handler is `|v|` there; in the air with neither,
the speed and the stored speed are those of the player's routine, and so is the moving direction when the speed is 0. `hOK`, `hfr`, `hso` are the checks on the ROM. -/
theorem stored_subs {m0 M : Machine} {i : UInt8} {n₀ : Nat} (hOK : modelOK sy m0 (ctrlStack sy m0) = true) (hfr : TopSpeed.frictionCheck sy m0 = true)
    (hso : storedOK sy m0 (ctrlStack sy m0) = true) (h : AtFrame sy (Rom.of m0) (ctrlStack sy m0) (trace M i n₀))
    (hstart : (trace M i n₀).frame = M.frame) (htime : ∀ n, (trace M i n).pc ≠ sy.EndlessLoop → (trace M i n).fdot ≤ dotsPerFrame - 64)
    (hidle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (honce : ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace M i k).pc = sy.PlayerSubs → (trace M i k').pc = sy.PlayerSubs → k = k') :
    ∀ k, n₀ ≤ k → (trace M i k).pc = sy.PlayerSubs →
      ((stOf (caseOf sy (trace M i n₀)).n = 0 ∨ lrOf (caseOf sy (trace M i n₀)).n ≠ 0) →
        peek (trace M i k) sy.Player_XSpeedAbsolute = absB (peek (trace M i k) sy.Player_X_Speed)) ∧
      (stOf (caseOf sy (trace M i n₀)).n ≠ 0 → lrOf (caseOf sy (trace M i n₀)).n = 0 →
        peek (trace M i k) sy.Player_X_Speed = peek (trace M i n₀) sy.Player_X_Speed ∧
        peek (trace M i k) sy.Player_XSpeedAbsolute = peek (trace M i n₀) sy.Player_XSpeedAbsolute ∧
        (peek (trace M i n₀) sy.Player_X_Speed = 0 → peek (trace M i k) sy.Player_MovingDir = peek (trace M i n₀) sy.Player_MovingDir)) := by
  have hF := facts_of hOK
  have hb := base_good hF.base
  simp only [storedOK, Bool.and_eq_true, List.all_eq_true] at hso
  obtain ⟨k1, A1, C1, G1, K1⟩ := stored_c4N hb hfr hF hso.1 h
  obtain ⟨t, ht, hte⟩ := hF.anyT _ (caseOf_memF h)
  have e4 : t = (planOf sy m0 (ctrlStack sy m0) (caseOf sy (trace M i n₀))).c4 := cutSame_eq hte
  have hst := hso.2 t ht
  have htl := hF.tails t ht
  rw [e4] at hst htl
  obtain ⟨k2, _, A2, W2, _, C2⟩ := piece_spec hst A1
  obtain ⟨k3, _, _, hpc3, v3, _, _, _, md3, _, C3⟩ := tail_spec htl hF.digits A1
  have t2 := (trace_inFrame hidle hstart (InFrameN.add C1 C2) htime (k1 + k2) (Nat.le_refl _)).1
  have t3 := (trace_inFrame hidle hstart (InFrameN.add C1 C3) htime (k1 + k3) (Nat.le_refl _)).1
  rw [stepN_add] at t2 t3
  intro k hk hpc
  have p2 : (trace M i (n₀ + (k1 + k2))).pc = sy.PlayerSubs := by rw [t2]; exact A2.pc
  have p3 : (trace M i (n₀ + (k1 + k3))).pc = sy.PlayerSubs := by rw [t3]; exact hpc3
  have e2 := honce k (n₀ + (k1 + k2)) hk (by omega) hpc p2
  have e3 := honce k (n₀ + (k1 + k3)) hk (by omega) hpc p3
  have e23 : k3 = k2 := by omega
  subst e23
  have eQ : trace M i k = stepN k3 (stepN k1 (trace M i n₀)) := by rw [e2, t2]
  generalize stepN k1 (trace M i n₀) = R1 at A1 G1 K1 eQ W2 v3 md3
  rw [eQ]
  have wv : (stepN k3 R1).ram.get! (I sy.Player_X_Speed) = R1.ram.get! (I sy.Player_X_Speed) := W2 _ (by simp) (I_lt _)
  have wa : (stepN k3 R1).ram.get! (I sy.Player_XSpeedAbsolute) = R1.ram.get! (I sy.Player_XSpeedAbsolute) := W2 _ (by simp) (I_lt _)
  refine ⟨fun hc => ?_, fun h1 h2 => ?_⟩
  · show (stepN k3 R1).ram.get! (I sy.Player_XSpeedAbsolute) = absB ((stepN k3 R1).ram.get! (I sy.Player_X_Speed))
    rw [wv, wa]
    exact G1 hc
  · obtain ⟨f1, f2, f3⟩ := K1 h1 h2
    refine ⟨wv.trans f1, wa.trans f2, fun h0 => ?_⟩
    show (stepN k3 R1).ram.get! (I sy.Player_MovingDir) = (trace M i n₀).ram.get! (I sy.Player_MovingDir)
    have h0' : R1.ram.get! (I sy.Player_X_Speed) = 0 := f1.trans h0
    rw [md3, h0']
    simpa using f3

/-! ## On the frames before the touch -/

section Frames
open SurfaceFrames (OnFrames AreaRun start_fm keepA_mem frOf vOf farN)
variable {m0 : Machine} {B : PoleJoin.Box} {T J g : Nat} {seq : Nat → Machine} {Sr : FrameKeep.RealRun} {ar : Nat} {K : FrameKeep.Frames sy m0 Sr ar g seq}

/-- the machine at the player's routine of the counted frame `j` -/
abbrev atR (sy : Syms) (K : FrameKeep.Frames sy m0 Sr ar g seq) (j : Nat) : Machine :=
  trace (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))

/-- **The stored speed and the moving direction at the end of a counted frame before the touch.** On the ground or in the air with Left or Right (the case of the
player's routine), the stored speed at the end is `|v₂|`; in the air with neither, it is that of the end of the frame before, and so is the moving direction when the
frame starts with the speed 0. `hv0`, `hP0`, `hg` are as in `OnFrames.reads`; `hso` is the check on the ROM of the stored speed. -/
theorem stored_end (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : modelOK sy m0 (ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : storedOK sy m0 (ctrlStack sy m0) = true) (hidle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) :
    ((stOf (caseOf sy (atR sy K j)).n = 0 ∨ lrOf (caseOf sy (atR sy K j)).n ≠ 0) →
        (peek (seq j) sy.Player_XSpeedAbsolute).toNat = (frOf sy m0 K j).v₂.natAbs) ∧
      (stOf (caseOf sy (atR sy K j)).n ≠ 0 → lrOf (caseOf sy (atR sy K j)).n = 0 →
        peek (seq j) sy.Player_XSpeedAbsolute = peek (seq (j - 1)) sy.Player_XSpeedAbsolute ∧
        (vOf sy (seq (j - 1)) = 0 → peek (seq j) sy.Player_MovingDir = peek (seq (j - 1)) sy.Player_MovingDir)) := by
  obtain ⟨hR, hS, hE⟩ := O.readE_at hck hOK hfr hidle hst Ar hv0 hP0 hg h1 (by omega)
  have a1 := K.order (j - 1) (by omega)
  have a2 := K.ix_mono j g (by omega) (Nat.le_refl g)
  rw [show j - 1 + 1 = j by omega] at a1
  have harr := O.arrive hck hst h1 (by omega)
  have hAf : CtrlKeep.AreaOK sy v (O.fm j) := Ar.all _ (by omega)
  have hkh := GuardE.keepHE hck Ar.keep (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have honce := GuardE.subs_onceE hck Ar.keep (start_fm hst h1 (by omega)) (K.cleanE (K.ix j - 1) (by show K.ix j - 1 < K.ix g; omega))
    (K.noStore (K.ix j - 1) (by show K.ix j - 1 + 1 < K.ix g; omega)) hAf harr.1 harr.2.1 harr.2.2
  have A := CtrlKeep.ctrl_keep hck (start_fm hst h1 (by omega)) (K.cleanAt j h1 (by omega)) harr.1 harr.2.1 harr.2.2
  have hlag := O.lagKeep hck hst Ar h1 (by omega)
  have kp : ∀ x ∈ CtrlKeep.keepA sy, peek (atR sy K j) x = peek (seq (j - 1)) x := fun x hx => (A.keep x hx).trans (hlag x hx)
  obtain ⟨k, hk, hpc, ev, _, _⟩ := SurfaceRead.frameE_move (hE h3) hS
  have hS2 := stored_subs hOK hfr hso hR.at_frame hR.time.start hR.time.time hR.time.loop honce k hk hpc
  have hend := K.ends j h1 (by omega)
  have eA : peek (seq j) sy.Player_XSpeedAbsolute = peek (trace (K.fm j) (K.pad j) k) sy.Player_XSpeedAbsolute := by
    rw [hend]
    exact hkh k hk hpc _ (by simp [AfterKeep.hI])
  have eD : peek (seq j) sy.Player_MovingDir = peek (trace (K.fm j) (K.pad j) k) sy.Player_MovingDir := by
    rw [hend]
    exact hkh k hk hpc _ (by simp [AfterKeep.hI])
  have efr : frOf sy m0 K j = SurfaceRead.frameE sy m0 (seq (j - 1)) (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j)) := by
    unfold frOf
    rw [if_pos h3]
  refine ⟨fun hc => ?_, fun c1 c2 => ?_⟩
  · rw [efr, ev, eA, hS2.1 hc, SurfaceFrames.absB_natAbs]
  · obtain ⟨f1, f2, f3⟩ := hS2.2 c1 c2
    have kA := kp _ (keepA_mem (x := sy.Player_XSpeedAbsolute) (by simp))
    have kV := kp _ (keepA_mem (x := sy.Player_X_Speed) (Or.inl (by simp [FrameModel.hBytes])))
    have kD := kp _ (keepA_mem (x := sy.Player_MovingDir) (Or.inl (by simp [FrameModel.hBytes])))
    refine ⟨eA.trans (f2.trans kA), fun h0 => ?_⟩
    have h0' : peek (atR sy K j) sy.Player_X_Speed = 0 := by
      rw [kV]
      apply SurfaceFrames.sbyte_inj
      exact h0.trans (by decide)
    rw [eD, f3 h0', kD]

/-- the bytes of `CtrlKeep.keepA` at the player's routine of the counted frame `j` are those at the end of the counted frame before: the walk of `CtrlKeep` and the `lag`
frames before it (`OnFrames.lagKeep`) -/
theorem keep_at (hck : CtrlKeep.ctrlCheck sy m0 = true) (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n))
    {v : UInt8} (Ar : AreaRun sy m0 K v) {j : Nat} (h1 : 1 ≤ j) (h3 : j ≤ g) : ∀ x ∈ CtrlKeep.keepA sy, peek (atR sy K j) x = peek (seq (j - 1)) x := by
  have harr := O.arrive hck hst h1 h3
  have A := CtrlKeep.ctrl_keep hck (start_fm hst h1 h3) (K.cleanAt j h1 h3) harr.1 harr.2.1 harr.2.2
  have hlag := O.lagKeep hck hst Ar h1 h3
  exact fun x hx => (A.keep x hx).trans (hlag x hx)

/-- **A frame from a stopped Mario** (the old field `stopped` of `PoleJoin.ApproachCases`): a counted frame before the touch that starts with the speed 0 ends with the
stored speed `|v₂|`, or with the stored speed and the moving direction of the end of the frame before -/
theorem stop_step (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : modelOK sy m0 (ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : storedOK sy m0 (ctrlStack sy m0) = true) (hidle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g) (h0 : (frOf sy m0 K j).v = 0) :
    (peek (seq j) sy.Player_XSpeedAbsolute).toNat = (frOf sy m0 K j).v₂.natAbs ∨
      (peek (seq j) sy.Player_XSpeedAbsolute = peek (seq (j - 1)) sy.Player_XSpeedAbsolute ∧
        peek (seq j) sy.Player_MovingDir = peek (seq (j - 1)) sy.Player_MovingDir) := by
  have H := stored_end hck hOK hfr hso hidle O hst Ar hv0 hP0 hg h1 h3
  rw [SurfaceFrames.frOf_v] at h0
  by_cases hc : stOf (caseOf sy (atR sy K j)).n = 0 ∨ lrOf (caseOf sy (atR sy K j)).n ≠ 0
  · exact Or.inl (H.1 hc)
  · have c1 : stOf (caseOf sy (atR sy K j)).n ≠ 0 := fun e => hc (Or.inl e)
    have c2 : lrOf (caseOf sy (atR sy K j)).n = 0 := by
      by_cases e : lrOf (caseOf sy (atR sy K j)).n = 0
      · exact e
      · exact absurd (Or.inr e) hc
    obtain ⟨e1, e2⟩ := H.2 c1 c2
    exact Or.inr ⟨e1, e2 h0⟩

/-- on the ground with no jump read, the case of the player's routine is on the ground -/
theorem stOf_ground {R : Machine} (h0 : peek R sy.Player_State = 0) (hj : (readIn sy R).jump = false) : stOf (caseOf sy R).n = 0 := by
  have hs : ((caseOf sy R).inp 0).st = 0 := by simp [Case.inp, caseOf, h0]
  have hjj : ((caseOf sy R).inp 0).jump = false := by
    have e : ((caseOf sy R).inp 0).jump = (readIn sy R).jump := by
      simp [Case.inp, caseOf, readIn, h0, bne]
    rw [e, hj]
  have e : (caseOf sy R).n.st = 0 ∧ (caseOf sy R).n.jump = false := by
    unfold Case.n Potential.norm
    split
    · exact ⟨hs, hjj⟩
    · exact ⟨hs, hjj⟩
  unfold stOf
  rw [e.1, e.2]
  rfl

/-- **A frame on the ground before a jump** (the old field `onGround` of `PoleJoin.ApproachCases`): a counted frame before the touch that starts on the ground and
whose player's routine reads no jump runs `ImposeFriction`, so it ends with the stored speed `|v₂|` -/
theorem ground_step (hck : CtrlKeep.ctrlCheck sy m0 = true) (hOK : modelOK sy m0 (ctrlStack sy m0) = true)
    (hfr : TopSpeed.frictionCheck sy m0 = true) (hso : storedOK sy m0 (ctrlStack sy m0) = true) (hidle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (O : OnFrames sy m0 B T J g seq K) (hst : ∀ n, n < K.ix g → FrameKeep.StartK sy m0 (K.all n)) {v : UInt8} (Ar : AreaRun sy m0 K v)
    (hv0 : vOf sy (seq 0) = 0) (hP0 : posP sy (seq 0) = posP sy B.m) (hg : g ≤ farN sy B.m) {j : Nat} (h1 : 1 ≤ j) (h3 : j < g)
    (hs : peek (seq (j - 1)) sy.Player_State = 0) (hj : (SurfaceFrames.inAt sy (K.fm j) (K.pad j) (CtrlKeep.arrAt sy (K.fm j) (K.pad j))).jump = false) :
    (peek (seq j) sy.Player_XSpeedAbsolute).toNat = (frOf sy m0 K j).v₂.natAbs := by
  have H := stored_end hck hOK hfr hso hidle O hst Ar hv0 hP0 hg h1 h3
  have kS := keep_at hck O hst Ar h1 (by omega) _ (keepA_mem (x := sy.Player_State) (Or.inr (Or.inl (by simp [SurfaceFrames.vKeep]))))
  exact H.1 (Or.inl (stOf_ground (kS.trans hs) hj))

end Frames

end Smbrta.StopRead
