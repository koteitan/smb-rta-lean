import Theorems.EdgeStep

/-!
# Above ground: the scroll's three tests from the player's routine to the scroll handler

The scroll handler (`ScrollRule`) moves the screen only when the scroll lock is 0, the byte of his place on the screen is at least a threshold and the side
collision's timer is 0 (`ScrollRule.Allows`). The field `near` of the frames above ground (rounds 26, 27) related these bytes, at the scroll handler, to his
position. Round 27
tried a condition on the state where the frame first comes to the player's routine (`PlayerCtrlRoutine`) in its place (`PlaceAt`): there the timer part of the frame
is done, and the move is not. This file proves that a counted frame keeps the three bytes and the edge's two from there to the scroll handler (`keep_place`), and that
with `PlaceAt` there and `AmountAt` at the scroll handler the edge moves only behind him, without `collide` (`edge_step_place`). `PlaceAt` held on every real
frame measured, but it fails on 8,640 overwritten states of `surface-frames-check` (his position is overwritten there and his place byte is not), where the field
`near` holds; so `edge_step_place` is not used by the route. Round 28: the route uses `keep_place` (`MoveScroll.nearX_of_a`, `SurfaceFrames.OnFrames.nearAt`), with
the field `nearA`, which asks 2 px in place of the threshold (round 29: a theorem, `SurfaceFrames.OnFrames.nearAAt`, from the field `nearStep`).

The walks of `EdgeStep` follow a byte that `FrameKeep.guardE` protects. These three bytes are not protected: the timer part of the frame decrements the timer
through an index, and `CleanK` asks every such store to miss the protected bytes. A walk may still follow a byte that is not protected: a store with a target not
known only stops the following (`PipeWrites.AS.forgetK`). On real frames such a store comes between the player's routine and the scroll handler at the move
routine: it stores the fraction, the pixel and the page through an index. Its target, the base plus any index, cannot be any of the three bytes. So the walk here
(`walkQP`) takes the step of `FrameKeep.kstep` and, at a store through an index whose every target misses the followed byte (`farRk`: an absolute base that no index
takes to it, as `PositionKeep.absFarAt`, or a zero page base, below 256), it keeps following (`s_kstepP`, with `StepWrites.step_ram`).

The check on the ROM is `placeCheck`. No game data: the three bytes are the operands of the scroll handler's loads (`ScrollRule.places`).
Page: `1-1/e-2-10-3-15-PlaceKeep.md`.
-/

namespace Smbrta.PlaceKeep
open FrameModel TaintRun
open PipeTransitionAll (go)

variable {sy : Syms}

/-! ## A store through an index that misses the followed byte -/

/-- the stores and read-modify-writes through a zero page address and an index -/
def zpIOps : List UInt8 := [0x95, 0x94, 0xD6, 0xF6, 0x16, 0x36, 0x56, 0x76, 0x96]

theorem wOf_zpI : ∀ op ∈ zpIOps, StepWrites.wOf op = StepWrites.wZpx ∨ StepWrites.wOf op = StepWrites.wZpy := by
  intro op h
  simp only [zpIOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem ramIdx_u8 (u : UInt8) {i : Nat} (h : i ∈ StepWrites.ramIdx u.toUInt16) : i < 256 := by
  unfold StepWrites.ramIdx at h
  split at h
  · simp only [List.mem_singleton] at h
    subst h
    have e : (u.toUInt16 &&& 0x7FF).toNat = u.toUInt16.toNat &&& 0x7FF := UInt16.toNat_and _ _
    rw [e]
    have := Nat.and_le_left (n := u.toUInt16.toNat) (m := 0x7FF)
    have h2 : u.toUInt16.toNat = u.toNat := UInt8.toNat_toUInt16 u
    have h3 := u.toNat_lt
    omega
  · simp at h

/-- **An instruction whose every target misses the byte `i`** does not write it: a store through an absolute base that no index takes to `i`
(`PositionKeep.absFarAt`), or through a zero page base and an index with `256 ≤ i`; and `i` is not in the stack's page (the interrupt pushes there) -/
theorem miss_loc {R : Machine} {i : Nat} (hoff : i < 256 ∨ 512 ≤ i) (hp : 0x8000 ≤ R.pc) (hp1 : 0x8000 ≤ R.pc + 1) (hp2 : 0x8000 ≤ R.pc + 1 + 1)
    (hf : PositionKeep.absFarAt [i] R.prg R.prgMask R.pc = true ∨ (zpIOps.contains (R.prg.get! (R.pc &&& R.prgMask).toNat) = true ∧ 256 ≤ i)) :
    i ∉ StepWrites.stepLocs R := by
  intro hloc
  unfold StepWrites.stepLocs at hloc
  split at hloc
  · have := PositionWriters.stk_range 3 _ _ hloc
    omega
  split at hloc
  · simp at hloc
  rw [PositionWriters.fetchP hp] at hloc
  dsimp only at hloc
  rcases hf with hf | ⟨hz, hi⟩
  · simp only [PositionKeep.absFarAt, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hf
    obtain ⟨hops, hfar⟩ := hf
    generalize hop : R.prg.get! (R.pc &&& R.prgMask).toNat = op at hloc hops
    have e2 : R.pc + 1 + 1 = R.pc + 2 := by rw [UInt16.add_assoc]; rfl
    rcases hops with hx | hy
    · rw [PositionKeep.wOf_absX op hx] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      have e : go Smbrta.mAbx { R with pc := R.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
          pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.x.toUInt16)) { R with pc := R.pc + 1 } := rfl
      rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1] at hloc
      dsimp only at hloc
      rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { R with pc := R.pc + 1 + 1 }) hp2] at hloc
      dsimp only at hloc
      rw [e2] at hloc
      have e3 : (go (get >>= fun s => pure ((((R.prg.get! ((R.pc + 1) &&& R.prgMask).toNat).toUInt16 |||
          ((R.prg.get! ((R.pc + 2) &&& R.prgMask).toNat).toUInt16 <<< 8))) + s.x.toUInt16) : M UInt16) { R with pc := R.pc + 2 + 1 }).1 =
          PositionKeep.operandAt R.prg R.prgMask R.pc + R.x.toUInt16 := rfl
      rw [e3] at hloc
      exact PositionKeep.farB_spec hfar R.x _ hloc List.mem_cons_self
    · rw [PositionKeep.wOf_absY op hy] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      have e : go Smbrta.mAby { R with pc := R.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
          pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.y.toUInt16)) { R with pc := R.pc + 1 } := rfl
      rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1] at hloc
      dsimp only at hloc
      rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { R with pc := R.pc + 1 + 1 }) hp2] at hloc
      dsimp only at hloc
      rw [e2] at hloc
      have e3 : (go (get >>= fun s => pure ((((R.prg.get! ((R.pc + 1) &&& R.prgMask).toNat).toUInt16 |||
          ((R.prg.get! ((R.pc + 2) &&& R.prgMask).toNat).toUInt16 <<< 8))) + s.y.toUInt16) : M UInt16) { R with pc := R.pc + 2 + 1 }).1 =
          PositionKeep.operandAt R.prg R.prgMask R.pc + R.y.toUInt16 := rfl
      rw [e3] at hloc
      exact PositionKeep.farB_spec hfar R.y _ hloc List.mem_cons_self
  · generalize hop : R.prg.get! (R.pc &&& R.prgMask).toNat = op at hloc hz
    rcases wOf_zpI op (List.contains_iff_mem.1 hz) with hx | hy
    · rw [hx] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      have e : go Smbrta.mZpx { R with pc := R.pc + 1 } = go (fetch >>= fun b => get >>= fun s => pure ((b + s.x).toUInt16)) { R with pc := R.pc + 1 } := rfl
      rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1] at hloc
      dsimp only at hloc
      have := ramIdx_u8 _ hloc
      omega
    · rw [hy] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      have e : go Smbrta.mZpy { R with pc := R.pc + 1 } = go (fetch >>= fun b => get >>= fun s => pure ((b + s.y).toUInt16)) { R with pc := R.pc + 1 } := rfl
      rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1] at hloc
      dsimp only at hloc
      have := ramIdx_u8 _ hloc
      omega

/-- **A state at a store through an index whose every target misses the followed byte** (and the byte is followed, not in the stack's page) -/
def farRk (E : Env) (A : AS) : Bool :=
  A.rk && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) && (decide (E.rkI < 256) || decide (512 ≤ E.rkI)) &&
    (PositionKeep.absFarAt [E.rkI] E.prg E.mask A.pc || (zpIOps.contains (E.prg.get! (A.pc &&& E.mask).toNat) && decide (256 ≤ E.rkI)))

theorem miss_far {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : farRk E A = true) : E.rkI ∉ StepWrites.stepLocs m := by
  simp only [farRk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hp⟩, hp1⟩, hp2⟩, hoff⟩, hf⟩ := h
  rw [← hs.pc] at hp hp1 hp2
  rw [← hs.prg, ← hs.mask, ← hs.pc] at hf
  exact miss_loc hoff hp hp1 hp2 hf

/-- **The step of the walk**: that of `FrameKeep.kstep`, and at a state of `farRk` the byte stays followed -/
def kstepP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if farRk E A then (FrameKeep.kstep S G E ops A).map (Option.map fun B => { B with rk := true, spent := A.spent }) else FrameKeep.kstep S G E ops A

/-- **A step of the machine** with the steps of `kstepP`, if the instruction does not decrement the followed byte (as `AfterKeep.s_kstepL`) -/
theorem s_kstepP {E : Env} {F : Nat × UInt8} {S : FrameKeep.Spot} {G : PipeWrites.Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (LagFrames.opOf E A) = false) (hc : FrameKeep.CleanK G S.store m) (hs : Sim E F A m) :
    ∃ r ∈ kstepP S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hc hs
  unfold kstepP
  by_cases hf : farRk E A = true
  · rw [if_pos hf]
    refine ⟨r.map (fun B => { B with rk := true, spent := A.spent }), List.mem_map_of_mem hr, fun B' hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B =>
      simp only [Option.map_some] at hB'
      cases hB'
      obtain ⟨h1, h2⟩ := hB B rfl
      have hrk : A.rk = true := by
        simp only [farRk, Bool.and_eq_true] at hf
        exact hf.1.1.1.1.1
      have hm : (go step m).2.ram.get! E.rkI = m.ram.get! E.rkI := StepWrites.step_ram m E.rkI (miss_far hs hf)
      exact ⟨{ h1 with rkv := fun _ => by rw [hm]; exact hs.rkv hrk }, h2⟩
  · rw [if_neg hf]
    exact ⟨r, hr, hB⟩

/-! ## The walk -/

/-- **The walk with a followed byte that is not protected**: `EdgeStep.walkQR` with the steps of `kstepP` -/
def walkQP (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (kstepP C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => B.k == A.k && (if B.pc == Q then atQ B else (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkQP C l Q atQ n B)

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {E : Env} {F : Nat × UInt8} {C : FrameKeep.CfgK} {l : List Nat} {Q : UInt16} {Fu : Nat} {atQ' : AS → Bool}

/-- `A` covers `m`, and the walk succeeds from `A` -/
def LiveQP (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ' : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkQP C l Q atQ' n A = true

theorem cover_liveQP (ht : C.t.all (walkQP C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveQP C l Q atQ' F D m := by
  unfold FrameKeep.coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le hle hs, Fu, hall⟩
  · cases h2

theorem live_stepQP (ht : C.t.all (walkQP C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveQP C l Q atQ' F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveQP C l Q atQ' F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc = Q ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkQP] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    simp only [walkQP, hx', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    obtain ⟨r, hr, hB⟩ := s_kstepP hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      simp only [Bool.and_eq_true, beq_iff_eq] at hw3
      obtain ⟨hkB, hw4⟩ := hw3
      rcases h2 with ⟨_, k2, k3⟩ | ⟨k1, _⟩
      · by_cases hq : B.pc = Q
        · rw [if_pos (by simp [hq])] at hw4
          exact Or.inr ⟨k2, k3, by rw [h1.pc]; exact hq, B, hw4, h1⟩
        · rw [if_neg (by simp [hq])] at hw4
          have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw4
          rcases hw4 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD⟩ := cover_liveQP ht hkl h1 h3
            exact Or.inl ⟨D, hD, k2, k3, hq'⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · exfalso
        rw [hk1] at k1
        omega

/-- **The walk: from `k` to `Q`.** As `EdgeStep.qR_run`, with the steps of `kstepP`. -/
theorem qP_run (ht : C.t.all (walkQP C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkQP C l Q atQ' Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ k₁, k < k₁ ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧
      ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁) := by
  have key : ∀ d, (∃ A, LiveQP C l Q atQ' F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        ∀ j, k < j → j ≤ k + d → (trace m i j).pc ≠ Q) ∨
      (∃ k₁, k < k₁ ∧ k₁ ≤ k + d ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧
        (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁)) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | h
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepQP ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b2⟩
        · rw [← e] at a1 a2 a3 a4
          refine Or.inl ⟨A', a1, a2.trans h2, by omega, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega]
            exact a4
        · rw [← e] at a1 a2 a3 b2
          exact Or.inr ⟨k + (d + 1), by omega, Nat.le_refl _, a3, a1.trans h2, by omega, fun j hj1 hj2 => h4 j hj1 (by omega), B, b1, b2⟩
      · obtain ⟨k₁, h1, h2, h3⟩ := h
        exact Or.inr ⟨k₁, h1, by omega, h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3, _⟩ | ⟨k₁, h1, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact ⟨k₁, h1, h3⟩

end

/-! ## On the ROM: the check -/

open AfterKeep (tableBut rkOn)

/-- **The three bytes of the scroll's tests and the edge's two bytes**, as indices of RAM: the side collision's timer, his place on the screen, the scroll lock, and
the pixel and the page of the screen's left edge (the operands of the scroll handler's loads and stores, `ScrollRule.places`) -/
def placeI (sy : Syms) (m0 : Machine) : List Nat :=
  [(ScrollRule.places sy m0).sideB, (ScrollRule.places sy m0).pfs, (ScrollRule.places sy m0).lockB, (ScrollRule.places sy m0).lx, (ScrollRule.places sy m0).lp]

/-- **The walk's table** for the byte `b` from the states at the cut `cuts` to the scroll handler, with the guard `FrameKeep.guardF` (the byte not protected): the
search is no part of the proof -/
def pbCfg (sy : Syms) (m0 : Machine) (v : UInt8) (b : Nat) (cuts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let P := PrevKeep.searchFrom sy m0 E (CtrlKeep.spareI sy m0) [] W (FrameKeep.ctlI sy) (fun A => A.pc == sy.PlayerSubs)
    (cuts.map fun B => rkOn (CtrlKeep.toA W (CtrlKeep.valA sy v) B))
  let q := tableBut key sy.PlayerSubs P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the walk of the pause bit up to the cut (`CtrlKeep.cfgPz`), and from the cut the walk with the byte followed to the scroll handler -/
def cfgPb (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQP C1 (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK (rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) }

/-- **The check of the three bytes**: for each, the walk of the pause bit up to the cut, and from there the walk with the byte followed to the scroll handler -/
def placeCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
  (placeI sy m0).all fun b =>
    let C1 := pbCfg sy m0 v b cuts
    CtrlKeep.ctrlCheck1 (cfgPb sy m0 v q C1) && C1.t.all (walkQP C1 (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK)

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)

variable {m0 : Machine}

/-- **A frame in control keeps the scroll's three bytes and the screen's left edge from the player's routine to the scroll handler.** The frame starts in the idle loop in control
(`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardF` and writes neither the routine, nor the mode, nor the task by its address; the area's type
is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time, and to the scroll handler at `k`, the first time after `n₀`.
Then at `k` the side collision's timer, his place on the screen, the scroll lock and the edge's two bytes are those at `n₀`. `hc`, `hp` are the checks on the ROM. -/
theorem keep_place (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : placeCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    {k : Nat} (hk : n₀ ≤ k) (hpc : (trace m i k).pc = sy.PlayerSubs) (hb : ∀ j, n₀ < j → j < k → (trace m i j).pc ≠ sy.PlayerSubs) :
    ∀ x ∈ placeI sy m0, (trace m i k).ram.get! x = (trace m i n₀).ram.get! x := by
  simp only [placeCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hp
  obtain ⟨⟨hne1, _⟩, hbq⟩ := hp
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  intro x hxI
  obtain ⟨h1, ht⟩ := hbq x hxI
  generalize CtrlKeep.cutTable sy m0 true = q at h1 ht
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at h1 ht
  rcases CtrlKeep.cut_or_end2 (C := cfgPb sy m0 v q (pbCfg sy m0 v x cuts)) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hsR := AfterKeep.sim_rkOn (b := x) hsA
    have hw : walkQP (pbCfg sy m0 v x cuts) (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK
        (rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) = true := hB2
    obtain ⟨k₁, hk1, hq1, _, _, hbt, B₁, hat, hs₁⟩ := qP_run (C := pbCfg sy m0 v x cuts) ht rfl rfl hw hsR a2 a5 hcl hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [a1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exact absurd hq1 (hb k₁ hk1 h)
    subst hkk
    simp only [EdgeStep.atRk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hat
    obtain ⟨⟨⟨hrk, hsp⟩, _⟩, _⟩ := hat
    have e := hs₁.rkv hrk
    rw [if_neg (by simp [hsp])] at e
    exact e
  · exact absurd harr (hno n₀ hf0)

end Frames

/-! ## The edge's step from the place at the player's routine -/

/-- **Place(m)** (round 27), at the state where a frame first comes to the player's routine: when the side collision's timer is 0 and his place on the screen is at
least the scroll's threshold, he is at least that many pixels right of the screen's left edge. A condition on one state. -/
def PlaceAt (sy : Syms) (P : ScrollRule.Places) (m : Machine) : Prop :=
  m.ram.get! P.sideB = 0 → P.thr1 ≤ m.ram.get! P.pfs → ScrollRule.left16 P m + P.thr1.toNat ≤ EdgeStep.pixel16 sy m

/-- **Amount(Q)** (round 27), at the scroll handler: when the scroll is allowed, the byte the move stores is below the scroll's threshold. A condition on one state. -/
def AmountAt (P : ScrollRule.Places) (Q : Machine) : Prop :=
  ScrollRule.Allows P Q → (Q.ram.get! P.xs).toNat + 1 ≤ P.thr1.toNat

/-- **The edge's step from the place at the player's routine.** `Q` is a machine at the scroll handler (with the program of `m0`), `R` the instruction after its
call, `b` the frame's end, `M` the end of the frame before and `n0` the first arrival at the player's routine. If the scroll's rule holds from `Q` to `R` (`hs`,
`ScrollRule.scroll_edge`), the edge at `Q` is that of `M` and the edge at `b` that of `R`, the bytes of `placeI` at `Q` are those of `n0` (`keep_place`), his pixel at
`n0` is that of `M`, `Place(n0)`, `Amount(Q)` and the platforms' force at `Q` is 0, then edge(b) ≤ max(base(M), P(b)). When the edge moves,

  edge(b) = edge(R) ≤ 256·(left16(n0) + Y) + 255 ≤ 256·(pixel16(M) − 1) + 255 < P(M),   Y ≤ xs(Q) < thr1 ≤ pixel16(n0) − left16(n0).

Neither `collide` nor the position at `b` is needed. -/
theorem edge_step_place {m0 : Machine} {M Q R b n0 : Machine} (hpQ : Q.prg = m0.prg) (hkQ : Q.prgMask = m0.prgMask)
    (hs : SurfaceRead.edgeOf sy R = SurfaceRead.edgeOf sy Q ∨
      (ScrollRule.Allows (ScrollRule.places sy m0) Q ∧ ∃ Y : UInt8, Y.toNat ≤ (ScrollRule.amountOf (ScrollRule.places sy m0) Q).toNat ∧
        SurfaceRead.edgeOf sy R ≤ SurfaceRead.edgeOf sy Q + 256 * (Y.toNat : Int)))
    (hQ : SurfaceRead.edgeOf sy Q = SurfaceRead.edgeOf sy M) (hR : SurfaceRead.edgeOf sy b = SurfaceRead.edgeOf sy R)
    (hkp : ∀ x ∈ placeI sy m0, Q.ram.get! x = n0.ram.get! x) (hpix : EdgeStep.pixel16 sy n0 = EdgeStep.pixel16 sy M)
    (hpl : PlaceAt sy (ScrollRule.places sy m0) n0) (ham : AmountAt (ScrollRule.places sy m0) Q) (hplat : Q.ram.get! (ScrollRule.places sy m0).plat = 0) :
    SurfaceRead.edgeOf sy b ≤ max (SurfaceRead.baseOf sy M) (posP sy b) := by
  have hb : SurfaceRead.baseOf sy M = max (posP sy M) (SurfaceRead.edgeOf sy M) := rfl
  rcases hs with h | ⟨ha, Y, hy, h⟩
  · rw [hR, h, hQ]
    exact Int.le_trans (by rw [hb]; exact Int.le_max_right _ _) (Int.le_max_left _ _)
  · have ham' := ham ha
    obtain ⟨_, hpfs, hside, _⟩ := ha
    have e1 : Q.ram.get! (ScrollRule.places sy m0).sideB = n0.ram.get! (ScrollRule.places sy m0).sideB := hkp _ List.mem_cons_self
    have e2 : Q.ram.get! (ScrollRule.places sy m0).pfs = n0.ram.get! (ScrollRule.places sy m0).pfs := hkp _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have e4 : Q.ram.get! (ScrollRule.places sy m0).lx = n0.ram.get! (ScrollRule.places sy m0).lx :=
      hkp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have e5 : Q.ram.get! (ScrollRule.places sy m0).lp = n0.ram.get! (ScrollRule.places sy m0).lp :=
      hkp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    have hl : ScrollRule.left16 (ScrollRule.places sy m0) Q = ScrollRule.left16 (ScrollRule.places sy m0) n0 := by
      unfold ScrollRule.left16
      rw [e4, e5]
    have hpl' := hpl (by rw [← e1]; exact hside) (by rw [← e2]; exact hpfs)
    have hX : ScrollRule.amountOf (ScrollRule.places sy m0) Q = Q.ram.get! (ScrollRule.places sy m0).xs := by
      unfold ScrollRule.amountOf
      rw [hplat]
      exact UInt8.add_zero _
    rw [hX] at hy
    have h3 := ScrollRule.edgeOf_left16 (sy := sy) hpQ hkQ
    have h4 := EdgeStep.posP_ge (sy := sy) M
    rw [hl] at h3
    rw [hpix] at hpl'
    have c1 : ((ScrollRule.left16 (ScrollRule.places sy m0) n0 + (ScrollRule.places sy m0).thr1.toNat : Nat) : Int) ≤ (EdgeStep.pixel16 sy M : Int) := by
      exact_mod_cast hpl'
    have c2 : ((Q.ram.get! (ScrollRule.places sy m0).xs).toNat + 1 : Int) ≤ ((ScrollRule.places sy m0).thr1.toNat : Int) := by exact_mod_cast ham'
    have c3 : (Y.toNat : Int) ≤ ((Q.ram.get! (ScrollRule.places sy m0).xs).toNat : Int) := by exact_mod_cast hy
    push_cast at c1
    have hlt : SurfaceRead.edgeOf sy b < posP sy M := by
      rw [hR]
      omega
    exact Int.le_trans (Int.le_of_lt hlt) (Int.le_trans (by rw [hb]; exact Int.le_max_left _ _) (Int.le_max_left _ _))

end Smbrta.PlaceKeep
