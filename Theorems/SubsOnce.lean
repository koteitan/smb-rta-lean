import Theorems.AfterKeep

/-!
# A frame in control comes to the scroll handler at most once

`AfterKeep.subs_once` shows that a frame comes to the scroll handler (`PlayerSubs`) once after the player's routine, but its walks cut the paths at a store to the routine,
the mode or the task by its address, so it needs that no instruction of the frame has one (`FrameKeep.Frames.noStore`). The frame of the touch has one: the write of the
pole's routine. Here two walks of `FrameKeep` (the steps `kstep` of the guard `guardK`, no path cut) follow the whole frame:

* the first from the frame's start until every path comes to the scroll handler, or ends the frame (`walkS1`);
* the second from there to the frame's end; it fails if a path comes to the scroll handler again (`walkS2`).

So (`subs_once`): a frame that starts in the idle loop in control (`FrameKeep.StartK`), each of whose instructions meets `CleanK` of `guardK`, comes to the scroll handler
at one instruction at most. The condition on each instruction is the one that every frame up to the touch meets (`FrameKeep.Frames.cleanAt`).

The searches are no part of the proof: the check walks every state of its tables. No game data. Page: `1-1/f-6-18-2-SubsOnce.md`.
-/

namespace Smbrta.SubsOnce

open TaintRun
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)
open FrameKeep (CfgK CleanK preK kstep coverK endOK)

/-! ## The walks -/

/-- **The first walk**: from `A`, step by step until every path comes to the `pc` `Q` where `atQ` holds, ends the frame at the start of a frame (`endOK`), or reaches a
state of the table -/
def walkS1 (C : CfgK) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (if B.pc == Q then atQ B else (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkS1 C Q atQ n B)
      else B.k == A.k + 1 && endOK C.G B

/-- **The second walk**: from `A`, step by step until every path ends the frame at the start of a frame, or reaches a state of the table; no path comes to `Q` -/
def walkS2 (C : CfgK) (Q : UInt16) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && ((C.cut.get! B.pc.toNat != 0 && coverK C B) || walkS2 C Q n B)
      else B.k == A.k + 1 && endOK C.G B

/-! ## On the ROM -/

/-- the search from the frame's start to the scroll handler: no part of the proof -/
def s1Search (sy : Syms) (m0 : Machine) : PrevKeep.PS :=
  let G := FrameKeep.guardK sy m0
  PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) [] [] [] [] (fun A => A.pc == sy.PlayerSubs) [FrameKeep.startK G [] false, FrameKeep.startK G [] true]

/-- the configuration of a walk with the table of the search `X` -/
def cfgOfX (sy : Syms) (m0 : Machine) (q : Array AS × Std.HashMap Nat (List Nat) × ByteArray) : CfgK :=
  let E := PipeEntryRule.envOf m0
  { E, ops := (aRows E).toArray, S := FrameKeep.spotOf sy m0, G := FrameKeep.guardK sy m0, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1,
    cut := q.2.2, key := PrevKeep.keyP (FrameKeep.spotOf sy m0) (FrameKeep.guardK sy m0) [], fin := fun _ => true }

/-- **The first walk's table**: the states of the search, but those at the scroll handler -/
def cfgS1 (sy : Syms) (m0 : Machine) (P : PrevKeep.PS) : CfgK :=
  cfgOfX sy m0 (AfterKeep.tableBut (PrevKeep.keyP (FrameKeep.spotOf sy m0) (FrameKeep.guardK sy m0) []) sy.PlayerSubs P.X)

/-- **The second walk's table**, from the states at the scroll handler `starts` -/
def cfgS2 (sy : Syms) (m0 : Machine) (starts : List AS) : CfgK :=
  let P := PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) [] [] [] [] (fun A => A.pc == sy.PlayerSubs) starts
  cfgOfX sy m0 (FrameKeep.tableOfKW (PrevKeep.keyP (FrameKeep.spotOf sy m0) (FrameKeep.guardK sy m0) []) P.X)

/-- what the first walk asks at the scroll handler: the second walk succeeds -/
def atS (C2 : CfgK) (Q : UInt16) (B : AS) : Bool := walkS2 C2 Q FrameKeep.fuelK B

/-- **The check**: the first walk from the frame's start and from its table, asking the second walk at the scroll handler; the second walk from its table -/
def subsCheck (sy : Syms) (m0 : Machine) : Bool :=
  let G := FrameKeep.guardK sy m0
  let P := s1Search sy m0
  let C1 := cfgS1 sy m0 P
  let C2 := cfgS2 sy m0 P.stops.toList
  let Q := sy.PlayerSubs
  Q != G.idle && decide (G.late < dotsPerFrame) &&
    C1.t.all (walkS1 C1 Q (atS C2 Q) FrameKeep.fuelK) && walkS1 C1 Q (atS C2 Q) FrameKeep.fuelK (FrameKeep.startK G [] false) &&
    walkS1 C1 Q (atS C2 Q) FrameKeep.fuelK (FrameKeep.startK G [] true) && C2.t.all (walkS2 C2 Q FrameKeep.fuelK)

/-! ## The walks cover the frame -/

section
variable {C : CfgK} {Q : UInt16} {atQ : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a first walk from `A` succeeds -/
def LiveS1 (C : CfgK) (Q : UInt16) (atQ : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkS1 C Q atQ n A = true

/-- `A` covers `m`, and a second walk from `A` succeeds -/
def LiveS2 (C : CfgK) (Q : UInt16) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkS2 C Q n A = true

theorem cover_of {P : AS → Prop} (ht : ∀ D ∈ C.t, P D) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : coverK C B = true) : ∃ D, P D ∧ Sim C.E F D m ∧ D.k = B.k := by
  unfold coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hD : D ∈ C.t := by rw [← he]; exact Array.getElem_mem hi
    exact ⟨D, ht D hD, sim_le hle hs, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepS1 (ht : C.t.all (walkS1 C Q atQ Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveS1 C Q atQ F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A', LiveS1 C Q atQ F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc = Q ∧ ∃ B, atQ B = true ∧ Sim C.E F B (go step m).2) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, endOK C.G B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkS1] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkS1, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        by_cases hq : B.pc = Q
        · rw [if_pos (by simp [hq])] at hw2
          exact Or.inr (Or.inl ⟨k2, k3, by rw [h1.pc]; exact hq, B, hw2, h1⟩)
        · rw [if_neg (by simp [hq])] at hw2
          have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
          rcases hw2 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD, hsD, _⟩ := cover_of (P := fun D => walkS1 C Q atQ Fu D = true) (Array.all_eq_true_iff_forall_mem.1 ht) hkl h1 h3
            exact Or.inl ⟨D, ⟨hsD, Fu, hD⟩, k2, k3, hq'⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact Or.inr (Or.inr ⟨k2, B, hw2.2, h1⟩)

theorem live_stepS2 (ht : C.t.all (walkS2 C Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveS2 C Q F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A', LiveS2 C Q F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, endOK C.G B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkS2] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkS2, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw2
        obtain ⟨hq, hw3⟩ := hw2
        have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hsD, _⟩ := cover_of (P := fun D => walkS2 C Q Fu D = true) (Array.all_eq_true_iff_forall_mem.1 ht) hkl h1 h3
          exact Or.inl ⟨D, ⟨hsD, Fu, hD⟩, k2, k3, hq'⟩
        · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact Or.inr ⟨k2, B, hw2.2, h1⟩

theorem pc_of_end {G : PipeWrites.Guard} {B : AS} {m : Machine} (hb : endOK G B = true) (hs : Sim C.E F B m) : m.pc = G.idle := by
  rw [hs.pc]
  simp only [endOK, Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.1.1.1.1

/-- after the frame's end the machine stays where it ended -/
theorem stays {m : Machine} {i : UInt8} {e : Nat} (h : (trace m i e).frame = m.frame + 1) : ∀ j, e ≤ j → trace m i j = trace m i e := by
  intro j hj
  have hst : ((trace m i e).frame ≥ m.frame + 1 || (trace m i e).halted) = true := by simp [h]
  have e2 := PipeEntryRule.trace_stop hst (j - e)
  rw [show e + (j - e) = j by omega] at e2
  exact e2

/-- **The first walk: from `k` to the first arrival at `Q`.** The machine `k` instructions into the frame of `m`, covered by a state from which the first walk succeeds,
comes to `Q` at a first instruction `k₁ > k`, in a state where `atQ` holds; or it never comes to `Q` after `k`. -/
theorem run_S1 (ht : C.t.all (walkS1 C Q atQ Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hQ : Q ≠ C.G.idle) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkS1 C Q atQ Fu' A = true) (hs : Sim C.E F A (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (∃ k₁, k < k₁ ∧ (trace m i k₁).pc = Q ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧ (trace m i k₁).frame = m.frame ∧
      m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ ∃ B, atQ B = true ∧ Sim C.E F B (trace m i k₁)) ∨
    (∀ j, k < j → (trace m i j).pc ≠ Q) := by
  have key : ∀ d, (∃ A, LiveS1 C Q atQ F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        ∀ j, k < j → j ≤ k + d → (trace m i j).pc ≠ Q) ∨
      (∃ k₁, k < k₁ ∧ k₁ ≤ k + d ∧ (trace m i k₁).pc = Q ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧ (trace m i k₁).frame = m.frame ∧
        m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ ∃ B, atQ B = true ∧ Sim C.E F B (trace m i k₁)) ∨
      (∃ e, e ≤ k + d ∧ (trace m i e).frame = m.frame + 1 ∧ (trace m i e).pc = C.G.idle ∧ ∀ j, k < j → j ≤ e → (trace m i j).pc ≠ Q) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | h | ⟨e, h1, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepS1 ht hkl hops hT h1 (hcl (k + d)) with ⟨A', a1, a3, a4, a5⟩ | ⟨a1, a2, a3, B, b1, b2⟩ | ⟨a1, B, b1, b2⟩
        · rw [← e] at a1 a3 a4 a5
          refine Or.inl ⟨A', a1, a3.trans h2, by omega, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega]
            exact a5
        · rw [← e] at a1 a2 a3 b2
          exact Or.inr (Or.inl ⟨k + (d + 1), by omega, Nat.le_refl _, a3, fun j hj1 hj2 => h4 j hj1 (by omega), a1.trans h2, by omega, B, b1, b2⟩)
        · rw [← e] at a1 b2
          have hpc : (trace m i (k + (d + 1))).pc = C.G.idle := pc_of_end b1 b2
          refine Or.inr (Or.inr ⟨k + (d + 1), Nat.le_refl _, by rw [a1, h2], hpc, fun j hj1 hj2 => ?_⟩)
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega, hpc]
            exact fun h => hQ h.symm
      · obtain ⟨k₁, h1, h2, h3⟩ := h
        exact Or.inr (Or.inl ⟨k₁, h1, by omega, h3⟩)
      · exact Or.inr (Or.inr ⟨e, by omega, h2, h3, h4⟩)
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A', h1, _, h3, _⟩ | ⟨k₁, h1, _, h3⟩ | ⟨e, _, h2, h3, h4⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact Or.inl ⟨k₁, h1, h3⟩
  · right
    intro j hj
    by_cases h5 : j ≤ e
    · exact h4 j hj h5
    · rw [stays h2 j (by omega), h3]
      exact fun h => hQ h.symm

/-- **The second walk: no arrival at `Q` after `k`.** The machine `k` instructions into the frame of `m`, covered by a state from which the second walk succeeds, does not
come to `Q` again. -/
theorem run_S2 (ht : C.t.all (walkS2 C Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hQ : Q ≠ C.G.idle) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkS2 C Q Fu' A = true) (hs : Sim C.E F A (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    ∀ j, k < j → (trace m i j).pc ≠ Q := by
  have key : ∀ d, (∃ A, LiveS2 C Q F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        ∀ j, k < j → j ≤ k + d → (trace m i j).pc ≠ Q) ∨
      (∃ e, e ≤ k + d ∧ (trace m i e).frame = m.frame + 1 ∧ (trace m i e).pc = C.G.idle ∧ ∀ j, k < j → j ≤ e → (trace m i j).pc ≠ Q) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨e, h1, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepS2 ht hkl hops hT h1 (hcl (k + d)) with ⟨A', a1, a3, a4, a5⟩ | ⟨a1, B, b1, b2⟩
        · rw [← e] at a1 a3 a4 a5
          refine Or.inl ⟨A', a1, a3.trans h2, by omega, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega]
            exact a5
        · rw [← e] at a1 b2
          have hpc : (trace m i (k + (d + 1))).pc = C.G.idle := pc_of_end b1 b2
          refine Or.inr ⟨k + (d + 1), Nat.le_refl _, by rw [a1, h2], hpc, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega, hpc]
            exact fun h => hQ h.symm
      · exact Or.inr ⟨e, by omega, h2, h3, h4⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A', h1, _, h3, _⟩ | ⟨e, _, h2, h3, h4⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · intro j hj
    by_cases h5 : j ≤ e
    · exact h4 j hj h5
    · rw [stays h2 j (by omega), h3]
      exact fun h => hQ h.symm

end

/-! ## A frame in control -/

variable {sy : Syms} {m0 : Machine}

/-- **A frame in control comes to the scroll handler at most once.** The frame of `m` starts in the idle loop in control (`FrameKeep.StartK`), and each of its instructions
meets `CleanK` of `FrameKeep.guardK`. Then two instructions of it at the scroll handler (`PlayerSubs`) are the same. `hc` is the check of the two walks on the ROM. No
condition on the stores to the routine, the mode or the task: the frame of the touch writes the routine. -/
theorem subs_once (hc : subsCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) :
    ∀ k k', (trace m i k).pc = sy.PlayerSubs → (trace m i k').pc = sy.PlayerSubs → k = k' := by
  simp only [subsCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hQ, _⟩, ht1⟩, hs0⟩, hs1⟩, ht2⟩ := hc
  generalize s1Search sy m0 = P at ht1 hs0 hs1 ht2
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (E := PipeEntryRule.envOf m0) (W := []) rfl h0 (fun w hw => absurd hw (List.not_mem_nil))
  have hs' : Sim (PipeEntryRule.envOf m0) (m.frame, 2) (FrameKeep.startK (FrameKeep.guardK sy m0) [] b) (trace m i 0) :=
    { hs with pad := mem_top _ }
  have hw0 : walkS1 (cfgS1 sy m0 P) sy.PlayerSubs (atS (cfgS2 sy m0 P.stops.toList) sy.PlayerSubs) FrameKeep.fuelK (FrameKeep.startK (FrameKeep.guardK sy m0) [] b) = true := by
    cases b with
    | false => exact hs0
    | true => exact hs1
  have hp0 : (trace m i 0).pc ≠ sy.PlayerSubs := by
    show m.pc ≠ sy.PlayerSubs
    rw [h0.pc]
    exact fun h => hQ h.symm
  have hT : 2 ≤ (m.frame, (2 : UInt8)).2.toNat := by show 2 ≤ (2 : UInt8).toNat; decide
  rcases run_S1 (C := cfgS1 sy m0 P) (F := (m.frame, 2)) ht1 rfl rfl hT hQ (k := 0) hw0 hs' rfl (by show m.fdot + 3 * 0 ≤ m.fdot; omega) hcl with
    ⟨k₁, h1, h2, h3, h4, h5, B, hB, hsB⟩ | hno
  · have hno2 := run_S2 (C := cfgS2 sy m0 P.stops.toList) (F := (m.frame, 2)) ht2 rfl rfl hT hQ hB hsB h4 h5 hcl
    have one : ∀ k, (trace m i k).pc = sy.PlayerSubs → k = k₁ := by
      intro k hk
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · by_cases hk0 : k = 0
        · subst hk0
          exact absurd hk hp0
        · exact absurd hk (h3 k (by omega) h)
      · exact h
      · exact absurd hk (hno2 k h)
    intro k k' hk hk'
    rw [one k hk, one k' hk']
  · intro k _ hk _
    by_cases hk0 : k = 0
    · subst hk0
      exact absurd hk hp0
    · exact absurd hk (hno k (by omega))

end Smbrta.SubsOnce
