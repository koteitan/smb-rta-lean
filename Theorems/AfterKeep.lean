import Theorems.PrevKeep

/-!
# Above ground: three horizontal bytes after the scroll handler

A frame in control comes to the player's routine (the cut of `CtrlKeep`), and from there to the scroll handler (`PlayerSubs`). Here two walks follow the rest of the frame:

* the first from the cut to the first time the frame comes to the scroll handler (`walkQ1`), as the walk of the area's bytes does (`CtrlKeep.area_end`);
* the second from there to the frame's end (`walkKR`), with one byte followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on any write to it, and asks at the frame's
  end that it is still followed. It also fails if the frame comes to the scroll handler again.

Both cut the paths at a store to the routine, the mode or the task by its address (`FrameKeep.Frames.noStore`). The bytes are the moving direction, the running speed and
the stored speed (`hI`): no instruction from the scroll handler to the frame's end writes them by its address. A store through an index or a pointer whose target the walk does
not know would make it drop the followed byte; so the condition on each instruction is `CleanK` of `FrameKeep.guardF` and `SpareH`: such a store does not write these bytes.

So (`keepH`): at the frame's end the three bytes are those at the scroll handler, which the frame passes once after the player's routine. The other horizontal bytes are written
after the scroll handler on some paths (the screen's edge, the collision routine, death, the flagpole, vines, platforms): the program `after-bytes` lists the stores.

The searches are no part of the proof. No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.AfterKeep

open TaintRun
open PipeWrites (SG)

/-! ## The walks -/

/-- **The first walk**: from `A`, step by step until every path comes to the `pc` `Q` (the scroll handler) where `atQ` holds, or reaches a state of the table; a path stops at a
store to a byte of `l` by its address. The frame must not end before `Q`. -/
def walkQ1 (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ => (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => B.k == A.k && (if B.pc == Q then atQ B else (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkQ1 C l Q atQ n B)

/-- **The second walk**: `FrameKeep.walkKC` with the followed byte not decremented (`isRkDec`), and no path at `Q` again -/
def walkKR (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && ((C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKR C l Q n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ## On the ROM -/

/-- **The bytes that the rest of the frame keeps from the scroll handler on**: the moving direction, the running speed, the stored speed -/
def hI (sy : Syms) : List Nat := [(sy.Player_MovingDir &&& 0x7FF).toNat, (sy.RunningSpeed &&& 0x7FF).toNat, (sy.Player_XSpeedAbsolute &&& 0x7FF).toNat]

/-- **A store through an index or a pointer does not write the bytes of `hI`** (one instruction) -/
def SpareH (sy : Syms) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ hI sy

/-- `SpareH`, for a program -/
def spareHB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && (hI sy).contains (t &&& 0x7FF).toNat)
  | none => true

/-- the guard of the second walk for the byte `b`: that of `FrameKeep.guardF`, with `b` protected too -/
def guardH (sy : Syms) (m0 : Machine) (b : Nat) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := [b] ++ (FrameKeep.guardF sy m0).prot }

/-- the search from the cut to the scroll handler, from the states at the cut: no part of the proof -/
def q1Search (sy : Syms) (m0 : Machine) (v : UInt8) (starts : List AS) : PrevKeep.PS :=
  PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) (CtrlKeep.spareI sy m0) [] (CtrlKeep.watchA sy m0 v) (FrameKeep.ctlI sy) (fun A => A.pc == sy.PlayerSubs)
    (starts.map (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v)))

/-- the table of a search, but its states at `Q` -/
def tableBut (key : AS → Nat) (Q : UInt16) (X : SG) : Array AS × Std.HashMap Nat (List Nat) × ByteArray :=
  let X' := { X with multi := X.multi.filter fun k _ => match X.done[k]? with
    | some (A, _) => A.pc != Q
    | none => false }
  FrameKeep.tableOfKW key X'

/-- **The first walk's table** -/
def q1Cfg (sy : Syms) (m0 : Machine) (v : UInt8) (P : PrevKeep.PS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let q := tableBut key sy.PlayerSubs P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the state at the scroll handler, with the byte followed -/
def rkOn (B : AS) : AS := { B with rk := true, spent := false }

/-- **The second walk's table** for the byte `b`, from the states at the scroll handler `starts` -/
def q2Cfg (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy) (fun A => A.pc == sy.PlayerSubs) (starts.map rkOn)
  let q := FrameKeep.tableOfKW key P.X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun B => B.rk && !B.spent }

/-- what the first walk asks at the scroll handler: the second walk succeeds for each byte -/
def atQ (sy : Syms) (C2 : List FrameKeep.CfgK) (B : AS) : Bool := C2.all fun C => walkKR C (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK (rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk, then the second walks -/
def cfgPH (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check**: the walk of the pause bit up to the cut; from there the first walk to the scroll handler; from there, for each byte of `hI`, the second walk to the
frame's end -/
def hCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := q1Search sy m0 v cuts
  let C1 := q1Cfg sy m0 v P
  let C2 := (hI sy).map fun b => q2Cfg sy m0 b P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPH sy m0 v q C1 C2) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (walkKR C (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

/-! ## A step with the followed byte, with no condition on its value -/

section
open PipeTransitionAll (go)

variable {E : Env} {F : Nat × UInt8}

set_option maxRecDepth 100000 in
/-- **A step of the machine**, with the steps of `FrameKeep.kstep`, if the instruction does not decrement the followed byte (`FrameKeep.s_kstep` asks the counter to be at least 2) -/
theorem s_kstepL {S : FrameKeep.Spot} {G : PipeWrites.Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (LagFrames.opOf E A) = false) (hc : FrameKeep.CleanK G S.store m) (hs : Sim E F A m) :
    ∃ r ∈ FrameKeep.kstep S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold FrameKeep.kstep
  by_cases h1 : (!A.nmi && A.pc == S.store) = true
  · rw [if_pos h1]
    by_cases h2 : (A.x.isK && E.prg.get! (A.pc &&& E.mask).toNat == 0x9D) = true
    · rw [if_pos h2]
      exact LagFrames.s_succsL hops hd hs
    · rw [if_neg h2]
      by_cases h3 : FrameKeep.nonZero A.x = true
      · rw [if_pos h3]
        have hx := FrameKeep.ne_of_nonZero h3 hs.x
        exact LagFrames.s_gsuccL hops hd (FrameKeep.clean_of hc fun h => hx h.2) hs
      · rw [if_neg h3]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  · rw [if_neg h1]
    by_cases h4 : FrameKeep.lowAdc E A = true
    · rw [if_pos h4]
      simp only [FrameKeep.lowAdc, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h4
      obtain ⟨⟨⟨⟨⟨⟨hn, hp⟩, hop⟩, _⟩, _⟩, _⟩, _⟩ := h4
      have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
        pc := by
          show m.pc + 1 = A.pc + 1
          rw [hs.pc] }
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      refine PipeWrites.custom_step hs hn hp hop (by decide) (by decide) (fun u A₂ he => ?_) B hB
      rw [FrameKeep.op_65]
      obtain ⟨_, g1, g2⟩ := FrameKeep.s_sumL _ _ hs1 _ _ he
      exact ⟨g1, g2⟩
    · rw [if_neg h4]
      by_cases hn : A.nmi = true
      · have e : PipeWrites.gsucc G E ops A = succs E ops A := by
          unfold PipeWrites.gsucc
          simp [hn]
        rw [e]
        exact LagFrames.s_succsL hops hd hs
      · have hq : A.pc ≠ S.store := by
          intro hq
          apply h1
          simp [hn, hq]
        exact LagFrames.s_gsuccL hops hd (FrameKeep.clean_of hc fun h => hq (hs.pc ▸ h.1)) hs

/-- the machine of the second walk: the byte `b` followed, with its value `x` at the scroll handler -/
theorem sim_rkOn {B : AS} {m : Machine} {b : Nat} (hs : Sim E F B m) : Sim { E with rkI := b } (F.1, m.ram.get! b) (rkOn B) m :=
  { hs with rkv := fun _ => by simp [rkOn] }

end

/-! ## The second walk covers the frame from the scroll handler to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {C : FrameKeep.CfgK} {l : List Nat} {Q : UInt16} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a second walk from `A` succeeds -/
def LiveKR (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkKR C l Q n A = true

theorem cover_liveKR (ht : C.t.all (walkKR C l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveKR C l Q F D m ∧ D.k = B.k := by
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
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepKR (ht : C.t.all (walkKR C l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) {A : AS} {m : Machine}
    (hl : LiveKR C l Q F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveKR C l Q F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKR] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    simp only [walkKR, hx', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    obtain ⟨r, hr, hB⟩ := s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw3
        obtain ⟨hq, hw4⟩ := hw3
        have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
        rcases hw4 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKR ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3, hq'⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3, hq'⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.1.1.2, hw3.1.2, hw3.2, k1, h1⟩

/-- **The second walk: from the scroll handler to the frame's end.** The machine `k` instructions into the frame of `m`, covered by a state from which the walk succeeds, comes
to the frame's end in a state that meets `fin`, and the frame does not come to `Q` again. -/
theorem endKR (ht : C.t.all (walkKR C l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hQ : Q ≠ C.G.idle)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKR C l Q Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∧ ∀ d, 1 ≤ d → (trace m i (k + d)).pc ≠ Q := by
  have key : ∀ d, ((∃ A, LiveKR C l Q F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ FrameKeep.endOK C.G B = true ∧ Sim C.E F B (trace m i (k + d)))) ∧
      (1 ≤ d → (trace m i (k + d)).pc ≠ Q) := by
    intro d
    induction d with
    | zero => exact ⟨Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩, fun h => absurd h (by omega)⟩
    | succ d ih =>
      obtain ⟨ih, _⟩ := ih
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h2', h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases live_stepKR ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, a4, a5⟩ | ⟨a1, B, _, a2, a2', _, a3⟩
        · exact ⟨Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩, fun _ => a5⟩
        · refine ⟨Or.inr ⟨by rw [a1, h2], B, a2', a2, a3⟩, fun _ => ?_⟩
          rw [a3.pc]
          simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at a2
          rw [a2.1.1.1.1]
          exact fun h => hQ h.symm
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        refine ⟨Or.inr ⟨h1, B, h2, h2', h3⟩, fun _ => ?_⟩
        rw [h3.pc]
        simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at h2'
        rw [h2'.1.1.1.1]
        exact fun h => hQ h.symm
  refine ⟨?_, fun d hd1 => (key d).2 hd1⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases (key (fuelPerFrame - k)).1 with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h3⟩

/-! ## The first walk covers the frame from the cut to the scroll handler -/

variable {atQ' : AS → Bool}

/-- `A` covers `m`, and a first walk from `A` succeeds -/
def LiveQ1 (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ' : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkQ1 C l Q atQ' n A = true

theorem cover_liveQ1 (ht : C.t.all (walkQ1 C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveQ1 C l Q atQ' F D m := by
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

theorem live_stepQ1 (ht : C.t.all (walkQ1 C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveQ1 C l Q atQ' F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveQ1 C l Q atQ' F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc = Q ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkQ1] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkQ1, hx', Bool.false_or, List.all_eq_true] at hw
    have hw3 := hw A₁ hA r hr
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
          · obtain ⟨D, hD⟩ := cover_liveQ1 ht hkl h1 h3
            exact Or.inl ⟨D, hD, k2, k3, hq'⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · exfalso
        rw [hk1] at k1
        omega

/-- **The first walk: from the cut to the scroll handler.** The machine `k` instructions into the frame of `m`, covered by a state from which the walk succeeds, comes to `Q`
in the same frame at a first instruction `k₁ > k`, in a state where `atQ'` holds. -/
theorem q1_run (ht : C.t.all (walkQ1 C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkQ1 C l Q atQ' Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ k₁, k < k₁ ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧
      ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁) := by
  have key : ∀ d, (∃ A, LiveQ1 C l Q atQ' F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
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
        rcases live_stepQ1 ht hkl hops hT h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b2⟩
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

/-! ## On the ROM: one frame -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- **A frame in control keeps the moving direction, the running speed and the stored speed from the scroll handler to its end.** The frame starts in the idle loop in control
(`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardF` and `SpareH`, and writes neither the routine, nor the mode, nor the task by its address; the
area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time. Then it comes to the scroll handler
(`PlayerSubs`) at one instruction `k₁` after `n₀` and at no other (the first walk stops at the first, the second fails at another), and `k₁` has the three bytes of the
frame's end. `hc`, `hh` are the checks on the ROM. -/
theorem keepH_onceG (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ hI sy, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ k₁, ∀ x ∈ hI sy, (frame m i).ram.get! x = (trace m i k₁).ram.get! x ∧ ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → k = k₁ := by
  simp only [hCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPH sy m0 v q (q1Cfg sy m0 v P) ((hI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQ sy ((hI sy).map fun b => q2Cfg sy m0 b P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ := q1_run (C := q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hcl hx'
    refine ⟨k₁, fun x hxI => ?_⟩
    have hmem : q2Cfg sy m0 x P.stops.toList ∈ (hI sy).map fun b => q2Cfg sy m0 b P.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
    have hw2 := List.all_eq_true.1 hat _ hmem
    have ht2 := List.all_eq_true.1 hp3 _ hmem
    have hs2 : Sim (q2Cfg sy m0 x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := sim_rkOn hs₁
    have hclH : ∀ j, FrameKeep.CleanK (q2Cfg sy m0 x P.stops.toList).G (q2Cfg sy m0 x P.stops.toList).S.store (trace m i j) := hH x hxI
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := endKR (C := q2Cfg sy m0 x P.stops.toList) ht2 rfl rfl hne2 hw2 hs2 hf1 hd1 hclH hx'
    refine ⟨?_, fun k hk hpc => ?_⟩
    · change (B₂.rk && !B₂.spent) = true at hfin
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
      have e := hs₂.rkv hfin.1
      rw [if_neg (by simp [hfin.2])] at e
      exact e
    · rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
  · exact absurd harr (hno n₀ hf0)

/-- `keepH_onceG` with the condition `SpareH` on each instruction: it gives the second walk's guard from `CleanK` of `FrameKeep.guardF` -/
theorem keepH_once (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsp : ∀ n, SpareH sy (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ k₁, ∀ x ∈ hI sy, (frame m i).ram.get! x = (trace m i k₁).ram.get! x ∧ ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → k = k₁ := by
  refine keepH_onceG hc hh h0 hcl (fun x hxI j => ?_) hx hv harr hf0 hfirst
  refine CtrlKeep.cleanK_prot (G := FrameKeep.guardF sy m0) (l := [x]) (hcl j) (fun t ht hlt hm => ?_)
  have e : (t &&& 0x7FF).toNat = x := List.mem_singleton.1 hm
  exact hsp j t ht hlt (e ▸ hxI)

/-- **A frame in control keeps the moving direction, the running speed and the stored speed from the scroll handler to its end** (`keepH_once`): each instruction
`k ≥ n₀` at the scroll handler has the three bytes of the frame's end. -/
theorem keepH (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsp : ∀ n, SpareH sy (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ x ∈ hI sy, (frame m i).ram.get! x = (trace m i k).ram.get! x := by
  intro k hk hpc x hx'
  obtain ⟨k₁, H⟩ := keepH_once hc hh h0 hcl hsp hx hv harr hf0 hfirst
  obtain ⟨e, u⟩ := H x hx'
  rw [u k hk hpc]
  exact e

/-- **The frame comes to the scroll handler once after the player's routine** (`keepH_once`, the walks of `hCheck`): two instructions `k, k' ≥ n₀` at the scroll
handler are the same. -/
theorem subs_once (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : hCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsp : ∀ n, SpareH sy (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k k', n₀ ≤ k → n₀ ≤ k' → (trace m i k).pc = sy.PlayerSubs → (trace m i k').pc = sy.PlayerSubs → k = k' := by
  intro k k' hk hk' hpc hpc'
  obtain ⟨k₁, H⟩ := keepH_once hc hh h0 hcl hsp hx hv harr hf0 hfirst
  have u := (H _ (by simp [hI] : (sy.Player_XSpeedAbsolute &&& 0x7FF).toNat ∈ hI sy)).2
  rw [u k hk hpc, u k' hk' hpc']

end

/-! ## The condition on each instruction, for both walks -/

/-- **The bytes that no store through an index or a pointer writes**, besides those of `FrameKeep.guardF`: A and B, A and B of the frame before (`PrevKeep.abP`), the moving
direction, the running speed, the stored speed (`hI`) -/
def eI (sy : Syms) : List Nat := PrevKeep.abP sy ++ hI sy

/-- **A store through an index or a pointer does not write a byte of `eI`** (one instruction) -/
def SpareE (sy : Syms) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ eI sy

/-- `SpareE`, for a program -/
def spareEB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && (eI sy).contains (t &&& 0x7FF).toNat)
  | none => true

theorem spareAB_of {sy : Syms} {m : Machine} (h : SpareE sy m) : PrevKeep.SpareAB sy m :=
  fun t ht hlt hm => h t ht hlt (List.mem_append_left _ hm)

theorem spareH_of {sy : Syms} {m : Machine} (h : SpareE sy m) : SpareH sy m :=
  fun t ht hlt hm => h t ht hlt (List.mem_append_right _ hm)

end Smbrta.AfterKeep
