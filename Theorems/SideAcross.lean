import Theorems.SideLoop
import Theorems.PlaceKeep
import Theorems.SideTimer

/-!
# Above ground: the stores that may reach the side timer, with the block buffer's column, the block objects' offset and the castle's start row

Round 35 (`SideLoop`) proved the field `OnFrames.sideW` (a store through an index or a pointer does not write the side collision's timer) at every store that may
reach the timer (`PushTimer.NearW`) but four (`SideLoop.Resid`): the area parser's store through the block buffer's pointer, the two stores through the pointer in
the head's collision with a block, and the store of the castle's loop of rows. The first three need two bytes that live across frames: the block buffer's column
`BlockBufferColumnPos` (the area parser takes the pointer's high byte from a table at an index from it) and `SprDataOffset_Ctrl` (the index of the head's
collision's stores to the zero page, which may write the pointer). The fourth needs the castle's start row, which the area's data gives.

The two bytes are not kept by a frame alone: a store through the block buffer's pointer at an index that the walk does not know may write the column, and the
stores of the screen's buffer through `Y` may write the offset. Part f assumes that no store through an index or a pointer writes them (the fields `keepB` and
`bKeep` of `PoleJoin.Run`), and proves from it that every frame starts with the column below 32 and the offset 0 or 1 (`PoleBcol.frames_bcol`,
`PoleTileKeep.frames_keepY`). Here the frame's condition `FactsAt` is exactly that: the two bytes so at the frame's start (`InvB`), and at each instruction no store
through an index or a pointer writes them (`MissB`). The castle's start row is the condition `CastleRow` on one instruction: at the loop's head the row is at
most 10.

On a frame with `FactsAt` and with `CastleRow` after the scroll handler's call, the walk of `SideLoop` with the two bytes protected (`guardA`) and known from the
scroll handler's call on (`setB`), and with `X` split at the castle loop's head into the rows 0 to 10 (`spC`), proves `SideW` at every store that may reach the
timer (`near_sideA`). Two more things make it pass:
* from the frame's start to the scroll handler's call the two bytes are not written (`keepCheckA`: the walks of `SideTimer.keep_at` and `PlaceKeep.keep_place`, for
  these two bytes: `keep_cutA`, `keep_subsA`);
* after a store through a pointer whose low byte the walk does not know, the walk takes back each byte of the zero page that the store cannot reach, from the
  pointer's high byte and the range of `Y` (`takeP`, `SideRange.missP`, `izy_locs`): the pointer itself stays known through the parser's loop of rows and through
  the head's collision.

So the field `sideW` is asked only on a frame without `FactsAt`, and the castle's part of it becomes the field `OnFrames.castleRow`.
The searches that make the tables are no part of the proof; the checks are `aCheck` and `keepCheckA`. There is no game data in this file: the two bytes and the
loop's head are symbols. Page: `1-1/e-2-10-3-26-SideAcross.md`.
-/

namespace Smbrta.SideAcross

open TaintRun
open PipeTransitionAll (go)
open AfterKeep (walkQ1)

variable {sy : Syms}

/-! ## The two bytes and the frame's condition -/

/-- the block buffer's column, as a RAM index -/
def bcpI (sy : Syms) : Nat := (sy.BlockBufferColumnPos &&& 0x7FF).toNat

/-- the control of the block objects' offset, as a RAM index -/
def sdoI (sy : Syms) : Nat := (sy.SprDataOffset_Ctrl &&& 0x7FF).toNat

/-- **The two bytes on one state**: the block buffer's column below 32, and bits 1 to 7 of the block objects' offset 0 -/
def InvB (sy : Syms) (m : Machine) : Prop := m.ram.get! (bcpI sy) &&& 0xE0 = 0 ∧ m.ram.get! (sdoI sy) &&& 0xFE = 0

/-- **At one instruction**: a store through an index or a pointer writes neither byte -/
def MissB (sy : Syms) (m : Machine) : Prop := PushTimer.SideWL [bcpI sy, sdoI sy] m

/-- **The frame's condition**: the frame of `M` with the input `i` starts with `InvB`, and each of its instructions meets `MissB` (only the frame's own
instructions: the walk uses no more) -/
def FactsAt (sy : Syms) (M : Machine) (i : UInt8) : Prop :=
  InvB sy M ∧ ∀ k, (PipeEntryRule.trace M i k).frame = M.frame → MissB sy (PipeEntryRule.trace M i k)

/-- `InvB`, for a program -/
def invBB (sy : Syms) (m : Machine) : Bool := m.ram.get! (bcpI sy) &&& 0xE0 == 0 && m.ram.get! (sdoI sy) &&& 0xFE == 0

/-- `MissB`, for a program -/
def missBB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && [bcpI sy, sdoI sy].contains (t &&& 0x7FF).toNat)
  | none => true

/-- **The castle's start row, at one instruction**: at the head of the castle's loop of rows (`CRendLoop`) the row (`X`) is at most 10. The loop starts at the
row that the castle object's data gives and stores rows up to 10; with a start row of 11 or more it would run over the whole page. -/
def CastleRow (sy : Syms) (m : Machine) : Prop := m.pc = sy.CRendLoop → m.x.toNat ≤ 10

/-- **The split of the walk**: at the head of the castle's loop, `X` into its values from 0 to 10 (by `CastleRow`); elsewhere `SideLoop.spL` -/
def spC (sy : Syms) (E : Env) (A : AS) : List AS :=
  if A.pc == sy.CRendLoop && !A.x.isK then (SideRange.valsIn A.x 0 10).map fun v => { A with x := AB.known v } else SideLoop.spL sy E A

/-- a split that covers the machines that meet `H` -/
def CovH (E : Env) (F : Nat × UInt8) (H : Machine → Prop) (f : AS → List AS) : Prop :=
  ∀ A m, H m → Sim E F A m → ∃ B ∈ f A, Sim E F B m ∧ B.k = A.k

theorem cov_spC {E : Env} {F : Nat × UInt8} : CovH E F (CastleRow sy) (spC sy E) := by
  intro A m hH hs
  unfold spC
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    have hx : m.x.toNat ≤ 10 := hH (by rw [hs.pc]; exact hc.1)
    exact ⟨{ A with x := AB.known m.x }, List.mem_map.2 ⟨m.x, SideRange.mem_valsIn hs.x (Nat.zero_le _) hx, rfl⟩, { hs with x := mem_known_self _ }, rfl⟩
  · exact SideLoop.cov_spL sy A m hs

/-- **The walk's guard**: `FrameKeep.guardE` with the two bytes protected -/
def guardA (sy : Syms) (m0 : Machine) : PipeWrites.Guard :=
  { FrameKeep.guardE sy m0 with prot := [bcpI sy, sdoI sy] ++ (FrameKeep.guardE sy m0).prot }

theorem plain_app {Z prot : List Nat} {t : UInt16} (h : PipeWrites.Plain prot t) (hz : t < 0x2000 → (t &&& 0x7FF).toNat ∉ Z) :
    PipeWrites.Plain (Z ++ prot) t := by
  rcases h with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, ?_⟩
    simp only [List.mem_append, not_or]
    exact ⟨hz h1, h2⟩
  · exact Or.inr h1

set_option maxRecDepth 100000 in
/-- `CleanK` of the walk's guard, from `CleanK` of `FrameKeep.guardE` and `MissB` -/
theorem cleanK_A {m0 : Machine} {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hb : MissB sy m) :
    FrameKeep.CleanK (guardA sy m0) q m :=
  ⟨fun t ht hq => plain_app (h.store t ht hq) (hb t ht), h.read, h.jump, h.time⟩

/-- the state with the two bytes' bits of `InvB` known, and nothing else known of them -/
def setB (sy : Syms) (A : AS) : AS := (A.setK (bcpI sy) ⟨0, 0xE0⟩).setK (sdoI sy) ⟨0, 0xFE⟩

theorem sim_setB {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hI : InvB sy m) : Sim E F (setB sy A) m := by
  unfold setB
  refine PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs ?_) ?_
  · show m.ram.get! (bcpI sy) &&& 0xE0 = 0 &&& 0xE0
    rw [hI.1]
    rfl
  · show m.ram.get! (sdoI sy) &&& 0xFE = 0 &&& 0xFE
    rw [hI.2]
    rfl

/-- the two bytes as the search sets them (no part of the proof) -/
def invL (sy : Syms) : List (Nat × UInt8) := [(bcpI sy, 0xE0), (sdoI sy, 0xFE)]

/-! ## A store through a pointer whose high byte is known -/

/-- **The target of `STA (zp),Y` misses `s`**, when `SideRange.missP` says so of the state that covers the machine -/
theorem missP_ne {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) {s : Nat} (h : SideRange.missP s E A = true)
    (hlt : ((m.ram.get! (SideRange.zop E A).toNat).toUInt16 ||| ((m.ram.get! (SideRange.zop E A + 1).toNat).toUInt16 <<< 8)) + m.y.toUInt16 < 0x2000) :
    ((((m.ram.get! (SideRange.zop E A).toNat).toUInt16 ||| ((m.ram.get! (SideRange.zop E A + 1).toNat).toUInt16 <<< 8)) + m.y.toUInt16) &&& 0x7FF).toNat ≠ s := by
  unfold SideRange.missP at h
  have hl0 : (SideRange.zop E A).toNat < 2048 := by have := (SideRange.zop E A).toNat_lt; omega
  have hh0 : (SideRange.zop E A + 1).toNat < 2048 := by have := (SideRange.zop E A + 1).toNat_lt; omega
  have hlo := hs.ram _ hl0
  have hhi := hs.ram _ hh0
  have hm1 := List.all_eq_true.1 h _ (SideRange.mem_valsAll hhi)
  have a1 := minv_le hlo
  have a2 := le_maxv hlo
  have a3 := minv_le hs.y
  have a4 := le_maxv hs.y
  have hm2 := List.all_eq_true.1 hm1 ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
      ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) (List.mem_range.2 (by omega))
  rw [show (A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat + ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
      ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) = (m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat by omega,
    SideRange.w16] at hm2
  exact SideRange.miss_of (by simpa using hm2) hlt

/-- **`STA (zp),Y` does not write `i`**, when `SideRange.missP` says that every target misses it -/
theorem izy_locs {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hop : SideRange.opA E A = 0x91) (hn : A.nmi = false)
    (hp : 0x8000 ≤ A.pc) (hp1 : 0x8000 ≤ A.pc + 1) {i : Nat} (h : SideRange.missP i E A = true) : i ∉ StepWrites.stepLocs m := by
  intro hloc
  have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
  have hp' : 0x8000 ≤ m.pc := by rw [hs.pc]; exact hp
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hopm : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
  obtain ⟨c, a, hw, hwt⟩ := PushTimer.w_md 0x91 (by decide) m
  unfold StepWrites.stepLocs at hloc
  rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted]), PositionWriters.fetchP hp'] at hloc
  dsimp only at hloc
  rw [hopm, hw] at hloc
  simp only [StepWrites.Wr.locs] at hloc
  have ht : PipeWrites.wTarget 0x91 m = some (go Smbrta.mIzy { m with pc := m.pc + 1 }).1 := rfl
  rw [ht] at hwt
  rw [← Option.some.inj hwt, SideRange.izy_t hp1' hs.trk] at hloc
  have hz : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = SideRange.zop E A := by unfold SideRange.zop; rw [hs.prg, hs.mask, hs.pc]
  rw [hz] at hloc
  unfold StepWrites.ramIdx at hloc
  split at hloc
  · rename_i hlt
    simp only [List.mem_singleton] at hloc
    exact missP_ne hs h hlt hloc.symm
  · simp at hloc

/-- one byte of `B`: that of `A₁`, when the step of `A₁` does not write it, by `StepWrites.keepOK` or, at `STA (zp),Y`, by `SideRange.missP` (every target that
the high byte of the pointer, the low byte and `Y` allow misses it), and `A₁` knows a bit of it -/
def takeP (E : Env) (A₁ B : AS) (i : Nat) : AS :=
  if (A₁.getK i).k != 0 && (StepWrites.keepOK E (· == i) A₁ ||
      (SideRange.opA E A₁ == 0x91 && !A₁.nmi && decide (0x8000 ≤ A₁.pc) && decide (0x8000 ≤ A₁.pc + 1) && SideRange.missP i E A₁)) then
    B.setK i (A₁.getK i)
  else B

/-- **After the step of `A₁`**: when it is a store through an index or a pointer, each byte of `bs` that the store does not write is that of `A₁` (`takeP`) -/
def fixP (E : Env) (bs : List Nat) (A₁ B : AS) : AS :=
  if PushTimer.wOps.contains (SideRange.opA E A₁) then bs.foldl (takeP E A₁) B else B

theorem takeP_go {E : Env} {F : Nat × UInt8} {A₁ : AS} {m : Machine} (hs1 : Sim E F A₁ m) :
    ∀ (l : List Nat) (B : AS), (∀ i ∈ l, i < 2048) → Sim E F B (go step m).2 → Sim E F (l.foldl (takeP E A₁) B) (go step m).2
  | [], _, _, h => h
  | i :: t, B, hl, h => by
    show Sim E F (t.foldl (takeP E A₁) (takeP E A₁ B i)) (go step m).2
    have hi : i < 2048 := hl i List.mem_cons_self
    refine takeP_go hs1 t _ (fun j hj => hl j (List.mem_cons_of_mem _ hj)) ?_
    unfold takeP
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      refine SideRange.sim_setK_same h ?_
      have hk : (go step m).2.ram.get! i = m.ram.get! i := by
        rcases hc.2 with h2 | ⟨⟨⟨⟨hop, hn⟩, hp⟩, hp1⟩, hm⟩
        · exact StepWrites.keep_step hs1 h2 i (beq_self_eq_true i)
        · simp only [beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hop hn hp hp1
          exact StepWrites.step_ram m i (izy_locs hs1 hop hn hp hp1 hm)
      rw [hk]
      exact hs1.ram i hi
    · exact h

theorem fixP_sim {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} {bs : List Nat} (hbs : ∀ i ∈ bs, i < 2048) (hs1 : Sim E F A₁ m)
    (hB : Sim E F B (go step m).2) : Sim E F (fixP E bs A₁ B) (go step m).2 := by
  unfold fixP
  split
  · exact takeP_go hs1 _ B hbs hB
  · exact hB

theorem takeP_k (E : Env) (A₁ B : AS) (i : Nat) : (takeP E A₁ B i).k = B.k := by
  unfold takeP; split <;> rfl

theorem takeP_fold_k (E : Env) (A₁ : AS) : ∀ (l : List Nat) (B : AS), (l.foldl (takeP E A₁) B).k = B.k
  | [], _ => rfl
  | i :: t, B => (takeP_fold_k E A₁ t _).trans (takeP_k E A₁ B i)

theorem fixP_k (E : Env) (bs : List Nat) (A₁ B : AS) : (fixP E bs A₁ B).k = B.k := by
  unfold fixP; split
  · exact takeP_fold_k _ _ _ _
  · rfl

theorem zKeep_lt : ∀ i ∈ SideRange.zKeep, i < 2048 := by
  intro i hi
  have := List.mem_range.1 hi
  omega

/-! ## The condition at a store -/

/-- **`SideRange.missK` gives `SideW`** (the proof of `SideRange.okR_spec`, from the part after its test of the places) -/
theorem sideW_of_missK {m0 : Machine} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hp1 : 0x8000 ≤ A.pc + 1)
    (hp2 : 0x8000 ≤ A.pc + 1 + 1) (hmk : SideRange.missK (ScrollRule.places sy m0).sideB E A = true) : PushTimer.SideW sy m0 m := by
  intro t ht hlt heq
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = SideRange.opnd E A := by
    unfold PositionKeep.operandAt SideRange.opnd; rw [hs.prg, hs.mask, hs.pc]
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hp2' : 0x8000 ≤ m.pc + 1 + 1 := by rw [hs.pc]; exact hp2
  unfold SideRange.missK at hmk
  unfold PipeWrites.wTarget at ht
  generalize hop2 : SideRange.opA E A = op at hmk
  rw [hop, hop2] at ht
  dsimp only at hmk
  by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
  · exfalso
    have hz : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = false ∧ (op == 0x99) = false ∧ (op == 0x91) = false := by
      simp only [Bool.or_eq_true, beq_iff_eq] at c1
      rcases c1 with ((e | e) | e) | e <;> subst e <;> exact ⟨rfl, rfl, rfl⟩
    rw [if_neg (by simp [hz.1]), if_neg (by simp [hz.2.1]), if_neg (by simp [hz.2.2])] at hmk
    cases hmk
  · rw [if_neg c1] at ht
    by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
    · rw [if_pos c2, PushTimer.abx_t hp1' hp2', hoa] at ht
      rw [if_pos c2] at hmk
      have hm := List.all_eq_true.1 hmk m.x (SideRange.mem_valsAll hs.x)
      have e := Option.some.inj ht
      rw [e] at hm
      exact SideRange.miss_of (by simpa using hm) hlt heq
    · rw [if_neg c2] at ht
      rw [if_neg c2] at hmk
      by_cases c3 : (op == 0x99) = true
      · rw [if_pos c3, PushTimer.aby_t hp1' hp2', hoa] at ht
        rw [if_pos c3] at hmk
        have hm := List.all_eq_true.1 hmk m.y (SideRange.mem_valsAll hs.y)
        have e := Option.some.inj ht
        rw [e] at hm
        exact SideRange.miss_of (by simpa using hm) hlt heq
      · rw [if_neg c3] at hmk
        rw [if_neg c3] at ht
        by_cases c4 : (op == 0x91) = true
        · rw [if_pos c4, SideRange.izy_t hp1' hs.trk] at ht
          rw [if_pos c4] at hmk
          have hz : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = SideRange.zop E A := by unfold SideRange.zop; rw [hs.prg, hs.mask, hs.pc]
          rw [hz] at ht
          have e := Option.some.inj ht
          subst e
          exact missP_ne hs hmk hlt heq
        · rw [if_neg c4] at hmk
          cases hmk

/-- **What the walk asks at a state**: `SideRange.okR` with no places left out -/
def okA (sy : Syms) (m0 : Machine) (E : Env) (A : AS) : Bool :=
  !PushTimer.wOps.contains (SideRange.opA E A) ||
    (!A.nmi && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
      (!SideRange.nearA (ScrollRule.places sy m0).sideB E A || SideRange.missK (ScrollRule.places sy m0).sideB E A))

/-- **`okA` gives `SideW`** at a store that may reach the timer -/
theorem okA_spec {m0 : Machine} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : okA sy m0 E A = true)
    (hn : PushTimer.NearW sy m0 m) : PushTimer.SideW sy m0 m := by
  intro t ht hlt heq
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = SideRange.opnd E A := by
    unfold PositionKeep.operandAt SideRange.opnd; rw [hs.prg, hs.mask, hs.pc]
  have hw : PushTimer.wOps.contains (SideRange.opA E A) = true := by rw [← hop]; exact List.contains_iff_mem.2 (PushTimer.wTarget_ops ht)
  unfold okA at h
  rw [hw] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨_, _⟩, hp1⟩, hp2⟩, hc⟩ := h
  have hnA : SideRange.nearA (ScrollRule.places sy m0).sideB E A = true := by
    have e : PushTimer.nearWB sy m0 m = true := hn
    unfold PushTimer.nearWB at e
    unfold SideRange.nearA
    rw [← hop, ← hoa]
    exact e
  rw [hnA] at hc
  have hmk : SideRange.missK (ScrollRule.places sy m0).sideB E A = true := by
    rcases hc with h1 | h1
    · cases h1
    · exact h1
  exact sideW_of_missK hs hp1 hp2 hmk t ht hlt heq

/-! ## The walk: `SideRange.walkR` with `fixP` -/

/-- **The walk**: `SideRange.walkR`, with `fixP` of the zero page after each step in place of `SideRange.fixR` -/
def walkP (C : SideRange.CfgR) (l : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (C.ok A && ((FrameKeep.preK C.S C.G A).flatMap C.sp).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B0 =>
      if (fixP C.E SideRange.zKeep A₁ B0).k == A.k then
        (C.cut.get! (fixP C.E SideRange.zKeep A₁ B0).pc.toNat != 0 && SideRange.coverR C (fixP C.E SideRange.zKeep A₁ B0)) ||
          walkP C l n (fixP C.E SideRange.zKeep A₁ B0)
      else true)

/-- the table's check: from each piece of each state, the walk succeeds -/
def tableOKP (C : SideRange.CfgR) (l : List Nat) (Fu : Nat) : Bool := C.t.all fun D => (SideRange.pieces C.W D).all (walkP C l Fu)

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {C : SideRange.CfgR} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveP (C : SideRange.CfgR) (l : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkP C l n A = true

theorem cover_liveP (ht : tableOKP C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : SideRange.coverR C B = true) : ∃ D, LiveP C l F D m ∧ D.k = B.k := by
  unfold SideRange.coverR at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    simp only [Bool.and_eq_true] at h2
    have hle := PipeWrites.leK_le h2.1
    have hsD := sim_le hle hs
    have hb := SideRange.bok_of_leB hs h2.2
    obtain ⟨P, hP, hsP, hkP⟩ := SideRange.pieces_cov C.W hsD hb
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨P, ⟨hsP, Fu, List.all_eq_true.1 hall P hP⟩, by rw [hkP]; exact (PipeWrites.le_k hle).symm⟩
  · cases h2

/-- one step of the walk, on a machine that meets `H` -/
theorem live_stepP {H : Machine → Prop} (hsp : CovH C.E F H C.sp) (ht : tableOKP C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) {A : AS} {m : Machine} (hl : LiveP C l F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hH : H m)
    (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    C.ok A = true ∧
    ((∃ A', LiveP C l F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
      (go step m).2.frame = m.frame + 1) := by
  obtain ⟨hs, n, hw0⟩ := hl
  cases n with
  | zero => simp [walkP] at hw0
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    simp only [walkP, hx', Bool.false_or, Bool.and_eq_true] at hw0
    obtain ⟨hokA, hw1⟩ := hw0
    refine ⟨hokA, ?_⟩
    obtain ⟨A₀, hA0, hs0, hk0⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨A₁, hA1, hs1, hk1'⟩ := hsp A₀ m hH hs0
    have hA : A₁ ∈ (FrameKeep.preK C.S C.G A).flatMap C.sp := List.mem_flatMap.2 ⟨A₀, hA0, hA1⟩
    have hk1 : A₁.k = A.k := hk1'.trans hk0
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw1
    obtain ⟨hd, hw2⟩ := hw1 A₁ hA
    obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      have h1' := fixP_sim zKeep_lt hs1 h1
      have hkf := fixP_k C.E SideRange.zKeep A₁ B
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨_, k2⟩
      · left
        have e : (fixP C.E SideRange.zKeep A₁ B).k = A.k := by rw [hkf, k1, hk1]
        rw [if_pos (by simp [e])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveP ht hkl h1' h3
          exact ⟨D, hD, by rw [hk, e], k2, k3⟩
        · exact ⟨_, ⟨h1', n, h3⟩, e, k2, k3⟩
      · right
        exact k2

/-- **The walk: from `k` to the frame's end, each instruction of the frame meets `ok` in a state that covers it** (as `SideRange.okR_all`; the split covers
the machines that meet `H`, and each instruction from `k` on meets it) -/
theorem okP_all {H : Machine → Prop} (hsp : CovH C.E F H C.sp) (ht : tableOKP C l Fu = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkP C l Fu' A = true)
    (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, k ≤ j → (trace m i j).frame = m.frame → FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hH : ∀ j, k ≤ j → (trace m i j).frame = m.frame → H (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∀ j, k ≤ j → (trace m i j).frame = m.frame → ∃ B, Sim C.E F B (trace m i j) ∧ C.ok B = true := by
  have key : ∀ d, (∃ A, LiveP C l F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      (trace m i (k + d)).frame = m.frame + 1 := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | h1
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases (live_stepP hsp ht hkl hops h1 (hcl (k + d) (by omega) h2) (hH (k + d) (by omega) h2) (hx (k + d))).2 with ⟨A', a1, _, a3, a4⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · exact Or.inr (by rw [a1, h2])
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr h1
  intro j hj hfj
  rcases key (j - k) with ⟨A, h1, h2, _⟩ | h1
  · rw [show k + (j - k) = j by omega] at h1 h2
    exact ⟨A, h1.1, (live_stepP hsp ht hkl hops h1 (hcl j hj hfj) (hH j hj hfj) (hx j)).1⟩
  · rw [show k + (j - k) = j by omega] at h1
    omega

end

/-! ## The search: no part of the proof -/

/-- each byte `i` of `inv` has the bits of its mask known to be 0 in `A` -/
def invOK (inv : List (Nat × UInt8)) (A : AS) : Bool := inv.all fun (i, m) => (A.getK i).k &&& m == m && (A.getK i).v &&& m == 0

/-- one byte of `inv` -/
def invOK1 (i : Nat) (m : UInt8) (A : AS) : Bool := (A.getK i).k &&& m == m && (A.getK i).v &&& m == 0

/-- `A` with each byte of `inv` known to have the bits of its mask 0, and nothing else known of it -/
def setInv (inv : List (Nat × UInt8)) (A : AS) : AS := inv.foldl (fun A (i, m) => A.setK i ⟨0, m⟩) A

/-- the search's state, with what it found of the bytes -/
structure St where
  P : PrevKeep.PS := {}
  endF : Std.HashMap Nat Nat := {}
  loss : Std.HashMap (Nat × Nat) Nat := {}
  lossS : Array (Nat × Nat × AS × AS) := #[]
  endN : Nat := 0
  endS : Array AS := #[]

/-- the search from one piece (as `SideRange.runR`, with `fixP` and the bytes of `inv` looked at) -/
partial def runI (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (ok : AS → Bool)
    (l : List Nat) (keep fb : List Nat) (inv : List (Nat × UInt8)) (P0 : St) (k0 : Nat) (A0 : AS) : St := Id.run do
  let ⟨X0, pred0, fa0, ch0, st0, dr0⟩ := P0.P
  let mut T := { P0 with P := {} }
  let mut X := X0
  let mut pred := pred0
  let mut fa := fa0
  let mut ch := ch0
  let mut work : List (AS × Nat) := [(A0, 0)]
  let mut guardN := 0
  while guardN < 100000 do
    guardN := guardN + 1
    match work with
    | [] => break
    | (c0, r0) :: rest =>
    work := rest
    let mut cur := c0
    let mut run := r0
    while true do
      if FrameKeep.storesTo l E.prg E.mask cur.pc then
        ch := ch.insert cur.pc.toNat (ch.getD cur.pc.toNat 0 + 1)
        break
      if !ok cur then
        fa := fa.push (k0, cur)
        X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
        break
      let pre := FrameKeep.preK S G cur
      let ps := pre.flatMap sp
      if pre.length == 1 && ps.length > 1 then
        work := (ps.map fun p => (p, run)) ++ work
        break
      let dec := ps.any fun A₁ => isRkDec E A₁.pc (LagFrames.opOf E A₁)
      let rs := ps.flatMap fun A₁ => (FrameKeep.kstep S G E ops A₁).map (Option.map (fixP E fb A₁))
      X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
      if dec || rs.any (·.isNone) then
        fa := fa.push (k0, cur)
        X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
      for b in rs.filterMap id do
        if b.k != cur.k then
          T := { T with endN := T.endN + 1 }
          if !invOK inv b then
            T := { T with endF := T.endF.insert cur.pc.toNat (T.endF.getD cur.pc.toNat 0 + 1), endS := if T.endS.size < 20 then T.endS.push b else T.endS }
        else
          for (i, m) in inv do
            if invOK1 i m cur && !invOK1 i m b then
              T := { T with loss := T.loss.insert (i, cur.pc.toNat) (T.loss.getD (i, cur.pc.toNat) 0 + 1) }
              if T.lossS.size < 40 then T := { T with lossS := T.lossS.push (k0, i, cur, b) }
      let good := (rs.filterMap id).filter fun b => b.k == cur.k
      match good with
      | [b] =>
        if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !FrameKeep.storesTo l E.prg E.mask b.pc &&
            (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
          cur := b
          run := run + 1
          continue
        else pure ()
      | _ => pure ()
      for b in good do
        let K := key (SideRange.withB (PrevKeep.normP S G keep b) (SideRange.bndS b 0) (SideRange.bndS b 1))
        if !(pred.contains K) then pred := pred.insert K (k0, cur.pc)
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := SideRange.routeB S G keep key X b
      break
  return { T with P := ⟨X, pred, fa, ch, st0, dr0⟩ }

/-- the search: each pending state of the table, in its pieces, at most `cap` of them -/
partial def searchI (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (ok : AS → Bool)
    (l : List Nat) (keep fb : List Nat) (inv : List (Nat × UInt8)) (W cap : Nat) (P0 : St) : St × Bool := Id.run do
  let mut P := P0
  let mut n := 0
  while true do
    if n ≥ cap then return (P, false)
    n := n + 1
    match P.P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P.P
      P := { P with P := {} }
      P := { P with P := ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩ }
      for B in SideRange.pieces W A do
        P := runI S G E key ops sp ok l keep fb inv P k B
  return (P, true)

/-- the search from the states at the scroll handler's call of the first walk of `AfterKeep`, with the bytes of `inv` set -/
def searchFrom (sy : Syms) (m0 : Machine) (v : UInt8) (ok : Env → AS → Bool) (sp : Env → AS → List AS) (key : FrameKeep.Spot → PipeWrites.Guard → AS → Nat)
    (inv : List (Nat × UInt8)) (extra prot : List Nat) (cap : Nat) : St × Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let S := FrameKeep.spotOf sy m0
  let G := { FrameKeep.guardE sy m0 with prot := prot ++ (FrameKeep.guardE sy m0).prot }
  let E := PipeEntryRule.envOf m0
  let key := key S G
  let bs := inv.map (·.1) ++ extra
  let keep := SideRange.zKeep ++ bs
  let X := (P.stops.toList.map (setInv inv)).foldl (SideRange.routeB S G keep key) {}
  searchI S G E key (aRows E).toArray (sp E) (ok E) (FrameKeep.ctlI sy) keep keep inv SideRange.wLim cap { P := { X } }

/-! ## The walk's table and the checks -/

/-- the search from the states at the scroll handler's call `starts` -/
def searchA (sy : Syms) (m0 : Machine) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := guardA sy m0
  let E := PipeEntryRule.envOf m0
  let key := SideLoop.keyL sy S G
  let X := starts.foldl (SideRange.routeB S G SideRange.zKeep key) {}
  (searchI S G E key (aRows E).toArray (spC sy E) (okA sy m0 E) (FrameKeep.ctlI sy) SideRange.zKeep SideRange.zKeep (invL sy) SideRange.wLim
    1000000000 { P := { X } }).1.P

/-- **The walk's table**, from the states at the scroll handler's call `starts` -/
def aCfg (sy : Syms) (m0 : Machine) (starts : List AS) : SideRange.CfgR :=
  let S := FrameKeep.spotOf sy m0
  let G := guardA sy m0
  let E := PipeEntryRule.envOf m0
  let key := SideLoop.keyL sy S G
  let q := FrameKeep.tableOfKW key (searchA sy m0 starts).X
  { E, ops := (aRows E).toArray, S, G, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, W := SideRange.wLim,
    sp := spC sy E, ok := okA sy m0 E }

/-- what the first walk asks at the scroll handler's call: the walk of this file succeeds from the state with the two bytes set -/
def atA (sy : Syms) (C : SideRange.CfgR) (B : AS) : Bool := walkP C (FrameKeep.ctlI sy) FrameKeep.fuelK (setB sy B)

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler's call, then the walk of this file -/
def cfgPA (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C : SideRange.CfgR) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atA sy C) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check on the ROM** of the walk: as `SideLoop.lCheck`, with the table of this file -/
def aCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C := aCfg sy m0 (P.stops.toList.map (setB sy))
  CtrlKeep.ctrlCheck1 (cfgPA sy m0 v q C1 C) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atA sy C) FrameKeep.fuelK) &&
    tableOKP C (FrameKeep.ctlI sy) FrameKeep.fuelK

/-- the search's failures and its size, for a program (no part of the proof) -/
def aFails (sy : Syms) (m0 : Machine) (v : UInt8) : Nat × List Nat × Nat × Nat :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let R := searchA sy m0 (P.stops.toList.map (setB sy))
  (R.X.fails, R.X.failPcs.toList.map (·.1), R.X.done.size, R.X.multi.size)

/-- **The check on the ROM of the two bytes from the frame's start to the scroll handler's call**: for each, the walk of `CtrlKeep` up to the player's
routine (as `SideTimer.keepCheck`), and the walk of `PlaceKeep` from there to the scroll handler (as `PlaceKeep.placeCheck`) -/
def keepCheckA (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q0 := CtrlKeep.cutTable sy m0 false
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
  [bcpI sy, sdoI sy].all fun b =>
    let C1 := PlaceKeep.pbCfg sy m0 v b cuts
    CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 q0 b false) && CtrlKeep.ctrlCheck1 (PlaceKeep.cfgPb sy m0 v q C1) &&
      C1.t.all (PlaceKeep.walkQP C1 (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK)

/-- **The checks on the ROM of this file**: the walk (`aCheck`) and the walks of the two bytes up to the scroll handler's call (`keepCheckA`) -/
def check (sy : Syms) (m0 : Machine) (v : UInt8) : Bool := aCheck sy m0 v && keepCheckA sy m0 v

theorem check_parts {m0 : Machine} {v : UInt8} (h : check sy m0 v = true) : aCheck sy m0 v = true ∧ keepCheckA sy m0 v = true := by
  simpa only [check, Bool.and_eq_true] using h

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- **The two bytes at the player's routine** are those of the frame's start (the proof of `SideTimer.keep_at`) -/
theorem keep_cutA {v : UInt8} (hc : keepCheckA sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ [bcpI sy, sdoI sy], (trace m i k).ram.get! x = m.ram.get! x := by
  intro b hb
  simp only [keepCheckA, Bool.and_eq_true, List.all_eq_true] at hc
  have hb1 := ((hc.2 b hb).1).1
  obtain ⟨B, hB, hs⟩ := CtrlKeep.at_cut (C := CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) b false) hb1 rfl rfl rfl
    (CtrlKeep.cfg_start _ _ false h0) hcl hk hf hfirst
  simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB
  have h1 := hs.rkv hB.1.1.1.1.1.1
  rw [if_neg (by simp [hB.1.1.1.1.1.2])] at h1
  exact h1

/-- **The two bytes at the scroll handler** are those at the player's routine (the proof of `PlaceKeep.keep_place`) -/
theorem keep_subsA (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : keepCheckA sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    {k : Nat} (hk : n₀ ≤ k) (hpc : (trace m i k).pc = sy.PlayerSubs) (hb : ∀ j, n₀ < j → j < k → (trace m i j).pc ≠ sy.PlayerSubs) :
    ∀ x ∈ [bcpI sy, sdoI sy], (trace m i k).ram.get! x = (trace m i n₀).ram.get! x := by
  simp only [keepCheckA, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hp
  obtain ⟨⟨hne1, _⟩, hbq⟩ := hp
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  intro x hxI
  obtain ⟨⟨_, h1⟩, ht⟩ := hbq x hxI
  generalize CtrlKeep.cutTable sy m0 true = q at h1 ht
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at h1 ht
  rcases CtrlKeep.cut_or_end2 (C := PlaceKeep.cfgPb sy m0 v q (PlaceKeep.pbCfg sy m0 v x cuts)) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
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
    have hw : PlaceKeep.walkQP (PlaceKeep.pbCfg sy m0 v x cuts) (FrameKeep.ctlI sy) sy.PlayerSubs EdgeStep.atRk FrameKeep.fuelK
        (AfterKeep.rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) = true := hB2
    obtain ⟨k₁, hk1, hq1, _, _, hbt, B₁, hat, hs₁⟩ := PlaceKeep.qP_run (C := PlaceKeep.pbCfg sy m0 v x cuts) ht rfl rfl hw hsR a2 a5 hcl hx'
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

/-- **On a frame with `FactsAt` and `CastleRow` after the scroll handler, a store that may reach the side collision's timer does not write it**, from the scroll
handler's call to the frame's end: with the hypotheses of `SideLoop.near_side`. `hr` and `hk` are the checks on the ROM. -/
theorem near_sideA {v : UInt8} (hr : aCheck sy m0 v = true) (hk : keepCheckA sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hc : CtrlKeep.ctrlCheck sy m0 = true) (hv : CtrlKeep.AreaOK sy v m)
    (hF : FactsAt sy m i) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (hrow : ∀ k n, n₀ ≤ k → k ≤ n → (trace m i k).pc = sy.PlayerSubs → (trace m i n).frame = m.frame → CastleRow sy (trace m i n)) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
      ∀ j, kq ≤ j → (trace m i j).frame = m.frame → PushTimer.NearW sy m0 (trace m i j) → PushTimer.SideW sy m0 (trace m i j) := by
  simp only [aCheck, Bool.and_eq_true] at hr
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hr
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  rcases CtrlKeep.cut_or_end2 (C := cfgPA sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (aCfg sy m0 (P.stops.toList.map (setB sy))))
      hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atA sy (aCfg sy m0 (P.stops.toList.map (setB sy)))) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hclF hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, fun j hj hfj hn => ?_⟩
    have e1 := keep_cutA hk h0 hclK a1 a2 a4
    have e2 := keep_subsA hc hk h0 hclF hx hv a1 a2 a4 (Nat.le_of_lt hkq) hqq hbq
    have hI : InvB sy (trace m i kq) := by
      unfold InvB
      rw [e2 (bcpI sy) (by simp), e2 (sdoI sy) (by simp), e1 (bcpI sy) (by simp), e1 (sdoI sy) (by simp)]
      exact hF.1
    have hw1 : walkP (aCfg sy m0 (P.stops.toList.map (setB sy))) (FrameKeep.ctlI sy) FrameKeep.fuelK (setB sy Bq) = true := hatq
    obtain ⟨B', hsB, hok⟩ := okP_all (C := aCfg sy m0 (P.stops.toList.map (setB sy))) cov_spC hp3 rfl rfl hw1 (sim_setB hsq hI) hfq hdq
      (fun j _ hfj => cleanK_A (hcl j) (hF.2 j hfj)) (fun j' hj' hfj' => hrow kq j' (Nat.le_of_lt hkq) hj' hqq hfj') hx' j hj hfj
    exact okA_spec hsB hok hn
  · exact absurd harr (hno n₀ hf0)

end Frames

end Smbrta.SideAcross
