import Theorems.SideRange

/-!
# Above ground: the stores that may reach the side collision's timer, in the area parser's loops

Round 34 asked the field `OnFrames.sideW` (a store through an index or a pointer does not write the side collision's timer) at every store that may reach the
timer (`PushTimer.NearW`) in the area parser's code and in the code of the head's collision with a block (`SideRange.Resid`), and proved it at the other such
stores (`SideRange.near_side`). Here the same walk, with a finer table and one more split, proves it at all of them but the four of `Resid` (`near_side`);
the field is asked only there (the program has 4 such stores; asked there too, the walk fails at 3 of them, and the fourth comes after one of those on
its paths):
* a store through a pointer (`STA (zp),Y`) in the area parser's code or in the code of the head's collision with a block. The walk does not know the
  pointer's high byte there: in the area parser it is read from a table of the program at an index from the block buffer's column (`BlockBufferColumnPos`),
  and in the head's collision the walk knows only some of its bits, and the stores to the zero page at the index `SprDataOffset_Ctrl` (the block's state,
  and the block's position in `InitBlock_XY_Pos`) may write it, as far as the walk knows. Both are bytes that live across frames;
* the store of the castle's loop of rows (from `CRendLoop` to `ChkCFloor`). The loop stores rows from a row read from the area's data up to a fixed row; a start
  past that row would run the loop over the whole page.

The walk (`SideRange.walkR`, with the configuration `lCfg`) differs from round 34's in two things, both in the code of `SideRange.residB` only:
* the table's key (`keyL`) also holds what the state knows of `X`, `Y` and the zero page byte 0, so that the states of a loop with a counter are not joined;
* before `LDX abs,Y` the walk splits `Y` into all its values (`spL`), so that `X` is known after the load.
Neither is a part of what the walk proves: a state is covered by a state of the table only when its known bits and its bounds say so (`SideRange.coverR`).

The search that makes the table is no part of the proof (`searchL`); the check is `lCheck`. There is no game data in this file.
Page: `1-1/e-2-10-3-25-SideLoop.md`.
-/

namespace Smbrta.SideLoop

open TaintRun
open PipeTransitionAll (go)
open AfterKeep (walkQ1)

variable {sy : Syms}

/-! ## The places where the field stays asked -/

/-- **The places where the field `OnFrames.sideW` stays asked**, for a program: a store through a pointer (`STA (zp),Y`) in the area parser's code or in
the code of the head's collision with a block (`SideRange.residB`), and the castle's loop of rows (from `CRendLoop` to `ChkCFloor`) -/
def residB (sy : Syms) (pc : UInt16) (op : UInt8) : Bool :=
  (SideRange.residB sy pc && op == 0x91) || (decide (sy.CRendLoop ≤ pc) && decide (pc < sy.ChkCFloor))

/-- **The places where the field `OnFrames.sideW` stays asked** (round 35) -/
def Resid (sy : Syms) (m : Machine) : Prop := residB sy m.pc (PipeWrites.opAt m) = true

/-- the new places are some of round 34's -/
theorem resid_old (hl : sy.AreaParserCore ≤ sy.CRendLoop) (hh : sy.ChkCFloor ≤ sy.GetBlockBufferAddr) {m : Machine} (h : Resid sy m) : SideRange.Resid sy m := by
  unfold Resid residB at h
  unfold SideRange.Resid SideRange.residB
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · unfold SideRange.residB at h1
    simpa using h1
  · left
    have e1 := UInt16.le_iff_toNat_le.1 hl
    have e2 := UInt16.le_iff_toNat_le.1 hh
    have e3 := UInt16.le_iff_toNat_le.1 h1
    have e4 := UInt16.lt_iff_toNat_lt.1 h2
    exact ⟨UInt16.le_iff_toNat_le.2 (by omega), UInt16.lt_iff_toNat_lt.2 (by omega)⟩

/-! ## The table's key and the split -/

/-- what a state knows of a byte, as a number -/
def numB (b : AB) : Nat := b.k.toNat * 256 + (b.v &&& b.k).toNat

/-- **The table's key**: `PrevKeep.keyP`, and in the code of `SideRange.residB` also what the state knows of `X`, `Y` and the zero page byte 0. No part of
the proof. -/
def keyL (sy : Syms) (S : FrameKeep.Spot) (G : PipeWrites.Guard) (A : AS) : Nat :=
  let k0 := PrevKeep.keyP S G [] A
  if SideRange.residB sy A.pc then ((k0 * 65536 + numB A.x) * 65536 + numB A.y) * 65536 + numB (A.getK 0) else k0

/-- **The split**: in the code of `SideRange.residB`, before `LDX abs,Y`, `Y` into all its values; elsewhere `SideRange`'s split -/
def spL (sy : Syms) (E : Env) (A : AS) : List AS :=
  if SideRange.residB sy A.pc && SideRange.opA E A == 0xBE then SideRange.splitR E 8 [] [0xBE] A
  else SideRange.splitR E 4 SideRange.xOps SideRange.yOps A

theorem cov_spL (sy : Syms) {E : Env} {F : Nat × UInt8} : Cov E F (spL sy E) := by
  intro A m hs
  unfold spL
  split
  · exact SideRange.cov_splitR 8 [] [0xBE] A m hs
  · exact SideRange.cov_splitR 4 SideRange.xOps SideRange.yOps A m hs

/-! ## The condition at a store -/

/-- **What the walk asks at a state**: `SideRange.okR` with the places of `residB` -/
def okL (sy : Syms) (m0 : Machine) (E : Env) (A : AS) : Bool :=
  !PushTimer.wOps.contains (SideRange.opA E A) ||
    (!A.nmi && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
      (!SideRange.nearA (ScrollRule.places sy m0).sideB E A || residB sy A.pc (SideRange.opA E A) || SideRange.missK (ScrollRule.places sy m0).sideB E A))

/-- **`okL` gives `SideW`** at a store that may reach the timer and is not one of `Resid` (the proof of `SideRange.okR_spec`) -/
theorem okL_spec {m0 : Machine} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : okL sy m0 E A = true)
    (hn : PushTimer.NearW sy m0 m) (hr : ¬ Resid sy m) : PushTimer.SideW sy m0 m := by
  intro t ht hlt heq
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = SideRange.opnd E A := by
    unfold PositionKeep.operandAt SideRange.opnd; rw [hs.prg, hs.mask, hs.pc]
  have hw : PushTimer.wOps.contains (SideRange.opA E A) = true := by rw [← hop]; exact List.contains_iff_mem.2 (PushTimer.wTarget_ops ht)
  unfold okL at h
  rw [hw] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨_, _⟩, hp1⟩, hp2⟩, hc⟩ := h
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hp2' : 0x8000 ≤ m.pc + 1 + 1 := by rw [hs.pc]; exact hp2
  have hnA : SideRange.nearA (ScrollRule.places sy m0).sideB E A = true := by
    have e : PushTimer.nearWB sy m0 m = true := hn
    unfold PushTimer.nearWB at e
    unfold SideRange.nearA
    rw [← hop, ← hoa]
    exact e
  have hrA : residB sy A.pc (SideRange.opA E A) = false := by
    cases e : residB sy A.pc (SideRange.opA E A) with
    | false => rfl
    | true => exact absurd (show residB sy m.pc (PipeWrites.opAt m) = true by rw [hs.pc, hop]; exact e) hr
  rw [hnA, hrA] at hc
  have hmk : SideRange.missK (ScrollRule.places sy m0).sideB E A = true := by
    rcases hc with (h1 | h1) | h1
    · cases h1
    · cases h1
    · exact h1
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
          unfold SideRange.missP at hmk
          have hl0 : (SideRange.zop E A).toNat < 2048 := by have := (SideRange.zop E A).toNat_lt; omega
          have hh0 : (SideRange.zop E A + 1).toNat < 2048 := by have := (SideRange.zop E A + 1).toNat_lt; omega
          have hlo := hs.ram _ hl0
          have hhi := hs.ram _ hh0
          have hm1 := List.all_eq_true.1 hmk _ (SideRange.mem_valsAll hhi)
          have a1 := minv_le hlo
          have a2 := le_maxv hlo
          have a3 := minv_le hs.y
          have a4 := le_maxv hs.y
          have hm2 := List.all_eq_true.1 hm1 ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
              ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) (List.mem_range.2 (by omega))
          rw [show (A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat + ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
              ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) = (m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat by omega,
            SideRange.w16, e] at hm2
          exact SideRange.miss_of (by simpa using hm2) hlt heq
        · rw [if_neg c4] at hmk
          cases hmk

/-! ## The search and the table: no part of the proof -/

/-- the search from the states at the scroll handler's call `starts` -/
def searchL (sy : Syms) (m0 : Machine) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyL sy S G
  let X := starts.foldl (SideRange.routeB S G SideRange.zKeep key) {}
  SideRange.searchR S G E key (aRows E).toArray (spL sy E) (okL sy m0 E) (FrameKeep.ctlI sy) SideRange.zKeep SideRange.wLim { X }

/-- **The walk's table**, from the states at the scroll handler's call `starts` -/
def lCfg (sy : Syms) (m0 : Machine) (starts : List AS) : SideRange.CfgR :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyL sy S G
  let q := FrameKeep.tableOfKW key (searchL sy m0 starts).X
  { E, ops := (aRows E).toArray, S, G, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, W := SideRange.wLim,
    sp := spL sy E, ok := okL sy m0 E }

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler's call, then the walk of this file -/
def cfgPL (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 : FrameKeep.CfgK) (C : SideRange.CfgR) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (SideRange.atR sy C) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check on the ROM**: as `SideRange.rCheck`, with the table of this file -/
def lCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C := lCfg sy m0 P.stops.toList
  CtrlKeep.ctrlCheck1 (cfgPL sy m0 v q C1 C) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (SideRange.atR sy C) FrameKeep.fuelK) &&
    SideRange.tableOK C (FrameKeep.ctlI sy) FrameKeep.fuelK

/-- the search's failures and its size, for a program (no part of the proof) -/
def lFails (sy : Syms) (m0 : Machine) (v : UInt8) : Nat × List Nat × Nat × Nat :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let R := searchL sy m0 P.stops.toList
  (R.X.fails, R.X.failPcs.toList.map (·.1), R.X.done.size, R.X.multi.size)

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- **A store that may reach the side collision's timer and is not one of `Resid` does not write it**, from the scroll handler's call to the frame's end: with the
hypotheses of `SideRange.near_side`. `hr` is the check on the ROM. -/
theorem near_side {v : UInt8} (hr : lCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hc : CtrlKeep.ctrlCheck sy m0 = true) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
      ∀ j, kq ≤ j → (trace m i j).frame = m.frame → PushTimer.NearW sy m0 (trace m i j) → ¬ Resid sy (trace m i j) →
        PushTimer.SideW sy m0 (trace m i j) := by
  simp only [lCheck, Bool.and_eq_true] at hr
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hr
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  rcases CtrlKeep.cut_or_end2 (C := cfgPL sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (lCfg sy m0 P.stops.toList))
      hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (SideRange.atR sy (lCfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hclF hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, fun j hj hfj hn hres => ?_⟩
    have hw1 : SideRange.walkR (lCfg sy m0 P.stops.toList) (FrameKeep.ctlI sy) FrameKeep.fuelK Bq = true := hatq
    obtain ⟨B', hsB, hok⟩ := SideRange.okR_all (C := lCfg sy m0 P.stops.toList) (cov_spL sy) hp3 rfl rfl hw1 hsq hfq hdq
      (fun j _ _ => hcl j) hx' j hj hfj
    exact okL_spec hsB hok hn hres
  · exact absurd harr (hno n₀ hf0)

end Frames

end Smbrta.SideLoop
