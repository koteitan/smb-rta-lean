import Theorems.StepWrites
import Theorems.FrameKeep

/-!
# One step of the CPU keeps the program

No instruction of the CPU, no interrupt and no tick of the clock changes the program (`prg`) or its mask (`prgMask`) of the machine. `KP f` says this of an action `f`.
It holds for each piece of the CPU (`rd`, `wr`, `tick`, the modes, the instructions), so for each of the 256 entries of `opTable` (the rows of `PipeTransitionAll`,
as `StepWrites` does for RAM), and so for `step` (`step_prg`). Along the instructions of a frame the program and the mask stay those of the frame's start (`trace_prg`),
and from frame to frame on a run of real frames (`frame_prg`).

There is no game data in this file. Page: `1-1/a-5-10-UpClean.md`.
-/

namespace Smbrta.StepPrg

open PipeTransitionAll (go go_bind incPC decS incS startNmi setAOnly bitFlags plpFlags laxRegs setXOnly setYOnly txs jam tick_eq tick1 tick2 tick3 tick4
  ioMark romRead rdRamF trF wrRamF oamDma_eq nmi_eq row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 rowA rowB rowC rowD rowE rowF allRows opTable_eq)

/-! ## Actions that keep the program -/

/-- `f` keeps the program and its mask -/
def KP {α : Type} (f : M α) : Prop := ∀ m, (go f m).2.prg = m.prg ∧ (go f m).2.prgMask = m.prgMask

theorem KP.bind {α β : Type} {f : M α} {g : α → M β} (hf : KP f) (hg : ∀ a, KP (g a)) : KP (f >>= g) := by
  intro m
  rw [go_bind]
  obtain ⟨a1, a2⟩ := hg (go f m).1 (go f m).2
  obtain ⟨b1, b2⟩ := hf m
  exact ⟨a1.trans b1, a2.trans b2⟩

theorem KP.get' {α : Type} {k : Machine → M α} (h : ∀ x, KP (k x)) : KP (get >>= k) := fun m => h m m

theorem KP.pure {α : Type} (a : α) : KP (Pure.pure a : M α) := fun _ => ⟨rfl, rfl⟩

theorem KP.congr {α : Type} {f g : M α} (h : ∀ m, go f m = go g m) (hg : KP g) : KP f := fun m => by
  rw [h]
  exact hg m

/-- an action that changes only fields other than the program and the mask -/
macro "kp_rfl" : term => `(fun _ => ⟨rfl, rfl⟩)

theorem kp_setZN (v : UInt8) : KP (setZN v) := kp_rfl
theorem kp_setFlag (a : UInt8) (b : Bool) : KP (setFlag a b) := kp_rfl
theorem kp_adc (v : UInt8) : KP (adc v) := kp_rfl
theorem kp_setPC (a : UInt16) : KP (setPC a) := kp_rfl
theorem kp_incPC : KP incPC := kp_rfl
theorem kp_decS : KP decS := kp_rfl
theorem kp_incS : KP incS := kp_rfl
theorem kp_startNmi : KP startNmi := kp_rfl
theorem kp_setAOnly (v : UInt8) : KP (setAOnly v) := kp_rfl
theorem kp_bitFlags (v : UInt8) : KP (bitFlags v) := kp_rfl
theorem kp_plpFlags (v : UInt8) : KP (plpFlags v) := kp_rfl
theorem kp_laxRegs (v : UInt8) : KP (laxRegs v) := kp_rfl
theorem kp_setXOnly (v : UInt8) : KP (setXOnly v) := kp_rfl
theorem kp_setYOnly (v : UInt8) : KP (setYOnly v) := kp_rfl
theorem kp_txs : KP txs := kp_rfl
theorem kp_jam : KP jam := kp_rfl
theorem kp_romRead (addr : UInt16) : KP (romRead addr) := kp_rfl

theorem tick1_prg (b : Bool) (m : Machine) : (tick1 b m).prg = m.prg ∧ (tick1 b m).prgMask = m.prgMask := by
  cases b <;> exact ⟨rfl, rfl⟩
theorem tick2_prg (b : Bool) (m : Machine) : (tick2 b m).prg = m.prg ∧ (tick2 b m).prgMask = m.prgMask := by
  cases b <;> exact ⟨rfl, rfl⟩
theorem tick3_prg (b : Bool) (m : Machine) : (tick3 b m).prg = m.prg ∧ (tick3 b m).prgMask = m.prgMask := by
  cases b <;> exact ⟨rfl, rfl⟩
theorem tick4_prg (new len : Nat) (m : Machine) : (tick4 new len m).prg = m.prg ∧ (tick4 new len m).prgMask = m.prgMask := by
  unfold tick4
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem kp_tick (c : Nat) : KP (tick c) := by
  intro m
  rw [tick_eq]
  simp only
  refine ⟨(tick4_prg _ _ _).1.trans ((tick3_prg _ _).1.trans ((tick2_prg _ _).1.trans (tick1_prg _ _).1)),
    (tick4_prg _ _ _).2.trans ((tick3_prg _ _).2.trans ((tick2_prg _ _).2.trans (tick1_prg _ _).2))⟩

theorem kp_ppuRead (r : UInt16) : KP (ppuRead r) := by
  intro m
  unfold ppuRead go
  split <;> exact ⟨rfl, rfl⟩

theorem kp_padRead : KP padRead := by
  intro m
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases padStrobe <;> exact ⟨rfl, rfl⟩

theorem kp_padWrite (v : UInt8) : KP (padWrite v) := by
  intro m
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    unfold padWrite go
    by_cases h : (v &&& 1 == 1) = true
    · simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h, if_true]
      exact ⟨rfl, rfl⟩
    · cases padStrobe <;> simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h] <;> exact ⟨rfl, rfl⟩

theorem kp_ppuWrite (r : UInt16) (v : UInt8) : KP (ppuWrite r v) := by
  unfold ppuWrite
  by_cases h0 : (r == 0) = true
  · simp only [h0, if_true]
    exact kp_rfl
  · by_cases h1 : (r == 1) = true
    · simp only [h0, h1, if_true]
      exact kp_rfl
    · simp only [h0, h1]
      exact kp_rfl

theorem kp_ioMark : KP ioMark := by
  intro m
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases trk <;> exact ⟨rfl, rfl⟩

theorem kp_oamDma : KP oamDma := fun m => by
  rw [oamDma_eq]
  exact kp_tick _ m

theorem trF_prg (i : Nat) (m : Machine) : (trF i m).prg = m.prg ∧ (trF i m).prgMask = m.prgMask := by
  unfold trF
  split <;> exact ⟨rfl, rfl⟩

theorem kp_rd (addr : UInt16) : KP (rd addr) := by
  by_cases h1 : addr < 0x2000
  · intro m
    have e : go (rd addr) m = rdRamF (addr &&& 0x7FF).toNat m := by
      unfold rd go
      rw [if_pos h1]
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases trk <;> rfl
    rw [e]
    unfold rdRamF
    split
    · exact trF_prg _ _
    · exact ⟨rfl, rfl⟩
  · by_cases h2 : addr ≥ 0x8000
    · refine KP.congr (g := romRead addr) (fun m => ?_) (kp_romRead addr)
      unfold rd go
      rw [if_neg h1, if_pos h2]
      rfl
    · by_cases h3 : addr < 0x4000
      · refine KP.congr (g := ioMark >>= fun _ => ppuRead (addr &&& 7)) (fun m => ?_)
          (KP.bind kp_ioMark fun _ => kp_ppuRead _)
        unfold rd go
        rw [if_neg h1, if_neg h2, if_pos h3]
        cases m with
        | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
          cases trk <;> rfl
      · by_cases h4 : (addr == 0x4016) = true
        · refine KP.congr (g := ioMark >>= fun _ => padRead) (fun m => ?_)
            (KP.bind kp_ioMark fun _ => kp_padRead)
          unfold rd go
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          cases m with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases trk <;> rfl
        · by_cases h5 : (addr == 0x4017) = true
          · refine KP.congr (g := Pure.pure 0x40) (fun m => ?_) (KP.pure _)
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
          · refine KP.congr (g := Pure.pure 0) (fun m => ?_) (KP.pure _)
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

theorem wrRamF_prg (i : Nat) (v : UInt8) (m : Machine) : (wrRamF i v m).prg = m.prg ∧ (wrRamF i v m).prgMask = m.prgMask := by
  unfold wrRamF
  split <;> exact ⟨rfl, rfl⟩

theorem kp_wr (addr : UInt16) (v : UInt8) : KP (wr addr v) := by
  by_cases h1 : addr < 0x2000
  · intro m
    have e : go (wr addr v) m = ((), wrRamF (addr &&& 0x7FF).toNat v m) := by
      unfold wr go
      rw [if_pos h1]
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases trk <;> rfl
    rw [e]
    exact wrRamF_prg _ _ _
  · by_cases h2 : addr < 0x4000
    · refine KP.congr (g := ppuWrite (addr &&& 7) v) (fun m => ?_) (kp_ppuWrite _ _)
      unfold wr go
      rw [if_neg h1, if_pos h2]
    · by_cases h3 : (addr == 0x4014) = true
      · refine KP.congr (g := oamDma) (fun m => ?_) kp_oamDma
        unfold wr go
        rw [if_neg h1, if_neg h2, if_pos h3]
      · by_cases h4 : (addr == 0x4016) = true
        · refine KP.congr (g := padWrite v) (fun m => ?_) (kp_padWrite v)
          unfold wr go
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
        · refine KP.congr (g := Pure.pure ()) (fun m => ?_) (KP.pure _)
          unfold wr go
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

theorem kp_fetch : KP fetch :=
  KP.congr (g := incPC >>= rd) (fun _ => rfl) (KP.bind kp_incPC kp_rd)
theorem kp_fetch16 : KP fetch16 := KP.bind kp_fetch fun _ => KP.bind kp_fetch fun _ => KP.pure _
theorem kp_rd16zp (z : UInt8) : KP (rd16zp z) := KP.bind (kp_rd _) fun _ => KP.bind (kp_rd _) fun _ => KP.pure _
theorem kp_pagePenalty (b e : UInt16) : KP (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact kp_tick 1
  · exact KP.pure _

theorem kp_mImm : KP mImm := kp_incPC
theorem kp_mZp : KP mZp := KP.bind kp_fetch fun _ => KP.pure _
theorem kp_mZpx : KP mZpx := KP.bind kp_fetch fun _ => KP.get' fun _ => KP.pure _
theorem kp_mZpy : KP mZpy := KP.bind kp_fetch fun _ => KP.get' fun _ => KP.pure _
theorem kp_mAbs : KP mAbs := kp_fetch16
theorem kp_mAbx : KP mAbx := KP.bind kp_fetch16 fun _ => KP.get' fun _ => KP.pure _
theorem kp_mAby : KP mAby := KP.bind kp_fetch16 fun _ => KP.get' fun _ => KP.pure _
theorem kp_mAbxR : KP mAbxR := KP.bind kp_fetch16 fun _ => KP.get' fun _ => KP.bind (kp_pagePenalty _ _) fun _ => KP.pure _
theorem kp_mAbyR : KP mAbyR := KP.bind kp_fetch16 fun _ => KP.get' fun _ => KP.bind (kp_pagePenalty _ _) fun _ => KP.pure _
theorem kp_mIzx : KP mIzx := KP.bind kp_fetch fun _ => KP.get' fun _ => kp_rd16zp _
theorem kp_mIzy : KP mIzy := KP.bind kp_fetch fun _ => KP.bind (kp_rd16zp _) fun _ => KP.get' fun _ => KP.pure _
theorem kp_mIzyR : KP mIzyR :=
  KP.bind kp_fetch fun _ => KP.bind (kp_rd16zp _) fun _ => KP.get' fun _ => KP.bind (kp_pagePenalty _ _) fun _ => KP.pure _

theorem kp_setA (v : UInt8) : KP (setA v) := KP.bind (kp_setAOnly v) fun _ => kp_setZN v
theorem kp_setX (v : UInt8) : KP (setX v) := KP.bind (kp_setXOnly v) fun _ => kp_setZN v
theorem kp_setY (v : UInt8) : KP (setY v) := KP.bind (kp_setYOnly v) fun _ => kp_setZN v
theorem kp_push (v : UInt8) : KP (push v) := fun m => by
  have e : go (push v) m = go (wr (0x100 ||| m.s.toUInt16) v) { m with s := m.s - 1 } := rfl
  rw [e]
  exact kp_wr _ _ _
theorem kp_pull : KP pull := fun m => by
  have e : go pull m = go (rd (0x100 ||| (m.s + 1).toUInt16)) { m with s := m.s + 1 } := rfl
  rw [e]
  exact kp_rd _ _
theorem kp_oraV (v : UInt8) : KP (oraV v) := KP.get' fun _ => kp_setA _
theorem kp_andV (v : UInt8) : KP (andV v) := KP.get' fun _ => kp_setA _
theorem kp_eorV (v : UInt8) : KP (eorV v) := KP.get' fun _ => kp_setA _
theorem kp_cmpV (r v : UInt8) : KP (cmpV r v) := KP.bind (kp_setZN _) fun _ => kp_setFlag _ _
theorem kp_aslV (v : UInt8) : KP (aslV v) := KP.bind (kp_setFlag _ _) fun _ => KP.bind (kp_setZN _) fun _ => KP.pure _
theorem kp_lsrV (v : UInt8) : KP (lsrV v) := KP.bind (kp_setFlag _ _) fun _ => KP.bind (kp_setZN _) fun _ => KP.pure _
theorem kp_rolV (v : UInt8) : KP (rolV v) :=
  KP.get' fun _ => KP.bind (kp_setFlag _ _) fun _ => KP.bind (kp_setZN _) fun _ => KP.pure _
theorem kp_rorV (v : UInt8) : KP (rorV v) :=
  KP.get' fun _ => KP.bind (kp_setFlag _ _) fun _ => KP.bind (kp_setZN _) fun _ => KP.pure _
theorem kp_incV (v : UInt8) : KP (incV v) := KP.bind (kp_setZN _) fun _ => KP.pure _
theorem kp_decV (v : UInt8) : KP (decV v) := KP.bind (kp_setZN _) fun _ => KP.pure _

/-! ## The instructions -/

section
variable {md : Mode}

theorem kp_opLDA (h : KP md) : KP (opLDA md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_setA _
theorem kp_opLDX (h : KP md) : KP (opLDX md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_setX _
theorem kp_opLDY (h : KP md) : KP (opLDY md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_setY _
theorem kp_opLAX (h : KP md) : KP (opLAX md) :=
  KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.bind (kp_laxRegs _) fun _ => kp_setZN _
theorem kp_opADC (h : KP md) : KP (opADC md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_adc _
theorem kp_opSBC (h : KP md) : KP (opSBC md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_adc _
theorem kp_opORA (h : KP md) : KP (opORA md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_oraV _
theorem kp_opAND (h : KP md) : KP (opAND md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_andV _
theorem kp_opEOR (h : KP md) : KP (opEOR md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_eorV _
theorem kp_opCMP (h : KP md) : KP (opCMP md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.get' fun _ => kp_cmpV _ _
theorem kp_opCPX (h : KP md) : KP (opCPX md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.get' fun _ => kp_cmpV _ _
theorem kp_opCPY (h : KP md) : KP (opCPY md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.get' fun _ => kp_cmpV _ _
theorem kp_opBIT (h : KP md) : KP (opBIT md) := KP.bind h fun _ => KP.bind (kp_rd _) fun _ => kp_bitFlags _
theorem kp_opNOPm (h : KP md) : KP (opNOPm md) := KP.bind h fun _ => KP.pure _

theorem kp_store {g : Machine → UInt8} (h : KP md) : KP (md >>= fun ad => get >>= fun x => wr ad (g x)) :=
  KP.bind h fun _ => KP.get' fun _ => kp_wr _ _
theorem kp_opSTA (h : KP md) : KP (opSTA md) := kp_store h
theorem kp_opSTX (h : KP md) : KP (opSTX md) := kp_store h
theorem kp_opSTY (h : KP md) : KP (opSTY md) := kp_store h
theorem kp_opSAX (h : KP md) : KP (opSAX md) := kp_store h

theorem kp_rmw {f : UInt8 → M UInt8} (hf : ∀ v, KP (f v)) (h : KP md) : KP (rmw f md) :=
  KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.bind (hf _) fun _ => kp_wr _ _
theorem kp_rmw2 {f : UInt8 → M UInt8} {g : UInt8 → M Unit} (hf : ∀ v, KP (f v)) (hg : ∀ v, KP (g v)) (h : KP md) : KP (rmw2 f g md) :=
  KP.bind h fun _ => KP.bind (kp_rd _) fun _ => KP.bind (hf _) fun _ => KP.bind (kp_wr _ _) fun _ => hg _

theorem kp_opASL (h : KP md) : KP (opASL md) := kp_rmw kp_aslV h
theorem kp_opLSR (h : KP md) : KP (opLSR md) := kp_rmw kp_lsrV h
theorem kp_opROL (h : KP md) : KP (opROL md) := kp_rmw kp_rolV h
theorem kp_opROR (h : KP md) : KP (opROR md) := kp_rmw kp_rorV h
theorem kp_opINC (h : KP md) : KP (opINC md) := kp_rmw kp_incV h
theorem kp_opDEC (h : KP md) : KP (opDEC md) := kp_rmw kp_decV h
theorem kp_opSLO (h : KP md) : KP (opSLO md) := kp_rmw2 kp_aslV kp_oraV h
theorem kp_opRLA (h : KP md) : KP (opRLA md) := kp_rmw2 kp_rolV kp_andV h
theorem kp_opSRE (h : KP md) : KP (opSRE md) := kp_rmw2 kp_lsrV kp_eorV h
theorem kp_opRRA (h : KP md) : KP (opRRA md) := kp_rmw2 kp_rorV kp_adc h
theorem kp_opDCP (h : KP md) : KP (opDCP md) := kp_rmw2 (fun _ => KP.pure _) (fun _ => KP.get' fun _ => kp_cmpV _ _) h
theorem kp_opISB (h : KP md) : KP (opISB md) := kp_rmw2 (fun _ => KP.pure _) (fun _ => kp_adc _) h
end

theorem kp_accOp {f : UInt8 → M UInt8} (hf : ∀ v, KP (f v)) : KP (accOp f) :=
  KP.get' fun _ => KP.bind (hf _) fun _ => kp_setAOnly _

theorem kp_opNOP : KP opNOP := KP.pure _
theorem kp_opJAM : KP opJAM := kp_jam

theorem kp_branch (cond : Machine → Bool) : KP (branch cond) := by
  refine KP.bind kp_fetch fun off => KP.get' fun m => ?_
  split
  · exact KP.bind (kp_setPC _) fun _ => kp_tick _
  · exact KP.pure _

theorem kp_opBPL : KP opBPL := kp_branch _
theorem kp_opBMI : KP opBMI := kp_branch _
theorem kp_opBVC : KP opBVC := kp_branch _
theorem kp_opBVS : KP opBVS := kp_branch _
theorem kp_opBCC : KP opBCC := kp_branch _
theorem kp_opBCS : KP opBCS := kp_branch _
theorem kp_opBNE : KP opBNE := kp_branch _
theorem kp_opBEQ : KP opBEQ := kp_branch _

theorem kp_opCLC : KP opCLC := kp_setFlag _ _
theorem kp_opSEC : KP opSEC := kp_setFlag _ _
theorem kp_opCLI : KP opCLI := kp_setFlag _ _
theorem kp_opSEI : KP opSEI := kp_setFlag _ _
theorem kp_opCLV : KP opCLV := kp_setFlag _ _
theorem kp_opCLD : KP opCLD := kp_setFlag _ _
theorem kp_opSED : KP opSED := kp_setFlag _ _

theorem kp_opTAX : KP opTAX := KP.get' fun _ => kp_setX _
theorem kp_opTAY : KP opTAY := KP.get' fun _ => kp_setY _
theorem kp_opTXA : KP opTXA := KP.get' fun _ => kp_setA _
theorem kp_opTYA : KP opTYA := KP.get' fun _ => kp_setA _
theorem kp_opTSX : KP opTSX := KP.get' fun _ => kp_setX _
theorem kp_opTXS : KP opTXS := kp_txs
theorem kp_opINX : KP opINX := KP.get' fun _ => kp_setX _
theorem kp_opINY : KP opINY := KP.get' fun _ => kp_setY _
theorem kp_opDEX : KP opDEX := KP.get' fun _ => kp_setX _
theorem kp_opDEY : KP opDEY := KP.get' fun _ => kp_setY _
theorem kp_opPLA : KP opPLA := KP.bind kp_pull fun _ => kp_setA _
theorem kp_opPLP : KP opPLP := KP.bind kp_pull fun _ => kp_plpFlags _
theorem kp_opPHA : KP opPHA := KP.get' fun _ => kp_push _
theorem kp_opPHP : KP opPHP := KP.get' fun _ => kp_push _
theorem kp_opJMP : KP opJMP := KP.bind kp_fetch16 fun _ => kp_setPC _
theorem kp_opJMPi : KP opJMPi := KP.bind kp_fetch16 fun _ => KP.bind (kp_rd _) fun _ => KP.bind (kp_rd _) fun _ => kp_setPC _
theorem kp_opRTS : KP opRTS := KP.bind kp_pull fun _ => KP.bind kp_pull fun _ => kp_setPC _
theorem kp_opRTI : KP opRTI := KP.bind kp_opPLP fun _ => KP.bind kp_pull fun _ => KP.bind kp_pull fun _ => kp_setPC _
theorem kp_opJSR : KP opJSR :=
  KP.bind kp_fetch16 fun _ => KP.get' fun _ => KP.bind (kp_push _) fun _ => KP.bind (kp_push _) fun _ => kp_setPC _
theorem kp_interrupt (pc : UInt16) (p : UInt8) (v : UInt16) : KP (interrupt pc p v) :=
  KP.bind (kp_push _) fun _ => KP.bind (kp_push _) fun _ => KP.bind (kp_push _) fun _ =>
    KP.bind (kp_setFlag _ _) fun _ => KP.bind (kp_rd _) fun _ => KP.bind (kp_rd _) fun _ => kp_setPC _
theorem kp_opBRK : KP opBRK := KP.get' fun _ => kp_interrupt _ _ _
theorem kp_nmi : KP nmi := by
  intro m
  rw [nmi_eq]
  exact (KP.bind (kp_interrupt m.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA) fun _ => kp_tick 7) { m with nmiPending := false }

/-! ## The table of opcodes -/

/-- each entry of the list keeps the program -/
def AllKP : List (M Unit) → Prop
  | [] => True
  | f :: l => KP f ∧ AllKP l

theorem AllKP.append {a b : List (M Unit)} (h1 : AllKP a) (h2 : AllKP b) : AllKP (a ++ b) := by
  induction a with
  | nil => simpa using h2
  | cons x l ih => exact ⟨h1.1, ih h1.2⟩

theorem AllKP.get {a : List (M Unit)} (h : AllKP a) (n : Nat) : KP (a[n]?.getD opJAM) := by
  induction a generalizing n with
  | nil => simpa using kp_opJAM
  | cons x l ih =>
    cases n with
    | zero => simpa using h.1
    | succ n => simpa using ih h.2 n

theorem k_row0 : AllKP row0 := ⟨kp_opBRK, kp_opORA kp_mIzx, kp_opJAM, kp_opSLO kp_mIzx, kp_opNOPm kp_mZp, kp_opORA kp_mZp, kp_opASL kp_mZp, kp_opSLO kp_mZp,
  kp_opPHP, kp_opORA kp_mImm, kp_accOp kp_aslV, kp_opJAM, kp_opNOPm kp_mAbs, kp_opORA kp_mAbs, kp_opASL kp_mAbs, kp_opSLO kp_mAbs, trivial⟩
theorem k_row1 : AllKP row1 := ⟨kp_opBPL, kp_opORA kp_mIzyR, kp_opJAM, kp_opSLO kp_mIzy, kp_opNOPm kp_mZpx, kp_opORA kp_mZpx, kp_opASL kp_mZpx, kp_opSLO kp_mZpx,
  kp_opCLC, kp_opORA kp_mAbyR, kp_opNOP, kp_opSLO kp_mAby, kp_opNOPm kp_mAbxR, kp_opORA kp_mAbxR, kp_opASL kp_mAbx, kp_opSLO kp_mAbx, trivial⟩
theorem k_row2 : AllKP row2 := ⟨kp_opJSR, kp_opAND kp_mIzx, kp_opJAM, kp_opRLA kp_mIzx, kp_opBIT kp_mZp, kp_opAND kp_mZp, kp_opROL kp_mZp, kp_opRLA kp_mZp,
  kp_opPLP, kp_opAND kp_mImm, kp_accOp kp_rolV, kp_opJAM, kp_opBIT kp_mAbs, kp_opAND kp_mAbs, kp_opROL kp_mAbs, kp_opRLA kp_mAbs, trivial⟩
theorem k_row3 : AllKP row3 := ⟨kp_opBMI, kp_opAND kp_mIzyR, kp_opJAM, kp_opRLA kp_mIzy, kp_opNOPm kp_mZpx, kp_opAND kp_mZpx, kp_opROL kp_mZpx, kp_opRLA kp_mZpx,
  kp_opSEC, kp_opAND kp_mAbyR, kp_opNOP, kp_opRLA kp_mAby, kp_opNOPm kp_mAbxR, kp_opAND kp_mAbxR, kp_opROL kp_mAbx, kp_opRLA kp_mAbx, trivial⟩
theorem k_row4 : AllKP row4 := ⟨kp_opRTI, kp_opEOR kp_mIzx, kp_opJAM, kp_opSRE kp_mIzx, kp_opNOPm kp_mZp, kp_opEOR kp_mZp, kp_opLSR kp_mZp, kp_opSRE kp_mZp,
  kp_opPHA, kp_opEOR kp_mImm, kp_accOp kp_lsrV, kp_opJAM, kp_opJMP, kp_opEOR kp_mAbs, kp_opLSR kp_mAbs, kp_opSRE kp_mAbs, trivial⟩
theorem k_row5 : AllKP row5 := ⟨kp_opBVC, kp_opEOR kp_mIzyR, kp_opJAM, kp_opSRE kp_mIzy, kp_opNOPm kp_mZpx, kp_opEOR kp_mZpx, kp_opLSR kp_mZpx, kp_opSRE kp_mZpx,
  kp_opCLI, kp_opEOR kp_mAbyR, kp_opNOP, kp_opSRE kp_mAby, kp_opNOPm kp_mAbxR, kp_opEOR kp_mAbxR, kp_opLSR kp_mAbx, kp_opSRE kp_mAbx, trivial⟩
theorem k_row6 : AllKP row6 := ⟨kp_opRTS, kp_opADC kp_mIzx, kp_opJAM, kp_opRRA kp_mIzx, kp_opNOPm kp_mZp, kp_opADC kp_mZp, kp_opROR kp_mZp, kp_opRRA kp_mZp,
  kp_opPLA, kp_opADC kp_mImm, kp_accOp kp_rorV, kp_opJAM, kp_opJMPi, kp_opADC kp_mAbs, kp_opROR kp_mAbs, kp_opRRA kp_mAbs, trivial⟩
theorem k_row7 : AllKP row7 := ⟨kp_opBVS, kp_opADC kp_mIzyR, kp_opJAM, kp_opRRA kp_mIzy, kp_opNOPm kp_mZpx, kp_opADC kp_mZpx, kp_opROR kp_mZpx, kp_opRRA kp_mZpx,
  kp_opSEI, kp_opADC kp_mAbyR, kp_opNOP, kp_opRRA kp_mAby, kp_opNOPm kp_mAbxR, kp_opADC kp_mAbxR, kp_opROR kp_mAbx, kp_opRRA kp_mAbx, trivial⟩
theorem k_row8 : AllKP row8 := ⟨kp_opNOPm kp_mImm, kp_opSTA kp_mIzx, kp_opNOPm kp_mImm, kp_opSAX kp_mIzx, kp_opSTY kp_mZp, kp_opSTA kp_mZp, kp_opSTX kp_mZp,
  kp_opSAX kp_mZp, kp_opDEY, kp_opNOPm kp_mImm, kp_opTXA, kp_opJAM, kp_opSTY kp_mAbs, kp_opSTA kp_mAbs, kp_opSTX kp_mAbs, kp_opSAX kp_mAbs, trivial⟩
theorem k_row9 : AllKP row9 := ⟨kp_opBCC, kp_opSTA kp_mIzy, kp_opJAM, kp_opJAM, kp_opSTY kp_mZpx, kp_opSTA kp_mZpx, kp_opSTX kp_mZpy, kp_opSAX kp_mZpy,
  kp_opTYA, kp_opSTA kp_mAby, kp_opTXS, kp_opJAM, kp_opJAM, kp_opSTA kp_mAbx, kp_opJAM, kp_opJAM, trivial⟩
theorem k_rowA : AllKP rowA := ⟨kp_opLDY kp_mImm, kp_opLDA kp_mIzx, kp_opLDX kp_mImm, kp_opLAX kp_mIzx, kp_opLDY kp_mZp, kp_opLDA kp_mZp, kp_opLDX kp_mZp,
  kp_opLAX kp_mZp, kp_opTAY, kp_opLDA kp_mImm, kp_opTAX, kp_opJAM, kp_opLDY kp_mAbs, kp_opLDA kp_mAbs, kp_opLDX kp_mAbs, kp_opLAX kp_mAbs, trivial⟩
theorem k_rowB : AllKP rowB := ⟨kp_opBCS, kp_opLDA kp_mIzyR, kp_opJAM, kp_opLAX kp_mIzyR, kp_opLDY kp_mZpx, kp_opLDA kp_mZpx, kp_opLDX kp_mZpy, kp_opLAX kp_mZpy,
  kp_opCLV, kp_opLDA kp_mAbyR, kp_opTSX, kp_opJAM, kp_opLDY kp_mAbxR, kp_opLDA kp_mAbxR, kp_opLDX kp_mAbyR, kp_opLAX kp_mAbyR, trivial⟩
theorem k_rowC : AllKP rowC := ⟨kp_opCPY kp_mImm, kp_opCMP kp_mIzx, kp_opNOPm kp_mImm, kp_opDCP kp_mIzx, kp_opCPY kp_mZp, kp_opCMP kp_mZp, kp_opDEC kp_mZp,
  kp_opDCP kp_mZp, kp_opINY, kp_opCMP kp_mImm, kp_opDEX, kp_opJAM, kp_opCPY kp_mAbs, kp_opCMP kp_mAbs, kp_opDEC kp_mAbs, kp_opDCP kp_mAbs, trivial⟩
theorem k_rowD : AllKP rowD := ⟨kp_opBNE, kp_opCMP kp_mIzyR, kp_opJAM, kp_opDCP kp_mIzy, kp_opNOPm kp_mZpx, kp_opCMP kp_mZpx, kp_opDEC kp_mZpx, kp_opDCP kp_mZpx,
  kp_opCLD, kp_opCMP kp_mAbyR, kp_opNOP, kp_opDCP kp_mAby, kp_opNOPm kp_mAbxR, kp_opCMP kp_mAbxR, kp_opDEC kp_mAbx, kp_opDCP kp_mAbx, trivial⟩
theorem k_rowE : AllKP rowE := ⟨kp_opCPX kp_mImm, kp_opSBC kp_mIzx, kp_opNOPm kp_mImm, kp_opISB kp_mIzx, kp_opCPX kp_mZp, kp_opSBC kp_mZp, kp_opINC kp_mZp,
  kp_opISB kp_mZp, kp_opINX, kp_opSBC kp_mImm, kp_opNOP, kp_opSBC kp_mImm, kp_opCPX kp_mAbs, kp_opSBC kp_mAbs, kp_opINC kp_mAbs, kp_opISB kp_mAbs, trivial⟩
theorem k_rowF : AllKP rowF := ⟨kp_opBEQ, kp_opSBC kp_mIzyR, kp_opJAM, kp_opISB kp_mIzy, kp_opNOPm kp_mZpx, kp_opSBC kp_mZpx, kp_opINC kp_mZpx, kp_opISB kp_mZpx,
  kp_opSED, kp_opSBC kp_mAbyR, kp_opNOP, kp_opISB kp_mAby, kp_opNOPm kp_mAbxR, kp_opSBC kp_mAbxR, kp_opINC kp_mAbx, kp_opISB kp_mAbx, trivial⟩

theorem k_all : AllKP allRows :=
  AllKP.append k_row0 (AllKP.append k_row1 (AllKP.append k_row2 (AllKP.append k_row3 (AllKP.append k_row4 (AllKP.append k_row5 (AllKP.append k_row6
    (AllKP.append k_row7 (AllKP.append k_row8 (AllKP.append k_row9 (AllKP.append k_rowA (AllKP.append k_rowB (AllKP.append k_rowC (AllKP.append k_rowD
    (AllKP.append k_rowE k_rowF))))))))))))))

/-- each entry of `opTable` keeps the program -/
theorem kp_op (op : UInt8) : KP (opTable[op.toNat]?.getD opJAM) := by
  rw [opTable_eq, List.getElem?_toArray]
  exact k_all.get op.toNat

/-! ## One step, a frame, a run -/

/-- **One step keeps the program and its mask.** -/
theorem step_prg (m : Machine) : (go step m).2.prg = m.prg ∧ (go step m).2.prgMask = m.prgMask := by
  by_cases hn : m.nmiPending = true
  · rw [TaintRun.step_nmi hn]
    exact kp_nmi m
  · by_cases hh : m.halted = true
    · have e : go step m = ((), m) := by
        unfold step go
        show (if m.nmiPending = true then nmi else if m.halted = true then _ else _) m = _
        rw [if_neg hn, if_pos hh]
        rfl
      rw [e]
      exact ⟨rfl, rfl⟩
    · have e : go step m = go (fetch >>= fun op => TaintRun.stepK m m.pc op) m := by
        unfold step go
        show (if m.nmiPending = true then nmi else if m.halted = true then _ else _) m = _
        rw [if_neg hn, if_neg hh]
        rfl
      rw [e]
      refine KP.bind kp_fetch (fun op => ?_) m
      unfold TaintRun.stepK
      split
      · exact KP.bind (kp_setPC _) fun _ => kp_tick _
      · exact KP.bind (kp_op _) fun _ => kp_tick _

/-- **Along the instructions of a frame** the program and the mask are those of the frame's start -/
theorem trace_prg (m : Machine) (i : UInt8) : ∀ n, (PipeEntryRule.trace m i n).prg = m.prg ∧ (PipeEntryRule.trace m i n).prgMask = m.prgMask
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := trace_prg m i n
    show (PipeEntryRule.nxt (m.frame + 1) (PipeEntryRule.trace m i n)).prg = m.prg ∧ (PipeEntryRule.nxt (m.frame + 1) (PipeEntryRule.trace m i n)).prgMask = m.prgMask
    unfold PipeEntryRule.nxt
    split
    · exact ih
    · exact ⟨(step_prg _).1.trans ih.1, (step_prg _).2.trans ih.2⟩

/-- a whole frame keeps the program and the mask -/
theorem frame_prg (m : Machine) (i : UInt8) : (PipeTransition.frame m i).prg = m.prg ∧ (PipeTransition.frame m i).prgMask = m.prgMask := by
  rw [PipeEntryRule.frame_trace]
  exact trace_prg m i _

/-- **On a run of real frames** every machine from frame `a` on has the program and the mask of frame `a` -/
theorem run_prg (S : FrameKeep.RealRun) (a : Nat) : ∀ d, (S.seq (a + d)).prg = (S.seq a).prg ∧ (S.seq (a + d)).prgMask = (S.seq a).prgMask
  | 0 => ⟨rfl, rfl⟩
  | d + 1 => by
    have ih := run_prg S a d
    rw [show a + (d + 1) = a + d + 1 by omega, S.next]
    exact ⟨(frame_prg _ _).1.trans ih.1, (frame_prg _ _).2.trans ih.2⟩

end Smbrta.StepPrg
