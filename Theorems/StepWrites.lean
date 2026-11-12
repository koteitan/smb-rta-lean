import Theorems.PipeEntryRule
import Theorems.SideChangeEnd

/-!
# Where one step of the CPU writes RAM

One step of the CPU changes RAM only at the address that its instruction stores to, and at the bytes of the stack that it pushes (`step_ram`). These places are
`stepLocs m`: for an instruction that stores or does a read-modify-write, the RAM index of its effective address; for `PHA`, `PHP`, `JSR`, `BRK` and the NMI, the
bytes of the stack at the stack pointer and below it; for every other instruction, none. A table says for each of the 256 opcodes what it writes (`wRows`), and a
routine lemma for each kind of instruction proves it (`AllW`), as `PipeTransitionAll` does for its relation. Along the instructions of a frame (`trace`), a byte that no
step writes keeps its value (`trace_ram`).

An abstract state of `TaintRun` knows enough to say where its step may write: `keepOK E P A` checks that the step of `A` writes no byte of `P`, and `keep_step` proves it
for every machine that `A` covers. With it a walk carries a fact about bytes that its states do not know:
* `kframe_of_walk`, `keep_frame`: a frame whose walk meets `keepOK` on every state writes no byte of `P`.
* `tframe_of_walk`: the bytes of a routine (the sound's) are in a state of a table. At the call the state is split by the table, the routine is walked with the bytes known,
  at the return the bytes are checked against a second table and forgotten (`tsuccs`). Outside the routine every step keeps the bytes, or writes them so that the table
  stays closed (`writeOK`).

There is no game data in this file. Page: `1-1/d-3-4-1-StepWrites.md`.
-/

namespace Smbrta.StepWrites

open PipeTransitionAll (go go_bind Leaf leaf_tick leaf_incPC leaf_decS leaf_incS leaf_jam leaf_ppuRead leaf_padRead leaf_ppuWrite leaf_padWrite leaf_oamDma
  ioMark leaf_ioMark romRead leaf_romRead rdRamF trF_ram wrRamF ba_get_set_ne
  leaf_setAOnly leaf_setXOnly leaf_setYOnly leaf_laxRegs leaf_bitFlags leaf_plpFlags leaf_txs leaf_setZN leaf_setFlag leaf_adc leaf_setPC nmi_eq
  row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 rowA rowB rowC rowD rowE rowF allRows opTable_eq)
open TaintRun (AS Env AAd AMode AdR Snd Sim AB AM)

/-! ## Actions that do not write RAM -/

/-- `f` does not change RAM -/
def NoWr {α : Type} (f : M α) : Prop := ∀ m, (go f m).2.ram = m.ram

theorem NoWr.ofLeaf {α : Type} {f : M α} (h : Leaf f) : NoWr f := h.ram

theorem NoWr.bind {α β : Type} {f : M α} {g : α → M β} (hf : NoWr f) (hg : ∀ a, NoWr (g a)) : NoWr (f >>= g) := by
  intro m
  rw [go_bind, hg, hf]

theorem NoWr.get' {α : Type} {k : Machine → M α} (h : ∀ x, NoWr (k x)) : NoWr (get >>= k) := fun m => h m m

theorem NoWr.pure {α : Type} (a : α) : NoWr (Pure.pure a : M α) := fun _ => rfl

theorem NoWr.congr {α : Type} {f g : M α} (h : ∀ m, go f m = go g m) (hg : NoWr g) : NoWr f := fun m => by
  rw [h]
  exact hg m

theorem nw_rd (addr : UInt16) : NoWr (rd addr) := by
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
    · exact trF_ram _ _
    · rfl
  · by_cases h2 : addr ≥ 0x8000
    · refine NoWr.congr (g := romRead addr) (fun m => ?_) (NoWr.ofLeaf (leaf_romRead addr))
      unfold rd go
      rw [if_neg h1, if_pos h2]
      rfl
    · by_cases h3 : addr < 0x4000
      · refine NoWr.congr (g := ioMark >>= fun _ => ppuRead (addr &&& 7)) (fun m => ?_)
          (NoWr.bind (NoWr.ofLeaf leaf_ioMark) fun _ => NoWr.ofLeaf (leaf_ppuRead _))
        unfold rd go
        rw [if_neg h1, if_neg h2, if_pos h3]
        cases m with
        | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
          cases trk <;> rfl
      · by_cases h4 : (addr == 0x4016) = true
        · refine NoWr.congr (g := ioMark >>= fun _ => padRead) (fun m => ?_)
            (NoWr.bind (NoWr.ofLeaf leaf_ioMark) fun _ => NoWr.ofLeaf leaf_padRead)
          unfold rd go
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          cases m with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases trk <;> rfl
        · by_cases h5 : (addr == 0x4017) = true
          · refine NoWr.congr (g := Pure.pure 0x40) (fun m => ?_) (NoWr.pure _)
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
          · refine NoWr.congr (g := Pure.pure 0) (fun m => ?_) (NoWr.pure _)
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- a write outside RAM does not change RAM -/
theorem nw_wr_io {addr : UInt16} (v : UInt8) (h1 : ¬ addr < 0x2000) : NoWr (wr addr v) := by
  by_cases h2 : addr < 0x4000
  · refine NoWr.congr (g := ppuWrite (addr &&& 7) v) (fun m => ?_) (NoWr.ofLeaf (leaf_ppuWrite _ _))
    unfold wr go
    rw [if_neg h1, if_pos h2]
  · by_cases h3 : (addr == 0x4014) = true
    · refine NoWr.congr (g := oamDma) (fun m => ?_) (NoWr.ofLeaf leaf_oamDma)
      unfold wr go
      rw [if_neg h1, if_neg h2, if_pos h3]
    · by_cases h4 : (addr == 0x4016) = true
      · refine NoWr.congr (g := padWrite v) (fun m => ?_) (NoWr.ofLeaf (leaf_padWrite v))
        unfold wr go
        rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
      · refine NoWr.congr (g := Pure.pure ()) (fun m => ?_) (NoWr.pure _)
        unfold wr go
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

theorem nw_fetch : NoWr fetch :=
  NoWr.congr (g := PipeTransitionAll.incPC >>= rd) (fun _ => rfl) (NoWr.bind (NoWr.ofLeaf leaf_incPC) nw_rd)
theorem nw_fetch16 : NoWr fetch16 := NoWr.bind nw_fetch fun _ => NoWr.bind nw_fetch fun _ => NoWr.pure _
theorem nw_rd16zp (z : UInt8) : NoWr (rd16zp z) := NoWr.bind (nw_rd _) fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.pure _
theorem nw_pagePenalty (b e : UInt16) : NoWr (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact NoWr.ofLeaf (leaf_tick 1)
  · exact NoWr.pure _

theorem nw_mImm : NoWr mImm := NoWr.ofLeaf leaf_incPC
theorem nw_mZp : NoWr mZp := NoWr.bind nw_fetch fun _ => NoWr.pure _
theorem nw_mZpx : NoWr mZpx := NoWr.bind nw_fetch fun _ => NoWr.get' fun _ => NoWr.pure _
theorem nw_mZpy : NoWr mZpy := NoWr.bind nw_fetch fun _ => NoWr.get' fun _ => NoWr.pure _
theorem nw_mAbs : NoWr mAbs := nw_fetch16
theorem nw_mAbx : NoWr mAbx := NoWr.bind nw_fetch16 fun _ => NoWr.get' fun _ => NoWr.pure _
theorem nw_mAby : NoWr mAby := NoWr.bind nw_fetch16 fun _ => NoWr.get' fun _ => NoWr.pure _
theorem nw_mAbxR : NoWr mAbxR := NoWr.bind nw_fetch16 fun _ => NoWr.get' fun _ => NoWr.bind (nw_pagePenalty _ _) fun _ => NoWr.pure _
theorem nw_mAbyR : NoWr mAbyR := NoWr.bind nw_fetch16 fun _ => NoWr.get' fun _ => NoWr.bind (nw_pagePenalty _ _) fun _ => NoWr.pure _
theorem nw_mIzx : NoWr mIzx := NoWr.bind nw_fetch fun _ => NoWr.get' fun _ => nw_rd16zp _
theorem nw_mIzy : NoWr mIzy := NoWr.bind nw_fetch fun _ => NoWr.bind (nw_rd16zp _) fun _ => NoWr.get' fun _ => NoWr.pure _
theorem nw_mIzyR : NoWr mIzyR :=
  NoWr.bind nw_fetch fun _ => NoWr.bind (nw_rd16zp _) fun _ => NoWr.get' fun _ => NoWr.bind (nw_pagePenalty _ _) fun _ => NoWr.pure _

theorem nw_setZN (v : UInt8) : NoWr (setZN v) := NoWr.ofLeaf (leaf_setZN v)
theorem nw_setFlag (a : UInt8) (b : Bool) : NoWr (setFlag a b) := NoWr.ofLeaf (leaf_setFlag a b)
theorem nw_setA (v : UInt8) : NoWr (setA v) := NoWr.bind (NoWr.ofLeaf (leaf_setAOnly v)) fun _ => nw_setZN v
theorem nw_setX (v : UInt8) : NoWr (setX v) := NoWr.bind (NoWr.ofLeaf (leaf_setXOnly v)) fun _ => nw_setZN v
theorem nw_setY (v : UInt8) : NoWr (setY v) := NoWr.bind (NoWr.ofLeaf (leaf_setYOnly v)) fun _ => nw_setZN v
theorem nw_pull : NoWr pull :=
  NoWr.congr (g := PipeTransitionAll.incS >>= fun sp => rd (0x100 ||| sp.toUInt16)) (fun _ => rfl)
    (NoWr.bind (NoWr.ofLeaf leaf_incS) fun _ => nw_rd _)
theorem nw_setPC (a : UInt16) : NoWr (setPC a) := NoWr.ofLeaf (leaf_setPC a)
theorem nw_adc (v : UInt8) : NoWr (adc v) := NoWr.ofLeaf (leaf_adc v)
theorem nw_oraV (v : UInt8) : NoWr (oraV v) := NoWr.get' fun _ => nw_setA _
theorem nw_andV (v : UInt8) : NoWr (andV v) := NoWr.get' fun _ => nw_setA _
theorem nw_eorV (v : UInt8) : NoWr (eorV v) := NoWr.get' fun _ => nw_setA _
theorem nw_cmpV (r v : UInt8) : NoWr (cmpV r v) := NoWr.bind (nw_setZN _) fun _ => nw_setFlag _ _
theorem nw_aslV (v : UInt8) : NoWr (aslV v) := NoWr.bind (nw_setFlag _ _) fun _ => NoWr.bind (nw_setZN _) fun _ => NoWr.pure _
theorem nw_lsrV (v : UInt8) : NoWr (lsrV v) := NoWr.bind (nw_setFlag _ _) fun _ => NoWr.bind (nw_setZN _) fun _ => NoWr.pure _
theorem nw_rolV (v : UInt8) : NoWr (rolV v) :=
  NoWr.get' fun _ => NoWr.bind (nw_setFlag _ _) fun _ => NoWr.bind (nw_setZN _) fun _ => NoWr.pure _
theorem nw_rorV (v : UInt8) : NoWr (rorV v) :=
  NoWr.get' fun _ => NoWr.bind (nw_setFlag _ _) fun _ => NoWr.bind (nw_setZN _) fun _ => NoWr.pure _
theorem nw_incV (v : UInt8) : NoWr (incV v) := NoWr.bind (nw_setZN _) fun _ => NoWr.pure _
theorem nw_decV (v : UInt8) : NoWr (decV v) := NoWr.bind (nw_setZN _) fun _ => NoWr.pure _

/-! ## Where an action writes -/

/-- the RAM index of an address, if the address is in RAM -/
def ramIdx (a : UInt16) : List Nat := if a < 0x2000 then [(a &&& 0x7FF).toNat] else []

/-- `f` changes RAM only at the indices `w m`, where `m` is the machine it starts from -/
def WrIn {α : Type} (w : Machine → List Nat) (f : M α) : Prop := ∀ m i, i ∉ w m → (go f m).2.ram.get! i = m.ram.get! i

theorem WrIn.ofNoWr {α : Type} {w : Machine → List Nat} {f : M α} (h : NoWr f) : WrIn w f := fun m _ _ => by rw [h m]

theorem WrIn.get' {α : Type} {w : Machine → List Nat} {k : Machine → M α} (h : ∀ x, WrIn w (k x)) : WrIn w (get >>= k) := fun m i hi => h m m i hi

/-- a part that does not write, then a part that writes at places fixed in advance -/
theorem WrIn.nw_then {α β : Type} {L : List Nat} {f : M α} {g : α → M β} (hf : NoWr f) (hg : ∀ a, WrIn (fun _ => L) (g a)) : WrIn (fun _ => L) (f >>= g) := by
  intro m i hi
  rw [go_bind, hg _ _ i hi, hf]

/-- a part that writes, then a part that does not -/
theorem WrIn.then_nw {α β : Type} {w : Machine → List Nat} {f : M α} {g : α → M β} (hf : WrIn w f) (hg : ∀ a, NoWr (g a)) : WrIn w (f >>= g) := by
  intro m i hi
  rw [go_bind, hg, hf m i hi]

/-- a part that does not write gives the address, then a part that writes there -/
theorem WrIn.at_md {β : Type} {md : M UInt16} {g : UInt16 → M β} (hf : NoWr md) (hg : ∀ a, WrIn (fun _ => ramIdx a) (g a)) :
    WrIn (fun m => ramIdx (go md m).1) (md >>= g) := by
  intro m i hi
  rw [go_bind, hg _ _ i hi, hf]

theorem wrin_wr (addr : UInt16) (v : UInt8) : WrIn (fun _ => ramIdx addr) (wr addr v) := by
  intro m i hi
  by_cases h1 : addr < 0x2000
  · have e : go (wr addr v) m = ((), wrRamF (addr &&& 0x7FF).toNat v m) := by
      unfold wr go
      rw [if_pos h1]
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases trk <;> rfl
    rw [e]
    have hne : (addr &&& 0x7FF).toNat ≠ i := by
      intro h
      apply hi
      simp [ramIdx, h1, h]
    unfold wrRamF
    split
    · exact ba_get_set_ne _ _ _ _ hne
    · exact ba_get_set_ne _ _ _ _ hne
  · rw [nw_wr_io v h1 m]

/-! ## The stack -/

/-- the RAM indices of `k` pushes from the stack pointer `s` -/
def stk (s : UInt8) : Nat → List Nat
  | 0 => []
  | k + 1 => ramIdx (0x100 ||| s.toUInt16) ++ stk (s - 1) k

theorem stk_lt (sp : UInt8) : (0x100 ||| sp.toUInt16 : UInt16) < 0x2000 := by
  apply UInt16.lt_iff_toNat_lt.2
  have h1 := sp.toNat_lt
  have h2 : (0x100 ||| sp.toUInt16 : UInt16).toNat = 256 ||| sp.toNat := by
    simp [UInt16.toNat_or]
  rw [h2]
  have h3 : 256 ||| sp.toNat < 2 ^ 13 := Nat.or_lt_two_pow (by decide) (by omega)
  simpa using h3

theorem push_eq (v : UInt8) (m : Machine) : go (push v) m = go (wr (0x100 ||| m.s.toUInt16) v) { m with s := m.s - 1 } := rfl

theorem push_s (v : UInt8) (m : Machine) : (go (push v) m).2.s = m.s - 1 := by
  rw [push_eq]
  have e : go (wr (0x100 ||| m.s.toUInt16) v) { m with s := m.s - 1 } = ((), wrRamF ((0x100 ||| m.s.toUInt16) &&& 0x7FF).toNat v { m with s := m.s - 1 }) := by
    unfold wr go
    rw [if_pos (stk_lt m.s)]
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  rw [e]
  unfold wrRamF
  split <;> rfl

/-- a push, then `k` more -/
theorem WrIn.push_then {β : Type} {k : Nat} {v : UInt8} {g : Unit → M β} (hg : ∀ a, WrIn (fun m => stk m.s k) (g a)) :
    WrIn (fun m => stk m.s (k + 1)) (push v >>= g) := by
  intro m i hi
  simp only [stk, List.mem_append, not_or] at hi
  rw [go_bind]
  have h2 : i ∉ stk (go (push v) m).2.s k := by
    rw [push_s]
    exact hi.2
  have h1 := hg (go (push v) m).1 (go (push v) m).2 i h2
  rw [h1, push_eq]
  exact wrin_wr _ v _ i hi.1

/-- `k` pushes after a part that does not write and keeps the stack pointer -/
theorem WrIn.nw_s_then {α β : Type} {k : Nat} {f : M α} {g : α → M β} (hf : NoWr f) (hs : ∀ m, (go f m).2.s = m.s)
    (hg : ∀ a, WrIn (fun m => stk m.s k) (g a)) : WrIn (fun m => stk m.s k) (f >>= g) := by
  intro m i hi
  have h2 : i ∉ stk (go f m).2.s k := by
    rw [hs]
    exact hi
  rw [go_bind, hg _ _ i h2, hf]

/-- `f` keeps the stack pointer -/
def KeepS {α : Type} (f : M α) : Prop := ∀ m, (go f m).2.s = m.s

theorem KeepS.bind {α β : Type} {f : M α} {g : α → M β} (hf : KeepS f) (hg : ∀ a, KeepS (g a)) : KeepS (f >>= g) := by
  intro m
  rw [go_bind, hg, hf]

theorem KeepS.congr {α : Type} {f g : M α} (h : ∀ m, go f m = go g m) (hg : KeepS g) : KeepS f := fun m => by
  rw [h]
  exact hg m

theorem ks_rd (addr : UInt16) : KeepS (rd addr) := by
  by_cases h1 : addr < 0x2000
  · intro m
    have e : go (rd addr) m = rdRamF (addr &&& 0x7FF).toNat m := by
      unfold rd go
      rw [if_pos h1]
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases trk <;> rfl
    rw [e]
    unfold rdRamF PipeTransitionAll.trF
    split
    · split <;> rfl
    · rfl
  · by_cases h2 : addr ≥ 0x8000
    · intro m
      unfold rd go
      rw [if_neg h1, if_pos h2]
      rfl
    · by_cases h3 : addr < 0x4000
      · intro m
        have e : go (rd addr) m = go (ioMark >>= fun _ => ppuRead (addr &&& 7)) m := by
          unfold rd go
          rw [if_neg h1, if_neg h2, if_pos h3]
          cases m with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases trk <;> rfl
        rw [e, go_bind]
        have e2 : (go ioMark m).2.s = m.s := by
          cases m with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases trk <;> rfl
        rw [← e2]
        generalize (go ioMark m).2 = m'
        unfold ppuRead go
        split <;> rfl
      · by_cases h4 : (addr == 0x4016) = true
        · intro m
          have e : go (rd addr) m = go (ioMark >>= fun _ => padRead) m := by
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
            cases m with
            | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
              cases trk <;> rfl
          rw [e, go_bind]
          have e2 : (go ioMark m).2.s = m.s := by
            cases m with
            | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
              cases trk <;> rfl
          rw [← e2]
          generalize (go ioMark m).2 = m'
          cases m' with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases padStrobe <;> rfl
        · by_cases h5 : (addr == 0x4017) = true
          · intro m
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
            rfl
          · intro m
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
            rfl

theorem fetch_s (m : Machine) : (go fetch m).2.s = m.s := by
  show (go (rd m.pc) { m with pc := m.pc + 1 }).2.s = m.s
  exact ks_rd m.pc _

theorem fetch16_s (m : Machine) : (go fetch16 m).2.s = m.s := by
  show (go fetch (go fetch m).2).2.s = m.s
  rw [fetch_s, fetch_s]

/-! ## The instructions -/

section
variable {md : Mode}

theorem nw_opLDA (h : NoWr md) : NoWr (opLDA md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_setA _
theorem nw_opLDX (h : NoWr md) : NoWr (opLDX md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_setX _
theorem nw_opLDY (h : NoWr md) : NoWr (opLDY md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_setY _
theorem nw_opLAX (h : NoWr md) : NoWr (opLAX md) :=
  NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.bind (NoWr.ofLeaf (leaf_laxRegs _)) fun _ => nw_setZN _
theorem nw_opADC (h : NoWr md) : NoWr (opADC md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_adc _
theorem nw_opSBC (h : NoWr md) : NoWr (opSBC md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_adc _
theorem nw_opORA (h : NoWr md) : NoWr (opORA md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_oraV _
theorem nw_opAND (h : NoWr md) : NoWr (opAND md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_andV _
theorem nw_opEOR (h : NoWr md) : NoWr (opEOR md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => nw_eorV _
theorem nw_opCMP (h : NoWr md) : NoWr (opCMP md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.get' fun _ => nw_cmpV _ _
theorem nw_opCPX (h : NoWr md) : NoWr (opCPX md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.get' fun _ => nw_cmpV _ _
theorem nw_opCPY (h : NoWr md) : NoWr (opCPY md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.get' fun _ => nw_cmpV _ _
theorem nw_opBIT (h : NoWr md) : NoWr (opBIT md) := NoWr.bind h fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.ofLeaf (leaf_bitFlags _)
theorem nw_opNOPm (h : NoWr md) : NoWr (opNOPm md) := NoWr.bind h fun _ => NoWr.pure _

/-- a store: it writes at the address of its mode -/
theorem w_store {g : Machine → UInt8} (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (md >>= fun ad => get >>= fun x => wr ad (g x)) :=
  WrIn.at_md h fun _ => WrIn.get' fun _ => wrin_wr _ _
theorem w_opSTA (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSTA md) := w_store h
theorem w_opSTX (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSTX md) := w_store h
theorem w_opSTY (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSTY md) := w_store h
theorem w_opSAX (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSAX md) := w_store h

theorem w_rmw {f : UInt8 → M UInt8} (hf : ∀ v, NoWr (f v)) (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (rmw f md) :=
  WrIn.at_md h fun _ => WrIn.nw_then (nw_rd _) fun _ => WrIn.nw_then (hf _) fun _ => wrin_wr _ _
theorem w_rmw2 {f : UInt8 → M UInt8} {g : UInt8 → M Unit} (hf : ∀ v, NoWr (f v)) (hg : ∀ v, NoWr (g v)) (h : NoWr md) :
    WrIn (fun m => ramIdx (go md m).1) (rmw2 f g md) :=
  WrIn.at_md h fun _ => WrIn.nw_then (nw_rd _) fun _ => WrIn.nw_then (hf _) fun _ => WrIn.then_nw (wrin_wr _ _) fun _ => hg _

theorem w_opASL (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opASL md) := w_rmw nw_aslV h
theorem w_opLSR (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opLSR md) := w_rmw nw_lsrV h
theorem w_opROL (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opROL md) := w_rmw nw_rolV h
theorem w_opROR (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opROR md) := w_rmw nw_rorV h
theorem w_opINC (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opINC md) := w_rmw nw_incV h
theorem w_opDEC (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opDEC md) := w_rmw nw_decV h
theorem w_opSLO (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSLO md) := w_rmw2 nw_aslV nw_oraV h
theorem w_opRLA (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opRLA md) := w_rmw2 nw_rolV nw_andV h
theorem w_opSRE (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opSRE md) := w_rmw2 nw_lsrV nw_eorV h
theorem w_opRRA (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opRRA md) := w_rmw2 nw_rorV nw_adc h
theorem w_opDCP (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opDCP md) :=
  w_rmw2 (fun _ => NoWr.pure _) (fun _ => NoWr.get' fun _ => nw_cmpV _ _) h
theorem w_opISB (h : NoWr md) : WrIn (fun m => ramIdx (go md m).1) (opISB md) :=
  w_rmw2 (fun _ => NoWr.pure _) (fun _ => nw_adc _) h
end

theorem nw_accOp {f : UInt8 → M UInt8} (hf : ∀ v, NoWr (f v)) : NoWr (accOp f) :=
  NoWr.get' fun _ => NoWr.bind (hf _) fun _ => NoWr.ofLeaf (leaf_setAOnly _)

theorem nw_opNOP : NoWr opNOP := NoWr.pure _
theorem nw_opJAM : NoWr opJAM := NoWr.ofLeaf leaf_jam

theorem nw_branch (cond : Machine → Bool) : NoWr (branch cond) := by
  refine NoWr.bind nw_fetch fun off => NoWr.get' fun m => ?_
  split
  · exact NoWr.bind (nw_setPC _) fun _ => NoWr.ofLeaf (leaf_tick _)
  · exact NoWr.pure _

theorem nw_opBPL : NoWr opBPL := nw_branch _
theorem nw_opBMI : NoWr opBMI := nw_branch _
theorem nw_opBVC : NoWr opBVC := nw_branch _
theorem nw_opBVS : NoWr opBVS := nw_branch _
theorem nw_opBCC : NoWr opBCC := nw_branch _
theorem nw_opBCS : NoWr opBCS := nw_branch _
theorem nw_opBNE : NoWr opBNE := nw_branch _
theorem nw_opBEQ : NoWr opBEQ := nw_branch _

theorem nw_opCLC : NoWr opCLC := nw_setFlag _ _
theorem nw_opSEC : NoWr opSEC := nw_setFlag _ _
theorem nw_opCLI : NoWr opCLI := nw_setFlag _ _
theorem nw_opSEI : NoWr opSEI := nw_setFlag _ _
theorem nw_opCLV : NoWr opCLV := nw_setFlag _ _
theorem nw_opCLD : NoWr opCLD := nw_setFlag _ _
theorem nw_opSED : NoWr opSED := nw_setFlag _ _

theorem nw_opTAX : NoWr opTAX := NoWr.get' fun _ => nw_setX _
theorem nw_opTAY : NoWr opTAY := NoWr.get' fun _ => nw_setY _
theorem nw_opTXA : NoWr opTXA := NoWr.get' fun _ => nw_setA _
theorem nw_opTYA : NoWr opTYA := NoWr.get' fun _ => nw_setA _
theorem nw_opTSX : NoWr opTSX := NoWr.get' fun _ => nw_setX _
theorem nw_opTXS : NoWr opTXS := NoWr.ofLeaf leaf_txs
theorem nw_opINX : NoWr opINX := NoWr.get' fun _ => nw_setX _
theorem nw_opINY : NoWr opINY := NoWr.get' fun _ => nw_setY _
theorem nw_opDEX : NoWr opDEX := NoWr.get' fun _ => nw_setX _
theorem nw_opDEY : NoWr opDEY := NoWr.get' fun _ => nw_setY _
theorem nw_opPLA : NoWr opPLA := NoWr.bind nw_pull fun _ => nw_setA _
theorem nw_opPLP : NoWr opPLP := NoWr.bind nw_pull fun _ => NoWr.ofLeaf (leaf_plpFlags _)
theorem nw_opJMP : NoWr opJMP := NoWr.bind nw_fetch16 fun _ => nw_setPC _
theorem nw_opJMPi : NoWr opJMPi := NoWr.bind nw_fetch16 fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.bind (nw_rd _) fun _ => nw_setPC _
theorem nw_opRTS : NoWr opRTS := NoWr.bind nw_pull fun _ => NoWr.bind nw_pull fun _ => nw_setPC _
theorem nw_opRTI : NoWr opRTI := NoWr.bind nw_opPLP fun _ => NoWr.bind nw_pull fun _ => NoWr.bind nw_pull fun _ => nw_setPC _

theorem w_push (v : UInt8) : WrIn (fun m => stk m.s 1) (push v) := by
  intro m i hi
  simp only [stk, List.append_nil] at hi
  rw [push_eq]
  exact wrin_wr _ v _ i hi
theorem w_opPHA : WrIn (fun m => stk m.s 1) opPHA := WrIn.get' fun _ => w_push _
theorem w_opPHP : WrIn (fun m => stk m.s 1) opPHP := WrIn.get' fun _ => w_push _
theorem w_opJSR : WrIn (fun m => stk m.s 2) opJSR :=
  WrIn.nw_s_then nw_fetch16 fetch16_s fun _ => WrIn.get' fun _ =>
    WrIn.push_then fun _ => WrIn.push_then fun _ => WrIn.ofNoWr (nw_setPC _)
theorem w_interrupt (pc : UInt16) (p : UInt8) (v : UInt16) : WrIn (fun m => stk m.s 3) (interrupt pc p v) :=
  WrIn.push_then fun _ => WrIn.push_then fun _ => WrIn.push_then fun _ => WrIn.ofNoWr
    (NoWr.bind (nw_setFlag _ _) fun _ => NoWr.bind (nw_rd _) fun _ => NoWr.bind (nw_rd _) fun _ => nw_setPC _)
theorem w_opBRK : WrIn (fun m => stk m.s 3) opBRK := WrIn.get' fun _ => w_interrupt _ _ _
theorem w_nmi : WrIn (fun m => stk m.s 3) nmi := by
  intro m i hi
  rw [nmi_eq]
  exact (WrIn.then_nw (w_interrupt m.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA) fun _ => NoWr.ofLeaf (leaf_tick 7)) { m with nmiPending := false } i hi

/-! ## The table of opcodes -/

/-- what an opcode writes: nothing, the address of its mode (with the abstract mode of `TaintRun` for the same mode), or `k` bytes of the stack -/
inductive Wr where
  | no : Wr
  | md : Mode → (Env → AMode) → Wr
  | st : Nat → Wr

/-- the RAM indices that the instruction writes, from the machine after its opcode -/
def Wr.locs : Wr → Machine → List Nat
  | .no, _ => []
  | .md c _, m => ramIdx (go c m).1
  | .st k, m => stk m.s k

/-- the abstract mode follows the mode -/
def Wr.ok : Wr → Prop
  | .md c a => ∀ E F, Snd E F AdR (a E) c
  | _ => True

/-- two tables of the same length, entry by entry -/
def AllW : List Wr → List (M Unit) → Prop
  | [], [] => True
  | w :: l, f :: r => (WrIn w.locs f ∧ w.ok) ∧ AllW l r
  | _, _ => False

theorem AllW.append {a b : List Wr} {f g : List (M Unit)} (h1 : AllW a f) (h2 : AllW b g) : AllW (a ++ b) (f ++ g) := by
  induction a generalizing f with
  | nil =>
    cases f with
    | nil => simpa using h2
    | cons _ _ => exact absurd h1 (by simp [AllW])
  | cons x l ih =>
    cases f with
    | nil => exact absurd h1 (by simp [AllW])
    | cons y r => exact ⟨h1.1, ih h1.2⟩

theorem AllW.get {a : List Wr} {f : List (M Unit)} (h : AllW a f) (n : Nat) :
    WrIn (a[n]?.getD .no).locs (f[n]?.getD opJAM) ∧ (a[n]?.getD .no).ok := by
  induction a generalizing f n with
  | nil =>
    cases f with
    | nil => exact ⟨WrIn.ofNoWr nw_opJAM, trivial⟩
    | cons _ _ => exact absurd h (by simp [AllW])
  | cons x l ih =>
    cases f with
    | nil => exact absurd h (by simp [AllW])
    | cons y r =>
      cases n with
      | zero => simpa using h.1
      | succ n => simpa using ih h.2 n

/-- an entry that does not write -/
theorem e_no {f : M Unit} (h : NoWr f) : WrIn Wr.no.locs f ∧ Wr.no.ok := ⟨WrIn.ofNoWr h, trivial⟩
/-- an entry that writes at its mode -/
theorem e_md {c : Mode} {a : Env → AMode} {f : M Unit} (h : WrIn (fun m => ramIdx (go c m).1) f) (hs : ∀ E F, Snd E F AdR (a E) c) :
    WrIn (Wr.md c a).locs f ∧ (Wr.md c a).ok := ⟨h, hs⟩
/-- an entry that pushes -/
theorem e_st {k : Nat} {f : M Unit} (h : WrIn (fun m => stk m.s k) f) : WrIn (Wr.st k).locs f ∧ (Wr.st k).ok := ⟨h, trivial⟩

open TaintRun (aIzx aIzy aZp aZpi aAbs aAbi s_mIzx s_mIzy s_mZp s_mZpx s_mZpy s_mAbs s_mAbx s_mAby)

/-- the modes that write, with their abstract modes -/
abbrev wIzx : Wr := .md mIzx aIzx
abbrev wIzy : Wr := .md mIzy aIzy
abbrev wZp : Wr := .md mZp aZp
abbrev wZpx : Wr := .md mZpx (fun E => aZpi E (·.x))
abbrev wZpy : Wr := .md mZpy (fun E => aZpi E (·.y))
abbrev wAbs : Wr := .md mAbs aAbs
abbrev wAbx : Wr := .md mAbx (fun E => aAbi E (·.x))
abbrev wAby : Wr := .md mAby (fun E => aAbi E (·.y))

theorem o_Izx : ∀ E F, Snd E F AdR (aIzx E) mIzx := fun _ _ => s_mIzx
theorem o_Izy : ∀ E F, Snd E F AdR (aIzy E) mIzy := fun _ _ => s_mIzy
theorem o_Zp : ∀ E F, Snd E F AdR (aZp E) mZp := fun _ _ => s_mZp
theorem o_Zpx : ∀ E F, Snd E F AdR ((fun E => aZpi E (·.x)) E) mZpx := fun _ _ => s_mZpx
theorem o_Zpy : ∀ E F, Snd E F AdR ((fun E => aZpi E (·.y)) E) mZpy := fun _ _ => s_mZpy
theorem o_Abs : ∀ E F, Snd E F AdR (aAbs E) mAbs := fun _ _ => s_mAbs
theorem o_Abx : ∀ E F, Snd E F AdR ((fun E => aAbi E (·.x)) E) mAbx := fun _ _ => s_mAbx
theorem o_Aby : ∀ E F, Snd E F AdR ((fun E => aAbi E (·.y)) E) mAby := fun _ _ => s_mAby

/-- the rows of odd high nibble 1, 3, 5, 7, D, F, after the first column -/
def wOdd : List Wr := [.no, .no, wIzy, .no, .no, wZpx, wZpx, .no, .no, .no, wAby, .no, .no, wAbx, wAbx]
/-- the rows 0, 2, 4, 6, C, E between the first column and the ninth -/
def wEvenA : List Wr := [.no, .no, wIzx, .no, .no, wZp, wZp]
/-- the same rows after the ninth column -/
def wEvenB : List Wr := [.no, .no, .no, .no, .no, wAbs, wAbs]

def w0 : List Wr := .st 3 :: wEvenA ++ .st 1 :: wEvenB
def w1 : List Wr := .no :: wOdd
def w2 : List Wr := .st 2 :: wEvenA ++ .no :: wEvenB
def w4 : List Wr := .no :: wEvenA ++ .st 1 :: wEvenB
def w6 : List Wr := .no :: wEvenA ++ .no :: wEvenB
def w8 : List Wr := [.no, wIzx, .no, wIzx, wZp, wZp, wZp, wZp, .no, .no, .no, .no, wAbs, wAbs, wAbs, wAbs]
def w9 : List Wr := [.no, wIzy, .no, .no, wZpx, wZpx, wZpy, wZpy, .no, wAby, .no, .no, .no, wAbx, .no, .no]
def wA : List Wr := List.replicate 16 .no

/-- what each of the 256 opcodes writes, in the order of `opTable` -/
def wRows : List Wr := w0 ++ (w1 ++ (w2 ++ (w1 ++ (w4 ++ (w1 ++ (w6 ++ (w1 ++ (w8 ++ (w9 ++ (wA ++ (wA ++ (w6 ++ (w1 ++ (w6 ++ w1))))))))))))))

theorem a_row0 : AllW w0 row0 := ⟨e_st w_opBRK, e_no (nw_opORA nw_mIzx), e_no nw_opJAM, e_md (w_opSLO nw_mIzx) o_Izx, e_no (nw_opNOPm nw_mZp),
  e_no (nw_opORA nw_mZp), e_md (w_opASL nw_mZp) o_Zp, e_md (w_opSLO nw_mZp) o_Zp, e_st w_opPHP, e_no (nw_opORA nw_mImm), e_no (nw_accOp nw_aslV), e_no nw_opJAM,
  e_no (nw_opNOPm nw_mAbs), e_no (nw_opORA nw_mAbs), e_md (w_opASL nw_mAbs) o_Abs, e_md (w_opSLO nw_mAbs) o_Abs, trivial⟩
theorem a_row1 : AllW w1 row1 := ⟨e_no nw_opBPL, e_no (nw_opORA nw_mIzyR), e_no nw_opJAM, e_md (w_opSLO nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opORA nw_mZpx), e_md (w_opASL nw_mZpx) o_Zpx, e_md (w_opSLO nw_mZpx) o_Zpx, e_no nw_opCLC, e_no (nw_opORA nw_mAbyR), e_no nw_opNOP,
  e_md (w_opSLO nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opORA nw_mAbxR), e_md (w_opASL nw_mAbx) o_Abx, e_md (w_opSLO nw_mAbx) o_Abx, trivial⟩
theorem a_row2 : AllW w2 row2 := ⟨e_st w_opJSR, e_no (nw_opAND nw_mIzx), e_no nw_opJAM, e_md (w_opRLA nw_mIzx) o_Izx, e_no (nw_opBIT nw_mZp),
  e_no (nw_opAND nw_mZp), e_md (w_opROL nw_mZp) o_Zp, e_md (w_opRLA nw_mZp) o_Zp, e_no nw_opPLP, e_no (nw_opAND nw_mImm), e_no (nw_accOp nw_rolV), e_no nw_opJAM,
  e_no (nw_opBIT nw_mAbs), e_no (nw_opAND nw_mAbs), e_md (w_opROL nw_mAbs) o_Abs, e_md (w_opRLA nw_mAbs) o_Abs, trivial⟩
theorem a_row3 : AllW w1 row3 := ⟨e_no nw_opBMI, e_no (nw_opAND nw_mIzyR), e_no nw_opJAM, e_md (w_opRLA nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opAND nw_mZpx), e_md (w_opROL nw_mZpx) o_Zpx, e_md (w_opRLA nw_mZpx) o_Zpx, e_no nw_opSEC, e_no (nw_opAND nw_mAbyR), e_no nw_opNOP,
  e_md (w_opRLA nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opAND nw_mAbxR), e_md (w_opROL nw_mAbx) o_Abx, e_md (w_opRLA nw_mAbx) o_Abx, trivial⟩
theorem a_row4 : AllW w4 row4 := ⟨e_no nw_opRTI, e_no (nw_opEOR nw_mIzx), e_no nw_opJAM, e_md (w_opSRE nw_mIzx) o_Izx, e_no (nw_opNOPm nw_mZp),
  e_no (nw_opEOR nw_mZp), e_md (w_opLSR nw_mZp) o_Zp, e_md (w_opSRE nw_mZp) o_Zp, e_st w_opPHA, e_no (nw_opEOR nw_mImm), e_no (nw_accOp nw_lsrV), e_no nw_opJAM,
  e_no nw_opJMP, e_no (nw_opEOR nw_mAbs), e_md (w_opLSR nw_mAbs) o_Abs, e_md (w_opSRE nw_mAbs) o_Abs, trivial⟩
theorem a_row5 : AllW w1 row5 := ⟨e_no nw_opBVC, e_no (nw_opEOR nw_mIzyR), e_no nw_opJAM, e_md (w_opSRE nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opEOR nw_mZpx), e_md (w_opLSR nw_mZpx) o_Zpx, e_md (w_opSRE nw_mZpx) o_Zpx, e_no nw_opCLI, e_no (nw_opEOR nw_mAbyR), e_no nw_opNOP,
  e_md (w_opSRE nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opEOR nw_mAbxR), e_md (w_opLSR nw_mAbx) o_Abx, e_md (w_opSRE nw_mAbx) o_Abx, trivial⟩
theorem a_row6 : AllW w6 row6 := ⟨e_no nw_opRTS, e_no (nw_opADC nw_mIzx), e_no nw_opJAM, e_md (w_opRRA nw_mIzx) o_Izx, e_no (nw_opNOPm nw_mZp),
  e_no (nw_opADC nw_mZp), e_md (w_opROR nw_mZp) o_Zp, e_md (w_opRRA nw_mZp) o_Zp, e_no nw_opPLA, e_no (nw_opADC nw_mImm), e_no (nw_accOp nw_rorV), e_no nw_opJAM,
  e_no nw_opJMPi, e_no (nw_opADC nw_mAbs), e_md (w_opROR nw_mAbs) o_Abs, e_md (w_opRRA nw_mAbs) o_Abs, trivial⟩
theorem a_row7 : AllW w1 row7 := ⟨e_no nw_opBVS, e_no (nw_opADC nw_mIzyR), e_no nw_opJAM, e_md (w_opRRA nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opADC nw_mZpx), e_md (w_opROR nw_mZpx) o_Zpx, e_md (w_opRRA nw_mZpx) o_Zpx, e_no nw_opSEI, e_no (nw_opADC nw_mAbyR), e_no nw_opNOP,
  e_md (w_opRRA nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opADC nw_mAbxR), e_md (w_opROR nw_mAbx) o_Abx, e_md (w_opRRA nw_mAbx) o_Abx, trivial⟩
theorem a_row8 : AllW w8 row8 := ⟨e_no (nw_opNOPm nw_mImm), e_md (w_opSTA nw_mIzx) o_Izx, e_no (nw_opNOPm nw_mImm), e_md (w_opSAX nw_mIzx) o_Izx,
  e_md (w_opSTY nw_mZp) o_Zp, e_md (w_opSTA nw_mZp) o_Zp, e_md (w_opSTX nw_mZp) o_Zp, e_md (w_opSAX nw_mZp) o_Zp, e_no nw_opDEY, e_no (nw_opNOPm nw_mImm),
  e_no nw_opTXA, e_no nw_opJAM, e_md (w_opSTY nw_mAbs) o_Abs, e_md (w_opSTA nw_mAbs) o_Abs, e_md (w_opSTX nw_mAbs) o_Abs, e_md (w_opSAX nw_mAbs) o_Abs, trivial⟩
theorem a_row9 : AllW w9 row9 := ⟨e_no nw_opBCC, e_md (w_opSTA nw_mIzy) o_Izy, e_no nw_opJAM, e_no nw_opJAM, e_md (w_opSTY nw_mZpx) o_Zpx,
  e_md (w_opSTA nw_mZpx) o_Zpx, e_md (w_opSTX nw_mZpy) o_Zpy, e_md (w_opSAX nw_mZpy) o_Zpy, e_no nw_opTYA, e_md (w_opSTA nw_mAby) o_Aby, e_no nw_opTXS,
  e_no nw_opJAM, e_no nw_opJAM, e_md (w_opSTA nw_mAbx) o_Abx, e_no nw_opJAM, e_no nw_opJAM, trivial⟩
theorem a_rowA : AllW wA rowA := ⟨e_no (nw_opLDY nw_mImm), e_no (nw_opLDA nw_mIzx), e_no (nw_opLDX nw_mImm), e_no (nw_opLAX nw_mIzx), e_no (nw_opLDY nw_mZp),
  e_no (nw_opLDA nw_mZp), e_no (nw_opLDX nw_mZp), e_no (nw_opLAX nw_mZp), e_no nw_opTAY, e_no (nw_opLDA nw_mImm), e_no nw_opTAX, e_no nw_opJAM,
  e_no (nw_opLDY nw_mAbs), e_no (nw_opLDA nw_mAbs), e_no (nw_opLDX nw_mAbs), e_no (nw_opLAX nw_mAbs), trivial⟩
theorem a_rowB : AllW wA rowB := ⟨e_no nw_opBCS, e_no (nw_opLDA nw_mIzyR), e_no nw_opJAM, e_no (nw_opLAX nw_mIzyR), e_no (nw_opLDY nw_mZpx),
  e_no (nw_opLDA nw_mZpx), e_no (nw_opLDX nw_mZpy), e_no (nw_opLAX nw_mZpy), e_no nw_opCLV, e_no (nw_opLDA nw_mAbyR), e_no nw_opTSX, e_no nw_opJAM,
  e_no (nw_opLDY nw_mAbxR), e_no (nw_opLDA nw_mAbxR), e_no (nw_opLDX nw_mAbyR), e_no (nw_opLAX nw_mAbyR), trivial⟩
theorem a_rowC : AllW w6 rowC := ⟨e_no (nw_opCPY nw_mImm), e_no (nw_opCMP nw_mIzx), e_no (nw_opNOPm nw_mImm), e_md (w_opDCP nw_mIzx) o_Izx,
  e_no (nw_opCPY nw_mZp), e_no (nw_opCMP nw_mZp), e_md (w_opDEC nw_mZp) o_Zp, e_md (w_opDCP nw_mZp) o_Zp, e_no nw_opINY, e_no (nw_opCMP nw_mImm), e_no nw_opDEX,
  e_no nw_opJAM, e_no (nw_opCPY nw_mAbs), e_no (nw_opCMP nw_mAbs), e_md (w_opDEC nw_mAbs) o_Abs, e_md (w_opDCP nw_mAbs) o_Abs, trivial⟩
theorem a_rowD : AllW w1 rowD := ⟨e_no nw_opBNE, e_no (nw_opCMP nw_mIzyR), e_no nw_opJAM, e_md (w_opDCP nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opCMP nw_mZpx), e_md (w_opDEC nw_mZpx) o_Zpx, e_md (w_opDCP nw_mZpx) o_Zpx, e_no nw_opCLD, e_no (nw_opCMP nw_mAbyR), e_no nw_opNOP,
  e_md (w_opDCP nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opCMP nw_mAbxR), e_md (w_opDEC nw_mAbx) o_Abx, e_md (w_opDCP nw_mAbx) o_Abx, trivial⟩
theorem a_rowE : AllW w6 rowE := ⟨e_no (nw_opCPX nw_mImm), e_no (nw_opSBC nw_mIzx), e_no (nw_opNOPm nw_mImm), e_md (w_opISB nw_mIzx) o_Izx,
  e_no (nw_opCPX nw_mZp), e_no (nw_opSBC nw_mZp), e_md (w_opINC nw_mZp) o_Zp, e_md (w_opISB nw_mZp) o_Zp, e_no nw_opINX, e_no (nw_opSBC nw_mImm), e_no nw_opNOP,
  e_no (nw_opSBC nw_mImm), e_no (nw_opCPX nw_mAbs), e_no (nw_opSBC nw_mAbs), e_md (w_opINC nw_mAbs) o_Abs, e_md (w_opISB nw_mAbs) o_Abs, trivial⟩
theorem a_rowF : AllW w1 rowF := ⟨e_no nw_opBEQ, e_no (nw_opSBC nw_mIzyR), e_no nw_opJAM, e_md (w_opISB nw_mIzy) o_Izy, e_no (nw_opNOPm nw_mZpx),
  e_no (nw_opSBC nw_mZpx), e_md (w_opINC nw_mZpx) o_Zpx, e_md (w_opISB nw_mZpx) o_Zpx, e_no nw_opSED, e_no (nw_opSBC nw_mAbyR), e_no nw_opNOP,
  e_md (w_opISB nw_mAby) o_Aby, e_no (nw_opNOPm nw_mAbxR), e_no (nw_opSBC nw_mAbxR), e_md (w_opINC nw_mAbx) o_Abx, e_md (w_opISB nw_mAbx) o_Abx, trivial⟩

theorem a_all : AllW wRows allRows :=
  AllW.append a_row0 (AllW.append a_row1 (AllW.append a_row2 (AllW.append a_row3 (AllW.append a_row4 (AllW.append a_row5 (AllW.append a_row6
    (AllW.append a_row7 (AllW.append a_row8 (AllW.append a_row9 (AllW.append a_rowA (AllW.append a_rowB (AllW.append a_rowC (AllW.append a_rowD
    (AllW.append a_rowE a_rowF))))))))))))))

/-- the entry of an opcode -/
def wOf (op : UInt8) : Wr := wRows[op.toNat]?.getD .no

theorem w_op (op : UInt8) : WrIn (wOf op).locs (opTable[op.toNat]?.getD opJAM) ∧ (wOf op).ok := by
  rw [opTable_eq, List.getElem?_toArray]
  exact a_all.get op.toNat

/-! ## One step -/

/-- **The RAM indices that one step of `m` may write.** The NMI pushes three bytes; a halted machine writes nothing; else the instruction writes as its entry in the table says,
from the machine after its opcode. -/
def stepLocs (m : Machine) : List Nat :=
  if m.nmiPending then stk m.s 3
  else if m.halted then []
  else (wOf (go fetch m).1).locs (go fetch m).2

/-- **One step changes RAM only at `stepLocs`.** -/
theorem step_ram (m : Machine) (i : Nat) (hi : i ∉ stepLocs m) : (go step m).2.ram.get! i = m.ram.get! i := by
  unfold stepLocs at hi
  by_cases hn : m.nmiPending = true
  · rw [if_pos hn] at hi
    rw [TaintRun.step_nmi hn]
    exact w_nmi m i hi
  · rw [if_neg hn] at hi
    by_cases hh : m.halted = true
    · have e : go step m = ((), m) := by
        unfold step go
        show (if m.nmiPending = true then nmi else if m.halted = true then _ else _) m = _
        rw [if_neg hn, if_pos hh]
        rfl
      rw [e]
    · rw [if_neg hh] at hi
      have e : go step m = go (fetch >>= fun op => TaintRun.stepK m m.pc op) m := by
        unfold step go
        show (if m.nmiPending = true then nmi else if m.halted = true then _ else _) m = _
        rw [if_neg hn, if_neg hh]
        rfl
      rw [e, go_bind]
      unfold TaintRun.stepK
      split
      · rw [(NoWr.bind (nw_setPC _) fun _ => NoWr.ofLeaf (leaf_tick _)) _, nw_fetch m]
      · rw [(WrIn.then_nw (w_op _).1 fun _ => NoWr.ofLeaf (leaf_tick _)) _ i hi, nw_fetch m]

/-- **Along the instructions of a frame**, a byte that no step writes keeps the value it has when the frame begins. -/
theorem trace_ram {m : Machine} {inp : UInt8} {i : Nat} :
    ∀ (n : Nat), (∀ k, k < n → i ∉ stepLocs (PipeEntryRule.trace m inp k)) → (PipeEntryRule.trace m inp n).ram.get! i = m.ram.get! i
  | 0, _ => rfl
  | n + 1, h => by
    have ih := trace_ram n (fun k hk => h k (by omega))
    show (PipeEntryRule.nxt (m.frame + 1) (PipeEntryRule.trace m inp n)).ram.get! i = _
    unfold PipeEntryRule.nxt
    split
    · exact ih
    · rw [step_ram _ i (h n (by omega))]
      exact ih

/-! ## What an abstract state knows of the writes -/

/-- every address of the interval that is in RAM has a RAM index outside `P` -/
def adAvoid (P : Nat → Bool) (ad : AAd) : Bool :=
  decide (ad.lo ≤ ad.hi) && (decide (0x2000 ≤ ad.lo) || (List.range ((ad.hi - ad.lo).toNat + 1)).all fun j => !P ((ad.lo + j.toUInt16) &&& 0x7FF).toNat)

theorem adAvoid_ok {P : Nat → Bool} {ad : AAd} {addr : UInt16} (h : adAvoid P ad = true) (ha : AdR ad addr) : ∀ i ∈ ramIdx addr, P i = false := by
  intro i hi
  simp only [adAvoid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨hle, h2⟩ := h
  rcases ha with ⟨_, a1, a2⟩ | ⟨a1, _⟩
  · unfold ramIdx at hi
    split at hi
    · rename_i hlt
      simp only [List.mem_singleton] at hi
      subst hi
      rcases h2 with h2 | h2
      · exfalso
        have b1 := UInt16.le_iff_toNat_le.1 h2
        have b2 := UInt16.le_iff_toNat_le.1 a1
        have b3 := UInt16.lt_iff_toNat_lt.1 hlt
        simp at b1 b3
        omega
      · have b1 := UInt16.le_iff_toNat_le.1 a1
        have b2 := UInt16.le_iff_toNat_le.1 a2
        have b3 := UInt16.le_iff_toNat_le.1 hle
        have hsub : (ad.hi - ad.lo).toNat = ad.hi.toNat - ad.lo.toNat := UInt16.toNat_sub_of_le _ _ hle
        have := h2 (addr.toNat - ad.lo.toNat) (by rw [hsub]; omega)
        rw [TaintRun.offset_of_le a1] at this
        exact this
    · simp at hi
  · exact absurd hle (by
      intro h3
      have b1 := UInt16.le_iff_toNat_le.1 h3
      have b2 := UInt16.lt_iff_toNat_lt.1 a1
      omega)

/-- **The step of `A` writes no RAM index of `P`**, as far as `A` says: an NMI pushes outside `P`; else the instruction is in the ROM, and it pushes outside `P`, or its
abstract mode gives addresses outside `P`, or it does not write -/
def keepOK (E : Env) (P : Nat → Bool) (A : AS) : Bool :=
  if A.nmi then (stk A.s 3).all (fun i => !P i)
  else if A.pc < 0x8000 then false
  else match wOf (E.prg.get! (A.pc &&& E.mask).toNat) with
    | .no => true
    | .st k => (stk A.s k).all (fun i => !P i)
    | .md _ a => match a E { A with pc := A.pc + 1 } with
      | some (ad, _) => adAvoid P ad
      | none => false

/-- **A machine that `A` covers keeps the bytes of `P` over one step**, if `keepOK` holds -/
theorem keep_step {E : Env} {F : Nat × UInt8} {P : Nat → Bool} {A : AS} {m : Machine} (hs : Sim E F A m) (hk : keepOK E P A = true) :
    ∀ i, P i = true → (go step m).2.ram.get! i = m.ram.get! i := by
  intro i hP
  apply step_ram
  intro hi
  unfold keepOK at hk
  unfold stepLocs at hi
  by_cases hn : A.nmi = true
  · rw [if_pos hn] at hk
    have hn' : m.nmiPending = true := by rw [hs.nmi]; exact hn
    rw [if_pos hn', hs.s] at hi
    have := List.all_eq_true.1 hk i hi
    simp [hP] at this
  · rw [if_neg hn] at hk
    have hn' : m.nmiPending = false := by rw [hs.nmi]; simpa using hn
    rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted])] at hi
    by_cases hp : A.pc < 0x8000
    · rw [if_pos hp] at hk
      cases hk
    · rw [if_neg hp] at hk
      have hpm : m.pc ≥ 0x8000 := by
        rw [hs.pc]
        have a1 : ¬ A.pc.toNat < (0x8000 : UInt16).toNat := fun h => hp (UInt16.lt_iff_toNat_lt.2 h)
        exact UInt16.le_iff_toNat_le.2 (by omega)
      rw [TaintRun.fetch_rom hpm] at hi
      have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = E.prg.get! (A.pc &&& E.mask).toNat := by rw [hs.prg, hs.mask, hs.pc]
      rw [hop] at hi
      have hok := (w_op (E.prg.get! (A.pc &&& E.mask).toNat)).2
      generalize wOf (E.prg.get! (A.pc &&& E.mask).toNat) = w at hi hk hok
      cases w with
      | no => simp [Wr.locs] at hi
      | st k =>
        simp only [Wr.locs] at hi
        have h1 : i ∈ stk A.s k := by
          rw [← hs.s]
          exact hi
        have := List.all_eq_true.1 hk i h1
        simp [hP] at this
      | md c a =>
        simp only [Wr.locs] at hi
        simp only at hk
        have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
          pc := by
            show m.pc + 1 = A.pc + 1
            rw [hs.pc] }
        cases ha : a E { A with pc := A.pc + 1 } with
        | none =>
          rw [ha] at hk
          cases hk
        | some p =>
          obtain ⟨ad, A'⟩ := p
          rw [ha] at hk
          obtain ⟨hr, _, _⟩ := hok E F _ _ hs1 ad A' ha
          have := adAvoid_ok hk hr i hi
          rw [hP] at this
          cases this

/-! ## A frame, with something that the abstract states do not hold

`xwalk` of `SideChangeEnd`, with a test `ok` on every state on the way. If every step from a machine that a state with `ok` covers keeps a property `Inv` of machines,
the frame keeps it (`kframe_of_walk`). With `Inv` "the bytes of `P` have their values at the start" and `ok := keepOK E P`, the frame writes no byte of `P` (`keep_frame`). -/

open SideChangeEnd (xsuccs s_xsuccs)
open TaintRun (Cfg coverIn sim_le)

/-- from `A`, step by step as `xwalk`, and every state on the way meets `ok` -/
def kwalk (C : Cfg) (fin ok : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => ok A && (xsuccs C.E C.ops A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverIn C B) || kwalk C fin ok n B
      else B.k == A.k + 1 && fin B

section
variable {C : Cfg} {Fu : Nat} {F : Nat × UInt8} {fin ok : AS → Bool} {Inv : Machine → Prop}

def KLive (C : Cfg) (fin ok : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, kwalk C fin ok n A = true

theorem cover_klive (ht : C.t.all (kwalk C fin ok Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverIn C B = true) :
    ∃ D, KLive C fin ok F D m ∧ D.k = B.k := by
  unfold coverIn at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [TaintRun.AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

theorem klive_step (ht : C.t.all (kwalk C fin ok Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hinv : ∀ A m, Sim C.E F A m → ok A = true → Inv m → Inv (go step m).2) {A : AS} {m : Machine} (hl : KLive C fin ok F A m) (hI : Inv m) :
    Inv (go step m).2 ∧
    ((∃ A', KLive C fin ok F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2)) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [kwalk] at hw
  | succ n =>
    simp only [kwalk, Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨hok, hw⟩ := hw
    refine ⟨hinv A m hs hok hI, ?_⟩
    obtain ⟨r, hr, hB⟩ := s_xsuccs hops hT hs
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_klive ht h1 h3
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

theorem kframe_run (ht : C.t.all (kwalk C fin ok Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hinv : ∀ A m, Sim C.E F A m → ok A = true → Inv m → Inv (go step m).2) {f : Nat} :
    ∀ (n : Nat) (A : AS) (m : Machine), KLive C fin ok F A m → Inv m → m.frame = f → dotsPerFrame ≤ m.fdot + 3 * n →
      (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧ Inv (go (runUntilFrame (f + 1) n) m).2 ∧
        ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 := by
  intro n
  induction n with
  | zero =>
    intro A m hl _ _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro A m hl hI hf hd
    have hh := hl.1.halted
    rw [PipeTransitionAll.ruf_eq, if_neg (by simp [hf, hh])]
    obtain ⟨hI', hc⟩ := klive_step ht hops hT hinv hl hI
    rcases hc with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
    · have := ih A' _ h1 hI' (h3.trans hf) (by omega)
      rw [h2] at this
      exact this
    · rw [TaintRun.ruf_doneF (by rw [h1, hf]; exact Nat.le_refl _) n]
      exact ⟨by rw [h1, hf], hI', B, h2, h3, h4⟩

/-- **One frame, with an invariant outside the abstract state.** A walk from `S` with `ok` on every state covers the frame of a machine of `S`, and `Inv` holds at the
frame's end if it holds at its start and every step from a covered state with `ok` keeps it. -/
theorem kframe_of_walk (ht : C.t.all (kwalk C fin ok Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hinv : ∀ A m, Sim C.E F A m → ok A = true → Inv m → Inv (go step m).2)
    {S : AS} {m : Machine} {i : UInt8} (hw : kwalk C fin ok Fu S = true) (hs : Sim C.E F S { m with pad := smbToPad i }) (hI : Inv { m with pad := smbToPad i }) :
    (PipeTransition.frame m i).frame = m.frame + 1 ∧ Inv (PipeTransition.frame m i) ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (PipeTransition.frame m i) := by
  rw [PipeTransitionAll.frame_eq]
  have hf : dotsPerFrame ≤ ({ m with pad := smbToPad i } : Machine).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  exact kframe_run ht hops hT hinv (f := m.frame) fuelPerFrame S _ ⟨hs, Fu, hw⟩ hI rfl hf

/-- **A frame writes no byte of `P`**, if every state of the walk meets `keepOK` -/
theorem keep_frame {P : Nat → Bool} (ht : C.t.all (kwalk C fin (keepOK C.E P) Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {S : AS} {m : Machine} {i : UInt8} (hw : kwalk C fin (keepOK C.E P) Fu S = true) (hs : Sim C.E F S { m with pad := smbToPad i }) :
    (∀ j, P j = true → (PipeTransition.frame m i).ram.get! j = m.ram.get! j) ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (PipeTransition.frame m i) := by
  have h := kframe_of_walk (Inv := fun x => ∀ j, P j = true → x.ram.get! j = m.ram.get! j) ht hops hT
    (fun A x hsx hok hx j hj => by rw [keep_step hsx hok j hj]; exact hx j hj) hw hs (fun _ _ => rfl)
  exact ⟨h.2.1, h.2.2⟩

end

/-! ## A routine split by a table of states, and forgotten after its return

The rows of a change know the game's bytes, not the sound's. The fact "the sound's bytes are one of a table's states" is carried outside the abstract states (`Ph`).
At the call of the routine the state is split into one piece for each state of the table, and each piece walks through the routine with the sound's bytes known.
At the return the walk checks that the bytes are in a state of a second table, and forgets them. Outside the routine every step keeps the sound's bytes (`keepOK`), or
writes some of them and every state of the table, so written, is in a state of the table (`writeOK`). The bit `spent` of a state, which nothing reads when `rk` is false,
says whether the routine has returned on this frame: before, the first table holds; after, the second. `tsuccs` is this step, `twalk` the walk with it, and
`tframe_of_walk` the frame. A state of a table is a list of bytes with what is known of each. There is no game data here. -/

/-- where a routine is: the bytes it may change, the call's place, the return's place, its code -/
structure Rt where
  SB : List Nat
  call : UInt16
  ret : UInt16
  inR : UInt16 → Bool

/-- a state of a table: bytes, with what is known of each -/
abbrev SState := List (Nat × AB)

/-- the bytes of `m` are in the state `t` -/
def SIn (t : SState) (m : Machine) : Prop := ∀ p ∈ t, p.2.mem (m.ram.get! p.1)

/-- every machine in `u` is in `t` -/
def entails (u t : SState) : Bool := t.all fun q => u.any fun p => p.1 == q.1 && p.2.le q.2

/-- the bytes of the table's states are bytes of the routine, in RAM -/
def tabOK (SB : List Nat) (T : List SState) : Bool := T.all fun t => t.all fun p => SB.contains p.1 && decide (p.1 < 2048)

/-- both: the bits known in either -/
def abMeet (a b : AB) : AB := ⟨(a.v &&& a.k) ||| (b.v &&& b.k), a.k ||| b.k⟩

/-- the two agree on the bits that both know -/
def abAgree (a b : AB) : Bool := (a.v ^^^ b.v) &&& a.k &&& b.k == 0

/-- the piece of `A` with the bytes of `t` -/
def refineAll (t : SState) (A : AS) : AS := t.foldl (fun A p => A.setK p.1 (abMeet (A.getK p.1) p.2)) A

/-- `A` and `t` agree on every byte of `t` -/
def agrees (t : SState) (A : AS) : Bool := t.all fun p => abAgree (A.getK p.1) p.2

/-- `A` without the bytes -/
def forgetAll (SB : List Nat) (A : AS) : AS := SB.foldl (fun A i => A.setK i TaintRun.AB.top) A

/-- what `B` knows of the bytes is in `t` -/
def soundLe (B : AS) (t : SState) : Bool := t.all fun q => decide (q.1 < 2048) && (B.getK q.1).le q.2

/-- the state with `rk` off and the bit `s` -/
def retag (s : Bool) (B : AS) : AS := { B with rk := false, spent := s }

/-- the RAM indices that the step of `A` may write, as far as `A` says -/
def aLocs (E : Env) (A : AS) : Option (List Nat) :=
  if A.nmi then some (stk A.s 3)
  else if A.pc < 0x8000 then none
  else match wOf (E.prg.get! (A.pc &&& E.mask).toNat) with
    | .no => some []
    | .st k => some (stk A.s k)
    | .md _ a => match a E { A with pc := A.pc + 1 } with
      | some (ad, _) => if ad.lo == ad.hi then some (ramIdx ad.lo) else if adAvoid (fun _ => true) ad then some [] else none
      | none => none

/-- `t` after a step that writes the RAM indices `L`, with what `B` knows of the written bytes -/
def updAt (SB L : List Nat) (B : AS) (t : SState) : SState :=
  t.filter (fun p => !L.contains p.1) ++ ((L.filter fun i => SB.contains i && decide (i < 2048)).map fun i => (i, B.getK i))

/-- a step that may write some of the bytes: every state of the table, so written, is in a state of the table -/
def writeOK (E : Env) (SB : List Nat) (T : List SState) (A B : AS) : Bool :=
  match aLocs E A with
  | some L => T.all fun t => T.any fun t' => entails (updAt SB L B t) t'
  | none => false

/-- a successor in the routine: at the return, the check and the forgetting -/
def inStep (R : Rt) (T1 : List SState) (A B : AS) : Option AS :=
  if B.pc == R.ret && B.k == A.k then (if T1.any (soundLe B) then some (retag true (forgetAll R.SB B)) else none)
  else if R.inR B.pc then some (retag A.spent B) else none

/-- a successor outside the routine: the step keeps the bytes or writes them as `writeOK` says -/
def outStep (E : Env) (R : Rt) (T : List SState) (A B : AS) : Option AS :=
  if keepOK E (fun i => R.SB.contains i) A || writeOK E R.SB T A B then some (retag A.spent B) else none

/-- **The step with the routine split and forgotten.** In the routine: the plain step, and at the return the check and the forgetting. At the call: the pieces of the first
table. Elsewhere: the plain step, which must keep the bytes or write them as `writeOK` says. -/
def tsuccs (E : Env) (ops : Array (AM Unit)) (R : Rt) (T0 T1 : List SState) (A : AS) : List (Option AS) :=
  if R.inR A.pc then (SideChangeEnd.xsuccs E ops A).map fun o => o.bind (inStep R T1 A)
  else if A.pc == R.call then
    if A.spent || !keepOK E (fun i => R.SB.contains i) A then [none]
    else T0.flatMap fun t => if agrees t A then (SideChangeEnd.xsuccs E ops (refineAll t A)).map fun o => o.map (retag false) else []
  else (SideChangeEnd.xsuccs E ops A).map fun o => o.bind (outStep E R (if A.spent then T1 else T0) A)

/-- the routine's bytes are in a state of the first table before the return, of the second after it; in the routine nothing is asked -/
def Ph (R : Rt) (T0 T1 : List SState) (A : AS) (m : Machine) : Prop :=
  R.inR A.pc = true ∨ (A.spent = false ∧ ∃ t ∈ T0, SIn t m) ∨ (A.spent = true ∧ ∃ t ∈ T1, SIn t m)

section
variable {E : Env} {F : Nat × UInt8}

theorem sim_retag (s : Bool) {B : AS} {m : Machine} (hs : Sim E F B m) : Sim E F (retag s B) m :=
  { hs with rkv := fun h => by cases h }

theorem refineAll_k : ∀ (t : SState) (A : AS), (refineAll t A).k = A.k
  | [], _ => rfl
  | p :: l, A => refineAll_k l (A.setK p.1 (abMeet (A.getK p.1) p.2))

theorem forgetAll_k : ∀ (SB : List Nat) (A : AS), (forgetAll SB A).k = A.k
  | [], _ => rfl
  | i :: l, A => forgetAll_k l (A.setK i TaintRun.AB.top)

theorem stepRel_k {A A' B B' : AS} {m m' : Machine} (ha : A'.k = A.k) (hb : B'.k = B.k) (h : TaintRun.StepRel A B m m') : TaintRun.StepRel A' B' m m' := by
  unfold TaintRun.StepRel at h ⊢
  rw [ha, hb]
  exact h

theorem inStep_some {R : Rt} {T1 : List SState} {A B C : AS} (h : inStep R T1 A B = some C) :
    (B.pc = R.ret ∧ C = retag true (forgetAll R.SB B) ∧ ∃ t ∈ T1, soundLe B t = true) ∨ (R.inR B.pc = true ∧ C = retag A.spent B) := by
  unfold inStep at h
  split at h
  · split at h
    · rename_i h1 h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      simp only [Option.some.injEq] at h
      obtain ⟨t, ht, hl⟩ := List.any_eq_true.1 h2
      exact Or.inl ⟨h1.1, h.symm, t, ht, hl⟩
    · cases h
  · split at h
    · rename_i _ h2
      simp only [Option.some.injEq] at h
      exact Or.inr ⟨h2, h.symm⟩
    · cases h

theorem outStep_some {E : Env} {R : Rt} {T : List SState} {A B C : AS} (h : outStep E R T A B = some C) :
    C = retag A.spent B ∧ (keepOK E (fun i => R.SB.contains i) A = true ∨ writeOK E R.SB T A B = true) := by
  unfold outStep at h
  split at h
  · rename_i h1
    simp only [Option.some.injEq] at h
    simp only [Bool.or_eq_true] at h1
    exact ⟨h.symm, h1⟩
  · cases h

theorem mem_meet {a b : AB} {x : UInt8} (h1 : a.mem x) (h2 : b.mem x) : (abMeet a b).mem x := by
  refine TaintRun.mem_iff.2 fun i hi => ?_
  have a1 := TaintRun.mem_iff.1 h1 i hi
  have a2 := TaintRun.mem_iff.1 h2 i hi
  simp only [abMeet, TaintRun.bt_and, TaintRun.bt_or]
  revert a1 a2
  generalize TaintRun.bt x i = p, TaintRun.bt a.v i = r, TaintRun.bt a.k i = s, TaintRun.bt b.v i = t, TaintRun.bt b.k i = u
  revert p r s t u
  decide

theorem agree_of_mem {a b : AB} {x : UInt8} (h1 : a.mem x) (h2 : b.mem x) : abAgree a b = true := by
  simp only [abAgree, beq_iff_eq]
  apply TaintRun.bt_ext
  intro i hi
  have a1 := TaintRun.mem_iff.1 h1 i hi
  have a2 := TaintRun.mem_iff.1 h2 i hi
  simp only [TaintRun.bt_and, TaintRun.bt_xor, TaintRun.bt_zero hi]
  revert a1 a2
  generalize TaintRun.bt x i = p, TaintRun.bt a.v i = r, TaintRun.bt a.k i = s, TaintRun.bt b.v i = t, TaintRun.bt b.k i = u
  revert p r s t u
  decide

theorem sim_refineAll {m : Machine} : ∀ (t : SState) {A : AS}, Sim E F A m → SIn t m → Sim E F (refineAll t A) m := by
  intro t
  induction t with
  | nil => intro A hs _; exact hs
  | cons p l ih =>
    intro A hs ht
    have h1 : p.2.mem (m.ram.get! p.1) := ht p (by simp)
    have h2 : SIn l m := fun q hq => ht q (by simp [hq])
    have h0 : (A.getK p.1).mem (m.ram.get! p.1) := by
      by_cases hi : p.1 < 2048
      · exact hs.ram p.1 hi
      · have e1 : A.ram.get! p.1 = default := by
          simp only [ByteArray.get!, getElem!_def]
          rw [Array.getElem?_eq_none (by rw [← ByteArray.size, hs.szR]; omega)]
        have e2 : A.kn.get! p.1 = default := by
          simp only [ByteArray.get!, getElem!_def]
          rw [Array.getElem?_eq_none (by rw [← ByteArray.size, hs.szK]; omega)]
        show TaintRun.AB.mem ⟨A.ram.get! p.1, A.kn.get! p.1⟩ _
        rw [e1, e2]
        exact TaintRun.mem_top _
    exact ih (SideChangeEnd.sim_refine hs (mem_meet h0 h1)) h2

theorem agrees_of {A : AS} {m : Machine} (hs : Sim E F A m) {t : SState} (hi : ∀ p ∈ t, p.1 < 2048) (ht : SIn t m) : agrees t A = true :=
  List.all_eq_true.2 fun p hp => agree_of_mem (hs.ram p.1 (hi p hp)) (ht p hp)

theorem sim_forgetAll (SB : List Nat) {m : Machine} : ∀ {A : AS}, Sim E F A m → Sim E F (forgetAll SB A) m := by
  induction SB with
  | nil => intro A hs; exact hs
  | cons i l ih =>
    intro A hs
    exact ih (SideChangeEnd.sim_refine hs (TaintRun.mem_top _))

theorem sIn_entails {u t : SState} {m : Machine} (hu : SIn u m) (h : entails u t = true) : SIn t m := by
  intro q hq
  obtain ⟨p, hp, h2⟩ := List.any_eq_true.1 (List.all_eq_true.1 h q hq)
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  rw [← h2.1]
  exact TaintRun.le_mem h2.2 (hu p hp)

theorem sIn_of_le {B : AS} {m : Machine} (hs : Sim E F B m) {t : SState} (h : soundLe B t = true) : SIn t m := by
  intro q hq
  have h1 := List.all_eq_true.1 h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact TaintRun.le_mem h1.2 (hs.ram q.1 h1.1)

/-- the step keeps the bytes of the table's states -/
theorem sIn_keep {SB : List Nat} {t : SState} (ht : ∀ p ∈ t, SB.contains p.1 = true) {m m' : Machine} (h : SIn t m)
    (hk : ∀ i, SB.contains i = true → m'.ram.get! i = m.ram.get! i) : SIn t m' := by
  intro p hp
  rw [hk p.1 (ht p hp)]
  exact h p hp

/-- `aLocs` holds what the step writes -/
theorem aLocs_ok {A : AS} {m : Machine} (hs : Sim E F A m) {L : List Nat} (hL : aLocs E A = some L) : ∀ i, i ∉ L → (go step m).2.ram.get! i = m.ram.get! i := by
  intro i hi
  apply step_ram
  intro hm
  unfold aLocs at hL
  unfold stepLocs at hm
  by_cases hn : A.nmi = true
  · rw [if_pos hn] at hL
    have hn' : m.nmiPending = true := by rw [hs.nmi]; exact hn
    rw [if_pos hn', hs.s] at hm
    cases hL
    exact hi hm
  · rw [if_neg hn] at hL
    have hn' : m.nmiPending = false := by rw [hs.nmi]; simpa using hn
    rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted])] at hm
    by_cases hp : A.pc < 0x8000
    · rw [if_pos hp] at hL
      cases hL
    · rw [if_neg hp] at hL
      have hpm : m.pc ≥ 0x8000 := by
        rw [hs.pc]
        have a1 : ¬ A.pc.toNat < (0x8000 : UInt16).toNat := fun h => hp (UInt16.lt_iff_toNat_lt.2 h)
        exact UInt16.le_iff_toNat_le.2 (by omega)
      rw [TaintRun.fetch_rom hpm] at hm
      have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = E.prg.get! (A.pc &&& E.mask).toNat := by rw [hs.prg, hs.mask, hs.pc]
      rw [hop] at hm
      have hok := (w_op (E.prg.get! (A.pc &&& E.mask).toNat)).2
      generalize wOf (E.prg.get! (A.pc &&& E.mask).toNat) = w at hm hL hok
      cases w with
      | no => simp [Wr.locs] at hm
      | st k =>
        simp only [Wr.locs] at hm
        simp only [Option.some.injEq] at hL
        subst hL
        rw [← hs.s] at hi
        exact hi hm
      | md c a =>
        simp only [Wr.locs] at hm
        simp only at hL
        have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
          pc := by
            show m.pc + 1 = A.pc + 1
            rw [hs.pc] }
        cases ha : a E { A with pc := A.pc + 1 } with
        | none =>
          rw [ha] at hL
          cases hL
        | some p =>
          obtain ⟨ad, A'⟩ := p
          rw [ha] at hL
          obtain ⟨hr, _, _⟩ := hok E F _ _ hs1 ad A' ha
          dsimp only at hL
          split at hL
          · rename_i he
            simp only [Option.some.injEq] at hL
            subst hL
            have he' : ad.lo = ad.hi := by simpa using he
            rw [TaintRun.adR_same hr he'] at hm
            exact hi hm
          · split at hL
            · rename_i hv
              have := adAvoid_ok hv hr i hm
              cases this
            · cases hL

/-- `writeOK`: the bytes after the step are in a state of the table -/
theorem sIn_write {SB : List Nat} {T : List SState} {A B : AS} {m : Machine} (hs : Sim E F A m) (hsB : Sim E F B (go step m).2)
    (hw : writeOK E SB T A B = true) {t : SState} (ht : t ∈ T) (hm : SIn t m) : ∃ t' ∈ T, SIn t' (go step m).2 := by
  unfold writeOK at hw
  cases hL : aLocs E A with
  | none => rw [hL] at hw; cases hw
  | some L =>
    rw [hL] at hw
    have h1 := List.all_eq_true.1 hw t ht
    obtain ⟨t', ht', h2⟩ := List.any_eq_true.1 h1
    refine ⟨t', ht', sIn_entails ?_ h2⟩
    intro p hp
    simp only [updAt, List.mem_append, List.mem_filter, List.mem_map] at hp
    rcases hp with ⟨hp1, hp2⟩ | ⟨i, ⟨_, hi⟩, rfl⟩
    · have hnot : p.1 ∉ L := by simpa using hp2
      rw [aLocs_ok hs hL p.1 hnot]
      exact hm p hp1
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hsB.ram i hi.2

variable {ops : Array (AM Unit)} {R : Rt} {T0 T1 : List SState}

/-- **One step**: `tsuccs` follows the machine, and `Ph` goes on -/
theorem s_tsuccs (hops : ops = (TaintRun.aRows E).toArray) (hT : 2 ≤ F.2.toNat) (h0 : tabOK R.SB T0 = true) (h1 : tabOK R.SB T1 = true)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hph : Ph R T0 T1 A m) :
    ∃ r ∈ tsuccs E ops R T0 T1 A, ∀ B, r = some B →
      Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 ∧ Ph R T0 T1 B (go step m).2 := by
  have tab : ∀ {T : List SState}, tabOK R.SB T = true → ∀ t ∈ T, ∀ p ∈ t, R.SB.contains p.1 = true := by
    intro T hT t ht p hp
    simp only [tabOK, List.all_eq_true, Bool.and_eq_true] at hT
    exact (hT t ht p hp).1
  unfold tsuccs
  by_cases hin : R.inR A.pc = true
  · rw [if_pos hin]
    obtain ⟨r, hr, hB⟩ := SideChangeEnd.s_xsuccs hops hT hs
    refine ⟨r.bind (inStep R T1 A), List.mem_map.2 ⟨r, hr, rfl⟩, fun B hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B0 =>
      obtain ⟨g1, g2⟩ := hB B0 rfl
      rcases inStep_some hB' with ⟨_, rfl, t, ht, hle⟩ | ⟨hin2, rfl⟩
      · exact ⟨sim_retag _ (sim_forgetAll _ g1), stepRel_k rfl (forgetAll_k _ _) g2, Or.inr (Or.inr ⟨rfl, t, ht, sIn_of_le g1 hle⟩)⟩
      · exact ⟨sim_retag _ g1, stepRel_k rfl rfl g2, Or.inl hin2⟩
  · rw [if_neg hin]
    by_cases hc : (A.pc == R.call) = true
    · rw [if_pos hc]
      by_cases hk : (A.spent || !keepOK E (fun i => R.SB.contains i) A) = true
      · rw [if_pos hk]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
      · rw [if_neg hk]
        simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or] at hk
        obtain ⟨hsp, hkp⟩ := hk
        have hsp' : A.spent = false := by simpa using hsp
        have hkp' : keepOK E (fun i => R.SB.contains i) A = true := by simpa using hkp
        obtain ⟨t, ht, htm⟩ : ∃ t ∈ T0, SIn t m := by
          rcases hph with h | ⟨_, h⟩ | ⟨h, _⟩
          · exact absurd h hin
          · exact h
          · rw [hsp'] at h; cases h
        obtain ⟨r, hr, hB⟩ := SideChangeEnd.s_xsuccs hops hT (sim_refineAll t hs htm)
        have hag : agrees t A = true := agrees_of hs (fun p hp => by
          simp only [tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0
          exact (h0 t ht p hp).2) htm
        refine ⟨r.map (retag false), List.mem_flatMap.2 ⟨t, ht, by rw [if_pos hag]; exact List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
        cases r with
        | none => cases hB'
        | some B0 =>
          simp only [Option.map_some, Option.some.injEq] at hB'
          subst hB'
          obtain ⟨g1, g2⟩ := hB B0 rfl
          exact ⟨sim_retag _ g1, stepRel_k (refineAll_k t A).symm rfl g2, Or.inr (Or.inl ⟨rfl, t, ht, sIn_keep (tab h0 t ht) htm (keep_step hs hkp')⟩)⟩
    · rw [if_neg hc]
      obtain ⟨r, hr, hB⟩ := SideChangeEnd.s_xsuccs hops hT hs
      refine ⟨r.bind (outStep E R (if A.spent then T1 else T0) A), List.mem_map.2 ⟨r, hr, rfl⟩, fun B hB' => ?_⟩
      cases r with
      | none => cases hB'
      | some B0 =>
        obtain ⟨g1, g2⟩ := hB B0 rfl
        obtain ⟨rfl, hok⟩ := outStep_some hB'
        refine ⟨sim_retag _ g1, stepRel_k rfl rfl g2, ?_⟩
        have hT' : tabOK R.SB (if A.spent then T1 else T0) = true := by
          split
          · exact h1
          · exact h0
        obtain ⟨t, ht, htm⟩ : ∃ t ∈ (if A.spent then T1 else T0), SIn t m := by
          rcases hph with h | ⟨h, h'⟩ | ⟨h, h'⟩
          · exact absurd h hin
          · rw [h]; exact h'
          · rw [h]; exact h'
        have hgoal : ∃ t' ∈ (if A.spent then T1 else T0), SIn t' (go step m).2 := by
          rcases hok with hk | hw
          · exact ⟨t, ht, sIn_keep (tab hT' t ht) htm (keep_step hs hk)⟩
          · exact sIn_write hs g1 hw ht htm
        right
        show ((retag A.spent B0).spent = false ∧ _) ∨ ((retag A.spent B0).spent = true ∧ _)
        cases hsp : A.spent with
        | false =>
          rw [hsp] at hgoal
          exact Or.inl ⟨by simp [retag, hsp], hgoal⟩
        | true =>
          rw [hsp] at hgoal
          exact Or.inr ⟨by simp [retag, hsp], hgoal⟩

end

/-! ### The walk with the routine split -/

theorem le_pc_spent {B D : AS} (h : B.le D = true) : B.pc = D.pc ∧ B.spent = D.spent := by
  simp only [TaintRun.AS.le, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.2⟩

/-- `xwalk` with `tsuccs` -/
def twalk (C : Cfg) (R : Rt) (T0 T1 : List SState) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (tsuccs C.E C.ops R T0 T1 A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverIn C B) || twalk C R T0 T1 fin n B
      else B.k == A.k + 1 && fin B

section
variable {C : Cfg} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool} {R : Rt} {T0 T1 : List SState}

def TLive (C : Cfg) (R : Rt) (T0 T1 : List SState) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph R T0 T1 A m ∧ ∃ n, twalk C R T0 T1 fin n A = true

theorem cover_tlive (ht : C.t.all (twalk C R T0 T1 fin Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph R T0 T1 B m) (h : coverIn C B = true) :
    ∃ D, TLive C R T0 T1 fin F D m ∧ D.k = B.k := by
  unfold coverIn at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [TaintRun.AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hpc, hsp⟩ := le_pc_spent hle
    have hp' : Ph R T0 T1 D m := by
      unfold Ph at hp ⊢
      rw [← hpc, ← hsp]
      exact hp
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, hp', Fu, hall⟩, hk⟩
  · cases h2

theorem tlive_step (ht : C.t.all (twalk C R T0 T1 fin Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : tabOK R.SB T0 = true) (h1 : tabOK R.SB T1 = true) {A : AS} {m : Machine} (hl : TLive C R T0 T1 fin F A m) :
    (∃ A', TLive C R T0 T1 fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph R T0 T1 B (go step m).2) := by
  obtain ⟨hs, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [twalk] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_tsuccs hops hT h0 h1 hs hp
    simp only [twalk, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      dsimp only at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_tlive ht g1 g3 h3
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨g1, g3, n, h3⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, g1, g3⟩

theorem tframe_run (ht : C.t.all (twalk C R T0 T1 fin Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : tabOK R.SB T0 = true) (h1 : tabOK R.SB T1 = true) {f : Nat} :
    ∀ (n : Nat) (A : AS) (m : Machine), TLive C R T0 T1 fin F A m → m.frame = f → dotsPerFrame ≤ m.fdot + 3 * n →
      (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧
        ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 ∧ Ph R T0 T1 B (go (runUntilFrame (f + 1) n) m).2 := by
  intro n
  induction n with
  | zero =>
    intro A m hl _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro A m hl hf hd
    have hh := hl.1.halted
    rw [PipeTransitionAll.ruf_eq, if_neg (by simp [hf, hh])]
    rcases tlive_step ht hops hT h0 h1 hl with ⟨A', g1, g2, g3, g4⟩ | ⟨g1, B, g2, g3, g4, g5⟩
    · have := ih A' _ g1 (g3.trans hf) (by omega)
      rw [g2] at this
      exact this
    · rw [TaintRun.ruf_doneF (by rw [g1, hf]; exact Nat.le_refl _) n]
      exact ⟨by rw [g1, hf], B, g2, g3, g4, g5⟩

/-- **One frame, with the routine split by a table and forgotten.** A walk from `S` covers the frame of a machine of `S`, and at the frame's end the routine's bytes are in a
state of the first table if the routine has not returned (`spent` false), or of the second if it has. -/
theorem tframe_of_walk (ht : C.t.all (twalk C R T0 T1 fin Fu) = true) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : tabOK R.SB T0 = true) (h1 : tabOK R.SB T1 = true)
    {S : AS} {m : Machine} {i : UInt8} (hw : twalk C R T0 T1 fin Fu S = true) (hs : Sim C.E F S { m with pad := smbToPad i }) (hp : Ph R T0 T1 S m) :
    (PipeTransition.frame m i).frame = m.frame + 1 ∧
      ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (PipeTransition.frame m i) ∧ Ph R T0 T1 B (PipeTransition.frame m i) := by
  rw [PipeTransitionAll.frame_eq]
  have hf : dotsPerFrame ≤ ({ m with pad := smbToPad i } : Machine).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  exact tframe_run ht hops hT h0 h1 (f := m.frame) fuelPerFrame S _ ⟨hs, hp, Fu, hw⟩ rfl hf

end

/-! ## The search with the routine split: no part of the proof

The searches of `SideChangeEnd` with a step function as a parameter, to build tables for `twalk` (`xsearch` with `tsuccs` in place of `xsuccs`), and the closure of a table
under single writes. -/

open TaintRun (Search route isSpin)
open SideChangeEnd (xroute)

partial def tsearchTurns (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 64 == 0 then X := { X with out := X.out.push A }
      let rs := step A
      X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
      if rs.any (·.isNone) then
        X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with ends := X.ends.push b }
        else X := xroute E keep X b
  return X

partial def trunChain (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (X0 : Search) (A0 : AS) : Search := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := step cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 128 &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := route E keep X b
    break
  return X

partial def tsearchChains (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 16 == 0 then X := { X with out := X.out.push A }
      if isSpin E A then X := { X with done := X.done.insert key A }
      X := trunChain step E keep X A
  return X

/-- `xsearch` with the step `step` -/
def tsearch (step : AS → List (Option AS)) (E : Env) (keep : List Nat) (starts : List AS) (limit : Nat := 1000000) : Search :=
  if starts.length > 8 then tsearchTurns step E keep limit (starts.foldl (xroute E keep) {})
  else tsearchChains step E keep limit (starts.foldl (route E keep) {})

/-- `t` with the bytes of `w` as `w` has them -/
def overwrite (t w : SState) : SState := t.filter (fun p => !w.any (·.1 == p.1)) ++ w

/-- the table with every state written by every write of `W`, as long as a state is not in one already there; at most `n` rounds -/
def closeUnder (W : List SState) : Nat → List SState → List SState
  | 0, T => T
  | n + 1, T =>
    let new := (T.flatMap fun t => W.map (overwrite t)).foldl (fun (acc : List SState) u =>
      if (T ++ acc).any (entails u) then acc else acc ++ [u]) []
    if new.isEmpty then T else closeUnder W n (T ++ new)

/-- the bytes that both states have, each joined -/
def sjoin (t u : SState) : SState := t.filterMap fun p => (u.find? (·.1 == p.1)).map fun q => (p.1, p.2.join q.2)

/-- the table with each write of `W` joined into the bytes it writes: closed under these writes -/
def joinUnder (W : List SState) (T : List SState) : List SState :=
  T.map fun t => W.foldl (fun t w => t.map fun p => match w.find? (·.1 == p.1) with
    | some q => (p.1, p.2.join q.2)
    | none => p) t

/-- the states with the same values of `key`, joined -/
def groupJoin (key : SState → List (Nat × AB)) (l : List SState) : List SState :=
  let groups := l.foldl (fun (acc : List (List (Nat × AB) × SState)) u =>
    let k := key u
    match acc.find? (·.1 == k) with
    | some _ => acc.map fun g => if g.1 == k then (g.1, sjoin g.2 u) else g
    | none => acc ++ [(k, u)]) []
  groups.map (·.2)

end Smbrta.StepWrites
