import Theorems.EraseRow

/-!
# Bounds on bytes in the walk: the erase's row with no split of the height that rides

Round 32 (`EraseRow`) split the player's height `y` into nine pieces in the collision routine and kept the pieces apart up to its return: the walk's byte knows
only bits, so `y ≤ 207` lives only in the pieces. The pieces multiply the table by about 5.6 in the collision routine (round 33: 183,921 table states of walk (ii)
there, 32,654 keys without the pieces).

Here the walk's state also carries bounds `lo ≤ val(m, i) ≤ hi` on a few bytes (`FOK`): RAM bytes, and the accumulator (`aI`). They are kept in the state's `log`,
which `Sim` does not read. A bound

* is made from the state's known bits at chosen places (`mkL`), and then the bits may be forgotten, so that pieces meet again with the bound;
* stays over a step that writes no byte `i` (`keepF`, from `StepWrites.keep_step`);
* of the accumulator is moved through `LDA zp,X`, `CLC`, `ADC abs,Y`, `AND #0xF0`, `SEC`, `SBC #` and `STA zp` at chosen places (`xferA`, proved from the CPU's
  code of each opcode: `step_rom`, `go_ldaZpx`, `go_adcAby`, `go_andImm`, `go_sbcImm`, `go_staZp`);
* removes the pieces of a split that it excludes (`piecesF`), and makes a split into the byte's values inside the bound (`splitVal`).

The walk with bounds is `walkV`; `frameV` has the conclusions of `EraseRow.frameG`. The cover of a table state asks its bounds too (`leF`). On the ROM the height is
split only at its six tests in the collision routine (`windows`), and the row's offset gets its bound from the height's through the block buffer routine's seven
instructions (`rowPcs`), with no split.

There is no game data in this file. Page: `1-1/d-2-4-2-7-EraseRange.md`.
-/

namespace Smbrta.EraseRange

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken startsR)
open RoomPause (Reg pstep Ph InCls)
open RoomLate (LateS sclamp sim_sclamp sclamp_k sclamp_spent)
open EraseSplit (SpentKeep)
open PipeTransitionAll (ba_size_set ba_get_set_self ba_get_set_ne)

/-! ## Bounds -/

/-- a bound `(i, lo, hi)` as one number -/
def mkF (i lo hi : Nat) : Nat := i * 65536 + lo * 256 + hi
def fI (f : Nat) : Nat := f / 65536
def fLo (f : Nat) : Nat := f / 256 % 256
def fHi (f : Nat) : Nat := f % 256

theorem mkF_dec {i lo hi : Nat} (hl : lo < 256) (hh : hi < 256) : fI (mkF i lo hi) = i ∧ fLo (mkF i lo hi) = lo ∧ fHi (mkF i lo hi) = hi := by
  unfold fI fLo fHi mkF
  omega

/-- the index of the accumulator among the bounds' bytes (outside the RAM's 2048) -/
def aI : Nat := 4096

/-- round 34: the index of `Y` among the bounds' bytes -/
def yI : Nat := 4097

/-- the byte `i` of the machine: the accumulator for `aI`, `Y` for `yI` (round 34), else the RAM byte -/
def valOf (m : Machine) (i : Nat) : UInt8 := if i = aI then m.a else if i = yI then m.y else m.ram.get! i

/-- what the abstract state knows of byte `i` -/
def abK (A : AS) (i : Nat) : AB := if i = aI then A.a else if i = yI then A.y else A.getK i

/-- **The bounds hold**: each byte `fI f` (a RAM byte, or the accumulator) is at least `fLo f` and at most `fHi f` -/
def FOK (l : List Nat) (m : Machine) : Prop := ∀ f ∈ l, fLo f ≤ (valOf m (fI f)).toNat ∧ (valOf m (fI f)).toNat ≤ fHi f

theorem fok_nil (m : Machine) : FOK [] m := fun _ h => absurd h List.not_mem_nil

theorem fok_append {l l' : List Nat} {m : Machine} (h : FOK l m) (h' : FOK l' m) : FOK (l ++ l') m := by
  intro f hf
  rcases List.mem_append.1 hf with e | e
  · exact h f e
  · exact h' f e

theorem fok_filter {l : List Nat} {m : Machine} (p : Nat → Bool) (h : FOK l m) : FOK (l.filter p) m := fun f hf => h f (List.mem_filter.1 hf).1

/-- the largest lower bound of byte `i` in `l`, from `b` -/
def loOf : List Nat → Nat → Nat → Nat
  | [], _, b => b
  | f :: t, i, b => loOf t i (if fI f == i then Nat.max b (fLo f) else b)

/-- the smallest upper bound of byte `i` in `l`, from `b` -/
def hiOf : List Nat → Nat → Nat → Nat
  | [], _, b => b
  | f :: t, i, b => hiOf t i (if fI f == i then Nat.min b (fHi f) else b)

theorem loOf_le {m : Machine} {i : Nat} : ∀ (l : List Nat) (b : Nat), FOK l m → b ≤ (valOf m i).toNat → loOf l i b ≤ (valOf m i).toNat
  | [], _, _, hb => hb
  | f :: t, b, h, hb => by
    have ht : FOK t m := fun g hg => h g (List.mem_cons_of_mem _ hg)
    show loOf t i (if fI f == i then Nat.max b (fLo f) else b) ≤ _
    apply loOf_le t _ ht
    by_cases e : (fI f == i) = true
    · rw [if_pos e]
      have e' : fI f = i := beq_iff_eq.1 e
      have := (h f List.mem_cons_self).1
      rw [e'] at this
      exact Nat.max_le.2 ⟨hb, this⟩
    · rw [if_neg e]
      exact hb

theorem le_hiOf {m : Machine} {i : Nat} : ∀ (l : List Nat) (b : Nat), FOK l m → (valOf m i).toNat ≤ b → (valOf m i).toNat ≤ hiOf l i b
  | [], _, _, hb => hb
  | f :: t, b, h, hb => by
    have ht : FOK t m := fun g hg => h g (List.mem_cons_of_mem _ hg)
    show _ ≤ hiOf t i (if fI f == i then Nat.min b (fHi f) else b)
    apply le_hiOf t _ ht
    by_cases e : (fI f == i) = true
    · rw [if_pos e]
      have e' : fI f = i := beq_iff_eq.1 e
      have := (h f List.mem_cons_self).2
      rw [e'] at this
      exact Nat.le_min.2 ⟨hb, this⟩
    · rw [if_neg e]
      exact hb

theorem loOf_lt : ∀ (l : List Nat) (i b : Nat), b < 256 → loOf l i b < 256
  | [], _, _, hb => hb
  | f :: t, i, b, hb => by
    show loOf t i (if fI f == i then Nat.max b (fLo f) else b) < 256
    apply loOf_lt t i
    by_cases e : (fI f == i) = true
    · rw [if_pos e]
      have : fLo f < 256 := Nat.mod_lt _ (by decide)
      exact Nat.max_lt.2 ⟨hb, this⟩
    · rw [if_neg e]
      exact hb

theorem hiOf_le : ∀ (l : List Nat) (i b : Nat), hiOf l i b ≤ b
  | [], _, _ => Nat.le_refl _
  | f :: t, i, b => by
    show hiOf t i (if fI f == i then Nat.min b (fHi f) else b) ≤ b
    by_cases e : (fI f == i) = true
    · rw [if_pos e]
      exact Nat.le_trans (hiOf_le t i _) (Nat.min_le_left _ _)
    · rw [if_neg e]
      exact hiOf_le t i b

/-- the smallest and the largest value of byte `i` that the known bits and the bounds of `A` allow -/
def rlo (A : AS) (i : Nat) : Nat := loOf A.log i (abK A i).minv.toNat
def rhi (A : AS) (i : Nat) : Nat := hiOf A.log i (abK A i).maxv.toNat

/-- a byte that the bounds may name: a RAM byte, the accumulator, or `Y` (round 34) -/
def okI (i : Nat) : Bool := decide (i < 2048) || i == aI || i == yI

theorem abK_mem {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) {i : Nat} (hi : okI i = true) : (abK A i).mem (valOf m i) := by
  unfold abK valOf
  by_cases e : i = aI
  · rw [if_pos e, if_pos e]
    exact hs.a
  · rw [if_neg e, if_neg e]
    by_cases e2 : i = yI
    · rw [if_pos e2, if_pos e2]
      exact hs.y
    · rw [if_neg e2, if_neg e2]
      have : i < 2048 := by simpa [okI, e, e2] using hi
      exact hs.ram i this

theorem range_ok {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : FOK A.log m) {i : Nat} (hi : okI i = true) :
    rlo A i ≤ (valOf m i).toNat ∧ (valOf m i).toNat ≤ rhi A i :=
  ⟨loOf_le _ _ hf (minv_le (abK_mem hs hi)), le_hiOf _ _ hf (le_maxv (abK_mem hs hi))⟩

theorem valOf_ram {m : Machine} {i : Nat} (hi : i < 2048) : valOf m i = m.ram.get! i := by
  unfold valOf
  rw [if_neg (by unfold aI; omega), if_neg (by unfold yI; omega)]

theorem rlo_lt (A : AS) (i : Nat) : rlo A i < 256 := loOf_lt _ _ _ (UInt8.toNat_lt _)
theorem rhi_lt (A : AS) (i : Nat) : rhi A i < 256 := Nat.lt_of_le_of_lt (hiOf_le _ _ _) (UInt8.toNat_lt _)

/-! ## Making, keeping and asking bounds -/

/-- **New bounds**: for each byte of `is`, its range in `B` -/
def mkL (is : List Nat) (B : AS) : List Nat := (is.filter (· < 2048)).map fun i => mkF i (rlo B i) (rhi B i)

/-- the bounds are no part of `Sim` -/
theorem sim_log {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (l : List Nat) (h : Sim E F B m) : Sim E F { B with log := l } m := { h with }

theorem mkL_ok {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim E F B m) (hf : FOK B.log m) (is : List Nat) : FOK (mkL is B) m := by
  intro f hf'
  obtain ⟨i, hi, e⟩ := List.mem_map.1 hf'
  have hi' : i < 2048 := by simpa using (List.mem_filter.1 hi).2
  subst e
  obtain ⟨d1, d2, d3⟩ := mkF_dec (i := i) (rlo_lt B i) (rhi_lt B i)
  rw [d1, d2, d3]
  exact range_ok hs hf (by simp [okI, hi'])

/-- **The bounds that stay over the step of `A`**: those on a RAM byte that the step does not write (`StepWrites.keepOK`) -/
def keepF (E : Env) (A : AS) (l : List Nat) : List Nat := l.filter fun f => decide (fI f < 2048) && StepWrites.keepOK E (fun j => j == fI f) A

theorem keepF_ok {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} {l : List Nat} (hs : Sim E F A m) (hf : FOK l m) : FOK (keepF E A l) (go step m).2 := by
  intro f hfm
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hfm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  rw [valOf_ram h2.1, StepWrites.keep_step hs h2.2 (fI f) (by simp)]
  rw [← valOf_ram h2.1]
  exact hf f h1


/-! ## The accumulator's bound over seven instructions

The row's offset is computed from the height by `LDA zp,X`, `CLC`, `ADC abs,Y`, `AND #`, `SEC`, `SBC #` and stored by `STA zp`. Each of these maps an interval
of the accumulator to an interval (when there is no carry out), so a bound on the height gives a bound on the row with no split. The machine's step for each
opcode, from the CPU's code: -/

section
open PipeTransitionAll (go_bind)

theorem tick_a (c : Nat) (m : Machine) : (go (tick c) m).2.a = m.a := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_ram (c : Nat) (m : Machine) : (go (tick c) m).2.ram = m.ram := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_p (c : Nat) (m : Machine) : (go (tick c) m).2.p = m.p := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_prg (c : Nat) (m : Machine) : (go (tick c) m).2.prg = m.prg := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_prgMask (c : Nat) (m : Machine) : (go (tick c) m).2.prgMask = m.prgMask := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_trk (c : Nat) (m : Machine) : (go (tick c) m).2.trk = m.trk := by
  unfold tick
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  (repeat' split) <;> rfl

theorem tick_all (c : Nat) (m : Machine) : (go (tick c) m).2.a = m.a ∧ (go (tick c) m).2.ram = m.ram ∧ (go (tick c) m).2.p = m.p ∧
    (go (tick c) m).2.prg = m.prg ∧ (go (tick c) m).2.prgMask = m.prgMask ∧ (go (tick c) m).2.trk = m.trk :=
  ⟨tick_a c m, tick_ram c m, tick_p c m, tick_prg c m, tick_prgMask c m, tick_trk c m⟩

theorem step_rom {m : Machine} {op : UInt8} {f : M Unit} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = op) (hj : op ≠ 0x4C) (hf : opTable[op.toNat]? = some f) :
    (go step m).2 = (go (tick (cycTable.get! op.toNat).toNat) (go f { m with pc := m.pc + 1 }).2).2 := by
  rw [TaintRun.step_op hn hh hp, hop]
  unfold TaintRun.stepK
  rw [if_neg (by simp [hj])]
  rw [hf]
  rfl

theorem go_mZpx {m : Machine} (hp : m.pc ≥ 0x8000) :
    go mZpx m = ((m.prg.get! (m.pc &&& m.prgMask).toNat + m.x).toUInt16, { m with pc := m.pc + 1 }) := by
  have hf := TaintRun.fetch_rom hp
  show go (fetch >>= fun b => (get >>= fun s => pure (b + s.x).toUInt16)) m = _
  rw [go_bind, hf]
  rfl

theorem go_ldaZpx {m : Machine} (hp : m.pc ≥ 0x8000) (ht : m.trk = false) :
    (go (opLDA mZpx) m).2.a = m.ram.get! ((((m.prg.get! (m.pc &&& m.prgMask).toNat + m.x).toUInt16) &&& 0x7FF).toNat) ∧
    (go (opLDA mZpx) m).2.ram = m.ram := by
  have hlt : ((m.prg.get! (m.pc &&& m.prgMask).toNat + m.x).toUInt16) < 0x2000 := by
    have := UInt8.toNat_lt (m.prg.get! (m.pc &&& m.prgMask).toNat + m.x)
    apply UInt16.lt_iff_toNat_lt.2
    simp only [UInt8.toNat_toUInt16]
    have e : (0x2000 : UInt16).toNat = 8192 := rfl
    omega
  show (go (mZpx >>= fun ad => rd ad >>= fun v => setA v) m).2.a = _ ∧ (go (mZpx >>= fun ad => rd ad >>= fun v => setA v) m).2.ram = _
  rw [go_bind, go_mZpx hp]
  simp only []
  rw [go_bind, TaintRun.rd_ram (m := { m with pc := m.pc + 1 }) hlt ht]
  exact ⟨rfl, rfl⟩

theorem go_fetch16 {m : Machine} (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000) :
    go fetch16 m = ((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 ||| ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 <<< 8),
      { m with pc := m.pc + 1 + 1 }) := by
  have hf := TaintRun.fetch_rom hp
  have hf2 := TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp1
  show go (fetch >>= fun lo => fetch >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m = _
  rw [go_bind, hf]
  simp only []
  rw [go_bind, hf2]
  rfl

theorem go_penalty (b e : UInt16) (m : Machine) : (go (pagePenalty b e) m).2.a = m.a ∧ (go (pagePenalty b e) m).2.ram = m.ram ∧
    (go (pagePenalty b e) m).2.p = m.p ∧ (go (pagePenalty b e) m).2.prg = m.prg ∧ (go (pagePenalty b e) m).2.prgMask = m.prgMask ∧
    (go (pagePenalty b e) m).2.trk = m.trk := by
  unfold pagePenalty
  split
  · exact tick_all 1 m
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `ADC abs,Y` from the ROM -/
theorem go_adcAby {m : Machine} (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (he : ((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 ||| ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)) + m.y.toUInt16 ≥ 0x8000) :
    (go (opADC mAbyR) m).2.a = (m.a.toUInt16 + (m.prg.get! ((((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 |||
      ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)) + m.y.toUInt16) &&& m.prgMask).toNat).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 ∧
    (go (opADC mAbyR) m).2.ram = m.ram := by
  generalize hb : ((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 ||| ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)) = b at he ⊢
  have hf := go_fetch16 hp hp1
  rw [hb] at hf
  have hn : ¬ (b + m.y.toUInt16) < 0x2000 := by
    intro h
    have a1 := UInt16.lt_iff_toNat_lt.1 h
    have a2 := UInt16.le_iff_toNat_le.1 he
    simp at a1 a2
    omega
  show (go (mAbyR >>= fun ad => rd ad >>= fun v => adc v) m).2.a = _ ∧ (go (mAbyR >>= fun ad => rd ad >>= fun v => adc v) m).2.ram = _
  have hm : go mAbyR m = (b + m.y.toUInt16, (go (pagePenalty b (b + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 }).2) := by
    show go (fetch16 >>= fun b => get >>= fun s => pagePenalty b (b + s.y.toUInt16) >>= fun _ => pure (b + s.y.toUInt16)) m = _
    rw [go_bind, hf]
    rfl
  obtain ⟨p1, p2, p3, p4, p5, _⟩ := go_penalty b (b + m.y.toUInt16) { m with pc := m.pc + 1 + 1 }
  rw [go_bind, hm]
  simp only []
  rw [go_bind, TaintRun.rd_rom _ hn he]
  simp only [p4, p5]
  refine ⟨?_, ?_⟩
  · show ((go (pagePenalty b (b + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 }).2.a.toUInt16 + _ + ((go (pagePenalty b (b + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 }).2.p &&& 1).toUInt16).toUInt8 = _
    rw [p1, p3]
  · show (go (pagePenalty b (b + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 }).2.ram = _
    rw [p2]

/-- `AND #` from the ROM -/
theorem go_andImm {m : Machine} (hp : m.pc ≥ 0x8000) :
    (go (opAND mImm) m).2.a = m.a &&& m.prg.get! (m.pc &&& m.prgMask).toNat ∧ (go (opAND mImm) m).2.ram = m.ram := by
  have hn : ¬ m.pc < 0x2000 := by
    intro h
    have a1 := UInt16.lt_iff_toNat_lt.1 h
    have a2 := UInt16.le_iff_toNat_le.1 hp
    simp at a1 a2
    omega
  show (go (mImm >>= fun ad => rd ad >>= fun v => andV v) m).2.a = _ ∧ (go (mImm >>= fun ad => rd ad >>= fun v => andV v) m).2.ram = _
  rw [go_bind]
  have hm : go mImm m = (m.pc, { m with pc := m.pc + 1 }) := rfl
  rw [hm]
  simp only []
  rw [go_bind, TaintRun.rd_rom _ hn hp]
  exact ⟨rfl, rfl⟩

/-- `SBC #` from the ROM -/
theorem go_sbcImm {m : Machine} (hp : m.pc ≥ 0x8000) :
    (go (opSBC mImm) m).2.a = (m.a.toUInt16 + (~~~(m.prg.get! (m.pc &&& m.prgMask).toNat)).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 ∧
    (go (opSBC mImm) m).2.ram = m.ram := by
  have hn : ¬ m.pc < 0x2000 := by
    intro h
    have a1 := UInt16.lt_iff_toNat_lt.1 h
    have a2 := UInt16.le_iff_toNat_le.1 hp
    simp at a1 a2
    omega
  show (go (mImm >>= fun ad => rd ad >>= fun v => adc (~~~v)) m).2.a = _ ∧ (go (mImm >>= fun ad => rd ad >>= fun v => adc (~~~v)) m).2.ram = _
  rw [go_bind]
  have hm : go mImm m = (m.pc, { m with pc := m.pc + 1 }) := rfl
  rw [hm]
  simp only []
  rw [go_bind, TaintRun.rd_rom _ hn hp]
  exact ⟨rfl, rfl⟩

/-- `STA zp` -/
theorem go_staZp {m : Machine} (hp : m.pc ≥ 0x8000) (ht : m.trk = false) :
    (go (opSTA mZp) m).2.ram = m.ram.set! (((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 &&& 0x7FF).toNat) m.a := by
  have hlt : (m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 < 0x2000 := by
    have := UInt8.toNat_lt (m.prg.get! (m.pc &&& m.prgMask).toNat)
    apply UInt16.lt_iff_toNat_lt.2
    simp only [UInt8.toNat_toUInt16]
    have e : (0x2000 : UInt16).toNat = 8192 := rfl
    omega
  have hf := TaintRun.fetch_rom hp
  show (go (mZp >>= fun ad => get >>= fun s => wr ad s.a) m).2.ram = _
  have hm : go mZp m = ((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16, { m with pc := m.pc + 1 }) := by
    show go (fetch >>= fun b => pure b.toUInt16) m = _
    rw [go_bind, hf]
    rfl
  rw [go_bind, hm]
  show (go (wr _ m.a) { m with pc := m.pc + 1 }).2.ram = _
  unfold wr
  rw [if_pos hlt]
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ht]
  rfl

/-- `STA zp` keeps the accumulator (round 34) -/
theorem go_staZp_a {m : Machine} (hp : m.pc ≥ 0x8000) (ht : m.trk = false) : (go (opSTA mZp) m).2.a = m.a := by
  have hlt : (m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16 < 0x2000 := by
    have := UInt8.toNat_lt (m.prg.get! (m.pc &&& m.prgMask).toNat)
    apply UInt16.lt_iff_toNat_lt.2
    simp only [UInt8.toNat_toUInt16]
    have e : (0x2000 : UInt16).toNat = 8192 := rfl
    omega
  have hf := TaintRun.fetch_rom hp
  show (go (mZp >>= fun ad => get >>= fun s => wr ad s.a) m).2.a = _
  have hm : go mZp m = ((m.prg.get! (m.pc &&& m.prgMask).toNat).toUInt16, { m with pc := m.pc + 1 }) := by
    show go (fetch >>= fun b => pure b.toUInt16) m = _
    rw [go_bind, hf]
    rfl
  rw [go_bind, hm]
  show (go (wr _ m.a) { m with pc := m.pc + 1 }).2.a = _
  unfold wr
  rw [if_pos hlt]
  simp only [go, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ht]
  rfl

theorem add3_toNat (x y z : UInt8) : (x.toUInt16 + y.toUInt16 + z.toUInt16).toUInt8.toNat = (x.toNat + y.toNat + z.toNat) % 256 := by
  have hx := UInt8.toNat_lt x
  have hy := UInt8.toNat_lt y
  have hz := UInt8.toNat_lt z
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_add, UInt8.toNat_toUInt16]
  omega
set_option maxRecDepth 20000 in
theorem and_f0_fin : ∀ n : Fin 256, (n.val &&& 240) = n.val / 16 * 16 := by decide
theorem and_f0 (x : UInt8) : (x &&& 0xF0).toNat = x.toNat / 16 * 16 := by
  rw [UInt8.toNat_and]
  exact and_f0_fin ⟨x.toNat, UInt8.toNat_lt x⟩
theorem not_toNat (x : UInt8) : (~~~x).toNat = 255 - x.toNat := by
  have := UInt8.toNat_not x
  omega

end


/-- the opcode at the state's program counter, and the two bytes after it -/
def opAt (E : Env) (A : AS) : UInt8 := E.prg.get! (A.pc &&& E.mask).toNat
def b1At (E : Env) (A : AS) : UInt8 := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
def b2At (E : Env) (A : AS) : UInt8 := E.prg.get! ((A.pc + 2) &&& E.mask).toNat

/-- the address of an `ADC abs,Y` with `Y` as `A` knows it -/
def absY (E : Env) (A : AS) : UInt16 := ((b1At E A).toUInt16 ||| ((b2At E A).toUInt16 <<< 8)) + A.y.v.toUInt16

/-- **The bounds that the step makes from the accumulator's bound**: after `LDA zp,X` (X known) the accumulator's from the byte's; after `CLC` and `SEC` the
same; after `ADC abs,Y` (Y and the carry known, the operand in the ROM, no carry out) it moves up by the operand and the carry; after `AND #0xF0` both ends are
rounded down to a multiple of 16; after `SBC #` (the carry known, no borrow) it moves down; after `STA zp` the byte's is the accumulator's. Only at the places
`xq` -/
def xferA (E : Env) (xq : List UInt16) (A : AS) : List Nat :=
  if xq.contains A.pc = true ∧ A.nmi = false ∧ 0x8000 ≤ A.pc ∧ 0x8000 ≤ A.pc + 1 ∧ 0x8000 ≤ A.pc + 2 then
    if opAt E A = 0xB5 then
      (if A.x.isK then [mkF aI (rlo A ((b1At E A + A.x.v).toUInt16 &&& 0x7FF).toNat) (rhi A ((b1At E A + A.x.v).toUInt16 &&& 0x7FF).toNat)] else [])
    else if opAt E A = 0x18 ∨ opAt E A = 0x38 then [mkF aI (rlo A aI) (rhi A aI)]
    else if opAt E A = 0x79 then
      (if A.y.isK = true ∧ A.p.k &&& 1 = 1 ∧ 0x8000 ≤ absY E A ∧
          rhi A aI + (E.prg.get! (absY E A &&& E.mask).toNat).toNat + (A.p.v &&& 1).toNat ≤ 255 then
        [mkF aI (rlo A aI + (E.prg.get! (absY E A &&& E.mask).toNat).toNat + (A.p.v &&& 1).toNat)
          (rhi A aI + (E.prg.get! (absY E A &&& E.mask).toNat).toNat + (A.p.v &&& 1).toNat)] else [])
    else if opAt E A = 0x29 ∧ b1At E A = 0xF0 then [mkF aI (rlo A aI / 16 * 16) (rhi A aI / 16 * 16)]
    else if opAt E A = 0xE9 then
      (if A.p.k &&& 1 = 1 ∧ (b1At E A).toNat + 1 - (A.p.v &&& 1).toNat ≤ rlo A aI then
        [mkF aI (rlo A aI - ((b1At E A).toNat + 1 - (A.p.v &&& 1).toNat)) (rhi A aI - ((b1At E A).toNat + 1 - (A.p.v &&& 1).toNat))] else [])
    else if opAt E A = 0x85 then [mkF (((b1At E A).toUInt16 &&& 0x7FF).toNat) (rlo A aI) (rhi A aI)]
    else []
  else []

theorem fok_one {m : Machine} {i lo hi : Nat} (hl : lo < 256) (hh : hi < 256) (h1 : lo ≤ (valOf m i).toNat) (h2 : (valOf m i).toNat ≤ hi) :
    FOK [mkF i lo hi] m := by
  intro f hf
  rw [List.mem_singleton.1 hf]
  obtain ⟨d1, d2, d3⟩ := mkF_dec (i := i) hl hh
  rw [d1, d2, d3]
  exact ⟨h1, h2⟩

theorem valOf_a (m : Machine) : valOf m aI = m.a := by unfold valOf; rw [if_pos rfl]

theorem valOf_y (m : Machine) : valOf m yI = m.y := by unfold valOf; rw [if_neg (by decide), if_pos rfl]

theorem and1_le (x : UInt8) : (x &&& 1).toNat ≤ 1 := by
  rw [UInt8.toNat_and]
  exact Nat.and_le_right

set_option maxRecDepth 100000 in
theorem xferA_ok {E : Env} {xq : List UInt16} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : FOK A.log m) :
    FOK (xferA E xq A) (go step m).2 := by
  unfold xferA
  split
  · rename_i hc
    obtain ⟨_, hn0, hp, hp1, hp2⟩ := hc
    have hn : m.nmiPending = false := by rw [hs.nmi]; exact hn0
    have hh : m.halted = false := hs.halted
    have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
    have ht : m.trk = false := hs.trk
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt E A := by rw [hs.prg, hs.mask, hs.pc]; rfl
    have hb1 : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = b1At E A := by rw [hs.prg, hs.mask, hs.pc]; rfl
    have hb2 : m.prg.get! ((m.pc + 1 + 1) &&& m.prgMask).toNat = b2At E A := by
      rw [hs.prg, hs.mask, hs.pc, show A.pc + 1 + 1 = A.pc + 2 by rw [UInt16.add_assoc]; rfl]; rfl
    have hp1' : (m.pc + 1) ≥ 0x8000 := by rw [hs.pc]; exact hp1
    have hp2' : (m.pc + 1 + 1) ≥ 0x8000 := by rw [hs.pc, show A.pc + 1 + 1 = A.pc + 2 by rw [UInt16.add_assoc]; rfl]; exact hp2
    have aOK := range_ok hs hf (i := aI) (by simp [okI])
    rw [valOf_a] at aOK
    split
    · -- LDA zp,X
      rename_i e0
      split
      · rename_i hx
        rw [e0] at hop
        rw [step_rom (f := opLDA mZpx) hn hh hpm hop (by decide) rfl]
        obtain ⟨a1, _⟩ := go_ldaZpx (m := { m with pc := m.pc + 1 }) hp1' ht
        have hxv : m.x = A.x.v := isK_eq hx hs.x
        generalize hi : ((b1At E A + A.x.v).toUInt16 &&& 0x7FF).toNat = i
        have hil : i < 2048 := by rw [← hi]; exact EraseRow.and7FF_lt _
        have hr := range_ok hs hf (i := i) (by simp [okI, hil])
        rw [valOf_ram hil] at hr
        apply fok_one (rlo_lt _ _) (rhi_lt _ _)
        · rw [valOf_a, tick_a, a1]
          show rlo A i ≤ (m.ram.get! (((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat + m.x).toUInt16 &&& 0x7FF).toNat)).toNat
          rw [hb1, hxv, hi]
          exact hr.1
        · rw [valOf_a, tick_a, a1]
          show (m.ram.get! (((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat + m.x).toUInt16 &&& 0x7FF).toNat)).toNat ≤ rhi A i
          rw [hb1, hxv, hi]
          exact hr.2
      · exact fok_nil _
    · split
      · -- CLC, SEC
        rename_i _ e0
        have ha : (go step m).2.a = m.a := by
          rcases e0 with e0 | e0
          · rw [e0] at hop
            rw [step_rom (f := opCLC) hn hh hpm hop (by decide) rfl, tick_a]
            rfl
          · rw [e0] at hop
            rw [step_rom (f := opSEC) hn hh hpm hop (by decide) rfl, tick_a]
            rfl
        apply fok_one (rlo_lt _ _) (rhi_lt _ _) <;> rw [valOf_a, ha]
        · exact aOK.1
        · exact aOK.2
      · split
        · -- ADC abs,Y
          rename_i _ _ e0
          split
          · rename_i hc2
            obtain ⟨hy, hk, he, hle⟩ := hc2
            rw [e0] at hop
            have hyv : m.y = A.y.v := isK_eq hy hs.y
            have hpc : m.p &&& 1 = A.p.v &&& 1 := bit_eq hs.p hk
            have he' : ((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 ||| ((m.prg.get! ((m.pc + 1 + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)) +
                m.y.toUInt16 ≥ 0x8000 := by
              rw [hb1, hb2, hyv]; exact he
            rw [step_rom (f := opADC mAbyR) hn hh hpm hop (by decide) rfl]
            obtain ⟨a1, _⟩ := go_adcAby (m := { m with pc := m.pc + 1 }) hp1' hp2' he'
            have hv : (go (opADC mAbyR) { m with pc := m.pc + 1 }).2.a =
                (m.a.toUInt16 + (E.prg.get! (absY E A &&& E.mask).toNat).toUInt16 + (A.p.v &&& 1).toUInt16).toUInt8 := by
              rw [a1]
              show (m.a.toUInt16 + (m.prg.get! ((((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 |||
                ((m.prg.get! ((m.pc + 1 + 1) &&& m.prgMask).toNat).toUInt16 <<< 8)) + m.y.toUInt16) &&& m.prgMask).toNat).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 = _
              rw [hb1, hb2, hyv, hpc, hs.prg, hs.mask]
              rfl
            have hn3 := add3_toNat m.a (E.prg.get! (absY E A &&& E.mask).toNat) (A.p.v &&& 1)
            have hc1 := and1_le A.p.v
            have hvl := UInt8.toNat_lt (E.prg.get! (absY E A &&& E.mask).toNat)
            have hlt1 : rlo A aI + (E.prg.get! (absY E A &&& E.mask).toNat).toNat + (A.p.v &&& 1).toNat < 256 := by
              have := aOK.1; have := aOK.2; omega
            apply fok_one hlt1 (by omega) <;> rw [valOf_a, tick_a, hv, hn3]
            · have := aOK.1; have := aOK.2; omega
            · have := aOK.1; have := aOK.2; omega
          · exact fok_nil _
        · split
          · -- AND #0xF0
            rename_i _ _ _ e0
            obtain ⟨e1, e2⟩ := e0
            rw [e1] at hop
            rw [step_rom (f := opAND mImm) hn hh hpm hop (by decide) rfl]
            obtain ⟨a1, _⟩ := go_andImm (m := { m with pc := m.pc + 1 }) hp1'
            have hv : (go (opAND mImm) { m with pc := m.pc + 1 }).2.a = m.a &&& 0xF0 := by
              rw [a1]
              show m.a &&& m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = _
              rw [hb1, e2]
            have h16 := and_f0 m.a
            have r1 := rlo_lt A aI
            have r2 := rhi_lt A aI
            apply fok_one (by omega) (by omega) <;> rw [valOf_a, tick_a, hv, h16]
            · have := aOK.1; omega
            · have := aOK.2; omega
          · split
            · -- SBC #
              rename_i _ _ _ _ e0
              split
              · rename_i hc2
                obtain ⟨hk, hle⟩ := hc2
                rw [e0] at hop
                have hpc : m.p &&& 1 = A.p.v &&& 1 := bit_eq hs.p hk
                rw [step_rom (f := opSBC mImm) hn hh hpm hop (by decide) rfl]
                obtain ⟨a1, _⟩ := go_sbcImm (m := { m with pc := m.pc + 1 }) hp1'
                have hv : (go (opSBC mImm) { m with pc := m.pc + 1 }).2.a = (m.a.toUInt16 + (~~~(b1At E A)).toUInt16 + (A.p.v &&& 1).toUInt16).toUInt8 := by
                  rw [a1]
                  show (m.a.toUInt16 + (~~~(m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat)).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 = _
                  rw [hb1, hpc]
                have hn3 := add3_toNat m.a (~~~(b1At E A)) (A.p.v &&& 1)
                have hnt := not_toNat (b1At E A)
                have hc1 := and1_le A.p.v
                have hbl := UInt8.toNat_lt (b1At E A)
                have r1 := rlo_lt A aI
                have r2 := rhi_lt A aI
                apply fok_one (by omega) (by omega) <;> rw [valOf_a, tick_a, hv, hn3, hnt]
                · have := aOK.1; have := aOK.2; omega
                · have := aOK.1; have := aOK.2; omega
              · exact fok_nil _
            · split
              · -- STA zp
                rename_i _ _ _ _ _ e0
                rw [e0] at hop
                rw [step_rom (f := opSTA mZp) hn hh hpm hop (by decide) rfl]
                have a1 := go_staZp (m := { m with pc := m.pc + 1 }) hp1' ht
                generalize hz : ((b1At E A).toUInt16 &&& 0x7FF).toNat = z
                have hzl : z < 2048 := by rw [← hz]; exact EraseRow.and7FF_lt _
                have hv : (go (opSTA mZp) { m with pc := m.pc + 1 }).2.ram.get! z = m.a := by
                  rw [a1]
                  show (m.ram.set! (((m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 &&& 0x7FF).toNat) m.a).get! z = m.a
                  rw [hb1, hz]
                  exact ba_get_set_self _ _ _ (by rw [hs.size]; exact hzl)
                apply fok_one (rlo_lt _ _) (rhi_lt _ _) <;> rw [valOf_ram hzl, tick_ram]
                · show rlo A aI ≤ ((go (opSTA mZp) { m with pc := m.pc + 1 }).2.ram.get! z).toNat
                  rw [hv]; exact aOK.1
                · show ((go (opSTA mZp) { m with pc := m.pc + 1 }).2.ram.get! z).toNat ≤ rhi A aI
                  rw [hv]; exact aOK.2
              · exact fok_nil _
  · exact fok_nil _

/-- **The bounds of the accumulator and of `Y` over `STA zp` and `TAY`** (round 34): `STA zp` keeps the accumulator's bound; after `TAY` both the accumulator
and `Y` have it. Only at the places `xq`. With it the walk knows a bound of `Y` at the block buffer routine's read, two instructions after the row's store -/
def xferY (E : Env) (xq : List UInt16) (A : AS) : List Nat :=
  if xq.contains A.pc = true ∧ A.nmi = false ∧ 0x8000 ≤ A.pc ∧ 0x8000 ≤ A.pc + 1 then
    if opAt E A = 0x85 then [mkF aI (rlo A aI) (rhi A aI)]
    else if opAt E A = 0xA8 then [mkF yI (rlo A aI) (rhi A aI), mkF aI (rlo A aI) (rhi A aI)]
    else []
  else []

set_option maxRecDepth 100000 in
theorem xferY_ok {E : Env} {xq : List UInt16} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : FOK A.log m) :
    FOK (xferY E xq A) (go step m).2 := by
  unfold xferY
  split
  · rename_i hc
    obtain ⟨_, hn0, hp, hp1⟩ := hc
    have hn : m.nmiPending = false := by rw [hs.nmi]; exact hn0
    have hh : m.halted = false := hs.halted
    have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
    have ht : m.trk = false := hs.trk
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt E A := by rw [hs.prg, hs.mask, hs.pc]; rfl
    have hp1' : (m.pc + 1) ≥ 0x8000 := by rw [hs.pc]; exact hp1
    have aOK := range_ok hs hf (i := aI) (by simp [okI])
    rw [valOf_a] at aOK
    split
    · -- STA zp
      rename_i e0
      rw [e0] at hop
      have ha : (go step m).2.a = m.a := by
        rw [step_rom (f := opSTA mZp) hn hh hpm hop (by decide) rfl, tick_a]
        exact go_staZp_a hp1' ht
      apply fok_one (rlo_lt _ _) (rhi_lt _ _) <;> rw [valOf_a, ha]
      · exact aOK.1
      · exact aOK.2
    · split
      · -- TAY
        rename_i _ e0
        rw [e0] at hop
        have e1 := step_rom (f := opTAY) hn hh hpm hop (by decide) rfl
        have ha : (go step m).2.a = m.a := by rw [e1, tick_a]; rfl
        have hy : (go step m).2.y = m.a := by rw [e1, RoomBlocks.tick_y]; rfl
        intro f hf'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
        rcases hf' with e | e <;> subst e
        · obtain ⟨d1, d2, d3⟩ := mkF_dec (i := yI) (rlo_lt A aI) (rhi_lt A aI)
          rw [d1, d2, d3, valOf_y, hy]
          exact aOK
        · obtain ⟨d1, d2, d3⟩ := mkF_dec (i := aI) (rlo_lt A aI) (rhi_lt A aI)
          rw [d1, d2, d3, valOf_a, ha]
          exact aOK
      · exact fok_nil _
  · exact fok_nil _

/-- what the walk does with bounds: where it makes them from the known bits (`mkAt`, on the bytes `mkB`), where it drops them all (`dropAt`), where it moves
the accumulator's (`xq`) -/
structure Rules where
  mkAt : List UInt16
  mkB : List Nat
  dropAt : List UInt16
  xq : List UInt16

/-- the bytes whose bounds are made at `pc` -/
def Rules.make (Ru : Rules) (pc : UInt16) : List Nat := if Ru.mkAt.contains pc then Ru.mkB else []

/-- all bounds are dropped at `pc` -/
def Rules.drop (Ru : Rules) (pc : UInt16) : Bool := Ru.dropAt.contains pc

/-- **The bounds after a step** from `A1` to `B`: none at the places `Ru.drop`; else those that stay (`keepF`) and those that the step makes from the
accumulator's (`xferA` at `Ru.xq`), but on the bytes of `Ru.make B.pc`, for which new ones are made from `B`; bounds 0 to 255 are dropped -/
def updF (Ru : Rules) (E : Env) (A1 B : AS) : AS :=
  if Ru.drop B.pc then { B with log := [] } else
  let K := keepF E A1 A1.log ++ xferA E Ru.xq A1 ++ xferY E Ru.xq A1
  { B with log := (mkL (Ru.make B.pc) { B with log := K } ++ K.filter fun f => !(Ru.make B.pc).contains (fI f)).filter fun f => !(fLo f == 0 && fHi f == 255) }

theorem updF_ok {Ru : Rules} {E : Env} {F : Nat × UInt8} {A1 B : AS} {m : Machine} (hs : Sim E F A1 m)
    (hf : FOK A1.log m) (hB : Sim E F B (go step m).2) : Sim E F (updF Ru E A1 B) (go step m).2 ∧ FOK (updF Ru E A1 B).log (go step m).2 ∧
      (updF Ru E A1 B).k = B.k ∧ (updF Ru E A1 B).spent = B.spent ∧ (updF Ru E A1 B).pc = B.pc := by
  unfold updF
  split
  · exact ⟨sim_log _ hB, fok_nil _, rfl, rfl, rfl⟩
  · have hK := fok_append (fok_append (keepF_ok (l := A1.log) hs hf) (xferA_ok (xq := Ru.xq) hs hf)) (xferY_ok (xq := Ru.xq) hs hf)
    exact ⟨sim_log _ hB, fok_filter _ (fok_append (mkL_ok (B := { B with log := keepF E A1 A1.log ++ xferA E Ru.xq A1 ++ xferY E Ru.xq A1 }) (sim_log _ hB) hK _) (fok_filter _ hK)),
      rfl, rfl, rfl⟩

/-- the bounds of `D` hold on every machine of `W` -/
def leF (W D : AS) : Bool := D.log.all fun f => okI (fI f) && decide (fLo f ≤ rlo W (fI f)) && decide (rhi W (fI f) ≤ fHi f)

theorem fok_of_leF {E : Env} {F : Nat × UInt8} {W D : AS} {m : Machine} (hs : Sim E F W m) (hf : FOK W.log m) (h : leF W D = true) : FOK D.log m := by
  intro f hfm
  have := List.all_eq_true.1 h f hfm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  have := range_ok hs hf h1
  omega

/-- every bound of `A` is not empty with the known bits of `A`: a piece that fails this has no machine -/
def consF (A : AS) : Bool := A.log.all fun f => !okI (fI f) || decide (rlo A (fI f) ≤ rhi A (fI f))

theorem consF_of {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : FOK A.log m) : consF A = true := by
  apply List.all_eq_true.2
  intro f _
  by_cases h : okI (fI f) = true
  · have := range_ok hs hf h
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
    right
    omega
  · simp [h]

/-! ## Splits with bounds -/

/-- every machine of a state with its bounds is in one of the pieces -/
def CovF (E : Env) (F : Nat × UInt8) (sp : AS → List AS) : Prop := ∀ A m, Sim E F A m → FOK A.log m → ∃ B ∈ sp A, Sim E F B m ∧ B.k = A.k

theorem covF_of {E : Env} {F : Nat × UInt8} {sp : AS → List AS} (h : Cov E F sp) : CovF E F sp := fun A m hs _ => h A m hs

/-- **The pieces with the bounds**: the pieces of `sp`, each with the bounds of `A`, but those that a bound excludes -/
def piecesF (sp : AS → List AS) (A : AS) : List AS :=
  (sp A).filterMap fun B => if consF { B with log := A.log } then some { B with log := A.log } else none

theorem cov_pieces {E : Env} {F : Nat × UInt8} {sp : AS → List AS} (hc : CovF E F sp) (hsk : SpentKeep sp) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hf : FOK A.log m) : ∃ B ∈ piecesF sp A, Sim E F B m ∧ B.k = A.k ∧ B.log = A.log ∧ B.spent = A.spent := by
  obtain ⟨B, hB, h1, h2⟩ := hc A m hs hf
  have hS : Sim E F { B with log := A.log } m := sim_log _ h1
  have hc' : consF { B with log := A.log } = true := consF_of hS hf
  refine ⟨{ B with log := A.log }, List.mem_filterMap.2 ⟨B, hB, by rw [if_pos hc']⟩, hS, h2, rfl, hsk A B hB⟩

theorem spent_pieces {sp : AS → List AS} (hsk : SpentKeep sp) {A B : AS} (hB : B ∈ piecesF sp A) : B.spent = A.spent := by
  obtain ⟨B0, h0, h1⟩ := List.mem_filterMap.1 hB
  split at h1
  · cases h1
    exact hsk A B0 h0
  · cases h1

/-- `A` with byte `i` known to be `v` covers each machine of `A` with that value -/
theorem sim_setK_same {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) {d : Nat} {v : AB} (hv : v.mem (m.ram.get! d)) :
    Sim E F (A.setK d v) m := by
  refine { hs with
    ram := ?_
    szR := ?_
    szK := ?_ }
  · intro i hi
    show AB.mem ⟨(A.ram.set! d v.v).get! i, (A.kn.set! d v.k).get! i⟩ (m.ram.get! i)
    by_cases hdi : d = i
    · subst hdi
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi)]
      exact hv
    · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
      exact hs.ram i hi
  · show (A.ram.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szR
  · show (A.kn.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szK

/-- **The byte's values**: a piece for each value of byte `d` inside its range (`rlo`, `rhi`) that its known bits allow -/
def splitVal (d : Nat) (A : AS) : List AS :=
  (List.range (rhi A d + 1 - rlo A d)).filterMap fun j =>
    if (rlo A d + j).toUInt8 &&& (A.getK d).k == (A.getK d).v &&& (A.getK d).k then some (A.setK d (AB.known (rlo A d + j).toUInt8)) else none

theorem covF_splitVal {E : Env} {F : Nat × UInt8} {d : Nat} (hd : d < 2048) : CovF E F (splitVal d) := by
  intro A m hs hf
  have hr := range_ok hs hf (i := d) (by simp [okI, hd])
  rw [valOf_ram hd] at hr
  have hv : (m.ram.get! d).toNat < 256 := UInt8.toNat_lt _
  refine ⟨A.setK d (AB.known (m.ram.get! d)), List.mem_filterMap.2 ⟨(m.ram.get! d).toNat - rlo A d, List.mem_range.2 (by omega), ?_⟩,
    sim_setK_same hs (mem_known_self _), rfl⟩
  have e : (rlo A d + ((m.ram.get! d).toNat - rlo A d)).toUInt8 = m.ram.get! d := by
    rw [show rlo A d + ((m.ram.get! d).toNat - rlo A d) = (m.ram.get! d).toNat by omega]
    exact UInt8.ofNat_toNat
  simp only [e]
  have hm := hs.ram d hd
  unfold AB.mem at hm
  rw [if_pos (beq_iff_eq.2 hm)]

theorem spent_splitVal (d : Nat) : SpentKeep (splitVal d) := by
  intro A B hB
  obtain ⟨j, _, h⟩ := List.mem_filterMap.1 hB
  split at h
  · cases h
    rfl
  · cases h

/-! ## The step with no hypothesis on the position's low bits (round 34)

`ScreenPage.preS` splits the position at the side pipe's read (`xAt`) into pieces with a low bit set; it needs `SiteOK.xbit` there. `preSX` adds a fifth
piece with the four low bits 0, so the step `pstepX` needs only `SiteX`, the other five parts of `SiteOK`. The other functions of the step do not look at
`xAt`: with `xAt` moved off the machine's place (`movX`), `SiteX` is `SiteOK` (`siteOK_movX`). -/

section
open ScreenPage (preS stepS RamRom readVal readAddr writeAddr)
open RoomPause (keepP inP)
open StepWrites (SIn tabOK agrees refineAll retag forgetAll)
variable {E : Env} {F : Nat × UInt8} {P : Places} {ops : Array (AM Unit)} {G : Reg}

/-- **`SiteOK` but the position's low bits at the side pipe's read** -/
structure SiteX (P : Places) (m : Machine) : Prop where
  late : m.pc ≠ P.idle → m.fdot ≤ P.late
  reads : 0x8000 ≤ m.pc → m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 → RamRom (readAddr m)
  read : m.pc = P.read → readVal m ∈ P.tiles ∧ (m.ram.get! P.saveI ∈ P.heads → readVal m ∈ P.headTiles)
  erase : m.pc = P.erase → writeAddr m < 0x2000 ∧ P.bufLo ≤ (writeAddr m &&& 0x7FF).toNat ∧ (writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN
  off : m.pc ∈ P.offAt → (m.ram.get! P.offI).toNat < 64

theorem siteX_of {m : Machine} (h : SiteOK P m) : SiteX P m := ⟨h.late, h.reads, h.read, h.erase, h.off⟩

theorem siteOK_of_X {m : Machine} (h : SiteX P m) (hx : m.pc = P.xAt → m.ram.get! P.xI &&& 0x0F ≠ 0) : SiteOK P m :=
  ⟨h.late, h.reads, h.read, h.erase, h.off, hx⟩

/-- the places with the side pipe's read of the position at `q` -/
def movX (P : Places) (q : UInt16) : Places := { P with xAt := q }

theorem ne_add_one (x : UInt16) : x ≠ x + 1 := by
  intro h
  have h2 := congrArg UInt16.toNat h
  rw [UInt16.toNat_add] at h2
  have := x.toNat_lt
  have e : (1 : UInt16).toNat = 1 := rfl
  rw [e] at h2
  omega

theorem siteOK_movX {m : Machine} (h : SiteX P m) : SiteOK (movX P (m.pc + 1)) m :=
  ⟨h.late, h.reads, h.read, h.erase, h.off, fun hpc => absurd hpc (ne_add_one _)⟩

theorem placesOK_movX (h : PlacesOK E P) (q : UInt16) : PlacesOK E (movX P q) :=
  ⟨h.late, h.read, h.erase, h.offI, h.xI, h.saveI, h.stI, h.hpI, h.noD⟩

theorem stepS_movX (q : UInt16) (A : AS) : stepS (movX P q) E ops A = stepS P E ops A := rfl

theorem keepP_movX (q : UInt16) (SB : List Nat) (A : AS) : keepP (movX P q) E SB A = keepP P E SB A := rfl

/-- **The pieces before a step, with the fifth piece**: at the side pipe's read of the position the four pieces of `preS` with a low bit set, and the piece
with the four low bits 0; elsewhere `preS` -/
def preSX (P : Places) (A : AS) : List AS :=
  if A.pc == P.xAt then
    ([1, 2, 4, 8] : List UInt8).map (fun b => A.setK P.xI ((A.getK P.xI).or (AB.known b))) ++ [A.setK P.xI ((A.getK P.xI).and (AB.known 0xF0))]
  else preS P A

set_option maxRecDepth 100000 in
theorem andF0_all : ((List.range 256).all fun n => (n.toUInt8 &&& 0x0F != 0) || (n.toUInt8 &&& 0xF0 == n.toUInt8)) = true := by decide

theorem andF0_of {x : UInt8} (h : x &&& 0x0F = 0) : x &&& 0xF0 = x := by
  have h1 := List.all_eq_true.1 andF0_all x.toNat (List.mem_range.2 x.toNat_lt)
  have e : x.toNat.toUInt8 = x := by simp
  rw [e] at h1
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
  rcases h1 with h2 | h2
  · exact absurd h h2
  · exact h2

theorem cov_preSX (hO : PlacesOK E P) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteX P m) : ∃ B ∈ preSX P A, Sim E F B m ∧ B.k = A.k := by
  unfold preSX
  by_cases h2 : (A.pc == P.xAt) = true
  · rw [if_pos h2]
    by_cases hx : m.ram.get! P.xI &&& 0x0F = 0
    · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_, rfl⟩
      apply PipeEntryRule.sim_setK' hs
      have := TaintRun.mem_and (hs.ram _ hO.xI) (mem_known_self (0xF0 : UInt8))
      rwa [andF0_of hx] at this
    · obtain ⟨b, hb, he⟩ := ScreenPage.or_bit_of hx
      refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩), ?_, rfl⟩
      apply PipeEntryRule.sim_setK' hs
      have := TaintRun.mem_or (hs.ram _ hO.xI) (mem_known_self b)
      rwa [he] at this
  · rw [if_neg h2]
    have hne : m.pc ≠ P.xAt := by
      rw [hs.pc]
      intro e
      exact h2 (beq_iff_eq.2 e)
    exact ScreenPage.cov_preS hO hs (siteOK_of_X hh (fun e => absurd e hne))

/-- the step of `ScreenPage` with the fifth piece -/
def baseSX (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) := (preSX P (clampS P A)).flatMap (stepS P E ops)

theorem s_baseSX (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteX P m) :
    ∃ r ∈ baseSX P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
  obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preSX hO hs0 hh
  obtain ⟨r, hr, hB⟩ := ScreenPage.s_stepS (placesOK_movX hO (m.pc + 1)) hops hT hs1 (siteOK_movX hh)
  rw [stepS_movX] at hr
  refine ⟨r, List.mem_flatMap.2 ⟨A₁, hA, hr⟩, fun B hB' => ?_⟩
  obtain ⟨g1, g2⟩ := hB B hB'
  exact ⟨g1, StepWrites.stepRel_k (by rw [hk1, ScreenPage.clamp_k]) rfl g2⟩

/-- **`RoomPause.pstep` with the fifth piece** -/
def pstepX (P : Places) (E : Env) (ops : Array (AM Unit)) (G : Reg) (A : AS) : List (Option AS) :=
  if A.spent then (baseSX P E ops A).map fun o => o.bind (inP G A)
  else if A.pc == G.call then
    G.T.flatMap fun t => if agrees t A then (baseSX P E ops (refineAll t A)).map fun o => o.map (retag true) else []
  else (preSX P (clampS P A)).flatMap fun A₁ => if keepP P E G.SB A₁ then stepS P E ops A₁
    else (stepS P E ops A₁).map fun o => o.bind fun B => if StepWrites.writeOK E G.SB G.T A₁ B then some B else none

/-- **One step of `pstepX`**, as `RoomPause.s_pstep`, from `SiteX` -/
theorem s_pstepX (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (h0 : tabOK G.SB G.T = true) (hg : G.gI < 2048)
    (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteX P m) (hph : Ph G A m) :
    ∃ r ∈ pstepX P E ops G A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 ∧ Ph G B (go step m).2 := by
  have tab : ∀ t ∈ G.T, ∀ p ∈ t, G.SB.contains p.1 = true ∧ p.1 < 2048 := by
    intro t ht p hp
    simp only [tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0
    exact h0 t ht p hp
  unfold pstepX
  by_cases hsp : A.spent = true
  · rw [if_pos hsp]
    obtain ⟨r, hr, hB⟩ := s_baseSX hO hops hT hs hh
    refine ⟨r.bind (inP G A), List.mem_map.2 ⟨r, hr, rfl⟩, fun B hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B0 =>
      obtain ⟨g1, g2⟩ := hB B0 rfl
      simp only [Option.bind_some, inP] at hB'
      split at hB'
      · split at hB'
        · rename_i _ hany
          simp only [Option.some.injEq] at hB'
          subst hB'
          obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 hany
          exact ⟨RoomPause.sim_keepBits g1 G.keepB hkb (RoomPause.sim_keep0 g1 (StepWrites.sim_retag _ (StepWrites.sim_forgetAll _ g1)) hg),
            StepWrites.stepRel_k rfl ((RoomPause.keepBits_k _ _ _).trans (StepWrites.forgetAll_k _ _)) g2, Or.inr ⟨t, ht, StepWrites.sIn_of_le g1 hle⟩⟩
        · cases hB'
      · simp only [Option.some.injEq] at hB'
        subst hB'
        exact ⟨StepWrites.sim_retag _ g1, StepWrites.stepRel_k rfl rfl g2, Or.inl rfl⟩
  · rw [if_neg hsp]
    obtain ⟨t, ht, htm⟩ : ∃ t ∈ G.T, SIn t m := by
      rcases hph with h | h
      · exact absurd h hsp
      · exact h
    by_cases hc : (A.pc == G.call) = true
    · rw [if_pos hc]
      have hag : agrees t A = true := StepWrites.agrees_of hs (fun p hp => (tab t ht p hp).2) htm
      obtain ⟨r, hr, hB⟩ := s_baseSX hO hops hT (StepWrites.sim_refineAll t hs htm) hh
      refine ⟨r.map (retag true), List.mem_flatMap.2 ⟨t, ht, by rw [if_pos hag]; exact List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
      cases r with
      | none => cases hB'
      | some B0 =>
        simp only [Option.map_some, Option.some.injEq] at hB'
        subst hB'
        obtain ⟨g1, g2⟩ := hB B0 rfl
        exact ⟨StepWrites.sim_retag _ g1, StepWrites.stepRel_k (StepWrites.refineAll_k t A).symm rfl g2, Or.inl rfl⟩
    · rw [if_neg hc]
      have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
      obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preSX hO hs0 hh
      have hO' := placesOK_movX hO (m.pc + 1)
      have hh' := siteOK_movX hh
      by_cases hk : keepP P E G.SB A₁ = true
      · obtain ⟨r, hr, hB⟩ := ScreenPage.s_stepS hO' hops hT hs1 hh'
        rw [stepS_movX] at hr
        refine ⟨r, List.mem_flatMap.2 ⟨A₁, hA, by rw [if_pos hk]; exact hr⟩, fun B hB' => ?_⟩
        obtain ⟨g1, g2⟩ := hB B hB'
        exact ⟨g1, StepWrites.stepRel_k (by rw [hk1, ScreenPage.clamp_k]) rfl g2,
          Or.inr ⟨t, ht, StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (RoomPause.keepP_ok hO' hs1 hh' (by rw [keepP_movX]; exact hk))⟩⟩
      · obtain ⟨r, hr, hB⟩ := ScreenPage.s_stepS hO' hops hT hs1 hh'
        rw [stepS_movX] at hr
        refine ⟨r.bind fun B => if StepWrites.writeOK E G.SB G.T A₁ B then some B else none,
          List.mem_flatMap.2 ⟨A₁, hA, by rw [if_neg hk]; exact List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
        cases r with
        | none => cases hB'
        | some B0 =>
          obtain ⟨g1, g2⟩ := hB B0 rfl
          simp only [Option.bind_some] at hB'
          split at hB'
          · rename_i hw
            simp only [Option.some.injEq] at hB'
            subst hB'
            exact ⟨g1, StepWrites.stepRel_k (by rw [hk1, ScreenPage.clamp_k]) rfl g2, Or.inr (StepWrites.sIn_write hs1 g1 hw ht htm)⟩
          · cases hB'

end

/-! ## The walk with bounds -/

section
variable {G : Reg} {C : CfgS} {chk : AS → Bool} {Fu : Nat} {F : Nat × UInt8} {sq : UInt16 → Bool} {D : Nat} {sp : AS → List AS}
  {Ru : Rules}

/-- **The step with bounds**: the pieces of `sp` that the bounds allow, the step of `RoomPause` (round 34: with the fifth piece at the side pipe's read,
`pstepX`), and the bounds after it -/
def stepV (sp : AS → List AS) (Ru : Rules) (G : Reg) (C : CfgS) (A : AS) : List (Option AS) :=
  (piecesF sp A).flatMap fun A1 => (pstepX C.P C.E C.ops G A1).map fun r => r.map (updF Ru C.E A1)

/-- a state of the table with the same key covers `B`, with its bounds -/
def coverV (C : CfgS) (B : AS) : Bool :=
  (C.idx.getD (C.key B) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D && leF B D
    | none => false

/-- `ScreenPage.weaken` with the bounds kept -/
def weakenV (C : CfgS) (B : AS) : AS := { weaken C B with log := B.log }

/-- **The walk with bounds**: `EraseRow.walkG` with `stepV` and `coverV` -/
def walkV (sp : AS → List AS) (Ru : Rules) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) :
    Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => chk (sclamp sq D A) && (stepV sp Ru G C (sclamp sq D A)).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weakenV C B).pc.toNat != 0 && coverV C (sclamp sq D (weakenV C B))) || walkV sp Ru G C chk sq D n (weakenV C B)
      else B.k == A.k + 1 && C.fin B && chk B

/-- `A` covers `m` with its bounds and `Ph`, and a walk from `A` succeeds -/
def LiveV (sp : AS → List AS) (Ru : Rules) (G : Reg) (C : CfgS) (chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat)
    (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ FOK A.log m ∧ Ph G A m ∧ ∃ n, walkV sp Ru G C chk sq D n A = true

theorem chkV_of_walk {n : Nat} {A : AS} (h : walkV sp Ru G C chk sq D n A = true) : chk (sclamp sq D A) = true := by
  cases n with
  | zero => simp [walkV] at h
  | succ n =>
    simp only [walkV, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveV (ht : C.t.all (walkV sp Ru G C chk sq D Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hf : FOK B.log m) (hp : Ph G B m)
    (h : coverV C B = true) : ∃ D', LiveV sp Ru G C chk sq D F D' m ∧ D'.k = B.k := by
  unfold coverV at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D' e
    simp only [Bool.and_eq_true] at h2
    obtain ⟨hle, hlf⟩ := h2
    have hk : D'.k = B.k := by
      have hle2 := hle
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle2
      exact hle2.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D', ⟨sim_le hle hs, fok_of_leF hs hf hlf, RoomPause.ph_of_spent (StepWrites.le_pc_spent hle).2 hp, Fu, hall⟩, hk⟩
  · cases h2

theorem weakenV_of {B : AS} {m : Machine} (hs : Sim C.E F B m) (hf : FOK B.log m) :
    Sim C.E F (weakenV C B) m ∧ FOK (weakenV C B).log m ∧ (weakenV C B).k = B.k ∧ (weakenV C B).spent = B.spent := by
  obtain ⟨n1, n2, n3⟩ := RoomPause.weaken_of (C := C) hs
  exact ⟨sim_log _ n1, hf, n2, n3⟩

/-- **One step of the walk with bounds**, as `EraseRow.live_stepG` -/
theorem live_stepV (hcv : CovF C.E F sp) (hsk : SpentKeep sp) {R : Machine → Prop}
    (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → FOK A.log m → chk A = true → R m → SiteX C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkV sp Ru G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine}
    (hl : LiveV sp Ru G C chk sq D F A m) (hr : R m) (hl2 : LateS sq D (go step m).2) :
    (∃ A', LiveV sp Ru G C chk sq D F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ FOK B.log (go step m).2 ∧
      Ph G B (go step m).2) := by
  obtain ⟨hs, hf, hp, n, hw⟩ := hl
  cases n with
  | zero => simp [walkV] at hw
  | succ n =>
    have hs1 : Sim C.E F (sclamp sq D A) m := sim_sclamp hD hs (hS hr)
    have hf1 : FOK (sclamp sq D A).log m := by unfold sclamp; split <;> exact hf
    have hp1 : Ph G (sclamp sq D A) m := RoomPause.ph_of_spent (sclamp_spent sq D A).symm hp
    have hh : SiteX C.P m := hQ hs1 hf1 (chkV_of_walk hw) hr
    obtain ⟨A2, hA2, hs2, hk2, hlog2, hsp2⟩ := cov_pieces hcv hsk hs1 hf1
    have hf2 : FOK A2.log m := by rw [hlog2]; exact hf1
    have hp2 : Ph G A2 m := RoomPause.ph_of_spent hsp2.symm hp1
    obtain ⟨r, hr', hB⟩ := s_pstepX hO hops hT h0 hg hkb hs2 hh hp2
    simp only [walkV, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 (r.map (updF Ru C.E A2)) (List.mem_flatMap.2 ⟨A2, hA2, List.mem_map.2 ⟨r, hr', rfl⟩⟩)
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨g1, g2, g3⟩ := hB B rfl
      obtain ⟨u1, u2, u3, u4, _⟩ := updF_ok (Ru := Ru) hs2 hf2 g1
      generalize hB' : updF Ru C.E A2 B = B' at u1 u2 u3 u4
      have g3' : Ph G B' (go step m).2 := RoomPause.ph_of_spent u4.symm g3
      simp only [Option.map_some, hB'] at hw2
      rcases g2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk2, sclamp_k] at k1
        have k1' : B'.k = A.k := u3.trans k1
        rw [if_pos (by simp [k1'])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        obtain ⟨n1, nf, n2, n3⟩ := weakenV_of (C := C) u1 u2
        have hpW : Ph G (weakenV C B') (go step m).2 := RoomPause.ph_of_spent n3.symm g3'
        rcases hw2 with ⟨_, h3⟩ | h3
        · have hpC : Ph G (sclamp sq D (weakenV C B')) (go step m).2 := RoomPause.ph_of_spent (sclamp_spent sq D _).symm hpW
          have nfC : FOK (sclamp sq D (weakenV C B')).log (go step m).2 := by unfold sclamp; split <;> exact nf
          obtain ⟨D', hD', hk⟩ := cover_liveV ht (sim_sclamp hD n1 hl2) nfC hpC h3
          exact ⟨D', hD', by rw [hk, sclamp_k, n2, k1'], k2, k3⟩
        · exact ⟨_, ⟨n1, nf, hpW, n, h3⟩, by rw [n2, k1'], k2, k3⟩
      · right
        rw [hk2, sclamp_k] at k1
        have k1' : B'.k = A.k + 1 := u3.trans k1
        rw [if_neg (by simp [k1'])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B', hw2.1.2, hw2.2, k1', u1, u2, g3'⟩

/-- **One frame of the walk with bounds**, as `EraseRow.frame_of_walkG` -/
theorem frame_of_walkV (hcv : CovF C.E F sp) (hsk : SpentKeep sp) {R : Machine → Prop}
    (hQ : ∀ {A : AS} {m : Machine}, Sim C.E F A m → FOK A.log m → chk A = true → R m → SiteX C.P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) (hD : D < dotsPerFrame)
    (hO : PlacesOK C.E C.P) (ht : C.t.all (walkV sp Ru G C chk sq D Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkV sp Ru G C chk sq D Fu S = true) (hs : Sim C.E F S m) (hf : FOK S.log m) (hph : Ph G S m)
    (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteX C.P (trace m i j)) ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hph0 : Ph G S { m with pad := smbToPad i } := hph
  have hf0 : FOK S.log { m with pad := smbToPad i } := hf
  have key : ∀ j, (∃ A, LiveV sp Ru G C chk sq D F A (trace m i j) ∧ A.k = S.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ chk B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (trace m i j) ∧ FOK B.log (trace m i j) ∧
        Ph G B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, hf0, hph0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h4', h5⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hS (hk (j + 1))
        rw [e2] at hh2 ⊢
        rcases live_stepV hcv hsk hQ hS hD hO ht hops hT h0 hg hkb h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a2', a3, a4, a4', a5⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a2', by rw [a3, h2], a4, a4', a5⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h2', h3, h4, h4', h5⟩
  refine ⟨fun j => ?_, ?_⟩
  · rcases key j with ⟨A, ⟨h1, hf1, _, n, h1'⟩, _, _, _⟩ | ⟨_, B, _, h2', _, h4, h4', _⟩
    · have hf1' : FOK (sclamp sq D A).log (trace m i j) := by unfold sclamp; split <;> exact hf1
      exact hQ (sim_sclamp hD h1 (hS (hk j))) hf1' (chkV_of_walk h1') (hk j)
    · exact hQ h4 h4' h2' (hk j)
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨_, B, h2, _, _, h4, _, _⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h4⟩


/-- **A successor covers the next machine** (round 34): one of the pieces of `sp` and one result of `pstepX` from it -/
theorem succ_of {E : Env} {P : Places} {ops : Array (AM Unit)} (hcv : CovF E F sp) (hsk : SpentKeep sp) (hO : PlacesOK E P)
    (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (h0 : StepWrites.tabOK G.SB G.T = true) (hg : G.gI < 2048) (hkb : ∀ p ∈ G.keepB, p.1 < 2048) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hf : FOK A.log m) (hh : SiteX P m) (hp : Ph G A m) :
    ∃ A2 ∈ piecesF sp A, ∃ r ∈ pstepX P E ops G A2, ∀ B, r = some B → Sim E F B (go step m).2 := by
  obtain ⟨A2, hA2, hs2, _, _, hsp2⟩ := cov_pieces hcv hsk hs hf
  obtain ⟨r, hr, hB⟩ := s_pstepX hO hops hT h0 hg hkb hs2 hh (RoomPause.ph_of_spent hsp2.symm hp)
  exact ⟨A2, hA2, r, hr, fun B e => (hB B e).1⟩
end

/-! ## Finding the table: a search with the bounds, no part of the proof, and the check -/

section
open ScreenPage (SearchS)

/-- the join of two states, with each bound of `D` widened to hold on `B` too; the bounds that `D` does not have are dropped -/
def joinV (D B : AS) : AS :=
  { D.join B with log := D.log.map fun f => mkF (fI f) (Nat.min (fLo f) (rlo B (fI f))) (Nat.max (fHi f) (rhi B (fI f))) }

/-- `EraseRow.routeR` with the bounds: a state is put to the one of its key that holds it with its bounds, or joined with it -/
def routeV (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (E : Env) (kb : AS → Nat) (sq : UInt16 → Bool) (D : Nat) (X : SearchS) (B0 : AS) :
    SearchS :=
  let B := sclamp sq D (clampS P { EraseRow.normR Z fy B0 with log := B0.log })
  let K := EraseRow.keyR Z E kb B
  let X := { X with arr := X.arr.insert K (X.arr.getD K 0 + 1) }
  match X.done[K]? with
  | some D' =>
    if B.le D' && leF B D' then X else
    let J := joinV D' B
    let n := X.vis.getD K 1 + 1
    let J := if n ≥ 3 && sq J.pc then { J with hi := D } else J
    RoomPause.putP { X with done := X.done.insert K J, vis := X.vis.insert K n, joins := X.joins + 1 } K J
  | none => RoomPause.putP { X with done := X.done.insert K B, vis := X.vis.insert K 1 } K B

/-- `EraseRow.advR` with `stepV`, and the forgetting `nf` of the walk after each step -/
partial def advV (sp : AS → List AS) (Ru : Rules) (G : Reg) (C : CfgS) (nf : AS → AS) (sq : UInt16 → Bool) (D : Nat)
    (ad : List UInt16) (n : Nat) (b : AS) : AS :=
  if n == 0 || !ad.contains b.pc then b else
  match (stepV sp Ru G C (sclamp sq D b)).filterMap id with
  | [c] => if c.k == b.k then advV sp Ru G C nf sq D ad (n - 1) { nf c with log := c.log } else b
  | _ => b

/-- `EraseRow.runR` with `stepV` and `routeV` -/
partial def runV (sp : AS → List AS) (Ru : Rules) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16)
    (kb : AS → Nat) (G : Reg) (C : CfgS) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := stepV sp Ru G C (sclamp sq D cur)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (Z.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          !fy.any (·.1 == b.pc) && Ru.make b.pc == [] && (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b0 in good do
      if b0.k != cur.k then X := { X with ends := X.ends.push b0 }
      else
        let b := if good.length ≥ 2 then advV sp Ru G C (EraseRow.normR Z fy) sq D ad 8 b0 else b0
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeV C.P Z fy C.E kb sq D X b
    break
  return X

/-- `EraseRow.searchR` with `runV` -/
partial def searchV (sp : AS → List AS) (Ru : Rules) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16)
    (kb : AS → Nat) (G : Reg) (C : CfgS) (sq : UInt16 → Bool) (D : Nat) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := EraseRow.keyR Z C.E kb A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runV sp Ru Z fy ad kb G C sq D X A
  return X

/-- the configuration that the search's steps use (its table is empty) -/
def cfg0 (P : Places) (E : Env) : CfgS :=
  { E, ops := (aRows E).toArray, P, fin := fun _ => true, t := #[], key := fun _ => 0, idx := {}, cut := ByteArray.empty, norm := id, normAt := ByteArray.empty }

/-- `EraseRow.searchBR` with `searchV`; the starts with no bounds -/
def searchBV (sp : AS → List AS) (Ru : Rules) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16)
    (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (sq : UInt16 → Bool) (D : Nat) :
    SearchS :=
  let Z := RoomPause.aidsP Z G
  let ops := (aRows E).toArray
  let S0 := (RK.flatMap fun q => startsR q.1 q.2).map fun S => { S with log := [] }
  let S := match pre with
    | some fpc => (S0.flatMap (BufferRecords.preWalk P E ops G fpc)).map fun S => { BufferRecords.forgetL fz S with log := [] }
    | none => S0
  searchV sp Ru Z fy ad kb G (cfg0 P E) sq D (S.foldl (routeV P Z fy E kb sq D) {})

/-- the table of `searchBV`, as `EraseRow.cfgBR` -/
def cfgBV (sp : AS → List AS) (Ru : Rules) (P : Places) (Z0 : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16)
    (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin : AS → Bool) (sq : UInt16 → Bool)
    (D : Nat) : CfgS :=
  let Z := RoomPause.aidsP Z0 G
  let X := searchBV sp Ru P Z0 fy ad E kb G pre fz RK sq D
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ pre.toList ++ fy.map (·.1)).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P, fin, t := q.1, key := EraseRow.keyR Z E kb, idx := q.2.1, cut := q.2.2,
    norm := fun A => if pre == some A.pc then BufferRecords.forgetL fz (EraseRow.normR Z fy A) else EraseRow.normR Z fy A, normAt := at0 }

/-- **The check of the walk with bounds**, as `EraseRow.walkCheckR`; the starts are walked with no bounds -/
def walkCheckV (sp : AS → List AS) (Ru : Rules) (P : Places) (Z : Aids) (fy : List (UInt16 × List Nat)) (ad : List UInt16)
    (E : Env) (kb : AS → Nat) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8))) (fin chk : AS → Bool) (sq : UInt16 → Bool)
    (D : Nat) : Bool :=
  let C := cfgBV sp Ru P Z fy ad E kb G pre fz RK fin sq D
  ScreenPage.placesOK E P && E.pad.v == 0 && E.pad.k == 0 && StepWrites.tabOK G.SB G.T && decide (G.gI < 2048) &&
    G.keepB.all (fun p => decide (p.1 < 2048)) && decide (D < dotsPerFrame) && C.t.all (walkV sp Ru G C chk sq D ScreenPage.fuelS) &&
    RK.all (fun q => ScreenPage.maskOK q.1 q.2 && (startsR q.1 q.2).all fun S => walkV sp Ru G C chk sq D ScreenPage.fuelS { S with log := [] })

/-- what the check says -/
structure VOK (sp : AS → List AS) (Ru : Rules) (E : Env) (P : Places) (G : Reg) (RK : List (Machine × List (Nat × UInt8)))
    (C : CfgS) (fin chk : AS → Bool) (sq : UInt16 → Bool) (D : Nat) : Prop where
  places : PlacesOK E P
  pad : E.pad = AB.top
  env : C.E = E
  pl : C.P = P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  tab : StepWrites.tabOK G.SB G.T = true
  gI : G.gI < 2048
  keepI : ∀ p ∈ G.keepB, p.1 < 2048
  dD : D < dotsPerFrame
  table : C.t.all (walkV sp Ru G C chk sq D ScreenPage.fuelS) = true
  starts : ∀ q ∈ RK, ScreenPage.MaskOK q.1 q.2 ∧ ∀ S ∈ startsR q.1 q.2, walkV sp Ru G C chk sq D ScreenPage.fuelS { S with log := [] } = true

theorem vok_of_check {sp : AS → List AS} {Ru : Rules} {P : Places} {Z : Aids} {fy : List (UInt16 × List Nat)}
    {ad : List UInt16} {E : Env} {kb : AS → Nat} {G : Reg} {pre : Option UInt16} {fz : List Nat} {RK : List (Machine × List (Nat × UInt8))}
    {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat} (h : walkCheckV sp Ru P Z fy ad E kb G pre fz RK fin chk sq D = true) :
    VOK sp Ru E P G RK (cfgBV sp Ru P Z fy ad E kb G pre fz RK fin sq D) fin chk sq D := by
  simp only [walkCheckV, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h4⟩, h5⟩, hkb⟩, hD⟩, h6⟩, h7⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  refine ⟨ScreenPage.placesOK_spec h1, hp, rfl, rfl, rfl, rfl, h4, h5, fun p hp => hkb p hp, hD, h6, ?_⟩
  intro q hq
  have := h7 q hq
  exact ⟨ScreenPage.maskOK_spec this.1, fun S hS => this.2 S hS⟩

end

/-- **One frame of the room from a reference of `RK`**, as `EraseRow.frameG`, for the walk with bounds -/
theorem frameV {sp : AS → List AS} {Ru : Rules} {E : Env} {P : Places} {G : Reg} {RK : List (Machine × List (Nat × UInt8))}
    {C : CfgS} {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat} {R : Machine → Prop} (hcv : ∀ F : Nat × UInt8, CovF E F sp) (hsk : SpentKeep sp)
    (h : VOK sp Ru E P G RK C fin chk sq D)
    (hQ : ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim E F A m → FOK A.log m → chk A = true → R m → SiteX P m)
    (hS : ∀ {m : Machine}, R m → LateS sq D m) {r : Machine} {K : List (Nat × UInt8)} (hq : (r, K) ∈ RK)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hc : InCls G m) (hk : ∀ j, R (trace m i j)) :
    (∀ j, SiteX P (trace m i j)) ∧ ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨hM, hw0⟩ := h.starts _ hq
  obtain ⟨S0, hS0, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) hM h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := hw0 S0 hS0
  have hs' : Sim C.E (m.frame, 2) { S0 with log := [] } m := by rw [h.env]; exact sim_log _ hs
  have hQ' : ∀ {A : AS} {m' : Machine}, Sim C.E (m.frame, 2) A m' → FOK A.log m' → chk A = true → R m' → SiteX C.P m' := by
    intro A m' hs2 hf2 hc2 hr
    rw [h.pl]
    rw [h.env] at hs2
    exact hQ hs2 hf2 hc2 hr
  have hcv' : CovF C.E (m.frame, 2) sp := by rw [h.env]; exact hcv _
  have := frame_of_walkV (G := G) (C := C) (chk := chk) (F := (m.frame, 2)) (R := R) hcv' hsk hQ' hS h.dD hO h.table h.ops
    (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) h.tab h.gI h.keepI hw hs' (fok_nil _) (Or.inr hc) hk
  rw [h.pl, h.fin, h.env] at this
  exact this

/-! ## The split with bounds -/

section
open EraseRow (splitY zsplitL cov_splitY cov_zsplitL spent_splitY spent_zsplitL spent_splitBit)
open EraseSplit (splitK cov_splitK spent_splitK)

/-- **The split**: at `yAt` the height `yI` (`EraseRow.splitY`), bit 0 of the size `sI` and the crouch byte `cI` by its lowest set bit; at the other places of `yW`
the height; at `eraY` (the erase's load of the row) the row byte's values inside its bounds, if it has one; then at `pc0` the accumulator and `Y`
(`EraseSplit.splitK`) -/
def splitV (yAt : UInt16) (yW : List UInt16) (yI sI cI : Nat) (eraY : UInt16) (rI : Nat) (pc0 : UInt16) (A : AS) : List AS :=
  (if A.pc == yAt then ((splitY yI A).flatMap (splitBit sI 1)).flatMap (zsplitL cI bitList)
   else if yW.contains A.pc then splitY yI A
   else if A.pc == eraY && A.log.any (fun f => fI f == rI) then splitVal rI A
   else [A]).flatMap (splitK pc0)

theorem covF_splitV {E : Env} {F : Nat × UInt8} {yAt eraY pc0 : UInt16} {yW : List UInt16} {yI sI cI rI : Nat} (hy : yI < 2048) (hs : sI < 2048)
    (hc : cI < 2048) (hr : rI < 2048) : CovF E F (splitV yAt yW yI sI cI eraY rI pc0) := by
  intro A m hm hf
  unfold splitV
  have h1 : ∃ B ∈ (if A.pc == yAt then ((splitY yI A).flatMap (splitBit sI 1)).flatMap (zsplitL cI bitList)
      else if yW.contains A.pc then splitY yI A
      else if A.pc == eraY && A.log.any (fun f => fI f == rI) then splitVal rI A
      else [A]), Sim E F B m ∧ B.k = A.k := by
    split
    · exact cov_flat (cov_zsplitL hc bitList (fun b hb => hb)) (cov_flat (cov_bit hs (by decide)) (cov_splitY hy A m hm))
    · split
      · exact cov_splitY hy A m hm
      · split
        · exact covF_splitVal hr A m hm hf
        · exact ⟨A, List.mem_singleton.2 rfl, hm, rfl⟩
  exact cov_flat (cov_splitK pc0) h1

theorem spent_splitV (yAt : UInt16) (yW : List UInt16) (yI sI cI : Nat) (eraY : UInt16) (rI : Nat) (pc0 : UInt16) :
    SpentKeep (splitV yAt yW yI sI cI eraY rI pc0) := by
  intro A B hB
  unfold splitV at hB
  obtain ⟨C1, h1, h2⟩ := List.mem_flatMap.1 hB
  rw [spent_splitK pc0 C1 B h2]
  split at h1
  · obtain ⟨D1, h4, h5⟩ := List.mem_flatMap.1 h1
    obtain ⟨D0, h6, h7⟩ := List.mem_flatMap.1 h4
    rw [spent_zsplitL cI bitList D1 C1 h5, spent_splitBit sI 1 D0 D1 h7, spent_splitY yI A D0 h6]
  · split at h1
    · exact spent_splitY yI A C1 h1
    · split at h1
      · exact spent_splitVal rI A C1 h1
      · rw [List.mem_singleton.1 h1]

end

/-! ## The places on the ROM -/

/-- a window of the height's tests from `pc`: the compares, branches and the store that follow (`(window, places after it)`) -/
def winGo (m0 : Machine) : Nat → UInt16 → List UInt16 → List UInt16 → List UInt16 × List UInt16
  | 0, pc, ws, ms => (ws, pc :: ms)
  | n + 1, pc, ws, ms =>
    let op := romByte m0 pc
    if op == 0xC9 || op == 0x85 then winGo m0 n (pc + 2) (pc :: ws) ms
    else if op == 0xDD then winGo m0 n (pc + 3) (pc :: ws) ms
    else if op == 0x90 || op == 0xB0 then
      let off := romByte m0 (pc + 1)
      let t := pc + 2 + off.toUInt16 - (if 0x80 ≤ off then 256 else 0)
      winGo m0 n (pc + 2) (pc :: ws) (t :: ms)
    else (ws, pc :: ms)

/-- **The height's tests in the collision routine**: each `LDA zp` of the height followed by a compare, and the `AND zp` of the height followed by its store -/
def winStarts (sy : Syms) (m0 : Machine) (P : Places) : List UInt16 :=
  let z := sy.Player_Y_Position.toUInt8
  (List.range (P.erase - sy.PlayerBGCollision).toNat).filterMap fun j =>
    let a := sy.PlayerBGCollision + j.toUInt16
    if (romByte m0 a == 0xA5 && romByte m0 (a + 1) == z && (romByte m0 (a + 2) == 0xC9 || romByte m0 (a + 2) == 0xDD)) ||
        (romByte m0 a == 0x25 && romByte m0 (a + 1) == z && romByte m0 (a + 2) == 0x85 && romByte m0 (a + 3) == z) then some a else none

/-- the windows: each start, its instructions after it, and the places after it -/
def windows (sy : Syms) (m0 : Machine) (P : Places) : List (UInt16 × List UInt16 × List UInt16) :=
  (winStarts sy m0 P).map fun w => let r := winGo m0 8 (w + 2) [] []; (w, r.1, r.2)

/-- the seven instructions of the row: the load of the height, `CLC`, `ADC abs,Y`, `AND #`, `SEC`, `SBC #`, the store -/
def rowPcs (sy : Syms) (m0 : Machine) : List UInt16 := let a := EraseRow.adcY sy m0; [a - 3, a - 1, a, a + 3, a + 5, a + 6, a + 8]

/-- the erase's load of the row (`LDY zp`), and the instructions to the erase -/
def eraY (P : Places) : UInt16 := P.erase - 4

/-- the pointer's low byte of the block buffer routine's read -/
def zPtr (sy : Syms) (m0 : Machine) : Nat := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 1)).toNat

/-- the places and bytes of the split -/
structure SplitD where
  yAt : UInt16
  yW : List UInt16
  yI : Nat
  sI : Nat
  cI : Nat
  eraY : UInt16
  rI : Nat
  pc0 : UInt16

/-- `splitV` from its data -/
def splitD (d : SplitD) (A : AS) : List AS := splitV d.yAt d.yW d.yI d.sI d.cI d.eraY d.rI d.pc0 A

/-- **The split's places on the ROM** -/
def splitData (sy : Syms) (m0 : Machine) (P : Places) : SplitD :=
  { yAt := EraseRow.yAt sy m0, yW := (windows sy m0 P).map (·.1), yI := EraseRow.yIdx sy, sI := EraseRow.sizeIdx sy, cI := EraseRow.crouchIdx sy m0,
    eraY := eraY P, rI := EraseRow.rowIdx sy m0, pc0 := EraseSplit.adcAt sy m0 }

/-- **The split on the ROM** -/
def splitRom (sy : Syms) (m0 : Machine) (P : Places) : AS → List AS := splitD (splitData sy m0 P)

theorem rowIdx_lt (sy : Syms) (m0 : Machine) : EraseRow.rowIdx sy m0 < 2048 := by
  have := UInt8.toNat_lt (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 - 2))
  unfold EraseRow.rowIdx
  omega

theorem covF_splitRom (sy : Syms) (m0 : Machine) (P : Places) (E : Env) (F : Nat × UInt8) : CovF E F (splitD (splitData sy m0 P)) :=
  covF_splitV (EraseRow.yIdx_lt sy) (EraseRow.sizeIdx_lt sy) (EraseRow.crouchIdx_lt sy m0) (rowIdx_lt sy m0)

theorem spent_splitRom (sy : Syms) (m0 : Machine) (P : Places) : SpentKeep (splitD (splitData sy m0 P)) := spent_splitV _ _ _ _ _ _ _ _

/-- the places after the windows -/
def merges (sy : Syms) (m0 : Machine) (P : Places) : List UInt16 := (windows sy m0 P).flatMap fun w => w.2.2

/-- the aids on the ROM: `EraseRow.aidsR`, and the accumulator and `Y` forgotten after the erase (the code after it loads both before it reads them) -/
def aidsV (sy : Syms) (m0 : Machine) (P : Places) (Z : Aids) : Aids :=
  let Z1 := EraseRow.aidsR sy m0 Z
  { Z1 with cutAY := Z1.cutAY ++ [P.erase + 2] }

/-- **The rules of the bounds on the ROM**: made after the windows, dropped at the collision routine's return and after the erase, moved through the row's
instructions; round 34: and through the `TAY` before the block buffer routine's read (`xferY`), so that the read knows a bound of `Y` -/
def rulesOf (sy : Syms) (m0 : Machine) (P : Places) (Z : Aids) : Rules :=
  { mkAt := merges sy m0 P, mkB := [EraseRow.yIdx sy], dropAt := [Z.colEnd, P.erase + 2], xq := rowPcs sy m0 ++ [P.read - 1] }

/-- what the search forgets, and where: `EraseRow.forgetAt`, and the height after each window -/
def forgetV (sy : Syms) (m0 : Machine) (Z : Aids) (P : Places) : List (UInt16 × List Nat) :=
  EraseRow.forgetAt sy m0 Z P ++ ((windows sy m0 P).flatMap fun w => w.2.2).map fun pc => (pc, [EraseRow.yIdx sy])

/-- where the search runs the pieces of a split on: the windows after their start, the erase's load to the erase -/
def advAt (sy : Syms) (m0 : Machine) (P : Places) : List UInt16 :=
  ((windows sy m0 P).flatMap fun w => w.2.1) ++ [eraY P + 2, P.erase]

/-- the places and bytes of the key's part -/
structure KeyD where
  zR : Nat
  st0 : UInt16
  yI : Nat
  rI : Nat
  cI : Nat
  sI : Nat
  yA : UInt16
  hc : UInt16
  wp : List UInt16
  ep : List UInt16

/-- **The key's part**: `EraseSplit.ptrKey` (bit 7 of the pointer byte `zR`, and of the accumulator at `st0`); a state whose first dot is below 10 apart; at the
places `wp` the known bits of byte `yI`; from `yA` to `hc` the classes of byte `cI` (`EraseRow.lowC`) and of bit 0 of byte `sI`; at the places `ep` the known
bits of byte `rI` -/
def keyL (d : KeyD) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let pk := EraseSplit.bit7Key d.zR A + (if A.pc == d.st0 then 3 * EraseSplit.bit7A A else 0)
  let st := if A.lo < 10 then 1 else 0
  let w := if d.wp.contains A.pc then 1 + num (A.getK d.yI) else 0
  let c := if d.yA ≤ A.pc && A.pc ≤ d.hc then 1 + EraseRow.lowC (A.getK d.cI) + 11 * EraseRow.bitC (A.getK d.sI) 1 else 0
  let z := if d.ep.contains A.pc then 1 + num (A.getK d.rI) else 0
  pk + 16 * (st + 2 * (w + 65537 * (c + 64 * z)))

/-- **The key's places on the ROM**: the pointer byte; the windows; from the height's first load to the head's test; the erase's load and the erase -/
def keyData (sy : Syms) (m0 : Machine) (P : Places) : KeyD :=
  { zR := zPtr sy m0, st0 := EraseSplit.adcAt sy m0 + 3, yI := EraseRow.yIdx sy, rI := EraseRow.rowIdx sy m0, cI := EraseRow.crouchIdx sy m0,
    sI := EraseRow.sizeIdx sy, yA := EraseRow.yAt sy m0, hc := EraseRow.hcAt sy m0 + 3, wp := (windows sy m0 P).flatMap fun w => w.1 :: w.2.1,
    ep := [eraY P, eraY P + 2, P.erase] }

end Smbrta.EraseRange
