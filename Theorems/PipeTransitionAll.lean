import Theorems.PipeTransition

/-!
# What decides the length of the change into the bonus room

The first part has no game in it. A tracked run of the emulator records the RAM bytes it reads before writing them. `decided_of_check`
proves, by a simulation of every instruction of the CPU, that every machine with the same registers and the same values in those bytes
runs the same frames, whatever its other bytes are.

The second part applies this from the state `T` when the pipe's timer has run out, `A` frames after the entry: control comes `B` frames
later for every machine that agrees with `T` on a set `R`. Frames `1..A` are not proved for every entry: `every_entry` takes them as
hypotheses, and the check runs a list of entry states. Page: `PipeTransitionAll.md`.
-/

namespace Smbrta.PipeTransitionAll

open PipeTransition (frame run zeros)

/-! ## Byte arrays -/

theorem ba_size_set (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  cases a
  simp [ByteArray.set!, ByteArray.size]

theorem ba_get_set_self (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) : (a.set! i v).get! i = v := by
  cases a with
  | mk d =>
    simp only [ByteArray.size] at h
    simp [ByteArray.set!, ByteArray.get!, h]

theorem ba_get_set_ne (a : ByteArray) (i j : Nat) (v : UInt8) (h : i ≠ j) : (a.set! i v).get! j = a.get! j := by
  cases a with
  | mk d =>
    simp only [ByteArray.set!, ByteArray.get!]
    rw [Array.set!_eq_setIfInBounds]
    simp only [Array.getElem?_setIfInBounds, h, getElem!_def]
    simp

theorem mask_lt (a : UInt16) : (a &&& 0x7FF).toNat < 2048 := by
  have h : (a &&& 0x7FF).toNat = a.toNat &&& 2047 := by
    simp [UInt16.toNat_and]
  rw [h]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! ## The plain machine next to a tracked one -/

/-- what a plain machine has in place of a tracked one: its RAM, its tracking fields, and an even shift of the two counters -/
structure Emb where
  r : ByteArray
  tr : ByteArray
  tw : ByteArray
  ti : Bool
  dc : Nat
  df : Nat

def plain (e : Emb) (m : Machine) : Machine :=
  { m with ram := e.r, trk := false, trkRead := e.tr, trkWrite := e.tw, trkIO := e.ti,
           cyc := m.cyc + e.dc, frame := m.frame + e.df }

/-- a state action as a plain function -/
def go {α : Type} (f : M α) (m : Machine) : α × Machine := f m

/-- touches neither RAM nor tracking, reads neither, and does not care about an even shift of the counters -/
structure Leaf {α : Type} (f : M α) : Prop where
  comm : ∀ e m, e.dc % 2 = 0 → e.df % 2 = 0 → go f (plain e m) = ((go f m).1, plain e (go f m).2)
  ram : ∀ m, (go f m).2.ram = m.ram
  trk : ∀ m, (go f m).2.trk = m.trk
  rdT : ∀ m, (go f m).2.trkRead = m.trkRead
  wtT : ∀ m, (go f m).2.trkWrite = m.trkWrite

/-- for a leaf with no branches -/
macro "leaf_rfl" : term => `(⟨fun _ _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩)

theorem leaf_pure {α : Type} (a : α) : Leaf (pure a : M α) := leaf_rfl
theorem leaf_setZN (v : UInt8) : Leaf (setZN v) := leaf_rfl
theorem leaf_setFlag (a : UInt8) (b : Bool) : Leaf (setFlag a b) := leaf_rfl
theorem leaf_adc (v : UInt8) : Leaf (adc v) := leaf_rfl
theorem leaf_setPC (a : UInt16) : Leaf (setPC a) := leaf_rfl
def incPC : M UInt16 := fun m => (m.pc, { m with pc := m.pc + 1 })
theorem leaf_incPC : Leaf incPC := leaf_rfl
def decS : M UInt8 := fun m => (m.s, { m with s := m.s - 1 })
theorem leaf_decS : Leaf decS := leaf_rfl
def incS : M UInt8 := fun m => (m.s + 1, { m with s := m.s + 1 })
theorem leaf_incS : Leaf incS := leaf_rfl
def startNmi : M (UInt16 × UInt8) := fun m => ((m.pc, m.p), { m with nmiPending := false })
theorem leaf_startNmi : Leaf startNmi := leaf_rfl
def setAOnly (v : UInt8) : M Unit := modify fun m => { m with a := v }
theorem leaf_setAOnly (v : UInt8) : Leaf (setAOnly v) := leaf_rfl
def bitFlags (v : UInt8) : M Unit :=
  modify fun m => { m with p := (m.p &&& 0x3D) ||| (v &&& 0xC0) ||| (if m.a &&& v == 0 then 0x02 else 0) }
theorem leaf_bitFlags (v : UInt8) : Leaf (bitFlags v) := leaf_rfl
def plpFlags (v : UInt8) : M Unit := modify fun m => { m with p := (v &&& 0xEF) ||| 0x20 }
theorem leaf_plpFlags (v : UInt8) : Leaf (plpFlags v) := leaf_rfl
def laxRegs (v : UInt8) : M Unit := modify (fun m => { m with a := v, x := v })
theorem leaf_laxRegs (v : UInt8) : Leaf (laxRegs v) := leaf_rfl
def setXOnly (v : UInt8) : M Unit := modify fun m => { m with x := v }
theorem leaf_setXOnly (v : UInt8) : Leaf (setXOnly v) := leaf_rfl
def setYOnly (v : UInt8) : M Unit := modify fun m => { m with y := v }
theorem leaf_setYOnly (v : UInt8) : Leaf (setYOnly v) := leaf_rfl
def txs : M Unit := modify fun m => { m with s := m.x }
theorem leaf_txs : Leaf txs := leaf_rfl
def jam : M Unit := modify fun m => { m with halted := true, pc := m.pc - 1 }
theorem leaf_jam : Leaf jam := leaf_rfl

theorem leaf_ppuRead (r : UInt16) : Leaf (ppuRead r) := by
  constructor
  · intro e m _ _
    unfold ppuRead go
    split <;> rfl
  all_goals
    intro m
    unfold ppuRead go
    split <;> rfl

theorem leaf_padRead : Leaf padRead := by
  constructor
  · intro e m _ _
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases padStrobe <;> rfl
  all_goals
    intro m
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases padStrobe <;> rfl

theorem leaf_padWrite (v : UInt8) : Leaf (padWrite v) := by
  constructor
  · intro e m _ _
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      unfold padWrite go
      by_cases h : (v &&& 1 == 1) = true
      · simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h, if_true]
        rfl
      · cases padStrobe <;> simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h, ] <;> rfl
  all_goals
    intro m
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      unfold padWrite go
      by_cases h : (v &&& 1 == 1) = true
      · simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h, if_true]
        rfl
      · cases padStrobe <;> simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h, ] <;> rfl

theorem leaf_ppuWrite (r : UInt16) (v : UInt8) : Leaf (ppuWrite r v) := by
  unfold ppuWrite
  by_cases h0 : (r == 0) = true
  · simp only [h0, if_true]
    exact leaf_rfl
  · by_cases h1 : (r == 1) = true
    · simp only [h0, h1, if_true]
      exact leaf_rfl
    · simp only [h0, h1]
      exact leaf_rfl

/-! `tick`, in pieces -/

def tick1 (b : Bool) (m : Machine) : Machine :=
  if b then { m with vblank := true, nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) } else m
def tick2 (b : Bool) (m : Machine) : Machine := if b then { m with vblank := false, sprite0 := false } else m
def tick3 (b : Bool) (m : Machine) : Machine := if b then { m with sprite0 := true } else m
def tickLen (m : Machine) : Nat :=
  if m.frame % 2 == 1 && (m.ppuMask &&& 0x18 != 0) then dotsPerFrame - 1 else dotsPerFrame
def tick4 (new len : Nat) (m : Machine) : Machine :=
  if new ≥ len then
    if dotVblSet ≤ new - len then
      { m with frame := m.frame + 1, fdot := new - len, vblank := true, nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) }
    else { m with frame := m.frame + 1, fdot := new - len }
  else { m with fdot := new }

theorem tick_eq (c : Nat) (m : Machine) : go (tick c) m =
    let old := m.fdot
    let new := old + 3 * c
    let n := tick3 (old < dotSpr0 && dotSpr0 ≤ new) (tick2 (old < dotVblClr && dotVblClr ≤ new)
      (tick1 (old < dotVblSet && dotVblSet ≤ new) { m with cyc := m.cyc + c }))
    ((), tick4 new (tickLen n) n) := rfl

theorem tick1_plain (b : Bool) (e : Emb) (m : Machine) : tick1 b (plain e m) = plain e (tick1 b m) := by
  cases b <;> rfl
theorem tick2_plain (b : Bool) (e : Emb) (m : Machine) : tick2 b (plain e m) = plain e (tick2 b m) := by
  cases b <;> rfl
theorem tick3_plain (b : Bool) (e : Emb) (m : Machine) : tick3 b (plain e m) = plain e (tick3 b m) := by
  cases b <;> rfl
theorem tickLen_plain (e : Emb) (m : Machine) (h : e.df % 2 = 0) : tickLen (plain e m) = tickLen m := by
  have hfr : (m.frame + e.df) % 2 = m.frame % 2 := by omega
  simp only [tickLen, plain, hfr]
theorem tick4_plain (new len : Nat) (e : Emb) (m : Machine) : tick4 new len (plain e m) = plain e (tick4 new len m) := by
  have hff : m.frame + e.df + 1 = m.frame + 1 + e.df := by omega
  unfold tick4
  split
  · split
    · simp only [plain, hff]
    · simp only [plain, hff]
  · rfl

/-- what `tick` leaves alone -/
structure Kept (a b : Machine) : Prop where
  ram : a.ram = b.ram
  trk : a.trk = b.trk
  rdT : a.trkRead = b.trkRead
  wtT : a.trkWrite = b.trkWrite

theorem Kept.tr {a b c : Machine} (h : Kept a b) (g : Kept b c) : Kept a c :=
  ⟨h.ram.trans g.ram, h.trk.trans g.trk, h.rdT.trans g.rdT, h.wtT.trans g.wtT⟩

theorem tick1_kept (b : Bool) (m : Machine) : Kept (tick1 b m) m := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem tick2_kept (b : Bool) (m : Machine) : Kept (tick2 b m) m := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem tick3_kept (b : Bool) (m : Machine) : Kept (tick3 b m) m := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem tick4_kept (new len : Nat) (m : Machine) : Kept (tick4 new len m) m := by
  unfold tick4
  split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem tick_kept (c : Nat) (m : Machine) : Kept (go (tick c) m).2 m := by
  rw [tick_eq]
  exact (tick4_kept _ _ _).tr <| (tick3_kept _ _).tr <| (tick2_kept _ _).tr <| (tick1_kept _ _).tr ⟨rfl, rfl, rfl, rfl⟩

theorem leaf_tick (c : Nat) : Leaf (tick c) where
  comm e m hc hf := by
    have hcc : ({ plain e m with cyc := (plain e m).cyc + c } : Machine) = plain e { m with cyc := m.cyc + c } := by
      have : m.cyc + e.dc + c = m.cyc + c + e.dc := by omega
      simp only [plain, this]
    rw [tick_eq, tick_eq]
    simp only [hcc]
    have hfd : (plain e m).fdot = m.fdot := rfl
    simp only [hfd, tick1_plain, tick2_plain, tick3_plain, tickLen_plain _ _ hf, tick4_plain]
  ram m := (tick_kept c m).ram
  trk m := (tick_kept c m).trk
  rdT m := (tick_kept c m).rdT
  wtT m := (tick_kept c m).wtT

def dmaLen (m : Machine) : Nat := if m.cyc % 2 == 1 then 514 else 513

theorem oamDma_eq0 : oamDma = (get >>= fun m => tick (if m.cyc % 2 == 1 then 514 else 513)) := rfl
theorem oamDma_eq1 (m : Machine) :
    go (get >>= fun (m : Machine) => tick (if m.cyc % 2 == 1 then 514 else 513)) m = go (tick (if m.cyc % 2 == 1 then 514 else 513)) m := rfl
theorem oamDma_eq2 (m : Machine) : (if m.cyc % 2 == 1 then 514 else 513) = dmaLen m := rfl
theorem oamDma_eq (m : Machine) : go oamDma m = go (tick (dmaLen m)) m := by
  rw [oamDma_eq0, oamDma_eq1, oamDma_eq2]

theorem leaf_oamDma : Leaf oamDma where
  comm e m hc hf := by
    have h : (m.cyc + e.dc) % 2 = m.cyc % 2 := by omega
    have h3 : dmaLen (plain e m) = dmaLen m := by
      simp only [dmaLen, plain, h]
    rw [oamDma_eq, oamDma_eq, h3]
    exact (leaf_tick _).comm e m hc hf
  ram m := by rw [oamDma_eq]; exact (leaf_tick _).ram m
  trk m := by rw [oamDma_eq]; exact (leaf_tick _).trk m
  rdT m := by rw [oamDma_eq]; exact (leaf_tick _).rdT m
  wtT m := by rw [oamDma_eq]; exact (leaf_tick _).wtT m

/-! ## Tracked and plain machines side by side -/

/-- a byte that may differ has been read before anything wrote it -/
def Bad (U : Nat → Bool) (m : Machine) : Prop := ∃ i, i < 2048 ∧ U i = true ∧ m.trkRead.get! i ≠ 0

/-- `m` is tracked, `m'` is plain; they differ in the fields of `Emb`; RAM differs only in bytes of `U` not written yet -/
structure Rel (U : Nat → Bool) (dc df : Nat) (m m' : Machine) : Prop where
  emb : ∃ r tr tw ti, m' = plain ⟨r, tr, tw, ti, dc, df⟩ m
  evc : dc % 2 = 0
  evf : df % 2 = 0
  trk : m.trk = true
  szR : m.trkRead.size = 2048
  szW : m.trkWrite.size = 2048
  szM : m.ram.size = 2048
  szP : m'.ram.size = 2048
  ram : ∀ i, i < 2048 → (U i = false ∨ m.trkWrite.get! i ≠ 0) → m.ram.get! i = m'.ram.get! i

/-- `f` keeps `Bad`, and unless it makes `Bad` it keeps `Rel` and returns the same value on both machines -/
structure RL (U : Nat → Bool) (dc df : Nat) {α : Type} (f : M α) : Prop where
  mono : ∀ m, Bad U m → Bad U (go f m).2
  rel : ∀ m m', Rel U dc df m m' → Bad U (go f m).2 ∨ ((go f m).1 = (go f m').1 ∧ Rel U dc df (go f m).2 (go f m').2)

section
variable {U : Nat → Bool} {dc df : Nat}

theorem RL.ofLeaf {α : Type} {f : M α} (h : Leaf f) : RL U dc df f where
  mono m hb := by
    obtain ⟨i, h1, h2, h3⟩ := hb
    exact ⟨i, h1, h2, by rw [h.rdT]; exact h3⟩
  rel m m' hr := by
    right
    obtain ⟨r, tr, tw, ti, rfl⟩ := hr.emb
    have hc := h.comm ⟨r, tr, tw, ti, dc, df⟩ m hr.evc hr.evf
    rw [hc]
    refine ⟨rfl, ?_⟩
    exact ⟨⟨r, tr, tw, ti, rfl⟩, hr.evc, hr.evf, by rw [h.trk]; exact hr.trk, by rw [h.rdT]; exact hr.szR,
      by rw [h.wtT]; exact hr.szW, by rw [h.ram]; exact hr.szM, hr.szP,
      fun i hi hu => by
        rw [h.ram]
        rw [h.wtT] at hu
        exact hr.ram i hi hu⟩

theorem RL.bind {α β : Type} {f : M α} {g : α → M β} (hf : RL U dc df f) (hg : ∀ a, RL U dc df (g a)) :
    RL U dc df (f >>= g) where
  mono m hb := (hg _).mono _ (hf.mono m hb)
  rel m m' hr := by
    rcases hf.rel m m' hr with hb | ⟨ha, hr'⟩
    · exact Or.inl ((hg _).mono _ hb)
    · have h1 : go (f >>= g) m = go (g (go f m).1) (go f m).2 := rfl
      have h2 : go (f >>= g) m' = go (g (go f m').1) (go f m').2 := rfl
      rw [h1, h2, ← ha]
      exact (hg _).rel _ _ hr'

theorem RL.get' {α : Type} {k : Machine → M α} (hk : ∀ e m, k (plain e m) = k m) (h : ∀ m, RL U dc df (k m)) :
    RL U dc df (get >>= k) where
  mono m hb := (h m).mono m hb
  rel m m' hr := by
    obtain ⟨r, tr, tw, ti, rfl⟩ := hr.emb
    have h1 : go (get >>= k) m = go (k m) m := rfl
    have h2 : go (get >>= k) (plain ⟨r, tr, tw, ti, dc, df⟩ m) = go (k m) (plain ⟨r, tr, tw, ti, dc, df⟩ m) := by
      show go (k (plain ⟨r, tr, tw, ti, dc, df⟩ m)) (plain ⟨r, tr, tw, ti, dc, df⟩ m) = _
      rw [hk]
    rw [h1, h2]
    exact (h m).rel _ _ hr

theorem RL.pure {α : Type} (a : α) : RL U dc df (Pure.pure a : M α) := RL.ofLeaf (leaf_pure a)

theorem go_bind {α β : Type} {f : M α} {g : α → M β} (m : Machine) : go (f >>= g) m = go (g (go f m).1) (go f m).2 := rfl

theorem RL.congr {α : Type} {f g : M α} (h : ∀ m, go f m = go g m) (hg : RL U dc df g) : RL U dc df f where
  mono m hb := by rw [h]; exact hg.mono m hb
  rel m m' hr := by rw [h, h]; exact hg.rel m m' hr

/-! ### RAM and I/O -/

/-- the effect of `trackRead` -/
def trF (i : Nat) (m : Machine) : Machine :=
  if m.trkWrite.get! i == 0 then { m with trkRead := m.trkRead.set! i 1 } else m

theorem ba_set_ne_zero (a : ByteArray) (i j : Nat) (h : a.get! j ≠ 0) : (a.set! i 1).get! j ≠ 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hs : i < a.size
    · rw [ba_get_set_self a i 1 hs]
      decide
    · cases a with
      | mk d =>
        simp only [ByteArray.size] at hs
        simp only [ByteArray.get!, getElem!_def] at h
        simp [hs] at h
        exact absurd rfl h
  · rw [ba_get_set_ne a i j 1 hij]
    exact h

theorem bad_trF {i : Nat} {m : Machine} (h : Bad U m) : Bad U (trF i m) := by
  obtain ⟨j, h1, h2, h3⟩ := h
  unfold trF
  split
  · exact ⟨j, h1, h2, ba_set_ne_zero _ _ _ h3⟩
  · exact ⟨j, h1, h2, h3⟩

/-- a read of RAM on a machine as a function -/
def rdRamF (i : Nat) (m : Machine) : UInt8 × Machine :=
  if m.trk then ((trF i m).ram.get! i, trF i m) else (m.ram.get! i, m)

theorem trF_ram (i : Nat) (m : Machine) : (trF i m).ram = m.ram := by
  unfold trF
  split <;> rfl

theorem rl_rdRamF {i : Nat} (hi : i < 2048) {f : M UInt8} (hf : ∀ m, go f m = rdRamF i m) : RL U dc df f where
  mono m hb := by
    rw [hf]
    unfold rdRamF
    split
    · exact bad_trF hb
    · exact hb
  rel m m' hr := by
    obtain ⟨r, tr, tw, ti, rfl⟩ := hr.emb
    rw [hf, hf]
    have h1 : rdRamF i m = ((trF i m).ram.get! i, trF i m) := by
      unfold rdRamF
      rw [if_pos hr.trk]
    have h2 : rdRamF i (plain ⟨r, tr, tw, ti, dc, df⟩ m) = (r.get! i, plain ⟨r, tr, tw, ti, dc, df⟩ m) := rfl
    rw [h1, h2]
    by_cases hb : U i = true ∧ m.trkWrite.get! i = 0
    · left
      obtain ⟨hu, hw⟩ := hb
      refine ⟨i, hi, hu, ?_⟩
      have : trF i m = { m with trkRead := m.trkRead.set! i 1 } := by
        unfold trF
        rw [if_pos (by simp [hw])]
      show (trF i m).trkRead.get! i ≠ 0
      rw [this]
      show (m.trkRead.set! i 1).get! i ≠ 0
      rw [ba_get_set_self _ _ _ (by rw [hr.szR]; exact hi)]
      decide
    · right
      have hh : U i = false ∨ m.trkWrite.get! i ≠ 0 := by
        by_cases hu : U i = true
        · exact Or.inr (fun hw => hb ⟨hu, hw⟩)
        · exact Or.inl (by simpa using hu)
      have hv := hr.ram i hi hh
      have hrm := trF_ram i m
      have hwt : (trF i m).trkWrite = m.trkWrite := by
        unfold trF
        split <;> rfl
      have hrd : (trF i m).trkRead.size = 2048 := by
        unfold trF
        split
        · show (m.trkRead.set! i 1).size = 2048
          rw [ba_size_set]; exact hr.szR
        · exact hr.szR
      have htk : (trF i m).trk = m.trk := by
        unfold trF
        split <;> rfl
      have hpl : plain ⟨r, tr, tw, ti, dc, df⟩ (trF i m) = plain ⟨r, tr, tw, ti, dc, df⟩ m := by
        unfold trF
        split <;> rfl
      refine ⟨?_, ⟨r, tr, tw, ti, hpl.symm⟩, hr.evc, hr.evf, by rw [htk]; exact hr.trk, hrd,
        by rw [hwt]; exact hr.szW, by rw [hrm]; exact hr.szM, hr.szP, ?_⟩
      · show (trF i m).ram.get! i = r.get! i
        rw [hrm]
        exact hv
      · intro j hj hu
        rw [hrm]
        rw [hwt] at hu
        exact hr.ram j hj hu

/-- marks an I/O read -/
def ioMark : M Unit := fun m => ((), if m.trk then { m with trkIO := true } else m)

theorem leaf_ioMark : Leaf ioMark := by
  constructor
  · intro e m _ _
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  all_goals
    intro m
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl

def romRead (addr : UInt16) : M UInt8 := do
  let m ← get
  return m.prg.get! (addr &&& m.prgMask).toNat

theorem leaf_romRead (addr : UInt16) : Leaf (romRead addr) := leaf_rfl

theorem rl_rd (addr : UInt16) : RL U dc df (rd addr) := by
  by_cases h1 : addr < 0x2000
  · refine rl_rdRamF (mask_lt addr) ?_
    intro m
    unfold rd go
    rw [if_pos h1]
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  · by_cases h2 : addr ≥ 0x8000
    · refine RL.congr (g := romRead addr) ?_ (RL.ofLeaf (leaf_romRead addr))
      intro m
      unfold rd go
      rw [if_neg h1, if_pos h2]
      rfl
    · by_cases h3 : addr < 0x4000
      · refine RL.congr (g := ioMark >>= fun _ => ppuRead (addr &&& 7)) ?_
          (RL.bind (RL.ofLeaf leaf_ioMark) fun _ => RL.ofLeaf (leaf_ppuRead _))
        intro m
        unfold rd go
        rw [if_neg h1, if_neg h2, if_pos h3]
        cases m with
        | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
          cases trk <;> rfl
      · by_cases h4 : (addr == 0x4016) = true
        · refine RL.congr (g := ioMark >>= fun _ => padRead) ?_
            (RL.bind (RL.ofLeaf leaf_ioMark) fun _ => RL.ofLeaf leaf_padRead)
          intro m
          unfold rd go
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          cases m with
          | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
            cases trk <;> rfl
        · by_cases h5 : (addr == 0x4017) = true
          · refine RL.congr (g := Pure.pure 0x40) ?_ (RL.pure _)
            intro m
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
          · refine RL.congr (g := Pure.pure 0) ?_ (RL.pure _)
            intro m
            unfold rd go
            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- a write to RAM on a machine as a function -/
def wrRamF (i : Nat) (v : UInt8) (m : Machine) : Machine :=
  if m.trk then { m with ram := m.ram.set! i v, trkWrite := m.trkWrite.set! i 1 } else { m with ram := m.ram.set! i v }

theorem rl_wrRamF {i : Nat} {v : UInt8} (hi : i < 2048) {f : M Unit} (hf : ∀ m, go f m = ((), wrRamF i v m)) : RL U dc df f where
  mono m hb := by
    rw [hf]
    obtain ⟨j, h1, h2, h3⟩ := hb
    refine ⟨j, h1, h2, ?_⟩
    unfold wrRamF
    split <;> exact h3
  rel m m' hr := by
    obtain ⟨r, tr, tw, ti, rfl⟩ := hr.emb
    rw [hf, hf]
    right
    refine ⟨rfl, ?_⟩
    have h1 : wrRamF i v m = { m with ram := m.ram.set! i v, trkWrite := m.trkWrite.set! i 1 } := by
      unfold wrRamF
      rw [if_pos hr.trk]
    have h2 : wrRamF i v (plain ⟨r, tr, tw, ti, dc, df⟩ m) = plain ⟨r.set! i v, tr, tw, ti, dc, df⟩ m := rfl
    simp only [h1, h2]
    have hszP : r.size = 2048 := hr.szP
    refine ⟨⟨r.set! i v, tr, tw, ti, rfl⟩, hr.evc, hr.evf, hr.trk, hr.szR, ?_, ?_, ?_, ?_⟩
    · show (m.trkWrite.set! i 1).size = 2048
      rw [ba_size_set]; exact hr.szW
    · show (m.ram.set! i v).size = 2048
      rw [ba_size_set]; exact hr.szM
    · show (r.set! i v).size = 2048
      rw [ba_size_set]; exact hszP
    · intro j hj hu
      show (m.ram.set! i v).get! j = (r.set! i v).get! j
      by_cases hij : i = j
      · subst hij
        rw [ba_get_set_self _ _ _ (by rw [hr.szM]; exact hi), ba_get_set_self _ _ _ (by rw [hszP]; exact hi)]
      · rw [ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij]
        refine hr.ram j hj ?_
        rcases hu with hu | hu
        · exact Or.inl hu
        · refine Or.inr ?_
          have : (m.trkWrite.set! i 1).get! j ≠ 0 := hu
          rwa [ba_get_set_ne _ _ _ _ hij] at this

theorem rl_wr (addr : UInt16) (v : UInt8) : RL U dc df (wr addr v) := by
  by_cases h1 : addr < 0x2000
  · refine rl_wrRamF (v := v) (mask_lt addr) ?_
    intro m
    unfold wr go
    rw [if_pos h1]
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  · by_cases h2 : addr < 0x4000
    · refine RL.congr (g := ppuWrite (addr &&& 7) v) ?_ (RL.ofLeaf (leaf_ppuWrite _ _))
      intro m
      unfold wr go
      rw [if_neg h1, if_pos h2]
    · by_cases h3 : (addr == 0x4014) = true
      · refine RL.congr (g := oamDma) ?_ (RL.ofLeaf leaf_oamDma)
        intro m
        unfold wr go
        rw [if_neg h1, if_neg h2, if_pos h3]
      · by_cases h4 : (addr == 0x4016) = true
        · refine RL.congr (g := padWrite v) ?_ (RL.ofLeaf (leaf_padWrite v))
          intro m
          unfold wr go
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
        · refine RL.congr (g := Pure.pure ()) ?_ (RL.pure _)
          intro m
          unfold wr go
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-! ### The instructions -/

theorem rl_fetch : RL U dc df fetch :=
  RL.congr (g := incPC >>= rd) (fun _ => rfl) (RL.bind (RL.ofLeaf leaf_incPC) rl_rd)
theorem rl_fetch16 : RL U dc df fetch16 :=
  RL.bind rl_fetch fun _ => RL.bind rl_fetch fun _ => RL.pure _
theorem rl_rd16zp (z : UInt8) : RL U dc df (rd16zp z) :=
  RL.bind (rl_rd _) fun _ => RL.bind (rl_rd _) fun _ => RL.pure _

theorem rl_mImm : RL U dc df mImm := RL.ofLeaf leaf_incPC
theorem rl_mZp : RL U dc df mZp := RL.bind rl_fetch fun _ => RL.pure _
theorem rl_mZpx : RL U dc df mZpx :=
  RL.bind rl_fetch fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.pure _
theorem rl_mZpy : RL U dc df mZpy :=
  RL.bind rl_fetch fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.pure _
theorem rl_mAbs : RL U dc df mAbs := rl_fetch16
theorem rl_pagePenalty (b e : UInt16) : RL U dc df (pagePenalty b e) := by
  unfold pagePenalty
  split
  · exact RL.ofLeaf (leaf_tick 1)
  · exact RL.pure _
theorem rl_mAbx : RL U dc df mAbx :=
  RL.bind rl_fetch16 fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.pure _
theorem rl_mAby : RL U dc df mAby :=
  RL.bind rl_fetch16 fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.pure _
theorem rl_mAbxR : RL U dc df mAbxR :=
  RL.bind rl_fetch16 fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.bind (rl_pagePenalty _ _) fun _ => RL.pure _
theorem rl_mAbyR : RL U dc df mAbyR :=
  RL.bind rl_fetch16 fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.bind (rl_pagePenalty _ _) fun _ => RL.pure _
theorem rl_mIzx : RL U dc df mIzx :=
  RL.bind rl_fetch fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_rd16zp _
theorem rl_mIzy : RL U dc df mIzy :=
  RL.bind rl_fetch fun _ => RL.bind (rl_rd16zp _) fun _ => RL.get' (fun _ _ => rfl) fun _ => RL.pure _
theorem rl_mIzyR : RL U dc df mIzyR :=
  RL.bind rl_fetch fun _ => RL.bind (rl_rd16zp _) fun _ => RL.get' (fun _ _ => rfl) fun _ =>
    RL.bind (rl_pagePenalty _ _) fun _ => RL.pure _

theorem rl_setZN (v : UInt8) : RL U dc df (setZN v) := RL.ofLeaf (leaf_setZN v)
theorem rl_setFlag (a : UInt8) (b : Bool) : RL U dc df (setFlag a b) := RL.ofLeaf (leaf_setFlag a b)
theorem rl_setA (v : UInt8) : RL U dc df (setA v) := RL.bind (RL.ofLeaf (leaf_setAOnly v)) fun _ => rl_setZN v
theorem rl_setX (v : UInt8) : RL U dc df (setX v) := RL.bind (RL.ofLeaf (leaf_setXOnly v)) fun _ => rl_setZN v
theorem rl_setY (v : UInt8) : RL U dc df (setY v) := RL.bind (RL.ofLeaf (leaf_setYOnly v)) fun _ => rl_setZN v
theorem rl_push (v : UInt8) : RL U dc df (push v) :=
  RL.congr (g := decS >>= fun sp => wr (0x100 ||| sp.toUInt16) v) (fun _ => rfl)
    (RL.bind (RL.ofLeaf leaf_decS) fun _ => rl_wr _ _)
theorem rl_pull : RL U dc df pull :=
  RL.congr (g := incS >>= fun sp => rd (0x100 ||| sp.toUInt16)) (fun _ => rfl)
    (RL.bind (RL.ofLeaf leaf_incS) fun _ => rl_rd _)
theorem rl_setPC (a : UInt16) : RL U dc df (setPC a) := RL.ofLeaf (leaf_setPC a)
theorem rl_adc (v : UInt8) : RL U dc df (adc v) := RL.ofLeaf (leaf_adc v)
theorem rl_oraV (v : UInt8) : RL U dc df (oraV v) := RL.get' (fun _ _ => rfl) fun _ => rl_setA _
theorem rl_andV (v : UInt8) : RL U dc df (andV v) := RL.get' (fun _ _ => rfl) fun _ => rl_setA _
theorem rl_eorV (v : UInt8) : RL U dc df (eorV v) := RL.get' (fun _ _ => rfl) fun _ => rl_setA _
theorem rl_cmpV (r v : UInt8) : RL U dc df (cmpV r v) := RL.bind (rl_setZN _) fun _ => rl_setFlag _ _
theorem rl_aslV (v : UInt8) : RL U dc df (aslV v) :=
  RL.bind (rl_setFlag _ _) fun _ => RL.bind (rl_setZN _) fun _ => RL.pure _
theorem rl_lsrV (v : UInt8) : RL U dc df (lsrV v) :=
  RL.bind (rl_setFlag _ _) fun _ => RL.bind (rl_setZN _) fun _ => RL.pure _
theorem rl_rolV (v : UInt8) : RL U dc df (rolV v) :=
  RL.get' (fun _ _ => rfl) fun _ => RL.bind (rl_setFlag _ _) fun _ => RL.bind (rl_setZN _) fun _ => RL.pure _
theorem rl_rorV (v : UInt8) : RL U dc df (rorV v) :=
  RL.get' (fun _ _ => rfl) fun _ => RL.bind (rl_setFlag _ _) fun _ => RL.bind (rl_setZN _) fun _ => RL.pure _
theorem rl_incV (v : UInt8) : RL U dc df (incV v) := RL.bind (rl_setZN _) fun _ => RL.pure _
theorem rl_decV (v : UInt8) : RL U dc df (decV v) := RL.bind (rl_setZN _) fun _ => RL.pure _

section
variable {md : Mode}

theorem rl_opLDA (h : RL U dc df md) : RL U dc df (opLDA md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_setA _
theorem rl_opLDX (h : RL U dc df md) : RL U dc df (opLDX md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_setX _
theorem rl_opLDY (h : RL U dc df md) : RL U dc df (opLDY md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_setY _
theorem rl_opLAX (h : RL U dc df md) : RL U dc df (opLAX md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.bind (RL.ofLeaf (leaf_laxRegs _)) fun _ => rl_setZN _
theorem rl_opSTA (h : RL U dc df md) : RL U dc df (opSTA md) :=
  RL.bind h fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_wr _ _
theorem rl_opSTX (h : RL U dc df md) : RL U dc df (opSTX md) :=
  RL.bind h fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_wr _ _
theorem rl_opSTY (h : RL U dc df md) : RL U dc df (opSTY md) :=
  RL.bind h fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_wr _ _
theorem rl_opSAX (h : RL U dc df md) : RL U dc df (opSAX md) :=
  RL.bind h fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_wr _ _
theorem rl_opADC (h : RL U dc df md) : RL U dc df (opADC md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_adc _
theorem rl_opSBC (h : RL U dc df md) : RL U dc df (opSBC md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_adc _
theorem rl_opORA (h : RL U dc df md) : RL U dc df (opORA md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_oraV _
theorem rl_opAND (h : RL U dc df md) : RL U dc df (opAND md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_andV _
theorem rl_opEOR (h : RL U dc df md) : RL U dc df (opEOR md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => rl_eorV _
theorem rl_opCMP (h : RL U dc df md) : RL U dc df (opCMP md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_cmpV _ _
theorem rl_opCPX (h : RL U dc df md) : RL U dc df (opCPX md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_cmpV _ _
theorem rl_opCPY (h : RL U dc df md) : RL U dc df (opCPY md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_cmpV _ _
theorem rl_opBIT (h : RL U dc df md) : RL U dc df (opBIT md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.ofLeaf (leaf_bitFlags _)

theorem rl_rmw {f : UInt8 → M UInt8} (hf : ∀ v, RL U dc df (f v)) (h : RL U dc df md) : RL U dc df (rmw f md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.bind (hf _) fun _ => rl_wr _ _
theorem rl_rmw2 {f : UInt8 → M UInt8} {g : UInt8 → M Unit} (hf : ∀ v, RL U dc df (f v)) (hg : ∀ v, RL U dc df (g v))
    (h : RL U dc df md) : RL U dc df (rmw2 f g md) :=
  RL.bind h fun _ => RL.bind (rl_rd _) fun _ => RL.bind (hf _) fun _ => RL.bind (rl_wr _ _) fun _ => hg _
theorem rl_accOp {f : UInt8 → M UInt8} (hf : ∀ v, RL U dc df (f v)) : RL U dc df (accOp f) :=
  RL.get' (fun _ _ => rfl) fun _ => RL.bind (hf _) fun _ => RL.ofLeaf (leaf_setAOnly _)

theorem rl_opASL (h : RL U dc df md) : RL U dc df (opASL md) := rl_rmw rl_aslV h
theorem rl_opLSR (h : RL U dc df md) : RL U dc df (opLSR md) := rl_rmw rl_lsrV h
theorem rl_opROL (h : RL U dc df md) : RL U dc df (opROL md) := rl_rmw rl_rolV h
theorem rl_opROR (h : RL U dc df md) : RL U dc df (opROR md) := rl_rmw rl_rorV h
theorem rl_opINC (h : RL U dc df md) : RL U dc df (opINC md) := rl_rmw rl_incV h
theorem rl_opDEC (h : RL U dc df md) : RL U dc df (opDEC md) := rl_rmw rl_decV h
theorem rl_opSLO (h : RL U dc df md) : RL U dc df (opSLO md) := rl_rmw2 rl_aslV rl_oraV h
theorem rl_opRLA (h : RL U dc df md) : RL U dc df (opRLA md) := rl_rmw2 rl_rolV rl_andV h
theorem rl_opSRE (h : RL U dc df md) : RL U dc df (opSRE md) := rl_rmw2 rl_lsrV rl_eorV h
theorem rl_opRRA (h : RL U dc df md) : RL U dc df (opRRA md) := rl_rmw2 rl_rorV rl_adc h
theorem rl_opDCP (h : RL U dc df md) : RL U dc df (opDCP md) :=
  rl_rmw2 (fun _ => RL.pure _) (fun _ => RL.get' (fun _ _ => rfl) fun _ => rl_cmpV _ _) h
theorem rl_opISB (h : RL U dc df md) : RL U dc df (opISB md) :=
  rl_rmw2 (fun _ => RL.pure _) (fun _ => rl_adc _) h
theorem rl_opNOPm (h : RL U dc df md) : RL U dc df (opNOPm md) :=
  RL.bind h fun _ => RL.pure _
end

theorem rl_opNOP : RL U dc df opNOP := RL.pure _
theorem rl_opJAM : RL U dc df opJAM := RL.ofLeaf leaf_jam

theorem rl_branch {cond : Machine → Bool} (hc : ∀ e m, cond (plain e m) = cond m) : RL U dc df (branch cond) := by
  refine RL.bind rl_fetch fun off => RL.get' (fun e m => ?_) fun m => ?_
  · simp only [hc]
    rfl
  · split
    · exact RL.bind (rl_setPC _) fun _ => RL.ofLeaf (leaf_tick _)
    · exact RL.pure _

theorem rl_opBPL : RL U dc df opBPL := rl_branch fun _ _ => rfl
theorem rl_opBMI : RL U dc df opBMI := rl_branch fun _ _ => rfl
theorem rl_opBVC : RL U dc df opBVC := rl_branch fun _ _ => rfl
theorem rl_opBVS : RL U dc df opBVS := rl_branch fun _ _ => rfl
theorem rl_opBCC : RL U dc df opBCC := rl_branch fun _ _ => rfl
theorem rl_opBCS : RL U dc df opBCS := rl_branch fun _ _ => rfl
theorem rl_opBNE : RL U dc df opBNE := rl_branch fun _ _ => rfl
theorem rl_opBEQ : RL U dc df opBEQ := rl_branch fun _ _ => rfl

theorem rl_opCLC : RL U dc df opCLC := rl_setFlag _ _
theorem rl_opSEC : RL U dc df opSEC := rl_setFlag _ _
theorem rl_opCLI : RL U dc df opCLI := rl_setFlag _ _
theorem rl_opSEI : RL U dc df opSEI := rl_setFlag _ _
theorem rl_opCLV : RL U dc df opCLV := rl_setFlag _ _
theorem rl_opCLD : RL U dc df opCLD := rl_setFlag _ _
theorem rl_opSED : RL U dc df opSED := rl_setFlag _ _

theorem rl_opTAX : RL U dc df opTAX := RL.get' (fun _ _ => rfl) fun _ => rl_setX _
theorem rl_opTAY : RL U dc df opTAY := RL.get' (fun _ _ => rfl) fun _ => rl_setY _
theorem rl_opTXA : RL U dc df opTXA := RL.get' (fun _ _ => rfl) fun _ => rl_setA _
theorem rl_opTYA : RL U dc df opTYA := RL.get' (fun _ _ => rfl) fun _ => rl_setA _
theorem rl_opTSX : RL U dc df opTSX := RL.get' (fun _ _ => rfl) fun _ => rl_setX _
theorem rl_opTXS : RL U dc df opTXS := RL.ofLeaf leaf_txs
theorem rl_opINX : RL U dc df opINX := RL.get' (fun _ _ => rfl) fun _ => rl_setX _
theorem rl_opINY : RL U dc df opINY := RL.get' (fun _ _ => rfl) fun _ => rl_setY _
theorem rl_opDEX : RL U dc df opDEX := RL.get' (fun _ _ => rfl) fun _ => rl_setX _
theorem rl_opDEY : RL U dc df opDEY := RL.get' (fun _ _ => rfl) fun _ => rl_setY _

theorem rl_opPHA : RL U dc df opPHA := RL.get' (fun _ _ => rfl) fun _ => rl_push _
theorem rl_opPHP : RL U dc df opPHP := RL.get' (fun _ _ => rfl) fun _ => rl_push _
theorem rl_opPLA : RL U dc df opPLA := RL.bind rl_pull fun _ => rl_setA _
theorem rl_opPLP : RL U dc df opPLP := RL.bind rl_pull fun _ => RL.ofLeaf (leaf_plpFlags _)

theorem rl_opJMP : RL U dc df opJMP := RL.bind rl_fetch16 fun _ => rl_setPC _
theorem rl_opJMPi : RL U dc df opJMPi :=
  RL.bind rl_fetch16 fun _ => RL.bind (rl_rd _) fun _ => RL.bind (rl_rd _) fun _ => rl_setPC _
theorem rl_opJSR : RL U dc df opJSR :=
  RL.bind rl_fetch16 fun _ => RL.get' (fun _ _ => rfl) fun _ =>
    RL.bind (rl_push _) fun _ => RL.bind (rl_push _) fun _ => rl_setPC _
theorem rl_opRTS : RL U dc df opRTS :=
  RL.bind rl_pull fun _ => RL.bind rl_pull fun _ => rl_setPC _
theorem rl_opRTI : RL U dc df opRTI :=
  RL.bind rl_opPLP fun _ => RL.bind rl_pull fun _ => RL.bind rl_pull fun _ => rl_setPC _
theorem rl_interrupt (pc : UInt16) (p : UInt8) (v : UInt16) : RL U dc df (interrupt pc p v) :=
  RL.bind (rl_push _) fun _ => RL.bind (rl_push _) fun _ => RL.bind (rl_push _) fun _ =>
    RL.bind (rl_setFlag _ _) fun _ => RL.bind (rl_rd _) fun _ => RL.bind (rl_rd _) fun _ => rl_setPC _
theorem rl_opBRK : RL U dc df opBRK := RL.get' (fun _ _ => rfl) fun _ => rl_interrupt _ _ _
theorem nmi_eq (m : Machine) : go nmi m =
    go (interrupt m.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA >>= fun _ => tick 7) { m with nmiPending := false } := by
  unfold nmi go
  rfl
theorem rl_nmi : RL U dc df nmi :=
  RL.congr (g := startNmi >>= fun q => interrupt q.1 ((q.2 &&& 0xEF) ||| 0x20) 0xFFFA >>= fun _ => tick 7)
    (fun m => by
      rw [nmi_eq, go_bind (f := startNmi)]
      rw [show go startNmi m = ((m.pc, m.p), { m with nmiPending := false }) from rfl])
    (RL.bind (RL.ofLeaf leaf_startNmi) fun _ => RL.bind (rl_interrupt _ _ _) fun _ => RL.ofLeaf (leaf_tick 7))


/-- every element of a list satisfies `RL` -/
def AllRL (U : Nat → Bool) (dc df : Nat) : List (M Unit) → Prop
  | [] => True
  | x :: l => RL U dc df x ∧ AllRL U dc df l

theorem AllRL.get {l : List (M Unit)} (h : AllRL U dc df l) : ∀ (n : Nat) (d : M Unit), RL U dc df d → RL U dc df (l[n]?.getD d) := by
  induction l with
  | nil =>
    intro n d hd
    simpa using hd
  | cons x l ih =>
    intro n d hd
    cases n with
    | zero => simpa using h.1
    | succ n => simpa using ih h.2 n d hd

theorem AllRL.append {a b : List (M Unit)} (ha : AllRL U dc df a) (hb : AllRL U dc df b) : AllRL U dc df (a ++ b) := by
  induction a with
  | nil => simpa using hb
  | cons x l ih => exact ⟨ha.1, ih ha.2⟩

def row0 : List (M Unit) := [opBRK, opORA mIzx, opJAM, opSLO mIzx, opNOPm mZp, opORA mZp, opASL mZp, opSLO mZp, opPHP, opORA mImm, accOp aslV, opJAM, opNOPm mAbs, opORA mAbs, opASL mAbs, opSLO mAbs]
theorem rl_row0 : AllRL U dc df row0 := ⟨rl_opBRK, (rl_opORA rl_mIzx), rl_opJAM, (rl_opSLO rl_mIzx), (rl_opNOPm rl_mZp), (rl_opORA rl_mZp), (rl_opASL rl_mZp), (rl_opSLO rl_mZp), rl_opPHP, (rl_opORA rl_mImm), (rl_accOp rl_aslV), rl_opJAM, (rl_opNOPm rl_mAbs), (rl_opORA rl_mAbs), (rl_opASL rl_mAbs), (rl_opSLO rl_mAbs), trivial⟩
def row1 : List (M Unit) := [opBPL, opORA mIzyR, opJAM, opSLO mIzy, opNOPm mZpx, opORA mZpx, opASL mZpx, opSLO mZpx, opCLC, opORA mAbyR, opNOP, opSLO mAby, opNOPm mAbxR, opORA mAbxR, opASL mAbx, opSLO mAbx]
theorem rl_row1 : AllRL U dc df row1 := ⟨rl_opBPL, (rl_opORA rl_mIzyR), rl_opJAM, (rl_opSLO rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opORA rl_mZpx), (rl_opASL rl_mZpx), (rl_opSLO rl_mZpx), rl_opCLC, (rl_opORA rl_mAbyR), rl_opNOP, (rl_opSLO rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opORA rl_mAbxR), (rl_opASL rl_mAbx), (rl_opSLO rl_mAbx), trivial⟩
def row2 : List (M Unit) := [opJSR, opAND mIzx, opJAM, opRLA mIzx, opBIT mZp, opAND mZp, opROL mZp, opRLA mZp, opPLP, opAND mImm, accOp rolV, opJAM, opBIT mAbs, opAND mAbs, opROL mAbs, opRLA mAbs]
theorem rl_row2 : AllRL U dc df row2 := ⟨rl_opJSR, (rl_opAND rl_mIzx), rl_opJAM, (rl_opRLA rl_mIzx), (rl_opBIT rl_mZp), (rl_opAND rl_mZp), (rl_opROL rl_mZp), (rl_opRLA rl_mZp), rl_opPLP, (rl_opAND rl_mImm), (rl_accOp rl_rolV), rl_opJAM, (rl_opBIT rl_mAbs), (rl_opAND rl_mAbs), (rl_opROL rl_mAbs), (rl_opRLA rl_mAbs), trivial⟩
def row3 : List (M Unit) := [opBMI, opAND mIzyR, opJAM, opRLA mIzy, opNOPm mZpx, opAND mZpx, opROL mZpx, opRLA mZpx, opSEC, opAND mAbyR, opNOP, opRLA mAby, opNOPm mAbxR, opAND mAbxR, opROL mAbx, opRLA mAbx]
theorem rl_row3 : AllRL U dc df row3 := ⟨rl_opBMI, (rl_opAND rl_mIzyR), rl_opJAM, (rl_opRLA rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opAND rl_mZpx), (rl_opROL rl_mZpx), (rl_opRLA rl_mZpx), rl_opSEC, (rl_opAND rl_mAbyR), rl_opNOP, (rl_opRLA rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opAND rl_mAbxR), (rl_opROL rl_mAbx), (rl_opRLA rl_mAbx), trivial⟩
def row4 : List (M Unit) := [opRTI, opEOR mIzx, opJAM, opSRE mIzx, opNOPm mZp, opEOR mZp, opLSR mZp, opSRE mZp, opPHA, opEOR mImm, accOp lsrV, opJAM, opJMP, opEOR mAbs, opLSR mAbs, opSRE mAbs]
theorem rl_row4 : AllRL U dc df row4 := ⟨rl_opRTI, (rl_opEOR rl_mIzx), rl_opJAM, (rl_opSRE rl_mIzx), (rl_opNOPm rl_mZp), (rl_opEOR rl_mZp), (rl_opLSR rl_mZp), (rl_opSRE rl_mZp), rl_opPHA, (rl_opEOR rl_mImm), (rl_accOp rl_lsrV), rl_opJAM, rl_opJMP, (rl_opEOR rl_mAbs), (rl_opLSR rl_mAbs), (rl_opSRE rl_mAbs), trivial⟩
def row5 : List (M Unit) := [opBVC, opEOR mIzyR, opJAM, opSRE mIzy, opNOPm mZpx, opEOR mZpx, opLSR mZpx, opSRE mZpx, opCLI, opEOR mAbyR, opNOP, opSRE mAby, opNOPm mAbxR, opEOR mAbxR, opLSR mAbx, opSRE mAbx]
theorem rl_row5 : AllRL U dc df row5 := ⟨rl_opBVC, (rl_opEOR rl_mIzyR), rl_opJAM, (rl_opSRE rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opEOR rl_mZpx), (rl_opLSR rl_mZpx), (rl_opSRE rl_mZpx), rl_opCLI, (rl_opEOR rl_mAbyR), rl_opNOP, (rl_opSRE rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opEOR rl_mAbxR), (rl_opLSR rl_mAbx), (rl_opSRE rl_mAbx), trivial⟩
def row6 : List (M Unit) := [opRTS, opADC mIzx, opJAM, opRRA mIzx, opNOPm mZp, opADC mZp, opROR mZp, opRRA mZp, opPLA, opADC mImm, accOp rorV, opJAM, opJMPi, opADC mAbs, opROR mAbs, opRRA mAbs]
theorem rl_row6 : AllRL U dc df row6 := ⟨rl_opRTS, (rl_opADC rl_mIzx), rl_opJAM, (rl_opRRA rl_mIzx), (rl_opNOPm rl_mZp), (rl_opADC rl_mZp), (rl_opROR rl_mZp), (rl_opRRA rl_mZp), rl_opPLA, (rl_opADC rl_mImm), (rl_accOp rl_rorV), rl_opJAM, rl_opJMPi, (rl_opADC rl_mAbs), (rl_opROR rl_mAbs), (rl_opRRA rl_mAbs), trivial⟩
def row7 : List (M Unit) := [opBVS, opADC mIzyR, opJAM, opRRA mIzy, opNOPm mZpx, opADC mZpx, opROR mZpx, opRRA mZpx, opSEI, opADC mAbyR, opNOP, opRRA mAby, opNOPm mAbxR, opADC mAbxR, opROR mAbx, opRRA mAbx]
theorem rl_row7 : AllRL U dc df row7 := ⟨rl_opBVS, (rl_opADC rl_mIzyR), rl_opJAM, (rl_opRRA rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opADC rl_mZpx), (rl_opROR rl_mZpx), (rl_opRRA rl_mZpx), rl_opSEI, (rl_opADC rl_mAbyR), rl_opNOP, (rl_opRRA rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opADC rl_mAbxR), (rl_opROR rl_mAbx), (rl_opRRA rl_mAbx), trivial⟩
def row8 : List (M Unit) := [opNOPm mImm, opSTA mIzx, opNOPm mImm, opSAX mIzx, opSTY mZp, opSTA mZp, opSTX mZp, opSAX mZp, opDEY, opNOPm mImm, opTXA, opJAM, opSTY mAbs, opSTA mAbs, opSTX mAbs, opSAX mAbs]
theorem rl_row8 : AllRL U dc df row8 := ⟨(rl_opNOPm rl_mImm), (rl_opSTA rl_mIzx), (rl_opNOPm rl_mImm), (rl_opSAX rl_mIzx), (rl_opSTY rl_mZp), (rl_opSTA rl_mZp), (rl_opSTX rl_mZp), (rl_opSAX rl_mZp), rl_opDEY, (rl_opNOPm rl_mImm), rl_opTXA, rl_opJAM, (rl_opSTY rl_mAbs), (rl_opSTA rl_mAbs), (rl_opSTX rl_mAbs), (rl_opSAX rl_mAbs), trivial⟩
def row9 : List (M Unit) := [opBCC, opSTA mIzy, opJAM, opJAM, opSTY mZpx, opSTA mZpx, opSTX mZpy, opSAX mZpy, opTYA, opSTA mAby, opTXS, opJAM, opJAM, opSTA mAbx, opJAM, opJAM]
theorem rl_row9 : AllRL U dc df row9 := ⟨rl_opBCC, (rl_opSTA rl_mIzy), rl_opJAM, rl_opJAM, (rl_opSTY rl_mZpx), (rl_opSTA rl_mZpx), (rl_opSTX rl_mZpy), (rl_opSAX rl_mZpy), rl_opTYA, (rl_opSTA rl_mAby), rl_opTXS, rl_opJAM, rl_opJAM, (rl_opSTA rl_mAbx), rl_opJAM, rl_opJAM, trivial⟩
def rowA : List (M Unit) := [opLDY mImm, opLDA mIzx, opLDX mImm, opLAX mIzx, opLDY mZp, opLDA mZp, opLDX mZp, opLAX mZp, opTAY, opLDA mImm, opTAX, opJAM, opLDY mAbs, opLDA mAbs, opLDX mAbs, opLAX mAbs]
theorem rl_rowA : AllRL U dc df rowA := ⟨(rl_opLDY rl_mImm), (rl_opLDA rl_mIzx), (rl_opLDX rl_mImm), (rl_opLAX rl_mIzx), (rl_opLDY rl_mZp), (rl_opLDA rl_mZp), (rl_opLDX rl_mZp), (rl_opLAX rl_mZp), rl_opTAY, (rl_opLDA rl_mImm), rl_opTAX, rl_opJAM, (rl_opLDY rl_mAbs), (rl_opLDA rl_mAbs), (rl_opLDX rl_mAbs), (rl_opLAX rl_mAbs), trivial⟩
def rowB : List (M Unit) := [opBCS, opLDA mIzyR, opJAM, opLAX mIzyR, opLDY mZpx, opLDA mZpx, opLDX mZpy, opLAX mZpy, opCLV, opLDA mAbyR, opTSX, opJAM, opLDY mAbxR, opLDA mAbxR, opLDX mAbyR, opLAX mAbyR]
theorem rl_rowB : AllRL U dc df rowB := ⟨rl_opBCS, (rl_opLDA rl_mIzyR), rl_opJAM, (rl_opLAX rl_mIzyR), (rl_opLDY rl_mZpx), (rl_opLDA rl_mZpx), (rl_opLDX rl_mZpy), (rl_opLAX rl_mZpy), rl_opCLV, (rl_opLDA rl_mAbyR), rl_opTSX, rl_opJAM, (rl_opLDY rl_mAbxR), (rl_opLDA rl_mAbxR), (rl_opLDX rl_mAbyR), (rl_opLAX rl_mAbyR), trivial⟩
def rowC : List (M Unit) := [opCPY mImm, opCMP mIzx, opNOPm mImm, opDCP mIzx, opCPY mZp, opCMP mZp, opDEC mZp, opDCP mZp, opINY, opCMP mImm, opDEX, opJAM, opCPY mAbs, opCMP mAbs, opDEC mAbs, opDCP mAbs]
theorem rl_rowC : AllRL U dc df rowC := ⟨(rl_opCPY rl_mImm), (rl_opCMP rl_mIzx), (rl_opNOPm rl_mImm), (rl_opDCP rl_mIzx), (rl_opCPY rl_mZp), (rl_opCMP rl_mZp), (rl_opDEC rl_mZp), (rl_opDCP rl_mZp), rl_opINY, (rl_opCMP rl_mImm), rl_opDEX, rl_opJAM, (rl_opCPY rl_mAbs), (rl_opCMP rl_mAbs), (rl_opDEC rl_mAbs), (rl_opDCP rl_mAbs), trivial⟩
def rowD : List (M Unit) := [opBNE, opCMP mIzyR, opJAM, opDCP mIzy, opNOPm mZpx, opCMP mZpx, opDEC mZpx, opDCP mZpx, opCLD, opCMP mAbyR, opNOP, opDCP mAby, opNOPm mAbxR, opCMP mAbxR, opDEC mAbx, opDCP mAbx]
theorem rl_rowD : AllRL U dc df rowD := ⟨rl_opBNE, (rl_opCMP rl_mIzyR), rl_opJAM, (rl_opDCP rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opCMP rl_mZpx), (rl_opDEC rl_mZpx), (rl_opDCP rl_mZpx), rl_opCLD, (rl_opCMP rl_mAbyR), rl_opNOP, (rl_opDCP rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opCMP rl_mAbxR), (rl_opDEC rl_mAbx), (rl_opDCP rl_mAbx), trivial⟩
def rowE : List (M Unit) := [opCPX mImm, opSBC mIzx, opNOPm mImm, opISB mIzx, opCPX mZp, opSBC mZp, opINC mZp, opISB mZp, opINX, opSBC mImm, opNOP, opSBC mImm, opCPX mAbs, opSBC mAbs, opINC mAbs, opISB mAbs]
theorem rl_rowE : AllRL U dc df rowE := ⟨(rl_opCPX rl_mImm), (rl_opSBC rl_mIzx), (rl_opNOPm rl_mImm), (rl_opISB rl_mIzx), (rl_opCPX rl_mZp), (rl_opSBC rl_mZp), (rl_opINC rl_mZp), (rl_opISB rl_mZp), rl_opINX, (rl_opSBC rl_mImm), rl_opNOP, (rl_opSBC rl_mImm), (rl_opCPX rl_mAbs), (rl_opSBC rl_mAbs), (rl_opINC rl_mAbs), (rl_opISB rl_mAbs), trivial⟩
def rowF : List (M Unit) := [opBEQ, opSBC mIzyR, opJAM, opISB mIzy, opNOPm mZpx, opSBC mZpx, opINC mZpx, opISB mZpx, opSED, opSBC mAbyR, opNOP, opISB mAby, opNOPm mAbxR, opSBC mAbxR, opINC mAbx, opISB mAbx]
theorem rl_rowF : AllRL U dc df rowF := ⟨rl_opBEQ, (rl_opSBC rl_mIzyR), rl_opJAM, (rl_opISB rl_mIzy), (rl_opNOPm rl_mZpx), (rl_opSBC rl_mZpx), (rl_opINC rl_mZpx), (rl_opISB rl_mZpx), rl_opSED, (rl_opSBC rl_mAbyR), rl_opNOP, (rl_opISB rl_mAby), (rl_opNOPm rl_mAbxR), (rl_opSBC rl_mAbxR), (rl_opINC rl_mAbx), (rl_opISB rl_mAbx), trivial⟩

def allRows : List (M Unit) := row0 ++ (row1 ++ (row2 ++ (row3 ++ (row4 ++ (row5 ++ (row6 ++ (row7 ++ (row8 ++ (row9 ++ (rowA ++ (rowB ++ (rowC ++ (rowD ++ (rowE ++ (rowF)))))))))))))))

set_option maxRecDepth 1000000 in
theorem opTable_eq : opTable = allRows.toArray := rfl

theorem rl_opTable_list : AllRL U dc df allRows :=
  AllRL.append rl_row0 (AllRL.append rl_row1 (AllRL.append rl_row2 (AllRL.append rl_row3 (AllRL.append rl_row4 (AllRL.append rl_row5 (AllRL.append rl_row6 (AllRL.append rl_row7 (AllRL.append rl_row8 (AllRL.append rl_row9 (AllRL.append rl_rowA (AllRL.append rl_rowB (AllRL.append rl_rowC (AllRL.append rl_rowD (AllRL.append rl_rowE (rl_rowF)))))))))))))))

theorem rl_opTable_get (n : Nat) : RL U dc df (opTable[n]?.getD opJAM) := by
  rw [opTable_eq, List.getElem?_toArray]
  exact (rl_opTable_list (U := U) (dc := dc) (df := df)).get n opJAM rl_opJAM

theorem rl_step : RL U dc df step := by
  refine RL.get' (fun _ _ => rfl) fun m => ?_
  split
  · exact rl_nmi
  · split
    · exact RL.pure _
    · refine RL.bind rl_fetch fun op => ?_
      split
      · exact RL.bind (rl_setPC _) fun _ => RL.ofLeaf (leaf_tick _)
      · exact RL.bind (rl_opTable_get _) fun _ => RL.ofLeaf (leaf_tick _)

/-! ### Frames -/

theorem ruf_eq (t n : Nat) (m : Machine) : go (runUntilFrame t (n + 1)) m =
    if m.frame ≥ t || m.halted then ((), m) else go (runUntilFrame t n) (go step m).2 := by
  simp only [go, runUntilFrame]
  show (if (decide (m.frame ≥ t) || m.halted) = true then (Pure.pure () : M Unit)
    else (step >>= fun _ => runUntilFrame t n)) m = _
  split <;> rfl

theorem ruf_zero (t : Nat) (m : Machine) : (go (runUntilFrame t 0) m).2 = m := rfl

theorem ruf_mono : ∀ (n t : Nat) (m : Machine), Bad U m → Bad U (go (runUntilFrame t n) m).2
  | 0, _, _, hb => hb
  | n + 1, t, m, hb => by
    rw [ruf_eq]
    split
    · exact hb
    · exact ruf_mono n t _ ((rl_step (dc := 0) (df := 0)).mono m hb)

theorem ruf_rel : ∀ (n t : Nat) (m m' : Machine), Rel U dc df m m' →
    Bad U (go (runUntilFrame t n) m).2 ∨ Rel U dc df (go (runUntilFrame t n) m).2 (go (runUntilFrame (t + df) n) m').2
  | 0, _, _, _, h => Or.inr h
  | n + 1, t, m, m', h => by
    rw [ruf_eq, ruf_eq]
    obtain ⟨r, tr, tw, ti, hm⟩ := h.emb
    have hf : m'.frame = m.frame + df := by rw [hm]; rfl
    have hh : m'.halted = m.halted := by rw [hm]; rfl
    have hc : (decide (m'.frame ≥ t + df) || m'.halted) = (decide (m.frame ≥ t) || m.halted) := by
      rw [hf, hh]
      congr 1
      simp only [decide_eq_decide]
      omega
    rw [hc]
    split
    · exact Or.inr h
    · rcases (rl_step (U := U) (dc := dc) (df := df)).rel m m' h with hb | ⟨_, hr⟩
      · exact Or.inl (ruf_mono n t _ hb)
      · exact ruf_rel n t _ _ hr

/-- related whatever the buttons are: at a frame boundary `pad` does not count, a frame overwrites it -/
def RelF (U : Nat → Bool) (dc df : Nat) (m m' : Machine) : Prop :=
  ∀ b : UInt8, Rel U dc df { m with pad := b } { m' with pad := b }

theorem Rel.toF {m m' : Machine} (h : Rel U dc df m m') : RelF U dc df m m' := by
  intro b
  obtain ⟨r, tr, tw, ti, hm⟩ := h.emb
  exact ⟨⟨r, tr, tw, ti, by rw [hm]; rfl⟩, h.evc, h.evf, h.trk, h.szR, h.szW, h.szM, h.szP, h.ram⟩

theorem frame_eq (m : Machine) (i : UInt8) :
    frame m i = (go (runUntilFrame (m.frame + 1) fuelPerFrame) { m with pad := smbToPad i }).2 := by
  simp only [frame, runFrame, go]
  generalize fuelPerFrame = n
  rfl

theorem frame_mono {m : Machine} (i : UInt8) (h : Bad U m) : Bad U (frame m i) := by
  rw [frame_eq]
  exact ruf_mono _ _ _ h

theorem frame_rel {m m' : Machine} (i : UInt8) (h : RelF U dc df m m') :
    Bad U (frame m i) ∨ Rel U dc df (frame m i) (frame m' i) := by
  have h0 := h (smbToPad i)
  obtain ⟨r, tr, tw, ti, hm⟩ := h0.emb
  have hf : ({ m' with pad := smbToPad i } : Machine).frame = m.frame + df := by rw [hm]; rfl
  have hf' : m'.frame = m.frame + df := hf
  rw [frame_eq, frame_eq]
  have ht : m'.frame + 1 = m.frame + 1 + df := by omega
  rw [ht]
  exact ruf_rel _ _ _ _ h0

theorem run_mono : ∀ (w : List UInt8) (m : Machine), Bad U m → Bad U (run m w)
  | [], _, h => h
  | i :: w, m, h => run_mono w (frame m i) (frame_mono i h)

theorem run_rel : ∀ (w : List UInt8) (m m' : Machine), RelF U dc df m m' →
    Bad U (run m w) ∨ RelF U dc df (run m w) (run m' w)
  | [], _, _, h => Or.inr h
  | i :: w, m, m', h => by
    rcases frame_rel i h with hb | hr
    · exact Or.inl (run_mono w _ hb)
    · exact run_rel w _ _ hr.toF

theorem RelF.ram {m m' : Machine} (h : RelF U dc df m m') (i : Nat) (hi : i < 2048)
    (hu : U i = false ∨ m.trkWrite.get! i ≠ 0) : m.ram.get! i = m'.ram.get! i :=
  (h 0).ram i hi hu

end

/-! ## What a tracked run gives -/

/-- the tracking fields at the start of a tracked run -/
def zeroTrack : ByteArray := ByteArray.mk (Array.replicate 2048 0)

/-- `m` with tracking switched on and nothing recorded -/
def track (m : Machine) : Machine :=
  { m with trk := true, trkRead := zeroTrack, trkWrite := zeroTrack, trkIO := false }

theorem zeroTrack_size : zeroTrack.size = 2048 := by
  simp [zeroTrack, ByteArray.size]

theorem zeroTrack_get (i : Nat) : zeroTrack.get! i = 0 := by
  simp only [zeroTrack, ByteArray.get!, getElem!_def]
  by_cases h : i < 2048 <;> simp [h]
  rfl

/-- `M` is a plain machine with the registers and the PPU state of `ref`. The two counters are at an even distance, and
`M` is ahead of `ref`. `pad` does not count: a frame overwrites it. RAM is not compared. -/
structure SameCore (ref M : Machine) : Prop where
  a : M.a = ref.a
  x : M.x = ref.x
  y : M.y = ref.y
  s : M.s = ref.s
  p : M.p = ref.p
  pc : M.pc = ref.pc
  prg : M.prg = ref.prg
  prgMask : M.prgMask = ref.prgMask
  ppuCtrl : M.ppuCtrl = ref.ppuCtrl
  ppuMask : M.ppuMask = ref.ppuMask
  vblank : M.vblank = ref.vblank
  sprite0 : M.sprite0 = ref.sprite0
  nmiPending : M.nmiPending = ref.nmiPending
  fdot : M.fdot = ref.fdot
  padShift : M.padShift = ref.padShift
  padStrobe : M.padStrobe = ref.padStrobe
  halted : M.halted = ref.halted
  cycLe : ref.cyc ≤ M.cyc
  cycEven : (M.cyc - ref.cyc) % 2 = 0
  frameLe : ref.frame ≤ M.frame
  frameEven : (M.frame - ref.frame) % 2 = 0
  trk : M.trk = false
  size : M.ram.size = 2048

theorem machine_ext {a b : Machine} (h1 : a.a = b.a) (h2 : a.x = b.x) (h3 : a.y = b.y) (h4 : a.s = b.s) (h5 : a.p = b.p)
    (h6 : a.pc = b.pc) (h7 : a.cyc = b.cyc) (h8 : a.ram = b.ram) (h9 : a.prg = b.prg) (h10 : a.prgMask = b.prgMask)
    (h11 : a.ppuCtrl = b.ppuCtrl) (h12 : a.ppuMask = b.ppuMask) (h13 : a.vblank = b.vblank) (h14 : a.sprite0 = b.sprite0)
    (h15 : a.nmiPending = b.nmiPending) (h16 : a.fdot = b.fdot) (h17 : a.frame = b.frame) (h18 : a.pad = b.pad)
    (h19 : a.padShift = b.padShift) (h20 : a.padStrobe = b.padStrobe) (h21 : a.halted = b.halted) (h22 : a.trk = b.trk)
    (h23 : a.trkRead = b.trkRead) (h24 : a.trkWrite = b.trkWrite) (h25 : a.trkIO = b.trkIO) : a = b := by
  cases a
  cases b
  simp_all

/-- the bytes that may differ: all but those of `R` -/
def notIn (R : List Nat) (i : Nat) : Bool := !R.contains i

/-- the run read no byte outside `R` before writing it -/
def readsIn (R : List Nat) (m : Machine) : Bool := (flagged m.trkRead).all (fun i => R.contains i)

theorem not_bad {R : List Nat} {m : Machine} (h : readsIn R m = true) : ¬ Bad (notIn R) m := by
  rintro ⟨i, h1, h2, h3⟩
  have hm : i ∈ flagged m.trkRead := by
    simp only [flagged, List.mem_filter, List.mem_range]
    exact ⟨h1, by simpa using h3⟩
  have hc := (List.all_eq_true.1 h) i hm
  simp only [notIn, hc, Bool.not_true] at h2
  exact Bool.noConfusion h2

theorem relF_track {R : List Nat} {ref M : Machine} (hs : SameCore ref M) (hr : ref.ram.size = 2048)
    (ha : ∀ i ∈ R, i < 2048 → M.ram.get! i = ref.ram.get! i) :
    RelF (notIn R) (M.cyc - ref.cyc) (M.frame - ref.frame) (track ref) M := by
  intro b
  refine ⟨⟨M.ram, M.trkRead, M.trkWrite, M.trkIO, ?_⟩, hs.cycEven, hs.frameEven, rfl, zeroTrack_size, zeroTrack_size, hr,
    hs.size, ?_⟩
  · refine machine_ext hs.a hs.x hs.y hs.s hs.p hs.pc ?_ rfl hs.prg hs.prgMask hs.ppuCtrl hs.ppuMask hs.vblank hs.sprite0
      hs.nmiPending hs.fdot ?_ rfl hs.padShift hs.padStrobe hs.halted hs.trk rfl rfl rfl
    · show M.cyc = ref.cyc + (M.cyc - ref.cyc)
      have := hs.cycLe
      omega
    · show M.frame = ref.frame + (M.frame - ref.frame)
      have := hs.frameLe
      omega
  · intro i hi hu
    rcases hu with hu | hu
    · have hm : i ∈ R := by
        simpa [notIn] using hu
      exact (ha i hm hi).symm
    · exact absurd (zeroTrack_get i) hu

/-- along a run that reads only `R`, a machine that agrees with `ref` on `R` stays related to it -/
theorem rel_prefix {R : List Nat} {ref M : Machine} (hs : SameCore ref M) (hr : ref.ram.size = 2048)
    (ha : ∀ i ∈ R, i < 2048 → M.ram.get! i = ref.ram.get! i) {u v : List UInt8}
    (hg : readsIn R (run (track ref) (u ++ v)) = true) :
    RelF (notIn R) (M.cyc - ref.cyc) (M.frame - ref.frame) (run (track ref) u) (run M u) := by
  rcases run_rel u _ _ (relF_track hs hr ha) with hb | h
  · refine absurd ?_ (not_bad hg)
    rw [PipeTransition.run_append]
    exact run_mono v _ hb
  · exact h

/-! ## Control -/

/-- the RAM indices of the bytes `controllable` looks at -/
def ctlBytes (sy : Syms) : List Nat :=
  [sy.OperMode, sy.OperMode_Task, sy.GameEngineSubroutine].map fun a => (a &&& 0x7FF).toNat

theorem ctl_congr {sy : Syms} {R : List Nat} {dc df : Nat} {a b : Machine} (h : RelF (notIn R) dc df a b)
    (hc : (ctlBytes sy).all (fun i => R.contains i) = true) : controllable sy a = controllable sy b := by
  simp only [ctlBytes, List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have pk : ∀ x : UInt16, R.contains (x &&& 0x7FF).toNat = true → peek a x = peek b x := by
    intro x hx
    exact h.ram _ (mask_lt x) (Or.inl (by simp only [notIn, hx, Bool.not_true]))
  simp only [controllable, pk _ h1, pk _ h2, pk _ h3]

/-- with no input: control only on the last of `n` frames, and `goal` holds at the end -/
def ctlAt (sy : Syms) (goal : Machine → Bool) : Nat → Machine → Bool
  | 0, m => goal m
  | n + 1, m =>
    let m' := frame m 0
    controllable sy m' == (n == 0) && ctlAt sy goal n m'

theorem ctlAt_goal {sy : Syms} {goal : Machine → Bool} :
    ∀ (n : Nat) (m : Machine), ctlAt sy goal n m = true → goal (run m (zeros n)) = true
  | 0, _, h => h
  | n + 1, m, h => by
    simp only [ctlAt, Bool.and_eq_true] at h
    rw [PipeTransition.run_zeros_cons]
    exact ctlAt_goal n _ h.2

theorem ctlAt_spec {sy : Syms} {goal : Machine → Bool} :
    ∀ (n : Nat) (m : Machine), ctlAt sy goal n m = true → ∀ k, 1 ≤ k → k ≤ n →
      controllable sy (run m (zeros k)) = decide (k = n)
  | 0, _, _, k, h1, h2 => by omega
  | n + 1, m, h, k, h1, h2 => by
    simp only [ctlAt, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [PipeTransition.run_zeros_cons]
    cases j with
    | zero =>
      show controllable sy (frame m 0) = _
      rw [h.1]
      by_cases hn : n = 0 <;> simp [hn]
    | succ i =>
      rw [ctlAt_spec n _ h.2 (i + 1) (by omega) (by omega)]
      simp

/-- the check on a reference machine: its RAM has the right size, `R` contains the bytes of `controllable`, and the tracked run
gives control only on the last of `n` frames and reads only `R` -/
def decideCheck (sy : Syms) (R : List Nat) (n : Nat) (ref : Machine) : Bool :=
  ref.ram.size == 2048 && (ctlBytes sy).all (fun i => R.contains i) && ctlAt sy (readsIn R) n (track ref)

theorem zeros_split {k n : Nat} (h : k ≤ n) : zeros n = zeros k ++ zeros (n - k) := by
  simp only [zeros]
  rw [List.replicate_append_replicate]
  congr 1
  omega

/-- **The run is decided by `R`.** Whatever the other bytes of RAM are, `M` gets control on the same frame as `ref`. -/
theorem decided_of_check {sy : Syms} {R : List Nat} {n : Nat} {ref M : Machine} (h : decideCheck sy R n ref = true)
    (hs : SameCore ref M) (ha : ∀ i ∈ R, i < 2048 → M.ram.get! i = ref.ram.get! i) :
    ∀ k, 1 ≤ k → k ≤ n → controllable sy (run M (zeros k)) = decide (k = n) := by
  simp only [decideCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hr, hc⟩, hch⟩ := h
  intro k h1 h2
  have hg := ctlAt_goal n _ hch
  rw [zeros_split h2] at hg
  rw [← ctl_congr (rel_prefix hs hr ha hg) hc]
  exact ctlAt_spec n _ hch k h1 h2

/-- At the end of the run, `M` and the tracked `ref` are related: the same registers, and the same value in every byte of `R` and in every
byte the run wrote. -/
theorem end_of_check {sy : Syms} {R : List Nat} {n : Nat} {ref M : Machine} (h : decideCheck sy R n ref = true)
    (hs : SameCore ref M) (ha : ∀ i ∈ R, i < 2048 → M.ram.get! i = ref.ram.get! i) :
    ∀ i, i < 2048 → (i ∈ R ∨ (run (track ref) (zeros n)).trkWrite.get! i ≠ 0) →
      (run M (zeros n)).ram.get! i = (run (track ref) (zeros n)).ram.get! i := by
  simp only [decideCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hr, _⟩, hch⟩ := h
  have hg := ctlAt_goal n _ hch
  have hg' : readsIn R (run (track ref) (zeros n ++ [])) = true := by simpa using hg
  have hrel := rel_prefix hs hr ha hg'
  intro i hi hu
  refine (hrel.ram i hi ?_).symm
  rcases hu with hu | hu
  · have hc : R.contains i = true := by simpa using hu
    exact Or.inl (by simp only [notIn, hc, Bool.not_true])
  · exact Or.inr hu

/-! ## Names from the disassembly -/

/-- names of the disassembly that `Syms` does not have, with their values. The values come from the private proof. -/
abbrev Names := List (String × Nat)

/-- the names the entry states below use -/
def nameList : List String :=
  ["Enemy_Flag", "Enemy_ID", "Enemy_State", "Enemy_MovingDir", "Enemy_X_Speed", "Enemy_PageLoc", "Enemy_X_Position",
   "Enemy_Y_HighPos", "Enemy_Y_Position", "Goomba", "GreenKoopa", "HammerBro", "PowerUpObject",
   "Fireball_State", "Fireball_PageLoc", "Fireball_X_Position", "Fireball_Y_HighPos", "Fireball_Y_Position",
   "Block_State", "Misc_State", "PlayerStatus", "StarInvincibleTimer",
   "ScreenLeft_PageLoc", "ScreenLeft_X_Pos", "HorizontalScroll", "Player_Pos_ForScroll", "Player_X_Scroll", "ScrollLock",
   "TopScoreDisplay", "PlayerScoreDisplay", "GameTimerDisplay", "CoinTally", "FrameCounter", "IntervalTimerControl",
   "PseudoRandomBitReg", "AreaMusicBuffer", "EventMusicBuffer", "Square1SoundBuffer", "Square2SoundBuffer",
   "NoiseSoundBuffer", "AreaMusicQueue", "EventMusicQueue", "Square2SoundQueue", "NoiseSoundQueue", "HalfwayPage", "WarpZoneControl", "GameTimerExpiredFlag", "Mirror_PPU_CTRL_REG1"]

/-- the value of a name in `Name = $hex` lines of the disassembly -/
def asmValue (lines : List String) (n : String) : Option Nat :=
  lines.findSome? fun l =>
    match (l.splitOn "=").map (fun x => (x.splitOn ";").headD "") with
    | a :: b :: _ =>
      if a.trimAscii.toString == n then
        match b.trimAscii.toString.toList with
        | '$' :: ds => some (ds.foldl (fun v c => 16 * v + (hexDigit c).toNat) 0)
        | _ => none
      else none
    | _ => none

/-- the names above, from the text of the disassembly -/
def namesFrom (text : String) : Names :=
  let ls := text.splitOn "\n"
  nameList.filterMap fun n => (asmValue ls n).map (n, ·)

def Names.ad (nm : Names) (n : String) : UInt16 := ((nm.lookup n).getD 0).toUInt16
def Names.vl (nm : Names) (n : String) : UInt8 := ((nm.lookup n).getD 0).toUInt8

/-! ## Entry states -/

open PipeTransition (Change applyChange entry entersAt standing downIn)

/-- active enemies of the kinds `ids` near Mario, `sp` pixels apart, overwriting the slots from the first -/
def enemies (sy : Syms) (nm : Names) (e : Machine) (ids : List String) (sp : Nat) : Change :=
  let page := (peek e sy.Player_PageLoc).toNat
  let px := (peek e sy.Player_X_Position).toNat
  (List.range ids.length).flatMap fun k =>
    let ex := px + 8 + k * sp
    let at_ := fun (n : String) => nm.ad n + k.toUInt16
    [(at_ "Enemy_Flag", 1), (at_ "Enemy_ID", nm.vl (ids.getD k "")), (at_ "Enemy_State", 0), (at_ "Enemy_MovingDir", 2),
     (at_ "Enemy_X_Speed", 0xF8), (at_ "Enemy_PageLoc", (page + ex / 256).toUInt8), (at_ "Enemy_X_Position", (ex % 256).toUInt8),
     (at_ "Enemy_Y_HighPos", 1), (at_ "Enemy_Y_Position", (120 + 8 * k).toUInt8)]

/-- `n` bytes from the address of a name, all set to `v` -/
def fill (nm : Names) (name : String) (n : Nat) (v : UInt8) : Change :=
  (List.range n).map fun k => (nm.ad name + k.toUInt16, v)

/-- two fireballs near Mario -/
def fireballs (sy : Syms) (nm : Names) (e : Machine) : Change :=
  let page := peek e sy.Player_PageLoc
  let px := peek e sy.Player_X_Position
  (List.range 2).flatMap fun k =>
    let at_ := fun (n : String) => nm.ad n + k.toUInt16
    [(at_ "Fireball_State", 1), (at_ "Fireball_PageLoc", page), (at_ "Fireball_X_Position", px + (8 * k).toUInt8 + 8),
     (at_ "Fireball_Y_HighPos", 1), (at_ "Fireball_Y_Position", 100)]

/-- every digit on the status line: from the top score up to the game timer -/
def allDigits (nm : Names) (v : UInt8) : Change :=
  fill nm "TopScoreDisplay" (nm.ad "GameTimerDisplay" - nm.ad "TopScoreDisplay").toNat v ++ fill nm "GameTimerDisplay" 2 v ++
    [(nm.ad "GameTimerDisplay" + 2, if v == 0 then 1 else v)]

/-- the game timer at 1, the last value before it runs out -/
def timeOne (nm : Names) : Change := fill nm "GameTimerDisplay" 2 0 ++ [(nm.ad "GameTimerDisplay" + 2, 1)]

/-- entry states overwritten from the real one `e`: a big or fiery Mario, enemies, objects, the scroll, timers, digits, random bytes, sound -/
def scenes (sy : Syms) (nm : Names) (e : Machine) : List Change :=
  let g := "Goomba"
  let k := "GreenKoopa"
  [fill nm "Enemy_Flag" 6 0] ++
  ([2, 3, 4, 5].flatMap fun n => [0, 8, 24].map fun sp => enemies sy nm e (List.replicate n g) sp) ++
  ([0, 8, 24].map fun sp => enemies sy nm e (List.replicate 5 k) sp) ++
  [enemies sy nm e [g, k, g, k, g] 16,
   enemies sy nm e [g, g, g, g, g, "PowerUpObject"] 24] ++
  -- Mario
  [[(sy.PlayerSize, 0)],
   [(sy.PlayerSize, 0), (nm.ad "PlayerStatus", 1)],
   [(sy.PlayerSize, 0), (nm.ad "PlayerStatus", 2)],
   [(nm.ad "StarInvincibleTimer", 0xFF)]] ++
  -- objects
  [fireballs sy nm e,
   fill nm "Block_State" 2 0x11,
   fill nm "Misc_State" 5 1] ++
  -- the scroll
  ([0, 0x30, 0x50, 0x80].map fun x => [(nm.ad "ScreenLeft_X_Pos", x), (nm.ad "HorizontalScroll", x)]) ++
  [[(sy.Player_PageLoc, peek e sy.Player_PageLoc + 1)],
   [(nm.ad "Player_Pos_ForScroll", 0)],
   [(nm.ad "Player_Pos_ForScroll", 0x70)],
   [(nm.ad "Player_X_Scroll", 2)],
   [(nm.ad "ScrollLock", 1)]] ++
  -- timers and counters
  [(List.range (sy.FrameTimersLast.toNat + 1)).map (fun i => (sy.Timers + i.toUInt16, 0xFF)),
   (List.range (sy.FrameTimersLast.toNat + 1)).map (fun i => (sy.Timers + i.toUInt16, 0)),
   [(sy.TimerControl, 0xFF)],
   [(nm.ad "IntervalTimerControl", 0)],
   [(nm.ad "IntervalTimerControl", 20)],
   [(nm.ad "FrameCounter", 0)],
   [(nm.ad "FrameCounter", 0xFF)]] ++
  -- digits
  [allDigits nm 9,
   allDigits nm 0,
   fill nm "PlayerScoreDisplay" 6 9,
   fill nm "TopScoreDisplay" 6 9,
   [(nm.ad "CoinTally", 99)],
   fill nm "GameTimerDisplay" 3 9,
   timeOne nm] ++
  -- random bytes
  [fill nm "PseudoRandomBitReg" 7 0,
   fill nm "PseudoRandomBitReg" 7 0xFF] ++
  -- sound
  [[(nm.ad "AreaMusicBuffer", 0), (nm.ad "EventMusicBuffer", 0), (nm.ad "Square1SoundBuffer", 0),
    (nm.ad "Square2SoundBuffer", 0), (nm.ad "NoiseSoundBuffer", 0)]] ++
  ([1, 4, 8, 0x40].map fun v => [(nm.ad "AreaMusicQueue", v)]) ++
  ([0x40, 0x04, 0x01].map fun v => [(nm.ad "EventMusicQueue", v)]) ++
  ([0x40, 0x10, 0x02].map fun v => [(nm.ad "Square2SoundQueue", v)]) ++
  [[(nm.ad "NoiseSoundQueue", 1)]] ++
  -- several at once
  [enemies sy nm e (List.replicate 5 g) 24 ++ [(sy.PlayerSize, 0), (nm.ad "PlayerStatus", 1)] ++
    fill nm "PlayerScoreDisplay" 6 9 ++ fill nm "TopScoreDisplay" 6 9 ++ timeOne nm ++
    fill nm "PseudoRandomBitReg" 7 0xFF ++ [(nm.ad "ScreenLeft_X_Pos", 0x50), (nm.ad "HorizontalScroll", 0x50)]]

/-- the screen elsewhere: on another page or about to leave its page. The name table bit changes, unlike at any real entry at this pipe. -/
def pageScenes (nm : Names) (e : Machine) : List Change :=
  [[(nm.ad "ScreenLeft_X_Pos", 0xFF), (nm.ad "HorizontalScroll", 0xFF)],
   [(nm.ad "ScreenLeft_PageLoc", peek e (nm.ad "ScreenLeft_PageLoc") - 1)],
   [(nm.ad "ScreenLeft_PageLoc", peek e (nm.ad "ScreenLeft_PageLoc") + 1)]]

/-- real entries: standing in the pipe's window, `step · j` more frames, then Down, for `j < n` -/
def standEntries (sy : Syms) (step : Nat) : Nat → Machine → List (Machine × Machine)
  | 0, _ => []
  | n + 1, s => (s, frame s downIn) :: standEntries sy step n (run s (zeros step))

/-- the states before and after the entry frame of the real runs; `step`, `n` as above -/
def realEntries (sy : Syms) (m0 : Machine) (step n : Nat) : List (Machine × Machine) :=
  standEntries sy step n (standing m0)

/-- overwritten states that frames take longer on: six objects close together -/
def lagScenes (sy : Syms) (nm : Names) (e : Machine) : List Change :=
  ([0, 2, 4, 8].map fun sp => enemies sy nm e (List.replicate 6 "Goomba") sp) ++
  [enemies sy nm e (List.replicate 6 "GreenKoopa") 4,
   enemies sy nm e (List.replicate 6 "HammerBro") 4]

/-- overwritten states with another length: these bytes decide it -/
def deciders (nm : Names) : List Change :=
  [[(nm.ad "HalfwayPage", 1)],
   [(nm.ad "WarpZoneControl", 1)],
   [(nm.ad "GameTimerExpiredFlag", 1)]]

/-- the game timer at 0: he dies on arrival instead of getting control -/
def timeUp (nm : Names) : Change := fill nm "GameTimerDisplay" 3 0

/-! ## The state when the timer has run out, at a frame boundary -/

/-- the place in the frame: the dot and the two parities. The vblank flag and the pending NMI follow from the dot. `b` is the VRAM increment bit of the
PPU control mirror (a column of the level written last): `A` and the PPU control register at a frame boundary hold the mirror with NMI on. -/
def atPhase (T : Machine) (nm : Names) (fd c f : Nat) (b : Bool) : Machine :=
  let mv : UInt8 := (peek T (nm.ad "Mirror_PPU_CTRL_REG1") &&& 0xFB) ||| (if b then 4 else 0)
  let T' := poke T (nm.ad "Mirror_PPU_CTRL_REG1") mv
  { T' with a := mv ||| 0x80, ppuCtrl := mv ||| 0x80, fdot := fd, cyc := c, frame := f, vblank := decide (1 ≤ fd),
            nmiPending := decide (1 ≤ fd) }

/-- `T` at the place in the frame of `t` -/
def phaseOf (T : Machine) (nm : Names) (t : Machine) : Machine :=
  atPhase T nm t.fdot (t.cyc % 2) (t.frame % 2) (t.a &&& 4 != 0)

/-- `t` with the smallest counters of the same parity -/
def norm (t : Machine) : Machine := { t with cyc := t.cyc % 2, frame := t.frame % 2 }

/-- `SameCore` as a check -/
def coreOK (v t : Machine) : Bool :=
  t.a == v.a && t.x == v.x && t.y == v.y && t.s == v.s && t.p == v.p && t.pc == v.pc &&
  t.prg.data == v.prg.data && t.prgMask == v.prgMask && t.ppuCtrl == v.ppuCtrl && t.ppuMask == v.ppuMask &&
  t.vblank == v.vblank && t.sprite0 == v.sprite0 && t.nmiPending == v.nmiPending && t.fdot == v.fdot &&
  t.padShift == v.padShift && t.padStrobe == v.padStrobe && t.halted == v.halted &&
  decide (v.cyc ≤ t.cyc) && (t.cyc - v.cyc) % 2 == 0 && decide (v.frame ≤ t.frame) && (t.frame - v.frame) % 2 == 0 &&
  !t.trk && t.ram.size == 2048

theorem sameCore_of_ok {v t : Machine} (h : coreOK v t = true) : SameCore v t := by
  simp only [coreOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩,
    h19⟩, h20⟩, h21⟩, h22⟩, h23⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
  have : ∀ a b : ByteArray, a.data = b.data → a = b := by
    intro a b hab
    cases a
    cases b
    simp_all
  exact this _ _ h7

theorem sameCore_norm {t : Machine} (h1 : t.trk = false) (h2 : t.ram.size = 2048) : SameCore (norm t) t := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, h1, h2⟩
  · exact Nat.mod_le _ _
  · show (t.cyc - t.cyc % 2) % 2 = 0
    omega
  · exact Nat.mod_le _ _
  · show (t.frame - t.frame % 2) % 2 = 0
    omega

/-- no control on frames `1..n` of no input, then `k` holds -/
def noneThen (sy : Syms) (k : Machine → Bool) : Nat → Machine → Bool
  | 0, m => k m
  | n + 1, m =>
    let m' := frame m 0
    !controllable sy m' && noneThen sy k n m'

theorem noneThen_goal {sy : Syms} {k : Machine → Bool} :
    ∀ (n : Nat) (m : Machine), noneThen sy k n m = true → k (run m (zeros n)) = true
  | 0, _, h => h
  | n + 1, m, h => by
    simp only [noneThen, Bool.and_eq_true] at h
    rw [PipeTransition.run_zeros_cons]
    exact noneThen_goal n _ h.2

theorem noneThen_none {sy : Syms} {k : Machine → Bool} :
    ∀ (n : Nat) (m : Machine), noneThen sy k n m = true → ∀ j, 1 ≤ j → j ≤ n → controllable sy (run m (zeros j)) = false
  | 0, _, _, j, h1, h2 => by omega
  | n + 1, m, h, j, h1, h2 => by
    simp only [noneThen, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [PipeTransition.run_zeros_cons]
    cases i with
    | zero => exact h.1
    | succ i => exact noneThen_none n _ h.2 (i + 1) (by omega) (by omega)

/-- no control until frame `A`, control at `B` frames from there: control exactly on frame `A + B` -/
theorem pattern_join {sy : Syms} {M : Machine} {A B : Nat} (hB : 1 ≤ B)
    (h1 : ∀ j, 1 ≤ j → j ≤ A → controllable sy (run M (zeros j)) = false)
    (h2 : ∀ k, 1 ≤ k → k ≤ B → controllable sy (run (run M (zeros A)) (zeros k)) = decide (k = B)) :
    ∀ k, 1 ≤ k → k ≤ A + B → controllable sy (run M (zeros k)) = decide (k = A + B) := by
  intro k hk1 hk2
  by_cases hk : k ≤ A
  · rw [h1 k hk1 hk]
    have : k ≠ A + B := by omega
    simp [this]
  · have hsplit : zeros k = zeros A ++ zeros (k - A) := zeros_split (by omega)
    rw [hsplit, PipeTransition.run_append, h2 (k - A) (by omega) (by omega)]
    congr 1
    simp only [eq_iff_iff]
    omega

/-! ## All of it -/

/-- what the check asks of an entry: `Rfix` the bytes of `R` that must have `T`'s values -/
def cutOK (nm : Names) (Rfix : List Nat) (T t : Machine) : Bool :=
  decide (t.fdot < 10) && coreOK (phaseOf T nm t) t && Rfix.all (fun i => t.ram.get! i == (phaseOf T nm t).ram.get! i)

def entryCheck (sy : Syms) (nm : Names) (R Rfix : List Nat) (B : Nat) (T : Machine) (A : Nat) (m : Machine) : Bool :=
  noneThen sy (fun t => cutOK nm Rfix T t && decideCheck sy R B (norm t)) A m

/-- what the check gives for an entry `m` -/
structure EntryFacts (sy : Syms) (nm : Names) (R Rfix : List Nat) (T : Machine) (A B : Nat) (m : Machine) : Prop where
  /-- no control while the timer runs -/
  timer : ∀ k, 1 ≤ k → k ≤ A → controllable sy (run m (zeros k)) = false
  /-- when the timer has run out, the state is `T` at some place in the frame, as far as the registers go -/
  dot : (run m (zeros A)).fdot < 10
  core : SameCore (phaseOf T nm (run m (zeros A))) (run m (zeros A))
  /-- and the bytes `Rfix` have `T`'s values -/
  fixed : ∀ i ∈ Rfix, (run m (zeros A)).ram.get! i = (phaseOf T nm (run m (zeros A))).ram.get! i
  /-- every machine that agrees with this state on `R` gets control `B` frames later, not before -/
  decided : ∀ M, SameCore (norm (run m (zeros A))) M →
    (∀ i ∈ R, i < 2048 → M.ram.get! i = (norm (run m (zeros A))).ram.get! i) →
    ∀ k, 1 ≤ k → k ≤ B → controllable sy (run M (zeros k)) = decide (k = B)
  /-- so `m` gets control exactly on frame `A + B` -/
  exact : ∀ k, 1 ≤ k → k ≤ A + B → controllable sy (run m (zeros k)) = decide (k = A + B)

theorem entryFacts_of_check {sy : Syms} {nm : Names} {R Rfix : List Nat} {T : Machine} {A B : Nat} {m : Machine} (hB : 1 ≤ B)
    (h : entryCheck sy nm R Rfix B T A m = true) : EntryFacts sy nm R Rfix T A B m := by
  have h0 := noneThen_goal A m h
  simp only [Bool.and_eq_true, cutOK, decide_eq_true_eq] at h0
  obtain ⟨⟨⟨hd, hc⟩, hf⟩, hdc⟩ := h0
  have hN := noneThen_none A m h
  have hcore := sameCore_of_ok hc
  have hdec : ∀ M, SameCore (norm (run m (zeros A))) M →
      (∀ i ∈ R, i < 2048 → M.ram.get! i = (norm (run m (zeros A))).ram.get! i) →
      ∀ k, 1 ≤ k → k ≤ B → controllable sy (run M (zeros k)) = decide (k = B) :=
    fun M hs ha => decided_of_check hdc hs ha
  refine ⟨hN, hd, hcore, ?_, hdec, ?_⟩
  · intro i hi
    have := (List.all_eq_true.1 hf) i hi
    simpa using this
  · refine pattern_join hB hN ?_
    exact hdec _ (sameCore_norm hcore.trk hcore.size) (fun _ _ _ => rfl)

/-- the state of the real entry `E` when the timer has run out -/
def cutOf (m0 : Machine) (A : Nat) : Machine := run (entry m0) (zeros A)

/-- the bytes of `R` that are not in `Rvar` -/
def fixedOf (R Rvar : List Nat) : List Nat := R.filter fun i => !Rvar.contains i

/-- standing `realStep · j` frames more before pressing Down, for `j < realCount` -/
def realStep : Nat := 25
def realCount : Nat := 13

/-- all the entries the check runs: the real one, the overwritten ones, the other real ones -/
def entries (sy : Syms) (nm : Names) (m0 : Machine) : List Machine :=
  let e := entry m0
  e :: ((scenes sy nm e).map (applyChange e) ++ (realEntries sy m0 realStep realCount).map (·.2))

/-- how many frames the state with the game timer at 0 is followed -/
def timeUpFrames : Nat := 100

/-- the whole check. The run up to the entry is shared. -/
def allCheck (sy : Syms) (m0 : Machine) (nm : Names) (R Rvar RE : List Nat) (lagL decL : List Nat) (A B : Nat) : Bool :=
  let e := entry m0
  let T := run e (zeros A)
  let Rfix := fixedOf R Rvar
  decideCheck sy RE (A + B) (norm e) &&
  (List.range 10).all (fun fd => (List.range 2).all fun c => (List.range 2).all fun f =>
      [false, true].all fun b => decideCheck sy R B (atPhase T nm fd c f b)) &&
    (entries sy nm m0).all (entryCheck sy nm R Rfix B T A) &&
    (realEntries sy m0 realStep realCount).all (fun p => entersAt sy p.1 downIn) &&
    (pageScenes nm e).all (fun c => ctlAt sy (fun _ => true) (A + B) (applyChange e c)) &&
    (lagScenes sy nm e).length == lagL.length &&
    ((lagScenes sy nm e).zip lagL).all (fun p => decide (A + B < p.2) && ctlAt sy (fun _ => true) p.2 (applyChange e p.1)) &&
    (deciders nm).length == decL.length &&
    ((deciders nm).zip decL).all (fun p => ctlAt sy (fun _ => true) p.2 (applyChange e p.1)) &&
    noneThen sy (fun _ => true) timeUpFrames (applyChange e (timeUp nm))

/-- what the theorem says -/
structure Statement (sy : Syms) (m0 : Machine) (nm : Names) (R Rvar RE : List Nat) (lagL decL : List Nat) (A B : Nat) : Prop where
  /-- From the real entry `E`: every machine with its registers and its values on `RE` gets control on frame `A + B`, not before. -/
  atEntry : ∀ M, SameCore (norm (entry m0)) M → (∀ i ∈ RE, i < 2048 → M.ram.get! i = (norm (entry m0)).ram.get! i) →
    ∀ k, 1 ≤ k → k ≤ A + B → controllable sy (run M (zeros k)) = decide (k = A + B)
  /-- **Decided by `R`**: for each place in the frame, every machine with the registers of the state `T` when the timer has run out and the
  same values on `R` gets control `B` frames later, not before. The other bytes of RAM are arbitrary. -/
  decided : ∀ fd c f b, fd < 10 → c < 2 → f < 2 → ∀ M, SameCore (atPhase (cutOf m0 A) nm fd c f b) M →
    (∀ i ∈ R, i < 2048 → M.ram.get! i = (atPhase (cutOf m0 A) nm fd c f b).ram.get! i) →
    ∀ k, 1 ≤ k → k ≤ B → controllable sy (run M (zeros k)) = decide (k = B)
  /-- and when control comes, it has the value of the reference in every byte of `R` and in every byte the reference's run wrote -/
  ends : ∀ fd c f b, fd < 10 → c < 2 → f < 2 → ∀ M, SameCore (atPhase (cutOf m0 A) nm fd c f b) M →
    (∀ i ∈ R, i < 2048 → M.ram.get! i = (atPhase (cutOf m0 A) nm fd c f b).ram.get! i) →
    ∀ i, i < 2048 → (i ∈ R ∨ (run (track (atPhase (cutOf m0 A) nm fd c f b)) (zeros B)).trkWrite.get! i ≠ 0) →
      (run M (zeros B)).ram.get! i = (run (track (atPhase (cutOf m0 A) nm fd c f b)) (zeros B)).ram.get! i
  /-- each entry that was run: control exactly on frame `A + B`, and the state when the timer has run out is of the form that `decided` needs -/
  entryStates : ∀ m ∈ entries sy nm m0, EntryFacts sy nm R (fixedOf R Rvar) (cutOf m0 A) A B m
  /-- the other real entries are real: Down enters the pipe -/
  real : ∀ p ∈ realEntries sy m0 realStep realCount, entersAt sy p.1 downIn = true
  /-- the screen on another page, no input: the same frame -/
  otherPage : ∀ c ∈ pageScenes nm (entry m0), ∀ k, 1 ≤ k → k ≤ A + B →
    controllable sy (run (applyChange (entry m0) c) (zeros k)) = decide (k = A + B)
  /-- six objects close together: frames run over, control comes later -/
  lag : ∀ p ∈ (lagScenes sy nm (entry m0)).zip lagL, A + B < p.2 ∧
    ∀ k, 1 ≤ k → k ≤ p.2 → controllable sy (run (applyChange (entry m0) p.1) (zeros k)) = decide (k = p.2)
  /-- these bytes decide the length -/
  other : ∀ p ∈ (deciders nm).zip decL,
    ∀ k, 1 ≤ k → k ≤ p.2 → controllable sy (run (applyChange (entry m0) p.1) (zeros k)) = decide (k = p.2)
  /-- the game timer at 0: no control -/
  died : ∀ k, 1 ≤ k → k ≤ timeUpFrames → controllable sy (run (applyChange (entry m0) (timeUp nm)) (zeros k)) = false

theorem statement_of_check {sy : Syms} {m0 : Machine} {nm : Names} {R Rvar RE lagL decL : List Nat} {A B : Nat} (hB : 1 ≤ B)
    (h : allCheck sy m0 nm R Rvar RE lagL decL A B = true) : Statement sy m0 nm R Rvar RE lagL decL A B := by
  simp only [allCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h3'⟩, _⟩, h5⟩, _⟩, h7⟩, h8⟩ := h
  have hphase : ∀ fd c f b, fd < 10 → c < 2 → f < 2 → decideCheck sy R B (atPhase (cutOf m0 A) nm fd c f b) = true := by
    intro fd c f b hfd hc hf
    refine h1 fd (List.mem_range.2 hfd) c (List.mem_range.2 hc) f (List.mem_range.2 hf) b ?_
    cases b <;> simp
  refine ⟨fun M hs ha => decided_of_check h0 hs ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fd c f b hfd hc hf M hs ha
    exact decided_of_check (hphase fd c f b hfd hc hf) hs ha
  · intro fd c f b hfd hc hf M hs ha
    exact end_of_check (hphase fd c f b hfd hc hf) hs ha
  · intro m hm
    exact entryFacts_of_check hB (h2 m hm)
  · intro p hp
    exact h3 p hp
  · intro c hc
    exact ctlAt_spec _ _ (h3' c hc)
  · intro p hp
    have := h5 p hp
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1, ctlAt_spec _ _ this.2⟩
  · intro p hp
    exact ctlAt_spec _ _ (h7 p hp)
  · exact noneThen_none _ _ h8

/-! ## Every entry, under assumptions -/

/-- `M` with the bytes `Rvar` taken from `src` -/
def overlay (Rvar : List Nat) (src M : Machine) : Machine :=
  { M with ram := Rvar.foldl (fun r i => r.set! i (src.ram.get! i)) M.ram }

theorem fold_size (Rvar : List Nat) (src : Machine) : ∀ r : ByteArray,
    (Rvar.foldl (fun r i => r.set! i (src.ram.get! i)) r).size = r.size := by
  induction Rvar with
  | nil => intro r; rfl
  | cons j l ih =>
    intro r
    simp only [List.foldl_cons]
    rw [ih, ba_size_set]

theorem fold_out (Rvar : List Nat) (src : Machine) (i : Nat) (hi : i ∉ Rvar) : ∀ r : ByteArray,
    (Rvar.foldl (fun r i => r.set! i (src.ram.get! i)) r).get! i = r.get! i := by
  induction Rvar with
  | nil => intro r; rfl
  | cons j l ih =>
    intro r
    simp only [List.foldl_cons]
    have hij : j ≠ i := fun h => hi (by simp [h])
    rw [ih (fun h => hi (by simp [h])), ba_get_set_ne _ _ _ _ hij]

theorem fold_in (Rvar : List Nat) (src : Machine) (i : Nat) (hi : i ∈ Rvar) (hs : i < 2048) : ∀ r : ByteArray, r.size = 2048 →
    (Rvar.foldl (fun r i => r.set! i (src.ram.get! i)) r).get! i = src.ram.get! i := by
  induction Rvar with
  | nil => simp at hi
  | cons j l ih =>
    intro r hr
    simp only [List.foldl_cons]
    by_cases hl : i ∈ l
    · exact ih hl _ (by rw [ba_size_set]; exact hr)
    · have hij : j = i := by
        simp only [List.mem_cons] at hi
        rcases hi with h | h
        · exact h.symm
        · exact absurd h hl
      subst hij
      rw [fold_out l src j hl, ba_get_set_self _ _ _ (by rw [hr]; exact hs)]

/-- **Every entry, under assumptions.** Let `M` be any machine, `t` its state `A` frames later. If `M` has no control in those frames (`hA`), if `t`
has the registers of `T` at some place in the frame (`hd`, `hc`), if `t` has `T`'s values in the bytes `Rfix` (`hf`), and if putting `T`'s values into the bytes `Rvar` changes
nothing about control (`hv`), then `M` gets control exactly on frame `A + B`. -/
theorem every_entry {sy : Syms} {m0 : Machine} {nm : Names} {R Rvar RE lagL decL : List Nat} {A B : Nat} (hB : 1 ≤ B)
    (S : Statement sy m0 nm R Rvar RE lagL decL A B) (M : Machine)
    (hA : ∀ k, 1 ≤ k → k ≤ A → controllable sy (run M (zeros k)) = false)
    (hd : (run M (zeros A)).fdot < 10)
    (hc : SameCore (phaseOf (cutOf m0 A) nm (run M (zeros A))) (run M (zeros A)))
    (hf : ∀ i ∈ fixedOf R Rvar, (run M (zeros A)).ram.get! i = (phaseOf (cutOf m0 A) nm (run M (zeros A))).ram.get! i)
    (hv : ∀ k, 1 ≤ k → k ≤ B → controllable sy (run (run M (zeros A)) (zeros k)) =
      controllable sy (run (overlay Rvar (phaseOf (cutOf m0 A) nm (run M (zeros A))) (run M (zeros A))) (zeros k))) :
    ∀ k, 1 ≤ k → k ≤ A + B → controllable sy (run M (zeros k)) = decide (k = A + B) := by
  refine pattern_join hB hA ?_
  intro k h1 h2
  rw [hv k h1 h2]
  generalize hT : run M (zeros A) = t at hd hc hf
  have hcs : t.cyc % 2 < 2 := Nat.mod_lt _ (by decide)
  have hfs : t.frame % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsize : (overlay Rvar (phaseOf (cutOf m0 A) nm t) t).ram.size = 2048 := by
    show (Rvar.foldl _ t.ram).size = 2048
    rw [fold_size]
    exact hc.size
  refine S.decided t.fdot (t.cyc % 2) (t.frame % 2) (t.a &&& 4 != 0) hd hcs hfs _ ?_ ?_ k h1 h2
  · exact ⟨hc.a, hc.x, hc.y, hc.s, hc.p, hc.pc, hc.prg, hc.prgMask, hc.ppuCtrl, hc.ppuMask, hc.vblank, hc.sprite0,
      hc.nmiPending, hc.fdot, hc.padShift, hc.padStrobe, hc.halted, hc.cycLe, hc.cycEven, hc.frameLe, hc.frameEven, hc.trk, hsize⟩
  · intro i hi hs
    show (Rvar.foldl _ t.ram).get! i = (phaseOf (cutOf m0 A) nm t).ram.get! i
    by_cases hin : i ∈ Rvar
    · exact fold_in Rvar _ i hin hs _ hc.size
    · rw [fold_out Rvar _ i hin]
      refine hf i ?_
      simp only [fixedOf, List.mem_filter]
      refine ⟨hi, ?_⟩
      simpa using hin

/-! ## Finding the sets, for the generated proof -/

/-- the bytes a tracked run of `n` frames from `ref` reads before writing them -/
def readSet (n : Nat) (ref : Machine) : List Nat := flagged (run (track ref) (zeros n)).trkRead

/-- the sorted union of lists of RAM indices -/
def unionOf (ls : List (List Nat)) : List Nat :=
  let marks := ls.foldl (fun (acc : Array Bool) l => l.foldl (fun a i => a.set! i true) acc) (Array.replicate 2048 false)
  (List.range 2048).filter fun i => marks[i]!

/-- `R`: everything the runs read, and the bytes of `controllable` -/
def computeR (sy : Syms) (nm : Names) (m0 : Machine) (A B : Nat) : List Nat :=
  let T := cutOf m0 A
  let phases := (List.range 10).flatMap fun fd => (List.range 2).flatMap fun c => (List.range 2).flatMap fun f =>
    [false, true].map fun b => atPhase T nm fd c f b
  let cuts := (entries sy nm m0).map fun m => norm (run m (zeros A))
  unionOf (ctlBytes sy :: (phases ++ cuts).map (readSet B))

/-- `Rvar`: the bytes of `R` in which the state of some entry differs from `T` when the timer has run out -/
def computeRvar (sy : Syms) (nm : Names) (m0 : Machine) (R : List Nat) (A : Nat) : List Nat :=
  let T := cutOf m0 A
  unionOf ((entries sy nm m0).map fun m =>
    let t := run m (zeros A)
    R.filter fun i => t.ram.get! i != (phaseOf T nm t).ram.get! i)

/-- `RE`: everything the run from the real entry reads, and the bytes of `controllable` -/
def computeRE (sy : Syms) (m0 : Machine) (n : Nat) : List Nat :=
  unionOf [ctlBytes sy, readSet n (norm (entry m0))]

/-- the length of each change: frames of no input until control -/
def lengthOf (sy : Syms) (m : Machine) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k =>
    let m' := frame m 0
    if controllable sy m' then k + 1 else lengthOf sy m' n (k + 1)

end Smbrta.PipeTransitionAll
