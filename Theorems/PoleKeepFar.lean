import Theorems.PoleTileKeep
import Theorems.PositionKeep

/-!
# The pole's tiles: the two bytes of `KeepB` and the stores that cannot reach them

`PoleTileKeep.KeepB` asks of each instruction of the frames up to the touch that a store through an index or a pointer writes neither of two bytes: the block
objects' offset and the player's number (`PoleTileKeep.bI`). Many such stores cannot reach them, whatever the index:

* a store through an absolute address and an index (`X` or `Y`) from whose base no index 0 to 255 reaches either byte (`PositionKeep.absFarAt`, round 23 of part e);
* a store through the zero page and `X`: its target is in the zero page (the sum goes round in it), and neither byte is in the zero page.

`farStore` says this from the instruction's bytes in the ROM alone, without the index. `far_target` proves it. So `KeepB` needs to be asked only of the other
stores (`KeepR`, `keepB_of_R`): the stores through a pointer (`STA (zp),Y`) and the absolute stores whose base is less than 256 bytes below one of the two bytes.

No game data. Page: `1-1/f-6-17-7-PoleKeepFar.md`.
-/

namespace Smbrta.PoleKeepFar

open PipeTransitionAll (go)
open PipeWrites (wTarget opAt)

/-- the opcodes of `wTarget`'s first case: a write to the zero page plus `X` -/
def zpXOps : List UInt8 := [0x95, 0x94, 0xD6, 0xF6]

/-- **The store at `m` cannot reach a byte of `pl`, whatever its index**: the instruction is in the ROM, and it is a store through an absolute address and an index
from whose base no index reaches a byte of `pl` (`PositionKeep.absFarAt`), or a store through the zero page and `X` while no byte of `pl` is in the zero page -/
def farStore (pl : List Nat) (m : Machine) : Bool :=
  decide (0x8000 ≤ m.pc) && decide (0x8000 ≤ m.pc + 1) && decide (0x8000 ≤ m.pc + 1 + 1) &&
    (PositionKeep.absFarAt pl m.prg m.prgMask m.pc || (zpXOps.contains (opAt m) && pl.all fun i => decide (256 ≤ i)))

theorem not_zpx {op : UInt8} (h : op ∈ PositionKeep.absXOps ∨ op ∈ PositionKeep.absYOps) :
    (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = false := by
  simp only [PositionKeep.absXOps, PositionKeep.absYOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h | h | h | h | h | h) <;> subst h <;> decide

theorem not_izy {op : UInt8} (h : op ∈ PositionKeep.absXOps ∨ op ∈ PositionKeep.absYOps) : (op == 0x91) = false := by
  simp only [PositionKeep.absXOps, PositionKeep.absYOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h | h | h | h | h | h) <;> subst h <;> decide

theorem zpx_of_mem {op : UInt8} (h : zpXOps.contains op = true) : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true := by
  simp only [zpXOps, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> subst h <;> decide

/-- the target of a store through an absolute address and `X` -/
theorem abx_eq {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAbx { m with pc := m.pc + 1 }).1 = PositionKeep.operandAt m.prg m.prgMask m.pc + m.x.toUInt16 := by
  have e : go Smbrta.mAbx { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.x.toUInt16)) { m with pc := m.pc + 1 } := rfl
  have e2 : m.pc + 1 + 1 = m.pc + 2 := by rw [UInt16.add_assoc]; rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  dsimp only
  rw [e2]
  rfl

/-- the target of a store through an absolute address and `Y` -/
theorem aby_eq {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAby { m with pc := m.pc + 1 }).1 = PositionKeep.operandAt m.prg m.prgMask m.pc + m.y.toUInt16 := by
  have e : go Smbrta.mAby { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  have e2 : m.pc + 1 + 1 = m.pc + 2 := by rw [UInt16.add_assoc]; rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  dsimp only
  rw [e2]
  rfl

/-- **A store that `farStore` settles writes no byte of `pl`**, whatever its index -/
theorem far_target {pl : List Nat} {m : Machine} (h : farStore pl m = true) :
    ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ pl := by
  intro t ht hlt hP
  simp only [farStore, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hp1⟩, hp2⟩, h⟩ := h
  have hidx : (t &&& 0x7FF).toNat ∈ StepWrites.ramIdx t := by simp [StepWrites.ramIdx, hlt]
  rcases h with hf | ⟨hz, hall⟩
  · simp only [PositionKeep.absFarAt, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hf
    obtain ⟨hops, hfar⟩ := hf
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt m := rfl
    rw [hop] at hops
    unfold wTarget at ht
    dsimp only at ht
    rw [if_neg (by rw [not_zpx hops]; decide)] at ht
    split at ht
    · have e := Option.some.inj ht
      rw [abx_eq hp1 hp2] at e
      subst e
      exact PositionKeep.farB_spec hfar m.x _ hidx hP
    · split at ht
      · have e := Option.some.inj ht
        rw [aby_eq hp1 hp2] at e
        subst e
        exact PositionKeep.farB_spec hfar m.y _ hidx hP
      · rw [if_neg (by rw [not_izy hops]; decide)] at ht
        cases ht
  · unfold wTarget at ht
    dsimp only at ht
    rw [if_pos (zpx_of_mem hz)] at ht
    have e := Option.some.inj ht
    rw [PoleTileKeep.zpx_eq hp1] at e
    rw [← e, PoleTileKeep.zp_idx] at hP
    have h1 := List.all_eq_true.1 hall _ hP
    simp only [decide_eq_true_eq] at h1
    have := (RoomBlocks.operand m + m.x).toNat_lt
    omega

/-- **What stays assumed of one instruction of the frames up to the touch**: `KeepB`, but only of an instruction that `farStore` does not settle -/
def KeepR (sy : Syms) (m0 : Machine) (m : Machine) : Prop :=
  farStore (PoleTileKeep.bI sy m0) m = false → PoleTileKeep.KeepB sy m0 m

/-- **`KeepB` of every instruction from `KeepR`** -/
theorem keepB_of_R {sy : Syms} {m0 : Machine} {m : Machine} (h : KeepR sy m0 m) : PoleTileKeep.KeepB sy m0 m := by
  cases hf : farStore (PoleTileKeep.bI sy m0) m with
  | false => exact h hf
  | true => exact far_target hf

/-! ## The same test for the block buffers: `bufAll` -/

/-- the RAM indices of the two block buffers -/
def bufL (Q : PoleEntryRule.Spots) : List Nat := List.range' Q.bufLo Q.bufBytes

/-- **The store at `m` cannot reach the block buffers, whatever its index**: `farStore` of the buffers' bytes, and the buffers are past the stack -/
def farBuf (Q : PoleEntryRule.Spots) (m : Machine) : Bool := farStore (bufL Q) m && (bufL Q).all fun i => decide (512 ≤ i)

theorem wOf_zpx : ∀ op ∈ zpXOps, StepWrites.wOf op = StepWrites.wZpx := by
  intro op h
  simp only [zpXOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- **A step that `farStore` settles changes no byte of `pl`**, when `pl` is past the stack (an interrupt's entry writes only the stack) -/
theorem far_locs {pl : List Nat} {m : Machine} (h : farStore pl m = true) (hst : ∀ i ∈ pl, 512 ≤ i) : ∀ i ∈ pl, i ∉ StepWrites.stepLocs m := by
  intro i hi hloc
  simp only [farStore, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hp1⟩, hp2⟩, h⟩ := h
  have hi5 := hst i hi
  unfold StepWrites.stepLocs at hloc
  split at hloc
  · have := PositionWriters.stk_range 3 _ _ hloc
    omega
  split at hloc
  · simp at hloc
  rw [PositionWriters.fetchP hp] at hloc
  dsimp only at hloc
  have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt m := rfl
  rw [hop] at hloc
  rcases h with hf | ⟨hz, _⟩
  · simp only [PositionKeep.absFarAt, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hf
    obtain ⟨hops, hfar⟩ := hf
    rw [hop] at hops
    rcases hops with hx | hy
    · rw [PositionKeep.wOf_absX _ hx] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      rw [abx_eq hp1 hp2] at hloc
      exact PositionKeep.farB_spec hfar m.x _ hloc hi
    · rw [PositionKeep.wOf_absY _ hy] at hloc
      simp only [StepWrites.Wr.locs] at hloc
      rw [aby_eq hp1 hp2] at hloc
      exact PositionKeep.farB_spec hfar m.y _ hloc hi
  · rw [wOf_zpx _ (List.contains_iff_mem.1 hz)] at hloc
    simp only [StepWrites.Wr.locs] at hloc
    rw [PoleTileKeep.zpx_eq hp1] at hloc
    simp only [StepWrites.ramIdx] at hloc
    split at hloc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hloc
      rw [PoleTileKeep.zp_idx] at hloc
      have := (RoomBlocks.operand m + m.x).toNat_lt
      omega
    · simp at hloc

/-- **A store that `farBuf` settles writes no pole's tile into the block buffers**: it changes no byte there -/
theorem noTile_of_far {Q : PoleEntryRule.Spots} {m : Machine} (h : farBuf Q m = true) : PoleTileWalk.NoTile Q m := by
  simp only [farBuf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  intro i h1 h2 hch _
  have hm : i ∈ bufL Q := by
    simp only [bufL, List.mem_range'_1]
    exact ⟨h1, h2⟩
  exact absurd (StepWrites.step_ram m i (far_locs h.1 h.2 i hm)) hch

/-- **What stays assumed of one instruction of the frames up to the touch, for the block buffers**: `BufAt`, but only of an instruction that `farBuf` does not
settle -/
def BufR (Q : PoleEntryRule.Spots) (m : Machine) : Prop :=
  farBuf Q m = false → PoleTileWalk.BufAt Q m

/-- **`BufAt` of every instruction from `BufR`** -/
theorem bufAt_of_R {Q : PoleEntryRule.Spots} {m : Machine} (h : BufR Q m) : PoleTileWalk.BufAt Q m := by
  cases hf : farBuf Q m with
  | false => exact h hf
  | true => exact fun _ => noTile_of_far hf

/-! ## The value of a store: `bufAll` asks nothing of an `STA` that stores no pole's tile -/

/-- the stores of the accumulator through an absolute address and an index, or through a pointer -/
def staOps : List UInt8 := [0x9D, 0x99, 0x91]

theorem ba_get_set_val (a : ByteArray) (j i : Nat) (v : UInt8) (h : (a.set! j v).get! i ≠ a.get! i) : (a.set! j v).get! i = v := by
  by_cases hij : j = i
  · subst hij
    by_cases hj : j < a.size
    · exact PipeTransitionAll.ba_get_set_self a j v hj
    · exfalso
      apply h
      cases a with
      | mk d =>
        simp only [ByteArray.size] at hj
        simp [ByteArray.set!, ByteArray.get!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, hj]
  · exact absurd (PipeTransitionAll.ba_get_set_ne a j i v hij) h

/-- a write changes a byte of the RAM only to the value written -/
theorem wr_val (addr : UInt16) (v : UInt8) (x : Machine) (i : Nat) (h : (go (wr addr v) x).2.ram.get! i ≠ x.ram.get! i) :
    (go (wr addr v) x).2.ram.get! i = v := by
  by_cases h1 : addr < 0x2000
  · have e : go (wr addr v) x = ((), PipeTransitionAll.wrRamF (addr &&& 0x7FF).toNat v x) := by
      unfold wr go
      rw [if_pos h1]
      cases x with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases trk <;> rfl
    rw [e] at h ⊢
    unfold PipeTransitionAll.wrRamF at h ⊢
    split
    · rename_i ht
      rw [if_pos ht] at h
      exact ba_get_set_val _ _ _ _ h
    · rename_i ht
      rw [if_neg ht] at h
      exact ba_get_set_val _ _ _ _ h
  · exact absurd (by rw [StepWrites.nw_wr_io v h1 x]) h

/-- an `STA` with a mode that keeps the RAM and A changes a byte of the RAM only to A -/
theorem sta_val {md : Mode} {c : Nat} {m1 : Machine} (hr : (go md m1).2.ram = m1.ram) (ha : (go md m1).2.a = m1.a) (i : Nat)
    (h : (go (opSTA md >>= fun _ => tick c) m1).2.ram.get! i ≠ m1.ram.get! i) : (go (opSTA md >>= fun _ => tick c) m1).2.ram.get! i = m1.a := by
  have e1 : (go (opSTA md >>= fun _ => tick c) m1).2.ram = (go (opSTA md) m1).2.ram := by
    rw [PipeTransitionAll.go_bind, (PipeTransitionAll.leaf_tick c).ram]
  have e2 : go (opSTA md) m1 = go (wr (go md m1).1 (go md m1).2.a) (go md m1).2 := by
    unfold opSTA
    rw [PipeTransitionAll.go_bind]
    rfl
  rw [e1, e2] at h ⊢
  rw [← hr] at h
  rw [← ha]
  exact wr_val _ _ _ i h

theorem abx_state {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAbx { m with pc := m.pc + 1 }).2.ram = m.ram ∧ (go Smbrta.mAbx { m with pc := m.pc + 1 }).2.a = m.a := by
  have e : go Smbrta.mAbx { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.x.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  exact ⟨rfl, rfl⟩

theorem aby_state {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAby { m with pc := m.pc + 1 }).2.ram = m.ram ∧ (go Smbrta.mAby { m with pc := m.pc + 1 }).2.a = m.a := by
  have e : go Smbrta.mAby { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  exact ⟨rfl, rfl⟩

/-- a read of the RAM keeps A -/
theorem rd_ram_a {addr : UInt16} (h : addr < 0x2000) (x : Machine) : (go (rd addr) x).2.a = x.a := by
  have e : go (rd addr) x = PipeTransitionAll.rdRamF (addr &&& 0x7FF).toNat x := by
    unfold rd go
    rw [if_pos h]
    cases x with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  rw [e]
  unfold PipeTransitionAll.rdRamF PipeTransitionAll.trF
  split
  · split <;> rfl
  · rfl

theorem izy_state {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) :
    (go Smbrta.mIzy { m with pc := m.pc + 1 }).2.ram = m.ram ∧ (go Smbrta.mIzy { m with pc := m.pc + 1 }).2.a = m.a := by
  refine ⟨StepWrites.nw_mIzy _, ?_⟩
  have e : go Smbrta.mIzy { m with pc := m.pc + 1 } = go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s =>
      pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind]
  have e2 : ∀ (z : UInt8) (x : Machine), (go (rd16zp z) x).2 = (go (rd (z + 1).toUInt16) (go (rd z.toUInt16) x).2).2 := fun _ _ => rfl
  show (go (rd16zp _) _).2.a = m.a
  rw [e2, rd_ram_a (RoomBlocks.zp_lt _), rd_ram_a (RoomBlocks.zp_lt _)]

/-- **An `STA abs,X`, `STA abs,Y` or `STA (zp),Y` from the ROM with no NMI pending changes a byte of the RAM only to A** -/
theorem sta_step {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : 0x8000 ≤ m.pc) (hp1 : 0x8000 ≤ m.pc + 1)
    (hp2 : 0x8000 ≤ m.pc + 1 + 1) (hop : staOps.contains (opAt m) = true) (i : Nat) (h : (go step m).2.ram.get! i ≠ m.ram.get! i) :
    (go step m).2.ram.get! i = m.a := by
  have hop' : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt m := rfl
  simp only [staOps, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with e | e | e
  · rw [ScreenPage.step_at hn hh hp (hop'.trans e) (by decide), PipeWrites.op_9D] at h ⊢
    obtain ⟨r1, r2⟩ := abx_state hp1 hp2
    exact sta_val r1 r2 i h
  · rw [ScreenPage.step_at hn hh hp (hop'.trans e) (by decide), PipeWrites.op_99] at h ⊢
    obtain ⟨r1, r2⟩ := aby_state hp1 hp2
    exact sta_val r1 r2 i h
  · rw [ScreenPage.step_at hn hh hp (hop'.trans e) (by decide), PipeWrites.op_91] at h ⊢
    obtain ⟨r1, r2⟩ := izy_state hp1
    exact sta_val r1 r2 i h

/-- **What stays assumed of one instruction of the frames up to the touch, for the block buffers** (round 26): `BufAt`, but only of an instruction that `farBuf`
does not settle; and of a store of A through an absolute address and an index or through a pointer (`staOps`), run from the ROM with no NMI pending, only when A
holds one of the pole's two tiles -/
def BufV (Q : PoleEntryRule.Spots) (m : Machine) : Prop :=
  farBuf Q m = false → (m.nmiPending = false → m.halted = false → 0x8000 ≤ m.pc → 0x8000 ≤ m.pc + 1 → 0x8000 ≤ m.pc + 1 + 1 →
    staOps.contains (opAt m) = true → PoleTiles.Tile Q m.a) → PoleTileWalk.BufAt Q m

/-- **`BufAt` of every instruction from `BufV`**: a store that `farBuf` settles writes no byte of the block buffers (`noTile_of_far`); an `STA` of a byte that is
not one of the pole's tiles writes no pole's tile (`sta_step`) -/
theorem bufAt_of_V {Q : PoleEntryRule.Spots} {m : Machine} (h : BufV Q m) : PoleTileWalk.BufAt Q m := by
  cases hf : farBuf Q m with
  | true => exact fun _ => noTile_of_far hf
  | false =>
    by_cases hc : m.nmiPending = false ∧ m.halted = false ∧ 0x8000 ≤ m.pc ∧ 0x8000 ≤ m.pc + 1 ∧ 0x8000 ≤ m.pc + 1 + 1 ∧
        staOps.contains (opAt m) = true ∧ ¬ PoleTiles.Tile Q m.a
    · obtain ⟨hn, hh, hp, hp1, hp2, hop, ht⟩ := hc
      intro _ i _ _ hch htile
      rw [sta_step hn hh hp hp1 hp2 hop i hch] at htile
      exact absurd htile ht
    · apply h hf
      intro hn hh hp hp1 hp2 hop
      by_cases ht : PoleTiles.Tile Q m.a
      · exact ht
      · exact absurd ⟨hn, hh, hp, hp1, hp2, hop, ht⟩ hc

end Smbrta.PoleKeepFar
