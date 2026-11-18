import Theorems.RoomFall
import Theorems.RoomPair

/-!
# The blocks of the room's map stay

`RoomMap` proves that every bit that is 0 in the map is 0 in the two block buffers on every frame of the room. Here: every byte of the block buffers that is not a coin
in the map keeps its value (a brick stays a brick, the floor stays the floor).

The only step of a frame of the room that may write a byte of the block buffers is the erase of a coin (the walk checks `RoomFall.mayWrite` at every other state). The
erase writes through a pointer that the abstract machine does not know. What is proved here is that the byte it writes holds a coin: the block buffer routine reads a tile
through the same pointer with the same offset and stores it in a byte of the zero page; from there to the erase no step writes that byte, the offset, the pointer or the
block buffers, and the tile was a coin. The three places of the zero page (the pointer, the offset's byte, the tile's byte) are read from the code (`ptrOf`, `offOf`,
`tileOf`). This is a fact about the machine that the abstract states do not hold; the walk carries it with marks, as `RoomFall` does
(`RoomVert.frame_of_walkV`).

There is no game data in this file. Page: `1-1/c-7-12-1-RoomBlocks.md`.
-/

namespace Smbrta.RoomBlocks

open PipeTransition (frame)
open PipeTransitionAll (Names go go_bind trF_ram rdRamF)
open TaintRun
open PipeEntryRule (trace)
open ScreenPage (Places SiteOK PlacesOK CfgS RoomCond readAddr readVal writeAddr)

/-! ## One instruction on the machine -/

theorem zp_lt (z : UInt8) : z.toUInt16 < 0x2000 := by
  apply UInt16.lt_iff_toNat_lt.2
  have h := z.toNat_lt
  simp
  omega

/-- a read of RAM: the byte read, and the machine keeps the RAM and Y -/
theorem rd_ram {addr : UInt16} (h : addr < 0x2000) (m : Machine) :
    (go (rd addr) m).1 = m.ram.get! (addr &&& 0x7FF).toNat ∧ (go (rd addr) m).2.ram = m.ram ∧ (go (rd addr) m).2.y = m.y := by
  have e : go (rd addr) m = rdRamF (addr &&& 0x7FF).toNat m := by
    unfold rd go
    rw [if_pos h]
    cases m with
    | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
      cases trk <;> rfl
  rw [e]
  unfold rdRamF
  split
  · refine ⟨by rw [trF_ram], trF_ram _ _, ?_⟩
    unfold PipeTransitionAll.trF
    split <;> rfl
  · exact ⟨rfl, rfl, rfl⟩

/-- the pointer in the zero page at the byte `z`, as an address -/
def ptrZ (m : Machine) (z : UInt8) : UInt16 :=
  (m.ram.get! (z.toUInt16 &&& 0x7FF).toNat).toUInt16 ||| ((m.ram.get! ((z + 1).toUInt16 &&& 0x7FF).toNat).toUInt16 <<< 8)

theorem rd16zp_eq (z : UInt8) (m : Machine) :
    (go (rd16zp z) m).1 = ptrZ m z ∧ (go (rd16zp z) m).2.ram = m.ram ∧ (go (rd16zp z) m).2.y = m.y := by
  have e : go (rd16zp z) m = go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m := rfl
  rw [e, go_bind, go_bind]
  obtain ⟨a1, a2, a3⟩ := rd_ram (zp_lt z) m
  obtain ⟨b1, b2, b3⟩ := rd_ram (zp_lt (z + 1)) (go (rd z.toUInt16) m).2
  refine ⟨?_, ?_, ?_⟩
  · show (go (rd z.toUInt16) m).1.toUInt16 ||| ((go (rd (z + 1).toUInt16) (go (rd z.toUInt16) m).2).1.toUInt16 <<< 8) = _
    rw [a1, b1, a2]
    rfl
  · show (go (rd (z + 1).toUInt16) (go (rd z.toUInt16) m).2).2.ram = m.ram
    rw [b2, a2]
  · show (go (rd (z + 1).toUInt16) (go (rd z.toUInt16) m).2).2.y = m.y
    rw [b3, a3]

/-- the operand of the instruction at `m.pc`: the byte after the opcode -/
def operand (m : Machine) : UInt8 := m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat

/-- **The address of an `STA (zp),Y`**: the pointer plus Y -/
theorem writeAddr_eq {m : Machine} (hp : m.pc + 1 ≥ 0x8000) : writeAddr m = ptrZ m (operand m) + m.y.toUInt16 := by
  unfold writeAddr
  have e : go mIzy { m with pc := m.pc + 1 } =
      go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s => pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp, go_bind]
  obtain ⟨a1, _, a3⟩ := rd16zp_eq (operand m) { m with pc := m.pc + 1 + 1 }
  show (go (rd16zp (operand m)) { m with pc := m.pc + 1 + 1 }).1 + (go (rd16zp (operand m)) { m with pc := m.pc + 1 + 1 }).2.y.toUInt16 = _
  rw [a1, a3]
  rfl

/-- **The address of an `LDA (zp),Y`**: the pointer plus Y -/
theorem readAddr_eq {m : Machine} (hp : m.pc + 1 ≥ 0x8000) : readAddr m = ptrZ m (operand m) + m.y.toUInt16 := by
  unfold readAddr
  have e : go mIzyR { m with pc := m.pc + 1 } =
      go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s => pagePenalty b (b + s.y.toUInt16) >>= fun _ => pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp, go_bind]
  obtain ⟨a1, _, a3⟩ := rd16zp_eq (operand m) { m with pc := m.pc + 1 + 1 }
  show (go (rd16zp (operand m)) { m with pc := m.pc + 1 + 1 }).1 + (go (rd16zp (operand m)) { m with pc := m.pc + 1 + 1 }).2.y.toUInt16 = _
  rw [a1, a3]
  rfl

/-- **The byte that an `LDA (zp),Y` reads from RAM** -/
theorem readVal_eq {m : Machine} (h : readAddr m < 0x2000) : readVal m = m.ram.get! (readAddr m &&& 0x7FF).toNat := by
  unfold readVal
  show (go (rd (readAddr m)) (go mIzyR { m with pc := m.pc + 1 }).2).1 = _
  rw [(rd_ram h _).1, StepWrites.nw_mIzyR]

theorem tick_a (c : Nat) (x : Machine) : (go (tick c) x).2.a = x.a := by
  rw [PipeTransitionAll.tick_eq]
  simp only [PipeTransitionAll.tick4, PipeTransitionAll.tick3, PipeTransitionAll.tick2, PipeTransitionAll.tick1]
  repeat' split
  all_goals rfl

/-- **An `LDA (zp),Y` puts the byte read in A and keeps the RAM** -/
theorem step_lda_izy {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1) : (go step m).2.a = readVal m ∧ (go step m).2.ram = m.ram := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), ScreenPage.op_B1, ScreenPage.cyc_B1]
  have e : go ((opLDA mIzyR) >>= fun _ => tick 5) { m with pc := m.pc + 1 } =
      go (tick 5) (go (setA (readVal m)) (go (rd (readAddr m)) (go mIzyR { m with pc := m.pc + 1 }).2).2).2 := by
    rw [go_bind]
    have e2 : go (opLDA mIzyR) { m with pc := m.pc + 1 } = go (mIzyR >>= fun ad => rd ad >>= fun v => setA v) { m with pc := m.pc + 1 } := rfl
    rw [e2, go_bind, go_bind]
    rfl
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [tick_a]
    rfl
  · rw [(PipeTransitionAll.leaf_tick 5).ram, StepWrites.nw_setA, StepWrites.nw_rd, StepWrites.nw_mIzyR]

set_option maxRecDepth 100000 in
theorem op_85 : opTable[(0x85 : UInt8).toNat]?.getD opJAM = opSTA mZp := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- a write to RAM -/
theorem wr_ram {addr : UInt16} (h : addr < 0x2000) (v : UInt8) (x : Machine) : (go (wr addr v) x).2.ram = x.ram.set! (addr &&& 0x7FF).toNat v := by
  unfold wr go
  rw [if_pos h]
  cases x with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases trk <;> rfl

/-- **An `STA zp` writes A into the byte that its operand names** -/
theorem step_sta_zp {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x85) (hsz : m.ram.size = 2048) :
    (go step m).2.ram.get! ((operand m).toUInt16 &&& 0x7FF).toNat = m.a := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_85]
  have e : go ((opSTA mZp) >>= fun _ => tick (cycTable.get! (0x85 : UInt8).toNat).toNat) { m with pc := m.pc + 1 } =
      go (tick (cycTable.get! (0x85 : UInt8).toNat).toNat) (go (wr (operand m).toUInt16 m.a) { m with pc := m.pc + 1 + 1 }).2 := by
    rw [go_bind]
    have e2 : go (opSTA mZp) { m with pc := m.pc + 1 } = go (fetch >>= fun b => get >>= fun x => wr b.toUInt16 x.a) { m with pc := m.pc + 1 } := rfl
    rw [e2, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp1]
    rfl
  rw [e, (PipeTransitionAll.leaf_tick _).ram, wr_ram (zp_lt _)]
  exact PipeTransitionAll.ba_get_set_self _ _ _ (by rw [hsz]; exact PipeTransitionAll.mask_lt _)

theorem tick_y (c : Nat) (x : Machine) : (go (tick c) x).2.y = x.y := by
  rw [PipeTransitionAll.tick_eq]
  simp only [PipeTransitionAll.tick4, PipeTransitionAll.tick3, PipeTransitionAll.tick2, PipeTransitionAll.tick1]
  repeat' split
  all_goals rfl

theorem wr_a {addr : UInt16} (h : addr < 0x2000) (v : UInt8) (x : Machine) : (go (wr addr v) x).2.a = x.a := by
  unfold wr go
  rw [if_pos h]
  cases x with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases trk <;> rfl

/-- **An `STA zp` keeps A** -/
theorem step_sta_zp_a {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x85) : (go step m).2.a = m.a := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_85]
  have e : go ((opSTA mZp) >>= fun _ => tick (cycTable.get! (0x85 : UInt8).toNat).toNat) { m with pc := m.pc + 1 } =
      go (tick (cycTable.get! (0x85 : UInt8).toNat).toNat) (go (wr (operand m).toUInt16 m.a) { m with pc := m.pc + 1 + 1 }).2 := by
    rw [go_bind]
    have e2 : go (opSTA mZp) { m with pc := m.pc + 1 } = go (fetch >>= fun b => get >>= fun x => wr b.toUInt16 x.a) { m with pc := m.pc + 1 } := rfl
    rw [e2, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp1]
    rfl
  rw [e, tick_a, wr_a (zp_lt _)]

set_option maxRecDepth 100000 in
theorem op_A8 : opTable[(0xA8 : UInt8).toNat]?.getD opJAM = opTAY := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- **`TAY` puts A in Y and keeps the RAM** -/
theorem step_tay {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xA8) : (go step m).2.y = m.a ∧ (go step m).2.ram = m.ram := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_A8]
  have e2 : go opTAY { m with pc := m.pc + 1 } = go (setY m.a) { m with pc := m.pc + 1 } := rfl
  rw [go_bind, e2]
  refine ⟨?_, ?_⟩
  · rw [tick_y]
    rfl
  · rw [(PipeTransitionAll.leaf_tick _).ram, StepWrites.nw_setY]

set_option maxRecDepth 100000 in
theorem op_A4 : opTable[(0xA4 : UInt8).toNat]?.getD opJAM = opLDY mZp := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- **An `LDY zp` puts the byte that its operand names in Y and keeps the RAM** -/
theorem step_ldy_zp {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xA4) :
    (go step m).2.y = m.ram.get! ((operand m).toUInt16 &&& 0x7FF).toNat ∧ (go step m).2.ram = m.ram := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_A4]
  have e : go ((opLDY mZp) >>= fun _ => tick (cycTable.get! (0xA4 : UInt8).toNat).toNat) { m with pc := m.pc + 1 } =
      go (tick (cycTable.get! (0xA4 : UInt8).toNat).toNat)
        (go (setY (go (rd (operand m).toUInt16) { m with pc := m.pc + 1 + 1 }).1) (go (rd (operand m).toUInt16) { m with pc := m.pc + 1 + 1 }).2).2 := by
    rw [go_bind]
    have e2 : go (opLDY mZp) { m with pc := m.pc + 1 } = go (fetch >>= fun b => rd b.toUInt16 >>= fun v => setY v) { m with pc := m.pc + 1 } := rfl
    rw [e2, go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp1, go_bind]
    rfl
  rw [e]
  obtain ⟨a1, a2, _⟩ := rd_ram (zp_lt (operand m)) { m with pc := m.pc + 1 + 1 }
  refine ⟨?_, ?_⟩
  · rw [tick_y]
    show (go (rd (operand m).toUInt16) { m with pc := m.pc + 1 + 1 }).1 = _
    rw [a1]
  · rw [(PipeTransitionAll.leaf_tick _).ram, StepWrites.nw_setY, a2]

set_option maxRecDepth 100000 in
theorem op_A9 : opTable[(0xA9 : UInt8).toNat]?.getD opJAM = opLDA mImm := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- **An `LDA #` keeps Y and the RAM** -/
theorem step_lda_imm {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xA9) : (go step m).2.y = m.y ∧ (go step m).2.ram = m.ram := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_A9]
  have h1 : ¬ m.pc + 1 < 0x2000 := by
    intro h
    have a1 := UInt16.lt_iff_toNat_lt.1 h
    have a2 := UInt16.le_iff_toNat_le.1 hp1
    revert a1 a2
    simp
    omega
  have e : go ((opLDA mImm) >>= fun _ => tick (cycTable.get! (0xA9 : UInt8).toNat).toNat) { m with pc := m.pc + 1 } =
      go (tick (cycTable.get! (0xA9 : UInt8).toNat).toNat)
        (go (setA (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat)) { m with pc := m.pc + 1 + 1 }).2 := by
    rw [go_bind]
    have e2 : go (opLDA mImm) { m with pc := m.pc + 1 } = go (rd (m.pc + 1) >>= fun v => setA v) { m with pc := m.pc + 1 + 1 } := rfl
    rw [e2, go_bind, TaintRun.rd_rom _ h1 hp1]
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [tick_y]
    rfl
  · rw [(PipeTransitionAll.leaf_tick _).ram, StepWrites.nw_setA]

section
variable {E : Env} {F : Nat × UInt8}

/-- **The erase of a coin writes only the byte of its address** -/
theorem erase_other {P : Places} {A : AS} {m : Machine} (hO : PlacesOK E P) (hs : Sim E F A m) (hn : A.nmi = false)
    (hpc : A.pc = P.erase) (hh : SiteOK P m) {x : Nat} (hx : x ≠ (writeAddr m &&& 0x7FF).toNat) : (go step m).2.ram.get! x = m.ram.get! x := by
  apply StepWrites.step_ram
  intro hi
  unfold StepWrites.stepLocs at hi
  have hn' : m.nmiPending = false := by rw [hs.nmi]; exact hn
  rw [if_neg (by simp [hn']), if_neg (by simp [hs.halted])] at hi
  have hmp : m.pc = P.erase := by rw [hs.pc]; exact hpc
  have hpm : m.pc ≥ 0x8000 := by rw [hmp]; exact hO.erase.1
  rw [TaintRun.fetch_rom hpm] at hi
  have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hmp]; exact hO.erase.2
  rw [hop] at hi
  have hw : StepWrites.wOf 0x91 = StepWrites.wIzy := rfl
  rw [hw] at hi
  obtain ⟨g1, _, _⟩ := hh.erase hmp
  have e : (StepWrites.wIzy).locs { m with pc := m.pc + 1 } = StepWrites.ramIdx (ScreenPage.writeAddr m) := rfl
  rw [e] at hi
  unfold StepWrites.ramIdx at hi
  rw [if_pos g1] at hi
  simp only [List.mem_singleton] at hi
  exact hx hi

end

/-! ## The blocks, and the walk -/

open RoomVert (Ph canBe knIs OKV)
open RoomFall (mayWrite)

/-- the RAM indices of the two block buffers -/
def bufL (P : Places) : List Nat := (List.range P.bufN).map (P.bufLo + ·)

/-- **The blocks stay**: every byte of the block buffers that is not a tile of `cs` (the coins) in the map `M` has the map's value -/
def Solid (P : Places) (cs : List UInt8) (M m : Machine) : Prop :=
  ∀ d, P.bufLo ≤ d → d < P.bufLo + P.bufN → M.ram.get! d ∉ cs → m.ram.get! d = M.ram.get! d

/-- the RAM index of a byte of the zero page -/
def zI (b : UInt8) : Nat := (b.toUInt16 &&& 0x7FF).toNat

/-- the address that the block buffer routine reads and that the erase writes: the pointer at the byte `z` of the zero page, plus the byte `o` (the routine's offset) -/
def adr (m : Machine) (z : UInt8) (o : Nat) : UInt16 := ptrZ m z + (m.ram.get! o).toUInt16

/-- its RAM index -/
def idx (m : Machine) (z : UInt8) (o : Nat) : Nat := (adr m z o &&& 0x7FF).toNat

/-- the address is a byte of the block buffers -/
def InB (P : Places) (m : Machine) (z : UInt8) (o : Nat) : Prop := adr m z o < 0x2000 ∧ P.bufLo ≤ idx m z o ∧ idx m z o < P.bufLo + P.bufN

/-- the two RAM indices of the pointer -/
def ptrI (z : UInt8) : List Nat := [(z.toUInt16 &&& 0x7FF).toNat, ((z + 1).toUInt16 &&& 0x7FF).toNat]

/-- the bytes that the address is made of (the offset's byte `o`, the pointer), and the byte `t` that keeps the tile read -/
def adrL (z : UInt8) (o t : Nat) : List Nat := [o, t] ++ ptrI z

/-- a mark that holds for one step only -/
def oneStep (l : List Nat) : Bool :=
  l.head? == some 3 || l.head? == some 6 || l.head? == some 4 || l.head? == some 5 || l.head? == some 7 || l.head? == some 10 || l == [8]

/-- the pieces of a state: one piece, with its mark. The marks follow the block buffer routine and the erase: `[3]` the store of the offset (the byte `o`) runs now, three
bytes before the read; `[6]` the copy of the offset to Y runs now; `[4]` the read runs now; `[5]` the store of the tile read (the byte `t`) runs now; `[9]` the tile read is a
coin, and no step since has written the offset's byte, the tile's byte, the pointer or the block buffers; `[7]` the load of the offset into Y runs now, four bytes before the erase; `[10]`
the load of the empty tile runs now; `[8]` the erase runs now. A mark for one step that comes to another place is dropped. -/
def zoneK (E : Env) (P : Places) (cs : List UInt8) (z : UInt8) (o t : Nat) (A : AS) : List AS :=
  if A.pc == P.read - 3 && !A.nmi then [{ A with log := [3] }]
  else if A.pc == P.read - 1 && !A.nmi && A.log.head? == some 3 then [{ A with log := [6] }]
  else if A.pc == P.read && !A.nmi && A.log.head? == some 6 then [{ A with log := [4] }]
  else if A.pc == P.read + 2 && !A.nmi && A.log.head? == some 4 then [{ A with log := [5] }]
  else if A.pc == P.read + 4 && !A.nmi && A.log.head? == some 5 then [{ A with log := if cs.any (knIs (A.getK t)) then [9] else [] }]
  else if A.pc == P.erase - 4 && !A.nmi && A.log.head? == some 9 then [{ A with log := [7] }]
  else if A.pc == P.erase - 2 && !A.nmi && A.log.head? == some 7 then [{ A with log := [10] }]
  else if A.pc == P.erase && !A.nmi && A.log.head? == some 10 then [{ A with log := [8] }]
  else if oneStep A.log then [{ A with log := [] }]
  else if A.log.head? == some 9 && mayWrite E P (adrL z o t) A then [{ A with log := [] }]
  else [A]

/-- what the walk asks of each piece: its step does not write the block buffers, or it is the erase; the store of the tile (`[5]`) writes only the tile's byte; a piece
marked `[9]` does not write the offset's byte, the tile's byte or the pointer; and the erase is marked `[8]` -/
def okK (E : Env) (P : Places) (z : UInt8) (o t : Nat) (A : AS) : Bool :=
  !mayWrite E P (bufL P) A &&
  (A.log.head? != some 5 || StepWrites.keepOK E (fun i => i != t) A) &&
  (A.log.head? != some 9 || !mayWrite E P (adrL z o t) A) &&
  (A.nmi || A.pc != P.erase || A.log == [8])

/-- the walk of one frame of the room that follows the tile read up to the erase -/
def phK (E : Env) (P : Places) (cs : List UInt8) (z : UInt8) (o t : Nat) : Ph where
  zone := zoneK E P cs z o t
  pre := fun _ => true
  ok := okK E P z o t

/-- **The code around the read and the erase**: three bytes before the read, the store of A in the byte `o`, then the copy of A to Y; the read and the erase use the
pointer at the byte `z` of the zero page; after the read, the store of A in the byte `t`; four bytes before the erase, the load of the byte `o` into Y, then a load of A
with a constant. The bytes of the address and the byte `t` are below the block buffers, and are apart -/
def codeOK (E : Env) (P : Places) (z : UInt8) (o t : Nat) : Bool :=
  E.prg.get! ((P.read - 3) &&& E.mask).toNat == 0x85 && zI (E.prg.get! ((P.read - 3 + 1) &&& E.mask).toNat) == o &&
  E.prg.get! ((P.read - 1) &&& E.mask).toNat == 0xA8 &&
  E.prg.get! ((P.read + 1) &&& E.mask).toNat == z && E.prg.get! ((P.erase + 1) &&& E.mask).toNat == z &&
  E.prg.get! ((P.read + 2) &&& E.mask).toNat == 0x85 && zI (E.prg.get! ((P.read + 2 + 1) &&& E.mask).toNat) == t &&
  E.prg.get! ((P.erase - 4) &&& E.mask).toNat == 0xA4 && zI (E.prg.get! ((P.erase - 4 + 1) &&& E.mask).toNat) == o &&
  E.prg.get! ((P.erase - 2) &&& E.mask).toNat == 0xA9 &&
  decide (P.read - 3 ≥ 0x8000) && decide (P.read - 3 + 1 ≥ 0x8000) && decide (P.read - 1 ≥ 0x8000) &&
  decide (P.read + 1 ≥ 0x8000) && decide (P.read + 2 ≥ 0x8000) && decide (P.read + 2 + 1 ≥ 0x8000) &&
  decide (P.erase - 4 ≥ 0x8000) && decide (P.erase - 4 + 1 ≥ 0x8000) && decide (P.erase - 2 ≥ 0x8000) && decide (P.erase - 2 + 1 ≥ 0x8000) &&
  decide (P.erase + 1 ≥ 0x8000) &&
  decide (t < P.bufLo) && (ptrI z).all (fun i => i != o && i != t && decide (i < P.bufLo)) && o != t && decide (o < P.bufLo) &&
  decide (P.bufLo + P.bufN ≤ 2048)

/-! ## One frame of the room -/

section
variable {E : Env} {F : Nat × UInt8}
open RoomVert (knIs_spec sim_bits)

/-- what the mark `[9]` says of the machine: the tile's byte `t` holds a coin, and if the address is a byte of the block buffers, that byte is the tile's -/
def Coin (P : Places) (cs : List UInt8) (z : UInt8) (o t : Nat) (x : Machine) : Prop :=
  x.ram.get! t ∈ cs ∧ (InB P x z o → x.ram.get! (idx x z o) = x.ram.get! t)

theorem mem_bufL {P : Places} {d : Nat} (h1 : P.bufLo ≤ d) (h2 : d < P.bufLo + P.bufN) : d ∈ bufL P :=
  List.mem_map.2 ⟨d - P.bufLo, List.mem_range.2 (by omega), by omega⟩

/-- the address depends on the offset's byte and the pointer only -/
theorem adr_congr {x x' : Machine} {z : UInt8} {o : Nat} (h2 : x'.ram.get! o = x.ram.get! o) (hp : ∀ i ∈ ptrI z, x'.ram.get! i = x.ram.get! i) :
    adr x' z o = adr x z o := by
  unfold adr ptrZ
  rw [h2, hp _ (by simp [ptrI]), hp _ (by simp [ptrI])]

theorem adr_ram {x x' : Machine} {z : UInt8} {o : Nat} (h : x'.ram = x.ram) : adr x' z o = adr x z o := adr_congr (by rw [h]) (fun _ _ => by rw [h])

theorem coin_ram {P : Places} {cs : List UInt8} {z : UInt8} {o t : Nat} {x x' : Machine} (h : x'.ram = x.ram) (hc : Coin P cs z o t x) : Coin P cs z o t x' := by
  unfold Coin InB idx at hc ⊢
  rw [adr_ram h, h]
  exact hc

/-- a step that keeps the offset's byte, the tile's byte, the pointer and the block buffers keeps the fact of the mark `[9]` -/
theorem coin_keep {P : Places} {cs : List UInt8} {z : UInt8} {o t : Nat} {x x' : Machine} (hA : ∀ i ∈ adrL z o t, x'.ram.get! i = x.ram.get! i)
    (hB : ∀ d ∈ bufL P, x'.ram.get! d = x.ram.get! d) (h3 : x.ram.get! t ∈ cs) (hI : InB P x z o → x.ram.get! (idx x z o) = x.ram.get! t) : Coin P cs z o t x' := by
  have ea : adr x' z o = adr x z o := adr_congr (hA o (by simp [adrL])) (fun i hi => hA i (by simp [adrL, hi]))
  have e3 : x'.ram.get! t = x.ram.get! t := hA t (by simp [adrL])
  refine ⟨by rw [e3]; exact h3, fun hin => ?_⟩
  have hin' : InB P x z o := by
    unfold InB idx at hin ⊢
    rw [ea] at hin
    exact hin
  have ei : idx x' z o = idx x z o := by unfold idx; rw [ea]
  rw [ei, e3, hB _ (mem_bufL hin'.2.1 hin'.2.2)]
  exact hI hin'

/-- a step of a piece that is not the erase and that may not write the bytes of `L` keeps them -/
theorem keep_of_mayB {P : Places} {A : AS} {y : Machine} {L : List Nat} (hs : Sim E F A y) (hne : ¬(A.pc = P.erase ∧ A.nmi = false))
    (hm : mayWrite E P L A = false) : ∀ x ∈ L, (go step y).2.ram.get! x = y.ram.get! x := by
  intro x hx
  unfold mayWrite at hm
  cases hc : (A.pc == P.erase && !A.nmi) with
  | true =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    exact absurd hc hne
  | false =>
    rw [hc] at hm
    simp only [Bool.not_false, Bool.true_and, Bool.not_eq_false'] at hm
    exact StepWrites.keep_step hs hm x (List.contains_iff_mem.2 hx)

/-- the zone gives one piece: the state with another mark -/
theorem zoneK_eq (P : Places) (cs : List UInt8) (z : UInt8) (o t : Nat) (A : AS) : ∃ l, zoneK E P cs z o t A = [{ A with log := l }] := by
  unfold zoneK
  by_cases h1 : (A.pc == P.read - 3 && !A.nmi) = true
  · exact ⟨_, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : (A.pc == P.read - 1 && !A.nmi && A.log.head? == some 3) = true
  · exact ⟨_, if_pos h2⟩
  rw [if_neg h2]
  by_cases h3 : (A.pc == P.read && !A.nmi && A.log.head? == some 6) = true
  · exact ⟨_, if_pos h3⟩
  rw [if_neg h3]
  by_cases h4 : (A.pc == P.read + 2 && !A.nmi && A.log.head? == some 4) = true
  · exact ⟨_, if_pos h4⟩
  rw [if_neg h4]
  by_cases h5 : (A.pc == P.read + 4 && !A.nmi && A.log.head? == some 5) = true
  · exact ⟨_, if_pos h5⟩
  rw [if_neg h5]
  by_cases h6 : (A.pc == P.erase - 4 && !A.nmi && A.log.head? == some 9) = true
  · exact ⟨_, if_pos h6⟩
  rw [if_neg h6]
  by_cases h7 : (A.pc == P.erase - 2 && !A.nmi && A.log.head? == some 7) = true
  · exact ⟨_, if_pos h7⟩
  rw [if_neg h7]
  by_cases h8 : (A.pc == P.erase && !A.nmi && A.log.head? == some 10) = true
  · exact ⟨_, if_pos h8⟩
  rw [if_neg h8]
  by_cases h9 : oneStep A.log = true
  · exact ⟨_, if_pos h9⟩
  rw [if_neg h9]
  by_cases h10 : (A.log.head? == some 9 && mayWrite E P (adrL z o t) A) = true
  · exact ⟨_, if_pos h10⟩
  rw [if_neg h10]
  exact ⟨A.log, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **One frame of the room keeps the blocks.** The frame starts in the room's condition with every byte of the block buffers that is not a coin in the map `M` at the
map's value, and each instruction meets `SiteOK`. Then the frame ends so. The only step that writes the block buffers is the erase, and the byte that it writes holds a
coin: the tile that the block buffer routine read through the same pointer with the same offset. -/
theorem blocks_frame {P : Places} {cs : List UInt8} {z : UInt8} {o t : Nat} {M r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat}
    (h : OKV (phK E P cs z o t) E P r K C Fu) (hc : codeOK E P z o t = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m)
    (hk : ∀ j, SiteOK P (trace m i j)) (h0 : Solid P cs M m) : Solid P cs M (frame m i) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hOE : PlacesOK E P := h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  simp only [codeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, c22⟩, c24⟩, cot⟩, cob⟩, c23⟩ := hc
  let Φ : Nat → Bool → List Nat → Prop := fun j _ l =>
    Solid P cs M (trace m i j) ∧
    (l.head? = some 3 → (trace m i j).ram.get! o = (trace m i j).a) ∧
    (l.head? = some 6 → (trace m i j).y = (trace m i j).ram.get! o) ∧
    (l.head? = some 4 → InB P (trace m i j) z o → (trace m i j).a = (trace m i j).ram.get! (idx (trace m i j) z o)) ∧
    (l.head? = some 5 → InB P (trace m i j) z o → (trace m i j).ram.get! (idx (trace m i j) z o) = (trace m i j).ram.get! t) ∧
    (l.head? = some 9 → Coin P cs z o t (trace m i j)) ∧
    (l.head? = some 7 → Coin P cs z o t (trace m i j) ∧ (trace m i j).y = (trace m i j).ram.get! o) ∧
    (l.head? = some 10 → Coin P cs z o t (trace m i j) ∧ (trace m i j).y = (trace m i j).ram.get! o)
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phK E P cs z o t).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    obtain ⟨l, hl⟩ := zoneK_eq (E := E) P cs z o t A'
    refine ⟨{ A' with log := l }, ?_, sim_bits hsx hr _ _⟩
    show _ ∈ zoneK E P cs z o t A'
    rw [hl]
    exact List.mem_singleton.2 rfl
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phK E P cs z o t).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phK E P cs z o t).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p0, p3, p6, p4, p5, p9, p7, p10⟩ hs' hf hr hA₁ hs₁ hok
    have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
    have hsE : Sim E (m.frame, 2) A' (trace m i j) := by rw [← h.env]; exact hs'
    have hnext : trace m i (j + 1) = (go step (trace m i j)).2 := RoomVert.trace_succ hf hs'.halted
    have hhalt := hsE.halted
    have hprg := hsE.prg
    have hmask := hsE.mask
    have hpcx := hsE.pc
    have hnmx := hsE.nmi
    have hsz := hsE.size
    -- what the walk asks of the piece
    have hok' : okK E P z o t A₁ = true := hok
    simp only [okK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at hok'
    obtain ⟨⟨⟨o1, o5⟩, o9⟩, o8⟩ := hok'
    have notErase : A₁.log ≠ [8] → ¬(A₁.pc = P.erase ∧ A₁.nmi = false) := by
      intro h8 hc
      rcases o8 with (o | o) | o
      · rw [hc.2] at o
        cases o
      · exact o hc.1
      · exact h8 o
    have keepB : A₁.log ≠ [8] → ∀ d ∈ bufL P, (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
      intro h8 d hd
      rw [hnext]
      exact keep_of_mayB hs₂ (notErase h8) o1 d hd
    have solid_keep : A₁.log ≠ [8] → Solid P cs M (trace m i (j + 1)) := by
      intro h8 d hd1 hd2 hd3
      rw [keepB h8 d (mem_bufL hd1 hd2)]
      exact p0 d hd1 hd2 hd3
    have keepA : A₁.log.head? = some 9 → ∀ d ∈ adrL z o t, (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
      intro h9 d hd
      rw [hnext]
      refine keep_of_mayB hs₂ (notErase (fun e => by rw [e] at h9; cases h9)) ?_ d hd
      rcases o9 with o | o
      · exact absurd h9 o
      · exact o
    -- the instruction at the machine's place
    have opAt : ∀ (q : UInt16) (v : UInt8), A'.pc = q → E.prg.get! (q &&& E.mask).toNat = v →
        (trace m i j).prg.get! ((trace m i j).pc &&& (trace m i j).prgMask).toNat = v := by
      intro q v e1 e2
      rw [hprg, hmask, hpcx, e1]
      exact e2
    have opdAt : ∀ (q : UInt16) (v : UInt8), A'.pc = q → E.prg.get! ((q + 1) &&& E.mask).toNat = v → operand (trace m i j) = v := by
      intro q v e1 e2
      unfold operand
      rw [hprg, hmask, hpcx, e1]
      exact e2
    have opdI : ∀ (q : UInt16) (v : Nat), A'.pc = q → zI (E.prg.get! ((q + 1) &&& E.mask).toNat) = v →
        ((operand (trace m i j)).toUInt16 &&& 0x7FF).toNat = v := by
      intro q v e1 e2
      rw [opdAt q _ e1 rfl]
      exact e2
    have hA := hA₁
    change A₁ ∈ zoneK E P cs z o t A' at hA
    unfold zoneK at hA
    by_cases hc : (A'.pc == P.read - 3 && !A'.nmi) = true
    · -- the store of the offset
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [3] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hc.2
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hc.1]; exact c11
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hc.1]; exact c12
      have a1 := step_sta_zp hn hhalt hp0 hp1 (opAt _ _ hc.1 c1) hsz
      have a2 := step_sta_zp_a hn hhalt hp0 hp1 (opAt _ _ hc.1 c1)
      rw [opdI _ _ hc.1 c2] at a1
      refine ⟨solid_keep (by rw [hlog]; decide), fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read - 1 && !A'.nmi && A'.log.head? == some 3) = true
    · -- the copy of the offset to Y
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [6] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c13
      obtain ⟨a1, a2⟩ := step_tay hn hhalt hp0 (opAt _ _ hq c3)
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
      exact (p3 hl).symm
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read && !A'.nmi && A'.log.head? == some 6) = true
    · -- the read
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [4] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact hOE.read.1
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c14
      obtain ⟨a1, a2⟩ := step_lda_izy hn hhalt hp0 (opAt _ _ hq hOE.read.2)
      have hy := p6 hl
      have hra : readAddr (trace m i j) = adr (trace m i j) z o := by
        rw [readAddr_eq hp1, opdAt _ _ hq c4, hy]
        rfl
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ hin => ?_, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      have ea : adr (trace m i (j + 1)) z o = adr (trace m i j) z o := adr_ram (by rw [hnext, a2])
      have hlt : adr (trace m i j) z o < 0x2000 := by rw [← ea]; exact hin.1
      have ei : idx (trace m i (j + 1)) z o = idx (trace m i j) z o := by unfold idx; rw [ea]
      rw [ei, hnext, a1, a2, readVal_eq (by rw [hra]; exact hlt), hra]
      rfl
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read + 2 && !A'.nmi && A'.log.head? == some 4) = true
    · -- the store of the tile read
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [5] := by rw [e]
      have hk3 : StepWrites.keepOK E (fun i => i != t) A₁ = true := by
        rcases o5 with o | o
        · rw [hlog] at o
          exact absurd rfl o
        · exact o
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c15
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c16
      have a1 := step_sta_zp hn hhalt hp0 hp1 (opAt _ _ hq c6) hsz
      rw [opdI _ _ hq c7] at a1
      have keep3 : ∀ d, d ≠ t → (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
        intro d hd
        rw [hnext]
        exact StepWrites.keep_step hs₂ hk3 d (by simpa using hd)
      have ea : adr (trace m i (j + 1)) z o = adr (trace m i j) z o :=
        adr_congr (keep3 o cot) (fun q hq' => keep3 q (c24 q hq').1.2)
      have ei : idx (trace m i (j + 1)) z o = idx (trace m i j) z o := by unfold idx; rw [ea]
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ hin => ?_,
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      have hin' : InB P (trace m i j) z o := by
        unfold InB idx at hin ⊢
        rw [ea] at hin
        exact hin
      have h3 : idx (trace m i j) z o ≠ t := by have := hin'.2.1; omega
      rw [ei, keep3 _ h3, ← p4 hl hin', hnext, a1]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read + 4 && !A'.nmi && A'.log.head? == some 5) = true
    · -- after the store of the tile read: a coin, or the mark is dropped
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = if cs.any (knIs (A'.getK t)) then [9] else [] := by rw [e]
      by_cases hcoin : cs.any (knIs (A'.getK t)) = true
      · rw [if_pos hcoin] at hlog
        have h9 : A₁.log.head? = some 9 := by rw [hlog]; rfl
        have h8 : A₁.log ≠ [8] := by rw [hlog]; decide
        rw [hlog]
        refine ⟨solid_keep h8, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        obtain ⟨c, hcm, hck⟩ := List.any_eq_true.1 hcoin
        have h3 : (trace m i j).ram.get! t = c := knIs_spec hck (hsE.ram t (by omega))
        exact coin_keep (keepA h9) (keepB h8) (by rw [h3]; exact hcm) (p5 hl)
      · rw [if_neg hcoin] at hlog
        rw [hlog]
        exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase - 4 && !A'.nmi && A'.log.head? == some 9) = true
    · -- the load of the offset into Y, before the erase
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [7] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c17
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c18
      obtain ⟨a1, a2⟩ := step_ldy_zp hn hhalt hp0 hp1 (opAt _ _ hq c8)
      rw [opdI _ _ hq c9] at a1
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨coin_ram (by rw [hnext, a2]) (p9 hl), ?_⟩, fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase - 2 && !A'.nmi && A'.log.head? == some 7) = true
    · -- the load of the empty tile
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [10] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c19
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c20
      obtain ⟨a1, a2⟩ := step_lda_imm hn hhalt hp0 hp1 (opAt _ _ hq c10)
      obtain ⟨g1, g2⟩ := p7 hl
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨coin_ram (by rw [hnext, a2]) g1, ?_⟩⟩
      rw [hnext, a1, a2]
      exact g2
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase && !A'.nmi && A'.log.head? == some 10) = true
    · -- the erase: the byte that it writes holds a coin
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [8] := by rw [e]
      have hpc1 : A₁.pc = P.erase := by rw [e]; exact hq
      have hnm1 : A₁.nmi = false := by rw [e]; exact hnm
      rw [hlog]
      obtain ⟨⟨g1, g2⟩, g3⟩ := p10 hl
      have hpe : (trace m i j).pc = P.erase := by rw [hpcx]; exact hq
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpe]; exact c21
      obtain ⟨w1, w2, w3⟩ := (hk j).erase hpe
      have hwa : writeAddr (trace m i j) = adr (trace m i j) z o := by
        rw [writeAddr_eq hp1, opdAt _ _ hq c5, g3]
        rfl
      have hin : InB P (trace m i j) z o := by
        unfold InB idx
        rw [← hwa]
        exact ⟨w1, w2, w3⟩
      have hcoin : (trace m i j).ram.get! (idx (trace m i j) z o) ∈ cs := by rw [g2 hin]; exact g1
      refine ⟨fun d hd1 hd2 hd3 => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      by_cases hd : d = idx (trace m i j) z o
      · exfalso
        apply hd3
        rw [← p0 d hd1 hd2 hd3, hd]
        exact hcoin
      · rw [hnext, erase_other hOE hs₂ hnm1 hpc1 (hk j) (by rw [hwa]; exact hd)]
        exact p0 d hd1 hd2 hd3
    rw [if_neg hc] at hA
    clear hc
    by_cases hone : oneStep A'.log = true
    · -- a mark for one step out of its place
      rw [if_pos hone] at hA
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [] := by rw [e]
      rw [hlog]
      exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hone] at hA
    by_cases hc : (A'.log.head? == some 9 && mayWrite E P (adrL z o t) A') = true
    · -- a step that may write the bytes of the address
      rw [if_pos hc] at hA
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [] := by rw [e]
      rw [hlog]
      exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hc] at hA
    clear hc
    -- the state stays
    have e := List.mem_singleton.1 hA
    have hlog : A₁.log = A'.log := by rw [e]
    simp only [oneStep, Bool.or_eq_true, beq_iff_eq, not_or] at hone
    obtain ⟨⟨⟨⟨⟨⟨n3, n6⟩, n4⟩, n5⟩, n7⟩, n10⟩, n8⟩ := hone
    have h8 : A₁.log ≠ [8] := by rw [hlog]; exact n8
    rw [hlog]
    refine ⟨solid_keep h8, fun h => absurd h n3, fun h => absurd h n6, fun h => absurd h n4, fun h => absurd h n5, fun h9 => ?_,
      fun h => absurd h n7, fun h => absurd h n10⟩
    have h9' : A₁.log.head? = some 9 := by rw [hlog]; exact h9
    obtain ⟨g1, g2⟩ := p9 h9
    exact coin_keep (keepA h9') (keepB h8) g1 g2

  have h0' : Φ 0 S.spent S.log := by
    refine ⟨fun d a b c => h0 d a b c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [s2] <;> exact fun h => absurd h (by decide)
  obtain ⟨_, J, _, _, hJ3, B, _, _, hB3⟩ := RoomVert.frame_of_walkV (Z := phK E P cs z o t) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0' hstep
  rw [hJ3]
  exact hB3.1


set_option maxHeartbeats 2000000 in
/-- The existing non-coin map invariant at every instruction still in this frame.
All hypotheses are identical to blocks_frame; no new frame condition is added. -/
theorem blocks_trace {P : Places} {cs : List UInt8} {z : UInt8} {o t : Nat} {M r : Machine} {K : List (Nat × UInt8)} {C : CfgS} {Fu : Nat}
    (h : OKV (phK E P cs z o t) E P r K C Fu) (hc : codeOK E P z o t = true) {m : Machine} {i : UInt8} (hm : RoomCond E r K m)
    (hk : ∀ j, SiteOK P (trace m i j)) (h0 : Solid P cs M m) : ∀ j, (trace m i j).frame = m.frame → Solid P cs M (trace m i j) := by
  obtain ⟨S, hw, hs, s1, s2, s3⟩ := RoomVert.start_of_room h hm
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hOE : PlacesOK E P := h.places
  have hk' : ∀ j, SiteOK C.P (trace m i j) := by rw [h.pl]; exact hk
  simp only [codeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, c22⟩, c24⟩, cot⟩, cob⟩, c23⟩ := hc
  let Φ : Nat → Bool → List Nat → Prop := fun j _ l =>
    Solid P cs M (trace m i j) ∧
    (l.head? = some 3 → (trace m i j).ram.get! o = (trace m i j).a) ∧
    (l.head? = some 6 → (trace m i j).y = (trace m i j).ram.get! o) ∧
    (l.head? = some 4 → InB P (trace m i j) z o → (trace m i j).a = (trace m i j).ram.get! (idx (trace m i j) z o)) ∧
    (l.head? = some 5 → InB P (trace m i j) z o → (trace m i j).ram.get! (idx (trace m i j) z o) = (trace m i j).ram.get! t) ∧
    (l.head? = some 9 → Coin P cs z o t (trace m i j)) ∧
    (l.head? = some 7 → Coin P cs z o t (trace m i j) ∧ (trace m i j).y = (trace m i j).ram.get! o) ∧
    (l.head? = some 10 → Coin P cs z o t (trace m i j) ∧ (trace m i j).y = (trace m i j).ram.get! o)
  have hz : ∀ (A' : AS) (x : Machine), A'.rk = false → Sim C.E (m.frame, 2) A' x → ∃ A₁ ∈ (phK E P cs z o t).zone A', Sim C.E (m.frame, 2) A₁ x := by
    intro A' x hr hsx
    obtain ⟨l, hl⟩ := zoneK_eq (E := E) P cs z o t A'
    refine ⟨{ A' with log := l }, ?_, sim_bits hsx hr _ _⟩
    show _ ∈ zoneK E P cs z o t A'
    rw [hl]
    exact List.mem_singleton.2 rfl
  have hstep : ∀ j (A' A₁ : AS), Φ j A'.spent A'.log → Sim C.E (m.frame, 2) A' (trace m i j) → (trace m i j).frame = m.frame → A'.rk = false →
      A₁ ∈ (phK E P cs z o t).zone A' → Sim C.E (m.frame, 2) A₁ (trace m i j) → (phK E P cs z o t).ok A₁ = true → Φ (j + 1) A₁.spent A₁.log := by
    intro j A' A₁ ⟨p0, p3, p6, p4, p5, p9, p7, p10⟩ hs' hf hr hA₁ hs₁ hok
    have hs₂ : Sim E (m.frame, 2) A₁ (trace m i j) := by rw [← h.env]; exact hs₁
    have hsE : Sim E (m.frame, 2) A' (trace m i j) := by rw [← h.env]; exact hs'
    have hnext : trace m i (j + 1) = (go step (trace m i j)).2 := RoomVert.trace_succ hf hs'.halted
    have hhalt := hsE.halted
    have hprg := hsE.prg
    have hmask := hsE.mask
    have hpcx := hsE.pc
    have hnmx := hsE.nmi
    have hsz := hsE.size
    -- what the walk asks of the piece
    have hok' : okK E P z o t A₁ = true := hok
    simp only [okK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq] at hok'
    obtain ⟨⟨⟨o1, o5⟩, o9⟩, o8⟩ := hok'
    have notErase : A₁.log ≠ [8] → ¬(A₁.pc = P.erase ∧ A₁.nmi = false) := by
      intro h8 hc
      rcases o8 with (o | o) | o
      · rw [hc.2] at o
        cases o
      · exact o hc.1
      · exact h8 o
    have keepB : A₁.log ≠ [8] → ∀ d ∈ bufL P, (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
      intro h8 d hd
      rw [hnext]
      exact keep_of_mayB hs₂ (notErase h8) o1 d hd
    have solid_keep : A₁.log ≠ [8] → Solid P cs M (trace m i (j + 1)) := by
      intro h8 d hd1 hd2 hd3
      rw [keepB h8 d (mem_bufL hd1 hd2)]
      exact p0 d hd1 hd2 hd3
    have keepA : A₁.log.head? = some 9 → ∀ d ∈ adrL z o t, (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
      intro h9 d hd
      rw [hnext]
      refine keep_of_mayB hs₂ (notErase (fun e => by rw [e] at h9; cases h9)) ?_ d hd
      rcases o9 with o | o
      · exact absurd h9 o
      · exact o
    -- the instruction at the machine's place
    have opAt : ∀ (q : UInt16) (v : UInt8), A'.pc = q → E.prg.get! (q &&& E.mask).toNat = v →
        (trace m i j).prg.get! ((trace m i j).pc &&& (trace m i j).prgMask).toNat = v := by
      intro q v e1 e2
      rw [hprg, hmask, hpcx, e1]
      exact e2
    have opdAt : ∀ (q : UInt16) (v : UInt8), A'.pc = q → E.prg.get! ((q + 1) &&& E.mask).toNat = v → operand (trace m i j) = v := by
      intro q v e1 e2
      unfold operand
      rw [hprg, hmask, hpcx, e1]
      exact e2
    have opdI : ∀ (q : UInt16) (v : Nat), A'.pc = q → zI (E.prg.get! ((q + 1) &&& E.mask).toNat) = v →
        ((operand (trace m i j)).toUInt16 &&& 0x7FF).toNat = v := by
      intro q v e1 e2
      rw [opdAt q _ e1 rfl]
      exact e2
    have hA := hA₁
    change A₁ ∈ zoneK E P cs z o t A' at hA
    unfold zoneK at hA
    by_cases hc : (A'.pc == P.read - 3 && !A'.nmi) = true
    · -- the store of the offset
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [3] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hc.2
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hc.1]; exact c11
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hc.1]; exact c12
      have a1 := step_sta_zp hn hhalt hp0 hp1 (opAt _ _ hc.1 c1) hsz
      have a2 := step_sta_zp_a hn hhalt hp0 hp1 (opAt _ _ hc.1 c1)
      rw [opdI _ _ hc.1 c2] at a1
      refine ⟨solid_keep (by rw [hlog]; decide), fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read - 1 && !A'.nmi && A'.log.head? == some 3) = true
    · -- the copy of the offset to Y
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [6] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c13
      obtain ⟨a1, a2⟩ := step_tay hn hhalt hp0 (opAt _ _ hq c3)
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
      exact (p3 hl).symm
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read && !A'.nmi && A'.log.head? == some 6) = true
    · -- the read
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [4] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact hOE.read.1
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c14
      obtain ⟨a1, a2⟩ := step_lda_izy hn hhalt hp0 (opAt _ _ hq hOE.read.2)
      have hy := p6 hl
      have hra : readAddr (trace m i j) = adr (trace m i j) z o := by
        rw [readAddr_eq hp1, opdAt _ _ hq c4, hy]
        rfl
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ hin => ?_, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      have ea : adr (trace m i (j + 1)) z o = adr (trace m i j) z o := adr_ram (by rw [hnext, a2])
      have hlt : adr (trace m i j) z o < 0x2000 := by rw [← ea]; exact hin.1
      have ei : idx (trace m i (j + 1)) z o = idx (trace m i j) z o := by unfold idx; rw [ea]
      rw [ei, hnext, a1, a2, readVal_eq (by rw [hra]; exact hlt), hra]
      rfl
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read + 2 && !A'.nmi && A'.log.head? == some 4) = true
    · -- the store of the tile read
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [5] := by rw [e]
      have hk3 : StepWrites.keepOK E (fun i => i != t) A₁ = true := by
        rcases o5 with o | o
        · rw [hlog] at o
          exact absurd rfl o
        · exact o
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c15
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c16
      have a1 := step_sta_zp hn hhalt hp0 hp1 (opAt _ _ hq c6) hsz
      rw [opdI _ _ hq c7] at a1
      have keep3 : ∀ d, d ≠ t → (trace m i (j + 1)).ram.get! d = (trace m i j).ram.get! d := by
        intro d hd
        rw [hnext]
        exact StepWrites.keep_step hs₂ hk3 d (by simpa using hd)
      have ea : adr (trace m i (j + 1)) z o = adr (trace m i j) z o :=
        adr_congr (keep3 o cot) (fun q hq' => keep3 q (c24 q hq').1.2)
      have ei : idx (trace m i (j + 1)) z o = idx (trace m i j) z o := by unfold idx; rw [ea]
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ hin => ?_,
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      have hin' : InB P (trace m i j) z o := by
        unfold InB idx at hin ⊢
        rw [ea] at hin
        exact hin
      have h3 : idx (trace m i j) z o ≠ t := by have := hin'.2.1; omega
      rw [ei, keep3 _ h3, ← p4 hl hin', hnext, a1]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.read + 4 && !A'.nmi && A'.log.head? == some 5) = true
    · -- after the store of the tile read: a coin, or the mark is dropped
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = if cs.any (knIs (A'.getK t)) then [9] else [] := by rw [e]
      by_cases hcoin : cs.any (knIs (A'.getK t)) = true
      · rw [if_pos hcoin] at hlog
        have h9 : A₁.log.head? = some 9 := by rw [hlog]; rfl
        have h8 : A₁.log ≠ [8] := by rw [hlog]; decide
        rw [hlog]
        refine ⟨solid_keep h8, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
        obtain ⟨c, hcm, hck⟩ := List.any_eq_true.1 hcoin
        have h3 : (trace m i j).ram.get! t = c := knIs_spec hck (hsE.ram t (by omega))
        exact coin_keep (keepA h9) (keepB h8) (by rw [h3]; exact hcm) (p5 hl)
      · rw [if_neg hcoin] at hlog
        rw [hlog]
        exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase - 4 && !A'.nmi && A'.log.head? == some 9) = true
    · -- the load of the offset into Y, before the erase
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [7] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c17
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c18
      obtain ⟨a1, a2⟩ := step_ldy_zp hn hhalt hp0 hp1 (opAt _ _ hq c8)
      rw [opdI _ _ hq c9] at a1
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨coin_ram (by rw [hnext, a2]) (p9 hl), ?_⟩, fun h => absurd h (by decide)⟩
      rw [hnext, a1, a2]
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase - 2 && !A'.nmi && A'.log.head? == some 7) = true
    · -- the load of the empty tile
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [10] := by rw [e]
      rw [hlog]
      have hn : (trace m i j).nmiPending = false := by rw [hnmx]; exact hnm
      have hp0 : (trace m i j).pc ≥ 0x8000 := by rw [hpcx, hq]; exact c19
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpcx, hq]; exact c20
      obtain ⟨a1, a2⟩ := step_lda_imm hn hhalt hp0 hp1 (opAt _ _ hq c10)
      obtain ⟨g1, g2⟩ := p7 hl
      refine ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨coin_ram (by rw [hnext, a2]) g1, ?_⟩⟩
      rw [hnext, a1, a2]
      exact g2
    rw [if_neg hc] at hA
    clear hc
    by_cases hc : (A'.pc == P.erase && !A'.nmi && A'.log.head? == some 10) = true
    · -- the erase: the byte that it writes holds a coin
      rw [if_pos hc] at hA
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨hq, hnm⟩, hl⟩ := hc
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [8] := by rw [e]
      have hpc1 : A₁.pc = P.erase := by rw [e]; exact hq
      have hnm1 : A₁.nmi = false := by rw [e]; exact hnm
      rw [hlog]
      obtain ⟨⟨g1, g2⟩, g3⟩ := p10 hl
      have hpe : (trace m i j).pc = P.erase := by rw [hpcx]; exact hq
      have hp1 : (trace m i j).pc + 1 ≥ 0x8000 := by rw [hpe]; exact c21
      obtain ⟨w1, w2, w3⟩ := (hk j).erase hpe
      have hwa : writeAddr (trace m i j) = adr (trace m i j) z o := by
        rw [writeAddr_eq hp1, opdAt _ _ hq c5, g3]
        rfl
      have hin : InB P (trace m i j) z o := by
        unfold InB idx
        rw [← hwa]
        exact ⟨w1, w2, w3⟩
      have hcoin : (trace m i j).ram.get! (idx (trace m i j) z o) ∈ cs := by rw [g2 hin]; exact g1
      refine ⟨fun d hd1 hd2 hd3 => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      by_cases hd : d = idx (trace m i j) z o
      · exfalso
        apply hd3
        rw [← p0 d hd1 hd2 hd3, hd]
        exact hcoin
      · rw [hnext, erase_other hOE hs₂ hnm1 hpc1 (hk j) (by rw [hwa]; exact hd)]
        exact p0 d hd1 hd2 hd3
    rw [if_neg hc] at hA
    clear hc
    by_cases hone : oneStep A'.log = true
    · -- a mark for one step out of its place
      rw [if_pos hone] at hA
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [] := by rw [e]
      rw [hlog]
      exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hone] at hA
    by_cases hc : (A'.log.head? == some 9 && mayWrite E P (adrL z o t) A') = true
    · -- a step that may write the bytes of the address
      rw [if_pos hc] at hA
      have e := List.mem_singleton.1 hA
      have hlog : A₁.log = [] := by rw [e]
      rw [hlog]
      exact ⟨solid_keep (by rw [hlog]; decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    rw [if_neg hc] at hA
    clear hc
    -- the state stays
    have e := List.mem_singleton.1 hA
    have hlog : A₁.log = A'.log := by rw [e]
    simp only [oneStep, Bool.or_eq_true, beq_iff_eq, not_or] at hone
    obtain ⟨⟨⟨⟨⟨⟨n3, n6⟩, n4⟩, n5⟩, n7⟩, n10⟩, n8⟩ := hone
    have h8 : A₁.log ≠ [8] := by rw [hlog]; exact n8
    rw [hlog]
    refine ⟨solid_keep h8, fun h => absurd h n3, fun h => absurd h n6, fun h => absurd h n4, fun h => absurd h n5, fun h9 => ?_,
      fun h => absurd h n7, fun h => absurd h n10⟩
    have h9' : A₁.log.head? = some 9 := by rw [hlog]; exact h9
    obtain ⟨g1, g2⟩ := p9 h9
    exact coin_keep (keepA h9') (keepB h8) g1 g2

  have h0' : Φ 0 S.spent S.log := by
    refine ⟨fun d a b c => h0 d a b c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [s2] <;> exact fun h => absurd h (by decide)
  obtain ⟨hall, _⟩ := RoomVert.frame_of_walkV (Z := phK E P cs z o t) Φ hO h.table h.ops (by show 2 ≤ (2 : UInt8).toNat; decide)
    (by rw [h.env]; exact h.pad) hz hw hs hk' h0' hstep
  intro j hj
  obtain ⟨_,_,_,hPhi⟩ := hall j hj
  exact hPhi.1

end

section
open ScreenPage (placesR envR refR)

/-- the coins: the tiles that a read for the head may give, but the empty one -/
def coinsOf (P : Places) : List UInt8 := P.headTiles.filter (· != 0)

/-- the byte of the zero page with the pointer of the block buffer routine: the operand of its read -/
def ptrOf (E : Env) (P : Places) : UInt8 := E.prg.get! ((P.read + 1) &&& E.mask).toNat

/-- the RAM index of the byte with the routine's offset: the operand of the store three bytes before the read -/
def offOf (E : Env) (P : Places) : Nat := zI (E.prg.get! ((P.read - 3 + 1) &&& E.mask).toNat)

/-- the RAM index of the byte with the tile read: the operand of the store after the read -/
def tileOf (E : Env) (P : Places) : Nat := zI (E.prg.get! ((P.read + 2 + 1) &&& E.mask).toNat)

/-- the walk of the room, with the places of the zero page read from the code -/
abbrev phR (sy : Syms) (nm : Names) (m0 : Machine) : Ph :=
  phK (envR sy nm m0) (placesR sy nm m0) (coinsOf (placesR sy nm m0)) (ptrOf (envR sy nm m0) (placesR sy nm m0)) (offOf (envR sy nm m0) (placesR sy nm m0))
    (tileOf (envR sy nm m0) (placesR sy nm m0))

/-- the walk, on the room -/
abbrev cfgK (sy : Syms) (nm : Names) (m0 : Machine) : CfgS :=
  RoomVert.cfgOfV sy (phR sy nm m0) (fun _ => true) (placesR sy nm m0)
    (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

/-- the check of the walk -/
def checkK (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  RoomVert.walkCheckV sy (phR sy nm m0) (fun _ => true) (placesR sy nm m0)
    (ScreenPage.aidsOf sy nm m0) (envR sy nm m0) (refR m0) (RoomMap.knownT sy nm m0)

end

/-! ## At the first control: from the rows of the change -/

section
open SideChangeEnd (Row Ctx InvL knowsAd mOf)
open PipeChangeEnd (Data timeCtx timeRows InRowsT)
open RoomPair (rowP rowQ rowV of_invL)

/-- a state of a row: it says whether it has control, and if it has, it knows every byte of the block buffers that is not a coin in the map, with the map's value -/
def rowB (sy : Syms) (P : Places) (cs : List UInt8) (M : Machine) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (knowsAd S) &&
    (!controllable sy (mOf S) || (List.range P.bufN).all fun j => cs.contains (M.ram.get! (P.bufLo + j)) || knIs (S.getK (P.bufLo + j)) (M.ram.get! (P.bufLo + j)))

/-- **The check on the ROM**: `RoomPair.rowsCheck`, and in the rows of the time of the change into the room a machine with control has the map's blocks -/
def rowsCheckB (sy : Syms) (nm : Names) (d : Data) (e : Machine) (v0 : List Jump.VS) (P : Places) (cs : List UInt8) (M : Machine) : Bool :=
  (timeRows (timeCtx sy nm d e) d e).all fun w => w.R.all fun S => rowP sy S && rowQ sy S && rowV sy v0 S && rowB sy P cs M S

variable {sy : Syms}

/-- the check with the blocks gives `RoomPair.rowsCheck` -/
theorem rowsCheck_of_B {nm : Names} {d : Data} {e : Machine} {v0 : List Jump.VS} {P : Places} {cs : List UInt8} {M : Machine}
    (h : rowsCheckB sy nm d e v0 P cs M = true) : RoomPair.rowsCheck sy nm d e v0 = true := by
  simp only [rowsCheckB, RoomPair.rowsCheck, List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun w hw S hS => (h w hw S hS).1

theorem solid_of_state {E : Env} {F : Nat × UInt8} {P : Places} {cs : List UInt8} {M : Machine} {S : AS} {m : Machine} (hB : P.bufLo + P.bufN ≤ 2048)
    (hs : Sim E F S m) (hr : rowB sy P cs M S = true) (h : controllable sy m = true) : Solid P cs M m := by
  simp only [rowB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | h1
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · intro d hd1 hd2 hd3
    have h2 := List.all_eq_true.1 h1 (d - P.bufLo) (List.mem_range.2 (by omega))
    rw [show P.bufLo + (d - P.bufLo) = d by omega] at h2
    simp only [Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact absurd (List.contains_iff_mem.1 h2) hd3
    · exact RoomVert.knIs_spec h2 (hs.ram d (by omega))

/-- **The blocks at the first control in the room**, for a machine with control in the rows of the time -/
theorem solid_of_rows {nm : Names} {d : Data} {e : Machine} {v0 : List Jump.VS} {P : Places} {cs : List UInt8} {M : Machine} (hB : P.bufLo + P.bufN ≤ 2048)
    (hc : rowsCheckB sy nm d e v0 P cs M = true) {m : Machine} (h : InRowsT sy nm d e m) (hm : controllable sy m = true) : Solid P cs M m :=
  of_invL (fun hs hq hc => solid_of_state hB hs (by simp only [Bool.and_eq_true] at hq; exact hq.2) hc) hc h hm

end

/-! ## Every frame of the room -/

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

/-- **The blocks of the room stay**: every byte of the block buffers that is not a coin in the map has the map's value -/
abbrev SolidR (sy : Syms) (nmS : Names) (m0 : Machine) (m : Machine) : Prop :=
  Solid (placesR sy nmS m0) (coinsOf (placesR sy nmS m0)) (RoomMap.mapRef m0) m

/-- the rows' check, on the room -/
abbrev rowsCheckR (sy : Syms) (nm : Names) (d : Data) (nmS : Names) (m0 : Machine) (v0 : List Jump.VS) : Bool :=
  rowsCheckB sy nm d (PipeTransition.entry m0) v0 (placesR sy nmS m0) (coinsOf (placesR sy nmS m0)) (RoomMap.mapRef m0)

/-- **The checks on the ROM** of this file: the walk, and the code around the read and the erase -/
structure BChecks (sy : Syms) (nmS : Names) (m0 : Machine) : Prop where
  walk : checkK sy nmS m0 = true
  code : codeOK (envR sy nmS m0) (placesR sy nmS m0) (ptrOf (envR sy nmS m0) (placesR sy nmS m0)) (offOf (envR sy nmS m0) (placesR sy nmS m0))
    (tileOf (envR sy nmS m0) (placesR sy nmS m0)) = true

variable {sy : Syms} {nm nmS : Names} {d : Data} {m0 : Machine} {v0 : List Jump.VS}

/-- **One frame of the room keeps the blocks**, on the room: `blocks_frame` with the checks -/
theorem blocks_step (hW : BChecks sy nmS m0) {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) m)
    (hk : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) (h0 : SolidR sy nmS m0 m) : SolidR sy nmS m0 (frame m i) :=
  blocks_frame (RoomVert.okV_of_check hW.walk) hW.code hm hk h0

/-- **The blocks stay on every frame of the room.** `seq` lists the frames of a run; frame `b` is the first control in the room, a machine with control in the rows of
the change; each frame before `a` meets `SiteOK` on each instruction and starts in the player's routine. Then at the start of each frame from `b` to `a` every byte of the
block buffers that is not a coin in the map has the map's value. -/
theorem blocks_run (hW : BChecks sy nmS m0) (hR : rowsCheckR sy nm d nmS m0 v0 = true) (hF : RoomMap.MapFacts sy nmS m0)
    (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n ≤ a → SolidR sy nmS m0 (seq n) := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay
  have hB : (placesR sy nmS m0).bufLo + (placesR sy nmS m0).bufN ≤ 2048 := by
    have h := hW.code
    simp only [codeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  have key : ∀ k, b + k ≤ a → SolidR sy nmS m0 (seq (b + k)) := by
    intro k
    induction k with
    | zero => exact fun _ => solid_of_rows hB hR hin hctl
    | succ k ih =>
      intro hk
      rw [show b + (k + 1) = b + k + 1 by omega, next]
      exact blocks_step hW (hcond (b + k) (by omega) (by omega)) (sites (b + k) (by omega) (by omega)) (ih (by omega))
  intro n h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, n = b + k := ⟨n - b, by omega⟩
  exact key k h2


/-- The same room-run assumptions give Solid at every instruction inside each room frame. -/
theorem blocks_run_trace (hW : BChecks sy nmS m0) (hR : rowsCheckR sy nm d nmS m0 v0 = true) (hF : RoomMap.MapFacts sy nmS m0)
    (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, (trace (seq n) (inp n) j).frame = (seq n).frame →
      SolidR sy nmS m0 (trace (seq n) (inp n) j) := by
  have hcnd := RoomMap.cond_of_rows hF hc next hin hctl sites stay
  have hs := blocks_run hW hR hF hc next hin hctl sites stay
  intro n hn ha
  exact blocks_trace (RoomVert.okV_of_check hW.walk) hW.code (hcnd n hn ha)
    (sites n hn ha) (hs n hn (Nat.le_of_lt ha))

end

end Smbrta.RoomBlocks
