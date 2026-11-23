import Theorems.ReadTiles
import Theorems.SideRead
import Theorems.SizeKeep
import Theorems.HeadSide

/-!
# The time of the room's frames from the loops' back jumps

Round 29 (`RoomLate`) proved the time (`SiteParts.Late`) on the room's frames that are not `BufferRecords.U` from one field: each instruction of the sound
routine's code runs at dot `RoomLate.sndDot` (9,000) or earlier (`roomLateS`). On the frames `U` (the room's first frame and the frames after a frame that starts
with the control of the screen's buffers at 6) it kept the whole of `Late` (`roomLate`): there the walks from buffers that they do not know fail at the screen
update, whose loop over the buffer's records has no count that the walk knows.

The walk's time grows for ever only on a loop whose count the walk does not know. Every loop of the code goes back: it has an instruction that branches or jumps
to an address at or before its own (`backJ`). So the walk needs the clamp only at those instructions. Here the walks of `RoomLate` (generalised in round 30 to a
clamp at the instructions that a predicate on the program counter picks) clamp the last dot to `sndDot` only at

* `sndQ`: the back jumps of the sound routine's code (from `SoundEngine` on in the ROM), on the frames that are not `U`;
* `scrQ`: these, and the back jumps of the screen update's loop over the records (from `RepeatByte` to the end of `UpdateScreen`'s test), on the frames `U`.

The four walks of `BufferRecords.recCheck` are all walked with the time (`recCheckB`): (ii) and (iii) from the buffers' patterns with `sndQ`, (i) and (iv) from
buffers that the walk does not know with `scrQ`. So `loop_sites_of_rows` asks no `Late` at all: on the frames `U` it asks `LateS scrQ`, on the others `LateS sndQ`.
The predicate is found from the ROM's bytes at the program counter; it has no address of its own.

The coin's erase (`SiteParts.Erase`: the `STA (zp),Y` that erases a coin writes in the block buffers). At the erase the walks know the pointer's high byte, the
block buffers' page, but neither its low byte nor Y (the row's offset): the walk's `ADC` gives a result only when every bit of both values is known, and the
player's position is not known. So the walks prove that the erase writes in the RAM, at or past the block buffers' start (`eraseOK`, `erase_of_ok`), and the
route asks only that it writes below their end (`EraseEnd`).

Round 31: the four walks split the state before the add of the pointer's low byte (`EraseSplit.splitK` at `EraseSplit.adcAt`, the walk `EraseSplit.walkK`), and the
search keeps the two block buffers apart (`EraseSplit.ptrKey`). Then at the erase through a pointer into the first block buffer the walk knows the low byte at most
15 (the column), and with `Y` at most 255 the erase is below the block buffers' end (`eraseOK2`, `erase_of_ok2`). The route asks `EraseEnd` only of an erase whose
pointer is at or past the second block buffer's start (`EraseTwo`).

Round 32: the walks also split the player's height in the collision routine, with bits 1 to 7 of the size known at each frame's start (`knownS`, from
`SizeKeep.byte_all` in the frames' induction) and the crouch byte split (`EraseRow`). Then they know `Y` at every erase, and the erase is below the block
buffers' end for every pointer (`eraseOK4`, `erase_of_ok4`): the route asks nothing of the erase.

Round 34: the walks also check at every state that its step writes no byte of the block buffers but the coin's erase with the accumulator 0
(`ReadTiles.keepOKB`), and at the block buffer routine's read that the address is in the block buffers (`readInOK`, with the bound of `Y` from
`EraseRange.xferY`). The frames' induction carries the tiles of the block buffers (`RoomMap.TilesIn`) from the room's first control (`RoomMap.tiles_of_rows`)
through every instruction (`ReadTiles.frameVI`): the route asks only the head's half of `SiteParts.Read` (`ReadTiles.ReadH`). And the walks' step has a
fifth piece at the side pipe's read of the position (`EraseRange.pstepX`), and two more checks (`SideRead.xChk`): a frame that reads the position ends with
another routine than the player's (`SideRead.no_xAt`), so the route asks `Xbit` only on the entering frame.

There is no game data in this file. Page: `1-1/d-2-4-2-4-LoopTime.md`.
-/

namespace Smbrta.LoopTime

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids RoomCond clampS weaken coverS startsR writeAddr)
open RoomPause (Reg pstep Ph InCls)
open SiteParts (Late Off)
open RoomLate (LateS timeOK late_of_time RestS sndDot fixCuts chkT siteOK_of_T)
open SideRead (stAtOf rtOK wsetOK finX XInv xinv_step xinv_stop xinv_zero no_xAt xChk xFacts)

/-! ## The loops' back jumps -/

/-- **A back jump**: the instruction at `pc` in the ROM is a relative branch with a negative offset, or a `JMP` to an address at or before `pc` -/
def backJ (m0 : Machine) (pc : UInt16) : Bool :=
  let op := romByte m0 pc
  (op &&& 0x1F == 0x10 && decide (0x80 ≤ romByte m0 (pc + 1))) ||
    (op == 0x4C && decide ((romByte m0 (pc + 1)).toUInt16 ||| ((romByte m0 (pc + 2)).toUInt16 <<< 8) ≤ pc))

/-- the back jumps of the sound routine's code (from `SoundEngine` on in the ROM): the sound routine's loops -/
def sndQ (sy : Syms) (m0 : Machine) (pc : UInt16) : Bool := decide (sy.SoundEngine ≤ pc) && backJ m0 pc

/-- the back jumps of the sound routine's code and of the screen update's loop over the buffer's records (from `RepeatByte` to the end of `UpdateScreen`'s test of
the next record) -/
def scrQ (sy : Syms) (m0 : Machine) (pc : UInt16) : Bool :=
  sndQ sy m0 pc || (decide (sy.RepeatByte ≤ pc) && decide (pc < sy.UpdateScreen + 16) && backJ m0 pc)

theorem lateS_snd {sy : Syms} {m0 m : Machine} {D : Nat} (h : LateS (scrQ sy m0) D m) : LateS (sndQ sy m0) D m := by
  intro hq
  apply h
  simp only [scrQ, hq, Bool.true_or]

/-! ## The coin's erase: the walk knows the pointer's page -/

/-- **The end of the coin's erase**: the `STA (zp),Y` that erases a coin writes below the end of the block buffers. The route asks this; the walk proves the rest
of `SiteParts.Erase` (the address is in the RAM, at or past the block buffers' start) -/
def EraseEnd (P : Places) (m : Machine) : Prop :=
  m.pc = P.erase → (writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN

/-- the check at the erase: the pointer's high byte is known, its page with 510 bytes more is inside the RAM (2048 bytes), and it is at or past the block
buffers' start -/
def eraseOK (P : Places) (E : Env) (A : AS) : Bool :=
  A.pc != P.erase ||
    (let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
     let h := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
     h.isK && decide (h.v.toNat * 256 + 510 < 2048) && decide (P.bufLo ≤ (h.v.toUInt16 <<< 8).toNat) && decide (0x8000 ≤ A.pc + 1))

set_option maxRecDepth 20000 in
/-- a pointer from a low byte and a high byte at most 6: the value, checked for all 7 · 256 of them -/
theorem ptr_val : ∀ lo : Fin 256, ∀ hi : Fin 7,
    ((lo.val.toUInt8).toUInt16 ||| ((hi.val.toUInt8).toUInt16 <<< 8)).toNat = lo.val + 256 * hi.val := by
  decide

/-- **The page of an `STA (zp),Y`**: with the pointer's high byte `hi` at most 6, the address is below `0x800` and at least `256 · hi` -/
theorem addr_page (lo hi y : UInt8) (h : hi ≤ 6) :
    (lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + y.toUInt16 < 0x800 ∧ hi.toUInt16 <<< 8 ≤ (lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + y.toUInt16 := by
  have hh : hi.toNat < 7 := by
    have := UInt8.le_iff_toNat_le.1 h
    have e : (6 : UInt8).toNat = 6 := rfl
    omega
  have hl : lo.toNat < 256 := UInt8.toNat_lt lo
  have hy : y.toNat < 256 := UInt8.toNat_lt y
  have hp := ptr_val ⟨lo.toNat, hl⟩ ⟨hi.toNat, hh⟩
  simp only [Nat.toUInt8, UInt8.ofNat_toNat] at hp
  have hs : (hi.toUInt16 <<< 8).toNat = 256 * hi.toNat := by
    rw [UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
    have e : (8 : UInt16).toNat % 16 = 8 := rfl
    rw [e, Nat.shiftLeft_eq]
    have : hi.toNat * 2 ^ 8 < 2 ^ 16 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  have ha : ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + y.toUInt16).toNat = lo.toNat + 256 * hi.toNat + y.toNat := by
    rw [UInt16.toNat_add, hp, UInt8.toNat_toUInt16]
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · rw [UInt16.lt_iff_toNat_lt, ha]
    have e : (0x800 : UInt16).toNat = 2048 := rfl
    omega
  · rw [UInt16.le_iff_toNat_le, ha, hs]
    omega

theorem and7FF_of_lt (a : UInt16) (h : a < 0x800) : a &&& 0x7FF = a := by
  apply UInt16.toNat_inj.1
  rw [UInt16.toNat_and]
  have e : (0x7FF : UInt16).toNat = 2 ^ 11 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  have h2 := UInt16.lt_iff_toNat_lt.1 h
  have e2 : (0x800 : UInt16).toNat = 2048 := rfl
  rw [e2] at h2
  exact Nat.mod_eq_of_lt h2

theorem and255 (x : UInt8) : x &&& 255 = x := by
  apply UInt8.toNat_inj.1
  rw [UInt8.toNat_and]
  have e : (255 : UInt8).toNat = 2 ^ 8 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt x)

/-- the value of a pointer from a low byte and a high byte at most 6, and of the pointer plus `Y` -/
theorem addr_val (lo hi y : UInt8) (h : hi ≤ 6) :
    (lo.toUInt16 ||| (hi.toUInt16 <<< 8)).toNat = lo.toNat + 256 * hi.toNat ∧
    ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + y.toUInt16).toNat = lo.toNat + 256 * hi.toNat + y.toNat := by
  have hh : hi.toNat < 7 := by
    have := UInt8.le_iff_toNat_le.1 h
    have e : (6 : UInt8).toNat = 6 := rfl
    omega
  have hl : lo.toNat < 256 := UInt8.toNat_lt lo
  have hy : y.toNat < 256 := UInt8.toNat_lt y
  have hp := ptr_val ⟨lo.toNat, hl⟩ ⟨hi.toNat, hh⟩
  simp only [Nat.toUInt8, UInt8.ofNat_toNat] at hp
  refine ⟨hp, ?_⟩
  rw [UInt16.toNat_add, hp, UInt8.toNat_toUInt16]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The second block buffer's erase** (round 31): an erase whose pointer is at or past the second block buffer's start (the middle of the block buffers) writes
below the block buffers' end. The route asks this; the walk with the split (`EraseSplit`) proves the rest of `SiteParts.Erase` -/
def EraseTwo (P : Places) (m : Machine) : Prop :=
  m.pc = P.erase → P.bufLo + P.bufN / 2 ≤ (RoomBlocks.ptrZ m (RoomBlocks.operand m) &&& 0x7FF).toNat → (writeAddr m &&& 0x7FF).toNat < P.bufLo + P.bufN

theorem eraseTwo_of_end {P : Places} {m : Machine} (h : EraseEnd P m) : EraseTwo P m := fun hp _ => h hp

/-- **The check at the erase** (round 31): `eraseOK`, and the pointer's high byte with the largest value of its low byte, plus 255 (the largest `Y`), is below the
block buffers' end, or the pointer's high byte with the smallest value of its low byte is at or past the second block buffer's start -/
def eraseOK2 (P : Places) (E : Env) (A : AS) : Bool :=
  eraseOK P E A &&
    (A.pc != P.erase ||
      (let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
       let l := A.getK (z.toUInt16 &&& 0x7FF).toNat
       let h := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
       decide (h.v.toNat * 256 + l.maxv.toNat + 255 < P.bufLo + P.bufN) || decide (P.bufLo + P.bufN / 2 ≤ h.v.toNat * 256 + l.minv.toNat)))

theorem erase_of_ok {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (h : eraseOK P E A = true) (he : EraseEnd P m) :
    SiteParts.Erase P m := by
  intro hpc
  have hA : A.pc = P.erase := by rw [← hs.pc]; exact hpc
  simp only [eraseOK] at h
  generalize hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = z at h
  generalize hI : ((z + 1).toUInt16 &&& 0x7FF).toNat = I at h
  generalize hb : A.getK I = b at h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨⟨hk, h5⟩, hbl⟩, hp⟩
  · exact absurd hA h
  · have hmp : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp
    have hop : RoomBlocks.operand m = z := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hs.pc]
      exact hz
    have hw := RoomBlocks.writeAddr_eq hmp
    rw [hop] at hw
    have hIl : I < 2048 := by
      rw [← hI, UInt16.toNat_and]
      have : ((z + 1).toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
      have e : (0x7FF : UInt16).toNat = 2047 := rfl
      omega
    have hm := hs.ram I hIl
    rw [hb] at hm
    have hk' : b.k = 0xFF := beq_iff_eq.1 hk
    have hv : m.ram.get! I = b.v := by
      unfold AB.mem at hm
      rw [hk', and255, and255] at hm
      exact hm
    have h5' : b.v ≤ 6 := by
      rw [UInt8.le_iff_toNat_le]
      show b.v.toNat ≤ 6
      have h6 := h5
      generalize b.v.toNat = n at h6 ⊢
      omega
    obtain ⟨a1, a2⟩ := addr_page (m.ram.get! (z.toUInt16 &&& 0x7FF).toNat) b.v m.y h5'
    have hw2 : writeAddr m = ((m.ram.get! (z.toUInt16 &&& 0x7FF).toNat).toUInt16 ||| (b.v.toUInt16 <<< 8)) + m.y.toUInt16 := by
      rw [hw]
      unfold RoomBlocks.ptrZ
      rw [hI, hv]
    rw [← hw2] at a1 a2
    refine ⟨?_, ?_, he hpc⟩
    · exact UInt16.lt_iff_toNat_lt.2 (Nat.lt_of_lt_of_le (UInt16.lt_iff_toNat_lt.1 a1) (by decide))
    · rw [and7FF_of_lt _ a1]
      exact Nat.le_trans hbl (UInt16.le_iff_toNat_le.1 a2)

theorem erase_of_ok2 {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (h : eraseOK2 P E A = true) (he : EraseTwo P m) :
    SiteParts.Erase P m := by
  simp only [eraseOK2, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine erase_of_ok hs h1 ?_
  intro hpc
  have hA : A.pc = P.erase := by rw [← hs.pc]; exact hpc
  have h1' := h1
  simp only [eraseOK] at h1'
  generalize hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = z at h1' h2
  generalize hI : ((z + 1).toUInt16 &&& 0x7FF).toNat = I at h1' h2
  generalize hJ : (z.toUInt16 &&& 0x7FF).toNat = J at h2
  generalize hb : A.getK I = b at h1' h2
  generalize hl : A.getK J = l at h2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at h1' h2
  rcases h1' with h1' | ⟨⟨⟨hk, h5⟩, _⟩, hp⟩
  · exact absurd hA h1'
  rcases h2 with h2 | h2
  · exact absurd hA h2
  have hmp : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp
  have hop : RoomBlocks.operand m = z := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hs.pc]
    exact hz
  have hw := RoomBlocks.writeAddr_eq hmp
  rw [hop] at hw
  have hIl : I < 2048 := by
    rw [← hI, UInt16.toNat_and]
    have : ((z + 1).toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hJl : J < 2048 := by
    rw [← hJ, UInt16.toNat_and]
    have : (z.toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hm := hs.ram I hIl
  rw [hb] at hm
  have hk' : b.k = 0xFF := beq_iff_eq.1 hk
  have hv : m.ram.get! I = b.v := by
    unfold AB.mem at hm
    rw [hk', and255, and255] at hm
    exact hm
  have hml := hs.ram J hJl
  rw [hl] at hml
  have h5' : b.v ≤ 6 := by
    rw [UInt8.le_iff_toNat_le]
    show b.v.toNat ≤ 6
    have h6 := h5
    generalize b.v.toNat = n at h6 ⊢
    omega
  have hptr : RoomBlocks.ptrZ m z = (m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8) := by
    unfold RoomBlocks.ptrZ
    rw [hJ, hI, hv]
  have hw2 : writeAddr m = ((m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8)) + m.y.toUInt16 := by
    rw [hw, hptr]
  obtain ⟨a1, _⟩ := addr_page (m.ram.get! J) b.v m.y h5'
  obtain ⟨v1, v2⟩ := addr_val (m.ram.get! J) b.v m.y h5'
  rw [← hw2] at a1 v2
  rw [and7FF_of_lt _ a1, v2]
  have hy : m.y.toNat < 256 := UInt8.toNat_lt m.y
  rcases h2 with h2 | h2
  · have := le_maxv hml
    omega
  · have hpl : (m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8) < 0x800 := by
      rw [UInt16.lt_iff_toNat_lt, v1]
      have e : (0x800 : UInt16).toNat = 2048 := rfl
      have hl2 : (m.ram.get! J).toNat < 256 := UInt8.toNat_lt _
      have hh2 : b.v.toNat ≤ 6 := UInt8.le_iff_toNat_le.1 h5'
      omega
    have hge : P.bufLo + P.bufN / 2 ≤ (RoomBlocks.ptrZ m (RoomBlocks.operand m) &&& 0x7FF).toNat := by
      rw [hop, hptr, and7FF_of_lt _ hpl, v1]
      have := minv_le hml
      omega
    have := he hpc hge
    rw [and7FF_of_lt _ a1, v2] at this
    exact this

/-- **The check at the erase** (round 32): `eraseOK`, and the pointer's high byte with the largest values of its low byte and of `Y` is below the block buffers'
end. With the height split in the collision routine (`EraseRow`) the walks know `Y` (the row's offset) at every erase, so no field is asked -/
def eraseOK4 (P : Places) (E : Env) (A : AS) : Bool :=
  eraseOK P E A &&
    (A.pc != P.erase ||
      (let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
       let l := A.getK (z.toUInt16 &&& 0x7FF).toNat
       let h := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
       decide (h.v.toNat * 256 + l.maxv.toNat + A.y.maxv.toNat < P.bufLo + P.bufN)))

theorem erase_of_ok4 {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (h : eraseOK4 P E A = true) :
    SiteParts.Erase P m := by
  simp only [eraseOK4, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine erase_of_ok hs h1 ?_
  intro hpc
  have hA : A.pc = P.erase := by rw [← hs.pc]; exact hpc
  have h1' := h1
  simp only [eraseOK] at h1'
  generalize hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = z at h1' h2
  generalize hI : ((z + 1).toUInt16 &&& 0x7FF).toNat = I at h1' h2
  generalize hJ : (z.toUInt16 &&& 0x7FF).toNat = J at h2
  generalize hb : A.getK I = b at h1' h2
  generalize hl : A.getK J = l at h2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at h1' h2
  rcases h1' with h1' | ⟨⟨⟨hk, h5⟩, _⟩, hp⟩
  · exact absurd hA h1'
  rcases h2 with h2 | h2
  · exact absurd hA h2
  have hmp : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp
  have hop : RoomBlocks.operand m = z := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hs.pc]
    exact hz
  have hw := RoomBlocks.writeAddr_eq hmp
  rw [hop] at hw
  have hIl : I < 2048 := by
    rw [← hI, UInt16.toNat_and]
    have : ((z + 1).toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hJl : J < 2048 := by
    rw [← hJ, UInt16.toNat_and]
    have : (z.toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hm := hs.ram I hIl
  rw [hb] at hm
  have hk' : b.k = 0xFF := beq_iff_eq.1 hk
  have hv : m.ram.get! I = b.v := by
    unfold AB.mem at hm
    rw [hk', and255, and255] at hm
    exact hm
  have hml := hs.ram J hJl
  rw [hl] at hml
  have h5' : b.v ≤ 6 := by
    rw [UInt8.le_iff_toNat_le]
    show b.v.toNat ≤ 6
    have h6 := h5
    generalize b.v.toNat = n at h6 ⊢
    omega
  have hptr : RoomBlocks.ptrZ m z = (m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8) := by
    unfold RoomBlocks.ptrZ
    rw [hJ, hI, hv]
  have hw2 : writeAddr m = ((m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8)) + m.y.toUInt16 := by
    rw [hw, hptr]
  obtain ⟨a1, _⟩ := addr_page (m.ram.get! J) b.v m.y h5'
  obtain ⟨_, v2⟩ := addr_val (m.ram.get! J) b.v m.y h5'
  rw [← hw2] at a1 v2
  rw [and7FF_of_lt _ a1, v2]
  have := le_maxv hml
  have := le_maxv hs.y
  omega

/-- **The check at the block buffer routine's read** (round 34): the pointer's high byte is known, its page with 510 bytes more is inside the RAM, the pointer
with the smallest value of its low byte is at or past the block buffers' start, and with the largest values of its low byte and of `Y` (from the bounds,
`EraseRange.rhi` of `EraseRange.yI`) the address is below their end -/
def readInOK (P : Places) (E : Env) (A : AS) : Bool :=
  A.pc != P.read ||
    (let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
     let l := A.getK (z.toUInt16 &&& 0x7FF).toNat
     let h := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
     h.isK && decide (h.v.toNat * 256 + 510 < 2048) && decide (P.bufLo ≤ h.v.toNat * 256 + l.minv.toNat) &&
       decide (h.v.toNat * 256 + l.maxv.toNat + EraseRange.rhi A EraseRange.yI < P.bufLo + P.bufN) && decide (0x8000 ≤ A.pc + 1))

theorem readIn_of_ok {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : EraseRange.FOK A.log m)
    (h : readInOK P E A = true) : ReadTiles.ReadIn P m := by
  intro hpc
  have hA : A.pc = P.read := by rw [← hs.pc]; exact hpc
  simp only [readInOK] at h
  generalize hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = z at h
  generalize hI : ((z + 1).toUInt16 &&& 0x7FF).toNat = I at h
  generalize hJ : (z.toUInt16 &&& 0x7FF).toNat = J at h
  generalize hb : A.getK I = b at h
  generalize hl : A.getK J = l at h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨⟨⟨hk, h5⟩, hlo⟩, hhi⟩, hp⟩
  · exact absurd hA h
  have hmp : m.pc + 1 ≥ 0x8000 := by rw [hs.pc]; exact hp
  have hop : RoomBlocks.operand m = z := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hs.pc]
    exact hz
  have hw := RoomBlocks.readAddr_eq hmp
  rw [hop] at hw
  have hIl : I < 2048 := by
    rw [← hI, UInt16.toNat_and]
    have : ((z + 1).toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hJl : J < 2048 := by
    rw [← hJ, UInt16.toNat_and]
    have : (z.toUInt16.toNat &&& (0x7FF : UInt16).toNat) ≤ (0x7FF : UInt16).toNat := Nat.and_le_right
    have e : (0x7FF : UInt16).toNat = 2047 := rfl
    omega
  have hm := hs.ram I hIl
  rw [hb] at hm
  have hk' : b.k = 0xFF := beq_iff_eq.1 hk
  have hv : m.ram.get! I = b.v := by
    unfold AB.mem at hm
    rw [hk', and255, and255] at hm
    exact hm
  have hml := hs.ram J hJl
  rw [hl] at hml
  have h5' : b.v ≤ 6 := by
    rw [UInt8.le_iff_toNat_le]
    show b.v.toNat ≤ 6
    have h6 := h5
    generalize b.v.toNat = n at h6 ⊢
    omega
  have hptr : RoomBlocks.ptrZ m z = (m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8) := by
    unfold RoomBlocks.ptrZ
    rw [hJ, hI, hv]
  have hw2 : ScreenPage.readAddr m = ((m.ram.get! J).toUInt16 ||| (b.v.toUInt16 <<< 8)) + m.y.toUInt16 := by
    rw [hw, hptr]
  obtain ⟨a1, _⟩ := addr_page (m.ram.get! J) b.v m.y h5'
  obtain ⟨_, v2⟩ := addr_val (m.ram.get! J) b.v m.y h5'
  rw [← hw2] at a1 v2
  have hY := (EraseRange.range_ok hs hf (i := EraseRange.yI) (by decide)).2
  rw [EraseRange.valOf_y] at hY
  have l1 := le_maxv hml
  have l2 := minv_le hml
  refine ⟨UInt16.lt_iff_toNat_lt.2 (Nat.lt_of_lt_of_le (UInt16.lt_iff_toNat_lt.1 a1) (by decide)), ?_, ?_⟩
  · rw [and7FF_of_lt _ a1, v2]
    omega
  · rw [and7FF_of_lt _ a1, v2]
    omega

/-- round 34: the checks of `ReadTiles`: the step keeps the block buffers' tiles, and the block buffer routine's read is in them -/
def tilesChk (P : Places) (E : Env) (A : AS) : Bool := ReadTiles.keepOKB P E A && readInOK P E A

/-! ## The four walks with the time, on the ROM -/

section
open BufferRecords (InPat Pat patOK starts0 starts6 fin0 noRegs zO zOC fpcOf ptrBytes ref6 cond_pat idx_of_all end0 reads_all)
open EntryBuffer (ctlI)
open ScreenPage (placesR envR refR aidsOf)
variable {sy : Syms} {nmS : Names} {m0 : Machine} {T : List StepWrites.SState}

/-- the check of the walks from buffers that the walk does not know: the reads' but at the screen update's pointer (and the offset's from the control at 0),
and the time's -/
def chk1B (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.chk0 P E Z A && timeOK P A && eraseOK2 P E A
def chk4B (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.readsOK E Z A && timeOK P A && eraseOK2 P E A

/-- the check of the walks from the patterns: `RoomLate.chkT` (the offset's, the reads' at every pointer, the time's) and the erase's -/
def chk2B (P : Places) (E : Env) (A : AS) : Bool := chkT P E A && eraseOK2 P E A

/-- round 32: `chk1B`, `chk4B`, `chk2B` with the erase's check `eraseOK4` -/
def chk1R (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.chk0 P E Z A && timeOK P A && eraseOK4 P E A
def chk4R (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.readsOK E Z A && timeOK P A && eraseOK4 P E A
def chk2R (P : Places) (E : Env) (A : AS) : Bool := chkT P E A && eraseOK4 P E A

/-- round 34: `chk1R`, `chk4R`, `chk2R` with the checks of `ReadTiles` (`tilesChk`) -/
def chk1T (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := chk1R P E Z A && tilesChk P E A
def chk4T (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := chk4R P E Z A && tilesChk P E A
def chk2T (P : Places) (E : Env) (A : AS) : Bool := chk2R P E A && tilesChk P E A

/-- **The walk's check on the ROM** (round 33): `EraseRange.walkCheckV`, the walk with bounds on RAM bytes: the height is split at each of its tests in the
collision routine and the pieces meet again after it with a bound (`EraseRange.splitRom`, `EraseRange.rulesOf`); the row's offset's bound is found
from the height's bound through the row's seven instructions (`EraseRange.xferA`) and kept as a bound up to the erase; the adder offset kept through the
collision routine's checks, and the registers forgotten after the erase (`EraseRange.aidsV`) -/
def walkChk (sy : Syms) (nm : Names) (m0 : Machine) (Z : Aids) (G : Reg) (pre : Option UInt16) (fz : List Nat) (RK : List (Machine × List (Nat × UInt8)))
    (fin chk : AS → Bool) (sq : UInt16 → Bool) : Bool :=
  EraseRange.walkCheckV (EraseRange.splitD (EraseRange.splitData sy m0 (placesR sy nm m0)))
    (EraseRange.rulesOf sy m0 (placesR sy nm m0) (EraseRange.aidsV sy m0 (placesR sy nm m0) Z)) (placesR sy nm m0) (EraseRange.aidsV sy m0 (placesR sy nm m0) Z)
    (EraseRange.forgetV sy m0 Z (placesR sy nm m0)) (EraseRange.advAt sy m0 (placesR sy nm m0))
    (envR sy nm m0) (EraseRange.keyL (EraseRange.keyData sy m0 (placesR sy nm m0))) G pre fz RK fin chk sq sndDot

/-- round 32: the bits that the room's walks know at a frame's start: those of `SiteParts.knownMC`, and bits 1 to 7 of the player's size (`SizeKeep`) -/
def knownS (sy : Syms) (nm : Names) : List (Nat × UInt8) := SiteParts.knownMC nm ++ [(SizeKeep.sizeI sy, 0xFE)]

/-- the starts of the patterns, with the size's bits -/
def starts0S (sy : Syms) (nm : Names) (m0 : Machine) (L : List (List (Nat × UInt8))) : List (Machine × List (Nat × UInt8)) :=
  L.map fun s => (BufferRecords.refPat (refR m0) s, BufferRecords.knownPat (knownS sy nm) s)

def starts6S (sy : Syms) (nm : Names) (m0 : Machine) (L6 : List (List (Nat × UInt8))) : List (Machine × List (Nat × UInt8)) :=
  L6.map fun s => (BufferRecords.refPat (ref6 nm m0) s, BufferRecords.knownPat (knownS sy nm) s)

/-- the checks for the size's bits: the two references have bits 1 to 7 of the size 0, and the patterns' bytes are not the size -/
def sizeCheck (sy : Syms) (nm : Names) (m0 : Machine) (L L6 : List (List (Nat × UInt8))) : Bool :=
  decide ((refR m0).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) && decide ((ref6 nm m0).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) &&
    L.all (patOK (knownS sy nm)) && L6.all (patOK (knownS sy nm))

theorem size_parts {nm : Names} {L L6 : List (List (Nat × UInt8))} (h : sizeCheck sy nm m0 L L6 = true) :
    (refR m0).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0 ∧ (ref6 nm m0).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0 ∧
    (∀ s ∈ L, patOK (knownS sy nm) s = true) ∧ (∀ s ∈ L6, patOK (knownS sy nm) s = true) := by
  simp only [sizeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- the room's condition with the size's bits -/
theorem cond_size {E : Env} {r m : Machine} {K : List (Nat × UInt8)} (hm : RoomCond E r K m) (hr : r.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0)
    (hz : m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) : RoomCond E r (K ++ [(SizeKeep.sizeI sy, 0xFE)]) m :=
  RoomMusic.roomCond_append hm (fun p hp => by
    rw [List.mem_singleton.1 hp]
    show m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = r.ram.get! (SizeKeep.sizeI sy) &&& 0xFE
    rw [hz, hr])

/-- round 34: the walks' checks with those of the side pipe's read (`xChk`), and the frame's end out of `xAt` to `stAt` (`finX`). The places are arguments, so
that a walk computes them once -/
def chk1X (P : Places) (E : Env) (Z : List UInt8) (G : Reg) (sp : AS → List AS) (st : UInt16) (v : UInt8) (A : AS) : Bool :=
  chk1T P E Z A && xChk P E G sp st v A
def chk2X (P : Places) (E : Env) (G : Reg) (sp : AS → List AS) (st : UInt16) (v : UInt8) (A : AS) : Bool := chk2T P E A && xChk P E G sp st v A
def chk4X (P : Places) (E : Env) (Z : List UInt8) (G : Reg) (sp : AS → List AS) (st : UInt16) (v : UInt8) (A : AS) : Bool :=
  chk4T P E Z A && xChk P E G sp st v A
def finAnd (f g : AS → Bool) (B : AS) : Bool := f B && g B

/-- the arguments of the side pipe's checks, on the room -/
abbrev spR (sy : Syms) (nm : Names) (m0 : Machine) : AS → List AS := EraseRange.splitD (EraseRange.splitData sy m0 (placesR sy nm m0))
abbrev stR (sy : Syms) (nm : Names) (m0 : Machine) : UInt16 := stAtOf sy m0 (placesR sy nm m0)
abbrev rtR (sy : Syms) (nm : Names) (m0 : Machine) : UInt8 := (refR m0).ram.get! (placesR sy nm m0).rtI

/-- (i) with the time: from the control at 0, nothing known of the buffers -/
def walk1B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  sizeCheck sy nm m0 L L6 && xFacts sy nm m0 && ReadTiles.headSub (placesR sy nm m0) && HeadSide.checkX sy nm m0 && walkChk sy nm m0 (fixCuts m0 (zO sy nm m0)) (RoomMusic.regM sy m0 nm T) none [] [(refR m0, knownS sy nm)]
    (finAnd (fin0 (ctlI nm) L L6) (finX (placesR sy nm m0) (stR sy nm m0)))
    (chk1X (placesR sy nm m0) (envR sy nm m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nm T) (spR sy nm m0) (stR sy nm m0) (rtR sy nm m0)) (scrQ sy m0)

/-- (ii) with the time: from the patterns of `L`, the control at 0 -/
def walk2B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkChk sy nm m0 (fixCuts m0 (noRegs (zO sy nm m0))) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0)
    (starts0S sy nm m0 L) (finAnd (fin0 (ctlI nm) L L6) (finX (placesR sy nm m0) (stR sy nm m0)))
    (chk2X (placesR sy nm m0) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (spR sy nm m0) (stR sy nm m0) (rtR sy nm m0)) (sndQ sy m0)

/-- (iii) with the time: from the patterns of `L6`, the control at 6 -/
def walk3B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L6 : List (List (Nat × UInt8))) : Bool :=
  walkChk sy nm m0 (fixCuts m0 (noRegs (zOC sy nm m0))) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0)
    (starts6S sy nm m0 L6) (finX (placesR sy nm m0) (stR sy nm m0))
    (chk2X (placesR sy nm m0) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (spR sy nm m0) (stR sy nm m0) (rtR sy nm m0)) (sndQ sy m0)

/-- (iv) with the time: from the control at 6, nothing known of the buffers -/
def walk4B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) : Bool :=
  walkChk sy nm m0 (fixCuts m0 (aidsOf sy nm m0)) (RoomMusic.regM sy m0 nm T) none [] [(ref6 nm m0, knownS sy nm)]
    (finX (placesR sy nm m0) (stR sy nm m0))
    (chk4X (placesR sy nm m0) (envR sy nm m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nm T) (spR sy nm m0) (stR sy nm m0) (rtR sy nm m0)) (scrQ sy m0)

/-- **The check on the ROM**: `BufferRecords.recCheck` with all four walks with the time, clamped only at the loops' back jumps; round 31: each walk with the split
of `EraseSplit` and the check `eraseOK2` at the erase -/
def recCheckB (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  (RoomMusic.knownM nm).all (fun p => p.1 != ctlI nm) && decide (ctlI nm < 2048) && L.all (patOK (SiteParts.knownMC nm)) &&
    L6.all (patOK (SiteParts.knownMC nm)) && walk1B sy nm m0 T L L6 && walk2B sy nm m0 T L L6 && walk3B sy nm m0 T L6 && walk4B sy nm m0 T

/-- the parts of `recCheckB` that are not walks -/
def recSmall (nm : Names) (L L6 : List (List (Nat × UInt8))) : Bool :=
  (RoomMusic.knownM nm).all (fun p => p.1 != ctlI nm) && decide (ctlI nm < 2048) && L.all (patOK (SiteParts.knownMC nm)) &&
    L6.all (patOK (SiteParts.knownMC nm))

/-- `recCheckB` from its parts: the private proof checks the four walks apart, so that they are built at the same time -/
theorem recCheckB_of {nm : Names} {L L6 : List (List (Nat × UInt8))} (h0 : recSmall nm L L6 = true) (h1 : walk1B sy nm m0 T L L6 = true)
    (h2 : walk2B sy nm m0 T L L6 = true) (h3 : walk3B sy nm m0 T L6 = true) (h4 : walk4B sy nm m0 T = true) : recCheckB sy nm m0 T L L6 = true := by
  show (recSmall nm L L6 && walk1B sy nm m0 T L L6 && walk2B sy nm m0 T L L6 && walk3B sy nm m0 T L6 && walk4B sy nm m0 T) = true
  rw [h0, h1, h2, h3, h4]
  rfl

theorem recB_parts {L L6 : List (List (Nat × UInt8))} (h : recCheckB sy nmS m0 T L L6 = true) :
    (RoomMusic.knownM nmS).all (fun p => p.1 != ctlI nmS) = true ∧ ctlI nmS < 2048 ∧ (∀ s ∈ L, patOK (SiteParts.knownMC nmS) s = true) ∧
    (∀ s ∈ L6, patOK (SiteParts.knownMC nmS) s = true) ∧ walk1B sy nmS m0 T L L6 = true ∧ walk2B sy nmS m0 T L L6 = true ∧ walk3B sy nmS m0 T L6 = true ∧
    walk4B sy nmS m0 T = true := by
  simp only [recCheckB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨List.all_eq_true.2 h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem walk1B_parts {L L6 : List (List (Nat × UInt8))} (h : walk1B sy nmS m0 T L L6 = true) : sizeCheck sy nmS m0 L L6 = true ∧
    walkChk sy nmS m0 (fixCuts m0 (zO sy nmS m0)) (RoomMusic.regM sy m0 nmS T) none [] [(refR m0, knownS sy nmS)]
      (finAnd (fin0 (ctlI nmS) L L6) (finX (placesR sy nmS m0) (stR sy nmS m0)))
      (chk1X (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0))
      (scrQ sy m0) = true := by
  simp only [walk1B, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.2⟩

theorem walk1B_x {L L6 : List (List (Nat × UInt8))} (h : walk1B sy nmS m0 T L L6 = true) : xFacts sy nmS m0 = true := by
  simp only [walk1B, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- round 35: the check `ReadTiles.headSub` is part of walk (i) -/
theorem walk1B_h {L L6 : List (List (Nat × UInt8))} (h : walk1B sy nmS m0 T L L6 = true) : ReadTiles.headSub (placesR sy nmS m0) = true := by
  simp only [walk1B, Bool.and_eq_true] at h
  exact h.1.1.2

/-- round 35: the check `HeadSide.checkX` (the walk that proves `Xbit` from the head's cell) is part of walk (i) -/
theorem walk1B_c {L L6 : List (List (Nat × UInt8))} (h : walk1B sy nmS m0 T L L6 = true) : HeadSide.checkX sy nmS m0 = true := by
  simp only [walk1B, Bool.and_eq_true] at h
  exact h.1.2

/-- what the route asks on each instruction of a frame `U` that the walks (i) and (iv) follow: `Reads` through the pointers `Z`, the head's cell free in the map
`M` (round 34: the rest of `Read` is proved, `ReadTiles`; round 35: `ReadTiles.HeadFree` in place of the head's
half of `Read`), and `LateS` -/
structure RestU (P : Places) (M : Machine) (Z : List UInt8) (sq : UInt16 → Bool) (D : Nat) (m : Machine) : Prop where
  reads : SiteParts.ReadsAt Z m
  headFree : ReadTiles.HeadFree P M m
  lateS : LateS sq D m

/-- what the route asks on each instruction of a frame that the walks (ii) and (iii) follow: `LateS` and the head's cell free in the map `M` (round 32: the erase
is proved; round 34: the rest of `Read`, and `Xbit` apart; round 35: `HeadFree` in place of the head's half of `Read`) -/
structure RestB (P : Places) (M : Machine) (sq : UInt16 → Bool) (D : Nat) (m : Machine) : Prop where
  lateS : LateS sq D m
  headFree : ReadTiles.HeadFree P M m

/-- round 35: the walks' invariant of the block buffers: the tiles of the list, and the map's bits -/
abbrev MapIn (sy : Syms) (nmS : Names) (m0 : Machine) (m : Machine) : Prop :=
  RoomMap.TilesIn (placesR sy nmS m0) m ∧ ReadTiles.ZeroIn (placesR sy nmS m0) (RoomMap.mapRef m0) m

/-- round 34: `Read` from the checks of `ReadTiles` at a state, the block buffers' tiles and the head's half -/
theorem read_of_chk {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : EraseRange.FOK A.log m)
    (hc : tilesChk P E A = true) (ht : RoomMap.TilesIn P m) (hh : ReadTiles.ReadH P m) : SiteParts.Read P m := by
  simp only [tilesChk, Bool.and_eq_true] at hc
  exact ReadTiles.read_of ht (readIn_of_ok hs hf hc.2) hh

/-- round 35: `Read` from the checks of `ReadTiles` at a state, the block buffers' tiles and the map's bits, and the head's cell free in the map -/
theorem read_of_chkF {E : Env} {F : Nat × UInt8} {P : Places} {M : Machine} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : EraseRange.FOK A.log m)
    (hc : tilesChk P E A = true) (hh : ReadTiles.headSub P = true) (ht : RoomMap.TilesIn P m) (hz : ReadTiles.ZeroIn P M m)
    (hfr : ReadTiles.HeadFree P M m) : SiteParts.Read P m := by
  simp only [tilesChk, Bool.and_eq_true] at hc
  have hi := readIn_of_ok hs hf hc.2
  exact ReadTiles.read_of ht hi (ReadTiles.readH_of_free hh ht hz hi hfr)

/-- round 35: the read is in the block buffers, from the checks of `ReadTiles` at a state -/
theorem readIn_of_chk {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hs : Sim E F A m) (hf : EraseRange.FOK A.log m)
    (hc : tilesChk P E A = true) : ReadTiles.ReadIn P m := by
  simp only [tilesChk, Bool.and_eq_true] at hc
  exact readIn_of_ok hs hf hc.2

/-- round 34: the step of a state with the checks of `ReadTiles` keeps the block buffers' tiles -/
theorem tiles_of_chk {E : Env} {F : Nat × UInt8} {P : Places} {A : AS} {m : Machine} (hO : PlacesOK E P) (h0 : (0 : UInt8) ∈ P.tiles) (hs : Sim E F A m)
    (hc : tilesChk P E A = true) (hh : EraseRange.SiteX P m) (ht : RoomMap.TilesIn P m) : RoomMap.TilesIn P (go step m).2 := by
  simp only [tilesChk, Bool.and_eq_true] at hc
  exact ReadTiles.tiles_step hO h0 hs hc.1 hh ht

theorem zero_tiles (sy : Syms) (nmS : Names) (m0 : Machine) : (0 : UInt8) ∈ (placesR sy nmS m0).tiles :=
  ReadTiles.zero_mem_tilesOf _ _ _

/-- the check of the walks from the patterns gives `SiteX` from `RestB` and the block buffers' tiles -/
theorem siteX_of_B {sy : Syms} {nmS : Names} {m0 : Machine} {F : Nat × UInt8} {A : AS} {m : Machine} (hI : (ScreenPage.placesR sy nmS m0).offI < 2048)
    (hs : Sim (ScreenPage.envR sy nmS m0) F A m) (hf : EraseRange.FOK A.log m) (hc : chk2T (ScreenPage.placesR sy nmS m0) (ScreenPage.envR sy nmS m0) A = true)
    (hh : ReadTiles.headSub (ScreenPage.placesR sy nmS m0) = true)
    {sq : UInt16 → Bool} {D : Nat} (hr : RestB (ScreenPage.placesR sy nmS m0) (RoomMap.mapRef m0) sq D m) (ht : MapIn sy nmS m0 m) :
    EraseRange.SiteX (ScreenPage.placesR sy nmS m0) m := by
  simp only [chk2T, chk2R, chkT, SiteParts.chk0, Bool.and_eq_true] at hc
  exact ⟨late_of_time hs hc.1.1.2, BufferRecords.reads_all hs hc.1.1.1.2, read_of_chkF hs hf hc.2 hh ht.1 ht.2 hr.headFree, erase_of_ok4 hs hc.1.2,
    SiteParts.off_of_ok hI hs hc.1.1.1.1⟩

/-- the tiles' step for the walks: the check `chk` includes `tilesChk` -/
theorem tilesI_of {sy : Syms} {nmS : Names} {m0 : Machine} {chk : AS → Bool} (hO : PlacesOK (envR sy nmS m0) (placesR sy nmS m0))
    (hc : ∀ A, chk A = true → tilesChk (placesR sy nmS m0) (envR sy nmS m0) A = true) {R : Machine → Prop} :
    ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim (envR sy nmS m0) F A m → EraseRange.FOK A.log m → chk A = true → R m →
      RoomMap.TilesIn (placesR sy nmS m0) m → EraseRange.SiteX (placesR sy nmS m0) m → RoomMap.TilesIn (placesR sy nmS m0) (go step m).2 :=
  fun hs _ hc2 _ ht hh => tiles_of_chk hO (zero_tiles sy nmS m0) hs (hc _ hc2) hh ht

/-- round 35: the step of the walks' invariant `MapIn`: the check `chk` includes `tilesChk` -/
theorem mapI_of {sy : Syms} {nmS : Names} {m0 : Machine} {chk : AS → Bool} (hO : PlacesOK (envR sy nmS m0) (placesR sy nmS m0))
    (hc : ∀ A, chk A = true → tilesChk (placesR sy nmS m0) (envR sy nmS m0) A = true) {R : Machine → Prop} :
    ∀ {F : Nat × UInt8} {A : AS} {m : Machine}, Sim (envR sy nmS m0) F A m → EraseRange.FOK A.log m → chk A = true → R m →
      MapIn sy nmS m0 m → EraseRange.SiteX (placesR sy nmS m0) m → MapIn sy nmS m0 (go step m).2 := by
  intro F A m hs _ hc2 _ ht hh
  have hc3 := hc _ hc2
  refine ⟨tiles_of_chk hO (zero_tiles sy nmS m0) hs hc3 hh ht.1, ?_⟩
  simp only [tilesChk, Bool.and_eq_true] at hc3
  exact ReadTiles.zero_step hO hs hc3.1 hh ht.2

/-- the invariant `XInv` on the room: with the places of the side pipe's read and the reference's routine -/
abbrev XInvR (sy : Syms) (nmS : Names) (m0 : Machine) (m : Machine) (i : UInt8) (j : Nat) : Prop :=
  XInv (placesR sy nmS m0) (stAtOf sy m0 (placesR sy nmS m0)) ((refR m0).ram.get! (placesR sy nmS m0).rtI) m i j

/-- the step of `XInvR` for the walks: the check `chk` includes `xChk` -/
theorem xJ_of {Ru : EraseRange.Rules} {RK : List (Machine × List (Nat × UInt8))} {C : CfgS} {fin chk : AS → Bool} {sq : UInt16 → Bool} {D : Nat}
    (w : EraseRange.VOK (EraseRange.splitD (EraseRange.splitData sy m0 (placesR sy nmS m0))) Ru (envR sy nmS m0) (placesR sy nmS m0)
      (RoomMusic.regM sy m0 nmS T) RK C fin chk sq D)
    (hx : xFacts sy nmS m0 = true)
    (hc : ∀ A, chk A = true → xChk (placesR sy nmS m0) (envR sy nmS m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0) A = true) {R I : Machine → Prop} {m : Machine} {i : UInt8} :
    ∀ j {A : AS}, Sim (envR sy nmS m0) (m.frame, 2) A (trace m i j) → EraseRange.FOK A.log (trace m i j) → Ph (RoomMusic.regM sy m0 nmS T) A (trace m i j) →
      chk A = true → R (trace m i j) → I (trace m i j) → EraseRange.SiteX (placesR sy nmS m0) (trace m i j) → (trace m i j).frame = m.frame →
      trace m i (j + 1) = (go step (trace m i j)).2 → XInvR sy nmS m0 m i j → XInvR sy nmS m0 m i (j + 1) := by
  intro j A hs hf hp hc2 _ _ hh _ e hJ
  simp only [xFacts, Bool.and_eq_true, decide_eq_true_eq] at hx
  have hx2 := hc A hc2
  simp only [xChk, Bool.and_eq_true] at hx2
  exact xinv_step hx.1.1 hx.1.2 hx.2 (EraseRange.covF_splitRom sy m0 _ _ _) (EraseRange.spent_splitRom sy m0 _) w.places (show 2 ≤ (2 : UInt8).toNat by decide)
    w.tab w.gI w.keepI
    hs hf hp hx2.1 hx2.2 hh e hJ

theorem xJs_of {m : Machine} {i : UInt8} :
    ∀ j, trace m i (j + 1) = trace m i j → XInvR sy nmS m0 m i j → XInvR sy nmS m0 m i (j + 1) :=
  fun _ e h => xinv_stop e h

theorem xJ0_of (hx : xFacts sy nmS m0 = true) {m : Machine} {i : UInt8} : XInvR sy nmS m0 m i 0 := by
  simp only [xFacts, Bool.and_eq_true, decide_eq_true_eq] at hx
  exact xinv_zero hx.1.1

/-- **What a frame of the four walks gives** (round 34): `SiteX` on each instruction, the block buffers' tiles at each instruction, `XInvR` at each
instruction, the frame's end by `fuelPerFrame`, and the end's place out of `xAt` to `stAt` -/
structure FrameOut (sy : Syms) (nmS : Names) (m0 : Machine) (m : Machine) (i : UInt8) : Prop where
  sites : ∀ j, EraseRange.SiteX (placesR sy nmS m0) (trace m i j)
  tiles : ∀ j, MapIn sy nmS m0 (trace m i j)
  xinv : ∀ j, XInvR sy nmS m0 m i j
  fend : (trace m i fuelPerFrame).frame = m.frame + 1
  pcOut : ¬ ((placesR sy nmS m0).xAt ≤ (frame m i).pc ∧ (frame m i).pc ≤ stAtOf sy m0 (placesR sy nmS m0))
  /-- round 35: the block buffer routine's read is in the block buffers -/
  readIn : ∀ j, ReadTiles.ReadIn (placesR sy nmS m0) (trace m i j)

theorem pcOut_of {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim (envR sy nmS m0) F B m) (h : finX (placesR sy nmS m0) (stR sy nmS m0) B = true) :
    ¬ ((placesR sy nmS m0).xAt ≤ m.pc ∧ m.pc ≤ stAtOf sy m0 (placesR sy nmS m0)) := by
  simp only [finX, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rw [hs.pc]
  intro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1
  · exact h h2

/-- **(ii) with the time at the back jumps: a frame from the control at 0 in a pattern of `L`**: from `RestB` with `sndQ`, `FrameOut`, and the frame ends in the
class of `L` or of `L6`; round 34: the block buffers' tiles and `XInvR` -/
theorem rec_frame2B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 0 L m) (hk : ∀ j, RestB (placesR sy nmS m0) (RoomMap.mapRef m0) (sndQ sy m0) sndDot (trace m i j))
    (hz : m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) (hV : MapIn sy nmS m0 m) :
    FrameOut sy nmS m0 m i ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, w2, _, _⟩ := recB_parts hO
  obtain ⟨hsc, w1'⟩ := walk1B_parts w1
  have hx := walk1B_x w1
  have hh := walk1B_h w1
  obtain ⟨hr0, _, hLS, _⟩ := size_parts hsc
  have w := EraseRange.vok_of_check w2
  have hsz : (refR m0).ram.size = 2048 := ((EraseRange.vok_of_check w1').starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := cond_size (BufferControl.cond0 hm (hv.trans h2.symm)) hr0 hz
  have hm2 := cond_pat s hm1 hsz (hLS s hs1) hs2
  obtain ⟨h1, ⟨B, hf, hs⟩, h3, h4, h5, h6⟩ := ReadTiles.frameVI (R := RestB (placesR sy nmS m0) (RoomMap.mapRef m0) (sndQ sy m0) sndDot)
    (I := MapIn sy nmS m0)
    (J := XInvR sy nmS m0 m i) (EraseRange.covF_splitRom sy m0 _ _) (EraseRange.spent_splitRom sy m0 _) w
    (fun hs hf hc2 hr ht => siteX_of_B hI hs hf (by simp only [chk2X, Bool.and_eq_true] at hc2; exact hc2.1) hh hr ht)
    (mapI_of w.places (fun A hA => by simp only [chk2X, chk2T, Bool.and_eq_true] at hA; exact hA.1.2)) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (refR m0) s, BufferRecords.knownPat (knownS sy nmS) s)) hs1) hm2 hc hk hV
    (xJ_of w hx (fun A hA => by simp only [chk2X, Bool.and_eq_true] at hA; exact hA.2)) xJs_of (xJ0_of hx)
  have h7 : ∀ j, ReadTiles.ReadIn (placesR sy nmS m0) (trace m i j) := fun j => by
    obtain ⟨A, a1, a2, a3⟩ := h6 j
    simp only [chk2X, chk2T, Bool.and_eq_true] at a3
    exact readIn_of_chk a1 a2 a3.1.2
  simp only [finAnd, Bool.and_eq_true] at hf
  exact ⟨⟨h1, h3, h4, h5, pcOut_of hs hf.2, h7⟩, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf.1 hs⟩

/-- **(iii) with the time at the back jumps: a frame from the control at 6 in a pattern of `L6`**: from `RestB` with `sndQ`, `FrameOut` -/
theorem rec_frame3B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 6 L6 m) (hk : ∀ j, RestB (placesR sy nmS m0) (RoomMap.mapRef m0) (sndQ sy m0) sndDot (trace m i j))
    (hz : m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) (hV : MapIn sy nmS m0 m) : FrameOut sy nmS m0 m i := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, _, w1, _, w3, _⟩ := recB_parts hO
  obtain ⟨hsc, w1'⟩ := walk1B_parts w1
  have hx := walk1B_x w1
  have hh := walk1B_h w1
  obtain ⟨_, hr6, _, hL6S⟩ := size_parts hsc
  have w := EraseRange.vok_of_check w3
  have hsz0 : (refR m0).ram.size = 2048 := ((EraseRange.vok_of_check w1').starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := cond_size (r := ref6 nmS m0) (BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv) hr6 hz
  have hsz : (ref6 nmS m0).ram.size = 2048 := by
    show ((refR m0).ram.set! (ctlI nmS) 6).size = 2048
    rw [PipeTransitionAll.ba_size_set, hsz0]
  have hm2 := cond_pat s hm1 hsz (hL6S s hs1) hs2
  obtain ⟨h1, ⟨B, hf, hs⟩, h3, h4, h5, h6⟩ := ReadTiles.frameVI (R := RestB (placesR sy nmS m0) (RoomMap.mapRef m0) (sndQ sy m0) sndDot)
    (I := MapIn sy nmS m0)
    (J := XInvR sy nmS m0 m i) (EraseRange.covF_splitRom sy m0 _ _) (EraseRange.spent_splitRom sy m0 _) w
    (fun hs hf hc2 hr ht => siteX_of_B hI hs hf (by simp only [chk2X, Bool.and_eq_true] at hc2; exact hc2.1) hh hr ht)
    (mapI_of w.places (fun A hA => by simp only [chk2X, chk2T, Bool.and_eq_true] at hA; exact hA.1.2)) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (ref6 nmS m0) s, BufferRecords.knownPat (knownS sy nmS) s)) hs1) hm2 hc hk hV
    (xJ_of w hx (fun A hA => by simp only [chk2X, Bool.and_eq_true] at hA; exact hA.2)) xJs_of (xJ0_of hx)
  have h7 : ∀ j, ReadTiles.ReadIn (placesR sy nmS m0) (trace m i j) := fun j => by
    obtain ⟨A, a1, a2, a3⟩ := h6 j
    simp only [chk2X, chk2T, Bool.and_eq_true] at a3
    exact readIn_of_chk a1 a2 a3.1.2
  exact ⟨h1, h3, h4, h5, pcOut_of hs hf, h7⟩

/-- **(i) with the time at the back jumps: a frame from the control at 0** with nothing known of the buffers: from `RestU` with `scrQ` (no `Late`), `FrameOut`,
and the frame ends in the class of `L` or of `L6` -/
theorem rec_frame1B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 0) (hk : ∀ j, RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace m i j))
    (hz : m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0) (hV : MapIn sy nmS m0 m) :
    FrameOut sy nmS m0 m i ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, _, _, _⟩ := recB_parts hO
  obtain ⟨hsc, w1'⟩ := walk1B_parts w1
  have hx := walk1B_x w1
  have hh := walk1B_h w1
  obtain ⟨hr0, _, _, _⟩ := size_parts hsc
  have w := EraseRange.vok_of_check w1'
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' → EraseRange.FOK A.log m' →
      chk1X (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0) A = true →
      RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' → MapIn sy nmS m0 m' →
      EraseRange.SiteX (placesR sy nmS m0) m' := by
    intro F A m' hs hf hc2 hr ht
    simp only [chk1X, chk1T, chk1R, SiteParts.chk0, Bool.and_eq_true] at hc2
    exact ⟨late_of_time hs hc2.1.1.1.2, SiteParts.reads_of_ok hs hc2.1.1.1.1.2 hr.reads, read_of_chkF hs hf hc2.1.2 hh ht.1 ht.2 hr.headFree,
      erase_of_ok4 hs hc2.1.1.2, SiteParts.off_of_ok hI hs hc2.1.1.1.1.1⟩
  obtain ⟨h1, ⟨B, hf, hs⟩, h3, h4, h5, h6⟩ := ReadTiles.frameVI (R := RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot)
    (I := MapIn sy nmS m0) (J := XInvR sy nmS m0 m i) (EraseRange.covF_splitRom sy m0 _ _) (EraseRange.spent_splitRom sy m0 _) w hQ
    (mapI_of w.places (fun A hA => by simp only [chk1X, chk1T, Bool.and_eq_true] at hA; exact hA.1.2)) (fun hr => hr.lateS)
    (List.mem_singleton_self _) (cond_size (BufferControl.cond0 hm (hv.trans h2.symm)) hr0 hz) hc hk hV
    (xJ_of w hx (fun A hA => by simp only [chk1X, Bool.and_eq_true] at hA; exact hA.2)) xJs_of (xJ0_of hx)
  have h7 : ∀ j, ReadTiles.ReadIn (placesR sy nmS m0) (trace m i j) := fun j => by
    obtain ⟨A, a1, a2, a3⟩ := h6 j
    simp only [chk1X, chk1T, Bool.and_eq_true] at a3
    exact readIn_of_chk a1 a2 a3.1.2
  simp only [finAnd, Bool.and_eq_true] at hf
  exact ⟨⟨h1, h3, h4, h5, pcOut_of hs hf.2, h7⟩, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf.1 hs⟩

/-- **(iv) with the time at the back jumps: a frame from the control at 6** with nothing known of the buffers: from `RestU` with `scrQ` and `Off`, `FrameOut` -/
theorem rec_frame4B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 6) (hk : ∀ j, RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace m i j))
    (ho : ∀ j, SiteParts.Off (placesR sy nmS m0) (trace m i j)) (hz : m.ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0)
    (hV : MapIn sy nmS m0 m) : FrameOut sy nmS m0 m i := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, _, w1, _, _, w4⟩ := recB_parts hO
  obtain ⟨hsc, w1'⟩ := walk1B_parts w1
  have hx := walk1B_x w1
  have hh := walk1B_h w1
  obtain ⟨_, hr6, _, _⟩ := size_parts hsc
  have w := EraseRange.vok_of_check w4
  have hsz0 : (refR m0).ram.size = 2048 := ((EraseRange.vok_of_check w1').starts _ (List.mem_singleton_self _)).1.szR
  have hm1 := cond_size (r := ref6 nmS m0) (BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv) hr6 hz
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' → EraseRange.FOK A.log m' →
      chk4X (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0) A = true →
      (RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' ∧ SiteParts.Off (placesR sy nmS m0) m') →
      MapIn sy nmS m0 m' → EraseRange.SiteX (placesR sy nmS m0) m' := by
    intro F A m' hs hf hc2 hr ht
    simp only [chk4X, chk4T, chk4R, Bool.and_eq_true] at hc2
    exact ⟨late_of_time hs hc2.1.1.1.2, SiteParts.reads_of_ok hs hc2.1.1.1.1 hr.1.reads, read_of_chkF hs hf hc2.1.2 hh ht.1 ht.2 hr.1.headFree,
      erase_of_ok4 hs hc2.1.1.2, hr.2⟩
  obtain ⟨h1, ⟨B, hf, hs⟩, h3, h4, h5, h6⟩ := ReadTiles.frameVI
    (R := fun m' => RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' ∧ SiteParts.Off (placesR sy nmS m0) m')
    (I := MapIn sy nmS m0) (J := XInvR sy nmS m0 m i) (EraseRange.covF_splitRom sy m0 _ _) (EraseRange.spent_splitRom sy m0 _) w hQ
    (mapI_of (chk := chk4X (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0))
      (R := fun m' => RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' ∧ SiteParts.Off (placesR sy nmS m0) m') w.places
      (fun A hA => by simp only [chk4X, chk4T, Bool.and_eq_true] at hA; exact hA.1.2)) (fun hr => hr.1.lateS)
    (List.mem_singleton_self _) hm1 hc (fun j => ⟨hk j, ho j⟩) hV
    (xJ_of (chk := chk4X (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) (RoomMusic.regM sy m0 nmS T) (spR sy nmS m0) (stR sy nmS m0) (rtR sy nmS m0))
      (R := fun m' => RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' ∧ SiteParts.Off (placesR sy nmS m0) m')
      (I := MapIn sy nmS m0) w hx (fun A hA => by simp only [chk4X, Bool.and_eq_true] at hA; exact hA.2)) xJs_of (xJ0_of hx)
  have h7 : ∀ j, ReadTiles.ReadIn (placesR sy nmS m0) (trace m i j) := fun j => by
    obtain ⟨A, a1, a2, a3⟩ := h6 j
    simp only [chk4X, chk4T, Bool.and_eq_true] at a3
    exact readIn_of_chk a1 a2 a3.1.2
  exact ⟨h1, h3, h4, h5, pcOut_of hs hf, h7⟩

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
open BufferRecords (U InPat)
open EntryBuffer (ctlI)
open ScreenPage (placesR envR refR)
variable {sy : Syms} {nm nmS : Names} {d : Data} {m0 : Machine}

/-- **`SiteOK` on every instruction of every frame of the room, with the time from the walks at the loops' back jumps**: as `RoomLate.late_sites_of_rows`, but
no `Late` is asked. On the frames `U` (the room's first frame and the frames after a frame that starts with the control at 6) the back jumps of the screen update's
loop and of the sound routine run at dot `sndDot` or earlier (`LateS scrQ`); on the other frames the back jumps of the sound routine (`LateS sndQ`). Round 34:
of `Read` only the head's half is asked (`ReadTiles.ReadH`): the block buffers hold tiles of the list at the room's first control (`RoomMap.tiles_of_rows`)
and the walks carry it through every instruction of every frame. Round 35: in place of the head's half, the head's cell free in the map (`ReadTiles.HeadFree`;
the walks carry the map's bits too, `ReadTiles.ZeroIn`, `MapIn`), and no `Xbit`: before the entering frame the side pipe's read is not run (`SideRead.no_xAt`),
and on the entering frame `Xbit` comes from the walk of `HeadSide` (its check is part of walk (i), `walk1B_c`). -/
theorem loop_sites_of_rows {V : List (Machine × List Nat)} {T : List StepWrites.SState} {L L6 : List (List (Nat × UInt8))}
    (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d (PipeTransition.entry m0) nmS m0 = true) (hM : RoomMusic.Facts sy m0 nm d V nmS T)
    (hO : recCheckB sy nmS m0 T L L6 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true) (h0 : ScreenPage.Room sy nmS m0 (seq b))
    (rest : ∀ n, b ≤ n → n < a → ∀ j, ReadTiles.HeadFree (placesR sy nmS m0) (RoomMap.mapRef m0) (trace (seq n) (inp n) j))
    (lateU : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, LateS (scrQ sy m0) sndDot (trace (seq n) (inp n) j))
    (lateS : ∀ n, b ≤ n → n < a → ¬ U (ctlI nmS) seq b n → ∀ j, LateS (sndQ sy m0) sndDot (trace (seq n) (inp n) j))
    (reads : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, SiteParts.ReadsAt (SiteParts.ptrS sy m0) (trace (seq n) (inp n) j))
    (off6 : ∀ n, b < n → n < a → (seq n).ram.get! (ctlI nmS) = 6 → (seq (n - 1)).ram.get! (ctlI nmS) = 6 → ∀ j, Off (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    (hkR : SizeKeep.KeepOK sy nmS m0 (SizeKeep.sizeI sy) (SizeKeep.refSize sy m0)) (hk0 : SizeKeep.KeepOK sy nmS m0 (SizeKeep.sizeI sy) 0)
    (hsz : (seq b).ram.get! (SizeKeep.sizeI sy) = SizeKeep.refSize sy m0 ∨ (seq b).ram.get! (SizeKeep.sizeI sy) = 0) :
    ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
  have hr0 : (refR m0).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0 := (size_parts (walk1B_parts (recB_parts hO).2.2.2.2.1).1).1
  have hq : RoomMusic.emq nmS < 2048 := by
    have : RoomMusic.emq nmS ≤ 0x7FF := Nat.and_le_right
    omega
  obtain ⟨hx, ht⟩ := RoomMusic.start_of_invL hq hM.bit hM.start hin hctl
  have hm0 : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq b) := RoomMusic.roomCond_append h0 hx
  have hb0 : (seq b).ram.get! (ctlI nmS) = 0 := (BufferControl.start_ctl hs hin hctl).trans (BufferControl.keep_parts hK).2.1
  have key : ∀ k, b + k ≤ a → (∀ n, b ≤ n → n < b + k → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j)) ∧
      (b + k < a → RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k)) ∧ InCls (RoomMusic.regM sy m0 nmS T) (seq (b + k)) ∧
        (InPat (ctlI nmS) 0 L (seq (b + k)) ∨ InPat (ctlI nmS) 6 L6 (seq (b + k)) ∨ U (ctlI nmS) seq b (b + k)) ∧
        MapIn sy nmS m0 (seq (b + k))) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun n h1 h2 => by omega, fun _ => ⟨hm0, ht, Or.inr (Or.inr (Or.inl rfl)), by rw [Nat.add_zero]; exact ⟨RoomMap.tiles_of_rows hc hin hctl, ReadTiles.zero_of_rows hF hc hin hctl⟩⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨sites, hmk⟩ := ih (by omega)
      obtain ⟨hmc, hcls, hC, hV⟩ := hmk (by omega)
      have hctl06 := BufferControl.ctl_of_rows hF hc hK hs next hin hctl (a := b + k) sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)
      have hR := rest (b + k) (by omega) (by omega)
      -- the size at the frame's start: the frames before keep it (`SizeKeep.byte_all`)
      have hz : (seq (b + k)).ram.get! (SizeKeep.sizeI sy) &&& 0xFE = 0 := by
        rcases hsz with e0 | e0
        · rw [SizeKeep.byte_all hkR next h0 e0 sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)]
          exact hr0
        · rw [SizeKeep.byte_all hk0 next h0 e0 sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)]
          rfl
      have hRS : U (ctlI nmS) seq b (b + k) → ∀ j, RestU (placesR sy nmS m0) (RoomMap.mapRef m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace (seq (b + k)) (inp (b + k)) j) :=
        fun hu j => ⟨reads (b + k) (by omega) (by omega) hu j, hR j, lateU (b + k) (by omega) (by omega) hu j⟩
      have hRT : ¬ U (ctlI nmS) seq b (b + k) → ∀ j, RestB (placesR sy nmS m0) (RoomMap.mapRef m0) (sndQ sy m0) sndDot (trace (seq (b + k)) (inp (b + k)) j) := fun hu j =>
        ⟨lateS (b + k) (by omega) (by omega) hu j, hR j⟩
      -- the frame `b + k`: `FrameOut`, and, if it starts with the control at 0, the class of the next frame; the block buffers' tiles at its end
      have hnow0 : FrameOut sy nmS m0 (seq (b + k)) (inp (b + k)) ∧
          ((seq (b + k)).ram.get! (ctlI nmS) = 0 →
            InPat (ctlI nmS) 0 L (frame (seq (b + k)) (inp (b + k))) ∨ InPat (ctlI nmS) 6 L6 (frame (seq (b + k)) (inp (b + k)))) ∧
          MapIn sy nmS m0 (frame (seq (b + k)) (inp (b + k))) := by
        by_cases hu : U (ctlI nmS) seq b (b + k)
        · rcases hctl06 with h0' | h6
          · obtain ⟨h1, h2⟩ := rec_frame1B hK hO hmc hcls h0' (hRS hu) hz hV
            exact ⟨h1, fun _ => h2, ReadTiles.inv_end h1.tiles⟩
          · -- the frame before started with the control at 6 too
            have hprev : b < b + k ∧ (seq (b + k - 1)).ram.get! (ctlI nmS) = 6 := by
              rcases hu with e | ⟨e1, e2⟩
              · exfalso
                have hk0 : k = 0 := by omega
                rw [hk0, Nat.add_zero, hb0] at h6
                exact absurd h6 (by decide)
              · exact ⟨e1, e2⟩
            have h1 := rec_frame4B hK hO hmc hcls h6 (hRS hu) (off6 (b + k) hprev.1 (by omega) h6 hprev.2) hz hV
            exact ⟨h1, fun h0' => absurd (h6.symm.trans h0') (by decide), ReadTiles.inv_end h1.tiles⟩
        · rcases hC with hp0 | hp6 | hu'
          · obtain ⟨h1, h2⟩ := rec_frame2B hK hO hmc hcls hp0 (hRT hu) hz hV
            exact ⟨h1, fun _ => h2, ReadTiles.inv_end h1.tiles⟩
          · have h1 := rec_frame3B hK hO hmc hcls hp6 (hRT hu) hz hV
            exact ⟨h1, fun h0' => absurd (hp6.1.symm.trans h0') (by decide), ReadTiles.inv_end h1.tiles⟩
          · exact absurd hu' hu
      -- round 34: `Xbit` on the frame: before the entering frame the side pipe's read is not run (the frame ends with the reference's routine)
      have hxb : ∀ j, SiteParts.Xbit (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j) := by
        by_cases hl : b + k + 1 < a
        · have hrt : (frame (seq (b + k)) (inp (b + k))).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI := by
            rw [← next]
            exact stay (b + k + 1) (by omega) hl
          have hno := no_xAt hnow0.1.xinv hnow0.1.fend hnow0.1.pcOut hrt
          exact fun j hpc => absurd hpc (hno j)
        · -- round 35: on the entering frame, from the head's cell free in the map, by the walk of `HeadSide` (its check is part of walk (i))
          have hr0 := (size_parts (walk1B_parts (recB_parts hO).2.2.2.2.1).1).1
          exact HeadSide.xbit_of_check (walk1B_c (recB_parts hO).2.2.2.2.1) (cond_size hmc hr0 hz) hnow0.1.sites (fun j => (hnow0.1.tiles j).2)
            hnow0.1.readIn hR
      have hnow : (∀ j, SiteOK (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j)) ∧
          ((seq (b + k)).ram.get! (ctlI nmS) = 0 →
            InPat (ctlI nmS) 0 L (frame (seq (b + k)) (inp (b + k))) ∨ InPat (ctlI nmS) 6 L6 (frame (seq (b + k)) (inp (b + k)))) ∧
          MapIn sy nmS m0 (frame (seq (b + k)) (inp (b + k))) :=
        ⟨fun j => EraseRange.siteOK_of_X (hnow0.1.sites j) (hxb j), hnow0.2⟩
      refine ⟨fun n h1 h2 => ?_, fun hlt => ?_⟩
      · rcases Nat.lt_or_ge n (b + k) with h3 | h3
        · exact sites n h1 h3
        · have e : n = b + k := by omega
          rw [e]
          exact hnow.1
      · have hstep := RoomPause.pause_step hM.walk hmc hnow.1 hcls
        have e1 : b + (k + 1) = b + k + 1 := rfl
        have hcond : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k + 1)) := by
          rw [next]
          rcases hstep.2 with h3 | ⟨h3, _⟩
          · exact h3
          · exfalso
            apply h3
            rw [← next]
            exact stay (b + k + 1) (by omega) (by omega)
        rw [e1]
        refine ⟨hcond, by rw [next]; exact hstep.1, ?_, by rw [next]; exact hnow.2.2⟩
        rcases hctl06 with h0' | h6
        · rcases hnow.2.1 h0' with h3 | h3
          · left; rw [next]; exact h3
          · right; left; rw [next]; exact h3
        · right; right; right
          have e2 : b + k + 1 - 1 = b + k := by omega
          rw [e2]
          exact ⟨by omega, h6⟩
  intro n h1 h2
  exact (key (n + 1 - b) (by omega)).1 n h1 (by omega)

end

end Smbrta.LoopTime
