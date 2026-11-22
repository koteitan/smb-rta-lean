import Theorems.RoomLate

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
open RoomLate (LateS timeOK late_of_time walkCheckST stok_of_check frameST RestS sndDot fixCuts chkT siteOK_of_T)

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

/-! ## The four walks with the time, on the ROM -/

section
open BufferRecords (InPat Pat patOK starts0 starts6 fin0 noRegs zO zOC fpcOf ptrBytes ref6 cond_pat idx_of_all end0 reads_all)
open EntryBuffer (ctlI)
open ScreenPage (placesR envR refR aidsOf)
variable {sy : Syms} {nmS : Names} {m0 : Machine} {T : List StepWrites.SState}

/-- the check of the walks from buffers that the walk does not know: the reads' but at the screen update's pointer (and the offset's from the control at 0),
and the time's -/
def chk1B (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.chk0 P E Z A && timeOK P A && eraseOK P E A
def chk4B (P : Places) (E : Env) (Z : List UInt8) (A : AS) : Bool := SiteParts.readsOK E Z A && timeOK P A && eraseOK P E A

/-- the check of the walks from the patterns: `RoomLate.chkT` (the offset's, the reads' at every pointer, the time's) and the erase's -/
def chk2B (P : Places) (E : Env) (A : AS) : Bool := chkT P E A && eraseOK P E A

/-- (i) with the time: from the control at 0, nothing known of the buffers -/
def walk1B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (zO sy nm m0)) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) none [] [(refR m0, SiteParts.knownMC nm)]
    (fin0 (ctlI nm) L L6) (chk1B (placesR sy nm m0) (envR sy nm m0) (SiteParts.ptrS sy m0)) (scrQ sy m0) sndDot

/-- (ii) with the time: from the patterns of `L`, the control at 0 -/
def walk2B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (noRegs (zO sy nm m0))) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0)
    (starts0 nm m0 L) (fin0 (ctlI nm) L L6) (chk2B (placesR sy nm m0) (envR sy nm m0)) (sndQ sy m0) sndDot

/-- (iii) with the time: from the patterns of `L6`, the control at 6 -/
def walk3B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) (L6 : List (List (Nat × UInt8))) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (noRegs (zOC sy nm m0))) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) (some (fpcOf sy m0)) (ptrBytes sy m0)
    (starts6 nm m0 L6) (fun _ => true) (chk2B (placesR sy nm m0) (envR sy nm m0)) (sndQ sy m0) sndDot

/-- (iv) with the time: from the control at 6, nothing known of the buffers -/
def walk4B (sy : Syms) (nm : Names) (m0 : Machine) (T : List StepWrites.SState) : Bool :=
  walkCheckST (placesR sy nm m0) (fixCuts m0 (aidsOf sy nm m0)) (envR sy nm m0) (RoomMusic.regM sy m0 nm T) none [] [(ref6 nm m0, SiteParts.knownMC nm)]
    (fun _ => true) (chk4B (placesR sy nm m0) (envR sy nm m0) (SiteParts.ptrS sy m0)) (scrQ sy m0) sndDot

/-- **The check on the ROM**: `BufferRecords.recCheck` with all four walks with the time, clamped only at the loops' back jumps -/
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

/-- what the route asks on each instruction of a frame `U` that the walks (i) and (iv) follow: `Reads` through the pointers `Z`, three parts of `SiteOK`, and
`LateS` -/
structure RestU (P : Places) (Z : List UInt8) (sq : UInt16 → Bool) (D : Nat) (m : Machine) : Prop where
  reads : SiteParts.ReadsAt Z m
  read : SiteParts.Read P m
  erase : EraseEnd P m
  xbit : SiteParts.Xbit P m
  lateS : LateS sq D m

/-- what the route asks on each instruction of a frame that the walks (ii) and (iii) follow: `LateS`, `Read`, `EraseEnd`, `Xbit` -/
structure RestB (P : Places) (sq : UInt16 → Bool) (D : Nat) (m : Machine) : Prop where
  lateS : LateS sq D m
  read : SiteParts.Read P m
  erase : EraseEnd P m
  xbit : SiteParts.Xbit P m

/-- the check of the walks from the patterns gives `SiteOK` from `RestB` -/
theorem siteOK_of_B {sy : Syms} {nmS : Names} {m0 : Machine} {F : Nat × UInt8} {A : AS} {m : Machine} (hI : (ScreenPage.placesR sy nmS m0).offI < 2048)
    (hs : Sim (ScreenPage.envR sy nmS m0) F A m) (hc : chk2B (ScreenPage.placesR sy nmS m0) (ScreenPage.envR sy nmS m0) A = true) {sq : UInt16 → Bool} {D : Nat}
    (hr : RestB (ScreenPage.placesR sy nmS m0) sq D m) : SiteOK (ScreenPage.placesR sy nmS m0) m := by
  simp only [chk2B, chkT, SiteParts.chk0, Bool.and_eq_true] at hc
  exact SiteParts.siteOK_of (late_of_time hs hc.1.2) (BufferRecords.reads_all hs hc.1.1.2) hr.read (erase_of_ok hs hc.2 hr.erase)
    (SiteParts.off_of_ok hI hs hc.1.1.1) hr.xbit

/-- **(ii) with the time at the back jumps: a frame from the control at 0 in a pattern of `L`**: from `RestB` with `sndQ`, `SiteOK` on each instruction, and the
frame ends in the class of `L` or of `L6` -/
theorem rec_frame2B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 0 L m) (hk : ∀ j, RestB (placesR sy nmS m0) (sndQ sy m0) sndDot (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, _, w2, _, _⟩ := recB_parts hO
  have w := stok_of_check w2
  have hsz : (refR m0).ram.size = 2048 := ((stok_of_check (recB_parts hO).2.2.2.2.1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond0 hm (hv.trans h2.symm)
  have hm2 := cond_pat s hm1 hsz (hL s hs1) hs2
  obtain ⟨h1, B, hf, hs⟩ := frameST (R := RestB (placesR sy nmS m0) (sndQ sy m0) sndDot) w (fun hs hc2 hr => siteOK_of_B hI hs hc2 hr) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (refR m0) s, BufferRecords.knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(iii) with the time at the back jumps: a frame from the control at 6 in a pattern of `L6`**: from `RestB` with `sndQ`, `SiteOK` on each instruction -/
theorem rec_frame3B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hp : InPat (ctlI nmS) 6 L6 m) (hk : ∀ j, RestB (placesR sy nmS m0) (sndQ sy m0) sndDot (trace m i j)) :
    ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, hL6, w1, _, w3, _⟩ := recB_parts hO
  have w := stok_of_check w3
  have hsz0 : (refR m0).ram.size = 2048 := ((stok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  obtain ⟨hv, s, hs1, hs2⟩ := hp
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  have hsz : (ref6 nmS m0).ram.size = 2048 := by
    show ((refR m0).ram.set! (ctlI nmS) 6).size = 2048
    rw [PipeTransitionAll.ba_size_set, hsz0]
  have hm2 := cond_pat s hm1 hsz (hL6 s hs1) hs2
  exact (frameST (R := RestB (placesR sy nmS m0) (sndQ sy m0) sndDot) w (fun hs hc2 hr => siteOK_of_B hI hs hc2 hr) (fun hr => hr.lateS)
    (List.mem_map_of_mem (f := fun s => (BufferRecords.refPat (ref6 nmS m0) s, BufferRecords.knownPat (SiteParts.knownMC nmS) s)) hs1) hm2 hc hk).1

/-- **(i) with the time at the back jumps: a frame from the control at 0** with nothing known of the buffers: from `RestU` with `scrQ` (no `Late`), `SiteOK`
on each instruction, and the frame ends in the class of `L` or of `L6` -/
theorem rec_frame1B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 0) (hk : ∀ j, RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace m i j)) :
    (∀ j, SiteOK (placesR sy nmS m0) (trace m i j)) ∧ (InPat (ctlI nmS) 0 L (frame m i) ∨ InPat (ctlI nmS) 6 L6 (frame m i)) := by
  obtain ⟨_, h2, _, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨_, hc6, hL, hL6, w1, _, _, _⟩ := recB_parts hO
  have w := stok_of_check w1
  have hI : (placesR sy nmS m0).offI < 2048 := w.places.offI
  have hQ : ∀ {F : Nat × UInt8} {A : AS} {m' : Machine}, Sim (envR sy nmS m0) F A m' →
      chk1B (placesR sy nmS m0) (envR sy nmS m0) (SiteParts.ptrS sy m0) A = true →
      RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' → SiteOK (placesR sy nmS m0) m' := by
    intro F A m' hs hc2 hr
    simp only [chk1B, SiteParts.chk0, Bool.and_eq_true] at hc2
    exact SiteParts.siteOK_of (late_of_time hs hc2.1.2) (SiteParts.reads_of_ok hs hc2.1.1.2 hr.reads) hr.read (erase_of_ok hs hc2.2 hr.erase)
      (SiteParts.off_of_ok hI hs hc2.1.1.1) hr.xbit
  obtain ⟨h1, B, hf, hs⟩ := frameST (R := RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot) w hQ (fun hr => hr.lateS)
    (List.mem_singleton_self _) (BufferControl.cond0 hm (hv.trans h2.symm)) hc hk
  exact ⟨h1, end0 hc6 (idx_of_all hL) (idx_of_all hL6) hf hs⟩

/-- **(iv) with the time at the back jumps: a frame from the control at 6** with nothing known of the buffers: from `RestU` with `scrQ` and `Off`, `SiteOK`
on each instruction -/
theorem rec_frame4B (hK : BufferControl.keepCheck sy nmS m0 = true) {L L6 : List (List (Nat × UInt8))} (hO : recCheckB sy nmS m0 T L L6 = true)
    {m : Machine} {i : UInt8} (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) m) (hc : InCls (RoomMusic.regM sy m0 nmS T) m)
    (hv : m.ram.get! (ctlI nmS) = 6) (hk : ∀ j, RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace m i j))
    (ho : ∀ j, SiteParts.Off (placesR sy nmS m0) (trace m i j)) : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j) := by
  obtain ⟨_, _, h3, _, _⟩ := BufferControl.keep_parts hK
  obtain ⟨hk1, _, _, _, w1, _, _, w4⟩ := recB_parts hO
  have w := stok_of_check w4
  have hsz0 : (refR m0).ram.size = 2048 := ((stok_of_check w1).starts _ (List.mem_singleton_self _)).1.szR
  have hm1 := BufferControl.cond6 hm hk1 (by rw [hsz0]; exact h3) hv
  refine (frameST (R := fun m' => RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot m' ∧ SiteParts.Off (placesR sy nmS m0) m') w ?_
    (fun hr => hr.1.lateS) (List.mem_singleton_self _) hm1 hc (fun j => ⟨hk j, ho j⟩)).1
  intro F A m' hs hc2 hr
  simp only [chk4B, Bool.and_eq_true] at hc2
  exact SiteParts.siteOK_of (late_of_time hs hc2.1.2) (SiteParts.reads_of_ok hs hc2.1.1 hr.1.reads) hr.1.read (erase_of_ok hs hc2.2 hr.1.erase) hr.2 hr.1.xbit

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
loop and of the sound routine run at dot `sndDot` or earlier (`LateS scrQ`); on the other frames the back jumps of the sound routine (`LateS sndQ`). -/
theorem loop_sites_of_rows {V : List (Machine × List Nat)} {T : List StepWrites.SState} {L L6 : List (List (Nat × UInt8))}
    (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d (PipeTransition.entry m0) nmS m0 = true) (hM : RoomMusic.Facts sy m0 nm d V nmS T)
    (hO : recCheckB sy nmS m0 T L L6 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat}
    (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b)) (hctl : controllable sy (seq b) = true) (h0 : ScreenPage.Room sy nmS m0 (seq b))
    (rest : ∀ n, b ≤ n → n < a → ∀ j, SiteParts.Read (placesR sy nmS m0) (trace (seq n) (inp n) j) ∧ EraseEnd (placesR sy nmS m0) (trace (seq n) (inp n) j) ∧
      SiteParts.Xbit (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (lateU : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, LateS (scrQ sy m0) sndDot (trace (seq n) (inp n) j))
    (lateS : ∀ n, b ≤ n → n < a → ¬ U (ctlI nmS) seq b n → ∀ j, LateS (sndQ sy m0) sndDot (trace (seq n) (inp n) j))
    (reads : ∀ n, b ≤ n → n < a → U (ctlI nmS) seq b n → ∀ j, SiteParts.ReadsAt (SiteParts.ptrS sy m0) (trace (seq n) (inp n) j))
    (off6 : ∀ n, b < n → n < a → (seq n).ram.get! (ctlI nmS) = 6 → (seq (n - 1)).ram.get! (ctlI nmS) = 6 → ∀ j, Off (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI) :
    ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j) := by
  have hq : RoomMusic.emq nmS < 2048 := by
    have : RoomMusic.emq nmS ≤ 0x7FF := Nat.and_le_right
    omega
  obtain ⟨hx, ht⟩ := RoomMusic.start_of_invL hq hM.bit hM.start hin hctl
  have hm0 : RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq b) := RoomMusic.roomCond_append h0 hx
  have hb0 : (seq b).ram.get! (ctlI nmS) = 0 := (BufferControl.start_ctl hs hin hctl).trans (BufferControl.keep_parts hK).2.1
  have key : ∀ k, b + k ≤ a → (∀ n, b ≤ n → n < b + k → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j)) ∧
      (b + k < a → RoomCond (envR sy nmS m0) (refR m0) (RoomMusic.knownM nmS) (seq (b + k)) ∧ InCls (RoomMusic.regM sy m0 nmS T) (seq (b + k)) ∧
        (InPat (ctlI nmS) 0 L (seq (b + k)) ∨ InPat (ctlI nmS) 6 L6 (seq (b + k)) ∨ U (ctlI nmS) seq b (b + k))) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun n h1 h2 => by omega, fun _ => ⟨hm0, ht, Or.inr (Or.inr (Or.inl rfl))⟩⟩
    | succ k ih =>
      intro hk
      obtain ⟨sites, hmk⟩ := ih (by omega)
      obtain ⟨hmc, hcls, hC⟩ := hmk (by omega)
      have hctl06 := BufferControl.ctl_of_rows hF hc hK hs next hin hctl (a := b + k) sites (fun q a1 a2 => stay q a1 (by omega)) (b + k) (by omega) (Nat.le_refl _)
      have hR := rest (b + k) (by omega) (by omega)
      have hRS : U (ctlI nmS) seq b (b + k) → ∀ j, RestU (placesR sy nmS m0) (SiteParts.ptrS sy m0) (scrQ sy m0) sndDot (trace (seq (b + k)) (inp (b + k)) j) :=
        fun hu j => ⟨reads (b + k) (by omega) (by omega) hu j, (hR j).1, (hR j).2.1, (hR j).2.2, lateU (b + k) (by omega) (by omega) hu j⟩
      have hRT : ¬ U (ctlI nmS) seq b (b + k) → ∀ j, RestB (placesR sy nmS m0) (sndQ sy m0) sndDot (trace (seq (b + k)) (inp (b + k)) j) := fun hu j =>
        ⟨lateS (b + k) (by omega) (by omega) hu j, (hR j).1, (hR j).2.1, (hR j).2.2⟩
      -- the frame `b + k`: `SiteOK`, and, if it starts with the control at 0, the class of the next frame
      have hnow : (∀ j, SiteOK (placesR sy nmS m0) (trace (seq (b + k)) (inp (b + k)) j)) ∧
          ((seq (b + k)).ram.get! (ctlI nmS) = 0 →
            InPat (ctlI nmS) 0 L (frame (seq (b + k)) (inp (b + k))) ∨ InPat (ctlI nmS) 6 L6 (frame (seq (b + k)) (inp (b + k)))) := by
        by_cases hu : U (ctlI nmS) seq b (b + k)
        · rcases hctl06 with h0' | h6
          · obtain ⟨h1, h2⟩ := rec_frame1B hK hO hmc hcls h0' (hRS hu)
            exact ⟨h1, fun _ => h2⟩
          · -- the frame before started with the control at 6 too
            have hprev : b < b + k ∧ (seq (b + k - 1)).ram.get! (ctlI nmS) = 6 := by
              rcases hu with e | ⟨e1, e2⟩
              · exfalso
                have hk0 : k = 0 := by omega
                rw [hk0, Nat.add_zero, hb0] at h6
                exact absurd h6 (by decide)
              · exact ⟨e1, e2⟩
            exact ⟨rec_frame4B hK hO hmc hcls h6 (hRS hu) (off6 (b + k) hprev.1 (by omega) h6 hprev.2), fun h0' => absurd (h6.symm.trans h0') (by decide)⟩
        · rcases hC with hp0 | hp6 | hu'
          · obtain ⟨h1, h2⟩ := rec_frame2B hK hO hmc hcls hp0 (hRT hu)
            exact ⟨h1, fun _ => h2⟩
          · exact ⟨rec_frame3B hK hO hmc hcls hp6 (hRT hu), fun h0' => absurd (hp6.1.symm.trans h0') (by decide)⟩
          · exact absurd hu' hu
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
        refine ⟨hcond, by rw [next]; exact hstep.1, ?_⟩
        rcases hctl06 with h0' | h6
        · rcases hnow.2 h0' with h3 | h3
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
