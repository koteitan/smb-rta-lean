import Theorems.EntrySolid
import Std.Tactic.BVDecide

/-!
# The height at the side pipe's entry, for a big player

`EntryHeight` proves the height at the side pipe's entry for a frame that starts with a small player. A big player's walk there had 8 frame ends at one row below
the reference height: the walk forgets where the head was read. Here one more walk of the room's frame proves the height for a big player (the size byte 0).

It is the walk of `EntryHeight` with two more splits and two more kinds of steps.

* Where the collision routine first reads the height: the height, bit by bit from the top, as long as the piece can still hold a value of the band (`band`): the
  row below the reference height, with the depth of a landing. So in the band the height is known before the head is read.
* At the head's call of the block buffer routine, when the height is known and in the band: the horizontal position and the low bit of the page. Then the head's
  cell and the cells of the side reads are known on the same piece.
* At the page's `ADC #0` of the block buffer routine with the carry known to be 0: the accumulator keeps the page (`refineA`).
* At the read of the block buffer routine with the place known, of a byte that is not a coin in the map: the map's byte, by `RoomBlocks.Solid` on that instruction.
  If the byte is not a tile that `SiteOK` allows there (a head read finds only 0 or a coin), the piece has no machine (`stepB`).

The search keeps the position and the page in the key, so that the pieces are not joined again before the collision routine returns; there it forgets them.

So a frame of the room that starts with a big player and ends with the side pipe's routine ends with the reference's height (`height_frameB`, `height_of_rowsB`).

There is no game data in this file. Page: `1-1/d-2-5-4-3-EntryHeightBig.md`.
-/

namespace Smbrta.EntryHeightBig

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS weaken coverS startsR RoomCond MaskOK)
open SideEntryEnd (isV)
open SideEntryRest (notV ne_of_notV)
open EntryHeight (HP preY stepY finY)

/-! ## The walk -/

/-- the places of the walk: those of `EntryHeight`, and the new ones -/
structure HB where
  H : HP
  /-- the player's size -/
  szI : Nat
  /-- the collision routine's first read of the height, and the band: `n` values from `lo` -/
  bandAt : UInt16
  lo : Nat
  n : Nat
  /-- the head's call of the block buffer routine, the horizontal position and the page -/
  headAt : UInt16
  xI : Nat
  pgI : Nat
  /-- the `ADC #0` of the page in the block buffer routine -/
  pageAdc : UInt16
  /-- the map, and its coins -/
  map : Machine
  coins : List UInt8
  deriving Inhabited

/-- some value of the band has the known bits of `b` -/
def meets (lo n : Nat) (b : AB) : Bool := (List.range n).any fun j => ((lo + j).toUInt8 &&& b.k) == (b.v &&& b.k)

/-- the bits of the byte `d` from the list, one after the other, as long as the piece meets the band -/
def band (d lo n : Nat) : List UInt8 → AS → List AS
  | [], A => [A]
  | b :: bs, A => if meets lo n (A.getK d) then (splitBit d b A).flatMap (band d lo n bs) else [A]

/-- the bits from the top -/
def bits : List UInt8 := [128, 64, 32, 16, 8, 4, 2, 1]

/-- the height is known and in the band -/
def inBand (D : HB) (A : AS) : Bool :=
  (A.getK D.H.yI).isK && decide (D.lo ≤ (A.getK D.H.yI).v.toNat) && decide ((A.getK D.H.yI).v.toNat < D.lo + D.n)

/-- the new pieces -/
def zoneB (D : HB) (A : AS) : List AS :=
  if A.pc == D.bandAt then band D.H.yI D.lo D.n bits A
  else if A.pc == D.headAt && inBand D A then (PipeEntryRule.splitAll D.xI A).flatMap (splitBit D.pgI 1)
  else [A]

/-- all the pieces before a step: those of `EntryHeight`, then the new ones -/
def preB (D : HB) (A : AS) : List AS := (preY D.H A).flatMap (zoneB D)

/-- after the page's `ADC #0` with the carry known to be 0, the accumulator is the page -/
def refineA (A B : AS) : AS :=
  if (A.p.and (AB.known 1)).isK && (A.p.and (AB.known 1)).v == 0 then { B with a := A.a } else B

/-- the two bytes of the pointer of an `LDA (zp),Y` -/
def ptrLo (E : Env) (A : AS) : AB := A.getK ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat
def ptrHi (E : Env) (A : AS) : AB := A.getK (((E.prg.get! ((A.pc + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat

/-- the address it reads, and its RAM index -/
def readAd (E : Env) (A : AS) : UInt16 := (((ptrLo E A).v.toUInt16 ||| ((ptrHi E A).v.toUInt16 <<< 8))) + A.y.v.toUInt16
def readI (E : Env) (A : AS) : Nat := (readAd E A &&& 0x7FF).toNat

/-- the read of the block buffer routine with the place known, in the block buffers, of a byte that is not a coin in the map -/
def solidAt (D : HB) (E : Env) (A : AS) : Bool :=
  !A.nmi && A.pc == D.H.P.read && (ptrLo E A).isK && (ptrHi E A).isK && A.y.isK && decide (readAd E A < 0x2000) &&
    decide (D.H.P.bufLo ≤ readI E A) && decide (readI E A < D.H.P.bufLo + D.H.P.bufN) && !D.coins.contains (D.map.ram.get! (readI E A))

/-- a step: at the page's `ADC #0`, the machine's own step, with the page kept; at a read of `solidAt`, the map's byte, if `SiteOK` allows it there (else no
machine); else the step of `EntryHeight` -/
def stepB (D : HB) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == D.pageAdc then (succs E ops A).map (Option.map (refineA A))
  else if solidAt D E A then
    if (ScreenPage.tilesFor D.H.P A).contains (D.map.ram.get! (readI E A)) then [ScreenPage.readStep E (AB.known (D.map.ram.get! (readI E A))) A] else []
  else stepY D.H.P E ops A

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkB (D : HB) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preB D (clampS C.P A)).all fun A₁ => (stepB D C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkB D C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- the key: that of `EntryHeight`, with the horizontal position, the page and the size, and 64 mixed bits below. The queue keeps the low 512 bits of a key, so
these bytes go below that. -/
def keyB (D : HB) (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let K := (EntryHeight.keyY D.H Z E A >>> 64) + ((num (A.getK D.xI) * 65536 + num (A.getK D.pgI)) * 65536 + num (A.getK D.szI)) * (1 <<< 380)
  K * 18446744073709551616 + EntryHeight.mix64 K

/-- what a state forgets: that of `EntryHeight`; at the return of the collision routine also the position and the page, unless the routine is the side pipe's -/
def normB (D : HB) (Z : Aids) (A : AS) : AS :=
  let B := EntryHeight.normY D.H Z A
  if A.pc == Z.colEnd && !isV D.H.ev (B.getK D.H.rtI) then (B.setK D.xI AB.top).setK D.pgI AB.top else B

def optsB (D : HB) (Z : Aids) (E : Env) : EntryHeight.Opts :=
  { key := keyB D Z E, norm := normB D Z, stops := [D.H.footAt, D.H.landAt, D.H.colAt, D.H.tileAt], normAt := [D.H.tileAt] }

partial def runB (D : HB) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preB D (clampS D.H.P cur)).flatMap (stepB D E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !fin B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (O.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc && !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd &&
          !O.stops.contains b.pc && (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := EntryHeight.routeY D.H.P O X b
    break
  return X

partial def searchB (D : HB) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := O.key A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runB D Z O fin E ops X A
  return X

def searchOfB (D : HB) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchB D Z O fin E ops ((startsR r K).foldl (EntryHeight.routeY D.H.P O) {})

/-- the configuration from the table found -/
def cfgOfB (D : HB) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfB D Z O fin E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  -- the accumulator is taken apart first, so that each part is updated in place (projections of a shared tuple copy the array at each push; round 26)
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := D.H.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- the page's `ADC #0` on the ROM -/
def adcOK (E : Env) (pc : UInt16) : Bool :=
  decide (0x8000 ≤ pc) && decide (0x8000 ≤ pc + 1) && E.prg.get! (pc &&& E.mask).toNat == 0x69 && E.prg.get! ((pc + 1) &&& E.mask).toNat == 0

/-- **The check of the walk**, with the condition `fin` on the frame's end -/
def walkCheckB (D : HB) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfB D Z O fin E r K
  ScreenPage.placesOK E D.H.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (D.H.rtI < 2048) && decide (D.H.yI < 2048) && decide (D.H.tileI < 2048) && decide (D.szI < 2048) && decide (D.xI < 2048) && decide (D.pgI < 2048) &&
    adcOK E D.pageAdc && decide (0x8000 ≤ D.H.P.read + 1) &&
    C.t.all (walkB D C ScreenPage.fuelS) && (startsR r K).all (walkB D C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_band {d lo n : Nat} (hd : d < 2048) : ∀ (bs : List UInt8), (∀ b ∈ bs, b ∈ bitList) → Cov E F (band d lo n bs)
  | [], _ => fun A _ hs => ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | b :: bs, hb => by
    intro A m hs
    unfold band
    split
    · exact PipeWrites.cov_then (cov_bit hd (hb b (List.mem_cons_self ..))) (cov_band hd bs (fun c hc => hb c (List.mem_cons_of_mem _ hc))) A m hs
    · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem bits_ok : ∀ b ∈ bits, b ∈ bitList := by decide

/-- the new pieces cover every machine: no hypothesis on the machine -/
theorem cov_zoneB {D : HB} (hy : D.H.yI < 2048) (hx : D.xI < 2048) (hp : D.pgI < 2048) : Cov E F (zoneB D) := by
  intro A m hs
  unfold zoneB
  by_cases h2 : (A.pc == D.bandAt) = true
  · rw [if_pos h2]
    exact cov_band hy bits bits_ok A m hs
  rw [if_neg h2]
  by_cases h3 : (A.pc == D.headAt && inBand D A) = true
  · rw [if_pos h3]
    exact PipeWrites.cov_then (PipeEntryRule.cov_all hx) (cov_bit hp (by decide)) A m hs
  rw [if_neg h3]
  exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preB {D : HB} (hO : PlacesOK E D.H.P) (hy : D.H.yI < 2048) (ht : D.H.tileI < 2048) (hz : D.szI < 2048) (hx : D.xI < 2048) (hp : D.pgI < 2048)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK D.H.P m) : ∃ B ∈ preB D A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := EntryHeight.cov_preY hO hy ht hs hh
  obtain ⟨C, hC, h2, k2⟩ := cov_zoneB hy hx hp B m h1
  exact ⟨C, List.mem_flatMap.2 ⟨B, hB, hC⟩, h2, k2.trans k1⟩

end

/-! ## The new steps -/

set_option maxRecDepth 100000 in
theorem op_69 : opTable[(0x69 : UInt8).toNat]?.getD opJAM = opADC mImm := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- **`ADC #0` with the carry 0 keeps the accumulator** -/
theorem adc0_a {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : 0x8000 ≤ m.pc + 1)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x69) (hv : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = 0) (hc : m.p &&& 1 = 0) :
    (go step m).2.a = m.a := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_69, PipeTransitionAll.go_bind, RoomBlocks.tick_a]
  show (go (mImm >>= fun a => rd a >>= fun v => adc v) { m with pc := m.pc + 1 }).2.a = m.a
  rw [PipeTransitionAll.go_bind]
  show (go (rd (m.pc + 1) >>= fun v => adc v) { m with pc := m.pc + 1 + 1 }).2.a = m.a
  rw [PipeTransitionAll.go_bind, TaintRun.rd_rom _ (by intro h; have := UInt16.le_iff_toNat_le.1 hp1; have := UInt16.lt_iff_toNat_lt.1 h; simp at *; omega) hp1]
  show (m.a.toUInt16 + (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 = m.a
  rw [hv, hc]
  bv_decide

section
variable {E : Env} {F : Nat × UInt8}

/-- the `ADC #0` of the page on the ROM -/
structure AdcOK (E : Env) (q : UInt16) : Prop where
  pc : 0x8000 ≤ q
  pc1 : 0x8000 ≤ q + 1
  op : E.prg.get! (q &&& E.mask).toNat = 0x69
  imm : E.prg.get! ((q + 1) &&& E.mask).toNat = 0

theorem adcOK_spec {pc : UInt16} (h : adcOK E pc = true) : AdcOK E pc := by
  simp only [adcOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **One step of the walk** is sound, if the instruction meets `SiteOK` and the block buffers have the map's bytes (`Solid`) -/
theorem s_stepB {D : HB} {ops : Array (AM Unit)} (hO : PlacesOK E D.H.P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (ha : AdcOK E D.pageAdc)
    (hr1 : 0x8000 ≤ D.H.P.read + 1) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK D.H.P m) (hsol : RoomBlocks.Solid D.H.P D.coins D.map m) :
    ∃ r ∈ stepB D E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepB
  by_cases c1 : (!A.nmi && A.pc == D.pageAdc) = true
  · rw [if_pos c1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c1
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs
    refine ⟨r.map (refineA A), List.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩
    intro B hB'
    cases r with
    | none => cases hB'
    | some B0 =>
      have e : refineA A B0 = B := Option.some.inj hB'
      subst e
      obtain ⟨h1, h2⟩ := hB B0 rfl
      unfold refineA
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        have hcm : (A.p.and (AB.known 1)).mem (m.p &&& 1) := mem_and hs.p (mem_known_self _)
        have hc0 : m.p &&& 1 = 0 := by rw [PipeEntryRule.known_eq hc.1 hcm, hc.2]
        have hn : m.nmiPending = false := by rw [hs.nmi]; exact c1.1
        have hpc : m.pc = D.pageAdc := hs.pc.trans c1.2
        have ea : (go step m).2.a = m.a := by
          apply adc0_a hn hs.halted (by rw [hpc]; exact ha.pc) (by rw [hpc]; exact ha.pc1)
          · rw [hs.prg, hs.mask, hpc]; exact ha.op
          · rw [hs.prg, hs.mask, hpc]; exact ha.imm
          · exact hc0
        refine ⟨{ h1 with a := ?_ }, h2⟩
        show A.a.mem (go step m).2.a
        rw [ea]
        exact hs.a
      · exact ⟨h1, h2⟩
  rw [if_neg c1]
  by_cases c2 : solidAt D E A = true
  · rw [if_pos c2]
    have c2' := c2
    simp only [solidAt, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at c2'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hpc⟩, hlo⟩, hhi⟩, hy⟩, hlt⟩, hb1⟩, hb2⟩, hnc⟩ := c2'
    have hnc' : D.map.ram.get! (readI E A) ∉ D.coins := fun h => by
      rw [List.contains_iff_mem.2 h] at hnc
      cases hnc
    have hpm : m.pc = D.H.P.read := hs.pc.trans hpc
    have hp1 : 0x8000 ≤ m.pc + 1 := by rw [hpm]; exact hr1
    have hra := RoomBlocks.readAddr_eq hp1
    have hz : RoomBlocks.operand m = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hs.pc]
    rw [hz] at hra
    have ey : m.y = A.y.v := PipeEntryRule.known_eq hy hs.y
    have el : m.ram.get! ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat = (ptrLo E A).v :=
      PipeEntryRule.known_eq hlo (hs.ram _ (PipeTransitionAll.mask_lt _))
    have eh : m.ram.get! (((E.prg.get! ((A.pc + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat = (ptrHi E A).v :=
      PipeEntryRule.known_eq hhi (hs.ram _ (PipeTransitionAll.mask_lt _))
    have ead : ScreenPage.readAddr m = readAd E A := by
      rw [hra]
      unfold readAd RoomBlocks.ptrZ
      rw [← ey, ← el, ← eh]
    have hval : ScreenPage.readVal m = D.map.ram.get! (readI E A) := by
      rw [RoomBlocks.readVal_eq (by rw [ead]; exact hlt), ead]
      exact hsol _ hb1 hb2 hnc'
    have hop : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 := by rw [hpc]; exact hO.read.2
    have hpA : 0x8000 ≤ A.pc := by rw [hpc]; exact hO.read.1
    by_cases c3 : (ScreenPage.tilesFor D.H.P A).contains (D.map.ram.get! (readI E A)) = true
    · rw [if_pos c3]
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      have hm : 0x8000 ≤ m.pc := by rw [hs.pc]; exact hpA
      have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
      exact ScreenPage.s_readStep hs hn hpA hop (hh.reads hm hop2) (by rw [hval]; exact mem_known_self _) hB
    · exfalso
      obtain ⟨t1, t2⟩ := hh.read hpm
      have hm := ScreenPage.mem_tilesFor hO hs t1 t2
      rw [hval] at hm
      exact c3 (List.contains_iff_mem.2 hm)
  rw [if_neg c2]
  exact EntryHeight.s_stepY hO hops hT hs hh

end

/-! ## The walk covers the machine -/

section
variable {D : HB} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveB (D : HB) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkB D C n A = true

theorem cover_liveB (ht : C.t.all (walkB D C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ A, LiveB D C F A m ∧ A.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i A e
    have hle : B.le A = true := h2
    have hk : A.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨A, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

/-- what the walk needs of the places -/
structure PlB (D : HB) (C : CfgS) : Prop where
  places : PlacesOK C.E C.P
  pl : C.P = D.H.P
  yI : D.H.yI < 2048
  tileI : D.H.tileI < 2048
  szI : D.szI < 2048
  xI : D.xI < 2048
  pgI : D.pgI < 2048
  adc : AdcOK C.E D.pageAdc
  read1 : 0x8000 ≤ D.H.P.read + 1
  ops : C.ops = (aRows C.E).toArray

/-- **One step of the walk**: the next machine is covered by a live state in the same frame, or the frame ends in a state that `fin` accepts -/
theorem live_stepB (hQ : PlB D C) (ht : C.t.all (walkB D C Fu) = true) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveB D C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) (hsol : RoomBlocks.Solid D.H.P D.coins D.map m) :
    (∃ A', LiveB D C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  have hO := hQ.places
  cases n with
  | zero => simp [walkB] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK D.H.P m := by rw [← hQ.pl]; exact hh
    have hOS : PlacesOK C.E D.H.P := by rw [← hQ.pl]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preB hOS hQ.yI hQ.tileI hQ.szI hQ.xI hQ.pgI hs0 hhS
    obtain ⟨r, hr, hB⟩ := s_stepB hOS hQ.ops hT hQ.adc hQ.read1 hs1 hhS hsol
    simp only [walkB, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    have hkA : A₁.k = A.k := by rw [hk1, ScreenPage.clamp_k]
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hkA] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        have hN : Sim C.E F (weaken C B) (go step m).2 ∧ (weaken C B).k = B.k := by
          unfold weaken
          split
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            have h5 := sim_le hc.2 h1
            refine ⟨h5, ?_⟩
            have hle := hc.2
            simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
            exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
          · exact ⟨h1, rfl⟩
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D', hD, hk⟩ := cover_liveB ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D', hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `A₀` that succeeds covers the frame of every machine of `A₀`, for every input, if each instruction meets `SiteOK` and each
instruction of the frame has the map's bytes in the block buffers. -/
theorem frame_of_walkB (hQ : PlB D C) (ht : C.t.all (walkB D C Fu) = true) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkB D C Fu A₀ = true) (hs : Sim C.E F A₀ m) (hk : ∀ j, SiteOK C.P (trace m i j))
    (hsol : ∀ j, (trace m i j).frame = m.frame → RoomBlocks.Solid D.H.P D.coins D.map (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveB D C F A (trace m i j) ∧ A.k = A₀.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨A₀, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepB hQ ht hT h1 (hk j) hh2 (hsol j h3) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  rw [frame_trace]
  rcases key fuelPerFrame with ⟨A, h1, _, _, h4⟩ | ⟨h1, B, h2, h3, h4⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    omega
  · exact ⟨h1, B, h2, h3, h4⟩

end

/-! ## The frame -/

/-- what the check says -/
structure WalkOKB (D : HB) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  pq : PlB D C
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  fin : C.fin = fin
  rt : D.H.rtI < 2048
  table : C.t.all (walkB D C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkB D C ScreenPage.fuelS A = true

theorem walkOKB_of_check {D : HB} {Z : Aids} {O : EntryHeight.Opts} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckB D Z O fin E r K = true) : WalkOKB D fin E r K (cfgOfB D Z O fin E r K) := by
  simp only [walkCheckB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨⟨ScreenPage.placesOK_spec h1, rfl, h5, h6, h7, h8, h9, adcOK_spec h10, h11, rfl⟩, hp, ScreenPage.maskOK_spec h3, rfl, rfl, h4, h12, h13⟩

/-- **The end of a frame of the room.** A frame that starts in the room's condition with the bits `K`, with `SiteOK` and the map's bytes on each instruction, ends in
a machine that a state accepted by `fin` covers. -/
theorem frame_endB {D : HB} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKB D fin E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK D.H.P (trace m i j))
    (hsol : ∀ j, (trace m i j).frame = m.frame → RoomBlocks.Solid D.H.P D.coins D.map (trace m i j)) :
    ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  obtain ⟨_, B, h2, _, h4⟩ := frame_of_walkB (i := i) h.pq h.table (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) hw hs'
    (by rw [h.pq.pl]; exact hk) hsol
  rw [h.fin] at h2
  rw [h.env] at h4
  exact ⟨B, h2, h4⟩

/-- **The height at the end of the entering frame.** A frame that starts in the room's condition, with `SiteOK` and the map's bytes on each instruction: if it ends
with the side pipe's routine, it ends with the reference's height. -/
theorem height_frameB {D : HB} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKB D (finY D.H) E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, SiteOK D.H.P (trace m i j))
    (hsol : ∀ j, (trace m i j).frame = m.frame → RoomBlocks.Solid D.H.P D.coins D.map (trace m i j)) (hrt : (frame m i).ram.get! D.H.rtI = D.H.ev) :
    (frame m i).ram.get! D.H.yI = D.H.yv := by
  obtain ⟨B, h2, h4⟩ := frame_endB h hm hk hsol
  simp only [finY, Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hrt (ne_of_notV h2 (h4.ram _ h.rt))
  · simp only [isV, Bool.and_eq_true, beq_iff_eq] at h2
    rw [PipeEntryRule.known_eq h2.1 (h4.ram _ h.pq.yI), h2.2]

/-! ## On the ROM -/

section
open ScreenPage (placesR envR refR)
open PipeEntryRule (findOp)

/-- the places, from the symbols and the ROM. The head's call is the entry of the block buffer routine for the head, 7 bytes before the routine itself; the band is
the row below the reference height, as deep as a landing goes (`LandDepth`). -/
def hbOf (sy : Syms) (nm : Names) (m0 : Machine) : HB :=
  let H := EntryHeight.hpOf sy nm m0
  { H := H
    szI := EntryHeight.sizeI sy
    bandAt := ScreenPage.findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_Position.toUInt8 64
    lo := (H.yv + 16).toNat
    n := sy.LandDepth.toNat
    headAt := sy.BlockBufferCollision - 7
    xI := (sy.Player_X_Position &&& 0x7FF).toNat
    pgI := (sy.Player_PageLoc &&& 0x7FF).toNat
    pageAdc := findOp m0 sy.BlockBufferCollision 0x69 32
    map := RoomMap.mapRef m0
    coins := RoomBlocks.coinsOf (placesR sy nm m0) }

theorem hbOf_H (sy : Syms) (nm : Names) (m0 : Machine) : (hbOf sy nm m0).H = EntryHeight.hpOf sy nm m0 := by dsimp only [hbOf]
theorem hbOf_coins (sy : Syms) (nm : Names) (m0 : Machine) : (hbOf sy nm m0).coins = RoomBlocks.coinsOf (placesR sy nm m0) := by dsimp only [hbOf]
theorem hbOf_map (sy : Syms) (nm : Names) (m0 : Machine) : (hbOf sy nm m0).map = RoomMap.mapRef m0 := by dsimp only [hbOf]
theorem hpOf_P (sy : Syms) (nm : Names) (m0 : Machine) : (EntryHeight.hpOf sy nm m0).P = placesR sy nm m0 := by dsimp only [EntryHeight.hpOf]

/-- the reference machine of the walk: the room's, with 0 (big) in the byte of the player's size. `knownT` does not list that byte (`checkB` checks it), so the
room's condition with `knownT` is the same for both (`cond_ref`); the walk knows the size from `EntryHeight.knownY`. -/
def refB (sy : Syms) (m0 : Machine) : Machine := { refR m0 with ram := (refR m0).ram.set! (EntryHeight.sizeI sy) 0 }

/-- **The check on the ROM**: the walk from the room's condition with the map's bits and a big player (`EntryHeight.knownY` with `refB`) -/
def checkB (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let D := hbOf sy nm m0
  let Z := EntryHeight.aidsY sy nm m0
  (RoomMap.knownT sy nm m0).all (fun p => p.1 != EntryHeight.sizeI sy) &&
    walkCheckB D Z (optsB D Z (envR sy nm m0)) (finY D.H) (envR sy nm m0) (refB sy m0) (EntryHeight.knownY sy nm m0)

/-- the room's condition does not look at a byte that `K` does not list -/
theorem cond_ref {E : Env} {r m : Machine} {K : List (Nat × UInt8)} {i : Nat} (hm : RoomCond E r K m) (hK : K.all (fun p => p.1 != i) = true) :
    RoomCond E { r with ram := r.ram.set! i 0 } K m := by
  refine { hm with bytes := ?_ }
  intro p hp
  have hne : i ≠ p.1 := by
    have h := List.all_eq_true.1 hK p hp
    simp only [bne_iff_ne, ne_eq] at h
    exact fun e => h e.symm
  show m.ram.get! p.1 &&& p.2 = (r.ram.set! i 0).get! p.1 &&& p.2
  rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ hne]
  exact hm.bytes p hp

/-- what the checks give: those of `EntryHeight` (the walk with the reference's size, the references' height), this walk, and the checks of `RoomBlocks` (the
map's bytes on each instruction of the room) -/
structure Facts (sy : Syms) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nmS : Names) (m0 : Machine) (V : List (Machine × List Nat)) : Prop
    extends EntryHeight.Facts sy nmS m0 V where
  big : checkB sy nmS m0 = true
  blocks : RoomBlocks.BChecks sy nmS m0
  rows : ∃ v0, RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 v0 = true

theorem factsOf {sy : Syms} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nmS : Names} {m0 : Machine} {V : List (Machine × List Nat)} {v0 : List Jump.VS}
    (h0 : EntryHeight.Facts sy nmS m0 V) (h2 : checkB sy nmS m0 = true) (h3 : RoomBlocks.BChecks sy nmS m0)
    (h4 : RoomBlocks.rowsCheckR sy nm₁ d₁ nmS m0 v0 = true) : Facts sy nm₁ d₁ nmS m0 V :=
  { h0 with big := h2, blocks := h3, rows := ⟨v0, h4⟩ }

end

/-! ## The entering frame of the room -/

section
open ScreenPage (placesR envR refR)
open PipeChangeEnd (Data InRowsT)

variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **The height at the end of the entering frame, on the real machines, for a big player.** A frame `k` of the room (from `b` to `a`, under the conditions of
`RoomMap.map_of_rows`) that starts with the player's size 0 (big) and ends with the side pipe's routine ends with the height of the reference entry. The map's bytes on each instruction come from
`RoomBlocks.blocks_run_trace`. `hF`, `hc`, `hH`, `hW`, `hR` are checks on the ROM. -/
theorem height_of_rowsB (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d (PipeTransition.entry m0) nmS m0 = true) (hH : checkB sy nmS m0 = true)
    (hW : RoomBlocks.BChecks sy nmS m0) {v0 : List Jump.VS} (hR : RoomBlocks.rowsCheckR sy nm d nmS m0 v0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d (PipeTransition.entry m0) (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {k : Nat} (h1 : b ≤ k) (h2 : k < a) (hsz : (seq k).ram.get! (EntryHeight.sizeI sy) = 0)
    (hrt : (frame (seq k) (inp k)).ram.get! (placesR sy nmS m0).rtI = (placesR sy nmS m0).eng) :
    (frame (seq k) (inp k)).ram.get! (EntryHeight.heightI sy) = (SideTransition.entry m0).ram.get! (EntryHeight.heightI sy) := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay k h1 h2
  have hsol := RoomBlocks.blocks_run_trace hW hR hF hc next hin hctl sites stay k h1 h2
  simp only [RoomBlocks.SolidR] at hsol
  rw [← hbOf_coins, ← hbOf_map, ← hpOf_P, ← hbOf_H] at hsol
  simp only [checkB, Bool.and_eq_true] at hH
  have hw := walkOKB_of_check hH.2
  have hsr : ((refR m0).ram.set! (EntryHeight.sizeI sy) 0).size = 2048 := hw.mask.szR
  rw [PipeTransitionAll.ba_size_set] at hsr
  have hcond0 := cond_ref hcond hH.1
  have hcond' : RoomCond (envR sy nmS m0) (refB sy m0) (EntryHeight.knownY sy nmS m0) (seq k) :=
    RoomMusic.roomCond_append hcond0 (fun p hp => by
      have e1 : p = (EntryHeight.sizeI sy, (0xFF : UInt8)) := List.mem_singleton.1 hp
      rw [e1]
      show (seq k).ram.get! (EntryHeight.sizeI sy) &&& 0xFF = ((refR m0).ram.set! (EntryHeight.sizeI sy) 0).get! (EntryHeight.sizeI sy) &&& 0xFF
      rw [hsz, PipeTransitionAll.ba_get_set_self _ _ _ (by rw [hsr]; exact PipeTransitionAll.mask_lt _)])
  have hk := sites k h1 h2
  rw [← hpOf_P, ← hbOf_H] at hk hrt
  exact height_frameB hw hcond' hk hsol hrt

end

end Smbrta.EntryHeightBig
