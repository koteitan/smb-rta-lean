import Theorems.EntryHeightBig
import Theorems.ReadTiles
import Theorems.SizeKeep

/-!
# The side pipe's read of the position on the entering frame, from the head's cell (round 35)

`SiteOK.xbit` asks that the position's low bits are not 0 where the side pipe's code reads the position (`xAt`). In round 34 the route asked it only on the
room's entering frame (the field `roomXbit`). Here one more walk of a frame of the room proves it on any frame of the room, from the field `roomRead` (the
head's cell is free in the map, `ReadTiles.HeadFree`) and from facts that the room's walks prove on each instruction (`SiteX`, the map's bits
`ReadTiles.ZeroIn`, the read in the block buffers `ReadTiles.ReadIn`). The field `roomXbit` is gone (round 35).

The side pipe's code runs only after a side read that finds the side pipe's tile. The collision routine reads the cell of the head before it reads the cells of
the sides, with the same position. A position with the low bits 0 puts the head and the side in the same column, and there the head's cell is a cell of the pipe.

The walk is that of `ScreenPage` with more pieces and steps:

* at the collision routine's entry (`splitAt`): the position's low bits, one after the other up to the first 1 (`lowBits`); with the four low bits 0 also its
  high bits and the page's low bit (`highX`); for the one position whose head and sides are read in the side pipe's column (the column times 16, page 0) also
  the height (its four high bits, and its values in the two rows of the reference entry's height and below, `yPieces`) and the low bit of the player's size;
* at the routine's read of the player's state, for that position: the state, bit by bit up to the first 1, so that a state that is not 0 stays known not to be 0;
* at the page's `ADC #0` of the block buffer routine with the carry 0: the accumulator keeps the page (`EntryHeightBig.refineA`);
* at the row's `SBC #` of the block buffer routine, with the carry 1 and an operand with the low bits 0: the accumulator keeps its low four bits (`refineS`,
  `sbc_low`), so the read's `Y` keeps the row's low bits 0;
* at the block buffer routine's read with the pointer known and at most 16 values of `Y` (`candRead`): the tiles of the list that a byte of the block buffers at
  one of the addresses may hold, by the map's bits, and for the head only where the map's byte is a head tile (`HeadFree`, `stepX`);
* at every state the walk asks that a state at `xAt` knows a set low bit of the position (`xbitOK`).

So each instruction of the frame meets `Xbit` (`xbit_frame`).

There is no game data in this file. Page: `1-1/d-2-4-2-11-HeadSide.md`.
-/

namespace Smbrta.HeadSide

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS weaken coverS startsR RoomCond MaskOK)
open EntryHeightBig (ptrLo ptrHi refineA AdcOK adcOK adcOK_spec)

/-! ## The walk -/

/-- the places of the walk -/
structure XD where
  /-- the room's places, of `ScreenPage` -/
  P : Places
  /-- the map -/
  M : Machine
  /-- the collision routine's entry: the position, the page's low bit, and for one position the height and the size's low bit, are split there -/
  splitAt : UInt16
  xI : Nat
  pgI : Nat
  yI : Nat
  /-- the player's size: for the position `xv` its low bit is split too, so that the head's check knows its bound -/
  szI : Nat
  /-- the rows of the height (its high four bits) where the height is split into its values: `yr` and the next one -/
  yr : UInt8
  /-- the position whose head and sides are read in the side pipe's column: there the height is split too -/
  xv : UInt8
  /-- the `ADC #0` of the page, and the `SBC #` of the row, in the block buffer routine -/
  pageAdc : UInt16
  rowSbc : UInt16
  /-- the collision routine's read of the player's state: for the position `xv` the state is split there bit by bit, so that a state that is not 0 is known not
  to be 0 -/
  stRead : UInt16
  /-- the places where the side check ends (for the search only: there it forgets the position) -/
  exits : List UInt16
  deriving Inhabited

/-- the low bits of the byte `d`, one after the other, as long as they are known to be 0 -/
def lowBits (d : Nat) : List UInt8 → AS → List AS
  | [], A => [A]
  | b :: bs, A => (splitBit d b A).flatMap fun B => if (B.getK d).bit b == some false then lowBits d bs B else [B]

/-- the bits of the byte `d` from the list, one after the other -/
def splitBits (d : Nat) : List UInt8 → AS → List AS
  | [], A => [A]
  | b :: bs, A => (splitBit d b A).flatMap (splitBits d bs)

/-- the pieces of the height for the position `xv`: its four high bits, and in the rows `yr` and `yr + 1` its values -/
def yPieces (D : XD) (C : AS) : List AS :=
  (splitBits D.yI [128, 64, 32, 16] C).flatMap fun B =>
    if (B.getK D.yI).k &&& 0xF0 == 0xF0 && ((B.getK D.yI).v >>> (4 : UInt8) == D.yr || (B.getK D.yI).v >>> (4 : UInt8) == D.yr + (1 : UInt8)) then
      PipeEntryRule.splitAll D.yI B
    else [B]

/-- the four low bits of the byte are known to be 0 -/
def low0 (b : AB) : Bool := b.k &&& 0x0F == 0x0F && b.v &&& 0x0F == 0

/-- the pieces of a position with the four low bits 0: its high bits, the page's low bit, and for the position `xv` on the page's low bit 0 the height -/
def highX (D : XD) (B : AS) : List AS :=
  if low0 (B.getK D.xI) then
    ((PipeEntryRule.splitAll D.xI B).flatMap (splitBit D.pgI 1)).flatMap fun C =>
      if (C.getK D.xI).isK && (C.getK D.xI).v == D.xv && (C.getK D.pgI).bit 1 == some false then
        (yPieces D C).flatMap (splitBit D.szI 1)
      else [C]
  else [B]

/-- the new pieces: at `splitAt` the position's low bits up to the first 1 (`lowBits`), and with the four low bits 0 the rest (`highX`) -/
def zoneX (D : XD) (A : AS) : List AS :=
  if A.pc == D.splitAt then (lowBits D.xI [1, 2, 4, 8] A).flatMap (highX D)
  else if A.pc == D.stRead && (A.getK D.xI).isK && (A.getK D.xI).v == D.xv && (A.getK D.pgI).bit 1 == some false then
    lowBits D.P.stI [1, 2, 4, 8, 16, 32, 64, 128] A
  else [A]

/-- all the pieces before a step: those of `ScreenPage` (by `SiteOK`), then the new ones -/
def preX (D : XD) (A : AS) : List AS := (ScreenPage.preS D.P A).flatMap (zoneX D)

/-- after the row's `SBC #` with the carry known to be 1, the accumulator keeps its four low bits, if they are known and the step does not know them (the
abstract `SBC` knows a result only when every bit is known) -/
def refineS (A B : AS) : AS :=
  if (A.p.and (AB.known 1)).isK && (A.p.and (AB.known 1)).v == 1 && A.a.k &&& 0x0F == 0x0F && B.a.k &&& 0x0F != 0x0F then
    { B with a := ⟨A.a.v &&& 0x0F, 0x0F⟩ }
  else B

/-- the values of a byte with the known bits of `b` -/
def vals (b : AB) : List UInt8 := (List.range 256).filterMap fun v => if v.toUInt8 &&& b.k == b.v &&& b.k then some v.toUInt8 else none

/-- the pointer of an `LDA (zp),Y`, from its two known bytes -/
def ptrOf (E : Env) (A : AS) : UInt16 := (ptrLo E A).v.toUInt16 ||| ((ptrHi E A).v.toUInt16 <<< 8)

/-- the addresses that the read may read: the pointer plus a value of `Y` -/
def candAds (E : Env) (A : AS) : List UInt16 := (vals A.y).map fun u => ptrOf E A + u.toUInt16

/-- the offset of the block buffer routine is known and one of the head's -/
def headK (P : Places) (A : AS) : Bool := (A.getK P.saveI).isK && P.heads.contains (A.getK P.saveI).v

/-- a byte of the block buffers at `ad` may hold the tile `v`: `v` has no bit that the map's byte has not, and for a head read the map's byte is a head tile -/
def okAt (D : XD) (A : AS) (ad : UInt16) (v : UInt8) : Bool :=
  decide (ad < 0x2000) && ReadTiles.inBuf D.P (ad &&& 0x7FF).toNat && v &&& ~~~ D.M.ram.get! (ad &&& 0x7FF).toNat == 0 &&
    (!headK D.P A || D.P.headTiles.contains (D.M.ram.get! (ad &&& 0x7FF).toNat))

/-- the block buffer routine's read with the pointer known and at most 16 values of `Y` -/
def candRead (D : XD) (E : Env) (A : AS) : Bool :=
  !A.nmi && A.pc == D.P.read && (ptrLo E A).isK && (ptrHi E A).isK && decide ((vals A.y).length ≤ 16)

/-- a step: at the page's `ADC #0` and at the row's `SBC #`, the machine's own step, with the page or the low bits kept; at a read of `candRead`, each tile that
some address allows (no tile: no machine); else the step of `ScreenPage` -/
def stepX (D : XD) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == D.pageAdc then (succs E ops A).map (Option.map (refineA A))
  else if !A.nmi && A.pc == D.rowSbc then (succs E ops A).map (Option.map (refineS A))
  else if candRead D E A then
    ((ScreenPage.tilesFor D.P A).filter fun v => (candAds E A).any fun ad => okAt D A ad v).map fun v => ScreenPage.readStep E (AB.known v) A
  else ScreenPage.stepS D.P E ops A

/-- **The state's check**: at the side pipe's read of the position, a low bit of the position is known to be 1 -/
def xbitOK (P : Places) (A : AS) : Bool := A.pc != P.xAt || (A.getK P.xI).k &&& (A.getK P.xI).v &&& 0x0F != 0

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts; each state meets `xbitOK` -/
def walkX (D : XD) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => xbitOK D.P A && (preX D (clampS C.P A)).all fun A₁ => (stepX D C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkX D C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- the key: that of the room's search, with the position, the page, the height, the player's state and the size, and 64 mixed bits below (the queue keeps
the low 512 bits of a key) -/
def keyX (D : XD) (Z : Aids) (E : Env) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let K := Z.key E A + ((((num (A.getK D.xI) * 65536 + num (A.getK D.pgI)) * 65536 + num (A.getK D.yI)) * 65536 + num (A.getK D.P.stI)) * 65536 +
    num (A.getK D.szI)) * (1 <<< 300)
  K * 18446744073709551616 + EntryHeight.mix64 K

/-- what a state forgets: that of the room's search while the position is not known; while it is known (in the collision routine) nothing, and at the
routine's return the position, the page and the height too -/
def normX (D : XD) (Z : Aids) (A : AS) : AS :=
  if (A.getK D.xI).isK then
    if A.pc == Z.colEnd then ((Z.norm A).setK D.xI AB.top |>.setK D.pgI AB.top).setK D.yI AB.top
    else if D.exits.contains A.pc then ((A.setK D.xI AB.top).setK D.pgI AB.top).setK D.yI AB.top
    else A
  else Z.norm A

def optsX (D : XD) (Z : Aids) (E : Env) : EntryHeight.Opts :=
  { key := keyX D Z E, norm := normX D Z, stops := [D.splitAt, D.stRead, D.pageAdc, D.rowSbc, D.P.read] ++ D.exits, normAt := D.exits }

partial def runX (D : XD) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := if xbitOK D.P cur then (preX D (clampS D.P cur)).flatMap (stepX D E ops) else [none]
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !fin B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 256 && (O.norm b).pc == b.pc && !Z.cutAY.contains b.pc && !Z.cutX.contains b.pc &&
          !Z.regs.contains b.pc && !Z.ends.contains b.pc && b.pc != Z.colEnd && !O.stops.contains b.pc &&
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
        X := EntryHeight.routeY D.P O X b
    break
  return X

partial def searchX (D : XD) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := O.key A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runX D Z O fin E ops X A
  return X

def searchOfX (D : XD) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchX D Z O fin E ops ((startsR r K).foldl (EntryHeight.routeY D.P O) {})

/-- the configuration from the table found -/
def cfgOfX (D : XD) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfX D Z O fin E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      match acc with
      | (arr, hm, ba) =>
        let i := arr.size
        let l := hm.getD e.1 []
        (arr.push e.2, hm.insert e.1 (i :: l), ba.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := D.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- the row's `SBC #` on the ROM: its operand has the low four bits 0 -/
def sbcOK (E : Env) (pc : UInt16) : Bool :=
  decide (0x8000 ≤ pc) && decide (0x8000 ≤ pc + 1) && E.prg.get! (pc &&& E.mask).toNat == 0xE9 && E.prg.get! ((pc + 1) &&& E.mask).toNat &&& 0x0F == 0

/-- **The check of the walk**, with the condition `fin` on the frame's end -/
def walkCheckX (D : XD) (Z : Aids) (O : EntryHeight.Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfX D Z O fin E r K
  ScreenPage.placesOK E D.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (D.xI < 2048) && decide (D.pgI < 2048) && decide (D.yI < 2048) && decide (D.szI < 2048) && adcOK E D.pageAdc && sbcOK E D.rowSbc && decide (0x8000 ≤ D.P.read + 1) &&
    C.t.all (walkX D C ScreenPage.fuelS) && (startsR r K).all (walkX D C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_splitBits {d : Nat} (hd : d < 2048) : ∀ (bs : List UInt8), (∀ b ∈ bs, b ∈ bitList) → Cov E F (splitBits d bs)
  | [], _ => fun A _ hs => ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | b :: bs, hb => by
    intro A m hs
    unfold splitBits
    exact PipeWrites.cov_then (cov_bit hd (hb b (List.mem_cons_self ..))) (cov_splitBits hd bs (fun c hc => hb c (List.mem_cons_of_mem _ hc))) A m hs

theorem cov_yPieces {D : XD} (hy : D.yI < 2048) : Cov E F (yPieces D) := by
  intro A m hs
  unfold yPieces
  refine PipeWrites.cov_then (cov_splitBits hy [128, 64, 32, 16] (by decide)) ?_ A m hs
  intro B m' hs'
  dsimp only
  split
  · exact PipeEntryRule.cov_all hy B m' hs'
  · exact ⟨B, List.mem_singleton.2 rfl, hs', rfl⟩

/-- the split of the height and the size's low bit for the one position covers every machine -/
theorem cov_condY {D : XD} (hy : D.yI < 2048) (hz : D.szI < 2048) :
    Cov E F (fun B => if (B.getK D.xI).isK && (B.getK D.xI).v == D.xv && (B.getK D.pgI).bit 1 == some false then
      (yPieces D B).flatMap (splitBit D.szI 1) else [B]) := by
  intro A m hs
  dsimp only
  split
  · exact PipeWrites.cov_then (cov_yPieces hy) (cov_bit hz (by decide)) A m hs
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_lowBits {d : Nat} (hd : d < 2048) : ∀ (bs : List UInt8), (∀ b ∈ bs, b ∈ bitList) → Cov E F (lowBits d bs)
  | [], _ => fun A _ hs => ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | b :: bs, hb => by
    intro A m hs
    unfold lowBits
    refine PipeWrites.cov_then (cov_bit hd (hb b (List.mem_cons_self ..))) ?_ A m hs
    intro B m' hs'
    dsimp only
    split
    · exact cov_lowBits hd bs (fun c hc => hb c (List.mem_cons_of_mem _ hc)) B m' hs'
    · exact ⟨B, List.mem_singleton.2 rfl, hs', rfl⟩

theorem cov_highX {D : XD} (hx : D.xI < 2048) (hp : D.pgI < 2048) (hy : D.yI < 2048) (hz : D.szI < 2048) : Cov E F (highX D) := by
  intro A m hs
  unfold highX
  split
  · exact PipeWrites.cov_then (PipeWrites.cov_then (PipeEntryRule.cov_all hx) (cov_bit hp (by decide))) (cov_condY hy hz) A m hs
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- the new pieces cover every machine: no hypothesis on the machine -/
theorem cov_zoneX {D : XD} (hx : D.xI < 2048) (hp : D.pgI < 2048) (hy : D.yI < 2048) (hz : D.szI < 2048) (hst : D.P.stI < 2048) :
    Cov E F (zoneX D) := by
  intro A m hs
  unfold zoneX
  split
  · exact PipeWrites.cov_then (cov_lowBits hx [1, 2, 4, 8] (by decide)) (cov_highX hx hp hy hz) A m hs
  · split
    · exact cov_lowBits hst [1, 2, 4, 8, 16, 32, 64, 128] (by decide) A m hs
    · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preX {D : XD} (hO : PlacesOK E D.P) (hx : D.xI < 2048) (hp : D.pgI < 2048) (hy : D.yI < 2048) (hz : D.szI < 2048) {A : AS} {m : Machine}
    (hs : Sim E F A m) (hh : SiteOK D.P m) : ∃ B ∈ preX D A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := ScreenPage.cov_preS hO hs hh
  obtain ⟨C, hC, h2, k2⟩ := cov_zoneX hx hp hy hz hO.stI B m h1
  exact ⟨C, List.mem_flatMap.2 ⟨B, hB, hC⟩, h2, k2.trans k1⟩

/-- a byte with the known bits of `b` is one of `vals b` -/
theorem mem_vals {b : AB} {u : UInt8} (h : b.mem u) : u ∈ vals b := by
  unfold vals
  refine List.mem_filterMap.2 ⟨u.toNat, List.mem_range.2 u.toNat_lt, ?_⟩
  have e : u.toNat.toUInt8 = u := UInt8.ofNat_toNat
  rw [e]
  have h' : u &&& b.k = b.v &&& b.k := h
  simp [h']

end

/-! ## The new steps -/

set_option maxRecDepth 100000 in
theorem op_E9 : opTable[(0xE9 : UInt8).toNat]?.getD opJAM = opSBC mImm := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

/-- the add of `SBC #v` with the carry 1, on numbers: with the low four bits of `v` 0 the low four bits stay -/
theorem sbc_nat (a v : UInt8) (hv : v &&& 0x0F = 0) :
    (a.toUInt16 + (~~~v).toUInt16 + (1 : UInt8).toUInt16).toUInt8 &&& 0x0F = a &&& 0x0F := by
  apply UInt8.toNat_inj.1
  have e : (0x0F : UInt8).toNat = 2 ^ 4 - 1 := rfl
  have hv' : v.toNat % 16 = 0 := by
    have := congrArg UInt8.toNat hv
    rw [UInt8.toNat_and, e, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  rw [UInt8.toNat_and, UInt8.toNat_and, e, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_add, UInt8.toNat_toUInt16, UInt8.toNat_not]
  have ha := a.toNat_lt
  have hvl := v.toNat_lt
  have hs : UInt8.size = 256 := rfl
  have h1 : UInt8.toNat 1 = 1 := rfl
  rw [hs, h1]
  omega

/-- **`SBC #v` with the carry 1 and the low four bits of `v` 0 keeps the low four bits of the accumulator** -/
theorem sbc_low {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : 0x8000 ≤ m.pc + 1)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xE9) (hv : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat &&& 0x0F = 0) (hc : m.p &&& 1 = 1) :
    (go step m).2.a &&& 0x0F = m.a &&& 0x0F := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), op_E9, PipeTransitionAll.go_bind, RoomBlocks.tick_a]
  show (go (mImm >>= fun a => rd a >>= fun v => adc (~~~v)) { m with pc := m.pc + 1 }).2.a &&& 0x0F = m.a &&& 0x0F
  rw [PipeTransitionAll.go_bind]
  show (go (rd (m.pc + 1) >>= fun v => adc (~~~v)) { m with pc := m.pc + 1 + 1 }).2.a &&& 0x0F = m.a &&& 0x0F
  rw [PipeTransitionAll.go_bind, TaintRun.rd_rom _ (by intro h; have := UInt16.le_iff_toNat_le.1 hp1; have := UInt16.lt_iff_toNat_lt.1 h; simp at *; omega) hp1]
  show (m.a.toUInt16 + (~~~(m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat)).toUInt16 + (m.p &&& 1).toUInt16).toUInt8 &&& 0x0F = m.a &&& 0x0F
  rw [hc]
  exact sbc_nat m.a _ hv

/-- the bits of `refineS`: the low bits of the accumulator before -/
theorem refineS_mem {a a' av ak : UInt8} (h2 : a &&& ak = av &&& ak) (h3 : ak &&& 0x0F = 0x0F) (h4 : a' &&& 0x0F = a &&& 0x0F) :
    a' &&& 0x0F = av &&& 0x0F &&& 0x0F := by
  have e1 : a &&& 0x0F = av &&& 0x0F := by
    have := congrArg (· &&& 0x0F) h2
    simp only [UInt8.and_assoc, h3] at this
    exact this
  rw [h4, e1, UInt8.and_assoc, UInt8.and_self]

/-- the low bits of a known byte -/
theorem xbit_of_mem {b : AB} {x : UInt8} (h : b.mem x) (hb : b.k &&& b.v &&& 0x0F ≠ 0) : x &&& 0x0F ≠ 0 := by
  have h' : x &&& b.k = b.v &&& b.k := h
  intro hx
  apply hb
  rw [UInt8.and_comm b.k b.v, ← h', UInt8.and_assoc, UInt8.and_comm b.k 0x0F, ← UInt8.and_assoc, hx, UInt8.zero_and]

section
variable {E : Env} {F : Nat × UInt8}

/-- the row's `SBC #` on the ROM -/
structure SbcOK (E : Env) (q : UInt16) : Prop where
  pc : 0x8000 ≤ q
  pc1 : 0x8000 ≤ q + 1
  op : E.prg.get! (q &&& E.mask).toNat = 0xE9
  imm : E.prg.get! ((q + 1) &&& E.mask).toNat &&& 0x0F = 0

theorem sbcOK_spec {pc : UInt16} (h : sbcOK E pc = true) : SbcOK E pc := by
  simp only [sbcOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **One step of the walk** is sound, if the instruction meets `SiteOK`, the map's bits, the read in the block buffers and the head's cell free in the map -/
theorem s_stepX {D : XD} {ops : Array (AM Unit)} (hO : PlacesOK E D.P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (ha : AdcOK E D.pageAdc)
    (hb : SbcOK E D.rowSbc) (hr1 : 0x8000 ≤ D.P.read + 1) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK D.P m)
    (hz : ReadTiles.ZeroIn D.P D.M m) (hi : ReadTiles.ReadIn D.P m) (hf : ReadTiles.HeadFree D.P D.M m) :
    ∃ r ∈ stepX D E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepX
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
          apply EntryHeightBig.adc0_a hn hs.halted (by rw [hpc]; exact ha.pc) (by rw [hpc]; exact ha.pc1)
          · rw [hs.prg, hs.mask, hpc]; exact ha.op
          · rw [hs.prg, hs.mask, hpc]; exact ha.imm
          · exact hc0
        refine ⟨{ h1 with a := ?_ }, h2⟩
        show A.a.mem (go step m).2.a
        rw [ea]
        exact hs.a
      · exact ⟨h1, h2⟩
  rw [if_neg c1]
  by_cases c2 : (!A.nmi && A.pc == D.rowSbc) = true
  · rw [if_pos c2]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c2
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs
    refine ⟨r.map (refineS A), List.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩
    intro B hB'
    cases r with
    | none => cases hB'
    | some B0 =>
      have e : refineS A B0 = B := Option.some.inj hB'
      subst e
      obtain ⟨h1, h2⟩ := hB B0 rfl
      unfold refineS
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        have hcm : (A.p.and (AB.known 1)).mem (m.p &&& 1) := mem_and hs.p (mem_known_self _)
        have hc1 : m.p &&& 1 = 1 := by rw [PipeEntryRule.known_eq hc.1.1.1 hcm, hc.1.1.2]
        have hn : m.nmiPending = false := by rw [hs.nmi]; exact c2.1
        have hpc : m.pc = D.rowSbc := hs.pc.trans c2.2
        have ea : (go step m).2.a &&& 0x0F = m.a &&& 0x0F := by
          apply sbc_low hn hs.halted (by rw [hpc]; exact hb.pc) (by rw [hpc]; exact hb.pc1)
          · rw [hs.prg, hs.mask, hpc]; exact hb.op
          · rw [hs.prg, hs.mask, hpc]; exact hb.imm
          · exact hc1
        refine ⟨{ h1 with a := ?_ }, h2⟩
        show AB.mem ⟨A.a.v &&& 0x0F, 0x0F⟩ (go step m).2.a
        exact refineS_mem hs.a hc.1.2 ea
      · exact ⟨h1, h2⟩
  rw [if_neg c2]
  by_cases c3 : candRead D E A = true
  · rw [if_pos c3]
    have c3' := c3
    simp only [candRead, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at c3'
    obtain ⟨⟨⟨⟨hn, hpc⟩, hlo⟩, hhi⟩, _⟩ := c3'
    have hpm : m.pc = D.P.read := hs.pc.trans hpc
    have hp1 : 0x8000 ≤ m.pc + 1 := by rw [hpm]; exact hr1
    have hra := RoomBlocks.readAddr_eq hp1
    have hz' : RoomBlocks.operand m = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hs.pc]
    rw [hz'] at hra
    have el : m.ram.get! ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat = (ptrLo E A).v :=
      PipeEntryRule.known_eq hlo (hs.ram _ (PipeTransitionAll.mask_lt _))
    have eh : m.ram.get! (((E.prg.get! ((A.pc + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat = (ptrHi E A).v :=
      PipeEntryRule.known_eq hhi (hs.ram _ (PipeTransitionAll.mask_lt _))
    have ead : ScreenPage.readAddr m = ptrOf E A + m.y.toUInt16 := by
      rw [hra]
      unfold ptrOf RoomBlocks.ptrZ
      rw [← el, ← eh]
    have hcand : ScreenPage.readAddr m ∈ candAds E A := by
      rw [ead]
      exact List.mem_map.2 ⟨m.y, mem_vals hs.y, rfl⟩
    obtain ⟨i1, i2, i3⟩ := hi hpm
    have hval : ScreenPage.readVal m = m.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat := RoomBlocks.readVal_eq i1
    obtain ⟨t1, t2⟩ := hh.read hpm
    have htf := ScreenPage.mem_tilesFor hO hs t1 t2
    have hok : okAt D A (ScreenPage.readAddr m) (ScreenPage.readVal m) = true := by
      unfold okAt
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
      refine ⟨⟨⟨i1, ?_⟩, ?_⟩, ?_⟩
      · simp only [ReadTiles.inBuf, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨i2, i3⟩
      · rw [hval]
        exact hz _ i2 i3
      · by_cases hk : headK D.P A = true
        · right
          simp only [headK, Bool.and_eq_true] at hk
          have esv : m.ram.get! D.P.saveI = (A.getK D.P.saveI).v := PipeEntryRule.known_eq hk.1 (hs.ram _ hO.saveI)
          have hmem : m.ram.get! D.P.saveI ∈ D.P.heads := by
            rw [esv]
            exact List.mem_of_elem_eq_true hk.2
          exact List.contains_iff_mem.2 (hf hpm hmem)
        · left
          simpa using hk
    have hop : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 := by rw [hpc]; exact hO.read.2
    have hpA : 0x8000 ≤ A.pc := by rw [hpc]; exact hO.read.1
    have hm : 0x8000 ≤ m.pc := by rw [hs.pc]; exact hpA
    have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
    refine ⟨_, List.mem_map.2 ⟨ScreenPage.readVal m, List.mem_filter.2 ⟨htf, List.any_eq_true.2 ⟨_, hcand, hok⟩⟩, rfl⟩, fun B hB => ?_⟩
    exact ScreenPage.s_readStep hs hn hpA hop (hh.reads hm hop2) (mem_known_self _) hB
  rw [if_neg c3]
  exact ScreenPage.s_stepS hO hops hT hs hh

end

/-! ## The walk covers the machine -/

section
variable {D : XD} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveX (D : XD) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkX D C n A = true

theorem cover_liveX (ht : C.t.all (walkX D C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ A, LiveX D C F A m ∧ A.k = B.k := by
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

/-- a state that meets `xbitOK` covers only machines that meet `Xbit` -/
theorem xbit_of_ok {E : Env} {P : Places} {A : AS} {m : Machine} (hO : PlacesOK E P) (hs : Sim E F A m) (h : xbitOK P A = true) : SiteParts.Xbit P m := by
  intro hpc
  unfold xbitOK at h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · exact absurd (hs.pc.symm.trans hpc) h
  · exact xbit_of_mem (hs.ram _ hO.xI) h

/-- a live state meets `xbitOK` -/
theorem xbitOK_of_live {A : AS} {m : Machine} (hl : LiveX D C F A m) : xbitOK D.P A = true := by
  obtain ⟨_, n, hw⟩ := hl
  cases n with
  | zero => simp [walkX] at hw
  | succ n =>
    simp only [walkX, Bool.and_eq_true] at hw
    exact hw.1

/-- what the walk needs of the places -/
structure PlX (D : XD) (C : CfgS) : Prop where
  places : PlacesOK C.E C.P
  pl : C.P = D.P
  xI : D.xI < 2048
  pgI : D.pgI < 2048
  yI : D.yI < 2048
  szI : D.szI < 2048
  adc : AdcOK C.E D.pageAdc
  sbc : SbcOK C.E D.rowSbc
  read1 : 0x8000 ≤ D.P.read + 1
  ops : C.ops = (aRows C.E).toArray

/-- **One step of the walk**: the next machine is covered by a live state in the same frame, or the frame ends in a state that `fin` accepts -/
theorem live_stepX (hQ : PlX D C) (ht : C.t.all (walkX D C Fu) = true) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveX D C F A m)
    (hh : EraseRange.SiteX C.P m) (hh2 : EraseRange.SiteX C.P (go step m).2) (hz : ReadTiles.ZeroIn D.P D.M m) (hi : ReadTiles.ReadIn D.P m)
    (hf : ReadTiles.HeadFree D.P D.M m) :
    (∃ A', LiveX D C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  have hx := xbitOK_of_live hl
  obtain ⟨hs, n, hw⟩ := hl
  have hO := hQ.places
  have hOS : PlacesOK C.E D.P := by rw [← hQ.pl]; exact hO
  have hhS : SiteOK D.P m := by
    have h1 : EraseRange.SiteX D.P m := by rw [← hQ.pl]; exact hh
    exact EraseRange.siteOK_of_X h1 (xbit_of_ok hOS hs hx)
  cases n with
  | zero => simp [walkX] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preX hOS hQ.xI hQ.pgI hQ.yI hQ.szI hs0 hhS
    obtain ⟨r, hr, hB⟩ := s_stepX hOS hQ.ops hT hQ.adc hQ.sbc hQ.read1 hs1 hhS hz hi hf
    simp only [walkX, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 A₁ hA r hr
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
        · obtain ⟨D', hD, hk⟩ := cover_liveX ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D', hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `A₀` that succeeds covers the frame of every machine of `A₀`, for every input, if each instruction meets `SiteX`, the map's
bits, the read in the block buffers and the head's cell free in the map. Then each instruction meets `Xbit`, if the frame's end states meet `xbitOK`. -/
theorem frame_of_walkX (hQ : PlX D C) (ht : C.t.all (walkX D C Fu) = true) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    (hfin : ∀ B, C.fin B = true → xbitOK D.P B = true)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkX D C Fu A₀ = true) (hs : Sim C.E F A₀ m) (hk : ∀ j, EraseRange.SiteX C.P (trace m i j))
    (hz : ∀ j, ReadTiles.ZeroIn D.P D.M (trace m i j)) (hi : ∀ j, ReadTiles.ReadIn D.P (trace m i j))
    (hf : ∀ j, ReadTiles.HeadFree D.P D.M (trace m i j)) :
    ∀ j, SiteParts.Xbit D.P (trace m i j) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have hOS : PlacesOK C.E D.P := by rw [← hQ.pl]; exact hQ.places
  have key : ∀ j, (∃ A, LiveX D C F A (trace m i j) ∧ A.k = A₀.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
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
        rcases live_stepX hQ ht hT h1 (hk j) hh2 (hz j) (hi j) (hf j) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3, h4⟩
  intro j
  rcases key j with ⟨A, h1, _, _, _⟩ | ⟨_, B, h2, _, h4⟩
  · exact xbit_of_ok hOS h1.1 (xbitOK_of_live h1)
  · exact xbit_of_ok hOS h4 (hfin B h2)

end

/-! ## The frame -/

/-- what the check says -/
structure WalkOKX (D : XD) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  pq : PlX D C
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  fin : C.fin = fin
  table : C.t.all (walkX D C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkX D C ScreenPage.fuelS A = true

theorem walkOKX_of_check {D : XD} {Z : Aids} {O : EntryHeight.Opts} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckX D Z O fin E r K = true) : WalkOKX D fin E r K (cfgOfX D Z O fin E r K) := by
  simp only [walkCheckX, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h5⟩, h6⟩, h7⟩, h7'⟩, h8⟩, h9⟩, h10⟩, h12⟩, h13⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨⟨ScreenPage.placesOK_spec h1, rfl, h5, h6, h7, h7', adcOK_spec h8, sbcOK_spec h9, h10, rfl⟩, hp, ScreenPage.maskOK_spec h3, rfl, rfl, h12, h13⟩

/-- **`Xbit` on a frame of the room.** A frame that starts in the room's condition with the bits `K`, with `SiteX`, the map's bits, the read in the block buffers
and the head's cell free in the map on each instruction, meets `Xbit` on each instruction. -/
theorem xbit_frame {D : XD} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKX D (xbitOK D.P) E r K C) {m : Machine} {i : UInt8}
    (hm : RoomCond E r K m) (hk : ∀ j, EraseRange.SiteX D.P (trace m i j)) (hz : ∀ j, ReadTiles.ZeroIn D.P D.M (trace m i j))
    (hi : ∀ j, ReadTiles.ReadIn D.P (trace m i j)) (hf : ∀ j, ReadTiles.HeadFree D.P D.M (trace m i j)) :
    ∀ j, SiteParts.Xbit D.P (trace m i j) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  exact frame_of_walkX (i := i) h.pq h.table (show 2 ≤ (2 : UInt8).toNat by decide) (by rw [h.env]; exact h.pad) (fun B hB => by rw [h.fin] at hB; exact hB)
    hw hs' (by rw [h.pq.pl]; exact hk) hz hi hf

/-! ## On the ROM -/

section
open ScreenPage (placesR envR refR aidsOf)
open PipeEntryRule (findOp)

/-- the places, from the symbols and the ROM. The split is at the collision routine's first read of the height; the one position with the height split is the
side pipe's column times 16; the page's `ADC #0` and the row's `SBC #` are the first of their kind in the block buffer routine -/
def xdOf (sy : Syms) (nm : Names) (m0 : Machine) : XD :=
  { P := placesR sy nm m0
    M := RoomMap.mapRef m0
    splitAt := sy.PlayerBGCollision
    stRead := ScreenPage.findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_State.toUInt8 32
    xI := (sy.Player_X_Position &&& 0x7FF).toNat
    pgI := (sy.Player_PageLoc &&& 0x7FF).toNat
    yI := (sy.Player_Y_Position &&& 0x7FF).toNat
    szI := SizeKeep.sizeI sy
    yr := (SideTransition.entry m0).ram.get! (EntryHeight.heightI sy) >>> (4 : UInt8)
    xv := (16 * SidePipe.column sy).toUInt8
    pageAdc := findOp m0 sy.BlockBufferCollision 0x69 32
    rowSbc := findOp m0 sy.BlockBufferCollision 0xE9 64
    exits := (SideEntryRule.spots sy m0).exits }

theorem xdOf_P (sy : Syms) (nm : Names) (m0 : Machine) : (xdOf sy nm m0).P = placesR sy nm m0 := by dsimp only [xdOf]
theorem xdOf_M (sy : Syms) (nm : Names) (m0 : Machine) : (xdOf sy nm m0).M = RoomMap.mapRef m0 := by dsimp only [xdOf]

/-- the known bits of the walk's start: those of the room's walks at a frame's start (`RoomMusic.knownM`), and bits 1 to 7 of the player's size
(`SizeKeep`: a small or a big player) -/
def knownX (sy : Syms) (nm : Names) : List (Nat × UInt8) := RoomMusic.knownM nm ++ [(SizeKeep.sizeI sy, 0xFE)]

/-- **The check on the ROM**: the walk from the room's condition with the bits of `knownX` -/
def checkX (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  let D := xdOf sy nm m0
  let Z := aidsOf sy nm m0
  walkCheckX D Z (optsX D Z (envR sy nm m0)) (xbitOK D.P) (envR sy nm m0) (refR m0) (knownX sy nm)

/-- **`Xbit` on a frame of the room, on the ROM**: a frame that starts in the room's condition (`knownX`), with `SiteX`, the map's bits, the read in the
block buffers and the head's cell free in the map on each instruction -/
theorem xbit_of_check {sy : Syms} {nm : Names} {m0 : Machine} (h : checkX sy nm m0 = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nm m0) (refR m0) (knownX sy nm) m) (hk : ∀ j, EraseRange.SiteX (placesR sy nm m0) (trace m i j))
    (hz : ∀ j, ReadTiles.ZeroIn (placesR sy nm m0) (RoomMap.mapRef m0) (trace m i j)) (hi : ∀ j, ReadTiles.ReadIn (placesR sy nm m0) (trace m i j))
    (hf : ∀ j, ReadTiles.HeadFree (placesR sy nm m0) (RoomMap.mapRef m0) (trace m i j)) :
    ∀ j, SiteParts.Xbit (placesR sy nm m0) (trace m i j) := by
  have hw := walkOKX_of_check h
  have e1 := xdOf_P sy nm m0
  have e2 := xdOf_M sy nm m0
  have h2 := xbit_frame (D := xdOf sy nm m0) hw hm (by rw [e1]; exact hk) (by rw [e1, e2]; exact hz) (by rw [e1]; exact hi) (by rw [e1, e2]; exact hf)
  rw [e1] at h2
  exact h2

end

end Smbrta.HeadSide
