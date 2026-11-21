import Theorems.BufferCoin
import Theorems.EntryHeightBig

/-!
# A frame that erases a coin ends at 16 to 180 px

`Route.Run.buffer₂` asked (round 24) that a frame of the room that ends with the control of the screen's buffers at 6 (the value after the erase of a coin) ends on
page 0 at 16 to 180 px, or that the screen buffer's bytes at the entry are a reference's. Here the position part is proved: a frame of the room that starts with
the control at 0 or 6 and ends with it at 6 ends with the position on the page (`x`) from 16 to 180 px (`end_frame`, `end_of_rows`).

Every way to a coin in the collision routine (a read for the head, for a foot or for a side) goes to the erase of the coin, which sets the control to 6, and then
returns from the collision routine; so does every push of a side collision. So on a frame that erases a coin, after the end of the move only the scroll handler
may store the position, and it stores a value at a screen's edge.

The walk is the room's walk with the control known (`EntryBuffer`), with more pieces (`zoneX`). At the end of the move (`PlayerSubs`) it splits the position into
pieces whose known bits are a run of high bits: the pieces of `[16, 181)` and those outside it (`piecesX`). With a piece outside, where the block buffer routine
adds the position (the player's, `X = 0`) it splits the position into its values (`fillB`); with the position known, where the routine makes the block buffer's
address it splits the page's bit (bit 4 of the accumulator), and at the mask of the row the high bits of the accumulator. So the read has a known place: it takes
the byte's bits that the room's condition knows (the bits that are 0 in the map), and after the save of the byte its values (`tileAt`); a coin is read only in a
coin's column. With a piece inside, the read may give any tile, a coin too, and the piece stays up to the frame's end. At the frame's end (`finX`) the control is
known not to be 6, or every value of the position's piece is from 16 to 180.

What stays assumed is the page: a frame that ends with the control at 6 is not shown to end on page 0. That needs the position on every frame of the room.

There is no game data in this file. Page: `1-1/d-2-5-5-3-BufferEnd.md`.
-/

namespace Smbrta.BufferEnd

open PipeTransition (frame)
open PipeTransitionAll (Names go)
open TaintRun
open PipeEntryRule (trace frame_trace trace_stop nxt)
open ScreenPage (Places SiteOK PlacesOK CfgS Aids SearchS clampS preS weaken coverS startsR RoomCond MaskOK placesR envR refR aidsOf)
open EntryHeight (HP Opts preY stepY mix64 putY routeY)
open SideEntryRest (notV ne_of_notV)

/-! ## The pieces of the position -/

/-- the pieces of the position: the aligned blocks before `lo`, from `lo` before `hi`, and from `hi` on -/
def piecesX (lo hi : Nat) : List AB := BufferCoin.rangePieces 0 lo ++ BufferCoin.rangePieces lo hi ++ BufferCoin.rangePieces hi 256

/-- every value is in a piece -/
def piecesCover (lo hi : Nat) : Bool := (List.range 256).all fun n => (piecesX lo hi).any fun a => SideFrame.memB a n.toUInt8

/-- every value that meets the byte's known bits is from `lo` before `hi` -/
def inside (lo hi : Nat) (b : AB) : Bool := (List.range 256).all fun n => !SideFrame.memB b n.toUInt8 || (decide (lo ≤ n) && decide (n < hi))

/-- the places of the walk -/
structure MX where
  /-- the position on the page -/
  xI : Nat
  /-- the end of the move (`PlayerSubs`) -/
  subs : UInt16
  /-- the collision routine's load of the adders' offset (by `Y`: the player's size, in the water or not) -/
  gbb : UInt16
  /-- the block buffer routine's add of the position, the start of the routine that makes the block buffer's address, the mask of the row -/
  adc : UInt16
  colAt : UInt16
  andAt : UInt16
  /-- the return from the collision routine, and more places where the search stops a run of single steps: only for the search -/
  colEnd : UInt16
  stopsX : List UInt16
  /-- the byte where the collision routine keeps the adders' offset, the pointer of the read and the row: only for the search -/
  sideI : Nat
  ptrI : Nat
  rowI : Nat
  /-- the byte where the routine saves the sum, and the save of the tile read: only for the search -/
  sumI : Nat
  tileAt : UInt16
  tileI : Nat
  coin : UInt8
  /-- the bounds of the inside -/
  lo : Nat
  hi : Nat
  deriving Inhabited

/-- the pieces of the position's walk: at the end of the move, with the position not known, its pieces; with the position's piece not inside: at the load of the
adders' offset the offset's bits, at the block buffer routine's add of the player's position the position's values, at the start of the address's routine the page's
bit, and at the mask of the row the high bits of the accumulator -/
def zoneX (M : MX) (A : AS) : List AS :=
  if A.pc == M.subs && (A.getK M.xI).k == 0 then (piecesX M.lo M.hi).map fun a => A.setK M.xI a
  else if A.pc == M.gbb && !inside M.lo M.hi (A.getK M.xI) then PipeChangeEnd.allBits PipeChangeEnd.bitY A
  else if A.pc == M.adc && A.x.isK && A.x.v == 0 && !inside M.lo M.hi (A.getK M.xI) then SideFrame.fillB M.xI A
  else if A.pc == M.colAt && !inside M.lo M.hi (A.getK M.xI) then PipeChangeEnd.bitA 16 A
  else if A.pc == M.andAt && !inside M.lo M.hi (A.getK M.xI) then SideFrame.highA A
  else [A]

/-- the pieces before a step: those of the room's walk (with the tile's values after its save), then those of the position -/
def preX (S : HP) (M : MX) (A : AS) : List AS := (preY S A).flatMap (zoneX M)

/-- at the frame's end: the control `c` known not to be 6, or the position's piece inside -/
def finX (c : Nat) (M : MX) (B : AS) : Bool := notV 6 (B.getK c) || inside M.lo M.hi (B.getK M.xI)

/-- the read of the block buffer routine with its pointer and `Y` known, in the RAM -/
def readAt (P : Places) (E : Env) (A : AS) : Bool :=
  !A.nmi && A.pc == P.read && (EntryHeightBig.ptrLo E A).isK && (EntryHeightBig.ptrHi E A).isK && A.y.isK && decide (EntryHeightBig.readAd E A < 0x2000)

/-- the erase of a coin with its place known outside the block buffers: `SiteOK` says that no machine comes there -/
def eraseOut (P : Places) (E : Env) (A : AS) : Bool :=
  !A.nmi && A.pc == P.erase && (EntryHeightBig.ptrLo E A).isK && (EntryHeightBig.ptrHi E A).isK && A.y.isK &&
    !(decide (EntryHeightBig.readAd E A < 0x2000) && decide (P.bufLo ≤ EntryHeightBig.readI E A) && decide (EntryHeightBig.readI E A < P.bufLo + P.bufN))

/-- a step: at `eraseOut`, no machine; at a read of `readAt`, each tile that `SiteOK` allows there and that meets the known bits of the byte read; else the step of
`EntryHeight` -/
def stepZ (P : Places) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if eraseOut P E A then []
  else if readAt P E A then
    ((ScreenPage.tilesFor P A).filter fun v => SideFrame.memB (A.getK (EntryHeightBig.readI E A)) v).map fun v => ScreenPage.readStep E (AB.known v) A
  else stepY P E ops A

/-- from `A`, step by step, until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkX (S : HP) (M : MX) (C : CfgS) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preX S M (clampS C.P A)).all fun A₁ => (stepZ C.P C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! (weaken C B).pc.toNat != 0 && coverS C (clampS C.P (weaken C B))) || walkX S M C n (weaken C B)
      else B.k == A.k + 1 && C.fin B

/-! ## The search: no part of the proof -/

/-- the piece of a known position -/
def pieceX (M : MX) (b : AB) : AB :=
  if b.isK then
    match (piecesX M.lo M.hi).find? (fun a => SideFrame.memB a b.v) with
    | some a => a
    | none => b
  else b

/-- the key: the room's, the control and the position, and with the position's piece not inside the registers; below them 64 mixed bits -/
def keyX (Z : Aids) (E : Env) (c : Nat) (M : MX) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let inR := (M.adc - 7 ≤ A.pc && A.pc < M.adc + 0x40) || (M.colAt ≤ A.pc && A.pc < M.colAt + 0x20)
  let inR := inR || (!inside M.lo M.hi (A.getK M.xI) && SideFrame.memB (A.getK M.tileI) M.coin)
  let r := if !inside M.lo M.hi (A.getK M.xI) && inR then
      ((((((num A.a * 65536 + num A.x) * 65536 + num A.y) * 65536 + num (A.getK M.ptrI)) * 65536 + num (A.getK (M.ptrI + 1))) * 65536 + num (A.getK M.rowI)) * 65536 +
        num (A.getK M.sumI)) * 4 + 1
    else if A.pc == M.gbb + 3 && !inside M.lo M.hi (A.getK M.xI) then num A.y * 4 + 2 else 0
  let K := Z.key E A + ((num (A.getK c) * 65536 + num (A.getK M.xI)) * (1 <<< 120) + r) * (1 <<< 300)
  K * 18446744073709551616 + mix64 K

/-- what a state forgets: what the room's search forgets, but with the position's piece not inside not the adders' offset; and at the return from the collision
routine the position, or with the control not known to differ from 6 a known position down to its piece -/
def normX (Z : Aids) (c : Nat) (M : MX) (A : AS) : AS :=
  let B := Z.norm A
  let B := if A.pc != M.colEnd && !inside M.lo M.hi (A.getK M.xI) then B.setK M.sideI (A.getK M.sideI) else B
  -- after the add of the position: the position down to its piece, the sum down to its high bits (the column)
  if A.pc == M.adc + 2 && (B.getK M.xI).isK then
    { B.setK M.xI (pieceX M (B.getK M.xI)) with a := ⟨B.a.v &&& 0xF0, B.a.k &&& 0xF0⟩ }
  -- after the save of the tile: the pointer, the row and `Y`
  else if A.pc == M.tileAt && !SideFrame.memB (B.getK M.tileI) M.coin then { (((B.setK M.ptrI AB.top).setK (M.ptrI + 1) AB.top).setK M.rowI AB.top) with y := AB.top }
  else if A.pc == M.colEnd then
    if notV 6 (A.getK c) then B.setK M.xI AB.top else B.setK M.xI (pieceX M (B.getK M.xI))
  else B

def optsX (Z : Aids) (E : Env) (c : Nat) (M : MX) : Opts :=
  { key := keyX Z E c M, norm := normX Z c M, stops := [M.subs, M.gbb, M.adc, M.adc + 2, M.colAt, M.andAt, M.tileAt] ++ M.stopsX,
    normAt := [M.colEnd, M.adc + 2, M.tileAt] }

partial def runX (S : HP) (M : MX) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) (A0 : AS) : SearchS := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preX S M (clampS S.P cur)).flatMap (stepZ S.P E ops)
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
        X := routeY S.P O X b
    break
  return X

partial def searchX (S : HP) (M : MX) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (ops : Array (AM Unit)) (X0 : SearchS) : SearchS := Id.run do
  let mut X := X0
  while true do
    if X.done.size > 1000000 then
      X := { X with fails := X.fails + 1000000 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (q, A) =>
      let K := O.key A
      X := { X with pending := X.pending.erase q, pendKey := X.pendKey.erase K }
      X := runX S M Z O fin E ops X A
  return X

def searchOfX (S : HP) (M : MX) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : SearchS :=
  let ops := (aRows E).toArray
  searchX S M Z O fin E ops ((startsR r K).foldl (routeY S.P O) {})

/-- the configuration from the table found -/
def cfgOfX (S : HP) (M : MX) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : CfgS :=
  let X := searchOfX S M Z O fin E r K
  let tab := X.done.toList.filter fun q => X.arr.getD q.1 0 ≥ 2
  let q := tab.foldl (fun (acc : Array AS × Std.HashMap Nat (List Nat) × ByteArray) e =>
      (acc.1.push e.2, acc.2.1.insert e.1 (acc.1.size :: acc.2.1.getD e.1 []), acc.2.2.set! e.2.pc.toNat 1))
    (#[], ({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0))
  let at0 := (Z.regs ++ Z.ends ++ Z.cutAY ++ Z.cutX ++ [Z.colEnd] ++ O.normAt).foldl (fun b a => b.set! a.toNat 1) (ByteArray.mk (Array.replicate 65536 0))
  { E, ops := (aRows E).toArray, P := S.P, fin, t := q.1, key := O.key, idx := q.2.1, cut := q.2.2, norm := O.norm, normAt := at0 }

/-- **The check of the walk**, with the condition `fin` on the frame's end -/
def walkCheckX (S : HP) (M : MX) (Z : Aids) (O : Opts) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) : Bool :=
  let C := cfgOfX S M Z O fin E r K
  ScreenPage.placesOK E S.P && E.pad.v == 0 && E.pad.k == 0 && ScreenPage.maskOK r K &&
    decide (S.yI < 2048) && decide (S.tileI < 2048) && decide (M.xI < 2048) && piecesCover M.lo M.hi && decide (0x8000 ≤ S.P.read + 1) && decide (0x8000 ≤ S.P.erase + 1) &&
    C.t.all (walkX S M C ScreenPage.fuelS) && (startsR r K).all (walkX S M C ScreenPage.fuelS)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- a value is in a piece -/
theorem piece_of_cover {lo hi : Nat} (hc : piecesCover lo hi = true) (x : UInt8) : ∃ a ∈ piecesX lo hi, a.mem x := by
  simp only [piecesCover, List.all_eq_true, List.mem_range, List.any_eq_true] at hc
  obtain ⟨a, ha, h⟩ := hc x.toNat x.toNat_lt
  have hv : x.toNat.toUInt8 = x := by simp
  rw [hv] at h
  exact ⟨a, ha, SideFrame.memB_iff.1 h⟩

/-- the pieces of the position's walk cover every machine -/
theorem cov_zoneX {M : MX} (hx : M.xI < 2048) (hc : piecesCover M.lo M.hi = true) : Cov E F (zoneX M) := by
  intro A m hs
  unfold zoneX
  by_cases h1 : (A.pc == M.subs && (A.getK M.xI).k == 0) = true
  · rw [if_pos h1]
    obtain ⟨a, ha, hm⟩ := piece_of_cover hc (m.ram.get! M.xI)
    exact ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, PipeEntryRule.sim_setK' hs hm, rfl⟩
  rw [if_neg h1]
  by_cases h1' : (A.pc == M.gbb && !inside M.lo M.hi (A.getK M.xI)) = true
  · rw [if_pos h1']
    exact PipeChangeEnd.cov_allBits (fun _ hb => PipeChangeEnd.cov_bitY hb) A m hs
  rw [if_neg h1']
  by_cases h2 : (A.pc == M.adc && A.x.isK && A.x.v == 0 && !inside M.lo M.hi (A.getK M.xI)) = true
  · rw [if_pos h2]
    exact SideFrame.cov_fill hx A m hs
  rw [if_neg h2]
  by_cases h3 : (A.pc == M.colAt && !inside M.lo M.hi (A.getK M.xI)) = true
  · rw [if_pos h3]
    exact PipeChangeEnd.cov_bitA (by decide) A m hs
  rw [if_neg h3]
  by_cases h4 : (A.pc == M.andAt && !inside M.lo M.hi (A.getK M.xI)) = true
  · rw [if_pos h4]
    exact SideFrame.cov_highA A m hs
  rw [if_neg h4]
  exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preX {S : HP} {M : MX} (hO : PlacesOK E S.P) (hy : S.yI < 2048) (ht : S.tileI < 2048) (hx : M.xI < 2048) (hc : piecesCover M.lo M.hi = true)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK S.P m) : ∃ B ∈ preX S M A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, k1⟩ := EntryHeight.cov_preY hO hy ht hs hh
  obtain ⟨D, hD, h2, k2⟩ := cov_zoneX hx hc B m h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2, k2.trans k1⟩

/-- **One step of the walk** is sound, if the instruction meets `SiteOK`: at a read with its place known, the byte read is a tile of `SiteOK`'s list and it meets
the known bits of its RAM byte -/
theorem s_stepZ {P : Places} {ops : Array (AM Unit)} (hO : PlacesOK E P) (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (hr1 : 0x8000 ≤ P.read + 1) (he1 : 0x8000 ≤ P.erase + 1) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : SiteOK P m) :
    ∃ r ∈ stepZ P E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold stepZ
  by_cases c0 : eraseOut P E A = true
  · exfalso
    have c0' := c0
    simp only [eraseOut, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c0'
    obtain ⟨⟨⟨⟨⟨_, hpc⟩, hlo⟩, hhi⟩, hy⟩, hout⟩ := c0'
    have hpm : m.pc = P.erase := hs.pc.trans hpc
    have hp1 : 0x8000 ≤ m.pc + 1 := by rw [hpm]; exact he1
    have hwa := RoomBlocks.writeAddr_eq hp1
    have hz : RoomBlocks.operand m = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hs.pc]
    rw [hz] at hwa
    have ey : m.y = A.y.v := PipeEntryRule.known_eq hy hs.y
    have el : m.ram.get! ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat = (EntryHeightBig.ptrLo E A).v :=
      PipeEntryRule.known_eq hlo (hs.ram _ (PipeTransitionAll.mask_lt _))
    have eh : m.ram.get! (((E.prg.get! ((A.pc + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat = (EntryHeightBig.ptrHi E A).v :=
      PipeEntryRule.known_eq hhi (hs.ram _ (PipeTransitionAll.mask_lt _))
    have ead : ScreenPage.writeAddr m = EntryHeightBig.readAd E A := by
      rw [hwa]
      unfold EntryHeightBig.readAd RoomBlocks.ptrZ
      rw [← ey, ← el, ← eh]
    obtain ⟨g1, g2, g3⟩ := hh.erase hpm
    rw [ead] at g1 g2 g3
    have key : (decide (EntryHeightBig.readAd E A < 0x2000) && decide (P.bufLo ≤ EntryHeightBig.readI E A) &&
        decide (EntryHeightBig.readI E A < P.bufLo + P.bufN)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨g1, g2⟩, g3⟩
    rw [key] at hout
    cases hout
  rw [if_neg c0]
  by_cases c2 : readAt P E A = true
  · rw [if_pos c2]
    have c2' := c2
    simp only [readAt, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at c2'
    obtain ⟨⟨⟨⟨⟨hn, hpc⟩, hlo⟩, hhi⟩, hy⟩, hlt⟩ := c2'
    have hpm : m.pc = P.read := hs.pc.trans hpc
    have hp1 : 0x8000 ≤ m.pc + 1 := by rw [hpm]; exact hr1
    have hra := RoomBlocks.readAddr_eq hp1
    have hz : RoomBlocks.operand m = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hs.pc]
    rw [hz] at hra
    have ey : m.y = A.y.v := PipeEntryRule.known_eq hy hs.y
    have el : m.ram.get! ((E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat = (EntryHeightBig.ptrLo E A).v :=
      PipeEntryRule.known_eq hlo (hs.ram _ (PipeTransitionAll.mask_lt _))
    have eh : m.ram.get! (((E.prg.get! ((A.pc + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat = (EntryHeightBig.ptrHi E A).v :=
      PipeEntryRule.known_eq hhi (hs.ram _ (PipeTransitionAll.mask_lt _))
    have ead : ScreenPage.readAddr m = EntryHeightBig.readAd E A := by
      rw [hra]
      unfold EntryHeightBig.readAd RoomBlocks.ptrZ
      rw [← ey, ← el, ← eh]
    have hval : ScreenPage.readVal m = m.ram.get! (EntryHeightBig.readI E A) := by
      rw [RoomBlocks.readVal_eq (by rw [ead]; exact hlt), ead]
      rfl
    have hop : E.prg.get! (A.pc &&& E.mask).toNat = 0xB1 := by rw [hpc]; exact hO.read.2
    have hpA : 0x8000 ≤ A.pc := by rw [hpc]; exact hO.read.1
    obtain ⟨t1, t2⟩ := hh.read hpm
    have hmT := ScreenPage.mem_tilesFor hO hs t1 t2
    have hmem : SideFrame.memB (A.getK (EntryHeightBig.readI E A)) (ScreenPage.readVal m) = true := by
      rw [hval]
      exact SideFrame.memB_iff.2 (hs.ram _ (PipeTransitionAll.mask_lt _))
    refine ⟨_, List.mem_map.2 ⟨ScreenPage.readVal m, List.mem_filter.2 ⟨hmT, hmem⟩, rfl⟩, fun B hB => ?_⟩
    have hm : 0x8000 ≤ m.pc := by rw [hs.pc]; exact hpA
    have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by rw [hs.prg, hs.mask, hs.pc]; exact hop
    exact ScreenPage.s_readStep hs hn hpA hop (hh.reads hm hop2) (mem_known_self _) hB
  · rw [if_neg c2]
    exact EntryHeight.s_stepY hO hops hT hs hh

end

/-! ## The walk covers the machine -/

section
variable {S : HP} {M : MX} {C : CfgS} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveX (S : HP) (M : MX) (C : CfgS) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkX S M C n A = true

theorem cover_liveX (ht : C.t.all (walkX S M C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverS C B = true) :
    ∃ D, LiveX S M C F D m ∧ D.k = B.k := by
  unfold coverS at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

/-- **One step of the walk**: the next machine is covered by a live state in the same frame, or the frame ends in a state that `fin` accepts -/
theorem live_stepX (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (hx : M.xI < 2048) (hc : piecesCover M.lo M.hi = true)
    (hr1 : 0x8000 ≤ C.P.read + 1) (he1 : 0x8000 ≤ C.P.erase + 1) (ht : C.t.all (walkX S M C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveX S M C F A m)
    (hh : SiteOK C.P m) (hh2 : SiteOK C.P (go step m).2) :
    (∃ A', LiveX S M C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkX] at hw
  | succ n =>
    have hs0 := ScreenPage.sim_clamp hO.late hs hh.late
    have hhS : SiteOK S.P m := by rw [← hP]; exact hh
    have hOS : PlacesOK C.E S.P := by rw [← hP]; exact hO
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preX hOS hy htl hx hc hs0 hhS
    obtain ⟨r, hr, hB⟩ := s_stepZ hO hops hT hr1 he1 hs1 hh
    simp only [walkX, List.all_eq_true] at hw
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
        · obtain ⟨D, hD, hk⟩ := cover_liveX ht (ScreenPage.sim_clamp hO.late hN.1 hh2.late) h3
          exact ⟨D, hD, by rw [hk, ScreenPage.clamp_k, hN.2, k1], k2, k3⟩
        · exact ⟨_, ⟨hN.1, n, h3⟩, by rw [hN.2, k1], k2, k3⟩
      · right
        rw [hkA] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

/-- **One frame.** A walk from `A₀` that succeeds covers the frame of every machine of `A₀`, for every input, if each instruction meets `SiteOK`. -/
theorem frame_of_walkX (hO : PlacesOK C.E C.P) (hP : C.P = S.P) (hy : S.yI < 2048) (htl : S.tileI < 2048) (hx : M.xI < 2048) (hc : piecesCover M.lo M.hi = true)
    (hr1 : 0x8000 ≤ C.P.read + 1) (he1 : 0x8000 ≤ C.P.erase + 1) (ht : C.t.all (walkX S M C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top)
    {A₀ : AS} {m : Machine} {i : UInt8} (hw : walkX S M C Fu A₀ = true) (hs : Sim C.E F A₀ m) (hk : ∀ j, SiteOK C.P (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs0 : Sim C.E F A₀ { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, (∃ A, LiveX S M C F A (trace m i j) ∧ A.k = A₀.k ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ B.k = A₀.k + 1 ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨A₀, ⟨hs0, Fu, hw⟩, rfl, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hc' : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc']
        have hh2 := hk (j + 1)
        rw [e2] at hh2 ⊢
        rcases live_stepX hO hP hy htl hx hc hr1 he1 ht hops hT h1 (hk j) hh2 with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a2, h2], by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, by rw [a3, h2], a4⟩
      · have hc' : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc']
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
structure WalkOKX (S : HP) (M : MX) (fin : AS → Bool) (E : Env) (r : Machine) (K : List (Nat × UInt8)) (C : CfgS) : Prop where
  places : PlacesOK E S.P
  pad : E.pad = AB.top
  mask : MaskOK r K
  env : C.E = E
  pl : C.P = S.P
  ops : C.ops = (aRows C.E).toArray
  fin : C.fin = fin
  yI : S.yI < 2048
  tileI : S.tileI < 2048
  xI : M.xI < 2048
  cover : piecesCover M.lo M.hi = true
  read1 : 0x8000 ≤ S.P.read + 1
  erase1 : 0x8000 ≤ S.P.erase + 1
  table : C.t.all (walkX S M C ScreenPage.fuelS) = true
  starts : ∀ A ∈ startsR r K, walkX S M C ScreenPage.fuelS A = true

theorem walkOKX_of_check {S : HP} {M : MX} {Z : Aids} {O : Opts} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)}
    (h : walkCheckX S M Z O fin E r K = true) : WalkOKX S M fin E r K (cfgOfX S M Z O fin E r K) := by
  simp only [walkCheckX, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hr⟩, he⟩, h8⟩, h9⟩ := h
  have hp : E.pad = AB.top := by
    show E.pad = ⟨0, 0⟩
    cases hq : E.pad
    rw [hq] at h2 h2'
    simp only at h2 h2'
    rw [h2, h2']
  exact ⟨ScreenPage.placesOK_spec h1, hp, ScreenPage.maskOK_spec h3, rfl, rfl, rfl, rfl, h4, h5, h6, h7, hr, he, h8, h9⟩

/-- **The end of a frame of the room.** A frame that starts in the room's condition with the bits `K`, with `SiteOK` on each instruction, ends in a machine that a
state accepted by `fin` covers. -/
theorem frame_endX {S : HP} {M : MX} {fin : AS → Bool} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKX S M fin E r K C) {m : Machine}
    {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) : ∃ B, fin B = true ∧ Sim E (m.frame, 2) B (frame m i) := by
  obtain ⟨S0, hS, hs⟩ := ScreenPage.sim_of_room (F := (m.frame, 2)) h.mask h.pad hm rfl
  have hO : PlacesOK C.E C.P := by rw [h.env, h.pl]; exact h.places
  have hw := h.starts S0 hS
  have hs' : Sim C.E (m.frame, 2) S0 m := by rw [h.env]; exact hs
  obtain ⟨_, B, h2, _, h4⟩ := frame_of_walkX (i := i) hO h.pl h.yI h.tileI h.xI h.cover (by rw [h.pl]; exact h.read1) (by rw [h.pl]; exact h.erase1) h.table h.ops (show 2 ≤ (2 : UInt8).toNat by decide)
    (by rw [h.env]; exact h.pad) hw hs' (by rw [h.pl]; exact hk)
  rw [h.fin] at h2
  rw [h.env] at h4
  exact ⟨B, h2, h4⟩

/-- what `finX` says of a machine that its state covers -/
theorem fin_spec {E : Env} {F : Nat × UInt8} {c : Nat} {M : MX} {B : AS} {m : Machine} (hs : Sim E F B m) (hc : c < 2048) (hx : M.xI < 2048)
    (h : finX c M B = true) : m.ram.get! c ≠ 6 ∨ (M.lo ≤ (m.ram.get! M.xI).toNat ∧ (m.ram.get! M.xI).toNat < M.hi) := by
  simp only [finX, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (ne_of_notV h (hs.ram c hc))
  · right
    simp only [inside, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at h
    have hm := SideFrame.memB_iff.2 (hs.ram M.xI hx)
    have hv : (m.ram.get! M.xI).toNat.toUInt8 = m.ram.get! M.xI := by simp
    rcases h (m.ram.get! M.xI).toNat (m.ram.get! M.xI).toNat_lt with h3 | h3
    · rw [hv, hm] at h3
      cases h3
    · exact h3

/-- **A frame of the room that ends with the control at 6 ends with the position from `lo` before `hi`**, if the walk from the room's condition with the bits `K`
succeeds, with `SiteOK` on each instruction -/
theorem end_frame {S : HP} {M : MX} {c : Nat} {E : Env} {r : Machine} {K : List (Nat × UInt8)} {C : CfgS} (h : WalkOKX S M (finX c M) E r K C) (hc : c < 2048)
    {m : Machine} {i : UInt8} (hm : RoomCond E r K m) (hk : ∀ j, SiteOK S.P (trace m i j)) (h6 : (frame m i).ram.get! c = 6) :
    M.lo ≤ ((frame m i).ram.get! M.xI).toNat ∧ ((frame m i).ram.get! M.xI).toNat < M.hi := by
  obtain ⟨B, h2, h4⟩ := frame_endX h hm hk
  rcases fin_spec h4 hc h.xI h2 with h3 | h3
  · exact absurd h6 h3
  · exact h3

/-! ## On the ROM -/

/-- the first instruction `op` with the absolute operand `t` from `a` on, within `n` bytes -/
def findAbs (m0 : Machine) (a t : UInt16) (op : UInt8) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m0 a == op && romByte m0 (a + 1) == t.toUInt8 && romByte m0 (a + 2) == (t >>> 8).toUInt8 then a else findAbs m0 (a + 1) t op n

/-- the places on the ROM: the load of the adders' offset is the collision routine's `LDA` of the table of offsets by `Y`; the add of the position is the instruction two bytes before the block buffer routine's first store to the zero page; the address's
routine is the target of the routine's first call, the mask of the row the first `AND` with an immediate byte after the load of the height; the return from the
collision routine is that of `ScreenPage` -/
def mxOf (sy : Syms) (m0 : Machine) : MX :=
  let sum := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x85 64
  let jsr := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x20 64
  let loadY := PipeEntryRule.findOp m0 jsr 0xB5 64
  { xI := (sy.Player_X_Position &&& 0x7FF).toNat, subs := sy.PlayerSubs, gbb := findAbs m0 sy.PlayerBGCollision sy.BlockBufferAdderData 0xB9 200, adc := sum - 2,
    colAt := (romByte m0 (jsr + 1)).toUInt16 ||| ((romByte m0 (jsr + 2)).toUInt16 <<< 8),
    andAt := PipeEntryRule.findOp m0 loadY 0x29 16,
    colEnd := ScreenPage.findJsr m0 sy.PlayerSubs sy.PlayerBGCollision 64 + 3, lo := 16, hi := 181,
    stopsX := [PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64, PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 2, PipeEntryRule.findOp m0 sy.ErACM 0x91 16],
    sideI := (romByte m0 (sy.DoFootCheck + 1)).toNat,
    ptrI := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 1)).toNat,
    rowI := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 - 2)).toNat,
    sumI := (romByte m0 (sum + 1)).toNat,
    tileAt := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 4,
    tileI := (romByte m0 (PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64 + 3)).toNat, coin := sy.CoinTile.toUInt8 }

/-- the places of the room's walk: those of `EntryBuffer`, and the save of the byte read (its values after the save) -/
def hpX (sy : Syms) (nm : Names) (m0 : Machine) : HP :=
  let read := PipeEntryRule.findOp m0 sy.BlockBufferCollision 0xB1 64
  { EntryBuffer.hpB sy nm m0 with tileI := (romByte m0 (read + 3)).toNat, tileAt := read + 4 }

/-- the walk from the reference `r`, with the known bits of `EntryBuffer` (the room's and the control) -/
abbrev walkE (sy : Syms) (nm : Names) (m0 r : Machine) : Bool :=
  walkCheckX (hpX sy nm m0) (mxOf sy m0) (aidsOf sy nm m0) (optsX (aidsOf sy nm m0) (envR sy nm m0) (EntryBuffer.ctlI nm) (mxOf sy m0))
    (finX (EntryBuffer.ctlI nm) (mxOf sy m0)) (envR sy nm m0) r (EntryBuffer.knownB sy nm m0)

/-- **The check on the ROM**: the walks from the control at 0 (the reference's) and at 6 -/
def endCheck (sy : Syms) (nm : Names) (m0 : Machine) : Bool :=
  walkE sy nm m0 (refR m0) && walkE sy nm m0 (BufferControl.ref6 (EntryBuffer.ctlI nm) (refR m0))

section
variable {sy : Syms} {nmS : Names} {m0 : Machine}

/-- **One frame of the room**: a frame that starts in the room's condition (with the map's bits) and with the control at 0 or 6, with `SiteOK` on each
instruction, and ends with the control at 6, ends with the position from 16 to 180 px -/
theorem end_step (hK : BufferControl.keepCheck sy nmS m0 = true) (hE : endCheck sy nmS m0 = true) {m : Machine} {i : UInt8}
    (hm : RoomCond (envR sy nmS m0) (refR m0) (RoomMap.knownT sy nmS m0) m)
    (hk : ∀ j, SiteOK (placesR sy nmS m0) (trace m i j))
    (hv : m.ram.get! (EntryBuffer.ctlI nmS) = 0 ∨ m.ram.get! (EntryBuffer.ctlI nmS) = 6)
    (h6 : (frame m i).ram.get! (EntryBuffer.ctlI nmS) = 6) :
    16 ≤ ((frame m i).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat ∧ ((frame m i).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat < 181 := by
  obtain ⟨h1, h2, h3, _, _⟩ := BufferControl.keep_parts hK
  simp only [endCheck, Bool.and_eq_true] at hE
  obtain ⟨e1, e2⟩ := hE
  rcases hv with hv | hv
  · exact end_frame (S := hpX sy nmS m0) (M := mxOf sy m0) (walkOKX_of_check e1) h3 (BufferControl.cond0 hm (hv.trans h2.symm)) hk h6
  · have w := walkOKX_of_check (S := hpX sy nmS m0) (M := mxOf sy m0) e2
    have hsz : ((refR m0).ram.set! (EntryBuffer.ctlI nmS) 6).size = 2048 := w.mask.szR
    rw [PipeTransitionAll.ba_size_set] at hsz
    exact end_frame w h3 (BufferControl.cond6 hm h1 (by rw [hsz]; exact h3) hv) hk h6

end

/-! ## The room's frames -/

section
open PipeChangeEnd (Data InRowsT)
variable {sy : Syms} {nm nmS : Names} {d : Data} {e m0 : Machine}

/-- **Every frame of the room that ends with the control at 6 ends with the position from 16 to 180 px**, on the real machines: from the room's first control `b`
(a machine with control in the rows of the time of the first change) before `a`, under the conditions of `RoomMap.map_of_rows` -/
theorem end_of_rows (hF : RoomMap.MapFacts sy nmS m0) (hc : RoomMap.startCheckT sy nm d e nmS m0 = true) (hK : BufferControl.keepCheck sy nmS m0 = true)
    (hs : BufferControl.startCheckC sy nm d e nmS m0 = true) (hE : endCheck sy nmS m0 = true)
    {seq : Nat → Machine} {inp : Nat → UInt8} (next : ∀ n, seq (n + 1) = frame (seq n) (inp n)) {b a : Nat} (hin : InRowsT sy nm d e (seq b))
    (hctl : controllable sy (seq b) = true)
    (sites : ∀ n, b ≤ n → n < a → ∀ j, SiteOK (placesR sy nmS m0) (trace (seq n) (inp n) j))
    (stay : ∀ n, b ≤ n → n < a → (seq n).ram.get! (placesR sy nmS m0).rtI = (refR m0).ram.get! (placesR sy nmS m0).rtI)
    {n : Nat} (h1 : b ≤ n) (h2 : n < a) (h6 : (seq (n + 1)).ram.get! (EntryBuffer.ctlI nmS) = 6) :
    16 ≤ ((seq (n + 1)).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat ∧ ((seq (n + 1)).ram.get! (sy.Player_X_Position &&& 0x7FF).toNat).toNat < 181 := by
  have hcond := RoomMap.cond_of_rows hF hc next hin hctl sites stay n h1 h2
  have hv := BufferControl.ctl_of_rows hF hc hK hs next hin hctl sites stay n h1 (Nat.le_of_lt h2)
  rw [next] at h6 ⊢
  exact end_step hK hE hcond (sites n h1 h2) hv h6

end

/-- what the checks on the ROM give for the screen's first buffer at the side pipe's entry: those of `BufferCoin.FactsB` and the walks of this file.
`Route.RoomChecks.buffer` asks it -/
structure FactsE (sy : Syms) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (nmS : Names) (m0 : Machine) (V : List (Machine × List Nat)) (L : List Nat) : Prop
    extends BufferCoin.FactsB sy nm₁ d₁ nmS m0 V L where
  ends : endCheck sy nmS m0 = true

end Smbrta.BufferEnd
