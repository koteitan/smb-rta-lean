import Theorems.PipeWrites
import Theorems.SideEntryRule
import Theorems.PipeChangeEnd
import Theorems.ScreenPage

/-!
# The side pipe's entry: one whole frame

`SideEntryRule` follows one pass of the side check and assumes the rest of the frame: the write of the routine byte ends a pass that started at the side check (`PassR`), and the position at
the read of the page is the frame's position (`pos`). Here the abstract machine of `PipeWrites` follows the whole frame, from the idle loop before the NMI to the frame's end, with the
conditions `PipeWrites.Clean` on each instruction and `PipeWrites.FrameStart` at the start, as for the vertical pipe.

The walk splits the position where the move ends (`PlayerSubs`), under the hypothesis that it is left of the mouth, and keeps it through the scroll handler, the bounding box, the head's
and the feet's checks to the side check. In the block buffer routine of a side check it splits the high bits of the sum of the height and the adder, so the row of the read is known: no
hypothesis on the row. At the read, the tiles' condition (`TilesOK`) divides the byte read into the pieces of `SideEntryRule`. No path comes to the side pipe's routine.

The guard is that of a frame in the room (`roomG`): the screen's bytes of the room are known at the frame's start and kept from stores with a target not known. Where the
scroll handler asks whether he is off the screen, the walk splits the position into its values, so the store at the screen's edges is followed: it comes only at the left edge,
and there it keeps the position. One place is cut: the routine of the head's collision with a block (`RoomMap` shows that no frame in the room comes to it).
There is no game data in this file. Page: `1-1/c-7-16-SideFrame.md`.
-/

namespace Smbrta.SideFrame

open PipeTransition (frame)
open PipeTransitionAll (go)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top)
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp findStore footStack envOf known_eq sim_setK' forget)
open PoleEntryRule (Spots onCol AtRead TilesOK px ptrAt)
open PipeWrites (Guard Clean FrameStart HypG capT jumpP gsucc okRt inZone normRt colEnd knownOf leK joinK startG zeros fuelG)

/-! ## The places -/

/-- what the walk knows: the guard of the whole frame (its routine is the side pipe's), the places of the side check, and the instruction of the block buffer routine that masks the
sum of the height and the adder -/
structure Side where
  G : Guard
  Q : Spots
  andAt : UInt16
  /-- the scroll handler's call of the routine of the offscreen bits, that routine, and the return from the scroll handler -/
  offAt : UInt16
  offR : UInt16
  back : UInt16
  deriving Inhabited

/-- the places of `SideEntryRule.spots` with the three values of the adders' offset: a big Mario, a big one in the water, a small or crouching one. A side check reads with
an offset of one of them. -/
def spotsF (sy : Syms) (m0 : Machine) : Spots :=
  let ads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 1), romByte m0 (sy.BlockBufferAdderData + 2)]
  { SideEntryRule.spots sy m0 with ads, idx := ads.flatMap fun e => [e + 3, e + 4, e + 5, e + 6] }

/-- the RAM index of the operand of the instruction at `a` -/
def opnd (m0 : Machine) (a : UInt16) : Nat := (((romByte m0 (a + 1)).toUInt16 ||| ((romByte m0 (a + 2)).toUInt16 <<< 8)) &&& 0x7FF).toNat

/-- the bytes of the screen that the scroll handler reads: the scroll lock (the second load of the scroll handler), the left and the right edges' positions and pages (the two
loads by `Y` of the routine of the offscreen bits) -/
def screenI (sy : Syms) (m0 : Machine) : List Nat :=
  let eX := findOp m0 sy.GetXOffscreenBits 0xB9 16
  let eP := findOp m0 (eX + 3) 0xB9 16
  let l1 := findOp m0 (PipeWrites.scrollAt sy m0) 0xAD 16
  let l2 := findOp m0 (l1 + 3) 0xAD 16
  [opnd m0 l2, opnd m0 eX, opnd m0 eX + 1, opnd m0 eP, opnd m0 eP + 1]

/-- these bytes with their values in the room: those of the reference machine of the room (`ScreenPage.refR`) -/
def screenK (sy : Syms) (m0 : Machine) : List (Nat × UInt8) := (screenI sy m0).map fun i => (i, (ScreenPage.refR m0).ram.get! i)

/-- a guard with more bytes known and protected, and its own places cut -/
def extG (G : Guard) (k : List (Nat × UInt8)) (p : List Nat) (c : List UInt16) : Guard := { G with known := G.known ++ k, prot := G.prot ++ p, cuts := c }

/-- **The guard of a frame in the room**: that of the vertical pipe, with the screen's bytes known at the start and kept from stores with a target not known, and the
routine of the head's collision with a block as the one place cut -/
def roomG (sy : Syms) (m0 : Machine) : Guard := extG (PipeWrites.guardOf sy m0) (screenK sy m0) (screenI sy m0) [PipeWrites.headAt sy m0]

/-- **The bump of the head on a solid block**: the collision routine's first store of the vertical speed after its jump to the foot check. The head's check comes there when the
block above the head is solid (or in the water, or while a block bounces): it sets the vertical speed so that the jump stops. With `PipeWrites.headAt` (a brick or a block with an
item) these are the two places where the head's collision changes the vertical motion. -/
def bumpAt (sy : Syms) (m0 : Machine) : UInt16 :=
  findStore m0 (PipeWrites.findJmp m0 sy.PlayerBGCollision sy.DoFootCheck 200) (sy.Player_Y_Speed &&& 0xFF).toUInt8 40

/-- the places, from the symbols and the ROM -/
def sideOf (sy : Syms) (m0 : Machine) : Side :=
  { G := { roomG sy m0 with subs := sy.PlayerSubs, ev := SideEntryRule.vs sy }
    Q := spotsF sy m0
    andAt := findOp m0 (PipeWrites.guardOf sy m0).loadY 0x29 16
    offAt := ScreenPage.findJsr m0 (PipeWrites.scrollAt sy m0) sy.GetXOffscreenBits 200
    offR := sy.GetXOffscreenBits
    back := sy.PlayerSubs + 3 }

/-! ## The pieces -/

/-- the routine reads for a side check: its offset is one of the side check's -/
def sideNow (Q : Spots) (A : AS) : Bool := (A.getK Q.saveI).isK && Q.idx.contains (A.getK Q.saveI).v

/-- the RAM index of the read, with the pointer and `Y` known -/
def readF (Q : Spots) (A : AS) : Nat := ((ptrAt Q A + A.y.v.toUInt16) &&& 0x7FF).toNat

/-- the byte is in the block buffers and not in the pipe's column -/
def safeF (Q : Spots) (i : Nat) : Bool := decide (Q.bufLo ≤ i) && decide (i < Q.bufLo + Q.bufBytes) && !onCol Q i

/-- the values left of `left` on page 0, as a few pieces: for each bit of `left` that is 1, the bits above it as in `left`, that bit 0, the bits below it not known -/
def posPieces (left : Nat) : List AB :=
  (List.range 8).filterMap fun b =>
    if (left / 2 ^ b) % 2 == 1 then
      let hi : UInt8 := (255 - (2 * 2 ^ b - 1) : Nat).toUInt8
      some ⟨left.toUInt8 &&& hi, hi ||| (2 ^ b : Nat).toUInt8⟩
    else none

/-- the byte meets the known bits -/
def memB (a : AB) (x : UInt8) : Bool := x &&& a.k == a.v &&& a.k

/-- every value left of `left` is in a piece -/
def posCover (left : Nat) : Bool := (List.range 256).all fun n => !decide (n < left) || (posPieces left).any fun a => memB a n.toUInt8

/-- the position left of the mouth: page 0, and the pixel in a piece -/
def splitQ (Q : Spots) (A : AS) : List AS :=
  (posPieces Q.left).map fun a => (A.setK Q.xI a).setK Q.pI (AB.known 0)

/-- a byte, by each of its values that meet its known bits -/
def fillB (d : Nat) (A : AS) : List AS :=
  if (A.getK d).isK then [A] else ((List.range 256).filter fun n => memB (A.getK d) n.toUInt8).map fun n => A.setK d (AB.known n.toUInt8)

/-- the high bits of the accumulator -/
def highA (A : AS) : List AS :=
  (PipeChangeEnd.bitA 128 A).flatMap fun B => (PipeChangeEnd.bitA 64 B).flatMap fun C => (PipeChangeEnd.bitA 32 C).flatMap (PipeChangeEnd.bitA 16)

/-- the pieces before a step -/
def zoneF (S : Side) (A : AS) : List AS :=
  if S.G.cuts.contains A.pc then []
  else if A.pc == S.G.subs then splitQ S.Q A
  else if A.pc == S.offAt && (A.getK S.Q.xI).k != 0 then fillB S.Q.xI A
  else if A.pc == S.Q.adc && sideNow S.Q A then fillB S.Q.xI A
  else if A.pc == S.andAt && sideNow S.Q A then highA A
  else if A.pc == S.Q.read && sideNow S.Q A && (A.getK S.Q.ptrI).isK && (A.getK (S.Q.ptrI + 1)).isK && A.y.isK && safeF S.Q (readF S.Q A) then
    (SideEntryRule.pieces S.Q).map fun a => A.setK (readF S.Q A) a
  else [A]

/-- all the pieces before a step -/
def preF (S : Side) (A : AS) : List AS := (jumpP S.G (capT S.G A)).flatMap (zoneF S)

/-- what the frame asks of one state: left of the mouth at the end of the move, the tiles at a read, no place of the cuts -/
def HypF (S : Side) (m : Machine) : Prop :=
  (m.pc = S.G.subs → px S.Q m < S.Q.left) ∧ (AtRead S.Q m → TilesOK S.Q m) ∧ m.pc ∉ S.G.cuts

/-! ## The walk -/

/-- the bytes kept apart in the collision routine -/
def keepF (S : Side) : List Nat := [S.G.yI, S.Q.adI, S.Q.saveI, S.Q.ptrI, S.Q.ptrI + 1, S.Q.xI, S.Q.pI, S.Q.cntI, S.Q.tempI]

/-- the piece of the position that holds this value -/
def pieceOf (Q : Spots) (x : AB) : AB :=
  if x.isK then (match (posPieces Q.left).find? (fun a => memB a x.v) with
    | some a => a
    | none => x) else x

/-- what the search forgets: no part of the proof -/
def normF (S : Side) (A0 : AS) : AS :=
  let G := S.G
  let Q := S.Q
  let A := normRt G { A0 with padShift := AB.top }
  let keepP := Q.xI :: Q.pI :: G.prot
  if !inZone G A then
    if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
    let B := PipeWrites.AS.forgetW keepP A
    let B := if A.pc == colEnd G then forget [Q.xI, Q.pI] B else B
    let B := if A.pc == S.back then B.setK Q.xI (pieceOf Q (B.getK Q.xI)) else B
    let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
    { B with kn }
  else if Q.exits.contains A.pc then { PipeWrites.AS.forgetW G.prot A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == Q.side then { PipeWrites.AS.forgetW keepP A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == S.andAt then (forget [Q.sumI] A).setK Q.xI (pieceOf Q (A.getK Q.xI))
  else if A.pc == Q.read + 2 then { forget [Q.ptrI, Q.ptrI + 1] A with y := AB.top }
  else A

/-- states with the same key are joined: no part of the proof -/
def keyF (S : Side) (A : AS) : Nat :=
  let G := S.G
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := num (A.getK G.rtI)
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0)
  let n :=
    if inZone G A then
      let n := n * 65536 + num A.x
      let n := n * 65536 + num A.y
      let n := n * 65536 + num A.a
      let n := n * 65536 + num (A.p.and (AB.known 1))
      (keepF S).foldl (fun n i => n * 65536 + num (A.getK i)) n
    else if G.je ≤ A.pc && A.pc ≤ G.je + 18 then
      let n := n * 65536 + num A.a
      n * 65536 + num A.y
    else if A.pc != colEnd G then
      let n := (n * 65536 + num (A.getK S.Q.xI)) * 65536 + num (A.getK S.Q.pI)
      -- with the position whole in the scroll handler's question whether he is off the screen, the registers and the carry too: its loop must not join its two passes
      if (A.getK S.Q.xI).k == 255 && ((S.offR ≤ A.pc && A.pc < S.offR + 0x90) || (S.offAt ≤ A.pc && A.pc < S.offAt + 0x40)) then
        (((n * 65536 + num A.x) * 65536 + num A.y) * 65536 + num A.a) * 65536 + num (A.p.and (AB.known 1))
      else n
    else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + TaintRun.stackHash A

/-- the table -/
structure CfgF where
  E : Env
  ops : Array (AM Unit)
  S : Side
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  cut : ByteArray

/-- the state whose key the table is looked up by: as the search normalized it (no part of the proof: any entry found must still be above the state) -/
def keyOf (S : Side) (B : AS) : AS :=
  if inZone S.G B then normF S B
  else
    let A := normRt S.G B
    if B.pc == S.back then A.setK S.Q.xI (pieceOf S.Q (A.getK S.Q.xI)) else A

def coverF (C : CfgF) (B : AS) : Bool :=
  match C.idx[keyF C.S (keyOf C.S B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path ends at the frame's end or in a state of the table. Everywhere the routine byte is not the side pipe's. -/
def walkF (C : CfgF) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preF C.S A).all fun A₁ => (gsucc C.S.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.S.G B && (B.k != A.k || (C.cut.get! B.pc.toNat != 0 && coverF C B) || walkF C n B)

/-! ## Finding the table: a search, no part of the proof -/

def isCutF (S : Side) (pc : UInt16) : Bool :=
  pc == S.Q.read || pc == S.Q.read + 2 || pc == S.andAt || pc == S.Q.side || pc == S.Q.adc || S.Q.exits.contains pc || pc == S.back

def routeF (S : Side) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := S.G
  let B := normF S B0
  let K := keyF S B
  let X := if isCutF S B.pc then { X with multi := X.multi.insert K () } else X
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runF (S : Side) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := S.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preF S cur).flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutF S b.pc && b.pc != G.je && b.pc != G.subs &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeF S X b
    break
  return X

partial def searchF (S : Side) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runF S E ops X A
  return X

def searchOf (S : Side) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchF S E ops ([startG S.G false, startG S.G true].foldl (routeF S) {})

def cfgOf (S : Side) (E : Env) : CfgF :=
  let q := PipeWrites.tableOfS (searchOf S E)
  { E, ops := (aRows E).toArray, S, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- **The check.** -/
def frameCheck (S : Side) (E : Env) : Bool :=
  let C := cfgOf S E
  let G := S.G
  decide (G.rtI < 2048) && decide (S.Q.xI < 2048) && decide (S.Q.pI < 2048) && decide (S.Q.saveI < 2048) && decide (S.Q.ptrI < 2048) &&
  decide (S.Q.left < 256) && posCover S.Q.left && SideEntryRule.piecesCover S.Q &&
  decide (G.late < dotsPerFrame) && okRt G (startG G false) && okRt G (startG G true) &&
  C.t.all (walkF C fuelG) && walkF C fuelG (startG G false) && walkF C fuelG (startG G true)

/-- **The check on the ROM.** -/
def sideFrameCheck (sy : Syms) (m0 : Machine) : Bool := sy.PlayerSubs != 0 && frameCheck (sideOf sy m0) (envOf m0)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem memB_iff {a : AB} {x : UInt8} : memB a x = true ↔ a.mem x := by
  simp [memB, AB.mem]

/-- a value left of `left` is in a piece -/
theorem pos_piece {left : Nat} (hc : posCover left = true) {x : UInt8} (hx : x.toNat < left) : ∃ a ∈ posPieces left, a.mem x := by
  simp only [posCover, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true] at hc
  rcases hc x.toNat x.toNat_lt with h | ⟨a, ha, h⟩
  · exact absurd hx h
  · have hv : x.toNat.toUInt8 = x := by simp
    rw [hv] at h
    exact ⟨a, ha, memB_iff.1 h⟩

/-- the split of the position covers a machine left of the mouth -/
theorem cov_splitQ {Q : Spots} {A : AS} {m : Machine} (hl : Q.left < 256) (hc : posCover Q.left = true) (hlt : px Q m < Q.left) (hs : Sim E F A m) :
    ∃ B ∈ splitQ Q A, Sim E F B m := by
  unfold px at hlt
  have hp : m.ram.get! Q.pI = 0 := by
    have h1 : (m.ram.get! Q.pI).toNat = 0 := by omega
    exact UInt8.toNat_inj.1 (by rw [h1]; rfl)
  obtain ⟨a, ha, hm⟩ := pos_piece hc (x := m.ram.get! Q.xI) (by omega)
  refine ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
  refine sim_setK' (sim_setK' hs hm) ?_
  rw [hp]
  exact mem_known_self _

/-- the split of a byte by its values covers every machine -/
theorem cov_fill {d : Nat} (hd : d < 2048) : TaintRun.Cov E F (fillB d) := by
  intro A m hs
  unfold fillB
  by_cases h : (A.getK d).isK = true
  · rw [if_pos h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · rw [if_neg h]
    have hm : (A.getK d).mem (m.ram.get! d) := hs.ram d hd
    have hv : (m.ram.get! d).toNat.toUInt8 = m.ram.get! d := by simp
    refine ⟨_, List.mem_map.2 ⟨(m.ram.get! d).toNat, List.mem_filter.2 ⟨List.mem_range.2 (m.ram.get! d).toNat_lt, ?_⟩, rfl⟩, ?_, rfl⟩
    · rw [hv]
      exact memB_iff.2 hm
    · refine sim_setK' hs ?_
      rw [hv]
      exact mem_known_self _

/-- the split of the accumulator's high bits covers every machine -/
theorem cov_highA : TaintRun.Cov E F highA := by
  have c1 : TaintRun.Cov E F (PipeChangeEnd.bitA 128) := PipeChangeEnd.cov_bitA (by decide)
  have c2 : TaintRun.Cov E F (PipeChangeEnd.bitA 64) := PipeChangeEnd.cov_bitA (by decide)
  have c3 : TaintRun.Cov E F (PipeChangeEnd.bitA 32) := PipeChangeEnd.cov_bitA (by decide)
  have c4 : TaintRun.Cov E F (PipeChangeEnd.bitA 16) := PipeChangeEnd.cov_bitA (by decide)
  exact PipeWrites.cov_then c1 (PipeWrites.cov_then c2 (PipeWrites.cov_then c3 c4))

/-- what the pieces need from the check -/
structure PreF (S : Side) : Prop where
  xI : S.Q.xI < 2048
  pI : S.Q.pI < 2048
  left : S.Q.left < 256
  pos : posCover S.Q.left = true
  cover : SideEntryRule.piecesCover S.Q = true

theorem cov_zoneF {S : Side} {A : AS} {m : Machine} (hb : PreF S) (hh : HypF S m) (hs : Sim E F A m) : ∃ B ∈ zoneF S A, Sim E F B m := by
  obtain ⟨hS, hT, hC⟩ := hh
  unfold zoneF
  by_cases h0 : S.G.cuts.contains A.pc = true
  · exfalso
    apply hC
    rw [hs.pc]
    exact List.mem_of_elem_eq_true h0
  rw [if_neg h0]
  by_cases h1 : (A.pc == S.G.subs) = true
  · rw [if_pos h1]
    exact cov_splitQ hb.left hb.pos (hS (by rw [hs.pc]; exact beq_iff_eq.1 h1)) hs
  rw [if_neg h1]
  by_cases h1o : (A.pc == S.offAt && (A.getK S.Q.xI).k != 0) = true
  · rw [if_pos h1o]
    obtain ⟨B, hB, h3, _⟩ := cov_fill hb.xI A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h1o]
  by_cases h1a : (A.pc == S.Q.adc && sideNow S.Q A) = true
  · rw [if_pos h1a]
    obtain ⟨B, hB, h3, _⟩ := cov_fill hb.xI A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h1a]
  by_cases h2 : (A.pc == S.andAt && sideNow S.Q A) = true
  · rw [if_pos h2]
    obtain ⟨B, hB, h3, _⟩ := cov_highA A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h2]
  by_cases h3 : (A.pc == S.Q.read && sideNow S.Q A && (A.getK S.Q.ptrI).isK && (A.getK (S.Q.ptrI + 1)).isK && A.y.isK && safeF S.Q (readF S.Q A)) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨⟨⟨⟨h4, _⟩, _⟩, _⟩, _⟩, h9⟩ := h3
    have hpc : m.pc = S.Q.read := by rw [hs.pc]; exact h4
    have htiles := hT hpc
    simp only [safeF, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h9
    obtain ⟨⟨h10, h11⟩, h12⟩ := h9
    have key : ∀ v, (v = S.Q.ball ∨ v = S.Q.shaft) → m.ram.get! (readF S.Q A) = v → False := by
      intro v hv he
      have ht := htiles _ h10 h11 (by rw [he]; exact hv)
      rw [ht.1] at h12
      cases h12
    obtain ⟨a, ha1, ha2⟩ := SideEntryRule.tile_piece hb.cover (fun he => key _ (Or.inl rfl) he) (fun he => key _ (Or.inr rfl) he)
    exact ⟨_, List.mem_map.2 ⟨a, ha1, rfl⟩, sim_setK' hs ha2⟩
  · rw [if_neg h3]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

/-- every machine that meets the conditions is in a piece -/
theorem cov_preF {S : Side} {A : AS} {m : Machine} (hb : PreF S) (hc : Clean S.G m) (hh : HypF S m) (hs : Sim E F A m) :
    ∃ B ∈ preF S A, Sim E F B m := by
  obtain ⟨B, hB, h1⟩ := PipeWrites.cov_jump hc (PipeWrites.sim_cap hc hs)
  obtain ⟨D, hD, h2⟩ := cov_zoneF hb hh h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2⟩

end

/-! ## The walk covers the machine -/

section
variable {C : CfgF} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveF (C : CfgF) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkF C n A = true

theorem cover_liveF (ht : C.t.all (walkF C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0) (h : coverF C B = true) : ∃ D, LiveF C F D m := by
  unfold coverF at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := PipeWrites.leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := PipeWrites.le_k hle
        omega
      exact ⟨D, TaintRun.sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

theorem live_stepF (ht : C.t.all (walkF C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : PreF C.S) (hr : C.S.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveF C F A m) (hc : Clean C.S.G m) (hh : HypF C.S m) :
    (go step m).2.ram.get! C.S.G.rtI ≠ C.S.G.ev ∧ (F.1 < (go step m).2.frame ∨ ∃ A', LiveF C F A' (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkF] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_preF hb hc hh hs
    obtain ⟨r, hr1, hB⟩ := PipeWrites.s_gsucc hops hT hc hs1
    simp only [walkF, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hw2
      obtain ⟨h2, h3⟩ := hw2
      refine ⟨PipeWrites.ne_of_okRt h2 (h1.ram _ hr), ?_⟩
      by_cases hk2 : B.k = 0
      · right
        rcases h3 with (h4 | ⟨_, h4⟩) | h4
        · rw [hk, hk2] at h4
          exact absurd rfl h4
        · exact cover_liveF ht hkl h1 hk2 h4
        · exact ⟨B, h1, hk2, n, h4⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The frame -/

/-- what the check says -/
structure FrameOK (S : Side) (E : Env) : Prop where
  rt : S.G.rtI < 2048
  pre : PreF S
  ok0 : okRt S.G (startG S.G false) = true
  ok1 : okRt S.G (startG S.G true) = true
  table : (cfgOf S E).t.all (walkF (cfgOf S E) fuelG) = true
  s0 : walkF (cfgOf S E) fuelG (startG S.G false) = true
  s1 : walkF (cfgOf S E) fuelG (startG S.G true) = true

theorem frameOK_of_check {S : Side} {E : Env} (h : frameCheck S E = true) : FrameOK S E := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, h6⟩, h6a⟩, h7⟩, _⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, ⟨h2, h3, h6, h6a, h7⟩, h9, h10, h11, h12, h13⟩

/-- **The frame.** From a `FrameStart`, while each instruction is `Clean` and meets `HypF`, the routine byte does not become the side pipe's. -/
theorem no_write_frame {S : Side} {E : Env} (hc : frameCheck S E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart S.G E (s 0))
    (hh : ∀ j, j ≤ n → Clean S.G (s j) ∧ HypF S (s j)) : (s (n + 1)).ram.get! S.G.rtI ≠ S.G.ev := by
  have hC := frameOK_of_check hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOf S E).kl = (cfgOf S E).t.map knownOf := rfl
  have hstart : ∃ A, LiveF (cfgOf S E) ((s 0).frame, 2) A (s 0) := by
    cases b with
    | false => exact ⟨_, hsim, rfl, fuelG, hC.s0⟩
    | true => exact ⟨_, hsim, rfl, fuelG, hC.s1⟩
  have live : ∀ j, j ≤ n → ∃ A, LiveF (cfgOf S E) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => hstart
    | succ j ih =>
      intro hj
      obtain ⟨A, hA⟩ := ih (by omega)
      obtain ⟨hh1, hh2⟩ := hh j (by omega)
      obtain ⟨_, h2⟩ := live_stepF hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.pre hC.rt hA hh1 hh2
      rw [← hs j (by omega)] at h2
      rcases h2 with h2 | h2
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := h2
        omega
      · exact h2
  obtain ⟨A, hA⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hh2⟩ := hh n (Nat.le_refl n)
  obtain ⟨h1, _⟩ := live_stepF hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.pre hC.rt hA hh1 hh2
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-- before the write the frame goes on -/
theorem frame_before {sy : Syms} {m : Machine} {i : UInt8} {n : Nat} (h : SideEntryRule.WriteStep sy m i n) : ∀ j, j ≤ n → (trace m i j).frame ≤ m.frame := by
  intro j hj
  by_cases hg : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
    have e1 := trace_stop hg k
    have e2 := trace_stop hg (k + 1)
    apply h.1
    rw [e1, ← e2]
    exact h.2
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hg
    omega

/-- the conditions of a guard do not depend on its routine -/
theorem clean_ev {G : Guard} {e : UInt8} {m : Machine} (h : Clean G m) : Clean { G with ev := e } m := ⟨h.store, h.read, h.jump, h.time⟩

theorem start_ev {G : Guard} {e : UInt8} {E : Env} {m : Machine} (h : FrameStart G E m) : FrameStart { G with ev := e } E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- the conditions of a guard do not depend on the place of the split and its routine -/
theorem clean_subsEv {G : Guard} {s : UInt16} {e : UInt8} {m : Machine} (h : Clean G m) : Clean { G with subs := s, ev := e } m := ⟨h.store, h.read, h.jump, h.time⟩

theorem start_subsEv {G : Guard} {s : UInt16} {e : UInt8} {E : Env} {m : Machine} (h : FrameStart G E m) : FrameStart { G with subs := s, ev := e } E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- a guard with more bytes known and protected asks more -/
theorem clean_less {G : Guard} {k : List (Nat × UInt8)} {p : List Nat} {c : List UInt16} {m : Machine} (h : Clean (extG G k p c) m) :
    Clean G m := by
  refine ⟨fun t ht => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht with ⟨a, b⟩ | b
  · exact Or.inl ⟨a, fun hm => b (List.mem_append_left _ hm)⟩
  · exact Or.inr b

theorem start_less {G : Guard} {k : List (Nat × UInt8)} {p : List Nat} {c : List UInt16} {E : Env} {m : Machine}
    (h : FrameStart (extG G k p c) E m) : FrameStart G E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, fun q hq => h.known q (List.mem_append_left _ hq)⟩

/-- the conditions of the room's guard are those of the side pipe's -/
theorem clean_side {sy : Syms} {m0 m : Machine} (h : Clean (roomG sy m0) m) : Clean (sideOf sy m0).G m :=
  clean_subsEv (G := roomG sy m0) (s := sy.PlayerSubs) (e := SideEntryRule.vs sy) h

theorem start_side {sy : Syms} {m0 : Machine} {E : Env} {m : Machine} (h : FrameStart (roomG sy m0) E m) : FrameStart (sideOf sy m0).G E m :=
  start_subsEv (G := roomG sy m0) (s := sy.PlayerSubs) (e := SideEntryRule.vs sy) h

/-- the room's guard asks more than the vertical pipe's -/
theorem clean_guardOf {sy : Syms} {m0 m : Machine} (h : Clean (roomG sy m0) m) : Clean (PipeWrites.guardOf sy m0) m :=
  clean_less (G := PipeWrites.guardOf sy m0) (k := screenK sy m0) (p := screenI sy m0) (c := [PipeWrites.headAt sy m0]) h

theorem start_guardOf {sy : Syms} {m0 : Machine} {E : Env} {m : Machine} (h : FrameStart (roomG sy m0) E m) : FrameStart (PipeWrites.guardOf sy m0) E m :=
  start_less (G := PipeWrites.guardOf sy m0) (k := screenK sy m0) (p := screenI sy m0) (c := [PipeWrites.headAt sy m0]) h

/-- **The side pipe's entry on a real frame, at the end of the move.** If the frame enters, it starts in control with the screen's bytes of the room, its instructions up to the write
are `Clean`, each read of the block buffer routine up to the write meets `TilesOK`, and it does not come to the routine of the head's collision with a block, then at the end of the
move, before the write, the position is at or right of the mouth's left end. -/
theorem entry_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : sideFrameCheck sy m0 = true) (he : SideEntryRule.Enters sy m i)
    (h0 : FrameStart (roomG sy m0) (envOf m0) m)
    (hp : ∀ n, SideEntryRule.WriteStep sy m i n → ∀ j, j ≤ n → Clean (roomG sy m0) (trace m i j) ∧
      (AtRead (SideEntryRule.spots sy m0) (trace m i j) → TilesOK (SideEntryRule.spots sy m0) (trace m i j)) ∧
      (trace m i j).pc ≠ PipeWrites.headAt sy m0) :
    ∃ n j, SideEntryRule.WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ SidePipe.xLo sy ≤ px (SideEntryRule.spots sy m0) (trace m i j) := by
  simp only [sideFrameCheck, Bool.and_eq_true, bne_iff_ne] at hc
  obtain ⟨_, hc⟩ := hc
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ SidePipe.xLo sy ≤ px (SideEntryRule.spots sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frame (S := sideOf sy m0) (s := trace m i) (n := n) hc rfl (fun j hj => SideEntryRule.step_before hw j hj)
      (fun j hj => frame_before hw j hj) (start_side (h0.pad _))
      (fun j hj => ⟨clean_side (hp n hw j hj).1, fun hs => by
        show px (SideEntryRule.spots sy m0) (trace m i j) < SidePipe.xLo sy
        by_cases hl : SidePipe.xLo sy ≤ px (SideEntryRule.spots sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, (hp n hw j hj).2.1, by
        show (trace m i j).pc ∉ [PipeWrites.headAt sy m0]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact (hp n hw j hj).2.2⟩)
    exact hn hw.2

/-- **At the mouth, from one whole frame.** `P` is the position at the end of the move before the write (`moved`). A frame that enters, under the conditions of `entry_right_of_left`, has
`P` at or right of the mouth's left end. -/
theorem mouth_of_frame {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : sideFrameCheck sy m0 = true) (he : SideEntryRule.Enters sy m i)
    (h0 : FrameStart (roomG sy m0) (envOf m0) m)
    (hp : ∀ n, SideEntryRule.WriteStep sy m i n → ∀ j, j ≤ n → Clean (roomG sy m0) (trace m i j) ∧
      (AtRead (SideEntryRule.spots sy m0) (trace m i j) → TilesOK (SideEntryRule.spots sy m0) (trace m i j)) ∧
      (trace m i j).pc ≠ PipeWrites.headAt sy m0)
    (hmoved : ∀ n j, SideEntryRule.WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SidePipe.mouthP sy 0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := entry_right_of_left hc he h0 hp
  rw [hmoved n j h1 h2 h3]
  have h7 : (SideEntryRule.spots sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (SideEntryRule.spots sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h7, h8] at h4
  unfold SidePipe.mouthP posP peek
  omega

/-! ## On real frames: a program, no part of the proof -/

/-- what real frames say about the hypotheses -/
structure Report where
  frames : Nat := 0
  /-- frames in control, and how many do not meet `FrameStart`; instructions of them that are not `Clean`; reads of the block buffer routine not `TilesOK`; frames that come to a cut place -/
  ctl : Nat := 0
  startBad : Nat := 0
  instrs : Nat := 0
  cleanBad : Nat := 0
  reads : Nat := 0
  tilesBad : Nat := 0
  cutFrames : Nat := 0
  /-- frames that enter; of them: not `FrameStart`; an instruction up to the write not `Clean`; a read up to it not `TilesOK`; a cut place before it; not the write `w`; not one arrival at
  the end of the move before it; the position there left of the mouth; the position there is not the frame's end position (`moved`); the position at a read of the page in the
  side check is not the one at the end of the move -/
  entries : Nat := 0
  eStart : Nat := 0
  eClean : Nat := 0
  eTiles : Nat := 0
  eCut : Nat := 0
  writeBad : Nat := 0
  subsN : Nat := 0
  leftBad : Nat := 0
  movedBad : Nat := 0
  pageBad : Nat := 0
  pxs : List Nat := []
  /-- frames in control that come to the bump on a solid block -/
  bumpN : Nat := 0
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, in control {r.ctl} (not FrameStart {r.startBad}), instructions {r.instrs} (not Clean {r.cleanBad}), reads {r.reads} (not TilesOK {r.tilesBad}), frames at a cut place {r.cutFrames}; entries {r.entries} (not FrameStart {r.eStart}, not Clean {r.eClean}, not TilesOK {r.eTiles}, at a cut place {r.eCut}, not the write {r.writeBad}, not one arrival at the end of the move {r.subsN}, left of the mouth there {r.leftBad}, moved {r.movedBad}, the page read elsewhere {r.pageBad}), positions {r.pxs.eraseDups.mergeSort}; frames at the bump on a solid block {r.bumpN}"

def Report.bad (r : Report) : Nat := r.startBad + r.cleanBad + r.tilesBad + r.eStart + r.eClean + r.eTiles + r.eCut + r.writeBad + r.subsN + r.leftBad + r.movedBad + r.pageBad

/-- one real frame with the bits `pad` of the controller. `G` is the room's guard (`roomG`, computed once by the caller): its conditions are those of `sideOf`. The cut places counted are the routine of the head's
collision and, apart, the scroll handler's store at the edges, which the walk no longer cuts. Apart, the frames that come to the bump on a solid block (`bumpAt`, which the walk of the
room's frames cuts; not in `bad`). -/
def scanFrame (sy : Syms) (m0 : Machine) (G : Guard) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let Q := SideEntryRule.spots sy m0
  let E := envOf m0
  let cuts := [PipeWrites.edgeStore sy m0, PipeWrites.headAt sy m0]
  let bump := bumpAt sy m0
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let ctl := controllable sy m
  let startOk := PipeWrites.startB G E c
  let mut r := { r0 with frames := r0.frames + 1, ctl := r0.ctl + (if ctl then 1 else 0), startBad := r0.startBad + (if ctl && !startOk then 1 else 0) }
  let mut clean := true
  let mut tiles := true
  let mut cutSeen := false
  let mut bumpSeen := false
  let mut subs : List Machine := []
  let mut pages : List Nat := []
  let mut entered := false
  let mut atSubs : Option Machine := none
  let mut n := 0
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if c.pc == bump then bumpSeen := true
    if !entered then
      if cuts.contains c.pc then cutSeen := true
      if c.pc == sy.PlayerSubs then subs := c :: subs
      if c.pc == Q.entry && Q.idx.contains c.y && c.x == 0 then pages := px Q c :: pages
    let (a, b, j, d) := PipeWrites.cleanB G c
    let ok := a && b && j && d
    if ctl then r := { r with instrs := r.instrs + 1, cleanBad := r.cleanBad + (if ok then 0 else 1) }
    if !ok && !entered then clean := false
    if c.pc == Q.read then
      let x := PoleEntryRule.tilesOK Q c
      if ctl then r := { r with reads := r.reads + 1, tilesBad := r.tilesBad + (if x then 0 else 1) }
      if !x && !entered then tiles := false
    let before := rt sy c
    let pc := c.pc
    c := (go step c).2
    if before != SideEntryRule.vs sy && rt sy c == SideEntryRule.vs sy && !entered then
      entered := true
      atSubs := subs.head?
      r := { r with
        entries := r.entries + 1
        eStart := r.eStart + (if startOk then 0 else 1)
        eClean := r.eClean + (if clean then 0 else 1)
        eTiles := r.eTiles + (if tiles then 0 else 1)
        eCut := r.eCut + (if cutSeen then 1 else 0)
        writeBad := r.writeBad + (if pc == Q.write then 0 else 1)
        subsN := r.subsN + (if subs.length == 1 then 0 else 1) }
      match subs.head? with
      | some u =>
        r := { r with leftBad := r.leftBad + (if px Q u < Q.left then 1 else 0), pxs := px Q u :: r.pxs,
                      pageBad := r.pageBad + (if pages.all (· == px Q u) then 0 else 1) }
      | none => pure ()
    n := n + 1
  if ctl && cutSeen then r := { r with cutFrames := r.cutFrames + 1 }
  if ctl && bumpSeen then r := { r with bumpN := r.bumpN + 1 }
  match atSubs with
  | some u => if posP sy u != posP sy c then r := { r with movedBad := r.movedBad + 1 }
  | none => pure ()
  return (r, c)

end Smbrta.SideFrame
