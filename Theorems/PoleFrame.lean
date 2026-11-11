import Theorems.SideFrame
import Theorems.FrameKeep

/-!
# The touch of the pole: one whole frame

`PoleEntryRule` follows one pass of the side check and assumes the rest of the frame: the write of the routine byte ends a pass that started at the side check (`Pass`), and the position at
the read of the page is the frame's position (`pos`). Here the abstract machine follows the whole frame of the touch, from the idle loop before the NMI to the frame's end, as
`SideFrame` does for the side pipe. Its steps are those of `FrameKeep` (`kstep`), so the condition on each instruction is `FrameKeep.CleanK`, and the frame starts as `FrameKeep.StartK`
asks: both are what the frames of `PoleJoin.Run.keep` give.

The walk splits the position where the move ends (`PlayerSubs`), under the hypothesis that it is left of the pole's range: a page two or more before the pole's (a few pieces), the page
before the pole's, or the pole's page with the pixel left of the left end (a few pieces). It keeps the position through the scroll handler, the bounding box, the head's and the feet's
checks to the side check. In a side check near the pole (the page is the pole's or the one before) it splits the pixel at the addition, and the high bits of the sum of the height and
the adder, so the place of the read is known. After a read of the side check, the byte read is not one of the pole's tiles, unless it is in the pole's column with the page at most one
before the pole's (`TileRead`). Then the comparisons of the climbing code do not come to the write. In the pole's column the pixel's low 4 bits make the climbing code leave.
No path makes the routine byte the pole's.

The two places of `PipeWrites.guardS` are cut: the scroll handler's store of the position at the screen's edges, and the routine of the head's collision with a block.
There is no game data in this file. Page: `1-1/f-6-16-PoleFrame.md`.
-/

namespace Smbrta.PoleFrame

open PipeTransition (frame)
open PipeTransitionAll (go)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top)
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp findStore footStack envOf known_eq sim_setK' forget)
open PoleEntryRule (Spots onCol px ptrAt vf WriteStep Touches)
open PipeWrites (Guard FrameStart okRt inZone normRt colEnd knownOf leK joinK startG zeros fuelG)
open FrameKeep (CleanK kstep preK)
open SideFrame (posPieces posCover memB fillB highA sideNow readF pos_piece cov_fill cov_highA)

/-! ## The places -/

/-- what the walk knows: the guard of the whole frame (its routine is the pole's), the move routine of `FrameKeep`, the places of the side check, and the instruction of the block
buffer routine that masks the sum of the height and the adder -/
structure Pole where
  G : Guard
  K : FrameKeep.Spot
  Q : Spots
  andAt : UInt16
  deriving Inhabited

/-- the places of `PoleEntryRule.spots` with the three values of the adders' offset: a big Mario, a big one in the water, a small or crouching one -/
def spotsF (sy : Syms) (m0 : Machine) : Spots :=
  let ads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 1), romByte m0 (sy.BlockBufferAdderData + 2)]
  { PoleEntryRule.spots sy m0 with ads, idx := ads.flatMap fun e => [e + 3, e + 4, e + 5, e + 6] }

/-- the guard of `FrameKeep` with the pole's routine, the split at the end of the move, and the two places cut of `PipeWrites.guardS` -/
def guardT (sy : Syms) (m0 : Machine) : Guard :=
  { FrameKeep.guardK sy m0 with ev := vf sy, subs := sy.PlayerSubs, cuts := [PipeWrites.edgeStore sy m0, PipeWrites.headAt sy m0] }

/-- the places, from the symbols and the ROM -/
def poleOf (sy : Syms) (m0 : Machine) : Pole :=
  { G := guardT sy m0
    K := FrameKeep.spotOf sy m0
    Q := spotsF sy m0
    andAt := findOp m0 (FrameKeep.guardK sy m0).loadY 0x29 16 }

/-! ## The conditions on one state -/

/-- the RAM index that the block buffer routine's read takes: its pointer plus `Y` -/
def readAt (Q : Spots) (m : Machine) : Nat :=
  ((((m.ram.get! Q.ptrI).toUInt16 ||| ((m.ram.get! (Q.ptrI + 1)).toUInt16 <<< 8)) + m.y.toUInt16) &&& 0x7FF).toNat

/-- **What stays assumed about a read.** Just after a read of the block buffer routine for a side check, if the byte read is one of the pole's tiles, then it was read in the pole's
column, and the page is at most one before the pole's. -/
def TileRead (Q : Spots) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.a = Q.ball ∨ m.a = Q.shaft) → onCol Q (readAt Q m) = true ∧ Q.pg ≤ (m.ram.get! Q.pI).toNat + 1

/-- what the frame asks of one state: left of the pole's range at the end of the move, `TileRead`, no place of the cuts -/
def HypT (T : Pole) (m : Machine) : Prop :=
  (m.pc = T.G.subs → px T.Q m < T.Q.left) ∧ TileRead T.Q m ∧ m.pc ∉ T.G.cuts

/-! ## The pieces -/

/-- the pixel of the left end on the pole's page -/
def lowOf (Q : Spots) : Nat := Q.left - 256 * Q.pg

/-- the position left of the pole's range: a page two or more before the pole's (as a few pieces), the page before the pole's, or the pole's page with the pixel in a piece -/
def splitL (Q : Spots) (A : AS) : List AS :=
  (posPieces (Q.pg - 1)).map (fun a => A.setK Q.pI a) ++ [A.setK Q.pI (AB.known (Q.pg - 1).toUInt8)] ++
    (posPieces (lowOf Q)).map fun a => (A.setK Q.xI a).setK Q.pI (AB.known Q.pg.toUInt8)

/-- the page may be the pole's or the one before -/
def nearP (Q : Spots) (A : AS) : Bool := decide (Q.pg ≤ (A.getK Q.pI).maxv.toNat + 1)

/-- the byte read cannot be the pole's tile: the page is two or more before the pole's, or the place of the read is known and not in the pole's column -/
def offTile (Q : Spots) (A : AS) : Bool :=
  !nearP Q A || ((A.getK Q.ptrI).isK && (A.getK (Q.ptrI + 1)).isK && A.y.isK && !onCol Q (readF Q A))

/-- the pieces before a step -/
def zoneT (T : Pole) (A : AS) : List AS :=
  if T.G.cuts.contains A.pc then []
  else if A.pc == T.G.subs then splitL T.Q A
  else if A.pc == T.Q.adc && sideNow T.Q A && nearP T.Q A then fillB T.Q.xI A
  else if A.pc == T.andAt && sideNow T.Q A && nearP T.Q A then highA A
  else if A.pc == T.Q.read + 2 && sideNow T.Q A && offTile T.Q A then T.Q.bits.map fun b => { A with a := PipeEntryRule.neBit T.Q.ball b }
  else [A]

/-- all the pieces before a step: those of `FrameKeep`, then these -/
def preT (T : Pole) (A : AS) : List AS := (preK T.K T.G A).flatMap (zoneT T)

/-! ## The walk -/

/-- the bytes kept apart in the collision routine -/
def keepT (T : Pole) : List Nat := [T.G.yI, T.Q.adI, T.Q.saveI, T.Q.ptrI, T.Q.ptrI + 1, T.Q.xI, T.Q.pI, T.Q.cntI, T.Q.tempI, T.Q.sumI]

/-- the piece of the position that holds this pixel, for the page: no part of the proof -/
def pieceOfT (Q : Spots) (x p : AB) : AB :=
  if x.isK && p.isK && p.v.toNat == Q.pg then
    (match (posPieces (lowOf Q)).find? (fun a => memB a x.v) with
    | some a => a
    | none => x)
  else if p.isK && p.v.toNat + 1 == Q.pg then AB.top
  else x

/-- the sum is in the pole's column on its page: no part of the proof -/
def onColSum (Q : Spots) (A : AS) : Bool :=
  let s := A.getK Q.sumI
  s.isK && s.v >>> 4 == Q.col && (A.getK Q.pI).isK && (A.getK Q.pI).v.toNat == Q.pg

/-- what the search forgets: no part of the proof -/
def normT (T : Pole) (A0 : AS) : AS :=
  let G := T.G
  let Q := T.Q
  let A := normRt G { A0 with padShift := AB.top }
  let keepP := Q.xI :: Q.pI :: G.prot
  if !inZone G A then
    if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
    let keep := if FrameKeep.inMove T.K A.pc then T.K.temps ++ keepP else keepP
    let B := PipeWrites.AS.forgetW keep A
    let B := if A.pc == colEnd G then forget [Q.xI, Q.pI] B else B
    let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
    { B with kn }
  else if Q.exits.contains A.pc then { PipeWrites.AS.forgetW G.prot A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == Q.side then { PipeWrites.AS.forgetW keepP A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == T.andAt then
    if onColSum Q A then A else (forget [Q.sumI] A).setK Q.xI (pieceOfT Q (A.getK Q.xI) (A.getK Q.pI))
  else if A.pc == Q.read + 4 then { forget [Q.ptrI, Q.ptrI + 1] A with y := AB.top }
  else A

/-- states with the same key are joined: no part of the proof -/
def keyT (T : Pole) (A : AS) : Nat :=
  let G := T.G
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := num (A.getK G.rtI)
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0)
  let n :=
    if inZone G A then
      let n := n * 65536 + num A.x
      let n := n * 65536 + num A.y
      let n := n * 65536 + num A.a
      let n := n * 65536 + num (A.p.and (AB.known 1))
      (keepT T).foldl (fun n i => n * 65536 + num (A.getK i)) n
    else if G.je ≤ A.pc && A.pc ≤ G.je + 18 then
      let n := n * 65536 + num A.a
      n * 65536 + num A.y
    else
      let n := if FrameKeep.inMove T.K A.pc then n * 65536 + num A.x else n
      if A.pc != colEnd G then (n * 65536 + num (A.getK T.Q.xI)) * 65536 + num (A.getK T.Q.pI) else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + TaintRun.stackHash A

/-- the table -/
structure CfgT where
  E : Env
  ops : Array (AM Unit)
  T : Pole
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  cut : ByteArray

def coverT (C : CfgT) (B : AS) : Bool :=
  match C.idx[keyT C.T (normT C.T B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path ends at the frame's end or in a state of the table. Everywhere the routine byte is not the pole's. -/
def walkT (C : CfgT) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preT C.T A).all fun A₁ => (kstep C.T.K C.T.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && (B.k != A.k || (C.cut.get! B.pc.toNat != 0 && coverT C B) || walkT C n B)

/-! ## Finding the table: a search, no part of the proof -/

def isCutT (T : Pole) (pc : UInt16) : Bool :=
  pc == T.Q.read || pc == T.Q.read + 2 || pc == T.Q.read + 4 || pc == T.andAt || pc == T.Q.side || pc == T.Q.adc || T.Q.exits.contains pc

def routeT (T : Pole) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := T.G
  let B := normT T B0
  let K := keyT T B
  let X := if isCutT T B.pc then { X with multi := X.multi.insert K () } else X
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

partial def runT (T : Pole) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := T.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preT T cur).flatMap (kstep T.K G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutT T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeT T X b
    break
  return X

partial def searchT (T : Pole) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runT T E ops X A
  return X

def searchOf (T : Pole) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchT T E ops ([startG T.G false, startG T.G true].foldl (routeT T) {})

def cfgOf (T : Pole) (E : Env) : CfgT :=
  let q := PipeWrites.tableOfS (searchOf T E)
  { E, ops := (aRows E).toArray, T, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- **The check.** -/
def frameCheck (T : Pole) (E : Env) : Bool :=
  let C := cfgOf T E
  let G := T.G
  let Q := T.Q
  decide (G.rtI < 2048) && decide (Q.xI < 2048) && decide (Q.pI < 2048) && decide (Q.saveI < 2048) &&
  decide (Q.left = 256 * Q.pg + lowOf Q) && decide (lowOf Q < 256) && decide (1 ≤ Q.pg) && decide (Q.pg < 256) &&
  posCover (Q.pg - 1) && posCover (lowOf Q) && PoleEntryRule.tilesCover Q &&
  decide (G.late < dotsPerFrame) && okRt G (startG G false) && okRt G (startG G true) &&
  C.t.all (walkT C fuelG) && walkT C fuelG (startG G false) && walkT C fuelG (startG G true)


/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

/-- what the pieces need from the check -/
structure PreT (Q : Spots) : Prop where
  xI : Q.xI < 2048
  pI : Q.pI < 2048
  saveI : Q.saveI < 2048
  left : Q.left = 256 * Q.pg + lowOf Q
  lo : lowOf Q < 256
  pg1 : 1 ≤ Q.pg
  pg2 : Q.pg < 256
  posP : posCover (Q.pg - 1) = true
  posL : posCover (lowOf Q) = true
  cover : PoleEntryRule.tilesCover Q = true

theorem toUInt8_eq {x : UInt8} {n : Nat} (h : x.toNat = n) : x = n.toUInt8 := by
  subst h
  simp

/-- the split of the position covers a machine left of the pole's range -/
theorem cov_splitL {Q : Spots} {A : AS} {m : Machine} (hb : PreT Q) (hlt : px Q m < Q.left) (hs : Sim E F A m) : ∃ B ∈ splitL Q A, Sim E F B m := by
  unfold px at hlt
  have hL := hb.left
  have hlo := hb.lo
  have hp1 := hb.pg1
  have hp2 := hb.pg2
  have hx := (m.ram.get! Q.xI).toNat_lt
  by_cases h1 : (m.ram.get! Q.pI).toNat + 1 < Q.pg
  · obtain ⟨a, ha, hm⟩ := pos_piece hb.posP (x := m.ram.get! Q.pI) (by omega)
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩)), sim_setK' hs hm⟩
  · by_cases h2 : (m.ram.get! Q.pI).toNat + 1 = Q.pg
    · refine ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)), sim_setK' hs ?_⟩
      rw [toUInt8_eq (x := m.ram.get! Q.pI) (n := Q.pg - 1) (by omega)]
      exact mem_known_self _
    · have h3 : (m.ram.get! Q.pI).toNat = Q.pg := by omega
      obtain ⟨a, ha, hm⟩ := pos_piece hb.posL (x := m.ram.get! Q.xI) (by omega)
      refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), sim_setK' (sim_setK' hs hm) ?_⟩
      rw [toUInt8_eq h3]
      exact mem_known_self _

/-- with the pointer and `Y` known, the place of the read is the machine's -/
theorem readAt_eq {Q : Spots} {A : AS} {m : Machine} (hp : Q.ptrI + 1 < 2048) (hs : Sim E F A m) (h1 : (A.getK Q.ptrI).isK = true) (h2 : (A.getK (Q.ptrI + 1)).isK = true)
    (h3 : A.y.isK = true) : readAt Q m = readF Q A := by
  have e1 : m.ram.get! Q.ptrI = (A.getK Q.ptrI).v := known_eq h1 (hs.ram _ (by omega))
  have e2 : m.ram.get! (Q.ptrI + 1) = (A.getK (Q.ptrI + 1)).v := known_eq h2 (hs.ram _ hp)
  have e3 : m.y = A.y.v := known_eq h3 hs.y
  unfold readAt readF ptrAt
  rw [e1, e2, e3]

/-- after a read of the side check that cannot be the pole's tile, the byte read is in a piece -/
theorem cov_tile {Q : Spots} {A : AS} {m : Machine} (hb : PreT Q) (hp : Q.ptrI + 1 < 2048) (hpc : m.pc = Q.read + 2) (hn : sideNow Q A = true)
    (ho : offTile Q A = true) (ht : TileRead Q m) (hs : Sim E F A m) :
    ∃ B ∈ Q.bits.map (fun b => ({ A with a := PipeEntryRule.neBit Q.ball b } : AS)), Sim E F B m := by
  simp only [sideNow, Bool.and_eq_true] at hn
  obtain ⟨hk, hc⟩ := hn
  have hsv : m.ram.get! Q.saveI = (A.getK Q.saveI).v := known_eq hk (hs.ram _ hb.saveI)
  have hidx : m.ram.get! Q.saveI ∈ Q.idx := by
    rw [hsv]
    exact List.mem_of_elem_eq_true hc
  have key : (m.a = Q.ball ∨ m.a = Q.shaft) → False := by
    intro htile
    obtain ⟨h1, h2⟩ := ht hpc hidx htile
    simp only [offTile, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at ho
    rcases ho with h3 | ⟨⟨⟨h4, h5⟩, h6⟩, h7⟩
    · have hle := TaintRun.le_maxv (hs.ram _ hb.pI)
      simp only [nearP, decide_eq_false_iff_not] at h3
      omega
    · rw [readAt_eq hp hs h4 h5 h6, h7] at h1
      cases h1
  obtain ⟨b, hb1, hb2⟩ := PoleEntryRule.tile_bit hb.cover (fun he => key (Or.inl he)) (fun he => key (Or.inr he))
  exact ⟨_, List.mem_map.2 ⟨b, hb1, rfl⟩, { hs with a := hb2 }⟩

/-- what the zone needs from the check -/
structure ZoneOK (T : Pole) : Prop where
  pre : PreT T.Q
  ptr : T.Q.ptrI + 1 < 2048

theorem cov_zoneT {T : Pole} {A : AS} {m : Machine} (hb : ZoneOK T) (hh : HypT T m) (hs : Sim E F A m) : ∃ B ∈ zoneT T A, Sim E F B m := by
  obtain ⟨hS, hT, hC⟩ := hh
  unfold zoneT
  by_cases h0 : T.G.cuts.contains A.pc = true
  · exfalso
    apply hC
    rw [hs.pc]
    exact List.mem_of_elem_eq_true h0
  rw [if_neg h0]
  by_cases h1 : (A.pc == T.G.subs) = true
  · rw [if_pos h1]
    exact cov_splitL hb.pre (hS (by rw [hs.pc]; exact beq_iff_eq.1 h1)) hs
  rw [if_neg h1]
  by_cases h1a : (A.pc == T.Q.adc && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h1a]
    obtain ⟨B, hB, h3, _⟩ := cov_fill hb.pre.xI A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h1a]
  by_cases h2 : (A.pc == T.andAt && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h2]
    obtain ⟨B, hB, h3, _⟩ := cov_highA A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h2]
  by_cases h3 : (A.pc == T.Q.read + 2 && sideNow T.Q A && offTile T.Q A) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨h4, h5⟩, h6⟩ := h3
    exact cov_tile hb.pre hb.ptr (by rw [hs.pc]; exact h4) h5 h6 hT hs
  · rw [if_neg h3]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

/-- every machine that meets the conditions is in a piece -/
theorem cov_preT {T : Pole} {A : AS} {m : Machine} (hb : ZoneOK T) (hc : CleanK T.G T.K.store m) (hh : HypT T m) (hs : Sim E F A m) :
    ∃ B ∈ preT T A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨D, hD, h3⟩ := cov_zoneT hb hh h1
  have h4 := FrameKeep.k_of_sim h1 h3
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

end

/-! ## The walk covers the machine -/

section
variable {C : CfgT} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveT (C : CfgT) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkT C n A = true

theorem cover_liveT (ht : C.t.all (walkT C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0) (h : coverT C B = true) : ∃ D, LiveT C F D m := by
  unfold coverT at h
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

theorem live_stepT (ht : C.t.all (walkT C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveT C F A m) (hc : CleanK C.T.G C.T.K.store m) (hh : HypT C.T m) :
    (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧ (F.1 < (go step m).2.frame ∨ ∃ A', LiveT C F A' (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkT] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preT hb hc hh hs
    obtain ⟨r, hr1, hB⟩ := FrameKeep.s_kstep hops hT hc hs1
    simp only [walkT, List.all_eq_true] at hw
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
        · exact cover_liveT ht hkl h1 hk2 h4
        · exact ⟨B, h1, hk2, n, h4⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The frame -/

/-- what the check says -/
structure FrameOK (T : Pole) (E : Env) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  ok0 : okRt T.G (startG T.G false) = true
  ok1 : okRt T.G (startG T.G true) = true
  table : (cfgOf T E).t.all (walkT (cfgOf T E) fuelG) = true
  s0 : walkT (cfgOf T E) fuelG (startG T.G false) = true
  s1 : walkT (cfgOf T E) fuelG (startG T.G true) = true

theorem frameOK_of_check {T : Pole} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (h : frameCheck T E = true) : FrameOK T E := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, _⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩ := h
  exact ⟨h1, ⟨⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hp⟩, h13, h14, h15, h16, h17⟩

/-- **The frame.** From a `FrameStart`, while each instruction is `CleanK` and meets `HypT`, the routine byte does not become the pole's. -/
theorem no_write_frame {T : Pole} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (hc : frameCheck T E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ HypT T (s j)) : (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOK_of_check hp hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOf T E).kl = (cfgOf T E).t.map knownOf := rfl
  have hstart : ∃ A, LiveT (cfgOf T E) ((s 0).frame, 2) A (s 0) := by
    cases b with
    | false => exact ⟨_, hsim, rfl, fuelG, hC.s0⟩
    | true => exact ⟨_, hsim, rfl, fuelG, hC.s1⟩
  have live : ∀ j, j ≤ n → ∃ A, LiveT (cfgOf T E) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => hstart
    | succ j ih =>
      intro hj
      obtain ⟨A, hA⟩ := ih (by omega)
      obtain ⟨hh1, hh2⟩ := hh j (by omega)
      obtain ⟨_, h2⟩ := live_stepT hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.zone hC.rt hA hh1 hh2
      rw [← hs j (by omega)] at h2
      rcases h2 with h2 | h2
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := h2
        omega
      · exact h2
  obtain ⟨A, hA⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hh2⟩ := hh n (Nat.le_refl n)
  obtain ⟨h1, _⟩ := live_stepT hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.zone hC.rt hA hh1 hh2
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-- before the write the frame goes on -/
theorem frame_before {sy : Syms} {m : Machine} {i : UInt8} {n : Nat} (h : WriteStep sy m i n) : ∀ j, j ≤ n → (trace m i j).frame ≤ m.frame := by
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

/-- `CleanK` and `FrameStart` do not depend on the routine, the split or the cuts of the guard -/
theorem cleanK_with {G : Guard} {e : UInt8} {s : UInt16} {c : List UInt16} {q : UInt16} {m : Machine} (h : CleanK G q m) :
    CleanK { G with ev := e, subs := s, cuts := c } q m := ⟨h.store, h.read, h.jump, h.time⟩

theorem start_with {G : Guard} {e : UInt8} {s : UInt16} {c : List UInt16} {E : Env} {m : Machine} (h : FrameStart G E m) :
    FrameStart { G with ev := e, subs := s, cuts := c } E m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

theorem cleanK_T {sy : Syms} {m0 m : Machine} {q : UInt16} (h : CleanK (FrameKeep.guardK sy m0) q m) : CleanK (guardT sy m0) q m := cleanK_with h

theorem start_T {sy : Syms} {m0 : Machine} {E : Env} {m : Machine} (h : FrameStart (FrameKeep.guardK sy m0) E m) : FrameStart (guardT sy m0) E m := start_with h

/-- the pointer's two bytes are in the RAM -/
def ptrOK (sy : Syms) (m0 : Machine) : Bool := decide ((spotsF sy m0).ptrI + 1 < 2048)

/-- **The check on the ROM.** -/
def poleFrameCheck (sy : Syms) (m0 : Machine) : Bool := ptrOK sy m0 && frameCheck (poleOf sy m0) (envOf m0)

/-- **The touch on a real frame, at the end of the move.** If the frame touches, it starts in control (`StartK`), each of its instructions is `CleanK`, and up to the write each
state meets `TileRead` and does not come to the two places cut, then at the end of the move, before the write, the position is at or right of the left end of the pole's range. -/
theorem touch_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleFrameCheck sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hh : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileRead (spotsF sy m0) (trace m i j) ∧
      (trace m i j).pc ≠ PipeWrites.edgeStore sy m0 ∧ (trace m i j).pc ≠ PipeWrites.headAt sy m0) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleFrameCheck, Bool.and_eq_true] at hc
  obtain ⟨hp, hc⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frame (T := poleOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw j hj)
      (fun j hj => frame_before hw j hj) (start_T (h0.pad _))
      (fun j hj => ⟨cleanK_T (hk j), fun hs => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, (hh n hw j hj).1, by
        show (trace m i j).pc ∉ [PipeWrites.edgeStore sy m0, PipeWrites.headAt sy m0]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact (hh n hw j hj).2⟩)
    exact hn hw.2

/-- **In the pole's range, from one whole frame.** `P` is the position at the end of the move before the write (`moved`). A frame that touches, under the conditions of
`touch_right_of_left`, has `P` at or right of the left end of the pole's range. -/
theorem inRange_of_frame {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleFrameCheck sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hh : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileRead (spotsF sy m0) (trace m i j) ∧
      (trace m i j).pc ≠ PipeWrites.edgeStore sy m0 ∧ (trace m i j).pc ≠ PipeWrites.headAt sy m0)
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_left hc he h0 hk hh
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

/-! ## On real frames: a program, no part of the proof -/

/-- `TileRead` as a check -/
def tileReadB (Q : Spots) (m : Machine) : Bool :=
  !(m.pc == Q.read + 2 && Q.idx.contains (m.ram.get! Q.saveI) && (m.a == Q.ball || m.a == Q.shaft)) ||
    (onCol Q (readAt Q m) && decide (Q.pg ≤ (m.ram.get! Q.pI).toNat + 1))

/-- `CleanK` as a check -/
def cleanKB (G : Guard) (q : UInt16) (m : Machine) : Bool :=
  let (a, b, j, d) := PipeWrites.cleanB G m
  (a || (m.pc == q && m.x == 0)) && b && j && d

/-- what real frames say about the hypotheses -/
structure Report where
  frames : Nat := 0
  /-- frames in control, and how many do not meet `StartK`; instructions of them not `CleanK`; side reads after which `TileRead` fails; frames that come to a cut place -/
  ctl : Nat := 0
  startBad : Nat := 0
  instrs : Nat := 0
  cleanBad : Nat := 0
  reads : Nat := 0
  tileBad : Nat := 0
  outside : Nat := 0
  cutFrames : Nat := 0
  /-- frames that touch; of them: not `StartK`; an instruction not `CleanK`; `TileRead` failing up to the write; a cut place before it; not one arrival at the end of the move
  before it; the position there left of the range; the position there is not the frame's start moved by the speed there (`P₂ = P + 16·v₂`, `moved`) -/
  touches : Nat := 0
  tStart : Nat := 0
  tClean : Nat := 0
  tTile : Nat := 0
  tCut : Nat := 0
  subsN : Nat := 0
  leftBad : Nat := 0
  movedBad : Nat := 0
  pxs : List Nat := []
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, in control {r.ctl} (not StartK {r.startBad}), instructions {r.instrs} (not CleanK {r.cleanBad}), side reads {r.reads} (TileRead fails {r.tileBad}, outside the block buffers {r.outside}), frames at a cut place {r.cutFrames}; touches {r.touches} (not StartK {r.tStart}, not CleanK {r.tClean}, TileRead fails {r.tTile}, at a cut place {r.tCut}, not one arrival at the end of the move {r.subsN}, left of the range there {r.leftBad}, moved {r.movedBad}), positions {r.pxs.eraseDups.mergeSort}"

def Report.bad (r : Report) : Nat := r.startBad + r.cleanBad + r.tileBad + r.tStart + r.tClean + r.tTile + r.tCut + r.subsN + r.leftBad + r.movedBad

/-- one real frame with the bits `pad` of the controller -/
def scanFrame (sy : Syms) (m0 : Machine) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let G := FrameKeep.guardK sy m0
  let q := (FrameKeep.spotOf sy m0).store
  let Q := spotsF sy m0
  let E := envOf m0
  let cuts := [PipeWrites.edgeStore sy m0, PipeWrites.headAt sy m0]
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let ctl := controllable sy m
  let startOk := PipeWrites.startB G E c
  let mut r := { r0 with frames := r0.frames + 1, ctl := r0.ctl + (if ctl then 1 else 0), startBad := r0.startBad + (if ctl && !startOk then 1 else 0) }
  let mut clean := true
  let mut tiles := true
  let mut cutSeen := false
  let mut subs : List Machine := []
  let mut touched := false
  let mut n := 0
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if !touched then
      if cuts.contains c.pc then cutSeen := true
      if c.pc == sy.PlayerSubs then subs := c :: subs
    let ok := cleanKB G q c
    if ctl then r := { r with instrs := r.instrs + 1, cleanBad := r.cleanBad + (if ok then 0 else 1) }
    if !ok && !touched then clean := false
    if c.pc == Q.read + 2 && Q.idx.contains (c.ram.get! Q.saveI) then
      let x := tileReadB Q c
      let i := readAt Q c
      let inBuf : Bool := decide (Q.bufLo ≤ i) && decide (i < Q.bufLo + Q.bufBytes)
      if ctl then r := { r with reads := r.reads + 1, tileBad := r.tileBad + (if x then 0 else 1), outside := r.outside + (if inBuf then 0 else 1) }
      if !x && !touched then tiles := false
    let before := rt sy c
    c := (go step c).2
    if before != vf sy && rt sy c == vf sy && !touched then
      touched := true
      r := { r with
        touches := r.touches + 1
        tStart := r.tStart + (if startOk then 0 else 1)
        tClean := r.tClean + (if clean then 0 else 1)
        tTile := r.tTile + (if tiles then 0 else 1)
        tCut := r.tCut + (if cutSeen then 1 else 0)
        subsN := r.subsN + (if subs.length == 1 then 0 else 1) }
      match subs.head? with
      | some u =>
        r := { r with leftBad := r.leftBad + (if px Q u < Q.left then 1 else 0), pxs := px Q u :: r.pxs,
                      movedBad := r.movedBad + (if posP sy u == posP sy m + 16 * sbyte (peek u sy.Player_X_Speed) then 0 else 1) }
      | none => pure ()
    n := n + 1
  if ctl && cutSeen then r := { r with cutFrames := r.cutFrames + 1 }
  return (r, c)

end Smbrta.PoleFrame
