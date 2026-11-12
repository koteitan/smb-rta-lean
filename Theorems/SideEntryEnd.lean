import Theorems.SideFrame

/-!
# The side pipe's entering frame: the position at the write

`SideFrame` shows that on the entering frame the position at the end of the move (`PlayerSubs`) before the write of the side pipe's routine is at or right of the mouth's left
end, under the hypothesis on the end of the move that it is left of the mouth (`HypF`) and its contrapositive. Here the abstract machine of `SideFrame` follows the frame up to
the first write of the side pipe's routine with no hypothesis on the position. Where the move ends it splits the position into pieces that cover every value: on page 0 the
pieces left of the mouth (those of `SideFrame`) and the pieces at or right of its left end (`rightPieces`), on any other page one piece for each bit of the page, that bit 1.
Where the collision routine first reads the player's height on the screen, the walk splits that byte into "on the screen" and the pieces that are not (`eqPieces`).

The walk asks, at every state before the first write: the routine byte is known not to be the side pipe's, and at the write itself the position is at or right of the mouth's
left end (`okA`): a page with a bit known to be 1, or page 0 with the pixel's known bits at or right of it. A path stops where the routine byte becomes the side pipe's.

So at the first write of the side pipe's routine in a frame, the position is at or right of the mouth's left end (`write_right_of_left`). `SideEntryRest` follows the frame
from there to its end on the walk of the room.

There is no game data in this file. Page: `1-1/c-7-18-2-SideEntryEnd.md`.
-/

namespace Smbrta.SideEntryEnd

open PipeTransition (frame)
open PipeTransitionAll (go)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top)
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp envOf known_eq sim_setK' forget)
open PoleEntryRule (Spots onCol AtRead TilesOK px ptrAt)
open PipeWrites (Guard Clean FrameStart capT jumpP gsucc okRt inZone normRt colEnd knownOf leK joinK startG zeros fuelG)
open SideFrame (Side posPieces fillB highA sideNow readF safeF keepF zoneF HypF PreF)

/-! ## The pieces -/

/-- the values at or right of `left` on page 0, as a few pieces: `left` itself, and for each bit of `left` that is 0, the bits above it as in `left`, that bit 1, the bits
below it not known -/
def rightPieces (left : Nat) : List AB :=
  ⟨left.toUInt8, 255⟩ :: (List.range 8).filterMap fun b =>
    if (left / 2 ^ b) % 2 == 0 then
      let hi : UInt8 := (255 - (2 * 2 ^ b - 1) : Nat).toUInt8
      some ⟨(left.toUInt8 &&& hi) ||| (2 ^ b : Nat).toUInt8, hi ||| (2 ^ b : Nat).toUInt8⟩
    else none

/-- the bits of a byte -/
def bitsB : List UInt8 := [1, 2, 4, 8, 16, 32, 64, 128]

/-- the pieces of a page that is not 0: one bit known to be 1 -/
def pageBits : List AB := bitsB.map fun b => ⟨b, b⟩

/-- the position, in pieces that cover every value: page 0 and the pixel left of the mouth, page 0 and the pixel at or right of it, or a page with one bit known to be 1 -/
def splitAll (Q : Spots) (A : AS) : List AS :=
  (posPieces Q.left ++ rightPieces Q.left).map (fun a => (A.setK Q.xI a).setK Q.pI (AB.known 0)) ++ pageBits.map fun b => A.setK Q.pI b

/-- every value at or right of `left` is in a piece, and every piece is at or right of `left` -/
def rightCover (left : Nat) : Bool :=
  (List.range 256).all (fun n => decide (n < left) || (rightPieces left).any fun a => SideFrame.memB a n.toUInt8) &&
  (rightPieces left).all fun a => decide (left ≤ (a.v &&& a.k).toNat)

/-- a byte: one piece where it is 1 (on the screen, for the height), and one for each bit where it differs from 1 -/
def onePieces : List AB := AB.known 1 :: bitsB.map fun b => ⟨~~~(1 : UInt8) &&& b, b⟩

/-- the byte `d` by `onePieces` -/
def splitOne (d : Nat) (A : AS) : List AS := onePieces.map fun a => A.setK d a

/-- what the walk knows besides the places of `SideFrame`: the player's height on the screen, and where the collision routine reads it first -/
structure SideE extends Side where
  hpI : Nat
  hpAt : UInt16
  deriving Inhabited

/-- the pieces before a step: at the end of the move, the position by `splitAll`; where the collision routine first reads the height on the screen, that byte by `onePieces`;
elsewhere those of `SideFrame` -/
def zoneE (S : SideE) (A : AS) : List AS :=
  if S.G.cuts.contains A.pc then []
  else if A.pc == S.G.subs then splitAll S.Q A
  else if A.pc == S.hpAt then splitOne S.hpI A
  else zoneF S.toSide A

/-- all the pieces before a step -/
def preE (S : SideE) (A : AS) : List AS := (jumpP S.G (capT S.G A)).flatMap (zoneE S)

/-- what the frame asks of one state: the tiles at a read, no place of the cuts. Nothing about the position. -/
def HypE (S : SideE) (m : Machine) : Prop := (AtRead S.Q m → TilesOK S.Q m) ∧ m.pc ∉ S.G.cuts

/-! ## What the walk asks -/

/-- the byte is known to be `v` -/
def isV (v : UInt8) (b : AB) : Bool := b.isK && b.v == v

/-- the position is at or right of the mouth's left end: a page with a bit known to be 1, or page 0 with the pixel's known bits at or right of it -/
def posOK (Q : Spots) (B : AS) : Bool :=
  let p := B.getK Q.pI
  let x := B.getK Q.xI
  (p.v &&& p.k != 0) || (isV 0 p && decide (Q.left ≤ (x.v &&& x.k).toNat))

/-- before the write: the routine byte is known not to be the side pipe's, and at the write the position is at or right of the mouth -/
def okA (S : SideE) (A : AS) : Bool := okRt S.G A && (A.pc != S.Q.write || posOK S.Q A)

/-! ## The walk -/

/-- the piece of the position that holds this value, on both sides of the mouth -/
def pieceOfE (Q : Spots) (x : AB) : AB :=
  if x.isK then (match (posPieces Q.left ++ rightPieces Q.left).find? (fun a => SideFrame.memB a x.v) with
    | some a => a
    | none => x) else x

/-- what the search forgets: no part of the proof. As `SideFrame.normF`, with the pieces on both sides of the mouth, and the height on the screen kept -/
def normE (S : SideE) (A0 : AS) : AS :=
  let G := S.G
  let Q := S.Q
  let A := normRt G { A0 with padShift := AB.top }
  let keepP := Q.xI :: Q.pI :: S.hpI :: G.prot
  if !inZone G A then
    if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
    let B := PipeWrites.AS.forgetW keepP A
    let B := if A.pc == colEnd G then forget [Q.xI, Q.pI] B else B
    let B := if A.pc == S.back then B.setK Q.xI (pieceOfE Q (B.getK Q.xI)) else B
    let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
    { B with kn }
  else if Q.exits.contains A.pc then { PipeWrites.AS.forgetW (S.hpI :: G.prot) A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == Q.side then { PipeWrites.AS.forgetW keepP A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == S.andAt then (forget [Q.sumI] A).setK Q.xI (pieceOfE Q (A.getK Q.xI))
  else if A.pc == Q.read + 2 then { forget [Q.ptrI, Q.ptrI + 1] A with y := AB.top }
  else A

/-- states with the same key are joined: no part of the proof. As `SideFrame.keyF`; with the page partly known in the scroll handler's question whether he is off the
screen, the registers and the carry too -/
def keyE (S : SideE) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := SideFrame.keyF S.toSide A
  if (A.getK S.Q.pI).k != 0 && (A.getK S.Q.xI).k != 255 && ((S.offR ≤ A.pc && A.pc < S.offR + 0x90) || (S.offAt ≤ A.pc && A.pc < S.offAt + 0x40)) then
    (((n * 65536 + num A.x) * 65536 + num A.y) * 65536 + num A.a) * 65536 + num (A.p.and (AB.known 1))
  else n

/-- the table -/
structure CfgE where
  E : Env
  ops : Array (AM Unit)
  S : SideE
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  cut : ByteArray

/-- the state whose key the table is looked up by: as the search normalized it (no part of the proof: any entry found must still be above the state) -/
def keyOfE (S : SideE) (B : AS) : AS :=
  if inZone S.G B then normE S B
  else
    let A := normRt S.G B
    if B.pc == S.back then A.setK S.Q.xI (pieceOfE S.Q (A.getK S.Q.xI)) else A

def coverE (C : CfgE) (B : AS) : Bool :=
  match C.idx[keyE C.S (keyOfE C.S B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path ends at the frame's end, in a state of the table, or where the routine byte becomes the side pipe's. At every state before that `okA`. -/
def walkE (C : CfgE) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => okA C.S A && (preE C.S A).all fun A₁ => (gsucc C.S.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => isV C.S.G.ev (B.getK C.S.G.rtI) || (okA C.S B && (B.k != A.k || (C.cut.get! B.pc.toNat != 0 && coverE C B) || walkE C n B))

/-! ## Finding the table: a search, no part of the proof -/

def isCutE (S : SideE) (pc : UInt16) : Bool := SideFrame.isCutF S.toSide pc

def routeE (S : SideE) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := S.G
  let B := normE S B0
  let K := keyE S B
  let X := if isCutE S B.pc then { X with multi := X.multi.insert K () } else X
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

partial def runE (S : SideE) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := S.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preE S cur).flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := !okA S cur || rs.any fun r => match r with
      | none => true
      | some B => !isV G.ev (B.getK G.rtI) && !okA S B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k && !isV G.ev (b.getK G.rtI)
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutE S b.pc && b.pc != G.je && b.pc != G.subs && b.pc != S.hpAt &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeE S X b
    break
  return X

partial def searchE (S : SideE) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runE S E ops X A
  return X

def searchOf (S : SideE) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchE S E ops ([startG S.G false, startG S.G true].foldl (routeE S) {})

def cfgOf (S : SideE) (E : Env) : CfgE :=
  let q := PipeWrites.tableOfS (searchOf S E)
  { E, ops := (aRows E).toArray, S, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- **The check.** -/
def frameCheck (S : SideE) (E : Env) : Bool :=
  let C := cfgOf S E
  let G := S.G
  decide (G.rtI < 2048) && decide (S.Q.xI < 2048) && decide (S.Q.pI < 2048) && decide (S.Q.saveI < 2048) && decide (S.Q.ptrI < 2048) && decide (S.hpI < 2048) &&
  decide (S.Q.left < 256) && SideFrame.posCover S.Q.left && rightCover S.Q.left && SideEntryRule.piecesCover S.Q &&
  decide (G.late < dotsPerFrame) && C.t.all (walkE C fuelG) && walkE C fuelG (startG G false) && walkE C fuelG (startG G true)

/-- the walk's places: those of `SideFrame`, with the bump on a solid block cut too -/
def sideOfE (sy : Syms) (m0 : Machine) : SideE :=
  let S := SideFrame.sideOf sy m0
  { S with G := { S.G with cuts := [PipeWrites.headAt sy m0, SideFrame.bumpAt sy m0] }
           hpI := (sy.Player_Y_HighPos &&& 0x7FF).toNat
           hpAt := ScreenPage.findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_HighPos.toUInt8 64 }

/-- **The check on the ROM.** -/
def sideEntryEndCheck (sy : Syms) (m0 : Machine) : Bool := sy.PlayerSubs != 0 && frameCheck (sideOfE sy m0) (envOf m0)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem page_bit_all : ∀ n : Fin 256, (UInt8.ofNat n.val == 0 || pageBits.any fun a => SideFrame.memB a (UInt8.ofNat n.val)) = true := by decide +kernel

/-- a page that is not 0 has a bit that is 1 -/
theorem page_bit {p : UInt8} (h : p ≠ 0) : ∃ a ∈ pageBits, a.mem p := by
  have h1 := page_bit_all ⟨p.toNat, p.toNat_lt⟩
  simp only [UInt8.ofNat_toNat, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h1
  rcases h1 with h2 | ⟨a, ha, h2⟩
  · exact absurd h2 h
  · exact ⟨a, ha, SideFrame.memB_iff.1 h2⟩

theorem one_all : ∀ n : Fin 256, (onePieces.any fun a => SideFrame.memB a (UInt8.ofNat n.val)) = true := by decide +kernel

/-- every byte is in a piece of `onePieces` -/
theorem one_piece (x : UInt8) : ∃ a ∈ onePieces, a.mem x := by
  have h := one_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat, List.any_eq_true] at h
  obtain ⟨a, ha, h2⟩ := h
  exact ⟨a, ha, SideFrame.memB_iff.1 h2⟩

/-- a value at or right of `left` is in a piece -/
theorem right_piece {left : Nat} (hc : rightCover left = true) {x : UInt8} (hx : left ≤ x.toNat) : ∃ a ∈ rightPieces left, a.mem x := by
  simp only [rightCover, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
  rcases hc.1 x.toNat x.toNat_lt with h | ⟨a, ha, h⟩
  · omega
  · have hv : x.toNat.toUInt8 = x := by simp
    rw [hv] at h
    exact ⟨a, ha, SideFrame.memB_iff.1 h⟩

/-- the split of the position covers every machine -/
theorem cov_splitAll {Q : Spots} (hx : Q.xI < 2048) (hp : Q.pI < 2048) (hc : SideFrame.posCover Q.left = true) (hr : rightCover Q.left = true)
    {A : AS} {m : Machine} (hs : Sim E F A m) : ∃ B ∈ splitAll Q A, Sim E F B m := by
  have _ := hx
  have _ := hp
  unfold splitAll
  by_cases h0 : m.ram.get! Q.pI = 0
  · have hpage : (AB.known 0).mem (m.ram.get! Q.pI) := by rw [h0]; exact mem_known_self _
    by_cases hl : (m.ram.get! Q.xI).toNat < Q.left
    · obtain ⟨a, ha, hm⟩ := SideFrame.pos_piece hc hl
      exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨a, List.mem_append_left _ ha, rfl⟩), sim_setK' (sim_setK' hs hm) hpage⟩
    · obtain ⟨a, ha, hm⟩ := right_piece hr (x := m.ram.get! Q.xI) (by omega)
      exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨a, List.mem_append_right _ ha, rfl⟩), sim_setK' (sim_setK' hs hm) hpage⟩
  · obtain ⟨a, ha, hm⟩ := page_bit h0
    exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), sim_setK' hs hm⟩

/-- the split of the height covers every machine -/
theorem cov_splitOne {d : Nat} {A : AS} {m : Machine} (hs : Sim E F A m) : ∃ B ∈ splitOne d A, Sim E F B m := by
  obtain ⟨a, ha, hm⟩ := one_piece (m.ram.get! d)
  exact ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, sim_setK' hs hm⟩

/-- the pieces of a step cover every machine that meets the conditions -/
theorem cov_zoneE {S : SideE} {A : AS} {m : Machine} (hb : PreF S.toSide) (hr : rightCover S.Q.left = true) (hh : HypE S m) (hs : Sim E F A m) :
    ∃ B ∈ zoneE S A, Sim E F B m := by
  obtain ⟨hT, hC⟩ := hh
  unfold zoneE
  by_cases h0 : S.G.cuts.contains A.pc = true
  · exfalso
    apply hC
    rw [hs.pc]
    exact List.mem_of_elem_eq_true h0
  rw [if_neg h0]
  by_cases h1 : (A.pc == S.G.subs) = true
  · rw [if_pos h1]
    exact cov_splitAll hb.xI hb.pI hb.pos hr hs
  rw [if_neg h1]
  by_cases h2 : (A.pc == S.hpAt) = true
  · rw [if_pos h2]
    exact cov_splitOne hs
  rw [if_neg h2]
  refine SideFrame.cov_zoneF hb ⟨fun he => ?_, hT, hC⟩ hs
  exfalso
  apply h1
  show (A.pc == S.toSide.G.subs) = true
  rw [← hs.pc, he]
  exact beq_self_eq_true _

/-- every machine that meets the conditions is in a piece -/
theorem cov_preE {S : SideE} {A : AS} {m : Machine} (hb : PreF S.toSide) (hr : rightCover S.Q.left = true) (hc : Clean S.G m) (hh : HypE S m)
    (hs : Sim E F A m) : ∃ B ∈ preE S A, Sim E F B m := by
  obtain ⟨B, hB, h1⟩ := PipeWrites.cov_jump hc (PipeWrites.sim_cap hc hs)
  obtain ⟨D, hD, h2⟩ := cov_zoneE hb hr hh h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2⟩

/-- a byte that meets known bits is at least their value with the other bits 0 -/
theorem minv_le {b : AB} {x : UInt8} (h : b.mem x) : (b.v &&& b.k).toNat ≤ x.toNat := by
  have e : x &&& b.k = b.v &&& b.k := h
  rw [← e, UInt8.toNat_and]
  exact Nat.and_le_left

/-- **The bound from `posOK`**: a machine covered by a state that passes `posOK` is at or right of the mouth's left end -/
theorem px_of_posOK {Q : Spots} (hx : Q.xI < 2048) (hp : Q.pI < 2048) (hl : Q.left < 256) {A : AS} {m : Machine} (hs : Sim E F A m)
    (h : posOK Q A = true) : Q.left ≤ px Q m := by
  have hmx := hs.ram Q.xI hx
  have hmp := hs.ram Q.pI hp
  unfold px
  simp only [posOK, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h1 | ⟨h1, h2⟩
  · -- a page with a bit known to be 1: not page 0
    have e : m.ram.get! Q.pI &&& (A.getK Q.pI).k = (A.getK Q.pI).v &&& (A.getK Q.pI).k := hmp
    have hne : m.ram.get! Q.pI ≠ 0 := by
      intro h0
      rw [h0, UInt8.zero_and] at e
      exact h1 e.symm
    have h3 : 1 ≤ (m.ram.get! Q.pI).toNat := by
      have h4 : (m.ram.get! Q.pI).toNat ≠ 0 := fun h5 => hne (UInt8.toNat_inj.1 (by rw [h5]; rfl))
      omega
    omega
  · -- page 0, and the pixel's known bits at or right of the mouth
    simp only [isV, Bool.and_eq_true, beq_iff_eq] at h1
    have hk : (A.getK Q.pI).isK = true := h1.1
    have e := known_eq (b := A.getK Q.pI) (x := m.ram.get! Q.pI) hk hmp
    have h0 : m.ram.get! Q.pI = 0 := by rw [e, h1.2]
    have h3 := minv_le hmx
    rw [h0]
    simp only [UInt8.toNat_zero, Nat.mul_zero, Nat.zero_add]
    omega

end

/-! ## The walk covers the machine -/

section
variable {C : CfgE} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveE (C : CfgE) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkE C n A = true

theorem okA_of_walk {n : Nat} {A : AS} (h : walkE C n A = true) : okA C.S A = true := by
  cases n with
  | zero => simp [walkE] at h
  | succ n =>
    simp only [walkE, Bool.and_eq_true] at h
    exact h.1

theorem cover_liveE (ht : C.t.all (walkE C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverE C B = true) : ∃ D, LiveE C F D m := by
  unfold coverE at h
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

/-- **One step of the walk.** The step from a machine that a live state covers: the routine byte becomes the side pipe's, or the next machine is covered by a state that passes
`okA`, and the frame has ended or a live state covers it. -/
theorem live_stepE (ht : C.t.all (walkE C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : PreF C.S.toSide) (hr : rightCover C.S.Q.left = true) {A : AS} {m : Machine} (hl : LiveE C F A m) (hc : Clean C.S.G m) (hh : HypE C.S m) :
    ∃ B, Sim C.E F B (go step m).2 ∧ (isV C.S.G.ev (B.getK C.S.G.rtI) = true ∨
      (okA C.S B = true ∧ (F.1 < (go step m).2.frame ∨ ∃ A', LiveE C F A' (go step m).2))) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkE] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_preE hb hr hc hh hs
    obtain ⟨r, hr1, hB⟩ := PipeWrites.s_gsucc hops hT hc hs1
    simp only [walkE, Bool.and_eq_true, List.all_eq_true] at hw
    have hw2 := hw.2 A₁ hA r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      refine ⟨B, h1, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at hw2
      rcases hw2 with h2 | ⟨h2, h3⟩
      · exact Or.inl h2
      · right
        refine ⟨h2, ?_⟩
        by_cases hk2 : B.k = 0
        · right
          rcases h3 with (h4 | ⟨_, h4⟩) | h4
          · rw [hk, hk2] at h4
            exact absurd rfl h4
          · exact cover_liveE ht hkl h1 hk2 h4
          · exact ⟨B, h1, hk2, n, h4⟩
        · left
          rw [h1.fr]
          omega

end

/-! ## The frame -/

/-- what the check says -/
structure FrameOK (S : SideE) (E : Env) : Prop where
  rt : S.G.rtI < 2048
  pre : PreF S.toSide
  right : rightCover S.Q.left = true
  table : (cfgOf S E).t.all (walkE (cfgOf S E) fuelG) = true
  s0 : walkE (cfgOf S E) fuelG (startG S.G false) = true
  s1 : walkE (cfgOf S E) fuelG (startG S.G true) = true

theorem frameOK_of_check {S : SideE} {E : Env} (h : frameCheck S E = true) : FrameOK S E := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩, h6⟩, h6a⟩, h6b⟩, h7⟩, _⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, ⟨h2, h3, h6, h6a, h7⟩, h6b, h9, h10, h11⟩

/-- **At the first write of the side pipe's routine, the position is at or right of the mouth's left end.** From a `FrameStart`, while each instruction is `Clean` and meets
`HypE`, every state at the write before the routine byte is the side pipe's has the position at or right of the mouth. No hypothesis on the position. -/
theorem write_right_of_left {S : SideE} {E : Env} (hc : frameCheck S E = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart S.G E m)
    (hp : ∀ j, Clean S.G (trace m i j) ∧ HypE S (trace m i j)) :
    ∀ j, (∀ k, k ≤ j → (trace m i k).ram.get! S.G.rtI ≠ S.G.ev) → (trace m i j).pc = S.Q.write → S.Q.left ≤ px S.Q (trace m i j) := by
  have hC := frameOK_of_check hc
  have hkl : (cfgOf S E).kl = (cfgOf S E).t.map knownOf := rfl
  have hF : (trace m i 0).frame = m.frame := rfl
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE (FrameStart.pad h0 (smbToPad i))
  have hsim' : Sim (cfgOf S E).E ((trace m i 0).frame, 2) (startG S.G b) (trace m i 0) := hsim
  rw [hF] at hsim'
  -- the invariant: a live state covers the machine, or the frame has ended and a state that passes `okA` covers it
  have key : ∀ j, (∀ k, k ≤ j → (trace m i k).ram.get! S.G.rtI ≠ S.G.ev) →
      (∃ A, LiveE (cfgOf S E) (m.frame, 2) A (trace m i j)) ∨
      (m.frame + 1 ≤ (trace m i j).frame ∧ ∃ B, Sim (cfgOf S E).E (m.frame, 2) B (trace m i j) ∧ okA S B = true) := by
    intro j
    induction j with
    | zero =>
      intro _
      left
      cases b with
      | false => exact ⟨_, hsim', rfl, fuelG, hC.s0⟩
      | true => exact ⟨_, hsim', rfl, fuelG, hC.s1⟩
    | succ j ih =>
      intro hr
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih (fun k hk => hr k (by omega)) with ⟨A, hA⟩ | ⟨h1, B, h2, h3⟩
      · have hh := hA.1.halted
        have hfr : (trace m i j).frame = m.frame := by
          rw [hA.1.fr, hA.2.1]
          rfl
        have hcnd : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [hfr, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hcnd]
        obtain ⟨B, hB, h4⟩ := live_stepE hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.pre hC.right hA (hp j).1 (hp j).2
        rw [← e2] at hB h4
        rcases h4 with h5 | ⟨h5, h6 | h6⟩
        · exfalso
          apply hr (j + 1) (Nat.le_refl _)
          have h5' : isV S.G.ev (B.getK S.G.rtI) = true := h5
          simp only [isV, Bool.and_eq_true, beq_iff_eq] at h5'
          have := known_eq (b := B.getK S.G.rtI) h5'.1 (hB.ram _ hC.rt)
          rw [this, h5'.2]
        · exact Or.inr ⟨h6, B, hB, h5⟩
        · exact Or.inl h6
      · have hcnd : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl h1
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hcnd]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h3⟩
  intro j hr hw
  have hgoal : ∀ B, Sim (cfgOf S E).E (m.frame, 2) B (trace m i j) → okA S B = true → S.Q.left ≤ px S.Q (trace m i j) := by
    intro B hB h1
    simp only [okA, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h1
    rcases h1.2 with h2 | h2
    · exact absurd (by rw [← hB.pc]; exact hw) h2
    · exact px_of_posOK hC.pre.xI hC.pre.pI hC.pre.left hB h2
  rcases key j hr with ⟨A, hA⟩ | ⟨_, B, h2, h3⟩
  · obtain ⟨hs, _, n, hwk⟩ := hA
    exact hgoal A hs (okA_of_walk hwk)
  · exact hgoal B h2 h3

end Smbrta.SideEntryEnd
