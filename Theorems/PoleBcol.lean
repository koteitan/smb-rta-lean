import Theorems.PoleCoin

/-!
# The pole's tiles: the area parser stores its column at the block buffer's column, which follows its column mod 32

Round 34 (`PoleRing`) made `PoleJoin.Run.bufAll` ask, at each store of a pole's tile into the block buffers, that the store is in the ring's column of the area
parser's column of the frame's start, or that the parser's column has come to the pole's (`PoleRing.NoTileM`). On real frames every such store is made by one
instruction, the parser's store of a column (`AreaParserCore`). That store does not compute its place from the parser's column: it reads a third byte, the block
buffer's column `B` (`BlockBufferColumnPos`), takes the address of that column of the block buffers (`GetBlockBufferAddr`), and stores the 13 rows through a
pointer. The column's step (`IncrementColumnPos`) adds one to the parser's column (with its page) and one to `B` (mod 32).

Here one walk of each whole frame in control (`walkB`, the walk of `FrameKeep` with two more tests) follows `B` and the parser's column and its page:

* the frame starts in one of 32 pieces `b`: `B = b`, the column `b mod 16`, the page's lowest bit `b / 16` (`startB`), which is `BInv`: `B = c mod 32` with the
  column below 16;
* its guard protects `B`, the column and the page (`guardB`): the field `keep.cleanE` protects the column and the page (`FrameKeep.parE`), and `BcR` (asked of
  each instruction, with `PoleKeepFar.farStore`) says that a store through an index or a pointer does not write `B`;
* at the parser's store, the target is known and, if it is in the block buffers, it is in the ring's column `b` (`storeOK`);
* at the frame's end `B`, the column and the page's lowest bit are known with `BInv` (`endB`).

So on each frame up to the touch's frame `BInv` holds at the start (`frames_bcol`, from `BInv` at control, a check on the rows), and the parser's store writes
only in the ring's column of the parser's column of the frame's start (`StoreRing`), which is `NoTileM` there. The walk's tables come from 32 searches, no part of
the proof. There is no game data in this file. Page: `1-1/f-6-17-18-PoleBcol.md`.
-/

namespace Smbrta.PoleBcol

open TaintRun (AS Env Sim AB aRows AM)
open PipeTransitionAll (go)
open PipeEntryRule (trace nxt frame_trace known_eq)
open PoleEntryRule (Spots)
open PipeWrites (Guard FrameStart wTarget opAt knownOf SG)
open FrameKeep (CfgK coverK preK kstep startK fuelK CleanK)

/-! ## The places -/

/-- the block buffers, the RAM indices of the block buffer's column `B`, the parser's column and its page, and the parser's store of a column -/
structure Bc where
  Q : Spots
  bI : Nat
  colI : Nat
  pageI : Nat
  store : UInt16
  /-- the search only: the parser's store loop, from the return of its call of `GetBlockBufferAddr` to its loop's branch back -/
  zlo : UInt16
  zhi : UInt16
  /-- the places where the walk splits the page into its 256 values: the column's step's `INC` of the page, and the entry of the loop command's step back
  (`ExecGameLoopback`, which subtracts from the page); the search keeps the page's value up to that routine's return -/
  incP : UInt16
  loopP : UInt16
  loopE : UInt16
  deriving Inhabited

/-- the first `JSR t` from `a` on, within `n` bytes -/
def findJsr (m : Machine) (a t : UInt16) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m a == 0x20 && romByte m (a + 1) == t.toUInt8 && romByte m (a + 2) == (t >>> 8).toUInt8 then a else findJsr m (a + 1) t n

/-- the places, from the code: the column's step (`FrameKeep.parRt`) increments the column (its first `INC`), the page (its second) and `B` (its third, `0x11`
bytes after its entry); the parser's store is the first `STA (zp),Y` from `AreaParserCore` on -/
def bcOf (sy : Syms) (m0 : Machine) : Bc :=
  let rt := FrameKeep.parRt sy m0
  { Q := PoleFrame.spotsF sy m0
    bI := (FrameKeep.romWE m0 (rt + 0x11) &&& 0x7FF).toNat
    colI := (FrameKeep.romWE m0 (rt + 1) &&& 0x7FF).toNat
    pageI := (FrameKeep.romWE m0 (rt + 0x0E) &&& 0x7FF).toNat
    store := PipeEntryRule.findOp m0 sy.AreaParserCore 0x91 512
    zlo := findJsr m0 sy.AreaParserCore sy.GetBlockBufferAddr 512 + 3
    zhi := PipeEntryRule.findOp m0 (PipeEntryRule.findOp m0 sy.AreaParserCore 0x91 512) 0x90 32
    incP := rt + 0x0D
    loopP := sy.ExecGameLoopback
    loopE := PipeEntryRule.findOp m0 sy.ExecGameLoopback 0x60 128 }

/-- **The invariant on one state**: `B` is the parser's column mod 32, and the column in its page is below 16 -/
def BInv (K : Bc) (m : Machine) : Prop :=
  (m.ram.get! K.bI).toNat = ((m.ram.get! K.pageI).toNat * 16 + (m.ram.get! K.colI).toNat) % 32 ∧ (m.ram.get! K.colI).toNat < 16

/-- **What the parser's store does** (one state, before the step): a byte of the block buffers that the step changes is in the ring's column `b` -/
def StoreRing (K : Bc) (b : Nat) (m : Machine) : Prop :=
  ∀ i, K.Q.bufLo ≤ i → i < K.Q.bufLo + K.Q.bufBytes → (go step m).2.ram.get! i ≠ m.ram.get! i → PoleRing.ringCol K.Q i = b

/-- **What is assumed of a store** (one instruction): a store through an index or a pointer that `PoleKeepFar.farStore` does not settle does not write `B` -/
def BcR (K : Bc) (m : Machine) : Prop :=
  PoleKeepFar.farStore [K.bI] m = false → ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ K.bI

/-- `BcR`, for a program -/
def bcRB (K : Bc) (m : Machine) : Bool :=
  PoleKeepFar.farStore [K.bI] m ||
    match wTarget (opAt m) m with
    | some t => !(decide (t < 0x2000) && (t &&& 0x7FF).toNat == K.bI)
    | none => true

/-- **The guard of the walk**: `FrameKeep.guardK` with `B`, the column and the page protected too -/
def guardB (sy : Syms) (m0 : Machine) : Guard :=
  { FrameKeep.guardK sy m0 with prot := (bcOf sy m0).bI :: (bcOf sy m0).colI :: (bcOf sy m0).pageI :: (FrameKeep.guardK sy m0).prot }

/-! ## The walk -/

/-- the state of a frame's start in the piece `b` -/
def startB (G : Guard) (K : Bc) (b : Nat) (late : Bool) : AS :=
  (((startK G [] late).setK K.bI (AB.known b.toUInt8)).setK K.colI (AB.known (b % 16).toUInt8)).setK K.pageI ⟨(b / 16).toUInt8, 1⟩

/-- the target of the parser's store, as far as the state knows it: the pointer's two bytes and Y known -/
def storeT (E : Env) (K : Bc) (A : AS) : Option UInt16 :=
  let z := E.prg.get! ((K.store + 1) &&& E.mask).toNat
  let lo := A.getK (z.toUInt16 &&& 0x7FF).toNat
  let hi := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
  if lo.isK && hi.isK && A.y.isK then some ((lo.v.toUInt16 ||| (hi.v.toUInt16 <<< 8)) + A.y.v.toUInt16) else none

/-- at the parser's store with no NMI pending, the target is known, and in the block buffers only in the ring's column `b` -/
def storeOK (E : Env) (K : Bc) (b : Nat) (A : AS) : Bool :=
  A.pc != K.store || A.nmi ||
    match storeT E K A with
    | some t => !(decide (t < 0x2000)) || !PoleTileWalk.inBufB K.Q (t &&& 0x7FF).toNat || PoleRing.ringCol K.Q (t &&& 0x7FF).toNat == b
    | none => false

/-- at the frame's end: `B`, the column and the page's lowest bit are known, with the invariant -/
def endB (K : Bc) (B : AS) : Bool :=
  let bb := B.getK K.bI
  let c := B.getK K.colI
  let p := B.getK K.pageI
  B.pc != K.store && bb.isK && c.isK && p.k &&& 1 == 1 && decide (c.v.toNat < 16) && bb.v.toNat == 16 * (p.v &&& 1).toNat + c.v.toNat

/-- the pieces before a step: at `incP` and `loopP` a page that is not known is split into its values that agree with its known bits -/
def prePage (K : Bc) (A : AS) : List AS :=
  let p := A.getK K.pageI
  if (A.pc == K.incP || A.pc == K.loopP) && !p.isK then
    ((List.range 256).filter fun v => v.toUInt8 &&& p.k == p.v &&& p.k).map fun v => A.setK K.pageI (AB.known v.toUInt8)
  else [A]

/-- all the pieces before a step: those of `FrameKeep`, then these -/
def preB (C : CfgK) (K : Bc) (A : AS) : List AS := (preK C.S C.G A).flatMap (prePage K)

/-- **The walk**: `FrameKeep.walkK` with the pieces of the page, the test `storeOK` on the way and `endB` at the frame's end -/
def walkB (C : CfgK) (K : Bc) (b : Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preB C K A).all fun A₁ => storeOK C.E K b A₁ && (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkB C K b n B else B.k == A.k + 1 && endB K B

/-- the facts of the ROM and of the places that the proof uses -/
def placesB (K : Bc) (E : Env) : Bool :=
  decide (0x8000 ≤ K.store) && decide (0x8000 ≤ K.store + 1) && E.prg.get! (K.store &&& E.mask).toNat == 0x91 &&
    decide (K.bI < 2048) && decide (K.colI < 2048) && decide (K.pageI < 2048) && decide (512 ≤ K.Q.bufLo)

/-- what `placesB` says -/
structure PlacesB (K : Bc) (E : Env) : Prop where
  s0 : 0x8000 ≤ K.store
  s1 : 0x8000 ≤ K.store + 1
  op : E.prg.get! (K.store &&& E.mask).toNat = 0x91
  bI : K.bI < 2048
  colI : K.colI < 2048
  pageI : K.pageI < 2048
  lo : 512 ≤ K.Q.bufLo

theorem placesB_spec {K : Bc} {E : Env} (h : placesB K E = true) : PlacesB K E := by
  simp only [placesB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-! ## Finding the tables: 32 searches, no part of the proof -/

/-- what the search forgets: as `FrameKeep.normK`, but in the parser's store loop it keeps the pointer of the store and the byte of its offset -/
def normB (S : FrameKeep.Spot) (G : Guard) (K : Bc) (keepL : List Nat) (lo hi : UInt16) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let keep := if FrameKeep.inMove S A.pc then S.temps ++ G.prot else G.prot
  let keep := if lo ≤ A.pc && A.pc ≤ hi then keepL ++ keep else keep
  let B := PipeWrites.AS.forgetW keep A
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
  let kn := if K.loopP ≤ A.pc && A.pc ≤ K.loopE then kn else kn.set! K.pageI (kn.get! K.pageI &&& 1)
  { B with kn }

/-- the key: as `FrameKeep.keyK`, with `B`, the column and the page; in the parser's store loop also the index and the byte of the offset -/
def keyB (S : FrameKeep.Spot) (G : Guard) (K : Bc) (oI : Nat) (lo hi : UInt16) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := FrameKeep.keyK S G [] A
  let pg := A.getK K.pageI
  let pgK := if K.loopP ≤ A.pc && A.pc ≤ K.loopE then num pg else num ⟨pg.v &&& 1, pg.k &&& 1⟩
  let n := ((n * 65536 + num (A.getK K.bI)) * 65536 + num (A.getK K.colI)) * 65536 + pgK
  if lo ≤ A.pc && A.pc ≤ hi then (n * 65536 + num A.x) * 65536 + num (A.getK oI) else n

/-- the search's step into the table -/
def routeB (G : Guard) (norm : AS → AS) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := norm B0
  let k := key B
  match X.pending[k]? with
  | some Q =>
    match X.done[k]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert k J, done := X.done.insert k (J, some l'), multi := X.multi.insert k () }
    | none => X
  | none =>
    match X.done[k]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert k (), done := X.done.insert k (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD k 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert k J, done := X.done.insert k (J, some l'), multi := X.multi.insert k (), arr := X.arr.insert k (c + 1) }
    | none => { X with pending := X.pending.insert k B, done := X.done.insert k (B, none) }

partial def runB (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Bc) (norm : AS → AS) (key : AS → Nat) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := ((preK S G cur).flatMap (prePage K)).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some _ => false
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && b.pc != K.incP && b.pc != K.loopP &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeB G norm key X b
    break
  return X

partial def searchB (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Bc) (norm : AS → AS) (key : AS → Nat) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runB S G E K norm key ops X A
  return X

/-- the byte of the store's offset: the operand of the `LDY zp` right before the store -/
def offI (E : Env) (K : Bc) : Nat := (E.prg.get! ((K.store - 1) &&& E.mask).toNat).toNat

/-- the pointer's two bytes of the store -/
def ptrL (E : Env) (K : Bc) : List Nat :=
  let z := E.prg.get! ((K.store + 1) &&& E.mask).toNat
  [(z.toUInt16 &&& 0x7FF).toNat, ((z + 1).toUInt16 &&& 0x7FF).toNat]

/-- **The walk's table for the piece `b`** -/
def cfgB (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Bc) (b : Nat) : CfgK :=
  let lo := K.zlo
  let hi := K.zhi
  let key := keyB S G K (offI E K) lo hi
  let norm := normB S G K (offI E K :: ptrL E K) lo hi
  let X := searchB S G E K norm key (aRows E).toArray ([startB G K b false, startB G K b true].foldl (routeB G norm key) {})
  let q := FrameKeep.tableOfKW key X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- **The check**: the facts of the places, and for each of the 32 pieces the walk from every state of its table and from the two states of a frame's start -/
def bcolCheckW (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Bc) : Bool :=
  placesB K E && (List.range 32).all fun b =>
    let C := cfgB S G E K b
    C.t.all (walkB C K b fuelK) && walkB C K b fuelK (startB G K b false) && walkB C K b fuelK (startB G K b true)

/-- **The check on the ROM** -/
def bcolCheck (sy : Syms) (m0 : Machine) : Bool :=
  bcolCheckW (FrameKeep.spotOf sy m0) (guardB sy m0) (PipeEntryRule.envOf m0) (bcOf sy m0)

/-! ## One step -/

section
variable {E : Env} {F : Nat × UInt8} {K : Bc}

/-- **The parser's store writes in the ring's column `b`**: from `storeOK`, the pointer and Y known -/
theorem store_ring (hP : PlacesB K E) {b : Nat} {A : AS} {m : Machine} (hs : Sim E F A m) (hpc : m.pc = K.store) (hok : storeOK E K b A = true) :
    StoreRing K b m := by
  intro i h1 h2 hch
  have hloc : i ∈ StepWrites.stepLocs m :=
    if h : i ∈ StepWrites.stepLocs m then h else absurd (StepWrites.step_ram m i h) hch
  have hA : A.pc = K.store := hs.pc.symm.trans hpc
  by_cases hn : m.nmiPending = true
  · unfold StepWrites.stepLocs at hloc
    rw [if_pos hn] at hloc
    have := PositionWriters.stk_range 3 _ _ hloc
    have := hP.lo
    omega
  · have hn' : A.nmi = false := by rw [← hs.nmi]; simpa using hn
    simp only [storeOK, hA, bne_self_eq_false, hn', Bool.false_or] at hok
    have hp0 : 0x8000 ≤ m.pc := by rw [hpc]; exact hP.s0
    have hp1 : m.pc + 1 ≥ 0x8000 := by rw [hpc]; exact hP.s1
    have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0x91 := by rw [hs.prg, hs.mask, hpc]; exact hP.op
    unfold StepWrites.stepLocs at hloc
    rw [if_neg hn, if_neg (by rw [hs.halted]; decide), PositionWriters.fetchP hp0] at hloc
    dsimp only at hloc
    rw [hop] at hloc
    have e1 : StepWrites.wOf 0x91 = StepWrites.wIzy := rfl
    rw [e1] at hloc
    simp only [StepWrites.Wr.locs] at hloc
    have ew : (go mIzy { m with pc := m.pc + 1 }).1 = ScreenPage.writeAddr m := rfl
    rw [ew, RoomBlocks.writeAddr_eq hp1] at hloc
    have hz : RoomBlocks.operand m = E.prg.get! ((K.store + 1) &&& E.mask).toNat := by
      unfold RoomBlocks.operand
      rw [hs.prg, hs.mask, hpc]
    rw [hz] at hloc
    cases ht : storeT E K A with
    | none =>
      rw [ht] at hok
      simp at hok
    | some t =>
      rw [ht] at hok
      dsimp only at hok
      unfold storeT at ht
      by_cases hk : ((A.getK ((E.prg.get! ((K.store + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat).isK &&
          (A.getK (((E.prg.get! ((K.store + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat).isK && A.y.isK) = true
      · rw [if_pos hk] at ht
        have et := (Option.some.inj ht).symm
        simp only [Bool.and_eq_true] at hk
        obtain ⟨⟨hlo, hhi⟩, hy⟩ := hk
        have e2 : RoomBlocks.ptrZ m (E.prg.get! ((K.store + 1) &&& E.mask).toNat) + m.y.toUInt16 = t := by
          rw [et]
          unfold RoomBlocks.ptrZ
          rw [known_eq hlo (hs.ram _ (PipeTransitionAll.mask_lt _)), known_eq hhi (hs.ram _ (PipeTransitionAll.mask_lt _)), known_eq hy hs.y]
        rw [e2] at hloc
        unfold StepWrites.ramIdx at hloc
        split at hloc
        · rename_i hlt
          simp only [List.mem_singleton] at hloc
          subst hloc
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hok
          rcases hok with (h3 | h3) | h3
          · exact absurd hlt h3
          · have hin : PoleTileWalk.inBufB K.Q (t &&& 0x7FF).toNat = true := by
              simp only [PoleTileWalk.inBufB, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨h1, h2⟩
            rw [hin] at h3
            cases h3
          · exact h3
        · simp at hloc
      · rw [if_neg hk] at ht
        cases ht

end

/-- every machine is in a piece of `prePage` -/
theorem cov_prePage {E : Env} {F : Nat × UInt8} {K : Bc} (hP : PlacesB K E) {A : AS} {m : Machine} (hs : Sim E F A m) :
    ∃ B ∈ prePage K A, Sim E F B m ∧ B.k = A.k := by
  unfold prePage
  have e1 : (m.ram.get! K.pageI).toNat.toUInt8 = m.ram.get! K.pageI := by simp [Nat.toUInt8_eq]
  dsimp only
  split
  · have hm : (m.ram.get! K.pageI) &&& (A.getK K.pageI).k = (A.getK K.pageI).v &&& (A.getK K.pageI).k := hs.ram _ hP.pageI
    refine ⟨A.setK K.pageI (AB.known (m.ram.get! K.pageI).toNat.toUInt8),
      List.mem_map.2 ⟨(m.ram.get! K.pageI).toNat, List.mem_filter.2 ⟨List.mem_range.2 (m.ram.get! K.pageI).toNat_lt, by rw [e1, hm]; simp⟩, rfl⟩,
      PipeEntryRule.sim_setK' hs ?_, rfl⟩
    rw [e1]
    exact TaintRun.mem_known_self _
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- every machine is in a piece of `preB` -/
theorem cov_preB {C : CfgK} {F : Nat × UInt8} {K : Bc} (hP : PlacesB K C.E) {A : AS} {m : Machine} (hc : CleanK C.G C.S.store m) (hs : Sim C.E F A m) :
    ∃ B ∈ preB C K A, Sim C.E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨D, hD, h3, h4⟩ := cov_prePage hP h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

/-! ## One frame -/

section
variable {C : CfgK} {K : Bc} {b : Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveB (C : CfgK) (K : Bc) (b : Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkB C K b n A = true

theorem cover_liveB (ht : C.t.all (walkB C K b Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverK C B = true) :
    ∃ D, LiveB C K b F D m ∧ D.k = B.k := by
  unfold coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨TaintRun.sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

/-- **One step from a live state**: the store's fact, and the next live state or the frame's end with `endB` -/
theorem live_stepB (hP : PlacesB K C.E) (ht : C.t.all (walkB C K b Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveB C K b F A m) (hh : CleanK C.G C.S.store m) :
    (m.pc = K.store → StoreRing K b m) ∧
    ((∃ A', LiveB C K b F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
      ((go step m).2.frame = m.frame + 1 ∧ ∃ B, endB K B = true ∧ Sim C.E F B (go step m).2)) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkB] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preB hP hh hs
    obtain ⟨r, hr1, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkB, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨hst, hw1⟩ := hw1
    have hw2 := hw1 r hr1
    refine ⟨fun hpc => store_ring hP hs1 hpc hst, ?_⟩
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveB ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true] at hw2
        exact ⟨k2, B, hw2.2, h1⟩

/-- **One frame from a walk**: the store's fact at each parser's store of the frame, and `endB` at the frame's end -/
theorem frame_of_walkB (hP : PlacesB K C.E) (ht : C.t.all (walkB C K b Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top) {S : AS} {m : Machine} {i : UInt8} (hw : walkB C K b Fu S = true) (hs : Sim C.E F S m)
    (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) :
    (∀ j, (trace m i j).pc = K.store → StoreRing K b (trace m i j)) ∧
      ∃ B, endB K B = true ∧ Sim C.E F B (PipeTransition.frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact TaintRun.mem_top _ }
  have key : ∀ j, (∃ A, LiveB C K b F A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, endB K B = true ∧ Sim C.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero => exact Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, Nat.le_refl _⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨A, h1, h3, h4⟩ | ⟨h1, B, h2, h4⟩
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        rcases (live_stepB hP ht hkl hops hT h1 (hk j)).2 with ⟨A', a1, _, a3, a4⟩ | ⟨a1, B, a2, a4⟩
        · exact Or.inl ⟨A', a1, by rw [a3, h3], by omega⟩
        · exact Or.inr ⟨by rw [a1, h3], B, a2, a4⟩
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact Or.inr ⟨h1, B, h2, h4⟩
  refine ⟨fun j hpc => ?_, ?_⟩
  · rcases key j with ⟨A, h1, _, _⟩ | ⟨_, B, h2, h4⟩
    · exact (live_stepB hP ht hkl hops hT h1 (hk j)).1 hpc
    · exfalso
      simp only [endB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
      exact h2.1.1.1.1.1 (h4.pc.symm.trans hpc)
  · rw [frame_trace]
    rcases key fuelPerFrame with ⟨A, h1, _, h4⟩ | ⟨_, B, h2, h4⟩
    · exfalso
      have a1 := h1.1.hi
      have a2 := h1.1.lim
      have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
      omega
    · exact ⟨B, h2, h4⟩

end

/-! ## One frame in control -/

section
variable {S : FrameKeep.Spot} {G : Guard} {E : Env} {K : Bc}

theorem and1_toNat (x : UInt8) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [UInt8.toNat_and]
  exact Nat.and_one_is_mod _

theorem toU8_toNat {n : Nat} (h : n < 256) : (n.toUInt8).toNat = n := by
  simp [Nat.toUInt8_eq]
  omega

/-- `BInv` from a state that `endB` accepts -/
theorem inv_of_end {F : Nat × UInt8} {B : AS} {m : Machine} (hP : PlacesB K E) (hs : Sim E F B m) (h : endB K B = true) : BInv K m := by
  simp only [endB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have eB := known_eq h1 (hs.ram _ hP.bI)
  have eC := known_eq h2 (hs.ram _ hP.colI)
  have hp : (m.ram.get! K.pageI) &&& (B.getK K.pageI).k = (B.getK K.pageI).v &&& (B.getK K.pageI).k := hs.ram _ hP.pageI
  have ep : (m.ram.get! K.pageI) &&& 1 = (B.getK K.pageI).v &&& 1 := by
    have e1 : ((m.ram.get! K.pageI) &&& (B.getK K.pageI).k) &&& 1 = ((B.getK K.pageI).v &&& (B.getK K.pageI).k) &&& 1 := by rw [hp]
    rwa [UInt8.and_assoc, UInt8.and_assoc, h3] at e1
  have ep' : (m.ram.get! K.pageI).toNat % 2 = ((B.getK K.pageI).v &&& 1).toNat := by rw [← and1_toNat, ep]
  refine ⟨?_, ?_⟩
  · rw [eB, eC, h5]
    omega
  · rw [eC]
    exact h4

/-- the state of the piece `b` covers a machine with `BInv` and `B = b` -/
theorem sim_startB {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hI : BInv K m) :
    Sim E F (((A.setK K.bI (AB.known (m.ram.get! K.bI).toNat.toUInt8)).setK K.colI (AB.known ((m.ram.get! K.bI).toNat % 16).toUInt8)).setK K.pageI
      ⟨((m.ram.get! K.bI).toNat / 16).toUInt8, 1⟩) m := by
  obtain ⟨h1, h2⟩ := hI
  have hb := (m.ram.get! K.bI).toNat_lt
  have hp := (m.ram.get! K.pageI).toNat_lt
  have e1 : (m.ram.get! K.bI).toNat.toUInt8 = m.ram.get! K.bI := UInt8.toNat_inj.1 (toU8_toNat hb)
  have e2 : ((m.ram.get! K.bI).toNat % 16).toUInt8 = m.ram.get! K.colI := by
    apply UInt8.toNat_inj.1
    rw [toU8_toNat (by omega)]
    omega
  refine PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' (PipeEntryRule.sim_setK' hs ?_) ?_) ?_
  · rw [e1]
    exact TaintRun.mem_known_self _
  · rw [e2]
    exact TaintRun.mem_known_self _
  · show m.ram.get! K.pageI &&& 1 = ((m.ram.get! K.bI).toNat / 16).toUInt8 &&& 1
    apply UInt8.toNat_inj.1
    rw [and1_toNat, and1_toNat, toU8_toNat (by omega)]
    omega

end

/-- **`NoTileM` from the store's fact**: a byte that the step changes is in the ring's column of `c` -/
theorem noTileM_of_ring {K : Bc} {c : Nat} {m : Machine} (h : StoreRing K (c % 32) m) : PoleRing.NoTileM K.Q c m :=
  fun i h1 h2 hch _ => Or.inr (h i h1 h2 hch)

/-! ## One frame in control, and the frames up to the touch's frame -/

section
variable {S : FrameKeep.Spot} {G : Guard} {E : Env} {K : Bc}

/-- what the check says -/
structure BcolOK (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Bc) : Prop where
  places : PlacesB K E
  walks : ∀ b, b < 32 → (cfgB S G E K b).t.all (walkB (cfgB S G E K b) K b fuelK) = true ∧ walkB (cfgB S G E K b) K b fuelK (startB G K b false) = true ∧
    walkB (cfgB S G E K b) K b fuelK (startB G K b true) = true

theorem bcolOK_of_check (h : bcolCheckW S G E K = true) : BcolOK S G E K := by
  simp only [bcolCheckW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨placesB_spec h1, fun b hb => by
    have h3 := h2 b hb
    exact ⟨h3.1.1, h3.1.2, h3.2⟩⟩

/-- **One frame in control**: a frame from `FrameStart` with `BInv`, whose instructions meet `CleanK` of the walk's guard, ends with `BInv`, and its parser's store
writes only in the ring's column `B` of its start -/
theorem frame_bcol (hc : bcolCheckW S G E K = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hI : BInv K m)
    (hk : ∀ j, CleanK G S.store (trace m i j)) :
    BInv K (PipeTransition.frame m i) ∧ ∀ j, (trace m i j).pc = K.store → StoreRing K (m.ram.get! K.bI).toNat (trace m i j) := by
  have hC := bcolOK_of_check hc
  have hb : (m.ram.get! K.bI).toNat < 32 := by
    rw [hI.1]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨late, hs⟩ := FrameKeep.sim_startK (W := []) hE h0 (fun _ h => by cases h)
  have hs1 := sim_startB hs hI
  obtain ⟨w1, w2, w3⟩ := hC.walks _ hb
  have hw0 : walkB (cfgB S G E K (m.ram.get! K.bI).toNat) K (m.ram.get! K.bI).toNat fuelK (startB G K (m.ram.get! K.bI).toNat late) = true := by
    cases late with
    | false => exact w2
    | true => exact w3
  obtain ⟨h1, B, h2, h3⟩ := frame_of_walkB (C := cfgB S G E K (m.ram.get! K.bI).toNat) (F := (m.frame, 2)) hC.places w1 rfl rfl
    (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs1 hk
  exact ⟨inv_of_end hC.places h3 h2, h1⟩

/-- **No store through an index or a pointer writes `B`**, from `BcR` -/
theorem b_of_R {m : Machine} (h : BcR K m) : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ K.bI := by
  cases hf : PoleKeepFar.farStore [K.bI] m with
  | false => exact h hf
  | true =>
    intro t ht hlt e
    exact PoleKeepFar.far_target hf t ht hlt (by rw [e]; exact List.mem_singleton.2 rfl)

end

/-- the column and the page are protected by `FrameKeep.guardE` (they are bytes of `FrameKeep.parE`), and so is every byte of `FrameKeep.guardK` -/
theorem prot_E {sy : Syms} {m0 : Machine} :
    ∀ x ∈ (bcOf sy m0).colI :: (bcOf sy m0).pageI :: (FrameKeep.guardK sy m0).prot, x ∈ (FrameKeep.guardE sy m0).prot := by
  intro x hx
  simp only [List.mem_cons] at hx
  have hc : (bcOf sy m0).colI ∈ FrameKeep.parE sy m0 := by simp [FrameKeep.parE, bcOf]
  have hp : (bcOf sy m0).pageI ∈ FrameKeep.parE sy m0 := by simp [FrameKeep.parE, bcOf]
  rcases hx with rfl | rfl | hx
  · simp [FrameKeep.guardE, hc]
  · simp [FrameKeep.guardE, hp]
  · simp [FrameKeep.guardE, FrameKeep.guardF, hx]

set_option maxRecDepth 100000 in
/-- the walk's guard: `CleanK` of it from `CleanK` of `FrameKeep.guardE` and `BcR` -/
theorem cleanK_B {sy : Syms} {m0 : Machine} {m : Machine} (h : CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store m) (hr : BcR (bcOf sy m0) m) :
    CleanK (guardB sy m0) (FrameKeep.spotOf sy m0).store m :=
  PoleCoin.cleanK_one (G := { FrameKeep.guardK sy m0 with prot := (bcOf sy m0).colI :: (bcOf sy m0).pageI :: (FrameKeep.guardK sy m0).prot })
    (FrameKeep.cleanK_sub h prot_E rfl rfl rfl rfl) (b_of_R hr)

/-- the start of a frame for the walk's guard: the same as for `FrameKeep.guardK` -/
theorem start_B {sy : Syms} {m0 : Machine} {m : Machine} (h : FrameKeep.StartK sy m0 m) : FrameStart (guardB sy m0) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- **On every frame up to the touch's frame `BInv` holds at the start, and the parser's store writes only in the ring's column `B` of the frame's start**: from
`BInv` at control (`hI0`), the walk of `FrameKeep` (`hcK`: every frame starts in control), the walk of this file (`hcB`), the field `keep.cleanE` and `BcR` on
each instruction (`hct`) -/
theorem frames_bcol {sy : Syms} {m0 : Machine} {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hcK : FrameKeep.keepCheckOf sy m0 = true)
    (hcB : bcolCheck sy m0 = true) (Fr : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0))
    (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0)) (hI0 : BInv (bcOf sy m0) (seq 0))
    (hct : ∀ n, n < Fr.ix g → ∀ k, BcR (bcOf sy m0) (trace (Fr.all n) (Fr.inp n) k)) :
    ∀ n, n < Fr.ix g → BInv (bcOf sy m0) (Fr.all n) ∧
      ∀ k, (trace (Fr.all n) (Fr.inp n) k).pc = (bcOf sy m0).store → StoreRing (bcOf sy m0) ((Fr.all n).ram.get! (bcOf sy m0).bI).toNat (trace (Fr.all n) (Fr.inp n) k) := by
  have e0 : seq 0 = Fr.all 0 := by rw [Fr.at_ix 0 (Nat.zero_le _), Fr.ix0]
  have one : ∀ n, n < Fr.ix g → BInv (bcOf sy m0) (Fr.all n) →
      BInv (bcOf sy m0) (PipeTransition.frame (Fr.all n) (Fr.inp n)) ∧
      ∀ k, (trace (Fr.all n) (Fr.inp n) k).pc = (bcOf sy m0).store → StoreRing (bcOf sy m0) ((Fr.all n).ram.get! (bcOf sy m0).bI).toNat (trace (Fr.all n) (Fr.inp n) k) := by
    intro n hn hI
    obtain ⟨a1, _⟩ := Fr.all_start hcK hs0 h0 n hn
    exact frame_bcol hcB rfl (start_B a1) hI (fun j => cleanK_B (Fr.cleanE n hn j) (hct n hn j))
  have invs : ∀ n, n < Fr.ix g → BInv (bcOf sy m0) (Fr.all n) := by
    intro n
    induction n with
    | zero => exact fun _ => e0 ▸ hI0
    | succ i ih =>
      intro hi
      rw [Fr.next i]
      exact (one i (by omega) (ih (by omega))).1
  intro n hn
  exact ⟨invs n hn, (one n hn (invs n hn)).2⟩

end Smbrta.PoleBcol
