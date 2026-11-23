import Theorems.PoleRing

/-!
# The screen buffers' control byte above ground: no coin in the block buffers, so it is not 6 at `UpdScrollVar`

`PoleJoin.Run.ctlU` asked, on each frame before the touch's frame, at `UpdScrollVar`: the screen buffers' control byte is not 6, or the parser's lag `S + 3·N` is
below 157 there. In the game core, before `UpdScrollVar`, the code writes the control byte only when it erases a coin or the axe (`RemoveCoin_Axe`, which writes 6).
It erases a coin when the player's collision routine finds a coin's tile, or when the check above a bumped block finds one (`CheckTopOfBlock`). The screen
update at the start of the frame sets the control byte to 0.

Here one walk of the whole frame in control (`walkC`, the walk of `FrameKeep` with more tests) follows the control byte, and cuts the coin's branch:

* the guard of the walk protects the control byte too (`guardC`), so a store whose target the walk does not know keeps it; that is asked of each instruction
  (`CtlR`, with `PoleKeepFar.farStore`);
* right after the collision routine's read of the block buffers with `X` = 0 (the player's), and right after the read above a bumped block, the byte read is
  split into pieces that are not a coin's tile (`pieceC`), when no coin's tile is there (`CoinRead`);
* that comes from a map of the frame's start, kept by every step (`ColMap` of the places `Coin.Q`, whose two tiles are the coin's tiles and which has no column:
  no coin's tile in the block buffers): a step writes no byte of the block buffers (`PoleTileWalk.okSK`), or it is a store through an index or a pointer, which
  writes no coin's tile there (`BufAt`, asked of each instruction); the player's read of a coin's tile is in the block buffers (`ReadC`, asked of each read; an
  `LDA (zp),Y` keeps `X`: `step_lda_izy_x`); the state after
  such a read comes from the read (`pairC`);
* a path stops at an instruction that writes the routine, the mode or the task by its address (`FrameKeep.Frames.noStore`): the axe's code writes the mode;
* at `UpdScrollVar` the control byte is known and not 6 (`ctlOK`).

So a frame in control keeps the map and has the control byte not 6 at `UpdScrollVar` (`frame_coin`), and so do all the frames before the touch's frame, from the
map at control (`frames_coin`). The walk's table comes from a search, no part of the proof. There is no game data in this file.
Page: `1-1/f-6-17-17-PoleCoin.md`.
-/

namespace Smbrta.PoleCoin

open TaintRun (AS Env Sim AB aRows AM)
open PipeTransitionAll (go)
open PipeEntryRule (trace nxt frame_trace neBit known_eq)
open PoleEntryRule (Spots)
open PipeWrites (Guard FrameStart wTarget opAt knownOf SG)
open FrameKeep (CfgK coverK preK kstep startK fuelK CleanK storesTo)
open PoleTileWalk (ColMap BufAt okSK)

/-! ## The places -/

/-- what the walk knows: the places of the coin's map (the block buffers, with the two coin's tiles in place of the pole's and no column), the collision
routine's read of the block buffers, the read above a bumped block, `UpdScrollVar`, and the RAM index of the screen buffers' control byte -/
structure Coin where
  Q : Spots
  read : UInt16
  top : UInt16
  upd : UInt16
  ctlI : Nat
  deriving Inhabited

/-- the places, from the symbols and the ROM: the two coin's tiles are the operands of the two comparisons of the coin's check; the control byte is the operand of
the first load of `UpdScrollVar` (as `PoleParser.places`) -/
def coinOf (sy : Syms) (m0 : Machine) : Coin :=
  let Q0 := PoleFrame.spotsF sy m0
  let c1 := sy.CoinTile.toUInt8
  let c2 := sy.CoinTile2.toUInt8
  { Q := { Q0 with ball := c1, shaft := c2, bits := TaintRun.bitList.filter (· != c1 ^^^ c2), dC := 2048 }
    read := Q0.read
    top := PipeEntryRule.findOp m0 sy.CheckTopOfBlock 0xB1 32
    upd := sy.UpdScrollVar
    ctlI := (FrameKeep.romWE m0 (sy.UpdScrollVar + 1) &&& 0x7FF).toNat }

/-- **The guard of the walk**: `FrameKeep.guardK` with the control byte protected too -/
def guardC (sy : Syms) (m0 : Machine) : Guard :=
  { FrameKeep.guardK sy m0 with prot := (coinOf sy m0).ctlI :: (FrameKeep.guardK sy m0).prot }

/-! ## The conditions -/

/-- **What is assumed of a read** (one state, before it): at the player's read of the collision routine (`X` = 0), or at the read above a bumped block, if the
byte read is a coin's tile, the read is in the RAM, in the block buffers -/
def ReadC (K : Coin) (m : Machine) : Prop :=
  ((m.pc = K.read ∧ m.x = 0) ∨ m.pc = K.top) → PoleTiles.Tile K.Q (ScreenPage.readVal m) →
    ScreenPage.readAddr m < 0x2000 ∧ K.Q.bufLo ≤ PoleTileWalk.readI m ∧ PoleTileWalk.readI m < K.Q.bufLo + K.Q.bufBytes

/-- right after such a read, the byte read is not a coin's tile (proved on the way) -/
def CoinRead (K : Coin) (m : Machine) : Prop := ((m.pc = K.read + 2 ∧ m.x = 0) ∨ m.pc = K.top + 2) → ¬ PoleTiles.Tile K.Q m.a

/-- **What is assumed of a store** (one instruction): a store through an index or a pointer that `PoleKeepFar.farStore` does not settle does not write the
control byte -/
def CtlR (K : Coin) (m : Machine) : Prop :=
  PoleKeepFar.farStore [K.ctlI] m = false → ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ K.ctlI

/-- `CtlR`, for a program -/
def ctlRB (K : Coin) (m : Machine) : Bool :=
  PoleKeepFar.farStore [K.ctlI] m ||
    match wTarget (opAt m) m with
    | some t => !(decide (t < 0x2000) && (t &&& 0x7FF).toNat == K.ctlI)
    | none => true

/-- `ReadC`, for a program -/
def readCB (K : Coin) (m : Machine) : Bool :=
  !((m.pc == K.read && m.x == 0) || m.pc == K.top) || !PoleTiles.tileB K.Q (ScreenPage.readVal m) ||
    (decide (ScreenPage.readAddr m < 0x2000) && decide (K.Q.bufLo ≤ PoleTileWalk.readI m) && decide (PoleTileWalk.readI m < K.Q.bufLo + K.Q.bufBytes))

/-! ## The walk -/

/-- right after the player's read of the collision routine (`X` known 0), or right after the read above a bumped block -/
def atRead (K : Coin) (A : AS) : Bool := (A.pc == K.read + 2 && A.x.isK && A.x.v == 0) || A.pc == K.top + 2

/-- the pieces there: a bit at which the byte read differs from both coin's tiles -/
def pieceC (K : Coin) (A : AS) : List AS :=
  if atRead K A then K.Q.bits.map fun b => { A with a := neBit K.Q.ball b } else [A]

/-- all the pieces before a step: those of `FrameKeep`, then these -/
def preC (C : CfgK) (K : Coin) (A : AS) : List AS := (preK C.S C.G A).flatMap (pieceC K)

/-- at `UpdScrollVar` the control byte is known and not 6 -/
def ctlOK (K : Coin) (A : AS) : Bool := A.pc != K.upd || ((A.getK K.ctlI).isK && (A.getK K.ctlI).v != 6)

/-- a state right after one of the two reads comes from the read, with no NMI pending -/
def pairC (K : Coin) (A₁ B : AS) : Bool :=
  (B.pc != K.read + 2 || (A₁.pc == K.read && !A₁.nmi)) && (B.pc != K.top + 2 || (A₁.pc == K.top && !A₁.nmi))

/-- **The walk**: `FrameKeep.walkKC` with the pieces, the tests `ctlOK`, `okSK` and `pairC` on the way, and no condition at the frame's end -/
def walkC (C : CfgK) (K : Coin) (l : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => storesTo l C.E.prg C.E.mask A.pc || (preC C K A).all fun A₁ => ctlOK K A₁ && okSK C.E K.Q A₁ && (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => pairC K A₁ B && (if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkC C K l n B else B.k == A.k + 1)

/-- the facts of the ROM and of the places that the proof uses -/
def placesOK (K : Coin) (E : Env) (G : Guard) : Bool :=
  decide (0x8000 ≤ K.read) && E.prg.get! (K.read &&& E.mask).toNat == 0xB1 && decide (0x8000 ≤ K.top) && E.prg.get! (K.top &&& E.mask).toNat == 0xB1 &&
    G.idle != K.read + 2 && G.idle != K.top + 2 && decide (K.ctlI < 2048) && decide (K.Q.dC = 2048) && decide (K.Q.bufLo + K.Q.bufBytes ≤ 2048) &&
    PoleEntryRule.tilesCover K.Q

/-- what `placesOK` says -/
structure PlacesOK (K : Coin) (E : Env) (G : Guard) : Prop where
  r0 : 0x8000 ≤ K.read
  rop : E.prg.get! (K.read &&& E.mask).toNat = 0xB1
  t0 : 0x8000 ≤ K.top
  top : E.prg.get! (K.top &&& E.mask).toNat = 0xB1
  idleR : G.idle ≠ K.read + 2
  idleT : G.idle ≠ K.top + 2
  ctl : K.ctlI < 2048
  dC : K.Q.dC = 2048
  buf : K.Q.bufLo + K.Q.bufBytes ≤ 2048
  cover : PoleEntryRule.tilesCover K.Q = true

theorem placesOK_spec {K : Coin} {E : Env} {G : Guard} (h : placesOK K E G = true) : PlacesOK K E G := by
  simp only [placesOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## Finding the table: a search, no part of the proof -/

/-- a coin's piece: one known bit, where the byte differs from the first coin's tile -/
def pieceOf (K : Coin) (b : AB) : Nat :=
  match K.Q.bits.findIdx? (fun c => b.k == c && b.v &&& c == (~~~K.Q.ball) &&& c) with
  | some i => i + 1
  | none => 0

/-- what the search forgets: as `FrameKeep.normK`, but in the collision routine it keeps the two zero page bytes that hold a byte read (`Spots.tempI`,
`Spots.cntI`) -/
def normC (S : FrameKeep.Spot) (G : Guard) (K : Coin) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let keep := if FrameKeep.inMove S A.pc then S.temps ++ G.prot else G.prot
  let keep := if PipeWrites.inZone G A then K.Q.tempI :: K.Q.cntI :: keep else keep
  let B := PipeWrites.AS.forgetW keep A
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
  { B with kn }

/-- the key: as `FrameKeep.keyK`, and in the collision routine the index and the coin's pieces in A and in the two zero page bytes keep states apart -/
def keyC (S : FrameKeep.Spot) (G : Guard) (K : Coin) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := FrameKeep.keyK S G [] A
  if PipeWrites.inZone G A then
    (((n * 65536 + num A.x) * 16 + pieceOf K A.a) * 16 + pieceOf K (A.getK K.Q.tempI)) * 16 + pieceOf K (A.getK K.Q.cntI)
  else n

/-- the search's step into the table -/
def routeC (S : FrameKeep.Spot) (G : Guard) (K : Coin) (X : SG) (B0 : AS) : SG :=
  let B := normC S G K B0
  let key := keyC S G K B
  match X.pending[key]? with
  | some Q =>
    match X.done[key]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert key J, done := X.done.insert key (J, some l'), multi := X.multi.insert key () }
    | none => X
  | none =>
    match X.done[key]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert key (), done := X.done.insert key (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD key 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert key J, done := X.done.insert key (J, some l'), multi := X.multi.insert key (), arr := X.arr.insert key (c + 1) }
    | none => { X with pending := X.pending.insert key B, done := X.done.insert key (B, none) }

/-- the pieces before a step, for the search -/
def preS (S : FrameKeep.Spot) (G : Guard) (K : Coin) (A : AS) : List AS := (preK S G A).flatMap (pieceC K)

partial def runC (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    if storesTo l E.prg E.mask cur.pc then break
    let rs := (preS S G K cur).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some _ => false
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !storesTo l E.prg E.mask b.pc && !atRead K b &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeC S G K X b
    break
  return X

partial def searchC (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      X := runC S G E K l ops X A
  return X

/-- the search from the two states of a frame's start -/
def searchOfC (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) : SG :=
  searchC S G E K l (aRows E).toArray ([startK G [] false, startK G [] true].foldl (routeC S G K) {})

/-- **The walk's table** -/
def cfgC (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) : CfgK :=
  let key := keyC S G K
  let q := FrameKeep.tableOfKW key (searchOfC S G E K l)
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- **The check**: the facts of the places, and the walk from every state of the table and from the two states of a frame's start -/
def coinCheckW (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) : Bool :=
  let C := cfgC S G E K l
  placesOK K E G && C.t.all (walkC C K l fuelK) && walkC C K l fuelK (startK G [] false) && walkC C K l fuelK (startK G [] true)

/-- **The check on the ROM** -/
def coinCheck (sy : Syms) (m0 : Machine) : Bool :=
  coinCheckW (FrameKeep.spotOf sy m0) (guardC sy m0) (PipeEntryRule.envOf m0) (coinOf sy m0) (FrameKeep.ctlI sy)

/-! ## An `LDA (zp),Y` keeps X -/

section
open PipeTransitionAll (go)

theorem tick_x (c : Nat) (x : Machine) : (go (tick c) x).2.x = x.x := by
  rw [PipeTransitionAll.tick_eq]
  simp only [PipeTransitionAll.tick4, PipeTransitionAll.tick3, PipeTransitionAll.tick2, PipeTransitionAll.tick1]
  repeat' split
  all_goals rfl

theorem rd_x (a : UInt16) (m : Machine) : (go (rd a) m).2.x = m.x := by
  unfold rd go
  by_cases h1 : a < 0x2000
  · simp only [h1, if_true]
    by_cases ht : m.trk = true
    · simp [ht, trackRead, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
      split <;> rfl
    · simp [ht, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
  · simp only [h1, if_false]
    by_cases h2 : a ≥ 0x8000
    · simp [h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
    · simp only [h2, if_false]
      by_cases h3 : a < 0x4000
      · simp only [h3, if_true]
        by_cases ht : m.trk = true
        · simp [ht, ppuRead, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, set, StateT.set, MonadStateOf.set]
          split <;> rfl
        · simp [ht, ppuRead, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, MonadStateOf.set]
          split <;> rfl
      · simp only [h3, if_false]
        by_cases h4 : (a == 0x4016) = true
        · simp only [h4, if_true]
          by_cases ht : m.trk = true
          · simp [ht, padRead, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, set, StateT.set, MonadStateOf.set]
            split <;> rfl
          · simp [ht, padRead, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, set, StateT.set, MonadStateOf.set]
            split <;> rfl
        · rw [if_neg h4]
          split <;> rfl

theorem fetch_x (m : Machine) : (go fetch m).2.x = m.x := by
  have e : go fetch m = go (rd m.pc) { m with pc := m.pc + 1 } := rfl
  rw [e, rd_x]

theorem rd16zp_x (z : UInt8) (m : Machine) : (go (rd16zp z) m).2.x = m.x := by
  have e : go (rd16zp z) m = go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m := rfl
  rw [e, PipeTransitionAll.go_bind, PipeTransitionAll.go_bind]
  show (go (rd (z + 1).toUInt16) (go (rd z.toUInt16) m).2).2.x = m.x
  rw [rd_x, rd_x]

theorem pagePenalty_x (b e : UInt16) (x : Machine) : (go (pagePenalty b e) x).2.x = x.x := by
  unfold pagePenalty
  split
  · exact tick_x 1 x
  · rfl

theorem mIzyR_x (m : Machine) : (go mIzyR m).2.x = m.x := by
  have e : go mIzyR m = go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s => pagePenalty b (b + s.y.toUInt16) >>= fun _ => pure (b + s.y.toUInt16)) m := rfl
  rw [e, PipeTransitionAll.go_bind, PipeTransitionAll.go_bind]
  show (go (get >>= fun s => pagePenalty _ (_ + s.y.toUInt16) >>= fun _ => pure _) (go (rd16zp _) (go fetch m).2).2).2.x = m.x
  rw [PipeTransitionAll.go_bind]
  show (go (pagePenalty _ _ >>= fun _ => pure _) (go (rd16zp _) (go fetch m).2).2).2.x = m.x
  rw [PipeTransitionAll.go_bind]
  show (go (pagePenalty _ _) (go (rd16zp _) (go fetch m).2).2).2.x = m.x
  rw [pagePenalty_x, rd16zp_x, fetch_x]

/-- **An `LDA (zp),Y` keeps X** -/
theorem step_lda_izy_x {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1) : (go step m).2.x = m.x := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), ScreenPage.op_B1, ScreenPage.cyc_B1]
  rw [PipeTransitionAll.go_bind, tick_x]
  have e2 : go (opLDA mIzyR) { m with pc := m.pc + 1 } = go (mIzyR >>= fun ad => rd ad >>= fun v => setA v) { m with pc := m.pc + 1 } := rfl
  rw [e2, PipeTransitionAll.go_bind, PipeTransitionAll.go_bind]
  show (go (setA _) (go (rd _) (go mIzyR { m with pc := m.pc + 1 }).2).2).2.x = m.x
  show (go (rd _) (go mIzyR { m with pc := m.pc + 1 }).2).2.x = m.x
  rw [rd_x, mIzyR_x]

end

/-! ## One step -/

section
variable {E : Env} {F : Nat × UInt8} {K : Coin}

/-- every machine that meets `CoinRead` is in a piece -/
theorem cov_pieceC (hcv : PoleEntryRule.tilesCover K.Q = true) {A : AS} {m : Machine} (hs : Sim E F A m) (hr : CoinRead K m) :
    ∃ B ∈ pieceC K A, Sim E F B m ∧ B.k = A.k := by
  unfold pieceC
  split
  · rename_i h
    have hc : (m.pc = K.read + 2 ∧ m.x = 0) ∨ m.pc = K.top + 2 := by
      simp only [atRead, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨h1, h2⟩, h3⟩ | h1
      · exact Or.inl ⟨hs.pc.trans h1, by rw [known_eq h2 hs.x, h3]⟩
      · exact Or.inr (hs.pc.trans h1)
    have ht := hr hc
    obtain ⟨b, hb1, hb2⟩ := PoleEntryRule.tile_bit hcv (fun e => ht (Or.inl e)) (fun e => ht (Or.inr e))
    exact ⟨_, List.mem_map.2 ⟨b, hb1, rfl⟩, { hs with a := hb2 }, rfl⟩
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- every machine is in a piece of `preC` -/
theorem cov_preC {C : CfgK} (hcv : PoleEntryRule.tilesCover K.Q = true) {A : AS} {m : Machine} (hc : CleanK C.G C.S.store m) (hs : Sim C.E F A m)
    (hr : CoinRead K m) : ∃ B ∈ preC C K A, Sim C.E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨D, hD, h3, h4⟩ := cov_pieceC hcv h1 hr
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

/-- **`ctlOK` on the machine**: at `UpdScrollVar` the control byte is not 6 -/
theorem ctl_of_ok {A : AS} {m : Machine} (hs : Sim E F A m) (hok : ctlOK K A = true) (hi : K.ctlI < 2048) (hpc : m.pc = K.upd) : m.ram.get! K.ctlI ≠ 6 := by
  simp only [ctlOK, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true] at hok
  rcases hok with h | ⟨h1, h2⟩
  · exact absurd (hs.pc.symm.trans hpc) h
  · rw [known_eq h1 (hs.ram _ hi)]
    exact h2

/-- **Right after one of the two reads, the byte read is not a coin's tile**: the read before it is one of the reads, with no NMI pending (`pairC`); a coin's tile
read is in the block buffers (`ReadC`), where the map has none -/
theorem coinRead_after (hP : PlacesOK K E G) {A₁ B : AS} {m : Machine} (hs : Sim E F A₁ m) (hsB : Sim E F B (go step m).2)
    (hpair : pairC K A₁ B = true) (hm : ColMap K.Q m) (hrd : ReadC K m) : CoinRead K (go step m).2 := by
  intro hpc htile
  simp only [pairC, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at hpair
  obtain ⟨hp1, hp2⟩ := hpair
  have key : ((m.pc = K.read ∧ (go step m).2.x = 0) ∨ m.pc = K.top) ∧ m.nmiPending = false ∧ 0x8000 ≤ m.pc ∧
      m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by
    rcases hpc with ⟨h, hx⟩ | h
    · have hB : B.pc = K.read + 2 := by rw [← hsB.pc]; exact h
      rcases hp1 with h1 | ⟨h1, h2⟩
      · exact absurd hB h1
      · have e : m.pc = K.read := hs.pc.trans h1
        refine ⟨Or.inl ⟨e, hx⟩, hs.nmi.trans h2, by rw [e]; exact hP.r0, ?_⟩
        rw [hs.prg, hs.mask, e]
        exact hP.rop
    · have hB : B.pc = K.top + 2 := by rw [← hsB.pc]; exact h
      rcases hp2 with h1 | ⟨h1, h2⟩
      · exact absurd hB h1
      · have e : m.pc = K.top := hs.pc.trans h1
        refine ⟨Or.inr e, hs.nmi.trans h2, by rw [e]; exact hP.t0, ?_⟩
        rw [hs.prg, hs.mask, e]
        exact hP.top
  obtain ⟨hpc0, hn, hp0, hop⟩ := key
  obtain ⟨ha, _⟩ := RoomBlocks.step_lda_izy hn hs.halted hp0 hop
  have hx := step_lda_izy_x hn hs.halted hp0 hop
  rw [ha] at htile
  have hpc1 : (m.pc = K.read ∧ m.x = 0) ∨ m.pc = K.top := by
    rcases hpc0 with ⟨e, h⟩ | e
    · exact Or.inl ⟨e, hx ▸ h⟩
    · exact Or.inr e
  obtain ⟨hr0, hl, hh⟩ := hrd hpc1 htile
  rw [RoomBlocks.readVal_eq hr0] at htile
  have hcol := hm _ hl hh htile
  simp only [PoleEntryRule.onCol, Bool.and_eq_true, decide_eq_true_eq] at hcol
  obtain ⟨⟨h4, _⟩, _⟩ := hcol
  have := hP.dC
  have := hP.buf
  omega

end

/-! ## One frame -/

section
variable {C : CfgK} {K : Coin} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveC (C : CfgK) (K : Coin) (l : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkC C K l n A = true

theorem cover_liveC (ht : C.t.all (walkC C K l Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverK C B = true) :
    ∃ D, LiveC C K l F D m ∧ D.k = B.k := by
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

/-- **One step from a live state**: the control byte at `UpdScrollVar`, the map after the step, the read's fact after the step, and the next live state or the
frame's end -/
theorem live_stepC (hP : PlacesOK K C.E C.G) (ht : C.t.all (walkC C K l Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveC C K l F A m) (hh : CleanK C.G C.S.store m) (hx : storesTo l m.prg m.prgMask m.pc = false)
    (hb : BufAt K.Q m) (hrd : ReadC K m) (hm : ColMap K.Q m) (hr : CoinRead K m) :
    (m.pc = K.upd → m.ram.get! K.ctlI ≠ 6) ∧ ColMap K.Q (go step m).2 ∧
    ((∃ A', LiveC C K l F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ CoinRead K (go step m).2) ∨ (go step m).2.frame = m.frame + 1) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkC] at hw
  | succ n =>
    have hx' : storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preC hP.cover hh hs hr
    obtain ⟨r, hr1, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkC, hx', Bool.false_or, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨⟨hctl, hok⟩, hw1⟩ := hw1
    have hw2 := hw1 r hr1
    refine ⟨fun hpc => ctl_of_ok hs1 hctl hP.ctl hpc, PoleTileWalk.colMap_stepQ hs1 hok hb hm, ?_⟩
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      simp only [Bool.and_eq_true] at hw2
      obtain ⟨hpair, hw3⟩ := hw2
      rcases h2 with ⟨k1, k2, _⟩ | ⟨_, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
        have hcr := coinRead_after hP hs1 h1 hpair hm hrd
        rcases hw3 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveC ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, hcr⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, hcr⟩
      · right
        exact k2

/-- **One frame from a walk**: from a live state at the frame's start with the map, while each instruction meets `CleanK`, does not write a byte of `l` by its
address, and meets `BufAt` and `ReadC`, the map holds at the frame's end and the control byte is not 6 at each `UpdScrollVar` of the frame -/
theorem frame_of_walkC (hP : PlacesOK K C.E C.G) (ht : C.t.all (walkC C K l Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top) {S : AS} {m : Machine} {i : UInt8} (hw : walkC C K l Fu S = true) (hs : Sim C.E F S m)
    (hr0 : CoinRead K m)
    (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) (hx : ∀ j, storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hb : ∀ j, BufAt K.Q (trace m i j)) (hrd : ∀ j, ReadC K (trace m i j)) (hm : ColMap K.Q m) :
    ColMap K.Q (PipeTransition.frame m i) ∧ ∀ j, (trace m i j).pc = K.upd → (trace m i j).frame = m.frame → (trace m i j).ram.get! K.ctlI ≠ 6 := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact TaintRun.mem_top _ }
  have key : ∀ j, ColMap K.Q (trace m i j) ∧
      ((∃ A, LiveC C K l F A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ CoinRead K (trace m i j)) ∨ (trace m i j).frame = m.frame + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hm, Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl, hr0⟩⟩
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      obtain ⟨hmj, ih⟩ := ih
      rcases ih with ⟨A, h1, h3, hcr⟩ | h1
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rw [e2]
        obtain ⟨_, a1, a2⟩ := live_stepC hP ht hkl hops hT h1 (hk j) (hx j) (hb j) (hrd j) hmj hcr
        refine ⟨a1, ?_⟩
        rcases a2 with ⟨A', b1, _, b3, b4⟩ | b1
        · exact Or.inl ⟨A', b1, by rw [b3, h3], b4⟩
        · exact Or.inr (by rw [b1, h3])
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        rw [e2]
        exact ⟨hmj, Or.inr h1⟩
  refine ⟨by rw [frame_trace]; exact (key fuelPerFrame).1, ?_⟩
  intro j hpc hfr
  obtain ⟨hmj, h⟩ := key j
  rcases h with ⟨A, h1, _, hcr⟩ | h1
  · exact (live_stepC hP ht hkl hops hT h1 (hk j) (hx j) (hb j) (hrd j) hmj hcr).1 hpc
  · omega

end

/-! ## One frame in control -/

section
variable {S : FrameKeep.Spot} {G : Guard} {E : Env} {K : Coin} {l : List Nat}

/-- what the check says -/
structure CoinOK (S : FrameKeep.Spot) (G : Guard) (E : Env) (K : Coin) (l : List Nat) : Prop where
  places : PlacesOK K E G
  table : (cfgC S G E K l).t.all (walkC (cfgC S G E K l) K l fuelK) = true
  s0 : walkC (cfgC S G E K l) K l fuelK (startK G [] false) = true
  s1 : walkC (cfgC S G E K l) K l fuelK (startK G [] true) = true

theorem coinOK_of_check (h : coinCheckW S G E K l = true) : CoinOK S G E K l := by
  simp only [coinCheckW, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨placesOK_spec h1, h2, h3, h4⟩

/-- **One frame in control**: a frame from `FrameStart`, whose instructions meet `CleanK`, do not write a byte of `l` by their addresses, and meet `BufAt` and
`ReadC`, keeps the map, and the control byte is not 6 at each `UpdScrollVar` of the frame -/
theorem frame_coin (hc : coinCheckW S G E K l = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m)
    (hk : ∀ j, CleanK G S.store (trace m i j)) (hx : ∀ j, storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hb : ∀ j, BufAt K.Q (trace m i j)) (hrd : ∀ j, ReadC K (trace m i j)) (hm : ColMap K.Q m) :
    ColMap K.Q (PipeTransition.frame m i) ∧ ∀ j, (trace m i j).pc = K.upd → (trace m i j).frame = m.frame → (trace m i j).ram.get! K.ctlI ≠ 6 := by
  have hC := coinOK_of_check hc
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (W := []) hE h0 (fun _ h => by cases h)
  have hw0 : walkC (cfgC S G E K l) K l fuelK (startK G [] b) = true := by
    cases b with
    | false => exact hC.s0
    | true => exact hC.s1
  have hr0 : CoinRead K m := by
    intro hpc
    rcases hpc with ⟨h, _⟩ | h
    · rw [h0.pc] at h
      exact absurd h hC.places.idleR
    · rw [h0.pc] at h
      exact absurd h hC.places.idleT
  exact frame_of_walkC (C := cfgC S G E K l) (F := (m.frame, 2)) hC.places hC.table rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs hr0 hk hx hb hrd hm

end

/-! ## The frames before the touch's frame -/

/-- `CleanK` with one more byte protected, from `CleanK` and no store through an index or a pointer to it -/
theorem cleanK_one {G : Guard} {q : UInt16} {m : Machine} {c : Nat} (h : CleanK G q m)
    (hc : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ c) : CleanK { G with prot := c :: G.prot } q m := by
  refine ⟨fun t ht hq => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨hc t ht h1, h2⟩
  · exact Or.inr h1

/-- **No store through an index or a pointer writes the control byte**, from `CtlR`: the stores that `farStore` settles cannot reach it -/
theorem ctl_of_R {K : Coin} {m : Machine} (h : CtlR K m) : ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ K.ctlI := by
  cases hf : PoleKeepFar.farStore [K.ctlI] m with
  | false => exact h hf
  | true =>
    intro t ht hlt e
    exact PoleKeepFar.far_target hf t ht hlt (by rw [e]; exact List.mem_singleton.2 rfl)

/-- the walk's guard: `CleanK` of it from `CleanK` of `FrameKeep.guardK` and `CtlR` -/
theorem cleanK_C {sy : Syms} {m0 : Machine} {m : Machine} (h : CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store m) (hr : CtlR (coinOf sy m0) m) :
    CleanK (guardC sy m0) (FrameKeep.spotOf sy m0).store m :=
  cleanK_one h (ctl_of_R hr)

/-- the start of a frame for the walk's guard: the same as for `FrameKeep.guardK` -/
theorem start_C {sy : Syms} {m0 : Machine} {m : Machine} (h : FrameKeep.StartK sy m0 m) : FrameStart (guardC sy m0) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- **The frames before the touch's frame keep the coin's map, and the control byte is not 6 at their `UpdScrollVar`**: the map at control, and on each
instruction of each frame before the touch's frame `BufAt`, `ReadC` and `CtlR`. `hcK` is the check of the walk of `FrameKeep` (every frame starts in control),
`hcC` the walk of this file. -/
theorem frames_coin {sy : Syms} {m0 : Machine} {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hcK : FrameKeep.keepCheckOf sy m0 = true)
    (hcC : coinCheck sy m0 = true) (Fr : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (hm0 : ColMap (coinOf sy m0).Q (seq 0))
    (hb : ∀ n, n + 1 < Fr.ix g → ∀ k, BufAt (coinOf sy m0).Q (trace (Fr.all n) (Fr.inp n) k))
    (hrd : ∀ n, n + 1 < Fr.ix g → ∀ k, ReadC (coinOf sy m0) (trace (Fr.all n) (Fr.inp n) k))
    (hct : ∀ n, n + 1 < Fr.ix g → ∀ k, CtlR (coinOf sy m0) (trace (Fr.all n) (Fr.inp n) k)) :
    ∀ n, n + 1 < Fr.ix g → ColMap (coinOf sy m0).Q (Fr.all n) ∧
      ∀ k, (trace (Fr.all n) (Fr.inp n) k).pc = sy.UpdScrollVar → (trace (Fr.all n) (Fr.inp n) k).frame = (Fr.all n).frame →
        (trace (Fr.all n) (Fr.inp n) k).ram.get! (coinOf sy m0).ctlI ≠ 6 := by
  have e0 : seq 0 = Fr.all 0 := by rw [Fr.at_ix 0 (Nat.zero_le _), Fr.ix0]
  have one : ∀ n, n + 1 < Fr.ix g → ColMap (coinOf sy m0).Q (Fr.all n) →
      ColMap (coinOf sy m0).Q (PipeTransition.frame (Fr.all n) (Fr.inp n)) ∧
      ∀ k, (trace (Fr.all n) (Fr.inp n) k).pc = (coinOf sy m0).upd → (trace (Fr.all n) (Fr.inp n) k).frame = (Fr.all n).frame →
        (trace (Fr.all n) (Fr.inp n) k).ram.get! (coinOf sy m0).ctlI ≠ 6 := by
    intro n hn hm
    obtain ⟨a1, _⟩ := Fr.all_start hcK hs0 h0 n (by omega)
    exact frame_coin hcC rfl (start_C a1) (fun j => cleanK_C (Fr.clean n (by omega) j) (hct n hn j)) (Fr.noStore n hn) (hb n hn) (hrd n hn) hm
  have maps : ∀ n, n + 1 < Fr.ix g → ColMap (coinOf sy m0).Q (Fr.all n) := by
    intro n
    induction n with
    | zero => exact fun _ => e0 ▸ hm0
    | succ i ih =>
      intro hi
      rw [Fr.next i]
      exact (one i (by omega) (ih (by omega))).1
  intro n hn
  exact ⟨maps n hn, (one n hn (maps n hn)).2⟩

end Smbrta.PoleCoin
