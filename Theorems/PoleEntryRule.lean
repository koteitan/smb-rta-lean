import Theorems.PipeEntryRule
import Theorems.SurfaceRun
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# A touch of the pole, on real frames

`PoleJoin.Run` had the hypothesis `inRange`: at the touch his position is in the pole's range. Its frame `g` had no link to machines. Here the touch is defined on real machines: an instruction of the frame of `m`
with the input `i` makes the routine byte the pole's (`Touches`). The frame need not end with the pole's routine: on a direct grab the flag's routine of the same frame starts the end of the level. The theorem says that such a frame was at or right of the left end of the pole's range when the block buffer routine read the page for the side check
(`touch_right_of_left`), and `inRange_of_pass` gives `inRange` from that.

The whole frame is not followed, as in `PipeEntryRule`. What is assumed stays on the single frame: the instruction that writes the routine byte is the collision routine's own, it comes at the end of one pass from the start
of the side check (`Pass`), and the block buffers hold the pole's tiles only in its column (`TilesOK`). What is proved is the pass (`no_write`): an abstract machine (the one of `SideChangeBound`) follows it, with
every byte unknown except the stack and the offset of the adders. There is no game data in this file. Page: `1-1/f-6-1-PoleEntryRule.md`.
-/

namespace Smbrta.PoleEntryRule

open PipeTransition (frame)
open PipeTransitionAll (go ba_get_set_self ba_get_set_ne ba_size_set)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top bt bt_and bt_not bt_ext bt_zero)
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp findStore footStack envOf neBit rowI forget sim_setK' known_eq row_of zeros_get zeros_size)

/-! ## The touch -/

/-- the value of the pole's routine -/
def vf (sy : Syms) : UInt8 := sy.EngFlagpole.toUInt8

/-- the instruction `n` of the frame makes the routine byte the pole's -/
def WriteStep (sy : Syms) (m : Machine) (i : UInt8) (n : Nat) : Prop :=
  rt sy (trace m i n) ≠ vf sy ∧ rt sy (trace m i (n + 1)) = vf sy

/-- **A touch.** An instruction of the frame of `m` with the input `i` makes the routine byte the pole's. The frame need not end with the pole's routine: on a direct grab the flag's
routine of the same frame finds him low on the pole and starts the end of the level at once. -/
def Touches (sy : Syms) (m : Machine) (i : UInt8) : Prop := ∃ n, WriteStep sy m i n

/-- a frame that ends with the pole's routine, from another routine: a touch at a height where the flag's routine does not end the level on the same frame -/
def EndsTouch (sy : Syms) (m : Machine) (i : UInt8) : Prop := rt sy m ≠ vf sy ∧ rt sy (frame m i) = vf sy

/-- such a frame has an instruction of the write -/
theorem writeStep_of_ends {sy : Syms} {m : Machine} {i : UInt8} (h : EndsTouch sy m i) : ∃ n, n < fuelPerFrame ∧ WriteStep sy m i n := by
  have h0 : rt sy (trace m i 0) ≠ vf sy := h.1
  have h1 : rt sy (trace m i fuelPerFrame) = vf sy := by rw [← frame_trace]; exact h.2
  have key : ∀ N, rt sy (trace m i N) = vf sy → ∃ n, n < N ∧ WriteStep sy m i n := by
    intro N
    induction N with
    | zero => exact fun hz => absurd hz h0
    | succ N ih =>
      intro hs
      by_cases hN : rt sy (trace m i N) = vf sy
      · obtain ⟨n, h2, h3⟩ := ih hN
        exact ⟨n, by omega, h3⟩
      · exact ⟨N, by omega, hN, hs⟩
  exact key _ h1

/-- so it is a touch -/
theorem touches_of_ends {sy : Syms} {m : Machine} {i : UInt8} (h : EndsTouch sy m i) : Touches sy m i := by
  obtain ⟨n, _, hn⟩ := writeStep_of_ends h
  exact ⟨n, hn⟩

/-- before the write the frame runs: each instruction is a step -/
theorem step_before {sy : Syms} {m : Machine} {i : UInt8} {n : Nat} (h : WriteStep sy m i n) :
    ∀ j, j ≤ n → trace m i (j + 1) = (go step (trace m i j)).2 := by
  intro j hj
  by_cases hg : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
    have e1 := trace_stop hg k
    have e2 := trace_stop hg (k + 1)
    apply h.1
    rw [e1, ← e2]
    exact h.2
  · show nxt (m.frame + 1) (trace m i j) = _
    simp only [nxt, if_neg hg]

/-! ## The places in the code -/

/-- what the check needs: places in the code and bytes, from the symbols and the ROM -/
structure Spots where
  /-- the start of the side check -/
  side : UInt16
  /-- in the block buffer routine: the addition of the horizontal position -/
  adc : UInt16
  /-- the read of the page, which is the instruction after the sum is stored -/
  entry : UInt16
  /-- the search only: the addition to the page, the point where the sum is joined with the page's bit -/
  afterPage : UInt16
  ora : UInt16
  /-- the routine's read of the block buffer -/
  read : UInt16
  /-- the instruction that writes the pole's routine -/
  write : UInt16
  /-- where a pass ends without that instruction -/
  exits : List UInt16
  /-- the byte with the offset of the adders, and its values out of the water: a big Mario, and a small or crouching one -/
  adI : Nat
  ads : List UInt8
  /-- the offsets of the four reads of the side check -/
  idx : List UInt8
  /-- the bytes of the routine: its offset, the pointer of the read, the sum, the count of the side check, the tile -/
  saveI : Nat
  ptrI : Nat
  sumI : Nat
  cntI : Nat
  tempI : Nat
  /-- the position -/
  xI : Nat
  pI : Nat
  /-- the stack pointer in the side check -/
  stack : UInt8
  /-- the pole's two tiles, and the bits at which a byte that is neither differs from the first -/
  ball : UInt8
  shaft : UInt8
  bits : List UInt8
  /-- the pole's column: its number, the top of it in the block buffers -/
  col : UInt8
  dC : Nat
  /-- the start of the block buffers, the rows of a block buffer -/
  bufLo : Nat
  rows : Nat
  /-- the pole's page, and the left end of its range in pixels -/
  pg : Nat
  left : Nat
  /-- no pass starts later in the frame than this dot -/
  late : Nat
  deriving Inhabited

/-- the bytes of the two block buffers -/
def Spots.bufBytes (P : Spots) : Nat := 2 * (16 * P.rows)

/-- the RAM index `i` is in the pole's column -/
def onCol (P : Spots) (i : Nat) : Bool :=
  decide (P.dC ≤ i) && decide (i < P.dC + 16 * P.rows) && ((i - P.dC) % 16 == 0)

/-- the places, from the symbols; `s` is the stack pointer -/
def spotsOf (sy : Syms) (m0 : Machine) (s : UInt8) : Spots :=
  let pg := SurfaceRun.polePage sy m0
  let buf := if pg % 2 == 0 then sy.Block_Buffer_1 else sy.Block_Buffer_2
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let sum := findOp m0 sy.BlockBufferCollision 0x85 64
  let ads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 2)]
  let ball := sy.FlagBallTile.toUInt8
  let shaft := sy.FlagShaftTile.toUInt8
  let col := PoleGrab.column sy
  { side := sy.DoPlayerSideCheck
    adc := sum - 2
    entry := sum + 2
    afterPage := sum + 4
    ora := findOp m0 (sum + 2) 0x05 16
    read
    write := findStore m0 sy.RunFR sy.GameEngineSubroutine.toUInt8 64
    exits := [sy.ExSCH, sy.ExCSM, sy.ExHC, sy.ContSChk, sy.VineCollision]
    adI := (romByte m0 (sy.DoPlayerSideCheck + 1)).toNat
    ads
    idx := ads.flatMap fun e => [e + 3, e + 4, e + 5, e + 6]
    saveI := (romByte m0 (sy.BlockBufferCollision + 2)).toNat
    ptrI := (romByte m0 (read + 1)).toNat
    sumI := (romByte m0 (sum + 1)).toNat
    cntI := (romByte m0 (findOp m0 sy.DoPlayerSideCheck 0x85 16 + 1)).toNat
    tempI := (romByte m0 (read + 3)).toNat
    xI := (sy.Player_X_Position &&& 0x7FF).toNat
    pI := (sy.Player_PageLoc &&& 0x7FF).toNat
    stack := s
    ball
    shaft
    bits := bitList.filter (· != ball ^^^ shaft)
    col := col.toUInt8
    dC := ((buf + col.toUInt16) &&& 0x7FF).toNat
    bufLo := (sy.Block_Buffer_1 &&& 0x7FF).toNat
    rows := (sy.Block_Buffer_2 - sy.Block_Buffer_1).toNat / 16
    pg
    left := 256 * pg + (PoleGrab.colX sy - 10)
    late := dotsPerFrame - 6000 }

/-- the places of the game -/
def spots (sy : Syms) (m0 : Machine) : Spots := spotsOf sy m0 (footStack sy m0)

/-! ## The conditions on one pass -/

/-- the machine starts the side check, between the frame's first event and its end -/
structure Start (P : Spots) (E : Env) (m : Machine) : Prop where
  pc : m.pc = P.side
  s : m.s = P.stack
  ad : m.ram.get! P.adI ∈ P.ads
  dot : dotVblClr ≤ m.fdot ∧ m.fdot ≤ P.late
  vb : m.vblank = false
  nmi : m.nmiPending = false
  s0 : m.sprite0 = s0f m.fdot
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048

/-- the block buffer routine reads the page for the player, with an offset of the side check -/
def AtEntry (P : Spots) (m : Machine) : Prop := m.pc = P.entry ∧ m.y ∈ P.idx ∧ m.x = 0

/-- the position in pixels -/
def px (P : Spots) (m : Machine) : Nat := 256 * (m.ram.get! P.pI).toNat + (m.ram.get! P.xI).toNat

/-- the machine is at the routine's read of the block buffer -/
def AtRead (P : Spots) (m : Machine) : Prop := m.pc = P.read

/-- the read's offset is a row of the block buffer -/
def RowOK (P : Spots) (m : Machine) : Prop := m.y.toNat % 16 = 0 ∧ m.y.toNat < 16 * P.rows

/-- the pole's tiles are in the block buffers only in its column, and only from the page before the pole's on -/
def TilesOK (P : Spots) (m : Machine) : Prop :=
  ∀ i, P.bufLo ≤ i → i < P.bufLo + P.bufBytes → (m.ram.get! i = P.ball ∨ m.ram.get! i = P.shaft) →
    onCol P i = true ∧ P.pg ≤ (m.ram.get! P.pI).toNat + 1

/-- **What stays assumed about a read.** -/
def ReadOK (P : Spots) (m : Machine) : Prop := RowOK P m ∧ TilesOK P m

/-- **What stays assumed about the write.** The instruction `n` is the routine's write. Before it in this frame the machine started the side check, and from there on it did not leave the check, and
each read is `ReadOK`. -/
def Pass (P : Spots) (E : Env) (tr : Nat → Machine) (n : Nat) : Prop :=
  (tr n).pc = P.write ∧ ∃ n₀, n₀ ≤ n ∧ Start P E (tr n₀) ∧ (∀ j, n₀ ≤ j → j ≤ n → (tr j).pc ∉ P.exits) ∧
    (∀ j, n₀ ≤ j → j < n → AtRead P (tr j) → ReadOK P (tr j))

/-! ## The walk -/

/-- the pointer, as far as its bytes say -/
def ptrAt (P : Spots) (A : AS) : UInt16 := (A.getK P.ptrI).v.toUInt16 ||| ((A.getK (P.ptrI + 1)).v.toUInt16 <<< 8)

/-- every row from this pointer is in the block buffers, and not in the pole's column unless the tiles cannot be there yet -/
def safe (P : Spots) (p : UInt16) (pa : AB) : Bool :=
  (List.range P.rows).all fun r =>
    decide (P.bufLo ≤ rowI p r) && decide (rowI p r < P.bufLo + P.bufBytes) && (!onCol P (rowI p r) || decide (pa.maxv.toNat + 1 < P.pg))

/-- every byte that is neither tile differs from the first at one of the bits -/
def tilesCover (P : Spots) : Bool :=
  (List.range 256).all fun n =>
    n.toUInt8 == P.ball || n.toUInt8 == P.shaft || P.bits.any fun b => n.toUInt8 &&& b == (~~~P.ball) &&& b

/-- the pieces before a step. At the addition: the horizontal position. At the read of the page: the page, left of the range. At the read of the block buffer: the row, and a bit where the byte read
differs from the pole's tiles. -/
def preP (P : Spots) (A : AS) : List AS :=
  if A.pc == P.adc then
    if (A.getK P.xI).isK then [A] else (List.range 256).map fun n => A.setK P.xI (AB.known n.toUInt8)
  else if A.pc == P.entry && A.y.isK && P.idx.contains A.y.v && A.x.isK && A.x.v == 0 then
    ((List.range (P.pg + 1)).filter fun n => !(A.getK P.xI).isK || decide (256 * n + (A.getK P.xI).v.toNat < P.left)).map fun n =>
      A.setK P.pI (AB.known n.toUInt8)
  else if A.pc == P.read then
    if (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && safe P (ptrAt P A) (A.getK P.pI) then
      (List.range P.rows).flatMap fun r =>
        P.bits.map fun b => ({ A with y := AB.known (16 * r).toUInt8 } : AS).setK (rowI (ptrAt P A) r) (neBit P.ball b)
    else [A]
  else [A]

/-- the bytes that keep states apart in the table -/
def keepP (P : Spots) : List Nat := [P.adI, P.saveI, P.cntI, P.ptrI, P.ptrI + 1, P.xI, P.pI, P.sumI, P.tempI]

/-- states with the same key are joined -/
def keyP (P : Spots) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := A.s.toNat * 65536 + A.pc.toNat
  let n := n * 65536 + num A.x
  let n := n * 65536 + num A.y
  let n := n * 65536 + num A.a
  let n := n * 65536 + num (A.p.and (AB.known 1))
  let n := (keepP P).foldl (fun n i => n * 65536 + num (A.getK i)) n
  n * 4294967296 + stackHash A

/-- the live part of the RAM is the stack and these bytes -/
def onlyKeep (l : List Nat) (A : AS) : AS :=
  let kn0 := (List.range (255 - A.s.toNat)).foldl (fun k j => k.set! (0x100 + A.s.toNat + 1 + j) (A.getK (0x100 + A.s.toNat + 1 + j)).k) (ByteArray.mk (Array.replicate 2048 0))
  { A with kn := l.foldl (fun k i => k.set! i (A.getK i).k) kn0 }

/-- the sum's column is the pole's -/
def sumOnCol (P : Spots) (A : AS) : Bool :=
  let s := A.getK P.sumI
  s.k &&& 0xF0 == 0xF0 && s.v >>> 4 == P.col

/-- what the table forgets at some places: the search only -/
def normP (P : Spots) (A : AS) : AS :=
  if A.pc == P.adc then
    { forget [P.tempI] A with lo := dotVblClr, hi := P.late + ((A.hi - P.late) / 1024 + 1) * 1024 }
  else if A.pc == P.entry then
    let s := A.getK P.sumI
    if s.isK then
      let B : AS := { A.setK P.sumI ⟨s.v, s.k &&& 0xF0⟩ with a := AB.top }
      if sumOnCol P A then B else forget [P.xI] B
    else A
  else if A.pc == P.afterPage then
    if (A.getK P.pI).isK && (A.getK P.pI).v.toNat != P.pg then forget [P.xI] A else A
  else if A.pc == P.ora then
    if sumOnCol P A then A else forget [P.pI] A
  else if A.pc == P.read then
    let onc := (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && (List.range P.rows).any (fun r => onCol P (rowI (ptrAt P A) r))
    { onlyKeep ([P.adI, P.saveI, P.cntI, P.ptrI, P.ptrI + 1] ++ (if onc then [P.xI, P.pI] else [])) A with a := AB.top }
  else if A.pc == P.read + 2 then
    { onlyKeep ([P.adI, P.saveI, P.cntI] ++ (if A.a.k == 0 then [P.xI] else [])) A with y := AB.top }
  else A

/-- the places where the search keeps a state in the table -/
def cutsP (P : Spots) : List UInt16 := [P.adc, P.entry, P.afterPage, P.ora, P.read, P.read + 2]

/-- the table -/
structure CfgP where
  E : Env
  ops : Array (AM Unit)
  P : Spots
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

def coverP (C : CfgP) (B : AS) : Bool :=
  (C.idx.getD (keyP C.P (normP C.P B)) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D
    | none => false

/-- from `A`, step by step until every path ends at an exit or in a state of the table. No path comes to the write. -/
def walkP (C : CfgP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preP C.P A).all fun A₁ => (succs C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      C.P.exits.contains B.pc ||
        (B.pc != C.P.write && ((C.cut.get! B.pc.toNat != 0 && coverP C B) || walkP C n B))

/-! ## Finding the table: a search, no part of the proof -/

structure SR where
  pending : Std.TreeMap Nat AS compare := {}
  inN : Std.HashMap Nat Nat := {}
  out : Array AS := #[]
  leaders : Std.HashMap Nat Unit := {}
  seen : Std.HashMap Nat (List AS) := {}
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  firstFail : Option AS := none

def routeP (P : Spots) (X : SR) (B0 : AS) : SR :=
  let B := normP P B0
  let K := keyP P B
  if (X.seen.getD K []).any fun D => B0.le D then X else
  match X.pending[K]? with
  | some Q => { X with pending := X.pending.insert K (Q.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

partial def runP (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) (A0 : AS) : SR := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preP P cur).flatMap (succs E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := (rs.filterMap id).filter fun b => !P.exits.contains b.pc
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !(cutsP P).contains b.pc && b.pc != P.write &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.pc == P.write then X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := routeP P X b
    break
  return X

partial def searchP (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) : SR := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      if n ≥ 2 || (cutsP P).contains A.pc then X := { X with out := X.out.push A, seen := X.seen.insert key (A :: X.seen.getD key []) }
      X := runP E ops P X A
  return X

/-- the abstract state at the start of the side check: only the stack pointer and the offset of the adders are known -/
def startAt (P : Spots) (e : UInt8) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := P.stack, p := AB.top, pc := P.side,
    ram := (ByteArray.mk (Array.replicate 2048 0)).set! P.adI e,
    kn := (ByteArray.mk (Array.replicate 2048 0)).set! P.adI 0xFF,
    ppuCtrl := AB.top, ppuMask := AB.top, vb := false, nmi := false, lo := dotVblClr, hi := P.late, padShift := AB.top, strobe := false, dg := false, k := 0 }

def searchOf (E : Env) (P : Spots) : SR :=
  let ops := (aRows E).toArray
  searchP E ops P ((P.ads.map (startAt P)).foldl (routeP P) {})

def cfgOf (E : Env) (P : Spots) : CfgP :=
  let X := searchOf E P
  let q := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyP P A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops := (aRows E).toArray, P, t := X.out, idx := q.1, cut := q.2.1 }

/-- the fuel of a walk -/
def fuelP : Nat := 4000

/-- **The check.** The places are bytes of the RAM, the start is not the write, the left end is on the pole's page, the tiles' bits cover the bytes, and the walks succeed. -/
def walkCheck (E : Env) (P : Spots) : Bool :=
  let C := cfgOf E P
  decide (P.adI < 2048) && decide (P.xI < 2048) && decide (P.pI < 2048) &&
  P.side != P.write && decide (P.late < dotsPerFrame) && decide (P.left < 256 * (P.pg + 1)) && tilesCover P &&
  C.t.all (walkP C fuelP) && (P.ads.map (startAt P)).all (walkP C fuelP)

/-- the check on the ROM -/
def ruleCheck (sy : Syms) (m0 : Machine) : Bool := walkCheck (envOf m0) (spots sy m0)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8} {P : Spots}

/-- what `preP` needs of the machine -/
def HypAt (P : Spots) (m : Machine) : Prop :=
  (AtEntry P m → px P m < P.left) ∧ (AtRead P m → ReadOK P m)

/-- a byte that is neither tile differs from the first at one of the bits -/
theorem tile_bit (hc : tilesCover P = true) {v : UInt8} (h1 : v ≠ P.ball) (h2 : v ≠ P.shaft) : ∃ b ∈ P.bits, (neBit P.ball b).mem v := by
  simp only [tilesCover, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hc
  have hv : v.toNat.toUInt8 = v := by simp
  rcases hc v.toNat (List.mem_range.2 v.toNat_lt) with (h | h) | ⟨b, hb, h⟩
  · rw [hv] at h
    exact absurd h h1
  · rw [hv] at h
    exact absurd h h2
  · rw [hv] at h
    exact ⟨b, hb, h⟩

/-- what the pieces need from the check -/
structure PreOK (P : Spots) : Prop where
  xI : P.xI < 2048
  pI : P.pI < 2048
  left : P.left < 256 * (P.pg + 1)
  tiles : tilesCover P = true

/-- every machine that meets `HypAt` is in a piece -/
theorem cov_pre (hb : PreOK P) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : HypAt P m) : ∃ B ∈ preP P A, Sim E F B m := by
  unfold preP
  by_cases h0 : (A.pc == P.adc) = true
  · rw [if_pos h0]
    by_cases hk : (A.getK P.xI).isK = true
    · rw [if_pos hk]
      exact ⟨A, List.mem_singleton.2 rfl, hs⟩
    · rw [if_neg hk]
      refine ⟨_, List.mem_map.2 ⟨(m.ram.get! P.xI).toNat, List.mem_range.2 (m.ram.get! P.xI).toNat_lt, rfl⟩, ?_⟩
      refine sim_setK' hs ?_
      have hv : (m.ram.get! P.xI).toNat.toUInt8 = m.ram.get! P.xI := by simp
      rw [hv]
      exact mem_known_self _
  · rw [if_neg h0]
    by_cases h1 : (A.pc == P.entry && A.y.isK && P.idx.contains A.y.v && A.x.isK && A.x.v == 0) = true
    · rw [if_pos h1]
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩ := h1
      have hy : m.y = A.y.v := known_eq h3 hs.y
      have hx : m.x = A.x.v := known_eq h5 hs.x
      have ha : AtEntry P m := ⟨by rw [hs.pc, h2], by
        rw [hy]
        exact List.mem_of_elem_eq_true h4, by rw [hx, h6]⟩
      have hlt := hh.1 ha
      have hL := hb.left
      unfold px at hlt
      have hp : (m.ram.get! P.pI).toNat < P.pg + 1 := by omega
      have hv : (m.ram.get! P.pI).toNat.toUInt8 = m.ram.get! P.pI := by simp
      refine ⟨_, List.mem_map.2 ⟨(m.ram.get! P.pI).toNat, List.mem_filter.2 ⟨List.mem_range.2 hp, ?_⟩, rfl⟩, ?_⟩
      · by_cases hk : (A.getK P.xI).isK = true
        · have he : m.ram.get! P.xI = (A.getK P.xI).v := known_eq hk (hs.ram _ hb.xI)
          rw [he] at hlt
          simp only [hk, Bool.not_true, Bool.false_or, decide_eq_true_eq]
          exact hlt
        · simp [hk]
      · refine sim_setK' hs ?_
        rw [hv]
        exact mem_known_self _
    · rw [if_neg h1]
      by_cases h2 : (A.pc == P.read) = true
      · rw [if_pos h2]
        by_cases h4 : ((A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && safe P (ptrAt P A) (A.getK P.pI)) = true
        · rw [if_pos h4]
          simp only [Bool.and_eq_true] at h4
          obtain ⟨_, h9⟩ := h4
          have hpc : m.pc = P.read := by rw [hs.pc]; exact beq_iff_eq.1 h2
          obtain ⟨hrow, htiles⟩ := hh.2 hpc
          obtain ⟨r, hr, hyr⟩ := row_of hrow
          have hpage : (m.ram.get! P.pI).toNat ≤ (A.getK P.pI).maxv.toNat := TaintRun.le_maxv (hs.ram _ hb.pI)
          simp only [safe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h9
          obtain ⟨⟨h12, h13⟩, h14⟩ := h9 r (List.mem_range.2 hr)
          have key : ∀ v, (v = P.ball ∨ v = P.shaft) → m.ram.get! (rowI (ptrAt P A) r) = v → False := by
            intro v hv he
            have ht := htiles _ h12 h13 (by rw [he]; exact hv)
            rcases h14 with h14 | h14
            · rw [ht.1] at h14
              cases h14
            · have := ht.2
              omega
          obtain ⟨b, hb1, hb2⟩ := tile_bit hb.tiles (fun he => key _ (Or.inl rfl) he) (fun he => key _ (Or.inr rfl) he)
          refine ⟨_, List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨b, hb1, rfl⟩⟩, ?_⟩
          have hs2 : Sim E F ({ A with y := AB.known (16 * r).toUInt8 } : AS) m := { hs with y := by rw [hyr]; exact mem_known_self _ }
          exact sim_setK' hs2 hb2
        · rw [if_neg h4]
          exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      · rw [if_neg h2]
        exact ⟨A, List.mem_singleton.2 rfl, hs⟩

end

/-! ## The walk covers the machine -/

section
variable {C : CfgP} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveP (C : CfgP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkP C n A = true

theorem cover_liveP (ht : C.t.all (walkP C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverP C B = true) : ∃ D, LiveP C F D m := by
  unfold coverP at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le h2 hs, Fu, hall⟩
  · cases h2

theorem live_stepP (ht : C.t.all (walkP C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : PreOK C.P) {A : AS} {m : Machine} (hl : LiveP C F A m) (hh : HypAt C.P m) (hex : (go step m).2.pc ∉ C.P.exits) :
    (go step m).2.pc ≠ C.P.write ∧ ∃ A', LiveP C F A' (go step m).2 := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkP] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_pre hb hs hh
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs1
    simp only [walkP, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      have hpc : (go step m).2.pc = B.pc := h1.pc
      simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at hw2
      rcases hw2 with h2 | ⟨h2, h3⟩
      · exact absurd (by rw [hpc]; exact List.mem_of_elem_eq_true h2) hex
      · refine ⟨by rw [hpc]; exact h2, ?_⟩
        rcases h3 with ⟨_, h4⟩ | h4
        · exact cover_liveP ht h1 h4
        · exact ⟨B, h1, n, h4⟩

end

/-! ## A pass that is left of the range does not come to the write -/

section
variable {E : Env} {P : Spots}

/-- the state at the start of the side check covers the machine -/
theorem sim_start (hl : P.late < dotsPerFrame) (hE : E.pad = AB.top) {m : Machine} (h : Start P E m) : ∃ e ∈ P.ads, Sim E (m.frame, 2) (startAt P e) m := by
  refine ⟨_, h.ad, ?_⟩
  refine ⟨mem_top _, mem_top _, mem_top _, mem_top _, h.s, h.pc, h.prg, h.mask, mem_top _, mem_top _, h.vb, h.nmi, h.s0, h.dot.1, h.dot.2, hl, by rw [hE]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    show AB.mem ⟨((ByteArray.mk (Array.replicate 2048 0)).set! P.adI (m.ram.get! P.adI)).get! i, ((ByteArray.mk (Array.replicate 2048 0)).set! P.adI 0xFF).get! i⟩ (m.ram.get! i)
    by_cases he : P.adI = i
    · subst he
      rw [ba_get_set_self _ _ _ (by rw [zeros_size]; exact hi), ba_get_set_self _ _ _ (by rw [zeros_size]; exact hi)]
      exact mem_known_self _
    · rw [ba_get_set_ne _ _ _ _ he, ba_get_set_ne _ _ _ _ he, zeros_get]
      show m.ram.get! i &&& 0 = _ &&& 0
      apply bt_ext
      intro j hj
      rw [bt_and, bt_and, bt_zero hj, Bool.and_false, Bool.and_false]
  · intro hd
    cases hd
  · show ((ByteArray.mk (Array.replicate 2048 0)).set! P.adI _).size = 2048
    rw [ba_size_set, zeros_size]
  · show ((ByteArray.mk (Array.replicate 2048 0)).set! P.adI _).size = 2048
    rw [ba_size_set, zeros_size]
  · show m.frame = m.frame + 0
    rfl
  · intro hd
    cases hd

/-- what the check says -/
structure WalkOK (E : Env) (P : Spots) : Prop where
  pre : PreOK P
  ne : P.side ≠ P.write
  late : P.late < dotsPerFrame
  table : (cfgOf E P).t.all (walkP (cfgOf E P) fuelP) = true
  starts : ∀ e ∈ P.ads, walkP (cfgOf E P) fuelP (startAt P e) = true

theorem walkOK_of_check (h : walkCheck E P = true) : WalkOK E P := by
  simp only [walkCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨h2, h3, h6, h7⟩, h4, h5, h8, h9⟩

/-- **A pass.** If the position at each read of the page is left of the range and each read of the block buffer is `ReadOK`, the machine does not come to the write. -/
theorem no_write (hc : walkCheck E P = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat} (hs : ∀ j, j < n → s (j + 1) = (go step (s j)).2)
    (h0 : Start P E (s 0)) (hh : ∀ j, j < n → HypAt P (s j)) (hex : ∀ j, j ≤ n → (s j).pc ∉ P.exits) : (s n).pc ≠ P.write := by
  have hC := walkOK_of_check hc
  obtain ⟨e, he, hsim⟩ := sim_start hC.late hE h0
  have live : ∀ j, j ≤ n → (j = 0 ∨ (s j).pc ≠ P.write) ∧ ∃ A, LiveP (cfgOf E P) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨Or.inl rfl, _, hsim, fuelP, hC.starts e he⟩
    | succ j ih =>
      intro hj
      obtain ⟨_, A, hA⟩ := ih (by omega)
      have e1 := hs j (by omega)
      have hx := hex (j + 1) hj
      rw [e1] at hx ⊢
      obtain ⟨h1, h2⟩ := live_stepP (C := cfgOf E P) hC.table rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.pre hA (hh j (by omega)) hx
      exact ⟨Or.inr h1, h2⟩
  rcases (live n (Nat.le_refl n)).1 with h1 | h1
  · subst h1
    rw [h0.pc]
    exact hC.ne
  · exact h1

end

/-! ## The frame -/

/-- **The touch on a real frame.** If the frame touches and the instruction that writes the routine byte ends a `Pass`, then in that pass, when the block buffer routine reads the page for the side check,
the position is at or right of the left end of the pole's range. -/
theorem touch_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : ruleCheck sy m0 = true) (he : Touches sy m i)
    (hp : ∀ n, WriteStep sy m i n → Pass (spots sy m0) (envOf m0) (trace m i) n) :
    ∃ n j, WriteStep sy m i n ∧ j < n ∧ AtEntry (spots sy m0) (trace m i j) ∧ (spots sy m0).left ≤ px (spots sy m0) (trace m i j) := by
  obtain ⟨n, hw⟩ := he
  obtain ⟨hW, n₀, h1, h2, h3, h4⟩ := hp n hw
  by_cases hx : ∃ j, j < n ∧ AtEntry (spots sy m0) (trace m i j) ∧ (spots sy m0).left ≤ px (spots sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = n₀ + k := ⟨n - n₀, by omega⟩
    have hn := no_write (s := fun j => trace m i (n₀ + j)) (n := k) hc rfl
      (fun j hj => step_before hw (n₀ + j) (by omega)) (by simpa using h2)
      (fun j hj => ⟨fun ha => by
        show px (spots sy m0) (trace m i (n₀ + j)) < (spots sy m0).left
        by_cases hl : (spots sy m0).left ≤ px (spots sy m0) (trace m i (n₀ + j))
        · exact absurd ⟨n₀ + j, by omega, ha, hl⟩ hx
        · omega, fun ha => h4 (n₀ + j) (by omega) (by omega) ha⟩)
      (fun j hj => h3 (n₀ + j) (by omega) (by omega))
    exact hn hW

/-- **`inRange` from one frame.** `P₂` is the position when the block buffer routine reads the page for the side check, before the write, with the fraction `f ≥ 0`. A frame that touches, whose instruction of the write ends a `Pass`,
has `P₂` at or right of the left end of the pole's range. -/
theorem inRange_of_pass {sy : Syms} {m0 m : Machine} {i : UInt8} {P₂ : Int} (hc : ruleCheck sy m0 = true) (he : Touches sy m i)
    (hp : ∀ n, WriteStep sy m i n → Pass (spots sy m0) (envOf m0) (trace m i) n)
    (hpos : ∀ n j, WriteStep sy m i n → j < n → AtEntry (spots sy m0) (trace m i j) →
      ∃ f : Int, 0 ≤ f ∧ P₂ = 256 * (px (spots sy m0) (trace m i j) : Int) + f) :
    SurfaceRun.poleP sy m0 ≤ P₂ := by
  obtain ⟨n, j, h0, h1, h2, h3⟩ := touch_right_of_left hc he hp
  obtain ⟨f, hf, h4⟩ := hpos n j h0 h1 h2
  rw [h4]
  have h5 : (spots sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  rw [h5] at h3
  unfold SurfaceRun.poleP
  omega

/-! ## On real frames: a program, no part of the proof -/

def startOK (P : Spots) (E : Env) (m : Machine) : Bool :=
  m.pc == P.side && m.s == P.stack && P.ads.contains (m.ram.get! P.adI) && decide (dotVblClr ≤ m.fdot) && decide (m.fdot ≤ P.late) &&
  !m.vblank && !m.nmiPending && m.sprite0 == s0f m.fdot && !m.padStrobe && !m.halted && !m.trk && m.prgMask == E.mask && m.ram.size == 2048

def rowOK (P : Spots) (m : Machine) : Bool := m.y.toNat % 16 == 0 && decide (m.y.toNat < 16 * P.rows)

def tilesOK (P : Spots) (m : Machine) : Bool :=
  let pa := (m.ram.get! P.pI).toNat
  (List.range P.bufBytes).all fun j =>
    let i := P.bufLo + j
    let v := m.ram.get! i
    (v != P.ball && v != P.shaft) || (onCol P i && decide (P.pg ≤ pa + 1))

/-- what real frames say about the hypotheses -/
structure Report where
  frames : Nat := 0
  /-- arrivals at the side check with the player's routine, and how many do not meet `Start` -/
  passes : Nat := 0
  startBad : Nat := 0
  /-- reads of a side check in such a pass, and how many do not meet `RowOK`, `TilesOK` -/
  reads : Nat := 0
  rowBad : Nat := 0
  tilesBad : Nat := 0
  /-- frames that touch; of them: not by the write; not at the end of a pass; left of the range; at no read of the page in the pass; the position at the read of the page is not the position when the collision routine starts -/
  touches : Nat := 0
  writeBad : Nat := 0
  passBad : Nat := 0
  leftBad : Nat := 0
  noEntry : Nat := 0
  posBad : Nat := 0
  /-- positions in pixels and heights of the touches -/
  pxs : List Nat := []
  ys : List Nat := []
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, passes {r.passes} (not Start: {r.startBad}), reads {r.reads} (not RowOK: {r.rowBad}, not TilesOK: {r.tilesBad}), touches {r.touches} (not the write: {r.writeBad}, not a pass: {r.passBad}, left of the range: {r.leftBad}, no read of the page: {r.noEntry}, pos: {r.posBad}), positions {r.pxs.eraseDups.mergeSort}, heights {r.ys.eraseDups.mergeSort}"

/-- one real frame with the bits `pad` of the controller -/
def scanFrame (sy : Syms) (P : Spots) (E : Env) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let mut r := { r0 with frames := r0.frames + 1 }
  let mut inPass := false
  let mut passOK := true
  let mut lastPx : Option Nat := none
  let mut posC : Option Int := none
  let mut n := 0
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if c.pc == sy.PlayerBGCollision then posC := some (posP sy c)
    if c.pc == P.side then
      let ok := startOK P E c
      let ctl := rt sy c == sy.Eng_PlayerCtrl.toUInt8
      r := { r with passes := r.passes + (if ctl then 1 else 0), startBad := r.startBad + (if ok || !ctl then 0 else 1) }
      inPass := ok
      passOK := ok
      lastPx := none
    if P.exits.contains c.pc then inPass := false
    if c.pc == P.entry && P.idx.contains c.y && c.x == 0 then
      let q := 256 * (c.ram.get! P.pI).toNat + (c.ram.get! P.xI).toNat
      if inPass then lastPx := some q
      match posC with
      | some p2 => unless decide (256 * (q : Int) ≤ p2) && decide (p2 < 256 * (q : Int) + 256) do r := { r with posBad := r.posBad + 1 }
      | none => r := { r with posBad := r.posBad + 1 }
    if inPass && c.pc == P.read then
      let a := rowOK P c
      let b := tilesOK P c
      r := { r with reads := r.reads + 1, rowBad := r.rowBad + (if a then 0 else 1), tilesBad := r.tilesBad + (if b then 0 else 1) }
      if !(a && b) then passOK := false
    let before := rt sy c
    let pc := c.pc
    c := (go step c).2
    if before != vf sy && rt sy c == vf sy then
      r := { r with touches := r.touches + 1, writeBad := r.writeBad + (if pc == P.write then 0 else 1),
                    passBad := r.passBad + (if inPass && passOK then 0 else 1),
                    ys := (peek c sy.Player_Y_Position).toNat :: r.ys }
      match lastPx with
      | some q =>
        r := { r with leftBad := r.leftBad + (if q < P.left then 1 else 0), pxs := q :: r.pxs }
      | none => r := { r with noEntry := r.noEntry + 1 }
    n := n + 1
  return (r, c)

end Smbrta.PoleEntryRule
