import Theorems.SideChangeBound
import Theorems.PipeEntry
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# An entry into the vertical pipe, on real frames

`PipeEntry.no_entry_by` takes an arbitrary predicate `Enter` and a hypothesis `rule`. Here the entry is defined on real machines: the frame of `m` with the input `i` ends with the pipe's routine and `m` has another
routine (`Enters`). The theorem says that such a frame was at or right of the left end of the pipe's window when the foot check read the right foot (`entry_right_of_left`).

The whole frame is not followed here. What is assumed stays on the single frame: the instruction that writes the routine byte is the collision routine's own, it comes at the end of one pass from the start
of the foot check (`Pass`), and the block buffer holds the pipe's right tile only at its place (`ReadOK`). What is proved is the pass (`no_write`): an abstract machine (the one of `SideChangeBound`) follows it, with
every byte unknown except the stack and the offset of the adders. `PipeWrites` follows the whole frame, and `Route` uses that. There is no game data in this file. Page: `1-1/a-5-1-PipeEntryRule.md`.
-/

namespace Smbrta.PipeEntryRule

open PipeTransition (frame)
open PipeTransitionAll (go ruf_eq frame_eq ba_get_set_self ba_get_set_ne ba_size_set)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top bt bt_and bt_not bt_ext bt_zero)

/-! ## The instructions of a frame -/

/-- one instruction of a frame that ends at frame `t`, as `runUntilFrame` does it -/
def nxt (t : Nat) (m : Machine) : Machine := if m.frame ≥ t || m.halted then m else (go step m).2

/-- the machine after `n` instructions of the frame of `m` with the input `i` -/
def trace (m : Machine) (i : UInt8) : Nat → Machine
  | 0 => { m with pad := smbToPad i }
  | n + 1 => nxt (m.frame + 1) (trace m i n)

theorem trace_stop {m : Machine} {i : UInt8} {j : Nat} (h : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) :
    ∀ k, trace m i (j + k) = trace m i j
  | 0 => rfl
  | k + 1 => by
    have e := trace_stop h k
    show nxt (m.frame + 1) (trace m i (j + k)) = _
    rw [e]
    simp only [nxt, if_pos h]

theorem run_trace (m : Machine) (i : UInt8) : ∀ (n j : Nat), (go (runUntilFrame (m.frame + 1) n) (trace m i j)).2 = trace m i (j + n)
  | 0, _ => rfl
  | n + 1, j => by
    rw [ruf_eq]
    by_cases h : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true
    · rw [if_pos h]
      exact (trace_stop h (n + 1)).symm
    · rw [if_neg h, show j + (n + 1) = (j + 1) + n by omega, ← run_trace m i n (j + 1)]
      show _ = (go (runUntilFrame (m.frame + 1) n) (nxt (m.frame + 1) (trace m i j))).2
      simp only [nxt, if_neg h]

/-- a frame is its last instruction -/
theorem frame_trace (m : Machine) (i : UInt8) : frame m i = trace m i fuelPerFrame := by
  rw [frame_eq]
  have := run_trace m i fuelPerFrame 0
  rw [Nat.zero_add] at this
  exact this

/-! ## The entry -/

/-- the routine byte -/
def rt (sy : Syms) (m : Machine) : UInt8 := peek m sy.GameEngineSubroutine

/-- the value of the pipe's routine -/
def vp (sy : Syms) : UInt8 := sy.EngVerticalPipe.toUInt8

/-- **An entry.** The frame of `m` with the input `i` ends with the pipe's routine, and `m` has another routine. -/
def Enters (sy : Syms) (m : Machine) (i : UInt8) : Prop := rt sy m ≠ vp sy ∧ rt sy (frame m i) = vp sy

/-- the instruction `n` of the frame makes the routine byte the pipe's -/
def WriteStep (sy : Syms) (m : Machine) (i : UInt8) (n : Nat) : Prop :=
  rt sy (trace m i n) ≠ vp sy ∧ rt sy (trace m i (n + 1)) = vp sy

/-- there is such an instruction -/
theorem writeStep_of_enters {sy : Syms} {m : Machine} {i : UInt8} (h : Enters sy m i) : ∃ n, n < fuelPerFrame ∧ WriteStep sy m i n := by
  have h0 : rt sy (trace m i 0) ≠ vp sy := h.1
  have h1 : rt sy (trace m i fuelPerFrame) = vp sy := by rw [← frame_trace]; exact h.2
  have key : ∀ N, rt sy (trace m i N) = vp sy → ∃ n, n < N ∧ WriteStep sy m i n := by
    intro N
    induction N with
    | zero => exact fun hz => absurd hz h0
    | succ N ih =>
      intro hs
      by_cases hN : rt sy (trace m i N) = vp sy
      · obtain ⟨n, h2, h3⟩ := ih hN
        exact ⟨n, by omega, h3⟩
      · exact ⟨N, by omega, hN, hs⟩
  exact key _ h1

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
  /-- the start of the foot check -/
  foot : UInt16
  /-- the block buffer routine -/
  entry : UInt16
  /-- its read of the block buffer -/
  read : UInt16
  /-- the instruction that writes the pipe's routine -/
  write : UInt16
  /-- where a pass ends without that instruction -/
  exits : List UInt16
  /-- the byte with the offset of the adders, and its values: a big Mario, a small or crouching one, and a big one in the water -/
  adI : Nat
  ads : List UInt8
  /-- the byte where the routine keeps its offset -/
  saveI : Nat
  /-- the pointer of the read -/
  ptrI : Nat
  /-- the search only: the byte with the foot's horizontal position, the place after it is stored, the bytes that keep a tile -/
  sumI : Nat
  afterSum : UInt16
  tempI : Nat
  rightI : Nat
  /-- the position -/
  xI : Nat
  pI : Nat
  /-- the stack pointer in the foot check -/
  stack : UInt8
  /-- the pipe's right tile, its place, the start of the block buffers, the rows of a block buffer -/
  tile : UInt8
  dR : Nat
  bufLo : Nat
  rows : Nat
  /-- the pipe's page, and the left end of the window in pixels -/
  pg : Nat
  left : Nat
  /-- no pass starts later in the frame than this dot -/
  late : Nat
  deriving Inhabited

/-- the offsets of the second foot -/
def Spots.idx2 (P : Spots) : List UInt8 := P.ads.map (· + 2)

/-- the bytes of the two block buffers -/
def Spots.bufBytes (P : Spots) : Nat := 2 * (16 * P.rows)

/-- the first address from `a` on, within `n` bytes, with this opcode -/
def findOp (m : Machine) (a : UInt16) (op : UInt8) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m a == op then a else findOp m (a + 1) op n

/-- the first `STA zero page` of the byte `z` from `a` on, within `n` bytes -/
def findStore (m : Machine) (a : UInt16) (z : UInt8) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m a == 0x85 && romByte m (a + 1) == z then a else findStore m (a + 1) z n

/-- the state of the machine when it first comes to `pc`, within `n` instructions -/
def firstAt (pc : UInt16) : Nat → Machine → Option Machine
  | 0, _ => none
  | n + 1, m => if m.pc == pc then some m else firstAt pc n (go step m).2

/-- the places, from the symbols; `s` is the stack pointer -/
def spotsOf (sy : Syms) (m0 : Machine) (s : UInt8) : Spots :=
  let pg := PipeEntry.pipePage sy m0
  let buf := if pg % 2 == 0 then sy.Block_Buffer_1 else sy.Block_Buffer_2
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let sum := findOp m0 sy.BlockBufferCollision 0x85 64
  { foot := sy.DoFootCheck
    entry := sy.BlockBufferCollision
    read
    write := findStore m0 sy.HandlePipeEntry sy.GameEngineSubroutine.toUInt8 64
    exits := [sy.DoPlayerSideCheck, sy.AwardTouchedCoin, sy.HandleAxeMetatile, sy.ImpedePlayerMove]
    adI := (romByte m0 (sy.DoFootCheck + 1)).toNat
    ads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 2), romByte m0 (sy.BlockBufferAdderData + 1)]
    saveI := (romByte m0 (sy.BlockBufferCollision + 2)).toNat
    ptrI := (romByte m0 (read + 1)).toNat
    sumI := (romByte m0 (sum + 1)).toNat
    afterSum := sum + 2
    tempI := (romByte m0 (read + 3)).toNat
    rightI := (romByte m0 (findOp m0 sy.HandlePipeEntry 0xC9 64 - 1)).toNat
    xI := (sy.Player_X_Position &&& 0x7FF).toNat
    pI := (sy.Player_PageLoc &&& 0x7FF).toNat
    stack := s
    tile := sy.PipeRightTile.toUInt8
    dR := ((buf + (PipeEntry.column sy + 1 + 16 * PipeEntry.row sy).toUInt16) &&& 0x7FF).toNat
    bufLo := (sy.Block_Buffer_1 &&& 0x7FF).toNat
    rows := (sy.Block_Buffer_2 - sy.Block_Buffer_1).toNat / 16
    pg
    left := 256 * pg + PipeEntry.xLo sy
    late := dotsPerFrame - 6000 }

/-- the stack pointer in the foot check, from the first frame with Right held -/
def footStack (sy : Syms) (m0 : Machine) : UInt8 :=
  match firstAt sy.DoFootCheck 100000 { m0 with pad := 0x01 } with
  | some m => m.s
  | none => 0

/-- the places of the game -/
def spots (sy : Syms) (m0 : Machine) : Spots := spotsOf sy m0 (footStack sy m0)

/-- the environment of the walk -/
def envOf (m0 : Machine) : Env := { prg := m0.prg, mask := m0.prgMask, pad := AB.top, D := [] }

/-! ## The conditions on one pass -/

/-- the machine starts the foot check, between the frame's first event and its end -/
structure Start (P : Spots) (E : Env) (m : Machine) : Prop where
  pc : m.pc = P.foot
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

/-- the machine enters the block buffer routine for the right foot -/
def AtEntry (P : Spots) (m : Machine) : Prop := m.pc = P.entry ∧ m.y ∈ P.idx2

/-- the position in pixels -/
def px (P : Spots) (m : Machine) : Nat := 256 * (m.ram.get! P.pI).toNat + (m.ram.get! P.xI).toNat

/-- the machine is at the read of the right foot -/
def AtRead (P : Spots) (m : Machine) : Prop := m.pc = P.read ∧ m.ram.get! P.saveI ∈ P.idx2

/-- the read's offset is a row of the block buffer -/
def RowOK (P : Spots) (m : Machine) : Prop := m.y.toNat % 16 = 0 ∧ m.y.toNat < 16 * P.rows

/-- on the pipe's page or before it, the pipe's right tile is in the block buffers only at its place, and only from the page before the pipe's on -/
def TilesOK (P : Spots) (m : Machine) : Prop :=
  (m.ram.get! P.pI).toNat ≤ P.pg → ∀ i, P.bufLo ≤ i → i < P.bufLo + P.bufBytes → m.ram.get! i = P.tile →
    i = P.dR ∧ P.pg ≤ (m.ram.get! P.pI).toNat + 1

/-- **What stays assumed about a read.** -/
def ReadOK (P : Spots) (m : Machine) : Prop := RowOK P m ∧ TilesOK P m

/-- **What stays assumed about the write.** The instruction `n` is the routine's write. Before it in this frame the machine started the foot check, and from there on it did not leave the check, and
each read of the right foot is `ReadOK`. -/
def Pass (P : Spots) (E : Env) (tr : Nat → Machine) (n : Nat) : Prop :=
  (tr n).pc = P.write ∧ ∃ n₀, n₀ ≤ n ∧ Start P E (tr n₀) ∧ (∀ j, n₀ ≤ j → j ≤ n → (tr j).pc ∉ P.exits) ∧
    (∀ j, n₀ ≤ j → j < n → AtRead P (tr j) → ReadOK P (tr j))

/-! ## The walk -/

/-- a byte whose bit `b` differs from that of `t` -/
def neBit (t b : UInt8) : AB := ⟨~~~t, b⟩

/-- the RAM index of the row `r` from the pointer `p` -/
def rowI (p : UInt16) (r : Nat) : Nat := ((p + (16 * r).toUInt16) &&& 0x7FF).toNat

/-- the pointer, as far as its bytes say -/
def ptrAt (P : Spots) (A : AS) : UInt16 := (A.getK P.ptrI).v.toUInt16 ||| ((A.getK (P.ptrI + 1)).v.toUInt16 <<< 8)

/-- every row from this pointer is in the block buffers, and not the tile's place unless the tile cannot be there yet -/
def safe (P : Spots) (p : UInt16) (pa : AB) : Bool :=
  decide (pa.maxv.toNat ≤ P.pg) && (List.range P.rows).all fun r =>
    decide (P.bufLo ≤ rowI p r) && decide (rowI p r < P.bufLo + P.bufBytes) && (rowI p r != P.dR || decide (pa.maxv.toNat + 1 < P.pg))

def splitAll (d : Nat) (A : AS) : List AS := bitList.foldl (fun l b => l.flatMap (splitBit d b)) [A]

/-- the pieces before a step. At the entry for the right foot: the position, left of the window. At the read of the right foot: the row, and a bit where the byte read differs from the pipe's tile.
At another read with the pointer not known: the pointer. -/
def preR (P : Spots) (A : AS) : List AS :=
  if A.pc == P.entry && A.y.isK && P.idx2.contains A.y.v then
    (List.range P.left).map fun n => (A.setK P.xI (AB.known (n % 256).toUInt8)).setK P.pI (AB.known (n / 256).toUInt8)
  else if A.pc == P.read then
    if (A.getK P.ptrI).isK then
      let sv := A.getK P.saveI
      let pa := A.getK P.pI
      if sv.isK && P.idx2.contains sv.v && (A.getK (P.ptrI + 1)).isK && safe P (ptrAt P A) pa then
        (List.range P.rows).flatMap fun r =>
          bitList.map fun b => ({ A with y := AB.known (16 * r).toUInt8 } : AS).setK (rowI (ptrAt P A) r) (neBit P.tile b)
      else [A]
    else splitAll P.ptrI A
  else [A]

/-- the bytes that keep states apart in the table -/
def keepR (P : Spots) : List Nat := [P.adI, P.saveI, P.ptrI, P.ptrI + 1, P.xI, P.pI, P.sumI, P.rightI, P.tempI]

/-- states with the same key are joined -/
def keyR (P : Spots) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := A.s.toNat * 65536 + A.pc.toNat
  let n := n * 65536 + num A.x
  let n := n * 65536 + num A.y
  let n := n * 65536 + num A.a
  let n := n * 65536 + num (A.p.and (AB.known 1))
  let n := (keepR P).foldl (fun n i => n * 65536 + num (A.getK i)) n
  n * 4294967296 + stackHash A

/-- what the table forgets at some places: the search only -/
def forget (l : List Nat) (A : AS) : AS := l.foldl (fun B i => B.setK i AB.top) A

/-- the live part of the RAM is the stack -/
def onlyStack (A : AS) : AS :=
  let kn := (List.range (255 - A.s.toNat)).foldl (fun k j => k.set! (0x100 + A.s.toNat + 1 + j) (A.getK (0x100 + A.s.toNat + 1 + j)).k) (ByteArray.mk (Array.replicate 2048 0))
  { A with kn }

def normR (P : Spots) (A : AS) : AS :=
  if A.pc == P.afterSum then
    if (A.getK P.xI).isK then
      { (forget [P.xI] A).setK P.sumI ⟨(A.getK P.sumI).v, (A.getK P.sumI).k &&& 0xF0⟩ with a := AB.top }
    else A
  else if A.pc == P.read then
    let sv := A.getK P.saveI
    if sv.isK && P.idx2.contains sv.v then
      if (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && (List.range P.rows).all (fun r => rowI (ptrAt P A) r != P.dR) then
        (forget [P.xI] A).setK P.pI ((List.range (P.pg + 1)).foldl (fun b n => b.join (AB.known n.toUInt8)) (AB.known 0))
      else forget [P.xI] A
    else A
  else if A.pc == P.read + 2 then
    let sv := A.getK P.saveI
    if sv.isK && P.idx2.contains sv.v then { onlyStack A with y := AB.top }
    else { forget [P.ptrI, P.ptrI + 1] A with y := AB.top }
  else A

/-- the table -/
structure CfgR where
  E : Env
  ops : Array (AM Unit)
  P : Spots
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

def coverR (C : CfgR) (B : AS) : Bool :=
  (C.idx.getD (keyR C.P (normR C.P B)) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D
    | none => false

/-- from `A`, step by step until every path ends at an exit or in a state of the table. No path comes to the write. -/
def walkR (C : CfgR) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preR C.P A).all fun A₁ => (succs C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      C.P.exits.contains B.pc ||
        (B.pc != C.P.write && ((C.cut.get! B.pc.toNat != 0 && coverR C B) || walkR C n B))

/-! ## Finding the table: a search, no part of the proof -/

structure SR where
  pending : Std.TreeMap Nat AS compare := {}
  inN : Std.HashMap Nat Nat := {}
  out : Array AS := #[]
  leaders : Std.HashMap Nat Unit := {}
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  firstFail : Option AS := none

def routeR (P : Spots) (X : SR) (B0 : AS) : SR :=
  let B := normR P B0
  let K := keyR P B
  match X.pending[K]? with
  | some Q => { X with pending := X.pending.insert K (Q.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

partial def runR (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) (A0 : AS) : SR := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preR P cur).flatMap (succs E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := (rs.filterMap id).filter fun b => !P.exits.contains b.pc
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != P.read && b.pc != P.write && b.pc != P.read + 2 && b.pc != P.afterSum &&
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
        X := routeR P X b
    break
  return X

partial def searchR (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) : SR := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      if n ≥ 2 || A.pc == P.read || A.pc == P.read + 2 || A.pc == P.afterSum then X := { X with out := X.out.push A }
      X := runR E ops P X A
  return X

/-- the abstract state at the start of the foot check: only the stack pointer and the offset of the adders are known -/
def startAt (P : Spots) (e : UInt8) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := P.stack, p := AB.top, pc := P.foot,
    ram := (ByteArray.mk (Array.replicate 2048 0)).set! P.adI e,
    kn := (ByteArray.mk (Array.replicate 2048 0)).set! P.adI 0xFF,
    ppuCtrl := AB.top, ppuMask := AB.top, vb := false, nmi := false, lo := dotVblClr, hi := P.late, padShift := AB.top, strobe := false, dg := false, k := 0 }

def searchOf (E : Env) (P : Spots) : SR :=
  let ops := (aRows E).toArray
  searchR E ops P ((P.ads.map (startAt P)).foldl (routeR P) {})

def cfgOf (E : Env) (P : Spots) : CfgR :=
  let X := searchOf E P
  let q := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyR P A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops := (aRows E).toArray, P, t := X.out, idx := q.1, cut := q.2.1 }

/-- the fuel of a walk -/
def fuelR : Nat := 4000

/-- **The check.** The places are bytes of the RAM, the start is not the write, and the walks succeed. -/
def walkCheck (E : Env) (P : Spots) : Bool :=
  let C := cfgOf E P
  decide (P.adI < 2048) && decide (P.ptrI + 1 < 2048) && decide (P.xI < 2048) && decide (P.pI < 2048) && decide (P.saveI < 2048) &&
  P.foot != P.write && decide (P.late < dotsPerFrame) &&
  C.t.all (walkR C fuelR) && (P.ads.map (startAt P)).all (walkR C fuelR)

/-- the check on the ROM -/
def ruleCheck (sy : Syms) (m0 : Machine) : Bool := walkCheck (envOf m0) (spots sy m0)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8} {P : Spots}

theorem sim_setK' {A : AS} {m : Machine} (hs : Sim E F A m) {d : Nat} {v : AB} (hv : v.mem (m.ram.get! d)) : Sim E F (A.setK d v) m := by
  refine { hs with
    ram := ?_
    szR := ?_
    szK := ?_ }
  · intro i hi
    show AB.mem ⟨(A.ram.set! d v.v).get! i, (A.kn.set! d v.k).get! i⟩ (m.ram.get! i)
    by_cases hdi : d = i
    · subst hdi
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi)]
      exact hv
    · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
      exact hs.ram i hi
  · show (A.ram.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szR
  · show (A.kn.set! d _).size = 2048
    rw [ba_size_set]
    exact hs.szK

theorem cov_all {d : Nat} (hd : d < 2048) : Cov E F (splitAll d) := by
  intro A m hs
  unfold splitAll
  have key : ∀ (l : List UInt8), (∀ b ∈ l, b ∈ bitList) → ∀ (x : List AS), (∃ B ∈ x, Sim E F B m ∧ B.k = A.k) →
      ∃ B ∈ l.foldl (fun l b => l.flatMap (splitBit d b)) x, Sim E F B m ∧ B.k = A.k := by
    intro l
    induction l with
    | nil => exact fun _ x hx => hx
    | cons b l ih =>
      intro hl x hx
      simp only [List.foldl_cons]
      exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) _ (cov_flat (cov_bit hd (hl b List.mem_cons_self)) hx)
  exact key bitList (fun _ h => h) [A] ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- a byte that is not `t` differs from it at a bit -/
theorem ne_bit {x t : UInt8} (h : x ≠ t) : ∃ b ∈ bitList, (neBit t b).mem x := by
  have hne : ∃ i, i < 8 ∧ bt x i ≠ bt t i := by
    by_cases hall : ∀ i, i < 8 → bt x i = bt t i
    · exact absurd (bt_ext hall) h
    · simp only [Classical.not_forall] at hall
      obtain ⟨i, hi, hn⟩ := hall
      exact ⟨i, hi, hn⟩
  obtain ⟨i, hi, hn⟩ := hne
  obtain ⟨b, hb, hbb⟩ := bit_list ⟨i, hi⟩
  refine ⟨b, hb, ?_⟩
  show x &&& b = ~~~t &&& b
  apply bt_ext
  intro j hj
  have e := hbb ⟨j, hj⟩
  simp only at e
  rw [bt_and, bt_and, e, bt_not _ _ hj]
  by_cases hji : j = i
  · subst hji
    cases h1 : bt x j <;> cases h2 : bt t j <;> simp_all
  · simp [hji]

/-- the row of a read, as a number -/
theorem row_of {y : UInt8} {R : Nat} (h : y.toNat % 16 = 0 ∧ y.toNat < 16 * R) : ∃ r, r < R ∧ y = (16 * r).toUInt8 := by
  refine ⟨y.toNat / 16, by omega, ?_⟩
  apply UInt8.toNat_inj.1
  have : 16 * (y.toNat / 16) = y.toNat := by omega
  rw [this]
  simp

theorem pos_digits {p x : UInt8} {n : Nat} (hn : n = 256 * p.toNat + x.toNat) : (n % 256).toUInt8 = x ∧ (n / 256).toUInt8 = p := by
  have hx := x.toNat_lt
  constructor
  · have : n % 256 = x.toNat := by omega
    rw [this]
    simp
  · have : n / 256 = p.toNat := by omega
    rw [this]
    simp

/-- what `preR` needs of the machine -/
def HypAt (P : Spots) (m : Machine) : Prop :=
  (AtEntry P m → px P m < P.left) ∧ (AtRead P m → ReadOK P m)

theorem known_eq {b : AB} {x : UInt8} (hk : b.isK = true) (h : b.mem x) : x = b.v := by
  have h1 : b.k = 0xFF := by simpa [AB.isK] using hk
  have h2 : x &&& b.k = b.v &&& b.k := h
  rw [h1] at h2
  have e : ∀ c : UInt8, c &&& 0xFF = c := fun c => by
    apply bt_ext
    intro j hj
    rw [bt_and, TaintRun.bt_ff hj, Bool.and_true]
  rwa [e, e] at h2

/-- every machine that meets `HypAt` is in a piece -/
theorem cov_pre (hb : P.xI < 2048 ∧ P.pI < 2048 ∧ P.ptrI < 2048 ∧ P.saveI < 2048) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : HypAt P m) : ∃ B ∈ preR P A, Sim E F B m := by
  unfold preR
  by_cases h1 : (A.pc == P.entry && A.y.isK && P.idx2.contains A.y.v) = true
  · rw [if_pos h1]
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨h2, h3⟩, h4⟩ := h1
    have hy : m.y = A.y.v := known_eq h3 hs.y
    have ha : AtEntry P m := ⟨by rw [hs.pc, h2], by
      rw [hy]
      exact List.mem_of_elem_eq_true h4⟩
    have hlt := hh.1 ha
    obtain ⟨d1, d2⟩ := pos_digits (n := px P m) (p := m.ram.get! P.pI) (x := m.ram.get! P.xI) rfl
    refine ⟨_, List.mem_map.2 ⟨px P m, List.mem_range.2 hlt, rfl⟩, ?_⟩
    refine sim_setK' (sim_setK' hs ?_) ?_
    · rw [d1]
      exact mem_known_self _
    · rw [d2]
      exact mem_known_self _
  · rw [if_neg h1]
    by_cases h2 : (A.pc == P.read) = true
    · rw [if_pos h2]
      by_cases h3 : (A.getK P.ptrI).isK = true
      · rw [if_pos h3]
        simp only
        by_cases h4 : ((A.getK P.saveI).isK && P.idx2.contains (A.getK P.saveI).v && (A.getK (P.ptrI + 1)).isK && safe P (ptrAt P A) (A.getK P.pI)) = true
        · rw [if_pos h4]
          simp only [Bool.and_eq_true] at h4
          obtain ⟨⟨⟨h5, h6⟩, _⟩, h9⟩ := h4
          have hpc : m.pc = P.read := by rw [hs.pc]; exact beq_iff_eq.1 h2
          have hsv : m.ram.get! P.saveI = (A.getK P.saveI).v := known_eq h5 (hs.ram _ hb.2.2.2)
          have hat : AtRead P m := ⟨hpc, by rw [hsv]; exact List.mem_of_elem_eq_true h6⟩
          obtain ⟨hrow, htiles⟩ := hh.2 hat
          obtain ⟨r, hr, hyr⟩ := row_of hrow
          have hpage : (m.ram.get! P.pI).toNat ≤ (A.getK P.pI).maxv.toNat := TaintRun.le_maxv (hs.ram _ hb.2.1)
          simp only [safe, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne] at h9
          obtain ⟨h10, h11⟩ := h9
          obtain ⟨⟨h12, h13⟩, h14⟩ := h11 r (List.mem_range.2 hr)
          have hnot : m.ram.get! (rowI (ptrAt P A) r) ≠ P.tile := by
            intro he
            have ht := htiles (by omega) _ h12 h13 he
            rcases h14 with h14 | h14
            · exact h14 ht.1
            · have := ht.2
              omega
          obtain ⟨b, hb1, hb2⟩ := ne_bit hnot
          refine ⟨_, List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨b, hb1, rfl⟩⟩, ?_⟩
          have hs2 : Sim E F ({ A with y := AB.known (16 * r).toUInt8 } : AS) m := { hs with y := by rw [hyr]; exact mem_known_self _ }
          exact sim_setK' hs2 hb2
        · rw [if_neg h4]
          exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      · rw [if_neg h3]
        obtain ⟨B, h5, h6, _⟩ := cov_all hb.2.2.1 A m hs
        exact ⟨B, h5, h6⟩
    · rw [if_neg h2]
      exact ⟨A, List.mem_singleton.2 rfl, hs⟩

end

/-! ## The walk covers the machine -/

section
variable {C : CfgR} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveR (C : CfgR) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkR C n A = true

theorem cover_liveR (ht : C.t.all (walkR C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverR C B = true) : ∃ D, LiveR C F D m := by
  unfold coverR at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le h2 hs, Fu, hall⟩
  · cases h2

theorem live_stepR (ht : C.t.all (walkR C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : C.P.xI < 2048 ∧ C.P.pI < 2048 ∧ C.P.ptrI < 2048 ∧ C.P.saveI < 2048) {A : AS} {m : Machine} (hl : LiveR C F A m) (hh : HypAt C.P m) (hex : (go step m).2.pc ∉ C.P.exits) :
    (go step m).2.pc ≠ C.P.write ∧ ∃ A', LiveR C F A' (go step m).2 := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkR] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_pre hb hs hh
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs1
    simp only [walkR, List.all_eq_true] at hw
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
        · exact cover_liveR ht h1 h4
        · exact ⟨B, h1, n, h4⟩

end

/-! ## A pass that starts left of the window does not come to the write -/

theorem zeros_get (n i : Nat) : (ByteArray.mk (Array.replicate n (0 : UInt8))).get! i = 0 := by
  show (Array.replicate n (0 : UInt8))[i]! = 0
  by_cases h : i < n
  · simp [h]
  · simp [h]
    rfl

theorem zeros_size (n : Nat) : (ByteArray.mk (Array.replicate n (0 : UInt8))).size = n := by
  simp [ByteArray.size]

section
variable {E : Env} {P : Spots}

/-- the state at the start of the foot check covers the machine -/
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
  bytes : P.adI < 2048 ∧ P.xI < 2048 ∧ P.pI < 2048 ∧ P.ptrI < 2048 ∧ P.saveI < 2048
  ne : P.foot ≠ P.write
  late : P.late < dotsPerFrame
  table : (cfgOf E P).t.all (walkR (cfgOf E P) fuelR) = true
  starts : ∀ e ∈ P.ads, walkR (cfgOf E P) fuelR (startAt P e) = true

theorem walkOK_of_check (h : walkCheck E P = true) : WalkOK E P := by
  simp only [walkCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨h1, h3, h4, by omega, h5⟩, h6, h7, h8, h9⟩

/-- **A pass.** If the position at each entry for the right foot is left of the window and each read of it is `ReadOK`, the machine does not come to the write. -/
theorem no_write (hc : walkCheck E P = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat} (hs : ∀ j, j < n → s (j + 1) = (go step (s j)).2)
    (h0 : Start P E (s 0)) (hh : ∀ j, j < n → HypAt P (s j)) (hex : ∀ j, j ≤ n → (s j).pc ∉ P.exits) : (s n).pc ≠ P.write := by
  have hC := walkOK_of_check hc
  obtain ⟨e, he, hsim⟩ := sim_start hC.late hE h0
  have hb : (cfgOf E P).P.xI < 2048 ∧ (cfgOf E P).P.pI < 2048 ∧ (cfgOf E P).P.ptrI < 2048 ∧ (cfgOf E P).P.saveI < 2048 :=
    ⟨hC.bytes.2.1, hC.bytes.2.2.1, hC.bytes.2.2.2.1, hC.bytes.2.2.2.2⟩
  have live : ∀ j, j ≤ n → (j = 0 ∨ (s j).pc ≠ P.write) ∧ ∃ A, LiveR (cfgOf E P) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨Or.inl rfl, _, hsim, fuelR, hC.starts e he⟩
    | succ j ih =>
      intro hj
      obtain ⟨_, A, hA⟩ := ih (by omega)
      have e1 := hs j (by omega)
      have hx := hex (j + 1) hj
      rw [e1] at hx ⊢
      obtain ⟨h1, h2⟩ := live_stepR hC.table rfl (show 2 ≤ (2 : UInt8).toNat by decide) hb hA (hh j (by omega)) hx
      exact ⟨Or.inr h1, h2⟩
  rcases (live n (Nat.le_refl n)).1 with h1 | h1
  · subst h1
    rw [h0.pc]
    exact hC.ne
  · exact h1

end

/-! ## The frame -/

/-- **The entry on a real frame.** If the frame enters and the instruction that writes the routine byte ends a `Pass`, then in that pass, when the block buffer routine is entered for the right foot,
the position is at or right of the window's left end. -/
theorem entry_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : ruleCheck sy m0 = true) (he : Enters sy m i)
    (hp : ∀ n, WriteStep sy m i n → Pass (spots sy m0) (envOf m0) (trace m i) n) :
    ∃ n j, WriteStep sy m i n ∧ j < n ∧ AtEntry (spots sy m0) (trace m i j) ∧ (spots sy m0).left ≤ px (spots sy m0) (trace m i j) := by
  obtain ⟨n, _, hw⟩ := writeStep_of_enters he
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

/-- **The rule on frames.** `fm t` is the machine when frame `t` begins and `inp t` its input. If a frame enters, the instruction of the write ends a `Pass`, and `P₂` is the position when the block buffer routine is entered
for the right foot before the write, then `P₂` is at or right of the window's left end. This is what `PipeEntry.no_entry_by` needs. `PipeWrites.rule_on_frames` gives the same without `Pass`, and `Route.Pipe` uses that. `PipeEntry.rule_of_cases` gives the same from `rule` on a hand-written buffer. -/
theorem rule_on_frames {top amax : Int} {sy : Syms} {m0 : Machine} (hc : ruleCheck sy m0 = true) (fr : Nat → TopSpeed.Frame top amax)
    (fm : Nat → Machine) (inp : Nat → UInt8)
    (hp : ∀ t, Enters sy (fm t) (inp t) → ∀ n, WriteStep sy (fm t) (inp t) n → Pass (spots sy m0) (envOf m0) (trace (fm t) (inp t)) n)
    (hpos : ∀ t, Enters sy (fm t) (inp t) → ∀ n j, WriteStep sy (fm t) (inp t) n → j < n → AtEntry (spots sy m0) (trace (fm t) (inp t) j) →
      ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (px (spots sy m0) (trace (fm t) (inp t) j) : Int) + f) :
    ∀ t, Enters sy (fm t) (inp t) → PipeEntry.windowP sy (PipeEntry.pipePage sy m0) ≤ (fr t).P₂ := by
  intro t he
  obtain ⟨n, j, h0, h1, h2, h3⟩ := entry_right_of_left hc he (hp t he)
  obtain ⟨f, hf, h4⟩ := hpos t he n j h0 h1 h2
  rw [h4]
  have h5 : (spots sy m0).left = 256 * PipeEntry.pipePage sy m0 + PipeEntry.xLo sy := rfl
  rw [h5] at h3
  unfold PipeEntry.windowP
  omega

/-! ## On real frames: a program, no part of the proof -/

def startOK (P : Spots) (E : Env) (m : Machine) : Bool :=
  m.pc == P.foot && m.s == P.stack && P.ads.contains (m.ram.get! P.adI) && decide (dotVblClr ≤ m.fdot) && decide (m.fdot ≤ P.late) &&
  !m.vblank && !m.nmiPending && m.sprite0 == s0f m.fdot && !m.padStrobe && !m.halted && !m.trk && m.prgMask == E.mask && m.ram.size == 2048

def rowOK (P : Spots) (m : Machine) : Bool := m.y.toNat % 16 == 0 && decide (m.y.toNat < 16 * P.rows)

def tilesOK (P : Spots) (m : Machine) : Bool :=
  let pa := (m.ram.get! P.pI).toNat
  !decide (pa ≤ P.pg) || (List.range P.bufBytes).all fun j =>
    let i := P.bufLo + j
    m.ram.get! i != P.tile || (i == P.dR && decide (P.pg ≤ pa + 1))

/-- what real frames say about the hypotheses -/
structure Report where
  frames : Nat := 0
  /-- arrivals at the foot check with the player's routine, and how many do not meet `Start` -/
  passes : Nat := 0
  startBad : Nat := 0
  /-- reads of the right foot on the pipe's page or before, and how many do not meet `RowOK`, `TilesOK` -/
  reads : Nat := 0
  rowBad : Nat := 0
  tilesBad : Nat := 0
  /-- frames that enter; of them: not by the write; not at the end of a pass; left of the window; right of it or on another page; the position changes after the foot check -/
  entries : Nat := 0
  writeBad : Nat := 0
  passBad : Nat := 0
  leftBad : Nat := 0
  rightOut : Nat := 0
  moved : Nat := 0
  /-- the positions at which frames entered -/
  pxs : List Nat := []
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, passes {r.passes} (not Start: {r.startBad}), reads {r.reads} (not RowOK: {r.rowBad}, not TilesOK: {r.tilesBad}), entries {r.entries} (not the write: {r.writeBad}, not a pass: {r.passBad}, left of the window: {r.leftBad}, right of it: {r.rightOut}, position moved after: {r.moved}), positions {r.pxs.eraseDups}"

/-- one real frame with the bits `pad` of the controller -/
def scanFrame (sy : Syms) (P : Spots) (E : Env) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let mut r := { r0 with frames := r0.frames + 1 }
  let mut inPass := false
  let mut passOK := true
  let mut lastPx : Option Nat := none
  let mut n := 0
  let mut entered : Option Nat := none
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if c.pc == P.foot then
      let ok := startOK P E c
      let ctl := rt sy c == sy.Eng_PlayerCtrl.toUInt8
      r := { r with passes := r.passes + (if ctl then 1 else 0), startBad := r.startBad + (if ok || !ctl then 0 else 1) }
      inPass := ok
      passOK := ok
      lastPx := none
    if P.exits.contains c.pc then inPass := false
    if c.pc == P.entry && P.idx2.contains c.y then lastPx := some (256 * (c.ram.get! P.pI).toNat + (c.ram.get! P.xI).toNat)
    if c.pc == P.read && P.idx2.contains (c.ram.get! P.saveI) then
      let a := rowOK P c
      let b := tilesOK P c
      r := { r with reads := r.reads + 1, rowBad := r.rowBad + (if a then 0 else 1), tilesBad := r.tilesBad + (if b then 0 else 1) }
      if !(a && b) then passOK := false
    let before := rt sy c
    let pc := c.pc
    c := (go step c).2
    if before != vp sy && rt sy c == vp sy then
      r := { r with entries := r.entries + 1, writeBad := r.writeBad + (if pc == P.write then 0 else 1),
                    passBad := r.passBad + (if inPass && passOK && lastPx.isSome then 0 else 1) }
      match lastPx with
      | some q =>
        r := { r with leftBad := r.leftBad + (if q < P.left then 1 else 0), pxs := q :: r.pxs,
                      rightOut := r.rightOut + (if q > 256 * P.pg + PipeEntry.xHi sy then 1 else 0) }
        entered := some q
      | none => pure ()
    n := n + 1
  match entered with
  | some q => if 256 * (c.ram.get! P.pI).toNat + (c.ram.get! P.xI).toNat != q then r := { r with moved := r.moved + 1 }
  | none => pure ()
  return (r, c)

end Smbrta.PipeEntryRule
