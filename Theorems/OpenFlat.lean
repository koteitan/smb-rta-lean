import Theorems.OpenMap
import Theorems.CtrlKeep
import Theorems.FrameWalk

/-!
# The flat ground of the opening: a frame on the ground with no jump ends on the ground

A counted frame of the opening that begins on the ground (the state 0, the height of `m0`, the high byte of the height 1, the vertical speed and its fraction 0) and
whose player's routine reads no jump ends on the ground, or out of control (`flat_end`). Three walks cover the frame:
* up to the player's routine, the walk of the pause bit of `CtrlKeep`: there the bytes of `CtrlKeep.keepA` are those of the frame's start (`CtrlKeep.ctrl_keep`), and one
  more walk of `CtrlKeep` follows the high byte of the height (`high_at_cut`). The jump that the routine reads gives two cases of the input: A not pressed, or A held;
* from there to the return of the collision routine (`collRet`), a walk with the step of `FrameKeep` but at the read of the block buffer routine (`fstep`): there the tiles
  are those of the first block buffer of `m0` at the addresses that the known bits of the pointer and of `Y` allow (`tilesAt`). At the routine that makes the pointer,
  `Y` (the buffer's number) is split into its two values (`yPieces`), so the pointer's high bits are known. With the height known, the row of each read is known: the feet
  read the ground, and he lands again (`walkQ`, `to_stop`);
* from the return to the frame's end, a walk of `FrameKeep` with the state and the jumpspring byte protected (`after_endK`).
What each instruction must meet: `CleanK` of `FrameKeep.guardK` and of `guardQ` (from `FrameKeep.guardF` and `OpenMap.MapOK`, `cleanQ_of`), and at the read: the address in
the first block buffer with the byte of `m0` (`RdOK1`, from `OpenMap.MapOK` and the walk of `OpenMap`, `rdOK1_of`).

There is no game data in this file. Page: `1-1/a-5-4-3-4-1-OpenFlat.md`.
-/

namespace Smbrta.OpenFlat

open PipeTransition (frame)
open TaintRun (AS Sim Env AB)
open PipeWrites (Guard Clean FrameStart guardOf SG knownOf)
open PipeEntryRule (trace)
open FrameKeep (Watch Watched CfgK Spot CleanK)
open PipeTransitionAll (go)

/-! ## The read of the block buffer routine, with the known bits of its address -/

/-- the read of the block buffer routine (`LDA (zp),Y`), the first block buffer, the RAM of `m0`, and the `ADC abs,Y` of the routine that makes the pointer -/
structure Rd1 where
  pc : UInt16
  lo : Nat
  ram : ByteArray
  adc : UInt16
  deriving Inhabited

/-- the value `c` has the known bits of `x` -/
def canBe (x : AB) (c : UInt8) : Bool := c &&& x.k == x.v &&& x.k

/-- a RAM index of the first block buffer -/
def inBuf1 (R : Rd1) (i : Nat) : Bool := decide (R.lo ≤ i) && decide (i < R.lo + 0xD0)

/-- every tile of the first block buffer of `m0` -/
def tilesAll (R : Rd1) : List UInt8 := ((List.range 0xD0).map fun j => R.ram.get! (R.lo + j)).eraseDups

/-- the address of `LDA (zp),Y` with the pointer `lo`, `hi` and the index `y` -/
def addrOf (lo hi y : UInt8) : UInt16 := ((lo.toUInt16 ||| (hi.toUInt16 <<< 8))) + y.toUInt16

/-- **The tiles that the read may give**: the bytes of the first block buffer of `m0` at the addresses that the known bits of the pointer (at `z`, `z + 1`) and of
`Y` allow. If `Y` or the pointer's high byte is not known, every tile of the buffer. -/
def tilesAt (R : Rd1) (z : UInt8) (A : AS) : List UInt8 :=
  let lo := A.getK (z.toUInt16 &&& 0x7FF).toNat
  let hi := A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat
  if A.y.isK && hi.isK then
    ((List.range 256).filterMap fun l =>
      if canBe lo l.toUInt8 then
        let ad := addrOf l.toUInt8 hi.v A.y.v
        if decide (ad < 0x2000) && inBuf1 R (ad &&& 0x7FF).toNat then some (R.ram.get! (ad &&& 0x7FF).toNat) else none
      else none).eraseDups
  else tilesAll R

/-- at the routine's `ADC abs,Y` that makes the pointer, `Y` is the buffer's number, 0 or 1: one piece for each -/
def yPieces (R : Rd1) (A : AS) : List AS :=
  if A.pc == R.adc && !A.y.isK && A.y.k == 0xFE then [{ A with y := AB.known (A.y.v &&& 0xFE) }, { A with y := AB.known ((A.y.v &&& 0xFE) ||| 1) }] else [A]

/-- the step of the walk: at the read, one path for each tile it may give; elsewhere the step of `FrameKeep` -/
def fstep (R : Rd1) (S : Spot) (G : Guard) (E : Env) (ops : Array (TaintRun.AM Unit)) (A : AS) : List (Option AS) :=
  if !A.nmi && A.pc == R.pc then
    if decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1 then
      (tilesAt R (E.prg.get! ((A.pc + 1) &&& E.mask).toNat) A).map fun T => ScreenPage.readStep E (AB.known T) A
    else [none]
  else if !A.nmi && decide (0x8000 ≤ A.pc) && E.prg.get! (A.pc &&& E.mask).toNat == 0x79 then
    let r := FrameKeep.kstep S G E ops A
    if r.all Option.isSome then r else TaintRun.succs E ops A
  else FrameKeep.kstep S G E ops A

/-- the pieces before a step -/
def preF (R : Rd1) (S : Spot) (G : Guard) (A : AS) : List AS := (FrameKeep.preK S G A).flatMap (yPieces R)

/-- the same walk with a stop: a path that comes to `Q` asks `after` there and is not followed further -/
def walkQ (R : Rd1) (C : CfgK) (Q : UInt16) (after : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preF R C.S C.G A).all fun A₁ => (fstep R C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        (if B.pc == Q then after B else (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkQ R C Q after n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ### Finding its table: a search, no part of the proof -/

/-- what the search forgets: as `OpenMap.normT`, but it keeps the bytes `extra` too -/
def normF (keepAt : UInt16 → Bool) (temps extra : List Nat) (S : Spot) (G : Guard) (A0 : AS) : AS :=
  let G' := { G with prot := extra ++ G.prot }
  if keepAt A0.pc then FrameKeep.normK { S with entry := A0.pc, store := A0.pc, temps } G' A0 else FrameKeep.normK S G' A0

/-- the search's step into the table, with the normalization `normF` -/
def routeF (keepAt : UInt16 → Bool) (temps extra : List Nat) (S : Spot) (G : Guard) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := normF keepAt temps extra S G B0
  let K := key B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

/-- the search with a stop: a state at `Q` is not followed but kept (for the walk after `Q`): no part of the proof -/
partial def runQ (R : Rd1) (keepAt : UInt16 → Bool) (temps extra : List Nat) (S : Spot) (G : Guard) (E : Env) (Q : UInt16) (key : AS → Nat) (ops : Array (TaintRun.AM Unit))
    (fin : AS → Bool) (X0 : SG × Array AS) (A0 : AS) : SG × Array AS := Id.run do
  let mut X := X0.1
  let mut qs := X0.2
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preF R S G cur).flatMap (fstep R S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !(fin B)
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good0 := (rs.filterMap id).filter fun b => b.k == cur.k
    for b in good0 do
      if b.pc == Q then qs := qs.push b
    let good := good0.filter fun b => b.pc != Q
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && b.pc != R.pc && b.pc != R.adc &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeF keepAt temps extra S G key X b
    break
  return (X, qs)

partial def searchQ (R : Rd1) (keepAt : UInt16 → Bool) (temps extra : List Nat) (S : Spot) (G : Guard) (E : Env) (Q : UInt16) (key : AS → Nat) (ops : Array (TaintRun.AM Unit))
    (fin : AS → Bool) (X0 : SG) : SG × Array AS := Id.run do
  let mut X := (X0, #[])
  while true do
    match X.1.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := ({ X.1 with pending := X.1.pending.erase k }, X.2)
      X := runQ R keepAt temps extra S G E Q key ops fin X A
  return X

/-- the search of a walk of `FrameKeep` (the steps `kstep`) that keeps the bytes `extra` too (`normF`), and keeps the states at the frame's end: no part of the proof -/
partial def runKF (extra : List Nat) (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool)
    (X0 : SG × Array AS) (A0 : AS) : SG × Array AS := Id.run do
  let mut X := X0.1
  let mut ends := X0.2
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (FrameKeep.preK S G cur).flatMap (FrameKeep.kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !(FrameKeep.watchOK W B && fin B)
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    for r in rs do
      match r with
      | some B => if B.k != cur.k then ends := ends.push B
      | none => pure ()
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeF (fun _ => false) [] extra S G key X b
    break
  return (X, ends)

partial def searchKF (extra : List Nat) (S : Spot) (G : Guard) (E : Env) (W : List Watch) (key : AS → Nat) (ops : Array (TaintRun.AM Unit)) (fin : AS → Bool)
    (X0 : SG) : SG × Array AS := Id.run do
  let mut X := (X0, #[])
  while true do
    match X.1.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := ({ X.1 with pending := X.1.pending.erase k }, X.2)
      X := runKF extra S G E W key ops fin X A
  return X

/-! ## The steps follow the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem u8_facts : ∀ n : Fin 256, (UInt8.ofNat n.val = ((UInt8.ofNat n.val &&& 0xFE) ||| (UInt8.ofNat n.val &&& 1))) ∧
    (UInt8.ofNat n.val &&& 1 = 0 ∨ UInt8.ofNat n.val &&& 1 = 1) ∧ (UInt8.ofNat n.val ||| 0 = UInt8.ofNat n.val) ∧ (UInt8.ofNat n.val &&& 0xFF = UInt8.ofNat n.val) := by
  decide +kernel

theorem u8f (y : UInt8) : y = ((y &&& 0xFE) ||| (y &&& 1)) ∧ (y &&& 1 = 0 ∨ y &&& 1 = 1) ∧ (y ||| 0 = y) ∧ (y &&& 0xFF = y) := by
  have h := u8_facts ⟨y.toNat, y.toNat_lt⟩
  simpa using h

/-- the pieces of `Y` cover the machine -/
theorem cov_yPieces (R : Rd1) {A : AS} {m : Machine} (hs : Sim E F A m) : ∃ B ∈ yPieces R A, Sim E F B m ∧ B.k = A.k := by
  unfold yPieces
  by_cases h : (A.pc == R.adc && !A.y.isK && A.y.k == 0xFE) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    have hy : m.y &&& 0xFE = A.y.v &&& 0xFE := by
      have h1 : m.y &&& A.y.k = A.y.v &&& A.y.k := hs.y
      rw [h.2] at h1
      exact h1
    obtain ⟨e1, e2, _, _⟩ := u8f m.y
    rcases e2 with e2 | e2
    · refine ⟨_, List.mem_cons_self, { hs with y := ?_ }, rfl⟩
      show m.y &&& 0xFF = (A.y.v &&& 0xFE) &&& 0xFF
      rw [(u8f m.y).2.2.2, (u8f (A.y.v &&& 0xFE)).2.2.2]
      calc m.y = (m.y &&& 0xFE) ||| (m.y &&& 1) := e1
        _ = (A.y.v &&& 0xFE) ||| 0 := by rw [hy, e2]
        _ = A.y.v &&& 0xFE := (u8f _).2.2.1
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, { hs with y := ?_ }, rfl⟩
      show m.y &&& 0xFF = ((A.y.v &&& 0xFE) ||| 1) &&& 0xFF
      rw [(u8f m.y).2.2.2, (u8f ((A.y.v &&& 0xFE) ||| 1)).2.2.2]
      calc m.y = (m.y &&& 0xFE) ||| (m.y &&& 1) := e1
        _ = (A.y.v &&& 0xFE) ||| 1 := by rw [hy, e2]
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- the pieces before a step cover the machine -/
theorem cov_preF (R : Rd1) {S : Spot} {G : Guard} {A : AS} {m : Machine} (hc : CleanK G S.store m) (hs : Sim E F A m) :
    ∃ B ∈ preF R S G A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨D, hD, h3, h4⟩ := cov_yPieces R h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, by rw [h4, h2]⟩

theorem rd16zp_val {n : Machine} (ht : n.trk = false) (z : UInt8) : go (rd16zp z) n = (FrameModel.ptrAt n z, n) := by
  show go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) n = _
  rw [PipeTransitionAll.go_bind, FrameModel.rd_ram (FrameModel.zp_lt z) ht]
  simp only
  rw [PipeTransitionAll.go_bind, FrameModel.rd_ram (FrameModel.zp_lt (z + 1)) ht]
  rfl

/-- **The address of `LDA (zp),Y`**: the pointer at the operand, plus `Y` -/
theorem readAddr_eq {m : Machine} (ht : m.trk = false) (hp : 0x8000 ≤ m.pc + 1) :
    ScreenPage.readAddr m = FrameModel.ptrAt m (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat) + m.y.toUInt16 := by
  unfold ScreenPage.readAddr
  have key : go mIzyR { m with pc := m.pc + 1 } =
      go (pagePenalty (FrameModel.ptrAt m (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat))
        (FrameModel.ptrAt m (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat) + m.y.toUInt16) >>= fun _ =>
          pure (FrameModel.ptrAt m (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat) + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 } := by
    show go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun n => pagePenalty b (b + n.y.toUInt16) >>= fun _ => pure (b + n.y.toUInt16)) { m with pc := m.pc + 1 } = _
    rw [PipeTransitionAll.go_bind, TaintRun.fetch_rom hp]
    simp only
    rw [PipeTransitionAll.go_bind, rd16zp_val (n := { m with pc := m.pc + 1 + 1 }) ht]
    rfl
  rw [key, PipeTransitionAll.go_bind]
  unfold pagePenalty
  split <;> rfl

/-- **What the read needs of the machine**: at the read, with no NMI coming, the address is in the first block buffer and its byte is that of `m0` -/
def RdOK1 (R : Rd1) (m : Machine) : Prop :=
  m.pc = R.pc → m.nmiPending = false → ScreenPage.readAddr m < 0x2000 ∧ inBuf1 R (ScreenPage.readAddr m &&& 0x7FF).toNat = true ∧
    m.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat = R.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat

theorem mem_tilesAll {R : Rd1} {i : Nat} (h : inBuf1 R i = true) : R.ram.get! i ∈ tilesAll R := by
  unfold inBuf1 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold tilesAll
  refine List.mem_eraseDups.2 (List.mem_map.2 ⟨i - R.lo, List.mem_range.2 (by omega), ?_⟩)
  rw [show R.lo + (i - R.lo) = i by omega]

theorem canBe_of {x : AB} {c : UInt8} (h : x.mem c) : canBe x c = true := by
  unfold canBe
  have e : c &&& x.k = x.v &&& x.k := h
  simp [e]

/-- **The byte read is one of the tiles the walk allows** -/
theorem mem_tilesAt {R : Rd1} {A : AS} {m : Machine} (hs : Sim E F A m) (hp : 0x8000 ≤ m.pc + 1) (hr : ScreenPage.readAddr m < 0x2000)
    (hb : inBuf1 R (ScreenPage.readAddr m &&& 0x7FF).toNat = true) :
    R.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat ∈ tilesAt R (E.prg.get! ((A.pc + 1) &&& E.mask).toNat) A := by
  unfold tilesAt
  dsimp only
  generalize hz : E.prg.get! ((A.pc + 1) &&& E.mask).toNat = z
  have hz' : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = z := by rw [hs.prg, hs.mask, hs.pc, hz]
  have ha := readAddr_eq hs.trk hp
  rw [hz'] at ha
  split
  · rename_i hk
    simp only [Bool.and_eq_true] at hk
    obtain ⟨hy, hh⟩ := hk
    have ey : m.y = A.y.v := PipeEntryRule.known_eq hy hs.y
    have eh : m.ram.get! ((z + 1).toUInt16 &&& 0x7FF).toNat = (A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat).v :=
      PipeEntryRule.known_eq hh (hs.ram _ (PipeTransitionAll.mask_lt _))
    have hl := hs.ram _ (PipeTransitionAll.mask_lt z.toUInt16)
    generalize hlo : m.ram.get! (z.toUInt16 &&& 0x7FF).toNat = lo at hl
    have ea : ScreenPage.readAddr m = addrOf lo (A.getK ((z + 1).toUInt16 &&& 0x7FF).toNat).v A.y.v := by
      rw [ha, ← ey, ← eh, ← hlo]
      rfl
    refine List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨lo.toNat, List.mem_range.2 lo.toNat_lt, ?_⟩)
    rw [if_pos (by simpa using canBe_of hl)]
    simp only [UInt8.ofNat_toNat]
    rw [← ea, if_pos (by rw [hb]; simp [hr])]
  · exact mem_tilesAll hb

/-- **A step of the machine**, with the steps of this walk -/
theorem s_fstep {R : Rd1} {S : Spot} {G : Guard} {A : AS} {m : Machine} {ops : Array (TaintRun.AM Unit)} (hops : ops = (TaintRun.aRows E).toArray)
    (hT : 2 ≤ F.2.toNat) (hc : CleanK G S.store m) (hs : Sim E F A m) (hr : RdOK1 R m) :
    ∃ r ∈ fstep R S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold fstep
  by_cases h1 : (!A.nmi && A.pc == R.pc) = true
  · rw [if_pos h1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
    obtain ⟨hn, hpc⟩ := h1
    by_cases h2 : (decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && E.prg.get! (A.pc &&& E.mask).toNat == 0xB1) = true
    · rw [if_pos h2]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
      obtain ⟨⟨g1, g0⟩, g2⟩ := h2
      have hm : m.pc = R.pc := by rw [hs.pc]; exact hpc
      have hnm : m.nmiPending = false := by rw [hs.nmi]; exact hn
      obtain ⟨ha, hb, hv⟩ := hr hm hnm
      have hp1 : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact g0
      have ht := mem_tilesAt (R := R) hs hp1 ha hb
      have hval : ScreenPage.readVal m = R.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat := by
        rw [OpenMap.readVal_ram hs.trk ha, hv]
      refine ⟨_, List.mem_map.2 ⟨_, ht, rfl⟩, fun B hB => ?_⟩
      exact ScreenPage.s_readStep hs hn g1 g2 (Or.inl ha) (by rw [hval]; exact TaintRun.mem_known_self _) hB
    · rw [if_neg h2]
      exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  · rw [if_neg h1]
    split
    · dsimp only
      split
      · exact FrameKeep.s_kstep hops hT hc hs
      · exact TaintRun.s_succs hops hT hs
    · exact FrameKeep.s_kstep hops hT hc hs

end

/-! ## The walk with a stop covers the frame up to the stop -/

section
variable {R : Rd1} {C : CfgK} {Q : UInt16} {after : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

def LiveQ (R : Rd1) (C : CfgK) (Q : UInt16) (after : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkQ R C Q after n A = true

theorem cover_liveQ (ht : C.t.all (walkQ R C Q after Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveQ R C Q after F D m ∧ D.k = B.k ∧ D.pc = B.pc := by
  unfold FrameKeep.coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    have hsD := TaintRun.sim_le hle hs
    exact ⟨D, ⟨hsD, Fu, hall⟩, (PipeWrites.le_k hle).symm, by rw [← hsD.pc, ← hs.pc]⟩
  · cases h2

theorem live_stepQ (ht : C.t.all (walkQ R C Q after Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveQ R C Q after F A m) (hh : CleanK C.G C.S.store m) (hr : RdOK1 R m) :
    (∃ A', LiveQ R C Q after F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ (go step m).2.pc ≠ Q ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = Q ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ ∃ B, after B = true ∧ B.k = A.k ∧ Sim C.E F B (go step m).2) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧
      Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkQ] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preF R hh hs
    obtain ⟨r, hr, hB⟩ := s_fstep hops hT hh hs1 hr
    simp only [walkQ, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        by_cases hq : B.pc = Q
        · rw [if_pos (by simp [hq])] at hw2
          exact Or.inr (Or.inl ⟨k2, by rw [h1.pc, hq], k3, B, hw2, k1, h1⟩)
        · rw [if_neg (by simp [hq])] at hw2
          left
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
          rcases hw2 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD, hk, hp⟩ := cover_liveQ ht hkl h1 h3
            exact ⟨D, hD, by rw [hk, k1], k2, by rw [h1.pc]; exact hq, k3⟩
          · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, by rw [h1.pc]; exact hq, k3⟩
      · right; right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.1.2, hw2.1.2, hw2.2, k1, h1⟩

/-- **From a machine inside the frame, to the stop or to the frame's end**: either the frame comes to `Q` after the instruction `k`, in its own frame, in a state
that `after` accepts, or it ends in a state with the watched bits, the start of a frame and `fin`. Each instruction meets `CleanK` of the guard and `RdOK1`. -/
theorem to_stop {Fu' : Nat} (ht : C.t.all (walkQ R C Q after Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (TaintRun.aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) {m : Machine} {i : UInt8} {k : Nat} {A : AS}
    (hw : walkQ R C Q after Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) (hr : ∀ j, (trace m i j).frame = m.frame → RdOK1 R (trace m i j)) :
    (∃ k', k ≤ k' ∧ (trace m i k').pc = Q ∧ (trace m i k').frame = m.frame ∧ m.fdot + 3 * k' ≤ (trace m i k').fdot ∧ ∃ B, after B = true ∧ Sim C.E F B (trace m i k')) ∨
    ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have key : ∀ d, (∃ A, LiveQ R C Q after F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      (∃ k', k ≤ k' ∧ (trace m i k').pc = Q ∧ (trace m i k').frame = m.frame ∧ m.fdot + 3 * k' ≤ (trace m i k').fdot ∧ ∃ B, after B = true ∧ Sim C.E F B (trace m i k')) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧
        Sim C.E F B (trace m i (k + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | h | ⟨h1, B, h2, h2', h2'', h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepQ ht hkl hops hT h1 (hcl (k + d)) (hr (k + d) h2) with ⟨A', a1, _, a3, _, a4⟩ | ⟨a1, a2, a3, B, b1, _, b3⟩ | ⟨a1, B, a2, a2', a2'', _, a3⟩
        · rw [← e] at a1 a3 a4
          exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · rw [← e] at a1 a2 a3 b3
          exact Or.inr (Or.inl ⟨k + (d + 1), by omega, a2, by rw [a1, h2], by omega, B, b1, b3⟩)
        · rw [← e] at a1 a3
          exact Or.inr (Or.inr ⟨by rw [a1, h2], B, a2, a2', a2'', a3⟩)
      · exact Or.inr (Or.inl h)
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr (Or.inr ⟨h1, B, h2, h2', h2'', h3⟩)
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3⟩ | h | ⟨_, B, h2, h2', h2'', h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact Or.inl h
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact Or.inr ⟨B, h2, h2', h2'', h3⟩

end

/-- **From a machine inside the frame to the frame's end**, by a walk of `FrameKeep`: as `CtrlKeep.after_end`, with the start of a frame and `fin` at the end -/
theorem after_endK {CA : CfgK} {Fu Fu' : Nat} {F : Nat × UInt8} (ht : CA.t.all (FrameKeep.walkK CA Fu) = true) (hkl : CA.kl = CA.t.map knownOf)
    (hops : CA.ops = (TaintRun.aRows CA.E).toArray) (hT : 2 ≤ F.2.toNat) {m : Machine} {i : UInt8} {k : Nat} {A : AS}
    (hw : FrameKeep.walkK CA Fu' A = true) (hs : Sim CA.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, CleanK CA.G CA.S.store (trace m i j)) :
    ∃ B, FrameKeep.watchOK CA.W B = true ∧ FrameKeep.endOK CA.G B = true ∧ CA.fin B = true ∧ Sim CA.E F B (frame m i) := by
  have key : ∀ d, (∃ A, FrameKeep.LiveK CA F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK CA.W B = true ∧ FrameKeep.endOK CA.G B = true ∧ CA.fin B = true ∧
        Sim CA.E F B (trace m i (k + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h2', h2'', h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases FrameKeep.live_stepK ht hkl hops hT h1 (hcl (k + d)) with ⟨A', a1, _, a3, a4⟩ | ⟨a1, B, a2, a2', a2'', _, a3⟩
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · exact Or.inr ⟨by rw [a1, h2], B, a2, a2', a2'', a3⟩
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr ⟨h1, B, h2, h2', h2'', h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, h2', h2'', h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h2', h2'', h3⟩

/-! ## The walk of a frame on the ground, from the player's routine -/

/-- a byte's RAM index -/
def I (a : UInt16) : Nat := (a &&& 0x7FF).toNat

/-- the routine that the block buffer routine calls for the buffer's address -/
def gbOf (sy : Syms) (m0 : Machine) : UInt16 :=
  (romByte m0 ((PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x20 64) + 1)).toUInt16 |||
    ((romByte m0 ((PipeEntryRule.findOp m0 sy.BlockBufferCollision 0x20 64) + 2)).toUInt16 <<< 8)

/-- the read of the block buffer routine, with the first buffer of `m0` -/
def rdOf (sy : Syms) (m0 : Machine) : Rd1 :=
  { pc := (OpenMap.rdOf sy m0).pc, lo := I sy.Block_Buffer_1, ram := m0.ram, adc := PipeEntryRule.findOp m0 (gbOf sy m0) 0x79 32 }

/-- the table's key: that of `FrameKeep` with the move routine's spot `S` (the index is in the key there), the player's state, the vertical bytes, the size, bit 7 of
the buttons; the index registers in the bounding box routine; `A`, `Y` and the temporaries in the collision code and in the routine of the buffer's address: no part of the
proof -/
def keyF (sy : Syms) (S : Spot) (G : Guard) (bb gb : UInt16) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := FrameKeep.keyK S G [] A
  let n := n * 65536 + num (A.getK (I sy.Player_State))
  let n := n * 65536 + num (A.getK (I sy.Player_Y_Position))
  let n := n * 65536 + num (A.getK (I sy.Player_Y_Speed))
  let n := ((n * 65536 + num (A.getK (I sy.Player_Y_HighPos))) * 65536 + num (A.getK (I sy.PlayerSize))) * 65536 + num (A.getK (I sy.Player_Y_MoveForce))
  let b7 := fun (b : AB) => (b.k &&& 0x80).toNat / 64 + (b.v &&& b.k &&& 0x80).toNat / 128
  let n := ((n * 4 + b7 (A.getK (I sy.SavedJoypadBits))) * 4 + b7 (A.getK (I sy.A_B_Buttons))) * 4 + b7 (A.getK (I sy.PreviousA_B_Buttons))
  let n := if decide (bb ≤ A.pc) && decide (A.pc < bb + 0x48) then (n * 65536 + num A.x) * 65536 + num A.y else n
  if OpenMap.inColl sy A.pc || (decide (gb ≤ A.pc) && decide (A.pc < gb + 0x20)) then
    OpenMap.tempsC.foldl (fun n i => n * 65536 + num (A.getK i)) ((n * 65536 + num A.a) * 65536 + num A.y) else n

/-- the bounding box routine, which the end of the move calls with the player's index: there the search keeps the index registers in its key -/
def bboxOf (sy : Syms) (m0 : Machine) : UInt16 :=
  let js := PipeEntryRule.findOp m0 (sy.PlayerSubs + 9) 0x20 32
  (romByte m0 (js + 1)).toUInt16 ||| ((romByte m0 (js + 2)).toUInt16 <<< 8)

/-- the return from the collision routine in the player's routine: there the walk on the ground stops -/
def collRet (sy : Syms) (m0 : Machine) : UInt16 :=
  PipeEntryRule.findOp m0 (PipeEntryRule.findOp m0 (sy.PlayerSubs + 9) 0x20 32 + 3) 0x20 8 + 3

/-- the bytes that the walk up to the return protects: those of `CtrlKeep.spareI`, the player's state and the jumpspring byte -/
def protQ (sy : Syms) (m0 : Machine) : List Nat := CtrlKeep.spareI sy m0 ++ [I sy.Player_State, I sy.JumpspringAnimCtrl]

/-- the guard up to the return -/
def guardQ (sy : Syms) (m0 : Machine) : Guard := CtrlKeep.guardP sy m0 (protQ sy m0)

/-- on the ground at the height `y`: the state 0, the height, its high byte 1, the vertical speed and its fraction 0 -/
def groundW (sy : Syms) (y : UInt8) : List Watch :=
  [(I sy.Player_State, 0xFF, 0), (I sy.Player_Y_Position, 0xFF, y), (I sy.Player_Y_HighPos, 0xFF, 1), (I sy.Player_Y_Speed, 0xFF, 0), (I sy.Player_Y_MoveForce, 0xFF, 0)]

/-- what is set at the cut on the ground: the area's bytes, the ground at `y`, the jumpspring byte 0, and the case of the input: `a` (A not pressed: bit 7 of the
joypad's bits 0) or not `a` (A held: bit 7 of the joypad's bits 1 and bit 7 of A of the frame before 1) -/
def valF (sy : Syms) (v y : UInt8) (a : Bool) : List Watch :=
  CtrlKeep.valA sy v ++ groundW sy y ++ [(I sy.JumpspringAnimCtrl, 0xFF, 0)] ++
    (if a then [(I sy.SavedJoypadBits, 0x80, 0)] else [(I sy.SavedJoypadBits, 0x80, 0x80), (I sy.PreviousA_B_Buttons, 0x80, 0x80)])

/-- what is watched at the frame's end: the pause bit 0 and the area's bytes -/
def watchF (sy : Syms) (m0 : Machine) (v : UInt8) : List Watch := CtrlKeep.watchA sy m0 v

/-- the frame's end: on the ground, or out of control (the routine, the task or the mode is known not to be that of control) -/
def finF (sy : Syms) (B : AS) : Bool :=
  let b := B.getK (I sy.Player_State)
  (b.isK && b.v == 0) || FrameKeep.excl (B.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode &&& 0x7FF).toNat) sy.GameModeValue.toUInt8

/-- the frame's end out of control: the routine, the task or the mode is known not to be that of control -/
def finX (sy : Syms) (B : AS) : Bool :=
  FrameKeep.excl (B.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore.toUInt8 ||
    FrameKeep.excl (B.getK (sy.OperMode &&& 0x7FF).toNat) sy.GameModeValue.toUInt8

/-- at the return of the collision routine: on the ground at the height of `m0` (the state 0, the height, its high byte 1, the vertical speed and its fraction 0) -/
def groundOK (sy : Syms) (m0 : Machine) (B : AS) : Bool := FrameKeep.watchOK (groundW sy (peek m0 sy.Player_Y_Position)) B

/-! ## The check on the ROM -/

/-- the states at the cut, for each case of the input -/
def startsF (sy : Syms) (m0 : Machine) (v y : UInt8) (cuts : List AS) : List AS :=
  cuts.flatMap fun B => [true, false].map fun a => CtrlKeep.toA (watchF sy m0 v) (valF sy v y a) B

/-- the search of the walk up to the return of the collision routine, from the states at the cut: its table and the states it reaches at the return. It keeps every
byte of the RAM. No part of the proof. -/
def searchB (sy : Syms) (m0 : Machine) (v : UInt8) : SG × Array AS :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let S := FrameKeep.spotOf sy m0
  let G := guardQ sy m0
  let key := keyF sy S G (bboxOf sy m0) (gbOf sy m0)
  let E := PipeEntryRule.envOf m0
  searchQ (rdOf sy m0) (OpenMap.inColl sy) OpenMap.tempsC (List.range 2048) S G E (collRet sy m0) key (TaintRun.aRows E).toArray (finX sy)
    ((startsF sy m0 v (peek m0 sy.Player_Y_Position) cuts).foldl (routeF (OpenMap.inColl sy) OpenMap.tempsC (List.range 2048) S G key) {})

/-- the walk up to the return, with the table of the search `X` -/
def cfgBOf (sy : Syms) (m0 : Machine) (v : UInt8) (X : SG × Array AS) : CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardQ sy m0
  let key := keyF sy S G (bboxOf sy m0) (gbOf sy m0)
  let E := PipeEntryRule.envOf m0
  let qB := FrameKeep.tableOfKW key X.1
  { E := E, ops := (TaintRun.aRows E).toArray, S := S, G := G, W := watchF sy m0 v, t := qB.1, kl := qB.1.map knownOf, idx := qB.2.1, cut := qB.2.2, key := key,
    fin := finX sy }

/-- the walk of `FrameKeep` after the return, with a table from a search from the states that `X` reaches there -/
def cfgCOf (sy : Syms) (m0 : Machine) (v : UInt8) (X : SG × Array AS) : CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardQ sy m0
  let W := watchF sy m0 v
  let E := PipeEntryRule.envOf m0
  let key2 := FrameKeep.keyK S G W
  let qC := FrameKeep.tableOfKW key2 (FrameKeep.searchKW S G E W key2 (TaintRun.aRows E).toArray (X.2.toList.foldl (FrameKeep.routeKW S G key2) {}))
  { E := E, ops := (TaintRun.aRows E).toArray, S := S, G := G, W := W, t := qC.1, kl := qC.1.map knownOf, idx := qC.2.1, cut := qC.2.2, key := key2, fin := finF sy }

/-- what the walk of the pause bit asks at the player's routine: for each case of the input, the walk up to the return (`CB`), which asks there that the walk after it
(`CC`) succeeds -/
@[irreducible] def hookF (sy : Syms) (m0 : Machine) (v : UInt8) (CB CC : CfgK) (B : AS) : Bool :=
  [true, false].all fun a =>
    walkQ (rdOf sy m0) CB (collRet sy m0) (fun B' => groundOK sy m0 B' && FrameKeep.walkK CC FrameKeep.fuelK B') FrameKeep.fuelK
      (CtrlKeep.toA (watchF sy m0 v) (valF sy v (peek m0 sy.Player_Y_Position) a) B)

/-- the walk of the pause bit of `CtrlKeep` up to the player's routine, with `hookF` there -/
def cfgPF (sy : Syms) (m0 : Machine) (v : UInt8) (CB CC : CfgK) : CtrlKeep.CfgR := { CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true) with after := hookF sy m0 v CB CC }

/-- the check with the walks `CB` and `CC` -/
def flatCheckWith (sy : Syms) (m0 : Machine) (v : UInt8) (CB CC : CfgK) : Bool :=
  CtrlKeep.ctrlCheck1 (cfgPF sy m0 v CB CC) &&
    CB.t.all (walkQ (rdOf sy m0) CB (collRet sy m0) (fun B => groundOK sy m0 B && FrameKeep.walkK CC FrameKeep.fuelK B) FrameKeep.fuelK) &&
    CC.t.all (FrameKeep.walkK CC FrameKeep.fuelK) &&
    CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (I sy.Player_Y_HighPos) false)

/-- **The check on the ROM**: the walk of the pause bit up to the player's routine, which asks there, for each case of the input, that the walk up to the return of the
collision routine succeeds (with the tiles of the first block buffer), which asks there that the walk of `FrameKeep` to the frame's end succeeds; and the walk of
`CtrlKeep` that follows the high byte of the height up to the player's routine -/
def flatCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let X := searchB sy m0 v
  flatCheckWith sy m0 v (cfgBOf sy m0 v X) (cfgCOf sy m0 v X)

/-! ## A frame on the ground -/

/-- **On the ground**: the height of `m0`, its high byte 1, the vertical speed and its fraction 0 -/
def GroundAt (sy : Syms) (m0 m : Machine) : Prop :=
  peek m sy.Player_Y_Position = peek m0 sy.Player_Y_Position ∧ peek m sy.Player_Y_HighPos = 1 ∧ peek m sy.Player_Y_Speed = 0 ∧ peek m sy.Player_Y_MoveForce = 0

instance (sy : Syms) (m0 m : Machine) : Decidable (GroundAt sy m0 m) := by unfold GroundAt; infer_instance

/-- the four vertical bytes of `GroundAt`: the height, its high byte, the vertical speed and its fraction -/
def vertA (sy : Syms) : List UInt16 := [sy.Player_Y_Position, sy.Player_Y_HighPos, sy.Player_Y_Speed, sy.Player_Y_MoveForce]

/-- **From the return of the collision routine to the frame's end the vertical bytes do not change**, on the frame from `m` with the input `i`: at every arrival at the
return after the first arrival at the player's routine, the four bytes of `vertA` are those of the frame's end -/
def AfterV (sy : Syms) (m0 m : Machine) (i : UInt8) : Prop :=
  ∀ k, CtrlKeep.arrAt sy m i ≤ k → (trace m i k).pc = collRet sy m0 → ∀ x ∈ vertA sy, peek (frame m i) x = peek (trace m i k) x

/-- `GroundAt` is read from the four bytes of `vertA` -/
theorem groundAt_congr {sy : Syms} {m0 m m' : Machine} (h : ∀ x ∈ vertA sy, peek m' x = peek m x) (hg : GroundAt sy m0 m) : GroundAt sy m0 m' := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h _ (by simp [vertA])]; exact g1
  · rw [h _ (by simp [vertA])]; exact g2
  · rw [h _ (by simp [vertA])]; exact g3
  · rw [h _ (by simp [vertA])]; exact g4

/-- the watched bytes of `groundW` give `GroundAt` and the state 0 -/
theorem groundAt_of {sy : Syms} {m0 m : Machine} (h : FrameKeep.Watched (groundW sy (peek m0 sy.Player_Y_Position)) m) :
    GroundAt sy m0 m ∧ peek m sy.Player_State = 0 := by
  have e : ∀ (a : UInt16) (c : UInt8), ((I a, (0xFF : UInt8), c) : Watch) ∈ groundW sy (peek m0 sy.Player_Y_Position) → peek m a = c := by
    intro a c hm
    have := h _ hm
    rw [FrameKeep.and_ff, FrameKeep.and_ff] at this
    exact this
  exact ⟨⟨e _ _ (by simp [groundW]), e _ _ (by simp [groundW]), e _ _ (by simp [groundW]), e _ _ (by simp [groundW])⟩, e _ _ (by simp [groundW])⟩

theorem finF_of_finX {sy : Syms} {B : AS} (h : finX sy B = true) : finF sy B = true := by
  unfold finF
  unfold finX at h
  dsimp only
  revert h
  generalize FrameKeep.excl (B.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl.toUInt8 = a
  generalize FrameKeep.excl (B.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore.toUInt8 = b
  generalize FrameKeep.excl (B.getK (sy.OperMode &&& 0x7FF).toNat) sy.GameModeValue.toUInt8 = c
  intro h
  cases a <;> cases b <;> cases c <;> simp_all

theorem flatCheck_parts {sy : Syms} {m0 : Machine} {v : UInt8} {CB CC : CfgK} (h : flatCheckWith sy m0 v CB CC = true) :
    CtrlKeep.ctrlCheck1 (cfgPF sy m0 v CB CC) = true ∧
    CB.t.all (walkQ (rdOf sy m0) CB (collRet sy m0) (fun B => groundOK sy m0 B && FrameKeep.walkK CC FrameKeep.fuelK B) FrameKeep.fuelK) = true ∧
    CC.t.all (FrameKeep.walkK CC FrameKeep.fuelK) = true ∧
    CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (I sy.Player_Y_HighPos) false) = true := by
  unfold flatCheckWith at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- the first arrival at the player's routine is unique -/
theorem first_eq {M : Machine} {i : UInt8} {pc : UInt16} {k k' : Nat} (h1 : (trace M i k).pc = pc) (h2 : ∀ j, j < k → (trace M i j).pc ≠ pc)
    (h3 : (trace M i k').pc = pc) (h4 : ∀ j, j < k' → (trace M i j).pc ≠ pc) : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact absurd h1 (h4 k h)
  · exact h
  · exact absurd h3 (h2 k' h)

/-- **The high byte of the height at the player's routine** is that of the frame's start: the walk of `CtrlKeep` that follows it -/
theorem high_at_cut {sy : Syms} {m0 : Machine} (hH : CtrlKeep.ctrlCheck1 (CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (I sy.Player_Y_HighPos) false) = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    {k : Nat} (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame) (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    peek (trace m i k) sy.Player_Y_HighPos = peek m sy.Player_Y_HighPos := by
  obtain ⟨B, hB, hs⟩ := CtrlKeep.at_cut (C := CtrlKeep.cfgOf sy m0 (CtrlKeep.cutTable sy m0 false) (I sy.Player_Y_HighPos) false) hH rfl rfl rfl
    (CtrlKeep.cfg_start _ _ false h0) hcl hk hf hfirst
  simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB
  have h1 := hs.rkv hB.1.1.1.1.1.1
  rw [if_neg (by simp [hB.1.1.1.1.1.2])] at h1
  exact h1

theorem and80_cases (x : UInt8) : x &&& 0x80 = 0 ∨ x &&& 0x80 = 0x80 := by
  have h : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = 0 ∨ UInt8.ofNat n.val &&& 0x80 = 0x80 := by decide +kernel
  have := h ⟨x.toNat, x.toNat_lt⟩
  simpa using this

/-- **A frame on the ground with no jump**: a frame in control that begins on the ground (the state 0, `GroundAt`, no jumpspring, the area's bytes `v`), ends
not paused, and whose player's routine reads no jump, ends on the ground or out of control. Each instruction meets `CleanK` of `FrameKeep.guardK` and of `guardQ` (the
state, the jumpspring byte and the bytes of `CtrlKeep.spareI` protected), and `RdOK1`. `hc`, `hF` are the checks on the ROM. -/
theorem flat_endW {sy : Syms} {m0 : Machine} {v : UInt8} {X : SG × Array AS} (hc : CtrlKeep.ctrlCheck sy m0 = true)
    (hF : flatCheckWith sy m0 v (cfgBOf sy m0 v X) (cfgCOf sy m0 v X) = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hcq : ∀ n, CleanK (guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hr : ∀ n, (trace m i n).frame = m.frame → RdOK1 (rdOf sy m0) (trace m i n))
    (hu : CtrlKeep.Unpaused sy m0 (frame m i)) (hv : CtrlKeep.AreaOK sy v m) (hg : peek m sy.Player_State = 0) (hG : GroundAt sy m0 m)
    (hj : peek m sy.JumpspringAnimCtrl = 0) (hjump : (FrameModel.readIn sy (trace m i (CtrlKeep.arrAt sy m i))).jump = false) (hA : AfterV sy m0 m i) :
    ∃ B, finF sy B = true ∧ Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (frame m i) ∧ (finX sy B = true ∨ GroundAt sy m0 (frame m i)) := by
  obtain ⟨hT1, hTB, hTC, hHP⟩ := flatCheck_parts hF
  obtain ⟨ha1, ha2, ha3⟩ := CtrlKeep.arrive_at hc h0 hcl hu
  generalize hk0 : CtrlKeep.arrAt sy m i = k₀ at ha1 ha2 ha3 hjump
  rcases CtrlKeep.cut_or_end2 (C := cfgPF sy m0 v (cfgBOf sy m0 v X) (cfgCOf sy m0 v X)) hT1 rfl rfl rfl
      (CtrlKeep.cfg_start (CtrlKeep.cutTable sy m0 true) (sy.Player_X_Speed &&& 0x7FF).toNat true h0) hcl with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk : k = k₀ := first_eq h1 h4 ha1 ha3
    subst hk
    have A := CtrlKeep.ctrl_keep hc h0 hcl h1 h2 h4
    have hkp : ∀ x ∈ CtrlKeep.keepA sy, peek (trace m i k) x = peek m x := A.keep
    have hst : peek (trace m i k) sy.Player_State = 0 := by rw [hkp _ (by simp [CtrlKeep.keepA])]; exact hg
    -- the case of the input, from the jump the routine reads
    have hcase : peek (trace m i k) sy.SavedJoypadBits &&& 0x80 = 0 ∨
        (peek (trace m i k) sy.SavedJoypadBits &&& 0x80 = 0x80 ∧ peek (trace m i k) sy.PreviousA_B_Buttons &&& 0x80 = 0x80) := by
      unfold FrameModel.readIn at hjump
      simp only [hst] at hjump
      rcases and80_cases (peek (trace m i k) sy.SavedJoypadBits) with e1 | e1
      · exact Or.inl e1
      · rcases and80_cases (peek (trace m i k) sy.PreviousA_B_Buttons) with e2 | e2
        · simp [e1, e2] at hjump
        · exact Or.inr ⟨e1, e2⟩
    have hw : hookF sy m0 v (cfgBOf sy m0 v X) (cfgCOf sy m0 v X) B = true := hB2
    unfold hookF at hw
    have hH := high_at_cut hHP h0 hcl h1 h2 h4
    -- the bits set at the cut hold on the machine there
    have wff : ∀ (x : UInt16) (c : UInt8), peek (trace m i k) x = c → (trace m i k).ram.get! (I x) &&& 0xFF = c &&& 0xFF := by
      intro x c h
      rw [FrameKeep.and_ff, FrameKeep.and_ff]
      exact h
    have hbase : ∀ w ∈ CtrlKeep.valA sy v ++ groundW sy (peek m0 sy.Player_Y_Position) ++ [(I sy.JumpspringAnimCtrl, (0xFF : UInt8), (0 : UInt8))],
        (trace m i k).ram.get! w.1 &&& w.2.1 = w.2.2 &&& w.2.1 := by
      intro w hw
      simp only [CtrlKeep.valA, groundW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ((hw | hw | hw) | hw | hw | hw | hw | hw) | hw <;> subst hw
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hv.1)
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hv.2.1)
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hv.2.2)
      · exact wff _ _ hst
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hG.1)
      · exact wff _ _ (hH.trans hG.2.1)
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hG.2.2.1)
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hG.2.2.2)
      · exact wff _ _ ((hkp _ (by simp [CtrlKeep.keepA])).trans hj)
    -- the walk up to the return, then the walk after it
    have run : ∀ a, walkQ (rdOf sy m0) (cfgBOf sy m0 v X) (collRet sy m0) (fun B' => groundOK sy m0 B' && FrameKeep.walkK (cfgCOf sy m0 v X) FrameKeep.fuelK B')
        FrameKeep.fuelK (CtrlKeep.toA (watchF sy m0 v) (valF sy v (peek m0 sy.Player_Y_Position) a) B) = true →
        FrameKeep.Watched (valF sy v (peek m0 sy.Player_Y_Position) a) (trace m i k) →
        ∃ B, finF sy B = true ∧ Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (frame m i) ∧ (finX sy B = true ∨ GroundAt sy m0 (frame m i)) := by
      intro a hwa hV
      have hsA := CtrlKeep.sim_toA (W := watchF sy m0 v) hs (CtrlKeep.watchA_lt v) hV
      rcases to_stop (C := cfgBOf sy m0 v X) hTB rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hwa hsA h2 h5 hcq hr with
        ⟨k', hkk, b1, b2, b3, B', b4, b5⟩ | ⟨B', _, _, b3, b4⟩
      · simp only [Bool.and_eq_true] at b4
        obtain ⟨B'', _, _, c3, c4⟩ := after_endK (CA := cfgCOf sy m0 v X) hTC rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) b4.2 b5 b2 b3 hcq
        have hQ := (groundAt_of (FrameKeep.watched_of b4.1 b5)).1
        exact ⟨B'', c3, c4, Or.inr (groundAt_congr (hA k' (by rw [hk0]; exact hkk) b1) hQ)⟩
      · exact ⟨B', finF_of_finX b3, b4, Or.inl b3⟩
    rcases hcase with hc1 | ⟨hc1, hc2⟩
    · refine run true (List.all_eq_true.1 hw true (by simp)) ?_
      intro w hwm
      unfold valF at hwm
      rcases List.mem_append.1 hwm with h | h
      · exact hbase w h
      · simp only [if_true, List.mem_singleton] at h
        subst h
        show (trace m i k).ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0 &&& 0x80
        exact hc1
    · refine run false (List.all_eq_true.1 hw false (by simp)) ?_
      intro w hwm
      unfold valF at hwm
      rcases List.mem_append.1 hwm with h | h
      · exact hbase w h
      · simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> subst h
        · show (trace m i k).ram.get! (I sy.SavedJoypadBits) &&& 0x80 = 0x80 &&& 0x80
          exact hc1
        · show (trace m i k).ram.get! (I sy.PreviousA_B_Buttons) &&& 0x80 = 0x80 &&& 0x80
          exact hc2
  · exact absurd ha1 (hno k₀ ha2)

/-- **A frame on the ground with no jump** (`flat_endW`), with the check on the ROM `flatCheck` -/
theorem flat_end {sy : Syms} {m0 : Machine} {v : UInt8} (hc : CtrlKeep.ctrlCheck sy m0 = true) (hF : flatCheck sy m0 v = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hcq : ∀ n, CleanK (guardQ sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hr : ∀ n, (trace m i n).frame = m.frame → RdOK1 (rdOf sy m0) (trace m i n))
    (hu : CtrlKeep.Unpaused sy m0 (frame m i)) (hv : CtrlKeep.AreaOK sy v m) (hg : peek m sy.Player_State = 0) (hG : GroundAt sy m0 m)
    (hj : peek m sy.JumpspringAnimCtrl = 0) (hjump : (FrameModel.readIn sy (trace m i (CtrlKeep.arrAt sy m i))).jump = false) (hA : AfterV sy m0 m i) :
    ∃ B, finF sy B = true ∧ Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (frame m i) ∧ (finX sy B = true ∨ GroundAt sy m0 (frame m i)) :=
  flat_endW (X := searchB sy m0 v) hc hF h0 hcl hcq hr hu hv hg hG hj hjump hA

/-! ## The conditions on one instruction, from those of the opening -/

/-- `CleanK` of `FrameKeep.guardF` and the stores of `OpenMap.MapOK` give `CleanK` of `guardQ` -/
theorem cleanQ_of {sy : Syms} {m0 m : Machine} {q : UInt16} (h : CleanK (FrameKeep.guardF sy m0) q m) (hm : OpenMap.MapOK sy m0 m) : CleanK (guardQ sy m0) q m := by
  refine ⟨fun t ht hq => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, fun hx => ?_⟩
    change (t &&& 0x7FF).toNat ∈ (CtrlKeep.spareI sy m0 ++ [I sy.Player_State, I sy.JumpspringAnimCtrl]) ++ (FrameKeep.guardK sy m0).prot at hx
    change (t &&& 0x7FF).toNat ∉ CtrlKeep.spareI sy m0 ++ (FrameKeep.guardK sy m0).prot at h2
    rcases List.mem_append.1 hx with h3 | h3
    · rcases List.mem_append.1 h3 with h4 | h4
      · exact h2 (List.mem_append_left _ h4)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with h4 | h4
        · exact hm.store t ht h1 (by rw [h4]; exact List.mem_cons_self)
        · exact hm.store t ht h1 (by rw [h4]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    · exact h2 (List.mem_append_right _ h3)
  · exact Or.inr h1

/-- **The read of the block buffer routine**: in the first buffer (`OpenMap.MapOK`), with the bytes of `m0` there (`hb`, from the walk of `OpenMap`: `OpenMap.map_reads`) -/
theorem rdOK1_of {sy : Syms} {m0 m : Machine} (hm : OpenMap.MapOK sy m0 m)
    (hb : m.pc = (OpenMap.rdOf sy m0).pc → m.nmiPending = false → ∀ p ∈ (OpenMap.rdOf sy m0).buf, m.ram.get! p.1 = p.2) : RdOK1 (rdOf sy m0) m := by
  intro hpc hn
  obtain ⟨h1, h2⟩ := hm.read hpc
  obtain ⟨j, hj, e⟩ := List.mem_map.1 h2
  have hj' := List.mem_range.1 hj
  refine ⟨h1, ?_, ?_⟩
  · unfold inBuf1
    rw [← e]
    simp only [rdOf, I, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · have hp : ((ScreenPage.readAddr m &&& 0x7FF).toNat, m0.ram.get! (ScreenPage.readAddr m &&& 0x7FF).toNat) ∈ (OpenMap.rdOf sy m0).buf :=
      List.mem_map.2 ⟨_, List.mem_append_left _ h2, rfl⟩
    exact hb hpc hn _ hp

end Smbrta.OpenFlat

