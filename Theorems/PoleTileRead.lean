import Theorems.PoleTileWalk

/-!
# The pole's tiles at the touch: the reads of the side check near the pole are in the block buffers

`PoleTileWalk` proves `TileRead` on the touch's frame from the map at the frame's start, `BufAt` on each store, and `ReadPre` at each read of the side check: the read is
in the RAM, in the block buffers, and a pole's tile in the pole's column is read only with the page at most one before the pole's.

Here the walk of the touch's frame is run once more, with two more splits and one more test (`walkU`):
* at the start of the side check, when the page may be the pole's or the one before (`nearP`): the height, in pieces below the bound of the collision routine's own
  check (`yPieces`), cut where the side check's compares of the height cut;
* at the addition of the height's adder in the block buffer routine, in a side check near the pole: the accumulator, bit by bit (`fullA`). So the sum and the row are
  known;
* on a step from a piece at the read to a state right after it that knows the offset to be the side check's, near the pole: at the read the pointer and `Y` are known,
  and the read is in the RAM and in the block buffers (`readP`).

`TileRead` is now proved only where the walk uses it (`TR`: right after the read, on a piece that knows the offset), with `PoleFrame`'s lemmas of the pieces taken again
with `TR` (`cov_zoneTW`, `cov_preTW`). A state right after the read is not covered by a state of the table, so the live state there is the step's own.

So `ReadPre` is no longer assumed. What is assumed in its place:
* `YSide`: at the start of the side check the height is below the bound of the collision routine's check (one state);
* `TileFar`: right after a read of the side check, with the page two or more before the pole's, the byte read is not one of the pole's tiles (one state).

There is no game data in this file. Page: `1-1/f-6-17-3-PoleTileRead.md`.
-/

namespace Smbrta.PoleTileRead

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px ptrAt)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt startG fuelG knownOf wTarget opAt)
open FrameKeep (CleanK)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTiles (Tile)
open PoleTileWalk (ColMap BufAt HypR inBufB okS pairOK readI)
open SideFrame (sideNow readF memB)

/-! ## The places and the pieces of the height -/

/-- the places: the height, the addition of its adder in the block buffer routine, the bound of the collision routine's check of the height, and the values where the
side check's compares of the height cut -/
structure RP where
  yI : Nat
  adcY : UInt16
  hiY : Nat
  cuts : List Nat
  deriving Inhabited

/-- the values `[lo, hi)` as pieces of known high bits -/
def blocks : Nat → Nat → Nat → List AB
  | 0, _, _ => []
  | f + 1, lo, hi =>
    if hi ≤ lo then [] else
    let e := ((List.range 9).reverse.find? fun e => lo % 2 ^ e == 0 && lo + 2 ^ e ≤ hi).getD 0
    ⟨lo.toUInt8, (256 - 2 ^ e : Nat).toUInt8⟩ :: blocks f (lo + 2 ^ e) hi

/-- the bound, up to a whole row of 16 pixels -/
def hiR (R : RP) : Nat := (R.hiY + 15) / 16 * 16

/-- the cut points below the bound, in order, from 0 to the bound up to a whole row -/
def cutList (R : RP) : List Nat :=
  (0 :: ((R.cuts.filter fun c => decide (0 < c) && decide (c < hiR R)).mergeSort (· ≤ ·)).eraseDups) ++ [hiR R]

/-- the pieces of the height below the bound (up to a whole row) -/
def yPieces (R : RP) : List AB :=
  let l := cutList R
  (l.zip l.tail).flatMap fun p => blocks 300 p.1 p.2

/-- every height below the bound is in a piece -/
def yCover (R : RP) : Bool := decide (R.hiY ≤ 256) && (List.range R.hiY).all fun n => (yPieces R).any fun a => memB a n.toUInt8

/-- the piece may hold a value of the byte -/
def meet (a p : AB) : Bool := (a.v ^^^ p.v) &&& a.k &&& p.k == 0

/-- the height, by the pieces that may hold it -/
def splitY (R : RP) (A : AS) : List AS := ((yPieces R).filter (meet (A.getK R.yI))).map fun p => A.setK R.yI p

/-- the accumulator, bit by bit -/
def fullA (A : AS) : List AS :=
  (PipeChangeEnd.bitA 128 A).flatMap fun A => (PipeChangeEnd.bitA 64 A).flatMap fun A => (PipeChangeEnd.bitA 32 A).flatMap fun A =>
    (PipeChangeEnd.bitA 16 A).flatMap fun A => (PipeChangeEnd.bitA 8 A).flatMap fun A => (PipeChangeEnd.bitA 4 A).flatMap fun A =>
      (PipeChangeEnd.bitA 2 A).flatMap (PipeChangeEnd.bitA 1)

/-- the new pieces: the height at the start of the side check, the accumulator at the addition of the height's adder, both near the pole -/
def zoneR (T : Pole) (R : RP) (A : AS) : List AS :=
  if A.pc == T.Q.side && nearP T.Q A then splitY R A
  else if A.pc == R.adcY && sideNow T.Q A && nearP T.Q A then fullA A
  else [A]

/-- all the pieces before a step: those of `PoleFrame`, then these -/
def preU (T : Pole) (R : RP) (A : AS) : List AS := (preT T A).flatMap (zoneR T R)

/-! ## The test at the read -/

/-- **The test at a read of the side check**, on a step from `A` to `B`: if `B` is right after the read and knows that the offset is one of the side check's, and the page
at the read may be the pole's or the one before, then at the read the pointer and `Y` are known, and the read is in the RAM and in the block buffers -/
def readP (Q : Spots) (A B : AS) : Bool :=
  B.pc != Q.read + 2 || !sideNow Q B || !nearP Q A ||
    ((A.getK Q.ptrI).isK && (A.getK (Q.ptrI + 1)).isK && A.y.isK && decide (ptrAt Q A + A.y.v.toUInt16 < 0x2000) && inBufB Q (readF Q A))

/-! ## The search: no part of the proof -/

/-- what the search forgets: as `PoleFrame.normT`; at the mask of the sum, the low 4 bits of the accumulator, which the mask clears; at the store of the horizontal sum
in a side check, the sum's low 4 bits and the position's piece, as `normT` does at the mask (the pointer needs only the sum's high 4 bits); at the load of the height in
the block buffer routine, what `normT` forgets at the mask of the sum (the pointer is known there, the sum no longer needed) -/
def normU (T : Pole) (A0 : AS) : AS :=
  let Q := T.Q
  let B := normT T A0
  if A0.pc == T.andAt then { B with a := ⟨B.a.v &&& 0xF0, B.a.k &&& 0xF0⟩ }
  else if A0.pc == Q.adc + 2 && PipeWrites.inZone T.G A0 && sideNow Q A0 then
    -- the store of the sum: only its high 4 bits make the pointer; keep it whole only in the pole's column on its page
    let onA := A0.a.isK && A0.a.v >>> 4 == Q.col && (A0.getK Q.pI).isK && (A0.getK Q.pI).v.toNat == Q.pg
    if onA then B else ({ B with a := ⟨B.a.v &&& 0xF0, B.a.k &&& 0xF0⟩ } : AS).setK Q.xI (pieceOfT Q (B.getK Q.xI) (B.getK Q.pI))
  else if A0.pc == T.G.loadY && PipeWrites.inZone T.G A0 then
    if onColSum Q B then B else (PipeEntryRule.forget [Q.sumI] B).setK Q.xI (pieceOfT Q (B.getK Q.xI) (B.getK Q.pI))
  else B

/-- the places where the search keeps a state -/
def isCutU (T : Pole) (pc : UInt16) : Bool := isCutT T pc || pc == T.G.loadY

def routeU (T : Pole) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := T.G
  let B := normU T B0
  let K := keyT T B
  let X := if isCutU T B.pc then { X with multi := X.multi.insert K () } else X
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

partial def runU (T : Pole) (R : RP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := T.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := preU T R cur
    for A₁ in ps do
      for r in kstepT T E ops A₁ do
        match r with
        | some B =>
          if !readP T.Q A₁ B || !pairOK T.Q A₁ B || !okS T E A₁ then
            X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A₁, failPcs := X.failPcs.insert (A₁.pc.toNat + 65536) (X.failPcs.getD (A₁.pc.toNat + 65536) 0 + 1) }
        | none => pure ()
    let rs := ps.flatMap (kstepT T E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutU T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeU T X b
    break
  return X

partial def searchU (T : Pole) (R : RP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runU T R E ops X A
  return X

def searchOfU (T : Pole) (R : RP) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchU T R E ops ([startG T.G false, startG T.G true].foldl (routeU T) {})

def cfgOfU (T : Pole) (R : RP) (E : Env) : CfgT :=
  let q := PipeWrites.tableOfS (searchOfU T R E)
  { E, ops := (aRows E).toArray, T, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-! ## The places from the symbols and the ROM -/

/-- the compares of the height after its loads from `a` on, within `n` bytes: `LDA zp` of the height, `CMP #c`, and a second `CMP #c` after a branch -/
def cmpsOf (m0 : Machine) (z : UInt8) (a : UInt16) : Nat → List Nat
  | 0 => []
  | n + 1 =>
    let here :=
      if romByte m0 a == 0xA5 && romByte m0 (a + 1) == z && romByte m0 (a + 2) == 0xC9 then
        [(romByte m0 (a + 3)).toNat] ++ (if romByte m0 (a + 6) == 0xC9 then [(romByte m0 (a + 7)).toNat] else [])
      else []
    here ++ cmpsOf m0 z (a + 1) n

/-- the collision routine's first load of the height (its check of the bottom of the screen) -/
def bandAt (sy : Syms) (m0 : Machine) : UInt16 := ScreenPage.findOpZ m0 sy.PlayerBGCollision 0xA5 sy.Player_Y_Position.toUInt8 64

def rpOf (sy : Syms) (m0 : Machine) : RP :=
  let G := FrameKeep.guardK sy m0
  { yI := G.yI
    adcY := G.loadY + 3
    hiY := (romByte m0 (bandAt sy m0 + 3)).toNat
    cuts := cmpsOf m0 sy.Player_Y_Position.toUInt8 sy.DoPlayerSideCheck 64 }

/-- what the search finds: no part of the proof -/
def searchReport (sy : Syms) (m0 : Machine) : String :=
  let T := poleOf sy m0
  let R := rpOf sy m0
  let E := PipeEntryRule.envOf m0
  let X := searchOfU T R E
  let fp := (X.failPcs.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 16
  let byPc := X.done.fold (fun (h : Std.HashMap Nat Nat) _ (A, _) => h.insert A.pc.toNat (h.getD A.pc.toNat 0 + 1)) {}
  let topPc := (byPc.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 12
  s!"the bound of the height {R.hiY}, the compares {R.cuts}, the pieces {(yPieces R).map fun a => (a.v, a.k)} (cover {yCover R}); one frame: {X.steps} steps, {X.forks} forks, {X.fails} failures {fp}, table {X.multi.size}, states {X.done.size}; states by place {topPc}"

/-! ## The conditions on one state -/

/-- **What is assumed of the start of the side check**: the height is below the bound of the collision routine's own check of it -/
def YSide (Q : Spots) (R : RP) (m : Machine) : Prop := m.pc = Q.side → (m.ram.get! R.yI).toNat < R.hiY

/-- **What is assumed right after a read of the side check far from the pole**: with the page two or more before the pole's, the byte read is not one of the pole's tiles -/
def TileFar (Q : Spots) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → ¬ (m.a = Q.ball ∨ m.a = Q.shaft)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_fullA : TaintRun.Cov E F fullA := by
  have c : ∀ b, b ∈ TaintRun.bitList → TaintRun.Cov E F (PipeChangeEnd.bitA b) := fun _ hb => PipeChangeEnd.cov_bitA hb
  exact PipeWrites.cov_then (c 128 (by decide)) (PipeWrites.cov_then (c 64 (by decide)) (PipeWrites.cov_then (c 32 (by decide))
    (PipeWrites.cov_then (c 16 (by decide)) (PipeWrites.cov_then (c 8 (by decide)) (PipeWrites.cov_then (c 4 (by decide))
      (PipeWrites.cov_then (c 2 (by decide)) (c 1 (by decide))))))))

theorem memB_mem {a : AB} {x : UInt8} (h : memB a x = true) : a.mem x := by
  unfold memB at h
  exact beq_iff_eq.1 h

/-- the pieces of the height cover a height below the bound -/
theorem cov_splitY {R : RP} (hc : yCover R = true) (hy : R.yI < 2048) {A : AS} {m : Machine} (hs : Sim E F A m) (hv : (m.ram.get! R.yI).toNat < R.hiY) :
    ∃ B ∈ splitY R A, Sim E F B m ∧ B.k = A.k := by
  simp only [yCover, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨_, hc⟩ := hc
  have h1 := hc _ hv
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.1 h1
  have hv' : (m.ram.get! R.yI).toNat.toUInt8 = m.ram.get! R.yI := by simp
  rw [hv'] at hm
  have hmem := memB_mem hm
  have hmeet : meet (A.getK R.yI) a = true := by
    have h0 := TaintRun.mem_iff.1 (hs.ram _ hy)
    have h8 := TaintRun.mem_iff.1 hmem
    unfold meet
    apply beq_iff_eq.2
    apply TaintRun.bt_ext
    intro i hi
    have e1 := h0 i hi
    have e2 := h8 i hi
    rw [TaintRun.bt_and, TaintRun.bt_and, TaintRun.bt_xor, TaintRun.bt_zero hi]
    cases h3 : TaintRun.bt (m.ram.get! R.yI) i <;> cases h4 : TaintRun.bt (A.getK R.yI).v i <;> cases h5 : TaintRun.bt (A.getK R.yI).k i <;>
      cases h6 : TaintRun.bt a.v i <;> cases h7 : TaintRun.bt a.k i <;> simp_all
  refine ⟨A.setK R.yI a, ?_, PipeEntryRule.sim_setK' hs hmem, rfl⟩
  exact List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, hmeet⟩, rfl⟩

/-- what the new pieces need from the check -/
structure ZoneR (T : Pole) (R : RP) : Prop where
  cover : yCover R = true
  yI : R.yI < 2048

theorem cov_zoneR {T : Pole} {R : RP} (hz : ZoneR T R) {A : AS} {m : Machine} (hs : Sim E F A m) (hy : YSide T.Q R m) :
    ∃ B ∈ zoneR T R A, Sim E F B m ∧ B.k = A.k := by
  unfold zoneR
  by_cases h1 : (A.pc == T.Q.side && nearP T.Q A) = true
  · rw [if_pos h1]
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact cov_splitY hz.cover hz.yI hs (hy (by rw [hs.pc]; exact h1.1))
  · rw [if_neg h1]
    by_cases h2 : (A.pc == R.adcY && sideNow T.Q A && nearP T.Q A) = true
    · rw [if_pos h2]
      exact cov_fullA A m hs
    · rw [if_neg h2]
      exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- the pieces of `FrameKeep.preK` keep the RAM, what is known of it, and the place -/
theorem preK_same {S : FrameKeep.Spot} {G : Guard} {A B : AS} (h : B ∈ FrameKeep.preK S G A) : B.ram = A.ram ∧ B.kn = A.kn ∧ B.pc = A.pc := by
  simp only [FrameKeep.preK, List.mem_flatMap] at h
  obtain ⟨B1, h1, h2⟩ := h
  have e1 : B1.ram = A.ram ∧ B1.kn = A.kn ∧ B1.pc = A.pc := by
    have ec : (PipeWrites.capT G A).ram = A.ram ∧ (PipeWrites.capT G A).kn = A.kn ∧ (PipeWrites.capT G A).pc = A.pc := by
      unfold PipeWrites.capT
      split <;> exact ⟨rfl, rfl, rfl⟩
    unfold PipeWrites.jumpP at h1
    split at h1
    · split at h1
      · split at h1
        · obtain ⟨i, _, rfl⟩ := List.mem_map.1 h1
          exact ec
        · rw [List.mem_singleton.1 h1]; exact ec
      · rw [List.mem_singleton.1 h1]; exact ec
    · rw [List.mem_singleton.1 h1]; exact ec
  unfold FrameKeep.splitX at h2
  split at h2
  · obtain ⟨x, _, rfl⟩ := List.mem_map.1 h2
    exact e1
  · rw [List.mem_singleton.1 h2]; exact e1

theorem sideNow_eq {Q : Spots} {A B : AS} (hr : B.ram = A.ram) (hk : B.kn = A.kn) : sideNow Q B = sideNow Q A := by
  unfold sideNow AS.getK
  rw [hr, hk]

/-- **What the walk asks of a state**: right after the read, if the piece knows that the offset is one of the side check's, then `TileRead` -/
def TR (Q : Spots) (A : AS) (m : Machine) : Prop := A.pc = Q.read + 2 → sideNow Q A = true → TileRead Q m

/-- `PoleFrame.cov_zoneT` with `TR` in place of `TileRead`: the split after the read uses it only on a piece that knows the offset -/
theorem cov_zoneTW {T : Pole} {A : AS} {m : Machine} (hb : ZoneOK T) (hh : HypR T m) (hT : TR T.Q A m) (hs : Sim E F A m) : ∃ B ∈ zoneT T A, Sim E F B m := by
  obtain ⟨hS, hA, hC⟩ := hh
  unfold zoneT
  by_cases h0 : T.G.cuts.contains A.pc = true
  · exfalso
    apply hC
    rw [hs.pc]
    exact List.mem_of_elem_eq_true h0
  rw [if_neg h0]
  by_cases h1 : (A.pc == T.G.subs || T.again.contains A.pc) = true
  · rw [if_pos h1]
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact cov_splitL hb.pre (hS (by rw [hs.pc]; exact h1)) hs
    · exact cov_splitL hb.pre (hA (by rw [hs.pc]; exact List.mem_of_elem_eq_true h1)) hs
  rw [if_neg h1]
  by_cases h1a : (A.pc == T.Q.adc && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h1a]
    obtain ⟨B, hB, h3, _⟩ := SideFrame.cov_fill hb.pre.xI A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h1a]
  by_cases h2 : (A.pc == T.andAt && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h2]
    obtain ⟨B, hB, h3, _⟩ := SideFrame.cov_highA A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h2]
  by_cases h3 : (A.pc == T.Q.read + 2 && sideNow T.Q A && offTile T.Q A) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨h4, h5⟩, h6⟩ := h3
    exact cov_tile hb.pre hb.ptr (by rw [hs.pc]; exact h4) h5 h6 (hT h4 h5) hs
  · rw [if_neg h3]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

/-- `PoleFrame.cov_preT` with `TR` -/
theorem cov_preTW {T : Pole} {A : AS} {m : Machine} (hb : ZoneOK T) (hc : CleanK T.G T.K.store m) (hh : HypR T m) (hT : TR T.Q A m) (hs : Sim E F A m) :
    ∃ B ∈ preT T A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨er, ek, ep⟩ := preK_same hB
  have hTB : TR T.Q B m := fun hp hn => hT (ep ▸ hp) (by rw [← sideNow_eq er ek]; exact hn)
  obtain ⟨D, hD, h3⟩ := cov_zoneTW hb hh hTB h1
  have h4 := FrameKeep.k_of_sim h1 h3
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

theorem cov_preU {T : Pole} {R : RP} {A : AS} {m : Machine} (hb : ZoneOK T) (hz : ZoneR T R) (hc : CleanK T.G T.K.store m) (hh : HypR T m) (hT : TR T.Q A m)
    (hy : YSide T.Q R m) (hs : Sim E F A m) : ∃ B ∈ preU T R A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := cov_preTW hb hc hh hT hs
  obtain ⟨D, hD, h3, h4⟩ := cov_zoneR hz h1 hy
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

end

/-! ## The walk -/

/-- a state of the table covers the state, by the key of `normU` -/
def coverU (C : CfgT) (B : AS) : Bool :=
  match C.idx[keyT C.T (normU C.T B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => PipeWrites.leK B D l
    | _, _ => false
  | none => false

/-- `PoleTileWalk.walkP` with the new pieces and the test at the read -/
def walkU (C : CfgT) (R : RP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preU C.T R A).all fun A₁ => okS C.T C.E A₁ && (kstepT C.T C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && pairOK C.T.Q A₁ B && readP C.T.Q A₁ B &&
      (B.k != A.k || (B.pc != C.T.Q.read + 2 && C.cut.get! B.pc.toNat != 0 && coverU C B) || walkU C R n B)

/-- **The check**: the checks of `PoleFrame.frameCheck` before its walk, the pieces of the height, the walk with the new pieces and the three tests, the facts at the
read -/
def frameCheckU (T : Pole) (R : RP) (E : Env) : Bool :=
  let C := cfgOfU T R E
  PoleTileWalk.frameBase T && yCover R && decide (R.yI < 2048) && C.t.all (walkU C R fuelG) && walkU C R fuelG (startG T.G false) &&
    walkU C R fuelG (startG T.G true) && PoleTileWalk.readOK T E

/-- what the check says -/
structure FrameOKU (T : Pole) (R : RP) (E : Env) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  zr : ZoneR T R
  table : (cfgOfU T R E).t.all (walkU (cfgOfU T R E) R fuelG) = true
  s0 : walkU (cfgOfU T R E) R fuelG (startG T.G false) = true
  s1 : walkU (cfgOfU T R E) R fuelG (startG T.G true) = true
  read : PoleTileWalk.ReadFacts T E

theorem frameOKU_of_check {T : Pole} {R : RP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (h : frameCheckU T R E = true) : FrameOKU T R E := by
  simp only [frameCheckU, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hB, hY⟩, hyI⟩, ht⟩, h0⟩, h1⟩, hr⟩ := h
  simp only [PoleTileWalk.frameBase, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, _⟩, _⟩, _⟩ := hB
  exact ⟨b1, ⟨⟨b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩, hp⟩, ⟨hY, hyI⟩, ht, h0, h1, PoleTileWalk.readFacts_of hr⟩

/-! ## One step -/

section
variable {C : CfgT} {R : RP} {Fu : Nat} {F : Nat × UInt8}

def LiveU (C : CfgT) (R : RP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkU C R n A = true

theorem cover_liveU (ht : C.t.all (walkU C R Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverU C B = true) : ∃ D, LiveU C R F D m := by
  unfold coverU at h
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

/-- one step of the machine from a live state: the piece before the step, the state after it, and the tests -/
theorem live_stepU (ht : C.t.all (walkU C R Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hz : ZoneR C.T R) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveU C R F A m) (hc : CleanK C.T.G C.T.K.store m)
    (hp : PosAt C.T.Q C.T.ps m) (hh : HypR C.T m) (hTR : TR C.T.Q A m) (hy : YSide C.T.Q R m) :
    ∃ A₁ B, Sim C.E F A₁ m ∧ okS C.T C.E A₁ = true ∧ Sim C.E F B (go step m).2 ∧ pairOK C.T.Q A₁ B = true ∧ readP C.T.Q A₁ B = true ∧
      (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧
      (F.1 < (go step m).2.frame ∨ ∃ A', LiveU C R F A' (go step m).2 ∧ (A'.pc = C.T.Q.read + 2 → A' = B)) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkU] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preU hb hz hc hh hTR hy hs
    obtain ⟨r, hr1, hB⟩ := s_kstepT hops hT hc hp hs1
    simp only [walkU, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨hok, hw1⟩ := hw1
    have hw2 := hw1 r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hw2
      obtain ⟨⟨⟨h2, hpair⟩, hrp⟩, h3⟩ := hw2
      refine ⟨A₁, B, hs1, hok, h1, hpair, hrp, PipeWrites.ne_of_okRt h2 (h1.ram _ hr), ?_⟩
      by_cases hk2 : B.k = 0
      · right
        rcases h3 with (h4 | ⟨⟨h5, _⟩, h4⟩) | h4
        · rw [hk, hk2] at h4
          exact absurd rfl h4
        · obtain ⟨D, hD⟩ := cover_liveU ht hkl h1 hk2 h4
          refine ⟨D, hD, fun hDp => absurd ?_ h5⟩
          rw [← h1.pc, hD.1.pc]
          exact hDp
        · exact ⟨B, ⟨h1, hk2, n, h4⟩, fun _ => rfl⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The read -/

/-- **`TileRead` right after a read**, for a piece `B` right after the read that knows the offset: the read before it is the `LDA (zp),Y` of the side check, with no NMI
pending (`pairOK`). With the page two or more before the pole's, the byte is not one of the pole's tiles (`TileFar`). Otherwise the walk knows the pointer and `Y` at the read
(`readP`), so the read is in the RAM, in the block buffers, and the map says that a pole's tile there is in the pole's column. -/
theorem tileRead_afterU {T : Pole} {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} (hb : ZoneOK T) (hR : PoleTileWalk.ReadFacts T E) (hs : Sim E F A₁ m)
    (hpair : pairOK T.Q A₁ B = true) (hrp : readP T.Q A₁ B = true) (hBpc : B.pc = T.Q.read + 2) (hsn : sideNow T.Q B = true)
    (hm : ColMap T.Q m) (hfar : TileFar T.Q (go step m).2) : TileRead T.Q (go step m).2 := by
  intro hpc hsv htile
  simp only [pairOK, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpair
  rcases hpair with h | ⟨h1, h2⟩
  · exact absurd hBpc h
  have hmpc : m.pc = T.Q.read := by rw [hs.pc]; exact h1
  have hnmi : m.nmiPending = false := by rw [hs.nmi]; exact h2
  have hhal : m.halted = false := hs.halted
  have hp0 : m.pc ≥ 0x8000 := by rw [hmpc]; exact hR.r0
  have hp1 : m.pc + 1 ≥ 0x8000 := by rw [hmpc]; exact hR.r1
  have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1 := by rw [hs.prg, hs.mask, hmpc]; exact hR.op
  obtain ⟨ha, hram⟩ := RoomBlocks.step_lda_izy hnmi hhal hp0 hop
  by_cases hf : ((go step m).2.ram.get! T.Q.pI).toNat + 1 < T.Q.pg
  · exact absurd htile (hfar hpc hsv hf)
  have hpg : T.Q.pg ≤ (m.ram.get! T.Q.pI).toNat + 1 := by rw [← hram]; omega
  have hnear : nearP T.Q A₁ = true := by
    unfold nearP
    have := TaintRun.le_maxv (hs.ram _ hb.pre.pI)
    apply decide_eq_true
    omega
  unfold readP at hrp
  rw [hBpc, hsn, hnear] at hrp
  simp only [bne_self_eq_false, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hrp
  obtain ⟨⟨⟨⟨k1, k2⟩, k3⟩, hadr⟩, hin⟩ := hrp
  have hptr := hb.ptr
  have e1 : m.ram.get! T.Q.ptrI = (A₁.getK T.Q.ptrI).v := PipeEntryRule.known_eq k1 (hs.ram _ (by omega))
  have e2 : m.ram.get! (T.Q.ptrI + 1) = (A₁.getK (T.Q.ptrI + 1)).v := PipeEntryRule.known_eq k2 (hs.ram _ hptr)
  have e3 : m.y = A₁.y.v := PipeEntryRule.known_eq k3 hs.y
  have hz : RoomBlocks.operand m = E.prg.get! ((T.Q.read + 1) &&& E.mask).toNat := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hmpc]
  have hadr' : ScreenPage.readAddr m = ptrAt T.Q A₁ + A₁.y.v.toUInt16 := by
    rw [RoomBlocks.readAddr_eq hp1]
    unfold RoomBlocks.ptrZ ptrAt
    rw [hz, hR.z1, hR.z2, e1, e2, e3]
  have hr0 : ScreenPage.readAddr m < 0x2000 := by rw [hadr']; exact hadr
  have hri : readI m = readF T.Q A₁ := by
    unfold readI readF
    rw [hadr']
  have hin' : T.Q.bufLo ≤ readI m ∧ readI m < T.Q.bufLo + T.Q.bufBytes := by
    rw [hri]
    simpa [inBufB] using hin
  have hy := PoleTileWalk.step_lda_izy_y hnmi hhal hp0 hp1 hop hr0
  have hat : readAt T.Q (go step m).2 = readI m :=
    PoleTileWalk.readAt_after hp1 (by rw [hz]; exact hR.z1) (by rw [hz]; exact hR.z2) hram hy
  have hval : (go step m).2.a = m.ram.get! (readI m) := by
    rw [ha, RoomBlocks.readVal_eq hr0]
    rfl
  have ht : Tile T.Q (m.ram.get! (readI m)) := by
    rw [← hval]
    exact htile
  have hcol := hm (readI m) hin'.1 hin'.2 ht
  refine ⟨by rw [hat]; exact hcol, ?_⟩
  rw [hram]
  exact hpg

/-! ## The frame -/

/-- **The frame.** From a `FrameStart` with the map `ColMap`, while each instruction is `CleanK`, meets `PosAt`, `HypR`, `BufAt`, `YSide` and `TileFar`, the routine byte
does not become the pole's. `TileRead` is proved at each step where the walk uses it (`TR`). -/
theorem no_write_frameU {T : Pole} {R : RP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (hc : frameCheckU T R E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hm0 : ColMap T.Q (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ YSide T.Q R (s j) ∧ TileFar T.Q (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOKU_of_check hp hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOfU T R E).kl = (cfgOfU T R E).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, LiveU (cfgOfU T R E) R ((s 0).frame, 2) A (s 0) ∧ TR T.Q A (s 0) := by
    have hT0 : ∀ A : AS, Sim E ((s 0).frame, 2) A (s 0) → TR T.Q A (s 0) := by
      intro A hA hpc
      rw [← hA.pc, h0.pc] at hpc
      exact absurd hpc hC.read.idle
    cases b with
    | false => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s0⟩, hT0 _ hsim⟩
    | true => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s1⟩, hT0 _ hsim⟩
  have live : ∀ j, j ≤ n → (∃ A, LiveU (cfgOfU T R E) R ((s 0).frame, 2) A (s j) ∧ TR T.Q A (s j)) ∧ ColMap T.Q (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA, hTA⟩, hmj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, hr1, hb1, hy1, _⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, _, hpair, hrp, _, h2⟩ :=
        live_stepU hC.table hkl rfl hT2 hC.zone hC.zr hC.rt hA hh1 hp1 hr1 hTA hy1
      have hfar : TileFar T.Q (go step (s j)).2 := by
        rw [← hs j (by omega)]
        exact (hh (j + 1) hj).2.2.2.2.2
      have hmj1 := PoleTileWalk.colMap_step hs1 hok hb1 hmj
      rw [← hs j (by omega)] at hmj1
      refine ⟨?_, hmj1⟩
      rcases h2 with h2 | ⟨A', hA', hAB⟩
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := by rw [hs j (by omega)]; exact h2
        omega
      · refine ⟨A', by rw [hs j (by omega)]; exact hA', fun hpc hsn => ?_⟩
        have e := hAB hpc
        subst e
        rw [hs j (by omega)]
        exact tileRead_afterU hC.zone hC.read hs1 hpair hrp hpc hsn hmj hfar
  obtain ⟨⟨A, hA, hTA⟩, _⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, hr1, _, hy1, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := live_stepU hC.table hkl rfl hT2 hC.zone hC.zr hC.rt hA hh1 hp1 hr1 hTA hy1
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-! ## The touch -/

/-- **The check on the ROM**: as `PoleTileWalk.poleCheckP`, with this walk in place of the walk of `PoleTileWalk` -/
def poleCheckU (sy : Syms) (m0 : Machine) : Bool :=
  ptrOK sy m0 && frameCheckU (poleOf sy m0) (rpOf sy m0) (PipeEntryRule.envOf m0) && SubsOnce.subsCheck sy m0 && PoleTileWalk.keepCheckOfS sy m0

theorem subs_of_U {sy : Syms} {m0 : Machine} (h : poleCheckU sy m0 = true) : SubsOnce.subsCheck sy m0 = true := by
  simp only [poleCheckU, Bool.and_eq_true] at h
  exact h.1.2

theorem keepS_of_U {sy : Syms} {m0 : Machine} (h : poleCheckU sy m0 = true) : PoleTileWalk.keepCheckOfS sy m0 = true := by
  simp only [poleCheckU, Bool.and_eq_true] at h
  exact h.2

/-- `YSide` with the places from the symbols and the ROM -/
abbrev YSideAt (sy : Syms) (m0 : Machine) (m : Machine) : Prop := YSide (spotsF sy m0) (rpOf sy m0) m

/-- **The touch on a real frame, at the end of the move**: as `PoleTileWalk.touch_right_of_leftP`, with `YSide` and `TileFar` in place of `ReadPre` -/
theorem touch_right_of_leftU {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleCheckU sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hys : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YSideAt sy m0 (trace m i j))
    (hfar : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileFar (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleCheckU, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frameU (T := poleOf sy m0) (R := rpOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw j hj)
      (fun j hj => frame_before hw j hj) (start_T (h0.pad _)) hm
      (fun j hj => ⟨cleanK_T (hk j), hpk n hw j hj, ⟨fun hs => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, fun ha => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd (hag n hw j hj ha hl) hx
        · exact Nat.lt_of_not_le hl, by
        show (trace m i j).pc ∉ ([] : List UInt16)
        simp⟩, hbuf n hw j hj, hys n hw j hj, hfar n hw j hj⟩)
    exact hn hw.2

/-- **In the pole's range, from one whole frame**: as `PoleTileWalk.inRange_of_frameP`, with `YSide` and `TileFar` in place of `ReadPre` -/
theorem inRange_of_frameU {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleCheckU sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hys : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YSideAt sy m0 (trace m i j))
    (hfar : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileFar (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftU hc he h0 hk hpk hm hbuf hys hfar hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleTileRead
