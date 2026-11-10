import Theorems.PoleEntryRule
import Theorems.SidePipe

/-!
# An entry into the side pipe, on real frames

`RoomJoin.RoomFields` had the hypotheses `entry`, `entry_mem`, `entered`, `entry_P`: the collision routine, run alone on a hand-written block buffer (`SidePipe.withPipe`), enters on a state of the domain of
`SidePipe.sideCheck`. Here the entry is defined on real machines: an instruction of the frame of `m` with the input `i` makes the routine byte the side pipe's (`Enters`). The theorem says that such a frame was
at or right of the left end of the mouth when the block buffer routine read the page for the side check (`entry_right_of_left`), and `mouth_of_pass` gives `P ≥ P₀` from that.

This is `PoleEntryRule` with other places: the side check is the same, the write is the one in the side pipe's part of it, the two tiles are those the routine enters by, the page is 0. The pieces of
a byte read are other ones, because the two tiles differ in more than one bit. The whole frame is not followed. What is assumed stays on the single frame: the instruction that writes the routine byte
is the collision routine's own, it comes at the end of one pass from the start of the side check (`PoleEntryRule.Pass`), and the block buffers hold the two tiles only in the pipe's column
(`PoleEntryRule.TilesOK`). What is proved is the pass (`no_write`). `PassR` is `Pass` without the tiles: `RoomMap.map_of_rows` proves the tiles on the frames of the room.
There is no game data in this file. Page: `1-1/c-7-3-SideEntryRule.md`.
-/

namespace Smbrta.SideEntryRule

open PipeTransition (frame)
open PipeTransitionAll (go)
open SideChangeBound
open TaintRun (AB mem_known_self mem_top)
open PipeEntryRule (trace frame_trace trace_stop nxt rt findOp findStore footStack envOf rowI sim_setK' known_eq row_of)
open PoleEntryRule (Spots onCol Start AtEntry px AtRead RowOK TilesOK ReadOK Pass HypAt ptrAt safe CfgP coverP SR routeP startAt sim_start fuelP)

/-! ## The entry -/

/-- the value of the side pipe's routine -/
def vs (sy : Syms) : UInt8 := sy.EngSidePipe.toUInt8

/-- the instruction `n` of the frame makes the routine byte the side pipe's -/
def WriteStep (sy : Syms) (m : Machine) (i : UInt8) (n : Nat) : Prop :=
  rt sy (trace m i n) ≠ vs sy ∧ rt sy (trace m i (n + 1)) = vs sy

/-- **An entry.** An instruction of the frame of `m` with the input `i` makes the routine byte the side pipe's. -/
def Enters (sy : Syms) (m : Machine) (i : UInt8) : Prop := ∃ n, WriteStep sy m i n

/-- a frame that ends with the side pipe's routine, from another routine -/
def EndsEntry (sy : Syms) (m : Machine) (i : UInt8) : Prop := rt sy m ≠ vs sy ∧ rt sy (frame m i) = vs sy

/-- such a frame has an instruction of the write -/
theorem writeStep_of_ends {sy : Syms} {m : Machine} {i : UInt8} (h : EndsEntry sy m i) : ∃ n, n < fuelPerFrame ∧ WriteStep sy m i n := by
  have h0 : rt sy (trace m i 0) ≠ vs sy := h.1
  have h1 : rt sy (trace m i fuelPerFrame) = vs sy := by rw [← frame_trace]; exact h.2
  have key : ∀ N, rt sy (trace m i N) = vs sy → ∃ n, n < N ∧ WriteStep sy m i n := by
    intro N
    induction N with
    | zero => exact fun hz => absurd hz h0
    | succ N ih =>
      intro hs
      by_cases hN : rt sy (trace m i N) = vs sy
      · obtain ⟨n, h2, h3⟩ := ih hN
        exact ⟨n, by omega, h3⟩
      · exact ⟨N, by omega, hN, hs⟩
  exact key _ h1

/-- so it is an entry -/
theorem enters_of_ends {sy : Syms} {m : Machine} {i : UInt8} (h : EndsEntry sy m i) : Enters sy m i := by
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

/-- the places, from the symbols; `s` is the stack pointer. The side check and the block buffer routine are those of `PoleEntryRule.spotsOf`. Here `ball` and `shaft` are the two tiles that the routine
enters the side pipe by: the side pipe's tile, and the operand of the first compare after `ContSChk`. `bits` is not used. The exits are the two returns, the jump to the climbing routine (the
instruction just before `ContSChk`), the coin's routine and the routine that stops him. -/
def spotsOf (sy : Syms) (m0 : Machine) (s : UInt8) : Spots :=
  let read := findOp m0 sy.BlockBufferCollision 0xB1 64
  let sum := findOp m0 sy.BlockBufferCollision 0x85 64
  let ads := [romByte m0 sy.BlockBufferAdderData, romByte m0 (sy.BlockBufferAdderData + 2)]
  let col := SidePipe.column sy
  { side := sy.DoPlayerSideCheck
    adc := sum - 2
    entry := sum + 2
    afterPage := sum + 4
    ora := findOp m0 (sum + 2) 0x05 16
    read
    write := findStore m0 sy.PlyrPipe sy.GameEngineSubroutine.toUInt8 64
    exits := [sy.ExSCH, sy.ExCSM, sy.ContSChk - 3, sy.ErACM, sy.ImpedePlayerMove]
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
    ball := sy.SidePipeTile.toUInt8
    shaft := romByte m0 (findOp m0 sy.ContSChk 0xC9 64 + 1)
    bits := []
    col := col.toUInt8
    dC := ((sy.Block_Buffer_1 + col.toUInt16) &&& 0x7FF).toNat
    bufLo := (sy.Block_Buffer_1 &&& 0x7FF).toNat
    rows := (sy.Block_Buffer_2 - sy.Block_Buffer_1).toNat / 16
    pg := 0
    left := SidePipe.xLo sy
    late := dotsPerFrame - 6000 }

/-- the places of the game -/
def spots (sy : Syms) (m0 : Machine) : Spots := spotsOf sy m0 (footStack sy m0)

/-! ## The pieces of a byte read -/

/-- the pieces of a byte that is neither tile: one known bit where the two tiles agree, set as neither has it; or two known bits where they differ, the first as the second tile has it and the next
one (in a cycle) as the first tile has it -/
def pieces (P : Spots) : List AB :=
  let d := P.ball ^^^ P.shaft
  let agree := bitList.filter fun b => d &&& b == 0
  let differ := bitList.filter fun b => d &&& b != 0
  agree.map (PipeEntryRule.neBit P.ball) ++ (List.range differ.length).map fun k =>
    let i := differ.getD k 0
    let j := differ.getD ((k + 1) % differ.length) 0
    ⟨(P.shaft &&& i) ||| (P.ball &&& j), i ||| j⟩

/-- every byte that is neither tile is in a piece -/
def piecesCover (P : Spots) : Bool :=
  (List.range 256).all fun n =>
    n.toUInt8 == P.ball || n.toUInt8 == P.shaft || (pieces P).any fun a => n.toUInt8 &&& a.k == a.v &&& a.k

/-! ## The walk -/

/-- the pieces before a step. At the addition: the horizontal position. At the read of the page: the page, left of the mouth. At the read of the block buffer: the row, and a piece of the byte read. -/
def preS (P : Spots) (A : AS) : List AS :=
  if A.pc == P.adc then
    if (A.getK P.xI).isK then [A] else (List.range 256).map fun n => A.setK P.xI (AB.known n.toUInt8)
  else if A.pc == P.entry && A.y.isK && P.idx.contains A.y.v && A.x.isK && A.x.v == 0 then
    ((List.range (P.pg + 1)).filter fun n => !(A.getK P.xI).isK || decide (256 * n + (A.getK P.xI).v.toNat < P.left)).map fun n =>
      A.setK P.pI (AB.known n.toUInt8)
  else if A.pc == P.read then
    if (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && safe P (ptrAt P A) (A.getK P.pI) then
      (List.range P.rows).flatMap fun r =>
        (pieces P).map fun a => ({ A with y := AB.known (16 * r).toUInt8 } : AS).setK (rowI (ptrAt P A) r) a
    else [A]
  else [A]

/-- from `A`, step by step until every path ends at an exit or in a state of the table. No path comes to the write. -/
def walkS (C : CfgP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preS C.P A).all fun A₁ => (succs C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      C.P.exits.contains B.pc ||
        (B.pc != C.P.write && ((C.cut.get! B.pc.toNat != 0 && coverP C B) || walkS C n B))

/-! ## Finding the table: a search, no part of the proof -/

partial def runS (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) (A0 : AS) : SR := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preS P cur).flatMap (succs E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := (rs.filterMap id).filter fun b => !P.exits.contains b.pc
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !(PoleEntryRule.cutsP P).contains b.pc && b.pc != P.write &&
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

partial def searchS (E : Env) (ops : Array (AM Unit)) (P : Spots) (X0 : SR) : SR := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      if n ≥ 2 || (PoleEntryRule.cutsP P).contains A.pc then X := { X with out := X.out.push A, seen := X.seen.insert key (A :: X.seen.getD key []) }
      X := runS E ops P X A
  return X

def searchOf (E : Env) (P : Spots) : SR :=
  let ops := (aRows E).toArray
  searchS E ops P ((P.ads.map (startAt P)).foldl (routeP P) {})

def cfgOf (E : Env) (P : Spots) : CfgP :=
  let X := searchOf E P
  let q := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := PoleEntryRule.keyP P A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops := (aRows E).toArray, P, t := X.out, idx := q.1, cut := q.2.1 }

/-- **The check.** The places are bytes of the RAM, the start is not the write, the left end is on the page, the pieces cover the bytes, and the walks succeed. -/
def walkCheck (E : Env) (P : Spots) : Bool :=
  let C := cfgOf E P
  decide (P.adI < 2048) && decide (P.xI < 2048) && decide (P.pI < 2048) &&
  P.side != P.write && decide (P.late < dotsPerFrame) && decide (P.left < 256 * (P.pg + 1)) && piecesCover P &&
  C.t.all (walkS C fuelP) && (P.ads.map (startAt P)).all (walkS C fuelP)

/-- the check on the ROM -/
def ruleCheck (sy : Syms) (m0 : Machine) : Bool := walkCheck (envOf m0) (spots sy m0)

/-! ## The pieces cover the machine -/

section
variable {E : Env} {F : Nat × UInt8} {P : Spots}

/-- a byte that is neither tile is in a piece -/
theorem tile_piece (hc : piecesCover P = true) {v : UInt8} (h1 : v ≠ P.ball) (h2 : v ≠ P.shaft) : ∃ a ∈ pieces P, a.mem v := by
  simp only [piecesCover, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hc
  have hv : v.toNat.toUInt8 = v := by simp
  rcases hc v.toNat (List.mem_range.2 v.toNat_lt) with (h | h) | ⟨a, ha, h⟩
  · rw [hv] at h
    exact absurd h h1
  · rw [hv] at h
    exact absurd h h2
  · rw [hv] at h
    exact ⟨a, ha, h⟩

/-- what the pieces need from the check -/
structure PreOK (P : Spots) : Prop where
  xI : P.xI < 2048
  pI : P.pI < 2048
  left : P.left < 256 * (P.pg + 1)
  cover : piecesCover P = true

/-- every machine that meets `HypAt` is in a piece -/
theorem cov_pre (hb : PreOK P) {A : AS} {m : Machine} (hs : Sim E F A m) (hh : HypAt P m) : ∃ B ∈ preS P A, Sim E F B m := by
  unfold preS
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
          obtain ⟨a, ha1, ha2⟩ := tile_piece hb.cover (fun he => key _ (Or.inl rfl) he) (fun he => key _ (Or.inr rfl) he)
          refine ⟨_, List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, List.mem_map.2 ⟨a, ha1, rfl⟩⟩, ?_⟩
          have hs2 : Sim E F ({ A with y := AB.known (16 * r).toUInt8 } : AS) m := { hs with y := by rw [hyr]; exact mem_known_self _ }
          exact sim_setK' hs2 ha2
        · rw [if_neg h4]
          exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      · rw [if_neg h2]
        exact ⟨A, List.mem_singleton.2 rfl, hs⟩

end

/-! ## The walk covers the machine -/

section
variable {C : CfgP} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveS (C : CfgP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkS C n A = true

theorem cover_liveS (ht : C.t.all (walkS C Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverP C B = true) : ∃ D, LiveS C F D m := by
  unfold coverP at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le h2 hs, Fu, hall⟩
  · cases h2

theorem live_stepS (ht : C.t.all (walkS C Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : PreOK C.P) {A : AS} {m : Machine} (hl : LiveS C F A m) (hh : HypAt C.P m) (hex : (go step m).2.pc ∉ C.P.exits) :
    (go step m).2.pc ≠ C.P.write ∧ ∃ A', LiveS C F A' (go step m).2 := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkS] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_pre hb hs hh
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs1
    simp only [walkS, List.all_eq_true] at hw
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
        · exact cover_liveS ht h1 h4
        · exact ⟨B, h1, n, h4⟩

end

/-! ## A pass that is left of the mouth does not come to the write -/

section
variable {E : Env} {P : Spots}

/-- what the check says -/
structure WalkOK (E : Env) (P : Spots) : Prop where
  pre : PreOK P
  ne : P.side ≠ P.write
  late : P.late < dotsPerFrame
  table : (cfgOf E P).t.all (walkS (cfgOf E P) fuelP) = true
  starts : ∀ e ∈ P.ads, walkS (cfgOf E P) fuelP (startAt P e) = true

theorem walkOK_of_check (h : walkCheck E P = true) : WalkOK E P := by
  simp only [walkCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨⟨h2, h3, h6, h7⟩, h4, h5, h8, h9⟩

/-- **A pass.** If the position at each read of the page is left of the mouth and each read of the block buffer is `ReadOK`, the machine does not come to the write. -/
theorem no_write (hc : walkCheck E P = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat} (hs : ∀ j, j < n → s (j + 1) = (go step (s j)).2)
    (h0 : Start P E (s 0)) (hh : ∀ j, j < n → HypAt P (s j)) (hex : ∀ j, j ≤ n → (s j).pc ∉ P.exits) : (s n).pc ≠ P.write := by
  have hC := walkOK_of_check hc
  obtain ⟨e, he, hsim⟩ := sim_start hC.late hE h0
  have live : ∀ j, j ≤ n → (j = 0 ∨ (s j).pc ≠ P.write) ∧ ∃ A, LiveS (cfgOf E P) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨Or.inl rfl, _, hsim, fuelP, hC.starts e he⟩
    | succ j ih =>
      intro hj
      obtain ⟨_, A, hA⟩ := ih (by omega)
      have e1 := hs j (by omega)
      have hx := hex (j + 1) hj
      rw [e1] at hx ⊢
      obtain ⟨h1, h2⟩ := live_stepS (C := cfgOf E P) hC.table rfl (show 2 ≤ (2 : UInt8).toNat by decide) hC.pre hA (hh j (by omega)) hx
      exact ⟨Or.inr h1, h2⟩
  rcases (live n (Nat.le_refl n)).1 with h1 | h1
  · subst h1
    rw [h0.pc]
    exact hC.ne
  · exact h1

end

/-! ## The frame -/

/-- **The entry on a real frame.** If the frame enters and the instruction that writes the routine byte ends a `Pass`, then in that pass, when the block buffer routine reads the page for the side check,
the position is at or right of the left end of the mouth. -/
theorem entry_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : ruleCheck sy m0 = true) (he : Enters sy m i)
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

/-- **At the mouth, from one frame.** `P₂` is the position when the block buffer routine reads the page for the side check, before the write, with the fraction `f ≥ 0`. A frame that enters, whose
instruction of the write ends a `Pass`, has `P₂` at or right of the mouth's left end. -/
theorem mouth_of_pass {sy : Syms} {m0 m : Machine} {i : UInt8} {P₂ : Int} (hc : ruleCheck sy m0 = true) (he : Enters sy m i)
    (hp : ∀ n, WriteStep sy m i n → Pass (spots sy m0) (envOf m0) (trace m i) n)
    (hpos : ∀ n j, WriteStep sy m i n → j < n → AtEntry (spots sy m0) (trace m i j) →
      ∃ f : Int, 0 ≤ f ∧ P₂ = 256 * (px (spots sy m0) (trace m i j) : Int) + f) :
    SidePipe.mouthP sy 0 ≤ P₂ := by
  obtain ⟨n, j, h0, h1, h2, h3⟩ := entry_right_of_left hc he hp
  obtain ⟨f, hf, h4⟩ := hpos n j h0 h1 h2
  rw [h4]
  have h5 : (spots sy m0).left = SidePipe.xLo sy := rfl
  rw [h5] at h3
  unfold SidePipe.mouthP
  omega

/-- `Pass` without the tiles: the reads of the pass meet `RowOK`. The tiles (`TilesOK`) are given apart: `RoomMap.map_of_rows` proves them on the frames in the room. -/
def PassR (P : Spots) (E : Env) (tr : Nat → Machine) (n : Nat) : Prop :=
  (tr n).pc = P.write ∧ ∃ n₀, n₀ ≤ n ∧ Start P E (tr n₀) ∧ (∀ j, n₀ ≤ j → j ≤ n → (tr j).pc ∉ P.exits) ∧
    (∀ j, n₀ ≤ j → j < n → AtRead P (tr j) → RowOK P (tr j))

/-- `PassR` and the tiles at the reads before the write give `Pass` -/
theorem pass_of {P : Spots} {E : Env} {tr : Nat → Machine} {n : Nat} (h : PassR P E tr n) (ht : ∀ j, j < n → AtRead P (tr j) → TilesOK P (tr j)) :
    Pass P E tr n := by
  obtain ⟨h1, n₀, h2, h3, h4, h5⟩ := h
  exact ⟨h1, n₀, h2, h3, h4, fun j a b c => ⟨h5 j a b c, ht j b c⟩⟩

/-! ## On real frames: a program, no part of the proof -/

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
  /-- frames that enter; of them: not by the write; not at the end of a pass; left of the mouth; at no read of the page in the pass; the position at the read of the page is not the position
  at the end of the frame -/
  entries : Nat := 0
  writeBad : Nat := 0
  passBad : Nat := 0
  leftBad : Nat := 0
  noEntry : Nat := 0
  posBad : Nat := 0
  /-- frames that end with the side pipe's routine and do not enter by an instruction, or enter and do not end with it -/
  endBad : Nat := 0
  /-- positions in pixels and heights of the entries -/
  pxs : List Nat := []
  ys : List Nat := []
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, passes {r.passes} (not Start: {r.startBad}), reads {r.reads} (not RowOK: {r.rowBad}, not TilesOK: {r.tilesBad}), entries {r.entries} (not the write: {r.writeBad}, not a pass: {r.passBad}, left of the mouth: {r.leftBad}, no read of the page: {r.noEntry}, pos: {r.posBad}, end: {r.endBad}), positions {r.pxs.eraseDups.mergeSort}, heights {r.ys.eraseDups.mergeSort}"

/-- the count of bad cases -/
def Report.bad (r : Report) : Nat := r.startBad + r.rowBad + r.tilesBad + r.writeBad + r.passBad + r.leftBad + r.noEntry + r.posBad + r.endBad

/-- one real frame with the bits `pad` of the controller -/
def scanFrame (sy : Syms) (P : Spots) (E : Env) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let mut r := { r0 with frames := r0.frames + 1 }
  let mut inPass := false
  let mut passOK := true
  let mut lastPx : Option Nat := none
  let mut pxs : List Nat := []
  let mut entered := false
  let mut n := 0
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    if c.pc == P.side then
      let ok := PoleEntryRule.startOK P E c
      let ctl := rt sy c == sy.Eng_PlayerCtrl.toUInt8
      r := { r with passes := r.passes + (if ctl then 1 else 0), startBad := r.startBad + (if ok || !ctl then 0 else 1) }
      inPass := ok
      passOK := ok
      lastPx := none
      pxs := []
    if P.exits.contains c.pc then inPass := false
    if c.pc == P.entry && P.idx.contains c.y && c.x == 0 then
      let q := 256 * (c.ram.get! P.pI).toNat + (c.ram.get! P.xI).toNat
      if inPass then
        lastPx := some q
        pxs := q :: pxs
    if inPass && c.pc == P.read then
      let a := PoleEntryRule.rowOK P c
      let b := PoleEntryRule.tilesOK P c
      r := { r with reads := r.reads + 1, rowBad := r.rowBad + (if a then 0 else 1), tilesBad := r.tilesBad + (if b then 0 else 1) }
      if !(a && b) then passOK := false
    let before := rt sy c
    let pc := c.pc
    c := (go step c).2
    if before != vs sy && rt sy c == vs sy then
      entered := true
      r := { r with entries := r.entries + 1, writeBad := r.writeBad + (if pc == P.write then 0 else 1),
                    passBad := r.passBad + (if inPass && passOK then 0 else 1),
                    ys := (peek c sy.Player_Y_Position).toNat :: r.ys }
      match lastPx with
      | some q =>
        r := { r with leftBad := r.leftBad + (if q < P.left then 1 else 0), pxs := q :: r.pxs }
      | none => r := { r with noEntry := r.noEntry + 1 }
    n := n + 1
  -- `pos`: every read of the page in the entering pass is the frame's end position, without its fraction
  if entered then
    let pe := posP sy c
    for q in pxs do
      unless decide (256 * (q : Int) ≤ pe) && decide (pe < 256 * (q : Int) + 256) do r := { r with posBad := r.posBad + 1 }
  let ends := rt sy m != vs sy && rt sy c == vs sy
  if ends != entered then r := { r with endBad := r.endBad + 1 }
  return (r, c)

end Smbrta.SideEntryRule
