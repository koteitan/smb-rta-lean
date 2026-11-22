import Theorems.PoleTileHeight

/-!
# The pole's tiles at the touch: the reads far from the pole are in the block buffers

`PoleTileHeight` follows the touch's frame and proves `TileRead` at each read of the side check. Near the pole (the page is the pole's or the one before) the walk knows the
pointer and `Y` at the read, so the read is in the RAM and in the block buffers, and the map of the frame's start (`ColMap`) says where a pole's tile can be. Far from the pole
(the page two or more before the pole's) it does not know them, and it assumed `TileFar`: right after a read there, the byte read is not one of the pole's tiles.

Here the walk knows the read far from the pole too (`walkF`):
* right before the page's bit is moved into the carry, in a side check far from the pole: that bit (`PipeChangeEnd.bitA 1`); it chooses the block buffer, so the
  pointer's high byte and the high 4 bits of its low byte are known (the walk's addition of a byte with no low bits, `PipeWrites.aadcH`);
* the height at the collision routine's first load of it, at the start of the side check and the accumulator at the addition of the height's adder, as `PoleTileHeight`
  does near the pole, on every page;
* the test at the read (`readPF`): at every read of the side check `Y` is known, and every address that the pointer's known bits allow (`readMin` to `readMax`) is in
  the block buffers, which are in the RAM.

So at a read far from the pole the byte read is a byte of the block buffers. With the map (`ColMap`) a pole's tile there is in the pole's column. What is assumed in place of
`TileFar` is `TileCol`: right after a read of the side check with the page two or more before the pole's, **at the pole's column**, the byte read is not one of the pole's tiles.
The reads far from the pole in the other columns are no longer assumed.

There is no game data in this file. Page: `1-1/f-6-17-5-PoleTileFar.md`.
-/

namespace Smbrta.PoleTileFar

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px ptrAt)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt startG fuelG knownOf wTarget opAt)
open FrameKeep (CleanK)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTiles (Tile)
open PoleTileWalk (ColMap BufAt HypR inBufB okS pairOK readI)
open PoleTileRead (RP hiR yPieces fullA TR preK_same sideNow_eq)
open PoleTileHeight (HP GY YAt kstepH s_kstepH splitP coverN bandPieces cov_splitP ZoneH hpOf YKeep)
open SideFrame (sideNow readF memB fillB highA)

/-! ## The condition on one state -/

/-- **What is assumed right after a read of the side check far from the pole, at the pole's column**: with the page two or more before the pole's, if the read was in
the pole's column, the byte read is not one of the pole's tiles -/
def TileCol (Q : Spots) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → onCol Q (readAt Q m) = true → ¬ (m.a = Q.ball ∨ m.a = Q.shaft)

/-- `TileFar` gives `TileCol` -/
theorem tileCol_of_far {Q : Spots} {m : Machine} (h : PoleTileRead.TileFar Q m) : TileCol Q m := fun a b c _ => h a b c

/-- **What stays assumed of a read far from the pole at the pole's column** (round 29, the field `PoleJoin.Run.tilesCol`), with `c₀` the area parser's column
(16 a page) and `e₀` the screen's left edge in px, both at the frame's start: right after a read of the side check with the page two or more before the pole's, at
the pole's column, (`slot`) if the byte read is one of the pole's tiles, the parser's column had come to the pole's; (`near`) his pixel is at most 112 px left of
`e₀`; (`read`) the read is in the column of his pixel plus less than 16 px, counted mod 32. With the parser's invariant at the frame's start (`16·c₀ ≤ e₀ + 384`) it
gives `TileCol` (`tileCol_of_slot`): the parser is at most 24 columns past the edge, so it has not come to the pole's column while he reads 32
columns or more before it. Round 30 (`1-1/f-6-17-11-PoleWrap.md`): (`read`) is asked only when his page is exactly two before the pole's. Three pages or more
before it, his pixel is at least 513 px before the pole's page, and (`near`) alone puts the parser's column before the pole's (`tileCol_of_slot`). -/
def TileSlot (Q : Spots) (c₀ e₀ : Nat) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → onCol Q (readAt Q m) = true →
    ((m.a = Q.ball ∨ m.a = Q.shaft) → 16 * Q.pg + Q.col.toNat ≤ c₀) ∧
    e₀ ≤ (m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + 112 ∧
    ((m.ram.get! Q.pI).toNat + 2 = Q.pg →
      ∃ a, a < 16 ∧ ((m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + a) / 16 % 32 = (16 * Q.pg + Q.col.toNat) % 32)

/-- **The old `TileSlot`** (round 29), which asked (`read`) on every page two or more before the pole's: it gives the new one (round 30 asks less) -/
def TileSlotR (Q : Spots) (c₀ e₀ : Nat) (m : Machine) : Prop :=
  m.pc = Q.read + 2 → m.ram.get! Q.saveI ∈ Q.idx → (m.ram.get! Q.pI).toNat + 1 < Q.pg → onCol Q (readAt Q m) = true →
    ((m.a = Q.ball ∨ m.a = Q.shaft) → 16 * Q.pg + Q.col.toNat ≤ c₀) ∧
    e₀ ≤ (m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + 112 ∧
    ∃ a, a < 16 ∧ ((m.ram.get! Q.pI).toNat * 256 + (m.ram.get! Q.xI).toNat + a) / 16 % 32 = (16 * Q.pg + Q.col.toNat) % 32

/-- the round 29 condition gives the round 30 one -/
theorem tileSlot_of_R {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlotR Q c₀ e₀ m) : TileSlot Q c₀ e₀ m := by
  intro h1 h2 hpg hon
  obtain ⟨hs, hn, hr⟩ := h h1 h2 hpg hon
  exact ⟨hs, hn, fun _ => hr⟩

/-- **`TileCol` from `TileSlot`** and the parser's column at most 384 px past the edge: pure arithmetic. His page `p ≤ pg − 2`. If `p = pg − 2`, (`read`) puts
his pixel 32 columns or more before the pole's column: `pix ≤ 16·colPole − 497`. If `p ≤ pg − 3`, `pix ≤ 256·pg − 513` already. In both cases
`16·c₀ ≤ e₀ + 384 ≤ pix + 496 < 16·colPole`, so by (`slot`) the byte read is not a pole's tile. -/
theorem tileCol_of_slot {Q : Spots} {c₀ e₀ : Nat} {m : Machine} (h : TileSlot Q c₀ e₀ m) (hc : 16 * c₀ ≤ e₀ + 384) : TileCol Q m := by
  intro h1 h2 hpg hon ht
  obtain ⟨hs, hn, hr⟩ := h h1 h2 hpg hon
  have h3 := hs ht
  have hx : (m.ram.get! Q.xI).toNat < 256 := (m.ram.get! Q.xI).toNat_lt
  by_cases h2p : (m.ram.get! Q.pI).toNat + 2 = Q.pg
  · obtain ⟨a, ha, hm⟩ := hr h2p
    omega
  · omega

/-! ## The pieces -/

/-- right before the page's bit is moved into the carry: the instruction before the `ORA` of the sum -/
def parAt (Q : Spots) : UInt16 := Q.ora - 1

/-- the pieces before a step: those of `PoleFrame.zoneT`, and far from the pole, the page's bit before it goes into the carry -/
def zoneTF (T : Pole) (A : AS) : List AS :=
  if T.G.cuts.contains A.pc then []
  else if A.pc == T.G.subs || T.again.contains A.pc then splitL T.Q A
  else if A.pc == T.Q.adc && sideNow T.Q A && nearP T.Q A then fillB T.Q.xI A
  else if A.pc == parAt T.Q && sideNow T.Q A && !nearP T.Q A then PipeChangeEnd.bitA 1 A
  else if A.pc == T.andAt && sideNow T.Q A && nearP T.Q A then highA A
  else if A.pc == T.Q.read + 2 && sideNow T.Q A && offTile T.Q A then T.Q.bits.map fun b => { A with a := PipeEntryRule.neBit T.Q.ball b }
  else [A]

/-- the pieces of the height and of the accumulator, as `PoleTileHeight.zoneH`, on every page -/
def zoneHF (T : Pole) (H : HP) (A : AS) : List AS :=
  let R := H.R
  if A.pc == H.band then splitP R.yI (bandPieces R) A
  else if A.pc == T.Q.side then
    if decide ((A.getK R.yI).maxv.toNat < hiR R) then splitP R.yI (yPieces R) A else [A]
  else if A.pc == R.adcY && sideNow T.Q A then fullA A
  else if H.wk.contains A.pc && A.a.k &&& 0xF0 == 0xF0 && !A.a.isK then [{ A with a := AB.top }]
  else [A]

/-- all the pieces before a step -/
def preF (T : Pole) (H : HP) (A : AS) : List AS := ((FrameKeep.preK T.K T.G A).flatMap (zoneTF T)).flatMap (zoneHF T H)

/-- the least address of the read that the piece allows, from what it knows of the pointer's two bytes, with `Y` -/
def readMin (Q : Spots) (A : AS) : Nat := (A.getK Q.ptrI).minv.toNat + 256 * (A.getK (Q.ptrI + 1)).minv.toNat + A.y.v.toNat

/-- the largest address of the read that the piece allows -/
def readMax (Q : Spots) (A : AS) : Nat := (A.getK Q.ptrI).maxv.toNat + 256 * (A.getK (Q.ptrI + 1)).maxv.toNat + A.y.v.toNat

/-- **The test at a read of the side check**, on a step from `A` to `B`: if `B` is right after the read and knows that the offset is one of the side check's, then at
the read `Y` is known, and every address that the pointer's known bits allow is in the block buffers, which are in the RAM (on every page) -/
def readPF (Q : Spots) (A B : AS) : Bool :=
  B.pc != Q.read + 2 || !sideNow Q B ||
    (A.y.isK && decide (Q.bufLo + Q.bufBytes ≤ 2048) && decide (Q.bufLo ≤ readMin Q A) && decide (readMax Q A < Q.bufLo + Q.bufBytes))

section
variable {E : Env} {F : Nat × UInt8}

/-- `PoleTileRead.cov_zoneTW` with the far pieces -/
theorem cov_zoneTF {T : Pole} {A : AS} {m : Machine} (hb : ZoneOK T) (hh : HypR T m) (hT : TR T.Q A m) (hs : Sim E F A m) :
    ∃ B ∈ zoneTF T A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨hS, hA, hC⟩ := hh
  unfold zoneTF
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
    · obtain ⟨B, hB, h2⟩ := cov_splitL hb.pre (hS (by rw [hs.pc]; exact h1)) hs
      exact ⟨B, hB, h2, FrameKeep.k_of_sim hs h2⟩
    · obtain ⟨B, hB, h2⟩ := cov_splitL hb.pre (hA (by rw [hs.pc]; exact List.mem_of_elem_eq_true h1)) hs
      exact ⟨B, hB, h2, FrameKeep.k_of_sim hs h2⟩
  rw [if_neg h1]
  by_cases h1a : (A.pc == T.Q.adc && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h1a]
    exact SideFrame.cov_fill hb.pre.xI A m hs
  rw [if_neg h1a]
  by_cases h1c : (A.pc == parAt T.Q && sideNow T.Q A && !nearP T.Q A) = true
  · rw [if_pos h1c]
    exact PipeChangeEnd.cov_bitA (by decide) A m hs
  rw [if_neg h1c]
  by_cases h2 : (A.pc == T.andAt && sideNow T.Q A && nearP T.Q A) = true
  · rw [if_pos h2]
    exact SideFrame.cov_highA A m hs
  rw [if_neg h2]
  by_cases h3 : (A.pc == T.Q.read + 2 && sideNow T.Q A && offTile T.Q A) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨h4, h5⟩, h6⟩ := h3
    obtain ⟨B, hB, h7⟩ := cov_tile hb.pre hb.ptr (by rw [hs.pc]; exact h4) h5 h6 (hT h4 h5) hs
    exact ⟨B, hB, h7, FrameKeep.k_of_sim hs h7⟩
  · rw [if_neg h3]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- `PoleTileHeight.cov_zoneH` on every page -/
theorem cov_zoneHF {T : Pole} {H : HP} (hz : ZoneH H) {A : AS} {m : Machine} (hs : Sim E F A m) : ∃ B ∈ zoneHF T H A, Sim E F B m ∧ B.k = A.k := by
  unfold zoneHF
  by_cases h1 : (A.pc == H.band) = true
  · rw [if_pos h1]
    have hlt := (m.ram.get! H.R.yI).toNat_lt
    exact cov_splitP hz.band hz.yI hs (by omega)
  · rw [if_neg h1]
    by_cases h2 : (A.pc == T.Q.side) = true
    · rw [if_pos h2]
      by_cases h3 : decide ((A.getK H.R.yI).maxv.toNat < hiR H.R) = true
      · rw [if_pos h3]
        have h4 := TaintRun.le_maxv (hs.ram _ hz.yI)
        simp only [decide_eq_true_eq] at h3
        exact cov_splitP hz.side hz.yI hs (by omega)
      · rw [if_neg h3]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
    · rw [if_neg h2]
      by_cases h5 : (A.pc == H.R.adcY && sideNow T.Q A) = true
      · rw [if_pos h5]
        exact PoleTileRead.cov_fullA A m hs
      · rw [if_neg h5]
        by_cases h5a : (H.wk.contains A.pc && A.a.k &&& 0xF0 == 0xF0 && !A.a.isK) = true
        · rw [if_pos h5a]
          exact ⟨{ A with a := AB.top }, List.mem_singleton.2 rfl, { hs with a := TaintRun.mem_top _ }, rfl⟩
        rw [if_neg h5a]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

/-- every machine that meets the conditions is in a piece -/
theorem cov_preF {T : Pole} {H : HP} {A : AS} {m : Machine} (hb : ZoneOK T) (hz : ZoneH H) (hc : CleanK T.G T.K.store m) (hh : HypR T m) (hT : TR T.Q A m)
    (hs : Sim E F A m) : ∃ B ∈ preF T H A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨er, ek, ep⟩ := preK_same hB
  have hTB : TR T.Q B m := fun hp hn => hT (ep ▸ hp) (by rw [← sideNow_eq er ek]; exact hn)
  obtain ⟨D, hD, h3, h4⟩ := cov_zoneTF hb hh hTB h1
  obtain ⟨D', hD', h5, h6⟩ := cov_zoneHF (T := T) hz h3
  exact ⟨D', List.mem_flatMap.2 ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, hD'⟩, h5, h6.trans (h4.trans h2)⟩

end

/-! ## The search: no part of the proof -/

/-- what the search forgets: as `PoleTileHeight.normH`; at the start of the side check the height stays known on every page -/
def normF (T : Pole) (H : HP) (A0 : AS) : AS :=
  let B := PoleTileRead.normU T A0
  if A0.pc == T.Q.side && PipeWrites.inZone T.G A0 then B.setK H.R.yI (A0.getK H.R.yI) else B

/-- the places where the search keeps a state in the table: those of `PoleTileRead.isCutU` but the one right after the read, where the walk does not cover -/
def isCutF (T : Pole) (pc : UInt16) : Bool := PoleTileRead.isCutU T pc && pc != T.Q.read + 2

def routeF (T : Pole) (H : HP) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := T.G
  let B := normF T H B0
  let K := keyT T B
  let X := if isCutF T B.pc then { X with multi := X.multi.insert K () } else X
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

partial def runF (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := T.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := preF T H cur
    for A₁ in ps do
      for r in kstepH T H E ops A₁ do
        match r with
        | some B =>
          if !readPF T.Q A₁ B || !pairOK T.Q A₁ B || !okS T E A₁ then
            X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A₁, failPcs := X.failPcs.insert (A₁.pc.toNat + 65536) (X.failPcs.getD (A₁.pc.toNat + 65536) 0 + 1) }
        | none => pure ()
    let rs := ps.flatMap (kstepH T H E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    if cur.pc == T.Q.side && PipeWrites.inZone G cur && !decide ((cur.getK H.R.yI).maxv.toNat < hiR H.R) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert (cur.pc.toNat + 131072) (X.failPcs.getD (cur.pc.toNat + 131072) 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutF T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry && b.pc != H.band &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeF T H X b
    break
  return X

partial def searchF (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runF T H E ops X A
  return X

def searchOfF (T : Pole) (H : HP) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchF T H E ops ([startG T.G false, startG T.G true].foldl (routeF T H) {})

def cfgOfF (T : Pole) (H : HP) (E : Env) : CfgT :=
  let q := PipeWrites.tableOfS (searchOfF T H E)
  { E, ops := (aRows E).toArray, T, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- what the search finds: no part of the proof -/
def searchReport (sy : Syms) (m0 : Machine) : String :=
  let T := poleOf sy m0
  let H := hpOf sy m0
  let E := PipeEntryRule.envOf m0
  let X := searchOfF T H E
  let fp := (X.failPcs.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 16
  let byPc := X.done.fold (fun (h : Std.HashMap Nat Nat) _ (A, _) => h.insert A.pc.toNat (h.getD A.pc.toNat 0 + 1)) {}
  let topPc := (byPc.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 12
  s!"one frame: {X.steps} steps, {X.forks} forks, {X.fails} failures {fp}, table {X.multi.size}, states {X.done.size}; states by place {topPc}"

/-- the search with a bound on its rounds, for measuring: no part of the proof -/
partial def searchFB (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (budget : Nat) : PipeWrites.SG × Nat := Id.run do
  let mut X := X0
  let mut k := 0
  while k < budget do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runF T H E ops X A
      k := k + 1
  return (X, k)

/-- what a bounded search finds: no part of the proof -/
def searchReportB (sy : Syms) (m0 : Machine) (budget : Nat) : String :=
  let T := poleOf sy m0
  let H := hpOf sy m0
  let E := PipeEntryRule.envOf m0
  let ops := (aRows E).toArray
  let (X, k) := searchFB T H E ops ([startG T.G false, startG T.G true].foldl (routeF T H) {}) budget
  let fp := (X.failPcs.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 16
  let byPc := X.done.fold (fun (h : Std.HashMap Nat Nat) _ (A, _) => h.insert A.pc.toNat (h.getD A.pc.toNat 0 + 1)) {}
  let topPc := (byPc.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 24
  let near := X.done.fold (fun (n : Nat) _ (A, _) => if nearP T.Q A then n + 1 else n) 0
  s!"rounds {k}, pending {X.pending.size}: {X.steps} steps, {X.fails} failures {fp}, table {X.multi.size}, states {X.done.size} (near {near}); places: side {T.Q.side.toNat}, adc {T.Q.adc.toNat}, read {T.Q.read.toNat}, ora {T.Q.ora.toNat}, andAt {T.andAt.toNat}, loadY {T.G.loadY.toNat}, band {H.band.toNat}; states by place {topPc}"

/-- for measuring `yKeep` in the walk: at each piece inside the collision routine whose step is a store through an index or a pointer, whether the walk shows that the
store does not write the height (`StepWrites.keepOK` of the height's byte); no part of the proof -/
partial def runFY (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (Y0 : Std.HashMap Nat Nat) (A0 : AS) : PipeWrites.SG × Std.HashMap Nat Nat := Id.run do
  let G := T.G
  let mut X := X0
  let mut Y := Y0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := preF T H cur
    for A₁ in ps do
      let op := E.prg.get! (A₁.pc &&& E.mask).toNat
      if PipeWrites.inZone G A₁ && PoleTileWalk.idxOps.contains op && !StepWrites.keepOK E (fun i => i == H.R.yI) A₁ then
        let key := A₁.pc.toNat * 4 + (if A₁.x.isK then 1 else 0) + (if A₁.y.isK then 2 else 0)
        Y := Y.insert key (Y.getD key 0 + 1)
    let rs := ps.flatMap (kstepH T H E ops)
    X := { X with steps := X.steps + rs.length }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutF T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry && b.pc != H.band &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeF T H X b
    break
  return (X, Y)

partial def searchFY (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG × Std.HashMap Nat Nat := Id.run do
  let mut X := X0
  let mut Y : Std.HashMap Nat Nat := {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      let r := runFY T H E ops X Y A
      X := r.1
      Y := r.2
  return (X, Y)

/-- the stores inside the collision routine that the walk cannot keep off the height: (place, the index register known?), and how many pieces; no part of the proof -/
def yReport (sy : Syms) (m0 : Machine) : String :=
  let T := poleOf sy m0
  let H := hpOf sy m0
  let E := PipeEntryRule.envOf m0
  let ops := (aRows E).toArray
  let (X, Y) := searchFY T H E ops ([startG T.G false, startG T.G true].foldl (routeF T H) {})
  let l := (Y.toList.mergeSort (fun a b => a.1 ≤ b.1)).map fun (k, n) => (k / 4, k % 4, n)
  s!"steps {X.steps}; stores inside the collision routine that the walk does not keep off the height (place, 1: X known + 2: Y known, pieces): {l}"

/-- for measuring `bufAll` in the walk of the frames from control (`PoleTileWalk.walkKS`): the pieces whose step may write a byte of the block buffers, by place, with how many
know the index `X`, and how many may store one of the pole's tiles (the accumulator may be the ball or the shaft). These are the steps that `okSK` allows only as
stores through an index or a pointer, by `BufAt`; no part of the proof -/
partial def failsKS (C : FrameKeep.CfgK) (Q : Spots) (n : Nat) (A : AS) (acc : Std.HashMap Nat (Nat × Nat × Nat)) : Std.HashMap Nat (Nat × Nat × Nat) := Id.run do
  if n == 0 then return acc
  let mut acc := acc
  for A₁ in FrameKeep.preK C.S C.G A do
    if !StepWrites.keepOK C.E (PoleTileWalk.inBufB Q) A₁ then
      let key := A₁.pc.toNat
      let (c, xk, vt) := acc.getD key (0, 0, 0)
      let mayTile := memB A₁.a Q.ball || memB A₁.a Q.shaft
      acc := acc.insert key (c + 1, xk + (if A₁.x.isK then 1 else 0), vt + (if mayTile then 1 else 0))
    for r in FrameKeep.kstep C.S C.G C.E C.ops A₁ do
      match r with
      | none => pure ()
      | some B =>
        if B.k == A.k && !(C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) then
          acc := failsKS C Q (n - 1) B acc
  return acc

/-- the places where the walk of the frames cannot show that a step writes no pole's tile into the block buffers off the pole's column: (place, pieces, pieces that
know `X`, pieces that may store a pole's tile); no part of the proof -/
def bufReport (sy : Syms) (m0 : Machine) : String :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardK sy m0
  let E := PipeEntryRule.envOf m0
  let W := FrameKeep.watchOf sy
  let C := FrameKeep.cfgOfKW S G E W (FrameKeep.keyKC sy S G W) (FrameKeep.endCtl sy)
  let Q := spotsF sy m0
  let acc0 : Std.HashMap Nat (Nat × Nat × Nat) := {}
  let acc := C.t.foldl (fun acc A => failsKS C Q FrameKeep.fuelK A acc) acc0
  let acc := failsKS C Q FrameKeep.fuelK (FrameKeep.startK G W false) acc
  let acc := failsKS C Q FrameKeep.fuelK (FrameKeep.startK G W true) acc
  let l := (acc.toList.mergeSort (fun a b => a.1 ≤ b.1)).map fun (k, (c, xk, vt)) => (k, c, xk, vt)
  s!"table {C.t.size}; places {l.length}: {l}"

/-! ## The walk -/

/-- a state of the table covers the state, by the key of `normF` -/
def coverF (C : CfgT) (H : HP) (B : AS) : Bool :=
  match C.idx[keyT C.T (normF C.T H B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => PipeWrites.leK B D l
    | _, _ => false
  | none => false

/-- `PoleTileHeight.walkH` with the far pieces and the test at the read on every page -/
def walkF (C : CfgT) (H : HP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preF C.T H A).all fun A₁ => okS C.T C.E A₁ && (kstepH C.T H C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && pairOK C.T.Q A₁ B && readPF C.T.Q A₁ B &&
      (B.k != A.k || (B.pc != C.T.Q.read + 2 && C.cut.get! B.pc.toNat != 0 && coverF C H B) || walkF C H n B)

/-- **The check**: the checks of `PoleFrame.frameCheck` before its walk, the pieces of the height, the walk with the far pieces and the three tests, the facts at the
read -/
def frameCheckF (T : Pole) (H : HP) (E : Env) : Bool :=
  let C := cfgOfF T H E
  PoleTileWalk.frameBase T && coverN (bandPieces H.R) 256 && coverN (yPieces H.R) (hiR H.R) && decide (H.R.yI < 2048) && C.t.all (walkF C H fuelG) &&
    walkF C H fuelG (startG T.G false) && walkF C H fuelG (startG T.G true) && PoleTileWalk.readOK T E

/-- what the check says -/
structure FrameOKF (T : Pole) (H : HP) (E : Env) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  zh : ZoneH H
  table : (cfgOfF T H E).t.all (walkF (cfgOfF T H E) H fuelG) = true
  s0 : walkF (cfgOfF T H E) H fuelG (startG T.G false) = true
  s1 : walkF (cfgOfF T H E) H fuelG (startG T.G true) = true
  read : PoleTileWalk.ReadFacts T E

theorem frameOKF_of_check {T : Pole} {H : HP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (h : frameCheckF T H E = true) : FrameOKF T H E := by
  simp only [frameCheckF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, hY1⟩, hY2⟩, hyI⟩, ht⟩, h0⟩, h1⟩, hr⟩ := h
  simp only [PoleTileWalk.frameBase, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, _⟩, _⟩, _⟩ := hB
  exact ⟨b1, ⟨⟨b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩, hp⟩, ⟨hY1, hY2, hyI⟩, ht, h0, h1, PoleTileWalk.readFacts_of hr⟩

/-! ## One step -/

section
variable {C : CfgT} {H : HP} {Fu : Nat} {F : Nat × UInt8}

def LiveF (C : CfgT) (H : HP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkF C H n A = true

theorem cover_liveF (ht : C.t.all (walkF C H Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverF C H B = true) : ∃ D, LiveF C H F D m := by
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

/-- one step of the machine from a live state: the piece before the step, the state after it, and the tests -/
theorem live_stepF (ht : C.t.all (walkF C H Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hz : ZoneH H) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveF C H F A m) (hc : CleanK C.T.G C.T.K.store m)
    (hp : PosAt C.T.Q C.T.ps m) (hy : YAt C.T.G H.R.yI m) (hh : HypR C.T m) (hTR : TR C.T.Q A m) :
    ∃ A₁ B, Sim C.E F A₁ m ∧ okS C.T C.E A₁ = true ∧ Sim C.E F B (go step m).2 ∧ pairOK C.T.Q A₁ B = true ∧ readPF C.T.Q A₁ B = true ∧
      (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧
      (F.1 < (go step m).2.frame ∨ ∃ A', LiveF C H F A' (go step m).2 ∧ (A'.pc = C.T.Q.read + 2 → A' = B)) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkF] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preF hb hz hc hh hTR hs
    obtain ⟨r, hr1, hB⟩ := s_kstepH (H := H) hops hT hc hp hy hs1
    simp only [walkF, List.all_eq_true] at hw
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
        · obtain ⟨D, hD⟩ := cover_liveF ht hkl h1 hk2 h4
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
pending (`pairOK`). On every page the walk knows the pointer and `Y` at the read (`readPF`), so the read is in the RAM and in the block buffers, and the map says that a
pole's tile there is in the pole's column. With the page two or more before the pole's, a pole's tile in the pole's column is excluded by `TileCol`. -/
theorem tileRead_afterF {T : Pole} {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} (hb : ZoneOK T) (hR : PoleTileWalk.ReadFacts T E) (hs : Sim E F A₁ m)
    (hpair : pairOK T.Q A₁ B = true) (hrp : readPF T.Q A₁ B = true) (hBpc : B.pc = T.Q.read + 2) (hsn : sideNow T.Q B = true)
    (hm : ColMap T.Q m) (hcol : TileCol T.Q (go step m).2) : TileRead T.Q (go step m).2 := by
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
  unfold readPF at hrp
  rw [hBpc, hsn] at hrp
  simp only [bne_self_eq_false, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hrp
  obtain ⟨⟨⟨k3, hB2⟩, hlo⟩, hhi⟩ := hrp
  have hptr := hb.ptr
  have hs1 := hs.ram _ (show T.Q.ptrI < 2048 by omega)
  have hs2 := hs.ram _ hptr
  have a1 := TaintRun.minv_le hs1
  have a2 := TaintRun.le_maxv hs1
  have a3 := TaintRun.minv_le hs2
  have a4 := TaintRun.le_maxv hs2
  have e3 : m.y = A₁.y.v := PipeEntryRule.known_eq k3 hs.y
  have hz : RoomBlocks.operand m = E.prg.get! ((T.Q.read + 1) &&& E.mask).toNat := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hmpc]
  have hadr' : ScreenPage.readAddr m = ((m.ram.get! T.Q.ptrI).toUInt16 ||| ((m.ram.get! (T.Q.ptrI + 1)).toUInt16 <<< 8)) + m.y.toUInt16 := by
    rw [RoomBlocks.readAddr_eq hp1]
    unfold RoomBlocks.ptrZ
    rw [hz, hR.z1, hR.z2]
  unfold readMin at hlo
  unfold readMax at hhi
  have hn : (ScreenPage.readAddr m).toNat = (m.ram.get! T.Q.ptrI).toNat + 256 * (m.ram.get! (T.Q.ptrI + 1)).toNat + m.y.toNat := by
    rw [hadr', UInt16.toNat_add, SideChangeEnd.ptr_toNat, UInt8.toNat_toUInt16]
    rw [e3]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : (ScreenPage.readAddr m).toNat < 2048 := by rw [hn, e3]; omega
  have hr0 : ScreenPage.readAddr m < 0x2000 := by
    apply UInt16.lt_iff_toNat_lt.2
    have e8 : (0x2000 : UInt16).toNat = 8192 := by decide
    rw [e8]
    omega
  have hri : readI m = (ScreenPage.readAddr m).toNat := by
    unfold readI
    rw [UInt16.toNat_and]
    have e7 : (0x7FF : UInt16).toNat = 2 ^ 11 - 1 := by decide
    rw [e7, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hlt
  have hin' : T.Q.bufLo ≤ readI m ∧ readI m < T.Q.bufLo + T.Q.bufBytes := by
    rw [hri, hn, e3]
    omega
  have hy := PoleTileWalk.step_lda_izy_y hnmi hhal hp0 hp1 hop hr0
  have hat : readAt T.Q (go step m).2 = readI m :=
    PoleTileWalk.readAt_after hp1 (by rw [hz]; exact hR.z1) (by rw [hz]; exact hR.z2) hram hy
  have hval : (go step m).2.a = m.ram.get! (readI m) := by
    rw [ha, RoomBlocks.readVal_eq hr0]
    rfl
  have ht : Tile T.Q (m.ram.get! (readI m)) := by
    rw [← hval]
    exact htile
  have hc := hm (readI m) hin'.1 hin'.2 ht
  have hc' : onCol T.Q (readAt T.Q (go step m).2) = true := by rw [hat]; exact hc
  refine ⟨hc', ?_⟩
  by_cases hf : ((go step m).2.ram.get! T.Q.pI).toNat + 1 < T.Q.pg
  · exact absurd htile (hcol hpc hsv hf hc')
  · omega

/-! ## The frame -/

/-- **The frame.** From a `FrameStart` with the map `ColMap`, while each instruction is `CleanK`, meets `PosAt`, `YAt`, `HypR`, `BufAt` and `TileCol`, the routine byte
does not become the pole's. `TileFar` is not assumed: only `TileCol`, at the pole's column. -/
theorem no_write_frameF {T : Pole} {H : HP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (hc : frameCheckF T H E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hm0 : ColMap T.Q (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ YAt T.G H.R.yI (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ TileCol T.Q (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOKF_of_check hp hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOfF T H E).kl = (cfgOfF T H E).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, LiveF (cfgOfF T H E) H ((s 0).frame, 2) A (s 0) ∧ TR T.Q A (s 0) := by
    have hT0 : ∀ A : AS, Sim E ((s 0).frame, 2) A (s 0) → TR T.Q A (s 0) := by
      intro A hA hpc
      rw [← hA.pc, h0.pc] at hpc
      exact absurd hpc hC.read.idle
    cases b with
    | false => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s0⟩, hT0 _ hsim⟩
    | true => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s1⟩, hT0 _ hsim⟩
  have live : ∀ j, j ≤ n → (∃ A, LiveF (cfgOfF T H E) H ((s 0).frame, 2) A (s j) ∧ TR T.Q A (s j)) ∧ ColMap T.Q (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA, hTA⟩, hmj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, hy1, hr1, hb1, _⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, _, hpair, hrp, _, h2⟩ :=
        live_stepF hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hy1 hr1 hTA
      have hcol : TileCol T.Q (go step (s j)).2 := by
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
        exact tileRead_afterF hC.zone hC.read hs1 hpair hrp hpc hsn hmj hcol
  obtain ⟨⟨A, hA, hTA⟩, _⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, hy1, hr1, _, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := live_stepF hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hy1 hr1 hTA
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-! ## The touch -/

/-- **The check on the ROM**: as `PoleTileHeight.poleCheckH`, with this walk in place of the walk of `PoleTileHeight` -/
def poleCheckF (sy : Syms) (m0 : Machine) : Bool :=
  ptrOK sy m0 && frameCheckF (poleOf sy m0) (hpOf sy m0) (PipeEntryRule.envOf m0) && SubsOnce.subsCheck sy m0 && PoleTileWalk.keepCheckOfS sy m0

theorem subs_of_F {sy : Syms} {m0 : Machine} (h : poleCheckF sy m0 = true) : SubsOnce.subsCheck sy m0 = true := by
  simp only [poleCheckF, Bool.and_eq_true] at h
  exact h.1.2

theorem keepS_of_F {sy : Syms} {m0 : Machine} (h : poleCheckF sy m0 = true) : PoleTileWalk.keepCheckOfS sy m0 = true := by
  simp only [poleCheckF, Bool.and_eq_true] at h
  exact h.2

/-- **The touch on a real frame, at the end of the move**: as `PoleTileHeight.touch_right_of_leftH`, with `TileCol` in place of `TileFar` -/
theorem touch_right_of_leftF {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleCheckF sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hyk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hcol : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileCol (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleCheckF, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frameF (T := poleOf sy m0) (H := hpOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw j hj)
      (fun j hj => frame_before hw j hj) (start_T (h0.pad _)) hm
      (fun j hj => ⟨cleanK_T (hk j), hpk n hw j hj, hyk n hw j hj, ⟨fun hs => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd ⟨j, hj, hs, hl⟩ hx
        · exact Nat.lt_of_not_le hl, fun ha => by
        show px (spotsF sy m0) (trace m i j) < (spotsF sy m0).left
        by_cases hl : (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
        · exact absurd (hag n hw j hj ha hl) hx
        · exact Nat.lt_of_not_le hl, by
        show (trace m i j).pc ∉ ([] : List UInt16)
        simp⟩, hbuf n hw j hj, hcol n hw j hj⟩)
    exact hn hw.2

/-- **In the pole's range, from one whole frame**: as `PoleTileHeight.inRange_of_frameH`, with `TileCol` in place of `TileFar` -/
theorem inRange_of_frameF {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleCheckF sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hyk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hcol : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileCol (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftF hc he h0 hk hpk hyk hm hbuf hcol hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleTileFar
