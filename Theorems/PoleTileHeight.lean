import Theorems.PoleTileRead

/-!
# The pole's tiles at the touch: the height at the side check, from the collision routine's own check

`PoleTileRead` follows the touch's frame with the height split at the start of the side check near the pole. For that it assumes `YSide`: at the start of the side check
the height is below the bound of the collision routine's own check of it. The routine checks the height at its start and leaves when it is too low; the height is not
known at the side check only because the walk forgets it at a store through an index it does not know (the routine of the head's collision has such stores).

Here the walk protects the height inside the collision routine, as `PoleFrame` protects the position (`PoleFrame.PosAt`): inside the routine (the stack holds its return
address, `PipeWrites.inZone`) the walk's guard is `GY`, that is `PoleFrame.Pole.GP` with the height too, so a store with a target not known does not touch it; outside it the
guard is `GP`, as before (`kstepH`). For that each instruction of the frame up to the write meets `YAt`: inside the collision routine, a store through an index or a pointer
does not write the height. The player's own vertical move (the gravity routine's store of the height through an index) comes before the collision routine.

The walk splits the height at the collision routine's first load of it (`HP.band`), near the pole, into pieces that hold every value (`bandPieces`): no hypothesis. The
routine's compare then leaves on the pieces that are too low. At the start of the side check the walk tests that the height is below the bound (up to a whole row), and
splits it into the pieces of `PoleTileRead` (`yPieces`); everything else is as in `PoleTileRead`.

So `YSide` is no longer assumed. What is assumed in its place is `YAt`, a condition on single instructions of the same kind as `PosAt` and `FrameKeep.CleanK`.

There is no game data in this file. Page: `1-1/f-6-17-4-PoleTileHeight.md`.
-/

namespace Smbrta.PoleTileHeight

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px ptrAt)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt startG fuelG knownOf wTarget opAt Plain Clean gsucc)
open FrameKeep (CleanK nonZero)
open TaintRun (AS Env Sim AB AM aRows)
open PoleTiles (Tile)
open PoleTileWalk (ColMap BufAt HypR inBufB okS pairOK readI)
open PoleTileRead (RP blocks hiR yPieces meet fullA readP TR TileFar)
open SideFrame (sideNow readF memB)

/-! ## The places -/

/-- the places: those of `PoleTileRead`, the collision routine's first load of the height, and the additions to the height where an accumulator with only its high
4 bits known is forgotten -/
structure HP where
  R : RP
  band : UInt16
  wk : List UInt16
  deriving Inhabited

/-- **The guard of the walk inside the collision routine**: `PoleFrame.Pole.GP` with the height protected too. A store with a target not known does not touch it (`YAt`). -/
def GY (T : Pole) (H : HP) : Guard := { T.GP with prot := H.R.yI :: T.GP.prot }

/-- the machine is inside the collision routine: the stack pointer is at most the routine's, and the stack holds the routine's return address there (as `PipeWrites.inZone`) -/
def InZone (G : Guard) (m : Machine) : Prop :=
  m.s.toNat ≤ G.P.stack.toNat ∧ m.ram.get! (0x100 + G.P.stack.toNat + 1) = G.zLo ∧ m.ram.get! (0x100 + G.P.stack.toNat + 2) = G.zHi

/-- **What is assumed of one instruction of the touch's frame, besides `CleanK` and `PosAt`.** Inside the collision routine, a store through an index or a pointer does
not write the height. -/
def YAt (G : Guard) (yI : Nat) (m : Machine) : Prop :=
  InZone G m → ∀ t, wTarget (opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ yI

/-- a state inside the collision routine covers only machines inside it -/
theorem inZone_of {G : Guard} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : PipeWrites.inZone G A = true) : InZone G m := by
  simp only [PipeWrites.inZone, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h1, ⟨⟨h2, h3⟩, h4⟩, h5⟩ := h
  have hlt := G.P.stack.toNat_lt
  refine ⟨by rw [hs.s]; exact h1, ?_, ?_⟩
  · rw [PipeEntryRule.known_eq h2 (hs.ram _ (by omega)), h3]
  · rw [PipeEntryRule.known_eq h4 (hs.ram _ (by omega)), h5]

/-! ## The steps with the height protected -/

/-- a store that is `Plain` and does not write the height is `Plain` with it protected -/
theorem plain_y {prot : List Nat} {yI : Nat} {t : UInt16} (h : Plain prot t) (hq : t < 0x2000 → (t &&& 0x7FF).toNat ≠ yI) : Plain (yI :: prot) t := by
  rcases h with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, ?_⟩
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => hq h1 e, h2⟩
  · exact Or.inr h1

/-- **`CleanK` of the walk's guard** inside the collision routine, away from the move routine's stores of the position: from `CleanK`, `PosAt`, `YAt` -/
theorem cleanK_GY {T : Pole} {H : HP} {q : UInt16} {m : Machine} (h : CleanK T.G q m) (hp : PosAt T.Q T.ps m) (hy : YAt T.G H.R.yI m) (hz : InZone T.G m)
    (hn : m.pc ∉ T.ps) : CleanK (GY T H) q m :=
  ⟨fun t ht hq => plain_y (plain_pos (h.store t ht hq) (fun hlt => ⟨fun e => hn (hp t ht hlt (Or.inl e)).1, fun e => hn (hp t ht hlt (Or.inr e)).1⟩))
    (fun hlt e => hy hz t ht hlt e), h.read, h.jump, h.time⟩

/-- **The steps of the walk**: those of `PoleFrame.kstepT`, with the guard `GY` inside the collision routine -/
def kstepH (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if T.ps.contains A.pc then kstepT T E ops A
  else if PipeWrites.inZone T.G A then FrameKeep.kstep T.K (GY T H) E ops A
  else FrameKeep.kstep T.K T.GP E ops A

section
variable {E : Env} {F : Nat × UInt8}

/-- **A step of the machine**, with the steps of this walk -/
theorem s_kstepH {T : Pole} {H : HP} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    (hc : CleanK T.G T.K.store m) (hp : PosAt T.Q T.ps m) (hy : YAt T.G H.R.yI m) (hs : Sim E F A m) :
    ∃ r ∈ kstepH T H E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ TaintRun.StepRel A B m (go step m).2 := by
  unfold kstepH
  by_cases h1 : T.ps.contains A.pc = true
  · rw [if_pos h1]
    exact s_kstepT hops hT hc hp hs
  · rw [if_neg h1]
    have hn : m.pc ∉ T.ps := by
      rw [hs.pc]
      intro h
      exact h1 (List.elem_eq_true_of_mem h)
    by_cases h2 : PipeWrites.inZone T.G A = true
    · rw [if_pos h2]
      exact FrameKeep.s_kstep hops hT (cleanK_GY hc hp hy (inZone_of hs h2) hn) hs
    · rw [if_neg h2]
      exact FrameKeep.s_kstep hops hT (cleanK_GP hc hp hn) hs

/-! ## The pieces of the height -/

/-- the height, by the pieces of `L` that may hold it -/
def splitP (yI : Nat) (L : List AB) (A : AS) : List AS := (L.filter (meet (A.getK yI))).map fun p => A.setK yI p

/-- every value below `n0` is in a piece of `L` -/
def coverN (L : List AB) (n0 : Nat) : Bool := (List.range n0).all fun n => L.any fun a => memB a n.toUInt8

/-- the pieces of the height at the collision routine's first load of it: every value, cut at the bound up to a whole row -/
def bandPieces (R : RP) : List AB := blocks 300 0 (hiR R) ++ blocks 300 (hiR R) 256

/-- the pieces of `L` cover a height below `n0` -/
theorem cov_splitP {L : List AB} {n0 yI : Nat} (hc : coverN L n0 = true) (hy : yI < 2048) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hv : (m.ram.get! yI).toNat < n0) : ∃ B ∈ splitP yI L A, Sim E F B m ∧ B.k = A.k := by
  simp only [coverN, List.all_eq_true, List.mem_range] at hc
  have h1 := hc _ hv
  obtain ⟨a, ha, hm⟩ := List.any_eq_true.1 h1
  have hv' : (m.ram.get! yI).toNat.toUInt8 = m.ram.get! yI := by simp
  rw [hv'] at hm
  have hmem := PoleTileRead.memB_mem hm
  have hmeet : meet (A.getK yI) a = true := by
    have h0 := TaintRun.mem_iff.1 (hs.ram _ hy)
    have h8 := TaintRun.mem_iff.1 hmem
    unfold meet
    apply beq_iff_eq.2
    apply TaintRun.bt_ext
    intro i hi
    have e1 := h0 i hi
    have e2 := h8 i hi
    rw [TaintRun.bt_and, TaintRun.bt_and, TaintRun.bt_xor, TaintRun.bt_zero hi]
    cases h3 : TaintRun.bt (m.ram.get! yI) i <;> cases h4 : TaintRun.bt (A.getK yI).v i <;> cases h5 : TaintRun.bt (A.getK yI).k i <;>
      cases h6 : TaintRun.bt a.v i <;> cases h7 : TaintRun.bt a.k i <;> simp_all
  refine ⟨A.setK yI a, ?_, PipeEntryRule.sim_setK' hs hmem, rfl⟩
  exact List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, hmeet⟩, rfl⟩

/-- the new pieces: the height at the collision routine's first load of it and at the start of the side check, the accumulator at the addition of the height's adder,
near the pole (elsewhere, at the additions `wk` to the height, an accumulator with only its high 4 bits known is forgotten, so that the addition is the usual one) -/
def zoneH (T : Pole) (H : HP) (A : AS) : List AS :=
  let R := H.R
  if A.pc == H.band && nearP T.Q A then splitP R.yI (bandPieces R) A
  else if A.pc == T.Q.side && nearP T.Q A then
    if decide ((A.getK R.yI).maxv.toNat < hiR R) then splitP R.yI (yPieces R) A else [A]
  else if A.pc == R.adcY && sideNow T.Q A && nearP T.Q A then fullA A
  else if H.wk.contains A.pc && A.a.k &&& 0xF0 == 0xF0 && !A.a.isK then [{ A with a := AB.top }]
  else [A]

/-- all the pieces before a step: those of `PoleFrame`, then these -/
def preH (T : Pole) (H : HP) (A : AS) : List AS := (preT T A).flatMap (zoneH T H)

/-- what the new pieces need from the check -/
structure ZoneH (H : HP) : Prop where
  band : coverN (bandPieces H.R) 256 = true
  side : coverN (yPieces H.R) (hiR H.R) = true
  yI : H.R.yI < 2048

theorem cov_zoneH {T : Pole} {H : HP} (hz : ZoneH H) {A : AS} {m : Machine} (hs : Sim E F A m) : ∃ B ∈ zoneH T H A, Sim E F B m ∧ B.k = A.k := by
  unfold zoneH
  by_cases h1 : (A.pc == H.band && nearP T.Q A) = true
  · rw [if_pos h1]
    have hlt := (m.ram.get! H.R.yI).toNat_lt
    exact cov_splitP hz.band hz.yI hs (by omega)
  · rw [if_neg h1]
    by_cases h2 : (A.pc == T.Q.side && nearP T.Q A) = true
    · rw [if_pos h2]
      by_cases h3 : decide ((A.getK H.R.yI).maxv.toNat < hiR H.R) = true
      · rw [if_pos h3]
        have h4 := TaintRun.le_maxv (hs.ram _ hz.yI)
        simp only [decide_eq_true_eq] at h3
        exact cov_splitP hz.side hz.yI hs (by omega)
      · rw [if_neg h3]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
    · rw [if_neg h2]
      by_cases h5 : (A.pc == H.R.adcY && sideNow T.Q A && nearP T.Q A) = true
      · rw [if_pos h5]
        exact PoleTileRead.cov_fullA A m hs
      · rw [if_neg h5]
        by_cases h5a : (H.wk.contains A.pc && A.a.k &&& 0xF0 == 0xF0 && !A.a.isK) = true
        · rw [if_pos h5a]
          exact ⟨{ A with a := AB.top }, List.mem_singleton.2 rfl, { hs with a := TaintRun.mem_top _ }, rfl⟩
        rw [if_neg h5a]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_preH {T : Pole} {H : HP} {A : AS} {m : Machine} (hb : ZoneOK T) (hz : ZoneH H) (hc : CleanK T.G T.K.store m) (hh : HypR T m) (hT : TR T.Q A m)
    (hs : Sim E F A m) : ∃ B ∈ preH T H A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1, h2⟩ := PoleTileRead.cov_preTW hb hc hh hT hs
  obtain ⟨D, hD, h3, h4⟩ := cov_zoneH (T := T) hz h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

end

/-! ## The search: no part of the proof -/

/-- what the search forgets: as `PoleTileRead.normU`; at the start of the side check near the pole, the height stays known -/
def normH (T : Pole) (H : HP) (A0 : AS) : AS :=
  let B := PoleTileRead.normU T A0
  if A0.pc == T.Q.side && PipeWrites.inZone T.G A0 && nearP T.Q A0 then B.setK H.R.yI (A0.getK H.R.yI) else B

def routeH (T : Pole) (H : HP) (X : PipeWrites.SG) (B0 : AS) : PipeWrites.SG :=
  let G := T.G
  let B := normH T H B0
  let K := keyT T B
  let X := if PoleTileRead.isCutU T B.pc then { X with multi := X.multi.insert K () } else X
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

partial def runH (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) (A0 : AS) : PipeWrites.SG := Id.run do
  let G := T.G
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let ps := preH T H cur
    for A₁ in ps do
      for r in kstepH T H E ops A₁ do
        match r with
        | some B =>
          if !readP T.Q A₁ B || !pairOK T.Q A₁ B || !okS T E A₁ then
            X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A₁, failPcs := X.failPcs.insert (A₁.pc.toNat + 65536) (X.failPcs.getD (A₁.pc.toNat + 65536) 0 + 1) }
        | none => pure ()
    let rs := ps.flatMap (kstepH T H E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    if cur.pc == T.Q.side && nearP T.Q cur && !decide ((cur.getK H.R.yI).maxv.toNat < hiR H.R) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert (cur.pc.toNat + 131072) (X.failPcs.getD (cur.pc.toNat + 131072) 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !PoleTileRead.isCutU T b.pc && b.pc != G.je && b.pc != G.subs && b.pc != T.K.entry && b.pc != H.band &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeH T H X b
    break
  return X

partial def searchH (T : Pole) (H : HP) (E : Env) (ops : Array (AM Unit)) (X0 : PipeWrites.SG) : PipeWrites.SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runH T H E ops X A
  return X

def searchOfH (T : Pole) (H : HP) (E : Env) : PipeWrites.SG :=
  let ops := (aRows E).toArray
  searchH T H E ops ([startG T.G false, startG T.G true].foldl (routeH T H) {})

def cfgOfH (T : Pole) (H : HP) (E : Env) : CfgT :=
  let q := PipeWrites.tableOfS (searchOfH T H E)
  { E, ops := (aRows E).toArray, T, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-! ## The places from the symbols and the ROM -/

/-- the addition to the height in the routine of the head's collision: the `ADC abs,Y` after its load of the height and a `CLC` -/
def headAdc (sy : Syms) (m0 : Machine) : UInt16 := ScreenPage.findOpZ m0 (PipeWrites.headAt sy m0) 0xA5 sy.Player_Y_Position.toUInt8 128 + 3

def hpOf (sy : Syms) (m0 : Machine) : HP :=
  let R := PoleTileRead.rpOf sy m0
  { R, band := PoleTileRead.bandAt sy m0, wk := [R.adcY, headAdc sy m0] }

/-- what the search finds: no part of the proof -/
def searchReport (sy : Syms) (m0 : Machine) : String :=
  let T := poleOf sy m0
  let H := hpOf sy m0
  let E := PipeEntryRule.envOf m0
  let X := searchOfH T H E
  let fp := (X.failPcs.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 16
  let byPc := X.done.fold (fun (h : Std.HashMap Nat Nat) _ (A, _) => h.insert A.pc.toNat (h.getD A.pc.toNat 0 + 1)) {}
  let topPc := (byPc.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 12
  s!"the pieces at the first load {(bandPieces H.R).map fun a => (a.v, a.k)} (cover {coverN (bandPieces H.R) 256}), at the side check {(yPieces H.R).map fun a => (a.v, a.k)} (cover {coverN (yPieces H.R) (hiR H.R)}); one frame: {X.steps} steps, {X.forks} forks, {X.fails} failures {fp}, table {X.multi.size}, states {X.done.size}; states by place {topPc}"

/-! ## The walk -/

/-- a state of the table covers the state, by the key of `normH` -/
def coverH (C : CfgT) (H : HP) (B : AS) : Bool :=
  match C.idx[keyT C.T (normH C.T H B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => PipeWrites.leK B D l
    | _, _ => false
  | none => false

/-- `PoleTileRead.walkU` with the new pieces and the steps with the height protected -/
def walkH (C : CfgT) (H : HP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preH C.T H A).all fun A₁ => okS C.T C.E A₁ && (kstepH C.T H C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && pairOK C.T.Q A₁ B && readP C.T.Q A₁ B &&
      (B.k != A.k || (B.pc != C.T.Q.read + 2 && C.cut.get! B.pc.toNat != 0 && coverH C H B) || walkH C H n B)

/-- **The check**: the checks of `PoleFrame.frameCheck` before its walk, the pieces of the height, the walk with the new pieces and the three tests, the facts at the
read -/
def frameCheckH (T : Pole) (H : HP) (E : Env) : Bool :=
  let C := cfgOfH T H E
  PoleTileWalk.frameBase T && coverN (bandPieces H.R) 256 && coverN (yPieces H.R) (hiR H.R) && decide (H.R.yI < 2048) && C.t.all (walkH C H fuelG) &&
    walkH C H fuelG (startG T.G false) && walkH C H fuelG (startG T.G true) && PoleTileWalk.readOK T E

/-- what the check says -/
structure FrameOKH (T : Pole) (H : HP) (E : Env) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  zh : ZoneH H
  table : (cfgOfH T H E).t.all (walkH (cfgOfH T H E) H fuelG) = true
  s0 : walkH (cfgOfH T H E) H fuelG (startG T.G false) = true
  s1 : walkH (cfgOfH T H E) H fuelG (startG T.G true) = true
  read : PoleTileWalk.ReadFacts T E

theorem frameOKH_of_check {T : Pole} {H : HP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (h : frameCheckH T H E = true) : FrameOKH T H E := by
  simp only [frameCheckH, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, hY1⟩, hY2⟩, hyI⟩, ht⟩, h0⟩, h1⟩, hr⟩ := h
  simp only [PoleTileWalk.frameBase, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩, _⟩, _⟩, _⟩ := hB
  exact ⟨b1, ⟨⟨b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩, hp⟩, ⟨hY1, hY2, hyI⟩, ht, h0, h1, PoleTileWalk.readFacts_of hr⟩

/-! ## One step -/

section
variable {C : CfgT} {H : HP} {Fu : Nat} {F : Nat × UInt8}

def LiveH (C : CfgT) (H : HP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkH C H n A = true

theorem cover_liveH (ht : C.t.all (walkH C H Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverH C H B = true) : ∃ D, LiveH C H F D m := by
  unfold coverH at h
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
theorem live_stepH (ht : C.t.all (walkH C H Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hz : ZoneH H) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveH C H F A m) (hc : CleanK C.T.G C.T.K.store m)
    (hp : PosAt C.T.Q C.T.ps m) (hy : YAt C.T.G H.R.yI m) (hh : HypR C.T m) (hTR : TR C.T.Q A m) :
    ∃ A₁ B, Sim C.E F A₁ m ∧ okS C.T C.E A₁ = true ∧ Sim C.E F B (go step m).2 ∧ pairOK C.T.Q A₁ B = true ∧ readP C.T.Q A₁ B = true ∧
      (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧
      (F.1 < (go step m).2.frame ∨ ∃ A', LiveH C H F A' (go step m).2 ∧ (A'.pc = C.T.Q.read + 2 → A' = B)) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkH] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preH hb hz hc hh hTR hs
    obtain ⟨r, hr1, hB⟩ := s_kstepH (H := H) hops hT hc hp hy hs1
    simp only [walkH, List.all_eq_true] at hw
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
        · obtain ⟨D, hD⟩ := cover_liveH ht hkl h1 hk2 h4
          refine ⟨D, hD, fun hDp => absurd ?_ h5⟩
          rw [← h1.pc, hD.1.pc]
          exact hDp
        · exact ⟨B, ⟨h1, hk2, n, h4⟩, fun _ => rfl⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The frame -/

/-- **The frame.** From a `FrameStart` with the map `ColMap`, while each instruction is `CleanK`, meets `PosAt`, `YAt`, `HypR`, `BufAt` and `TileFar`, the routine byte
does not become the pole's. `YSide` is not assumed: the walk keeps the height from the collision routine's own check of it. -/
theorem no_write_frameH {T : Pole} {H : HP} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (hc : frameCheckH T H E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hm0 : ColMap T.Q (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ YAt T.G H.R.yI (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ TileFar T.Q (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOKH_of_check hp hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOfH T H E).kl = (cfgOfH T H E).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, LiveH (cfgOfH T H E) H ((s 0).frame, 2) A (s 0) ∧ TR T.Q A (s 0) := by
    have hT0 : ∀ A : AS, Sim E ((s 0).frame, 2) A (s 0) → TR T.Q A (s 0) := by
      intro A hA hpc
      rw [← hA.pc, h0.pc] at hpc
      exact absurd hpc hC.read.idle
    cases b with
    | false => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s0⟩, hT0 _ hsim⟩
    | true => exact ⟨_, ⟨hsim, rfl, fuelG, hC.s1⟩, hT0 _ hsim⟩
  have live : ∀ j, j ≤ n → (∃ A, LiveH (cfgOfH T H E) H ((s 0).frame, 2) A (s j) ∧ TR T.Q A (s j)) ∧ ColMap T.Q (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA, hTA⟩, hmj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, hy1, hr1, hb1, _⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, _, hpair, hrp, _, h2⟩ :=
        live_stepH hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hy1 hr1 hTA
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
        exact PoleTileRead.tileRead_afterU hC.zone hC.read hs1 hpair hrp hpc hsn hmj hfar
  obtain ⟨⟨A, hA, hTA⟩, _⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, hy1, hr1, _, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := live_stepH hC.table hkl rfl hT2 hC.zone hC.zh hC.rt hA hh1 hp1 hy1 hr1 hTA
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-! ## The touch -/

/-- **The check on the ROM**: as `PoleTileRead.poleCheckU`, with this walk in place of the walk of `PoleTileRead` -/
def poleCheckH (sy : Syms) (m0 : Machine) : Bool :=
  ptrOK sy m0 && frameCheckH (poleOf sy m0) (hpOf sy m0) (PipeEntryRule.envOf m0) && SubsOnce.subsCheck sy m0 && PoleTileWalk.keepCheckOfS sy m0

theorem subs_of_H {sy : Syms} {m0 : Machine} (h : poleCheckH sy m0 = true) : SubsOnce.subsCheck sy m0 = true := by
  simp only [poleCheckH, Bool.and_eq_true] at h
  exact h.1.2

theorem keepS_of_H {sy : Syms} {m0 : Machine} (h : poleCheckH sy m0 = true) : PoleTileWalk.keepCheckOfS sy m0 = true := by
  simp only [poleCheckH, Bool.and_eq_true] at h
  exact h.2

/-- `YAt` with the places from the symbols and the ROM -/
abbrev YKeep (sy : Syms) (m0 : Machine) (m : Machine) : Prop := YAt (poleOf sy m0).G (hpOf sy m0).R.yI m

/-- **The touch on a real frame, at the end of the move**: as `PoleTileRead.touch_right_of_leftU`, with `YAt` in place of `YSide` -/
theorem touch_right_of_leftH {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleCheckH sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hyk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hfar : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileFar (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleCheckH, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frameH (T := poleOf sy m0) (H := hpOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw j hj)
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
        simp⟩, hbuf n hw j hj, hfar n hw j hj⟩)
    exact hn hw.2

/-- **In the pole's range, from one whole frame**: as `PoleTileRead.inRange_of_frameU`, with `YAt` in place of `YSide` -/
theorem inRange_of_frameH {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleCheckH sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hyk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → YKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hfar : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → TileFar (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftH hc he h0 hk hpk hyk hm hbuf hfar hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleTileHeight
