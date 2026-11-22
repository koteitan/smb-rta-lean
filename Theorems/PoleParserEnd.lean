import Theorems.PoleParser

/-!
# The area parser: the second half of a frame

`PoleParser` proves the parser's invariant at control (`inv₀`), that the rule of one frame keeps it (`inv_rule`), and the first half of that rule on a real frame
(`frame_toU`: from the frame's start to `UpdScrollVar`). What was left is the second half (`ParseU`): from `UpdScrollVar` to the frame's end.

This file proves it for every value of the tasks left `N` from 0 to 8, in the weak form `ParseW` (the bytes kept, or one task; `inv_ruleW`: the weak rule `RuleW`
keeps the invariant as `Rule` does). `rule_frame`: a frame in control that comes to the player's routine follows `RuleW`, when at its start `N ≤ 8`, the column in its
page is below 16 and the page is not 255. Its cases: `rule_six` (`N` ∈ `vSix` = {2, 3, 4, 6, 7, 8}: `RenderAreaGraphics` or `AreaParserCore`, the counter, the
column and the page kept, `N` kept or one less), `rule_col` (`N` ∈ `vCol` = {1, 5}: the column's step), `rule_zero` (`N` = 0: no task, or the start of a new column
with the counter less 32). `col₀`, `col_frame`, `page_of_inv`, `inv_runC`, `step_frame`, `step_noCut`: the column below 16 at control and on every frame, so the
invariant holds on a run from the conditions of each frame and the edge below `65280 − L` px. `inv_onFrames`: the same on the frames of a run up to the touch's
frame (`FrameKeep.Frames`), where the frames give the start in control, `cleanE`, `noStore` and the time; `cleanPar_of`: with `cleanE`, the new condition on each
instruction is `CleanK` of `guardPI` (no store through an index or a pointer writes the parser's four bytes).

How: the walks of `PoleParser.uCheckP` to `UpdScrollVar`, one for each byte with the byte followed (`rk`), go on from there (`atE`). Each state at `UpdScrollVar` is
split by the value of `N` (`SideFrame.fillB`), and for each value walks go to the frame's end: for `vSix` they follow the byte (`atRkE`); for `vCol` the page's walk is
split by the column and, for the column 15, by the page (`atRkV`); for `N` = 0 the counter's walk is split by its value, goes to the frame's end or to the call of the
task handler (`walkEQ`, `endEQ`), and from there on with the counter followed (`atRkZ`). Round 27's walks of this kind ran out of fuel: the walk's guard did not protect
`N`, so a store through an index with an unknown target in `RenderAreaGraphics` made the walk forget `N`, and no state of the loop was covered by the table, whose
search did protect `N`. Here the guard of each walk to the end protects the byte, `N`, the column and the page (`guardN`), and the table's key holds their values
(`keyN`). That asks one more condition of each instruction of the frame: no store through an index or a pointer writes them (`CleanK` of `guardN`; measured on real
frames by `pole-keep parser`, 0 hits). The checks on the ROM are `eCheckP` and `colCheckK`.

What is not proved here: `CleanK` of `guardN` and `AfterKeep.guardH` for the parser's bytes on the frames of the run, no wrap of the scroll (`NoWrap`), the edge below
`65280 − L` px, and the rest of `tilesCol` (`hslot`, `hnear`, `hread`). Round 29: `PoleParserRun` takes `inv_onFrames` to the route's frames (`guardE` protects the
parser's four bytes, so `cleanE` gives `CleanK` of `guardPI`; no wrap is the field `PoleJoin.Run.parWrap`, the edge's bound the theorem `PoleParserRun.edgeLow_run`), and the old field
`tilesCol` is a theorem from the narrower field (`PoleTileFar.TileSlot`).
There is no game data in this file. Page: `1-1/f-6-17-9-PoleParserEnd.md`.
-/

namespace Smbrta.PoleParser

open TaintRun (AS Sim Env)

/-! ## The weak rule -/

/-- **One task of the parser**: from the counter and the tasks left at `UpdScrollVar` -/
def Step (a b : Vals) : Prop :=
  if a.n = 0 then 32 ≤ a.s ∧ a.s < 160 ∧ b.n = 7 ∧ b.s = a.s - 32 ∧ b.col = a.col
  else b.n = a.n - 1 ∧ b.s = a.s ∧ b.col = (if a.n = 1 ∨ a.n = 5 then a.col + 1 else a.col)

/-- **The parser's part, weak**: the edge kept, and the parser's bytes kept, or one task -/
def ParseW (a b : Vals) : Prop := b.edge = a.edge ∧ ((b.n = a.n ∧ b.s = a.s ∧ b.col = a.col) ∨ Step a b)

/-- **The rule of one frame, weak**: the scroll, then the parser's part, weak -/
def RuleW (a b : Vals) : Prop := ∃ c, Scroll a c ∧ ParseW c b

/-- `Parse` gives `ParseW` -/
theorem parseW_of {ctl6 : Bool} {a b : Vals} (h : Parse ctl6 a b) : ParseW a b := by
  obtain ⟨he, hp⟩ := h
  refine ⟨he, ?_⟩
  cases ctl6 with
  | true => simp only [if_true] at hp; exact Or.inl hp
  | false =>
    simp only [Bool.false_eq_true, if_false] at hp
    by_cases hn : a.n = 0
    · rw [if_pos hn] at hp
      rcases hp with ⟨h1, h2, h3, h4, h5⟩ | ⟨_, h3, h4, h5⟩
      · right; unfold Step; rw [if_pos hn]; exact ⟨h1, h2, h3, h4, h5⟩
      · left; exact ⟨h3, h4, h5⟩
    · rw [if_neg hn] at hp
      right; unfold Step; rw [if_neg hn]; exact hp

/-- `Rule` gives `RuleW` -/
theorem ruleW_of {a b : Vals} (h : Rule a b) : RuleW a b := by
  obtain ⟨_, c, hs, hp⟩ := h
  exact ⟨c, hs, parseW_of hp⟩

/-- **The weak rule keeps the invariant**: each of its cases is a case of `Parse` -/
theorem inv_ruleW {L : Nat} {a b : Vals} (h : InvV L a) (hr : RuleW a b) : InvV L b := by
  obtain ⟨c, hs, he, hp⟩ := hr
  rcases hp with hk | hst
  · exact inv_rule h ⟨true, c, hs, he, by simp only [if_true]; exact hk⟩
  · refine inv_rule h ⟨false, c, hs, he, ?_⟩
    simp only [Bool.false_eq_true, if_false]
    unfold Step at hst
    by_cases hn : c.n = 0
    · rw [if_pos hn] at hst ⊢
      exact Or.inl hst
    · rw [if_neg hn] at hst ⊢
      exact hst

/-- **Frames by the weak rule keep the invariant** -/
theorem inv_runW {sy : Syms} {m0 : Machine} {L : Nat} {ms : Nat → Machine} (h0 : Inv (places sy m0) L (ms 0))
    (hr : ∀ n, RuleW (valsOf (places sy m0) (ms n)) (valsOf (places sy m0) (ms (n + 1)))) : ∀ n, Inv (places sy m0) L (ms n)
  | 0 => h0
  | n + 1 => (invV_iff (P := places sy m0) (m := ms (n + 1))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := ms n)).1 (inv_runW h0 hr n)) (hr n))

/-! ## The walks to the frame's end -/

/-- the index of the tasks left -/
def nI (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).task &&& 0x7FF).toNat

/-- the values of `N` for which the column's step does not run -/
def vSix : List UInt8 := [2, 3, 4, 6, 7, 8]

/-- a byte that no instruction decrements: the walk of `N` follows no byte -/
def noRk : Nat := 2048

/-- the followed byte of the walk to the end for the byte `b`: `b`, or none for `N` -/
def rkOf (sy : Syms) (m0 : Machine) (b : Nat) : Nat := if b == nI sy m0 then noRk else b

/-- the environment of the walk to the end -/
def envE (sy : Syms) (m0 : Machine) (b : Nat) : Env := { PipeEntryRule.envOf m0 with rkI := rkOf sy m0 b }

/-- the state at `UpdScrollVar` for the walk to the end: for `N`, the followed byte is dropped -/
def startE (sy : Syms) (m0 : Machine) (b : Nat) (B : AS) : AS := if b == nI sy m0 then { B with rk := false } else B

/-- the index of the parser's column in its page -/
def cIdx (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).col &&& 0x7FF).toNat

/-- the index of the parser's page -/
def gIdx (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).page &&& 0x7FF).toNat

/-- **The guard of the walk to the end**: that of the frames, with the byte, `N`, the column and the page protected -/
def guardN (sy : Syms) (m0 : Machine) (b : Nat) : PipeWrites.Guard :=
  { FrameKeep.guardF sy m0 with prot := [b, nI sy m0, cIdx sy m0, gIdx sy m0] ++ (FrameKeep.guardF sy m0).prot }

/-- what the walk to the end asks there: the byte followed and not decremented; for `N`, known, and `v` or `v − 1` -/
def finE (sy : Syms) (m0 : Machine) (b : Nat) (v : UInt8) (B : AS) : Bool :=
  if b == nI sy m0 then (B.getK (nI sy m0)).isK && ((B.getK (nI sy m0)).v == v || (B.getK (nI sy m0)).v == v - 1) else B.rk && !B.spent

/-- the key of the search and of the table of the walk to the end: that of `PrevKeep`, and the value of `N` (states with different values of `N` are not joined; no
part of the proof) -/
def keyN (sy : Syms) (m0 : Machine) (S : FrameKeep.Spot) (G : PipeWrites.Guard) (A : AS) : Nat :=
  let num := fun (b : TaintRun.AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  ((PrevKeep.keyP S G [] A * 65536 + num (A.getK (nI sy m0))) * 65536 + num (A.getK (cIdx sy m0))) * 65536 + num (A.getK (gIdx sy m0))

/-- **The walk to the frame's end** for the byte `b` and the value `v` of `N` at `UpdScrollVar`, from the states `starts` there: its table (the search is no part of
the proof) -/
def qfCfg (sy : Syms) (m0 : Machine) (b : Nat) (fin : AS → Bool) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardN sy m0 b
  let E := envE sy m0 b
  let key := keyN sy m0 S G
  let G' := CtrlKeep.guardP sy m0 (b :: nI sy m0 :: cIdx sy m0 :: gIdx sy m0 :: CtrlKeep.spareI sy m0)
  let keyS := keyN sy m0 S G'
  let X := starts.foldl (PrevKeep.routeP S G' [] keyS) {}
  let P := PrevKeep.searchP S G' E [] [] keyS (TaintRun.aRows E).toArray (FrameKeep.ctlI sy) (fun A => A.pc == EdgeStep.rPc sy) { X }
  let q := FrameKeep.tableOfKW key P.X
  { E, ops := (TaintRun.aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin }

/-- the walk to the end with `finE` -/
def qeCfg (sy : Syms) (m0 : Machine) (b : Nat) (v : UInt8) (starts : List AS) : FrameKeep.CfgK := qfCfg sy m0 b (finE sy m0 b v) starts

/-- the search of the walk to `UpdScrollVar` for the byte `b` (as in `quCfg`): no part of the proof -/
def quSearch (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : PrevKeep.PS :=
  PrevKeep.searchFrom sy m0 { PipeEntryRule.envOf m0 with rkI := b } (b :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy) (fun A => A.pc == sy.UpdScrollVar)
    (starts.map AfterKeep.rkOn)

/-- the starts of the walk to the end: the states at `UpdScrollVar` of the walk to it, split by `N`, with the value `v` (no part of the proof) -/
def startsE (sy : Syms) (m0 : Machine) (b : Nat) (v : UInt8) (U : List AS) : List AS :=
  (U.flatMap fun B => SideFrame.fillB (nI sy m0) (startE sy m0 b B)).filter fun B => (B.getK (nI sy m0)).isK && (B.getK (nI sy m0)).v == v

/-- the walk to the end -/
def walkE (sy : Syms) (m0 : Machine) (C : FrameKeep.CfgK) : AS → Bool :=
  EdgeStep.walkKP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK

/-- what the walk to `UpdScrollVar` for a parser's byte asks there: the byte followed and not decremented, and for each value of `N` in `vSix` the walk to the end -/
def atRkE (sy : Syms) (m0 : Machine) (b : Nat) (Ce : UInt8 → FrameKeep.CfgK) (B : AS) : Bool :=
  atRkU B && (SideFrame.fillB (nI sy m0) (startE sy m0 b B)).all fun B' =>
    !((B'.getK (nI sy m0)).isK && vSix.contains (B'.getK (nI sy m0)).v) || walkE sy m0 (Ce (B'.getK (nI sy m0)).v) B'

/-! ### The column's step: `N` = 1 or 5 -/

/-- the values of `N` for which the column's step runs -/
def vCol : List UInt8 := [1, 5]

/-- what the walk of the page asks at the end, for `N` = `w` and the column `c` < 15 at `UpdScrollVar`: the page followed and not decremented, and `N` and the
column known, kept, or `w − 1` and `c + 1` -/
def finC (sy : Syms) (m0 : Machine) (w c : UInt8) (B : AS) : Bool :=
  B.rk && !B.spent && (B.getK (nI sy m0)).isK && (B.getK (cIdx sy m0)).isK &&
    (((B.getK (nI sy m0)).v == w && (B.getK (cIdx sy m0)).v == c) || ((B.getK (nI sy m0)).v == w - 1 && (B.getK (cIdx sy m0)).v == c + 1))

/-- what the walk asks at the end, for `N` = `w`, the column 15 and the page `p` at `UpdScrollVar`: `N`, the column and the page known, kept, or `w − 1`, 0 and
`p + 1` -/
def finP (sy : Syms) (m0 : Machine) (w p : UInt8) (B : AS) : Bool :=
  (B.getK (nI sy m0)).isK && (B.getK (cIdx sy m0)).isK && (B.getK (gIdx sy m0)).isK &&
    (((B.getK (nI sy m0)).v == w && (B.getK (cIdx sy m0)).v == 15 && (B.getK (gIdx sy m0)).v == p) ||
      ((B.getK (nI sy m0)).v == w - 1 && (B.getK (cIdx sy m0)).v == 0 && (B.getK (gIdx sy m0)).v == p + 1))

/-- the starts of the search for the column `c` (no part of the proof) -/
def startsC (sy : Syms) (m0 : Machine) (w c : UInt8) (U : List AS) : List AS :=
  U.filterMap fun B => if SideFrame.memB (B.getK (nI sy m0)) w && SideFrame.memB (B.getK (cIdx sy m0)) c then
    some ((B.setK (nI sy m0) (TaintRun.AB.known w)).setK (cIdx sy m0) (TaintRun.AB.known c)) else none

/-- the starts of the search for the column 15 and the page `p` (no part of the proof) -/
def startsP (sy : Syms) (m0 : Machine) (w p : UInt8) (U : List AS) : List AS :=
  U.filterMap fun B => if SideFrame.memB (B.getK (nI sy m0)) w && SideFrame.memB (B.getK (cIdx sy m0)) 15 && SideFrame.memB (B.getK (gIdx sy m0)) p then
    some ((({ B with rk := false } : AS).setK (nI sy m0) (TaintRun.AB.known w)).setK (cIdx sy m0) (TaintRun.AB.known 15) |>.setK (gIdx sy m0) (TaintRun.AB.known p))
  else none

/-- the tables of the walks to the end: for each byte and value of `N` (`e`), for the column `c` < 15 (`c`), for the column 15 and the page `p` (`p`) -/
structure Cfgs where
  e : Nat → UInt8 → FrameKeep.CfgK
  c : UInt8 → UInt8 → FrameKeep.CfgK
  p : UInt8 → UInt8 → FrameKeep.CfgK
  /-- after the task handler's call, for `N` = 0 -/
  tail : FrameKeep.CfgK

/-- the part for `vCol` at `UpdScrollVar`, of a state of the walk for the byte `b`, split by `N`: for the column and its page nothing (the walk of the page knows
them), for the others the walk with `finE`; for the page, split by the column: for `c` < 15 the walk with `finC`, for 15 split by the page: for `p` < 255 the
walk with `finP` -/
def atRkV (sy : Syms) (m0 : Machine) (b : Nat) (Ce : Cfgs) (B : AS) : Bool :=
  (SideFrame.fillB (nI sy m0) (startE sy m0 b B)).all fun B' =>
    !((B'.getK (nI sy m0)).isK && vCol.contains (B'.getK (nI sy m0)).v) ||
      (if b == cIdx sy m0 then true
       else if b == gIdx sy m0 then
         (SideFrame.fillB (cIdx sy m0) B').all fun B'' =>
           !(B''.getK (cIdx sy m0)).isK || decide (15 < (B''.getK (cIdx sy m0)).v.toNat) ||
             (if (B''.getK (cIdx sy m0)).v == 15 then
                (SideFrame.fillB (gIdx sy m0) { B'' with rk := false }).all fun B3 =>
                  !(B3.getK (gIdx sy m0)).isK || (B3.getK (gIdx sy m0)).v == 255 ||
                    walkE sy m0 (Ce.p (B'.getK (nI sy m0)).v (B3.getK (gIdx sy m0)).v) B3
              else walkE sy m0 (Ce.c (B'.getK (nI sy m0)).v (B''.getK (cIdx sy m0)).v) B'')
       else walkE sy m0 (Ce.e b (B'.getK (nI sy m0)).v) B')

/-- the bytes followed to the frame's end: the parser's four and the edge's two -/
def pE (sy : Syms) (m0 : Machine) : List Nat := pI sy m0 ++ [((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat, ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat]

/-- the indices of the counter and of the edge's pixel and page -/
def sIdx (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).s32 &&& 0x7FF).toNat
def xIdx (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).ex &&& 0x7FF).toNat
def yIdx (sy : Syms) (m0 : Machine) : Nat := ((places sy m0).ep &&& 0x7FF).toNat

theorem pE_eq {sy : Syms} {m0 : Machine} : pE sy m0 = [nI sy m0, sIdx sy m0, cIdx sy m0, gIdx sy m0, xIdx sy m0, yIdx sy m0] := rfl

/-- **What the walk of the page gives at the frame's end for `vCol`**, from `u` at `UpdScrollVar`: for the column below 15 the page kept, and `N` and the column
kept, or `N − 1` and the column + 1; for the column 15, `N`, the column and the page kept, or `N − 1`, the column 0 and the page + 1 -/
def ColEnd (sy : Syms) (m0 : Machine) (u e : Machine) : Prop :=
  ((u.ram.get! (cIdx sy m0)).toNat < 15 → e.ram.get! (gIdx sy m0) = u.ram.get! (gIdx sy m0) ∧
      ((e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) ∧ e.ram.get! (cIdx sy m0) = u.ram.get! (cIdx sy m0)) ∨
       (e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) - 1 ∧ e.ram.get! (cIdx sy m0) = u.ram.get! (cIdx sy m0) + 1))) ∧
  (u.ram.get! (cIdx sy m0) = 15 →
      (e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) ∧ e.ram.get! (cIdx sy m0) = 15 ∧ e.ram.get! (gIdx sy m0) = u.ram.get! (gIdx sy m0)) ∨
      (e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) - 1 ∧ e.ram.get! (cIdx sy m0) = 0 ∧ e.ram.get! (gIdx sy m0) = u.ram.get! (gIdx sy m0) + 1))


/-! ## A walk to the frame's end or to a place

`EdgeStep.walkKP`, and a path also stops at the place `Q`, where it asks `atQ` (the walk does not step from `Q`). So from a state where it succeeds, the frame ends in a
state that meets `fin`, or comes to `Q` in a state that meets `atQ` (`endEQ`). -/

open TaintRun in
/-- **The walk to the frame's end or to `Q`** -/
def walkEQ (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || cutP A.pc || (A.pc == Q && atQ A) || (A.pc != Q && (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkEQ C l cutP Q atQ n B
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B)

section WalkEQ
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun

variable {E : Env} {F : Nat × UInt8} {C : FrameKeep.CfgK} {l : List Nat} {cutP : UInt16 → Bool} {Q : UInt16} {atQ : AS → Bool} {Fu : Nat}

/-- `A` covers `m`, and the walk succeeds from `A` -/
def LiveEQ (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) (atQ : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkEQ C l cutP Q atQ n A = true

theorem cover_liveEQ (ht : C.t.all (walkEQ C l cutP Q atQ Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveEQ C l cutP Q atQ F D m := by
  unfold FrameKeep.coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le hle hs, Fu, hall⟩
  · cases h2

theorem live_stepEQ (ht : C.t.all (walkEQ C l cutP Q atQ Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveEQ C l cutP Q atQ F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false)
    (hp : cutP m.pc = false) :
    (m.pc = Q ∧ ∃ B, atQ B = true ∧ Sim C.E F B m) ∨
    (∃ A', LiveEQ C l cutP Q atQ F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkEQ] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    have hp' : cutP A.pc = false := by rw [← hs.pc]; exact hp
    simp only [walkEQ, hx', hp', Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hw
    rcases hw with ⟨hq, ha⟩ | ⟨hq, hw⟩
    · exact Or.inl ⟨by rw [hs.pc]; exact hq, A, ha, hs⟩
    · right
      obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
      simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
      obtain ⟨hd, hw2⟩ := hw A₁ hA
      obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
      have hw3 := hw2 r hr
      cases r with
      | none => simp at hw3
      | some B =>
        obtain ⟨h1, h2⟩ := hB B rfl
        dsimp only at hw3
        rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
        · left
          rw [hk1] at k1
          rw [if_pos (by simp [k1])] at hw3
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
          rcases hw3 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD⟩ := cover_liveEQ ht hkl h1 h3
            exact ⟨D, hD, k2, k3⟩
          · exact ⟨B, ⟨h1, n, h3⟩, k2, k3⟩
        · right
          rw [hk1] at k1
          rw [if_neg (by simp [k1])] at hw3
          simp only [Bool.and_eq_true, beq_iff_eq] at hw3
          exact ⟨k2, B, hw3.1.2, hw3.2, h1⟩

/-- **The walk to the frame's end or to `Q`: from `k`.** The frame ends in a state that meets `fin`, or comes to `Q` at some `k' ≥ k` in a state that meets
`atQ`. -/
theorem endEQ (ht : C.t.all (walkEQ C l cutP Q atQ Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkEQ C l cutP Q atQ Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → cutP (trace m i j).pc = false) :
    (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∨
    (∃ k', k ≤ k' ∧ (trace m i k').pc = Q ∧ (trace m i k').frame = m.frame ∧ m.fdot + 3 * k' ≤ (trace m i k').fdot ∧ ∃ B, atQ B = true ∧ Sim C.E F B (trace m i k')) := by
  have key : ∀ d, (∃ A, LiveEQ C l cutP Q atQ F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ FrameKeep.endOK C.G B = true ∧ Sim C.E F B (trace m i (k + d))) ∨
      (∃ k', k ≤ k' ∧ (trace m i k').pc = Q ∧ (trace m i k').frame = m.frame ∧ m.fdot + 3 * k' ≤ (trace m i k').fdot ∧ ∃ B, atQ B = true ∧ Sim C.E F B (trace m i k')) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h2', h3⟩ | h
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepEQ ht hkl hops h1 (hcl (k + d)) (hx (k + d)) (hp (k + d) (by omega) h2) with ⟨a1, B, b1, b2⟩ | ⟨A', a1, a2, a3⟩ | ⟨a1, B, a2, a3, a4⟩
        · exact Or.inr (Or.inr ⟨k + d, by omega, a1, h2, h3, B, b1, b2⟩)
        · rw [← e] at a1 a2 a3
          exact Or.inl ⟨A', a1, a2.trans h2, by omega⟩
        · rw [← e] at a1 a4
          exact Or.inr (Or.inl ⟨by rw [a1, h2], B, a3, a2, a4⟩)
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr (Or.inl ⟨h1, B, h2, h2', h3⟩)
      · exact Or.inr (Or.inr h)
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, _, h3⟩ | h
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact Or.inl ⟨B, h2, h3⟩
  · exact Or.inr h

end WalkEQ


/-! ### No task left: `N` = 0 -/

/-- the call of the task handler in `UpdScrollVar` (`RunParser`): `UpdScrollVar` loads the control byte (3 bytes), compares it (2), branches (2), loads `N` (3),
branches (2), loads the counter (3), compares it (2), branches (2), loads it (3), subtracts (2), stores it (3), loads 0 (2) and stores it (3): 32 bytes.
`PoleParser.places` reads the task handler's address from the operand right after this place. No check reads the instruction here: the walks only compare the pc
with `qR`, and `endEQ` holds for any place. -/
def qR (sy : Syms) : UInt16 := sy.UpdScrollVar + 32

/-- what the walk of the counter asks at the frame's end, for `N` = 0 and the counter `s` at `UpdScrollVar`: `N` 0 and the counter `s` -/
def fin0 (sy : Syms) (m0 : Machine) (s : UInt8) (B : AS) : Bool :=
  (B.getK (nI sy m0)).isK && (B.getK (sIdx sy m0)).isK && (B.getK (nI sy m0)).v == 0 && (B.getK (sIdx sy m0)).v == s

/-- what the walk after the task handler's call asks at the frame's end: the counter followed and not decremented, and `N` known as 7 -/
def finT (sy : Syms) (m0 : Machine) (B : AS) : Bool := B.rk && !B.spent && (B.getK (nI sy m0)).isK && (B.getK (nI sy m0)).v == 7

/-- **A walk with no table**, for the byte `b` (its environment and guard as `qfCfg`) -/
def emptyCfg (sy : Syms) (m0 : Machine) (b : Nat) (fin : AS → Bool) : FrameKeep.CfgK :=
  { E := envE sy m0 b, ops := (TaintRun.aRows (envE sy m0 b)).toArray, S := FrameKeep.spotOf sy m0, G := guardN sy m0 b, W := [], t := #[], kl := #[], idx := {},
    cut := ByteArray.mk (Array.replicate 65536 0), key := fun _ => 0, fin }

/-- what the walk of the counter asks at the task handler's call: the counter `s` was in 32 ‥ 159, it is `s − 32` now, and the walk `Ct` with the counter followed
succeeds -/
def at0 (sy : Syms) (m0 : Machine) (Ct : FrameKeep.CfgK) (s : UInt8) (B : AS) : Bool :=
  decide (32 ≤ s.toNat) && decide (s.toNat < 160) && (B.getK (sIdx sy m0)).isK && (B.getK (sIdx sy m0)).v == s - 32 && walkE sy m0 Ct (AfterKeep.rkOn B)

/-- the head's walk for the counter `s`: no table, `N` followed by no byte -/
def headCfg (sy : Syms) (m0 : Machine) (s : UInt8) : FrameKeep.CfgK := emptyCfg sy m0 (nI sy m0) (fin0 sy m0 s)

/-- the part for `N` = 0 at `UpdScrollVar`, of a state of the walk for the byte `b`, split by `N`: for `N` nothing, for the counter split by its value and the walk
to the frame's end or to the task handler's call, for the others the walk with `finE` -/
def atRkZ (sy : Syms) (m0 : Machine) (b : Nat) (Ce : Cfgs) (Ct : FrameKeep.CfgK) (B : AS) : Bool :=
  (SideFrame.fillB (nI sy m0) (startE sy m0 b B)).all fun B' =>
    !((B'.getK (nI sy m0)).isK && (B'.getK (nI sy m0)).v == 0) ||
      (if b == nI sy m0 then true
       else if b == sIdx sy m0 then
         (SideFrame.fillB (sIdx sy m0) { B' with rk := false }).all fun B'' =>
           !(B''.getK (sIdx sy m0)).isK ||
             walkEQ (headCfg sy m0 (B''.getK (sIdx sy m0)).v) (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (qR sy) (at0 sy m0 Ct (B''.getK (sIdx sy m0)).v)
               FrameKeep.fuelK B''
       else walkE sy m0 (Ce.e b 0) B')

/-- the table of the walk after the task handler's call (the searches are no part of the proof): from the states at `UpdScrollVar` of the walk for the counter,
with `N` 0 and the counter in 32 ‥ 159, a search to the call, and from there a search to the frame's end with the counter followed -/
def ctOf (sy : Syms) (m0 : Machine) (Ps' : List AS) : FrameKeep.CfgK :=
  let U := (quSearch sy m0 (sIdx sy m0) Ps').stops.toList
  let st := (List.range 128).flatMap fun j => U.filterMap fun B =>
    let s := (j + 32).toUInt8
    if SideFrame.memB (B.getK (nI sy m0)) 0 && SideFrame.memB (B.getK (sIdx sy m0)) s then
      some ((({ B with rk := false } : AS).setK (nI sy m0) (TaintRun.AB.known 0)).setK (sIdx sy m0) (TaintRun.AB.known s)) else none
  let H := PrevKeep.searchFrom sy m0 (envE sy m0 (nI sy m0)) (sIdx sy m0 :: nI sy m0 :: cIdx sy m0 :: gIdx sy m0 :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy)
    (fun A => A.pc == qR sy) st
  qfCfg sy m0 (sIdx sy m0) (finT sy m0) (H.stops.toList.map AfterKeep.rkOn)

/-- what the walk to `UpdScrollVar` asks there, for each byte of `pU`: for the bytes of `pE` `atRkE`, for the platforms' force `atRkU` -/
def atE (sy : Syms) (m0 : Machine) (Ce : Cfgs) (b : Nat) (B : AS) : Bool :=
  if (pE sy m0).contains b then atRkE sy m0 b (Ce.e b) B && atRkV sy m0 b Ce B && atRkZ sy m0 b Ce Ce.tail B else atRkU B

/-- what the middle walk asks after the scroll handler's call: for each byte the walk to `UpdScrollVar` with `atE`, and the walk of `EdgeStep` to the frame's end -/
def atRE (sy : Syms) (m0 : Machine) (Ps' : List AS) (Ce : Cfgs) (Cn : List FrameKeep.CfgK) (B : AS) : Bool :=
  ((pU sy m0).all fun b => walkQP (quCfg sy m0 b Ps') (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) sy.UpdScrollVar (atE sy m0 Ce b) FrameKeep.fuelK (AfterKeep.rkOn B)) &&
    Cn.all fun C => EdgeStep.walkKP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK (AfterKeep.rkOn B)

/-- what the first walk asks at the scroll handler: the middle walk succeeds, and for each of `pK` the middle walk with the byte followed -/
def atSE (sy : Syms) (m0 : Machine) (Cs : FrameKeep.CfgK) (Cm : List FrameKeep.CfgK) (Ps' : List AS) (Ce : Cfgs) (Cn : List FrameKeep.CfgK)
    (B : AS) : Bool :=
  AfterKeep.walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRE sy m0 Ps' Ce Cn) FrameKeep.fuelK B &&
    Cm.all fun C => EdgeStep.walkQR C (FrameKeep.ctlI sy) (EdgeStep.rPc sy) atRkU FrameKeep.fuelK (AfterKeep.rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler, the middle walks, the walks to `UpdScrollVar` and on to the frame's end -/
def cfgPE (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 Cs : FrameKeep.CfgK) (Cm : List FrameKeep.CfgK) (Ps' : List AS)
    (Ce : Cfgs) (Cn : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSE sy m0 Cs Cm Ps' Ce Cn) FrameKeep.fuelK
      (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- the tables of the walks to the end -/
def ceOf (sy : Syms) (m0 : Machine) (Ps' : List AS) (b : Nat) (w : UInt8) : FrameKeep.CfgK :=
  qeCfg sy m0 b w (startsE sy m0 b w (quSearch sy m0 b Ps').stops.toList)

/-- all the tables of the walks to the end -/
def cfgsOf (sy : Syms) (m0 : Machine) (Ps' : List AS) : Cfgs :=
  let U := (quSearch sy m0 (gIdx sy m0) Ps').stops.toList
  { e := ceOf sy m0 Ps', c := fun w c => qfCfg sy m0 (gIdx sy m0) (finC sy m0 w c) (startsC sy m0 w c U),
    p := fun w p => qfCfg sy m0 (nI sy m0) (finP sy m0 w p) (startsP sy m0 w p U), tail := ctOf sy m0 Ps' }

/-- the values of the column below 15, and of the page below 255 -/
def cols : List UInt8 := (List.range 15).map Nat.toUInt8
def pages : List UInt8 := (List.range 255).map Nat.toUInt8

/-- **The check of the second half**: as `uCheckP`, and from `UpdScrollVar` for each byte of `pE` and each value of `N` from 0 to 8 the walks to the frame's end
(`atE`), with their tables -/
def eCheckP (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let Ps := EdgeStep.qsSearch sy m0 v P.stops.toList
  let Cs := EdgeStep.qsCfg sy m0 v Ps
  let Cm := (pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList
  let Ce := cfgsOf sy m0 Ps.stops.toList
  let Cn := [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList]
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop && EdgeStep.rPc sy != sy.EndlessLoop && sy.UpdScrollVar != EdgeStep.rPc sy &&
    decide (nI sy m0 < 2048) && decide (pE sy m0).Nodup &&
    CtrlKeep.ctrlCheck1 (cfgPE sy m0 v q C1 Cs Cm Ps.stops.toList Ce Cn) &&
    C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSE sy m0 Cs Cm Ps.stops.toList Ce Cn) FrameKeep.fuelK) &&
    Cs.t.all (AfterKeep.walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRE sy m0 Ps.stops.toList Ce Cn) FrameKeep.fuelK) &&
    (Cm.all fun C => C.t.all (EdgeStep.walkQR C (FrameKeep.ctlI sy) (EdgeStep.rPc sy) atRkU FrameKeep.fuelK)) &&
    ((pU sy m0).all fun b => (quCfg sy m0 b Ps.stops.toList).t.all
      (walkQP (quCfg sy m0 b Ps.stops.toList) (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) sy.UpdScrollVar (atE sy m0 Ce b) FrameKeep.fuelK)) &&
    ((pE sy m0).all fun b => vSix.all fun w => (Ce.e b w).t.all (walkE sy m0 (Ce.e b w))) &&
    (Cn.all fun C => C.t.all (EdgeStep.walkKP C (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK)) &&
    ((pE sy m0).all fun b => b == cIdx sy m0 || b == gIdx sy m0 || vCol.all fun w => (Ce.e b w).t.all (walkE sy m0 (Ce.e b w))) &&
    (vCol.all fun w => cols.all fun c => (Ce.c w c).t.all (walkE sy m0 (Ce.c w c))) &&
    (vCol.all fun w => pages.all fun p => (Ce.p w p).t.all (walkE sy m0 (Ce.p w p))) &&
    ((pE sy m0).all fun b => b == nI sy m0 || b == sIdx sy m0 || (Ce.e b 0).t.all (walkE sy m0 (Ce.e b 0))) &&
    Ce.tail.t.all (walkE sy m0 Ce.tail)



/-! ## The proofs -/

section Proofs
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (guardH)

variable {sy : Syms} {m0 : Machine}

theorem sim_drop {r r' : Nat} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim { PipeEntryRule.envOf m0 with rkI := r } F B m) :
    Sim { PipeEntryRule.envOf m0 with rkI := r' } F { B with rk := false } m :=
  { hs with rkv := fun h => absurd h (by simp) }

/-- the state for the walk to the end covers the machine -/
theorem sim_startE {b : Nat} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim { PipeEntryRule.envOf m0 with rkI := b } F B m) :
    Sim (envE sy m0 b) F (startE sy m0 b B) m := by
  cases hb : (b == nI sy m0) with
  | true =>
    have e1 : rkOf sy m0 b = noRk := by unfold rkOf; rw [hb]; rfl
    have e2 : startE sy m0 b B = { B with rk := false } := by unfold startE; rw [hb]; rfl
    rw [e2]
    unfold envE
    rw [e1]
    exact sim_drop hs
  | false =>
    have e1 : rkOf sy m0 b = b := by unfold rkOf; rw [hb]; rfl
    have e2 : startE sy m0 b B = B := by unfold startE; rw [hb]; rfl
    rw [e2]
    unfold envE
    rw [e1]
    exact hs

/-- **The split of a byte by its values covers the machine, with the byte known** (as `SideFrame.cov_fill`) -/
theorem cov_fillK {E : Env} {F : Nat × UInt8} {d : Nat} (hd : d < 2048) {A : AS} {m : Machine} (hs : Sim E F A m) :
    ∃ B ∈ SideFrame.fillB d A, Sim E F B m ∧ (B.getK d).isK = true := by
  unfold SideFrame.fillB
  by_cases h : (A.getK d).isK = true
  · rw [if_pos h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, h⟩
  · rw [if_neg h]
    have hm : (A.getK d).mem (m.ram.get! d) := hs.ram d hd
    have hv : (m.ram.get! d).toNat.toUInt8 = m.ram.get! d := by simp
    refine ⟨_, List.mem_map.2 ⟨(m.ram.get! d).toNat, List.mem_filter.2 ⟨List.mem_range.2 (m.ram.get! d).toNat_lt, ?_⟩, rfl⟩, ?_, ?_⟩
    · rw [hv]
      exact SideFrame.memB_iff.2 hm
    · refine PipeEntryRule.sim_setK' hs ?_
      rw [hv]
      exact TaintRun.mem_known_self _
    · rw [RoomVert.getK_setK_self (by rw [hs.szR]; exact hd) (by rw [hs.szK]; exact hd)]
      rfl

theorem atE_rkU {Ce : Cfgs} {b : Nat} {B : AS} (h : atE sy m0 Ce b B = true) : atRkU B = true := by
  unfold atE at h
  split at h
  · simp only [atRkE, Bool.and_eq_true] at h
    exact h.1.1.1
  · exact h

/-- **The walk to the frame's end from `UpdScrollVar`**: from a state of the walk to `UpdScrollVar` for a parser's byte `b` that meets `atRkE`, with `N` at
`UpdScrollVar` in `vSix`, the frame ends in a state that meets `finE` -/
theorem end_walk {Ps' : List AS} {b : Nat} (hn : nI sy m0 < 2048)
    (ht : ∀ w ∈ vSix, (ceOf sy m0 Ps' b w).t.all (walkE sy m0 (ceOf sy m0 Ps' b w)) = true) (hQ : EdgeStep.rPc sy ≠ sy.EndlessLoop)
    {m : Machine} {i : UInt8} {k : Nat} {F : Nat × UInt8} {B : AS}
    (hat : atRkE sy m0 b (ceOf sy m0 Ps' b) B = true) (hs : Sim { PipeEntryRule.envOf m0 with rkI := b } F B (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK (guardN sy m0 b) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hv : vSix.contains ((trace m i k).ram.get! (nI sy m0)) = true) :
    ∃ Be, finE sy m0 b ((trace m i k).ram.get! (nI sy m0)) Be = true ∧ Sim (envE sy m0 b) F Be (frame m i) := by
  simp only [atRkE, Bool.and_eq_true, List.all_eq_true] at hat
  obtain ⟨_, hall⟩ := hat
  have hs1 := sim_startE (sy := sy) hs
  obtain ⟨B', hB', hs', hk'⟩ := cov_fillK hn hs1
  have hval : (trace m i k).ram.get! (nI sy m0) = (B'.getK (nI sy m0)).v := PipeEntryRule.known_eq hk' (hs'.ram _ hn)
  have hw := hall B' hB'
  rw [← hval, hk', hv] at hw
  simp only [Bool.and_self, Bool.not_true, Bool.false_or] at hw
  have htab := ht _ (List.mem_of_elem_eq_true hv)
  exact (EdgeStep.endKP (C := ceOf sy m0 Ps' b ((trace m i k).ram.get! (nI sy m0))) htab rfl rfl hQ hw hs' hf hd hcl hx hp).1

/-- the end of the walk for a byte other than `N`: the byte is that of the start of the walk -/
theorem fin_rk {b : Nat} {v : UInt8} {F : Nat × UInt8} {B : AS} {m : Machine} (hb : b ≠ nI sy m0) (hf : finE sy m0 b v B = true) (hs : Sim (envE sy m0 b) F B m) :
    m.ram.get! b = F.2 := by
  have hb' : (b == nI sy m0) = false := by simpa using hb
  have e1 : rkOf sy m0 b = b := by unfold rkOf; rw [hb']; rfl
  unfold finE at hf
  rw [hb'] at hf
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, Bool.not_eq_true'] at hf
  have e := hs.rkv hf.1
  rw [if_neg (by simp [hf.2])] at e
  have e2 : (envE sy m0 b).rkI = b := e1
  rw [e2] at e
  exact e

/-- the end of the walk for `N`: it is `v` or `v − 1` -/
theorem fin_n {v : UInt8} {F : Nat × UInt8} {B : AS} {m : Machine} (hn : nI sy m0 < 2048) (hf : finE sy m0 (nI sy m0) v B = true)
    (hs : Sim (envE sy m0 (nI sy m0)) F B m) : m.ram.get! (nI sy m0) = v ∨ m.ram.get! (nI sy m0) = v - 1 := by
  unfold finE at hf
  simp only [beq_self_eq_true, if_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
  obtain ⟨hk, h2⟩ := hf
  have e := PipeEntryRule.known_eq hk (hs.ram _ hn)
  rw [e]
  exact h2

theorem nI_mem : nI sy m0 ∈ pI sy m0 := List.mem_map.2 ⟨(places sy m0).task, List.mem_cons_self, rfl⟩

theorem nI_memE : nI sy m0 ∈ pE sy m0 := List.mem_append_left _ nI_mem

theorem pE_sub {x : Nat} (h : x ∈ pE sy m0) : x ∈ pU sy m0 := by
  unfold pE at h
  rcases List.mem_append.1 h with h | h
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    unfold EdgeStep.eI
    rcases h with h | h <;> simp [h]


theorem idx_lt (a : UInt16) : (a &&& 0x7FF).toNat < 2048 := by
  have : (a &&& 0x7FF).toNat ≤ 0x7FF := UInt16.le_iff_toNat_le.1 (UInt16.and_le_right (a := a) (b := 0x7FF))
  omega

/-- **The walk to the end for `vCol`, a byte other than the column and its page** -/
theorem end_walkO {Ce : Cfgs} {b : Nat} (hn : nI sy m0 < 2048) (hbc : b ≠ cIdx sy m0) (hbg : b ≠ gIdx sy m0)
    (ht : ∀ w ∈ vCol, (Ce.e b w).t.all (walkE sy m0 (Ce.e b w)) = true) (hQ : EdgeStep.rPc sy ≠ sy.EndlessLoop)
    (hE : ∀ w, (Ce.e b w).E = envE sy m0 b ∧ (Ce.e b w).G = guardN sy m0 b ∧ (Ce.e b w).S = FrameKeep.spotOf sy m0 ∧ (Ce.e b w).fin = finE sy m0 b w ∧
      (Ce.e b w).kl = (Ce.e b w).t.map PipeWrites.knownOf ∧ (Ce.e b w).ops = (TaintRun.aRows (Ce.e b w).E).toArray)
    {m : Machine} {i : UInt8} {k : Nat} {F : Nat × UInt8} {B : AS}
    (hat : atRkV sy m0 b Ce B = true) (hs : Sim { PipeEntryRule.envOf m0 with rkI := b } F B (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK (guardN sy m0 b) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hv : vCol.contains ((trace m i k).ram.get! (nI sy m0)) = true) :
    ∃ Be, finE sy m0 b ((trace m i k).ram.get! (nI sy m0)) Be = true ∧ Sim (envE sy m0 b) F Be (frame m i) := by
  unfold atRkV at hat
  simp only [List.all_eq_true] at hat
  have hs1 := sim_startE (sy := sy) hs
  obtain ⟨B', hB', hs', hk'⟩ := cov_fillK hn hs1
  have hval : (trace m i k).ram.get! (nI sy m0) = (B'.getK (nI sy m0)).v := PipeEntryRule.known_eq hk' (hs'.ram _ hn)
  have hw := hat B' hB'
  rw [← hval, hk', hv] at hw
  have hbc' : (b == cIdx sy m0) = false := by simpa using hbc
  have hbg' : (b == gIdx sy m0) = false := by simpa using hbg
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, hbc', hbg', Bool.false_eq_true, if_false] at hw
  have htab := ht _ (List.mem_of_elem_eq_true hv)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE ((trace m i k).ram.get! (nI sy m0))
  have hs'' : Sim (Ce.e b ((trace m i k).ram.get! (nI sy m0))).E F B' (trace m i k) := by rw [e1]; exact hs'
  have hcl' : ∀ j, FrameKeep.CleanK (Ce.e b ((trace m i k).ram.get! (nI sy m0))).G (Ce.e b ((trace m i k).ram.get! (nI sy m0))).S.store (trace m i j) := by
    rw [e2, e3]; exact hcl
  have hQ' : EdgeStep.rPc sy ≠ (Ce.e b ((trace m i k).ram.get! (nI sy m0))).G.idle := by rw [e2]; exact hQ
  obtain ⟨⟨Be, h1, h2⟩, _⟩ := EdgeStep.endKP (C := Ce.e b ((trace m i k).ram.get! (nI sy m0))) htab e5 e6 hQ' hw hs'' hf hd hcl' hx hp
  rw [e4] at h1
  rw [e1] at h2
  exact ⟨Be, h1, h2⟩


theorem mem_cols {c : UInt8} (h : c.toNat < 15) : c ∈ cols := List.mem_map.2 ⟨c.toNat, List.mem_range.2 h, by simp⟩

theorem mem_pages {p : UInt8} (h : p ≠ 255) : p ∈ pages := by
  have h1 : p.toNat ≠ 255 := fun e => h (UInt8.toNat_inj.1 (by rw [e]; rfl))
  exact List.mem_map.2 ⟨p.toNat, List.mem_range.2 (by have := p.toNat_lt; omega), by simp⟩

/-- **The walk to the end for `vCol`, the page's walk**: split by the column (below 16) and, for 15, by the page (not 255) -/
theorem end_walkG {Ps' : List AS} (hn : nI sy m0 < 2048) (hgn : gIdx sy m0 ≠ nI sy m0) (hcg : gIdx sy m0 ≠ cIdx sy m0)
    (htc : ∀ w ∈ vCol, ∀ c ∈ cols, ((cfgsOf sy m0 Ps').c w c).t.all (walkE sy m0 ((cfgsOf sy m0 Ps').c w c)) = true)
    (htp : ∀ w ∈ vCol, ∀ p ∈ pages, ((cfgsOf sy m0 Ps').p w p).t.all (walkE sy m0 ((cfgsOf sy m0 Ps').p w p)) = true)
    (hQ : EdgeStep.rPc sy ≠ sy.EndlessLoop)
    {m : Machine} {i : UInt8} {k : Nat} {F : Nat × UInt8} {B : AS}
    (hat : atRkV sy m0 (gIdx sy m0) (cfgsOf sy m0 Ps') B = true) (hs : Sim { PipeEntryRule.envOf m0 with rkI := gIdx sy m0 } F B (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hclg : ∀ j, FrameKeep.CleanK (guardN sy m0 (gIdx sy m0)) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hcln : ∀ j, FrameKeep.CleanK (guardN sy m0 (nI sy m0)) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hv : vCol.contains ((trace m i k).ram.get! (nI sy m0)) = true) (hc16 : ((trace m i k).ram.get! (cIdx sy m0)).toNat < 16)
    (hp255 : (trace m i k).ram.get! (gIdx sy m0) ≠ 255) :
    (((trace m i k).ram.get! (cIdx sy m0)).toNat < 15 → (frame m i).ram.get! (gIdx sy m0) = F.2 ∧
      (((frame m i).ram.get! (nI sy m0) = (trace m i k).ram.get! (nI sy m0) ∧ (frame m i).ram.get! (cIdx sy m0) = (trace m i k).ram.get! (cIdx sy m0)) ∨
       ((frame m i).ram.get! (nI sy m0) = (trace m i k).ram.get! (nI sy m0) - 1 ∧ (frame m i).ram.get! (cIdx sy m0) = (trace m i k).ram.get! (cIdx sy m0) + 1))) ∧
    ((trace m i k).ram.get! (cIdx sy m0) = 15 →
      ((frame m i).ram.get! (nI sy m0) = (trace m i k).ram.get! (nI sy m0) ∧ (frame m i).ram.get! (cIdx sy m0) = 15 ∧
          (frame m i).ram.get! (gIdx sy m0) = (trace m i k).ram.get! (gIdx sy m0)) ∨
        ((frame m i).ram.get! (nI sy m0) = (trace m i k).ram.get! (nI sy m0) - 1 ∧ (frame m i).ram.get! (cIdx sy m0) = 0 ∧
          (frame m i).ram.get! (gIdx sy m0) = (trace m i k).ram.get! (gIdx sy m0) + 1)) := by
  have hc : cIdx sy m0 < 2048 := idx_lt _
  have hg : gIdx sy m0 < 2048 := idx_lt _
  unfold atRkV at hat
  simp only [List.all_eq_true] at hat
  have hs1 := sim_startE (sy := sy) hs
  obtain ⟨B', hB', hs', hk'⟩ := cov_fillK hn hs1
  have hval : (trace m i k).ram.get! (nI sy m0) = (B'.getK (nI sy m0)).v := PipeEntryRule.known_eq hk' (hs'.ram _ hn)
  have hw := hat B' hB'
  rw [← hval, hk', hv] at hw
  have hgc' : (gIdx sy m0 == cIdx sy m0) = false := by simpa using hcg
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, hgc', beq_self_eq_true, Bool.false_eq_true, if_false, if_true, List.all_eq_true] at hw
  obtain ⟨B'', hB'', hs'', hk''⟩ := cov_fillK hc hs'
  have hvc : (trace m i k).ram.get! (cIdx sy m0) = (B''.getK (cIdx sy m0)).v := PipeEntryRule.known_eq hk'' (hs''.ram _ hc)
  have hw2 := hw B'' hB''
  rw [← hvc, hk''] at hw2
  have h16 : decide (15 < ((trace m i k).ram.get! (cIdx sy m0)).toNat) = false := by simp; omega
  rw [h16] at hw2
  simp only [Bool.not_true, Bool.false_or] at hw2
  have hgr : rkOf sy m0 (gIdx sy m0) = gIdx sy m0 := by
    have : (gIdx sy m0 == nI sy m0) = false := by simpa using hgn
    unfold rkOf; rw [this]; rfl
  refine ⟨fun hlt => ?_, fun h15 => ?_⟩
  · have hne : ((trace m i k).ram.get! (cIdx sy m0) == 15) = false := by
      have : (trace m i k).ram.get! (cIdx sy m0) ≠ 15 := fun e => by rw [e] at hlt; simp at hlt
      simpa using this
    rw [hne] at hw2
    simp only [Bool.false_eq_true, if_false] at hw2
    have htab := htc _ (List.mem_of_elem_eq_true hv) _ (mem_cols hlt)
    obtain ⟨⟨Be, h1, h2⟩, _⟩ := EdgeStep.endKP (C := (cfgsOf sy m0 Ps').c ((trace m i k).ram.get! (nI sy m0)) ((trace m i k).ram.get! (cIdx sy m0)))
      htab rfl rfl hQ hw2 hs'' hf hd hclg hx hp
    simp only [cfgsOf, qfCfg, finC, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨⟨⟨hrk, hsp⟩, hkn⟩, hkc⟩, hor⟩ := h1
    have en := PipeEntryRule.known_eq hkn (h2.ram _ hn)
    have ec := PipeEntryRule.known_eq hkc (h2.ram _ hc)
    have eg := h2.rkv hrk
    rw [if_neg (by simp [hsp])] at eg
    have eg' : ((cfgsOf sy m0 Ps').c ((trace m i k).ram.get! (nI sy m0)) ((trace m i k).ram.get! (cIdx sy m0))).E.rkI = gIdx sy m0 := hgr
    rw [eg'] at eg
    refine ⟨eg, ?_⟩
    rw [en, ec]
    exact hor
  · rw [h15] at hw2
    simp only [beq_self_eq_true, if_true, List.all_eq_true] at hw2
    have hsd : Sim (envE sy m0 (nI sy m0)) F { B'' with rk := false } (trace m i k) := by
      unfold envE
      unfold envE at hs''
      exact sim_drop hs''
    obtain ⟨B3, hB3, hs3, hk3⟩ := cov_fillK hg hsd
    have hvg : (trace m i k).ram.get! (gIdx sy m0) = (B3.getK (gIdx sy m0)).v := PipeEntryRule.known_eq hk3 (hs3.ram _ hg)
    have hw3 := hw2 B3 hB3
    rw [← hvg, hk3] at hw3
    have hne : ((trace m i k).ram.get! (gIdx sy m0) == 255) = false := by simpa using hp255
    rw [hne] at hw3
    simp only [Bool.not_true, Bool.false_or] at hw3
    have htab := htp _ (List.mem_of_elem_eq_true hv) _ (mem_pages hp255)
    obtain ⟨⟨Be, h1, h2⟩, _⟩ := EdgeStep.endKP (C := (cfgsOf sy m0 Ps').p ((trace m i k).ram.get! (nI sy m0)) ((trace m i k).ram.get! (gIdx sy m0)))
      htab rfl rfl hQ hw3 hs3 hf hd hcln hx hp
    simp only [cfgsOf, qfCfg, finP, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨⟨hkn, hkc⟩, hkg⟩, hor⟩ := h1
    have en := PipeEntryRule.known_eq hkn (h2.ram _ hn)
    have ec := PipeEntryRule.known_eq hkc (h2.ram _ hc)
    have eg := PipeEntryRule.known_eq hkg (h2.ram _ hg)
    rw [en, ec, eg]
    rcases hor with ⟨⟨a1, a2⟩, a3⟩ | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl ⟨a1, a2, a3⟩
    · exact Or.inr ⟨a1, a2, a3⟩

theorem nodup_of_check {v : UInt8} (he : eCheckP sy m0 v = true) : (pE sy m0).Nodup := by
  simp only [eCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at he
  exact he.1.1.1.1.1.1.1.1.1.1.1.1.2


/-- **The walk to the end for `N` = 0, a byte other than `N` and the counter** -/
theorem end_walkZO {Ce : Cfgs} {b : Nat} (hn : nI sy m0 < 2048) (hbn : b ≠ nI sy m0) (hbs : b ≠ sIdx sy m0)
    (ht : (Ce.e b 0).t.all (walkE sy m0 (Ce.e b 0)) = true) (hQ : EdgeStep.rPc sy ≠ sy.EndlessLoop)
    (hE : (Ce.e b 0).E = envE sy m0 b ∧ (Ce.e b 0).G = guardN sy m0 b ∧ (Ce.e b 0).S = FrameKeep.spotOf sy m0 ∧ (Ce.e b 0).fin = finE sy m0 b 0 ∧
      (Ce.e b 0).kl = (Ce.e b 0).t.map PipeWrites.knownOf ∧ (Ce.e b 0).ops = (TaintRun.aRows (Ce.e b 0).E).toArray)
    {m : Machine} {i : UInt8} {k : Nat} {F : Nat × UInt8} {B : AS}
    (hat : atRkZ sy m0 b Ce Ce.tail B = true) (hs : Sim { PipeEntryRule.envOf m0 with rkI := b } F B (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK (guardN sy m0 b) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hv : (trace m i k).ram.get! (nI sy m0) = 0) :
    ∃ Be, finE sy m0 b 0 Be = true ∧ Sim (envE sy m0 b) F Be (frame m i) := by
  unfold atRkZ at hat
  simp only [List.all_eq_true] at hat
  have hs1 := sim_startE (sy := sy) hs
  obtain ⟨B', hB', hs', hk'⟩ := cov_fillK hn hs1
  have hval : (trace m i k).ram.get! (nI sy m0) = (B'.getK (nI sy m0)).v := PipeEntryRule.known_eq hk' (hs'.ram _ hn)
  have hw := hat B' hB'
  rw [← hval, hk', hv] at hw
  have hbn' : (b == nI sy m0) = false := by simpa using hbn
  have hbs' : (b == sIdx sy m0) = false := by simpa using hbs
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, hbn', hbs', Bool.false_eq_true, if_false] at hw
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
  have hs'' : Sim (Ce.e b 0).E F B' (trace m i k) := by rw [e1]; exact hs'
  have hcl' : ∀ j, FrameKeep.CleanK (Ce.e b 0).G (Ce.e b 0).S.store (trace m i j) := by rw [e2, e3]; exact hcl
  have hQ' : EdgeStep.rPc sy ≠ (Ce.e b 0).G.idle := by rw [e2]; exact hQ
  obtain ⟨⟨Be, h1, h2⟩, _⟩ := EdgeStep.endKP (C := Ce.e b 0) ht e5 e6 hQ' hw hs'' hf hd hcl' hx hp
  rw [e4] at h1
  rw [e1] at h2
  exact ⟨Be, h1, h2⟩

/-- **The walk of the counter for `N` = 0**: split by the counter's value `s`, the head's walk to the frame's end (`N` 0, the counter `s`) or to the task
handler's call, and from there the walk with the counter followed (`N` 7, the counter `s − 32`) -/
theorem end_walkZS {Ce : Cfgs} (hn : nI sy m0 < 2048) (hsn : sIdx sy m0 ≠ nI sy m0)
    (htT : Ce.tail.t.all (walkE sy m0 Ce.tail) = true) (hQ : EdgeStep.rPc sy ≠ sy.EndlessLoop)
    (hT : Ce.tail.E = envE sy m0 (sIdx sy m0) ∧ Ce.tail.G = guardN sy m0 (sIdx sy m0) ∧ Ce.tail.S = FrameKeep.spotOf sy m0 ∧ Ce.tail.fin = finT sy m0 ∧
      Ce.tail.kl = Ce.tail.t.map PipeWrites.knownOf ∧ Ce.tail.ops = (TaintRun.aRows Ce.tail.E).toArray)
    {m : Machine} {i : UInt8} {k : Nat} {F : Nat × UInt8} {B : AS}
    (hat : atRkZ sy m0 (sIdx sy m0) Ce Ce.tail B = true) (hs : Sim { PipeEntryRule.envOf m0 with rkI := sIdx sy m0 } F B (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcls : ∀ j, FrameKeep.CleanK (guardN sy m0 (sIdx sy m0)) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hcln : ∀ j, FrameKeep.CleanK (guardN sy m0 (nI sy m0)) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hv : (trace m i k).ram.get! (nI sy m0) = 0) :
    ((frame m i).ram.get! (nI sy m0) = 0 ∧ (frame m i).ram.get! (sIdx sy m0) = (trace m i k).ram.get! (sIdx sy m0)) ∨
    (32 ≤ ((trace m i k).ram.get! (sIdx sy m0)).toNat ∧ ((trace m i k).ram.get! (sIdx sy m0)).toNat < 160 ∧ (frame m i).ram.get! (nI sy m0) = 7 ∧
      (frame m i).ram.get! (sIdx sy m0) = (trace m i k).ram.get! (sIdx sy m0) - 32) := by
  have hsl : sIdx sy m0 < 2048 := idx_lt _
  unfold atRkZ at hat
  simp only [List.all_eq_true] at hat
  have hs1 := sim_startE (sy := sy) hs
  obtain ⟨B', hB', hs', hk'⟩ := cov_fillK hn hs1
  have hval : (trace m i k).ram.get! (nI sy m0) = (B'.getK (nI sy m0)).v := PipeEntryRule.known_eq hk' (hs'.ram _ hn)
  have hw := hat B' hB'
  rw [← hval, hk', hv] at hw
  have hsn' : (sIdx sy m0 == nI sy m0) = false := by simpa using hsn
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or, hsn', Bool.false_eq_true, if_false, if_true, List.all_eq_true] at hw
  have hsd : Sim (envE sy m0 (nI sy m0)) F { B' with rk := false } (trace m i k) := by
    unfold envE
    unfold envE at hs'
    exact sim_drop hs'
  obtain ⟨B'', hB'', hs'', hk''⟩ := cov_fillK hsl hsd
  have hvs : (trace m i k).ram.get! (sIdx sy m0) = (B''.getK (sIdx sy m0)).v := PipeEntryRule.known_eq hk'' (hs''.ram _ hsl)
  have hw2 := hw B'' hB''
  rw [← hvs, hk''] at hw2
  simp only [Bool.not_true, Bool.false_or] at hw2
  have hrs : rkOf sy m0 (sIdx sy m0) = sIdx sy m0 := by unfold rkOf; rw [hsn']; rfl
  rcases endEQ (C := headCfg sy m0 ((trace m i k).ram.get! (sIdx sy m0))) (Fu := FrameKeep.fuelK) (by simp [headCfg, emptyCfg]) (by simp [headCfg, emptyCfg]) rfl hw2 hs'' hf hd hcln hx hp with
    ⟨Be, h1, h2⟩ | ⟨k', hk', hq', hf', hd', BQ, hat0, hsQ⟩
  · simp only [headCfg, emptyCfg, fin0, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h1
    have en := PipeEntryRule.known_eq a1 (h2.ram _ hn)
    have es := PipeEntryRule.known_eq a2 (h2.ram _ hsl)
    exact Or.inl ⟨by rw [en, a3], by rw [es, a4]⟩
  · simp only [at0, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hat0
    obtain ⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩ := hat0
    have esQ := PipeEntryRule.known_eq b3 (hsQ.ram _ hsl)
    have hsR := AfterKeep.sim_rkOn (b := sIdx sy m0) hsQ
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hT
    have hsR' : Sim Ce.tail.E (F.1, (trace m i k').ram.get! (sIdx sy m0)) (AfterKeep.rkOn BQ) (trace m i k') := by
      rw [e1]
      unfold envE
      rw [hrs]
      simpa using hsR
    have hcl' : ∀ j, FrameKeep.CleanK Ce.tail.G Ce.tail.S.store (trace m i j) := by rw [e2, e3]; exact hcls
    have hQ' : EdgeStep.rPc sy ≠ Ce.tail.G.idle := by rw [e2]; exact hQ
    obtain ⟨⟨Be, h1, h2⟩, _⟩ := EdgeStep.endKP (C := Ce.tail) htT e5 e6 hQ' b5 hsR' hf' hd' hcl' hx (fun j hj hfj => hp j (by omega) hfj)
    rw [e4] at h1
    simp only [finT, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h1
    obtain ⟨⟨⟨hrk, hsp⟩, hkn⟩, h7⟩ := h1
    have en := PipeEntryRule.known_eq hkn (h2.ram _ hn)
    have es := h2.rkv hrk
    rw [if_neg (by simp [hsp])] at es
    have er : Ce.tail.E.rkI = sIdx sy m0 := by rw [e1]; exact hrs
    rw [er] at es
    refine Or.inr ⟨b1, b2, by rw [en, h7], ?_⟩
    rw [es, esQ, b4, hvs]

/-- **A frame in control from the scroll handler to `UpdScrollVar`, and on to its end.** The conclusions of `keep_uP` (by the same walks, with `atE` at
`UpdScrollVar`), and with `N` at that `UpdScrollVar` (`k₂`): for `vSix`, at the frame's end the bytes of `pE` but `N` are those at `k₂`, and `N` is that at `k₂` or
one less; for `vCol`, the counter and the edge are those at `k₂`, and `ColEnd` (for the column below 16 and the page not 255); for 0, the column, the page and the
edge are those at `k₂`, and `N` and the counter kept, or `32 ≤ S < 160`, `N` 7 and the counter less 32. The conditions of `keep_uP`, and `CleanK` of `guardN` for
each byte of `pE` (`hN`: no store through an index or a pointer writes the byte, `N`, the column or the page). `hc`, `he` are the checks on the ROM. -/
theorem keep_eP (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (he : eCheckP sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
    ∃ k₁, kq < k₁ ∧ (trace m i k₁).pc = EdgeStep.rPc sy ∧ (trace m i k₁).frame = m.frame ∧ (∀ j, kq < j → j < k₁ → (trace m i j).pc ≠ EdgeStep.rPc sy) ∧
      (∀ x ∈ pK sy m0, (trace m i k₁).ram.get! x = (trace m i kq).ram.get! x) ∧
      ((∀ j, kq ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false) →
        (∀ n, kq < n → (trace m i n).pc = EdgeStep.rPc sy → n = k₁) ∧
        ∃ k₂, k₁ < k₂ ∧ (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧ (∀ j, k₁ < j → j < k₂ → (trace m i j).pc ≠ sy.UpdScrollVar) ∧
          (∀ x ∈ pU sy m0, (trace m i k₂).ram.get! x = (trace m i k₁).ram.get! x) ∧
          (vSix.contains ((trace m i k₂).ram.get! (nI sy m0)) = true →
            (∀ x ∈ pE sy m0, x ≠ nI sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
            ((frame m i).ram.get! (nI sy m0) = (trace m i k₂).ram.get! (nI sy m0) ∨
              (frame m i).ram.get! (nI sy m0) = (trace m i k₂).ram.get! (nI sy m0) - 1)) ∧
          (vCol.contains ((trace m i k₂).ram.get! (nI sy m0)) = true →
            (∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ cIdx sy m0 → x ≠ gIdx sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
            (((trace m i k₂).ram.get! (cIdx sy m0)).toNat < 16 → (trace m i k₂).ram.get! (gIdx sy m0) ≠ 255 → ColEnd sy m0 (trace m i k₂) (frame m i))) ∧
          ((trace m i k₂).ram.get! (nI sy m0) = 0 →
            (∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ sIdx sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
            (((frame m i).ram.get! (nI sy m0) = 0 ∧ (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0)) ∨
              (32 ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat ∧ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat < 160 ∧ (frame m i).ram.get! (nI sy m0) = 7 ∧
                (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) - 32)))) := by
  have hnd := nodup_of_check he
  rw [pE_eq] at hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨nns, _, ngn, _, _⟩, ⟨_, _, _, _⟩, ⟨ncg, _, _⟩, _⟩ := hnd
  simp only [eCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hne3⟩, _⟩, hn⟩, _⟩, hp1⟩, hp2⟩, hp3⟩, hp4⟩, hp5⟩, hp6⟩, hp7⟩, hp8⟩, hp9⟩, hp10⟩, hp11⟩, hp12⟩ := he
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  generalize EdgeStep.qsSearch sy m0 v P.stops.toList = Ps at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
  rcases CtrlKeep.cut_or_end2 (C := cfgPE sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (EdgeStep.qsCfg sy m0 v Ps) ((pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList)
      Ps.stops.toList (cfgsOf sy m0 Ps.stops.toList) [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList]) hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs
        (atSE sy m0 (EdgeStep.qsCfg sy m0 v Ps) ((pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList) Ps.stops.toList (cfgsOf sy m0 Ps.stops.toList)
          [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList])
        FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hcl hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, ?_⟩
    simp only [atSE, Bool.and_eq_true, List.all_eq_true] at hatq
    obtain ⟨hw1, hwm⟩ := hatq
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hb1, B₁, hat1, hs1⟩ :=
      AfterKeep.q1_run (C := EdgeStep.qsCfg sy m0 v Ps) hp3 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw1 hsq hfq hdq hcl hx'
    refine ⟨k₁, hk1, hq1, hf1, hb1, ?_, ?_⟩
    · intro x hxK
      have hmem : qmCfg sy m0 v x P.stops.toList ∈ (pK sy m0).map fun b => qmCfg sy m0 v b P.stops.toList := List.mem_map.2 ⟨x, hxK, rfl⟩
      have hw2 := hwm _ hmem
      have ht2 := List.all_eq_true.1 hp4 _ hmem
      have hs2 : TaintRun.Sim (qmCfg sy m0 v x P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i kq).ram.get! x) (AfterKeep.rkOn Bq) (trace m i kq) :=
        AfterKeep.sim_rkOn hsq
      obtain ⟨k₁', hk1', hq1', _, _, hb1', B₂, hat2, hs₂⟩ :=
        EdgeStep.qR_run (C := qmCfg sy m0 v x P.stops.toList) ht2 rfl rfl hw2 hs2 hfq hdq (hH x (pU_sub (pK_sub hxK))) hx'
      have e1 : k₁' = k₁ := first_eq hk1' hq1' hb1' hk1 hq1 hb1
      subst e1
      simp only [atRkU, Bool.and_eq_true, Bool.not_eq_true'] at hat2
      have e := hs₂.rkv hat2.1
      rw [if_neg (by simp [hat2.2])] at e
      exact e
    · intro hp
      simp only [atRE, Bool.and_eq_true, List.all_eq_true] at hat1
      obtain ⟨hatU, hatN⟩ := hat1
      -- no second arrival at the instruction after the call: the walk of `EdgeStep` to the frame's end
      have huniq : ∀ n, kq < n → (trace m i n).pc = EdgeStep.rPc sy → n = k₁ := by
        have hmem : EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList ∈ [EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList] := List.mem_singleton.2 rfl
        have hw2 := hatN _ hmem
        have ht2 := List.all_eq_true.1 hp7 _ hmem
        have hs2 : TaintRun.Sim (EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (e0 sy m0))
            (AfterKeep.rkOn B₁) (trace m i k₁) := AfterKeep.sim_rkOn hs1
        obtain ⟨_, hnoQ⟩ := EdgeStep.endKP (C := EdgeStep.q2CfgR sy m0 (e0 sy m0) Ps.stops.toList) ht2 rfl rfl hne3 hw2 hs2 hf1 hd1 (hH _ e0_mem) hx'
          (fun j hj hfj => hp j (by omega) hfj)
        intro n hn' hrp
        rcases Nat.lt_trichotomy n k₁ with h | h | h
        · exact absurd hrp (hb1 n hn' h)
        · exact h
        · exfalso
          have := hnoQ (n - k₁) (by omega)
          rw [show k₁ + (n - k₁) = n by omega] at this
          exact this hrp
      refine ⟨huniq, ?_⟩
      have run : ∀ x ∈ pU sy m0, ∃ k₂, k₁ < k₂ ∧ (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧
          (∀ j, k₁ < j → j < k₂ → (trace m i j).pc ≠ sy.UpdScrollVar) ∧ (trace m i k₂).ram.get! x = (trace m i k₁).ram.get! x ∧
          (x ∈ pE sy m0 → vSix.contains ((trace m i k₂).ram.get! (nI sy m0)) = true →
            (x ≠ nI sy m0 → (frame m i).ram.get! x = (trace m i k₁).ram.get! x) ∧
            (x = nI sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! (nI sy m0) ∨
              (frame m i).ram.get! x = (trace m i k₂).ram.get! (nI sy m0) - 1)) ∧
          (x ∈ pE sy m0 → vCol.contains ((trace m i k₂).ram.get! (nI sy m0)) = true →
            (x ≠ nI sy m0 → x ≠ cIdx sy m0 → x ≠ gIdx sy m0 → (frame m i).ram.get! x = (trace m i k₁).ram.get! x) ∧
            (x = gIdx sy m0 → ((trace m i k₂).ram.get! (cIdx sy m0)).toNat < 16 → (trace m i k₂).ram.get! (gIdx sy m0) ≠ 255 →
              ColEnd sy m0 (trace m i k₂) (frame m i))) ∧
          (x ∈ pE sy m0 → (trace m i k₂).ram.get! (nI sy m0) = 0 →
            (x ≠ nI sy m0 → x ≠ sIdx sy m0 → (frame m i).ram.get! x = (trace m i k₁).ram.get! x) ∧
            (x = sIdx sy m0 → ((frame m i).ram.get! (nI sy m0) = 0 ∧ (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∨
              (32 ≤ ((trace m i k₂).ram.get! x).toNat ∧ ((trace m i k₂).ram.get! x).toNat < 160 ∧ (frame m i).ram.get! (nI sy m0) = 7 ∧
                (frame m i).ram.get! x = (trace m i k₂).ram.get! x - 32))) := by
        intro x hxI
        have hw2 := hatU x hxI
        have ht2 := List.all_eq_true.1 hp5 x hxI
        have hs2 : TaintRun.Sim (quCfg sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (AfterKeep.rkOn B₁) (trace m i k₁) :=
          AfterKeep.sim_rkOn hs1
        obtain ⟨k₂, hk2, hq2, hf2, hd2, hb2, B₂, hat2, hs₂⟩ := qP_run (C := quCfg sy m0 x Ps.stops.toList) ht2 rfl rfl hw2 hs2 hf1 hd1 (hH x hxI) hx'
          (fun j hj hfj => hp j (by omega) hfj)
        have hat2' := atE_rkU hat2
        simp only [atRkU, Bool.and_eq_true, Bool.not_eq_true'] at hat2'
        have e := hs₂.rkv hat2'.1
        rw [if_neg (by simp [hat2'.2])] at e
        refine ⟨k₂, hk2, hq2, hf2, hb2, e, fun hxP hsix => ?_, fun hxP hcol => ?_, fun hxP hz => ?_⟩
        rotate_left 2
        · have hcon : (pE sy m0).contains x = true := List.elem_eq_true_of_mem hxP
          have hatZ : atRkZ sy m0 x (cfgsOf sy m0 Ps.stops.toList) (cfgsOf sy m0 Ps.stops.toList).tail B₂ = true := by
            unfold atE at hat2
            rw [if_pos hcon] at hat2
            simp only [Bool.and_eq_true] at hat2
            exact hat2.2
          refine ⟨fun hne hns => ?_, fun heq => ?_⟩
          · have hor := List.all_eq_true.1 hp11 x hxP
            have hn' : (x == nI sy m0) = false := by simpa using hne
            have hs' : (x == sIdx sy m0) = false := by simpa using hns
            simp only [hn', hs', Bool.false_or] at hor
            obtain ⟨Be, hfin, hse⟩ := end_walkZO hn hne hns hor hne3 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hatZ hs₂ hf2 (by omega) (hN x hxP) hx'
              (fun j hj hfj => hp j (by omega) hfj) hz
            exact fin_rk hne hfin hse
          · subst heq
            exact end_walkZS hn (Ne.symm nns) hp12 hne3 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hatZ hs₂ hf2 (by omega) (hN _ hxP) (hN _ nI_memE) hx'
              (fun j hj hfj => hp j (by omega) hfj) hz
        rotate_left
        · have hcon : (pE sy m0).contains x = true := List.elem_eq_true_of_mem hxP
          have hatV : atRkV sy m0 x (cfgsOf sy m0 Ps.stops.toList) B₂ = true := by
            unfold atE at hat2
            rw [if_pos hcon] at hat2
            simp only [Bool.and_eq_true] at hat2
            exact hat2.1.2
          refine ⟨fun hne hnc hng => ?_, fun heq hc16 hp255 => ?_⟩
          · have hor := List.all_eq_true.1 hp8 x hxP
            have hc' : (x == cIdx sy m0) = false := by simpa using hnc
            have hg' : (x == gIdx sy m0) = false := by simpa using hng
            simp only [hc', hg', Bool.false_or] at hor
            have htab : ∀ w ∈ vCol, ((cfgsOf sy m0 Ps.stops.toList).e x w).t.all (walkE sy m0 ((cfgsOf sy m0 Ps.stops.toList).e x w)) = true :=
              fun w hw => List.all_eq_true.1 hor w hw
            obtain ⟨Be, hfin, hse⟩ := end_walkO hn hnc hng htab hne3 (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) hatV hs₂ hf2 (by omega) (hN x hxP) hx'
              (fun j hj hfj => hp j (by omega) hfj) hcol
            exact fin_rk hne hfin hse
          · subst heq
            have htc : ∀ w ∈ vCol, ∀ c ∈ cols, ((cfgsOf sy m0 Ps.stops.toList).c w c).t.all (walkE sy m0 ((cfgsOf sy m0 Ps.stops.toList).c w c)) = true :=
              fun w hw c hc => List.all_eq_true.1 (List.all_eq_true.1 hp9 w hw) c hc
            have htp : ∀ w ∈ vCol, ∀ p ∈ pages, ((cfgsOf sy m0 Ps.stops.toList).p w p).t.all (walkE sy m0 ((cfgsOf sy m0 Ps.stops.toList).p w p)) = true :=
              fun w hw p hp' => List.all_eq_true.1 (List.all_eq_true.1 hp10 w hw) p hp'
            obtain ⟨G1, G2⟩ := end_walkG hn (Ne.symm ngn) (Ne.symm ncg) htc htp hne3 hatV hs₂ hf2 (by omega) (hN _ hxP) (hN _ nI_memE) hx'
              (fun j hj hfj => hp j (by omega) hfj) hcol hc16 hp255
            refine ⟨fun hlt => ?_, G2⟩
            obtain ⟨g1, g2⟩ := G1 hlt
            exact ⟨g1.trans e.symm, g2⟩
        have hcon : (pE sy m0).contains x = true := List.elem_eq_true_of_mem hxP
        have hatR : atRkE sy m0 x ((cfgsOf sy m0 Ps.stops.toList).e x) B₂ = true := by
          unfold atE at hat2
          rw [if_pos hcon] at hat2
          simp only [Bool.and_eq_true] at hat2
          exact hat2.1.1
        have htab : ∀ w ∈ vSix, ((cfgsOf sy m0 Ps.stops.toList).e x w).t.all (walkE sy m0 ((cfgsOf sy m0 Ps.stops.toList).e x w)) = true :=
          fun w hw => List.all_eq_true.1 (List.all_eq_true.1 hp6 x hxP) w hw
        obtain ⟨Be, hfin, hse⟩ := end_walk hn htab hne3 hatR hs₂ hf2 (by omega) (hN x hxP) hx' (fun j hj hfj => hp j (by omega) hfj) hsix
        refine ⟨fun hne => fin_rk hne hfin hse, fun heq => ?_⟩
        subst heq
        exact fin_n hn hfin hse
      have h0x : e0 sy m0 ∈ pU sy m0 := e0_mem
      obtain ⟨k₂, hk2, hq2, hf2, hb2, _, _, _⟩ := run _ h0x
      have same : ∀ x ∈ pU sy m0, ∀ k₂', k₁ < k₂' → (trace m i k₂').pc = sy.UpdScrollVar → (∀ j, k₁ < j → j < k₂' → (trace m i j).pc ≠ sy.UpdScrollVar) →
          k₂' = k₂ := fun _ _ k₂' a b c => first_eq a b c hk2 hq2 hb2
      refine ⟨k₂, hk2, hq2, hf2, hb2, fun x hxI => ?_, fun hsix => ⟨fun x hxP hne => ?_, ?_⟩, fun hcol => ⟨fun x hxP hne hnc hng => ?_, ?_⟩,
        fun hz => ⟨fun x hxP hne hns => ?_, ?_⟩⟩
      · obtain ⟨k₂', hk2', hq2', _, hb2', e, _⟩ := run x hxI
        rw [← same x hxI k₂' hk2' hq2' hb2']
        exact e
      · obtain ⟨k₂', hk2', hq2', _, hb2', e, hend, _⟩ := run x (pE_sub hxP)
        have e2 := same x (pE_sub hxP) k₂' hk2' hq2' hb2'
        subst e2
        rw [(hend hxP hsix).1 hne, e]
      · obtain ⟨k₂', hk2', hq2', _, hb2', _, hend, _, _⟩ := run _ (pU_sub nI_mem)
        have e2 := same _ (pU_sub nI_mem) k₂' hk2' hq2' hb2'
        subst e2
        exact (hend nI_memE hsix).2 rfl
      · obtain ⟨k₂', hk2', hq2', _, hb2', e, _, hend, _⟩ := run x (pE_sub hxP)
        have e2 := same x (pE_sub hxP) k₂' hk2' hq2' hb2'
        subst e2
        rw [(hend hxP hcol).1 hne hnc hng, e]
      · have hgE : gIdx sy m0 ∈ pE sy m0 := by rw [pE_eq]; simp
        obtain ⟨k₂', hk2', hq2', _, hb2', _, _, hend, _⟩ := run _ (pE_sub hgE)
        have e2 := same _ (pE_sub hgE) k₂' hk2' hq2' hb2'
        subst e2
        exact (hend hgE hcol).2 rfl
      · obtain ⟨k₂', hk2', hq2', _, hb2', e, _, _, hend⟩ := run x (pE_sub hxP)
        have e2 := same x (pE_sub hxP) k₂' hk2' hq2' hb2'
        subst e2
        rw [(hend hxP hz).1 hne hns, e]
      · have hsE : sIdx sy m0 ∈ pE sy m0 := by rw [pE_eq]; simp
        obtain ⟨k₂', hk2', hq2', _, hb2', _, _, _, hend⟩ := run _ (pE_sub hsE)
        have e2 := same _ (pE_sub hsE) k₂' hk2' hq2' hb2'
        subst e2
        exact (hend hsE hz).2 rfl
  · exact absurd harr (hno n₀ hf0)


theorem nI_memK : nI sy m0 ∈ pK sy m0 := List.mem_map.2 ⟨(places sy m0).task, List.mem_cons_self, rfl⟩


/-- **A frame in control, from its start to its end**: the conclusions of `frame_toU`, and the end facts of `keep_eP` for `N` at the frame's start (equal to `N`
at `UpdScrollVar`). The conditions of `frame_toU` (with `eCheckP` in place of `uCheckP`), and `CleanK` of `guardN` for each byte of `pE` (`hN`). -/
theorem frame_six (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false) :
    ∃ k₂, (trace m i k₂).pc = sy.UpdScrollVar ∧ (trace m i k₂).frame = m.frame ∧
      (∀ x ∈ pK sy m0, (trace m i k₂).ram.get! x = m.ram.get! x) ∧
      ((ScrollRule.left16 (placesS sy m0) (trace m i k₂) = ScrollRule.left16 (placesS sy m0) m ∧
          (trace m i k₂).ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac) ∨
        (∃ Y : UInt8, ScrollRule.left16 (placesS sy m0) (trace m i k₂) = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 ∧
          ((trace m i k₂).ram.get! (placesS sy m0).frac).toNat = ((m.ram.get! (placesS sy m0).frac).toNat + Y.toNat) % 256)) ∧
      (vSix.contains (m.ram.get! (nI sy m0)) = true →
        (∀ x ∈ pE sy m0, x ≠ nI sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
        ((frame m i).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) ∨ (frame m i).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) - 1)) ∧
      (vCol.contains (m.ram.get! (nI sy m0)) = true →
        (∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ cIdx sy m0 → x ≠ gIdx sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
        ((m.ram.get! (cIdx sy m0)).toNat < 16 → m.ram.get! (gIdx sy m0) ≠ 255 → ColEnd sy m0 (trace m i k₂) (frame m i))) ∧
      (m.ram.get! (nI sy m0) = 0 →
        (∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ sIdx sy m0 → (frame m i).ram.get! x = (trace m i k₂).ram.get! x) ∧
        (((frame m i).ram.get! (nI sy m0) = 0 ∧ (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0)) ∨
          (32 ≤ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat ∧ ((trace m i k₂).ram.get! (sIdx sy m0)).toNat < 160 ∧ (frame m i).ram.get! (nI sy m0) = 7 ∧
            (frame m i).ram.get! (sIdx sy m0) = (trace m i k₂).ram.get! (sIdx sy m0) - 32))) := by
  obtain ⟨kq, hkq, hqq, hfq, hbq, k₁, hk1, hq1, hf1, hb1, hK, HU⟩ := keep_eP hc he h0 hcl hH hN hx hv harr hf0 hfirst
  have HQ := keep_qP hc hq h0 hcl (fun x hx j => hH x (pU_sub hx) j) hx hv harr hf0 hfirst (Nat.le_of_lt hkq) hqq hbq
  have HE := EdgeStep.keep_q hc hqe h0 hcl (fun x hx j => hH x (List.mem_append_right _ hx) j) hx hv harr hf0 hfirst (Nat.le_of_lt hkq) hqq hbq
  have hgQ := (HQ _ s_memI).1
  obtain ⟨k, _, pcR, _, L, ifr⟩ := scroll_callS hs hgQ hqq
  have eq := FrameModel.trace_inFrame hidle hfq ifr ht k (Nat.le_refl _)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with e | e
    · exfalso
      subst e
      have e2 : (FrameModel.stepN 0 (trace m i kq)).pc = sy.PlayerSubs := hqq
      rw [pcR] at e2
      have e3 := congrArg UInt16.toNat e2
      simp only [UInt16.toNat_add] at e3
      have e4 : (3 : UInt16).toNat = 3 := rfl
      rw [e4] at e3
      have := sy.PlayerSubs.toNat_lt
      omega
    · exact e
  obtain ⟨huniq, k₂, _, hq2, hf2, _, hU, hEnd⟩ := HU (fun j hj hfj => hp kq (Nat.le_of_lt hkq) hqq j hj hfj)
  have e1 : kq + k = k₁ := huniq (kq + k) (by omega) (by rw [eq.1]; exact pcR)
  have hk₁ : trace m i k₁ = FrameModel.stepN k (trace m i kq) := by rw [← e1]; exact eq.1
  have hKm : ∀ x ∈ pK sy m0, (trace m i k₂).ram.get! x = m.ram.get! x := by
    intro x hx
    rw [hU x (pU_sub (pK_sub hx)), hK x hx]
    exact (HQ x (pK_sub hx)).2
  have hcK : (trace m i k₂).ram.get! (cIdx sy m0) = m.ram.get! (cIdx sy m0) :=
    hKm _ (List.mem_map.2 ⟨(places sy m0).col, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hgK : (trace m i k₂).ram.get! (gIdx sy m0) = m.ram.get! (gIdx sy m0) :=
    hKm _ (List.mem_map.2 ⟨(places sy m0).page, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  refine ⟨k₂, hq2, hf2, hKm, ?_, fun hsix => ?_, fun hcol => ?_, fun hz => ?_⟩
  · have lx2 : (trace m i k₂).ram.get! (placesS sy m0).lx = (trace m i k₁).ram.get! (placesS sy m0).lx := hU _ lx_mem
    have lp2 : (trace m i k₂).ram.get! (placesS sy m0).lp = (trace m i k₁).ram.get! (placesS sy m0).lp := hU _ lp_mem
    have s2 : (trace m i k₂).ram.get! (placesS sy m0).frac = (trace m i k₁).ram.get! (placesS sy m0).frac := hU _ (pU_sub s_memI)
    have lxq : (trace m i kq).ram.get! (placesS sy m0).lx = m.ram.get! (placesS sy m0).lx := (HE _ List.mem_cons_self).2
    have lpq : (trace m i kq).ram.get! (placesS sy m0).lp = m.ram.get! (placesS sy m0).lp := (HE _ (List.mem_cons_of_mem _ List.mem_cons_self)).2
    have sq : (trace m i kq).ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac := (HQ _ s_memI).2
    have L2 : ScrollRule.left16 (placesS sy m0) (trace m i k₂) = ScrollRule.left16 (placesS sy m0) (FrameModel.stepN k (trace m i kq)) := by
      unfold ScrollRule.left16
      rw [lx2, lp2, hk₁]
    have Lq : ScrollRule.left16 (placesS sy m0) (trace m i kq) = ScrollRule.left16 (placesS sy m0) m := by
      unfold ScrollRule.left16
      rw [lxq, lpq]
    rw [L2, s2, hk₁, ← Lq, ← sq]
    exact L
  · have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hKm _ nI_memK
    rw [← hn2] at hsix ⊢
    exact hEnd.1 hsix

  · have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hKm _ nI_memK
    rw [← hn2] at hcol
    obtain ⟨c1, c2⟩ := hEnd.2.1 hcol
    exact ⟨c1, fun a b => c2 (by rw [hcK]; exact a) (by rw [hgK]; exact b)⟩
  · have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hKm _ nI_memK
    rw [← hn2] at hz
    exact hEnd.2.2 hz

/-! ## The rule of a frame -/

/-- **No wrap of the scroll** from the frame's start `m` to `UpdScrollVar` (`u`): if the edge moved by `Y`, the counter and the edge do not pass their tops -/
def NoWrap (sy : Syms) (m0 : Machine) (m u : Machine) : Prop :=
  ∀ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 →
    (m.ram.get! (placesS sy m0).frac).toNat + Y.toNat < 256 ∧ ScrollRule.left16 (placesS sy m0) m + Y.toNat < 65536

/-- the scroll's part of the rule, from `frame_toU`'s conclusion and no wrap (as in `rule_of_toU`) -/
theorem scroll_of {m u : Machine} (hK : ∀ x ∈ pK sy m0, u.ram.get! x = m.ram.get! x)
    (hS : (ScrollRule.left16 (placesS sy m0) u = ScrollRule.left16 (placesS sy m0) m ∧ u.ram.get! (placesS sy m0).frac = m.ram.get! (placesS sy m0).frac) ∨
      (∃ Y : UInt8, ScrollRule.left16 (placesS sy m0) u = (ScrollRule.left16 (placesS sy m0) m + Y.toNat) % 65536 ∧
        (u.ram.get! (placesS sy m0).frac).toNat = ((m.ram.get! (placesS sy m0).frac).toNat + Y.toNat) % 256))
    (hw : NoWrap sy m0 m u) : Scroll (valsOf (places sy m0) m) (valsOf (places sy m0) u) := by
  have hn : peek u (places sy m0).task = peek m (places sy m0).task := hK _ (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  have hc : peek u (places sy m0).col = peek m (places sy m0).col := hK _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hp : peek u (places sy m0).page = peek m (places sy m0).page :=
    hK _ (List.mem_map.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  have el : ∀ x : Machine, edgeOf (places sy m0) x = ScrollRule.left16 (placesS sy m0) x := fun _ => rfl
  have es : ∀ x : Machine, (peek x (places sy m0).s32) = x.ram.get! (placesS sy m0).frac := fun _ => rfl
  rcases hS with ⟨h1, h2⟩ | ⟨Y, h1, h2⟩
  · refine ⟨0, ?_, ?_, ?_, ?_⟩
    · show (peek u (places sy m0).task).toNat = (peek m (places sy m0).task).toNat
      rw [hn]
    · show colOf (places sy m0) u = colOf (places sy m0) m
      unfold colOf
      rw [hc, hp]
    · show (peek u (places sy m0).s32).toNat = (peek m (places sy m0).s32).toNat + 0
      rw [es, es, h2]
      exact (Nat.add_zero _).symm
    · show edgeOf (places sy m0) u = edgeOf (places sy m0) m + 0
      rw [el, el, h1]
      exact (Nat.add_zero _).symm
  · obtain ⟨w1, w2⟩ := hw Y h1
    refine ⟨Y.toNat, ?_, ?_, ?_, ?_⟩
    · show (peek u (places sy m0).task).toNat = (peek m (places sy m0).task).toNat
      rw [hn]
    · show colOf (places sy m0) u = colOf (places sy m0) m
      unfold colOf
      rw [hc, hp]
    · show (peek u (places sy m0).s32).toNat = (peek m (places sy m0).s32).toNat + Y.toNat
      rw [es, es, h2]
      exact Nat.mod_eq_of_lt w1
    · show edgeOf (places sy m0) u = edgeOf (places sy m0) m + Y.toNat
      rw [el, el, h1]
      exact Nat.mod_eq_of_lt w2

theorem six_facts {w : UInt8} (h : vSix.contains w = true) : w.toNat ≠ 0 ∧ (w - 1).toNat = w.toNat - 1 ∧ ¬ (w.toNat = 1 ∨ w.toNat = 5) := by
  have h' : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by simpa [vSix] using h
  rcases h' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide


/-- **The parser's part, weak, for `vSix`**: from the end facts of `frame_six` -/
theorem parseW_six {u e : Machine} (hnd : (pE sy m0).Nodup) (hsix : vSix.contains (u.ram.get! (nI sy m0)) = true)
    (hE : ∀ x ∈ pE sy m0, x ≠ nI sy m0 → e.ram.get! x = u.ram.get! x)
    (hN : e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) ∨ e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) - 1) :
    ParseW (valsOf (places sy m0) u) (valsOf (places sy m0) e) := by
  have hnd' := hnd
  rw [pE_eq] at hnd'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, _⟩ := hnd'
  have es : peek e (places sy m0).s32 = peek u (places sy m0).s32 := hE (sIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n1)
  have ec : peek e (places sy m0).col = peek u (places sy m0).col := hE (cIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n2)
  have eg : peek e (places sy m0).page = peek u (places sy m0).page := hE (gIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n3)
  have ex : peek e (places sy m0).ex = peek u (places sy m0).ex := hE (xIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n4)
  have ey : peek e (places sy m0).ep = peek u (places sy m0).ep := hE (yIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n5)
  have hedge : edgeOf (places sy m0) e = edgeOf (places sy m0) u := by unfold edgeOf; rw [ex, ey]
  have hcol : colOf (places sy m0) e = colOf (places sy m0) u := by unfold colOf; rw [ec, eg]
  obtain ⟨f1, f2, f3⟩ := six_facts hsix
  refine ⟨hedge, ?_⟩
  rcases hN with h | h
  · refine Or.inl ⟨?_, ?_, hcol⟩
    · show (peek e (places sy m0).task).toNat = (peek u (places sy m0).task).toNat
      exact congrArg UInt8.toNat h
    · show (peek e (places sy m0).s32).toNat = (peek u (places sy m0).s32).toNat
      rw [es]
  · refine Or.inr ?_
    unfold Step
    have hn0 : (valsOf (places sy m0) u).n ≠ 0 := f1
    rw [if_neg hn0]
    refine ⟨?_, ?_, ?_⟩
    · show (peek e (places sy m0).task).toNat = (peek u (places sy m0).task).toNat - 1
      have h' : peek e (places sy m0).task = u.ram.get! (nI sy m0) - 1 := h
      rw [h']
      exact f2
    · show (peek e (places sy m0).s32).toNat = (peek u (places sy m0).s32).toNat
      rw [es]
    · have hn15 : ¬ ((valsOf (places sy m0) u).n = 1 ∨ (valsOf (places sy m0) u).n = 5) := f3
      rw [if_neg hn15]
      exact hcol

/-- **A frame in control with `N` in `vSix` at its start follows the weak rule**: the conditions of `frame_six`, and no wrap of the scroll at `UpdScrollVar` -/
theorem rule_six (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hw : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → NoWrap sy m0 m (trace m i k))
    (hsix : vSix.contains (m.ram.get! (nI sy m0)) = true) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
  obtain ⟨k₂, hq2, hf2, hK, hS, hE⟩ := frame_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  obtain ⟨hE1, hE2⟩ := hE.1 hsix
  have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hK _ nI_memK
  refine ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS (hw k₂ hq2 hf2), parseW_six (nodup_of_check he) (by rw [hn2]; exact hsix) hE1 ?_⟩
  rw [hn2]
  exact hE2


theorem col_facts {w : UInt8} (h : vCol.contains w = true) : w.toNat ≠ 0 ∧ (w - 1).toNat = w.toNat - 1 ∧ (w.toNat = 1 ∨ w.toNat = 5) := by
  have h' : w = 1 ∨ w = 5 := by simpa [vCol] using h
  rcases h' with rfl | rfl <;> decide

/-- **The parser's part, weak, for `vCol`**: from the end facts of `frame_six` -/
theorem parseW_col {u e : Machine} (hnd : (pE sy m0).Nodup) (hcol : vCol.contains (u.ram.get! (nI sy m0)) = true)
    (hE : ∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ cIdx sy m0 → x ≠ gIdx sy m0 → e.ram.get! x = u.ram.get! x)
    (hc16 : (u.ram.get! (cIdx sy m0)).toNat < 16) (hp255 : u.ram.get! (gIdx sy m0) ≠ 255) (hC : ColEnd sy m0 u e) :
    ParseW (valsOf (places sy m0) u) (valsOf (places sy m0) e) := by
  have hnd' := hnd
  rw [pE_eq] at hnd'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨n1, _, _, n4, n5⟩, ⟨s1, s2, _, _⟩, ⟨_, c4, c5⟩, ⟨g4, g5⟩, _⟩ := hnd'
  have es : peek e (places sy m0).s32 = peek u (places sy m0).s32 := hE (sIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n1) s1 s2
  have ex : peek e (places sy m0).ex = peek u (places sy m0).ex := hE (xIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n4) (Ne.symm c4) (Ne.symm g4)
  have ey : peek e (places sy m0).ep = peek u (places sy m0).ep := hE (yIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n5) (Ne.symm c5) (Ne.symm g5)
  have hedge : edgeOf (places sy m0) e = edgeOf (places sy m0) u := by unfold edgeOf; rw [ex, ey]
  obtain ⟨f1, f2, f3⟩ := col_facts hcol
  refine ⟨hedge, ?_⟩
  have hn : ∀ x : Machine, (valsOf (places sy m0) x).n = (x.ram.get! (nI sy m0)).toNat := fun _ => rfl
  have hs : ∀ x : Machine, (valsOf (places sy m0) x).s = (peek x (places sy m0).s32).toNat := fun _ => rfl
  have hc : ∀ x : Machine, (valsOf (places sy m0) x).col = (x.ram.get! (gIdx sy m0)).toNat * 16 + (x.ram.get! (cIdx sy m0)).toNat := fun _ => rfl
  have step : e.ram.get! (nI sy m0) = u.ram.get! (nI sy m0) - 1 →
      (valsOf (places sy m0) e).col = (valsOf (places sy m0) u).col + 1 → Step (valsOf (places sy m0) u) (valsOf (places sy m0) e) := by
    intro h1 h2
    unfold Step
    rw [if_neg (by rw [hn]; exact f1), if_pos (by rw [hn]; exact f3)]
    refine ⟨?_, ?_, h2⟩
    · rw [hn, hn, h1]
      exact f2
    · rw [hs, hs, es]
  obtain ⟨C1, C2⟩ := hC
  by_cases h15 : (u.ram.get! (cIdx sy m0)).toNat < 15
  · obtain ⟨hg, hor⟩ := C1 h15
    rcases hor with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · refine Or.inl ⟨by rw [hn, hn, a1], by rw [hs, hs, es], by rw [hc, hc, hg, a2]⟩
    · refine Or.inr (step a1 ?_)
      rw [hc, hc, hg, a2]
      have : (u.ram.get! (cIdx sy m0) + 1).toNat = (u.ram.get! (cIdx sy m0)).toNat + 1 := by
        rw [UInt8.toNat_add]
        have : (1 : UInt8).toNat = 1 := rfl
        rw [this]
        omega
      rw [this]
      omega
  · have e15 : u.ram.get! (cIdx sy m0) = 15 := UInt8.toNat_inj.1 (by have : (15 : UInt8).toNat = 15 := rfl; rw [this]; omega)
    rcases C2 e15 with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · refine Or.inl ⟨by rw [hn, hn, a1], by rw [hs, hs, es], by rw [hc, hc, a3, a2, e15]⟩
    · refine Or.inr (step a1 ?_)
      rw [hc, hc, a3, a2, e15]
      have hp1 : (u.ram.get! (gIdx sy m0)).toNat ≠ 255 := fun h => hp255 (UInt8.toNat_inj.1 (by rw [h]; rfl))
      have : (u.ram.get! (gIdx sy m0) + 1).toNat = (u.ram.get! (gIdx sy m0)).toNat + 1 := by
        rw [UInt8.toNat_add]
        have : (1 : UInt8).toNat = 1 := rfl
        rw [this]
        have := (u.ram.get! (gIdx sy m0)).toNat_lt
        omega
      rw [this]
      have h0 : (0 : UInt8).toNat = 0 := rfl
      have h15' : (15 : UInt8).toNat = 15 := rfl
      rw [h0, h15']
      omega

/-- **A frame in control with `N` = 1 or 5 at its start follows the weak rule**, when the parser's column is below 16 and its page is not 255: the conditions of
`frame_six` and no wrap of the scroll at `UpdScrollVar` -/
theorem rule_col (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hw : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → NoWrap sy m0 m (trace m i k))
    (hcol : vCol.contains (m.ram.get! (nI sy m0)) = true) (hc16 : (m.ram.get! (cIdx sy m0)).toNat < 16) (hp255 : m.ram.get! (gIdx sy m0) ≠ 255) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
  obtain ⟨k₂, hq2, hf2, hK, hS, hE⟩ := frame_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  obtain ⟨hE1, hE2⟩ := hE.2.1 hcol
  have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hK _ nI_memK
  have hcK : (trace m i k₂).ram.get! (cIdx sy m0) = m.ram.get! (cIdx sy m0) :=
    hK _ (List.mem_map.2 ⟨(places sy m0).col, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hgK : (trace m i k₂).ram.get! (gIdx sy m0) = m.ram.get! (gIdx sy m0) :=
    hK _ (List.mem_map.2 ⟨(places sy m0).page, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  refine ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS (hw k₂ hq2 hf2),
    parseW_col (nodup_of_check he) (by rw [hn2]; exact hcol) hE1 (by rw [hcK]; exact hc16) (by rw [hgK]; exact hp255) (hE2 hc16 hp255)⟩


/-- **The parser's part, weak, for `N` = 0**: from the end facts of `frame_six` -/
theorem parseW_zero {u e : Machine} (hnd : (pE sy m0).Nodup) (hz : u.ram.get! (nI sy m0) = 0)
    (hE : ∀ x ∈ pE sy m0, x ≠ nI sy m0 → x ≠ sIdx sy m0 → e.ram.get! x = u.ram.get! x)
    (hS : (e.ram.get! (nI sy m0) = 0 ∧ e.ram.get! (sIdx sy m0) = u.ram.get! (sIdx sy m0)) ∨
      (32 ≤ (u.ram.get! (sIdx sy m0)).toNat ∧ (u.ram.get! (sIdx sy m0)).toNat < 160 ∧ e.ram.get! (nI sy m0) = 7 ∧
        e.ram.get! (sIdx sy m0) = u.ram.get! (sIdx sy m0) - 32)) :
    ParseW (valsOf (places sy m0) u) (valsOf (places sy m0) e) := by
  have hnd' := hnd
  rw [pE_eq] at hnd'
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨_, n2, n3, n4, n5⟩, ⟨s1, s2, s3, s4⟩, _⟩ := hnd'
  have ec : peek e (places sy m0).col = peek u (places sy m0).col := hE (cIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n2) (Ne.symm s1)
  have eg : peek e (places sy m0).page = peek u (places sy m0).page := hE (gIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n3) (Ne.symm s2)
  have ex : peek e (places sy m0).ex = peek u (places sy m0).ex := hE (xIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n4) (Ne.symm s3)
  have ey : peek e (places sy m0).ep = peek u (places sy m0).ep := hE (yIdx sy m0) (by rw [pE_eq]; simp) (Ne.symm n5) (Ne.symm s4)
  have hedge : edgeOf (places sy m0) e = edgeOf (places sy m0) u := by unfold edgeOf; rw [ex, ey]
  have hcol : colOf (places sy m0) e = colOf (places sy m0) u := by unfold colOf; rw [ec, eg]
  have hn : ∀ x : Machine, (valsOf (places sy m0) x).n = (x.ram.get! (nI sy m0)).toNat := fun _ => rfl
  have hs : ∀ x : Machine, (valsOf (places sy m0) x).s = (x.ram.get! (sIdx sy m0)).toNat := fun _ => rfl
  refine ⟨hedge, ?_⟩
  rcases hS with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩
  · exact Or.inl ⟨by rw [hn, hn, a1, hz], by rw [hs, hs, a2], hcol⟩
  · refine Or.inr ?_
    unfold Step
    rw [if_pos (by rw [hn, hz]; rfl)]
    refine ⟨by rw [hs]; exact a1, by rw [hs]; exact a2, by rw [hn, a3]; rfl, ?_, hcol⟩
    rw [hs, hs, a4, UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.2 (by have : (32 : UInt8).toNat = 32 := rfl; rw [this]; exact a1))]
    rfl

/-- **A frame in control with `N` = 0 at its start follows the weak rule**: the conditions of `frame_six` and no wrap of the scroll at `UpdScrollVar` -/
theorem rule_zero (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hw : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → NoWrap sy m0 m (trace m i k))
    (hz : m.ram.get! (nI sy m0) = 0) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
  obtain ⟨k₂, hq2, hf2, hK, hS, hE⟩ := frame_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  obtain ⟨hE1, hE2⟩ := hE.2.2 hz
  have hn2 : (trace m i k₂).ram.get! (nI sy m0) = m.ram.get! (nI sy m0) := hK _ nI_memK
  exact ⟨valsOf (places sy m0) (trace m i k₂), scroll_of hK hS (hw k₂ hq2 hf2), parseW_zero (nodup_of_check he) (by rw [hn2]; exact hz) hE1 hE2⟩

/-- the values of `N` up to 8: 0, `vCol`, `vSix` -/
theorem n_cases {w : UInt8} (h : w.toNat ≤ 8) : w = 0 ∨ vCol.contains w = true ∨ vSix.contains w = true := by
  have h' : w.toNat = 0 ∨ w.toNat = 1 ∨ w.toNat = 2 ∨ w.toNat = 3 ∨ w.toNat = 4 ∨ w.toNat = 5 ∨ w.toNat = 6 ∨ w.toNat = 7 ∨ w.toNat = 8 := by omega
  have e : w = w.toNat.toUInt8 := by simp
  rcases h' with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [e, h1] <;> decide

/-- **Every frame in control follows the weak rule**, when at its start `N` is at most 8, the parser's column is below 16 and its page is not 255: the conditions
of `frame_six` and no wrap of the scroll at `UpdScrollVar` (`rule_zero`, `rule_col`, `rule_six`) -/
theorem rule_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hw : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → NoWrap sy m0 m (trace m i k))
    (h8 : (m.ram.get! (nI sy m0)).toNat ≤ 8) (hc16 : (m.ram.get! (cIdx sy m0)).toNat < 16) (hp255 : m.ram.get! (gIdx sy m0) ≠ 255) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) := by
  rcases n_cases h8 with h | h | h
  · exact rule_zero hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp hw h
  · exact rule_col hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp hw h hc16 hp255
  · exact rule_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp hw h

end Proofs

/-! ## The column in its page, at control and on every frame; the invariant on a run

The weak rule asks the parser's column in its page below 16 at the frame's start (for the column's step). It holds at control (`col₀`, from the rows of the change
out of the side pipe; check `colCheckK`), and each frame keeps it (`col_frame`). With the invariant (`N ≤ 8`) it is the induction of `inv_runC`. The page is not
255 when the edge is below 64896 px (`page_of_inv`, with `L = 384`). -/

/-- **The column in its page is below 16** -/
def ColOK (sy : Syms) (m0 : Machine) (m : Machine) : Prop := (m.ram.get! (cIdx sy m0)).toNat < 16

/-- a state of a row: it knows the bytes of control, and if it has control, it knows the column and it is below 16 -/
def rowCol (sy : Syms) (m0 : Machine) (S : AS) : Bool :=
  (SurfaceFrames.ctlBytes sy).all (SideChangeEnd.knowsAd S) &&
    (!controllable sy (SideChangeEnd.mOf S) || ((S.getK (cIdx sy m0)).isK && decide ((S.getK (cIdx sy m0)).v.toNat < 16)))

/-- **The check on the ROM**: in every state with control of the rows of the change out of the side pipe the column is below 16 -/
def colCheckK (sy : Syms) (m0 : Machine) (nm nx : PipeTransitionAll.Names) (e : Machine) (A B : Nat) (R : StepWrites.Rt) : Bool :=
  ((SideChangeSound.rowsOf sy nm nx e A B R).map (·.row)).all fun r => r.R.all (rowCol sy m0)

section Col
variable {sy : Syms} {m0 : Machine}

theorem col_of_state {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m) (hr : rowCol sy m0 S = true) (h : controllable sy m = true) :
    ColOK sy m0 m := by
  simp only [rowCol, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hr
  obtain ⟨hk, hr⟩ := hr
  rcases hr with h1 | ⟨h1, h2⟩
  · have := SurfaceFrames.controllable_of_known hs hk h
    rw [this] at h1
    cases h1
  · have e := PipeEntryRule.known_eq h1 (hs.ram _ (idx_lt _))
    unfold ColOK
    rw [e]
    exact h2

theorem col_of_invL {C : SideChangeEnd.Ctx} :
    ∀ {l : List SideChangeEnd.Row}, (l.all fun r => r.R.all (rowCol sy m0)) = true → ∀ {m : Machine}, SideChangeEnd.InvL C l m → controllable sy m = true →
      ColOK sy m0 m
  | [], _, _, h, _ => by cases h
  | r :: t, hl, _, h, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rcases h with ⟨S, hS, hs⟩ | h
    · exact col_of_state hs (List.all_eq_true.1 hl.1 S hS) hc
    · exact col_of_invL hl.2 h hc

/-- **The column at control is below 16**, on a real run of the change (as `PoleParser.EndRunQ.inv`) -/
theorem EndRunQ.col {nm nx : PipeTransitionAll.Names} {e : Machine} {A B : Nat} {R : StepWrites.Rt} {es : List Machine}
    (S : SideChangeBound.Statement sy nm e es A B) (T : SideChangeSound.EndStatementK sy nm nx e A B R) (Q : SidePause.PipeQ sy nm nx e A B R)
    (hk : colCheckK sy m0 nm nx e A B R = true) (R' : SidePause.EndRunQ sy nm nx e A) (hc : ∀ n, R'.a ≤ n → n < R'.b → controllable sy (R'.seq n) = false) :
    ColOK sy m0 (R'.seq R'.b) :=
  col_of_invL hk (SideChangeSound.invL_of_invS (SidePause.EndRunQ.inRows S T Q R' hc)) R'.atCtl

end Col

section Col0
open Route

variable {sy : Syms} {m0 : Machine} {N : Nat} {D : Int} {rN : RoomJoin.Nums}
  {b : Machine} {vs : List Jump.VS} {PA : PoleJoin.Box} {Ts J Nc : Nat} {F : Int} {q t0 : Nat} {nm₁ : PipeTransitionAll.Names} {d₁ : PipeChangeEnd.Data}
  {nm₂ nx₂ nmS : PipeTransitionAll.Names} {fc : FlagRule.Ctx} {tc : TitleStart.Ctx}

/-- **The column at control above ground is below 16**, on the real machines (as `PoleParser.inv₀`). `hm` is the check on the ROM. -/
theorem col₀ {es : List Machine} {rt : StepWrites.Rt} (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122)
    (hT : SideChangeSound.EndStatementK sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt) (hQ : SidePause.PipeQ sy nm₂ nx₂ (SideTransition.entry m0) 160 122 rt)
    (hR : RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS)
    (hm : colCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (R : Run sy m0 N D rN b vs PA Ts J Nc F q t0 nm₁ d₁ nm₂ nx₂ nmS fc tc) :
    ColOK sy m0 (R.pole.seq 0) := by
  rw [R.atCtl]
  exact EndRunQ.col hS hT hQ hm ((R.chgK hR hB hK).run₂ hR (R.entry₁ hB hK)) R.chg.ctlFirst₂

end Col0

section ColFrame
open PipeEntryRule (trace)
open PipeTransition (frame)
open AfterKeep (guardH)

variable {sy : Syms} {m0 : Machine}

/-- **A frame in control keeps the column below 16**: the conditions of `frame_six`, `N ≤ 8` and the page not 255 at its start -/
theorem col_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (h8 : (m.ram.get! (nI sy m0)).toNat ≤ 8) (hc16 : ColOK sy m0 m) (hp255 : m.ram.get! (gIdx sy m0) ≠ 255) :
    ColOK sy m0 (frame m i) := by
  obtain ⟨k₂, _, _, hK, _, hE⟩ := frame_six hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp
  have hcK : (trace m i k₂).ram.get! (cIdx sy m0) = m.ram.get! (cIdx sy m0) :=
    hK _ (List.mem_map.2 ⟨(places sy m0).col, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
  have hnd := nodup_of_check he
  rw [pE_eq] at hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨_, n2, _, _, _⟩, ⟨s1, _, _, _⟩, _⟩ := hnd
  have hmem : cIdx sy m0 ∈ pE sy m0 := by rw [pE_eq]; simp
  unfold ColOK at hc16 ⊢
  rcases n_cases h8 with hz | hcol | hsix
  · rw [(hE.2.2 hz).1 _ hmem (Ne.symm n2) (Ne.symm s1), hcK]
    exact hc16
  · obtain ⟨C1, C2⟩ := (hE.2.1 hcol).2 hc16 hp255
    rw [← hcK] at hc16
    by_cases h15 : ((trace m i k₂).ram.get! (cIdx sy m0)).toNat < 15
    · rcases (C1 h15).2 with ⟨_, a⟩ | ⟨_, a⟩
      · rw [a]; exact hc16
      · rw [a, UInt8.toNat_add]
        have : (1 : UInt8).toNat = 1 := rfl
        rw [this]
        omega
    · have e15 : (trace m i k₂).ram.get! (cIdx sy m0) = 15 := UInt8.toNat_inj.1 (by have : (15 : UInt8).toNat = 15 := rfl; rw [this]; omega)
      rcases C2 e15 with ⟨_, a, _⟩ | ⟨_, a, _⟩
      · rw [a]; decide
      · rw [a]; decide
  · rw [(hE.1 hsix).1 _ hmem (Ne.symm n2), hcK]
    exact hc16

/-- **The page is not 255** when the invariant holds and the edge is below `65280 − L` px -/
theorem page_of_inv {L : Nat} {m : Machine} (h : Inv (places sy m0) L m) (he : edgeOf (places sy m0) m + L < 65280) : m.ram.get! (gIdx sy m0) ≠ 255 := by
  intro hp
  have h2 := h.2
  unfold sumOf colOf at h2
  have e : (peek m (places sy m0).page).toNat = 255 := by
    show (m.ram.get! (gIdx sy m0)).toNat = 255
    rw [hp]
    rfl
  rw [e] at h2
  omega

/-- **The invariant and the column on a run**: if they hold at the first frame's start, and each frame from a start with them follows the weak rule and keeps the
column below 16, they hold at every frame's start -/
theorem inv_runC {L : Nat} {ms : Nat → Machine} (h0 : Inv (places sy m0) L (ms 0) ∧ ColOK sy m0 (ms 0))
    (hstep : ∀ n, Inv (places sy m0) L (ms n) → ColOK sy m0 (ms n) →
      RuleW (valsOf (places sy m0) (ms n)) (valsOf (places sy m0) (ms (n + 1))) ∧ ColOK sy m0 (ms (n + 1))) :
    ∀ n, Inv (places sy m0) L (ms n) ∧ ColOK sy m0 (ms n)
  | 0 => h0
  | n + 1 =>
    have ih := inv_runC h0 hstep n
    have st := hstep n ih.1 ih.2
    ⟨(invV_iff (P := places sy m0) (m := ms (n + 1))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := ms n)).1 ih.1) st.1), st.2⟩

/-- **The guard of the parser's bytes**: that of the frames, with the bytes of `pU` protected (the parser's four, the edge's two, the platforms' force). One condition
on each instruction, `CleanK` of it, gives those of `AfterKeep.guardH` and `guardN` that the walks ask (`cleanH_of_par`, `cleanN_of_par`). -/
def guardPar (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := pU sy m0 ++ (FrameKeep.guardF sy m0).prot }

theorem cleanH_of_par {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ pU sy m0) (h : FrameKeep.CleanK (guardPar sy m0) q m) : FrameKeep.CleanK (guardH sy m0 x) q m :=
  FrameKeep.cleanK_sub h (fun y hy => by
    simp only [guardH, guardPar, List.mem_append, List.mem_singleton] at hy ⊢
    rcases hy with rfl | hy
    · exact Or.inl hx
    · exact Or.inr hy) rfl rfl rfl rfl

theorem cleanN_of_par {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ pE sy m0) (h : FrameKeep.CleanK (guardPar sy m0) q m) : FrameKeep.CleanK (guardN sy m0 x) q m := by
  have hc : cIdx sy m0 ∈ pU sy m0 := pE_sub (by rw [pE_eq]; simp)
  have hg : gIdx sy m0 ∈ pU sy m0 := pE_sub (by rw [pE_eq]; simp)
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardN, guardPar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  rcases hy with (rfl | rfl | rfl | rfl) | hy
  · exact Or.inl (pE_sub hx)
  · exact Or.inl (pU_sub nI_mem)
  · exact Or.inl hc
  · exact Or.inl hg
  · exact Or.inr hy

/-- **The guard of the parser's four bytes**: that of the frames, with the parser's four bytes protected -/
def guardPI (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := pI sy m0 ++ (FrameKeep.guardF sy m0).prot }

/-- **What is new in `guardPar`**: with `CleanK` of `FrameKeep.guardE` (the field `cleanE` of the frames of a run, which protects the edge's two bytes and the
platforms' force), `CleanK` of `guardPar` is `CleanK` of `guardPI`: no store through an index or a pointer writes the parser's four bytes -/
theorem cleanPar_of {q : UInt16} {m : Machine} (hE : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hI : FrameKeep.CleanK (guardPI sy m0) q m) :
    FrameKeep.CleanK (guardPar sy m0) q m := by
  refine ⟨fun t ht hq => ?_, hI.read, hI.jump, hI.time⟩
  rcases hI.store t ht hq with ⟨h1, h2⟩ | h1
  · rcases hE.store t ht hq with ⟨_, h4⟩ | h3
    · refine Or.inl ⟨h1, fun h5 => ?_⟩
      simp only [guardPar, pU, List.mem_append] at h5
      rcases h5 with (h5 | h5) | h5
      · exact h2 (List.mem_append_left _ h5)
      · exact h4 (EdgeStep.eI_mem h5)
      · exact h2 (List.mem_append_right _ h5)
    · exact Or.inr h3
  · exact Or.inr h1

/-- **One step of `inv_runC` for a frame that comes to the player's routine**: from the invariant, the column below 16 and the edge below `65280 − L` px at its
start, and the conditions of `rule_frame` with one guard for the parser's bytes (`hP`, which gives `CleanK` of `FrameKeep.guardF` too) (`rule_frame`, `col_frame`,
`page_of_inv`) -/
theorem step_frame {L : Nat} (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hP : ∀ j, FrameKeep.CleanK (guardPar sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (ht : ∀ n, (trace m i n).pc ≠ sy.EndlessLoop → (trace m i n).fdot ≤ dotsPerFrame - 64)
    (hp : ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false)
    (hw : ∀ k, (trace m i k).pc = sy.UpdScrollVar → (trace m i k).frame = m.frame → NoWrap sy m0 m (trace m i k))
    (hI : Inv (places sy m0) L m) (hC : ColOK sy m0 m) (hE : edgeOf (places sy m0) m + L < 65280) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) ∧ ColOK sy m0 (frame m i) :=
  have hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_weak (hP n)
  have hH : ∀ x ∈ pU sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j) := fun x hx j => cleanH_of_par hx (hP j)
  have hN : ∀ x ∈ pE sy m0, ∀ j, FrameKeep.CleanK (guardN sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j) := fun x hx j => cleanN_of_par hx (hP j)
  ⟨rule_frame hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp hw hI.1 hC (page_of_inv hI hE),
    col_frame hc hq hqe he hs hidle h0 hcl hH hN hx hv harr hf0 hfirst ht hp hI.1 hC (page_of_inv hI hE)⟩

end ColFrame

section NoCut
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- **One step of `inv_runC` for a frame that does not come to the player's routine**: it keeps the bytes (`rule_of_noCut`, `keep_noCutP`) -/
theorem step_noCut {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) (hC : ColOK sy m0 m) :
    RuleW (valsOf (places sy m0) m) (valsOf (places sy m0) (frame m i)) ∧ ColOK sy m0 (frame m i) := by
  refine ⟨ruleW_of (rule_of_noCut hq hqe h0 hcl hn), ?_⟩
  have e : (frame m i).ram.get! (cIdx sy m0) = m.ram.get! (cIdx sy m0) :=
    keep_noCutP hq h0 hcl hn _ (List.mem_map.2 ⟨(places sy m0).col, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩)
  unfold ColOK
  rw [e]
  exact hC

end NoCut


/-! ## On the frames of a run

`inv_onFrames`: on the frames of a run up to the touch's frame (`FrameKeep.Frames`, from the machine at control on), the invariant and the column below 16 hold at
every frame's start, from their values at the first and, for each frame before the touch's frame, the area's type `v`, the field `posW` from the scroll handler on
(round 29: only on a frame that comes to the player's routine, from its first arrival there), no
wrap of the scroll (round 30: only on a frame that comes to the player's routine), the edge below `65280 − L` px and `CleanK` of `guardPI` (no store through an index or a pointer writes the parser's four bytes). The rest comes from
the frames: each starts in the idle loop in control (`Frames.all_start`), `cleanE` (with `cleanPar_of`), `noStore`, and the time. A frame that comes to the player's
routine takes `step_frame`, one that does not `step_noCut` (`arrival_cases`). -/

section RunFrames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- **A frame in control comes to the player's routine a first time, or not at all** (the walk of `CtrlKeep` in `qCheckP`) -/
theorem arrival_cases {v : UInt8} (hq : qCheckP sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) :
    (∃ n₀, (trace m i n₀).pc = sy.PlayerCtrlRoutine ∧ (trace m i n₀).frame = m.frame ∧ ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) ∨
    (∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) := by
  simp only [qCheckP, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hq
  obtain ⟨_, hb⟩ := hq
  obtain ⟨h1, _⟩ := hb (nI sy m0) nI_mem
  generalize CtrlKeep.cutTable sy m0 true = q at h1
  rcases CtrlKeep.cut_or_end2 (C := EdgeStep.cfgQb sy m0 v q (nI sy m0) _) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hcl with
    ⟨k₀, a1, a2, _, a4, _⟩ | ⟨hno, _⟩
  · exact Or.inl ⟨k₀, a1, a2, a4⟩
  · exact Or.inr hno

/-- **The invariant and the column at every frame's start up to the touch's frame**, on the frames of a run -/
theorem inv_onFrames {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (K : FrameKeep.Frames sy m0 S a g seq)
    (hkc : FrameKeep.keepCheckOf sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (hw0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheckP sy m0 v = true) (hqe : EdgeStep.qCheck sy m0 v = true)
    (he : eCheckP sy m0 v = true) (hs : checkS sy m0 = true) (hidle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) {L : Nat}
    (h0 : Inv (places sy m0) L (K.all 0) ∧ ColOK sy m0 (K.all 0))
    (hI : ∀ n, n + 1 < K.ix g → ∀ k, FrameKeep.CleanK (guardPI sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k))
    (hv : ∀ n, n + 1 < K.ix g → CtrlKeep.AreaOK sy v (K.all n))
    (hp : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      (∀ j, j < n₀ → (trace (K.all n) (K.inp n) j).pc ≠ sy.PlayerCtrlRoutine) →
      ∀ k, n₀ ≤ k → (trace (K.all n) (K.inp n) k).pc = sy.PlayerSubs → ∀ j, k ≤ j → (trace (K.all n) (K.inp n) j).frame = (K.all n).frame →
      EdgeStep.cutPos sy m0 (trace (K.all n) (K.inp n) j).pc = false)
    (hw : ∀ n, n + 1 < K.ix g → ∀ n₀, (trace (K.all n) (K.inp n) n₀).pc = sy.PlayerCtrlRoutine → (trace (K.all n) (K.inp n) n₀).frame = (K.all n).frame →
      ∀ k, (trace (K.all n) (K.inp n) k).pc = sy.UpdScrollVar → (trace (K.all n) (K.inp n) k).frame = (K.all n).frame →
      NoWrap sy m0 (K.all n) (trace (K.all n) (K.inp n) k))
    (hE : ∀ n, n + 1 < K.ix g → edgeOf (places sy m0) (K.all n) + L < 65280) :
    ∀ n, n < K.ix g → Inv (places sy m0) L (K.all n) ∧ ColOK sy m0 (K.all n) := by
  intro n
  induction n with
  | zero => exact fun _ => h0
  | succ n ih =>
    intro hn
    obtain ⟨hIn, hCn⟩ := ih (by omega)
    have hst := (K.all_start hkc hs0 hw0 n (by omega)).1
    have hix : K.ix g = FrameKeep.ixOf sy m0 S a K.top g := rfl
    have hcE := K.cleanE n (by omega)
    have hclF : ∀ k, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
      fun k => FrameKeep.cleanK_of_E (hcE k)
    have hclK : ∀ k, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) :=
      fun k => FrameKeep.cleanK_of_F (hclF k)
    have hP : ∀ k, FrameKeep.CleanK (guardPar sy m0) (FrameKeep.spotOf sy m0).store (trace (K.all n) (K.inp n) k) := fun k => cleanPar_of (hcE k) (hI n hn k)
    have ht : ∀ k, (trace (K.all n) (K.inp n) k).pc ≠ sy.EndlessLoop → (trace (K.all n) (K.inp n) k).fdot ≤ dotsPerFrame - 64 := fun k hk => (hcE k).time hk
    rw [K.next n]
    rcases arrival_cases hq hst hclK with ⟨n₀, a1, a2, a3⟩ | hno
    · have r := step_frame hc hq hqe he hs hidle hst hP (K.noStore n hn) (hv n hn) a1 a2 a3 ht (hp n hn n₀ a1 a2 a3) (hw n hn n₀ a1 a2) hIn hCn (hE n hn)
      exact ⟨(invV_iff (P := places sy m0) (m := frame (K.all n) (K.inp n))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := K.all n)).1 hIn) r.1), r.2⟩
    · have r := step_noCut hq hqe hst hclK hno hCn
      exact ⟨(invV_iff (P := places sy m0) (m := frame (K.all n) (K.inp n))).2 (inv_ruleW ((invV_iff (P := places sy m0) (m := K.all n)).1 hIn) r.1), r.2⟩

end RunFrames

end Smbrta.PoleParser
