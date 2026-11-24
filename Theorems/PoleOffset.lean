import Theorems.PoleNear
import Theorems.SideAcross
import Theorems.PoleTileKeep

/-!
# Above ground: the head's collision with the block objects' offset known

Round 36 (`PoleNear`) asked the field `PoleJoin.Run.ctlKeep` (no store through an index or a pointer writes the screen buffers' control byte) only at three
kinds of place (`PoleNear.ResidC`): the two stores through a pointer in the code of the head's collision with a block, the castle's loop of rows and the store of
`RenderUnderPart`.

The head's collision stores through the zero page with the block objects' offset (`SprDataOffset_Ctrl`, `PoleTileKeep.sprI`) as the index. The walk of
`PoleNear` does not know the offset, so such a store may write the pointer of the block buffer, and the walk loses the pointer's high byte. Here the walk is that
of `PoleNear` with the offset protected (`guardO`: no store through an index or a pointer writes it, the field `keepB` through `PoleTileKeep.KeepB`) and with
its bits 1 to 7 known to be 0 at the frame's start (`InvS`), and with `SideAcross.fixP` after each step (the zero page bytes that a store through a pointer
cannot reach stay known). Then the pointer's high byte stays known through the head's collision, and its two stores miss the control byte.

So the walk proves the field's condition at every instruction of a frame that starts with `InvS`, up to its first store of the routine, the mode or the task by
its address, but at the castle's loop and the store of `RenderUnderPart` (`ResidC`; `off_frame`, `off_frames`). On a frame that does not start with `InvS`
round 36's walk (`PoleNear.near_frames`) still gives it away from `PoleNear.ResidC`. So `ctlKeep` asks only at `ResidC`, and at the two stores of the head's
collision only on a frame that does not start with `InvS`. Every frame of the route starts with `InvS` (`PoleTileKeep.frames_keepY`, from the fields `keepB` and
`bufAll` and the offset at control), but the route's theorems that use `ctlKeep` do not have those hypotheses.

What the walk does not know at the two places left: the castle's loop starts at a row read from the area's data, and `RenderUnderPart` draws from a row that a
staircase reads from a table at an index that lives across frames (`StaircaseControl`).

The search that makes the table is no part of the proof (`searchO`); the check is `oCheck`. From this round `PoleNear.nCheck` is round 36's check and this one.
There is no game data in this file. Page: `1-1/f-6-17-20-PoleOffset.md`.
-/

namespace Smbrta.PoleOffset

open TaintRun (AS Env Sim AB aRows AM Cov)
open PipeTransitionAll (go)
open PipeEntryRule (trace nxt)
open PipeWrites (Guard FrameStart wTarget opAt knownOf)
open FrameKeep (CleanK storesTo)
open PoleBcol (NoW)

variable {sy : Syms}

/-! ## The offset, the guard, the frame's start -/

/-- the block objects' offset, as a RAM index -/
def sI (sy : Syms) (m0 : Machine) : Nat := PoleTileKeep.sprI sy m0

/-- **The frame's start that the walk needs** (one state): bits 1 to 7 of the block objects' offset are 0 -/
def InvS (sy : Syms) (m0 : Machine) (m : Machine) : Prop := m.ram.get! (sI sy m0) &&& 0xFE = 0

/-- the walk's guard: `FrameKeep.guardE` with the offset protected -/
def guardO (sy : Syms) (m0 : Machine) : Guard := { FrameKeep.guardE sy m0 with prot := sI sy m0 :: (FrameKeep.guardE sy m0).prot }

/-- the state of a frame's start: `FrameKeep.startK`, with bits 1 to 7 of the offset known to be 0 -/
def startO (sy : Syms) (m0 : Machine) (late : Bool) : AS := (FrameKeep.startK (guardO sy m0) [] late).setK (sI sy m0) ⟨0, 0xFE⟩

set_option maxRecDepth 100000 in
/-- `CleanK` of the walk's guard, from `CleanK` of `FrameKeep.guardE` and no store through an index or a pointer to the offset -/
theorem cleanK_O {m0 : Machine} {q : UInt16} {m : Machine} (h : CleanK (FrameKeep.guardE sy m0) q m) (hb : NoW (sI sy m0) m) : CleanK (guardO sy m0) q m :=
  ⟨fun t ht hq => by
    have e : (guardO sy m0).prot = [sI sy m0] ++ (FrameKeep.guardE sy m0).prot := rfl
    rw [e]
    exact SideAcross.plain_app (h.store t ht hq) (fun hlt hm => hb t ht hlt (List.mem_singleton.1 hm)), h.read, h.jump, h.time⟩

/-- `PoleTileKeep.KeepB` gives no store through an index or a pointer to the offset -/
theorem noW_of_keepB {m0 : Machine} {m : Machine} (h : PoleTileKeep.KeepB sy m0 m) : NoW (sI sy m0) m :=
  fun t ht hlt heq => h t ht hlt (by rw [heq]; simp [PoleTileKeep.bI, sI])

/-- the start of a frame for the walk's guard: the same as for `FrameKeep.guardK` -/
theorem start_O {m0 : Machine} {m : Machine} (h : FrameKeep.StartK sy m0 m) : FrameStart (guardO sy m0) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- **The state of a frame's start covers the machine**, with `InvS` -/
theorem sim_startO {m0 : Machine} {m : Machine} (h : FrameKeep.StartK sy m0 m) (hS : InvS sy m0 m) :
    ∃ b : Bool, Sim (PipeEntryRule.envOf m0) (m.frame, 2) (startO sy m0 b) m := by
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (W := []) (E := PipeEntryRule.envOf m0) rfl (start_O h) (fun _ h => by cases h)
  refine ⟨b, PipeEntryRule.sim_setK' hs ?_⟩
  show m.ram.get! (sI sy m0) &&& 0xFE = 0 &&& 0xFE
  rw [hS]
  rfl

/-! ## The places where the field stays asked, and the test -/

/-- **The places where the field `ctlKeep` stays asked**, for a program: the castle's loop of rows (from `CRendLoop` to `ChkCFloor`) and the store of
`RenderUnderPart` -/
def residC (sy : Syms) (P : PoleNear.NearP) (pc : UInt16) : Bool := (decide (sy.CRendLoop ≤ pc) && decide (pc < sy.ChkCFloor)) || pc == P.rup

/-- **The places where the field `ctlKeep` stays asked** -/
def ResidC (sy : Syms) (m0 : Machine) (m : Machine) : Prop := residC sy (PoleNear.nearOf sy m0) m.pc = true

/-- the new places are some of round 36's -/
theorem residC_old {m0 : Machine} {m : Machine} (h : ResidC sy m0 m) : PoleNear.ResidC sy m0 m := by
  unfold ResidC residC at h
  unfold PoleNear.ResidC PoleNear.residC
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **What the walk asks at a state**: nothing at the area parser's store of a column; elsewhere `PoleNear.missT` for the control byte, or a place of
`residC` -/
def okO (sy : Syms) (P : PoleNear.NearP) (E : Env) (A : AS) : Bool := A.pc == P.store || PoleNear.missT P.ctlI E A || residC sy P A.pc

/-! ## The search and the table: no part of the proof -/

/-- the search of the whole frame from the two states of a frame's start, with `SideRange`'s table, the splits of `SideLoop`, `SideAcross.fixP` after each
step and the test `ok` -/
def searchO (sy : Syms) (m0 : Machine) (ok : AS → Bool) : SideAcross.St :=
  let S := FrameKeep.spotOf sy m0
  let G := guardO sy m0
  let E := PipeEntryRule.envOf m0
  let key := PoleNear.keyN sy (PoleNear.shufE sy m0) S G
  let X := [startO sy m0 false, startO sy m0 true].foldl (SideRange.routeB S G SideRange.zKeep key) {}
  (SideAcross.searchI S G E key (aRows E).toArray (SideLoop.spL sy E) ok (FrameKeep.ctlI sy) SideRange.zKeep SideRange.zKeep [(sI sy m0, 0xFE)]
    SideRange.wLim 1000000000 { P := { X } }).1

/-- **The walk's table** -/
def cfgO (sy : Syms) (m0 : Machine) : SideRange.CfgR :=
  let S := FrameKeep.spotOf sy m0
  let G := guardO sy m0
  let E := PipeEntryRule.envOf m0
  let P := PoleNear.nearOf sy m0
  let key := PoleNear.keyN sy (PoleNear.shufE sy m0) S G
  let q := FrameKeep.tableOfKW key (searchO sy m0 (okO sy P E)).P.X
  { E, ops := (aRows E).toArray, S, G, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, W := SideRange.wLim,
    sp := SideLoop.spL sy E, ok := okO sy P E }

/-- **The check on the ROM**: the walk (`SideAcross.walkP`) from every piece of every state of the table and from the two states of a frame's start -/
def oCheck (sy : Syms) (m0 : Machine) : Bool :=
  let C := cfgO sy m0
  SideAcross.tableOKP C (FrameKeep.ctlI sy) FrameKeep.fuelK && SideAcross.walkP C (FrameKeep.ctlI sy) FrameKeep.fuelK (startO sy m0 false) &&
    SideAcross.walkP C (FrameKeep.ctlI sy) FrameKeep.fuelK (startO sy m0 true)

/-- the search's failures and the table's size, for a program (no part of the proof) -/
def oFails (sy : Syms) (m0 : Machine) : Nat × List (Nat × Nat) × Nat :=
  let R := (searchO sy m0 (okO sy (PoleNear.nearOf sy m0) (PipeEntryRule.envOf m0))).P
  (R.X.fails, R.X.failPcs.toList, R.X.done.size)

/-! ## The walk up to the first store of the routine, the mode or the task -/

section
variable {C : SideRange.CfgR} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- **The walk: each instruction of the frame up to the first store of a byte of `l` by its address meets `ok` in a state that covers it** (as
`PoleNear.ok_prefix`, for the walk `SideAcross.walkP`, whose split covers every machine) -/
theorem ok_prefixP (hsp : SideAcross.CovH C.E F (fun _ => True) C.sp) (ht : SideAcross.tableOKP C l Fu = true) (hkl : C.kl = C.t.map knownOf)
    (hops : C.ops = (aRows C.E).toArray) {m : Machine} {i : UInt8} {Fu' : Nat} {A : AS} (hw : SideAcross.walkP C l Fu' A = true)
    (hs : Sim C.E F A (trace m i 0)) (hcl : ∀ j, (trace m i j).frame = m.frame → CleanK C.G C.S.store (trace m i j)) :
    ∀ k, (∀ j, j ≤ k → storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) → (trace m i k).frame = m.frame →
      ∃ B, Sim C.E F B (trace m i k) ∧ C.ok B = true := by
  have key : ∀ d, (∀ j, j < d → storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) →
      (∃ A, SideAcross.LiveP C l F A (trace m i d) ∧ (trace m i d).frame = m.frame) ∨ (trace m i d).frame = m.frame + 1 := by
    intro d
    induction d with
    | zero => exact fun _ => Or.inl ⟨A, ⟨hs, Fu', hw⟩, rfl⟩
    | succ d ih =>
      intro hx
      rcases ih (fun j hj => hx j (by omega)) with ⟨A, h1, h2⟩ | h1
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i d).frame ≥ m.frame + 1 || (trace m i d).halted) = true) := by simp [h2, hh]
        have e : trace m i (d + 1) = (go step (trace m i d)).2 := by
          show nxt (m.frame + 1) (trace m i d) = _
          simp only [nxt, if_neg hn]
        rw [e]
        rcases (SideAcross.live_stepP hsp ht hkl hops h1 (hcl d h2) trivial (hx d (by omega))).2 with ⟨A', a1, _, a3, _⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h2]⟩
        · exact Or.inr (by rw [a1, h2])
      · have hst : ((trace m i d).frame ≥ m.frame + 1 || (trace m i d).halted) = true := by simp [h1]
        have e : trace m i (d + 1) = trace m i d := by
          show nxt (m.frame + 1) (trace m i d) = _
          simp only [nxt, if_pos hst]
        rw [e]
        exact Or.inr h1
  intro k hx hf
  rcases key k (fun j hj => hx j (by omega)) with ⟨A, h1, h2⟩ | h1
  · exact ⟨A, h1.1, (SideAcross.live_stepP hsp ht hkl hops h1 (hcl k h2) trivial (hx k (Nat.le_refl _))).1⟩
  · omega

end

/-! ## On the ROM: one frame, and the frames up to the touch's frame -/

section Frames
variable {m0 : Machine}

theorem cov_spL : SideAcross.CovH (PipeEntryRule.envOf m0) F (fun _ => True) (SideLoop.spL sy (PipeEntryRule.envOf m0)) :=
  fun A m _ hs => SideLoop.cov_spL sy A m hs

/-- **One frame that starts with `InvS`**: up to its first store of the routine, the mode or the task by its address, each instruction of the frame but the
parser's store of a column writes the control byte through an index or a pointer only at a place of `ResidC`. `hc` is the check on the ROM; `hcl` is `CleanK`
of `FrameKeep.guardE` on the instructions of the frame (the field `keep.cleanE`); `hkb` is `PoleTileKeep.KeepB` on them (the field `keepB`) -/
theorem off_frame (hc : oCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hS : InvS sy m0 m)
    (hcl : ∀ j, (trace m i j).frame = m.frame → CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hkb : ∀ j, (trace m i j).frame = m.frame → PoleTileKeep.KeepB sy m0 (trace m i j)) :
    ∀ k, (∀ j, j < k → FrameKeep.CtlStore sy (trace m i j) = false) → (trace m i k).frame = m.frame → (trace m i k).pc ≠ (PoleBcol.bcOf sy m0).store →
      ¬ ResidC sy m0 (trace m i k) → NoW (PoleBcol.bcOf sy m0).ctlI (trace m i k) := by
  intro k hx hf hpc hr
  cases hk : FrameKeep.CtlStore sy (trace m i k) with
  | true => exact PoleNear.noW_of_storesTo hk _
  | false =>
    simp only [oCheck, Bool.and_eq_true] at hc
    obtain ⟨⟨ht, hw0⟩, hw1⟩ := hc
    obtain ⟨b, hs⟩ := sim_startO h0 hS
    have hs0 : Sim (PipeEntryRule.envOf m0) (m.frame, 2) (startO sy m0 b) (trace m i 0) := { hs with pad := TaintRun.mem_top _ }
    have hw : SideAcross.walkP (cfgO sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK (startO sy m0 b) = true := by
      cases b with
      | false => exact hw0
      | true => exact hw1
    have hx' : ∀ j, j ≤ k → storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := by
      intro j hj
      rcases Nat.lt_or_ge j k with h | h
      · exact hx j h
      · rw [show j = k by omega]; exact hk
    obtain ⟨B, hsB0, hok⟩ := ok_prefixP (C := cfgO sy m0) cov_spL ht rfl rfl hw hs0
      (fun j hj => cleanK_O (hcl j hj) (noW_of_keepB (hkb j hj))) k hx' hf
    have hsB : Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (trace m i k) := hsB0
    have hB : B.pc ≠ (PoleBcol.bcOf sy m0).store := by rw [← hsB.pc]; exact hpc
    have hok' : okO sy (PoleNear.nearOf sy m0) (PipeEntryRule.envOf m0) B = true := hok
    simp only [okO, Bool.or_eq_true, beq_iff_eq] at hok'
    rcases hok' with (h | h) | h
    · exact absurd h hB
    · exact PoleNear.noW_of_missT hsB h
    · exact absurd (show residC sy (PoleNear.nearOf sy m0) (trace m i k).pc = true by rw [hsB.pc]; exact h) hr

/-- **On every frame up to the touch's frame that starts with `InvS`**, up to its first store of the routine, the mode or the task by its address, each
instruction of the frame but the parser's store of a column writes the control byte through an index or a pointer only at a place of `ResidC`. `hcK` is the
check of the walk of `FrameKeep` (every frame starts in control), `hc` the check of this file, `hkb` the field `keepB` -/
theorem off_frames {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hcK : FrameKeep.keepCheckOf sy m0 = true) (hc : oCheck sy m0 = true)
    (Fr : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (hkb : ∀ n, n < Fr.ix g → ∀ k, PoleTileKeep.KeepB sy m0 (trace (Fr.all n) (Fr.inp n) k)) :
    ∀ n, n < Fr.ix g → InvS sy m0 (Fr.all n) → ∀ k, (∀ j, j < k → FrameKeep.CtlStore sy (trace (Fr.all n) (Fr.inp n) j) = false) →
      (trace (Fr.all n) (Fr.inp n) k).frame = (Fr.all n).frame → (trace (Fr.all n) (Fr.inp n) k).pc ≠ (PoleBcol.bcOf sy m0).store →
      ¬ ResidC sy m0 (trace (Fr.all n) (Fr.inp n) k) → NoW (PoleBcol.bcOf sy m0).ctlI (trace (Fr.all n) (Fr.inp n) k) := by
  intro n hn hS
  obtain ⟨a1, _⟩ := Fr.all_start hcK hs0 h0 n hn
  exact off_frame hc a1 hS (fun j _ => Fr.cleanE n hn j) (fun j _ => hkb n hn j)

/-- **`InvS` at each frame's start up to the touch's frame** (`PoleTileKeep.frames_keepY`), for a route that has its hypotheses -/
theorem invS_frames {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hcK : FrameKeep.keepCheckOf sy m0 = true)
    (hcY : PoleTileKeep.keepCheckOfY sy m0 = true) (Fr : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0))
    (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0)) (hw0 : FrameKeep.Watched (PoleTileKeep.watchB sy m0) (seq 0))
    (hm0 : PoleTileWalk.ColMap (PoleFrame.spotsF sy m0) (seq 0))
    (hkb : ∀ n, n + 1 < Fr.ix g → ∀ k, PoleTileKeep.KeepB sy m0 (trace (Fr.all n) (Fr.inp n) k))
    (hb : ∀ n, n + 1 < Fr.ix g → ∀ k, PoleTileWalk.BufAt (PoleFrame.spotsF sy m0) (trace (Fr.all n) (Fr.inp n) k)) :
    ∀ n, n < Fr.ix g → InvS sy m0 (Fr.all n) := by
  intro n hn
  have e := (PoleTileKeep.frames_keepY hcK hcY Fr hs0 h0 hw0 hm0 hkb hb n hn).2 (PoleTileKeep.sprI sy m0, 0xFE, 0) (by simp [PoleTileKeep.watchB])
  show (Fr.all n).ram.get! (PoleTileKeep.sprI sy m0) &&& 0xFE = 0
  dsimp only at e
  rw [e]
  rfl

end Frames

end Smbrta.PoleOffset

namespace Smbrta.PoleNear

variable {sy : Syms}

/-- **The check of `PoleNear` from round 37**: round 36's walk (`nCheckN`) and the walk of `PoleOffset` (`PoleOffset.oCheck`) -/
def nCheck (sy : Syms) (m0 : Machine) : Bool := nCheckN sy m0 && PoleOffset.oCheck sy m0

theorem nCheck_n {m0 : Machine} (h : nCheck sy m0 = true) : nCheckN sy m0 = true := by
  simp only [nCheck, Bool.and_eq_true] at h
  exact h.1

theorem nCheck_o {m0 : Machine} (h : nCheck sy m0 = true) : PoleOffset.oCheck sy m0 = true := by
  simp only [nCheck, Bool.and_eq_true] at h
  exact h.2

end Smbrta.PoleNear
