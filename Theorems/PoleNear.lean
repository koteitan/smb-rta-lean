import Theorems.PoleBcol
import Theorems.SideLoop
import Theorems.OpenStore

/-!
# Above ground: the stores through an index or a pointer that may reach the control byte or the block buffer's column

Round 35 asked two fields on each instruction of the frames from control: a store through an index or a pointer does not write the screen buffers' control byte
(`PoleJoin.Run.ctlKeep`, `PoleCoin.CtlR`) or the block buffer's column `B` (`PoleJoin.Run.bKeep`, `PoleBcol.BcR`). Here one walk of each whole frame proves both at
almost every store (`near_frame`, `near_frames`); the fields stay asked only at the stores of `ResidC` and `ResidB`.

The walk is that of part e's `SideRange` (`SideRange.walkR`, with bounds on `X` and `Y` at the table's states and splits of them), started at the frame's start,
with the guard `FrameKeep.guardE` (the field `keep.cleanE`). A path stops at an instruction that writes the routine, the mode or the task by its address
(`FrameKeep.storesTo`), so on the touch's frame it covers the instructions up to the first such store. At each store through an index or a pointer (the opcodes
of `PushTimer.wOps`) it asks, for each of the two bytes, that the store is one that `PoleKeepFar.farStore` settles, or that every target that the state allows
misses the byte (`missT`, with `SideRange.missK`), or that the store is one of the places where the field stays (`residC`, `residB`). At the area parser's
store of a column it asks nothing: there the walk of `PoleBcol` knows `B`, so it knows the target (`PoleBcol.missS`, `PoleBcol.frames_bcol`).

The places where the walk does not know enough:
* for the control byte (`residC`): a store through a pointer in the code of the head's collision with a block (its pointer comes from his position); the
  castle's loop of rows (from `CRendLoop` to `ChkCFloor`) and the store of `RenderUnderPart`, which draw rows from a row read from the area's data; the walk
  does not know that this row is in the screen;
* for `B` (`residB`): every store through a pointer but the parser's store of a column. They write the block buffers, whose last byte is right before `B`;
  the walk does not know the row there.

The table's key (`keyN`) also holds `X`, `Y` and the zero page byte 0 in the code of `SideRange.residB` and in the sprites' shuffle (`SpriteShuffler`), so that
the states of a loop with a counter are not joined; it is no part of what the walk proves. The search that makes the table is no part of the proof (`searchN`);
the check is `nCheck`. A test for the coin's tiles in the block buffers (`missB`, `bufAt_of_missB`) is proved but not used: the walk does not know enough for it.
There is no game data in this file. Page: `1-1/f-6-17-19-PoleNear.md`.
-/

namespace Smbrta.PoleNear

open TaintRun (AS Env Sim AB aRows AM Cov)
open PipeTransitionAll (go)
open PipeEntryRule (trace nxt)
open PipeWrites (Guard FrameStart wTarget opAt knownOf)
open FrameKeep (CleanK storesTo)
open PoleBcol (NoW)

variable {sy : Syms}

/-! ## The test at a store -/

/-- `PoleKeepFar.farStore` on a state: the instruction and its two next bytes in the program's half, and a store through an absolute address and an index from whose
base no index reaches a byte of `pl`, or a store through the zero page and `X` while no byte of `pl` is in the zero page -/
def farA (pl : List Nat) (E : Env) (A : AS) : Bool :=
  decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
    (PositionKeep.absFarAt pl E.prg E.mask A.pc || (PoleKeepFar.zpXOps.contains (SideRange.opA E A) && pl.all fun i => decide (256 ≤ i)))

/-- **What the walk asks at a state for the byte `s`**: at a store through an index or a pointer, the instruction and its two next bytes in the program's half,
and `farA` or every target that the state allows misses the byte (`SideRange.missK`) -/
def missT (s : Nat) (E : Env) (A : AS) : Bool :=
  !PushTimer.wOps.contains (SideRange.opA E A) ||
    (decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) && (farA [s] E A || SideRange.missK s E A))

theorem farA_eq {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (pl : List Nat) : farA pl E A = PoleKeepFar.farStore pl m := by
  unfold farA PoleKeepFar.farStore SideRange.opA PipeWrites.opAt
  rw [hs.prg, hs.mask, hs.pc]

/-- **`missT` gives `NoW`** (the proof of `SideRange.okR_spec`, for any byte) -/
theorem noW_of_missT {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} {s : Nat} (hs : Sim E F A m) (h : missT s E A = true) : NoW s m := by
  intro t ht hlt heq
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = SideRange.opnd E A := by
    unfold PositionKeep.operandAt SideRange.opnd; rw [hs.prg, hs.mask, hs.pc]
  have hw : PushTimer.wOps.contains (SideRange.opA E A) = true := by rw [← hop]; exact List.contains_iff_mem.2 (PushTimer.wTarget_ops ht)
  unfold missT at h
  rw [hw] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨_, hp1⟩, hp2⟩, hc⟩ := h
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hp2' : 0x8000 ≤ m.pc + 1 + 1 := by rw [hs.pc]; exact hp2
  rcases hc with hf | hmk
  · rw [farA_eq hs] at hf
    exact PoleKeepFar.far_target hf t ht hlt (by rw [heq]; exact List.mem_singleton.2 rfl)
  · unfold SideRange.missK at hmk
    unfold PipeWrites.wTarget at ht
    generalize hop2 : SideRange.opA E A = op at hmk
    rw [hop, hop2] at ht
    dsimp only at hmk
    by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
    · exfalso
      have hz : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = false ∧ (op == 0x99) = false ∧ (op == 0x91) = false := by
        simp only [Bool.or_eq_true, beq_iff_eq] at c1
        rcases c1 with ((e | e) | e) | e <;> subst e <;> exact ⟨rfl, rfl, rfl⟩
      rw [if_neg (by simp [hz.1]), if_neg (by simp [hz.2.1]), if_neg (by simp [hz.2.2])] at hmk
      cases hmk
    · rw [if_neg c1] at ht
      by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
      · rw [if_pos c2, PushTimer.abx_t hp1' hp2', hoa] at ht
        rw [if_pos c2] at hmk
        have hm := List.all_eq_true.1 hmk m.x (SideRange.mem_valsAll hs.x)
        have e := Option.some.inj ht
        rw [e] at hm
        exact SideRange.miss_of (by simpa using hm) hlt heq
      · rw [if_neg c2] at ht
        rw [if_neg c2] at hmk
        by_cases c3 : (op == 0x99) = true
        · rw [if_pos c3, PushTimer.aby_t hp1' hp2', hoa] at ht
          rw [if_pos c3] at hmk
          have hm := List.all_eq_true.1 hmk m.y (SideRange.mem_valsAll hs.y)
          have e := Option.some.inj ht
          rw [e] at hm
          exact SideRange.miss_of (by simpa using hm) hlt heq
        · rw [if_neg c3] at hmk
          rw [if_neg c3] at ht
          by_cases c4 : (op == 0x91) = true
          · rw [if_pos c4, SideRange.izy_t hp1' hs.trk] at ht
            rw [if_pos c4] at hmk
            have hz : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = SideRange.zop E A := by unfold SideRange.zop; rw [hs.prg, hs.mask, hs.pc]
            rw [hz] at ht
            have e := Option.some.inj ht
            unfold SideRange.missP at hmk
            have hl0 : (SideRange.zop E A).toNat < 2048 := by have := (SideRange.zop E A).toNat_lt; omega
            have hh0 : (SideRange.zop E A + 1).toNat < 2048 := by have := (SideRange.zop E A + 1).toNat_lt; omega
            have hlo := hs.ram _ hl0
            have hhi := hs.ram _ hh0
            have hm1 := List.all_eq_true.1 hmk _ (SideRange.mem_valsAll hhi)
            have a1 := TaintRun.minv_le hlo
            have a2 := TaintRun.le_maxv hlo
            have a3 := TaintRun.minv_le hs.y
            have a4 := TaintRun.le_maxv hs.y
            have hm2 := List.all_eq_true.1 hm1 ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
                ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) (List.mem_range.2 (by omega))
            rw [show (A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat + ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
                ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) = (m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat by omega,
              SideRange.w16, e] at hm2
            exact SideRange.miss_of (by simpa using hm2) hlt heq
          · rw [if_neg c4] at hmk
            cases hmk

/-- **A store by its address is no store through an index or a pointer**: an instruction that `FrameKeep.storesTo` finds has no target of `wTarget` -/
theorem noW_of_storesTo {l : List Nat} {m : Machine} (h : storesTo l m.prg m.prgMask m.pc = true) (s : Nat) : NoW s m := by
  intro t ht
  have hw := PushTimer.wTarget_ops ht
  have hz : ∀ op ∈ FrameKeep.zpWrites, op ∉ PushTimer.wOps := by decide
  have ha : ∀ op ∈ FrameKeep.absWrites, op ∉ PushTimer.wOps := by decide
  unfold storesTo at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact absurd hw (hz _ (List.contains_iff_mem.1 h1))
  · exact absurd hw (ha _ (List.contains_iff_mem.1 h1))

/-! ## The coin's tiles: a test for the field `coinBuf`, not used yet

`missB` is a test that would give `PoleTileWalk.BufAt` (the store leaves no tile of `Q` in the block buffers) at a store through an index or a pointer
(`bufAt_of_missB`). Asked in the walk of this file with the coin's places `PoleCoin.Coin.Q`, the search fails at more than 30 stores (round 36, measured): stores
through an absolute address and an index into the object arrays in the 256 bytes before the block buffers, where the walk does not know the index after a join
nor the byte stored, and the stores through a pointer whose byte comes from the RAM. So `coinBuf` stays as it is, and these lemmas are not used yet. -/

/-- `PoleKeepFar.farBuf` on a state -/
def farBufA (Q : PoleEntryRule.Spots) (E : Env) (A : AS) : Bool := farA (PoleKeepFar.bufL Q) E A && (PoleKeepFar.bufL Q).all fun i => decide (512 ≤ i)

theorem farBufA_eq {Q : PoleEntryRule.Spots} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) : farBufA Q E A = PoleKeepFar.farBuf Q m := by
  unfold farBufA PoleKeepFar.farBuf
  rw [farA_eq hs]

/-- the byte in A is neither of the two tiles of `Q`, as far as the state knows -/
def noTileA (Q : PoleEntryRule.Spots) (A : AS) : Bool := !SideRange.memB A.a Q.ball && !SideRange.memB A.a Q.shaft

/-- **Through a pointer**, for a set `P` of RAM indices: as `SideRange.missP`, every address that the state allows misses `P` -/
def missPR (P : Nat → Bool) (E : Env) (A : AS) : Bool :=
  let lo := A.getK (SideRange.zop E A).toNat
  let hi := A.getK (SideRange.zop E A + 1).toNat
  let dmin := lo.minv.toNat + A.y.minv.toNat
  let dmax := lo.maxv.toNat + A.y.maxv.toNat
  (SideRange.valsIn hi 0 255).all fun h => (List.range (dmax + 1 - dmin)).all fun d => (StepWrites.ramIdx (h.toNat * 256 + (dmin + d)).toUInt16).all fun i => !P i

/-- **Every target that the state allows misses the set `P`** (`SideRange.missK` for a set) -/
def missR (P : Nat → Bool) (E : Env) (A : AS) : Bool :=
  let op := SideRange.opA E A
  if op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E then
    (SideRange.valsIn A.x 0 255).all fun v => (StepWrites.ramIdx (SideRange.opnd E A + v.toUInt16)).all fun i => !P i
  else if op == 0x99 then (SideRange.valsIn A.y 0 255).all fun v => (StepWrites.ramIdx (SideRange.opnd E A + v.toUInt16)).all fun i => !P i
  else if op == 0x91 then missPR P E A
  else false

/-- **What the walk asks at a state for the block buffers and the tiles of `Q`**: at a store through an index or a pointer, the instruction and its two next bytes in
the program's half, and the store is one that `farBuf` settles, or an `STA` (of `PoleKeepFar.staOps`) with no interrupt pending of a byte that is not one of the
tiles, or every target that the state allows misses the block buffers -/
def missB (Q : PoleEntryRule.Spots) (E : Env) (A : AS) : Bool :=
  !PushTimer.wOps.contains (SideRange.opA E A) ||
    (decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
      (farBufA Q E A || (PoleKeepFar.staOps.contains (SideRange.opA E A) && !A.nmi && noTileA Q A) || missR (PoleTileWalk.inBufB Q) E A))

theorem missR_spec {P : Nat → Bool} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1)
    (h : missR P E A = true) {t : UInt16} (ht : wTarget (opAt m) m = some t) : ∀ i ∈ StepWrites.ramIdx t, P i = false := by
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc = SideRange.opnd E A := by
    unfold PositionKeep.operandAt SideRange.opnd; rw [hs.prg, hs.mask, hs.pc]
  have fin : ∀ {u : UInt16}, (StepWrites.ramIdx u).all (fun i => !P i) = true → u = t → ∀ i ∈ StepWrites.ramIdx t, P i = false := by
    intro u hu e i hi
    rw [e] at hu
    simpa using List.all_eq_true.1 hu i hi
  unfold missR at h
  unfold PipeWrites.wTarget at ht
  generalize hop2 : SideRange.opA E A = op at h
  rw [hop, hop2] at ht
  dsimp only at h
  by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
  · exfalso
    have hz : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = false ∧ (op == 0x99) = false ∧ (op == 0x91) = false := by
      simp only [Bool.or_eq_true, beq_iff_eq] at c1
      rcases c1 with ((e | e) | e) | e <;> subst e <;> exact ⟨rfl, rfl, rfl⟩
    rw [if_neg (by simp [hz.1]), if_neg (by simp [hz.2.1]), if_neg (by simp [hz.2.2])] at h
    cases h
  · rw [if_neg c1] at ht
    by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
    · rw [if_pos c2, PushTimer.abx_t hp1 hp2, hoa] at ht
      rw [if_pos c2] at h
      exact fin (List.all_eq_true.1 h m.x (SideRange.mem_valsAll hs.x)) (Option.some.inj ht)
    · rw [if_neg c2] at ht
      rw [if_neg c2] at h
      by_cases c3 : (op == 0x99) = true
      · rw [if_pos c3, PushTimer.aby_t hp1 hp2, hoa] at ht
        rw [if_pos c3] at h
        exact fin (List.all_eq_true.1 h m.y (SideRange.mem_valsAll hs.y)) (Option.some.inj ht)
      · rw [if_neg c3] at h
        rw [if_neg c3] at ht
        by_cases c4 : (op == 0x91) = true
        · rw [if_pos c4, SideRange.izy_t hp1 hs.trk] at ht
          rw [if_pos c4] at h
          have hz : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = SideRange.zop E A := by unfold SideRange.zop; rw [hs.prg, hs.mask, hs.pc]
          rw [hz] at ht
          have e := Option.some.inj ht
          unfold missPR at h
          have hl0 : (SideRange.zop E A).toNat < 2048 := by have := (SideRange.zop E A).toNat_lt; omega
          have hh0 : (SideRange.zop E A + 1).toNat < 2048 := by have := (SideRange.zop E A + 1).toNat_lt; omega
          have hlo := hs.ram _ hl0
          have hhi := hs.ram _ hh0
          have hm1 := List.all_eq_true.1 h _ (SideRange.mem_valsAll hhi)
          have a1 := TaintRun.minv_le hlo
          have a2 := TaintRun.le_maxv hlo
          have a3 := TaintRun.minv_le hs.y
          have a4 := TaintRun.le_maxv hs.y
          have hm2 := List.all_eq_true.1 hm1 ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
              ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) (List.mem_range.2 (by omega))
          rw [show (A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat + ((m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat -
              ((A.getK (SideRange.zop E A).toNat).minv.toNat + A.y.minv.toNat)) = (m.ram.get! (SideRange.zop E A).toNat).toNat + m.y.toNat by omega,
            SideRange.w16] at hm2
          exact fin hm2 e
        · rw [if_neg c4] at h
          cases h

/-- **A store through an index or a pointer stores only at its target**: a byte that the step may change is the RAM index of the target of `wTarget` -/
theorem locs_wTarget {m : Machine} {i : Nat} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hop : opAt m ∈ OpenStore.wtOps)
    (hi : i ∈ StepWrites.stepLocs m) : ∃ t, wTarget (opAt m) m = some t ∧ i ∈ StepWrites.ramIdx t := by
  unfold StepWrites.stepLocs at hi
  rw [if_neg (by simp [hn]), if_neg (by simp [hh]), TaintRun.fetch_rom hp] at hi
  have hop' : m.prg.get! (m.pc &&& m.prgMask).toNat = opAt m := rfl
  simp only [hop'] at hi
  simp only [OpenStore.wtOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨e1, e2⟩ := OpenStore.wt_zpx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_zpx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_zpx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_zpx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_abx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_abx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_abx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_abx (m := m) (by simp [h]); rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_aby (m := m) h; rw [e2] at hi; exact ⟨_, e1, hi⟩
  · obtain ⟨e1, e2⟩ := OpenStore.wt_izy (m := m) h; rw [e2] at hi; exact ⟨_, e1, hi⟩

/-- **`missB` gives `BufAt`** (the store leaves no tile of `Q` in the block buffers), when the block buffers are past the stack -/
theorem bufAt_of_missB {Q : PoleEntryRule.Spots} (hlo : 512 ≤ Q.bufLo) {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m)
    (h : missB Q E A = true) : PoleTileWalk.BufAt Q m := by
  intro hsome
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hsome
  have hop : PipeWrites.opAt m = SideRange.opA E A := by unfold PipeWrites.opAt SideRange.opA; rw [hs.prg, hs.mask, hs.pc]
  have hwo := PushTimer.wTarget_ops ht
  have hw : PushTimer.wOps.contains (SideRange.opA E A) = true := by rw [← hop]; exact List.contains_iff_mem.2 hwo
  unfold missB at h
  rw [hw] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hp0, hp1⟩, hp2⟩, hc⟩ := h
  have hp0' : 0x8000 ≤ m.pc := by rw [hs.pc]; exact hp0
  have hp1' : 0x8000 ≤ m.pc + 1 := by rw [hs.pc]; exact hp1
  have hp2' : 0x8000 ≤ m.pc + 1 + 1 := by rw [hs.pc]; exact hp2
  rcases hc with (hf | ⟨⟨hsta, hnmi⟩, hnt⟩) | hmr
  · rw [farBufA_eq hs] at hf
    exact PoleKeepFar.noTile_of_far hf
  · have hn : m.nmiPending = false := by rw [hs.nmi]; exact hnmi
    have hst : PoleKeepFar.staOps.contains (opAt m) = true := by rw [hop]; exact hsta
    intro i _ _ hch htile
    rw [PoleKeepFar.sta_step hn hs.halted hp0' hp1' hp2' hst i hch] at htile
    simp only [noTileA, Bool.and_eq_true, Bool.not_eq_true'] at hnt
    rcases htile with e | e
    · have := SideRange.memB_of (b := A.a) (x := m.a) hs.a
      rw [e] at this
      rw [this] at hnt
      cases hnt.1
    · have := SideRange.memB_of (b := A.a) (x := m.a) hs.a
      rw [e] at this
      rw [this] at hnt
      cases hnt.2
  · intro i h1 h2 hch _
    exfalso
    have hloc : i ∈ StepWrites.stepLocs m := by
      by_cases hl : i ∈ StepWrites.stepLocs m
      · exact hl
      · exact absurd (StepWrites.step_ram m i hl) hch
    cases hn : m.nmiPending with
    | true =>
      unfold StepWrites.stepLocs at hloc
      rw [if_pos hn] at hloc
      have := PositionWriters.stk_range 3 _ _ hloc
      omega
    | false =>
      have hwt : opAt m ∈ OpenStore.wtOps := by
        have : OpenStore.wtOps = PushTimer.wOps := rfl
        rw [this]; exact hwo
      obtain ⟨t', ht', hit⟩ := locs_wTarget hn hs.halted hp0' hwt hloc
      have hP := missR_spec hs hp1' hp2' hmr ht' i hit
      simp [PoleTileWalk.inBufB, h1, h2] at hP

/-! ## The places where the fields stay asked -/

/-- the places, from the code and the symbols: the parser's store of a column, the RAM indices of the control byte and of `B`, the store of
`RenderUnderPart` (its first `STA abs,X`) -/
structure NearP where
  store : UInt16
  ctlI : Nat
  bI : Nat
  rup : UInt16
  deriving Inhabited

def nearOf (sy : Syms) (m0 : Machine) : NearP :=
  { store := (PoleBcol.bcOf sy m0).store, ctlI := (PoleBcol.bcOf sy m0).ctlI, bI := (PoleBcol.bcOf sy m0).bI,
    rup := PipeEntryRule.findOp m0 sy.RenderUnderPart 0x9D 64 }

/-- **The places where the field `ctlKeep` stays asked**, for a program: a store through a pointer in the code of `SideRange.residB` but the parser's store of a
column, the castle's loop of rows (from `CRendLoop` to `ChkCFloor`), and the store of `RenderUnderPart` -/
def residC (sy : Syms) (P : NearP) (pc : UInt16) (op : UInt8) : Bool :=
  (SideRange.residB sy pc && op == 0x91 && pc != P.store) || (decide (sy.CRendLoop ≤ pc) && decide (pc < sy.ChkCFloor)) || pc == P.rup

/-- **The places where the field `bKeep` stays asked**, for a program: a store through a pointer (`STA (zp),Y`) but the parser's store of a column -/
def residB (P : NearP) (pc : UInt16) (op : UInt8) : Bool := op == 0x91 && pc != P.store

/-- **The places where the field `ctlKeep` stays asked** -/
def ResidC (sy : Syms) (m0 : Machine) (m : Machine) : Prop := residC sy (nearOf sy m0) m.pc (opAt m) = true

/-- **The places where the field `bKeep` stays asked** -/
def ResidB (sy : Syms) (m0 : Machine) (m : Machine) : Prop := residB (nearOf sy m0) m.pc (opAt m) = true

/-- **What the walk asks at a state**: nothing at the parser's store of a column; elsewhere `missT` for the control byte or a place of `residC`, and `missT`
for `B` or a place of `residB` -/
def okN (sy : Syms) (P : NearP) (E : Env) (A : AS) : Bool :=
  A.pc == P.store || ((missT P.ctlI E A || residC sy P A.pc (SideRange.opA E A)) && (missT P.bI E A || residB P A.pc (SideRange.opA E A)))

/-! ## The search and the table: no part of the proof -/

/-- the last instruction of the sprites' shuffle (its return) -/
def shufE (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 sy.SpriteShuffler 0x60 128

/-- in the sprites' shuffle, whose last instruction is `se` -/
def inShuf (sy : Syms) (se : UInt16) (pc : UInt16) : Bool := decide (sy.SpriteShuffler ≤ pc) && decide (pc ≤ se)

/-- **The table's key**: `PrevKeep.keyP`, and in the code of `SideRange.residB` and in the sprites' shuffle (to `se`) also what the state knows of `X`, `Y` and the
zero page byte 0. No part of the proof. -/
def keyN (sy : Syms) (se : UInt16) (S : FrameKeep.Spot) (G : Guard) (A : AS) : Nat :=
  let k0 := PrevKeep.keyP S G [] A
  if SideRange.residB sy A.pc || inShuf sy se A.pc then ((k0 * 65536 + SideLoop.numB A.x) * 65536 + SideLoop.numB A.y) * 65536 + SideLoop.numB (A.getK 0) else k0

/-- the search of the whole frame from the two states of a frame's start, with `SideRange`'s table and the splits of `SideLoop` -/
def searchN (sy : Syms) (m0 : Machine) (l : List Nat) (ok : AS → Bool) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let key := keyN sy (shufE sy m0) S G
  let X := [FrameKeep.startK G [] false, FrameKeep.startK G [] true].foldl (SideRange.routeB S G SideRange.zKeep key) {}
  SideRange.searchR S G E key (aRows E).toArray (SideLoop.spL sy E) ok l SideRange.zKeep SideRange.wLim { X }

/-- **The walk's table** -/
def cfgN (sy : Syms) (m0 : Machine) : SideRange.CfgR :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardE sy m0
  let E := PipeEntryRule.envOf m0
  let P := nearOf sy m0
  let key := keyN sy (shufE sy m0) S G
  let q := FrameKeep.tableOfKW key (searchN sy m0 (FrameKeep.ctlI sy) (okN sy P E)).X
  { E, ops := (aRows E).toArray, S, G, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2, key, W := SideRange.wLim,
    sp := SideLoop.spL sy E, ok := okN sy P E }

/-- **The check on the ROM**: the walk from every piece of every state of the table and from the two states of a frame's start -/
def nCheck (sy : Syms) (m0 : Machine) : Bool :=
  let C := cfgN sy m0
  let G := FrameKeep.guardE sy m0
  SideRange.tableOK C (FrameKeep.ctlI sy) FrameKeep.fuelK && SideRange.walkR C (FrameKeep.ctlI sy) FrameKeep.fuelK (FrameKeep.startK G [] false) &&
    SideRange.walkR C (FrameKeep.ctlI sy) FrameKeep.fuelK (FrameKeep.startK G [] true)

/-- the search's failures, for a program (no part of the proof) -/
def nFails (sy : Syms) (m0 : Machine) : Nat × List (Nat × Nat) × Nat :=
  let R := searchN sy m0 (FrameKeep.ctlI sy) (okN sy (nearOf sy m0) (PipeEntryRule.envOf m0))
  (R.X.fails, R.X.failPcs.toList, R.X.done.size)

/-! ## The walk up to the first store of the routine, the mode or the task -/

section
variable {C : SideRange.CfgR} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- **The walk: each instruction of the frame up to the first store of a byte of `l` by its address meets `ok` in a state that covers it** (`SideRange.okR_all`,
from the frame's start, for a frame whose later instructions may store to `l`) -/
theorem ok_prefix (hsp : Cov C.E F C.sp) (ht : SideRange.tableOK C l Fu = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {Fu' : Nat} {A : AS} (hw : SideRange.walkR C l Fu' A = true) (hs : Sim C.E F A (trace m i 0))
    (hcl : ∀ j, (trace m i j).frame = m.frame → CleanK C.G C.S.store (trace m i j)) :
    ∀ k, (∀ j, j ≤ k → storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) → (trace m i k).frame = m.frame →
      ∃ B, Sim C.E F B (trace m i k) ∧ C.ok B = true := by
  have key : ∀ d, (∀ j, j < d → storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) →
      (∃ A, SideRange.LiveR C l F A (trace m i d) ∧ (trace m i d).frame = m.frame) ∨ (trace m i d).frame = m.frame + 1 := by
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
        rcases (SideRange.live_stepR hsp ht hkl hops h1 (hcl d h2) (hx d (by omega))).2 with ⟨A', a1, _, a3, _⟩ | a1
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
  · exact ⟨A, h1.1, (SideRange.live_stepR hsp ht hkl hops h1 (hcl k h2) (hx k (Nat.le_refl _))).1⟩
  · omega

end

/-! ## On the ROM: one frame, and the frames up to the touch's frame -/

section Frames
variable {m0 : Machine}

/-- the start of a frame for the guard `FrameKeep.guardE`: the same as for `FrameKeep.guardK` -/
theorem start_E {m : Machine} (h : FrameKeep.StartK sy m0 m) : FrameStart (FrameKeep.guardE sy m0) (PipeEntryRule.envOf m0) m :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- **One frame in control**: up to its first store of the routine, the mode or the task by its address, each instruction of the frame but the parser's store
of a column writes the control byte through an index or a pointer only at a place of `ResidC`, and `B` only at a place of `ResidB`. `hc` is the check on the
ROM; `hcl` is `CleanK` of `FrameKeep.guardE` on the instructions of the frame (the field `keep.cleanE`) -/
theorem near_frame (hc : nCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ j, (trace m i j).frame = m.frame → CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i j)) :
    ∀ k, (∀ j, j < k → FrameKeep.CtlStore sy (trace m i j) = false) → (trace m i k).frame = m.frame → (trace m i k).pc ≠ (PoleBcol.bcOf sy m0).store →
      (¬ ResidC sy m0 (trace m i k) → NoW (PoleBcol.bcOf sy m0).ctlI (trace m i k)) ∧ (¬ ResidB sy m0 (trace m i k) → NoW (PoleBcol.bcOf sy m0).bI (trace m i k)) := by
  intro k hx hf hpc
  cases hk : FrameKeep.CtlStore sy (trace m i k) with
  | true => exact ⟨fun _ => noW_of_storesTo hk _, fun _ => noW_of_storesTo hk _⟩
  | false =>
    simp only [nCheck, Bool.and_eq_true] at hc
    obtain ⟨⟨ht, hw0⟩, hw1⟩ := hc
    obtain ⟨b, hs⟩ := FrameKeep.sim_startK (W := []) (E := PipeEntryRule.envOf m0) rfl (start_E h0) (fun _ h => by cases h)
    have hs0 : Sim (PipeEntryRule.envOf m0) (m.frame, 2) (FrameKeep.startK (FrameKeep.guardE sy m0) [] b) (trace m i 0) :=
      { hs with pad := TaintRun.mem_top _ }
    have hw : SideRange.walkR (cfgN sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK (FrameKeep.startK (FrameKeep.guardE sy m0) [] b) = true := by
      cases b with
      | false => exact hw0
      | true => exact hw1
    have hx' : ∀ j, j ≤ k → storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := by
      intro j hj
      rcases Nat.lt_or_ge j k with h | h
      · exact hx j h
      · rw [show j = k by omega]; exact hk
    obtain ⟨B, hsB0, hok⟩ := ok_prefix (C := cfgN sy m0) (SideLoop.cov_spL sy) ht rfl rfl hw hs0 hcl k hx' hf
    have hsB : Sim (PipeEntryRule.envOf m0) (m.frame, 2) B (trace m i k) := hsB0
    have hB : B.pc ≠ (PoleBcol.bcOf sy m0).store := by rw [← hsB.pc]; exact hpc
    have hop : SideRange.opA (PipeEntryRule.envOf m0) B = opAt (trace m i k) := by
      unfold PipeWrites.opAt SideRange.opA; rw [hsB.prg, hsB.mask, hsB.pc]
    have hok' : okN sy (nearOf sy m0) (PipeEntryRule.envOf m0) B = true := hok
    simp only [okN, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hok'
    rcases hok' with h | ⟨h1, h2⟩
    · exact absurd h hB
    · refine ⟨fun hr => ?_, fun hr => ?_⟩
      · rcases h1 with h | h
        · exact noW_of_missT hsB h
        · exact absurd (show residC sy (nearOf sy m0) (trace m i k).pc (opAt (trace m i k)) = true by rw [hsB.pc, ← hop]; exact h) hr
      · rcases h2 with h | h
        · exact noW_of_missT hsB h
        · exact absurd (show residB (nearOf sy m0) (trace m i k).pc (opAt (trace m i k)) = true by rw [hsB.pc, ← hop]; exact h) hr

/-- **On every frame up to the touch's frame**, up to its first store of the routine, the mode or the task by its address, each instruction of the frame but the
parser's store of a column writes the control byte through an index or a pointer only at a place of `ResidC`, and `B` only at a place of `ResidB`. `hcK` is the
check of the walk of `FrameKeep` (every frame starts in control), `hcN` the check of this file -/
theorem near_frames {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hcK : FrameKeep.keepCheckOf sy m0 = true) (hcN : nCheck sy m0 = true)
    (Fr : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0)) :
    ∀ n, n < Fr.ix g → ∀ k, (∀ j, j < k → FrameKeep.CtlStore sy (trace (Fr.all n) (Fr.inp n) j) = false) →
      (trace (Fr.all n) (Fr.inp n) k).frame = (Fr.all n).frame → (trace (Fr.all n) (Fr.inp n) k).pc ≠ (PoleBcol.bcOf sy m0).store →
      (¬ ResidC sy m0 (trace (Fr.all n) (Fr.inp n) k) → NoW (PoleBcol.bcOf sy m0).ctlI (trace (Fr.all n) (Fr.inp n) k)) ∧
      (¬ ResidB sy m0 (trace (Fr.all n) (Fr.inp n) k) → NoW (PoleBcol.bcOf sy m0).bI (trace (Fr.all n) (Fr.inp n) k)) := by
  intro n hn
  obtain ⟨a1, _⟩ := Fr.all_start hcK hs0 h0 n hn
  exact near_frame hcN a1 (fun j _ => Fr.cleanE n hn j)

end Frames

end Smbrta.PoleNear
