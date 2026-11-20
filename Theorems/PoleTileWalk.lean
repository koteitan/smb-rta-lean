import Theorems.PoleTiles

/-!
# The pole's tiles at the touch: the walk of the frame carries the map of the frame's start

`PoleFrame` follows the whole frame of the touch. At a read of the side check it asks `TileRead`: if the byte read is one of the pole's tiles, the read was in the
pole's column, with the page at most one before the pole's. That was the field `PoleJoin.Run.tiles`, one condition for every instruction of the frame up to the write.

Here the walk is run again on the same table, with two more tests on every state on the way (`walkP`):
* `okS`: the step writes no byte of the block buffers (`StepWrites.keepOK`), or it is a store through an index or a pointer (the opcodes of `PipeWrites.wTarget`);
* `pairOK`: a state right after the read of the side check comes from the read itself, with no NMI pending.

With them `TileRead` is no longer assumed. It is proved on the way (`no_write_frameP`), from:
* `ColMap` at the frame's start (one state): every pole's tile in the block buffers is in the pole's column;
* `BufAt` on each instruction: a store through an index or a pointer writes a pole's tile into the block buffers only in the pole's column (the other steps write
  nothing there: `okS`);
* `ReadPre` at each read of the side check: the read is in the RAM, in the block buffers, and if the byte there is a pole's tile in the pole's column, the page is at
  most one before the pole's.

So the map of the frame's start goes from step to step (`ColMap`), and at a read the byte read is the byte of the RAM at the read's address (`RoomBlocks.step_lda_izy`,
`RoomBlocks.readVal_eq`), which the map says is in the pole's column if it is one of the pole's tiles.

The map at the start of the touch's frame comes from the map at control: the walk of one whole frame in control of `FrameKeep` is run again with the test `okSK`
(`walkKS`), so with `BufAt` on each instruction every frame from control to the touch's frame keeps `ColMap` (`frame_colMap`, `frames_colMap`). The area parser draws
the pole's column with the pole's tiles; `BufAt` allows that, as the tiles go in the pole's column. The map at control comes from the rows of the change out of the
side pipe (`PoleTileCtl`).

There is no game data in this file. Page: `1-1/f-6-17-2-PoleTileWalk.md`.
-/

namespace Smbrta.PoleTileWalk

open PoleFrame
open PoleEntryRule (Spots onCol WriteStep Touches px)
open PipeEntryRule (trace)
open PipeTransitionAll (go)
open PipeWrites (Guard FrameStart okRt startG fuelG knownOf wTarget opAt)
open FrameKeep (CleanK)
open TaintRun (AS Env Sim AB aRows)
open PoleTiles (Tile)

/-! ## The conditions -/

/-- the RAM index `i` is in the block buffers -/
def inBufB (Q : Spots) (i : Nat) : Bool := decide (Q.bufLo ≤ i) && decide (i < Q.bufLo + Q.bufBytes)

/-- **The map at the start of the touch's frame** (one state): a pole's tile in the block buffers is in the pole's column -/
def ColMap (Q : Spots) (m : Machine) : Prop :=
  ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → Tile Q (m.ram.get! i) → onCol Q i = true

/-- the step of `m` writes a pole's tile into the block buffers only in the pole's column: a byte there that the step changes to a pole's tile is in the column -/
def NoTile (Q : Spots) (m : Machine) : Prop :=
  ∀ i, Q.bufLo ≤ i → i < Q.bufLo + Q.bufBytes → (go step m).2.ram.get! i ≠ m.ram.get! i → Tile Q ((go step m).2.ram.get! i) → onCol Q i = true

/-- **What is assumed of a store through an index or a pointer**: it writes a pole's tile into the block buffers only in the pole's column -/
def BufAt (Q : Spots) (m : Machine) : Prop := (wTarget (opAt m) m).isSome = true → NoTile Q m

/-- the RAM index of the read of the `LDA (zp),Y` at `m` -/
def readI (m : Machine) : Nat := (ScreenPage.readAddr m &&& 0x7FF).toNat

/-- **What is assumed of a read of the side check**, before it: the read is in the RAM, in the block buffers; if the byte there is a pole's tile in the pole's column,
the page is at most one before the pole's -/
def ReadPre (Q : Spots) (m : Machine) : Prop :=
  m.pc = Q.read → m.ram.get! Q.saveI ∈ Q.idx →
    ScreenPage.readAddr m < 0x2000 ∧ Q.bufLo ≤ readI m ∧ readI m < Q.bufLo + Q.bufBytes ∧
      (Tile Q (m.ram.get! (readI m)) → onCol Q (readI m) = true → Q.pg ≤ (m.ram.get! Q.pI).toNat + 1)

/-- `HypT` without `TileRead` -/
def HypR (T : Pole) (m : Machine) : Prop :=
  (m.pc = T.G.subs → px T.Q m < T.Q.left) ∧ (m.pc ∈ T.again → px T.Q m < T.Q.left) ∧ m.pc ∉ T.G.cuts

/-! ## The walk with the two tests -/

/-- the opcodes of the stores through an index or a pointer, as `PipeWrites.wTarget` -/
def idxOps : List UInt8 := [0x95, 0x94, 0xD6, 0xF6, 0x9D, 0xDE, 0xFE, 0x7E, 0x99, 0x91]

/-- the step writes no byte of the block buffers, or it is a store through an index or a pointer -/
def okS (T : Pole) (E : Env) (A : AS) : Bool :=
  StepWrites.keepOK E (inBufB T.Q) A || idxOps.contains (E.prg.get! (A.pc &&& E.mask).toNat)

/-- a state right after the read of the side check comes from the read, with no NMI pending -/
def pairOK (Q : Spots) (A B : AS) : Bool := B.pc != Q.read + 2 || (A.pc == Q.read && !A.nmi)

/-- `PoleFrame.walkT` with the two tests on every state on the way -/
def walkP (C : CfgT) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preT C.T A).all fun A₁ => okS C.T C.E A₁ && (kstepT C.T C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.T.G B && pairOK C.T.Q A₁ B && (B.k != A.k || (C.cut.get! B.pc.toNat != 0 && coverT C B) || walkP C n B)

/-- the facts of the ROM at the read: the `LDA (zp),Y`, in the ROM, with the pointer's two bytes at `ptrI` -/
def readOK (T : Pole) (E : Env) : Bool :=
  let Q := T.Q
  let z := E.prg.get! ((Q.read + 1) &&& E.mask).toNat
  decide (0x8000 ≤ Q.read) && decide (0x8000 ≤ Q.read + 1) && E.prg.get! (Q.read &&& E.mask).toNat == 0xB1 &&
    decide ((z.toUInt16 &&& 0x7FF).toNat = Q.ptrI) && decide (((z + 1).toUInt16 &&& 0x7FF).toNat = Q.ptrI + 1) &&
    T.G.idle != Q.read + 2

/-- the checks of `PoleFrame.frameCheck` before its walk -/
def frameBase (T : Pole) : Bool :=
  let G := T.G
  let Q := T.Q
  decide (G.rtI < 2048) && decide (Q.xI < 2048) && decide (Q.pI < 2048) && decide (Q.saveI < 2048) &&
  decide (Q.left = 256 * Q.pg + lowOf Q) && decide (lowOf Q < 256) && decide (1 ≤ Q.pg) && decide (Q.pg < 256) &&
  SideFrame.posCover (Q.pg - 1) && SideFrame.posCover (lowOf Q) && PoleEntryRule.tilesCover Q &&
  decide (G.late < dotsPerFrame) && okRt G (startG G false) && okRt G (startG G true)

theorem frameCheck_eq (T : Pole) (E : Env) : frameCheck T E = (frameBase T && (cfgOf T E).t.all (walkT (cfgOf T E) fuelG) &&
    walkT (cfgOf T E) fuelG (startG T.G false) && walkT (cfgOf T E) fuelG (startG T.G true)) := rfl

/-- **The check**: the checks of `PoleFrame.frameCheck`, the walk with the two tests, the facts at the read -/
def frameCheckP (T : Pole) (E : Env) : Bool :=
  frameBase T && (cfgOf T E).t.all (walkP (cfgOf T E) fuelG) && walkP (cfgOf T E) fuelG (startG T.G false) &&
    walkP (cfgOf T E) fuelG (startG T.G true) && readOK T E

/-! ## The walk with the tests is the walk -/

theorem walkT_of_walkP {C : CfgT} : ∀ {n : Nat} {A : AS}, walkP C n A = true → walkT C n A = true
  | 0, _, h => by simp [walkP] at h
  | n + 1, A, h => by
    simp only [walkP, walkT, List.all_eq_true] at h ⊢
    intro A₁ hA r hr
    have h1 := h A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at h1
    have h2 := h1.2 r hr
    cases r with
    | none => simp at h2
    | some B =>
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h2 ⊢
      obtain ⟨⟨h3, _⟩, h4⟩ := h2
      refine ⟨h3, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (walkT_of_walkP h4)

/-- the parts of `frameCheckP` -/
theorem parts_of_P {T : Pole} {E : Env} (h : frameCheckP T E = true) :
    frameBase T = true ∧ (cfgOf T E).t.all (walkP (cfgOf T E) fuelG) = true ∧ walkP (cfgOf T E) fuelG (startG T.G false) = true ∧
      walkP (cfgOf T E) fuelG (startG T.G true) = true ∧ readOK T E = true := by
  simp only [frameCheckP, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem frameCheck_of_P {T : Pole} {E : Env} (h : frameCheckP T E = true) : frameCheck T E = true := by
  obtain ⟨h1, h2, h3, h4, _⟩ := parts_of_P h
  rw [frameCheck_eq]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, Array.all_eq_true.2 fun i hi => walkT_of_walkP (Array.all_eq_true.1 h2 i hi)⟩, walkT_of_walkP h3⟩, walkT_of_walkP h4⟩

/-! ## One step -/

section
variable {C : CfgT} {Fu : Nat} {F : Nat × UInt8}

def LiveP (C : CfgT) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkP C n A = true

theorem cover_liveP (ht : C.t.all (walkP C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverT C B = true) : ∃ D, LiveP C F D m := by
  unfold coverT at h
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
theorem live_stepP (ht : C.t.all (walkP C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : ZoneOK C.T) (hr : C.T.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveP C F A m) (hc : CleanK C.T.G C.T.K.store m) (hp : PosAt C.T.Q C.T.ps m)
    (hh : HypT C.T m) :
    ∃ A₁ B, Sim C.E F A₁ m ∧ okS C.T C.E A₁ = true ∧ Sim C.E F B (go step m).2 ∧ pairOK C.T.Q A₁ B = true ∧
      (go step m).2.ram.get! C.T.G.rtI ≠ C.T.G.ev ∧ (F.1 < (go step m).2.frame ∨ ∃ A', LiveP C F A' (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkP] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preT hb hc hh hs
    obtain ⟨r, hr1, hB⟩ := s_kstepT hops hT hc hp hs1
    simp only [walkP, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨hok, hw1⟩ := hw1
    have hw2 := hw1 r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hw2
      obtain ⟨⟨h2, hpair⟩, h3⟩ := hw2
      refine ⟨A₁, B, hs1, hok, h1, hpair, PipeWrites.ne_of_okRt h2 (h1.ram _ hr), ?_⟩
      by_cases hk2 : B.k = 0
      · right
        rcases h3 with (h4 | ⟨_, h4⟩) | h4
        · rw [hk, hk2] at h4
          exact absurd rfl h4
        · exact cover_liveP ht hkl h1 hk2 h4
        · exact ⟨B, h1, hk2, n, h4⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The map from step to step -/

/-- an opcode of `idxOps` has a target -/
theorem target_isSome (op : UInt8) (m : Machine) (h : idxOps.contains op = true) : (wTarget op m).isSome = true := by
  simp [idxOps] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [wTarget]

theorem target_of_idx {m : Machine} (h : idxOps.contains (opAt m) = true) : (wTarget (opAt m) m).isSome = true :=
  target_isSome _ m h

/-- **The map goes on over a step that `okS` allows**: the step writes no byte of the block buffers, or it is a store through an index or a pointer, which writes a
pole's tile there only in the pole's column (`BufAt`) -/
theorem colMap_step {T : Pole} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hok : okS T E A = true) (hbuf : BufAt T.Q m)
    (hm : ColMap T.Q m) : ColMap T.Q (go step m).2 := by
  intro i h1 h2 ht
  simp only [okS, Bool.or_eq_true] at hok
  rcases hok with hk | hk
  · have e := StepWrites.keep_step hs hk i (by simp [inBufB, h1, h2])
    rw [e] at ht
    exact hm i h1 h2 ht
  · have hop : opAt m = E.prg.get! (A.pc &&& E.mask).toNat := by
      unfold opAt
      rw [hs.prg, hs.mask, hs.pc]
    rw [← hop] at hk
    have hn := hbuf (target_of_idx hk)
    by_cases he : (go step m).2.ram.get! i = m.ram.get! i
    · rw [he] at ht
      exact hm i h1 h2 ht
    · exact hn i h1 h2 he ht

/-! ## The read -/

theorem pagePenalty_y (b e : UInt16) (x : Machine) : (go (pagePenalty b e) x).2.y = x.y := by
  unfold pagePenalty
  split
  · exact RoomBlocks.tick_y 1 x
  · rfl

/-- the addressing of an `LDA (zp),Y` keeps Y -/
theorem mIzyR_y {m : Machine} (hp : m.pc + 1 ≥ 0x8000) : (go mIzyR { m with pc := m.pc + 1 }).2.y = m.y := by
  have e : go mIzyR { m with pc := m.pc + 1 } =
      go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun s => pagePenalty b (b + s.y.toUInt16) >>= fun _ => pure (b + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, TaintRun.fetch_rom (m := { m with pc := m.pc + 1 }) hp, PipeTransitionAll.go_bind]
  obtain ⟨_, _, a3⟩ := RoomBlocks.rd16zp_eq (RoomBlocks.operand m) { m with pc := m.pc + 1 + 1 }
  show (go (pagePenalty _ _ >>= fun _ => pure _) (go (rd16zp (RoomBlocks.operand m)) { m with pc := m.pc + 1 + 1 }).2).2.y = m.y
  rw [PipeTransitionAll.go_bind]
  show (go (pagePenalty _ _) (go (rd16zp (RoomBlocks.operand m)) { m with pc := m.pc + 1 + 1 }).2).2.y = m.y
  rw [pagePenalty_y, a3]

theorem setA_y (v : UInt8) (x : Machine) : (go (setA v) x).2.y = x.y := rfl

/-- **An `LDA (zp),Y` of the RAM keeps Y** -/
theorem step_lda_izy_y {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) (hp1 : m.pc + 1 ≥ 0x8000)
    (hop : m.prg.get! (m.pc &&& m.prgMask).toNat = 0xB1) (hr : ScreenPage.readAddr m < 0x2000) : (go step m).2.y = m.y := by
  rw [ScreenPage.step_at hn hh hp hop (by decide), ScreenPage.op_B1, ScreenPage.cyc_B1]
  have e : go ((opLDA mIzyR) >>= fun _ => tick 5) { m with pc := m.pc + 1 } =
      go (tick 5) (go (setA (ScreenPage.readVal m)) (go (rd (ScreenPage.readAddr m)) (go mIzyR { m with pc := m.pc + 1 }).2).2).2 := by
    rw [PipeTransitionAll.go_bind]
    have e2 : go (opLDA mIzyR) { m with pc := m.pc + 1 } = go (mIzyR >>= fun ad => rd ad >>= fun v => setA v) { m with pc := m.pc + 1 } := rfl
    rw [e2, PipeTransitionAll.go_bind, PipeTransitionAll.go_bind]
    rfl
  rw [e, RoomBlocks.tick_y, setA_y, (RoomBlocks.rd_ram hr _).2.2, mIzyR_y hp1]

/-- the place of the read after it is its address before it -/
theorem readAt_after {Q : Spots} {m : Machine} (hp1 : m.pc + 1 ≥ 0x8000) (hz1 : ((RoomBlocks.operand m).toUInt16 &&& 0x7FF).toNat = Q.ptrI)
    (hz2 : ((RoomBlocks.operand m + 1).toUInt16 &&& 0x7FF).toNat = Q.ptrI + 1) {m' : Machine} (hram : m'.ram = m.ram) (hy : m'.y = m.y) :
    readAt Q m' = readI m := by
  unfold readAt readI
  rw [RoomBlocks.readAddr_eq hp1, hram, hy]
  unfold RoomBlocks.ptrZ
  rw [hz1, hz2]

/-- the facts of `readOK` -/
structure ReadFacts (T : Pole) (E : Env) : Prop where
  r0 : 0x8000 ≤ T.Q.read
  r1 : 0x8000 ≤ T.Q.read + 1
  op : E.prg.get! (T.Q.read &&& E.mask).toNat = 0xB1
  z1 : ((E.prg.get! ((T.Q.read + 1) &&& E.mask).toNat).toUInt16 &&& 0x7FF).toNat = T.Q.ptrI
  z2 : (((E.prg.get! ((T.Q.read + 1) &&& E.mask).toNat) + 1).toUInt16 &&& 0x7FF).toNat = T.Q.ptrI + 1
  idle : T.G.idle ≠ T.Q.read + 2

theorem readFacts_of {T : Pole} {E : Env} (h : readOK T E = true) : ReadFacts T E := by
  simp only [readOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **`TileRead` right after a read**: the read before it is the `LDA (zp),Y` of the side check, with no NMI pending (`pairOK`); the byte read is the byte of the RAM at
its address (`ReadPre`), which the map says is in the pole's column if it is one of the pole's tiles -/
theorem tileRead_after {T : Pole} {E : Env} {F : Nat × UInt8} {A₁ B : AS} {m : Machine} (hR : ReadFacts T E) (hs : Sim E F A₁ m) (hsB : Sim E F B (go step m).2)
    (hpair : pairOK T.Q A₁ B = true) (hm : ColMap T.Q m) (hrd : ReadPre T.Q m) : TileRead T.Q (go step m).2 := by
  intro hpc hsv htile
  have hBpc : B.pc = T.Q.read + 2 := by rw [← hsB.pc]; exact hpc
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
  have hsv' : m.ram.get! T.Q.saveI ∈ T.Q.idx := by rw [← hram]; exact hsv
  obtain ⟨hr0, hl, hh, hpg⟩ := hrd hmpc hsv'
  have hy := step_lda_izy_y hnmi hhal hp0 hp1 hop hr0
  have hz : RoomBlocks.operand m = E.prg.get! ((T.Q.read + 1) &&& E.mask).toNat := by
    unfold RoomBlocks.operand
    rw [hs.prg, hs.mask, hmpc]
  have hat : readAt T.Q (go step m).2 = readI m :=
    readAt_after hp1 (by rw [hz]; exact hR.z1) (by rw [hz]; exact hR.z2) hram hy
  have hval : (go step m).2.a = m.ram.get! (readI m) := by
    rw [ha, RoomBlocks.readVal_eq hr0]
    rfl
  have ht : Tile T.Q (m.ram.get! (readI m)) := by
    rw [← hval]
    exact htile
  have hcol := hm (readI m) hl hh ht
  refine ⟨by rw [hat]; exact hcol, ?_⟩
  rw [hram]
  exact hpg ht hcol

/-! ## The frame -/

/-- what the check says -/
structure FrameOKP (T : Pole) (E : Env) : Prop where
  rt : T.G.rtI < 2048
  zone : ZoneOK T
  ok0 : okRt T.G (startG T.G false) = true
  ok1 : okRt T.G (startG T.G true) = true
  table : (cfgOf T E).t.all (walkP (cfgOf T E) fuelG) = true
  s0 : walkP (cfgOf T E) fuelG (startG T.G false) = true
  s1 : walkP (cfgOf T E) fuelG (startG T.G true) = true
  read : ReadFacts T E

theorem frameOKP_of_check {T : Pole} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (h : frameCheckP T E = true) : FrameOKP T E := by
  have hC := frameOK_of_check hp (frameCheck_of_P h)
  obtain ⟨_, h2, h3, h4, h5⟩ := parts_of_P h
  exact ⟨hC.rt, hC.zone, hC.ok0, hC.ok1, h2, h3, h4, readFacts_of h5⟩

/-- **The frame.** From a `FrameStart` with the map `ColMap`, while each instruction is `CleanK`, meets `PosAt`, `HypR`, `BufAt` and `ReadPre`, the routine byte does not
become the pole's. `TileRead` is not assumed: it is proved at each step. -/
theorem no_write_frameP {T : Pole} {E : Env} (hp : T.Q.ptrI + 1 < 2048) (hc : frameCheckP T E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart T.G E (s 0)) (hm0 : ColMap T.Q (s 0))
    (hh : ∀ j, j ≤ n → CleanK T.G T.K.store (s j) ∧ PosAt T.Q T.ps (s j) ∧ HypR T (s j) ∧ BufAt T.Q (s j) ∧ ReadPre T.Q (s j)) :
    (s (n + 1)).ram.get! T.G.rtI ≠ T.G.ev := by
  have hC := frameOKP_of_check hp hc
  obtain ⟨b, hsim⟩ := PipeWrites.sim_startG hE h0
  have hkl : (cfgOf T E).kl = (cfgOf T E).t.map knownOf := rfl
  have hT2 : 2 ≤ (2 : UInt8).toNat := by decide
  have hstart : ∃ A, LiveP (cfgOf T E) ((s 0).frame, 2) A (s 0) := by
    cases b with
    | false => exact ⟨_, hsim, rfl, fuelG, hC.s0⟩
    | true => exact ⟨_, hsim, rfl, fuelG, hC.s1⟩
  have hT0 : TileRead T.Q (s 0) := by
    intro hpc
    rw [h0.pc] at hpc
    exact absurd hpc hC.read.idle
  have hyp : ∀ j, j ≤ n → TileRead T.Q (s j) → HypT T (s j) := fun j hj ht =>
    ⟨(hh j hj).2.2.1.1, (hh j hj).2.2.1.2.1, ht, (hh j hj).2.2.1.2.2⟩
  have live : ∀ j, j ≤ n → (∃ A, LiveP (cfgOf T E) ((s 0).frame, 2) A (s j)) ∧ ColMap T.Q (s j) ∧ TileRead T.Q (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨hstart, hm0, hT0⟩
    | succ j ih =>
      intro hj
      obtain ⟨⟨A, hA⟩, hmj, htj⟩ := ih (by omega)
      obtain ⟨hh1, hp1, _, hb1, hr1⟩ := hh j (by omega)
      obtain ⟨A₁, B, hs1, hok, hsB, hpair, _, h2⟩ := live_stepP hC.table hkl rfl hT2 hC.zone hC.rt hA hh1 hp1 (hyp j (by omega) htj)
      have hmj1 := colMap_step hs1 hok hb1 hmj
      have htj1 := tileRead_after hC.read hs1 hsB hpair hmj hr1
      rw [← hs j (by omega)] at h2 hmj1 htj1
      refine ⟨?_, hmj1, htj1⟩
      rcases h2 with h2 | h2
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := h2
        omega
      · exact h2
  obtain ⟨⟨A, hA⟩, _, htn⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hp1, _, _, _⟩ := hh n (Nat.le_refl n)
  obtain ⟨_, _, _, _, _, _, h1, _⟩ := live_stepP hC.table hkl rfl hT2 hC.zone hC.rt hA hh1 hp1 (hyp n (Nat.le_refl n) htn)
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-! ## The frames before the touch's frame: the map from control on

The walk of `FrameKeep` (one whole frame in control) is run again with the test `okSK` (the step writes no byte of the block buffers, or it is a store through an
index or a pointer) on every state on the way (`walkKS`). With `BufAt` on each instruction, a frame in control keeps `ColMap` (`frame_colMap`), and so do all the
frames from control to the touch's frame (`frames_colMap`). -/

open FrameKeep (CfgK coverK preK kstep cfgOfKW startK fuelK watchOK endOK Watched)

/-- `okS` with the places `Q` -/
def okSK (E : Env) (Q : Spots) (A : AS) : Bool :=
  StepWrites.keepOK E (inBufB Q) A || idxOps.contains (E.prg.get! (A.pc &&& E.mask).toNat)

/-- `FrameKeep.walkK` with the test `okSK` on every state on the way -/
def walkKS (C : CfgK) (Q : Spots) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => okSK C.E Q A₁ && (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverK C B) || walkKS C Q n B
      else B.k == A.k + 1 && watchOK C.W B && endOK C.G B && C.fin B

/-- **The check**: `FrameKeep.keepCheckW` with `walkKS` -/
def keepCheckS (S : FrameKeep.Spot) (G : Guard) (E : Env) (W : List FrameKeep.Watch) (key : AS → Nat) (fin : AS → Bool) (Q : Spots) : Bool :=
  let C := cfgOfKW S G E W key fin
  decide (G.late < dotsPerFrame) && W.all (fun w => decide (w.1 < 2048)) &&
    C.t.all (walkKS C Q fuelK) && walkKS C Q fuelK (startK G W false) && walkKS C Q fuelK (startK G W true)

/-- the check with the places of `FrameKeep.keepCheckOf` -/
def keepCheckOfS (sy : Syms) (m0 : Machine) : Bool :=
  keepCheckS (FrameKeep.spotOf sy m0) (FrameKeep.guardK sy m0) (PipeEntryRule.envOf m0) (FrameKeep.watchOf sy)
    (FrameKeep.keyKC sy (FrameKeep.spotOf sy m0) (FrameKeep.guardK sy m0) (FrameKeep.watchOf sy)) (FrameKeep.endCtl sy) (spotsF sy m0)

/-- **The map goes on over a step that `okSK` allows** -/
theorem colMap_stepQ {Q : Spots} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (hok : okSK E Q A = true) (hbuf : BufAt Q m)
    (hm : ColMap Q m) : ColMap Q (go step m).2 := by
  intro i h1 h2 ht
  simp only [okSK, Bool.or_eq_true] at hok
  rcases hok with hk | hk
  · have e := StepWrites.keep_step hs hk i (by simp [inBufB, h1, h2])
    rw [e] at ht
    exact hm i h1 h2 ht
  · have hop : opAt m = E.prg.get! (A.pc &&& E.mask).toNat := by
      unfold opAt
      rw [hs.prg, hs.mask, hs.pc]
    rw [← hop] at hk
    have hn := hbuf (target_of_idx hk)
    by_cases he : (go step m).2.ram.get! i = m.ram.get! i
    · rw [he] at ht
      exact hm i h1 h2 ht
    · exact hn i h1 h2 he ht

section
variable {C : CfgK} {Q : Spots} {Fu : Nat} {F : Nat × UInt8}

def LiveKS (C : CfgK) (Q : Spots) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkKS C Q n A = true

theorem cover_liveKS (ht : C.t.all (walkKS C Q Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverK C B = true) :
    ∃ D, LiveKS C Q F D m ∧ D.k = B.k := by
  unfold coverK at h
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
    exact ⟨D, ⟨TaintRun.sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepKS (ht : C.t.all (walkKS C Q Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    {A : AS} {m : Machine} (hl : LiveKS C Q F A m) (hh : CleanK C.G C.S.store m) :
    (∃ A₁, Sim C.E F A₁ m ∧ okSK C.E Q A₁ = true) ∧
    ((∃ A', LiveKS C Q F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame) ∨ (go step m).2.frame = m.frame + 1) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKS] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkKS, List.all_eq_true] at hw
    have hw1 := hw A₁ hA
    simp only [Bool.and_eq_true, List.all_eq_true] at hw1
    obtain ⟨hok, hw1⟩ := hw1
    have hw2 := hw1 r hr
    refine ⟨⟨A₁, hs1, hok⟩, ?_⟩
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, _⟩ | ⟨_, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKS ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2⟩
      · right
        exact k2

/-- **One frame keeps the map**: a walk with the test `okSK` from `S` that succeeds covers the frame, and each step on the way keeps `ColMap` -/
theorem colMap_of_walkKS (ht : C.t.all (walkKS C Q Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hp : C.E.pad = AB.top) {S : AS} {m : Machine} {i : UInt8} (hw : walkKS C Q Fu S = true) (hs : Sim C.E F S m)
    (hk : ∀ j, CleanK C.G C.S.store (trace m i j)) (hb : ∀ j, BufAt Q (trace m i j)) (hm : ColMap Q m) : ColMap Q (PipeTransition.frame m i) := by
  have hs0 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact TaintRun.mem_top _ }
  have key : ∀ j, ColMap Q (trace m i j) ∧ ((∃ A, LiveKS C Q F A (trace m i j) ∧ (trace m i j).frame = m.frame) ∨ (trace m i j).frame = m.frame + 1) := by
    intro j
    induction j with
    | zero => exact ⟨hm, Or.inl ⟨S, ⟨hs0, Fu, hw⟩, rfl⟩⟩
    | succ j ih =>
      have e : trace m i (j + 1) = PipeEntryRule.nxt (m.frame + 1) (trace m i j) := rfl
      obtain ⟨hmj, ih⟩ := ih
      rcases ih with ⟨A, h1, h3⟩ | h1
      · have hh := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by
          simp [h3, hh]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [PipeEntryRule.nxt, if_neg hc]
        rw [e2]
        obtain ⟨⟨A₁, hs1, hok⟩, h2⟩ := live_stepKS ht hkl hops hT h1 (hk j)
        refine ⟨colMap_stepQ hs1 hok (hb j) hmj, ?_⟩
        rcases h2 with ⟨A', a1, _, a3⟩ | a1
        · exact Or.inl ⟨A', a1, by rw [a3, h3]⟩
        · exact Or.inr (by rw [a1, h3])
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by
          simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [PipeEntryRule.nxt, if_pos hc]
        rw [e2]
        exact ⟨hmj, Or.inr h1⟩
  rw [PipeEntryRule.frame_trace]
  exact (key fuelPerFrame).1

end

/-- **A frame in control keeps the map**: it starts as `FrameStart` asks, with the watched bits, its instructions meet `CleanK` and `BufAt` -/
theorem frame_colMap {S : FrameKeep.Spot} {G : Guard} {E : Env} {W : List FrameKeep.Watch} {key : AS → Nat} {fin : AS → Bool} {Q : Spots}
    (hc : keepCheckS S G E W key fin Q = true) (hE : E.pad = AB.top) {m : Machine} {i : UInt8} (h0 : FrameStart G E m) (hw : Watched W m)
    (hk : ∀ j, CleanK G S.store (trace m i j)) (hb : ∀ j, BufAt Q (trace m i j)) (hm : ColMap Q m) : ColMap Q (PipeTransition.frame m i) := by
  simp only [keepCheckS, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, _⟩, h2⟩, h3⟩, h4⟩ := hc
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK hE h0 hw
  have hw0 : walkKS (cfgOfKW S G E W key fin) Q fuelK (startK G W b) = true := by
    cases b with
    | false => exact h3
    | true => exact h4
  exact colMap_of_walkKS (C := cfgOfKW S G E W key fin) (F := (m.frame, 2)) h2 rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hE hw0 hs hk hb hm

/-- **The map at the start of the touch's frame, from control**: `ColMap` at control, and every frame before the touch's frame keeps it (`frame_colMap`, the frames start
in control: `FrameKeep.Frames.all_start`) -/
theorem frames_colMap {sy : Syms} {m0 : Machine} {Sr : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hc : FrameKeep.keepCheckOf sy m0 = true)
    (hcS : keepCheckOfS sy m0 = true) (K : FrameKeep.Frames sy m0 Sr a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : Watched (FrameKeep.watchOf sy) (seq 0))
    (hm0 : ColMap (spotsF sy m0) (seq 0)) (hb : ∀ n, n + 1 < K.ix g → ∀ k, BufAt (spotsF sy m0) (trace (K.all n) (K.inp n) k)) :
    ∀ n, n < K.ix g → ColMap (spotsF sy m0) (K.all n) := by
  have e0 : seq 0 = K.all 0 := by rw [K.at_ix 0 (Nat.zero_le _), K.ix0]
  intro n
  induction n with
  | zero => exact fun _ => e0 ▸ hm0
  | succ i ih =>
    intro hi
    have hmi := ih (by omega)
    obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 i (by omega)
    rw [K.next i]
    exact frame_colMap hcS rfl a1 a2 (K.clean i (by omega)) (hb i hi) hmi

/-! ## The touch -/

/-- **The check on the ROM**: `PoleFrame.poleFrameCheck` with the walk of the two tests in place of the walk, and the walk of the frames with `okSK` -/
def poleCheckP (sy : Syms) (m0 : Machine) : Bool :=
  ptrOK sy m0 && frameCheckP (poleOf sy m0) (PipeEntryRule.envOf m0) && SubsOnce.subsCheck sy m0 && keepCheckOfS sy m0

theorem poleFrameCheck_of_P {sy : Syms} {m0 : Machine} (h : poleCheckP sy m0 = true) : poleFrameCheck sy m0 = true := by
  simp only [poleCheckP, poleFrameCheck, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1.1, frameCheck_of_P h.1.1.2⟩, h.1.2⟩

theorem keepS_of_P {sy : Syms} {m0 : Machine} (h : poleCheckP sy m0 = true) : keepCheckOfS sy m0 = true := by
  simp only [poleCheckP, Bool.and_eq_true] at h
  exact h.2

/-- **The touch on a real frame, at the end of the move**, without `TileRead`: as `PoleFrame.touch_right_of_left`, with the map at the frame's start (`ColMap`), and
up to the write `BufAt` and `ReadPre` on each instruction -/
theorem touch_right_of_leftP {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : poleCheckP sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hrd : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → ReadPre (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k)) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) := by
  simp only [poleCheckP, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hp, hc⟩, _⟩, _⟩ := hc
  have hp' : (spotsF sy m0).ptrI + 1 < 2048 := by simpa [ptrOK] using hp
  obtain ⟨n, hw⟩ := he
  by_cases hx : ∃ j, j ≤ n ∧ (trace m i j).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frameP (T := poleOf sy m0) (s := trace m i) (n := n) hp' hc rfl (fun j hj => PoleEntryRule.step_before hw j hj)
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
        simp⟩, hbuf n hw j hj, hrd n hw j hj⟩)
    exact hn hw.2

/-- **In the pole's range, from one whole frame**, without `TileRead`: as `PoleFrame.inRange_of_frame` -/
theorem inRange_of_frameP {sy : Syms} {m0 m : Machine} {i : UInt8} {P : Int} (hc : poleCheckP sy m0 = true) (he : Touches sy m i)
    (h0 : FrameKeep.StartK sy m0 m) (hk : ∀ j, CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hpk : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → PosKeep sy m0 (trace m i j))
    (hm : ColMap (spotsF sy m0) m)
    (hbuf : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → BufAt (spotsF sy m0) (trace m i j))
    (hrd : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → ReadPre (spotsF sy m0) (trace m i j))
    (hag : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → (trace m i j).pc ∈ again sy m0 → (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i j) →
        ∃ k, k ≤ n ∧ (trace m i k).pc = sy.PlayerSubs ∧ (spotsF sy m0).left ≤ px (spotsF sy m0) (trace m i k))
    (hmoved : ∀ n j, WriteStep sy m i n → j ≤ n → (trace m i j).pc = sy.PlayerSubs → P = posP sy (trace m i j)) :
    SurfaceRun.poleP sy m0 ≤ P := by
  obtain ⟨n, j, h1, h2, h3, h4⟩ := touch_right_of_leftP hc he h0 hk hpk hm hbuf hrd hag
  rw [hmoved n j h1 h2 h3]
  have h5 : (spotsF sy m0).left = 256 * SurfaceRun.polePage sy m0 + (PoleGrab.colX sy - 10) := rfl
  have h7 : (spotsF sy m0).xI = (sy.Player_X_Position &&& 0x7FF).toNat := rfl
  have h8 : (spotsF sy m0).pI = (sy.Player_PageLoc &&& 0x7FF).toNat := rfl
  unfold px at h4
  rw [h5, h7, h8] at h4
  unfold SurfaceRun.poleP posP peek
  omega

end Smbrta.PoleTileWalk
