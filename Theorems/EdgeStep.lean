import Theorems.ScrollRule
import Theorems.GuardE
import Theorems.PositionKeep
import Theorems.StepPrg

/-!
# Above ground: the edge's step of one frame, from the scroll's rule and three walks

The old field `edge` of `SurfaceFrames.OnFrames` said, for each counted frame from `M` (the end of the frame before) to `b` (its end):

  edge(b) ≤ max(base(M), P(b)),   edge = `SurfaceRead.edgeOf` = 256·left16 + 255,   base = `SurfaceRead.baseOf` = max(P, edge).

Here it follows from five things of the frame (`edge_step_of`, `edge_frame`):

* the edge at the scroll handler's call `Q` (`PlayerSubs`) is that of `M`: the frames not counted keep the edge's two bytes (`keep_noCut`), and so does the
  counted frame up to `Q` (`keep_q`): the walk of `CtrlKeep` up to the player's routine and a first walk from there to `Q` follow each byte (`TaintRun`'s counter);
* the scroll's rule (`ScrollRule.scroll_edge`, round 25): at the instruction after the call `R`, the edge is that of `Q`, or the scroll is allowed at `Q` and the
  edge is at most `256·Y` further, `Y ≤ X(Q)` (the scroll's amount);
* the edge at the frame's end is that of `R` (`keep_r`): the first walk of `AfterKeep` from the player's routine to the scroll handler, a middle walk from there to
  `R`, and from `R` a second walk that follows each byte to the frame's end; it stops a path at a store to his position by its address outside the push and the clamp
  (`cutPos`), which the field `posW` excludes;
* `P(Q) − 256 ≤ P(b)`: this is a part of `SurfaceRead.CollideE` (`collideE_lower`);
* `Near(Q)`, a condition on the one state `Q`: when the scroll is allowed at `Q`, left16(Q) + X(Q) + 2 ≤ pixel16(Q).

The walks' guards protect the followed byte (`AfterKeep.guardH`); `FrameKeep.guardE` protects both bytes (`FrameKeep.edgeE`), so `CleanK` of `guardE` gives
`CleanK` of the walks' guards. The checks on the ROM are `qCheck` and `rCheck`. No game data. Page: `1-1/e-2-10-3-13-EdgeStep.md`.

Round 27: the same walks follow a third byte, the platforms' force on the scroll (`platI`), which the scroll's amount `X` adds to the byte the move stores. The
scroll handler stores 0 to it at its end, and `rCheck` also asks that the middle walk knows it as 0 at the instruction after the call (`atR`); so `keep_r` gives it 0
there and at the frame's end. The only other store to it in the ROM comes after a store to his position by its address in the platforms' routine, where the second
walk stops (`cutPos`, excluded by the field `posW`). So at each scroll handler it is 0 (`SurfaceFrames.OnFrames.platQ`), and the field `near` asks `NearX`, with the
byte the move stores in place of `X` (`near_of_x`). Page: `1-1/e-2-10-3-14-PlatformForce.md`. Round 28: `NearX` at the scroll handler is a theorem
(`SurfaceFrames.OnFrames.nearAt`) from the field `nearA` at the player's routine (`MoveScroll`). Round 29: `nearA` is a theorem too (`SideTimer`), from `NearM`
at the frame's start and the field `nearStep` (round 30: a theorem, `SurfaceFrames.OnFrames.nearStepAt`, with the clamp's choice of `ClampSide` and the
fields `rightRel`, `endKeep`).
-/

namespace Smbrta.EdgeStep
open FrameModel ImpedePosition ScrollRule

variable {sy : Syms}

/-- his pixel with its page, `256·page + pixel` (the position `posP` without its fraction) -/
def pixel16 (sy : Syms) (m : Machine) : Nat := (peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat

/-- **Near(Q)**: when the scroll is allowed at `Q` (`ScrollRule.Allows`), the screen's left edge (`ScrollRule.left16`) plus the scroll's amount (`amountOf`) plus
2 px is at most his pixel. A condition on one state. -/
def Near (sy : Syms) (P : Places) (Q : Machine) : Prop :=
  Allows P Q → left16 P Q + (amountOf P Q).toNat + 2 ≤ pixel16 sy Q

/-- **NearX(Q)** (round 27): `Near` with the scroll's amount `X` replaced by the byte the move stores (`Places.xs`), as `X` is on the frames above ground: there the
platforms' force on the scroll (`Places.plat`) is 0 at the scroll handler (`SurfaceFrames.OnFrames.platQ`). A condition on one state. -/
def NearX (sy : Syms) (P : Places) (Q : Machine) : Prop :=
  Allows P Q → left16 P Q + (Q.ram.get! P.xs).toNat + 2 ≤ pixel16 sy Q

/-- **`NearX` gives `Near`** when the platforms' force on the scroll is 0: then `X` is the byte the move stores -/
theorem near_of_x {P : Places} {Q : Machine} (h : NearX sy P Q) (hp : Q.ram.get! P.plat = 0) : Near sy P Q := by
  intro ha
  have e : amountOf P Q = Q.ram.get! P.xs := by
    unfold amountOf
    rw [hp]
    exact UInt8.add_zero _
  rw [e]
  exact h ha

theorem posP_ge (m : Machine) : 256 * (pixel16 sy m : Int) ≤ posP sy m := by
  show 256 * (((peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat : Nat) : Int) ≤
    (((peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat) * 256 + (peek m sy.SprObject_X_MoveForce).toNat : Int)
  omega

/-- a frame's end `b` after `Q` with `CollideR` is at most 1 px behind `Q` -/
theorem collide_lower {B₀ : Int} {Q b : Machine} (h : SurfaceRead.CollideR sy B₀ Q b) : posP sy Q - 256 ≤ posP sy b := by
  rcases h.P with e | e | ⟨e1, _, _⟩ <;> omega

/-- the same from `SurfaceRead.CollideE` -/
theorem collideE_lower {B₀ : Int} {Q b : Machine} (h : SurfaceRead.CollideE sy B₀ Q b) : posP sy Q - 256 ≤ posP sy b := by
  rcases h.P with e | e | ⟨e1, _, _⟩ <;> omega

/-- **The edge's step, from the scroll's alternative**: if the edge at `Q` is that of `M` (`hQ`), the edge at `b` is that of `R` (`hR`), `R`'s edge is `Q`'s or,
when `A` holds, at most `256·Y` further with `Y ≤ X` (`hs`), `A` puts the edge plus `256·(X + 1)` at most at `P(Q)` (`hn`), and `P(Q) − 256 ≤ P(b)` (`hc`), then
edge(b) ≤ max(base(M), P(b)). -/
theorem edge_step_of {M Q R b : Machine} {A : Prop} {X : Nat}
    (hQ : SurfaceRead.edgeOf sy Q = SurfaceRead.edgeOf sy M)
    (hR : SurfaceRead.edgeOf sy b = SurfaceRead.edgeOf sy R)
    (hs : SurfaceRead.edgeOf sy R = SurfaceRead.edgeOf sy Q ∨
      (A ∧ ∃ Y : UInt8, Y.toNat ≤ X ∧ SurfaceRead.edgeOf sy R ≤ SurfaceRead.edgeOf sy Q + 256 * (Y.toNat : Int)))
    (hn : A → SurfaceRead.edgeOf sy Q + 256 * ((X : Int) + 1) ≤ posP sy Q)
    (hc : posP sy Q - 256 ≤ posP sy b) :
    SurfaceRead.edgeOf sy b ≤ max (SurfaceRead.baseOf sy M) (posP sy b) := by
  have hb : SurfaceRead.baseOf sy M = max (posP sy M) (SurfaceRead.edgeOf sy M) := rfl
  rcases hs with h | ⟨ha, Y, hy, h⟩
  · have e1 : SurfaceRead.edgeOf sy M ≤ SurfaceRead.baseOf sy M := by rw [hb]; exact Int.le_max_right _ _
    rw [hR, h, hQ]
    exact Int.le_trans e1 (Int.le_max_left _ _)
  · have e2 := hn ha
    have e3 : SurfaceRead.edgeOf sy b ≤ posP sy b := by
      have : (Y.toNat : Int) ≤ (X : Int) := by exact_mod_cast hy
      omega
    exact Int.le_trans e3 (Int.le_max_right _ _)

/-- **One frame's edge step, with the scroll's rule from the ROM** (`ScrollRule.check`): take a real machine `Q` at the scroll handler's call (`PlayerSubs`, with
`Good`). Then there is `k` with `R = stepN k Q` at the instruction after the call (in the frame, the stack kept), and for any end `b` of the frame and any `M`:
if edge(Q) = edge(M), `Near(Q)`, P(Q) − 256 ≤ P(b) and edge(b) = edge(R), then edge(b) ≤ max(base(M), P(b)). -/
theorem edge_frame {m0 : Machine} (hk : ScrollRule.check sy m0 = true) {Q : Machine} (hg : Good (Rom.of m0) Q) (hpc : Q.pc = sy.PlayerSubs) :
    ∃ k, Good (Rom.of m0) (stepN k Q) ∧ (stepN k Q).pc = sy.PlayerSubs + 3 ∧ (stepN k Q).s = Q.s ∧ InFrameN (Rom.of m0) Q k ∧
      ∀ M b : Machine, SurfaceRead.edgeOf sy Q = SurfaceRead.edgeOf sy M → Near sy (places sy m0) Q → posP sy Q - 256 ≤ posP sy b →
        SurfaceRead.edgeOf sy b = SurfaceRead.edgeOf sy (stepN k Q) → SurfaceRead.edgeOf sy b ≤ max (SurfaceRead.baseOf sy M) (posP sy b) := by
  obtain ⟨k, g, pc, sp, hs, f⟩ := scroll_edge hk hg hpc
  refine ⟨k, g, pc, sp, f, fun M b hQ hn hc hR => ?_⟩
  refine edge_step_of (A := Allows (places sy m0) Q) (X := (amountOf (places sy m0) Q).toNat) hQ hR hs ?_ hc
  intro ha
  have h1 := hn ha
  have h2 := posP_ge (sy := sy) Q
  have h3 := edgeOf_left16 (sy := sy) hg.prg hg.mask
  rw [h3]
  have h4 : ((left16 (places sy m0) Q + (amountOf (places sy m0) Q).toNat + 2 : Nat) : Int) ≤ (pixel16 sy Q : Int) := by exact_mod_cast h1
  push_cast at h4
  omega

/-! ## A first walk with a followed byte

`AfterKeep.walkQ1` walks from the player's routine to the scroll handler with no byte followed; its proof asks the counter to be at least 2 (`FrameKeep.s_kstep`).
`walkQR` is the same walk that also refuses a decrement of the followed byte (`isRkDec`), as the second walk `AfterKeep.walkKR` does; so its proof takes the steps of
`AfterKeep.s_kstepL`, with no condition on the byte's value. -/

open TaintRun

/-- **The first walk with a followed byte**: `AfterKeep.walkQ1`, and no step decrements the followed byte -/
def walkQR (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => B.k == A.k && (if B.pc == Q then atQ B else (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkQR C l Q atQ n B)

/-- what the first walk with the byte followed asks at the scroll handler: the byte still followed and not decremented, no NMI pending, the NMI off -/
def atRk (B : AS) : Bool := B.rk && !B.spent && !B.nmi && B.ppuCtrl.bit 0x80 == some false

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {E : Env} {F : Nat × UInt8} {C : FrameKeep.CfgK} {l : List Nat} {Q : UInt16} {Fu : Nat} {atQ' : AS → Bool}

/-- `A` covers `m`, and a first walk with the byte followed succeeds from `A` -/
def LiveQR (C : FrameKeep.CfgK) (l : List Nat) (Q : UInt16) (atQ' : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkQR C l Q atQ' n A = true

theorem cover_liveQR (ht : C.t.all (walkQR C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveQR C l Q atQ' F D m := by
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

theorem live_stepQR (ht : C.t.all (walkQR C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveQR C l Q atQ' F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveQR C l Q atQ' F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc = Q ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkQR] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    simp only [walkQR, hx', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      simp only [Bool.and_eq_true, beq_iff_eq] at hw3
      obtain ⟨hkB, hw4⟩ := hw3
      rcases h2 with ⟨_, k2, k3⟩ | ⟨k1, _⟩
      · by_cases hq : B.pc = Q
        · rw [if_pos (by simp [hq])] at hw4
          exact Or.inr ⟨k2, k3, by rw [h1.pc]; exact hq, B, hw4, h1⟩
        · rw [if_neg (by simp [hq])] at hw4
          have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw4
          rcases hw4 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD⟩ := cover_liveQR ht hkl h1 h3
            exact Or.inl ⟨D, hD, k2, k3, hq'⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hq'⟩
      · exfalso
        rw [hk1] at k1
        omega

/-- **The first walk with the byte followed: from the cut to `Q`.** The machine `k` instructions into the frame of `m`, covered by a state from which the walk
succeeds, comes to `Q` in the same frame at a first instruction `k₁ > k`, in a state where `atQ'` holds. -/
theorem qR_run (ht : C.t.all (walkQR C l Q atQ' Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkQR C l Q atQ' Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ k₁, k < k₁ ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧ (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧
      ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁) := by
  have key : ∀ d, (∃ A, LiveQR C l Q atQ' F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        ∀ j, k < j → j ≤ k + d → (trace m i j).pc ≠ Q) ∨
      (∃ k₁, k < k₁ ∧ k₁ ≤ k + d ∧ (trace m i k₁).pc = Q ∧ (trace m i k₁).frame = m.frame ∧ m.fdot + 3 * k₁ ≤ (trace m i k₁).fdot ∧
        (∀ j, k < j → j < k₁ → (trace m i j).pc ≠ Q) ∧ ∃ B, atQ' B = true ∧ Sim C.E F B (trace m i k₁)) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun j h1 h2 => absurd h2 (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | h
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepQR ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b2⟩
        · rw [← e] at a1 a2 a3 a4
          refine Or.inl ⟨A', a1, a2.trans h2, by omega, fun j hj1 hj2 => ?_⟩
          by_cases h5 : j ≤ k + d
          · exact h4 j hj1 h5
          · rw [show j = k + (d + 1) by omega]
            exact a4
        · rw [← e] at a1 a2 a3 b2
          exact Or.inr ⟨k + (d + 1), by omega, Nat.le_refl _, a3, a1.trans h2, by omega, fun j hj1 hj2 => h4 j hj1 (by omega), B, b1, b2⟩
      · obtain ⟨k₁, h1, h2, h3⟩ := h
        exact Or.inr ⟨k₁, h1, by omega, h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3, _⟩ | ⟨k₁, h1, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact ⟨k₁, h1, h3⟩

/-! ## A second walk that also cuts at a store of the position

`AfterKeep.walkKR` with one more place where a path stops: an instruction where `cutP` holds. Here `cutP` is a store to a byte of his position by its address
outside the push and the clamp (`cutPos`); the field `posW` of the frames above ground (`PositionKeep.PosW`) says that no instruction from the scroll handler to the
frame's end is such a store. The only path that this cuts in the ROM is the loop back of a castle (it moves his page and the screen's page back): the walk does not
know the world, and without the cut it fails at the store to the screen's page. -/

/-- **The second walk with a cut**: `AfterKeep.walkKR`, and a path stops at an instruction where `cutP` holds -/
def walkKP (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || cutP A.pc || (FrameKeep.preK C.S C.G A).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && ((C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKP C l cutP Q n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

variable {cutP : UInt16 → Bool}

/-- `A` covers `m`, and the second walk with the cut succeeds from `A` -/
def LiveKP (C : FrameKeep.CfgK) (l : List Nat) (cutP : UInt16 → Bool) (Q : UInt16) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkKP C l cutP Q n A = true

theorem cover_liveKP (ht : C.t.all (walkKP C l cutP Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveKP C l cutP Q F D m ∧ D.k = B.k := by
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
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepKP (ht : C.t.all (walkKP C l cutP Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) {A : AS} {m : Machine}
    (hl : LiveKP C l cutP Q F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) (hp : cutP m.pc = false) :
    (∃ A', LiveKP C l cutP Q F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKP] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    have hp' : cutP A.pc = false := by rw [← hs.pc]; exact hp
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    simp only [walkKP, hx', hp', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
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
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw3
        obtain ⟨hq, hw4⟩ := hw3
        have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
        rcases hw4 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKP ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3, hq'⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3, hq'⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.1.1.2, hw3.1.2, hw3.2, k1, h1⟩

/-- **The second walk with the cut: from `k` to the frame's end.** As `AfterKeep.endKR`, when no instruction of the frame from `k` on is at a place of `cutP`. -/
theorem endKP (ht : C.t.all (walkKP C l cutP Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray) (hQ : Q ≠ C.G.idle)
    {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKP C l cutP Q Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame)
    (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → cutP (trace m i j).pc = false) :
    (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∧ ∀ d, 1 ≤ d → (trace m i (k + d)).pc ≠ Q := by
  have key : ∀ d, ((∃ A, LiveKP C l cutP Q F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ FrameKeep.endOK C.G B = true ∧ Sim C.E F B (trace m i (k + d)))) ∧
      (1 ≤ d → (trace m i (k + d)).pc ≠ Q) := by
    intro d
    induction d with
    | zero => exact ⟨Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩, fun h => absurd h (by omega)⟩
    | succ d ih =>
      obtain ⟨ih, _⟩ := ih
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h2', h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases live_stepKP ht hkl hops h1 (hcl (k + d)) (hx (k + d)) (hp (k + d) (by omega) h2) with ⟨A', a1, _, a3, a4, a5⟩ | ⟨a1, B, _, a2, a2', _, a3⟩
        · exact ⟨Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩, fun _ => a5⟩
        · refine ⟨Or.inr ⟨by rw [a1, h2], B, a2', a2, a3⟩, fun _ => ?_⟩
          rw [a3.pc]
          simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at a2
          rw [a2.1.1.1.1]
          exact fun h => hQ h.symm
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        refine ⟨Or.inr ⟨h1, B, h2, h2', h3⟩, fun _ => ?_⟩
        rw [h3.pc]
        simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at h2'
        rw [h2'.1.1.1.1]
        exact fun h => hQ h.symm
  refine ⟨?_, fun d hd1 => (key d).2 hd1⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases (key (fuelPerFrame - k)).1 with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h3⟩

end

/-! ## On the ROM: the checks -/

/-- **The cut of the second walk**: a store to a byte of his position by its address outside the push and the clamp (`PositionKeep.PosW` excludes it) -/
def cutPos (sy : Syms) (m0 : Machine) (pc : UInt16) : Bool :=
  FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask pc && !PositionWriters.innerP sy m0 pc

open AfterKeep (walkQ1 tableBut rkOn guardH)

/-- **The platforms' force on the scroll** (round 27), as an index of RAM: the byte that the scroll handler adds to the byte the move stores (`Platform_X_Scroll`) -/
def platI (sy : Syms) : Nat := (sy.Platform_X_Scroll &&& 0x7FF).toNat

/-- **The edge's two bytes**, as indices of RAM: the screen's left edge, its pixel and its page (`ScreenClamp.places`: the operands of the clamp's two loads); round 27:
and the platforms' force on the scroll (`platI`) -/
def eI (sy : Syms) (m0 : Machine) : List Nat :=
  [((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat, ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat, platI sy]

theorem platI_mem {m0 : Machine} : platI sy ∈ eI sy m0 := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **The first walk with the byte `b` followed**, from the states at the cut `cuts` to the scroll handler: its table (the search is no part of the proof) -/
def qbCfg (sy : Syms) (m0 : Machine) (v : UInt8) (b : Nat) (cuts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] W (FrameKeep.ctlI sy) (fun A => A.pc == sy.PlayerSubs)
    (cuts.map fun B => rkOn (CtrlKeep.toA W (CtrlKeep.valA sy v) B))
  let q := tableBut key sy.PlayerSubs P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the walk of `CtrlKeep` with the byte `b` followed, and at the cut the first walk with `b` followed to the scroll handler -/
def cfgQb (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (b : Nat) (C1 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgOf sy m0 q b true with
    after := fun B => walkQR C1 (FrameKeep.ctlI sy) sy.PlayerSubs atRk FrameKeep.fuelK (rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) }

/-- **The check of the edge up to the scroll handler**: for each byte of `eI`, the walk of `CtrlKeep` with the byte followed (a frame that does not come to the
player's routine keeps it), and from the cut the first walk with the byte followed to the scroll handler -/
def qCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
  (eI sy m0).all fun b =>
    let C1 := qbCfg sy m0 v b cuts
    CtrlKeep.ctrlCheck1 (cfgQb sy m0 v q b C1) && C1.t.all (walkQR C1 (FrameKeep.ctlI sy) sy.PlayerSubs atRk FrameKeep.fuelK)

/-- the instruction after the scroll handler's call: `JSR` takes 3 bytes -/
abbrev rPc (sy : Syms) : UInt16 := sy.PlayerSubs + 3

/-- the search from the scroll handler to the instruction after its call, from the states at the scroll handler `starts` (no part of the proof) -/
def qsSearch (sy : Syms) (m0 : Machine) (v : UInt8) (starts : List AS) : PrevKeep.PS :=
  PrevKeep.searchFrom sy m0 (PipeEntryRule.envOf m0) (CtrlKeep.spareI sy m0) [] (CtrlKeep.watchA sy m0 v) (FrameKeep.ctlI sy) (fun A => A.pc == rPc sy) starts

/-- **The middle walk's table**, from the scroll handler to the instruction after its call -/
def qsCfg (sy : Syms) (m0 : Machine) (v : UInt8) (P : PrevKeep.PS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := FrameKeep.guardF sy m0
  let E := PipeEntryRule.envOf m0
  let W := CtrlKeep.watchA sy m0 v
  let key := PrevKeep.keyP S G W
  let q := tableBut key (rPc sy) P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- **The second walk's table** for the byte `b`, from the states after the scroll handler's call `starts` -/
def q2CfgR (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardH sy m0 b
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let P := PrevKeep.searchFrom sy m0 E (b :: CtrlKeep.spareI sy m0) [] [] (FrameKeep.ctlI sy) (fun A => A.pc == rPc sy) (starts.map rkOn)
  let q := FrameKeep.tableOfKW key P.X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun B => B.rk && !B.spent }

/-- what the middle walk asks after the scroll handler's call: it knows the platforms' force on the scroll as 0 (round 27), and the second walk succeeds for each
byte -/
def atR (sy : Syms) (m0 : Machine) (C2 : List FrameKeep.CfgK) (B : AS) : Bool :=
  knownIs B (platI sy, 0) && C2.all fun C => walkKP C (FrameKeep.ctlI sy) (cutPos sy m0) (rPc sy) FrameKeep.fuelK (rkOn B)

/-- what the first walk asks at the scroll handler: the middle walk succeeds -/
def atS (sy : Syms) (m0 : Machine) (Cs : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) (B : AS) : Bool :=
  walkQ1 Cs (FrameKeep.ctlI sy) (rPc sy) (atR sy m0 C2) FrameKeep.fuelK B

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler, the middle walk to the instruction after its call, the second walks -/
def cfgPR (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 Cs : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atS sy m0 Cs C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check of the edge after the scroll handler**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from
there the middle walk to the instruction after the call, where it knows the platforms' force on the scroll as 0; from there, for each byte of `eI`, the second walk to
the frame's end -/
def rCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let Ps := qsSearch sy m0 v P.stops.toList
  let Cs := qsCfg sy m0 v Ps
  let C2 := (eI sy m0).map fun b => q2CfgR sy m0 b Ps.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop && rPc sy != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPR sy m0 v q C1 Cs C2) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atS sy m0 Cs C2) FrameKeep.fuelK) &&
    Cs.t.all (walkQ1 Cs (FrameKeep.ctlI sy) (rPc sy) (atR sy m0 C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (walkKP C (FrameKeep.ctlI sy) (cutPos sy m0) (rPc sy) FrameKeep.fuelK)

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- the edge's two bytes are those that `FrameKeep.guardE` protects as `FrameKeep.edgeE` -/
theorem eI_eq : eI sy m0 = FrameKeep.edgeE sy m0 := rfl

/-- **`FrameKeep.guardE` protects the edge's two bytes** -/
theorem eI_mem {x : Nat} (hx : x ∈ eI sy m0) : x ∈ (FrameKeep.guardE sy m0).prot :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (eI_eq (sy := sy) (m0 := m0) ▸ hx)))))))

/-- **`CleanK` of `guardE` gives `CleanK` of the guard of the walks for a byte of `eI`** -/
theorem cleanH_of_E {q : UInt16} {m : Machine} {x : Nat} (hx : x ∈ eI sy m0) (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) :
    FrameKeep.CleanK (guardH sy m0 x) q m := by
  refine FrameKeep.cleanK_sub h (fun y hy => ?_) rfl rfl rfl rfl
  simp only [guardH, List.mem_append, List.mem_singleton] at hy
  rcases hy with rfl | hy
  · exact eI_mem hx
  · exact List.mem_append_right _ hy

/-- the edge as a position (`SurfaceRead.edgeOf`) is read from the two bytes of `eI` -/
theorem edgeOf_eq {m m' : Machine} (hp : m.prg = m0.prg) (hk : m.prgMask = m0.prgMask) (hp' : m'.prg = m0.prg) (hk' : m'.prgMask = m0.prgMask)
    (h : ∀ x ∈ eI sy m0, m.ram.get! x = m'.ram.get! x) : SurfaceRead.edgeOf sy m = SurfaceRead.edgeOf sy m' := by
  unfold SurfaceRead.edgeOf
  rw [SurfaceRead.places_congr hp hk, SurfaceRead.places_congr hp' hk']
  have e1 := h _ (List.mem_cons_self (a := (((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat)))
  have e2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  show (((m.ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat).toNat * 256 + (m.ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat).toNat) * 256 + 255 : Int) =
    ((m'.ram.get! ((ScreenClamp.places sy m0).edgeP &&& 0x7FF).toNat).toNat * 256 + (m'.ram.get! ((ScreenClamp.places sy m0).edgeX &&& 0x7FF).toNat).toNat) * 256 + 255
  rw [e1, e2]

/-- **A frame in control that does not come to the player's routine keeps the edge's two bytes.** The frame starts in the idle loop in control and each instruction
meets `CleanK` of `FrameKeep.guardK`. `hq` is the check on the ROM: on every path of the walk of `CtrlKeep` that does not come to the routine no instruction writes the
followed byte. -/
theorem keep_noCut {v : UInt8} (hq : qCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hn : ∀ k, (trace m i k).frame = m.frame → (trace m i k).pc ≠ sy.PlayerCtrlRoutine) : ∀ x ∈ eI sy m0, (frame m i).ram.get! x = m.ram.get! x := by
  simp only [qCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hq
  obtain ⟨_, hb⟩ := hq
  intro x hx
  obtain ⟨h1, _⟩ := hb x hx
  generalize CtrlKeep.cutTable sy m0 true = q at h1
  rcases CtrlKeep.cut_or_end (C := cfgQb sy m0 v q x _) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hcl with ⟨k, h2, h3, _, _⟩ | ⟨B, hB, hs⟩
  · exact absurd h2 (hn k h3)
  · simp only [CtrlKeep.endR, Bool.and_eq_true, Bool.not_eq_true'] at hB
    have e := hs.rkv hB.1.1
    rw [if_neg (by simp [hB.1.2])] at e
    exact e

/-- the area's bytes at the cut, as the walk after the cut watches them -/
theorem watched_at (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hv : CtrlKeep.AreaOK sy v m) {k₀ : Nat}
    (h1 : (trace m i k₀).pc = sy.PlayerCtrlRoutine) (h2 : (trace m i k₀).frame = m.frame) (h4 : ∀ j, j < k₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
  have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
  intro w hw
  simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
    rw [FrameKeep.and_ff, FrameKeep.and_ff]
    exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
  · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
    rw [FrameKeep.and_ff, FrameKeep.and_ff]
    exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
  · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
    rw [FrameKeep.and_ff, FrameKeep.and_ff]
    exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2

/-- **A frame in control keeps the edge's two bytes from its start to the scroll handler.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each
instruction meets `CleanK` of `FrameKeep.guardF` and of the walk's guard for each byte (`hH`), and writes neither the routine, nor the mode, nor the task by its
address; the area's type is `v`, the swimming flag 0, the change of size 0. It comes to the player's routine at `n₀`, the first time, and to the scroll handler at `k`,
the first time after `n₀`. Then at `k` the machine is `Good` and has the two bytes of the frame's start. `hc`, `hq` are the checks on the ROM. -/
theorem keep_q (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hq : qCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ eI sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    {k : Nat} (hk : n₀ ≤ k) (hpc : (trace m i k).pc = sy.PlayerSubs) (hb : ∀ j, n₀ < j → j < k → (trace m i j).pc ≠ sy.PlayerSubs) :
    ∀ x ∈ eI sy m0, Good (Rom.of m0) (trace m i k) ∧ (trace m i k).ram.get! x = m.ram.get! x := by
  simp only [qCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hq
  obtain ⟨⟨hne1, _⟩, hbq⟩ := hq
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  intro x hxI
  obtain ⟨h1, ht⟩ := hbq x hxI
  generalize CtrlKeep.cutTable sy m0 true = q at h1 ht
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at h1 ht
  rcases CtrlKeep.cut_or_end2 (C := cfgQb sy m0 v q x (qbCfg sy m0 v x cuts)) h1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k₀, a1, a2, _, a4, a5, B, hB1, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    simp only [CtrlKeep.atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB1
    have hcut := hs.rkv hB1.1.1.1.1.1.1
    rw [if_neg (by simp [hB1.1.1.1.1.1.2])] at hcut
    have hV := watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hsR := AfterKeep.sim_rkOn (b := x) hsA
    have hw : walkQR (qbCfg sy m0 v x cuts) (FrameKeep.ctlI sy) sy.PlayerSubs atRk FrameKeep.fuelK
        (rkOn (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B)) = true := hB2
    obtain ⟨k₁, hk1, hq1, _, _, hbt, B₁, hat, hs₁⟩ := qR_run (C := qbCfg sy m0 v x cuts) ht rfl rfl hw hsR a2 a5 (hH x hxI) hx'
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [a1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exact absurd hq1 (hb k₁ hk1 h)
    subst hkk
    simp only [atRk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hat
    obtain ⟨⟨⟨hrk, hsp⟩, hnmi⟩, hctl⟩ := hat
    refine ⟨⟨hs₁.prg, hs₁.mask, by rw [hs₁.nmi]; exact hnmi, hs₁.halted, hs₁.trk, hs₁.size, CtrlKeep.nmi_off_of (by rw [hctl]; rfl) hs₁.ppuCtrl⟩, ?_⟩
    have e := hs₁.rkv hrk
    rw [if_neg (by simp [hsp])] at e
    exact e.trans hcut
  · exact absurd harr (hno n₀ hf0)

/-- **A frame in control keeps the edge's two bytes from the instruction after the scroll handler's call to its end.** The conditions of `keep_q`. Then the frame
comes to the scroll handler at `kq`, the first time after `n₀`, in the frame; and if from `kq` on no instruction of the frame is a store to his position by its address
outside the push and the clamp (the field `posW`), then at any instruction `n > kq` of the frame at the instruction after the call (`rPc`) the bytes of `eI` are those
of the frame's end, and the platforms' force on the scroll is 0 there (round 27). `hc`, `hr` are the checks on the ROM. -/
theorem keep_r (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hr : rCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hH : ∀ x ∈ eI sy m0, ∀ j, FrameKeep.CleanK (guardH sy m0 x) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
      ((∀ j, kq ≤ j → (trace m i j).frame = m.frame → cutPos sy m0 (trace m i j).pc = false) →
        ∀ n, kq < n → (trace m i n).pc = rPc sy →
          (∀ x ∈ eI sy m0, (frame m i).ram.get! x = (trace m i n).ram.get! x) ∧ (trace m i n).ram.get! (platI sy) = 0) := by
  simp only [rCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hne3⟩, hp1⟩, hp2⟩, hp3⟩, hp4⟩ := hr
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3 hp4
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3 hp4
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3 hp4
  generalize qsSearch sy m0 v P.stops.toList = Ps at hp1 hp2 hp3 hp4
  rcases CtrlKeep.cut_or_end2 (C := cfgPR sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (qsCfg sy m0 v Ps) ((eI sy m0).map fun b => q2CfgR sy m0 b Ps.stops.toList))
      hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs
        (atS sy m0 (qsCfg sy m0 v Ps) ((eI sy m0).map fun b => q2CfgR sy m0 b Ps.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hcl hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, fun hp => ?_⟩
    have hw1 : walkQ1 (qsCfg sy m0 v Ps) (FrameKeep.ctlI sy) (rPc sy) (atR sy m0 ((eI sy m0).map fun b => q2CfgR sy m0 b Ps.stops.toList)) FrameKeep.fuelK Bq = true := hatq
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hb1, B₁, hat1, hs1⟩ :=
      AfterKeep.q1_run (C := qsCfg sy m0 v Ps) hp3 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw1 hsq hfq hdq hcl hx'
    intro n hn hrp
    simp only [atR, Bool.and_eq_true] at hat1
    obtain ⟨hpl, hat2⟩ := hat1
    have hend : ∀ x ∈ eI sy m0, (∃ B₂, (q2CfgR sy m0 x Ps.stops.toList).fin B₂ = true ∧
        Sim (q2CfgR sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) B₂ (frame m i)) ∧
        ∀ d, 1 ≤ d → (trace m i (k₁ + d)).pc ≠ rPc sy := by
      intro x hxI
      have hmem : q2CfgR sy m0 x Ps.stops.toList ∈ (eI sy m0).map fun b => q2CfgR sy m0 b Ps.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
      have hw2 := List.all_eq_true.1 hat2 _ hmem
      have ht2 := List.all_eq_true.1 hp4 _ hmem
      have hs2 : Sim (q2CfgR sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := AfterKeep.sim_rkOn hs1
      exact endKP (C := q2CfgR sy m0 x Ps.stops.toList) ht2 rfl rfl hne3 hw2 hs2 hf1 hd1 (hH x hxI) hx' (fun j hj hfj => hp j (by omega) hfj)
    have hnn : n = k₁ := by
      rcases Nat.lt_trichotomy n k₁ with h | h | h
      · exact absurd hrp (hb1 n hn h)
      · exact h
      · exfalso
        have := (hend (platI sy) platI_mem).2 (n - k₁) (by omega)
        rw [show k₁ + (n - k₁) = n by omega] at this
        exact this hrp
    subst hnn
    refine ⟨fun x hxI => ?_, TaintRun.sim_known hs1 hpl⟩
    obtain ⟨B₂, hfin, hs₂⟩ := (hend x hxI).1
    change (B₂.rk && !B₂.spent) = true at hfin
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfin
    have e := hs₂.rkv hfin.1
    rw [if_neg (by simp [hfin.2])] at e
    exact e
  · exact absurd harr (hno n₀ hf0)

end Frames

end Smbrta.EdgeStep
