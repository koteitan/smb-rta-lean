import Theorems.PositionWriters

/-!
# Above ground: a frame that moves right and keeps its speed keeps its position after the scroll handler

`PositionWriters.writers_end` follows a frame in control from the scroll handler `Q` (`PlayerSubs`) to its end (`FrameW`). Here two conditions on single
instructions of that part of the frame give the field `AfterP.keep` (`keep_end`, `keep_frame`):

* `PosW`: an instruction that stores a byte of the position by its address is inside the push (`ImpedePlayerMove`) or the clamp at the screen's edge
  (`PositionWriters.innerP`), and outside them an instruction that stores through an index or a pointer (not `PositionWriters.plainOp`) writes none of the
  three bytes of the position (`PositionDispatch.Ordinary`). The walk proves the rest: a plain instruction outside them writes no byte of the position;
* `ClampR`: at the clamp's entry, when he moves right there, the clamp's target is his position.

On such a frame (`0 < v(Q)`, and the frame ends with the speed of `Q`) every machine from `Q` on has the speed of `Q` (`FrameW.kept`). So a push does not move
him: a push that moves sets the speed to 0 (`ImpedePosition.routine_return`), and a push that does not move needs no margins of the position, since its effect is
0 modulo `2²⁴` and the position stays in its range. The clamp moves him to its target, which `ClampR` makes his position. Every other reached instruction is
`Ordinary`, since a reached cut is never inside the two calls (`reached_in`): a plain one by the walk (`PositionWriters.ordinary_plain`), the others by `PosW`.
So the frame is a chain of pieces that each keep the position.

The conditions `PositionWriters.ready_all` asked at the push (the margins) and at the clamp (`Y = 0`) are not needed here. No game data. Page:
`1-1/e-2-10-3-8-PositionKeep.md`.
-/

namespace Smbrta.PositionKeep

open PipeEntryRule (trace)

/-- **The condition on one instruction after the scroll handler**: an instruction that stores a byte of the position by its address is inside the push or the
clamp (`PositionWriters.innerP`); and an instruction outside them that is not plain (it stores through an index or a pointer, `PositionWriters.plainOp`) writes
none of the three bytes of the position -/
def PosW (sy : Syms) (m0 : Machine) (R : Machine) : Prop :=
  (FrameKeep.storesTo (PositionWriters.posI sy) R.prg R.prgMask R.pc = true → PositionWriters.innerP sy m0 R.pc = true) ∧
  (PositionWriters.plainOp (R.prg.get! (R.pc &&& R.prgMask).toNat) = false →
    PositionWriters.innerP sy m0 R.pc = true ∨ PositionDispatch.Ordinary sy R)

/-- **The condition at the clamp's entry**: when he moves right there, the clamp's target is his position -/
def ClampR (sy : Syms) (m0 : Machine) (R : Machine) : Prop :=
  R.pc = (ScreenClamp.places sy m0).entry → 0 < sbyte (peek R sy.Player_X_Speed) →
    ScreenClamp.target (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) R R.y = posP sy R

/-- the checks on the ROM that the theorem needs besides `CtrlKeep.ctrlCheck`: the walk of `PositionWriters` with the list `writersIn`, the push, the clamp, the
scroll handler not inside the two calls, and the idle loop a `JMP` to itself -/
def pCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  PositionWriters.wCheck sy m0 v (PositionWriters.writersIn sy m0 v) && ImpedePosition.check sy m0 && ScreenClamp.check sy m0 &&
    !PositionWriters.innerP sy m0 sy.PlayerSubs && FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop

theorem pCheck_parts {sy : Syms} {m0 : Machine} {v : UInt8} (h : pCheck sy m0 v = true) :
    PositionWriters.wCheck sy m0 v (PositionWriters.writersIn sy m0 v) = true ∧ ImpedePosition.check sy m0 = true ∧ ScreenClamp.check sy m0 = true ∧
      PositionWriters.innerP sy m0 sy.PlayerSubs = false ∧ FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true := by
  simp only [pCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- the first index from `k` on where a property holds -/
theorem least_of {P : Nat → Prop} [DecidablePred P] : ∀ d k, P (k + d) → ∃ b, k ≤ b ∧ b ≤ k + d ∧ P b ∧ ∀ n, k ≤ n → n < b → ¬ P n
  | 0, k, h => ⟨k, Nat.le_refl _, by omega, by simpa using h, fun n h1 h2 => absurd h2 (by omega)⟩
  | d + 1, k, h => by
    by_cases hk : P k
    · exact ⟨k, Nat.le_refl _, by omega, hk, fun n h1 h2 => absurd h2 (by omega)⟩
    · have h' : P (k + 1 + d) := by
        have e : k + 1 + d = k + (d + 1) := by omega
        rw [e]
        exact h
      obtain ⟨b, hb1, hb2, hb3, hb4⟩ := least_of (P := P) d (k + 1) h'
      refine ⟨b, by omega, by omega, hb3, fun n h1 h2 => ?_⟩
      by_cases e : n = k
      · rw [e]; exact hk
      · exact hb4 n (by omega) h2

section
variable {sy : Syms} {m0 : Machine}

theorem ret_pos_all : ∀ n : Fin 256, UInt8.ofNat n.val ≠ UInt8.ofNat n.val + 1 + 1 := by decide +kernel

/-- a call that returns with the stack two bytes up took at least one instruction -/
theorem pos_of_stack {R : Machine} {k : Nat} (h : (FrameModel.stepN k R).s = R.s + 1 + 1) : 0 < k := by
  by_cases e : k = 0
  · subst e
    have := ret_pos_all ⟨R.s.toNat, R.s.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at this
    exact absurd h this
  · omega

/-- **A reached cut is not inside the two calls**: as `PositionWriters.reached_outside`, from the scroll handler not inside them -/
theorem reached_in {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q b f : Nat} (hs : PositionWriters.innerP sy m0 sy.PlayerSubs = false)
    (F : PositionWriters.FrameW sy m0 w s0 T q f) (hq : (T q).pc = sy.PlayerSubs) (live : ∀ n, q ≤ n → n < b → (T n).frame = f) :
    ∀ n, PositionDispatch.Reached sy m0 T q n → n < b → PositionWriters.innerP sy m0 (T n).pc = false := by
  intro n hr
  induction hr with
  | start => intro _; rw [hq]; exact hs
  | @next a c e ha edge ih =>
    intro hc
    have hac := edge.forward
    have hqa := PositionWriters.Reached.le ha
    have ia := ih (by omega)
    cases edge with
    | ordinary ni nc _ _ =>
      cases hin : PositionWriters.innerP sy m0 (T (a + 1)).pc with
      | false => rfl
      | true =>
        rcases F.step a hqa (live (a + 1) (by omega) hc) hin with h | h | h
        · rw [ia] at h; cases h
        · exact absurd h ni
        · exact absurd h nc
    | impede _ en ret _ _ =>
      rw [ret]
      exact (F.atW a hqa (live a hqa (by omega))).ret (Or.inl en)
    | clamp _ en ret _ _ =>
      rw [ret]
      exact (F.atW a hqa (live a hqa (by omega))).ret (Or.inr en)

/-- **One piece that keeps the position**: on a frame whose machines from `q` on all have the speed `s0 ≠ 0`, at a reached cut `a` before the frame's end `b` there is
a next piece, to `c ≤ b`, and `P(c) = P(a)` -/
theorem piece_keep (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hs : PositionWriters.innerP sy m0 sy.PlayerSubs = false)
    (hoff : PositionWriters.offStack sy = true) {w : List UInt16} {M : Machine} {input : UInt8} {q b : Nat} {s0 : UInt8}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : PositionWriters.FrameW sy m0 w s0 (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hall : ∀ j, q ≤ j → (trace M input j).frame = M.frame → peek (trace M input j) sy.Player_X_Speed = s0) (hnz : s0 ≠ 0)
    (hpos : 0 < sbyte s0)
    (hw : ∀ n, q ≤ n → n < b → PosW sy m0 (trace M input n)) (hcl : ∀ n, q ≤ n → n < b → ClampR sy m0 (trace M input n))
    {a : Nat} (hqa : q ≤ a) (hab : a < b) (hr : PositionDispatch.Reached sy m0 (trace M input) q a) :
    ∃ c e, c ≤ b ∧ PositionDispatch.Edge sy m0 (trace M input) a c e ∧ posP sy (trace M input c) = posP sy (trace M input a) := by
  have la := live a hqa hab
  have A := F.atW a hqa la
  by_cases pi : (trace M input a).pc = sy.ImpedePlayerMove
  · have g := A.good (Or.inl pi)
    obtain ⟨k, _, _, ret, sp, vel, _, _, hm, ifr⟩ := ImpedePosition.routine_return hi g pi
    have kp := pos_of_stack sp
    have eq := FrameModel.trace_inFrame idle la ifr time k (Nat.le_refl _)
    have cb := PositionDispatch.before_end finish eq.2
    have hnp : ImpedePosition.pushes ((trace M input a).ram.get! (ImpedePosition.sites sy m0).side) (peek (trace M input a) sy.Player_X_Speed) = false := by
      cases hp : ImpedePosition.pushes ((trace M input a).ram.get! (ImpedePosition.sites sy m0).side) (peek (trace M input a) sy.Player_X_Speed) with
      | false => rfl
      | true =>
        exfalso
        rw [hp, if_pos rfl, ← eq.1] at vel
        exact hnz ((hall (a + k) (by omega) eq.2).symm.trans vel)
    have hd : ImpedePosition.delta ((trace M input a).ram.get! (ImpedePosition.sites sy m0).side) (peek (trace M input a) sy.Player_X_Speed) = 0 := by
      simp [ImpedePosition.delta, hnp]
    rw [hd, ← eq.1] at hm
    have r1 := ImpedePosition.pos_range sy (trace M input (a + k))
    have r2 := ImpedePosition.pos_range sy (trace M input a)
    have hP : posP sy (trace M input (a + k)) = posP sy (trace M input a) := by omega
    refine ⟨a + k, _, by omega, PositionDispatch.Edge.impede (by omega) pi ?_ ?_ ?_, hP⟩
    · rw [eq.1]; exact ret
    · rw [eq.1]; exact sp
    · rw [hd, hP]; omega
  · by_cases pc : (trace M input a).pc = (ScreenClamp.places sy m0).entry
    · have g := A.good (Or.inr pc)
      have hy := A.sel pc
      have hv : 0 < sbyte (peek (trace M input a) sy.Player_X_Speed) := by rw [hall a hqa la]; exact hpos
      have ht := hcl a hqa hab pc hv
      obtain ⟨k, _, _, ret, sp, _, hm, ifr⟩ := ScreenClamp.clamp_return hcC g pc hy
      have kp := pos_of_stack sp
      have eq := FrameModel.trace_inFrame idle la ifr time k (Nat.le_refl _)
      have cb := PositionDispatch.before_end finish eq.2
      rw [ht, ← eq.1] at hm
      have r1 := ImpedePosition.pos_range sy (trace M input (a + k))
      have r2 := ImpedePosition.pos_range sy (trace M input a)
      have hP : posP sy (trace M input (a + k)) = posP sy (trace M input a) := by omega
      refine ⟨a + k, _, by omega, PositionDispatch.Edge.clamp (by omega) pc ?_ ?_ ?_, hP⟩
      · rw [eq.1]; exact ret
      · rw [eq.1]; exact sp
      · rw [ht, hP]
    · have hin := reached_in hs F hq live a hr hab
      have ho : PositionDispatch.Ordinary sy (trace M input a) := by
        obtain ⟨hw1, hw2⟩ := hw a hqa hab
        cases hp : PositionWriters.plainOp ((trace M input a).prg.get! ((trace M input a).pc &&& (trace M input a).prgMask).toNat) with
        | true =>
          have hst : FrameKeep.storesTo (PositionWriters.posI sy) (trace M input a).prg (trace M input a).prgMask (trace M input a).pc = false := by
            cases e : FrameKeep.storesTo (PositionWriters.posI sy) (trace M input a).prg (trace M input a).prgMask (trace M input a).pc with
            | false => rfl
            | true => rw [hw1 e] at hin; cases hin
          exact PositionWriters.ordinary_plain hoff A.rom.1 A.rom.2.1 A.rom.2.2 hp hst
        | false =>
          rcases hw2 hp with h | h
          · rw [hin] at h; cases h
          · exact h
      have ready : PositionDispatch.Ready sy m0 (trace M input a) := by
        unfold PositionDispatch.Ready
        rw [if_neg pi, if_neg pc]
        exact ho
      obtain ⟨c, e, hcb, edge⟩ := PositionDispatch.next_piece hi hcC idle time finish la hab ready
      refine ⟨c, e, hcb, edge, ?_⟩
      have he := edge.effect
      cases edge with
      | ordinary => simpa using he
      | impede _ en _ _ _ => exact absurd en pi
      | clamp _ en _ _ _ => exact absurd en pc

/-- **A frame that moves right at the scroll handler `q` and ends (at `b`) with the speed of `q` keeps the position** (the field `AfterP.keep`), from `FrameW`
(`PositionWriters.writers_end`) and the two conditions on single instructions `PosW` and `ClampR` from `q` to the frame's end -/
theorem keep_end (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hs : PositionWriters.innerP sy m0 sy.PlayerSubs = false)
    (hoff : PositionWriters.offStack sy = true) {w : List UInt16} {M : Machine} {input : UInt8} {q b : Nat}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (qb : q ≤ b) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : PositionWriters.FrameW sy m0 w (peek (trace M input q) sy.Player_X_Speed) (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hw : ∀ n, q ≤ n → n < b → PosW sy m0 (trace M input n)) (hcl : ∀ n, q ≤ n → n < b → ClampR sy m0 (trace M input n))
    (hpos : 0 < sbyte (peek (trace M input q) sy.Player_X_Speed))
    (hsame : peek (trace M input b) sy.Player_X_Speed = peek (trace M input q) sy.Player_X_Speed) :
    posP sy (trace M input b) = posP sy (trace M input q) := by
  have hnz : peek (trace M input q) sy.Player_X_Speed ≠ 0 := by
    intro e
    rw [e] at hpos
    have : sbyte (0 : UInt8) = 0 := by decide
    omega
  have hall := F.kept b finish hsame hnz
  have build : ∀ d a, b - a = d → q ≤ a → a ≤ b → PositionDispatch.Reached sy m0 (trace M input) q a →
      posP sy (trace M input a) = posP sy (trace M input q) → posP sy (trace M input b) = posP sy (trace M input q) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a dist qa ab reached ha
      by_cases done : a = b
      · subst a; exact ha
      · have lt : a < b := by omega
        obtain ⟨c, e, hcb, edge, hc⟩ := piece_keep hi hcC idle hs hoff time finish live F hq hall hnz hpos hw hcl qa lt reached
        have ac := edge.forward
        exact ih (b - c) (by omega) c rfl (by omega) hcb (PositionDispatch.Reached.next reached edge) (hc.trans ha)
  exact build (b - q) q rfl (Nat.le_refl _) qb PositionDispatch.Reached.start rfl

/-- **`AfterP.keep` on a frame in control**: the hypotheses of `PositionWriters.writers_end` (the frame starts in the idle loop in control, each instruction meets
`CleanK` of `FrameKeep.guardE` and stores no routine, mode or task by address, the area is `v`, the frame comes to the player's routine at `n₀`, the first time), the
checks on the ROM (`hc`, `hp`), the time of each instruction, and the two conditions `PosW` and `ClampR` on each instruction from the scroll handler `k` to the
frame's end. Then if he moves right at `k` and the frame ends with the speed there, the frame ends with the position there. -/
theorem keep_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : pCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (time : ∀ j, (trace m i j).pc ≠ sy.EndlessLoop → (trace m i j).fdot ≤ dotsPerFrame - 64)
    (hw : ∀ k n, n₀ ≤ k → k ≤ n → (trace m i k).pc = sy.PlayerSubs → (trace m i n).frame = m.frame → PosW sy m0 (trace m i n))
    (hcr : ∀ k n, n₀ ≤ k → k ≤ n → (trace m i k).pc = sy.PlayerSubs → (trace m i n).frame = m.frame → ClampR sy m0 (trace m i n)) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → 0 < sbyte (peek (trace m i k) sy.Player_X_Speed) →
      peek (PipeTransition.frame m i) sy.Player_X_Speed = peek (trace m i k) sy.Player_X_Speed →
      posP sy (PipeTransition.frame m i) = posP sy (trace m i k) := by
  obtain ⟨hw0, hi, hcC, hs, idle⟩ := pCheck_parts hp
  intro k hk hpc hpos hsame
  rcases PositionWriters.subs_frame hc hw0 h0 hcl hx hv harr hf0 hfirst k hk hpc with hfk | he
  · have F := PositionWriters.writers_end hc hw0 h0 hcl hx hv harr hf0 hfirst k hk hpc hfk
    have hfe := F.ends
    have hkf : k ≤ fuelPerFrame := by
      rcases Nat.lt_or_ge fuelPerFrame k with h | h
      · exfalso
        have s2 : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [hfe]
        have := PipeEntryRule.trace_stop s2 (k - fuelPerFrame)
        rw [show fuelPerFrame + (k - fuelPerFrame) = k by omega] at this
        rw [this, hfe] at hfk
        omega
      · exact h
    obtain ⟨b, hkb, hbf, hb, hlt⟩ := least_of (P := fun n => (trace m i n).frame = m.frame + 1) (fuelPerFrame - k) k
      (by show (trace m i (k + (fuelPerFrame - k))).frame = m.frame + 1; rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega]; exact hfe)
    have live : ∀ n, k ≤ n → n < b → (trace m i n).frame = m.frame := by
      intro n h1 h2
      rcases F.two n h1 with h | h
      · exact h
      · exact absurd h (hlt n h1 h2)
    have hend : PipeTransition.frame m i = trace m i b := by
      rw [PipeEntryRule.frame_trace]
      have s1 : ((trace m i b).frame ≥ m.frame + 1 || (trace m i b).halted) = true := by simp [hb]
      have := PipeEntryRule.trace_stop s1 (fuelPerFrame - b)
      rw [show b + (fuelPerFrame - b) = fuelPerFrame by omega] at this
      exact this
    rw [hend] at hsame ⊢
    exact keep_end hi hcC idle hs (PositionWriters.wCheck_facts hw0).2.2 time hb hkb live F hpc (fun n h1 h2 => hw k n hk h1 hpc (live n h1 h2))
      (fun n h1 h2 => hcr k n hk h1 hpc (live n h1 h2)) hpos hsame
  · rw [he]

/-- **An ordinary piece keeps the position**: at a reached cut `a` before the frame's end that is at neither entry, the next piece is an ordinary step, and it keeps
the position (from `PosW` and the walk) -/
theorem piece_ord (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hs : PositionWriters.innerP sy m0 sy.PlayerSubs = false)
    (hoff : PositionWriters.offStack sy = true) {w : List UInt16} {M : Machine} {input : UInt8} {q b : Nat} {s0 : UInt8}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : PositionWriters.FrameW sy m0 w s0 (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hw : ∀ n, q ≤ n → n < b → PosW sy m0 (trace M input n))
    {a : Nat} (hqa : q ≤ a) (hab : a < b) (hr : PositionDispatch.Reached sy m0 (trace M input) q a)
    (pi : (trace M input a).pc ≠ sy.ImpedePlayerMove) (pc : (trace M input a).pc ≠ (ScreenClamp.places sy m0).entry) :
    ∃ c e, c ≤ b ∧ PositionDispatch.Edge sy m0 (trace M input) a c e ∧ posP sy (trace M input c) = posP sy (trace M input a) := by
  have la := live a hqa hab
  have A := F.atW a hqa la
  have hin := reached_in hs F hq live a hr hab
  have ho : PositionDispatch.Ordinary sy (trace M input a) := by
    obtain ⟨hw1, hw2⟩ := hw a hqa hab
    cases hp : PositionWriters.plainOp ((trace M input a).prg.get! ((trace M input a).pc &&& (trace M input a).prgMask).toNat) with
    | true =>
      have hst : FrameKeep.storesTo (PositionWriters.posI sy) (trace M input a).prg (trace M input a).prgMask (trace M input a).pc = false := by
        cases e : FrameKeep.storesTo (PositionWriters.posI sy) (trace M input a).prg (trace M input a).prgMask (trace M input a).pc with
        | false => rfl
        | true => rw [hw1 e] at hin; cases hin
      exact PositionWriters.ordinary_plain hoff A.rom.1 A.rom.2.1 A.rom.2.2 hp hst
    | false =>
      rcases hw2 hp with h | h
      · rw [hin] at h; cases h
      · exact h
  have ready : PositionDispatch.Ready sy m0 (trace M input a) := by
    unfold PositionDispatch.Ready
    rw [if_neg pi, if_neg pc]
    exact ho
  obtain ⟨c, e, hcb, edge⟩ := PositionDispatch.next_piece hi hcC idle time finish la hab ready
  refine ⟨c, e, hcb, edge, ?_⟩
  have he := edge.effect
  cases edge with
  | ordinary => simpa using he
  | impede _ en _ _ _ => exact absurd en pi
  | clamp _ en _ _ _ => exact absurd en pc

/-- **A frame that makes no call after the scroll handler keeps the position**: if no instruction from the scroll handler `q` to the frame's end `b` is at the
push's entry or at the clamp's entry, then `P(b) = P(Q)`, from `FrameW` and `PosW` -/
theorem still_end (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) (hs : PositionWriters.innerP sy m0 sy.PlayerSubs = false)
    (hoff : PositionWriters.offStack sy = true) {w : List UInt16} {M : Machine} {input : UInt8} {q b : Nat} {s0 : UInt8}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (qb : q ≤ b) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : PositionWriters.FrameW sy m0 w s0 (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hw : ∀ n, q ≤ n → n < b → PosW sy m0 (trace M input n))
    (hnc : ∀ n, q ≤ n → n < b → (trace M input n).pc ≠ sy.ImpedePlayerMove ∧ (trace M input n).pc ≠ (ScreenClamp.places sy m0).entry) :
    posP sy (trace M input b) = posP sy (trace M input q) := by
  have build : ∀ d a, b - a = d → q ≤ a → a ≤ b → PositionDispatch.Reached sy m0 (trace M input) q a →
      posP sy (trace M input a) = posP sy (trace M input q) → posP sy (trace M input b) = posP sy (trace M input q) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro a dist qa ab reached ha
      by_cases done : a = b
      · subst a; exact ha
      · have lt : a < b := by omega
        obtain ⟨c, e, hcb, edge, hc⟩ := piece_ord hi hcC idle hs hoff time finish live F hq hw qa lt reached (hnc a qa lt).1 (hnc a qa lt).2
        have ac := edge.forward
        exact ih (b - c) (by omega) c rfl (by omega) hcb (PositionDispatch.Reached.next reached edge) (hc.trans ha)
  exact build (b - q) q rfl (Nat.le_refl _) qb PositionDispatch.Reached.start rfl

/-- **A frame in control that makes no call after the scroll handler keeps the position there** (`still_end` on a real frame, as `keep_frame`): if no
instruction from the scroll handler `k` on in the frame is at the push's or the clamp's entry, the frame ends with the position of `k` -/
theorem still_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : pCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine)
    (time : ∀ j, (trace m i j).pc ≠ sy.EndlessLoop → (trace m i j).fdot ≤ dotsPerFrame - 64)
    (hw : ∀ k n, n₀ ≤ k → k ≤ n → (trace m i k).pc = sy.PlayerSubs → (trace m i n).frame = m.frame → PosW sy m0 (trace m i n)) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs →
      (∀ n, k ≤ n → (trace m i n).frame = m.frame → (trace m i n).pc ≠ sy.ImpedePlayerMove ∧ (trace m i n).pc ≠ (ScreenClamp.places sy m0).entry) →
      posP sy (PipeTransition.frame m i) = posP sy (trace m i k) := by
  obtain ⟨hw0, hi, hcC, hs, idle⟩ := pCheck_parts hp
  intro k hk hpc hnc
  rcases PositionWriters.subs_frame hc hw0 h0 hcl hx hv harr hf0 hfirst k hk hpc with hfk | he
  · have F := PositionWriters.writers_end hc hw0 h0 hcl hx hv harr hf0 hfirst k hk hpc hfk
    have hfe := F.ends
    have hkf : k ≤ fuelPerFrame := by
      rcases Nat.lt_or_ge fuelPerFrame k with h | h
      · exfalso
        have s2 : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [hfe]
        have := PipeEntryRule.trace_stop s2 (k - fuelPerFrame)
        rw [show fuelPerFrame + (k - fuelPerFrame) = k by omega] at this
        rw [this, hfe] at hfk
        omega
      · exact h
    obtain ⟨b, hkb, hbf, hb, hlt⟩ := least_of (P := fun n => (trace m i n).frame = m.frame + 1) (fuelPerFrame - k) k
      (by show (trace m i (k + (fuelPerFrame - k))).frame = m.frame + 1; rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega]; exact hfe)
    have live : ∀ n, k ≤ n → n < b → (trace m i n).frame = m.frame := by
      intro n h1 h2
      rcases F.two n h1 with h | h
      · exact h
      · exact absurd h (hlt n h1 h2)
    have hend : PipeTransition.frame m i = trace m i b := by
      rw [PipeEntryRule.frame_trace]
      have s1 : ((trace m i b).frame ≥ m.frame + 1 || (trace m i b).halted) = true := by simp [hb]
      have := PipeEntryRule.trace_stop s1 (fuelPerFrame - b)
      rw [show b + (fuelPerFrame - b) = fuelPerFrame by omega] at this
      exact this
    rw [hend]
    exact still_end hi hcC idle hs (PositionWriters.wCheck_facts hw0).2.2 time hb hkb live F hpc (fun n h1 h2 => hw k n hk h1 hpc (live n h1 h2))
      (fun n h1 h2 => hnc n h1 (live n h1 h2))
  · rw [he]

end

end Smbrta.PositionKeep
