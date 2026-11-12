import Theorems.Route
import Theorems.HurryFrame

/-!
# The first frame of control after a change, as the walk of the hurry-up music needs it

`HurryMusic.Run` asked of one frame that it begins as `HurryFrame.Start` says: the idle loop, the routine of control or of the entrance, the game's mode and its core, and the
six bytes of `DigitModifier` 0 (`Run.start`). When the music comes after a change of area, that frame is the last frame of the change: it begins in the routine of the
entrance and ends with control. Here it comes from the rows of the change.

The rows of the two changes (`PipeChangeEnd`, `SideChangeEnd`) hold every machine from the exit of the pipe to the first control. A frame goes from a row to the next, and the
number `left` of the row falls by at most one. On a run of the change `left` is not 0 before control, and it is 0 at control. So the machine of the last frame before control is
in a row with `left` 1 (`PipeRun.startLast`, `EndRun.startLast`). In every state of these rows the frame starts in the idle loop, in the routine of the entrance, and the bytes of
`DigitModifier` are known 0 (`rowsCheck₁`, `rowsCheck₂`, checks on the ROM): the change clears them when it loads the area. So that machine is as `HurryFrame.Start` asks.

On a run as `Route.Base` numbers it, the last frame of the first change is frame `b₁ − 1` (`Chg₁.startLast`), and that of the second change frame `b₂ − 1` (`changes_startLast`).
The conditions of the first change are those of `Route.Changes` on it (`Chg₁`): a run whose music starts in the room fails a condition of the second change (`entry₂`, the music's bytes),
so the first change has its own structure. No game data. Page: `1-1/0-6-4-2-2-2-1-HurryStart.md`.
-/

namespace Smbrta.HurryStart

open TaintRun (AS Sim Env)
open SideChangeEnd (Row Ctx Covered InvL statesOK knowsAd mOf covered_of_invL left_of_covered peek_of_known)
open PipeTransitionAll (Names)
open PipeTransition (frame)
open PipeWrites (Guard FrameStart)
open CastleToLevel (Kind)

/-! ## The check on the rows -/

/-- a state as `HurryFrame.Start` asks it with the routine of the entrance: at the start of a frame (`FrameKeep.endOK`), the bytes of `DigitModifier` known 0, the routine of the
entrance, the game's mode and its core known -/
def rowE (sy : Syms) (G : Guard) (P : HurryFrame.Places) (S : AS) : Bool :=
  FrameKeep.endOK G S && FrameKeep.watchOK (HurryFrame.modsW P) S &&
    knowsAd S sy.GameEngineSubroutine && knowsAd S sy.OperMode && knowsAd S sy.OperMode_Task &&
    peek (mOf S) sy.GameEngineSubroutine == sy.Eng_PlayerEntrance.toUInt8 && peek (mOf S) sy.OperMode == sy.GameModeValue.toUInt8 &&
    peek (mOf S) sy.OperMode_Task == sy.Task_GameCore.toUInt8

/-- every row is as `statesOK` says, and every state of a row with `left` 1 is as `rowE` says -/
def rowsE (sy : Syms) (G : Guard) (P : HurryFrame.Places) (c : Ctx) (l : List Row) : Bool :=
  l.all fun r => statesOK c r && (r.v != 1 || r.R.all (rowE sy G P))

/-- the environment has the program of `m0` -/
def envSame (E : Env) (m0 : Machine) : Bool := decide (E.prg.data = (PipeEntryRule.envOf m0).prg.data) && E.mask == (PipeEntryRule.envOf m0).mask

/-- the reference machine at the exit is not in the game core: a machine with its bytes at the exit has no control -/
def exitOff (sy : Syms) (x : Machine) : Bool := (peek x sy.OperMode_Task).toUInt16 != sy.Task_GameCore

/-- **The check of the first change** (into the room): its rows `rowsA` and `rowsB` (`PipeChangeEnd.InRows`) -/
def rowsCheck₁ (sy : Syms) (nm : Names) (m0 : Machine) (nm₁ : Names) (d : PipeChangeEnd.Data) (e : Machine) : Bool :=
  let G := HurryFrame.guardOf sy nm m0
  let P := HurryFrame.placesOf sy nm m0
  let c := PipeChangeEnd.ctxOf sy nm₁ d e
  envSame c.E m0 && exitOff sy (PipeChangeEnd.refX e) && rowsE sy G P c (PipeChangeEnd.rowsA c d e) && rowsE sy G P c (PipeChangeEnd.rowsB c d e)

/-- **The check of the second change** (out of the side pipe): its rows `rows0` and `rows1` (`SideChangeEnd.InRows`) -/
def rowsCheck₂ (sy : Syms) (nm : Names) (m0 : Machine) (nm₂ nx₂ : Names) (e : Machine) (A B : Nat) : Bool :=
  let G := HurryFrame.guardOf sy nm m0
  let P := HurryFrame.placesOf sy nm m0
  let c := SideChangeEnd.rowCtx sy nm₂ nx₂ e A B
  envSame c.E m0 && exitOff sy (SideChangeEnd.refExit e A) && rowsE sy G P c (SideChangeEnd.rows0 c nx₂ e A B) && rowsE sy G P c (SideChangeEnd.rows1 c nx₂ e A B)

/-! ## From a state of the rows to `HurryFrame.Start` -/

section
variable {sy : Syms} {nm : Names} {m0 : Machine}

theorem ba_eq {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- the known bytes of the guard with the routine of the entrance, on a machine in that routine, in the game's mode and its core, with the bytes of `DigitModifier` 0 -/
theorem known_E {m : Machine} (hr : m.ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = sy.Eng_PlayerEntrance.toUInt8)
    (hmo : m.ram.get! (sy.OperMode &&& 0x7FF).toNat = sy.GameModeValue.toUInt8) (hta : m.ram.get! (sy.OperMode_Task &&& 0x7FF).toNat = sy.Task_GameCore.toUInt8)
    (hm : FrameKeep.Watched (HurryFrame.modsW (HurryFrame.placesOf sy nm m0)) m) :
    ∀ p ∈ (HurryFrame.guardE sy (HurryFrame.guardOf sy nm m0)).known, m.ram.get! p.1 = p.2 := by
  intro p hp
  have e : (HurryFrame.guardE sy (HurryFrame.guardOf sy nm m0)).known =
      ((FrameKeep.guardK sy m0).known ++ (HurryFrame.placesOf sy nm m0).mods.map (fun i => (i, (0 : UInt8)))).map
        (fun p => if p.1 == (sy.GameEngineSubroutine &&& 0x7FF).toNat then (p.1, sy.Eng_PlayerEntrance.toUInt8) else p) := rfl
  rw [e] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  by_cases hq1 : q.1 = (sy.GameEngineSubroutine &&& 0x7FF).toNat
  · rw [if_pos (by simpa using hq1)]
    show m.ram.get! q.1 = _
    rw [hq1]
    exact hr
  · rw [if_neg (by simpa using hq1)]
    rcases List.mem_append.1 hq with hq | hq
    · have e2 : (FrameKeep.guardK sy m0).known = [((sy.GameEngineSubroutine &&& 0x7FF).toNat, sy.Eng_PlayerCtrl.toUInt8), ((sy.OperMode &&& 0x7FF).toNat, sy.GameModeValue.toUInt8),
          ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8)] := rfl
      rw [e2] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact absurd rfl hq1
      · exact hmo
      · exact hta
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
      have h1 : m.ram.get! i &&& 0xFF = (0 : UInt8) &&& 0xFF := hm (i, 0xFF, 0) (List.mem_map.2 ⟨i, hi, rfl⟩)
      rw [FrameKeep.and_ff, FrameKeep.and_ff] at h1
      exact h1

/-- **A machine covered by a state of `rowE` begins as `HurryFrame.Start` asks**, with the routine of the entrance -/
theorem start_of_rowE {E : Env} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim E F S m)
    (hr : rowE sy (HurryFrame.guardOf sy nm m0) (HurryFrame.placesOf sy nm m0) S = true) (he : envSame E m0 = true) : HurryFrame.Start sy nm m0 m := by
  simp only [rowE, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, k1⟩, k2⟩, k3⟩, v1⟩, v2⟩, v3⟩ := hr
  simp only [envSame, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
  have hr' : peek m sy.GameEngineSubroutine = sy.Eng_PlayerEntrance.toUInt8 := (peek_of_known hs k1).trans v1
  have hmo : peek m sy.OperMode = sy.GameModeValue.toUInt8 := (peek_of_known hs k2).trans v2
  have hta : peek m sy.OperMode_Task = sy.Task_GameCore.toUInt8 := (peek_of_known hs k3).trans v3
  exact Or.inr (FrameKeep.start_of_sim hs h1 (ba_eq he.1) he.2 (known_E hr' hmo hta (FrameKeep.watched_of h2 hs)))

/-- **A machine in rows that pass `rowsE`, with `left` 1, begins as `HurryFrame.Start` asks** -/
theorem start_of_left {c : Ctx} {l : List Row} (hck : rowsE sy (HurryFrame.guardOf sy nm m0) (HurryFrame.placesOf sy nm m0) c l = true)
    (he : envSame c.E m0 = true) {m : Machine} (h : InvL c l m) (h1 : c.left m = 1) : HurryFrame.Start sy nm m0 m := by
  obtain ⟨r, hr, S, hS, hs⟩ := covered_of_invL h
  have hc := List.all_eq_true.1 hck r hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
  have hv : c.left m = r.v := left_of_covered hc.1 ⟨S, hS, hs⟩
  rcases hc.2 with h2 | h2
  · exact absurd (hv.symm.trans h1) h2
  · exact start_of_rowE hs (List.all_eq_true.1 h2 S hS) he

/-- a machine with the bytes of a reference exit that is not in the game core has no control -/
theorem ctl_of_exitOff {nmx : Names} {x m : Machine} (hx : exitOff sy x = true) (h : TaintRun.ExitAt (SideChangeBound.exitBytes sy nmx x) m) : controllable sy m = false := by
  have e1 : peek m sy.OperMode_Task = peek x sy.OperMode_Task := h ((sy.OperMode_Task &&& 0x7FF).toNat, peek x sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  simp only [exitOff, bne_iff_ne, ne_eq] at hx
  cases hc : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    rw [e1] at hc
    exact hx hc.1.2

end

/-! ## The first change: the last frame before control -/

section
open PipeChangeEnd (EndStatement PipeRun During InRows leftP during_left)
variable {sy : Syms} {nm₁ : Names} {d : PipeChangeEnd.Data} {e : Machine} {es : List Machine}

/-- on a run of the change into the room, each machine up to control is in the pipe or in the rows, when `left` is not 0 before control -/
theorem PipeRun.way (T : EndStatement sy nm₁ d e es) (R : PipeRun sy nm₁ d e) (hf : ∀ n, R.a ≤ n → n < R.b → leftP sy nm₁ e (R.seq n) ≠ 0) :
    ∀ k, R.a + k ≤ R.b → During d e (R.seq (R.a + k)) ∨ InRows sy nm₁ d e (R.seq (R.a + k)) := by
  intro k
  induction k with
  | zero => exact fun _ => Or.inl (T.during _ R.entry)
  | succ k ih =>
    intro hk
    have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
    rw [e1, R.next (R.a + k)]
    have hgap : R.a ≤ R.a + k := by omega
    have hlt : R.a + k < R.b := by omega
    rcases ih (by omega) with h1 | h1
    · have hP := R.places _ hgap hlt (T.inRoutine _ h1)
      rcases (T.step _ h1 (R.inp (R.a + k)) hP).2 with g | ⟨g1, g2⟩
      · exact Or.inl g
      · right
        rw [← R.next (R.a + k)] at g1 g2 ⊢
        obtain ⟨q1, q2, q3⟩ := R.quiet _ (by omega) (by omega) g1
        exact g2 q1 q2 q3
    · rcases T.rows _ h1 (R.inp (R.a + k)) (R.noStart _ hgap hlt) with g | ⟨g1, _⟩
      · exact absurd g (hf _ hgap hlt)
      · exact Or.inr g1

/-- **The last frame of the change into the room begins as `HurryFrame.Start` asks**, with the routine of the entrance: frame `b − 1`, after the entry. `hf`: `left` is not 0
before control (`PipeChangeEnd.PipeRun.first`). `hH` is the check on the ROM. -/
theorem PipeRun.startLast {nm : Names} {m0 : Machine} (T : EndStatement sy nm₁ d e es) (R : PipeRun sy nm₁ d e)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftP sy nm₁ e (R.seq n) ≠ 0) (hH : rowsCheck₁ sy nm m0 nm₁ d e = true) :
    R.a + 1 ≤ R.b ∧ HurryFrame.Start sy nm m0 (R.seq (R.b - 1)) := by
  simp only [rowsCheck₁, Bool.and_eq_true] at hH
  obtain ⟨⟨⟨hE, hX⟩, hA⟩, hB⟩ := hH
  have h0 := T.atControl _ R.atCtl
  have hab : R.a + 1 ≤ R.b := by
    have := R.order
    refine Nat.lt_of_le_of_ne this fun heq => ?_
    have hd := during_left T (T.during _ R.entry)
    rw [heq] at hd
    exact hd h0
  refine ⟨hab, ?_⟩
  have e1 : R.a + (R.b - 1 - R.a) = R.b - 1 := by omega
  have hw := PipeRun.way T R hf (R.b - 1 - R.a) (by omega)
  rw [e1] at hw
  have hn := R.next (R.b - 1)
  rw [show R.b - 1 + 1 = R.b by omega] at hn
  have hf1 := hf (R.b - 1) (by omega) (by omega)
  rcases hw with h | h
  · exfalso
    have hP := R.places _ (by omega) (by omega) (T.inRoutine _ h)
    rcases (T.step _ h (R.inp (R.b - 1)) hP).2 with g | ⟨g1, _⟩
    · rw [← hn] at g
      exact during_left T g h0
    · rw [← hn] at g1
      have := ctl_of_exitOff hX g1
      rw [R.atCtl] at this
      cases this
  · rcases T.rows _ h (R.inp (R.b - 1)) (R.noStart _ (by omega) (by omega)) with g | ⟨g1, g2⟩
    · exact absurd g hf1
    · rw [← hn, h0] at g2
      have hl : leftP sy nm₁ e (R.seq (R.b - 1)) = 1 := by omega
      rcases h with h | h
      · exact start_of_left hA hE h hl
      · exact start_of_left hB hE h hl

end

/-! ## The second change: the last frame before control -/

section
open SideChangeEnd (EndStatement EndRun St st_step)
open SideChangeBound (Statement leftAt)
variable {sy : Syms} {nm₂ nx₂ : Names} {e : Machine} {A B : Nat} {es : List Machine}

/-- on a run of the change out of the side pipe, each machine up to control is in the pipe or in the rows, when `left` is not 0 before control -/
theorem EndRun.way (S : Statement sy nm₂ e es A B) (T : EndStatement sy nm₂ nx₂ e A B) (R : EndRun sy nm₂ nx₂ e A B)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm₂ e A B (R.seq n) ≠ 0) : ∀ k, R.a + k ≤ R.b → St sy nm₂ nx₂ e A B (R.seq (R.a + k)) := by
  intro k
  induction k with
  | zero => exact fun _ => Or.inl (T.during _ R.entry)
  | succ k ih =>
    intro hk
    have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
    rw [e1, R.next (R.a + k)]
    have hn := R.next (R.a + k)
    have hq : TaintRun.ExitAt (SideChangeBound.exitBytes sy nm₂ (SideChangeEnd.refExit e A)) (frame (R.seq (R.a + k)) (R.inp (R.a + k))) →
        SideChangeEnd.Quiet (SideChangeEnd.quietBytes nx₂ e A) (frame (R.seq (R.a + k)) (R.inp (R.a + k))) := by
      intro hx
      rw [← hn] at hx ⊢
      exact R.quiet _ (by omega) (by omega) hx
    rcases st_step S T (ih (by omega)) (R.noStart (R.a + k) (by omega) (by omega)) hq with g | ⟨g1, _⟩
    · exact absurd g (hf _ (by omega) (by omega))
    · exact g1

/-- **The last frame of the change out of the side pipe begins as `HurryFrame.Start` asks**, with the routine of the entrance: frame `b − 1`, after the entry. `hf`: `left` is
not 0 before control (`SideChangeEnd.EndRun.firstF`). `hH` is the check on the ROM. -/
theorem EndRun.startLast {nm : Names} {m0 : Machine} (S : Statement sy nm₂ e es A B) (T : EndStatement sy nm₂ nx₂ e A B) (R : EndRun sy nm₂ nx₂ e A B)
    (hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm₂ e A B (R.seq n) ≠ 0) (hH : rowsCheck₂ sy nm m0 nm₂ nx₂ e A B = true) :
    R.a + 1 ≤ R.b ∧ HurryFrame.Start sy nm m0 (R.seq (R.b - 1)) := by
  simp only [rowsCheck₂, Bool.and_eq_true] at hH
  obtain ⟨⟨⟨hE, hX⟩, hA⟩, hB⟩ := hH
  have h0 := S.atControl _ R.atCtl
  have hab : R.a + 1 ≤ R.b := by
    have := R.order
    refine Nat.lt_of_le_of_ne this fun heq => ?_
    have hd := T.duringLeft _ (T.during _ R.entry)
    rw [heq] at hd
    exact hd h0
  refine ⟨hab, ?_⟩
  have e1 : R.a + (R.b - 1 - R.a) = R.b - 1 := by omega
  have hw := EndRun.way S T R hf (R.b - 1 - R.a) (by omega)
  rw [e1] at hw
  have hn := R.next (R.b - 1)
  rw [show R.b - 1 + 1 = R.b by omega] at hn
  have hf1 := hf (R.b - 1) (by omega) (by omega)
  rcases hw with h | h
  · exfalso
    rcases T.step _ h (R.inp (R.b - 1)) with g | ⟨g1, _⟩
    · rw [← hn] at g
      exact T.duringLeft _ g h0
    · rw [← hn] at g1
      have := ctl_of_exitOff hX g1
      rw [R.atCtl] at this
      cases this
  · rcases T.rows _ h (R.inp (R.b - 1)) (R.noStart _ (by omega) (by omega)) with g | ⟨g1, g2⟩
    · exact absurd g hf1
    · rw [← hn, h0] at g2
      have hl : leftAt sy nm₂ e A B (R.seq (R.b - 1)) = 1 := by omega
      rcases h with h | h
      · exact start_of_left hA hE h hl
      · exact start_of_left hB hE h hl

end

/-! ## On the frames of a run -/

/-- **The conditions of the first change** on the frames of a run, those of `Route.Changes` on the first change: a run whose hurry-up music starts in the room fails a condition
of the second change (`Route.Changes.entry₂`), so the first change has its own structure here. -/
structure Chg₁ (sy : Syms) (m0 : Machine) (nm₁ : Names) (d₁ : PipeChangeEnd.Data) (B : Route.Base) (kind : Nat → Kind) : Prop where
  /-- the part of the condition at the entry that the press of Start and the frames from control do not give -/
  entryRest₁ : EntryKeep.Rest d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))
  /-- each instruction of the frames from control to the entry is `Clean` -/
  upClean₁ : ∀ n, 1 ≤ n → n < B.a₁ sy → ∀ j, PipeWrites.Clean (EntryKeep.guardOf sy m0 d₁ (PipeTransition.entry m0)) (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- control within `dB` frames of the entry -/
  ctlBy₁ : controllable sy (B.seq (B.a₁ sy + B.dB)) = true
  /-- a `lag` frame is a paused frame -/
  paused₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → kind n = .lag → PipeChangeEnd.Paused d₁ (B.seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → PipeChangeBound.inPipe sy sy.EngVerticalPipe (B.seq n) = true →
    ∀ j, PipeChangeEnd.PlaceOK d₁.places (PipeEntryRule.trace (B.seq n) (B.inp n) j)
  /-- at the exit, the sound's bytes, the song and the screen buffer are as the condition says -/
  quiet₁ : ∀ n, B.a₁ sy ≤ n → n ≤ B.b₁ sy → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (B.seq n) →
    SideChangeEnd.Quiet (PipeChangeEnd.quietQ d₁ (PipeTransition.entry m0)) (B.seq n) ∧ PipeChangeEnd.SongAt d₁.song (B.seq n) ∧ PipeChangeEnd.SongAt d₁.xshape (B.seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart₁ : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → SideChangeEnd.coreFrame sy sy.EngVerticalPipe (B.seq n) = true → SideChangeEnd.noStart (B.inp n) = true
  /-- at the exit, the sound's pause flag is 0 and the game timer is not 000 -/
  time₁ : ∀ n, B.a₁ sy ≤ n → n ≤ B.b₁ sy → SideChangeBound.ExitAt (PipeChangeEnd.exitQ sy nm₁ (PipeTransition.entry m0)) (B.seq n) → SideChangeEnd.TimeOK d₁.nx (B.seq n)

section
variable {sy : Syms} {m0 : Machine} {nm₁ : Names} {d₁ : PipeChangeEnd.Data} {nm₂ nx₂ nmS : Names} {B : Route.Base} {kind : Nat → Kind} {e₁ c₂ e₂ c₃ : Nat}

/-- the first change's conditions of `Route.Changes` -/
theorem chg₁_of_changes (C : Route.Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) : Chg₁ sy m0 nm₁ d₁ B kind :=
  ⟨C.entryRest₁, C.upClean₁, C.ctlBy₁, C.paused₁, C.places₁, C.quiet₁, C.noStart₁, C.time₁⟩

/-- the end of the first change is the first control after the entry, by the choice of `b₁` -/
theorem Chg₁.ctlFirst (_C : Chg₁ sy m0 nm₁ d₁ B kind) : ∀ n, B.a₁ sy ≤ n → n < B.b₁ sy → controllable sy (B.seq n) = false :=
  fun n h1 h2 => Route.firstWith_first (fun n => controllable sy (B.seq n)) _ B.dB n h1 h2

/-- the condition at the vertical pipe's entry, from the press of Start on the title, as `Route.Run.entry₁` -/
theorem Chg₁.entry {tc : TitleStart.Ctx} {t0 : Nat} (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (T : TitleStart.Begin sy tc B.seq B.inp)
    (C : Chg₁ sy m0 nm₁ d₁ B kind) : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy)) := by
  have stay : ∀ n, 1 ≤ n → n < B.a₁ sy → controllable sy (B.seq n) = true := fun n h1 h2 => by
    have h := Route.firstWith_first _ 1 B.dA n h1 h2
    simpa using h
  exact EntryKeep.entry_of_title hB hK T B.next (Route.firstWith_ge _ 1 B.dA) (EntryKeep.starts_of_title hB hK T B.next stay C.upClean₁) C.upClean₁ C.entryRest₁

/-- the first change as `PipeChangeEnd.PipeRun`, as `Route.Changes.run₁` -/
def Chg₁.run₁ (C : Chg₁ sy m0 nm₁ d₁ B kind) (he : PipeChangeEnd.Entry d₁ (PipeTransition.entry m0) (B.seq (B.a₁ sy))) :
    PipeChangeEnd.PipeRun sy nm₁ d₁ (PipeTransition.entry m0) where
  seq := B.seq
  inp := B.inp
  next := B.next
  lag := fun n => kind n = .lag
  dec := fun _ => inferInstance
  cnt := CastleToLevel.seen kind
  hcnt := fun _ => rfl
  a := B.a₁ sy
  b := B.b₁ sy
  order := Route.firstWith_ge _ _ B.dB
  entry := he
  atCtl := Route.firstWith_at (fun n => controllable sy (B.seq n)) _ B.dB C.ctlBy₁
  lagPaused := C.paused₁
  places := C.places₁
  quiet := C.quiet₁
  noStart := C.noStart₁

/-- **The last frame of the first change, frame `b₁ − 1`, begins as `HurryFrame.Start` asks**, on the frames of a run. `hT` is the check of the change, `hB` and `hK`
those of the start from the title, `hH` that of the rows. -/
theorem Chg₁.startLast {nm : Names} {es₁ : List Machine} {tc : TitleStart.Ctx} {t0 : Nat} (hT : PipeChangeEnd.EndStatement sy nm₁ d₁ (PipeTransition.entry m0) es₁)
    (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc) (hH : rowsCheck₁ sy nm m0 nm₁ d₁ (PipeTransition.entry m0) = true)
    (T : TitleStart.Begin sy tc B.seq B.inp) (C : Chg₁ sy m0 nm₁ d₁ B kind) :
    B.a₁ sy + 1 ≤ B.b₁ sy ∧ HurryFrame.Start sy nm m0 (B.seq (B.b₁ sy - 1)) :=
  PipeRun.startLast hT (C.run₁ (C.entry hB hK T)) ((C.run₁ (C.entry hB hK T)).first hT C.time₁ C.ctlFirst) hH

/-- **The last frame of the second change, frame `b₂ − 1`, begins as `HurryFrame.Start` asks**, on the frames of a run with the conditions of both changes. `hS`, `hT`, `hR`
are the checks of the changes, `hB` and `hK` those of the start from the title, `hH` that of the rows. -/
theorem changes_startLast {nm : Names} {es : List Machine} {tc : TitleStart.Ctx} {t0 : Nat}
    (hS : SideChangeBound.Statement sy nm₂ (SideTransition.entry m0) es 160 122) (hT : SideChangeEnd.EndStatement sy nm₂ nx₂ (SideTransition.entry m0) 160 122)
    (hR : Route.RoomChecks sy m0 nm₁ d₁ nm₂ nx₂ nmS) (hB : TitleStart.check sy tc t0 = true) (hK : EntryKeep.Checks sy m0 d₁ tc)
    (hH : rowsCheck₂ sy nm m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 = true) (T : TitleStart.Begin sy tc B.seq B.inp)
    (C : Route.Changes sy m0 nm₁ d₁ nm₂ nx₂ nmS B kind e₁ c₂ e₂ c₃) :
    B.a₂ sy nmS m0 + 1 ≤ B.b₂ sy nmS m0 ∧ HurryFrame.Start sy nm m0 (B.seq (B.b₂ sy nmS m0 - 1)) := by
  have he := (chg₁_of_changes C).entry hB hK T
  exact EndRun.startLast hS hT (C.run₂ hR he) ((C.run₂ hR he).firstF hT C.time₂ C.ctlFirst₂) hH

end

end Smbrta.HurryStart
