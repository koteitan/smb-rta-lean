import Theorems.PipeTransitionAll

/-!
# A lower bound for the change into the room, from single frames

`Route` assumes `change₁ : pipe.E + 91 ≤ room.C`. Here that bound follows from a statement about single frames: a number `left` of the state falls by at
most one per frame, it is 91 at the entry, and it is 0 when Mario has control. A frame that takes longer, a pause or a handler that never ends keep `left`, so they only delay control.

`left` is computed from a few bytes: the pipe's timer while the pipe's routine runs, and then a table found by running the reference entry `E` with no input.
That `left` falls by at most one is a hypothesis for each frame of a run. It is checked here on the entries that are run with no input (`entries_ok`), and by a program on runs with random inputs.
It is not proved for every state. The file has no game data; another pipe can use it with its own routine and numbers. Page: `1-1/b-2-2-PipeChangeBound.md`.
-/

namespace Smbrta.PipeChangeBound

open PipeTransition (frame run zeros entry)
open PipeTransitionAll (Names)

/-! ## From single frames to the whole change -/

section
variable {fm : Nat → Machine} {left : Machine → Nat}

/-- if `left` falls by at most one per frame, then after `j` frames it has fallen by at most `j` -/
theorem low_of_fall {a n : Nat} (h : ∀ j, a ≤ j → j < a + n → left (fm j) ≤ left (fm (j + 1)) + 1) :
    left (fm a) ≤ left (fm (a + n)) + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih fun j h2 h3 => h j h2 (by omega)
    have h4 := h (a + n) (by omega) (by omega)
    have e : a + (n + 1) = a + n + 1 := rfl
    rw [e]
    omega

/-- **No control before `left` has run out.** Control is only possible where `left` is 0. -/
theorem no_ctl_of_fall (ctl : Machine → Bool) {n : Nat} (hf : ∀ j, j < n → left (fm j) ≤ left (fm (j + 1)) + 1)
    (hc : ∀ j, j ≤ n → ctl (fm j) = true → left (fm j) = 0) :
    ∀ j, j ≤ n → j < left (fm 0) → ctl (fm j) = false := by
  intro j hj hl
  have h1 := low_of_fall (fm := fm) (left := left) (a := 0) (n := j) fun i _ h3 => hf i (by omega)
  simp only [Nat.zero_add] at h1
  cases hb : ctl (fm j) with
  | false => rfl
  | true =>
    have := hc j hj hb
    omega

/-- **The bound on the change.** `left` falls by at most one per frame from `E` to `C`, and `left` is 0 at `C`. -/
theorem change_ge {E C : Nat} (hEC : E ≤ C) (hf : ∀ j, E ≤ j → j < C → left (fm j) ≤ left (fm (j + 1)) + 1) (hC : left (fm C) = 0) :
    E + left (fm E) ≤ C := by
  obtain ⟨n, rfl⟩ : ∃ n, C = E + n := ⟨C - E, by omega⟩
  have h1 := low_of_fall (fm := fm) (left := left) (a := E) (n := n) hf
  rw [hC] at h1
  omega

end

/-- the frames of a run with inputs: after `j` frames, the first `j` inputs -/
def seqOf (M : Machine) (w : List UInt8) (j : Nat) : Machine := run M (w.take j)

theorem seqOf_succ (M : Machine) (w : List UInt8) {j : Nat} (hj : j < w.length) :
    seqOf M w (j + 1) = frame (seqOf M w j) (w[j]) := by
  simp only [seqOf]
  rw [← List.take_append_getElem hj, PipeTransition.run_append]
  rfl

/-! ## The number `left` -/

/-- the names this file needs, besides the symbols -/
def nameList : List String := ["ChangeAreaTimer", "ScreenRoutineTask", "DisableScreenFlag"]

def namesOf (text : String) : Names :=
  let lines := text.splitOn "\n"
  nameList.filterMap fun n => (PipeTransitionAll.asmValue lines n).map (n, ·)

/-- the bytes that say how far the change is, after the pipe's routine. In the game core, the position and the fraction of the fall into the room count too. -/
def keyOf (sy : Syms) (nm : Names) (m : Machine) : List UInt8 :=
  let task := peek m sy.OperMode_Task
  [task, peek m (nm.ad "ScreenRoutineTask"), peek m sy.GameEngineSubroutine, peek m (nm.ad "DisableScreenFlag")] ++
    (if task.toUInt16 == sy.Task_GameCore then [peek m sy.Player_State, peek m sy.Player_Y_Position, peek m sy.Player_Y_MoveForce, peek m sy.Player_YMF_Dummy, peek m sy.Player_Y_Speed] else [])

/-- the frames of `e` from `A` on, before control at `A + B`: each key with the frames left -/
def tableOf (sy : Syms) (nm : Names) (e : Machine) (A B : Nat) : List (List UInt8 × Nat) :=
  (List.range B).map fun i => (keyOf sy nm (run e (zeros (A + i))), B - i)

/-- the pipe's routine `eng` runs in the game core -/
def inPipe (sy : Syms) (eng : UInt16) (m : Machine) : Bool :=
  (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore && (peek m sy.GameEngineSubroutine).toUInt16 == eng

/-- the frames that are left at least: the timer and `B` frames after it in the pipe's routine `eng`; else from the table; 0 for a key that is not in the table -/
def leftOf (sy : Syms) (nm : Names) (eng : UInt16) (tbl : List (List UInt8 × Nat)) (B : Nat) (m : Machine) : Nat :=
  if inPipe sy eng m then (peek m (nm.ad "ChangeAreaTimer")).toNat + B else (tbl.lookup (keyOf sy nm m)).getD 0

/-- no key of the table is a state of the player control routine, and the pipe's routine is another routine -/
def keysOK (sy : Syms) (eng : UInt16) (tbl : List (List UInt8 × Nat)) : Bool :=
  eng != sy.Eng_PlayerCtrl && tbl.all fun p => (p.1[2]?).map (·.toUInt16) != some sy.Eng_PlayerCtrl

theorem lookup_mem {k : List UInt8} {v : Nat} : ∀ {t : List (List UInt8 × Nat)}, t.lookup k = some v → ∃ p ∈ t, p.1 = k := by
  intro t
  induction t with
  | nil => intro h; cases h
  | cons a t ih =>
    intro h
    obtain ⟨a1, a2⟩ := a
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hb
      have hk : k = a1 := by simpa using hb
      exact ⟨(a1, a2), List.mem_cons_self, hk.symm⟩
    · obtain ⟨p, hp, hq⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hq⟩

/-- **Control only where `left` is 0.** -/
theorem left_zero_of_ctl {sy : Syms} {nm : Names} {eng : UInt16} {tbl : List (List UInt8 × Nat)} {B : Nat} {m : Machine}
    (hk : keysOK sy eng tbl = true) (hc : controllable sy m = true) : leftOf sy nm eng tbl B m = 0 := by
  simp only [keysOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hk
  obtain ⟨h1, h2⟩ := hk
  simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
  have he := hc.2
  have hp : inPipe sy eng m = false := by
    cases hq : inPipe sy eng m with
    | false => rfl
    | true =>
      simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at hq
      exact absurd (hq.2.symm.trans he) h1
  simp only [leftOf, hp]
  cases hl : tbl.lookup (keyOf sy nm m) with
  | none => rfl
  | some v =>
    exfalso
    obtain ⟨p, hm, hq⟩ := lookup_mem hl
    have h3 := h2 p hm
    apply h3
    rw [hq]
    simp only [keyOf]
    have : ([peek m sy.OperMode_Task, peek m (nm.ad "ScreenRoutineTask"), peek m sy.GameEngineSubroutine, peek m (nm.ad "DisableScreenFlag")] ++
      (if (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore then [peek m sy.Player_State, peek m sy.Player_Y_Position, peek m sy.Player_Y_MoveForce, peek m sy.Player_YMF_Dummy, peek m sy.Player_Y_Speed] else []))[2]? = some (peek m sy.GameEngineSubroutine) := by
      simp
    rw [this]
    simp [he]

/-- **The condition on the entry.** The pipe's routine runs in the game core, and the timer is at least `c`. All other bytes are free. -/
structure EntryCond (sy : Syms) (nm : Names) (eng : UInt16) (c : Nat) (M : Machine) : Prop where
  pipe : inPipe sy eng M = true
  timer : c ≤ (peek M (nm.ad "ChangeAreaTimer")).toNat

theorem left_of_entry {sy : Syms} {nm : Names} {eng : UInt16} {c : Nat} {M : Machine} (tbl : List (List UInt8 × Nat)) (B : Nat) (h : EntryCond sy nm eng c M) :
    c + B ≤ leftOf sy nm eng tbl B M := by
  simp only [leftOf, h.pipe, if_true]
  have := h.timer
  omega

/-- control only where `left` is 0, and `left` falls by at most one per frame, for `n` frames with no input -/
def chainOK (sy : Syms) (lf : Machine → Nat) : Nat → Machine → Bool
  | 0, m => !controllable sy m || lf m == 0
  | n + 1, m =>
    (!controllable sy m || lf m == 0) && decide (lf m ≤ lf (frame m 0) + 1) && chainOK sy lf n (frame m 0)

theorem chainOK_spec (sy : Syms) (lf : Machine → Nat) : ∀ (n : Nat) (m : Machine), chainOK sy lf n m = true →
    (∀ j, j < n → lf (run m (zeros j)) ≤ lf (run m (zeros (j + 1))) + 1) ∧
    (∀ j, j ≤ n → controllable sy (run m (zeros j)) = true → lf (run m (zeros j)) = 0) := by
  intro n
  induction n with
  | zero =>
    intro m h
    refine ⟨fun j hj => by omega, fun j hj hc => ?_⟩
    obtain rfl : j = 0 := by omega
    simp only [chainOK, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    change controllable sy m = true at hc
    change lf m = 0
    rcases h with h | h
    · rw [h] at hc
      cases hc
    · exact h
  | succ n ih =>
    intro m h
    simp only [chainOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨i1, i2⟩ := ih _ h3
    constructor
    · intro j hj
      cases j with
      | zero => exact h2
      | succ j =>
        rw [PipeTransition.run_zeros_cons m j, PipeTransition.run_zeros_cons m (j + 1)]
        exact i1 j (by omega)
    · intro j hj hc
      cases j with
      | zero =>
        change controllable sy m = true at hc
        change lf m = 0
        rcases h1 with h | h
        · rw [h] at hc
          cases hc
        · exact h
      | succ j =>
        rw [PipeTransition.run_zeros_cons m j] at hc ⊢
        exact i2 j (by omega) hc

/-- with no input, a state whose chain was checked has no control while `left` lasts -/
theorem no_ctl_of_chain {sy : Syms} {lf : Machine → Nat} {n : Nat} {m : Machine} (h : chainOK sy lf n m = true) :
    ∀ j, j ≤ n → j < lf m → controllable sy (run m (zeros j)) = false := by
  obtain ⟨h1, h2⟩ := chainOK_spec sy lf n m h
  exact no_ctl_of_fall (fm := fun j => run m (zeros j)) (left := lf) (controllable sy) (n := n) h1 h2

/-! ## The check on the entries that are run -/

/-- the states `es`: `left` at each is `A + B`, and the chain holds for `A + B` frames. The table comes from the reference `e`. -/
def entriesOK (sy : Syms) (nm : Names) (eng : UInt16) (e : Machine) (es : List Machine) (A B : Nat) : Bool :=
  let lf := leftOf sy nm eng (tableOf sy nm e A B) B
  es.all fun m => lf m == A + B && chainOK sy lf (A + B) m

/-- what the check says -/
theorem entries_ok {sy : Syms} {nm : Names} {eng : UInt16} {e : Machine} {es : List Machine} {A B : Nat} (h : entriesOK sy nm eng e es A B = true) :
    ∀ m ∈ es, leftOf sy nm eng (tableOf sy nm e A B) B m = A + B ∧
      ∀ j, j < A + B → controllable sy (run m (zeros j)) = false := by
  intro m hm
  simp only [entriesOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h m hm
  refine ⟨h1, fun j hj => no_ctl_of_chain h2 j (by omega) ?_⟩
  rw [h1]
  exact hj

/-! ## The statement for a run -/

/-- A change of area in a run, on single frames. `fm j` is the state of the frame `j` of the run, counted as `pipe.E` and `room.C` are counted. `n` is the length of the bound. -/
structure Change (left : Machine → Nat) (n : Nat) where
  fm : Nat → Machine
  E : Nat
  C : Nat
  order : E ≤ C
  /-- `left` falls by at most one per frame -/
  fall : ∀ j, E ≤ j → j < C → left (fm j) ≤ left (fm (j + 1)) + 1
  /-- `left` at the entry -/
  start : n ≤ left (fm E)
  /-- `left` when Mario has control -/
  atControl : left (fm C) = 0

/-- the bound on the change follows from the single frames: `change₁` of `Route` with `n = 91` -/
theorem Change.bound {left : Machine → Nat} {n : Nat} (R : Change left n) : R.E + n ≤ R.C := by
  have h := change_ge (fm := R.fm) (left := left) R.order R.fall R.atControl
  have := R.start
  omega

/-- **No control for any inputs, from single frames.** For a machine and a list of inputs, if `left` falls by at most one on each of these frames and control is possible only where `left` is 0,
there is no control on the first `left M - 1` frames. -/
theorem no_control (ctl : Machine → Bool) {left : Machine → Nat} (M : Machine) (w : List UInt8)
    (hf : ∀ j (h : j < w.length), left (seqOf M w j) ≤ left (frame (seqOf M w j) w[j]) + 1)
    (hc : ∀ j, j ≤ w.length → ctl (seqOf M w j) = true → left (seqOf M w j) = 0) :
    ∀ j, j ≤ w.length → j < left M → ctl (seqOf M w j) = false := by
  refine no_ctl_of_fall (fm := seqOf M w) (left := left) ctl (n := w.length) (fun j hj => ?_) hc
  rw [seqOf_succ M w hj]
  exact hf j hj

/-- **No control, for any inputs, if `left` falls by at most one on each frame of this run.** The condition on the entry is on one state. The hypothesis `hf` is on single frames of the run, and it is not proved. -/
theorem no_control_entry {sy : Syms} {nm : Names} {eng : UInt16} {tbl : List (List UInt8 × Nat)} {B c : Nat} (hk : keysOK sy eng tbl = true) (M : Machine)
    (hE : EntryCond sy nm eng c M) (w : List UInt8)
    (hf : ∀ j (h : j < w.length), leftOf sy nm eng tbl B (seqOf M w j) ≤ leftOf sy nm eng tbl B (frame (seqOf M w j) w[j]) + 1) :
    ∀ j, j ≤ w.length → j < c + B → controllable sy (seqOf M w j) = false := by
  intro j h1 h2
  exact no_control (controllable sy) (left := leftOf sy nm eng tbl B) M w hf (fun i _ hc => left_zero_of_ctl hk hc) j h1
    (Nat.lt_of_lt_of_le h2 (left_of_entry tbl B hE))

end Smbrta.PipeChangeBound
