import Std.Data.HashSet

/-!
# Reachability certificates

For a step function `step : σ → ι → σ` and a finite input alphabet, `next L` is the
list of all states one step away from some state of `L` (duplicates removed with a
hash set). `layer k` = `iter next k [s0]` contains every state reachable in exactly `k`
steps (`run_mem`), so a property checked on the layers `0..n` holds after every
input sequence of length `≤ n` (`lower_bound`). Only the check `checkUpTo` has to be
computed (by `native_decide`); this file proves the rest once, for any `step`.
-/

namespace Smbrta.Cert

variable {σ ι : Type} [DecidableEq σ] [Hashable σ] [LawfulHashable σ]

def run (step : σ → ι → σ) (s : σ) (seq : List ι) : σ := seq.foldl step s

/-- `iter f n x` = f applied `n` times to `x` -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

def next (step : σ → ι → σ) (inputs : List ι) (L : List σ) : List σ :=
  (Std.HashSet.ofList (L.flatMap fun s => inputs.map (step s))).toList

theorem mem_next (step : σ → ι → σ) (inputs : List ι) (L : List σ) {s : σ} {i : ι}
    (hs : s ∈ L) (hi : i ∈ inputs) : step s i ∈ next step inputs L := by
  unfold next
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList, List.contains_iff_mem]
  exact List.mem_flatMap.2 ⟨s, hs, List.mem_map.2 ⟨i, hi, rfl⟩⟩

theorem run_mem (step : σ → ι → σ) (inputs : List ι) :
    ∀ (seq : List ι) (L : List σ) (s : σ), s ∈ L → (∀ i ∈ seq, i ∈ inputs) →
      run step s seq ∈ iter (next step inputs) seq.length L
  | [], _, _, hs, _ => hs
  | i :: rest, L, s, hs, hseq => by
    simp only [run, List.foldl_cons, iter]
    exact run_mem step inputs rest _ _ (mem_next step inputs L hs (hseq i (by simp)))
      (fun j hj => hseq j (by simp [hj]))

/-- `checkUpTo P n L` checks `P` on the layers `L, next L, …, next^[n] L`. -/
def checkUpTo (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool) : Nat → List σ → Bool
  | 0, L => L.all P
  | n + 1, L => L.all P && checkUpTo step inputs P n (next step inputs L)

omit [LawfulHashable σ] in
theorem checkUpTo_spec (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool) :
    ∀ (n : Nat) (L : List σ), checkUpTo step inputs P n L = true →
      ∀ k ≤ n, ∀ s ∈ iter (next step inputs) k L, P s = true
  | 0, L, h, k, hk, s, hs => by
    have : k = 0 := by omega
    subst this
    simp only [checkUpTo, List.all_eq_true] at h
    exact h s hs
  | n + 1, L, h, k, hk, s, hs => by
    simp only [checkUpTo, Bool.and_eq_true, List.all_eq_true] at h
    cases k with
    | zero => exact h.1 s hs
    | succ k =>
      simp only [iter] at hs
      exact checkUpTo_spec step inputs P n _ h.2 k (by omega) s hs

/-- If the check passes, `P` holds after every input sequence of length at most `n`. -/
theorem lower_bound (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool) (s0 : σ) (n : Nat)
    (h : checkUpTo step inputs P n [s0] = true) :
    ∀ seq : List ι, (∀ i ∈ seq, i ∈ inputs) → seq.length ≤ n → P (run step s0 seq) = true :=
  fun seq hseq hlen =>
    checkUpTo_spec step inputs P n [s0] h seq.length hlen _
      (run_mem step inputs seq [s0] s0 (by simp) hseq)

end Smbrta.Cert

namespace Smbrta.Cert

variable {σ ι : Type} [DecidableEq σ] [Hashable σ] [LawfulHashable σ]

/-! ## Pruned search

`keep r s` says whether to follow `s` when `r` frames remain. The dropped states must be
safe by another argument (`hdrop`): every sequence of at most `r` frames from them keeps `P`. -/

def checkPruned (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool) (keep : Nat → σ → Bool) :
    Nat → List σ → Bool
  | 0, L => L.all P
  | r + 1, L => L.all P && checkPruned step inputs P keep r ((next step inputs L).filter (keep r))

theorem pruned_spec (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool) (keep : Nat → σ → Bool)
    (hdrop : ∀ r s, keep r s = false →
      ∀ seq : List ι, (∀ i ∈ seq, i ∈ inputs) → seq.length ≤ r → P (run step s seq) = true) :
    ∀ (r : Nat) (L : List σ), checkPruned step inputs P keep r L = true →
      ∀ s ∈ L, ∀ seq : List ι, (∀ i ∈ seq, i ∈ inputs) → seq.length ≤ r → P (run step s seq) = true
  | 0, L, h, s, hs, seq, _, hlen => by
    have : seq = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [checkPruned, List.all_eq_true] at h
    exact h s hs
  | r + 1, L, h, s, hs, seq, hseq, hlen => by
    simp only [checkPruned, Bool.and_eq_true, List.all_eq_true] at h
    cases seq with
    | nil => exact h.1 s hs
    | cons i rest =>
      have hi : i ∈ inputs := hseq i (by simp)
      have hrest : ∀ j ∈ rest, j ∈ inputs := fun j hj => hseq j (by simp [hj])
      have hlen' : rest.length ≤ r := by simp at hlen; omega
      have ht : step s i ∈ next step inputs L := mem_next step inputs L hs hi
      show P (rest.foldl step (step s i)) = true
      by_cases hk : keep r (step s i) = true
      · exact pruned_spec step inputs P keep hdrop r _ h.2 (step s i)
          (List.mem_filter.2 ⟨ht, hk⟩) rest hrest hlen'
      · exact hdrop r (step s i) (by simpa using hk) rest hrest hlen'

/-- If the pruned check passes from `s0`, `P` holds after every sequence of at most `n` frames. -/
theorem lower_bound_pruned (step : σ → ι → σ) (inputs : List ι) (P : σ → Bool)
    (keep : Nat → σ → Bool) (s0 : σ) (n : Nat)
    (hdrop : ∀ r s, keep r s = false →
      ∀ seq : List ι, (∀ i ∈ seq, i ∈ inputs) → seq.length ≤ r → P (run step s seq) = true)
    (h : checkPruned step inputs P keep n [s0] = true) :
    ∀ seq : List ι, (∀ i ∈ seq, i ∈ inputs) → seq.length ≤ n → P (run step s0 seq) = true :=
  fun seq hseq hlen => pruned_spec step inputs P keep hdrop n [s0] h s0 (by simp) seq hseq hlen

end Smbrta.Cert

namespace Smbrta.Cert

/-! ## Searches where each state has its own successors

`succ s` lists the states one step from `s` (the inputs allowed in `s` may depend on it).
`Reach succ s n t`: `t` is reached from `s` in `n` steps. -/

inductive Reach {σ : Type} (succ : σ → List σ) : σ → Nat → σ → Prop
  | refl (s : σ) : Reach succ s 0 s
  | step {s t u : σ} {n : Nat} : t ∈ succ s → Reach succ t n u → Reach succ s (n + 1) u

theorem Reach.zero {σ : Type} {succ : σ → List σ} {s u : σ} (h : Reach succ s 0 u) : u = s := by
  cases h; rfl

theorem Reach.split {σ : Type} {succ : σ → List σ} :
    ∀ {s u : σ} (a b : Nat), Reach succ s (a + b) u → ∃ y, Reach succ s a y ∧ Reach succ y b u
  | s, u, 0, b, h => ⟨s, .refl s, by simpa using h⟩
  | s, u, a + 1, b, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega] at h
    cases h with
    | step ht hr =>
      obtain ⟨y, h1, h2⟩ := Reach.split a b hr
      exact ⟨y, .step ht h1, h2⟩

variable {σ : Type} [DecidableEq σ] [Hashable σ] [LawfulHashable σ]

def nextS (succ : σ → List σ) (L : List σ) : List σ :=
  (Std.HashSet.ofList (L.flatMap succ)).toList

theorem mem_nextS (succ : σ → List σ) (L : List σ) {s t : σ} (hs : s ∈ L) (ht : t ∈ succ s) :
    t ∈ nextS succ L := by
  unfold nextS
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList, List.contains_iff_mem]
  exact List.mem_flatMap.2 ⟨s, hs, ht⟩

/-- `P` on every kept state of the layers `0..r`; `keep r s`: follow `s` with `r` steps left -/
def checkPrunedS (succ : σ → List σ) (P : σ → Bool) (keep : Nat → σ → Bool) : Nat → List σ → Bool
  | 0, L => L.all P
  | r + 1, L => L.all P && checkPrunedS succ P keep r ((nextS succ L).filter (keep r))

theorem prunedS_spec (succ : σ → List σ) (P : σ → Bool) (keep : Nat → σ → Bool)
    (hdrop : ∀ r s, keep r s = false → ∀ m u, m ≤ r → Reach succ s m u → P u = true) :
    ∀ (r : Nat) (L : List σ), checkPrunedS succ P keep r L = true →
      ∀ s ∈ L, ∀ m u, m ≤ r → Reach succ s m u → P u = true
  | 0, L, h, s, hs, m, u, hm, hr => by
    have : m = 0 := by omega
    subst this
    rw [hr.zero]
    simp only [checkPrunedS, List.all_eq_true] at h
    exact h s hs
  | r + 1, L, h, s, hs, m, u, hm, hr => by
    simp only [checkPrunedS, Bool.and_eq_true, List.all_eq_true] at h
    cases hr with
    | refl => exact h.1 s hs
    | @step _ t _ m' ht hrest =>
      have htn : t ∈ nextS succ L := mem_nextS succ L hs ht
      by_cases hk : keep r t = true
      · exact prunedS_spec succ P keep hdrop r _ h.2 t (List.mem_filter.2 ⟨htn, hk⟩) m' u (by omega) hrest
      · exact hdrop r t (by simpa using hk) m' u (by omega) hrest

end Smbrta.Cert
