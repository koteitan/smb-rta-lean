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
