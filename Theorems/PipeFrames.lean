import Theorems.PipeEntry
import Theorems.SurfaceFrames

/-!
# Up to the vertical pipe: the frames read from the machines

`PipeEntry.no_entry_by` assumed that the frames after frame `N` follow each other (`next`) and that the speed at the end of frame `N` is at most the top
speed (`speed`). Here the frames are read from the machines, as `SurfaceFrames.Reads` does above ground: `fm t` is the machine when frame `t` begins, and
frame `t` begins with its speed, subspeed and position. Before the entry frame `E` it ends with those of `fm (t + 1)`. Frame 0 ends at control, so `fm 1`
is the machine at control, and frame 0 is not read.

* `next_of_reads`: the frames from 1 to `E` follow each other, by the definition.
* `speed_of_reads`: with the speed 0 at control, every frame from 1 to `E` begins and ends with at most the top speed (`TopSpeed.Frame.bound`).
* `no_entry_of_reads`: the bound of `no_entry_by` from these, with no `next` and no `speed`. Its conclusion is `T < E`.

No game data. Page: `1-1/a-5-5-PipeFrames.md`.
-/

namespace Smbrta.PipeFrames

open TopSpeed (Frame)
open PoleGrab (Next)
open SurfaceFrames (vOf fOf)

variable {sy : Syms} {top amax : Int}

/-- **The frames are read from the machines.** Frame `t` begins with the speed, subspeed and position of `fm t`, from frame 1 to the entry frame `E`.
Before `E` it ends with those of `fm (t + 1)`. -/
structure Reads (sy : Syms) (E : Nat) (fm : Nat → Machine) (fr : Nat → Frame top amax) : Prop where
  v : ∀ t, 1 ≤ t → t ≤ E → (fr t).v = vOf sy (fm t)
  f : ∀ t, 1 ≤ t → t ≤ E → (fr t).f = fOf sy (fm t)
  P : ∀ t, 1 ≤ t → t ≤ E → (fr t).P = posP sy (fm t)
  v' : ∀ t, 1 ≤ t → t < E → (fr t).v' = vOf sy (fm (t + 1))
  f' : ∀ t, 1 ≤ t → t < E → (fr t).f' = fOf sy (fm (t + 1))
  P' : ∀ t, 1 ≤ t → t < E → (fr t).P' = posP sy (fm (t + 1))

variable {E : Nat} {fm : Nat → Machine} {fr : Nat → Frame top amax}

/-- The frames follow each other by the definition: both ends are read from the same machine. -/
theorem next_of_reads (R : Reads sy E fm fr) : ∀ t, 1 ≤ t → t < E → Next (fr t) (fr (t + 1)) := by
  intro t h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [R.v (t + 1) (by omega) (by omega), R.v' t h1 h2]
  · rw [R.f (t + 1) (by omega) (by omega), R.f' t h1 h2]
  · rw [R.P (t + 1) (by omega) (by omega), R.P' t h1 h2]

/-- With the speed 0 at control, each frame from 1 to `E` begins with at most the top speed. -/
theorem speed_of_reads (h16 : 16 ≤ top) (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0) :
    ∀ n, n + 1 ≤ E → -top ≤ (fr (n + 1)).v ∧ (fr (n + 1)).v ≤ top
  | 0, h => by
    rw [R.v 1 (by omega) h, h0]
    omega
  | n + 1, h => by
    have ih := speed_of_reads h16 R h0 n (by omega)
    have h1 := ((fr (n + 1)).bound h16 ih).1
    have h2 := (next_of_reads R (n + 1) (by omega) (by omega)).1
    rw [h2]
    exact h1

/-- and ends with at most the top speed: the field `speed` of the old `Route.Pipe`, at any frame from 1 to `E` -/
theorem speed_end (h16 : 16 ≤ top) (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0) (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ E) :
    -top ≤ (fr t).v' ∧ (fr t).v' ≤ top := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  exact ((fr (n + 1)).bound h16 (speed_of_reads h16 R h0 n h2)).1

/-- after frame `N`, each frame up to `E` moves at most `16·top`: the end of frame `N + k` is at most `B + 16·top·k` -/
theorem end_le (h16 : 16 ≤ top) (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0) {N : Nat} {B : Int} (hN : 1 ≤ N)
    (hB : (fr N).P' ≤ B) : ∀ k : Nat, N + k < E → (fr (N + k)).P' ≤ B + 16 * top * (k : Int)
  | 0, _ => by simp only [Nat.add_zero, Int.natCast_zero, Int.mul_zero, Int.add_zero]; exact hB
  | k + 1, h => by
    have ih := end_le h16 R h0 hN hB k (by omega)
    have hv := speed_of_reads h16 R h0 (N + k) (by omega)
    have hb := ((fr (N + k + 1)).bound h16 hv).2
    have hn := (next_of_reads R (N + k) (by omega) (by omega)).2.2
    rw [show N + (k + 1) = N + k + 1 by omega]
    have e : 16 * top * ((k + 1 : Nat) : Int) = 16 * top * (k : Int) + 16 * top := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [e]
    omega

/-- **No entry by frame `T`, from the frames read from the machines.** Up to frame `N` the position is at most `B`. The frames from 1 to the entry frame `E`
are read from the machines, and the speed at control is 0. If that leaves him left of `L` at frame `T`, and entering needs `L`, the entry is after `T`. -/
theorem no_entry_of_reads (h16 : 16 ≤ top) (Enter : Nat → Prop) (L B : Int) (N T : Nat) (hN : 1 ≤ N)
    (hrule : ∀ t, Enter t → L ≤ (fr t).P₂)
    (hopen : ∀ t, t ≤ N → (fr t).P₂ ≤ B)
    (hB : (fr N).P' ≤ B)
    (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0)
    (hgap : B + 16 * top * ((T - N : Nat) : Int) < L)
    (hE : Enter E) : T < E := by
  have hc : 0 ≤ 16 * top := by omega
  have hL := hrule E hE
  refine Nat.lt_of_not_le fun hET => ?_
  by_cases hEN : E ≤ N
  · have h1 := hopen E hEN
    have h2 : 0 ≤ 16 * top * ((T - N : Nat) : Int) := Int.mul_nonneg hc (by omega)
    omega
  · obtain ⟨k, hk⟩ : ∃ k, E = N + k + 1 := ⟨E - N - 1, by omega⟩
    have h1 := end_le h16 R h0 hN hB k (by omega)
    have hv := speed_of_reads h16 R h0 (N + k) (by omega)
    have h2 := PipeEntry.p2_le (fr (N + k + 1)) hv
    have hn := (next_of_reads R (N + k) (by omega) (by omega)).2.2
    have h3 : 16 * top * ((k : Int) + 1) ≤ 16 * top * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hc
    rw [← hk] at h2 hn
    rw [Int.mul_add, Int.mul_one] at h3
    omega

end Smbrta.PipeFrames
