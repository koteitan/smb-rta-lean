import Theorems.PipeEntry
import Theorems.SurfaceFrames
import Theorems.LagFrames

/-!
# Up to the vertical pipe: the frames read from the machines

`PipeEntry.no_entry_by` assumed that the frames after frame `N` follow each other (`next`) and that the speed at the end of frame `N` is at most the top
speed (`speed`). Here the frames are read from the machines, as `SurfaceFrames.Reads` does above ground: `fm t` is the machine when frame `t` begins, and
frame `t` begins with its speed, subspeed and position. Before the entry frame `E` it ends with those of `fm (t + 1)`. Frame 0 ends at control, so `fm 1`
is the machine at control, and frame 0 is not read.

* `next_of_reads`: the frames from 1 to `E` follow each other, by the definition.
* `speed_of_reads`: with the speed 0 at control, every frame from 1 to `E` begins and ends with at most the top speed (`TopSpeed.Frame.bound`).
* `no_entry_of_reads`: the bound of `no_entry_by` from these, with no `next` and no `speed`. Its conclusion is `T < E`.
* `reads_of_lags`: `Reads` from `ReadsOwn` (each counted frame ends at its own machine) and `Lags` (the frames not counted between them, which keep the three values:
  `lags_keep`, by `LagFrames.keeps_frame` for a frame that does not call the mode's routine).

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

/-! ## The frames not counted

`Reads` reads the end of frame `t` from the machine of the next counted frame, `fm (t + 1)`. Between the two there may be frames not counted (`lag`). Here each counted frame
ends at its own machine, `frame (fm t) (inp t)`, and the frames not counted are a sequence of real frames between. They keep the three values: by `LagFrames.keeps_frame`
when they do not call the routine of the mode (a paused frame), and by assumption (`Lags.game`) when they do (the master timer control). -/

open PipeTransition (frame)
open PipeEntryRule (trace)

/-- the speed, the subspeed and the position of `m'` are those of `m` -/
def Same3 (sy : Syms) (m m' : Machine) : Prop := vOf sy m' = vOf sy m ∧ fOf sy m' = fOf sy m ∧ posP sy m' = posP sy m

theorem Same3.trans {a b c : Machine} (h1 : Same3 sy a b) (h2 : Same3 sy b c) : Same3 sy a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem same3_of_bytes {m m' : Machine} (h : ∀ b ∈ LagFrames.vfpI sy, m'.ram.get! b = m.ram.get! b) : Same3 sy m m' := by
  have e1 : peek m' sy.Player_X_Speed = peek m sy.Player_X_Speed := h (LagFrames.I sy.Player_X_Speed) (List.Mem.head _)
  have e2 : peek m' sy.Player_X_MoveForce = peek m sy.Player_X_MoveForce := h (LagFrames.I sy.Player_X_MoveForce) (List.Mem.tail _ (List.Mem.head _))
  have e3 : peek m' sy.Player_PageLoc = peek m sy.Player_PageLoc := h (LagFrames.I sy.Player_PageLoc) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have e4 : peek m' sy.Player_X_Position = peek m sy.Player_X_Position :=
    h (LagFrames.I sy.Player_X_Position) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e5 : peek m' sy.SprObject_X_MoveForce = peek m sy.SprObject_X_MoveForce :=
    h (LagFrames.I sy.SprObject_X_MoveForce) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  refine ⟨?_, ?_, ?_⟩
  · unfold vOf
    rw [e1]
  · unfold fOf
    rw [e2]
  · unfold posP
    rw [e3, e4, e5]

/-- **The counted frames, read from their own machines.** Frame `t` begins with the speed, subspeed and position of `fm t`, from frame 1 to the entry frame `E`.
Before `E` it ends with those of its own end, `frame (fm t) (inp t)`. -/
structure ReadsOwn (sy : Syms) (E : Nat) (fm : Nat → Machine) (inp : Nat → UInt8) (fr : Nat → Frame top amax) : Prop where
  v : ∀ t, 1 ≤ t → t ≤ E → (fr t).v = vOf sy (fm t)
  f : ∀ t, 1 ≤ t → t ≤ E → (fr t).f = fOf sy (fm t)
  P : ∀ t, 1 ≤ t → t ≤ E → (fr t).P = posP sy (fm t)
  v' : ∀ t, 1 ≤ t → t < E → (fr t).v' = vOf sy (frame (fm t) (inp t))
  f' : ∀ t, 1 ≤ t → t < E → (fr t).f' = fOf sy (frame (fm t) (inp t))
  P' : ∀ t, 1 ≤ t → t < E → (fr t).P' = posP sy (frame (fm t) (inp t))

/-- **The frames, with the frames not counted.** `seq n` is the machine when frame `n` of the run begins, every frame counted, and `sin n` is its input. The counted
frame `t` is the frame `ix t`; the frames between two counted frames are not counted. Each of these starts in the idle loop, each of its instructions before the call of the
mode's routine is `Clean`, and if it calls
the routine of the mode it keeps the three values. -/
structure Lags (sy : Syms) (m0 : Machine) (E : Nat) (fm : Nat → Machine) (inp : Nat → UInt8) where
  seq : Nat → Machine
  sin : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (sin n)
  ix : Nat → Nat
  fm_ix : ∀ t, 1 ≤ t → t ≤ E → seq (ix t) = fm t
  inp_ix : ∀ t, 1 ≤ t → t ≤ E → sin (ix t) = inp t
  order : ∀ t, 1 ≤ t → t < E → ix t < ix (t + 1)
  /-- a frame not counted starts in the idle loop -/
  start : ∀ t n, 1 ≤ t → t < E → ix t < n → n < ix (t + 1) → PipeWrites.FrameStart (LagFrames.lagGuard sy m0) (PipeEntryRule.envOf m0) (seq n)
  /-- each of its instructions before the call of the mode's routine is `Clean` -/
  clean : ∀ t n, 1 ≤ t → t < E → ix t < n → n < ix (t + 1) → ∀ k, (trace (seq n) (sin n) k).frame = (seq n).frame →
    (∀ j, j ≤ k → (trace (seq n) (sin n) j).pc ≠ LagFrames.modeCall sy) → PipeWrites.Clean (LagFrames.lagGuard sy m0) (trace (seq n) (sin n) k)
  /-- if it calls the routine of the mode, it keeps the speed, the subspeed and the position -/
  game : ∀ t n, 1 ≤ t → t < E → ix t < n → n < ix (t + 1) →
    (∃ k, (trace (seq n) (sin n) k).frame = (seq n).frame ∧ (trace (seq n) (sin n) k).pc = LagFrames.modeCall sy) → Same3 sy (seq n) (seq (n + 1))

variable {m0 : Machine} {inp : Nat → UInt8}

/-- **The frames not counted keep the three values**: from the end of frame `t` to the start of frame `t + 1`. `hc` is the check on the ROM. -/
theorem lags_keep (hc : LagFrames.lagCheck sy m0 = true) (L : Lags sy m0 E fm inp) (t : Nat) (h1 : 1 ≤ t) (h2 : t < E) :
    Same3 sy (frame (fm t) (inp t)) (fm (t + 1)) := by
  have e0 : frame (fm t) (inp t) = L.seq (L.ix t + 1) := by
    rw [L.next, L.fm_ix t h1 (by omega), L.inp_ix t h1 (by omega)]
  have e1 : fm (t + 1) = L.seq (L.ix (t + 1)) := (L.fm_ix (t + 1) (by omega) (by omega)).symm
  rw [e0, e1]
  have ho := L.order t h1 h2
  have key : ∀ d, L.ix t + 1 + d ≤ L.ix (t + 1) → Same3 sy (L.seq (L.ix t + 1)) (L.seq (L.ix t + 1 + d)) := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨rfl, rfl, rfl⟩
    | succ d ih =>
      intro hd
      refine (ih (by omega)).trans ?_
      have hn1 : L.ix t < L.ix t + 1 + d := by omega
      have hn2 : L.ix t + 1 + d < L.ix (t + 1) := by omega
      rw [show L.ix t + 1 + (d + 1) = (L.ix t + 1 + d) + 1 by omega, L.next (L.ix t + 1 + d)]
      rcases LagFrames.keeps_frame hc (L.start t _ h1 h2 hn1 hn2) (L.clean t _ h1 h2 hn1 hn2) with hx | hx
      · have := L.game t _ h1 h2 hn1 hn2 hx
        rw [L.next] at this
        exact this
      · exact same3_of_bytes hx
  have := key (L.ix (t + 1) - (L.ix t + 1)) (by omega)
  rw [show L.ix t + 1 + (L.ix (t + 1) - (L.ix t + 1)) = L.ix (t + 1) by omega] at this
  exact this

/-- **`Reads` from the frames read from their own machines and the frames not counted.** -/
theorem reads_of_lags (hc : LagFrames.lagCheck sy m0 = true) (R : ReadsOwn sy E fm inp fr) (L : Lags sy m0 E fm inp) : Reads sy E fm fr where
  v := R.v
  f := R.f
  P := R.P
  v' := fun t h1 h2 => (R.v' t h1 h2).trans (lags_keep hc L t h1 h2).1.symm
  f' := fun t h1 h2 => (R.f' t h1 h2).trans (lags_keep hc L t h1 h2).2.1.symm
  P' := fun t h1 h2 => (R.P' t h1 h2).trans (lags_keep hc L t h1 h2).2.2.symm

end Smbrta.PipeFrames
