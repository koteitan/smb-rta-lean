import Theorems.PipeEntry
import Theorems.SurfaceFrames
import Theorems.LagFrames
import Theorems.StartRun
import Theorems.LagPause

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
  `lags_keep`, by `LagFrames.keeps_frame`, since a frame not counted ends paused and so does not call the mode's routine: `Lags.no_call`, by `LagPause`).
* `Lags.starts`: every frame from control to the entry starts in the idle loop in control, by induction from the machine at control (`StartRun.starts_clean_dep`). So the start
  of a frame not counted (`Lags.lagStart`) and of the entering frame (`Lags.startE`) are theorems. A counted frame ends in control by `Lags.ctl`; a frame not counted
  ends in control by the check of `LagFrames` (`Lags.known_end`).

No game data. Pages: `1-1/a-5-5-PipeFrames.md`, `1-1/a-5-5-3-2-StartRun.md`.
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

variable {E : Nat} {fr : Nat → Frame top amax}

section Read
variable {fm : Nat → Machine}

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

/-- from control, each frame up to `E` moves at most `16·top`: frame `1 + k` begins at most `16·top·k` right of frame 1 -/
theorem pos_le (h16 : 16 ≤ top) (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0) : ∀ k : Nat, 1 + k ≤ E → (fr (1 + k)).P ≤ (fr 1).P + 16 * top * (k : Int)
  | 0, _ => by simp
  | k + 1, h => by
    have ih := pos_le h16 R h0 k (by omega)
    have hv := speed_of_reads h16 R h0 k (by omega)
    rw [show k + 1 = 1 + k by omega] at hv
    have hb := ((fr (1 + k)).bound h16 hv).2
    have hn := (next_of_reads R (1 + k) (by omega) (by omega)).2.2
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, hn]
    have e : 16 * top * ((k + 1 : Nat) : Int) = 16 * top * (k : Int) + 16 * top := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rw [e]
    omega

/-- **No entry by frame `T`, with a bound on the position only at control and at the end of frame `N`.** The position at control is at most `B` (`hP1`), the speed there is 0, and
each frame moves at most `16·top`: so an entry at frame `E ≤ N` would be at most `B + 16·top·N`, which is not more than `B + 16·top·(T − N)` when `2·N ≤ T`. After `N` it is
the argument of `no_entry_of_reads`, with the bound at the end of frame `N` (`hB`), needed only when `N < E`. This takes the place of the bound on every frame up to `N` (`hopen`). -/
theorem no_entry_of_start (h16 : 16 ≤ top) (Enter : Nat → Prop) (L B : Int) (N T : Nat) (hN : 1 ≤ N) (h2N : 2 * N ≤ T)
    (hrule : ∀ t, Enter t → L ≤ (fr t).P₂)
    (hP1 : (fr 1).P ≤ B)
    (hB : N < E → (fr N).P' ≤ B)
    (R : Reads sy E fm fr) (h0 : vOf sy (fm 1) = 0)
    (hgap : B + 16 * top * ((T - N : Nat) : Int) < L)
    (hE : Enter E) (hE1 : 1 ≤ E) : T < E := by
  have hc : 0 ≤ 16 * top := by omega
  by_cases hEN : E ≤ N
  · exfalso
    have hL := hrule E hE
    obtain ⟨k, rfl⟩ : ∃ k, E = 1 + k := ⟨E - 1, by omega⟩
    have h1 := pos_le h16 R h0 k (Nat.le_refl _)
    have hv := speed_of_reads h16 R h0 k (by omega)
    rw [show k + 1 = 1 + k by omega] at hv
    have h2 := PipeEntry.p2_le (fr (1 + k)) hv
    have h3 : 16 * top * ((k : Int) + 1) ≤ 16 * top * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hc
    rw [Int.mul_add, Int.mul_one] at h3
    omega
  · refine Nat.lt_of_not_le fun hET => ?_
    have hL := hrule E hE
    obtain ⟨k, hk⟩ : ∃ k, E = N + k + 1 := ⟨E - N - 1, by omega⟩
    have h1 := end_le h16 R h0 hN (hB (by omega)) k (by omega)
    have hv := speed_of_reads h16 R h0 (N + k) (by omega)
    have h2 := PipeEntry.p2_le (fr (N + k + 1)) hv
    have hn := (next_of_reads R (N + k) (by omega) (by omega)).2.2
    have h3 : 16 * top * ((k : Int) + 1) ≤ 16 * top * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hc
    rw [← hk] at h2 hn
    rw [Int.mul_add, Int.mul_one] at h3
    omega

end Read

/-! ## The frames not counted

`Reads` reads the end of frame `t` from the machine of the next counted frame, `fm (t + 1)`. Between the two there may be frames not counted (`lag`). Here each counted frame
ends at its own machine, `frame (fm t) (inp t)`, and the frames not counted are a sequence of real frames between. Which frames are counted is read from the machines
(`ixP`): a counted frame is a frame that ends with the game not paused, and the frames between two counted frames end paused (`Lags.paused`, by the definition). The counted
frame 1 is the first frame from frame 1 on that ends not paused; the frames before it end paused too. A frame not counted keeps the bytes of `LagFrames.lagI` by
`LagFrames.keeps_frame`: it ends paused, so it does not call the routine of the mode (`LagPause.no_call_of_paused`, under `Lags.keeps`). `keeps_frame` needs that
the frame starts in the idle loop in control and that its instructions before the call are `Clean`: the start follows by induction from frame 1 (`Lags.starts`, by
`StartRun.starts_clean_dep`), since every frame from frame 1 to the entry ends in control and each of its instructions is `Clean` (`Lags.clean`). A counted frame ends in
control by `Lags.ctl`, a frame not counted by `LagFrames.keeps_frame`: it keeps the routine, the mode and the task. -/

open PipeTransition (frame)
open PipeEntryRule (trace)
open PipeWrites (FrameStart Clean guardOf)

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

/-! ### Where the counted frames are -/

/-- the first `j` from `t` on with `p j`, looking at `d` of them; `t + d` if there is none -/
def landFrom (p : Nat → Bool) : Nat → Nat → Nat
  | t, 0 => t
  | t, d + 1 => if p t then t else landFrom p (t + 1) d

theorem landFrom_ge (p : Nat → Bool) : ∀ t d, t ≤ landFrom p t d
  | _, 0 => Nat.le_refl _
  | t, d + 1 => by
    unfold landFrom
    split
    · exact Nat.le_refl _
    · have := landFrom_ge p (t + 1) d
      omega

theorem landFrom_self {p : Nat → Bool} {t : Nat} (h : p t = true) : ∀ d, landFrom p t d = t
  | 0 => rfl
  | _ + 1 => by simp [landFrom, h]

theorem landFrom_succ {p : Nat → Bool} {t : Nat} (h : p t = false) (d : Nat) : landFrom p t (d + 1) = landFrom p (t + 1) d := by
  simp [landFrom, h]

/-- before the first `j`, `p` is false -/
theorem landFrom_lt (p : Nat → Bool) : ∀ t d j, t ≤ j → j < landFrom p t d → p j = false
  | t, 0, j, h1, h2 => by simp only [landFrom] at h2; omega
  | t, d + 1, j, h1, h2 => by
    by_cases h : p t = true
    · rw [landFrom_self h] at h2; omega
    · have hf : p t = false := by simpa using h
      rw [landFrom_succ hf] at h2
      by_cases e : j = t
      · rw [e]; exact hf
      · exact landFrom_lt p (t + 1) d j (by omega) h2

/-- if the first `j` is found before `t + d`, `p j` holds -/
theorem landFrom_found (p : Nat → Bool) : ∀ t d, landFrom p t d < t + d → p (landFrom p t d) = true
  | t, 0, h => by simp only [landFrom] at h; omega
  | t, d + 1, h => by
    by_cases hp : p t = true
    · rw [landFrom_self hp]; exact hp
    · have hf : p t = false := by simpa using hp
      rw [landFrom_succ hf] at h ⊢
      exact landFrom_found p (t + 1) d (by omega)

/-- the first `j` is `t + n`, when `p` is false before it and `n ≤ d` -/
theorem landFrom_at {p : Nat → Bool} : ∀ (n t d : Nat), (∀ j, t ≤ j → j < t + n → p j = false) → p (t + n) = true → n ≤ d → landFrom p t d = t + n
  | 0, t, d, _, h, _ => by rw [Nat.add_zero] at h ⊢; exact landFrom_self h d
  | n + 1, t, d, hf, h, hn => by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [landFrom_succ (hf t (Nat.le_refl _) (by omega))]
    rw [show t + (n + 1) = t + 1 + n by omega] at h ⊢
    exact landFrom_at n (t + 1) d' (fun j h1 h2 => hf j (by omega) (by omega)) h (by omega)

/-- frame `n` of the run ends with the game not paused: the low bit of the pause byte `g` is 0 when it ends -/
def unpB (g : Nat) (S : FrameKeep.RealRun) (n : Nat) : Bool := (S.seq (n + 1)).ram.get! g &&& 1 == 0

/-- **Where the counted frames are.** The counted frame `t` of the pipe is the frame `ixP g S d t` of the run. The counted frame `t + 1` is the first frame after the
counted frame `t` that ends with the game not paused, looking at `d` frames; the counted frame 0 is frame 0, so the counted frame 1 is the first frame from frame 1 on that
ends not paused. A definition: the counted frames come in order (`ixP_lt`), and the frames between two of them end paused (`ixP_paused`). -/
def ixP (g : Nat) (S : FrameKeep.RealRun) (d : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => landFrom (unpB g S) (ixP g S d t + 1) d

theorem ixP_lt (g : Nat) (S : FrameKeep.RealRun) (d : Nat) (t : Nat) : ixP g S d t < ixP g S d (t + 1) := by
  show ixP g S d t < landFrom (unpB g S) (ixP g S d t + 1) d
  have := landFrom_ge (unpB g S) (ixP g S d t + 1) d
  omega

theorem and1_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 1 = 0 ∨ UInt8.ofNat n.val &&& 1 = 1 := by decide +kernel

theorem and1_of_ne {x : UInt8} (h : ¬ (x &&& 1 = 0)) : x &&& 1 = 1 := by
  have := and1_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  rcases this with e | e
  · exact absurd e h
  · exact e

/-- **A frame between two counted frames ends paused**: by the definition of `ixP` -/
theorem ixP_paused (g : Nat) (S : FrameKeep.RealRun) (d : Nat) {t n : Nat} (h1 : ixP g S d t < n) (h2 : n < ixP g S d (t + 1)) :
    (S.seq (n + 1)).ram.get! g &&& 1 = 1 := by
  have hf := landFrom_lt (unpB g S) (ixP g S d t + 1) d n (by omega) h2
  simp only [unpB, beq_eq_false_iff_ne, ne_eq] at hf
  exact and1_of_ne hf

/-- **The frames, with the frames not counted.** They are the frames of the real run `S`: `S.seq n` is the machine when frame `n` of the run begins, every frame counted,
and `S.inp n` is its input. The counted frame `t` is the frame `ixP g S dP t`, read from the machines (a frame that ends not paused); `dP` is how many frames the search for the
next counted frame looks at, longer than every pause before the entry (`resume`). Each counted frame from control to the entry (`ixP g S dP E`) ends in control, and each
instruction of each frame from frame 1 to the entry,
counted or not, is `Clean`. None of the instructions of a frame not counted writes the pause byte through an index or a pointer. That a frame not counted ends paused is not a
field: it holds by the definition of `ixP` (`Lags.paused`). That each frame starts in the idle loop is not a field: it follows from frame 1 (`Lags.starts`). That a frame not
counted does not call the routine of the mode is not a field: it ends paused (`LagPause.no_call_of_paused`, `Lags.no_call`). So it keeps the bytes of the walk and ends in
control, by the check of `LagFrames` (`lags_keepI`, `Lags.known_end`). -/
structure Lags (sy : Syms) (m0 : Machine) (g : Nat) (S : FrameKeep.RealRun) (E : Nat) where
  /-- how many frames the search for the next counted frame looks at -/
  dP : Nat
  /-- each counted frame from control to the entry ends in control -/
  ctl : ∀ t, 1 ≤ t → t < E → controllable sy (S.seq (ixP g S dP t + 1)) = true
  /-- each counted frame up to the entry comes within `dP` frames of the one before (frame 0): no pause from frame 1 to the entry lasts `dP` frames. A run takes `dP` larger
  than its pauses -/
  resume : ∀ t, t < E → ixP g S dP (t + 1) < ixP g S dP t + 1 + dP
  /-- each instruction of each frame from frame 1 to the entry, counted or not, is `Clean` -/
  clean : ∀ n, 1 ≤ n → n < ixP g S dP E → ∀ k, Clean (guardOf sy m0) (trace (S.seq n) (S.inp n) k)
  /-- no instruction of a frame not counted writes the pause byte through an index or a pointer -/
  keeps : ∀ t n, t < E → ixP g S dP t < n → n < ixP g S dP (t + 1) → ∀ k, LagPause.KeepsPause g (trace (S.seq n) (S.inp n) k)

variable {m0 : Machine} {g : Nat} {S : FrameKeep.RealRun}

/-- the frame of the run where the counted frame `t` begins -/
abbrev Lags.ix (L : Lags sy m0 g S E) (t : Nat) : Nat := ixP g S L.dP t

/-- the machine when the counted frame `t` begins: frame `ix t` of the run -/
abbrev Lags.fm (L : Lags sy m0 g S E) (t : Nat) : Machine := S.seq (L.ix t)

/-- the input of the counted frame `t` -/
abbrev Lags.inp (L : Lags sy m0 g S E) (t : Nat) : UInt8 := S.inp (L.ix t)

/-- the machine of the counted frame 0 is frame 0 of the run -/
theorem Lags.fm_zero (L : Lags sy m0 g S E) : L.fm 0 = S.seq 0 ∧ L.inp 0 = S.inp 0 := ⟨rfl, rfl⟩

/-- the counted frames are in order -/
theorem Lags.ix_le (L : Lags sy m0 g S E) (t : Nat) : ∀ d, L.ix t ≤ L.ix (t + d)
  | 0 => Nat.le_refl _
  | d + 1 => by
    have g1 := L.ix_le t d
    have g2 : L.ix (t + d) < L.ix (t + d + 1) := ixP_lt g S L.dP (t + d)
    show L.ix t ≤ L.ix (t + d + 1)
    omega

theorem Lags.ix_mono (L : Lags sy m0 g S E) {a b : Nat} (h : a ≤ b) : L.ix a ≤ L.ix b := by
  have := L.ix_le a (b - a)
  rwa [show a + (b - a) = b by omega] at this

/-- the counted frame 1 is not before frame 1 -/
theorem Lags.one_le_ix (L : Lags sy m0 g S E) {t : Nat} (h : 1 ≤ t) : 1 ≤ L.ix t := by
  have a : L.ix 0 < L.ix 1 := ixP_lt g S L.dP 0
  have b := L.ix_mono h
  have c : L.ix 0 = 0 := rfl
  omega

/-- **A frame not counted ends paused**: the low bit of the pause byte is 1 when it ends (the old field `lags.paused`, by the definition of `ixP`) -/
theorem Lags.paused (L : Lags sy m0 g S E) {t n : Nat} (hn1 : L.ix t < n) (hn2 : n < L.ix (t + 1)) : (S.seq (n + 1)).ram.get! g &&& 1 = 1 :=
  ixP_paused g S L.dP hn1 hn2

/-- **A counted frame up to the entry ends not paused**: the low bit of the pause byte is 0 when it ends. By the definition of `ixP`: the search finds the frame within `dP`
frames (`resume`). -/
theorem Lags.unpaused (L : Lags sy m0 g S E) {t : Nat} (h1 : 1 ≤ t) (h2 : t ≤ E) : (S.seq (L.ix t + 1)).ram.get! g &&& 1 = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hr := L.resume s (by omega)
  have hf := landFrom_found (unpB g S) (ixP g S L.dP s + 1) L.dP hr
  simpa [unpB] using hf

/-- a frame not counted lies between frame 1 and the entry -/
theorem Lags.between (L : Lags sy m0 g S E) {t n : Nat} (ht2 : t < E) (hn1 : L.ix t < n) (hn2 : n < L.ix (t + 1)) : 1 ≤ n ∧ n < L.ix E := by
  have g2 := L.ix_mono (show t + 1 ≤ E by omega)
  omega

/-- each frame from frame 1 to the entry is counted, or lies between two counted frames -/
theorem Lags.cases (L : Lags sy m0 g S E) : ∀ d, d ≤ E → ∀ n, 1 ≤ n → n < L.ix d →
    (∃ t, 1 ≤ t ∧ t < E ∧ L.ix t = n) ∨ ∃ t, t < E ∧ L.ix t < n ∧ n < L.ix (t + 1)
  | 0, _, n, h1, h2 => absurd h2 (by show ¬ n < 0; omega)
  | d + 1, hd, n, h1, h2 => by
    by_cases h3 : n < L.ix d
    · exact L.cases d (by omega) n h1 h3
    · by_cases h4 : L.ix d = n
      · by_cases h5 : d = 0
        · subst h5
          exact absurd h4 (by show ¬ (0 = n); omega)
        · exact Or.inl ⟨d, by omega, by omega, h4⟩
      · exact Or.inr ⟨d, by omega, by omega, h2⟩

/-- **A frame not counted does not call the routine of the mode**: it ends paused (`LagPause.no_call_of_paused`). `hp` is the check on the ROM, `hs` the start of the frame. -/
theorem Lags.no_call (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E) {t n : Nat} (ht2 : t < E) (hn1 : L.ix t < n)
    (hn2 : n < L.ix (t + 1)) (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq n)) :
    ¬ ∃ k, (trace (S.seq n) (S.inp n) k).frame = (S.seq n).frame ∧ (trace (S.seq n) (S.inp n) k).pc = LagFrames.modeCall sy := by
  obtain ⟨g1, g2⟩ := L.between ht2 hn1 hn2
  have he := L.paused hn1 hn2
  rw [S.next] at he
  exact LagPause.no_call_of_paused hp hs (L.clean n g1 g2) (L.keeps t n ht2 hn1 hn2) he

/-- **Each frame from frame 1 to the entry that starts in the idle loop in control ends in control**: a counted frame by `ctl`, and a frame not counted by the check
of `LagFrames`, since it does not call the mode's routine (`Lags.no_call`) -/
theorem Lags.known_end (hc : LagFrames.lagCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E) {n : Nat}
    (h1 : 1 ≤ n) (h2 : n < L.ix E)
    (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq n)) : ∀ p ∈ (guardOf sy m0).known, (S.seq (n + 1)).ram.get! p.1 = p.2 := by
  rcases L.cases E (Nat.le_refl _) n h1 h2 with ⟨t, ht1, ht2, rfl⟩ | ⟨t, ht2, hn1, hn2⟩
  · exact StartRun.known_ctl (L.ctl t ht1 ht2)
  · rcases LagFrames.keeps_frame hc hs (fun k _ _ => L.clean n h1 h2 k) with hx | hx
    · exact absurd hx (L.no_call hp ht2 hn1 hn2 hs)
    · rw [S.next]
      exact LagFrames.known_of_keep hs hx

/-- **Each frame from frame 1 to the entry starts in the idle loop in control**, from frame 1, the machine at control: by induction (`StartRun.starts_clean_dep`), with
`clean` and `known_end`. `hc` and `hk` are the checks on the ROM. -/
theorem Lags.starts (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (h1 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) :
    ∀ n, 1 ≤ n → n ≤ L.ix E → FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq n) :=
  StartRun.starts_clean_dep (S := StartRun.noSpot) hk rfl S.next h1 L.clean
    (fun _ a b hs => L.known_end hc hp a b hs)

/-- **A frame not counted starts in the idle loop in control**: from `Lags.starts` -/
theorem Lags.lagStart (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (h1 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1))
    {t n : Nat} (ht2 : t < E) (hn1 : L.ix t < n) (hn2 : n < L.ix (t + 1)) :
    FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq n) := by
  obtain ⟨g1, g2⟩ := L.between ht2 hn1 hn2
  exact L.starts hc hk hp h1 n g1 (by omega)

/-- **A counted frame from control to the entry starts in the idle loop in control**: from `Lags.starts` -/
theorem Lags.startAt (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (h1 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) {t : Nat} (ht1 : 1 ≤ t) (ht2 : t ≤ E) :
    FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (L.fm t) :=
  L.starts hc hk hp h1 (L.ix t) (L.one_le_ix ht1) (L.ix_mono ht2)

/-- **The frames not counted keep the bytes of the walk** (`LagFrames.lagI`): from the end of the counted frame `t` (frame `ix t + 1`) to the start of the counted
frame `t + 1`; for `t = 0`, from frame 1 to the counted frame 1. `hc` and `hk` are checks on the ROM, `hs` the start of frame 1. -/
theorem lags_keep0 (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (t : Nat) (h2 : t < E) :
    ∀ b ∈ LagFrames.lagI sy, (S.seq (L.ix (t + 1))).ram.get! b = (S.seq (L.ix t + 1)).ram.get! b := by
  have ho : L.ix t < L.ix (t + 1) := ixP_lt g S L.dP t
  have key : ∀ d, L.ix t + 1 + d ≤ L.ix (t + 1) → ∀ b ∈ LagFrames.lagI sy,
      (S.seq (L.ix t + 1 + d)).ram.get! b = (S.seq (L.ix t + 1)).ram.get! b := by
    intro d
    induction d with
    | zero => exact fun _ _ _ => rfl
    | succ d ih =>
      intro hd b hb
      have hn1 : L.ix t < L.ix t + 1 + d := by omega
      have hn2 : L.ix t + 1 + d < L.ix (t + 1) := by omega
      rw [show L.ix t + 1 + (d + 1) = (L.ix t + 1 + d) + 1 by omega, S.next (L.ix t + 1 + d)]
      obtain ⟨g1, g2⟩ := L.between h2 hn1 hn2
      have hst := L.lagStart hc hk hp hs h2 hn1 hn2
      rcases LagFrames.keeps_frame hc hst (fun k _ _ => L.clean _ g1 g2 k) with hx | hx
      · exact absurd hx (L.no_call hp h2 hn1 hn2 hst)
      · rw [hx b hb]
        exact ih (by omega) b hb
  have := key (L.ix (t + 1) - (L.ix t + 1)) (by omega)
  rw [show L.ix t + 1 + (L.ix (t + 1) - (L.ix t + 1)) = L.ix (t + 1) by omega] at this
  exact this

/-- **The frames not counted keep the bytes of the walk**: from the end of the counted frame `t` to the start of the counted frame `t + 1` -/
theorem lags_keepI (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (t : Nat) (h2 : t < E) :
    ∀ b ∈ LagFrames.lagI sy, (L.fm (t + 1)).ram.get! b = (frame (L.fm t) (L.inp t)).ram.get! b := by
  have e0 : frame (L.fm t) (L.inp t) = S.seq (L.ix t + 1) := (S.next _).symm
  rw [e0]
  exact lags_keep0 hc hk hp L hs t h2

/-- **The frames not counted keep the three values**: from the end of frame `t` to the start of frame `t + 1`. `hc` and `hk` are checks on the ROM, `hs` the start of
frame 1. -/
theorem lags_keep (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E)
    (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) (t : Nat) (h2 : t < E) :
    Same3 sy (frame (L.fm t) (L.inp t)) (L.fm (t + 1)) :=
  same3_of_bytes fun b hb => lags_keepI hc hk hp L hs t h2 b (List.mem_append_left _ (List.mem_append_left _ hb))

/-- **`Reads` from the frames read from their own machines and the frames not counted.** -/
theorem reads_of_lags (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E) (R : ReadsOwn sy E L.fm L.inp fr)
    (hs : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) : Reads sy E L.fm fr where
  v := R.v
  f := R.f
  P := R.P
  v' := fun t _ h2 => (R.v' t (by omega) h2).trans (lags_keep hc hk hp L hs t h2).1.symm
  f' := fun t _ h2 => (R.f' t (by omega) h2).trans (lags_keep hc hk hp L hs t h2).2.1.symm
  P' := fun t _ h2 => (R.P' t (by omega) h2).trans (lags_keep hc hk hp L hs t h2).2.2.symm

/-- **The entering frame starts in the idle loop in control**: the old field `start` of `Route.Pipe`, from `Lags.starts` -/
theorem Lags.startE (hc : LagFrames.lagCheck sy m0 = true) (hk : StartRun.walkCheck sy m0 = true) (hp : LagPause.pauseCheck sy m0 g = true) (L : Lags sy m0 g S E) (hE : 1 ≤ E)
    (h1 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (S.seq 1)) : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) (L.fm E) :=
  L.startAt hc hk hp h1 hE (Nat.le_refl _)

end Smbrta.PipeFrames
