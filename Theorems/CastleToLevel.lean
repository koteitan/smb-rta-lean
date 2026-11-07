import Theorems.CastleWalk
import Theorems.PipeTransitionAll

/-!
# From the castle entry to the level change

Two parts. The arithmetic part has no machine in it: from the lengths of the parts of a run, the game timer's rule, the 21-frame grid and a lower bound on the
level change's frame, it concludes that the level does not change before frame 1748 (`level_ge`). `Frames` states the timer's rule and the grid on single frames, and proves from them the
facts about the whole run that `level_ge` takes. The check part runs real frames, on a castle entry reached by the route of `CastleWalk`, and compares them with the rules that the arithmetic
part takes as hypotheses. The checks cover the listed states only. Page: `1-1/g-1-CastleToLevel.md`.

Values of the game do not appear here: the timer's period `q`, its first value `t0` and the names read from the disassembly are parameters.
-/

namespace Smbrta.CastleToLevel

open PipeTransition (frame run zeros gchain GMerge no_input_of_chain first_control zero_mem_inputs witness)
open PipeTransitionAll (Names asmValue)
open CastleWalk (castle beside beforeGrab touchAt firstX bigFrac route)

/-! ## The level change as a formula -/

/-- `(c − n) mod 21`, in natural numbers -/
def wait (c n : Nat) : Nat := (c + 20 * n) % 21

theorem wait_lt (c n : Nat) : wait c n < 21 := by unfold wait; omega

theorem wait_spec (c n : Nat) : (wait c n + n) % 21 = c % 21 := by unfold wait; omega

/-- the frames from the castle entry to the level change: the timer `T`, the flag and fireworks `D`, the delay to the first grid point after them -/
def formula (c T D : Nat) : Nat := T + D + 107 + wait c (T + D)

/-- `D`: 33, or more by the timer's last digit. Fireworks are the digits 1, 3, 6. -/
def fireD (T : Nat) : Nat :=
  match T % 10 with
  | 1 => 34
  | 3 => 98
  | 6 => 194
  | _ => 33

theorem fireD_ge (T : Nat) : 33 ≤ fireD T := by
  unfold fireD
  split <;> omega

/-- the level change comes at the first grid point not before the sum: the wait is below 21, and the grid point is fixed by `c + E` -/
theorem level_next (c E T D : Nat) :
    E + T + D + 107 ≤ E + formula c T D ∧ E + formula c T D < E + T + D + 107 + 21 ∧
      (E + formula c T D) % 21 = (c + E + 107) % 21 := by
  have h1 := wait_lt c (T + D)
  have h2 := wait_spec c (T + D)
  unfold formula
  omega

/-- with the same grid, a later sum never gives an earlier level change. Fireworks and later arrivals are cases of this. -/
theorem level_mono {c c' E E' S S' : Nat} (hc : (c + E) % 21 = (c' + E') % 21) (hES : E + S ≤ E' + S') :
    E + S + wait c S ≤ E' + S' + wait c' S' := by
  have h1 := wait_lt c S
  have h2 := wait_lt c' S'
  have h3 := wait_spec c S
  have h4 := wait_spec c' S'
  omega

/-! ## The game timer -/

/-- `⌈p / q⌉`: the ticks in `p` frames of play, when the sub-counter starts at 0 -/
def ticks (q p : Nat) : Nat := (p + q - 1) / q

theorem ticks_zero {q : Nat} (hq : 1 ≤ q) : ticks q 0 = 0 := by
  unfold ticks
  exact Nat.div_eq_of_lt (by omega)

theorem ticks_mono {q p p' : Nat} (h : p ≤ p') : ticks q p ≤ ticks q p' :=
  Nat.div_le_div_right (by omega)

theorem ticks_succ_le {q : Nat} (hq : 1 ≤ q) (p : Nat) : ticks q (p + 1) ≤ ticks q p + 1 := by
  unfold ticks
  have h : p + 1 + q - 1 = p + q := by omega
  rw [h, Nat.add_div_right _ (by omega : 0 < q)]
  have : p / q ≤ (p + q - 1) / q := Nat.div_le_div_right (by omega)
  exact Nat.succ_le_succ this

theorem ticks_le_self {q : Nat} (hq : 1 ≤ q) : ∀ p, ticks q p ≤ p
  | 0 => by rw [ticks_zero hq]; omega
  | p + 1 => by
    have h1 := ticks_le_self hq p
    have h2 := ticks_succ_le hq p
    omega

/-- one more frame of play costs one frame and gains at most one tick -/
theorem sub_ticks_mono {q : Nat} (hq : 1 ≤ q) {p p' : Nat} (h : p ≤ p') : p - ticks q p ≤ p' - ticks q p' := by
  induction p' with
  | zero =>
    have : p = 0 := by omega
    subst this
    omega
  | succ n ih =>
    by_cases hp : p = n + 1
    · subst hp; omega
    · have h1 := ih (by omega)
      have h2 := ticks_succ_le hq n
      have h3 := ticks_le_self hq n
      omega

/-- the timer's digits and its sub-counter -/
structure TS where
  t : Nat
  sub : Nat
  deriving Repr, DecidableEq

/-- a frame of play: the sub-counter falls; at 0 the timer falls and the sub-counter is set to `q` -/
def playStep (q : Nat) (s : TS) : TS :=
  if s.sub - 1 = 0 then ⟨s.t - 1, q⟩ else ⟨s.t, s.sub - 1⟩

/-- `n` frames of play -/
def playN (q : Nat) : Nat → TS → TS
  | 0, s => s
  | n + 1, s => playStep q (playN q n s)

theorem div_of_form {q k r : Nat} (hq : 1 ≤ q) (hr : r < q) : (k * q + r) / q = k := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < q), Nat.div_eq_of_lt hr]
  omega

/-- after `p ≥ 1` frames of play from sub-counter 0: `k` ticks, and the sub-counter says where in the period he is -/
theorem playN_inv {q : Nat} (hq : 1 ≤ q) (t : Nat) (p : Nat) :
    ∃ k, (playN q (p + 1) ⟨t, 0⟩).sub + (p + 1) = k * q + 1 ∧ 1 ≤ (playN q (p + 1) ⟨t, 0⟩).sub ∧
      (playN q (p + 1) ⟨t, 0⟩).sub ≤ q ∧ (playN q (p + 1) ⟨t, 0⟩).t = t - k := by
  induction p with
  | zero =>
    refine ⟨1, ?_⟩
    simp [playN, playStep]
    omega
  | succ n ih =>
    obtain ⟨k, h1, h2, h3, h4⟩ := ih
    rw [show n + 1 + 1 = (n + 1) + 1 from rfl]
    simp only [playN] at h1 h2 h3 h4 ⊢
    generalize hs : playStep q (playN q n ⟨t, 0⟩) = s at h1 h2 h3 h4 ⊢
    by_cases hz : s.sub - 1 = 0
    · refine ⟨k + 1, ?_⟩
      simp only [playStep, hz, if_true]
      rw [Nat.succ_mul]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · refine ⟨k, ?_⟩
      simp only [playStep, hz, if_false]
      refine ⟨by omega, by omega, by omega, h4⟩

/-- the rule in one line: `p` frames of play from sub-counter 0 take `⌈p / q⌉` off the timer -/
theorem playN_t {q : Nat} (hq : 1 ≤ q) (t p : Nat) : (playN q p ⟨t, 0⟩).t = t - ticks q p := by
  cases p with
  | zero =>
    rw [ticks_zero hq]
    rfl
  | succ n =>
    obtain ⟨k, h1, h2, h3, h4⟩ := playN_inv hq t n
    rw [h4]
    have : ticks q (n + 1) = k := by
      unfold ticks
      generalize hs : (playN q (n + 1) ⟨t, 0⟩).sub = s at h1 h2 h3
      have hk : 1 ≤ k := by
        rcases k with _ | k
        · simp at h1; omega
        · omega
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.succ_mul] at h1
      have e2 : n + 1 + q - 1 = (j + 1) * q + (q - s) := by
        rw [Nat.succ_mul]
        omega
      rw [e2, div_of_form hq (by omega)]
    rw [this]

/-- three stretches of play, each starting at sub-counter 0, with the timer unchanged between them, satisfy the hypothesis `hT` of `level_ge` -/
theorem timer_of_rule {q t0 P1 P2 P3 T : Nat} (hq : 1 ≤ q)
    (hT : T = (playN q P3 ⟨(playN q P2 ⟨(playN q P1 ⟨t0, 0⟩).t, 0⟩).t, 0⟩).t) :
    t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3) := by
  rw [hT, playN_t hq, playN_t hq, playN_t hq]
  omega

/-! ## The sum: arriving later does not make it smaller -/

/-- the sum `E + T` does not fall when a stretch of play gets longer -/
theorem sum_mono {q t0 P1 P1' P2 P2' P3 P3' : Nat} (hq : 1 ≤ q) (h1 : P1 ≤ P1') (h2 : P2 ≤ P2') (h3 : P3 ≤ P3')
    (ht : ticks q P1' + ticks q P2' + ticks q P3' ≤ t0) :
    P1 + P2 + P3 + (t0 - (ticks q P1 + ticks q P2 + ticks q P3)) ≤
      P1' + P2' + P3' + (t0 - (ticks q P1' + ticks q P2' + ticks q P3')) := by
  have a1 := sub_ticks_mono hq h1
  have a2 := sub_ticks_mono hq h2
  have a3 := sub_ticks_mono hq h3
  have b1 := ticks_le_self hq P1
  have b2 := ticks_le_self hq P2
  have b3 := ticks_le_self hq P3
  have c1 := ticks_le_self hq P1'
  have c2 := ticks_le_self hq P2'
  have c3 := ticks_le_self hq P3'
  have d1 := ticks_mono (q := q) h1
  have d2 := ticks_mono (q := q) h2
  have d3 := ticks_mono (q := q) h3
  omega

/-- two more frames of play tick the timer at most once more, when its period is at least two frames -/
theorem ticks_add_two_le {q : Nat} (hq : 2 ≤ q) (p : Nat) : ticks q (p + 2) ≤ ticks q p + 1 := by
  unfold ticks
  have h1 : (p + 2 + q - 1) / q ≤ (p + q - 1 + q) / q := Nat.div_le_div_right (by omega)
  have h2 : (p + q - 1 + q) / q = (p + q - 1) / q + 1 := Nat.add_div_right _ (by omega)
  omega

/-- the bound on the sum, in all the cases of the touch: another touch with its longer delay; a direct grab on the frame of the TAS or the next one with the delay of the TAS;
a later direct grab with one frame less. The last is not smaller, because from `P3 = 241` on, two more frames tick the timer at most once more. -/
theorem sum_ge {q t0 P1 X1 P2 X2 P3 W E T j : Nat} (hq : 2 ≤ q)
    (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hP1 : 368 ≤ P1) (hX1 : 91 ≤ X1) (hP2 : 111 ≤ P2) (hX2 : 282 ≤ X2)
    (hP3 : (234 ≤ P3 ∧ 132 ≤ W) ∨ (240 ≤ P3 ∧ P3 ≤ 241 ∧ 126 ≤ W) ∨ (242 ≤ P3 ∧ 125 ≤ W))
    (hE : E = P1 + X1 + P2 + X2 + P3 + W + j)
    (hT : t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3)) :
    1588 + j ≤ E + T := by
  have hq1 : 1 ≤ q := by omega
  have a1 := sub_ticks_mono hq1 hP1
  have a2 := sub_ticks_mono hq1 hP2
  have b1 := ticks_le_self hq1 368
  have b2 := ticks_le_self hq1 111
  have b3 := ticks_le_self hq1 240
  have c1 := ticks_le_self hq1 P1
  have c2 := ticks_le_self hq1 P2
  have c3 := ticks_le_self hq1 P3
  rcases hP3 with ⟨h3, hW⟩ | ⟨h3, _, hW⟩ | ⟨h3, hW⟩
  · have a3 := sub_ticks_mono hq1 h3
    have d := ticks_mono (q := q) (show 234 ≤ 240 by omega)
    have e := ticks_le_self hq1 234
    omega
  · have a3 := sub_ticks_mono hq1 h3
    omega
  · have a3 := sub_ticks_mono hq1 h3
    have d : ticks q 242 ≤ ticks q 240 + 1 := ticks_add_two_le hq 240
    have e := ticks_le_self hq1 242
    omega

/-! ## The theorem -/

/-- from the sum and the grid: `S ≥ 1728 + j`, the grid passes through `1748 + j`, and the first grid point not before `S` is not before `1748 + j` -/
theorem level_ge_of_sum {E T D L c j : Nat} (hS : 1588 + j ≤ E + T) (hD : 33 ≤ D)
    (hc : (c + E) % 21 = (3 + j) % 21)
    (hL : E + T + D + 107 + wait c (T + D) ≤ L) : 1748 + j ≤ L := by
  have h1 := wait_lt c (T + D)
  have h2 := wait_spec c (T + D)
  omega

/-- **The level does not change before frame 1748.** `P1`, `P2`, `P3`: frames of play in each area, `X1`, `X2`: the two changes of area, `W`: touch to castle,
`j`: frames on which no timer runs (other than one in each change). The conclusion is `1748 + j`. -/
theorem level_ge {q t0 P1 X1 P2 X2 P3 W E T D L c j : Nat} (hq : 2 ≤ q)
    (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hP1 : 368 ≤ P1) (hX1 : 91 ≤ X1) (hP2 : 111 ≤ P2) (hX2 : 282 ≤ X2)
    (hP3 : (234 ≤ P3 ∧ 132 ≤ W) ∨ (240 ≤ P3 ∧ P3 ≤ 241 ∧ 126 ≤ W) ∨ (242 ≤ P3 ∧ 125 ≤ W))
    (hE : E = P1 + X1 + P2 + X2 + P3 + W + j)
    (hT : t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3))
    (hD : 33 ≤ D)
    (hc : (c + E) % 21 = (3 + j) % 21)
    (hL : E + T + D + 107 + wait c (T + D) ≤ L) : 1748 + j ≤ L :=
  level_ge_of_sum (sum_ge hq ht0 hP1 hX1 hP2 hX2 hP3 hE hT) hD hc hL

/-- a run `F ≥ 20` frames later than the sum's bound needs no grid: `L ≥ S` is enough. A power-up freezes more frames than that. -/
theorem level_ge_of_late {q t0 P1 X1 P2 X2 P3 W E T D L c F : Nat} (hq : 2 ≤ q)
    (ht0 : t0 = 370 + ticks q 368 + ticks q 111 + ticks q 240)
    (hP1 : 368 ≤ P1) (hX1 : 91 ≤ X1) (hP2 : 111 ≤ P2) (hX2 : 282 ≤ X2)
    (hP3 : (234 ≤ P3 ∧ 132 ≤ W) ∨ (240 ≤ P3 ∧ P3 ≤ 241 ∧ 126 ≤ W) ∨ (242 ≤ P3 ∧ 125 ≤ W))
    (hE : E = P1 + X1 + P2 + X2 + P3 + W + F) (hF : 20 ≤ F)
    (hT : t0 ≤ T + (ticks q P1 + ticks q P2 + ticks q P3))
    (hD : 33 ≤ D)
    (hL : E + T + D + 107 + wait c (T + D) ≤ L) : 1748 ≤ L := by
  have h := sum_ge hq ht0 hP1 hX1 hP2 hX2 hP3 hE hT
  omega

/-! ## The frames of a run

One sequence of frames. Every frame has a number, counting all frames from the first controllable frame of 1-1, a kind, and the counters. The rule is on one frame at a time (`Step`, `Segs.kind`).
The three facts that `level_ge` takes about the whole run follow from it: `Frames.hE`, `Frames.hT`, `Frames.hc`. -/

/-- what a frame does -/
inductive Kind where
  /-- a frame of play -/
  | play
  /-- the timers run and the play routine does not: a frame of a change, or a frame after the touch -/
  | auto
  /-- the one frame of a change on which the timers do not run -/
  | setup
  /-- any other frame on which the timers do not run: the frames of `j` -/
  | lag
  deriving DecidableEq, Repr

/-- the rule of one frame, from the counters before it (`a`, `p`) to the counters after it (`b`, `p'`). A frame of play follows `playStep`. On an `auto` frame the digits stay and the
sub-counter falls, down to 0. The phase falls by 1 modulo 21 on the frames on which the timers run. -/
def Step (q : Nat) : Kind → TS → TS → Nat → Nat → Prop
  | .play, a, b, p, p' => b = playStep q a ∧ p' = (p + 20) % 21
  | .auto, a, b, p, p' => b.t = a.t ∧ b.sub ≤ a.sub - 1 ∧ p' = (p + 20) % 21
  | .setup, a, b, p, p' => b.t = a.t ∧ b.sub ≤ a.sub ∧ p' = p
  | .lag, a, b, p, p' => b = a ∧ p' = p

instance (q : Nat) (k : Kind) (a b : TS) (p p' : Nat) : Decidable (Step q k a b p p') := by
  cases k <;> unfold Step <;> exact inferInstance

/-- where the segments of a run end, in frames counted without the `lag` frames: play up to `e₁`, a change up to `c₂` with its `setup` frame `z₁`, play up to `e₂`, a change up to `c₃`
with its `setup` frame `z₂`, play up to the touch `g`, and `auto` frames up to the castle entry `last` -/
structure Segs where
  e₁ : Nat
  z₁ : Nat
  c₂ : Nat
  e₂ : Nat
  z₂ : Nat
  c₃ : Nat
  g : Nat
  last : Nat

/-- the kind of the frame with this count, when it is not a `lag` frame -/
def Segs.kind (S : Segs) (r : Nat) : Kind :=
  if r < S.e₁ then .play
  else if r < S.c₂ then (if r = S.z₁ then .setup else .auto)
  else if r < S.e₂ then .play
  else if r < S.c₃ then (if r = S.z₂ then .setup else .auto)
  else if r < S.g then .play
  else .auto

/-- the segments are in order, and a change is longer than the timer's period -/
structure Segs.Ok (q : Nat) (S : Segs) : Prop where
  z₁_ge : S.e₁ ≤ S.z₁
  z₁_lt : S.z₁ < S.c₂
  len₁ : S.e₁ + q < S.c₂
  c₂_le : S.c₂ ≤ S.e₂
  z₂_ge : S.e₂ ≤ S.z₂
  z₂_lt : S.z₂ < S.c₃
  len₂ : S.e₂ + q < S.c₃
  c₃_le : S.c₃ ≤ S.g
  g_le : S.g ≤ S.last

/-- the frames before `n` of the kind `x` -/
def count (k : Nat → Kind) (x : Kind) : Nat → Nat
  | 0 => 0
  | n + 1 => count k x n + if k n = x then 1 else 0

/-- the frames before `n` that are not `lag` frames -/
def seen (k : Nat → Kind) : Nat → Nat
  | 0 => 0
  | n + 1 => seen k n + if k n = .lag then 0 else 1

/-- the frames of a run up to its castle entry, frame `E`. `s n` and `ph n` are the counters when frame `n` begins, so `n + 1` holds what frame `n` leaves. A frame's values are those at the end of
its routine. On a frame that runs over, that end comes after the next frame has begun, and the next frame is the `lag` frame. -/
structure Frames (q t0 E : Nat) (S : Segs) where
  kind : Nat → Kind
  s : Nat → TS
  ph : Nat → Nat
  /-- before frame 0 -/
  s_zero : s 0 = ⟨t0, 0⟩
  ph_zero : ph 0 = 2
  /-- each frame follows its kind -/
  step : ∀ n, n ≤ E → Step q (kind n) (s n) (s (n + 1)) (ph n) (ph (n + 1))
  /-- each frame is a `lag` frame or has the kind of its place -/
  plan : ∀ n, n ≤ E → kind n = .lag ∨ kind n = S.kind (seen kind n)
  /-- the castle entry is the frame with the count `last` that runs -/
  runs_E : kind E ≠ .lag
  seen_E : seen kind E = S.last

theorem seen_add_lag (k : Nat → Kind) : ∀ n, seen k n + count k .lag n = n
  | 0 => rfl
  | n + 1 => by
    have h := seen_add_lag k n
    by_cases hk : k n = .lag <;> simp [seen, count, hk] <;> omega

theorem seen_mono (k : Nat → Kind) {a b : Nat} (h : a ≤ b) : seen k a ≤ seen k b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    omega
  | succ n ih =>
    by_cases ha : a = n + 1
    · subst ha; omega
    · have h1 := ih (by omega)
      simp only [seen]
      omega

/-- the first frame with a count, for any count reached -/
theorem first_at (k : Nat → Kind) (r : Nat) : ∀ n, r ≤ seen k n →
    ∃ a, a ≤ n ∧ seen k a = r ∧ ∀ i, i < a → seen k i < r
  | 0, h => by
    have h0 : r = 0 := by simpa [seen] using h
    subst h0
    exact ⟨0, by omega, rfl, fun i hi => by omega⟩
  | n + 1, h => by
    by_cases hr : r ≤ seen k n
    · obtain ⟨a, ha, h1, h2⟩ := first_at k r n hr
      exact ⟨a, by omega, h1, h2⟩
    · have hle : seen k (n + 1) ≤ seen k n + 1 := by
        simp only [seen]
        split <;> omega
      refine ⟨n + 1, by omega, by omega, fun i hi => ?_⟩
      have := seen_mono k (show i ≤ n by omega)
      omega

theorem Segs.kind_ne_lag (S : Segs) (r : Nat) : S.kind r ≠ .lag := by
  unfold Segs.kind
  repeat' split
  all_goals exact fun h => Kind.noConfusion h

theorem Segs.kind_setup {q : Nat} {S : Segs} (hS : S.Ok q) (r : Nat) : S.kind r = .setup ↔ r = S.z₁ ∨ r = S.z₂ := by
  have h1 := hS.z₁_ge
  have h2 := hS.z₁_lt
  have h3 := hS.c₂_le
  have h4 := hS.z₂_ge
  have h5 := hS.z₂_lt
  unfold Segs.kind
  repeat' split
  all_goals first
    | exact ⟨fun _ => by omega, fun _ => rfl⟩
    | exact ⟨fun h => Kind.noConfusion h, fun _ => by omega⟩

theorem Segs.kind_play₁ {S : Segs} {r : Nat} (h : r < S.e₁) : S.kind r = .play := by
  unfold Segs.kind
  rw [if_pos h]

theorem Segs.kind_change₁ {S : Segs} {r : Nat} (h1 : S.e₁ ≤ r) (h2 : r < S.c₂) : S.kind r ≠ .play := by
  unfold Segs.kind
  rw [if_neg (by omega), if_pos h2]
  split <;> exact fun h => Kind.noConfusion h

theorem Segs.kind_play₂ {q : Nat} {S : Segs} (hS : S.Ok q) {r : Nat} (h1 : S.c₂ ≤ r) (h2 : r < S.e₂) : S.kind r = .play := by
  have := hS.z₁_ge
  have := hS.z₁_lt
  unfold Segs.kind
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem Segs.kind_change₂ {q : Nat} {S : Segs} (hS : S.Ok q) {r : Nat} (h1 : S.e₂ ≤ r) (h2 : r < S.c₃) : S.kind r ≠ .play := by
  have := hS.z₁_ge
  have := hS.z₁_lt
  have := hS.c₂_le
  unfold Segs.kind
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
  split <;> exact fun h => Kind.noConfusion h

theorem Segs.kind_play₃ {q : Nat} {S : Segs} (hS : S.Ok q) {r : Nat} (h1 : S.c₃ ≤ r) (h2 : r < S.g) : S.kind r = .play := by
  have := hS.z₁_ge
  have := hS.z₁_lt
  have := hS.c₂_le
  have := hS.z₂_ge
  have := hS.z₂_lt
  unfold Segs.kind
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem Segs.kind_after {q : Nat} {S : Segs} (hS : S.Ok q) {r : Nat} (h : S.g ≤ r) : S.kind r = .auto := by
  have := hS.z₁_ge
  have := hS.z₁_lt
  have := hS.c₂_le
  have := hS.z₂_ge
  have := hS.z₂_lt
  have := hS.c₃_le
  unfold Segs.kind
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem playN_sub_le {q : Nat} (hq : 1 ≤ q) (t p : Nat) : (playN q p ⟨t, 0⟩).sub ≤ q := by
  cases p with
  | zero => exact Nat.zero_le _
  | succ n =>
    obtain ⟨k, _, _, h, _⟩ := playN_inv hq t n
    exact h

namespace Frames

variable {q t0 E : Nat} {S : Segs} (F : Frames q t0 E S)

/-- the frames of `j`: up to the castle entry, the frames on which the timers do not run, other than one in each change -/
def j : Nat := count F.kind .lag E

/-- the timer that the castle entry leaves -/
def T : Nat := (F.s (E + 1)).t

/-- the phase that the castle entry leaves -/
def c : Nat := F.ph (E + 1)

/-- a stretch of play and of `lag` frames: `playN` for its frames of play -/
theorem play_stretch (a : Nat) : ∀ d, a + d ≤ E + 1 → (∀ i, a ≤ i → i < a + d → F.kind i = .play ∨ F.kind i = .lag) →
    F.s (a + d) = playN q (seen F.kind (a + d) - seen F.kind a) (F.s a)
  | 0, _, _ => by simp [playN]
  | d + 1, hn, hk => by
    have ih := play_stretch a d (by omega) (fun i h1 h2 => hk i h1 (by omega))
    have hs := F.step (a + d) (by omega)
    have hm := seen_mono F.kind (show a ≤ a + d by omega)
    rw [show a + (d + 1) = a + d + 1 from rfl]
    rcases hk (a + d) (by omega) (by omega) with h | h
    · rw [h] at hs
      have e : seen F.kind (a + d + 1) = seen F.kind (a + d) + 1 := by simp [seen, h]
      rw [e, show seen F.kind (a + d) + 1 - seen F.kind a = (seen F.kind (a + d) - seen F.kind a) + 1 by omega]
      simp only [playN]
      rw [← ih]
      exact hs.1
    · rw [h] at hs
      have e : seen F.kind (a + d + 1) = seen F.kind (a + d) := by simp [seen, h]
      rw [e, ← ih]
      exact hs.1

/-- frames without play: the digits stay, and each frame other than a `setup` or a `lag` frame takes one off the sub-counter, down to 0 -/
theorem change_stretch (a : Nat) : ∀ d, a + d ≤ E + 1 → (∀ i, a ≤ i → i < a + d → F.kind i ≠ .play) →
    (F.s (a + d)).t = (F.s a).t ∧ ((F.s (a + d)).sub = 0 ∨
      (F.s (a + d)).sub + seen F.kind (a + d) + count F.kind .setup a ≤ (F.s a).sub + seen F.kind a + count F.kind .setup (a + d))
  | 0, _, _ => ⟨rfl, Or.inr (by simp only [Nat.add_zero]; omega)⟩
  | d + 1, hn, hk => by
    obtain ⟨ih1, ih2⟩ := change_stretch a d (by omega) (fun i h1 h2 => hk i h1 (by omega))
    have hs := F.step (a + d) (by omega)
    have hp := hk (a + d) (by omega) (by omega)
    rw [show a + (d + 1) = a + d + 1 from rfl]
    generalize hx : F.kind (a + d) = x at hs hp
    cases x with
    | play => exact absurd rfl hp
    | auto =>
      obtain ⟨h1, h2, _⟩ := hs
      have e1 : seen F.kind (a + d + 1) = seen F.kind (a + d) + 1 := by simp [seen, hx]
      have e2 : count F.kind .setup (a + d + 1) = count F.kind .setup (a + d) := by simp [count, hx]
      rw [e1, e2]
      refine ⟨by omega, ?_⟩
      omega
    | setup =>
      obtain ⟨h1, h2, _⟩ := hs
      have e1 : seen F.kind (a + d + 1) = seen F.kind (a + d) + 1 := by simp [seen, hx]
      have e2 : count F.kind .setup (a + d + 1) = count F.kind .setup (a + d) + 1 := by simp [count, hx]
      rw [e1, e2]
      refine ⟨by omega, ?_⟩
      omega
    | lag =>
      obtain ⟨h1, _⟩ := hs
      have e1 : seen F.kind (a + d + 1) = seen F.kind (a + d) := by simp [seen, hx]
      have e2 : count F.kind .setup (a + d + 1) = count F.kind .setup (a + d) := by simp [count, hx]
      rw [e1, e2, h1]
      exact ⟨ih1, ih2⟩

/-- the `setup` frames so far: one when the count has passed `z₁`, one when it has passed `z₂` -/
theorem setups (hS : S.Ok q) : ∀ n, n ≤ E + 1 →
    count F.kind .setup n = (if S.z₁ < seen F.kind n then 1 else 0) + (if S.z₂ < seen F.kind n then 1 else 0)
  | 0, _ => by
    simp [count, seen]
  | n + 1, hn => by
    have ih := setups hS n (by omega)
    have h1 := hS.z₁_lt
    have h2 := hS.c₂_le
    have h3 := hS.z₂_ge
    rcases F.plan n (by omega) with h | h
    · have e1 : seen F.kind (n + 1) = seen F.kind n := by simp [seen, h]
      have e2 : count F.kind .setup (n + 1) = count F.kind .setup n := by simp [count, h]
      rw [e1, e2, ih]
    · have hne : F.kind n ≠ .lag := by rw [h]; exact S.kind_ne_lag _
      have e1 : seen F.kind (n + 1) = seen F.kind n + 1 := by simp [seen, hne]
      rw [e1]
      simp only [count]
      rw [ih]
      by_cases hz : seen F.kind n = S.z₁ ∨ seen F.kind n = S.z₂
      · have hk : F.kind n = .setup := by rw [h]; exact (S.kind_setup hS _).2 hz
        rw [if_pos hk]
        rcases hz with hz | hz
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      · have hk : F.kind n ≠ .setup := by
          rw [h]
          exact fun hh => hz ((S.kind_setup hS _).1 hh)
        rw [if_neg hk]
        have a1 : (S.z₁ < seen F.kind n + 1) = (S.z₁ < seen F.kind n) := propext (by omega)
        have a2 : (S.z₂ < seen F.kind n + 1) = (S.z₂ < seen F.kind n) := propext (by omega)
        simp only [a1, a2, Nat.add_zero]

/-- the phase and the frame number: only the frames on which the timers do not run move their sum -/
theorem phase : ∀ n, n ≤ E + 1 → (F.ph n + n) % 21 = (2 + count F.kind .lag n + count F.kind .setup n) % 21
  | 0, _ => by
    simp [count, F.ph_zero]
  | n + 1, hn => by
    have ih := phase n (by omega)
    have hs := F.step n (by omega)
    generalize hx : F.kind n = x at hs
    have e1 : count F.kind .lag (n + 1) = count F.kind .lag n + if x = .lag then 1 else 0 := by simp [count, hx]
    have e2 : count F.kind .setup (n + 1) = count F.kind .setup n + if x = .setup then 1 else 0 := by simp [count, hx]
    rw [e1, e2]
    cases x with
    | play =>
      have := hs.2
      simp only [reduceCtorEq, if_false]
      omega
    | auto =>
      have := hs.2.2
      simp only [reduceCtorEq, if_false]
      omega
    | setup =>
      have := hs.2.2
      simp only [reduceCtorEq, if_false, if_true]
      omega
    | lag =>
      have := hs.2
      simp only [reduceCtorEq, if_false, if_true]
      omega

/-- **`hE`.** The castle entry's number: the frames of its count, and the frames of `j`. -/
theorem hE : E = S.last + F.j := by
  have h := seen_add_lag F.kind E
  rw [F.seen_E] at h
  unfold j
  omega

/-- the castle entry is an `auto` frame -/
theorem kind_E (hS : S.Ok q) : F.kind E = .auto := by
  rcases F.plan E (by omega) with h | h
  · exact absurd h F.runs_E
  · rw [h, F.seen_E]
    exact S.kind_after hS hS.g_le

/-- **`hc`.** The grid at the castle entry. -/
theorem hc (hS : S.Ok q) : (F.c + E) % 21 = (3 + F.j) % 21 := by
  have hk := F.kind_E hS
  have h1 := F.phase (E + 1) (by omega)
  have h2 := F.setups hS (E + 1) (by omega)
  have hg := hS.g_le
  have hz1 := hS.z₁_lt
  have hc2 := hS.c₂_le
  have hz2 := hS.z₂_lt
  have hc3 := hS.c₃_le
  have hz2' := hS.z₂_ge
  have e1 : seen F.kind (E + 1) = S.last + 1 := by simp [seen, hk, F.seen_E]
  have e2 : count F.kind .lag (E + 1) = F.j := by simp [count, hk, j]
  rw [e1, if_pos (by omega), if_pos (by omega)] at h2
  rw [e2, h2] at h1
  unfold c
  omega

/-- the first frame of a segment, and the count on the frames before it -/
theorem seg {a b r r' : Nat} (ha : seen F.kind a = r) (hb : ∀ i, i < b → seen F.kind i < r') {i : Nat} (h1 : a ≤ i) (h2 : i < b) :
    r ≤ seen F.kind i ∧ seen F.kind i < r' :=
  ⟨ha ▸ seen_mono F.kind h1, hb i h2⟩

theorem ts_of_sub_zero {x : TS} (hx : x.sub = 0) : x = ⟨x.t, 0⟩ := by
  cases x
  simp_all

/-- **`hT`.** The timer at the castle entry: each stretch of play takes `⌈p/q⌉`, because each change leaves the sub-counter at 0. -/
theorem hT (hq : 1 ≤ q) (hS : S.Ok q) : t0 ≤ F.T + (ticks q S.e₁ + ticks q (S.e₂ - S.c₂) + ticks q (S.g - S.c₃)) := by
  have o1 := hS.z₁_ge
  have o2 := hS.z₁_lt
  have o3 := hS.c₂_le
  have o4 := hS.z₂_ge
  have o5 := hS.z₂_lt
  have o6 := hS.c₃_le
  have o7 := hS.g_le
  have l1 := hS.len₁
  have l2 := hS.len₂
  have hE' := F.seen_E
  -- the first frame of each segment
  obtain ⟨a₁, ha₁, s₁, f₁⟩ := first_at F.kind S.e₁ E (by omega)
  obtain ⟨a₂, ha₂, s₂, f₂⟩ := first_at F.kind S.c₂ E (by omega)
  obtain ⟨a₃, ha₃, s₃, f₃⟩ := first_at F.kind S.e₂ E (by omega)
  obtain ⟨a₄, ha₄, s₄, f₄⟩ := first_at F.kind S.c₃ E (by omega)
  obtain ⟨a₅, ha₅, s₅, f₅⟩ := first_at F.kind S.g E (by omega)
  have le₁₂ : a₁ ≤ a₂ := Nat.le_of_not_lt fun h => by have := f₁ a₂ h; omega
  have le₂₃ : a₂ ≤ a₃ := Nat.le_of_not_lt fun h => by have := f₂ a₃ h; omega
  have le₃₄ : a₃ ≤ a₄ := Nat.le_of_not_lt fun h => by have := f₃ a₄ h; omega
  have le₄₅ : a₄ ≤ a₅ := Nat.le_of_not_lt fun h => by have := f₄ a₅ h; omega
  -- the setup frames at the ends of the changes
  have c₁ := F.setups hS a₁ (by omega)
  have c₂ := F.setups hS a₂ (by omega)
  have c₃ := F.setups hS a₃ (by omega)
  have c₄ := F.setups hS a₄ (by omega)
  rw [s₁, if_neg (by omega), if_neg (by omega)] at c₁
  rw [s₂, if_pos (by omega), if_neg (by omega)] at c₂
  rw [s₃, if_pos (by omega), if_neg (by omega)] at c₃
  rw [s₄, if_pos (by omega), if_pos (by omega)] at c₄
  -- first stretch
  have p₁ : F.s a₁ = playN q S.e₁ ⟨t0, 0⟩ := by
    have h := F.play_stretch 0 a₁ (by omega) (fun i _ h2 => by
      have hi : i ≤ E := by omega
      have := f₁ i (by omega)
      rcases F.plan i hi with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans (Segs.kind_play₁ this)))
    simp only [Nat.zero_add, seen, Nat.sub_zero, F.s_zero, s₁] at h
    exact h
  have sb₁ : (F.s a₁).sub ≤ q := by rw [p₁]; exact playN_sub_le hq _ _
  -- first change
  obtain ⟨d₂, rfl⟩ : ∃ d, a₂ = a₁ + d := ⟨a₂ - a₁, by omega⟩
  have ch₁ := F.change_stretch a₁ d₂ (by omega) (fun i h1 h2 => by
    have hi := F.seg s₁ f₂ h1 h2
    rcases F.plan i (by omega) with h | h
    · rw [h]; exact fun hh => Kind.noConfusion hh
    · rw [h]; exact Segs.kind_change₁ hi.1 hi.2)
  have z₂ : F.s (a₁ + d₂) = ⟨(F.s a₁).t, 0⟩ := by
    obtain ⟨t1, t2⟩ := ch₁
    have : (F.s (a₁ + d₂)).sub = 0 := by
      rw [s₂, s₁, c₁, c₂] at t2
      omega
    rw [ts_of_sub_zero this, t1]
  -- second stretch
  obtain ⟨d₃, rfl⟩ : ∃ d, a₃ = a₁ + d₂ + d := ⟨a₃ - (a₁ + d₂), by omega⟩
  have p₂ : F.s (a₁ + d₂ + d₃) = playN q (S.e₂ - S.c₂) ⟨(F.s a₁).t, 0⟩ := by
    have h := F.play_stretch (a₁ + d₂) d₃ (by omega) (fun i h1 h2 => by
      have hi := F.seg s₂ f₃ h1 h2
      rcases F.plan i (by omega) with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans (Segs.kind_play₂ hS hi.1 hi.2)))
    rw [s₃, s₂, z₂] at h
    exact h
  have sb₂ : (F.s (a₁ + d₂ + d₃)).sub ≤ q := by rw [p₂]; exact playN_sub_le hq _ _
  -- second change
  obtain ⟨d₄, rfl⟩ : ∃ d, a₄ = a₁ + d₂ + d₃ + d := ⟨a₄ - (a₁ + d₂ + d₃), by omega⟩
  have ch₂ := F.change_stretch (a₁ + d₂ + d₃) d₄ (by omega) (fun i h1 h2 => by
    have hi := F.seg s₃ f₄ h1 h2
    rcases F.plan i (by omega) with h | h
    · rw [h]; exact fun hh => Kind.noConfusion hh
    · rw [h]; exact Segs.kind_change₂ hS hi.1 hi.2)
  have z₄ : F.s (a₁ + d₂ + d₃ + d₄) = ⟨(F.s (a₁ + d₂ + d₃)).t, 0⟩ := by
    obtain ⟨t1, t2⟩ := ch₂
    have : (F.s (a₁ + d₂ + d₃ + d₄)).sub = 0 := by
      rw [s₄, s₃, c₃, c₄] at t2
      omega
    rw [ts_of_sub_zero this, t1]
  -- third stretch
  obtain ⟨d₅, rfl⟩ : ∃ d, a₅ = a₁ + d₂ + d₃ + d₄ + d := ⟨a₅ - (a₁ + d₂ + d₃ + d₄), by omega⟩
  have p₃ : F.s (a₁ + d₂ + d₃ + d₄ + d₅) = playN q (S.g - S.c₃) ⟨(F.s (a₁ + d₂ + d₃)).t, 0⟩ := by
    have h := F.play_stretch (a₁ + d₂ + d₃ + d₄) d₅ (by omega) (fun i h1 h2 => by
      have hi := F.seg s₄ f₅ h1 h2
      rcases F.plan i (by omega) with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans (Segs.kind_play₃ hS hi.1 hi.2)))
    rw [s₅, s₄, z₄] at h
    exact h
  -- after the touch, up to and with the castle entry
  obtain ⟨d₆, hd₆⟩ : ∃ d, E + 1 = a₁ + d₂ + d₃ + d₄ + d₅ + d := ⟨E + 1 - (a₁ + d₂ + d₃ + d₄ + d₅), by omega⟩
  have ch₃ := F.change_stretch (a₁ + d₂ + d₃ + d₄ + d₅) d₆ (by omega) (fun i h1 h2 => by
    have hm := seen_mono F.kind h1
    rcases F.plan i (by omega) with h | h
    · rw [h]; exact fun hh => Kind.noConfusion hh
    · rw [h, Segs.kind_after hS (by omega)]; exact fun hh => Kind.noConfusion hh)
  have hTe : F.T = (playN q (S.g - S.c₃) ⟨(playN q (S.e₂ - S.c₂) ⟨(playN q S.e₁ ⟨t0, 0⟩).t, 0⟩).t, 0⟩).t := by
    unfold T
    rw [hd₆, ch₃.1, p₃, p₂, p₁]
  exact timer_of_rule hq hTe

end Frames

/-! The fields of `Frames` hold together: for any segments there is a sequence with no `lag` frames. -/

/-- one frame on the counters and the phase, the sub-counter falling by exactly 1 on an `auto` frame -/
def Kind.next (q : Nat) : Kind → TS × Nat → TS × Nat
  | .play, x => (playStep q x.1, (x.2 + 20) % 21)
  | .auto, x => (⟨x.1.t, x.1.sub - 1⟩, (x.2 + 20) % 21)
  | .setup, x => x
  | .lag, x => x

/-- the counters of the sequence with no `lag` frames -/
def noLagC (q t0 : Nat) (S : Segs) : Nat → TS × Nat
  | 0 => (⟨t0, 0⟩, 2)
  | n + 1 => Kind.next q (S.kind n) (noLagC q t0 S n)

theorem seen_noLag (S : Segs) : ∀ n, seen S.kind n = n
  | 0 => rfl
  | n + 1 => by
    have h := seen_noLag S n
    simp [seen, h, S.kind_ne_lag]

/-- the sequence with no `lag` frames: its castle entry is the frame `S.last` -/
def Frames.noLag (q t0 : Nat) (S : Segs) : Frames q t0 S.last S where
  kind := S.kind
  s n := (noLagC q t0 S n).1
  ph n := (noLagC q t0 S n).2
  s_zero := rfl
  ph_zero := rfl
  step n _ := by
    simp only [noLagC]
    generalize S.kind n = x
    generalize noLagC q t0 S n = y
    cases x <;> simp [Kind.next, Step]
  plan n _ := Or.inr (by rw [seen_noLag])
  runs_E := S.kind_ne_lag _
  seen_E := seen_noLag S _

/-! ## Real frames: the names and the states -/

/-- the names of the disassembly this file reads -/
def nameList : List String := ["GameTimerDisplay", "GameTimerCtrlTimer", "IntervalTimerControl", "EventMusicBuffer"]

/-- the names above, from the text of the disassembly -/
def namesFrom (text : String) : Names :=
  let ls := text.splitOn "\n"
  nameList.filterMap fun n => (asmValue ls n).map (n, ·)

/-- the level has changed -/
def level (sy : Syms) (m : Machine) : Bool := peek m sy.LevelNumber != 0 || peek m sy.WorldNumber != 0

/-- the value of the timer's three digits -/
def timerOf (nm : Names) (m : Machine) : Nat :=
  let a := nm.ad "GameTimerDisplay"
  100 * (peek m a).toNat + 10 * (peek m (a + 1)).toNat + (peek m (a + 2)).toNat

/-- the three digits overwritten -/
def setTimer (nm : Names) (m : Machine) (t : Nat) : Machine :=
  let a := nm.ad "GameTimerDisplay"
  poke (poke (poke m a (t / 100).toUInt8) (a + 1) (t / 10 % 10).toUInt8) (a + 2) (t % 10).toUInt8

def subOf (nm : Names) (m : Machine) : Nat := (peek m (nm.ad "GameTimerCtrlTimer")).toNat

/-- the interval timer's phase -/
def phaseOf (nm : Names) (m : Machine) : Nat := (peek m (nm.ad "IntervalTimerControl")).toNat

/-- the numbers the checks are told -/
structure Params where
  /-- touch to castle -/
  W : Nat
  /-- the timer's period -/
  q : Nat
  /-- the timer's value before its first tick -/
  t0 : Nat
  /-- the phase at frame 0 -/
  c0 : Nat
  /-- `(c + E) % 21` after the two changes of area -/
  grid : Nat

/-- the castle entry of a run: `b` a machine beside the base block, `t` the timer's value if overwritten. The digits are overwritten on the frame of the touch, so
they are the ones read on the frame of the entry. -/
def entryState (sy : Syms) (nm : Names) (p : Params) (v0 : Jump.VS) (b : Machine) (t : Option Nat) : Machine :=
  let e := touchAt sy b (firstX sy) bigFrac v0
  let e := match t with
    | some t => setTimer nm e t
    | none => e
  run e (zeros p.W)

/-- level change exactly on frame `n` of no input -/
def LevelAt (sy : Syms) (e : Machine) (n : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → level sy (run e (zeros k)) = decide (k = n)

/-- one case, on the machine at a castle entry: the castle has been entered, and the level changes on the frame of the formula -/
def caseOK (sy : Syms) (nm : Names) (e : Machine) : Bool :=
  castle sy e && gchain (level sy) sy [] (fun _ => true) (formula (phaseOf nm e) (timerOf nm e) (fireD (timerOf nm e))) e

/-- what a case gives -/
def CaseProp (sy : Syms) (nm : Names) (e : Machine) : Prop :=
  castle sy e = true ∧ LevelAt sy e (formula (phaseOf nm e) (timerOf nm e) (fireD (timerOf nm e)))

theorem caseProp_of_ok {sy : Syms} {nm : Names} {e : Machine} (h : caseOK sy nm e = true) : CaseProp sy nm e := by
  simp only [caseOK, Bool.and_eq_true] at h
  exact ⟨h.1, no_input_of_chain h.2⟩

/-- the timer's value in the check of all the phases, big enough for the music to have ended -/
def phaseT : Nat := 125

/-- another value of the timer -/
def valuesT : List Nat := [200]

/-- a value with each last digit that gives fireworks -/
def fireT : List Nat := [131, 133, 136]

/-- a touch at another height, the timer overwritten, `n` frames to the castle, from the machine `b` beside the base block -/
def slideState (sy : Syms) (nm : Names) (v0 : Jump.VS) (b : Machine) (t n : Nat) : Machine :=
  let y := (CastleWalk.otherYs sy).headD 0
  run (setTimer nm (touchAt sy b (PoleGrab.colX sy - 9).toUInt8 bigFrac { v0 with y := y + 3 }) t) (zeros n)

/-- frames to the level change with one input held, for the program -/
def framesToLevel (sy : Syms) (e : Machine) (i : UInt8 := 0) (limit : Nat := 2000) : Option Nat := Id.run do
  let mut x := e
  for k in [0:limit] do
    x := frame x i
    if level sy x then return some (k + 1)
  return none

/-- the frame of a castle entry, `d` frames after the route -/
def entryFrame (p : Params) (d : Nat) : Nat := route.length + d + 1 + p.W

/-- the castle entry `d` frames after the route, `t` the timer if overwritten -/
def entryAt (sy : Syms) (nm : Names) (p : Params) (m0 : Machine) (d : Nat) (t : Option Nat) : Machine :=
  entryState sy nm p ((beforeGrab sy m0).headD default) (run (beside m0) (zeros d)) t

/-- the check of the formula: 21 real delays beside the block, with the timer overwritten; the real timer; another value; fireworks. On each delay the grid is
compared too. The real timer also shows that the walk does not change the digits. -/
def formulaCheck (sy : Syms) (nm : Names) (m0 : Machine) (p : Params) (slideN : Nat) : Bool :=
  let b := beside m0
  let v0 := (beforeGrab sy m0).headD default
  (List.range 21).all (fun d =>
    let e := entryState sy nm p v0 (run b (zeros d)) (some phaseT)
    caseOK sy nm e && ((phaseOf nm e + entryFrame p d) % 21 == p.grid % 21)) &&
    (let e := entryState sy nm p v0 (run b (zeros 0)) none
     caseOK sy nm e && (timerOf nm e == timerOf nm b)) &&
    valuesT.all (fun t => caseOK sy nm (entryState sy nm p v0 (run b (zeros 0)) (some t))) &&
    fireT.all (fun t => caseOK sy nm (entryState sy nm p v0 (run b (zeros 0)) (some t))) &&
    caseOK sy nm (slideState sy nm v0 b phaseT slideN)

/-! ## Real frames: every input -/

/-- the state of the check over all inputs: a real castle entry `d` frames later, the timer overwritten, the music stopped, so the chain is short -/
def inputState (sy : Syms) (nm : Names) (p : Params) (m0 : Machine) (d t : Nat) : Machine :=
  poke (setTimer nm (entryAt sy nm p m0 d none) t) (nm.ad "EventMusicBuffer") 0

/-- every input on every frame gives the state of no input, and the level changes on frame `N` -/
def inputCheck (sy : Syms) (nm : Names) (p : Params) (m0 : Machine) (d t N : Nat) : Bool :=
  gchain (level sy) sy PipeTransition.inputs (fun _ => true) N (inputState sy nm p m0 d t)

/-! ## Real frames: the timer and the grid -/

/-- the kind of a real frame from `m` to `m2`, read from the phase and from control. A frame whose phase stays reads as `lag`: on the frames of the checks its rule holds, and it implies the rule of `setup`. -/
def kindOf (sy : Syms) (nm : Names) (m m2 : Machine) : Kind :=
  if phaseOf nm m2 == phaseOf nm m then .lag
  else if controllable sy m2 then .play
  else .auto

/-- the rule `Step` on a real frame from `m` to `m2` -/
def ruleOK (sy : Syms) (nm : Names) (q : Nat) (m m2 : Machine) : Bool :=
  decide (Step q (kindOf sy nm m m2) ⟨timerOf nm m, subOf nm m⟩ ⟨timerOf nm m2, subOf nm m2⟩ (phaseOf nm m) (phaseOf nm m2))

/-- what a run is scanned for -/
structure Scan where
  m : Machine
  ok : Bool
  /-- frames of play in the finished areas -/
  ps : List Nat
  /-- frames of play in the current area, frame 0 counted -/
  cur : Nat
  /-- frames on which the phase did not move -/
  lag : Nat
  /-- frames counted without `lag` frames, frame 0 counted -/
  seen : Nat
  /-- each frame is a `lag` frame or has the kind of its place -/
  planOk : Bool

def scanStep (sy : Syms) (nm : Names) (q : Nat) (S : Segs) (s : Scan) (i : UInt8) : Scan :=
  let y := frame s.m i
  let k := kindOf sy nm s.m y
  let want := S.kind s.seen
  { m := y
    ok := s.ok && ruleOK sy nm q s.m y
    ps := if k == .auto && s.cur != 0 then s.ps ++ [s.cur] else s.ps
    cur := if k == .play then s.cur + 1 else if k == .auto then 0 else s.cur
    lag := s.lag + (if k == .lag then 1 else 0)
    seen := if k == .lag && want != .setup then s.seen else s.seen + 1
    planOk := s.planOk && (k == want || k == .lag) }

def scan (sy : Syms) (nm : Names) (q : Nat) (S : Segs) (m0 : Machine) (w : List UInt8) : Scan :=
  w.foldl (scanStep sy nm q S) ⟨m0, true, [], 1, 0, 1, true⟩

/-- the frames of play in each area -/
def Scan.areas (s : Scan) : List Nat := s.ps ++ (if s.cur != 0 then [s.cur] else [])

/-- `route` with idle frames added: before the first pipe, in the bonus room, above ground -/
def routeWith (d1 d2 d3 : Nat) : List UInt8 :=
  let r2 := witness.length + 91
  let r3 := r2 + 169 + 282
  zeros d1 ++ route.take r2 ++ zeros d2 ++ (route.drop r2).take (r3 - r2) ++ zeros d3 ++ route.drop r3

/-- the segments of a run of this route, from its frames of play. These runs stop before the touch. -/
def segsOf : List Nat → Segs
  | [a, b, c] =>
    let c₂ := a + 91
    let e₂ := c₂ + b
    let c₃ := e₂ + 282
    ⟨a, a + 50, c₂, e₂, e₂ + 162, c₃, c₃ + c, c₃ + c⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- a run: its frames follow the rule and the segments, the timer is `t0` minus `⌈p / q⌉` for each area, each change has one frame without the timers, `j` frames more are without them, and the grid has moved by those frames -/
def runOK (sy : Syms) (nm : Names) (p : Params) (m0 : Machine) (w : List UInt8) (areas : List Nat) (j : Nat) : Bool :=
  let r := scan sy nm p.q (segsOf areas) m0 w
  r.ok && r.planOk && (r.areas == areas) && (timerOf nm r.m + (areas.map (ticks p.q)).sum == p.t0) && (r.lag == 2 + j) &&
    ((phaseOf nm r.m + w.length) % 21 == (p.c0 + r.lag) % 21)

/-- the runs of the check: idle frames in each of the three areas, and the frames of play they give -/
def runsT : List ((Nat × Nat × Nat) × List Nat) :=
  [((0, 0, 0), [440, 169, 316]), ((2, 0, 0), [442, 169, 316]), ((24, 0, 0), [464, 169, 316]),
   ((0, 1, 0), [440, 170, 316]), ((0, 14, 0), [440, 183, 316]), ((0, 0, 23), [440, 169, 339])]

/-- the input Start, in the format of `frame` -/
def startBit : UInt8 := 0x10

/-- a pause: Start with the input at position `f`, `d - 1` frames of nothing, and Start with that input again, on which the game goes on -/
def withPause (f d : Nat) (w : List UInt8) : List UInt8 :=
  let i := w.getD f 0 ||| startBit
  w.take f ++ [i] ++ zeros (d - 1) ++ [i] ++ w.drop (f + 1)

/-- a pause in each of the three stretches and in each of the two changes: the position of the input and the pause's length -/
def pausesT : List (Nat × Nat) := [(99, 45), (459, 46), (599, 47), (799, 48), (1099, 66)]

/-- the first run of `runsT` with the pauses of `pausesT` -/
def pauseRun : List UInt8 := pausesT.foldr (fun x w => withPause x.1 x.2 w) (routeWith 0 0 0)

/-- the frames of the pauses -/
def pauseJ : Nat := (pausesT.map (·.2)).sum

/-- the frames of play of the run with the pauses -/
def pauseAreas : List Nat := [440, 169, 316]

/-- the frames of power-on before the Start press, in the check of frame 0 -/
def startsT : List Nat := [39, 40, 60, 70, 100]

/-- from power-on with Start on frame `kk`, the machine one frame before the first control, and the machine at the first control -/
def startPair (sy : Syms) (cart : Machine) (kk : Nat) : Machine × Machine := Id.run do
  let mut m := powerOn cart 0
  for k in [0:600] do
    let y := runFrame m (if k == kk then 0x08 else 0)
    if k > kk && controllable sy y then return (m, y)
    m := y
  return (m, m)

/-- the machine at the first control -/
def startAt (sy : Syms) (cart : Machine) (kk : Nat) : Machine := (startPair sy cart kk).2

/-- the machine one frame before the first control -/
def beforeStart (sy : Syms) (cart : Machine) (kk : Nat) : Machine := (startPair sy cart kk).1

/-- frame 0 does not depend on the Start press: the phase, the timer and the sub-counter are the same, on frame 0 and before it. The last three are `Frames.s_zero` and `Frames.ph_zero`. -/
def startOK (sy : Syms) (nm : Names) (p : Params) (cart : Machine) (kk : Nat) : Bool :=
  let (b, m) := startPair sy cart kk
  controllable sy m && phaseOf nm m == p.c0 && timerOf nm m + 1 == p.t0 && subOf nm m == p.q &&
    timerOf nm b == p.t0 && subOf nm b == 0 && phaseOf nm b == 2

/-- the check of the timer and the grid -/
def timerCheck (sy : Syms) (nm : Names) (p : Params) (cart m0 : Machine) : Bool :=
  runsT.all (fun r => runOK sy nm p m0 (routeWith r.1.1 r.1.2.1 r.1.2.2) r.2 0) &&
    runOK sy nm p m0 pauseRun pauseAreas pauseJ &&
    startsT.all (startOK sy nm p cart) &&
    (p.c0 + 2) % 21 == p.grid % 21

/-! ## What the checks give -/

/-- what the check of one run gives -/
structure RunProp (sy : Syms) (nm : Names) (p : Params) (m0 : Machine) (w : List UInt8) (areas : List Nat) (j : Nat) : Prop where
  /-- `Step` on every frame -/
  rule : (scan sy nm p.q (segsOf areas) m0 w).ok = true
  /-- `Segs.kind` on every frame that is not a `lag` frame -/
  plan : (scan sy nm p.q (segsOf areas) m0 w).planOk = true
  plays : (scan sy nm p.q (segsOf areas) m0 w).areas = areas
  timer : timerOf nm (scan sy nm p.q (segsOf areas) m0 w).m + (areas.map (ticks p.q)).sum = p.t0
  lag : (scan sy nm p.q (segsOf areas) m0 w).lag = 2 + j
  grid : (phaseOf nm (scan sy nm p.q (segsOf areas) m0 w).m + w.length) % 21 = (p.c0 + (2 + j)) % 21

/-- what the checks give on the machine `m0`, the 1-1 start, and `cart`, the machine at power-on -/
structure Statement (sy : Syms) (nm : Names) (p : Params) (cart m0 : Machine) (slideN d t N : Nat) : Prop where
  /-- every phase, by real delays: the formula, and the grid -/
  phases : ∀ dl, dl < 21 → CaseProp sy nm (entryAt sy nm p m0 dl (some phaseT)) ∧
    (phaseOf nm (entryAt sy nm p m0 dl (some phaseT)) + entryFrame p dl) % 21 = p.grid % 21
  /-- the real timer of the route, unchanged by the walk -/
  real : CaseProp sy nm (entryAt sy nm p m0 0 none) ∧ timerOf nm (entryAt sy nm p m0 0 none) = timerOf nm (beside m0)
  /-- another value of the timer -/
  values : ∀ v ∈ valuesT, CaseProp sy nm (entryAt sy nm p m0 0 (some v))
  /-- the last digits that give fireworks -/
  fireworks : ∀ v ∈ fireT, CaseProp sy nm (entryAt sy nm p m0 0 (some v))
  /-- a touch at another height -/
  slide : CaseProp sy nm (slideState sy nm ((beforeGrab sy m0).headD default) (beside m0) phaseT slideN)
  /-- every input on every frame, from one state. Hypothesis: `GMerge`. -/
  allInputs : GMerge (level sy) sy PipeTransition.inputs N (inputState sy nm p m0 d t) →
    ∀ w : List UInt8, (∀ i ∈ w, i ∈ PipeTransition.inputs) → w.length = N →
      level sy (run (inputState sy nm p m0 d t) w) = true ∧
        ∀ k, 1 ≤ k → k < N → level sy (run (inputState sy nm p m0 d t) (w.take k)) = false
  /-- real runs with idle frames: the rule and the segments on every frame, the timer as `t0 − Σ⌈p/q⌉`, two frames without the timers, the grid moved by them -/
  runs : ∀ r ∈ runsT, RunProp sy nm p m0 (routeWith r.1.1 r.1.2.1 r.1.2.2) r.2 0
  /-- a real run with a pause in each segment: the same, and the frames of the pauses are `lag` frames -/
  pauses : RunProp sy nm p m0 pauseRun pauseAreas pauseJ
  /-- frame 0 does not depend on the Start press, and the counters before frame 0 are those of `Frames.s_zero`, `Frames.ph_zero` -/
  starts : ∀ kk ∈ startsT, phaseOf nm (startAt sy cart kk) = p.c0 ∧ timerOf nm (startAt sy cart kk) + 1 = p.t0 ∧
    timerOf nm (beforeStart sy cart kk) = p.t0 ∧ subOf nm (beforeStart sy cart kk) = 0 ∧ phaseOf nm (beforeStart sy cart kk) = 2

theorem runProp_of_ok {sy : Syms} {nm : Names} {p : Params} {m0 : Machine} {w : List UInt8} {areas : List Nat} {j : Nat}
    (h : runOK sy nm p m0 w areas j = true) : RunProp sy nm p m0 w areas j := by
  simp only [runOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  refine ⟨a, b, c, d, e, ?_⟩
  rw [← e]
  exact f

theorem statement_of_check {sy : Syms} {nm : Names} {p : Params} {cart m0 : Machine} {slideN d t N : Nat} (hN : 1 ≤ N)
    (h1 : formulaCheck sy nm m0 p slideN = true) (h2 : inputCheck sy nm p m0 d t N = true)
    (h3 : timerCheck sy nm p cart m0 = true) : Statement sy nm p cart m0 slideN d t N := by
  simp only [formulaCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨h1a, h1b⟩, h1d⟩, h1e⟩, h1s⟩ := h1
  simp only [timerCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h3
  obtain ⟨⟨⟨h3a, h3p⟩, h3b⟩, h3c⟩ := h3
  refine ⟨?_, ⟨caseProp_of_ok h1b.1, h1b.2⟩, fun v hv => caseProp_of_ok (h1d v hv), fun v hv => caseProp_of_ok (h1e v hv), caseProp_of_ok h1s, ?_, ?_, runProp_of_ok h3p, ?_⟩
  · intro dl hd
    exact ⟨caseProp_of_ok (h1a dl hd).1, (h1a dl hd).2⟩
  · intro hM w hw hl
    exact first_control h2 zero_mem_inputs hM w hw hl hN
  · intro r hr
    exact runProp_of_ok (h3a r hr)
  · intro kk hk
    have h := h3b kk hk
    simp only [startOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨_, a⟩, b⟩, _⟩, c⟩, d⟩, e⟩ := h
    exact ⟨a, b, c, d, e⟩

end Smbrta.CastleToLevel
