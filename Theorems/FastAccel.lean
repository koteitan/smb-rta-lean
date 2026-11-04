import Smbrta

/-!
# Fast accel: fewest frames to the running top speed, with jumps

From the first controllable frame of 1-1 (`ctx = smb11Start sy cart`).
* `Upper`: on the full emulator (no model), the input sequence `w` reaches the top speed.
* `Lower`: in the relaxed model (`stepRelax`: horizontal state + ground/air flag, landing
  chosen freely), no sequence of at most `n` frames reaches it.
Real controller: `Bounds sy ctx padInputsA relaxInputs 33 34`. With Left+Right
(`Theorems/TasFastAccel.lean`): `Bounds sy ctx lrInputsA relaxInputsLR 30 32`.
Page: `Theorems/FastAccel.md`.
-/

namespace Smbrta.FastAccel

def start (sy : Syms) (ctx : Machine) : RState := { h := dropPos (PState.read sy ctx), air := false }
def top (sy : Syms) : Int := sy.RunTopSpeed.toNat

/-- in the relaxed model, nothing over `rins` of at most `n` frames reaches the top speed -/
def Lower (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat) : Prop :=
  ∀ seq : List (UInt8 × Bool), (∀ c ∈ seq, c ∈ rins) → seq.length ≤ n →
    (Cert.run (stepRelax sy ctx) (start sy ctx) seq).h.speedInt < top sy

/-- on the full emulator, `w` (inputs from `eins`) reaches the top speed -/
def Upper (sy : Syms) (ctx : Machine) (eins : List UInt8) (w : List UInt8) : Prop :=
  (∀ i ∈ w, i ∈ eins) ∧ (PState.read sy (playFull ctx w)).speedInt ≥ top sy

/-- relaxed lower bound `lo` and an emulator witness of `n` frames -/
def Bounds (sy : Syms) (ctx : Machine) (eins : List UInt8) (rins : List (UInt8 × Bool))
    (lo n : Nat) : Prop :=
  Lower sy ctx rins lo ∧ ∃ w, w.length = n ∧ Upper sy ctx eins w

instance (sy : Syms) (ctx : Machine) (eins w : List UInt8) : Decidable (Upper sy ctx eins w) := by
  unfold Upper; infer_instance

def lowerCheck (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat) : Bool :=
  Cert.checkUpTo (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy)) n [start sy ctx]

theorem lower_of_check (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat)
    (h : lowerCheck sy ctx rins n = true) : Lower sy ctx rins n := by
  intro seq h1 h2
  have := Cert.lower_bound (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy))
    (start sy ctx) n h seq h1 h2
  simpa using this

/-! ## A faster lower bound: drop the states that cannot catch up

`V = 256·speed + subspeed` (`Player_X_MoveForce`). If one frame raises `V` by at most `amax`, and
only from above 0 (`V' ≤ max(V, 0) + amax`: `GainBound`), then a state with
`max(V, 0) + amax·r < 256·top` cannot reach the top speed in `r` more frames, and the search
drops it. `GainBound` is an assumption about the relaxed step; the routine checks of
`Theorems/TopSpeed.lean` support it (`ImposeFriction` adds at most the adder, `X_Physics` takes
the adder from the table, `GetPlayerAnimSpeed` keeps the speed or sets it and the subspeed to 0). -/

/-- speed with subspeed, in 1/256 speed units -/
def V (s : RState) : Int := 256 * s.h.speedInt + s.h.fricMF.toNat

def inRange (sy : Syms) (s : RState) : Bool :=
  decide (-(top sy) ≤ s.h.speedInt) && decide (s.h.speedInt ≤ top sy)

def GainBound (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) : Prop :=
  ∀ s : RState, inRange sy s = true → ∀ c ∈ rins,
    inRange sy (stepRelax sy ctx s c) = true ∧ V (stepRelax sy ctx s c) ≤ max (V s) 0 + amax sy ctx

/-- follow a state if it is out of range (not covered by `GainBound`) or can still catch up -/
def keepFast (sy : Syms) (ctx : Machine) (r : Nat) (s : RState) : Bool :=
  !(inRange sy s) || decide (256 * top sy ≤ max (V s) 0 + amax sy ctx * r)

def lowerFastCheck (sy : Syms) (ctx : Machine) (rins : List (UInt8 × Bool)) (n : Nat) : Bool :=
  Cert.checkPruned (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy))
    (keepFast sy ctx) n [start sy ctx]

theorem foldl_max_ge : ∀ (l : List Int) (a : Int), a ≤ l.foldl max a
  | [], _ => Int.le_refl _
  | x :: l, a => Int.le_trans (Int.le_max_left a x) (foldl_max_ge l (max a x))

theorem amax_nonneg (sy : Syms) (ctx : Machine) : 0 ≤ amax sy ctx := foldl_max_ge _ 0

theorem gain_run {sy : Syms} {ctx : Machine} {rins : List (UInt8 × Bool)} (hG : GainBound sy ctx rins) :
    ∀ (seq : List (UInt8 × Bool)) (s : RState), inRange sy s = true → (∀ c ∈ seq, c ∈ rins) →
      inRange sy (Cert.run (stepRelax sy ctx) s seq) = true ∧
      V (Cert.run (stepRelax sy ctx) s seq) ≤ max (V s) 0 + amax sy ctx * seq.length
  | [], s, hs, _ => by
    simp only [Cert.run, List.foldl_nil, List.length_nil]
    exact ⟨hs, by omega⟩
  | c :: rest, s, hs, hseq => by
    have hc := hG s hs c (hseq c (by simp))
    have ih := gain_run hG rest (stepRelax sy ctx s c) hc.1 (fun d hd => hseq d (by simp [hd]))
    have ha := amax_nonneg sy ctx
    refine ⟨ih.1, ?_⟩
    have e : amax sy ctx * ((c :: rest).length : Int) = amax sy ctx * (rest.length : Int) + amax sy ctx := by
      simp only [List.length_cons]; push_cast; rw [Int.mul_add, Int.mul_one]
    simp only [Cert.run, List.foldl_cons] at ih ⊢
    rw [e]
    have : max (V (stepRelax sy ctx s c)) 0 ≤ max (V s) 0 + amax sy ctx := by omega
    omega

theorem lower_of_fast {sy : Syms} {ctx : Machine} {rins : List (UInt8 × Bool)} {n : Nat}
    (hG : GainBound sy ctx rins) (h : lowerFastCheck sy ctx rins n = true) : Lower sy ctx rins n := by
  intro seq h1 h2
  have := Cert.lower_bound_pruned (stepRelax sy ctx) rins (fun s => decide (s.h.speedInt < top sy))
    (keepFast sy ctx) (start sy ctx) n ?_ h seq h1 h2
  · simpa using this
  intro r s hk seq' hseq hlen
  simp only [keepFast, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at hk
  obtain ⟨hin, hlt⟩ := hk
  have g := gain_run hG seq' s hin hseq
  have hmul : amax sy ctx * (seq'.length : Int) ≤ amax sy ctx * (r : Int) :=
    Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) (amax_nonneg sy ctx)
  have hf : (0 : Int) ≤ ((Cert.run (stepRelax sy ctx) s seq').h.fricMF.toNat : Int) := by omega
  simp only [V] at g hlt
  simp only [decide_eq_true_eq]
  omega

/-! ## Every land area

The relaxed step reads, besides its state, the input and bytes shown not to matter, only the
scene bytes `PlayerSize`, `AreaType`, `SwimmingFlag`, `PlayerChangeSizeFlag`,
`JumpspringAnimCtrl`, `TimerControl`, `GameEngineSubroutine`, `Player_CollisionBits`
(found by `smbrta relax-reads`). The bounds are proved for each land `AreaType`; the other
scene bytes keep their values at the 1-1 start (small Mario, normal play, open area). -/

/-- the `AreaType` values of land areas: ground, underground, castle (water is 0) -/
def landAreas : List UInt8 := [1, 2, 3]

/-- the 1-1 start with `AreaType` set to `a` -/
def inArea (sy : Syms) (ctx : Machine) (a : UInt8) : Machine := poke ctx sy.AreaType a

/-- `Bounds` in every land area -/
def BoundsAllAreas (sy : Syms) (ctx : Machine) (eins : List UInt8) (rins : List (UInt8 × Bool))
    (lo n : Nat) : Prop :=
  ∀ a ∈ landAreas, Bounds sy (inArea sy ctx a) eins rins lo n

/-- a property of every land area from its three cases -/
theorem forall_land {P : UInt8 → Prop} (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ a ∈ landAreas, P a := by
  intro a ha
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h1
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h2
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h3
  exact absurd ha List.not_mem_nil

theorem allAreas_of {sy : Syms} {ctx : Machine} {eins : List UInt8} {rins : List (UInt8 × Bool)}
    {lo n : Nat} (h1 : Bounds sy (inArea sy ctx 1) eins rins lo n)
    (h2 : Bounds sy (inArea sy ctx 2) eins rins lo n) (h3 : Bounds sy (inArea sy ctx 3) eins rins lo n) :
    BoundsAllAreas sy ctx eins rins lo n := by
  intro a ha
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h1
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h2
  rcases List.mem_cons.mp ha with h | ha
  · exact h ▸ h3
  exact absurd ha List.not_mem_nil

/-- 34 frames, real controller: two backward jumps (found by the pruned exact search) -/
def witness : List UInt8 := [0x02, 0x04, 0x81, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x41, 0x01, 0x02, 0x81,
  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01]

end Smbrta.FastAccel
