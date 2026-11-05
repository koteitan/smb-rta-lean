import Theorems.Potential

/-!
# The opening: no input gets further than the TAS fast accel

The model: the horizontal frame `hstep` (`Theorems/Potential.lean`), and jumps. A jump starts
on the ground; from its start to its landing frame it lasts between the lengths of a one-frame A
press and of a held A, measured on the emulator for the takeoff speed (`Lens`). In the air
`hstep` runs with `Player_State` = air, on the ground with ground.

A search state is the horizontal state, the air frames left (0 on the ground), and the distance
`P` has moved (`16·v` per frame). `optCheck` follows every input from the 1-1 start for `n`
frames and drops the states that cannot get past `T` any more: the potential bound `dbound`
(`dist_le`) of what is left is too small. Page: `Opening.md`.
-/

namespace Smbrta.Opening

open Potential
open TopSpeed (top)

/-- horizontal state, air frames left, distance -/
abbrev St := (HS × Nat) × Int

/-- jump lengths by takeoff speed `|v|`: (shortest, longest), frames from the jump start to the
landing frame -/
abbrev Lens := Array (Nat × Nat)

/-- the inputs allowed: on the ground any (with or without a jump start), in the air no jump -/
def valid (r : Nat) (i : HIn) : Bool := if r == 0 then i.st == 0 else i.st == 1 && !i.jump

/-- the air frames left after the frame -/
def modes (lens : Lens) (s : HS) (r : Nat) (i : HIn) : List Nat :=
  if r == 0 then
    if i.jump then
      let lh := lens[(sbyte s.v).natAbs]!
      (List.range (lh.2 + 1 - lh.1)).map fun j => lh.1 - 1 + j
    else [0]
  else [r - 1]

def succ (sy : Syms) (m : Machine) (lens : Lens) (x : St) : List St :=
  (inputsN.filter (valid x.1.2)).flatMap fun i =>
    let t := hstep sy m x.1.1 i
    (modes lens x.1.1 x.1.2 i).map fun r' => ((t, r'), x.2 + 16 * sbyte t.v)

/-- a bound on `Φ` that `J` accepts -/
def pOf (sy : Syms) (m : Machine) (s : HS) : Int :=
  if s.rs == 0 then phi sy m s else max (phi sy m s) (theta sy)

/-- follow `x` with `r` frames left unless it is in the domain and cannot get past `T` -/
def keep (sy : Syms) (m : Machine) (T : Int) (r : Nat) (x : St) : Bool :=
  !inD sy x.1.1 || decide (T + 1 ≤ x.2 + dbound sy m (pOf sy m x.1.1) r)

def start (sy : Syms) (m : Machine) : St := ((startHS sy m, 0), 0)

def optCheck (sy : Syms) (m : Machine) (lens : Lens) (T : Int) (n : Nat) : Bool :=
  Cert.checkPrunedS (succ sy m lens) (fun x => decide (x.2 ≤ T)) (keep sy m T) n [start sy m]

/-! ## Soundness -/

theorem phi_nonneg {sy : Syms} {m : Machine} (F : Facts sy m) (s : HS) : 0 ≤ phi sy m s := by
  have := w_nonneg F s
  unfold phi; omega

theorem J_pOf {sy : Syms} {m : Machine} {s : HS} (hD : inD sy s = true) :
    J sy m s (pOf sy m s) := by
  refine ⟨hD, ?_, fun h => ?_⟩
  · unfold pOf; split <;> omega
  · unfold pOf
    have : (s.rs == 0) = false := by simpa using h
    rw [this]; simp only [Bool.false_eq_true, if_false]; omega

theorem dbound_nonneg {sy : Syms} {m : Machine} (F : Facts sy m) :
    ∀ (n : Nat) (p : Int), 0 ≤ p → 0 ≤ dbound sy m p n
  | 0, _, _ => by simp [dbound]
  | n + 1, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_nonneg F n (nxt sy m p) (by omega)
    simp only [dbound]
    have : 0 ≤ nxt sy m p / 256 := by omega
    omega

theorem dbound_mono {sy : Syms} {m : Machine} (F : Facts sy m) :
    ∀ (a k : Nat) (p : Int), 0 ≤ p → dbound sy m p a ≤ dbound sy m p (a + k)
  | 0, k, p, hp => by simpa [dbound] using dbound_nonneg F k p hp
  | a + 1, k, p, hp => by
    have h1 := le_nxt F p
    have ih := dbound_mono F a k (nxt sy m p) (by omega)
    rw [show a + 1 + k = (a + k) + 1 by omega]
    simp only [dbound]
    omega

theorem mem_succ {sy : Syms} {m : Machine} {lens : Lens} {x y : St} (h : y ∈ succ sy m lens x) :
    ∃ i ∈ inputsN, y.1.1 = hstep sy m x.1.1 i ∧ y.2 = x.2 + 16 * sbyte (hstep sy m x.1.1 i).v := by
  unfold succ at h
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.1 h
  obtain ⟨r', _, hr⟩ := List.mem_map.1 hy
  exact ⟨i, (List.mem_filter.1 hi).1, by rw [← hr], by rw [← hr]⟩

/-- what `potCheck` and the input lists give -/
structure OFacts (sy : Syms) (m : Machine) : Prop where
  facts : Facts sy m
  inputs_sub : ∀ i ∈ inputsN, i ∈ inputs

/-- from a state in the domain, `m` steps add at most `dbound` to the distance -/
theorem reach_le {sy : Syms} {m : Machine} {lens : Lens} (F : OFacts sy m) :
    ∀ {x u : St} {k : Nat} (p : Int), Cert.Reach (succ sy m lens) x k u → J sy m x.1.1 p →
      u.2 ≤ x.2 + dbound sy m p k
  | _, _, _, p, .refl _, _ => by simp [dbound]
  | x, u, _, p, @Cert.Reach.step _ _ _ y _ k hy hr, hJ => by
    obtain ⟨i, hi, hy1, hy2⟩ := mem_succ hy
    obtain ⟨hJ', h256, htop⟩ := step_J F.facts hJ (F.inputs_sub i hi)
    have hJy : J sy m y.1.1 (nxt sy m p) := by rw [hy1]; exact hJ'
    have ih := reach_le F (nxt sy m p) hr hJy
    have h3 : sbyte (hstep sy m x.1.1 i).v ≤ nxt sy m p / 256 := by omega
    have h4 : 16 * sbyte (hstep sy m x.1.1 i).v ≤ 16 * min (top sy : Int) (nxt sy m p / 256) := by omega
    simp only [dbound]
    omega

/-- the domain is kept along the steps -/
theorem reach_inD {sy : Syms} {m : Machine} {lens : Lens} (F : OFacts sy m) :
    ∀ {x u : St} {k : Nat}, Cert.Reach (succ sy m lens) x k u → inD sy x.1.1 = true → inD sy u.1.1 = true
  | _, _, _, .refl _, h => h
  | x, _, _, @Cert.Reach.step _ _ _ y _ _ hy hr, h => by
    obtain ⟨i, hi, hy1, _⟩ := mem_succ hy
    have hc := F.facts.check x.1.1 h i (F.inputs_sub i hi)
    simp only [stepOk, Bool.and_eq_true] at hc
    exact reach_inD F hr (by rw [hy1]; exact hc.1.1.1)

/-- each step adds at most `16·top` -/
theorem reach_top {sy : Syms} {m : Machine} {lens : Lens} (F : OFacts sy m) :
    ∀ {x u : St} {k : Nat}, Cert.Reach (succ sy m lens) x k u → inD sy x.1.1 = true →
      u.2 ≤ x.2 + 16 * (top sy : Int) * k
  | _, _, _, .refl _, _ => by simp
  | x, u, _, @Cert.Reach.step _ _ _ y _ k hy hr, h => by
    obtain ⟨i, hi, hy1, hy2⟩ := mem_succ hy
    have hc := F.facts.check x.1.1 h i (F.inputs_sub i hi)
    simp only [stepOk, Bool.and_eq_true] at hc
    have hDy : inD sy y.1.1 = true := by rw [hy1]; exact hc.1.1.1
    have ih := reach_top F hr hDy
    have hv : sbyte (hstep sy m x.1.1 i).v ≤ (top sy : Int) := by
      have := hc.1.1.1
      simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-- the search proves: within `n` frames the distance never gets past `T` -/
theorem opt_of_check {sy : Syms} {m : Machine} {lens : Lens} {T : Int} {n : Nat} (F : OFacts sy m)
    (h : optCheck sy m lens T n = true) :
    ∀ k u, k ≤ n → Cert.Reach (succ sy m lens) (start sy m) k u → u.2 ≤ T := by
  intro k u hk hr
  have := Cert.prunedS_spec (succ sy m lens) (fun x => decide (x.2 ≤ T)) (keep sy m T) ?_ n
    [start sy m] h (start sy m) (by simp) k u hk hr
  · simpa using this
  intro r x hx k' u' hk' hr'
  simp only [keep, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at hx
  obtain ⟨hD, hlt⟩ := hx
  have h1 := reach_le F (pOf sy m x.1.1) hr' (J_pOf hD)
  have h2 := dbound_mono F.facts k' (r - k') (pOf sy m x.1.1) (by
    have := phi_nonneg F.facts x.1.1
    unfold pOf; split <;> omega)
  rw [show k' + (r - k') = r by omega] at h2
  simp only [decide_eq_true_eq]
  omega

/-- past `n` frames, each frame adds at most `16·top` -/
theorem opt_after {sy : Syms} {m : Machine} {lens : Lens} {T : Int} {n : Nat} (F : OFacts sy m)
    (hD : inD sy (startHS sy m) = true) (h : optCheck sy m lens T n = true) :
    ∀ k u, Cert.Reach (succ sy m lens) (start sy m) (n + k) u → u.2 ≤ T + 16 * (top sy : Int) * k := by
  intro k u hr
  obtain ⟨y, h1, h2⟩ := Cert.Reach.split n k hr
  have hy := opt_of_check F h n y (Nat.le_refl _) h1
  have hDy := reach_inD F h1 hD
  have := reach_top F h2 hDy
  omega

/-! ## The game's jump lengths -/

/-- frames from a jump start to the landing frame, from the 1-1 start with speed `v` and Right
held, A held for `hold` frames -/
def airTime (sy : Syms) (m0 : Machine) (v : UInt8) (hold : Nat) : Nat := Id.run do
  let m := poke m0 sy.Player_X_Speed v
  let mut m := poke m sy.Player_XSpeedAbsolute v
  for k in [0:80] do
    m := runFrame m (smbToPad (if k < hold then 0x81 else 0x01))
    if peek m sy.Player_State == 0 then return k + 1
  return 80

/-- for `|v| = 0 .. top`: (a one-frame press, A held throughout) -/
def jumpLens (sy : Syms) (m0 : Machine) : Lens :=
  ((List.range (top sy + 1)).map fun v => (airTime sy m0 v.toUInt8 1, airTime sy m0 v.toUInt8 80)).toArray

end Smbrta.Opening
