import Theorems.Potential

/-!
# The air speed cap

In the air, below the air threshold (`|v| < AirFastSpeed`) the speed stays below it. It can only
reach the threshold on a ground frame, and that frame gains at most `a_max`. So from a state below
the threshold, a run of air frames followed by any frames moves `P` by at most
`16·(A − 1)·K + capDist m`. Page: `AirCap.md`.
-/

namespace Smbrta.AirCap

open Potential
open TopSpeed (top speedsB bytes)

/-- the largest `Φ` right after the speed reaches the air threshold -/
def B (sy : Syms) (m : Machine) : Int := 256 * (sy.AirFastSpeed.toNat : Int) - 1 + gFast sy m

/-- the speed is below the air threshold -/
def capped (sy : Syms) (s : HS) : Bool := decide ((sbyte s.v).natAbs < sy.AirFastSpeed.toNat)

/-- the frame runs in the air (it started there, or it starts a jump) -/
def isAir (i : HIn) : Bool := i.st != 0 || i.jump

/-- from `s`, the frame stays below the threshold, or it is a ground frame and `Φ ≤ B` after it -/
def capOk (sy : Syms) (m : Machine) (s : HS) (i : HIn) : Bool :=
  let t := hstep sy m s i
  capped sy t || (!isAir i && decide (phi sy m t ≤ B sy m))

/-- speeds in the four steps below the threshold; further below, `stepOk` is enough -/
def near (sy : Syms) (v : UInt8) : Bool :=
  decide ((sbyte v).natAbs < sy.AirFastSpeed.toNat) && decide (sy.AirFastSpeed.toNat ≤ (sbyte v).natAbs + 4)

def nearStates (sy : Syms) : List HS :=
  ((speedsB sy).filter (near sy)).flatMap fun v => bytes.flatMap fun f => (mds v).flatMap fun md =>
    facings.flatMap fun fd => (rsVals sy).map fun rs => { v, f, fd, md, rs }

def capCheck (sy : Syms) (m : Machine) : Bool :=
  (nearStates sy).all fun s => inputsN.all (capOk sy m s)

/-- the bound on the distance of `n` frames from a state below the threshold -/
def capDist (sy : Syms) (m : Machine) : Nat → Int
  | 0 => 0
  | n + 1 => max (16 * ((sy.AirFastSpeed.toNat : Int) - 1) + capDist sy m n)
      (16 * min (top sy : Int) (B sy m / 256) + dbound sy m (B sy m) n)

/-- what the computation provides -/
structure CFacts (sy : Syms) (m : Machine) : Prop where
  pot : Facts sy m
  cap : capCheck sy m = true
  speeds : speedsComplete sy = true
  normI : normIdem = true
  small : 2 * c sy m + gFast sy m < 770

theorem isAir_norm (i : HIn) : isAir (norm i) = isAir i := by
  unfold norm isAir; split <;> rfl

theorem capOk_norm {sy : Syms} {m : Machine} (s : HS) (i : HIn) (h : norm (norm i) = norm i) :
    capOk sy m s (norm i) = capOk sy m s i := by
  unfold capOk hstep; rw [h, isAir_norm]

theorem w_le {sy : Syms} {m : Machine} (F : Facts sy m) (s : HS) : w sy m s ≤ 2 * c sy m := by
  have := F.c_nonneg
  unfold w; split <;> (try split) <;> omega

theorem inD_step {sy : Syms} {m : Machine} (F : Facts sy m) {s : HS} (hD : inD sy s = true) {i : HIn}
    (hi : i ∈ inputs) : inD sy (hstep sy m s i) = true := by
  have h := F.check s hD i hi
  simp only [stepOk, Bool.and_eq_true] at h
  exact h.1.1.1

/-- one frame from a state below the threshold -/
theorem step_cap {sy : Syms} {m : Machine} (F : CFacts sy m) {s : HS} (hD : inD sy s = true)
    (hc : capped sy s = true) {i : HIn} (hi : i ∈ inputs) :
    capped sy (hstep sy m s i) = true ∨
      (isAir i = false ∧ phi sy m (hstep sy m s i) ≤ B sy m) := by
  by_cases hn : near sy s.v = true
  · -- near the threshold: the check
    obtain ⟨v, f, fd, md, rs⟩ := s
    have hD' := hD
    simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD'
    obtain ⟨⟨⟨hv, hfd⟩, hmd⟩, hrs⟩ := hD'
    have hvs : v ∈ speedsB sy := by
      have hsp := F.speeds
      simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.contains_iff_mem] at hsp
      rcases hsp v (mem_bytes v) with h | h
      · rw [h] at hv; exact absurd hv (by decide)
      · exact h
    have hmem : ({ v, f, fd, md, rs } : HS) ∈ nearStates sy :=
      List.mem_flatMap.2 ⟨v, List.mem_filter.2 ⟨hvs, hn⟩, List.mem_flatMap.2 ⟨f, mem_bytes f,
        List.mem_flatMap.2 ⟨md, hmd, List.mem_flatMap.2 ⟨fd, hfd, List.mem_map.2 ⟨rs, hrs, rfl⟩⟩⟩⟩⟩
    have hall := F.cap
    simp only [capCheck, List.all_eq_true] at hall
    have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
    have hid : norm (norm i) = norm i := by
      have hn' := F.normI
      simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn'
      exact hn' i hi
    have h := hall _ hmem _ hin
    rw [capOk_norm _ i hid] at h
    simp only [capOk, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_true_eq] at h
    exact h
  · -- further below: one frame cannot reach it
    left
    have hF := F.pot
    have h := hF.check s hD i hi
    generalize ht : hstep sy m s i = t at h ⊢
    simp only [stepOk, ht, Bool.and_eq_true, decide_eq_true_eq] at h
    have hgain := h.1.1.2
    have hw := w_le hF s
    have hsm := F.small
    have hpt := phi_ge hF t
    simp only [near, Bool.and_eq_true, decide_eq_true_eq, not_and] at hn
    simp only [capped, decide_eq_true_eq] at hc ⊢
    have hlo := hn hc
    have hft : t.f.toNat < 256 := t.f.toNat_lt
    have hfs : s.f.toNat < 256 := s.f.toNat_lt
    have hVt : 256 * ((sbyte t.v).natAbs : Int) ≤ ((V t).natAbs : Int) + 255 := by
      unfold V; omega
    have hVs : ((V s).natAbs : Int) ≤ 256 * ((sbyte s.v).natAbs : Int) + 255 := by
      unfold V; omega
    have hps : phi sy m s = ((V s).natAbs : Int) + w sy m s := rfl
    omega

theorem J_B {sy : Syms} {m : Machine} (F : Facts sy m) {t : HS} (hD : inD sy t = true)
    (h : phi sy m t ≤ B sy m) : J sy m t (B sy m) := by
  have := F.gf_nonneg
  exact ⟨hD, h, fun _ => by unfold theta B; omega⟩

/-- from a state below the threshold, the distance of any frames is at most `capDist` -/
theorem dist_capped {sy : Syms} {m : Machine} (F : CFacts sy m) :
    ∀ (is : List HIn) (s : HS), inD sy s = true → capped sy s = true → (∀ i ∈ is, i ∈ inputs) →
      hdist sy m s is ≤ capDist sy m is.length
  | [], _, _, _, _ => by simp [hdist, capDist]
  | i :: rest, s, hD, hc, his => by
    have hi := his i (by simp)
    have hDt := inD_step F.pot hD hi
    have hrest : ∀ j ∈ rest, j ∈ inputs := fun j hj => his j (by simp [hj])
    rcases step_cap F hD hc hi with h | ⟨_, h⟩
    · have ih := dist_capped F rest _ hDt h hrest
      simp only [capped, decide_eq_true_eq] at h
      simp only [hdist, capDist]
      omega
    · have hd := dist_le F.pot rest _ _ (J_B F.pot hDt h) hrest
      have hpt := phi_ge F.pot (hstep sy m s i)
      generalize ht : hstep sy m s i = t at *
      have hft : t.f.toNat < 256 := t.f.toNat_lt
      have hVt : 256 * sbyte t.v ≤ ((V t).natAbs : Int) := by unfold V; omega
      have htop : sbyte t.v ≤ (top sy : Int) := by
        simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at hDt
        omega
      have h2 : sbyte t.v ≤ B sy m / 256 := by omega
      have h3 : 16 * sbyte t.v ≤ 16 * min (top sy : Int) (B sy m / 256) := by omega
      simp only [hdist, capDist, ht]
      omega

/-- air frames keep the state below the threshold; each moves at most `16·(A − 1)` -/
theorem air_run {sy : Syms} {m : Machine} (F : CFacts sy m) :
    ∀ (is : List HIn) (s : HS), inD sy s = true → capped sy s = true →
      (∀ i ∈ is, i ∈ inputs ∧ isAir i = true) →
      inD sy (hrun sy m s is) = true ∧ capped sy (hrun sy m s is) = true ∧
        hdist sy m s is ≤ 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * is.length
  | [], _, hD, hc, _ => by simp [hrun, hdist, hD, hc]
  | i :: rest, s, hD, hc, his => by
    obtain ⟨hi, ha⟩ := his i (by simp)
    have hDt := inD_step F.pot hD hi
    have hct : capped sy (hstep sy m s i) = true := by
      rcases step_cap F hD hc hi with h | ⟨h, _⟩
      · exact h
      · rw [h] at ha; exact absurd ha (by decide)
    obtain ⟨h1, h2, h3⟩ := air_run F rest _ hDt hct (fun j hj => his j (by simp [hj]))
    refine ⟨h1, h2, ?_⟩
    simp only [capped, decide_eq_true_eq] at hct
    simp only [hdist, List.length_cons]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

theorem hdist_append {sy : Syms} {m : Machine} :
    ∀ (a b : List HIn) (s : HS),
      hdist sy m s (a ++ b) = hdist sy m s a + hdist sy m (hrun sy m s a) b
  | [], _, _ => by simp [hdist, hrun]
  | i :: rest, b, s => by
    have ih := hdist_append (sy := sy) (m := m) rest b (hstep sy m s i)
    simp only [List.cons_append, hdist]
    rw [ih, show hrun sy m s (i :: rest) = hrun sy m (hstep sy m s i) rest from rfl]
    omega

/-- `K` air frames from a state below the threshold, then any frames -/
theorem landing_bound {sy : Syms} {m : Machine} (F : CFacts sy m) (s : HS) (hD : inD sy s = true)
    (hc : capped sy s = true) (a b : List HIn) (ha : ∀ i ∈ a, i ∈ inputs ∧ isAir i = true)
    (hb : ∀ i ∈ b, i ∈ inputs) :
    hdist sy m s (a ++ b) ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * a.length + capDist sy m b.length := by
  obtain ⟨h1, h2, h3⟩ := air_run F a s hD hc ha
  have h4 := dist_capped F b _ h1 h2 hb
  rw [hdist_append]
  omega

/-- landing later is never better: the bound does not grow when a frame moves into the air part -/
theorem landing_later {sy : Syms} {m : Machine} (K : Int) :
    ∀ (n k : Nat), 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (K + k) + capDist sy m n ≤
      16 * ((sy.AirFastSpeed.toNat : Int) - 1) * K + capDist sy m (n + k)
  | _, 0 => by simp
  | n, k + 1 => by
    have ih := landing_later (sy := sy) (m := m) K n k
    have h : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) + capDist sy m (n + k) ≤ capDist sy m (n + k + 1) := by
      simp only [capDist]; omega
    rw [show n + (k + 1) = n + k + 1 by omega]
    push_cast
    rw [show K + ((k : Int) + 1) = (K + k) + 1 by omega, Int.mul_add, Int.mul_one]
    omega

end Smbrta.AirCap
