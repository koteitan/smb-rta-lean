import Theorems.Opening
import Std.Data.HashMap

/-!
# A fast takeoff in the bonus room

The room: a fall that does not depend on the input, then the floor, and a block to the right. While
Mario's feet are below the block's top, `P` has to stay left of its corner, or he hits it. A jump from
the floor at the air threshold of `X_Physics` or more rises fast, but his feet stay low for a fixed
number of air frames after the jump frame (`Theorems/Jump.lean`).

`roomCheck` follows `hstep` over all inputs from the room's first frame. It keeps, for each horizontal
state, the least and the greatest `P` of the runs that reach it: `hstep` does not read `P`, so these two
numbers bound `P` of every run through that state (`Cov`). A state is dropped once the bound on the
potential says that `|v|` cannot reach the threshold by the last takeoff (`keep_of_run`).

Result, for a takeoff by the last frame searched:
* moving right: `P` does not stay left of the corner (`no_right_takeoff`);
* moving left: he is so far back that `P` is short of the goal frame's position (`left_short`).
A later takeoff is short by the top speed alone (`late_short`). All together: `fast_takeoff_short`.
Page: `FastTakeoff.md`.
-/

namespace Smbrta.FastTakeoff

open Potential
open TopSpeed (top)

/-! ## Runs -/

/-- horizontal state and `P` -/
abbrev Pos := HS × Int

/-- one frame: the open area moves `P` by `16·v`, with the new speed -/
def adv (sy : Syms) (m : Machine) (x : Pos) (i : HIn) : Pos :=
  (hstep sy m x.1 i, x.2 + 16 * sbyte (hstep sy m x.1 i).v)

/-- the frames of a list of inputs -/
def go (sy : Syms) (m : Machine) : Pos → List HIn → Pos
  | x, [] => x
  | x, i :: r => go sy m (adv sy m x i) r

/-- `P` is left of the corner after each of these frames -/
def Low (sy : Syms) (m : Machine) (cp : Int) : Pos → List HIn → Prop
  | _, [] => True
  | x, i :: r => (adv sy m x i).2 < cp ∧ Low sy m cp (adv sy m x i) r

/-- an input of an air frame -/
def AirIn (i : HIn) : Prop := i ∈ inputs ∧ i.st = 1 ∧ i.jump = false
/-- an input of a ground frame without a jump -/
def GndIn (i : HIn) : Prop := i ∈ inputs ∧ i.st = 0 ∧ i.jump = false
/-- an input of a jump frame -/
def JmpIn (i : HIn) : Prop := i ∈ inputs ∧ i.st = 0 ∧ i.jump = true

/-- the numbers of a room -/
structure Room where
  /-- the horizontal state of the room's first frame -/
  s0 : HS
  /-- `P` at the room's first frame is at least this -/
  P0 : Int
  /-- and at most this -/
  P1 : Int
  /-- the air frames of the fall -/
  A : Nat
  /-- the most ground frames before a takeoff searched -/
  G : Nat
  /-- the air frames after the jump frame during which the feet stay low -/
  L : Nat
  /-- the frames from the landing frame to the goal frame -/
  N : Nat
  /-- `P` of the corner: left of it the block is not hit -/
  cp : Int
  /-- `P` that has to be reached at the goal frame -/
  goal : Int
  deriving Repr, Inhabited

/-- the corner: the block's first column is the object's column plus one (a terrain change takes effect one
column later), and his side reaches the block at the side adder -/
def cornerP (sy : Syms) : Int :=
  256 * (16 * ((sy.RoomBlockLeftByte.toNat / 16 + 1 : Nat) : Int) - (sy.SideAdderX.toNat : Int))

/-- the block's right end, with his left foot past it: the left foot is as far from the left of his box as
the right foot (`FeetAdderX`) from the right of it -/
def goalP (sy : Syms) : Int :=
  256 * (16 * ((sy.RoomBlockRightByte.toNat / 16 + 1 : Nat) : Int) - (15 - (sy.FeetAdderX.toNat : Int)))

/-- the bonus room: stopped, facing right, at the start position, with any fraction of a pixel -/
def bonusRoom (sy : Syms) (A G L N : Nat) : Room :=
  { s0 := { v := 0, f := 0, fd := 1, md := 0, rs := 0 }
    P0 := 256 * (sy.RoomStartX.toNat : Int)
    P1 := 256 * (sy.RoomStartX.toNat : Int) + 255
    A, G, L, N, cp := cornerP sy, goal := goalP sy }

/-! ## The search -/

def airI : List HIn := inputsN.filter fun i => i.st == 1 && !i.jump
def gndI : List HIn := inputsN.filter fun i => i.st == 0 && !i.jump
def jmpI : List HIn := inputsN.filter fun i => i.st == 0 && i.jump

/-- a horizontal state with the least and the greatest `P` of the runs that reach it -/
abbrev Ent := HS × (Int × Int)
abbrev Lay := Std.HashMap HS (Int × Int)

/-- merge an entry into the map -/
def addE (l : Lay) (s : HS) (lo hi : Int) : Lay :=
  match l[s]? with
  | some e => if e.1 ≤ lo ∧ hi ≤ e.2 then l else l.insert s (min e.1 lo, max e.2 hi)
  | none => l.insert s (lo, hi)

/-- one input from one entry; `keep` reads the least `P` of the new frame -/
def addI (sy : Syms) (m : Machine) (keep : Int → Bool) (e : Ent) (nx : Lay) (i : HIn) : Lay :=
  let t := hstep sy m e.1 i
  let d := 16 * sbyte t.v
  if keep (e.2.1 + d) then addE nx t (e.2.1 + d) (e.2.2 + d) else nx

/-- the next layer -/
def stepE (sy : Syms) (m : Machine) (is : List HIn) (keep : Int → Bool) (es : List Ent) : List Ent :=
  (es.foldl (fun nx e => is.foldl (addI sy m keep e) nx) {}).toList

/-- `|v|` can still reach the threshold in `rem` more frames: `Φ` grows by at most `g_fast` per frame, and while
its bound is below `θ` by at most `g_slow` -/
def keepPhi (sy : Syms) (m : Machine) (rem : Nat) (e : Ent) : Bool :=
  decide (theta sy ≤ phi sy m e.1 + gFast sy m * (rem : Int)) &&
    decide (theta sy ≤ Opening.pOf sy m e.1 + gSlow sy m * (rem : Int))

/-- the air frames of the fall, `G` ground frames after them -/
def fall (sy : Syms) (m : Machine) (G : Nat) : Nat → List Ent → List Ent
  | 0, l => l
  | k + 1, l => fall sy m G k ((stepE sy m airI (fun _ => true) l).filter (keepPhi sy m (k + G)))

/-- air frames while left of the corner -/
def airRun (sy : Syms) (m : Machine) (cp : Int) : Nat → List Ent → List Ent
  | 0, l => l
  | k + 1, l => airRun sy m cp k (stepE sy m airI (fun q => decide (q < cp)) l)

/-- moving right at the threshold or more: no jump stays left of the corner for `L` air frames -/
def rightOk (sy : Syms) (m : Machine) (cp : Int) (L : Nat) (es : List Ent) : Bool :=
  let r := es.filter fun e => decide ((sy.AirFastSpeed.toNat : Int) ≤ sbyte e.1.v)
  (airRun sy m cp L (stepE sy m jmpI (fun q => decide (q < cp)) r)).isEmpty

/-- moving left at the threshold or more: `D` more frames are short of the goal, by the potential bound -/
def leftOk (sy : Syms) (m : Machine) (D : Nat) (goal : Int) (es : List Ent) : Bool :=
  let l := es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))
  let H := l.foldl (fun b e => max b e.2.2) 0
  let Q := l.foldl (fun b e => max b (Opening.pOf sy m e.1)) 0
  l.all (fun e => inD sy e.1 && decide (e.2.2 ≤ H) && decide (Opening.pOf sy m e.1 ≤ Q)) &&
    decide (H + dbound sy m Q D < goal)

/-- the ground frames: `r` more may come before the last takeoff -/
def gndCheck (sy : Syms) (m : Machine) (cp : Int) (L D : Nat) (goal : Int) : Nat → List Ent → Bool
  | 0, l => rightOk sy m cp L l && leftOk sy m D goal l
  | r + 1, l => rightOk sy m cp L l && leftOk sy m (D + (r + 1)) goal l &&
      gndCheck sy m cp L D goal r
        ((stepE sy m gndI (fun q => decide (q < cp)) l).filter (keepPhi sy m r))

/-- the whole search -/
def roomCheck (sy : Syms) (m : Machine) (R : Room) : Bool :=
  inD sy R.s0 && decide (R.G ≤ R.N) &&
    gndCheck sy m R.cp R.L (R.N - R.G) R.goal R.G (fall sy m R.G R.A [(R.s0, (R.P0, R.P1))])

/-- past the last takeoff searched, the top speed from the corner is short of the goal -/
def lateOk (sy : Syms) (R : Room) : Bool :=
  decide (R.cp - 1 + 16 * (top sy : Int) * ((R.N - R.G - 2 - R.L : Nat) : Int) < R.goal)

/-- what the computation provides -/
structure TFacts (sy : Syms) (m : Machine) : Prop where
  pot : Facts sy m
  normI : normIdem = true

/-! ## Merging is sound -/

/-- the entry of `x.1` in the list bounds `x.2` -/
def Cov (es : List Ent) (x : Pos) : Prop := ∃ a b, (x.1, (a, b)) ∈ es ∧ a ≤ x.2 ∧ x.2 ≤ b

/-- the same, in the map -/
def HCov (l : Lay) (t : HS) (p : Int) : Prop := ∃ a b, l[t]? = some (a, b) ∧ a ≤ p ∧ p ≤ b

theorem addE_old {l : Lay} {s t : HS} {lo hi p : Int} (h : HCov l t p) : HCov (addE l s lo hi) t p := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  by_cases hst : s = t
  · subst hst
    unfold addE
    rw [h1]
    simp only
    split
    · exact ⟨a, b, h1, h2, h3⟩
    · exact ⟨min a lo, max b hi, by simp, by omega, by omega⟩
  · refine ⟨a, b, ?_, h2, h3⟩
    unfold addE
    split
    · split
      · exact h1
      · simp [Std.HashMap.getElem?_insert, hst, h1]
    · simp [Std.HashMap.getElem?_insert, hst, h1]

theorem addE_new {l : Lay} {s : HS} {lo hi p : Int} (h1 : lo ≤ p) (h2 : p ≤ hi) :
    HCov (addE l s lo hi) s p := by
  unfold addE
  split
  next e he =>
    split
    · exact ⟨e.1, e.2, he, by omega, by omega⟩
    · exact ⟨min e.1 lo, max e.2 hi, by simp, by omega, by omega⟩
  next => exact ⟨lo, hi, by simp, h1, h2⟩

theorem addI_old {sy : Syms} {m : Machine} {keep : Int → Bool} {e : Ent} {nx : Lay} {i : HIn} {t : HS} {p : Int}
    (h : HCov nx t p) : HCov (addI sy m keep e nx i) t p := by
  unfold addI
  simp only
  split
  · exact addE_old h
  · exact h

theorem inner_old {sy : Syms} {m : Machine} {keep : Int → Bool} {e : Ent} {t : HS} {p : Int} :
    ∀ (is : List HIn) (nx : Lay), HCov nx t p → HCov (is.foldl (addI sy m keep e) nx) t p
  | [], _, h => h
  | _ :: r, _, h => inner_old r _ (addI_old h)

theorem outer_old {sy : Syms} {m : Machine} {is : List HIn} {keep : Int → Bool} {t : HS} {p : Int} :
    ∀ (es : List Ent) (nx : Lay), HCov nx t p →
      HCov (es.foldl (fun nx e => is.foldl (addI sy m keep e) nx) nx) t p
  | [], _, h => h
  | _ :: r, _, h => outer_old r _ (inner_old _ _ h)

theorem inner_new {sy : Syms} {m : Machine} {keep : Int → Bool} {e : Ent} {i : HIn} {p : Int}
    (h1 : e.2.1 ≤ p) (h2 : p ≤ e.2.2) (hk : keep (e.2.1 + 16 * sbyte (hstep sy m e.1 i).v) = true) :
    ∀ (is : List HIn) (nx : Lay), i ∈ is →
      HCov (is.foldl (addI sy m keep e) nx) (hstep sy m e.1 i) (p + 16 * sbyte (hstep sy m e.1 i).v)
  | j :: r, nx, hi => by
    rcases List.mem_cons.1 hi with rfl | h
    · refine inner_old r _ ?_
      unfold addI
      simp only [hk, if_true]
      exact addE_new (by omega) (by omega)
    · exact inner_new h1 h2 hk r _ h

theorem outer_new {sy : Syms} {m : Machine} {is : List HIn} {keep : Int → Bool} {e : Ent} {i : HIn} {p : Int}
    (h1 : e.2.1 ≤ p) (h2 : p ≤ e.2.2) (hk : keep (e.2.1 + 16 * sbyte (hstep sy m e.1 i).v) = true)
    (hi : i ∈ is) :
    ∀ (es : List Ent) (nx : Lay), e ∈ es →
      HCov (es.foldl (fun nx e => is.foldl (addI sy m keep e) nx) nx)
        (hstep sy m e.1 i) (p + 16 * sbyte (hstep sy m e.1 i).v)
  | f :: r, nx, he => by
    rcases List.mem_cons.1 he with rfl | h
    · exact outer_old r _ (inner_new h1 h2 hk is _ hi)
    · exact outer_new h1 h2 hk hi r _ h

/-- a run through a covered state is covered after the frame, if `keep` holds at every `P` up to its own -/
theorem cov_step {sy : Syms} {m : Machine} {is : List HIn} {keep : Int → Bool} {es : List Ent} {x : Pos} {i : HIn}
    (hc : Cov es x) (hi : i ∈ is)
    (hk : ∀ a, a ≤ x.2 → keep (a + 16 * sbyte (hstep sy m x.1 i).v) = true) :
    Cov (stepE sy m is keep es) (adv sy m x i) := by
  obtain ⟨a, b, h1, h2, h3⟩ := hc
  have h := outer_new (sy := sy) (m := m) (is := is) (keep := keep) (e := (x.1, (a, b))) (i := i) (p := x.2)
    h2 h3 (hk a h2) hi es {} h1
  obtain ⟨a', b', h4, h5, h6⟩ := h
  exact ⟨a', b', Std.HashMap.mem_toList_iff_getElem?_eq_some.2 h4, h5, h6⟩

theorem cov_filter {es : List Ent} {x : Pos} {f : Ent → Bool} (hc : Cov es x)
    (hf : ∀ a b, f (x.1, (a, b)) = true) : Cov (es.filter f) x := by
  obtain ⟨a, b, h1, h2, h3⟩ := hc
  exact ⟨a, b, List.mem_filter.2 ⟨h1, hf a b⟩, h2, h3⟩

theorem cov_ne_nil {es : List Ent} {x : Pos} (hc : Cov es x) : es.isEmpty = false := by
  obtain ⟨a, b, h1, _, _⟩ := hc
  cases es with
  | nil => simp at h1
  | cons _ _ => rfl

/-! ## Inputs -/

theorem norm_st (i : HIn) : (norm i).st = i.st := by unfold norm; split <;> rfl
theorem norm_jump (i : HIn) : (norm i).jump = i.jump := by unfold norm; split <;> rfl

theorem norm_mem {i : HIn} (hi : i ∈ inputs) : norm i ∈ inputsN :=
  List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)

theorem hstep_norm {sy : Syms} {m : Machine} (hn : normIdem = true) {i : HIn} (hi : i ∈ inputs) (s : HS) :
    hstep sy m s (norm i) = hstep sy m s i := by
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  unfold hstep
  rw [hid]

theorem adv_norm {sy : Syms} {m : Machine} (hn : normIdem = true) {i : HIn} (hi : i ∈ inputs) (x : Pos) :
    adv sy m x (norm i) = adv sy m x i := by
  unfold adv
  rw [hstep_norm hn hi]

theorem mem_airI {i : HIn} (h : AirIn i) : norm i ∈ airI :=
  List.mem_filter.2 ⟨norm_mem h.1, by simp [norm_st, norm_jump, h.2.1, h.2.2]⟩
theorem mem_gndI {i : HIn} (h : GndIn i) : norm i ∈ gndI :=
  List.mem_filter.2 ⟨norm_mem h.1, by simp [norm_st, norm_jump, h.2.1, h.2.2]⟩
theorem mem_jmpI {i : HIn} (h : JmpIn i) : norm i ∈ jmpI :=
  List.mem_filter.2 ⟨norm_mem h.1, by simp [norm_st, norm_jump, h.2.1, h.2.2]⟩

/-- one frame of a run, in a list that holds the normalized input -/
theorem cov_step_norm {sy : Syms} {m : Machine} (hn : normIdem = true) {is : List HIn} {keep : Int → Bool}
    {es : List Ent} {x : Pos} {i : HIn} (hc : Cov es x) (hi : i ∈ inputs) (hm : norm i ∈ is)
    (hk : ∀ a, a ≤ x.2 → keep (a + 16 * sbyte (hstep sy m x.1 i).v) = true) :
    Cov (stepE sy m is keep es) (adv sy m x i) := by
  rw [← adv_norm hn hi]
  refine cov_step hc hm fun a ha => ?_
  rw [hstep_norm hn hi]
  exact hk a ha

/-! ## Facts about runs -/

theorem go_cons {sy : Syms} {m : Machine} (x : Pos) (i : HIn) (r : List HIn) :
    go sy m x (i :: r) = go sy m (adv sy m x i) r := rfl

theorem go_append {sy : Syms} {m : Machine} : ∀ (a b : List HIn) (x : Pos),
    go sy m x (a ++ b) = go sy m (go sy m x a) b
  | [], _, _ => rfl
  | i :: r, b, x => go_append r b (adv sy m x i)

theorem low_append {sy : Syms} {m : Machine} {cp : Int} : ∀ (a b : List HIn) (x : Pos),
    Low sy m cp x (a ++ b) → Low sy m cp x a ∧ Low sy m cp (go sy m x a) b
  | [], _, _, h => ⟨trivial, h⟩
  | i :: r, b, x, h => by
    obtain ⟨h1, h2⟩ := low_append r b (adv sy m x i) h.2
    exact ⟨⟨h.1, h1⟩, h2⟩

theorem go_snd {sy : Syms} {m : Machine} : ∀ (is : List HIn) (x : Pos),
    (go sy m x is).2 = x.2 + hdist sy m x.1 is
  | [], x => by simp [go, hdist]
  | i :: r, x => by
    have := go_snd (sy := sy) (m := m) r (adv sy m x i)
    simp only [go, hdist]
    rw [this]
    simp only [adv]
    omega

theorem step_facts {sy : Syms} {m : Machine} (F : Facts sy m) {s : HS} (hD : inD sy s = true) {i : HIn}
    (hi : i ∈ inputs) :
    inD sy (hstep sy m s i) = true ∧ phi sy m (hstep sy m s i) ≤ phi sy m s + gFast sy m := by
  have h := F.check s hD i hi
  simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-- the domain is kept and `Φ` grows by at most `g_fast` per frame -/
theorem go_facts {sy : Syms} {m : Machine} (F : Facts sy m) : ∀ (is : List HIn) (x : Pos),
    inD sy x.1 = true → (∀ i ∈ is, i ∈ inputs) →
      inD sy (go sy m x is).1 = true ∧
        phi sy m (go sy m x is).1 ≤ phi sy m x.1 + gFast sy m * (is.length : Int)
  | [], _, hD, _ => ⟨hD, by simp [go]⟩
  | i :: r, x, hD, his => by
    obtain ⟨h1, h2⟩ := step_facts F hD (his i (by simp))
    obtain ⟨h3, h4⟩ := go_facts F r (adv sy m x i) h1 (fun j hj => his j (by simp [hj]))
    refine ⟨h3, ?_⟩
    have h5 : phi sy m (adv sy m x i).1 = phi sy m (hstep sy m x.1 i) := rfl
    simp only [go, List.length_cons]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-- while the bound stays below `θ`, it grows by `g_slow` per frame -/
theorem phi_slow {sy : Syms} {m : Machine} (F : Facts sy m) : ∀ (is : List HIn) (x : Pos) (p : Int),
    J sy m x.1 p → (∀ i ∈ is, i ∈ inputs) → p + gSlow sy m * (is.length : Int) < theta sy →
      phi sy m (go sy m x is).1 ≤ p + gSlow sy m * (is.length : Int)
  | [], _, _, hJ, _, _ => by
    simp only [go, List.length_nil]
    have := hJ.2.1
    omega
  | i :: r, x, p, hJ, his, hlt => by
    have hgs := F.gs_nonneg
    simp only [List.length_cons] at hlt ⊢
    push_cast at hlt ⊢
    rw [Int.mul_add, Int.mul_one] at hlt ⊢
    have hr : 0 ≤ gSlow sy m * (r.length : Int) := Int.mul_nonneg hgs (by omega)
    have hn : nxt sy m p = p + gSlow sy m := by
      unfold nxt
      rw [if_pos (by omega)]
    have hJ' := (step_J F hJ (his i (by simp))).1
    rw [hn] at hJ'
    have h := phi_slow F r (adv sy m x i) (p + gSlow sy m) hJ' (fun j hj => his j (by simp [hj])) (by omega)
    rw [go_cons]
    omega

/-- a state of a run that reaches `θ` within `r` frames passes `keepPhi` -/
theorem keep_of_run {sy : Syms} {m : Machine} (F : Facts sy m) {y : Pos} (hD : inD sy y.1 = true) {is : List HIn}
    (his : ∀ i ∈ is, i ∈ inputs) {r : Nat} (hlen : is.length ≤ r)
    (hth : theta sy ≤ phi sy m (go sy m y is).1) (a : Int × Int) :
    keepPhi sy m r (y.1, a) = true := by
  have hgs := F.gs_nonneg
  have hgf := F.gf_nonneg
  have h1 : gSlow sy m * (is.length : Int) ≤ gSlow sy m * (r : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hgs
  have h3 : gFast sy m * (is.length : Int) ≤ gFast sy m * (r : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hgf
  have h4 := (go_facts F is y hD his).2
  simp only [keepPhi, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  by_cases h : theta sy ≤ Opening.pOf sy m y.1 + gSlow sy m * (r : Int)
  · exact h
  · have h2 := phi_slow F is y _ (Opening.J_pOf hD) his (by omega)
    omega

/-- at the threshold or more, in either direction, `Φ ≥ θ` -/
theorem theta_le_phi {sy : Syms} {m : Machine} (F : Facts sy m) {s : HS}
    (h : sy.AirFastSpeed.toNat ≤ (sbyte s.v).natAbs) : theta sy ≤ phi sy m s := by
  have h1 := phi_ge F s
  have h2 : s.f.toNat < 256 := s.f.toNat_lt
  unfold theta
  unfold V at h1
  omega

/-- each frame moves `P` by at most `16·top` -/
theorem hdist_top {sy : Syms} {m : Machine} (F : Facts sy m) : ∀ (is : List HIn) (s : HS),
    inD sy s = true → (∀ i ∈ is, i ∈ inputs) → hdist sy m s is ≤ 16 * (top sy : Int) * (is.length : Int)
  | [], _, _, _ => by simp [hdist]
  | i :: r, s, hD, his => by
    obtain ⟨h1, _⟩ := step_facts F hD (his i (by simp))
    have ih := hdist_top F r _ h1 (fun j hj => his j (by simp [hj]))
    have hv : sbyte (hstep sy m s i).v ≤ (top sy : Int) := by
      have := h1
      simp only [inD, TopSpeed.inSpeed, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    simp only [hdist, List.length_cons]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-! ## The search covers every run -/

/-- the fall, for a run that is at the threshold or more after `g'` more frames -/
theorem fall_cov {sy : Syms} {m : Machine} (F : TFacts sy m) {G : Nat} (g' : List HIn) (hg' : g'.length ≤ G)
    (hgi : ∀ i ∈ g', i ∈ inputs) :
    ∀ (is : List HIn) (x : Pos) (l : List Ent), Cov l x → inD sy x.1 = true → (∀ i ∈ is, AirIn i) →
      theta sy ≤ phi sy m (go sy m x (is ++ g')).1 →
      Cov (fall sy m G is.length l) (go sy m x is)
  | [], _, _, hc, _, _, _ => hc
  | i :: r, x, l, hc, hD, his, hth => by
    rw [List.cons_append, go_cons] at hth
    have hi := his i (by simp)
    have hDy : inD sy (adv sy m x i).1 = true := (step_facts F.pot hD hi.1).1
    have hall : ∀ j ∈ r ++ g', j ∈ inputs := fun j hj => by
      rcases List.mem_append.1 hj with h | h
      · exact (his j (by simp [h])).1
      · exact hgi j h
    refine fall_cov F g' hg' hgi r (adv sy m x i) _ ?_ hDy (fun j hj => his j (by simp [hj])) hth
    refine cov_filter (cov_step_norm F.normI hc hi.1 (mem_airI hi) fun _ _ => rfl) fun a b => ?_
    exact keep_of_run F.pot hDy hall (by simp only [List.length_append]; omega) hth _

/-- the ground frames: the layer of the frame before the jump passed the checks -/
theorem gnd_walk {sy : Syms} {m : Machine} (F : TFacts sy m) {cp : Int} {L D : Nat} {goal : Int} :
    ∀ (g : List HIn) (r : Nat) (x : Pos) (l : List Ent), g.length ≤ r →
      gndCheck sy m cp L D goal r l = true → Cov l x → inD sy x.1 = true → (∀ i ∈ g, GndIn i) →
      Low sy m cp x g → theta sy ≤ phi sy m (go sy m x g).1 →
      ∃ es, rightOk sy m cp L es = true ∧ leftOk sy m (D + (r - g.length)) goal es = true ∧
        Cov es (go sy m x g)
  | [], 0, _, l, _, hc, hcov, _, _, _, _ => by
    simp only [gndCheck, Bool.and_eq_true] at hc
    exact ⟨l, hc.1, hc.2, hcov⟩
  | [], _ + 1, _, l, _, hc, hcov, _, _, _, _ => by
    simp only [gndCheck, Bool.and_eq_true] at hc
    exact ⟨l, hc.1.1, hc.1.2, hcov⟩
  | i :: g1, r + 1, x, l, hlen, hc, hcov, hD, hg, hlow, hth => by
    rw [go_cons] at hth
    simp only [gndCheck, Bool.and_eq_true] at hc
    simp only [List.length_cons] at hlen
    have hi := hg i (by simp)
    have hDy : inD sy (adv sy m x i).1 = true := (step_facts F.pot hD hi.1).1
    have hgi : ∀ j ∈ g1, j ∈ inputs := fun j hj => (hg j (by simp [hj])).1
    have hcov' : Cov ((stepE sy m gndI (fun q => decide (q < cp)) l).filter (keepPhi sy m r))
        (adv sy m x i) := by
      refine cov_filter (cov_step_norm F.normI hcov hi.1 (mem_gndI hi) fun a ha => ?_) fun a b => ?_
      · have h1 : x.2 + 16 * sbyte (hstep sy m x.1 i).v < cp := hlow.1
        simp only [decide_eq_true_eq]
        omega
      · exact keep_of_run F.pot hDy hgi (by omega) hth _
    obtain ⟨es, h1, h2, h3⟩ := gnd_walk F g1 r (adv sy m x i) _ (by omega) hc.2 hcov' hDy
      (fun j hj => hg j (by simp [hj])) hlow.2 hth
    refine ⟨es, h1, ?_, h3⟩
    rw [show r + 1 - (i :: g1).length = r - g1.length by simp]
    exact h2

/-- the air frames while left of the corner -/
theorem airRun_cov {sy : Syms} {m : Machine} (F : TFacts sy m) {cp : Int} :
    ∀ (k : List HIn) (x : Pos) (l : List Ent), Cov l x → (∀ i ∈ k, AirIn i) → Low sy m cp x k →
      Cov (airRun sy m cp k.length l) (go sy m x k)
  | [], _, _, hc, _, _ => hc
  | i :: r, x, l, hc, hk, hlow => by
    have hi := hk i (by simp)
    refine airRun_cov F r (adv sy m x i) _ ?_ (fun j hj => hk j (by simp [hj])) hlow.2
    refine cov_step_norm F.normI hc hi.1 (mem_airI hi) fun a ha => ?_
    have h1 : x.2 + 16 * sbyte (hstep sy m x.1 i).v < cp := hlow.1
    simp only [decide_eq_true_eq]
    omega

/-- what `rightOk` says -/
theorem right_spec {sy : Syms} {m : Machine} (F : TFacts sy m) {cp : Int} {L : Nat} {es : List Ent} {y : Pos}
    {j : HIn} {k : List HIn} (hr : rightOk sy m cp L es = true) (hc : Cov es y)
    (hv : (sy.AirFastSpeed.toNat : Int) ≤ sbyte y.1.v) (hj : JmpIn j) (hk : ∀ i ∈ k, AirIn i)
    (hkl : k.length = L) (hlow : Low sy m cp y (j :: k)) : False := by
  have h1 : Cov (es.filter fun e => decide ((sy.AirFastSpeed.toNat : Int) ≤ sbyte e.1.v)) y :=
    cov_filter hc fun _ _ => by simp only [decide_eq_true_eq]; exact hv
  have h2 := cov_step_norm (sy := sy) (m := m) F.normI (keep := fun q => decide (q < cp)) h1 hj.1 (mem_jmpI hj)
    fun a ha => by
      have h3 : y.2 + 16 * sbyte (hstep sy m y.1 j).v < cp := hlow.1
      simp only [decide_eq_true_eq]
      omega
  have h4 := airRun_cov F k _ _ h2 hk hlow.2
  rw [hkl] at h4
  have h5 := cov_ne_nil h4
  simp only [rightOk] at hr
  rw [hr] at h5
  exact absurd h5 (by decide)

/-- what `leftOk` says -/
theorem left_spec {sy : Syms} {m : Machine} (F : Facts sy m) {D : Nat} {goal : Int} {es : List Ent} {y : Pos}
    (hl : leftOk sy m D goal es = true) (hc : Cov es y)
    (hv : sbyte y.1.v ≤ -(sy.AirFastSpeed.toNat : Int)) {rest : List HIn} (hin : ∀ i ∈ rest, i ∈ inputs)
    (hlen : rest.length = D) : (go sy m y rest).2 < goal := by
  simp only [leftOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hl
  obtain ⟨hall, hgoal⟩ := hl
  obtain ⟨a, b, h1, h2, h3⟩ := cov_filter (f := fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int)))
    hc (fun _ _ => by simp only [decide_eq_true_eq]; exact hv)
  obtain ⟨⟨h4, h5⟩, h6⟩ := hall _ h1
  simp only at h4 h5 h6
  generalize hH : List.foldl (fun b (e : Ent) => max b e.2.2) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = H at hgoal h5
  generalize hQ : List.foldl (fun b (e : Ent) => max b (Opening.pOf sy m e.1)) (0 : Int)
    (es.filter fun e => decide (sbyte e.1.v ≤ -(sy.AirFastSpeed.toNat : Int))) = Q at hgoal h6
  obtain ⟨hJ1, hJ2, hJ3⟩ := Opening.J_pOf (sy := sy) (m := m) h4
  have hJ : J sy m y.1 Q := ⟨hJ1, by omega, fun h => by have := hJ3 h; omega⟩
  have h7 := dist_le F rest y.1 Q hJ hin
  rw [hlen] at h7
  rw [go_snd]
  omega

/-! ## The theorems -/

/-- the inputs of a run with a jump: the fall, ground frames, the jump frame, the air frames while low -/
structure Takeoff (R : Room) (a g : List HIn) (j : HIn) (k : List HIn) : Prop where
  fall_in : ∀ i ∈ a, AirIn i
  fall_len : a.length = R.A
  gnd_in : ∀ i ∈ g, GndIn i
  jump_in : JmpIn j
  air_in : ∀ i ∈ k, AirIn i
  air_len : k.length = R.L

/-- the search reaches the frame before the jump -/
theorem layer_of {sy : Syms} {m : Machine} (F : TFacts sy m) {R : Room} (hc : roomCheck sy m R = true) {p0 : Int}
    (hp0 : R.P0 ≤ p0) (hp1 : p0 ≤ R.P1) {a g : List HIn} (ha : ∀ i ∈ a, AirIn i) (hal : a.length = R.A)
    (hg : ∀ i ∈ g, GndIn i) (hgl : g.length ≤ R.G)
    (hfast : sy.AirFastSpeed.toNat ≤ (sbyte (go sy m (R.s0, p0) (a ++ g)).1.v).natAbs)
    (hlow : Low sy m R.cp (go sy m (R.s0, p0) a) g) :
    ∃ es, rightOk sy m R.cp R.L es = true ∧ leftOk sy m (R.N - g.length) R.goal es = true ∧
      Cov es (go sy m (R.s0, p0) (a ++ g)) := by
  simp only [roomCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hD, hGN⟩, hgc⟩ := hc
  have hth := theta_le_phi F.pot hfast
  have hgi : ∀ i ∈ g, i ∈ inputs := fun i hi => (hg i hi).1
  have hc0 : Cov [(R.s0, (R.P0, R.P1))] (R.s0, p0) := ⟨R.P0, R.P1, by simp, hp0, hp1⟩
  have hfall := fall_cov F (G := R.G) g hgl hgi a (R.s0, p0) _ hc0 hD ha hth
  rw [hal] at hfall
  have hai : ∀ i ∈ a, i ∈ inputs := fun i hi => (ha i hi).1
  have hD1 := (go_facts F.pot a (R.s0, p0) hD hai).1
  rw [go_append] at hth hfast ⊢
  obtain ⟨es, h1, h2, h3⟩ := gnd_walk F g R.G _ _ hgl hgc hfall hD1 hg hlow hth
  refine ⟨es, h1, ?_, h3⟩
  rw [show R.N - g.length = R.N - R.G + (R.G - g.length) by omega]
  exact h2

/-- moving right at the threshold or more before a jump by the last takeoff searched: `P` does not stay left of
the corner -/
theorem no_right_takeoff {sy : Syms} {m : Machine} (F : TFacts sy m) {R : Room} (hc : roomCheck sy m R = true)
    {p0 : Int} (hp0 : R.P0 ≤ p0) (hp1 : p0 ≤ R.P1) {a g : List HIn} {j : HIn} {k : List HIn}
    (T : Takeoff R a g j k) (hgl : g.length ≤ R.G) (hv : (sy.AirFastSpeed.toNat : Int) ≤ sbyte (go sy m (R.s0, p0) (a ++ g)).1.v)
    (hlow : Low sy m R.cp (go sy m (R.s0, p0) a) (g ++ j :: k)) : False := by
  obtain ⟨h1, h2⟩ := low_append g (j :: k) _ hlow
  obtain ⟨es, h3, _, h4⟩ := layer_of F hc hp0 hp1 T.fall_in T.fall_len T.gnd_in hgl (by omega) h1
  rw [← go_append] at h2
  exact right_spec F h3 h4 hv T.jump_in T.air_in T.air_len h2

/-- moving left at the threshold or more, by the last takeoff searched: any frames up to the goal frame are short
of the goal -/
theorem left_short {sy : Syms} {m : Machine} (F : TFacts sy m) {R : Room} (hc : roomCheck sy m R = true)
    {p0 : Int} (hp0 : R.P0 ≤ p0) (hp1 : p0 ≤ R.P1) {a g : List HIn} (ha : ∀ i ∈ a, AirIn i)
    (hal : a.length = R.A)
    (hg : ∀ i ∈ g, GndIn i) (hgl : g.length ≤ R.G)
    (hv : sbyte (go sy m (R.s0, p0) (a ++ g)).1.v ≤ -(sy.AirFastSpeed.toNat : Int))
    (hlow : Low sy m R.cp (go sy m (R.s0, p0) a) g) {rest : List HIn} (hin : ∀ i ∈ rest, i ∈ inputs)
    (hN : g.length + rest.length = R.N) : (go sy m (R.s0, p0) (a ++ g ++ rest)).2 < R.goal := by
  obtain ⟨es, _, h3, h4⟩ := layer_of F hc hp0 hp1 ha hal hg hgl (by omega) hlow
  rw [go_append]
  exact left_spec F.pot h3 h4 hv hin (by omega)

/-- from a state in the domain left of the corner, `n` frames reach at most `cp − 1 + 16·top·n` -/
theorem late_bound {sy : Syms} {m : Machine} (F : Facts sy m) {cp : Int} {x : Pos} (hD : inD sy x.1 = true)
    (hx : x.2 < cp) {b : List HIn} (hb : ∀ i ∈ b, i ∈ inputs) :
    (go sy m x b).2 ≤ cp - 1 + 16 * (top sy : Int) * (b.length : Int) := by
  have h := hdist_top F b x.1 hD hb
  rw [go_snd]
  omega

theorem low_last {sy : Syms} {m : Machine} {cp : Int} (r : List HIn) :
    ∀ (i : HIn) (x : Pos), Low sy m cp x (i :: r) → (go sy m x (i :: r)).2 < cp := by
  induction r with
  | nil =>
    intro i x h
    rw [go_cons]
    exact h.1
  | cons j r ih =>
    intro i x h
    rw [go_cons]
    exact ih j _ h.2

/-- a takeoff past the last one searched is short of the goal: at the end of the low frames he is left of the
corner, and from there the top speed is not enough -/
theorem late_short {sy : Syms} {m : Machine} (F : TFacts sy m) {R : Room} (hD : inD sy R.s0 = true)
    (hlate : lateOk sy R = true) {p0 : Int} {a g : List HIn} {j : HIn} {k b : List HIn}
    (T : Takeoff R a g j k) (hb : ∀ i ∈ b, i ∈ inputs) (hN : g.length + 1 + R.L + b.length = R.N)
    (hgl : R.G < g.length) (hlow : Low sy m R.cp (go sy m (R.s0, p0) a) (g ++ j :: k)) :
    (go sy m (R.s0, p0) (a ++ g ++ j :: (k ++ b))).2 < R.goal := by
  obtain ⟨_, h1⟩ := low_append g (j :: k) _ hlow
  have h2 := low_last _ _ _ h1
  have hin : ∀ i ∈ a ++ g ++ j :: k, i ∈ inputs := fun i hi => by
    simp only [List.mem_append, List.mem_cons] at hi
    rcases hi with (h | h) | rfl | h
    · exact (T.fall_in i h).1
    · exact (T.gnd_in i h).1
    · exact T.jump_in.1
    · exact (T.air_in i h).1
  have hD1 := (go_facts F.pot (a ++ g ++ j :: k) (R.s0, p0) hD hin).1
  have heq : go sy m (R.s0, p0) (a ++ g ++ j :: (k ++ b)) =
      go sy m (go sy m (R.s0, p0) (a ++ g ++ j :: k)) b := by
    rw [← go_append]
    simp
  have heq2 : go sy m (R.s0, p0) (a ++ g ++ j :: k) =
      go sy m (go sy m (go sy m (R.s0, p0) a) g) (j :: k) := by
    rw [go_append, go_append]
  rw [heq]
  have h3 : (go sy m (R.s0, p0) (a ++ g ++ j :: k)).2 < R.cp := by rw [heq2]; exact h2
  have h4 := late_bound F.pot hD1 h3 hb
  have hL := T.air_len
  have htop : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  have h5 : 16 * (top sy : Int) * (b.length : Int) ≤
      16 * (top sy : Int) * ((R.N - R.G - 2 - R.L : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) htop
  simp only [lateOk, decide_eq_true_eq] at hlate
  omega

/-- every fast takeoff in the room is short of the goal: a jump at the threshold or more, in either direction,
at any frame, with `P` left of the corner from the fall's end through the air frames while low -/
theorem fast_takeoff_short {sy : Syms} {m : Machine} (F : TFacts sy m) {R : Room} (hc : roomCheck sy m R = true)
    (hlate : lateOk sy R = true) {p0 : Int} (hp0 : R.P0 ≤ p0) (hp1 : p0 ≤ R.P1) {a g : List HIn} {j : HIn}
    {k b : List HIn} (T : Takeoff R a g j k) (hb : ∀ i ∈ b, i ∈ inputs)
    (hN : g.length + 1 + R.L + b.length = R.N)
    (hfast : sy.AirFastSpeed.toNat ≤ (sbyte (go sy m (R.s0, p0) (a ++ g)).1.v).natAbs)
    (hlow : Low sy m R.cp (go sy m (R.s0, p0) a) (g ++ j :: k)) :
    (go sy m (R.s0, p0) (a ++ g ++ j :: (k ++ b))).2 < R.goal := by
  have hinp : ∀ i ∈ j :: (k ++ b), i ∈ inputs := fun i hi => by
    simp only [List.mem_cons, List.mem_append] at hi
    rcases hi with rfl | h | h
    · exact T.jump_in.1
    · exact (T.air_in i h).1
    · exact hb i h
  by_cases hgl : g.length ≤ R.G
  · by_cases hv : (sy.AirFastSpeed.toNat : Int) ≤ sbyte (go sy m (R.s0, p0) (a ++ g)).1.v
    · exact (no_right_takeoff F hc hp0 hp1 T hgl hv hlow).elim
    · obtain ⟨h1, _⟩ := low_append g (j :: k) _ hlow
      refine left_short F hc hp0 hp1 T.fall_in T.fall_len T.gnd_in hgl (by omega) h1 hinp ?_
      have := T.air_len
      simp only [List.length_cons, List.length_append]
      omega
  · have hD : inD sy R.s0 = true := by
      simp only [roomCheck, Bool.and_eq_true] at hc
      exact hc.1.1
    exact late_short F hD hlate T hb hN (by omega) hlow

end Smbrta.FastTakeoff
