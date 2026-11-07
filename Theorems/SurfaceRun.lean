import Theorems.FastTakeoff
import Theorems.CastleWalk
import Theorems.PipeEntry

/-!
# Above ground: from control to the flagpole's range

From control above ground (a real run gives the machine there), Mario is stopped, in the same horizontal state as at the 1-1
start. The model is the horizontal frame `Potential.hstep` with ground or air chosen freely on every frame, so walking off a
ledge, landing at any height and every way of jumping are all inputs of the model. `runCheck` follows every input for `N` frames.
For each horizontal state it keeps the largest distance (`hstep` does not read the position), and drops a state once `dbound` says it
cannot get past `X`. Past `N` frames each frame adds at most `16·top`. So at frame `T` he is still left of the pole's range.

A hit is outside `hstep`. A first hit at frame `j ≥ J` is treated by `hit_bound`: up to the hit `dbound`, after it any frames of
`TopSpeed.Frame` (hits included) from a speed of at most 0, by `TopSpeed.chain_reach`. A hit before `J` does not happen: `noHitCheck`
runs the collision routine on the real machine on the states around the start. Page: `SurfaceRun.md`.
-/

namespace Smbrta.SurfaceRun

open Potential
open FastTakeoff (Pos Ent Cov go adv stepE TFacts)
open TopSpeed (top Frame Chain)

/-! ## The search -/

/-- follow a state with `r` frames left, unless it is in the domain and cannot get past `T` -/
def follow (sy : Syms) (m : Machine) (T : Int) (r : Nat) (e : Ent) : Bool :=
  !inD sy e.1 || decide (T + 1 ≤ e.2.2 + dbound sy m (Opening.pOf sy m e.1) r)

/-- every input of every frame: the greatest distance of each kept state is at most `T` -/
def maxCheck (sy : Syms) (m : Machine) (T : Int) : Nat → List Ent → Bool
  | 0, l => l.all fun e => decide (e.2.2 ≤ T)
  | r + 1, l => l.all (fun e => decide (e.2.2 ≤ T)) &&
      maxCheck sy m T r ((stepE sy m inputsN (fun _ => true) l).filter (follow sy m T r))

/-- the search from `s0`: at most `T` within `N` frames -/
def runCheck (sy : Syms) (m : Machine) (s0 : HS) (T : Int) (N : Nat) : Bool :=
  inD sy s0 && maxCheck sy m T N [(s0, (0, 0))]

theorem pOf_nonneg {sy : Syms} {m : Machine} (F : Facts sy m) (s : HS) : 0 ≤ Opening.pOf sy m s := by
  have := Opening.phi_nonneg F s
  unfold Opening.pOf
  split <;> omega

/-- what the search says about a run through a covered state -/
theorem maxCheck_spec {sy : Syms} {m : Machine} {T : Int} (F : TFacts sy m) :
    ∀ (r : Nat) (l : List Ent) (x : Pos) (is : List HIn), maxCheck sy m T r l = true → Cov l x →
      (∀ i ∈ is, i ∈ inputs) → is.length ≤ r → (go sy m x is).2 ≤ T
  | 0, l, x, [], h, hc, _, _ => by
    obtain ⟨a, b, h1, _, h3⟩ := hc
    simp only [maxCheck, List.all_eq_true, decide_eq_true_eq] at h
    have h4 := h _ h1
    simp only at h4
    show x.2 ≤ T
    omega
  | 0, _, _, _ :: _, _, _, _, hl => by simp at hl
  | r + 1, l, x, [], h, hc, _, _ => by
    obtain ⟨a, b, h1, _, h3⟩ := hc
    simp only [maxCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have h4 := h.1 _ h1
    simp only at h4
    show x.2 ≤ T
    omega
  | r + 1, l, x, i :: rest, h, hc, his, hl => by
    simp only [maxCheck, Bool.and_eq_true] at h
    have hi : i ∈ inputs := his i (by simp)
    have hrest : ∀ j ∈ rest, j ∈ inputs := fun j hj => his j (by simp [hj])
    have hlen : rest.length ≤ r := by simp at hl; omega
    have hc' : Cov (stepE sy m inputsN (fun _ => true) l) (adv sy m x i) :=
      FastTakeoff.cov_step_norm F.normI hc hi (FastTakeoff.norm_mem hi) fun _ _ => rfl
    obtain ⟨a, b, h1, h2, h3⟩ := hc'
    rw [FastTakeoff.go_cons]
    by_cases hf : follow sy m T r ((adv sy m x i).1, (a, b)) = true
    · exact maxCheck_spec F r _ (adv sy m x i) rest h.2 ⟨a, b, List.mem_filter.2 ⟨h1, hf⟩, h2, h3⟩ hrest hlen
    · simp only [follow, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, not_or,
        Bool.not_eq_false] at hf
      obtain ⟨hD, hlt⟩ := hf
      have hd := dist_le F.pot rest _ _ (Opening.J_pOf hD) hrest
      have hm := Opening.dbound_mono F.pot rest.length (r - rest.length) _ (pOf_nonneg F.pot (adv sy m x i).1)
      rw [show rest.length + (r - rest.length) = r by omega] at hm
      rw [FastTakeoff.go_snd]
      omega

theorem hdist_append {sy : Syms} {m : Machine} (a b : List HIn) (s : HS) :
    hdist sy m s (a ++ b) = hdist sy m s a + hdist sy m (go sy m (s, 0) a).1 b := by
  have h := FastTakeoff.go_append (sy := sy) (m := m) a b (s, 0)
  have h1 := FastTakeoff.go_snd (sy := sy) (m := m) (a ++ b) (s, 0)
  have h2 := FastTakeoff.go_snd (sy := sy) (m := m) b (go sy m (s, 0) a)
  have h3 := FastTakeoff.go_snd (sy := sy) (m := m) a (s, 0)
  rw [h, h2, h3] at h1
  simp only at h1
  omega

/-- within `N` frames at most `T` -/
theorem within_of_check {sy : Syms} {m : Machine} {s0 : HS} {T : Int} {N : Nat} (F : TFacts sy m)
    (h : runCheck sy m s0 T N = true) {is : List HIn} (hi : ∀ i ∈ is, i ∈ inputs) (hl : is.length ≤ N) :
    hdist sy m s0 is ≤ T := by
  simp only [runCheck, Bool.and_eq_true] at h
  have h1 := maxCheck_spec F N _ (s0, 0) is h.2 ⟨0, 0, by simp, Int.le_refl _, Int.le_refl _⟩ hi hl
  rw [FastTakeoff.go_snd] at h1
  simp only at h1
  omega

/-- past `N` frames, each frame adds at most `16·top` -/
theorem after_of_check {sy : Syms} {m : Machine} {s0 : HS} {T : Int} {N : Nat} (F : TFacts sy m)
    (h : runCheck sy m s0 T N = true) {is : List HIn} (hi : ∀ i ∈ is, i ∈ inputs) {k : Nat}
    (hl : is.length = N + k) : hdist sy m s0 is ≤ T + 16 * (top sy : Int) * (k : Int) := by
  have hD : inD sy s0 = true := by
    simp only [runCheck, Bool.and_eq_true] at h
    exact h.1
  have ht : ∀ i ∈ is.take N, i ∈ inputs := fun i hm => hi i (List.mem_of_mem_take hm)
  have hd : ∀ i ∈ is.drop N, i ∈ inputs := fun i hm => hi i (List.mem_of_mem_drop hm)
  have h1 := within_of_check F h ht (by simp; omega)
  have h2 := FastTakeoff.go_facts F.pot (is.take N) (s0, 0) hD ht
  have h3 := FastTakeoff.hdist_top F.pot (is.drop N) _ h2.1 hd
  have hlen : (is.drop N).length = k := by simp [hl]
  rw [hlen] at h3
  have h4 := hdist_append (sy := sy) (m := m) (is.take N) (is.drop N) s0
  rw [List.take_append_drop] at h4
  omega

/-! ## A hit -/

/-- where a first hit on frame `j` leaves him, relative to the start: a hit moving right or stopped ends 1 px behind the frame's
move; a hit moving left or stopped ends at most 1 px past the frame before -/
def hitPos (sy : Syms) (m : Machine) (p0 : Int) (j : Nat) : Int :=
  max (dbound sy m p0 j - 256) (dbound sy m p0 (j - 1) + 256)

/-- each first hit on the frames `J .. N`, with the frames after it by `TopSpeed.reach`, stays within the bound at frame `N + E` -/
def hitTable (sy : Syms) (m : Machine) (p0 X : Int) (N E J : Nat) : Bool :=
  (List.range (N + 1)).all fun j => decide (j < J) ||
    decide (hitPos sy m p0 j + TopSpeed.reach (top sy) (amax sy m) 255 (N + E - j) ≤ X + 16 * (top sy : Int) * (E : Int))

theorem reach_le_top {t a : Int} (h16 : 16 ≤ t) :
    ∀ (n : Nat) (w : Int), TopSpeed.reach t a w n ≤ 16 * t * (n : Int)
  | 0, w => by simp [TopSpeed.reach]
  | n + 1, w => by
    have ih := reach_le_top (a := a) h16 n (w + a)
    have hadv : TopSpeed.adv t a w ≤ 16 * t := by unfold TopSpeed.adv; omega
    simp only [TopSpeed.reach]
    push_cast
    rw [Int.mul_add, Int.mul_one]
    omega

/-- The frames up to the first hit follow `hstep` (`pre`, then `i`); the frame `i` ends with a hit; the frames after it are any `Frame`s
(so they may hit again), the first with a speed of at most 0 and a fraction. If the first hit is on frame `J` or later, at frame
`N + E + k` the position is at most `X + 16·top·(E + k)` past the start. -/
theorem hit_bound {sy : Syms} {m : Machine} {s0 : HS} {X : Int} {N E J : Nat} (F : TFacts sy m)
    (h : runCheck sy m s0 X N = true) (ht : hitTable sy m (Opening.pOf sy m s0) X N E J = true)
    (h16 : 16 ≤ (top sy : Int)) (h255 : 255 ≤ amax sy m)
    {pre : List HIn} {i : HIn} (hpre : ∀ j ∈ pre, j ∈ inputs) (hi : i ∈ inputs) (hj : J ≤ pre.length + 1)
    {P0 Pj : Int}
    (hit : Pj ≤ P0 + hdist sy m s0 (pre ++ [i]) - 256 ∨ Pj ≤ P0 + hdist sy m s0 pre + 256)
    (f : Frame (top sy) (amax sy m)) (fs : List (Frame (top sy) (amax sy m))) (hc : Chain (f :: fs))
    (hv : -(top sy : Int) ≤ f.v ∧ f.v ≤ 0) (hf : f.f ≤ 255) (hP : f.P = Pj)
    {k : Nat} (hlen : pre.length + 1 + (fs.length + 1) = N + E + k) :
    (fs.getLastD f).P' ≤ P0 + X + 16 * (top sy : Int) * ((E + k : Nat) : Int) := by
  have hD : inD sy s0 = true := by
    simp only [runCheck, Bool.and_eq_true] at h
    exact h.1
  have hall : ∀ j ∈ pre ++ [i], j ∈ inputs := fun j hm => by
    rcases List.mem_append.1 hm with h1 | h1
    · exact hpre j h1
    · rw [List.mem_singleton.1 h1]
      exact hi
  have hreach := TopSpeed.chain_reach (w := 255) h16 (by omega) fs f hc ⟨hv.1, by omega⟩ (by omega)
  have htop : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  have eEk : 16 * (top sy : Int) * ((E + k : Nat) : Int) = 16 * (top sy : Int) * (E : Int) + 16 * (top sy : Int) * (k : Int) := by
    push_cast
    rw [Int.mul_add]
  by_cases hjN : pre.length + 1 ≤ N
  · -- the hit comes within `N` frames: the table
    have hd1 := dist_le F.pot pre s0 _ (Opening.J_pOf hD) hpre
    have hd2 := dist_le F.pot (pre ++ [i]) s0 _ (Opening.J_pOf hD) hall
    simp only [List.length_append, List.length_singleton] at hd2
    have hrow : hitPos sy m (Opening.pOf sy m s0) (pre.length + 1) +
        TopSpeed.reach (top sy) (amax sy m) 255 (N + E - (pre.length + 1)) ≤ X + 16 * (top sy : Int) * (E : Int) := by
      simp only [hitTable, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ht
      rcases ht (pre.length + 1) (List.mem_range.2 (by omega)) with h1 | h1
      · omega
      · exact h1
    have hsplit := TopSpeed.reach_add (top := (top sy : Int)) (amax := amax sy m)
      (N + E - (pre.length + 1)) k 255
    rw [show N + E - (pre.length + 1) + k = fs.length + 1 by omega] at hsplit
    have hk := reach_le_top (a := amax sy m) h16 k (255 + amax sy m * ((N + E - (pre.length + 1) : Nat) : Int))
    have hpos : Pj - P0 ≤ hitPos sy m (Opening.pOf sy m s0) (pre.length + 1) := by
      unfold hitPos
      simp only [Nat.add_sub_cancel]
      rcases hit with h1 | h1 <;> omega
    omega
  · -- the hit comes past `N` frames: the bound of the search, and at most `16·top` per frame after
    obtain ⟨d, hd⟩ : ∃ d, pre.length = N + d := ⟨pre.length - N, by omega⟩
    have h1 := after_of_check F h hpre hd
    have h2 := after_of_check F h hall (k := d + 1) (by simp; omega)
    have hk : E + k = d + 1 + (fs.length + 1) := by omega
    have hr := reach_le_top (a := amax sy m) h16 (fs.length + 1) 255
    have e1 : 16 * (top sy : Int) * ((E + k : Nat) : Int) =
        16 * (top sy : Int) * ((d + 1 : Nat) : Int) + 16 * (top sy : Int) * ((fs.length + 1 : Nat) : Int) := by
      rw [hk]
      push_cast
      rw [← Int.mul_add]
    have e2 : 16 * (top sy : Int) * ((d + 1 : Nat) : Int) = 16 * (top sy : Int) * (d : Int) + 16 * (top sy : Int) := by
      push_cast
      rw [Int.mul_add, Int.mul_one]
    rcases hit with h3 | h3 <;> omega

/-- A wall behind him while he moves right blocks Left on the next frame, and nothing else. With Left blocked, a frame moving right is
the same frame as without, or it stops him (Left on the ground at a low speed stops a skid, and the blocked Left does not start him moving
left). A stop is a first hit for `hit_bound`: speed 0, and `P` does not move. Checked on these fractions. -/
def maskSame (sy : Syms) (m : Machine) : Bool :=
  let mb := poke m sy.Player_CollisionBits 0xFD
  (List.range (top sy)).all fun v => [(0 : UInt8), 128, 255].all fun f => facings.all fun fd => (rsVals sy).all fun rs =>
    inputsN.all fun i =>
      let s : HS := { v := (v + 1).toUInt8, f, fd, md := 1, rs }
      let t := hstep sy mb s i
      t == hstep sy m s i || (t.v == 0 && t.f == 0)

/-! ## No hit around the start -/

/-- the collision routine on `m`, with Mario at `x`, `y`, the speed `v` and the fall speed and state `(vy, st)`, moves nothing sideways
and blocks nothing -/
def noHitAt (sy : Syms) (m : Machine) (x y v vy st : UInt8) : Bool :=
  let m1 := poke m sy.Player_X_Position x
  let m1 := poke m1 sy.Player_Y_Position y
  let m1 := poke m1 sy.Player_X_Speed v
  let m1 := poke m1 sy.Player_MovingDir (if v < 0x80 then 1 else 2)
  let m1 := poke m1 sy.Player_Y_Speed vy
  let m1 := poke m1 sy.Player_State st
  let r := runSub m1 sy.PlayerBGCollision 0 0 0
  peek r sy.Player_X_Position == x && peek r sy.Player_X_Speed == v && peek r sy.Player_CollisionBits == 0xFF

/-- fall speeds and states: rising at the speeds of a jump, falling up to the top fall speed -/
def vyStates (sy : Syms) : List (UInt8 × UInt8) :=
  (List.range (256 - sy.FastJumpSpeed.toNat)).map (fun i => ((sy.FastJumpSpeed.toNat + i).toUInt8, (1 : UInt8))) ++
    (List.range (sy.MaxFallSpeed.toNat + 1)).flatMap fun vy => [(vy.toUInt8, (1 : UInt8)), (vy.toUInt8, 2)]

/-- speeds in both directions and stopped: the routine reads a speed only by its sign -/
def someSpeeds : List UInt8 := [0, 1, 8, 0xFF, 0xF8]

/-- on the machine `m`, within `dx` px of its position and up to `dy` px above its height, nothing is hit -/
def noHitCheck (sy : Syms) (m : Machine) (dx dy : Nat) : Bool :=
  let x0 := (peek m sy.Player_X_Position).toNat
  let y0 := (peek m sy.Player_Y_Position).toNat
  (List.range (2 * dx + 1)).all fun a =>
    let x := (x0 + a - dx).toUInt8
    someSpeeds.all (fun v => noHitAt sy m x y0.toUInt8 v 0 0) &&
      (List.range (dy + 1)).all fun b =>
        let y := (y0 - b).toUInt8
        someSpeeds.all fun v => (vyStates sy).all fun (vy, st) => noHitAt sy m x y v vy st

/-! ## The start and the goal -/

/-- the machine at control above ground: the first part of `CastleWalk.route`, up to `n` frames -/
def above (m0 : Machine) (n : Nat) : Machine := PipeTransition.run m0 (CastleWalk.route.take n)

/-- the object pairs before the flagpole's, in the level data -/
def beforePole (sy : Syms) (m : Machine) : List (UInt8 × UInt8) :=
  (PipeEntry.pairs sy m PipeEntry.maxPairs).takeWhile fun p => p.1 != sy.FlagColumnByte.toUInt8

/-- the flagpole's pair and the pairs after it -/
def fromPole (sy : Syms) (m : Machine) : List (UInt8 × UInt8) :=
  (PipeEntry.pairs sy m PipeEntry.maxPairs).dropWhile fun p => p.1 != sy.FlagColumnByte.toUInt8

/-- the flagpole's page: second bytes with bit 7 set among the pairs up to and including its own -/
def polePage (sy : Syms) (m : Machine) : Nat :=
  (beforePole sy m).countP PipeEntry.pageBit + ((fromPole sy m).head?.map PipeEntry.pageBit == some true).toNat

/-- the pole's pair is found and no object before it sets the page directly -/
def poleLevelOk (sy : Syms) (m : Machine) : Bool :=
  (fromPole sy m).head?.isSome && (beforePole sy m).all fun p => !PipeEntry.pageControl p

/-- the left end of the pole's range -/
def poleP (sy : Syms) (m : Machine) : Int :=
  256 * (256 * (polePage sy m : Int) + ((PoleGrab.colX sy - 10 : Nat) : Int))

/-! ## A run of the model that reaches the bound -/

/-- on the ground, no jump -/
def gnd (joy rt : UInt8) : HIn := { st := 0, jump := false, joy, rt }
/-- in the air -/
def air (joy : UInt8) : HIn := { st := 1, jump := false, joy, rt := 0 }

/-- inputs of the model that reach the bound. Ground and air alternate as no real run can. -/
def freeWitness : List HIn :=
  [gnd 3 0] ++ List.replicate 8 (air 1) ++
  [gnd 1 1, gnd 3 0, gnd 3 0, gnd 1 1, gnd 3 0, gnd 1 1, gnd 3 0, gnd 3 0, gnd 1 1, gnd 3 0, gnd 1 1, gnd 3 0, gnd 1 1, gnd 2 0] ++
  List.replicate 9 (air 1) ++ [gnd 1 1, gnd 2 0, gnd 1 1] ++ List.replicate 5 (air 0)

/-! ## The whole check -/

/-- everything the theorem needs: `n` frames of the route up to control; the search of `N` frames with the bound `X`; `E` the frames
from there to the end of `freeWitness`; `T` the frames to the last frame that counts; `J` the first frame of a hit that the arithmetic
covers; `dx`, `dy` the box around the start -/
def allCheck (sy : Syms) (m0 : Machine) (n : Nat) (X : Int) (N E T J dx dy : Nat) : Bool :=
  let s0 := startHS sy m0
  let a := above m0 n
  controllable sy a && decide (startHS sy a = s0) && decide (peek a sy.AreaType = peek m0 sy.AreaType) &&
    decide (peek a sy.Player_CollisionBits = peek m0 sy.Player_CollisionBits) &&
    runCheck sy m0 s0 X N && decide (hdist sy m0 s0 freeWitness = X + 16 * (top sy : Int) * (E : Int)) &&
    decide (freeWitness.length = N + E) && (freeWitness.all fun i => inputs.contains i) &&
    poleLevelOk sy m0 && decide ((peek (CastleWalk.beside m0) sy.Player_PageLoc).toNat = polePage sy m0) &&
    decide (posP sy a + X + 16 * (top sy : Int) * ((T - N : Nat) : Int) + 32 < poleP sy m0) &&
    hitTable sy m0 (Opening.pOf sy m0 s0) X N E J && noHitCheck sy a dx dy && maskSame sy m0

/-- What the theorem says. `s₀` is the horizontal state of the 1-1 start. -/
structure Statement (sy : Syms) (m0 : Machine) (n : Nat) (X : Int) (N E T J dx dy : Nat) : Prop where
  /-- a real run has control there, in the state `s₀` -/
  start : controllable sy (above m0 n) = true ∧ startHS sy (above m0 n) = startHS sy m0
  /-- the search -/
  search : runCheck sy m0 (startHS sy m0) X N = true
  /-- every input of the model, within `N` frames: at most `X` -/
  within : ∀ is : List HIn, (∀ i ∈ is, i ∈ inputs) → is.length ≤ N → hdist sy m0 (startHS sy m0) is ≤ X
  /-- past `N` frames, at most `16·top` more per frame -/
  after : ∀ is : List HIn, (∀ i ∈ is, i ∈ inputs) → ∀ k, is.length = N + k →
    hdist sy m0 (startHS sy m0) is ≤ X + 16 * (top sy : Int) * (k : Int)
  /-- inputs of the model reach the bound at `N + E` frames: the bound is exact in the model -/
  reached : (∀ i ∈ freeWitness, i ∈ inputs) ∧ freeWitness.length = N + E ∧
    hdist sy m0 (startHS sy m0) freeWitness = X + 16 * (top sy : Int) * (E : Int)
  /-- at frame `T` the bound is left of the pole's range, by more than the 32 of `PoleGrab.no_grab_far` -/
  gap : posP sy (above m0 n) + X + 16 * (top sy : Int) * ((T - N : Nat) : Int) + 32 < poleP sy m0
  /-- so every input of the model, up to frame `T`, is left of it -/
  short : ∀ is : List HIn, (∀ i ∈ is, i ∈ inputs) → is.length ≤ T →
    posP sy (above m0 n) + hdist sy m0 (startHS sy m0) is + 32 < poleP sy m0
  /-- the table for a first hit from frame `J` on -/
  hits : hitTable sy m0 (Opening.pOf sy m0 (startHS sy m0)) X N E J = true
  /-- the collision routine hits nothing around the start -/
  noHit : noHitCheck sy (above m0 n) dx dy = true
  /-- a wall behind him while he moves right changes nothing, or stops him -/
  mask : maskSame sy m0 = true
  /-- the level data's page of the pole is the page beside its base block on a real run -/
  page : (peek (CastleWalk.beside m0) sy.Player_PageLoc).toNat = polePage sy m0

theorem statement_of_check {sy : Syms} {m0 : Machine} {n : Nat} {X : Int} {N E T J dx dy : Nat} (F : TFacts sy m0)
    (hN : N ≤ T) (h : allCheck sy m0 n X N E T J dx dy = true) : Statement sy m0 n X N E T J dx dy := by
  simp only [allCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have htop : (0 : Int) ≤ 16 * (top sy : Int) := by omega
  refine ⟨⟨h1, h2⟩, h3, fun is hi hl => within_of_check F h3 hi hl, fun is hi k hl => after_of_check F h3 hi hl,
    ⟨h6, h5, h4⟩, h8, fun is hi hl => ?_, h9, h10, h11, h7⟩
  by_cases hlN : is.length ≤ N
  · have h12 := within_of_check F h3 hi hlN
    have h13 : 0 ≤ 16 * (top sy : Int) * ((T - N : Nat) : Int) := Int.mul_nonneg htop (by omega)
    omega
  · obtain ⟨k, hk⟩ : ∃ k, is.length = N + k := ⟨is.length - N, by omega⟩
    have h12 := after_of_check F h3 hi hk
    have h13 : 16 * (top sy : Int) * (k : Int) ≤ 16 * (top sy : Int) * ((T - N : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) htop
    omega

/-- with a first hit from frame `J` on, at frame `T` he is still left of the pole's range, by more than the 32 of `PoleGrab.no_grab_far` -/
theorem hit_short {sy : Syms} {m0 : Machine} {n : Nat} {X : Int} {N E T J dx dy : Nat} (F : TFacts sy m0)
    (S : Statement sy m0 n X N E T J dx dy) (hNE : N + E ≤ T) (h16 : 16 ≤ (top sy : Int)) (h255 : 255 ≤ amax sy m0)
    {pre : List HIn} {i : HIn} (hpre : ∀ j ∈ pre, j ∈ inputs) (hi : i ∈ inputs) (hj : J ≤ pre.length + 1) {Pj : Int}
    (hit : Pj ≤ posP sy (above m0 n) + hdist sy m0 (startHS sy m0) (pre ++ [i]) - 256 ∨
      Pj ≤ posP sy (above m0 n) + hdist sy m0 (startHS sy m0) pre + 256)
    (f : Frame (top sy) (amax sy m0)) (fs : List (Frame (top sy) (amax sy m0))) (hc : Chain (f :: fs))
    (hv : -(top sy : Int) ≤ f.v ∧ f.v ≤ 0) (hf : f.f ≤ 255) (hP : f.P = Pj)
    (hlen : pre.length + 1 + (fs.length + 1) = T) :
    (fs.getLastD f).P' + 32 < poleP sy m0 := by
  have h := hit_bound (k := T - N - E) F S.search S.hits h16 h255 hpre hi hj hit f fs hc hv hf hP (by omega)
  have hg := S.gap
  rw [show E + (T - N - E) = T - N by omega] at h
  omega

/-- the same for a first hit on frame `T` itself, with no frame after it -/
theorem hit_last {sy : Syms} {m0 : Machine} {n : Nat} {X : Int} {N E T J dx dy : Nat}
    (S : Statement sy m0 n X N E T J dx dy) (hNT : N < T) (h16 : 16 ≤ (top sy : Int))
    {pre : List HIn} {i : HIn} (hpre : ∀ j ∈ pre, j ∈ inputs) (hi : i ∈ inputs) {Pj : Int}
    (hit : Pj ≤ posP sy (above m0 n) + hdist sy m0 (startHS sy m0) (pre ++ [i]) - 256 ∨
      Pj ≤ posP sy (above m0 n) + hdist sy m0 (startHS sy m0) pre + 256)
    (hlen : pre.length + 1 = T) : Pj + 32 < poleP sy m0 := by
  have hall : ∀ j ∈ pre ++ [i], j ∈ inputs := fun j hm => by
    rcases List.mem_append.1 hm with h1 | h1
    · exact hpre j h1
    · rw [List.mem_singleton.1 h1]
      exact hi
  obtain ⟨d, hd⟩ : ∃ d, pre.length = N + d := ⟨pre.length - N, by omega⟩
  have h1 := S.after pre hpre d hd
  have h2 := S.after (pre ++ [i]) hall (d + 1) (by simp; omega)
  have hg := S.gap
  rw [show T - N = d + 1 by omega] at hg
  have e : 16 * (top sy : Int) * ((d + 1 : Nat) : Int) = 16 * (top sy : Int) * (d : Int) + 16 * (top sy : Int) := by
    push_cast
    rw [Int.mul_add, Int.mul_one]
  rcases hit with h3 | h3 <;> omega

end Smbrta.SurfaceRun
