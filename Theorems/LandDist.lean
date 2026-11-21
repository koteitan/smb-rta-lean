import Theorems.AirCap
import Theorems.FastTakeoff

/-!
# The distance of the frames, by a table

`AirCap.capDist` bounds the distance of `n` frames from a state below the air threshold by the potential `Φ`. Here the bound is a table
`T[k][s]` for every state `s` of the horizontal model and `k ≤ n` frames, made by taking the best input on each frame (`table`).

One pass of `hstep` over every state and input (`trans`) gives, for each state, its entry: the state itself and, for each input, whether
it is an air frame's, the distance of the frame and the number of the next state. Every entry of the array is the entry of its own state
(`inv_trans`), and `trOk` checks that each state sits at its number, so the checks below read the frames from the array and never run
`hstep` again. `layerOk` asks, for every state and input: `16·v' + X[s'] ≤ Y[s]`. From it, `dist_table`: any `k ≤ n` frames from `s` move
`P` by at most `T[k][s]`, and `dist_air`: `a` air frames and then frames bounded by `T0` move it by at most `X[a][s]`.

`search` follows `hstep` from the room's first frame with `FastTakeoff.stepE` (the least and the greatest `P` of each state): the air frames of the fall, the
jump frame and more air frames, with the greatest `P` cut to the corner less one from the jump frame on (`search_cov`: the run is covered when it stays left of the
corner there). `slowCheck` asks, for each slow pair and each number of frames after the landing, the bound from the corner less one with air frames at the air
speed and the table (`looseOk`), or the bound from the search's states with air frames and the table (`exactOk`). `slow_short`: a big player's slow takeoff on the
first frame after the fall is short of the goal (`RoomJoin.landed_short`, `RoomJoin.Checks.slowLand`). There is no game data in this file.
Page: `1-1/c-7-14-2-LandDist.md`.
-/

namespace Smbrta.LandDist

open Potential
open TopSpeed (top speedsB bytes)
open AirCap (capped isAir)

/-- every state of the domain -/
def states (sy : Syms) : List HS := facings.flatMap fun fd => statesFd sy fd

/-- a number for each state -/
def key (sy : Syms) (s : HS) : Nat :=
  ((((sbyte s.v + (top sy : Int)).toNat * 256 + s.f.toNat) * 4 + s.fd.toNat % 4) * 4 + s.md.toNat % 4) * 2 +
    (if s.rs == 0 then 0 else 1)

/-- the numbers of the states are below this -/
def size (sy : Syms) : Nat := (2 * top sy + 1) * 8192

/-- the entry of a state: the state, and for each input whether it is an air frame's, the distance of the frame and the next state's number -/
abbrev Ent := HS × List (Bool × Int × Nat)

def entry (sy : Syms) (m : Machine) (s : HS) : Ent :=
  (s, inputsN.map fun i => let t := hstep sy m s i; (isAir i, 16 * sbyte t.v, key sy t))

abbrev Tr := Array Ent

/-- the entries of all states, each at its number: one frame of `hstep` for each state and input -/
def trans (sy : Syms) (m : Machine) : Tr :=
  (states sy).foldl (fun a s => a.set! (key sy s) (entry sy m s)) (Array.replicate (size sy) (entry sy m default))

/-- every entry of the array is the entry of its own state -/
def Inv (sy : Syms) (m : Machine) (tr : Tr) : Prop := ∀ j (h : j < tr.size), tr[j] = entry sy m tr[j].1

theorem inv_foldl {sy : Syms} {m : Machine} : ∀ (l : List HS) (a : Tr), Inv sy m a →
    Inv sy m (l.foldl (fun a s => a.set! (key sy s) (entry sy m s)) a)
  | [], _, h => h
  | s :: l, a, h => by
    apply inv_foldl l
    intro j hj
    have hj' : j < a.size := by simpa using hj
    simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hj']
    split
    · rfl
    · exact h j hj'

theorem inv_trans (sy : Syms) (m : Machine) : Inv sy m (trans sy m) :=
  inv_foldl _ _ fun j h => by simp only [Array.getElem_replicate]; rfl

/-- each state sits at its number -/
def trOk (sy : Syms) (tr : Tr) : Bool :=
  (states sy).all fun s => decide (key sy s < tr.size) && decide ((tr[key sy s]!).1 = s)

theorem mem_states {sy : Syms} (hsp : speedsComplete sy = true) {s : HS} (hD : inD sy s = true) : s ∈ states sy := by
  obtain ⟨v, f, fd, md, rs⟩ := s
  simp only [inD, Bool.and_eq_true, List.contains_iff_mem] at hD
  obtain ⟨⟨⟨hv, hfd⟩, hmd⟩, hrs⟩ := hD
  have hvs : v ∈ speedsB sy := by
    simp only [speedsComplete, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_iff_mem] at hsp
    rcases hsp v (mem_bytes v) with h | h
    · rw [h] at hv; exact absurd hv (by decide)
    · exact h
  exact List.mem_flatMap.2 ⟨fd, hfd, List.mem_flatMap.2 ⟨v, hvs, List.mem_flatMap.2 ⟨f, mem_bytes f,
    List.mem_flatMap.2 ⟨md, hmd, List.mem_map.2 ⟨rs, hrs, rfl⟩⟩⟩⟩⟩

theorem entry_of {sy : Syms} {m : Machine} {tr : Tr} (hinv : Inv sy m tr) (hok : trOk sy tr = true) {s : HS}
    (hs : s ∈ states sy) : tr[key sy s]! = entry sy m s := by
  simp only [trOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h1, h2⟩ := hok s hs
  rw [getElem!_pos tr (key sy s) h1] at h2 ⊢
  rw [hinv _ h1, h2]

theorem hstep_norm {sy : Syms} {m : Machine} (s : HS) (i : HIn) (h : norm (norm i) = norm i) :
    hstep sy m s (norm i) = hstep sy m s i := by
  unfold hstep; rw [h]

/-- one more frame from each state: the best of all inputs, or (`air`) of the inputs of air frames -/
def layer (air : Bool) (tr : Tr) (keys : List Nat) (sz : Nat) (prev : Array Int) : Array Int :=
  keys.foldl (fun a k => a.set! k ((tr[k]!).2.foldl (fun b p => if air && !p.1 then b else max b (p.2.1 + prev[p.2.2]!)) (-1000000)))
    (Array.replicate sz 0)

/-- `Y` bounds one more frame over `X` from every state, for every input (or every input of an air frame) -/
def layerOk (sy : Syms) (air : Bool) (tr : Tr) (X Y : Array Int) : Bool :=
  (states sy).all fun s => (tr[key sy s]!).2.all fun p => (air && !p.1) || decide (p.2.1 + X[p.2.2]! ≤ Y[key sy s]!)

/-- one frame, read from the array -/
theorem step_le {sy : Syms} {m : Machine} {tr : Tr} (hinv : Inv sy m tr) (hok : trOk sy tr = true)
    (hsp : speedsComplete sy = true) (hn : normIdem = true) {air : Bool} {X Y : Array Int}
    (hl : layerOk sy air tr X Y = true) {s : HS} (hD : inD sy s = true) {i : HIn} (hi : i ∈ inputs)
    (ha : air = true → isAir i = true) :
    16 * sbyte (hstep sy m s i).v + X[key sy (hstep sy m s i)]! ≤ Y[key sy s]! := by
  have hm := mem_states hsp hD
  have hid : norm (norm i) = norm i := by
    simp only [normIdem, List.all_eq_true, beq_iff_eq] at hn
    exact hn i hi
  have hin : norm i ∈ inputsN := List.mem_eraseDups.2 (List.mem_map.2 ⟨i, hi, rfl⟩)
  have he := entry_of hinv hok hm
  simp only [layerOk, List.all_eq_true] at hl
  have hmem : (isAir (norm i), 16 * sbyte (hstep sy m s (norm i)).v, key sy (hstep sy m s (norm i))) ∈ (tr[key sy s]!).2 := by
    rw [he]
    exact List.mem_map.2 ⟨norm i, hin, rfl⟩
  have h := hl s hm _ hmem
  rw [hstep_norm s i hid, AirCap.isAir_norm] at h
  cases air with
  | false => simpa using h
  | true =>
    have h2 := ha rfl
    simpa [h2] using h

/-- the table of `n` frames: no bound is negative for no frames, and each layer bounds one more frame over all inputs -/
def tableOk (sy : Syms) (tr : Tr) (T : Array (Array Int)) (n : Nat) : Bool :=
  (states sy).all (fun s => decide (0 ≤ T[0]![key sy s]!)) && (List.range n).all fun k => layerOk sy false tr T[k]! T[k + 1]!

/-- **The table bounds the distance**: from a state of the domain, `k ≤ n` frames move `P` by at most `T[k][s]` -/
theorem dist_table {sy : Syms} {m : Machine} (F : Facts sy m) {tr : Tr} (hinv : Inv sy m tr) (hok : trOk sy tr = true)
    (hsp : speedsComplete sy = true) (hn : normIdem = true) {T : Array (Array Int)} {n : Nat} (hT : tableOk sy tr T n = true) :
    ∀ (is : List HIn) (s : HS), inD sy s = true → (∀ i ∈ is, i ∈ inputs) → is.length ≤ n →
      hdist sy m s is ≤ T[is.length]![key sy s]!
  | [], s, hD, _, _ => by
    simp only [tableOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hT
    simpa [hdist] using hT.1 s (mem_states hsp hD)
  | i :: rest, s, hD, his, hl => by
    have hi := his i (by simp)
    have hDt := AirCap.inD_step F hD hi
    simp only [List.length_cons] at hl
    have ih := dist_table F hinv hok hsp hn hT rest (hstep sy m s i) hDt (fun j hj => his j (by simp [hj])) (by omega)
    have hT' := hT
    simp only [tableOk, Bool.and_eq_true, List.all_eq_true] at hT'
    have hk := hT'.2 rest.length (List.mem_range.2 (by omega))
    have h := step_le hinv hok hsp hn hk hD hi (fun h => absurd h (by decide))
    simp only [hdist, List.length_cons]
    omega

/-- air layers over `T0`: `X[0]` is at least `T0`, and each layer bounds one more air frame -/
def airOk (sy : Syms) (tr : Tr) (X : Array (Array Int)) (A : Nat) (T0 : Array Int) : Bool :=
  (states sy).all (fun s => decide (T0[key sy s]! ≤ X[0]![key sy s]!)) && (List.range A).all fun a => layerOk sy true tr X[a]! X[a + 1]!

/-- **The air layers bound the distance**: `a ≤ A` air frames from a state of the domain, then frames that `T0` bounds -/
theorem dist_air {sy : Syms} {m : Machine} (F : Facts sy m) {tr : Tr} (hinv : Inv sy m tr) (hok : trOk sy tr = true)
    (hsp : speedsComplete sy = true) (hn : normIdem = true) {X : Array (Array Int)} {A : Nat} {T0 : Array Int}
    (hX : airOk sy tr X A T0 = true) {bs : List HIn} (hb : ∀ s, inD sy s = true → hdist sy m s bs ≤ T0[key sy s]!) :
    ∀ (as : List HIn) (s : HS), inD sy s = true → (∀ i ∈ as, i ∈ inputs ∧ isAir i = true) → as.length ≤ A →
      hdist sy m s (as ++ bs) ≤ X[as.length]![key sy s]!
  | [], s, hD, _, _ => by
    simp only [airOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hX
    have h1 := hX.1 s (mem_states hsp hD)
    have h2 := hb s hD
    simp only [List.nil_append, List.length_nil]
    omega
  | i :: rest, s, hD, his, hl => by
    obtain ⟨hi, ha⟩ := his i (by simp)
    have hDt := AirCap.inD_step F hD hi
    simp only [List.length_cons] at hl
    have ih := dist_air F hinv hok hsp hn hX hb rest (hstep sy m s i) hDt (fun j hj => his j (by simp [hj])) (by omega)
    have hX' := hX
    simp only [airOk, Bool.and_eq_true, List.all_eq_true] at hX'
    have hk := hX'.2 rest.length (List.mem_range.2 (by omega))
    have h := step_le hinv hok hsp hn hk hD hi (fun _ => ha)
    simp only [List.cons_append, hdist, List.length_cons]
    omega

/-- the table of `0..n` frames, the best input on each frame -/
def table (tr : Tr) (keys : List Nat) (sz n : Nat) : Array (Array Int) :=
  (List.range n).foldl (fun t _ => t.push (layer false tr keys sz t.back!)) #[Array.replicate sz 0]

/-! ## The search from the room's first frame -/

open FastTakeoff (Room Pos Cov stepE airI jmpI adv go Low AirIn JmpIn)

/-- the inputs of air frames: a frame that starts in the air, or a jump frame -/
def airAll : List HIn := inputsN.filter isAir

/-- cut the greatest `P` of each state to `cp − 1`: on these frames he is left of the corner -/
def clamp (cp : Int) (es : List FastTakeoff.Ent) : List FastTakeoff.Ent := es.map fun e => (e.1, (e.2.1, min e.2.2 (cp - 1)))

/-- air frames of the fall -/
def fallS (sy : Syms) (m : Machine) : Nat → List FastTakeoff.Ent → List FastTakeoff.Ent
  | 0, l => l
  | k + 1, l => fallS sy m k (stepE sy m airI (fun _ => true) l)

/-- air frames left of the corner -/
def lowS (sy : Syms) (m : Machine) (cp : Int) : Nat → List FastTakeoff.Ent → List FastTakeoff.Ent
  | 0, l => l
  | k + 1, l => lowS sy m cp k (clamp cp (stepE sy m airAll (fun q => decide (q < cp)) l))

/-- any air frames -/
def airS (sy : Syms) (m : Machine) : Nat → List FastTakeoff.Ent → List FastTakeoff.Ent
  | 0, l => l
  | k + 1, l => airS sy m k (stepE sy m airAll (fun _ => true) l)

/-- from the room's first frame: the fall, the jump frame and `k` air frames, left of the corner from the jump frame on -/
def search (sy : Syms) (m : Machine) (R : Room) (k : Nat) : List FastTakeoff.Ent :=
  lowS sy m R.cp k (clamp R.cp (stepE sy m jmpI (fun q => decide (q < R.cp)) (fallS sy m R.A [(R.s0, (R.P0, R.P1))])))

theorem cov_clamp {cp : Int} {es : List FastTakeoff.Ent} {x : Pos} (hc : Cov es x) (h : x.2 < cp) : Cov (clamp cp es) x := by
  obtain ⟨a, b, h1, h2, h3⟩ := hc
  exact ⟨a, min b (cp - 1), List.mem_map.2 ⟨(x.1, (a, b)), h1, rfl⟩, h2, by omega⟩

theorem mem_airAll {i : HIn} (hi : i ∈ inputs) (ha : isAir i = true) : norm i ∈ airAll :=
  List.mem_filter.2 ⟨FastTakeoff.norm_mem hi, by rw [AirCap.isAir_norm]; exact ha⟩

theorem go_fst {sy : Syms} {m : Machine} : ∀ (is : List HIn) (x : Pos), (go sy m x is).1 = hrun sy m x.1 is
  | [], _ => rfl
  | i :: r, x => go_fst (sy := sy) (m := m) r (adv sy m x i)

theorem cov_fallS {sy : Syms} {m : Machine} (hn : normIdem = true) :
    ∀ (is : List HIn) (es : List FastTakeoff.Ent) (x : Pos), Cov es x → (∀ i ∈ is, AirIn i) →
      Cov (fallS sy m is.length es) (go sy m x is)
  | [], _, _, hc, _ => hc
  | i :: r, es, x, hc, his => by
    have hi := his i (by simp)
    have h := FastTakeoff.cov_step_norm (sy := sy) (m := m) (keep := fun _ => true) hn hc hi.1 (FastTakeoff.mem_airI hi) (fun _ _ => rfl)
    exact cov_fallS hn r _ _ h (fun j hj => his j (by simp [hj]))

theorem cov_lowS {sy : Syms} {m : Machine} (hn : normIdem = true) {cp : Int} :
    ∀ (is : List HIn) (es : List FastTakeoff.Ent) (x : Pos), Cov es x → (∀ i ∈ is, i ∈ inputs ∧ isAir i = true) →
      Low sy m cp x is → Cov (lowS sy m cp is.length es) (go sy m x is)
  | [], _, _, hc, _, _ => hc
  | i :: r, es, x, hc, his, hl => by
    obtain ⟨hi, ha⟩ := his i (by simp)
    have hlt : (adv sy m x i).2 < cp := hl.1
    have h := FastTakeoff.cov_step_norm (sy := sy) (m := m) (keep := fun q => decide (q < cp)) hn hc hi (mem_airAll hi ha) (fun a ha' => by
      simp only [adv] at hlt
      simp only [decide_eq_true_eq]
      omega)
    exact cov_lowS hn r _ _ (cov_clamp h hlt) (fun j hj => his j (by simp [hj])) hl.2

theorem cov_airS {sy : Syms} {m : Machine} (hn : normIdem = true) :
    ∀ (is : List HIn) (es : List FastTakeoff.Ent) (x : Pos), Cov es x → (∀ i ∈ is, i ∈ inputs ∧ isAir i = true) →
      Cov (airS sy m is.length es) (go sy m x is)
  | [], _, _, hc, _ => hc
  | i :: r, es, x, hc, his => by
    obtain ⟨hi, ha⟩ := his i (by simp)
    have h := FastTakeoff.cov_step_norm (sy := sy) (m := m) (keep := fun _ => true) hn hc hi (mem_airAll hi ha) (fun _ _ => rfl)
    exact cov_airS hn r _ _ h (fun j hj => his j (by simp [hj]))

/-- **The search covers the run**: from the room's first frame, the fall, the jump frame and `k` air frames, left of the corner from the jump
frame on -/
theorem search_cov {sy : Syms} {m : Machine} (hn : normIdem = true) {R : Room} {p0 : Int} (hp0 : R.P0 ≤ p0) (hp1 : p0 ≤ R.P1)
    {fa : List HIn} (hfa : ∀ i ∈ fa, AirIn i) (hl : fa.length = R.A) {j : HIn} (hj : JmpIn j) {ls : List HIn}
    (hls : ∀ i ∈ ls, i ∈ inputs ∧ isAir i = true) (hlow : Low sy m R.cp (go sy m (R.s0, p0) fa) (j :: ls)) :
    Cov (search sy m R ls.length) (go sy m (R.s0, p0) (fa ++ j :: ls)) := by
  have hc0 : Cov [(R.s0, (R.P0, R.P1))] (R.s0, p0) := ⟨R.P0, R.P1, by simp, hp0, hp1⟩
  have h1 := cov_fallS (sy := sy) (m := m) hn fa _ _ hc0 hfa
  rw [hl] at h1
  have hlt : (adv sy m (go sy m (R.s0, p0) fa) j).2 < R.cp := hlow.1
  have h2 := FastTakeoff.cov_step_norm (sy := sy) (m := m) (keep := fun q => decide (q < R.cp)) hn h1 hj.1 (FastTakeoff.mem_jmpI hj) (fun a ha' => by
    simp only [adv] at hlt
    simp only [decide_eq_true_eq]
    omega)
  have h3 := cov_lowS (sy := sy) (m := m) hn ls _ _ (cov_clamp h2 hlt) hls hlow.2
  rw [FastTakeoff.go_append]
  exact h3

/-! ## The check -/

/-- `a ≤ K − b` air frames below the threshold from `start`, then `b` frames of the table: short of `goal` -/
def looseOk (sy : Syms) (T : Array (Array Int)) (K b : Nat) (start goal : Int) : Bool :=
  (states sy).all fun s => !capped sy s ||
    decide (start + 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((K - b : Nat) : Int) + T[b]![key sy s]! < goal)

/-- from the search's states, `a ≤ A` air frames, then `b` frames of the table: short of `goal` -/
def exactOk (sy : Syms) (m : Machine) (T : Array (Array Int)) (es : List FastTakeoff.Ent) (A b : Nat) (goal : Int) : Bool :=
  (List.range (A + 1)).all fun a => (airS sy m a es).all fun e => decide (e.2.2 + T[b]![key sy e.1]! < goal)

/-- the frames after the landing for the slow pair `q` -/
def bOf (fall goalF : Nat) (q : Nat × Nat) : Nat := goalF - (fall + 1 + q.2)
/-- the frames from the search's last frame (the takeoff on the first frame after the fall, `q.1` low frames) to `goalF` -/
def kOf (fall goalF : Nat) (q : Nat × Nat) : Nat := goalF - (fall + q.1)

/-- **The check**: the transitions of every state, the table, and for each slow pair `q` and each number `b` of frames after the landing, the
bound from the corner less one with air frames at the air speed (`looseOk`), or from the search's states (`exactOk`) -/
def slowCheck (sy : Syms) (m : Machine) (R : Room) (pairs : List (Nat × Nat)) (fall goalF : Nat) : Bool :=
  let tr := trans sy m
  let n := pairs.foldl (fun x q => max x (bOf fall goalF q)) 0
  let T := table tr ((states sy).map (key sy)) (size sy) n
  trOk sy tr && tableOk sy tr T n && pairs.all fun q =>
    decide (bOf fall goalF q ≤ n) && (List.range (bOf fall goalF q + 1)).all fun b =>
      looseOk sy T (kOf fall goalF q) b (R.cp - 1) R.goal ||
        exactOk sy m T (search sy m R (q.1 - 1)) (kOf fall goalF q - b) b R.goal

/-- **Short of the goal**: a state of the search after the takeoff on the first frame after the fall and `q.1` low frames, below the air
threshold and left of the corner, then air frames and at most `bOf q` more frames, `kOf q` frames in all: short of the goal -/
theorem slow_short {sy : Syms} {m : Machine} (F : AirCap.CFacts sy m) {R : Room} {pairs : List (Nat × Nat)} {fall goalF : Nat}
    (h : slowCheck sy m R pairs fall goalF = true) {q : Nat × Nat} (hq : q ∈ pairs) {x : Pos}
    (hcov : Cov (search sy m R (q.1 - 1)) x) (hD : inD sy x.1 = true) (hc : capped sy x.1 = true) (hP : x.2 < R.cp)
    (as bs : List HIn) (ha : ∀ i ∈ as, i ∈ inputs ∧ isAir i = true) (hb : ∀ i ∈ bs, i ∈ inputs)
    (h2 : bs.length ≤ bOf fall goalF q) (h3 : as.length + bs.length ≤ kOf fall goalF q) :
    x.2 + hdist sy m x.1 (as ++ bs) < R.goal := by
  have hinv := inv_trans sy m
  simp only [slowCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, hT⟩, hp⟩ := h
  obtain ⟨hBn, hb'⟩ := hp q hq
  have hbl := hb' bs.length (List.mem_range.2 (by omega))
  have hdt := dist_table F.pot hinv hok F.speeds F.normI hT
  have hA : 1 ≤ sy.AirFastSpeed.toNat := by
    simp only [capped, decide_eq_true_eq] at hc
    omega
  have hsplit := AirCap.hdist_append (sy := sy) (m := m) as bs x.1
  have hai : ∀ i ∈ as, i ∈ inputs := fun i hi => (ha i hi).1
  obtain ⟨hD1, _⟩ := FastTakeoff.go_facts F.pot as x hD hai
  rw [go_fst] at hD1
  have hd2 := hdt bs (hrun sy m x.1 as) hD1 hb (by omega)
  rcases Bool.or_eq_true _ _ ▸ hbl with hl | he
  · -- air frames at the air speed, then the table
    obtain ⟨_, hc1, h4⟩ := AirCap.air_run F as x.1 hD hc ha
    simp only [looseOk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hl
    rcases hl (hrun sy m x.1 as) (mem_states F.speeds hD1) with h5 | h5
    · rw [h5] at hc1; exact absurd hc1 (by decide)
    · have h6 : 16 * ((sy.AirFastSpeed.toNat : Int) - 1) * (as.length : Int) ≤
          16 * ((sy.AirFastSpeed.toNat : Int) - 1) * ((kOf fall goalF q - bs.length : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
  · -- the search's states, the air frames, then the table
    simp only [exactOk, List.all_eq_true, decide_eq_true_eq] at he
    obtain ⟨lo, hi, hm, h4, h5⟩ := cov_airS F.normI as _ x hcov ha
    have h6 := he as.length (List.mem_range.2 (by omega)) _ hm
    rw [go_fst] at h6
    have h7 := FastTakeoff.go_snd (sy := sy) (m := m) as x
    simp only at h6
    omega

end Smbrta.LandDist
