import Theorems.CastleToLevel
import Theorems.SideChangeEnd

/-!
# The star flag's rule on real frames

After the castle entry Mario has no control: the star flag counts the timer's digits down (task 2), rises (task 3), and waits on the interval timer (task 4); then
the level changes (task 5). `CastleToLevel.Flag` takes the rule of one frame (`FlagRun`) on every frame as a field. Here it is proved on real machines, from one
condition on the machine at the castle entry and inputs with no Start (`After`, `flagOf_after`).

The condition `Good` says the machine is in one of the abstract states `Data.B0` of a frame's start, and the counters and Mario's numbers have values in stated
ranges. One frame from such a machine is cut at 13 named places of the program (`cutOf`). On each stage the walks of the abstract machine of `TaintRun` show
three kinds of facts (`Checked`): the machine comes to the next place in a state of the next stage (`CoverP`), a byte has one of some values there (`FactP`),
a byte is the same there (`KeepP`, with the counter `Env.rkI` for values of at least 2). `frame_step` joins them: the counters follow `FlagRun`, and the next
frame is in `Good` again or begins with task 5. `flagCheck` is the check on the ROM, and `checked_of_check` turns it into `Checked`.

The states are found by searches that are no part of the proof (`csearch`, `mainRun`, `marioTable`); the proof only uses that each walk of the check
succeeds. The context `Ctx` comes from a machine `r` at the castle entry and the names of the bytes (`ctxOf`). Page: `1-1/g-2-1-FlagRule.md`.
-/

namespace Smbrta.FlagRule

open PipeTransition (frame run zeros)
open PipeTransitionAll (go Names asmValue)
open TaintRun
open SideChangeBound (startOf)
open SideChangeEnd (xsuccs s_xsuccs canon sim_refine)

/-! ## Splitting a state by the value of a byte -/

/-- the values a byte can have -/
def valuesOf (b : AB) : List UInt8 :=
  (List.range 256).filterMap fun v => if v.toUInt8 &&& b.k == b.v &&& b.k then some v.toUInt8 else none

theorem mem_valuesOf {b : AB} {x : UInt8} (h : b.mem x) : x ∈ valuesOf b := by
  unfold valuesOf
  refine List.mem_filterMap.2 ⟨x.toNat, List.mem_range.2 x.toNat_lt, ?_⟩
  have e : x.toNat.toUInt8 = x := by simp
  rw [e]
  have h' : (x &&& b.k == b.v &&& b.k) = true := by simpa [AB.mem] using h
  rw [if_pos h']

/-- at the places `spl`, one state for each value of the byte -/
def splitAt (spl : List (UInt16 × Nat)) (A : AS) : List AS :=
  match spl.find? (fun p => p.1 == A.pc) with
  | none => [A]
  | some p => (valuesOf (A.getK p.2)).map fun v => A.setK p.2 (AB.known v)

section
variable {E : Env} {F : Nat × UInt8}

theorem cov_split {spl : List (UInt16 × Nat)} {A : AS} {m : Machine} (hs : Sim E F A m) (hsz : ∀ p ∈ spl, p.2 < 2048) :
    ∃ B ∈ splitAt spl A, Sim E F B m ∧ B.k = A.k := by
  unfold splitAt
  cases e : spl.find? (fun p => p.1 == A.pc) with
  | none => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | some p =>
    have hp : p ∈ spl := List.mem_of_find?_eq_some e
    have hm := hs.ram p.2 (hsz p hp)
    refine ⟨A.setK p.2 (AB.known (m.ram.get! p.2)), List.mem_map.2 ⟨_, mem_valuesOf hm, rfl⟩, sim_refine hs (mem_known_self _), rfl⟩

/-- the successors with the splits -/
def fsuccs (E : Env) (ops : Array (AM Unit)) (spl : List (UInt16 × Nat)) (A : AS) : List (Option AS) :=
  (splitAt spl A).flatMap (xsuccs E ops)

theorem s_fsuccs {ops : Array (AM Unit)} {spl : List (UInt16 × Nat)} {A : AS} {m : Machine} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hsz : ∀ p ∈ spl, p.2 < 2048) (hs : Sim E F A m) :
    ∃ r ∈ fsuccs E ops spl A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨P, hP, h1, h2⟩ := cov_split hs hsz
  obtain ⟨r, hr, h3⟩ := s_xsuccs hops hT h1
  refine ⟨r, List.mem_flatMap.2 ⟨P, hP, hr⟩, fun B hB => ?_⟩
  obtain ⟨h4, h5⟩ := h3 B hB
  refine ⟨h4, ?_⟩
  unfold StepRel at h5 ⊢
  rw [h2] at h5
  exact h5

end

/-! ## A walk up to a place of the program -/

/-- the state with the registers not known -/
def regsTop (A : AS) : AS := { A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }

/-- the table covers `B`; at the places `wide` it may cover `B` with the registers not known -/
def fcover (C : Cfg) (wide : List UInt16) (B : AS) : Bool :=
  C.cut.get! B.pc.toNat != 0 && (coverIn C B || (wide.contains B.pc && coverIn C (regsTop B)))

/-- from `A`, step by step until every path comes to one of `cuts`, in a state that `stop` accepts, or to a state of the table. The frame must not end before that. -/
def cwalk (C : Cfg) (spl : List (UInt16 × Nat)) (wide : List UInt16) (cuts : List UInt16) (stop : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (fsuccs C.E C.ops spl A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        if cuts.contains B.pc then stop B
        else fcover C wide B || cwalk C spl wide cuts stop n B
      else false

/-- from `A`, step by step until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def ewalk (C : Cfg) (spl : List (UInt16 × Nat)) (wide : List UInt16) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (fsuccs C.E C.ops spl A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then fcover C wide B || ewalk C spl wide fin n B
      else B.k == A.k + 1 && fin B

/-- one step of the machine -/
def st (m : Machine) : Machine := (go step m).2

/-- `n` steps of the machine -/
def stN : Nat → Machine → Machine
  | 0, m => m
  | n + 1, m => stN n (st m)

/-- the machine `m` comes to one of `cuts` first after `j` steps, inside its frame -/
structure Arr (cuts : List UInt16) (m : Machine) (j : Nat) : Prop where
  pos : 1 ≤ j
  at_ : (stN j m).pc ∈ cuts
  first : ∀ i, 1 ≤ i → i < j → (stN i m).pc ∉ cuts
  frame : ∀ i, i ≤ j → (stN i m).frame = m.frame
  halted : ∀ i, i ≤ j → (stN i m).halted = false
  dot : m.fdot + 3 * j ≤ (stN j m).fdot

theorem Arr.unique {c : List UInt16} {m : Machine} {j j' : Nat} (h : Arr c m j) (h' : Arr c m j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with l | l | l
  · exact absurd h.at_ (h'.first j h.pos l)
  · exact l
  · exact absurd h'.at_ (h.first j' h'.pos l)

section
variable {C : Cfg} {spl : List (UInt16 × Nat)} {wide : List UInt16} {cut : List UInt16} {stop fin : AS → Bool} {Fu : Nat} {F : Nat × UInt8}

def CLive (C : Cfg) (spl : List (UInt16 × Nat)) (wide : List UInt16) (cut : List UInt16) (stop : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, cwalk C spl wide cut stop n A = true

def ELive (C : Cfg) (spl : List (UInt16 × Nat)) (wide : List UInt16) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, ewalk C spl wide fin n A = true

theorem sim_regsTop {E : Env} {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E F (regsTop A) m :=
  { hs with a := mem_top _, x := mem_top _, y := mem_top _, p := mem_top _ }

/-- the state of the table that covers `B` -/
theorem cover_state {w : Nat → AS → Bool} (ht : C.t.all (w Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverIn C B = true) :
    ∃ D, Sim C.E F D m ∧ w Fu D = true ∧ D.k = B.k := by
  unfold coverIn at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, sim_le hle hs, hall, hk⟩
  · cases h2

/-- what `fcover` gives -/
theorem fcover_state {w : Nat → AS → Bool} (ht : C.t.all (w Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : fcover C wide B = true) :
    ∃ D, Sim C.E F D m ∧ w Fu D = true ∧ D.k = B.k := by
  unfold fcover at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with h2 | ⟨_, h2⟩
  · exact cover_state ht hs h2
  · obtain ⟨D, a1, a2, a3⟩ := cover_state (B := regsTop B) ht (sim_regsTop hs) h2
    exact ⟨D, a1, a2, a3⟩

/-- **A walk up to the first of `cut`.** -/
theorem cwalk_run (ht : C.t.all (cwalk C spl wide cut stop Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hsz : ∀ p ∈ spl, p.2 < 2048) :
    ∀ (fuel : Nat) (A : AS) (m : Machine), CLive C spl wide cut stop F A m → dotsPerFrame ≤ m.fdot + 3 * fuel →
      ∃ j, Arr cut m j ∧ ∃ B, stop B = true ∧ B.k = A.k ∧ Sim C.E F B (stN j m) := by
  intro fuel
  induction fuel with
  | zero =>
    intro A m hl hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ fuel ih =>
    intro A m hl hd
    obtain ⟨hs, n, hw⟩ := hl
    cases n with
    | zero => simp [cwalk] at hw
    | succ n =>
      obtain ⟨r, hr, hB⟩ := s_fsuccs hops hT hsz hs
      simp only [cwalk, List.all_eq_true] at hw
      have hw2 := hw r hr
      cases r with
      | none => simp at hw2
      | some B =>
        obtain ⟨h1, h2⟩ := hB B rfl
        dsimp only at hw2
        have hm1 : st m = (go step m).2 := rfl
        rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
        · rw [if_pos (by simp [k1])] at hw2
          have hp1 : (st m).pc = B.pc := h1.pc
          by_cases hc : cut.contains B.pc = true
          · rw [if_pos hc] at hw2
            have hc' : B.pc ∈ cut := by simpa using hc
            refine ⟨1, ⟨Nat.le_refl _, ?_, fun i h3 h4 => by omega, ?_, ?_, ?_⟩, B, hw2, k1, h1⟩
            · show (st m).pc ∈ cut
              rw [hp1]
              exact hc'
            · intro i hi
              cases i with
              | zero => rfl
              | succ i =>
                have : i = 0 := by omega
                subst this
                exact k2
            · intro i hi
              cases i with
              | zero => exact hs.halted
              | succ i =>
                have : i = 0 := by omega
                subst this
                exact h1.halted
            · show m.fdot + 3 * 1 ≤ (st m).fdot
              have : m.fdot + 3 ≤ (go step m).2.fdot := k3
              rw [hm1]
              omega
          · rw [if_neg hc] at hw2
            simp only [Bool.or_eq_true] at hw2
            have hlive : ∃ D, CLive C spl wide cut stop F D (st m) ∧ D.k = A.k := by
              rcases hw2 with h3 | h3
              · obtain ⟨D, g1, g2, g3⟩ := fcover_state (w := cwalk C spl wide cut stop) ht h1 h3
                exact ⟨D, ⟨g1, Fu, g2⟩, g3.trans k1⟩
              · exact ⟨B, ⟨h1, n, h3⟩, k1⟩
            obtain ⟨D, hD, hk⟩ := hlive
            have hd2 : dotsPerFrame ≤ (st m).fdot + 3 * fuel := by
              have : m.fdot + 3 ≤ (st m).fdot := k3
              omega
            obtain ⟨j, hA, B2, g1, g2, g3⟩ := ih D (st m) hD hd2
            refine ⟨j + 1, ⟨by omega, hA.at_, ?_, ?_, ?_, ?_⟩, B2, g1, g2.trans hk, g3⟩
            · intro i h3 h4
              cases i with
              | zero => omega
              | succ i =>
                cases i with
                | zero =>
                  show (st m).pc ∉ cut
                  rw [hp1]
                  simpa using hc
                | succ i => exact hA.first (i + 1) (by omega) (by omega)
            · intro i h3
              cases i with
              | zero => rfl
              | succ i =>
                have := hA.frame i (by omega)
                show (stN i (st m)).frame = m.frame
                rw [this]
                exact k2
            · intro i h3
              cases i with
              | zero => exact hs.halted
              | succ i => exact hA.halted i (by omega)
            · have h5 := hA.dot
              have h6 : m.fdot + 3 ≤ (st m).fdot := k3
              show m.fdot + 3 * (j + 1) ≤ (stN j (st m)).fdot
              omega
        · rw [if_neg (by simp [k1])] at hw2
          simp at hw2

theorem ruf_steps {f : Nat} : ∀ (j n : Nat) (m : Machine), j ≤ n → (∀ i, i < j → (stN i m).frame = f ∧ (stN i m).halted = false) →
    go (runUntilFrame (f + 1) n) m = go (runUntilFrame (f + 1) (n - j)) (stN j m) := by
  intro j
  induction j with
  | zero =>
    intro n m _ _
    rfl
  | succ j ih =>
    intro n m h1 h2
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h0 := h2 0 (by omega)
    rw [PipeTransitionAll.ruf_eq, if_neg (by
      have a : m.frame = f := h0.1
      have b : m.halted = false := h0.2
      simp [a, b])]
    have := ih n (st m) (by omega) (fun i hi => h2 (i + 1) (by omega))
    rw [Nat.add_sub_add_right]
    exact this

/-- **A walk to the frame's end.** -/
theorem ewalk_run (ht : C.t.all (ewalk C spl wide fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hsz : ∀ p ∈ spl, p.2 < 2048) {f : Nat} :
    ∀ (n : Nat) (A : AS) (m : Machine), ELive C spl wide fin F A m → m.frame = f → dotsPerFrame ≤ m.fdot + 3 * n →
      (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 := by
  intro n
  induction n with
  | zero =>
    intro A m hl _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro A m hl hf hd
    have hh := hl.1.halted
    rw [PipeTransitionAll.ruf_eq, if_neg (by simp [hf, hh])]
    obtain ⟨hs, q, hw⟩ := hl
    cases q with
    | zero => simp [ewalk] at hw
    | succ q =>
      obtain ⟨r, hr, hB⟩ := s_fsuccs hops hT hsz hs
      simp only [ewalk, List.all_eq_true] at hw
      have hw2 := hw r hr
      cases r with
      | none => simp at hw2
      | some B =>
        obtain ⟨h1, h2⟩ := hB B rfl
        dsimp only at hw2
        rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
        · rw [if_pos (by simp [k1])] at hw2
          simp only [Bool.or_eq_true] at hw2
          have hlive : ∃ D, ELive C spl wide fin F D (go step m).2 ∧ D.k = A.k := by
            rcases hw2 with h3 | h3
            · obtain ⟨D, g1, g2, g3⟩ := fcover_state (w := ewalk C spl wide fin) ht h1 h3
              exact ⟨D, ⟨g1, Fu, g2⟩, g3.trans k1⟩
            · exact ⟨B, ⟨h1, q, h3⟩, k1⟩
          obtain ⟨D, hD, hk⟩ := hlive
          have := ih D _ hD (k2.trans hf) (by omega)
          rw [hk] at this
          exact this
        · rw [if_neg (by simp [k1])] at hw2
          simp only [Bool.and_eq_true, beq_iff_eq] at hw2
          rw [ruf_doneF (by rw [k2, hf]; exact Nat.le_refl _) n]
          exact ⟨by rw [k2, hf], B, hw2.2, k1, h1⟩

end

/-! ## A search from a state up to a place of the program: no part of the proof -/

/-- the 16 bytes of the stack below its pointer: not known -/
def deadStack (A : AS) : AS := (List.range 16).foldl (fun B j => B.setK (0x100 + A.s.toNat - j) AB.top) A

/-- the order of the waiting list: by the program, or by the turns of a loop that counts `x` and `y` down -/
def ckey (turns : Bool) (E : Env) (keep : List Nat) (B : AS) : Nat :=
  if turns then SideChangeEnd.xkey E keep B else keyOf E keep B

/-- a new state goes to the waiting list -/
def croute (turns : Bool) (E : Env) (keep : List Nat) (X : Search) (B : AS) : Search :=
  let K := ckey turns E keep B
  match X.pending[K]? with
  | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none =>
    if isSpin E B then
      match X.done[K]? with
      | some D =>
        if B.le D then X else
        let J := widen (D.join B)
        { X with pending := X.pending.insert K J, done := X.done.insert K J, inN := X.inN.insert K 2 }
      | none => { X with pending := X.pending.insert K B, done := X.done.insert K B, inN := X.inN.insert K 2 }
    else { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- follow one waiting state as far as no other path can join; a path that comes to one of `cuts` stops there, a frame's end is a failure if `cuts` is not empty -/
partial def crunChain (turns : Bool) (E : Env) (ops : Array (AM Unit)) (spl : List (UInt16 × Nat)) (rel : List (UInt16 × Nat × AB)) (wide gates : List UInt16) (sset : List (UInt16 × Nat × UInt8)) (keep : List Nat) (cuts : List UInt16) (X0 : Search) (A0 : AS) : Search := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := fsuccs E ops spl cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    let good := good.map fun b => (rel.filter (·.1 == b.pc)).foldl (fun B p => B.setK p.2.1 p.2.2) b
    let good := good.map fun b => match sset.find? (·.1 == b.pc) with
      | some p => b.setK p.2.1 (AB.known p.2.2)
      | none => b
    let good := good.map fun b =>
      if wide.contains b.pc then
        if rel.any (·.1 == b.pc) then deadStack { regsTop b with lo := b.lo - 240, hi := b.hi + 240 } else regsTop b
      else b
    let isRel := fun (b : AS) => rel.any (·.1 == b.pc) || wide.contains b.pc || gates.contains b.pc
    match good with
    | [b] =>
      if b.k == cur.k && !cuts.contains b.pc && !isRel b && (X.leaders[b.pc.toNat]?).isNone && run < 128 &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k then
        if !cuts.isEmpty then X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
        else X := { X with ends := X.ends.push b }
      else if cuts.contains b.pc then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := croute turns E keep X b
        if isRel b then X := { X with inN := X.inN.insert (ckey turns E keep b) 2 }
    break
  return X

/-- the search up to the first of `cuts`, or up to the frame's end if `cuts` is empty. It stops after `limit` steps, with a failure. -/
partial def csearch (turns : Bool) (E : Env) (ops : Array (AM Unit)) (spl : List (UInt16 × Nat)) (rel : List (UInt16 × Nat × AB)) (wide gates : List UInt16) (sset : List (UInt16 × Nat × UInt8)) (keep : List Nat) (cuts : List UInt16) (starts : List AS) (limit : Nat := 300000) : Search := Id.run do
  let mut X : Search := starts.foldl (croute turns E keep) {}
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 then X := { X with out := X.out.push A }
      if isSpin E A then X := { X with done := X.done.insert key A }
      X := crunChain turns E ops spl rel wide gates sset keep cuts X A
  return X

/-- the table from a search -/
def cfgOf (E : Env) (ops : Array (AM Unit)) (sy : Syms) (keep : List Nat) (X : Search) : Cfg :=
  let P := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops, sy, K := 1, keep, t := X.out, idx := P.1, cut := P.2.1 }

/-- the value of a byte in a state, if it is known -/
def byteOf (S : AS) (i : Nat) : Option UInt8 := if (S.getK i).isK then some (S.getK i).v else none

/-- states with the same known values of the bytes `key` are joined -/
def groupBy (key : List Nat) (l : List AS) : List AS := Id.run do
  let mut h : Std.HashMap (List (Option UInt8)) AS := {}
  for S in l do
    let k := key.map (byteOf S)
    match h[k]? with
    | some T => h := h.insert k (T.join S)
    | none => h := h.insert k S
  return h.values

/-- the state from the machine `r`: only the bytes `K` are known -/
def knownStart (r : Machine) (K : List Nat) (low : Bool) : AS := { startOf r K low with rk := false }

/-! ## Walks from a state, with a table from a search -/

/-- what a stage is to the proof and to the search -/
structure Stage where
  name : String
  cut : Option UInt16
  /-- other places the stage may end at: the stage ends at the first of `cut` and these -/
  alt : List UInt16 := []
  spl : List (UInt16 × Nat) := []
  wide : List UInt16 := []
  /-- at these places the search forgets a byte: no part of the proof -/
  rel : List (UInt16 × Nat × AB) := []
  /-- at these places the search takes one value of a byte, and not all as the walk does: no part of the proof -/
  sset : List (UInt16 × Nat × UInt8) := []
  /-- the bytes that the search keeps apart: no part of the proof -/
  keep : List Nat := []
  /-- the order of the search: no part of the proof -/
  turns : Bool := false
  deriving Inhabited

/-- the places a stage ends at: none if it ends at the frame's end -/
def Stage.cuts (st : Stage) : List UInt16 := st.cut.toList ++ st.alt

/-- the search of a stage -/
def searchOf (E : Env) (st : Stage) (starts : List AS) (limit : Nat := 3000000) : Search :=
  csearch st.turns E (aRows E).toArray (if st.sset.isEmpty then st.spl else []) st.rel st.wide (st.spl.map (·.1)) st.sset st.keep st.cuts starts limit

/-- the table of a list of states -/
def cfgFrom (sy : Syms) (E : Env) (st : Stage) (t : Array AS) : Cfg :=
  cfgOf E (aRows E).toArray sy (st.keep.filter fun b => !st.spl.any (·.2 == b) && !st.rel.any (·.2.1 == b)) ({ out := t } : Search)

/-- walks with a table: every state of the table and the states `l` -/
def walkAll (C : Cfg) (st : Stage) (l : List AS) (stop : AS → Bool) : Bool :=
  st.spl.all (fun p => decide (p.2 < 2048)) &&
  match st.cut with
  | some _ => C.t.all (cwalk C st.spl st.wide st.cuts stop walkFuel) && l.all (cwalk C st.spl st.wide st.cuts stop walkFuel)
  | none => C.t.all (ewalk C st.spl st.wide stop walkFuel) && l.all (ewalk C st.spl st.wide stop walkFuel)

/-- a walk with a table from `A0` -/
def walkOK (C : Cfg) (st : Stage) (A0 : AS) (stop : AS → Bool) : Bool := walkAll C st [A0] stop

/-! ## The stages of a frame -/

/-- what the stages have in common -/
structure Ctx where
  E : Env
  sy : Syms
  nm : Names
  /-- the machine that gives the values of the known bytes -/
  r : Machine
  /-- the known bytes -/
  K : List Nat
  /-- the largest value of the game timer -/
  tmax : Nat

/-- a name as a RAM index -/
def Ctx.i (c : Ctx) (n : String) : Nat := ((c.nm.ad n) &&& 0x7FF).toNat

def forgetAll (l : List Nat) (A : AS) : AS := l.foldl (fun B i => B.setK i AB.top) A

def refineAB (r : List (Nat × AB)) (A : AS) : AS := r.foldl (fun B p => B.setK p.1 p.2) A

def Ctx.y (c : Ctx) : Nat := c.i "Enemy_Y_Position"
def Ctx.w (c : Ctx) : Nat := c.i "EnemyIntervalTimer"
def Ctx.ph (c : Ctx) : Nat := c.i "IntervalTimerControl"
def Ctx.task (c : Ctx) : Nat := (c.sy.StarFlagTaskControl &&& 0x7FF).toNat
def Ctx.d (c : Ctx) (k : Nat) : Nat := ((c.nm.ad "GameTimerDisplay" + k.toUInt16) &&& 0x7FF).toNat
def Ctx.v (c : Ctx) : Nat := c.i "SprObject_X_Speed"
def Ctx.fF (c : Ctx) : Nat := c.i "Player_X_MoveForce"
def Ctx.ff (c : Ctx) : Nat := c.i "SprObject_X_MoveForce"
def Ctx.abs (c : Ctx) : Nat := c.i "Player_XSpeedAbsolute"
def Ctx.coll (c : Ctx) : Nat := c.i "Player_CollisionBits"
def Ctx.tm (c : Ctx) : Nat := c.i "SideCollisionTimer"
def Ctx.x (c : Ctx) : Nat := c.i "SprObject_X_Position"
def Ctx.pg (c : Ctx) : Nat := c.i "SprObject_PageLoc"

def Ctx.rs (c : Ctx) : Nat := c.i "RunningSpeed"
def Ctx.md (c : Ctx) : Nat := c.i "Player_MovingDir"

/-- the pause status: its bit 0 says that the game is paused -/
def Ctx.gps (c : Ctx) : Nat := c.i "GamePauseStatus"

/-- the bit 0 of the pause status, if the state knows it -/
def pausedBit (c : Ctx) (X : AS) : Option Bool := (X.getK c.gps).bit 0x01

def Ctx.lim (c : Ctx) : Nat := c.sy.StarFlagTopY.toNat
def Ctx.w0 (c : Ctx) : Nat := c.sy.StarFlagDelay.toNat
def Ctx.x0 (c : Ctx) : UInt8 := c.r.ram.get! c.x
def Ctx.pg0 (c : Ctx) : UInt8 := c.r.ram.get! c.pg

abbrev Bytes := List (Nat × UInt8)

/-- the values that the walks of a stage start from -/
def refsOf (c : Ctx) : Nat → List Bytes
  | 7 => (List.range c.sy.SideTimerBump.toNat).map fun t => [(c.tm, (t + 1).toUInt8)]
  | 8 => [c.x0, c.x0 + 1].map fun a => [(c.x, a), (c.pg, c.pg0)]
  | 9 => [2, 3, 4].flatMap fun t => [[(c.task, t), (c.x, c.x0), (c.pg, c.pg0)]] ++ (List.range 7).map fun v => [(c.task, t), (c.x, c.x0 + 1), (c.pg, c.pg0), (c.v, v.toUInt8)]
  | 10 => [2, 3, 4].map fun t => [(c.task, t)]
  | _ => [[]]

/-- the slots of the other enemies: when they all hold the fireworks, the flags need not be known, but for the low bit -/
def normF (c : Ctx) (A : AS) : AS :=
  let ids := (List.range 4).map fun j => A.getK (c.i "Enemy_ID" + 1 + j)
  let fw := AB.known (c.i "Fireworks").toUInt8
  if ids.all (· == fw) then
    (List.range 4).foldl (fun B j => B.setK (c.i "Enemy_Flag" + 1 + j) ⟨0, 0xFE⟩) A
  else A

/-- what the main walk of a stage tries at its start, and what the walk forgets at its end -/
structure Main where
  st : Stage
  refs : List (List (Nat × UInt8)) := [[]]
  forget : List Nat := []
  forgetP : List (Nat × AB) := []
  key : List Nat := []
  deriving Inhabited

/-- the variants kept apart at every place -/
def varKey (c : Ctx) : List Nat :=
  [c.i "SprShuffleAmtOffset", c.i "EventMusicBuffer", c.i "Enemy_ID" + 1]

/-- the bytes that the end of a frame keeps apart -/
def endKey (c : Ctx) : List Nat := [c.i "VRAM_Buffer1_Offset", c.i "Square2SoundQueue"] ++ varKey c

def mainStages (c : Ctx) : List Main :=
  let sy := c.sy
  let vI := c.i "SprObject_X_Speed"
  let xI := c.i "SprObject_X_Position"
  let pgI := c.i "SprObject_PageLoc"
  let tI := c.task
  let qI := c.i "Square2SoundQueue"
  let oI := c.i "MusicOffset_Square1"
  let tmI := c.tm
  let bufK := [c.i "VRAM_Buffer1_Offset", c.i "EnemyFrenzyBuffer", qI]
  let sprK := varKey c
  let squ1 := [oI, c.i "Squ1_NoteLenCounter", c.i "Squ1_EnvelopeDataCtrl", c.i "AltRegContentFlag"]
  let stages : List Main := [ { st := { name := "screen", cut := some sy.SoundEngine, keep := [c.i "VRAM_Buffer1_Offset", qI] ++ sprK }, key := [qI] },
    { st := { name := "sound effects", cut := some sy.MusicHandler, alt := [sy.SkipSoundSubroutines], keep := [qI] ++ sprK } },
    { st := { name := "music", cut := some sy.ReadJoypads, spl := [(sy.FetchSqu1MusicData, oI)], wide := [sy.FetchSqu1MusicData, sy.MiscSqu1MusicTasks], rel := squ1.map (fun b => (sy.MiscSqu1MusicTasks, b, AB.top)), sset := [(sy.FetchSqu1MusicData, oI, c.r.ram.get! oI)], keep := sprK } },
    { st := { name := "pad", cut := some sy.DecTimers, alt := [sy.SkipMainOper], keep := sprK } },
    { st := { name := "timers", cut := some sy.NoDecTimers, keep := sprK } },
    { st := { name := "sprites", cut := some sy.PlayerEndLevel, keep := sprK } },
    { st := { name := "move", cut := some sy.PlayerSubs, keep := sprK }, forget := [xI, pgI] },
    { st := { name := "scroll", cut := some sy.GetXOffscreenBits, keep := sprK ++ [tmI] }, refs := refsOf c 7, forget := [tmI] },
    { st := { name := "offscreen", cut := some sy.GetPlayerOffscreenBits, spl := [(sy.GetXOffscreenBits, c.i "ScreenRight_X_Pos"), (sy.XLdBData, c.i "ScreenEdge_X_Pos")], rel := [(sy.XLdBData, c.i "ScreenRight_X_Pos", ⟨0, 0xC0⟩), (sy.ExXOfsBS, c.i "ScreenEdge_X_Pos", ⟨0, 0xC0⟩)], keep := sprK ++ [xI, c.i "ScreenRight_X_Pos", c.i "ScreenEdge_X_Pos"] },
      refs := refsOf c 8, forget := [xI, pgI], forgetP := [(c.i "ScreenRight_X_Pos", ⟨0, 0xC0⟩), (c.i "ScreenEdge_X_Pos", ⟨0, 0xC0⟩)] },
    { st := { name := "collision", cut := some sy.RunStarFlagObj, keep := sprK ++ [tI, vI, xI] },
      refs := refsOf c 9, forget := [tI, vI, tmI, c.i "Player_CollisionBits"] },
    { st := { name := "the flag", cut := some sy.FloateyNumbersRoutine, turns := true, keep := sprK ++ bufK ++ [tI] },
      refs := refsOf c 10, forget := [tI], key := bufK },
    { st := { name := "the other slots", cut := some sy.FlagpoleRoutine, keep := sprK ++ bufK ++ [c.i "ObjectOffset"], turns := true }, key := bufK },
    { st := { name := "the pole", cut := some sy.RunGameTimer, keep := sprK ++ bufK }, key := bufK },
    { st := { name := "the end", cut := none, spl := [(sy.UpdScrollVar, c.i "ScrollThirtyTwo")], keep := sprK ++ bufK ++ [c.i "ScrollThirtyTwo"] }, forgetP := [(c.i "ScrollThirtyTwo", ⟨0, 0xE0⟩)], key := bufK },
    { st := { name := "no sound", cut := some sy.ReadJoypads, keep := sprK } },
    { st := { name := "paused", cut := none, keep := sprK ++ bufK }, key := bufK } ]
  -- the search keeps the pause status apart: a join before its branch would lose the bit
  stages.map fun ms => { ms with st := { ms.st with keep := ms.st.keep ++ [c.gps] } }

/-- the place each stage ends at. Stages 13 and 15 end at the frame's end. -/
def cutOf (sy : Syms) : Nat → UInt16
  | 0 => sy.SoundEngine
  | 1 => sy.MusicHandler
  | 2 => sy.ReadJoypads
  | 3 => sy.DecTimers
  | 4 => sy.NoDecTimers
  | 5 => sy.PlayerEndLevel
  | 6 => sy.PlayerSubs
  | 7 => sy.GetXOffscreenBits
  | 8 => sy.GetPlayerOffscreenBits
  | 9 => sy.RunStarFlagObj
  | 10 => sy.FloateyNumbersRoutine
  | 11 => sy.FlagpoleRoutine
  | 12 => sy.RunGameTimer
  | 14 => sy.ReadJoypads
  | _ => 0

/-- the other place a stage may end at: the sound with the pause's sound, and a paused frame -/
def altOf (sy : Syms) : Nat → List UInt16
  | 1 => [sy.SkipSoundSubroutines]
  | 3 => [sy.SkipMainOper]
  | _ => []

/-- the places a stage ends at: it ends at the first of them -/
def cutsOf (sy : Syms) (j : Nat) : List UInt16 := cutOf sy j :: altOf sy j

/-- the stage that comes after the stage `j` ended at `pc`: the stage 14 after the sound of the pause, the stage 15 after a paused frame's main part -/
def nextIdx (sy : Syms) (j : Nat) (pc : UInt16) : Nat :=
  if j == 1 && pc == sy.SkipSoundSubroutines then 14
  else if j == 3 && pc == sy.SkipMainOper then 15
  else if j == 14 then 3
  else j + 1

/-- the states of a list, grouped at each place by the known values of `key` -/
def groupAt (key : List Nat) (l : List AS) : List AS :=
  let pcs := (l.map (·.pc)).eraseDups
  pcs.flatMap fun p => groupBy key (l.filter (·.pc == p))

/-- a stage of the main walk: the next states -/
def runMain (c : Ctx) (ms : Main) (B : List AS) : Search × List AS :=
  let starts := B.flatMap fun A => ms.refs.map fun r => SideChangeEnd.refine r A
  let X := searchOf c.E ms.st starts
  let e := X.ends.toList.map (fun b => normF c (refineAB ms.forgetP (forgetAll ms.forget b)))
  (X, if ms.st.cut.isSome then groupAt (ms.key ++ varKey c) e else e)

/-! ## The states of each place -/

/-- the sprites' bytes -/
def sprBytes (c : Ctx) : List Nat := (List.range 19).map (c.i "SprShuffleAmtOffset" + ·)

/-- the bytes that the start of a frame knows -/
def startKnown (c : Ctx) : List Nat :=
  c.K ++ sprBytes c ++ [c.i "VRAM_Buffer1_Offset", c.i "Square2SoundQueue", c.i "EventMusicBuffer", c.i "ScrollThirtyTwo", c.i "ScreenEdge_X_Pos", c.i "ScreenRight_X_Pos"] ++
    (List.range 80).map (c.i "VRAM_Buffer1" + ·) ++ (List.range 6).map (c.i "Enemy_ID" + ·) ++ (List.range 6).map (c.i "Enemy_Flag" + ·)

/-- what the seeds know of the bytes that the screen's position has, and of the pause: the status is 0, 1, 0x80 or 0x81, the pause's sound queue and mode 0 to 3,
the pause timer any value. The height of the flagpole's floating number may have any value and the number of its score is below 8: both are set by the height of the
touch, so the castle entries after touches at other heights are in the states too. -/
def partials (c : Ctx) : List (Nat × AB) :=
  [(c.i "ScrollThirtyTwo", ⟨0, 0xE0⟩), (c.i "ScreenEdge_X_Pos", ⟨0, 0xC0⟩), (c.i "ScreenRight_X_Pos", ⟨0, 0xC0⟩), (c.i "VRAM_Buffer1", AB.known 0), (c.i "Square2SoundQueue", AB.known 0),
   (c.gps, ⟨0, 0x7E⟩), (c.i "GamePauseTimer", AB.top), (c.i "PauseModeFlag", ⟨0, 0xFC⟩), (c.i "PauseSoundQueue", ⟨0, 0xFC⟩),
   (c.i "FlagpoleFNum_Y_Pos", AB.top), (c.i "FlagpoleScore", ⟨0, 0xF8⟩)]

/-- the states a frame can start from, before any frame -/
def seeds (c : Ctx) : List AS :=
  let rots := [c.r, frame c.r 0, frame (frame c.r 0) 0]
  let fws := fun (A : AS) (f1 : Bool) =>
    if f1 then normF c ((List.range 4).foldl (fun B j => B.setK (c.i "Enemy_ID" + 1 + j) (AB.known (c.i "Fireworks").toUInt8)) A) else A
  [true, false].flatMap fun low => rots.flatMap fun rm => [false, true].flatMap fun f1 => [c.r.ram.get! (c.i "EventMusicBuffer"), 0].map fun v =>
    let A := fws (refineAB (partials c) (knownStart c.r c.K low)) f1
    let A := (sprBytes c).foldl (fun B i => B.setK i (AB.known (rm.ram.get! i))) A
    A.setK (c.i "EventMusicBuffer") (AB.known v)

/-- the end of a frame as the start of the next -/
def endState (c : Ctx) (mask : ByteArray) (b : AS) : AS :=
  (List.range 2048).foldl (fun B i => if mask.get! i == 0 then B.setK i AB.top else B) (canon b)

/-- the main walk from the states `B0`: the states at each place, and the ends of the frame. The stages 0 to 13 follow each other; the sound of the pause goes
through the stage 14 from the stage 1 to the stage 3, and a paused frame goes from the stage 3 to its end through the stage 15. -/
def mainRun (c : Ctx) (B0 : List AS) : List (Main × List AS × List AS × Array AS) × List AS :=
  let mask := SideChangeBound.knOf (startKnown c)
  let ms := (mainStages c).toArray
  let empty : Main × List AS × List AS × Array AS := (default, [], [], #[])
  let step := fun (pl : Array (Main × List AS × List AS × Array AS)) (j : Nat) (B : List AS) =>
    let (X, nx) := runMain c ms[j]! B
    pl.set! j (ms[j]!, B, nx, X.out)
  let nxOf := fun (pl : Array (Main × List AS × List AS × Array AS)) (j : Nat) => pl[j]!.2.2.1
  let pl := step (Array.replicate 16 empty) 0 B0
  let pl := step pl 1 (nxOf pl 0)
  let pl := step pl 2 ((nxOf pl 1).filter (nextIdx c.sy 1 ·.pc == 2))
  let pl := step pl 14 ((nxOf pl 1).filter (nextIdx c.sy 1 ·.pc == 14))
  let pl := step pl 3 (groupAt (varKey c) (nxOf pl 2 ++ nxOf pl 14))
  let pl := step pl 15 ((nxOf pl 3).filter (nextIdx c.sy 3 ·.pc == 15))
  let pl := (List.range 10).foldl (fun pl k =>
    let j := k + 4
    step pl j (if j == 4 then (nxOf pl 3).filter (nextIdx c.sy 3 ·.pc == 4) else nxOf pl (j - 1))) pl
  let e := (nxOf pl 13 ++ nxOf pl 15).map (endState c mask)
  (pl.toList, groupBy (endKey c) (e.filter (·.lo == 0)) ++ groupBy (endKey c) (e.filter (·.lo != 0)))

/-- the states a frame can start from: the seeds and the ends of a frame from the seeds -/
def frameStarts (c : Ctx) : List AS :=
  let nx := (mainRun c (seeds c)).2
  let keyOf := fun (S : AS) => (endKey c).map (byteOf S)
  nx.foldl (fun (B : List AS) n =>
    if B.any (n.le ·) then B
    else
      let same := fun (S : AS) => keyOf S == keyOf n && (S.lo == 0) == (n.lo == 0) && (byteOf S (c.i "VRAM_Buffer1")).isSome == (byteOf n (c.i "VRAM_Buffer1")).isSome
      match B.find? same with
      | some T => (T.join n) :: B.filter (fun S => !same S)
      | none => n :: B) (seeds c)

/-! ## The bytes that follow a rule -/

/-- the state knows these values -/
def knows (X : AS) (l : Bytes) : Bool := l.all fun p => (X.getK p.1).isK && (X.getK p.1).v == p.2

/-- a fact on a stage: under `pre`, one of `alts` holds at the end -/
structure Fact where
  pre : Bytes
  alts : List Bytes
  /-- the walk needs no table -/
  plain : Bool := false
  deriving Inhabited

/-- Mario's bytes that the frames carry -/
def Ctx.mario (c : Ctx) : List Nat := [c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md]

def Ctx.digits (c : Ctx) : List Nat := [c.d 0, c.d 1, c.d 2]

/-- the bytes that follow a rule -/
def Ctx.ruled (c : Ctx) : List Nat := [c.ph, c.w, c.y, c.task] ++ c.digits ++ c.mario

/-! ### Mario on a frame -/

/-- the five bytes as a number -/
def q5 (a b c d e : UInt8) : Nat := a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * (d.toNat + 256 * e.toNat)))
def byteN (n k : Nat) : UInt8 := (n / 256 ^ k % 256).toUInt8

/-- `v, F, f, A, C` before the move, as a list of known bytes -/
def moveIn (c : Ctx) (q : Nat) : Bytes :=
  [(c.v, byteN q 0), (c.fF, byteN q 1), (c.ff, byteN q 2), (c.abs, byteN q 3), (c.coll, byteN q 4), (c.rs, c.r.ram.get! c.rs), (c.md, c.r.ram.get! c.md)]

/-- what the state knows after the move: `v, F, f, A` and `x` -/
def moveOutOf (c : Ctx) (X : AS) : Option Nat :=
  match byteOf X c.v, byteOf X c.fF, byteOf X c.ff, byteOf X c.abs, byteOf X c.x with
  | some a, some b, some d, some e, some f => some (q5 a b d e f)
  | _, _, _, _, _ => none

/-- the bytes the move leaves -/
def moveOut (c : Ctx) (o : Nat) : Bytes :=
  [(c.v, byteN o 0), (c.fF, byteN o 1), (c.ff, byteN o 2), (c.abs, byteN o 3), (c.x, byteN o 4), (c.pg, c.pg0), (c.rs, c.r.ram.get! c.rs), (c.md, c.r.ram.get! c.md)]

/-- the next numbers of Mario: `q` is `v, F, f, A, C` and `t`, `o` is what the move leaves -/
def nextMario (c : Ctx) (t : UInt8) (o : Nat) : Option (Nat × UInt8) :=
  if byteN o 4 == c.x0 + 1 then some (q5 0 (byteN o 1) (byteN o 2) (byteN o 3) (c.r.ram.get! c.coll), c.sy.SideTimerBump.toUInt8)
  else if byteN o 4 == c.x0 then some (q5 (byteN o 0) (byteN o 1) (byteN o 2) (byteN o 3) c.sy.CollisionInit.toUInt8, t - 1)
  else none

/-! ## The plan of a frame -/

abbrev Plan := List (Main × List AS × List AS × Array AS)

/-- the states of each stage: the stage, the states at its start, the states at its end -/
def planFrom (c : Ctx) (B0 : List AS) : Plan := (mainRun c B0).1

/-- join by the known values of `key`, the two kinds of dots apart -/
def coarse (key : List Nat) (l : List AS) : List AS :=
  groupBy key (l.filter (·.lo == 0)) ++ groupBy key (l.filter (·.lo != 0))

/-- `X` is covered by one of `l`, quickly -/
def coverKey (key : List Nat) (l : List AS) (X : AS) : Bool :=
  l.any fun D => key.all (fun i => (X.getK i).le (D.getK i)) && X.le D

/-- at the frame's end: a state of the frame's start -/
def coverEnd (c : Ctx) (l : List AS) (X : AS) : Bool :=
  coverKey (endKey c) l { X with k := 0 }

/-- the bytes that the walks of keeping and of facts need known at a stage -/
def coarseKey (c : Ctx) : Nat → List Nat
  | 14 => []
  | 15 => []
  | 0 => [c.i "VRAM_Buffer1_Offset"]
  | 1 => [c.i "Square2SoundQueue"]
  | 2 => [c.i "EventMusicBuffer"]
  | 10 => [c.i "SprShuffleAmtOffset", c.i "EventMusicBuffer"]
  | 11 => [c.i "SprShuffleAmtOffset", c.i "Enemy_ID" + 1, c.i "EnemyFrenzyBuffer", c.i "VRAM_Buffer1_Offset"]
  | 12 => [c.i "SprShuffleAmtOffset"]
  | 13 => [c.i "VRAM_Buffer1_Offset"]
  | _ => []

/-- a walk from each state `Cs` with `pre`: one of `alts` holds at the end -/
def factOK (c : Ctx) (st : Stage) (Cs : List AS) (f : Fact) : Bool :=
  f.alts.all (fun a => a.all fun p => decide (p.1 < 2048)) &&
  Cs.all fun T =>
    let A0 := SideChangeEnd.refine f.pre T
    let C := if f.plain then cfgFrom c.sy c.E st #[] else cfgFrom c.sy c.E st (searchOf c.E st [A0] 400000).out
    walkOK C st A0 (fun X => f.alts.any (knows X))

/-- the state with the counter `b` followed -/
def rkState (b : Nat) (A : AS) : AS := { A.setK b AB.top with rk := true, spent := false }

/-- the walks for bytes that stay under `pre`, from a table of one search -/
def keepsOK (c : Ctx) (st : Stage) (Cs : List AS) (pre : Bytes) (bs : List Nat) : Bool :=
  Cs.all fun T0 =>
    let T := SideChangeEnd.refine pre T0
    let X := searchOf c.E st [T] 400000
    bs.all fun b => decide (b < 2048) &&
      let kT := fun (v : UInt8) (A : AS) => A.setK b (AB.known v)
      walkOK (cfgFrom c.sy { c.E with rkI := b } st (X.out.map (rkState b))) st (rkState b T) (fun Y => Y.rk && !Y.spent) &&
      walkOK (cfgFrom c.sy c.E st (X.out.map (kT 0))) st (kT 0 T) (fun Y => knows Y [(b, 0)]) &&
      walkOK (cfgFrom c.sy c.E st (X.out.map (kT 1))) st (kT 1 T) (fun Y => knows Y [(b, 1)])

/-- the same with no condition, for the stage that ends at the frame's end -/
def keepsEndOK (c : Ctx) (st : Stage) (Cs : List AS) (bs : List Nat) : Bool := keepsOK c st Cs [] bs

/-! ### The facts of the stages -/

/-- the digits of a value of the timer -/
def Ctx.ds (c : Ctx) (n : Nat) : Bytes := [(c.d 0, (n / 100).toUInt8), (c.d 1, (n / 10 % 10).toUInt8), (c.d 2, (n % 10).toUInt8)]

/-- the phase -/
def phFacts (c : Ctx) : List Fact :=
  (List.range 21).map fun v => { pre := [(c.ph, v.toUInt8)], alts := [[(c.ph, ((v + 20) % 21).toUInt8)]] }

/-- the star flag's interval timer when the phase wraps -/
def wFacts (c : Ctx) : List Fact :=
  (List.range 256).map fun v => { pre := [(c.ph, 0), (c.w, v.toUInt8)], alts := [[(c.w, (v - 1).toUInt8)]] }

/-- the side timer -/
def tmFacts (c : Ctx) : List Fact :=
  (List.range (c.sy.SideTimerBump.toNat + 1)).map fun v => { pre := [(c.tm, v.toUInt8)], alts := [[(c.tm, (v - 1).toUInt8)]] }

/-- the digits, on the flag's stage in task 2 -/
def digitFacts (c : Ctx) : List Fact :=
  (List.range (c.tmax + 1)).map fun t =>
    { pre := (c.task, 2) :: c.ds t, alts := [(c.task, (if t == 0 then 3 else 2 : UInt8)) :: c.ds (t - 1)] }

/-- the flag's height in task 3 while it rises -/
def yFacts (c : Ctx) : List Fact :=
  ((List.range ((c.r.ram.get! c.y).toNat + 1)).filter (c.lim ≤ ·)).map fun v => { pre := [(c.task, 3), (c.y, v.toUInt8)], alts := [[(c.task, 3), (c.y, (v - 1).toUInt8)]] }

/-- the frame when the flag is up: by the fireworks' counter -/
def upFacts (c : Ctx) : List Fact :=
  (List.range 256).map fun v =>
    { pre := [(c.task, 3), (c.y, (c.lim - 1).toUInt8), (c.i "FireworksCounter", v.toUInt8)],
      alts := if v == 0 || 128 ≤ v then [[(c.task, 4), (c.y, (c.lim - 1).toUInt8), (c.w, c.w0.toUInt8)]] else [[(c.task, 3), (c.y, (c.lim - 1).toUInt8)]] }

/-- the last task -/
def lastFacts (c : Ctx) : List Fact :=
  (List.range (c.w0 + 1)).map fun v =>
    { pre := [(c.task, 4), (c.w, v.toUInt8)],
      alts := if v == 0 then [[(c.task, 4), (c.w, 0)], [(c.task, 5), (c.w, 0)]] else [[(c.task, 4), (c.w, v.toUInt8)]] }

/-! ### Mario's numbers -/

/-- the numbers of Mario at the castle entry -/
def marioStarts (c : Ctx) : List (Nat × UInt8) :=
  ((List.range 64).flatMap fun a => (List.range 16).map fun b =>
    (q5 0 (a * 4).toUInt8 (b * 16).toUInt8 (c.r.ram.get! c.abs) (c.r.ram.get! c.coll), c.sy.SideTimerBump.toUInt8))

/-- what the move leaves from the numbers `q`: the search, no part of the proof -/
def moveOutSearch (c : Ctx) (st : Stage) (T : AS) (q : Nat) : Option Nat :=
  let X := searchOf c.E st [SideChangeEnd.refine (moveIn c q) T] 100000
  (X.ends.toList.head?).bind (moveOutOf c)

/-- all the numbers of Mario from the castle entry: a search, no part of the proof -/
partial def marioClosure (c : Ctx) (st : Stage) (T : AS) (todo : List (Nat × UInt8)) (seen : Std.HashMap Nat Unit) (tbl : Std.HashMap Nat Nat) : Std.HashMap Nat Unit × Std.HashMap Nat Nat :=
  match todo with
  | [] => (seen, tbl)
  | (q, t) :: rest =>
    let n := q + 2 ^ 40 * t.toNat
    if seen.contains n then marioClosure c st T rest seen tbl
    else
      let seen := seen.insert n ()
      match tbl[q]? with
      | some o =>
        match nextMario c t o with
        | some x => marioClosure c st T (x :: rest) seen tbl
        | none => marioClosure c st T rest seen tbl
      | none =>
        match moveOutSearch c st T q with
        | some o =>
          let tbl := tbl.insert q o
          match nextMario c t o with
          | some x => marioClosure c st T (x :: rest) seen tbl
          | none => marioClosure c st T rest seen tbl
        | none => marioClosure c st T rest seen tbl

/-- the coarse state of the move -/
def moveState (pl : Plan) : Option (Stage × AS) :=
  match pl[6]? with
  | none => none
  | some (ms, B, _, _) =>
    match coarse [] B with
    | T :: _ => some (ms.st, T)
    | [] => none

def marioTable (c : Ctx) (pl : Plan) : List (Nat × UInt8) × List (Nat × Nat) :=
  match moveState pl with
  | none => ([], [])
  | some (st, T) =>
    let r := marioClosure c st T (marioStarts c) {} {}
    (r.1.toList.map (fun p => (p.1 % 2 ^ 40, (p.1 / 2 ^ 40).toUInt8)), r.2.toList)

/-- one of Mario's numbers on a frame -/
def marioOK (c : Ctx) (Q : List (Nat × UInt8)) (tbl : List (Nat × Nat)) (p : Nat × UInt8) : Bool :=
  match tbl.lookup p.1 with
  | none => false
  | some o =>
    p.2 != 1 && p.2 != 0 && decide (p.2.toNat ≤ c.sy.SideTimerBump.toNat) && decide ((byteN o 0).toNat ≤ 6) &&
    match nextMario c p.2 o with
    | none => false
    | some x => Q.contains x

/-- the numbers of Mario are closed under a frame -/
def marioCheck (c : Ctx) (Q : List (Nat × UInt8)) (tbl : List (Nat × Nat)) : Bool :=
  Q.all (marioOK c Q tbl)

/-- the collision: where he stands, and where he has moved into the wall -/
def collFacts (c : Ctx) : List Fact :=
  [2, 3, 4].flatMap fun t =>
    { pre := [(c.task, t), (c.x, c.x0), (c.pg, c.pg0)], alts := [[(c.task, t), (c.coll, c.sy.CollisionInit.toUInt8)]] } ::
    (List.range 7).map fun v =>
      { pre := [(c.task, t), (c.x, c.x0 + 1), (c.pg, c.pg0), (c.v, v.toUInt8)], alts := [[(c.task, t), (c.v, 0), (c.tm, c.sy.SideTimerBump.toUInt8), (c.coll, c.r.ram.get! c.coll)]] }

/-- the move of each of Mario's numbers -/
def moveFacts (c : Ctx) (tbl : List (Nat × Nat)) : List Fact :=
  tbl.map fun p => { pre := moveIn c p.1, alts := [moveOut c p.2], plain := true }

/-- what the check of a frame is about -/
structure Data where
  B0 : List AS
  pl : Plan
  Q : List (Nat × UInt8)
  tbl : List (Nat × Nat)

def Data.B (d : Data) (j : Nat) : List AS :=
  match d.pl[j]? with
  | some (_, B, _, _) => B
  | none => []

def dataOf (c : Ctx) : Data :=
  let B0 := frameStarts c
  let pl := planFrom c B0
  let r := marioTable c pl
  { B0, pl, Q := r.1, tbl := r.2 }

/-- the facts of the stages: the bytes that their walks need known, and the facts -/
def factSpec (c : Ctx) (d : Data) : Nat → List (List Nat × List Fact)
  | 4 => [([], phFacts c ++ wFacts c ++ tmFacts c)]
  | 6 => [([], moveFacts c d.tbl)]
  | 8 => [([], [c.x0, c.x0 + 1].map fun a => { pre := [(c.x, a), (c.pg, c.pg0)], alts := [[(c.x, a), (c.pg, c.pg0)]] })]
  | 9 => [([], collFacts c)]
  | 10 => [([], digitFacts c), (coarseKey c 10, yFacts c ++ upFacts c ++ lastFacts c)]
  | _ => []

/-- the bytes that the stages keep: the bytes that their walks need known, what holds at the start, the bytes -/
def keepSpec (c : Ctx) : Nat → List (List Nat × Bytes × List Nat)
  | 4 => ([], [], [c.y, c.task] ++ c.digits ++ [c.v, c.fF, c.ff, c.abs, c.coll, c.rs, c.md]) ::
      (List.range 20).map fun u => ([], [(c.ph, (u + 1).toUInt8)], [c.w])
  | 6 => [([], [], [c.ph, c.w, c.y, c.task] ++ c.digits ++ [c.coll, c.tm])]
  | 7 => [([], [], c.ruled ++ [c.x, c.pg])]
  | 8 => [([], [(c.x, c.x0), (c.pg, c.pg0)], c.ruled), ([], [(c.x, c.x0 + 1), (c.pg, c.pg0)], c.ruled)]
  | 9 => [2, 3, 4].flatMap fun t =>
      [([], [(c.task, t), (c.x, c.x0), (c.pg, c.pg0)], [c.ph, c.w, c.y, c.v, c.fF, c.ff, c.abs, c.tm, c.rs, c.md] ++ c.digits),
       ([], [(c.task, t), (c.x, c.x0 + 1), (c.pg, c.pg0)], [c.ph, c.w, c.y, c.fF, c.ff, c.abs, c.rs, c.md] ++ c.digits)]
  | 10 =>
      [([], [(c.task, 2)], [c.ph, c.w, c.y, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md]),
       (coarseKey c 10, [(c.task, 3)], [c.ph, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md] ++ c.digits),
       (coarseKey c 10, [(c.task, 4)], [c.ph, c.y, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md] ++ c.digits)] ++
      (((List.range ((c.r.ram.get! c.y).toNat + 1)).filter (c.lim ≤ ·)).map fun v => (coarseKey c 10, [(c.task, 3), (c.y, v.toUInt8)], [c.w])) ++
      ((List.range 127).map fun v => (coarseKey c 10, [(c.task, 3), (c.y, (c.lim - 1).toUInt8), (c.i "FireworksCounter", (v + 1).toUInt8)], [c.w]))
  | j => [(coarseKey c j, [], c.ruled)]

/-- the walks of one stage that ends at a place -/
def stageOK (c : Ctx) (d : Data) (j : Nat) : Bool :=
  match d.pl[j]? with
  | none => false
  | some (ms, B, nx, t) =>
    ms.st.cut == some (cutOf c.sy j) && ms.st.alt == altOf c.sy j && ms.refs == refsOf c j &&
    nx.all (fun D => (d.B (nextIdx c.sy j D.pc)).any (D.le ·)) &&
    walkAll (cfgFrom c.sy c.E ms.st t) ms.st (B.flatMap fun S => ms.refs.map fun r => SideChangeEnd.refine r S) (coverKey (ms.key ++ varKey c) nx) &&
    (factSpec c d j).all (fun e =>
      let Cs := coarse e.1 B
      B.all (fun S => Cs.any (S.le ·)) && e.2.all (factOK c ms.st Cs)) &&
    (keepSpec c j).all (fun e =>
      let Cs := coarse e.1 B
      B.all (fun S => Cs.any (S.le ·)) && keepsOK c ms.st Cs e.2.1 e.2.2)

/-- the walks of a stage that ends at the frame's end: the stage 13 ends the frame not paused, the stage 15 paused (`p`) -/
def endStageOK (c : Ctx) (d : Data) (j : Nat) (p : Bool) : Bool :=
  match d.pl[j]? with
  | none => false
  | some (ms, B, _, t) =>
    ms.st.cut == none && ms.refs == [[]] &&
    walkAll (cfgFrom c.sy c.E ms.st t) ms.st (B.flatMap fun S => ms.refs.map fun r => SideChangeEnd.refine r S) (fun X => coverEnd c d.B0 X && pausedBit c X == some p) &&
    (let Cs := coarse (coarseKey c j) B
     B.all (fun S => Cs.any (S.le ·)) && keepsEndOK c ms.st Cs c.ruled)

/-- the machine is one of the state: as a program -/
def covers (S : AS) (m : Machine) : Bool :=
  m.pc == S.pc && m.s == S.s && m.vblank == S.vb && m.nmiPending == S.nmi && decide (S.lo ≤ m.fdot) && decide (m.fdot ≤ S.hi) && m.sprite0 == s0f m.fdot &&
    m.ppuCtrl &&& S.ppuCtrl.k == S.ppuCtrl.v &&& S.ppuCtrl.k && !m.padStrobe && !m.halted && !m.trk &&
    (List.range 2048).all fun i => m.ram.get! i &&& (S.getK i).k == (S.getK i).v &&& (S.getK i).k

/-- the bytes of a state that a machine does not have: as a program -/
def coverDiff (S : AS) (m : Machine) : List Nat :=
  (List.range 2048).filter fun i => m.ram.get! i &&& (S.getK i).k != (S.getK i).v &&& (S.getK i).k

/-- the bytes that say the level has not changed, and that the star flag is in the first slot -/
def startFacts (c : Ctx) : Bytes :=
  [((c.sy.LevelNumber &&& 0x7FF).toNat, 0), ((c.sy.WorldNumber &&& 0x7FF).toNat, 0), (((c.nm.ad "Enemy_ID" + (0 : Nat).toUInt16) &&& 0x7FF).toNat, c.nm.vl "StarFlagObject")]

/-- what the rest of the proof needs of the numbers -/
def basicOK (c : Ctx) (d : Data) : Bool :=
  c.E.pad.v == AB.top.v && c.E.pad.k == AB.top.k && decide (c.gps < 2048) && c.ruled.all (fun b => decide (b < 2048)) &&
  d.B0.all (fun S => (d.B 0).any (S.le ·)) && d.B0.all (fun S => knows S (startFacts c)) && (startFacts c).all (fun p => decide (p.1 < 2048)) &&
  decide (1 ≤ c.lim) && decide (c.lim ≤ 255) && decide (c.lim + 30 ≤ (c.r.ram.get! c.y).toNat) && decide (c.w0 ≤ 255) && decide ((c.r.ram.get! c.y).toNat ≤ 255) && decide (c.tmax ≤ 999)

/-- **The whole check on the ROM.** -/
def flagCheck (c : Ctx) (d : Data) : Bool :=
  (List.range 13).all (stageOK c d) && stageOK c d 14 && endStageOK c d 13 false && endStageOK c d 15 true && marioCheck c d.Q d.tbl && basicOK c d

/-- the machine is one of the states `B0`, and its numbers are those of the rule: as a program -/
def goodOK (c : Ctx) (d : Data) (m : Machine) : Bool :=
  let v := fun (i : Nat) => m.ram.get! i
  d.B0.any (fun S => covers S m) && decide ((v c.ph).toNat < 21) && (v c.task == 2 || v c.task == 3 || v c.task == 4) &&
    (List.range (c.tmax + 1)).any (fun t => (c.ds t).all fun p => v p.1 == p.2) &&
    d.Q.any (fun p => p.1 == q5 (v c.v) (v c.fF) (v c.ff) (v c.abs) (v c.coll) && p.2 == v c.tm) &&
    v c.rs == c.r.ram.get! c.rs && v c.md == c.r.ram.get! c.md &&
    (v c.task == 4 || (decide (c.lim - 1 ≤ (v c.y).toNat) && decide ((v c.y).toNat ≤ (c.r.ram.get! c.y).toNat))) &&
    (v c.task != 4 || decide ((v c.w).toNat ≤ c.w0))

/-! ## What the walks give -/

open SideChangeEnd (Quiet refine sim_refines two_le)

/-- `m'` is the machine when `m` first comes to one of `cut`, inside its frame -/
def Next (cut : List UInt16) (m m' : Machine) : Prop := ∃ j, Arr cut m j ∧ m' = stN j m

theorem Next.unique {c : List UInt16} {m a b : Machine} (h1 : Next c m a) (h2 : Next c m b) : a = b := by
  obtain ⟨j, h3, rfl⟩ := h1
  obtain ⟨k, h4, rfl⟩ := h2
  rw [h3.unique h4]

section
variable {C : Cfg} {st : Stage} {l : List AS} {stop : AS → Bool} {F : Nat × UInt8}

theorem walkAll_cut {cut : UInt16} (h : walkAll C st l stop = true) (hc : st.cut = some cut) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} (hA : A ∈ l) {m : Machine} (hs : Sim C.E F A m) :
    ∃ m', Next st.cuts m m' ∧ ∃ B, stop B = true ∧ B.k = A.k ∧ Sim C.E F B m' := by
  unfold walkAll at h
  rw [hc] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hsz : ∀ p ∈ st.spl, p.2 < 2048 := fun p hp => by simpa using List.all_eq_true.1 h1 p hp
  have h4 := List.all_eq_true.1 h3 A hA
  obtain ⟨j, hj, B, g1, g2, g3⟩ := cwalk_run h2 hops hT hsz dotsPerFrame A m ⟨hs, walkFuel, h4⟩ (by omega)
  exact ⟨_, ⟨j, hj, rfl⟩, B, g1, g2, g3⟩

theorem walkAll_end (h : walkAll C st l stop = true) (hc : st.cut = none) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} (hA : A ∈ l) {m : Machine} (hs : Sim C.E F A m)
    {f n : Nat} (hf : m.frame = f) (hd : dotsPerFrame ≤ m.fdot + 3 * n) :
    (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧ ∃ B, stop B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 := by
  unfold walkAll at h
  rw [hc] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hsz : ∀ p ∈ st.spl, p.2 < 2048 := fun p hp => by simpa using List.all_eq_true.1 h1 p hp
  have h4 := List.all_eq_true.1 h3 A hA
  exact ewalk_run h2 hops hT hsz n A m ⟨hs, walkFuel, h4⟩ hf hd

end

theorem quiet_of_knows {E : Env} {F : Nat × UInt8} {X : AS} {m : Machine} {l : Bytes} (hs : Sim E F X m) (hsz : ∀ p ∈ l, p.1 < 2048) (h : knows X l = true) : Quiet l m := by
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  have h2 := isK_eq h1.1 (hs.ram p.1 (hsz p hp))
  rw [h2, h1.2]

/-- the machine is in one of the states -/
abbrev AtL (E : Env) (f : Nat) (B : List AS) (m : Machine) : Prop := ∃ S ∈ B, Sim E (f, 2) S m

/-- from each state of `B` with one of `refs`, the machine comes to the first of `cut` in a state of `nx` at that place -/
def CoverP (E : Env) (cut : List UInt16) (B : List AS) (nx : UInt16 → List AS) (refs : List Bytes) : Prop :=
  ∀ f m, AtL E f B m → ∀ r ∈ refs, Quiet r m → ∃ m', Next cut m m' ∧ AtL E f (nx m'.pc) m'

/-- under `pre`, one of `alts` holds when the machine comes to the first of `cut` -/
def FactP (E : Env) (cut : List UInt16) (B : List AS) (fa : Fact) : Prop :=
  ∀ f m, AtL E f B m → Quiet fa.pre m → ∀ m', Next cut m m' → ∃ a ∈ fa.alts, Quiet a m'

/-- under `pre`, the byte `b` is the same when the machine comes to the first of `cut` -/
def KeepP (E : Env) (cut : List UInt16) (B : List AS) (pre : Bytes) (b : Nat) : Prop :=
  ∀ f m, AtL E f B m → Quiet pre m → ∀ m', Next cut m m' → m'.ram.get! b = m.ram.get! b

/-- the machine `e` is where `m` ends its frame, with enough fuel -/
def EndsAt (m e : Machine) : Prop := ∃ n, dotsPerFrame ≤ m.fdot + 3 * n ∧ e = (go (runUntilFrame (m.frame + 1) n) m).2

/-- the bit 0 of the byte `g`: the game is paused when `g` is the pause status -/
def bit0 (g : Nat) (m : Machine) : Bool := m.ram.get! g &&& 0x01 != 0

/-- from each state of `B`, for every fuel that is enough, the frame ends in a state of `nx`, with the bit 0 of the byte `g` equal to `p` -/
def EndCoverP (E : Env) (B nx : List AS) (g : Nat) (p : Bool) : Prop :=
  ∀ m, AtL E m.frame B m → ∀ e, EndsAt m e → e.frame = m.frame + 1 ∧ AtL E (m.frame + 1) nx e ∧ bit0 g e = p

def EndKeepP (E : Env) (B : List AS) (b : Nat) : Prop :=
  ∀ m, AtL E m.frame B m → ∀ e, EndsAt m e → e.ram.get! b = m.ram.get! b

section
variable {c : Ctx} {st : Stage}

theorem sim_le_any {E : Env} {F : Nat × UInt8} {key : List Nat} {nx : List AS} {X : AS} {m : Machine} (h : coverKey key nx X = true) (hs : Sim E F X m) : ∃ D ∈ nx, Sim E F D m := by
  obtain ⟨D, hD, h2⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at h2
  exact ⟨D, hD, sim_le h2.2 hs⟩

theorem coverP_of {ms : Main} {B nx : List AS} {t : Array AS} {key : List Nat} {cut : UInt16} (hc : ms.st.cut = some cut)
    (h : walkAll (cfgFrom c.sy c.E ms.st t) ms.st (B.flatMap fun S => ms.refs.map fun r => refine r S) (coverKey key nx) = true) : CoverP c.E ms.st.cuts B (fun _ => nx) ms.refs := by
  intro f m ⟨S, hS, hs⟩ r hr hq
  have hA : refine r S ∈ (B.flatMap fun S => ms.refs.map fun r => refine r S) :=
    List.mem_flatMap.2 ⟨S, hS, List.mem_map.2 ⟨r, hr, rfl⟩⟩
  obtain ⟨m', g1, X, g2, _, g3⟩ := walkAll_cut (C := cfgFrom c.sy c.E ms.st t) (F := (f, 2)) h hc rfl two_le hA (sim_refines hq hs)
  exact ⟨m', g1, sim_le_any g2 g3⟩

theorem atL_coarse {E : Env} {f : Nat} {B Cs : List AS} {m : Machine} (h : B.all (fun S => Cs.any (S.le ·)) = true) (ha : AtL E f B m) : AtL E f Cs m := by
  obtain ⟨S, hS, hs⟩ := ha
  obtain ⟨T, hT, hle⟩ := List.any_eq_true.1 (List.all_eq_true.1 h S hS)
  exact ⟨T, hT, sim_le hle hs⟩

theorem cfgFrom_E (sy : Syms) (E : Env) (st : Stage) (t : Array AS) : (cfgFrom sy E st t).E = E := rfl
theorem cfgFrom_ops (sy : Syms) (E : Env) (st : Stage) (t : Array AS) : (cfgFrom sy E st t).ops = (aRows (cfgFrom sy E st t).E).toArray := rfl

theorem walkOK_cut {sy : Syms} {E : Env} {st : Stage} {t : Array AS} {cut : UInt16} {A : AS} {stop : AS → Bool} {F : Nat × UInt8} (h : walkOK (cfgFrom sy E st t) st A stop = true) (hc : st.cut = some cut) (hT : 2 ≤ F.2.toNat)
    {m : Machine} (hs : Sim E F A m) : ∃ m', Next st.cuts m m' ∧ ∃ B, stop B = true ∧ Sim E F B m' := by
  have hs2 : Sim (cfgFrom sy E st t).E F A m := by rw [cfgFrom_E]; exact hs
  obtain ⟨m2, g1, X, g2, _, g3⟩ := walkAll_cut h hc (cfgFrom_ops sy E st t) hT (List.mem_singleton.2 rfl) hs2
  rw [cfgFrom_E] at g3
  exact ⟨m2, g1, X, g2, g3⟩

theorem factP_of {Cs : List AS} {cut : UInt16} (hc : st.cut = some cut) {fa : Fact} (h : factOK c st Cs fa = true) : FactP c.E st.cuts Cs fa := by
  intro f m ⟨T, hT, hs⟩ hq m' hn
  simp only [factOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  have h2 := h1 T hT
  have key : ∀ t : Array AS, walkOK (cfgFrom c.sy c.E st t) st (refine fa.pre T) (fun X => fa.alts.any (knows X)) = true → ∃ a ∈ fa.alts, Quiet a m' := by
    intro t hw
    obtain ⟨m2, g1, X, g2, g3⟩ := walkOK_cut (F := (f, 2)) hw hc two_le (sim_refines hq hs)
    rw [g1.unique hn] at g3
    obtain ⟨a, ha, g4⟩ := List.any_eq_true.1 g2
    exact ⟨a, ha, quiet_of_knows g3 (fun p hp => by simpa using h0 a ha p hp) g4⟩
  split at h2
  · exact key _ h2
  · exact key _ h2

/-- a state with the counter followed, from the same state -/
theorem sim_rk {E : Env} {f : Nat} {A : AS} {m : Machine} {b : Nat} (hs : Sim E (f, 2) A m) (hb : b < 2048) :
    Sim { E with rkI := b } (f, m.ram.get! b) (rkState b A) m := by
  have h1 : Sim E (f, 2) (A.setK b AB.top) m := sim_refine hs (mem_top _)
  exact ⟨h1.a, h1.x, h1.y, h1.p, h1.s, h1.pc, h1.prg, h1.mask, h1.ppuCtrl, h1.ppuMask, h1.vb, h1.nmi, h1.s0, h1.lo, h1.hi, h1.lim, h1.pad, h1.padShift, h1.strobe, h1.halted, h1.trk, h1.size, h1.ram,
    h1.dg, h1.szR, h1.szK, h1.fr, fun _ => rfl⟩

theorem keep_of_walks {b : Nat} {cut : UInt16} {T : AS} {t : Array AS} (hc : st.cut = some cut) (hb : b < 2048)
    (h1 : walkOK (cfgFrom c.sy { c.E with rkI := b } st (t.map (rkState b))) st (rkState b T) (fun Y => Y.rk && !Y.spent) = true)
    (h2 : walkOK (cfgFrom c.sy c.E st (t.map fun A => A.setK b (AB.known 0))) st (T.setK b (AB.known 0)) (fun Y => knows Y [(b, 0)]) = true)
    (h3 : walkOK (cfgFrom c.sy c.E st (t.map fun A => A.setK b (AB.known 1))) st (T.setK b (AB.known 1)) (fun Y => knows Y [(b, 1)]) = true)
    {f : Nat} {m m' : Machine} (hs : Sim c.E (f, 2) T m) (hn : Next st.cuts m m') : m'.ram.get! b = m.ram.get! b := by
  have hbsz : ∀ (v : UInt8), ∀ p ∈ [(b, v)], p.1 < 2048 := by
    intro v p hp
    rw [List.mem_singleton.1 hp]
    exact hb
  by_cases h0 : m.ram.get! b = 0
  · have hs2 := sim_refine hs (v := AB.known 0) (by rw [h0]; exact mem_known_self _)
    obtain ⟨m2, g1, X, g2, g3⟩ := walkOK_cut (F := (f, 2)) h2 hc two_le hs2
    rw [g1.unique hn] at g3
    have := quiet_of_knows g3 (hbsz 0) g2 (b, 0) (List.mem_singleton.2 rfl)
    rw [h0]
    exact this
  by_cases h01 : m.ram.get! b = 1
  · have hs2 := sim_refine hs (v := AB.known 1) (by rw [h01]; exact mem_known_self _)
    obtain ⟨m2, g1, X, g2, g3⟩ := walkOK_cut (F := (f, 2)) h3 hc two_le hs2
    rw [g1.unique hn] at g3
    have := quiet_of_knows g3 (hbsz 1) g2 (b, 1) (List.mem_singleton.2 rfl)
    rw [h01]
    exact this
  · have hT : 2 ≤ (m.ram.get! b).toNat := by
      have a0 : (m.ram.get! b).toNat ≠ 0 := fun e => h0 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      have a1 : (m.ram.get! b).toNat ≠ 1 := fun e => h01 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      omega
    obtain ⟨m2, g1, X, g2, g3⟩ := walkOK_cut (F := (f, m.ram.get! b)) h1 hc hT (sim_rk hs hb)
    rw [g1.unique hn] at g3
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at g2
    have := g3.rkv g2.1
    rw [g2.2] at this
    exact this

theorem keepP_of {Cs : List AS} {cut : UInt16} (hc : st.cut = some cut) {pre : Bytes} {bs : List Nat} (h : keepsOK c st Cs pre bs = true) {b : Nat} (hb : b ∈ bs) : KeepP c.E st.cuts Cs pre b := by
  intro f m ⟨T0, hT, hs⟩ hq m' hn
  simp only [keepsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, ⟨h1, h2⟩, h3⟩ := h T0 hT b hb
  exact keep_of_walks hc h0 h1 h2 h3 (sim_refines hq hs) hn

end

/-! ### The stage that ends the frame -/

section
variable {c : Ctx} {st : Stage}

theorem walkOK_end {sy : Syms} {E : Env} {st : Stage} {t : Array AS} {A : AS} {stop : AS → Bool} {F : Nat × UInt8} (h : walkOK (cfgFrom sy E st t) st A stop = true) (hc : st.cut = none) (hT : 2 ≤ F.2.toNat)
    {m : Machine} (hs : Sim E F A m) {f n : Nat} (hf : m.frame = f) (hd : dotsPerFrame ≤ m.fdot + 3 * n) :
    ∃ B, stop B = true ∧ Sim E F B (go (runUntilFrame (f + 1) n) m).2 := by
  have hs2 : Sim (cfgFrom sy E st t).E F A m := by rw [cfgFrom_E]; exact hs
  obtain ⟨_, X, g2, _, g3⟩ := walkAll_end h hc (cfgFrom_ops sy E st t) hT (List.mem_singleton.2 rfl) hs2 hf hd
  rw [cfgFrom_E] at g3
  exact ⟨X, g2, g3⟩

/-- the bit 0 of the byte `g` of a machine, from a state that knows it -/
theorem bit0_of {E : Env} {F : Nat × UInt8} {X : AS} {m : Machine} {g : Nat} {p : Bool} (hg : g < 2048) (hs : Sim E F X m) (h : (X.getK g).bit 0x01 = some p) :
    bit0 g m = p := by
  have t := TR_bit 0x01 (hs.ram g hg)
  rw [h] at t
  rcases t with t | t
  · cases t
  · exact (Option.some.inj t).symm

theorem endCover_of {ms : Main} {B nx : List AS} {t : Array AS} (hc : ms.st.cut = none) (hr : ms.refs = [[]]) {p : Bool} (hg : c.gps < 2048)
    (h : walkAll (cfgFrom c.sy c.E ms.st t) ms.st (B.flatMap fun S => ms.refs.map fun r => refine r S) (fun X => coverEnd c nx X && pausedBit c X == some p) = true) :
    EndCoverP c.E B nx c.gps p := by
  intro m ⟨S, hS, hs⟩ e ⟨n, hd, he⟩
  have hA : refine [] S ∈ (B.flatMap fun S => ms.refs.map fun r => refine r S) :=
    List.mem_flatMap.2 ⟨S, hS, List.mem_map.2 ⟨[], by rw [hr]; exact List.mem_singleton.2 rfl, rfl⟩⟩
  have hs2 : Sim (cfgFrom c.sy c.E ms.st t).E (m.frame, 2) (refine [] S) m := hs
  obtain ⟨g0, X, g1, g2, g3⟩ := walkAll_end (C := cfgFrom c.sy c.E ms.st t) (F := (m.frame, 2)) h hc (cfgFrom_ops _ _ _ _) two_le hA hs2 rfl hd
  rw [← he] at g0 g3
  simp only [Bool.and_eq_true, beq_iff_eq] at g1
  refine ⟨g0, ?_, bit0_of hg g3 g1.2⟩
  have hbase : Sim c.E (m.frame + 1, 2) ({ X with k := 0 } : AS) e := by
    have g4 : Sim c.E (m.frame, 2) X e := g3
    refine { g4 with fr := ?_, rkv := ?_ }
    · show e.frame = m.frame + 1 + 0
      omega
    · exact g4.rkv
  exact sim_le_any g1.1 hbase

theorem keepEnd_of {Cs : List AS} (hc : st.cut = none) {bs : List Nat} (h : keepsEndOK c st Cs bs = true) {b : Nat} (hb : b ∈ bs) : EndKeepP c.E Cs b := by
  intro m ⟨T0, hT, hs⟩ e ⟨n, hd, he⟩
  simp only [keepsEndOK, keepsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, ⟨h1, h2⟩, h3⟩ := h T0 hT b hb
  have hsT : Sim c.E (m.frame, 2) (refine [] T0) m := hs
  by_cases h00 : m.ram.get! b = 0
  · have hs2 := sim_refine hsT (v := AB.known 0) (by rw [h00]; exact mem_known_self _)
    obtain ⟨X, g2, g3⟩ := walkOK_end (F := (m.frame, 2)) h2 hc two_le hs2 rfl hd
    rw [← he] at g3
    have := quiet_of_knows g3 (fun p hp => by rw [List.mem_singleton.1 hp]; exact h0) g2 (b, 0) (List.mem_singleton.2 rfl)
    rw [h00]
    exact this
  by_cases h01 : m.ram.get! b = 1
  · have hs2 := sim_refine hsT (v := AB.known 1) (by rw [h01]; exact mem_known_self _)
    obtain ⟨X, g2, g3⟩ := walkOK_end (F := (m.frame, 2)) h3 hc two_le hs2 rfl hd
    rw [← he] at g3
    have := quiet_of_knows g3 (fun p hp => by rw [List.mem_singleton.1 hp]; exact h0) g2 (b, 1) (List.mem_singleton.2 rfl)
    rw [h01]
    exact this
  · have hT2 : 2 ≤ (m.ram.get! b).toNat := by
      have a0 : (m.ram.get! b).toNat ≠ 0 := fun e => h00 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      have a1 : (m.ram.get! b).toNat ≠ 1 := fun e => h01 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      omega
    obtain ⟨X, g2, g3⟩ := walkOK_end (F := (m.frame, m.ram.get! b)) h1 hc hT2 (sim_rk hsT h0) rfl hd
    rw [← he] at g3
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at g2
    have := g3.rkv g2.1
    rw [g2.2] at this
    exact this

end

/-! ### What the whole check gives -/

/-- **What the check gives on the machines of a frame.** The stages 0 to 12 and 14 end at a place (`cov`), the stages 13 and 15 at the frame's end: the stage 13 not
paused, the stage 15 paused. -/
structure Checked (c : Ctx) (d : Data) : Prop where
  cov : ∀ j, (j < 13 ∨ j = 14) → CoverP c.E (cutsOf c.sy j) (d.B j) (fun pc => d.B (nextIdx c.sy j pc)) (refsOf c j)
  fact : ∀ j, (j < 13 ∨ j = 14) → ∀ e ∈ factSpec c d j, ∀ f ∈ e.2, FactP c.E (cutsOf c.sy j) (d.B j) f
  keep : ∀ j, (j < 13 ∨ j = 14) → ∀ e ∈ keepSpec c j, ∀ b ∈ e.2.2, KeepP c.E (cutsOf c.sy j) (d.B j) e.2.1 b
  endCov : EndCoverP c.E (d.B 13) d.B0 c.gps false
  endKeep : ∀ b ∈ c.ruled, EndKeepP c.E (d.B 13) b
  pauseCov : EndCoverP c.E (d.B 15) d.B0 c.gps true
  pauseKeep : ∀ b ∈ c.ruled, EndKeepP c.E (d.B 15) b
  mario : ∀ p ∈ d.Q, marioOK c d.Q d.tbl p = true
  pad : c.E.pad = AB.top
  gpsI : c.gps < 2048
  start : d.B0.all (fun S => (d.B 0).any (S.le ·)) = true
  known : ∀ S ∈ d.B0, knows S (startFacts c) = true
  knownI : ∀ p ∈ startFacts c, p.1 < 2048
  lim1 : 1 ≤ c.lim
  lim2 : c.lim ≤ 255
  y0 : c.lim + 30 ≤ (c.r.ram.get! c.y).toNat
  w0 : c.w0 ≤ 255
  tmax : c.tmax ≤ 999

theorem factP_mono {E : Env} {cut : List UInt16} {B Cs : List AS} {f : Fact} (h : B.all (fun S => Cs.any (S.le ·)) = true) (hf : FactP E cut Cs f) : FactP E cut B f :=
  fun fr m ha hq m' hn => hf fr m (atL_coarse h ha) hq m' hn

theorem keepP_mono {E : Env} {cut : List UInt16} {B Cs : List AS} {pre : Bytes} {b : Nat} (h : B.all (fun S => Cs.any (S.le ·)) = true) (hf : KeepP E cut Cs pre b) : KeepP E cut B pre b :=
  fun fr m ha hq m' hn => hf fr m (atL_coarse h ha) hq m' hn

theorem stage_sound {c : Ctx} {d : Data} {j : Nat} (h : stageOK c d j = true) :
    CoverP c.E (cutsOf c.sy j) (d.B j) (fun pc => d.B (nextIdx c.sy j pc)) (refsOf c j) ∧
    (∀ e ∈ factSpec c d j, ∀ f ∈ e.2, FactP c.E (cutsOf c.sy j) (d.B j) f) ∧
    (∀ e ∈ keepSpec c j, ∀ b ∈ e.2.2, KeepP c.E (cutsOf c.sy j) (d.B j) e.2.1 b) := by
  unfold stageOK at h
  cases hj : d.pl[j]? with
  | none =>
    rw [hj] at h
    cases h
  | some x =>
    obtain ⟨ms, B, nx, t⟩ := x
    rw [hj] at h
    have hB : d.B j = B := by simp [Data.B, hj]
    rw [hB]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h1a⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have hcuts : ms.st.cuts = cutsOf c.sy j := by simp [Stage.cuts, cutsOf, h1, h1a]
    refine ⟨?_, ?_, ?_⟩
    · have g := coverP_of (c := c) (key := ms.key ++ varKey c) h1 h4
      rw [h2, hcuts] at g
      intro f m ha r hr hq
      obtain ⟨m', g1, S, hS, g2⟩ := g f m ha r hr hq
      obtain ⟨T, hT, hle⟩ := List.any_eq_true.1 (h3 S hS)
      have hpc : m'.pc = S.pc := g2.pc
      refine ⟨m', g1, T, ?_, sim_le hle g2⟩
      rw [hpc]
      exact hT
    · intro e he f hf
      have g := h5 e he
      obtain ⟨g1, g2⟩ := g
      rw [← hcuts]
      exact factP_mono (List.all_eq_true.2 g1) (factP_of h1 (g2 f hf))
    · intro e he b hb
      have g := h6 e he
      obtain ⟨g1, g2⟩ := g
      rw [← hcuts]
      exact keepP_mono (List.all_eq_true.2 g1) (keepP_of h1 g2 hb)

theorem endStage_sound {c : Ctx} {d : Data} {j : Nat} {p : Bool} (h : endStageOK c d j p = true) (hg : c.gps < 2048) :
    EndCoverP c.E (d.B j) d.B0 c.gps p ∧ ∀ b ∈ c.ruled, EndKeepP c.E (d.B j) b := by
  unfold endStageOK at h
  cases hj : d.pl[j]? with
  | none =>
    rw [hj] at h
    cases h
  | some x =>
    obtain ⟨ms, B, nx, t⟩ := x
    rw [hj] at h
    have hB : d.B j = B := by simp [Data.B, hj]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4, b5⟩ := h
    refine ⟨?_, ?_⟩
    · rw [hB]
      exact endCover_of b1 b2 hg b3
    · intro b hb
      rw [hB]
      intro m ha e he
      exact keepEnd_of b1 b5 hb m (atL_coarse (List.all_eq_true.2 b4) ha) e he

theorem checked_of_check {c : Ctx} {d : Data} (h : flagCheck c d = true) : Checked c d := by
  simp only [flagCheck, basicOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h14⟩, h13⟩, h15⟩, h3⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a0⟩, ag⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩⟩ := h
  have hpad : c.E.pad = AB.top := by
    cases hE : c.E.pad with
    | mk v k =>
      rw [hE] at a1 a0
      simp only at a1 a0
      rw [a1, a0]
  have hs : ∀ j, (j < 13 ∨ j = 14) → stageOK c d j = true := fun j hj => by
    rcases hj with hj | rfl
    · exact h1 j (List.mem_range.2 hj)
    · exact h14
  have e13 := endStage_sound h13 ag
  have e15 := endStage_sound h15 ag
  exact ⟨fun j hj => (stage_sound (hs j hj)).1, fun j hj => (stage_sound (hs j hj)).2.1, fun j hj => (stage_sound (hs j hj)).2.2, e13.1, e13.2, e15.1, e15.2,
    List.all_eq_true.1 h3, hpad, ag, List.all_eq_true.2 a3, a4, a5, a6, a7, a8, a9, a11⟩

/-! ## One frame -/

/-- the numbers that the rule follows, on a machine at the start of a frame -/
structure Ok (c : Ctx) (d : Data) (m : Machine) : Prop where
  ph : (m.ram.get! c.ph).toNat < 21
  task : m.ram.get! c.task = 2 ∨ m.ram.get! c.task = 3 ∨ m.ram.get! c.task = 4
  digits : ∃ t, t ≤ c.tmax ∧ Quiet (c.ds t) m
  mario : (q5 (m.ram.get! c.v) (m.ram.get! c.fF) (m.ram.get! c.ff) (m.ram.get! c.abs) (m.ram.get! c.coll), m.ram.get! c.tm) ∈ d.Q
  rs : m.ram.get! c.rs = c.r.ram.get! c.rs
  md : m.ram.get! c.md = c.r.ram.get! c.md
  y : m.ram.get! c.task ≠ 4 → c.lim - 1 ≤ (m.ram.get! c.y).toNat ∧ (m.ram.get! c.y).toNat ≤ (c.r.ram.get! c.y).toNat
  w : m.ram.get! c.task = 4 → (m.ram.get! c.w).toNat ≤ c.w0

/-- **The condition on a machine at the start of a frame.** The machine is in one of the states of the frame's start, and the numbers that the rule follows have these values. -/
structure Good (c : Ctx) (d : Data) (m : Machine) : Prop where
  at0 : AtL { c.E with pad := AB.top } m.frame d.B0 m
  ok : Ok c d m

theorem qn {m : Machine} : Quiet [] m := fun _ h => by cases h

theorem qc {m : Machine} {i : Nat} {v : UInt8} {l : Bytes} (h : m.ram.get! i = v) (t : Quiet l m) : Quiet ((i, v) :: l) m := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h
  · exact t p hp

theorem qget {m : Machine} {i : Nat} {v : UInt8} {l : Bytes} (t : Quiet l m) (h : (i, v) ∈ l) : m.ram.get! i = v := t _ h

theorem toNat_small {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem byteN_q5 (a b c d e : UInt8) :
    byteN (q5 a b c d e) 0 = a ∧ byteN (q5 a b c d e) 1 = b ∧ byteN (q5 a b c d e) 2 = c ∧ byteN (q5 a b c d e) 3 = d ∧ byteN (q5 a b c d e) 4 = e := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have key : ∀ (x : UInt8) (n : Nat), n = x.toNat → n.toUInt8 = x := by
    intro x n h
    rw [h]
    simp
  simp only [byteN, q5]
  have p0 : (256 : Nat) ^ 0 = 1 := rfl
  have p1 : (256 : Nat) ^ 1 = 256 := rfl
  have p2 : (256 : Nat) ^ 2 = 65536 := rfl
  have p3 : (256 : Nat) ^ 3 = 16777216 := rfl
  have p4 : (256 : Nat) ^ 4 = 4294967296 := rfl
  rw [p0, p1, p2, p3, p4]
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;> omega

theorem tt (x : UInt8) : x.toNat.toUInt8 = x := by simp

theorem Next.frame {cut : List UInt16} {m m' : Machine} (h : Next cut m m') : m'.frame = m.frame := by
  obtain ⟨j, hj, rfl⟩ := h
  exact hj.frame j (Nat.le_refl _)

theorem atL_fdot {E : Env} {f : Nat} {B : List AS} {m : Machine} (h : AtL E f B m) : m.fdot < dotsPerFrame := by
  obtain ⟨_, _, hs⟩ := h
  exact Nat.lt_of_le_of_lt hs.hi hs.lim

theorem EndsAt.next {cut : List UInt16} {m m' e : Machine} (he : EndsAt m e) (hn : Next cut m m') (hl : m'.fdot < dotsPerFrame) : EndsAt m' e := by
  obtain ⟨n, hd, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hn
  have h1 := hj.dot
  have hjn : j ≤ n := by omega
  have h2 := ruf_steps (f := m.frame) j n m hjn (fun i hi => ⟨hj.frame i (by omega), hj.halted i (by omega)⟩)
  refine ⟨n - j, by omega, ?_⟩
  rw [hj.frame j (Nat.le_refl _), h2]

theorem mem_of_lookup {l : List (Nat × Nat)} {a b : Nat} (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    obtain ⟨u, v⟩ := x
    simp only [List.lookup_cons] at h
    split at h
    · rename_i e
      have e' : a = u := by simpa using e
      obtain rfl := Option.some.inj h
      subst e'
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem sim_anyPad {c : Ctx} {F : Nat × UInt8} {S : AS} {m : Machine} (hs : Sim c.E F S m) : Sim { c.E with pad := AB.top } F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, mem_top _, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩

/-- the bytes of the rule's list -/
theorem ruled_mem (c : Ctx) : c.ph ∈ c.ruled ∧ c.w ∈ c.ruled ∧ c.y ∈ c.ruled ∧ c.task ∈ c.ruled ∧ c.d 0 ∈ c.ruled ∧ c.d 1 ∈ c.ruled ∧ c.d 2 ∈ c.ruled ∧
    c.v ∈ c.ruled ∧ c.fF ∈ c.ruled ∧ c.ff ∈ c.ruled ∧ c.abs ∈ c.ruled ∧ c.coll ∈ c.ruled ∧ c.tm ∈ c.ruled ∧ c.rs ∈ c.ruled ∧ c.md ∈ c.ruled := by
  simp [Ctx.ruled, Ctx.digits, Ctx.mario]

theorem fact1 {E : Env} {cut : List UInt16} {B : List AS} {pre al : Bytes} {pl : Bool} (h : FactP E cut B { pre := pre, alts := [al], plain := pl }) {f : Nat} {m m' : Machine}
    (a : AtL E f B m) (q : Quiet pre m) (n : Next cut m m') : Quiet al m' := by
  obtain ⟨x, hx, hq⟩ := h f m a q m' n
  rw [List.mem_singleton.1 hx] at hq
  exact hq

theorem marioOK_spec {c : Ctx} {Q : List (Nat × UInt8)} {tbl : List (Nat × Nat)} {p : Nat × UInt8} (h : marioOK c Q tbl p = true) :
    ∃ o x, tbl.lookup p.1 = some o ∧ p.2 ≠ 1 ∧ p.2 ≠ 0 ∧ p.2.toNat ≤ c.sy.SideTimerBump.toNat ∧ (byteN o 0).toNat ≤ 6 ∧ nextMario c p.2 o = some x ∧ x ∈ Q := by
  unfold marioOK at h
  split at h
  · cases h
  · rename_i o hl
    split at h
    · simp at h
    · rename_i x hx
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      exact ⟨o, x, hl, h1, h2, h3, h4, hx, by simpa using h5⟩

theorem nextMario_spec {c : Ctx} {t : UInt8} {o : Nat} {x : Nat × UInt8} (h : nextMario c t o = some x) :
    (byteN o 4 = c.x0 + 1 ∧ x = (q5 0 (byteN o 1) (byteN o 2) (byteN o 3) (c.r.ram.get! c.coll), c.sy.SideTimerBump.toUInt8)) ∨
      (byteN o 4 = c.x0 ∧ x = (q5 (byteN o 0) (byteN o 1) (byteN o 2) (byteN o 3) c.sy.CollisionInit.toUInt8, t - 1)) := by
  unfold nextMario at h
  split at h
  · rename_i e
    exact Or.inl ⟨by simpa using e, (Option.some.inj h).symm⟩
  · split at h
    · rename_i _ e
      exact Or.inr ⟨by simpa using e, (Option.some.inj h).symm⟩
    · cases h

theorem pred_byte {t : UInt8} (h : t ≠ 0) : (t.toNat - 1).toUInt8 = t - 1 := by
  have h1 : t.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.1 (by rw [e]; rfl))
  have hl := t.toNat_lt
  apply UInt8.toNat_inj.1
  rw [toNat_small (by omega), UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; simp; omega)]
  simp

theorem sub6 (c : Ctx) : ∀ b ∈ [c.ph, c.w, c.y, c.task] ++ c.digits ++ [c.coll, c.tm], b ∈ c.ruled := by
  intro b hb
  simp only [Ctx.digits, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with ((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl) <;> simp [Ctx.ruled, Ctx.digits, Ctx.mario]

/-- what the first stages of a frame do, up to the star flag's routine. `o` is what the move leaves, `t1` the side timer after the timers -/
structure UpToFlag (c : Ctx) (d : Data) (m m10 : Machine) : Prop where
  at10 : AtL c.E m.frame (d.B 10) m10
  ph : (m10.ram.get! c.ph).toNat = ((m.ram.get! c.ph).toNat + 20) % 21
  w : m10.ram.get! c.w = if m.ram.get! c.ph = 0 then ((m.ram.get! c.w).toNat - 1).toUInt8 else m.ram.get! c.w
  y : m10.ram.get! c.y = m.ram.get! c.y
  task : m10.ram.get! c.task = m.ram.get! c.task
  d0 : m10.ram.get! (c.d 0) = m.ram.get! (c.d 0)
  d1 : m10.ram.get! (c.d 1) = m.ram.get! (c.d 1)
  d2 : m10.ram.get! (c.d 2) = m.ram.get! (c.d 2)
  rs : m10.ram.get! c.rs = c.r.ram.get! c.rs
  md : m10.ram.get! c.md = c.r.ram.get! c.md
  mario : (q5 (m10.ram.get! c.v) (m10.ram.get! c.fF) (m10.ram.get! c.ff) (m10.ram.get! c.abs) (m10.ram.get! c.coll), m10.ram.get! c.tm) ∈ d.Q

/-- the cover of a stage that has one place to end at: the next stage is the one after it -/
theorem Checked.covL {c : Ctx} {d : Data} (hC : Checked c d) {j : Nat} (hj : j < 13) (h1 : j ≠ 1) (h3 : j ≠ 3) :
    ∀ f m, AtL c.E f (d.B j) m → ∀ r ∈ refsOf c j, Quiet r m → ∃ m', Next (cutsOf c.sy j) m m' ∧ AtL c.E f (d.B (j + 1)) m' := by
  intro f m a r hr q
  obtain ⟨m', n, a0⟩ := hC.cov j (Or.inl hj) f m a r hr q
  have a' : AtL c.E f (d.B (nextIdx c.sy j m'.pc)) m' := a0
  have h14 : j ≠ 14 := by omega
  have e : nextIdx c.sy j m'.pc = j + 1 := by
    unfold nextIdx
    simp [h1, h3, h14]
  rw [e] at a'
  exact ⟨m', n, a'⟩

variable {c : Ctx} {d : Data} in
/-- the stages 4 to 9, from the timers to the star flag's routine, from a machine at the timers whose bytes of the rule are those of `m` -/
theorem upToFlag (hC : Checked c d) {m m4 e : Machine} (hm : Ok c d m) (a4 : AtL c.E m.frame (d.B 4) m4) (k4 : ∀ b ∈ c.ruled, m4.ram.get! b = m.ram.get! b)
    (hf : m4.frame = m.frame) (he : EndsAt m4 e) :
    ∃ m10, EndsAt m10 e ∧ m10.frame = m.frame ∧ UpToFlag c d m m10 := by
  have R := ruled_mem c
  obtain ⟨Rph, Rw, Ry, Rt, Rd0, Rd1, Rd2, Rv, RF, Rf, RA, RC, Rtm, Rrs, Rmd⟩ := R
  have tk3 : m.ram.get! c.task = 2 ∨ m.ram.get! c.task = 3 ∨ m.ram.get! c.task = 4 := hm.task
  -- the timers
  obtain ⟨m5, n5, a5⟩ := hC.covL (j := 4) (by decide) (by decide) (by decide) _ m4 a4 [] (List.mem_singleton.2 rfl) qn
  have F4 : ∀ f ∈ phFacts c ++ wFacts c ++ tmFacts c, FactP c.E (cutsOf c.sy 4) (d.B 4) f := hC.fact 4 (by decide) _ (List.mem_singleton.2 rfl)
  have K4 : ∀ b ∈ [c.y, c.task] ++ c.digits ++ [c.v, c.fF, c.ff, c.abs, c.coll, c.rs, c.md], m5.ram.get! b = m4.ram.get! b := fun b hb =>
    hC.keep 4 (by decide) _ List.mem_cons_self b hb _ m4 a4 qn m5 n5
  have ph5 : m5.ram.get! c.ph = (((m.ram.get! c.ph).toNat + 20) % 21).toUInt8 := by
    obtain ⟨al, ha, hq⟩ := F4 { pre := [(c.ph, (m.ram.get! c.ph).toNat.toUInt8)], alts := [[(c.ph, (((m.ram.get! c.ph).toNat + 20) % 21).toUInt8)]] }
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_range.2 hm.ph, rfl⟩))) _ m4 a4 (qc (by rw [k4 _ Rph, tt]) qn) m5 n5
    rw [List.mem_singleton.1 ha] at hq
    exact qget hq (List.mem_singleton.2 rfl)
  have w5 : m5.ram.get! c.w = if m.ram.get! c.ph = 0 then ((m.ram.get! c.w).toNat - 1).toUInt8 else m.ram.get! c.w := by
    by_cases h0 : m.ram.get! c.ph = 0
    · rw [if_pos h0]
      obtain ⟨al, ha, hq⟩ := F4 { pre := [(c.ph, 0), (c.w, (m.ram.get! c.w).toNat.toUInt8)], alts := [[(c.w, ((m.ram.get! c.w).toNat - 1).toUInt8)]] }
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 (m.ram.get! c.w).toNat_lt, rfl⟩))) _ m4 a4
        (qc (by rw [k4 _ Rph, h0]) (qc (by rw [k4 _ Rw, tt]) qn)) m5 n5
      rw [List.mem_singleton.1 ha] at hq
      exact qget hq (List.mem_singleton.2 rfl)
    · rw [if_neg h0]
      have h1 : (m.ram.get! c.ph).toNat ≠ 0 := fun e => h0 (UInt8.toNat_inj.1 (by rw [e]; rfl))
      have hp := hm.ph
      obtain ⟨u, hu⟩ : ∃ u, (m.ram.get! c.ph).toNat = u + 1 := ⟨(m.ram.get! c.ph).toNat - 1, by omega⟩
      have hmem : (([] : List Nat), [(c.ph, (u + 1).toUInt8)], [c.w]) ∈ keepSpec c 4 :=
        List.mem_cons_of_mem _ (List.mem_map.2 ⟨u, List.mem_range.2 (by omega), rfl⟩)
      have := hC.keep 4 (by decide) _ hmem c.w (List.mem_singleton.2 rfl) _ m4 a4 (qc (by rw [k4 _ Rph, ← hu, tt]) qn) m5 n5
      rw [this, k4 _ Rw]
  -- the sprites
  obtain ⟨m6, n6, a6⟩ := hC.covL (j := 5) (by decide) (by decide) (by decide) _ m5 a5 [] (List.mem_singleton.2 rfl) qn
  have k6 : ∀ b ∈ c.ruled, m6.ram.get! b = m5.ram.get! b := fun b hb => hC.keep 5 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m5 a5 qn m6 n6
  have ht := hm.mario
  obtain ⟨o, x, hl, ht1, ht0, ht16, hv6, hx, hxQ⟩ := marioOK_spec (hC.mario _ ht)
  simp only at hl ht1 ht0 ht16 hx
  have tm6 : m6.ram.get! c.tm = ((m.ram.get! c.tm).toNat - 1).toUInt8 := by
    rw [k6 _ Rtm]
    have := fact1 (pre := [(c.tm, (m.ram.get! c.tm).toNat.toUInt8)]) (al := [(c.tm, ((m.ram.get! c.tm).toNat - 1).toUInt8)]) (pl := false)
      (F4 _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩))) a4 (qc (by rw [k4 _ Rtm, tt]) qn) n5
    exact qget this (List.mem_singleton.2 rfl)
  have g6 : ∀ b ∈ [c.v, c.fF, c.ff, c.abs, c.coll, c.rs, c.md], b ∈ c.ruled → m6.ram.get! b = m.ram.get! b := by
    intro b hb hr
    rw [k6 _ hr, K4 _ (List.mem_append_right _ hb), k4 _ hr]
  have bq := byteN_q5 (m.ram.get! c.v) (m.ram.get! c.fF) (m.ram.get! c.ff) (m.ram.get! c.abs) (m.ram.get! c.coll)
  -- the move
  obtain ⟨m7, n7, a7⟩ := hC.covL (j := 6) (by decide) (by decide) (by decide) _ m6 a6 [] (List.mem_singleton.2 rfl) qn
  have M7 := fact1 (h := hC.fact 6 (by decide) _ (List.mem_singleton.2 rfl) _ (List.mem_map.2 ⟨_, mem_of_lookup hl, rfl⟩)) a6
    (by
      simp only [moveIn]
      refine qc ?_ (qc ?_ (qc ?_ (qc ?_ (qc ?_ (qc ?_ (qc ?_ qn))))))
      · rw [g6 _ (by simp) Rv, bq.1]
      · rw [g6 _ (by simp) RF, bq.2.1]
      · rw [g6 _ (by simp) Rf, bq.2.2.1]
      · rw [g6 _ (by simp) RA, bq.2.2.2.1]
      · rw [g6 _ (by simp) RC, bq.2.2.2.2]
      · rw [g6 _ (by simp) Rrs, hm.rs]
      · rw [g6 _ (by simp) Rmd, hm.md]) n7
  have K6 : ∀ b ∈ [c.ph, c.w, c.y, c.task] ++ c.digits ++ [c.coll, c.tm], m7.ram.get! b = m6.ram.get! b := fun b hb =>
    hC.keep 6 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m6 a6 qn m7 n7
  -- the scroll
  have t2 : 2 ≤ (m.ram.get! c.tm).toNat := by
    have h0 : (m.ram.get! c.tm).toNat ≠ 0 := fun e => ht0 (UInt8.toNat_inj.1 (by rw [e]; rfl))
    have h1 : (m.ram.get! c.tm).toNat ≠ 1 := fun e => ht1 (UInt8.toNat_inj.1 (by rw [e]; rfl))
    omega
  have tm7 : m7.ram.get! c.tm = ((m.ram.get! c.tm).toNat - 1).toUInt8 := by rw [K6 _ (by simp), tm6]
  obtain ⟨m8, n8, a8⟩ := hC.covL (j := 7) (by decide) (by decide) (by decide) _ m7 a7 [(c.tm, ((m.ram.get! c.tm).toNat - 2 + 1).toUInt8)]
    (List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩) (qc (by rw [tm7]; congr 1; omega) qn)
  have K7 : ∀ b ∈ c.ruled ++ [c.x, c.pg], m8.ram.get! b = m7.ram.get! b := fun b hb =>
    hC.keep 7 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m7 a7 qn m8 n8
  have x8 : m8.ram.get! c.x = byteN o 4 := by rw [K7 _ (by simp), qget (v := byteN o 4) M7 (by simp [moveOut])]
  have pg8 : m8.ram.get! c.pg = c.pg0 := by rw [K7 _ (by simp), qget (v := c.pg0) M7 (by simp [moveOut])]
  have e8 : ∀ b ∈ [c.ph, c.w, c.y, c.task] ++ c.digits ++ [c.coll, c.tm], m8.ram.get! b = m6.ram.get! b := fun b hb => by
    rw [K7 _ (List.mem_append_left _ (sub6 c b hb)), K6 _ hb]
  -- the offscreen bits
  have hxa : byteN o 4 = c.x0 ∨ byteN o 4 = c.x0 + 1 := by
    rcases nextMario_spec hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h
  have hxm : byteN o 4 ∈ [c.x0, c.x0 + 1] := by rcases hxa with h | h <;> rw [h] <;> simp
  obtain ⟨m9, n9, a9⟩ := hC.covL (j := 8) (by decide) (by decide) (by decide) _ m8 a8 [(c.x, byteN o 4), (c.pg, c.pg0)] (List.mem_map.2 ⟨_, hxm, rfl⟩) (qc x8 (qc pg8 qn))
  have M9 := fact1 (h := hC.fact 8 (by decide) _ (List.mem_singleton.2 rfl) _ (List.mem_map.2 ⟨_, hxm, rfl⟩)) a8 (qc x8 (qc pg8 qn)) n9
  have hk8 : (([] : List Nat), [(c.x, byteN o 4), (c.pg, c.pg0)], c.ruled) ∈ keepSpec c 8 := by
    rcases hxa with h | h
    · rw [h]; exact List.mem_cons_self
    · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have K8 : ∀ b ∈ c.ruled, m9.ram.get! b = m8.ram.get! b := fun b hb => hC.keep 8 (by decide) _ hk8 b hb _ m8 a8 (qc x8 (qc pg8 qn)) m9 n9
  have x9 : m9.ram.get! c.x = byteN o 4 := qget M9 List.mem_cons_self
  have pg9 : m9.ram.get! c.pg = c.pg0 := qget M9 (List.mem_cons_of_mem _ List.mem_cons_self)
  have ph9 : m9.ram.get! c.ph = (((m.ram.get! c.ph).toNat + 20) % 21).toUInt8 := by rw [K8 _ Rph, e8 _ (by simp), k6 _ Rph, ph5]
  have w9 : m9.ram.get! c.w = if m.ram.get! c.ph = 0 then ((m.ram.get! c.w).toNat - 1).toUInt8 else m.ram.get! c.w := by
    rw [K8 _ Rw, e8 _ (by simp), k6 _ Rw, w5]
  have y9 : m9.ram.get! c.y = m.ram.get! c.y := by rw [K8 _ Ry, e8 _ (by simp), k6 _ Ry, K4 _ (by simp), k4 _ Ry]
  have task9 : m9.ram.get! c.task = m.ram.get! c.task := by rw [K8 _ Rt, e8 _ (by simp), k6 _ Rt, K4 _ (by simp), k4 _ Rt]
  have d09 : m9.ram.get! (c.d 0) = m.ram.get! (c.d 0) := by rw [K8 _ Rd0, e8 _ (by simp [Ctx.digits]), k6 _ Rd0, K4 _ (by simp [Ctx.digits]), k4 _ Rd0]
  have d19 : m9.ram.get! (c.d 1) = m.ram.get! (c.d 1) := by rw [K8 _ Rd1, e8 _ (by simp [Ctx.digits]), k6 _ Rd1, K4 _ (by simp [Ctx.digits]), k4 _ Rd1]
  have d29 : m9.ram.get! (c.d 2) = m.ram.get! (c.d 2) := by rw [K8 _ Rd2, e8 _ (by simp [Ctx.digits]), k6 _ Rd2, K4 _ (by simp [Ctx.digits]), k4 _ Rd2]
  have tm9 : m9.ram.get! c.tm = m.ram.get! c.tm - 1 := by rw [K8 _ Rtm, e8 _ (by simp), tm6, pred_byte ht0]
  have v9 : m9.ram.get! c.v = byteN o 0 := by rw [K8 _ Rv, K7 _ (List.mem_append_left _ Rv)]; exact qget (v := byteN o 0) M7 (by simp [moveOut])
  have F9 : m9.ram.get! c.fF = byteN o 1 := by rw [K8 _ RF, K7 _ (List.mem_append_left _ RF)]; exact qget (v := byteN o 1) M7 (by simp [moveOut])
  have f9 : m9.ram.get! c.ff = byteN o 2 := by rw [K8 _ Rf, K7 _ (List.mem_append_left _ Rf)]; exact qget (v := byteN o 2) M7 (by simp [moveOut])
  have A9 : m9.ram.get! c.abs = byteN o 3 := by rw [K8 _ RA, K7 _ (List.mem_append_left _ RA)]; exact qget (v := byteN o 3) M7 (by simp [moveOut])
  have rs9 : m9.ram.get! c.rs = c.r.ram.get! c.rs := by rw [K8 _ Rrs, K7 _ (List.mem_append_left _ Rrs)]; exact qget (v := c.r.ram.get! c.rs) M7 (by simp [moveOut])
  have md9 : m9.ram.get! c.md = c.r.ram.get! c.md := by rw [K8 _ Rmd, K7 _ (List.mem_append_left _ Rmd)]; exact qget (v := c.r.ram.get! c.md) M7 (by simp [moveOut])
  have htk : m.ram.get! c.task ∈ ([2, 3, 4] : List UInt8) := by rcases tk3 with h | h | h <;> rw [h] <;> simp
  -- the collision
  have last : ∃ m10, Next (cutsOf c.sy 9) m9 m10 ∧ AtL c.E m.frame (d.B 10) m10 ∧ UpToFlag c d m m10 := by
    have hp : ((m.ram.get! c.ph).toNat + 20) % 21 < 256 := by omega
    rcases nextMario_spec hx with ⟨hB, hxB⟩ | ⟨hA, hxA⟩
    · have q9 : Quiet [(c.task, m.ram.get! c.task), (c.x, c.x0 + 1), (c.pg, c.pg0), (c.v, (byteN o 0).toNat.toUInt8)] m9 :=
        qc task9 (qc (x9.trans hB) (qc pg9 (qc (by rw [v9, tt]) qn)))
      obtain ⟨m10, n10, a10⟩ := hC.covL (j := 9) (by decide) (by decide) (by decide) _ m9 a9 _
        (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_of_mem _ (List.mem_map.2 ⟨(byteN o 0).toNat, List.mem_range.2 (by omega), rfl⟩)⟩) q9
      have M10 := fact1 (h := hC.fact 9 (by decide) _ (List.mem_singleton.2 rfl) _
        (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_of_mem _ (List.mem_map.2 ⟨(byteN o 0).toNat, List.mem_range.2 (by omega), rfl⟩)⟩)) a9 q9 n10
      have K9 : ∀ b ∈ [c.ph, c.w, c.y, c.fF, c.ff, c.abs, c.rs, c.md] ++ c.digits, m10.ram.get! b = m9.ram.get! b := fun b hb =>
        hC.keep 9 (by decide) _ (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_of_mem _ List.mem_cons_self⟩) b hb _ m9 a9 (qc task9 (qc (x9.trans hB) (qc pg9 qn))) m10 n10
      refine ⟨m10, n10, a10, ⟨a10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [K9 _ (by simp), ph9, toNat_small hp]
      · rw [K9 _ (by simp), w9]
      · rw [K9 _ (by simp), y9]
      · rw [qget M10 List.mem_cons_self]
      · rw [K9 _ (by simp [Ctx.digits]), d09]
      · rw [K9 _ (by simp [Ctx.digits]), d19]
      · rw [K9 _ (by simp [Ctx.digits]), d29]
      · rw [K9 _ (by simp), rs9]
      · rw [K9 _ (by simp), md9]
      · rw [hxB] at hxQ
        rw [qget (v := 0) M10 (by simp), K9 _ (by simp), K9 _ (by simp), K9 _ (by simp), qget (v := c.r.ram.get! c.coll) M10 (by simp),
          qget (v := c.sy.SideTimerBump.toUInt8) M10 (by simp), F9, f9, A9]
        exact hxQ
    · have q9 : Quiet [(c.task, m.ram.get! c.task), (c.x, c.x0), (c.pg, c.pg0)] m9 := qc task9 (qc (x9.trans hA) (qc pg9 qn))
      obtain ⟨m10, n10, a10⟩ := hC.covL (j := 9) (by decide) (by decide) (by decide) _ m9 a9 _ (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_self⟩) q9
      have M10 := fact1 (h := hC.fact 9 (by decide) _ (List.mem_singleton.2 rfl) _ (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_self⟩)) a9 q9 n10
      have K9 : ∀ b ∈ [c.ph, c.w, c.y, c.v, c.fF, c.ff, c.abs, c.tm, c.rs, c.md] ++ c.digits, m10.ram.get! b = m9.ram.get! b := fun b hb =>
        hC.keep 9 (by decide) _ (List.mem_flatMap.2 ⟨_, htk, List.mem_cons_self⟩) b hb _ m9 a9 q9 m10 n10
      refine ⟨m10, n10, a10, ⟨a10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [K9 _ (by simp), ph9, toNat_small hp]
      · rw [K9 _ (by simp), w9]
      · rw [K9 _ (by simp), y9]
      · rw [qget M10 List.mem_cons_self]
      · rw [K9 _ (by simp [Ctx.digits]), d09]
      · rw [K9 _ (by simp [Ctx.digits]), d19]
      · rw [K9 _ (by simp [Ctx.digits]), d29]
      · rw [K9 _ (by simp), rs9]
      · rw [K9 _ (by simp), md9]
      · rw [hxA] at hxQ
        rw [K9 _ (by simp), K9 _ (by simp), K9 _ (by simp), K9 _ (by simp), qget (v := c.sy.CollisionInit.toUInt8) M10 (by simp), K9 _ (by simp), v9, F9, f9, A9, tm9]
        exact hxQ
  obtain ⟨m10, n10, a10, U⟩ := last
  have hE := ((((((he.next n5 (atL_fdot a5)).next n6 (atL_fdot a6)).next n7
    (atL_fdot a7)).next n8 (atL_fdot a8)).next n9 (atL_fdot a9)).next n10 (atL_fdot a10))
  refine ⟨m10, hE, ?_, U⟩
  rw [n10.frame, n9.frame, n8.frame, n7.frame, n6.frame, n5.frame, hf]



/-- the counters of `FC`, read from the bytes of the rule -/
def cnt (c : Ctx) (m : Machine) : CastleToLevel.FC :=
  ⟨(m.ram.get! c.task).toNat, 100 * (m.ram.get! (c.d 0)).toNat + 10 * (m.ram.get! (c.d 1)).toNat + (m.ram.get! (c.d 2)).toNat,
    (m.ram.get! c.y).toNat, (m.ram.get! c.w).toNat, (m.ram.get! c.ph).toNat⟩

theorem timer_ds {c : Ctx} {m : Machine} {t : Nat} (q : Quiet (c.ds t) m) (ht : t ≤ 999) :
    100 * (m.ram.get! (c.d 0)).toNat + 10 * (m.ram.get! (c.d 1)).toNat + (m.ram.get! (c.d 2)).toNat = t := by
  rw [qget q List.mem_cons_self, qget q (List.mem_cons_of_mem _ List.mem_cons_self),
    qget q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    toNat_small (by omega), toNat_small (by omega), toNat_small (by omega)]
  omega

theorem ds_of {c : Ctx} {m m' : Machine} {t : Nat} (h0 : m'.ram.get! (c.d 0) = m.ram.get! (c.d 0)) (h1 : m'.ram.get! (c.d 1) = m.ram.get! (c.d 1))
    (h2 : m'.ram.get! (c.d 2) = m.ram.get! (c.d 2)) (q : Quiet (c.ds t) m) : Quiet (c.ds t) m' :=
  qc (h0.trans (qget q List.mem_cons_self)) (qc (h1.trans (qget q (List.mem_cons_of_mem _ List.mem_cons_self)))
    (qc (h2.trans (qget q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) qn))

theorem tick_eq (p w : UInt8) : (if p = 0 then (w.toNat - 1).toUInt8 else w).toNat = if p.toNat = 0 then w.toNat - 1 else w.toNat := by
  by_cases h : p = 0
  · rw [if_pos h, if_pos (by rw [h]; rfl), toNat_small (by have := w.toNat_lt; omega)]
  · rw [if_neg h, if_neg (fun e => h (UInt8.toNat_inj.1 (by rw [e]; rfl)))]

open CastleToLevel (FC FlagRun) in
theorem flagRun_two {lim w₀ : Nat} {a b : FC} (h : a.task = 2) (hp : b.ph = (a.ph + 20) % 21) (hy : b.y = a.y) (hw : b.w = a.tick)
    (ht : if a.t = 0 then b.task = 3 ∧ b.t = 0 else b.task = 2 ∧ b.t = a.t - 1) : FlagRun lim w₀ a b := by
  unfold FlagRun
  rw [h]
  exact ⟨hp, hy, hw, ht⟩

open CastleToLevel (FC FlagRun) in
theorem flagRun_three {lim w₀ : Nat} {a b : FC} (h : a.task = 3) (hp : b.ph = (a.ph + 20) % 21) (ht : b.t = a.t)
    (hr : if lim ≤ a.y then b.task = 3 ∧ b.y = a.y - 1 ∧ b.w = a.tick else b.y = a.y ∧ ((b.task = 3 ∧ b.w = a.tick) ∨ (b.task = 4 ∧ b.w = w₀))) :
    FlagRun lim w₀ a b := by
  unfold FlagRun
  rw [h]
  exact ⟨hp, ht, hr⟩

open CastleToLevel (FC FlagRun) in
theorem flagRun_four {lim w₀ : Nat} {a b : FC} (h : a.task = 4) (hp : b.ph = (a.ph + 20) % 21) (ht : b.t = a.t) (hy : b.y = a.y) (hw : b.w = a.tick)
    (hk : b.task = 4 ∨ (b.task = 5 ∧ b.w = 0)) : FlagRun lim w₀ a b := by
  unfold FlagRun
  rw [h]
  exact ⟨hp, ht, hy, hw, hk⟩

/-- what the star flag's routine leaves -/
structure AfterFlag (c : Ctx) (d : Data) (m m11 : Machine) : Prop where
  run : CastleToLevel.FlagRun c.lim c.w0 (cnt c m) (cnt c m11)
  ok : m11.ram.get! c.task = 5 ∨ Ok c d m11

variable {c : Ctx} {d : Data} in
theorem flagStage (hC : Checked c d) {m m10 : Machine} (hm : Ok c d m) (U : UpToFlag c d m m10) :
    ∃ m11, Next (cutsOf c.sy 10) m10 m11 ∧ AtL c.E m.frame (d.B 11) m11 ∧ AfterFlag c d m m11 := by
  have hp : ((m.ram.get! c.ph).toNat + 20) % 21 < 21 := Nat.mod_lt _ (by decide)
  have hw : (m10.ram.get! c.w).toNat = (cnt c m).tick := by
    rw [U.w, tick_eq]
    rfl
  obtain ⟨t, htm, hq⟩ := hm.digits
  have hT : (cnt c m).t = t := timer_ds hq (Nat.le_trans htm hC.tmax)
  have q10 : Quiet (c.ds t) m10 := ds_of U.d0 U.d1 U.d2 hq
  have F10 : ∀ f ∈ digitFacts c, FactP c.E (cutsOf c.sy 10) (d.B 10) f := hC.fact 10 (by decide) _ List.mem_cons_self
  have G10 : ∀ f ∈ yFacts c ++ upFacts c ++ lastFacts c, FactP c.E (cutsOf c.sy 10) (d.B 10) f :=
    hC.fact 10 (by decide) _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mario' : ∀ m11 : Machine, (∀ b ∈ [c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md], m11.ram.get! b = m10.ram.get! b) →
      (q5 (m11.ram.get! c.v) (m11.ram.get! c.fF) (m11.ram.get! c.ff) (m11.ram.get! c.abs) (m11.ram.get! c.coll), m11.ram.get! c.tm) ∈ d.Q ∧
      m11.ram.get! c.rs = c.r.ram.get! c.rs ∧ m11.ram.get! c.md = c.r.ram.get! c.md := by
    intro m11 h
    rw [h c.v (by simp), h c.fF (by simp), h c.ff (by simp), h c.abs (by simp), h c.coll (by simp), h c.tm (by simp), h c.rs (by simp), h c.md (by simp)]
    exact ⟨U.mario, U.rs, U.md⟩
  rcases hm.task with h2 | h3 | h4
  · -- the digits count down
    have r10 : Quiet [(c.task, 2)] m10 := qc (U.task.trans h2) qn
    obtain ⟨m11, n11, a11⟩ := hC.covL (j := 10) (by decide) (by decide) (by decide) _ m10 U.at10 [(c.task, 2)] List.mem_cons_self r10
    refine ⟨m11, n11, a11, ?_⟩
    have M := fact1 (h := F10 _ (List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩)) U.at10 (qc (U.task.trans h2) q10) n11
    have K : ∀ b ∈ [c.ph, c.w, c.y, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md], m11.ram.get! b = m10.ram.get! b := fun b hb =>
      hC.keep 10 (by decide) _ List.mem_cons_self b hb _ m10 U.at10 r10 m11 n11
    have qd : Quiet (c.ds (t - 1)) m11 := fun p hp => M p (List.mem_cons_of_mem _ hp)
    have tk : m11.ram.get! c.task = if t == 0 then 3 else 2 := qget M List.mem_cons_self
    have hT' : (cnt c m11).t = t - 1 := timer_ds qd (by have := hC.tmax; omega)
    have ph11 : (m11.ram.get! c.ph).toNat = ((m.ram.get! c.ph).toNat + 20) % 21 := by rw [K _ (by simp), U.ph]
    have y11 : m11.ram.get! c.y = m.ram.get! c.y := by rw [K _ (by simp), U.y]
    obtain ⟨M1, M2, M3⟩ := mario' m11 (fun b hb => K b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))))
    constructor
    · refine flagRun_two (by show (m.ram.get! c.task).toNat = 2; rw [h2]; rfl) ph11 (by show (m11.ram.get! c.y).toNat = _; rw [y11]; rfl)
        (by show (m11.ram.get! c.w).toNat = _; rw [K _ (by simp), hw]) ?_
      rw [hT]
      by_cases ht0 : t = 0
      · rw [if_pos ht0]
        refine ⟨by show (m11.ram.get! c.task).toNat = 3; rw [tk, ht0]; rfl, by rw [hT', ht0]⟩
      · rw [if_neg ht0]
        have e : (t == 0) = false := by simpa using ht0
        exact ⟨by show (m11.ram.get! c.task).toNat = 2; rw [tk, e]; rfl, hT'⟩
    · right
      have hy := hm.y (by rw [h2]; decide)
      have tk' : m11.ram.get! c.task = 2 ∨ m11.ram.get! c.task = 3 := by
        rw [tk]; by_cases ht0 : t = 0
        · right; simp [ht0]
        · left; simp [ht0]
      refine ⟨by rw [ph11]; exact hp, by rcases tk' with h | h <;> simp [h], ⟨t - 1, by omega, qd⟩, M1, M2, M3, fun _ => by rw [y11]; exact hy, fun h4 => ?_⟩
      rcases tk' with h | h <;> rw [h] at h4 <;> cases h4
  · -- the flag rises
    have r10 : Quiet [(c.task, 3)] m10 := qc (U.task.trans h3) qn
    obtain ⟨m11, n11, a11⟩ := hC.covL (j := 10) (by decide) (by decide) (by decide) _ m10 U.at10 [(c.task, 3)] (List.mem_cons_of_mem _ List.mem_cons_self) r10
    refine ⟨m11, n11, a11, ?_⟩
    have K : ∀ b ∈ [c.ph, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md] ++ c.digits, m11.ram.get! b = m10.ram.get! b := fun b hb =>
      hC.keep 10 (by decide) _ (List.mem_cons_of_mem _ List.mem_cons_self) b hb _ m10 U.at10 r10 m11 n11
    have ph11 : (m11.ram.get! c.ph).toNat = ((m.ram.get! c.ph).toNat + 20) % 21 := by rw [K _ (by simp), U.ph]
    have qd : Quiet (c.ds t) m11 := ds_of ((K _ (by simp [Ctx.digits])).trans U.d0) ((K _ (by simp [Ctx.digits])).trans U.d1)
      ((K _ (by simp [Ctx.digits])).trans U.d2) hq
    have hT' : (cnt c m11).t = t := timer_ds qd (Nat.le_trans htm hC.tmax)
    obtain ⟨M1, M2, M3⟩ := mario' m11 (fun b hb => K b (List.mem_append_left _ (List.mem_cons_of_mem _ hb)))
    have hy := hm.y (by rw [h3]; decide)
    have ha3 : (cnt c m).task = 3 := by show (m.ram.get! c.task).toNat = 3; rw [h3]; rfl
    have y0 := hC.y0
    have l2 := hC.lim2
    by_cases hly : c.lim ≤ (m.ram.get! c.y).toNat
    · have hmem : (m.ram.get! c.y).toNat ∈ (List.range ((c.r.ram.get! c.y).toNat + 1)).filter (c.lim ≤ ·) :=
        List.mem_filter.2 ⟨List.mem_range.2 (Nat.lt_succ_of_le hy.2), decide_eq_true hly⟩
      have pre : Quiet [(c.task, 3), (c.y, (m.ram.get! c.y).toNat.toUInt8)] m10 := qc (U.task.trans h3) (qc (by rw [U.y, tt]) qn)
      have M := fact1 (h := G10 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨_, hmem, rfl⟩)))) U.at10 pre n11
      have kw : m11.ram.get! c.w = m10.ram.get! c.w :=
        hC.keep 10 (by decide) _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, hmem, rfl⟩))) c.w List.mem_cons_self _ m10 U.at10 pre m11 n11
      have tk : m11.ram.get! c.task = 3 := qget M List.mem_cons_self
      have y11 : (m11.ram.get! c.y).toNat = (m.ram.get! c.y).toNat - 1 := by
        rw [qget M (List.mem_cons_of_mem _ List.mem_cons_self), toNat_small (by have := (m.ram.get! c.y).toNat_lt; omega)]
      constructor
      · refine flagRun_three ha3 ph11 (by rw [hT', hT]) ?_
        rw [if_pos (show c.lim ≤ (cnt c m).y from hly)]
        exact ⟨by show (m11.ram.get! c.task).toNat = 3; rw [tk]; rfl, y11, by show (m11.ram.get! c.w).toNat = _; rw [kw, hw]⟩
      · right
        refine ⟨by rw [ph11]; exact hp, Or.inr (Or.inl tk), ⟨t, htm, qd⟩, M1, M2, M3, fun _ => by rw [y11]; omega, fun h => ?_⟩
        rw [tk] at h; cases h
    · have hyv : (m.ram.get! c.y).toNat = c.lim - 1 := by omega
      have hy1 : m.ram.get! c.y = (c.lim - 1).toUInt8 := by rw [← hyv, tt]
      have hfm := List.mem_range.2 (m10.ram.get! (c.i "FireworksCounter")).toNat_lt
      have pre : Quiet [(c.task, 3), (c.y, (c.lim - 1).toUInt8), (c.i "FireworksCounter", (m10.ram.get! (c.i "FireworksCounter")).toNat.toUInt8)] m10 :=
        qc (U.task.trans h3) (qc (by rw [U.y, hy1]) (qc (tt _).symm qn))
      obtain ⟨al, hal, hq'⟩ := G10 _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, hfm, rfl⟩))) _ m10 U.at10 pre m11 n11
      have hyl : ((c.lim - 1).toUInt8).toNat = c.lim - 1 := toNat_small (by omega)
      by_cases hv : ((m10.ram.get! (c.i "FireworksCounter")).toNat == 0 || decide (128 ≤ (m10.ram.get! (c.i "FireworksCounter")).toNat)) = true
      · have hal' : al ∈ (if ((m10.ram.get! (c.i "FireworksCounter")).toNat == 0 || decide (128 ≤ (m10.ram.get! (c.i "FireworksCounter")).toNat)) = true then
            [[(c.task, 4), (c.y, (c.lim - 1).toUInt8), (c.w, c.w0.toUInt8)]] else [[(c.task, 3), (c.y, (c.lim - 1).toUInt8)]]) := hal
        rw [if_pos hv] at hal'
        rw [List.mem_singleton.1 hal'] at hq'
        have tk : m11.ram.get! c.task = 4 := qget hq' List.mem_cons_self
        have y11 : (m11.ram.get! c.y).toNat = c.lim - 1 := by rw [qget hq' (List.mem_cons_of_mem _ List.mem_cons_self), hyl]
        have w11 : (m11.ram.get! c.w).toNat = c.w0 := by
          rw [qget hq' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), toNat_small (by have := hC.w0; omega)]
        constructor
        · refine flagRun_three ha3 ph11 (by rw [hT', hT]) ?_
          rw [if_neg (show ¬ c.lim ≤ (cnt c m).y from hly)]
          exact ⟨by show (m11.ram.get! c.y).toNat = (m.ram.get! c.y).toNat; rw [y11]; exact hyv.symm, Or.inr ⟨by show (m11.ram.get! c.task).toNat = 4; rw [tk]; rfl, w11⟩⟩
        · right
          refine ⟨by rw [ph11]; exact hp, Or.inr (Or.inr tk), ⟨t, htm, qd⟩, M1, M2, M3, fun h => absurd tk h, fun _ => by rw [w11]; exact Nat.le_refl _⟩
      · have hal' : al ∈ (if ((m10.ram.get! (c.i "FireworksCounter")).toNat == 0 || decide (128 ≤ (m10.ram.get! (c.i "FireworksCounter")).toNat)) = true then
            [[(c.task, 4), (c.y, (c.lim - 1).toUInt8), (c.w, c.w0.toUInt8)]] else [[(c.task, 3), (c.y, (c.lim - 1).toUInt8)]]) := hal
        rw [if_neg hv] at hal'
        rw [List.mem_singleton.1 hal'] at hq'
        have hv' : (m10.ram.get! (c.i "FireworksCounter")).toNat ≠ 0 ∧ (m10.ram.get! (c.i "FireworksCounter")).toNat < 128 := by
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hv
          omega
        have pre' : Quiet [(c.task, 3), (c.y, (c.lim - 1).toUInt8), (c.i "FireworksCounter", ((m10.ram.get! (c.i "FireworksCounter")).toNat - 1 + 1).toUInt8)] m10 :=
          qc (U.task.trans h3) (qc (by rw [U.y, hy1]) (qc (by rw [show (m10.ram.get! (c.i "FireworksCounter")).toNat - 1 + 1 = (m10.ram.get! (c.i "FireworksCounter")).toNat by omega, tt]) qn))
        have kw : m11.ram.get! c.w = m10.ram.get! c.w :=
          hC.keep 10 (by decide) _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩)) c.w List.mem_cons_self _ m10 U.at10 pre' m11 n11
        have tk : m11.ram.get! c.task = 3 := qget hq' List.mem_cons_self
        have y11 : (m11.ram.get! c.y).toNat = c.lim - 1 := by rw [qget hq' (List.mem_cons_of_mem _ List.mem_cons_self), hyl]
        constructor
        · refine flagRun_three ha3 ph11 (by rw [hT', hT]) ?_
          rw [if_neg (show ¬ c.lim ≤ (cnt c m).y from hly)]
          exact ⟨by show (m11.ram.get! c.y).toNat = (m.ram.get! c.y).toNat; rw [y11]; exact hyv.symm, Or.inl ⟨by show (m11.ram.get! c.task).toNat = 3; rw [tk]; rfl, by show (m11.ram.get! c.w).toNat = _; rw [kw, hw]⟩⟩
        · right
          refine ⟨by rw [ph11]; exact hp, Or.inr (Or.inl tk), ⟨t, htm, qd⟩, M1, M2, M3, fun _ => by rw [y11]; omega, fun h => ?_⟩
          rw [tk] at h; cases h
  · -- the last wait
    have r10 : Quiet [(c.task, 4)] m10 := qc (U.task.trans h4) qn
    obtain ⟨m11, n11, a11⟩ := hC.covL (j := 10) (by decide) (by decide) (by decide) _ m10 U.at10 [(c.task, 4)] (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) r10
    refine ⟨m11, n11, a11, ?_⟩
    have K : ∀ b ∈ [c.ph, c.y, c.v, c.fF, c.ff, c.abs, c.coll, c.tm, c.rs, c.md] ++ c.digits, m11.ram.get! b = m10.ram.get! b := fun b hb =>
      hC.keep 10 (by decide) _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) b hb _ m10 U.at10 r10 m11 n11
    have ph11 : (m11.ram.get! c.ph).toNat = ((m.ram.get! c.ph).toNat + 20) % 21 := by rw [K _ (by simp), U.ph]
    have qd : Quiet (c.ds t) m11 := ds_of ((K _ (by simp [Ctx.digits])).trans U.d0) ((K _ (by simp [Ctx.digits])).trans U.d1)
      ((K _ (by simp [Ctx.digits])).trans U.d2) hq
    have hT' : (cnt c m11).t = t := timer_ds qd (Nat.le_trans htm hC.tmax)
    obtain ⟨M1, M2, M3⟩ := mario' m11 (fun b hb => K b (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))))
    have y11 : m11.ram.get! c.y = m.ram.get! c.y := by rw [K _ (by simp), U.y]
    have ha4 : (cnt c m).task = 4 := by show (m.ram.get! c.task).toNat = 4; rw [h4]; rfl
    have hwm := hm.w h4
    have hv : (m10.ram.get! c.w).toNat ≤ c.w0 := by
      rw [hw]
      show (if (m.ram.get! c.ph).toNat = 0 then (m.ram.get! c.w).toNat - 1 else (m.ram.get! c.w).toNat) ≤ c.w0
      split <;> omega
    have pre : Quiet [(c.task, 4), (c.w, (m10.ram.get! c.w).toNat.toUInt8)] m10 := qc (U.task.trans h4) (qc (tt _).symm qn)
    obtain ⟨al, hal, hq'⟩ := G10 _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_range.2 (Nat.lt_succ_of_le hv), rfl⟩)) _ m10 U.at10 pre m11 n11
    have hal' : al ∈ (if (m10.ram.get! c.w).toNat == 0 then [[(c.task, 4), (c.w, 0)], [(c.task, 5), (c.w, 0)]] else
        [[(c.task, 4), (c.w, (m10.ram.get! c.w).toNat.toUInt8)]]) := hal
    have run : ∀ k : UInt8, m11.ram.get! c.task = k → (k = 4 ∨ k = 5) → m11.ram.get! c.w = m10.ram.get! c.w → (k = 5 → (m10.ram.get! c.w).toNat = 0) →
        AfterFlag c d m m11 := by
      intro k hk hk45 hw11 h5
      constructor
      · refine flagRun_four ha4 ph11 (by rw [hT', hT]) (by show (m11.ram.get! c.y).toNat = _; rw [y11]; rfl)
          (by show (m11.ram.get! c.w).toNat = _; rw [hw11, hw]) ?_
        rcases hk45 with rfl | rfl
        · left; show (m11.ram.get! c.task).toNat = 4; rw [hk]; rfl
        · right; exact ⟨by show (m11.ram.get! c.task).toNat = 5; rw [hk]; rfl, by show (m11.ram.get! c.w).toNat = 0; rw [hw11]; exact h5 rfl⟩
      · rcases hk45 with rfl | rfl
        · right
          exact ⟨by rw [ph11]; exact hp, Or.inr (Or.inr hk), ⟨t, htm, qd⟩, M1, M2, M3, fun h => absurd hk h, fun _ => by rw [hw11]; exact hv⟩
        · left; exact hk
    by_cases hv0 : (m10.ram.get! c.w).toNat = 0
    · rw [if_pos (by simpa using hv0)] at hal'
      have w0' : m10.ram.get! c.w = 0 := UInt8.toNat_inj.1 (by rw [hv0]; rfl)
      rcases List.mem_cons.1 hal' with e | e
      · rw [e] at hq'
        exact run 4 (qget hq' List.mem_cons_self) (Or.inl rfl) (by rw [qget hq' (List.mem_cons_of_mem _ List.mem_cons_self), w0']) (fun h => by cases h)
      · rw [List.mem_singleton.1 e] at hq'
        exact run 5 (qget hq' List.mem_cons_self) (Or.inr rfl) (by rw [qget hq' (List.mem_cons_of_mem _ List.mem_cons_self), w0']) (fun _ => hv0)
    · rw [if_neg (by simpa using hv0)] at hal'
      rw [List.mem_singleton.1 hal'] at hq'
      exact run 4 (qget hq' List.mem_cons_self) (Or.inl rfl) (by rw [qget hq' (List.mem_cons_of_mem _ List.mem_cons_self), tt]) (fun h => by cases h)

theorem flagSlot_zero {c : Ctx} {m : Machine} (q : Quiet (startFacts c) m) : CastleToLevel.flagSlot c.nm m = 0 := by
  have h : peek m (c.nm.ad "Enemy_ID" + (0 : Nat).toUInt16) = c.nm.vl "StarFlagObject" :=
    qget q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hp : (peek m (c.nm.ad "Enemy_ID" + (0 : Nat).toUInt16) == c.nm.vl "StarFlagObject") = true := beq_iff_eq.2 h
  unfold CastleToLevel.flagSlot
  rw [show List.range 6 = 0 :: [1, 2, 3, 4, 5] from rfl]
  simp only [List.find?_cons, hp]
  rfl

/-- the counters of a real machine are those of the rule's bytes, when the star flag is in the first slot -/
theorem flagOf_cnt {c : Ctx} {m : Machine} (q : Quiet (startFacts c) m) : CastleToLevel.flagOf c.sy c.nm m = cnt c m := by
  unfold CastleToLevel.flagOf
  rw [flagSlot_zero q]
  have e0 : c.d 0 = ((c.nm.ad "GameTimerDisplay") &&& 0x7FF).toNat := by simp [Ctx.d]
  have e1 : c.d 1 = ((c.nm.ad "GameTimerDisplay" + 1) &&& 0x7FF).toNat := rfl
  have e2 : c.d 2 = ((c.nm.ad "GameTimerDisplay" + 2) &&& 0x7FF).toNat := rfl
  simp only [cnt, e0, e1, e2, UInt16.add_zero, CastleToLevel.timerOf, CastleToLevel.phaseOf, peek, Ctx.task, Ctx.y, Ctx.w, Ctx.ph, Ctx.i]

theorem level_false {c : Ctx} {m : Machine} (q : Quiet (startFacts c) m) : CastleToLevel.level c.sy m = false := by
  have h1 : peek m c.sy.LevelNumber = 0 := qget q List.mem_cons_self
  have h2 : peek m c.sy.WorldNumber = 0 := qget q (List.mem_cons_of_mem _ List.mem_cons_self)
  simp [CastleToLevel.level, h1, h2]

theorem cnt_same {c : Ctx} {m m' : Machine} (h : ∀ b ∈ c.ruled, m'.ram.get! b = m.ram.get! b) : cnt c m' = cnt c m := by
  have R := ruled_mem c
  simp only [cnt, h _ R.1, h _ R.2.1, h _ R.2.2.1, h _ R.2.2.2.1, h _ R.2.2.2.2.1, h _ R.2.2.2.2.2.1, h _ R.2.2.2.2.2.2.1]

theorem ok_same {c : Ctx} {d : Data} {m m' : Machine} (h : ∀ b ∈ c.ruled, m'.ram.get! b = m.ram.get! b) (o : Ok c d m) : Ok c d m' := by
  obtain ⟨Rph, Rw, Ry, Rt, Rd0, Rd1, Rd2, Rv, RF, Rf, RA, RC, Rtm, Rrs, Rmd⟩ := ruled_mem c
  obtain ⟨t, ht, hq⟩ := o.digits
  exact ⟨by rw [h _ Rph]; exact o.ph, by rw [h _ Rt]; exact o.task, ⟨t, ht, ds_of (h _ Rd0) (h _ Rd1) (h _ Rd2) hq⟩,
    by rw [h _ Rv, h _ RF, h _ Rf, h _ RA, h _ RC, h _ Rtm]; exact o.mario, by rw [h _ Rrs]; exact o.rs, by rw [h _ Rmd]; exact o.md,
    by rw [h _ Rt, h _ Ry]; exact o.y, by rw [h _ Rt, h _ Rw]; exact o.w⟩

theorem quiet_start {c : Ctx} {d : Data} (hC : Checked c d) {E : Env} {f : Nat} {m : Machine} (h : AtL E f d.B0 m) : Quiet (startFacts c) m := by
  obtain ⟨S, hS, hs⟩ := h
  exact quiet_of_knows hs hC.knownI (hC.known S hS)

/-- the game is paused: the bit 0 of the pause status -/
def paused (c : Ctx) (m : Machine) : Bool := bit0 c.gps m

theorem nextIdx_one (sy : Syms) (pc : UInt16) : nextIdx sy 1 pc = 14 ∨ nextIdx sy 1 pc = 2 := by
  unfold nextIdx
  split
  · exact Or.inl rfl
  · right
    simp

theorem nextIdx_three (sy : Syms) (pc : UInt16) : nextIdx sy 3 pc = 15 ∨ nextIdx sy 3 pc = 4 := by
  unfold nextIdx
  split
  · rename_i h
    simp at h
  · split
    · exact Or.inl rfl
    · right
      simp

theorem nextIdx_14 (sy : Syms) (pc : UInt16) : nextIdx sy 14 pc = 3 := by
  unfold nextIdx
  simp

variable {c : Ctx} {d : Data} in
/-- the stages 0 to 2 and 14: the screen and the sound (the music, or the sound of the pause), up to the pad. The bytes of the rule do not change. -/
theorem toPad (hC : Checked c d) {m0 e : Machine} (a0 : AtL c.E m0.frame (d.B 0) m0) (he : EndsAt m0 e) :
    ∃ m3, EndsAt m3 e ∧ m3.frame = m0.frame ∧ AtL c.E m0.frame (d.B 3) m3 ∧ ∀ b ∈ c.ruled, m3.ram.get! b = m0.ram.get! b := by
  obtain ⟨m1, n1, a1⟩ := hC.covL (j := 0) (by decide) (by decide) (by decide) _ m0 a0 [] (List.mem_singleton.2 rfl) qn
  obtain ⟨m2, n2, a2⟩ := hC.cov 1 (by decide) _ m1 a1 [] (List.mem_singleton.2 rfl) qn
  have k2 : ∀ b ∈ c.ruled, m2.ram.get! b = m0.ram.get! b := by
    intro b hb
    rw [hC.keep 1 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m1 a1 qn m2 n2,
      hC.keep 0 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m0 a0 qn m1 n1]
  have he2 := (he.next n1 (atL_fdot a1)).next n2 (atL_fdot a2)
  have hf2 : m2.frame = m0.frame := by rw [n2.frame, n1.frame]
  have a2' : AtL c.E m0.frame (d.B (nextIdx c.sy 1 m2.pc)) m2 := a2
  rcases nextIdx_one c.sy m2.pc with h | h <;> rw [h] at a2'
  · obtain ⟨m3, n3, a3'⟩ := hC.cov 14 (by decide) _ m2 a2' [] (List.mem_singleton.2 rfl) qn
    have a3 : AtL c.E m0.frame (d.B (nextIdx c.sy 14 m3.pc)) m3 := a3'
    rw [nextIdx_14] at a3
    refine ⟨m3, he2.next n3 (atL_fdot a3), by rw [n3.frame, hf2], a3, fun b hb => ?_⟩
    rw [hC.keep 14 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m2 a2' qn m3 n3, k2 b hb]
  · obtain ⟨m3, n3, a3⟩ := hC.covL (j := 2) (by decide) (by decide) (by decide) _ m2 a2' [] (List.mem_singleton.2 rfl) qn
    refine ⟨m3, he2.next n3 (atL_fdot a3), by rw [n3.frame, hf2], a3, fun b hb => ?_⟩
    rw [hC.keep 2 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m2 a2' qn m3 n3, k2 b hb]

/-- the machine with any pad, from a state where the pad is not known -/
theorem sim_pad {c : Ctx} (hp : c.E.pad = AB.top) {F : Nat × UInt8} {S : AS} {m : Machine} (p : UInt8) (hs : Sim { c.E with pad := AB.top } F S m) :
    Sim c.E F S { m with pad := p } := by
  refine ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, ?_, hs.padShift, hs.strobe, hs.halted, hs.trk, hs.size, hs.ram, hs.dg, hs.szR, hs.szK, hs.fr, hs.rkv⟩
  rw [hp]
  exact mem_top _

/-- **One frame after the castle entry.** From a machine in the condition, a frame with any input: the frame ends and the level has not changed. If the frame
ends paused, the counters are the same and the condition holds again. Otherwise the counters follow the rule of one frame, and either the flag's task is 5 or
the condition holds again. -/
theorem frame_step {c : Ctx} {d : Data} (hC : Checked c d) {m : Machine} (hm : Good c d m) (i : UInt8) :
    (frame m i).frame = m.frame + 1 ∧ CastleToLevel.level c.sy m = false ∧ CastleToLevel.level c.sy (frame m i) = false ∧
    (if paused c (frame m i) then CastleToLevel.flagOf c.sy c.nm (frame m i) = CastleToLevel.flagOf c.sy c.nm m ∧ Good c d (frame m i)
     else CastleToLevel.FlagRun c.lim c.w0 (CastleToLevel.flagOf c.sy c.nm m) (CastleToLevel.flagOf c.sy c.nm (frame m i)) ∧
      ((CastleToLevel.flagOf c.sy c.nm (frame m i)).task = 5 ∨ Good c d (frame m i))) := by
  obtain ⟨S, hS, hs⟩ := hm.at0
  have q0 : Quiet (startFacts c) m := quiet_start hC hm.at0
  have a0 : AtL c.E m.frame (d.B 0) { m with pad := smbToPad i } := atL_coarse hC.start ⟨S, hS, sim_pad hC.pad _ hs⟩
  have he : EndsAt { m with pad := smbToPad i } (frame m i) :=
    ⟨fuelPerFrame, by have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
                      omega, PipeTransitionAll.frame_eq m i⟩
  obtain ⟨m3, he3, hf3, a3, k3⟩ := toPad hC a0 he
  -- the pad: the timers, or a paused frame
  obtain ⟨m4, n4, a4⟩ := hC.cov 3 (by decide) _ m3 a3 [] (List.mem_singleton.2 rfl) qn
  have k4 : ∀ b ∈ c.ruled, m4.ram.get! b = m.ram.get! b := fun b hb => by
    rw [hC.keep 3 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m3 a3 qn m4 n4, k3 b hb]
  have he4 := he3.next n4 (atL_fdot a4)
  have hf4 : m4.frame = m.frame := by rw [n4.frame, hf3]
  have a4'' : AtL c.E m.frame (d.B (nextIdx c.sy 3 m4.pc)) m4 := a4
  rcases nextIdx_three c.sy m4.pc with h | h <;> rw [h] at a4''
  · -- a paused frame
    have a4' : AtL c.E m4.frame (d.B 15) m4 := by rw [hf4]; exact a4''
    obtain ⟨hfr, ae, hp⟩ := hC.pauseCov m4 a4' (frame m i) he4
    have same : ∀ b ∈ c.ruled, (frame m i).ram.get! b = m.ram.get! b := fun b hb => by
      rw [hC.pauseKeep b hb m4 a4' _ he4, k4 b hb]
    have q1 : Quiet (startFacts c) (frame m i) := quiet_start hC ae
    have hfr' : (frame m i).frame = m.frame + 1 := by rw [hfr, hf4]
    refine ⟨hfr', level_false q0, level_false q1, ?_⟩
    have hp' : paused c (frame m i) = true := hp
    rw [if_pos hp']
    refine ⟨by rw [flagOf_cnt q0, flagOf_cnt q1, cnt_same same], ?_, ok_same same hm.ok⟩
    obtain ⟨S', hS', hs'⟩ := ae
    exact ⟨S', hS', by rw [hfr, hf4] at *; exact sim_anyPad hs'⟩
  · -- the timers and the rest of the frame
    obtain ⟨m10, hE10, hf10, U⟩ := upToFlag hC hm.ok a4'' k4 hf4 he4
    obtain ⟨m11, n11, a11, AF⟩ := flagStage hC hm.ok U
    obtain ⟨m12, n12, a12⟩ := hC.covL (j := 11) (by decide) (by decide) (by decide) _ m11 a11 [] (List.mem_singleton.2 rfl) qn
    obtain ⟨m13, n13, a13⟩ := hC.covL (j := 12) (by decide) (by decide) (by decide) _ m12 a12 [] (List.mem_singleton.2 rfl) qn
    have hE13 := ((hE10.next n11 (atL_fdot a11)).next n12 (atL_fdot a12)).next n13 (atL_fdot a13)
    have hf13 : m13.frame = m.frame := by rw [n13.frame, n12.frame, n11.frame, hf10]
    have a13' : AtL c.E m13.frame (d.B 13) m13 := by rw [hf13]; exact a13
    obtain ⟨hfr, ae, hp⟩ := hC.endCov m13 a13' (frame m i) hE13
    have same : ∀ b ∈ c.ruled, (frame m i).ram.get! b = m11.ram.get! b := by
      intro b hb
      rw [hC.endKeep b hb m13 a13' _ hE13, hC.keep 12 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m12 a12 qn m13 n13,
        hC.keep 11 (by decide) _ (List.mem_singleton.2 rfl) b hb _ m11 a11 qn m12 n12]
    have q1 : Quiet (startFacts c) (frame m i) := quiet_start hC ae
    have hfr' : (frame m i).frame = m.frame + 1 := by rw [hfr, hf13]
    refine ⟨hfr', level_false q0, level_false q1, ?_⟩
    have hp' : paused c (frame m i) = false := hp
    rw [if_neg (by rw [hp']; decide)]
    refine ⟨?_, ?_⟩
    · rw [flagOf_cnt q0, flagOf_cnt q1, cnt_same same]
      exact AF.run
    · rcases AF.ok with h5 | ok
      · left
        rw [flagOf_cnt q1]
        show ((frame m i).ram.get! c.task).toNat = 5
        rw [same _ (ruled_mem c).2.2.2.1, h5]
        rfl
      · right
        obtain ⟨S', hS', hs'⟩ := ae
        exact ⟨⟨S', hS', by rw [hfr, hf13] at *; exact sim_anyPad hs'⟩, ok_same same ok⟩

/-- the next frame is in the condition, or begins with task 5 -/
theorem frame_next {c : Ctx} {d : Data} (hC : Checked c d) {m : Machine} (hm : Good c d m) (i : UInt8) :
    (CastleToLevel.flagOf c.sy c.nm (frame m i)).task = 5 ∨ Good c d (frame m i) := by
  have h := (frame_step hC hm i).2.2.2
  split at h
  · exact Or.inr h.2
  · exact h.2

/-! ## The frames after the castle entry -/

/-- **The frames after the castle entry, on real machines.** `seq n` is the machine when frame `n` begins and `inp n` its input, as in `Route.Changes`. `T` and `ph` are what the frames
up to the castle entry `E` leave. The level has changed when frame `L + 1` begins. -/
structure After (c : Ctx) (seq : Nat → Machine) (inp : Nat → UInt8) (E T ph L : Nat) : Prop where
  /-- the machine after the castle entry is in the condition of `frame_step`, with task 2 and the flag at the height it is made at -/
  entry : Good c (dataOf c) (seq (E + 1))
  task_E : (seq (E + 1)).ram.get! c.task = 2
  y_E : (seq (E + 1)).ram.get! c.y = c.r.ram.get! c.y
  /-- the timer and the phase that the castle entry leaves -/
  t_E : CastleToLevel.timerOf c.nm (seq (E + 1)) = T
  ph_E : CastleToLevel.phaseOf c.nm (seq (E + 1)) = ph
  after : E < L
  /-- the level has changed when frame `L + 1` begins -/
  level : CastleToLevel.level c.sy (seq (L + 1)) = true

/-- the machines of the frames, held at the first frame of task 5 after `E` -/
def held (c : Ctx) (seq : Nat → Machine) (E : Nat) : Nat → Machine
  | 0 => seq 0
  | n + 1 => if E < n ∧ (CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5 then held c seq E n else seq (n + 1)

section
variable {c : Ctx} {seq : Nat → Machine} {inp : Nat → UInt8} {E T ph L : Nat}

theorem held_E (c : Ctx) (seq : Nat → Machine) (E : Nat) : held c seq E (E + 1) = seq (E + 1) := by
  simp [held]

theorem held_five {n : Nat} (hn : E < n) (h : (CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5) : held c seq E (n + 1) = held c seq E n := by
  simp only [held]
  rw [if_pos ⟨hn, h⟩]

theorem held_run {n : Nat} (h : ¬ (CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5) : held c seq E (n + 1) = seq (n + 1) := by
  simp only [held]
  rw [if_neg (fun e => h e.2)]

/-- what holds on each frame from `E + 1` to `L + 1` -/
theorem held_inv (hC : Checked c (dataOf c)) (hn : ∀ n, seq (n + 1) = frame (seq n) (inp n)) (A : After c seq inp E T ph L) :
    ∀ k, E + 1 + k ≤ L + 1 → (CastleToLevel.flagOf c.sy c.nm (held c seq E (E + 1 + k))).task = 5 ∨
      (held c seq E (E + 1 + k) = seq (E + 1 + k) ∧ Good c (dataOf c) (seq (E + 1 + k)))
  | 0, _ => Or.inr ⟨held_E c seq E, A.entry⟩
  | k + 1, hk => by
    rcases held_inv hC hn A k (by omega) with h5 | ⟨he, hg⟩
    · left
      rw [show E + 1 + (k + 1) = E + 1 + k + 1 by omega, held_five (by omega) h5]
      exact h5
    · by_cases h5 : (CastleToLevel.flagOf c.sy c.nm (held c seq E (E + 1 + k))).task = 5
      · left
        rw [show E + 1 + (k + 1) = E + 1 + k + 1 by omega, held_five (by omega) h5]
        exact h5
      · have hr := frame_next hC hg (inp (E + 1 + k))
        rw [show E + 1 + (k + 1) = E + 1 + k + 1 by omega, held_run h5, hn]
        rcases hr with h | h
        · exact Or.inl h
        · exact Or.inr ⟨rfl, h⟩

theorem held_inv' (hC : Checked c (dataOf c)) (hn : ∀ n, seq (n + 1) = frame (seq n) (inp n)) (A : After c seq inp E T ph L) {n : Nat} (h1 : E < n) (h2 : n ≤ L + 1) :
    (CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5 ∨ (held c seq E n = seq n ∧ Good c (dataOf c) (seq n)) := by
  have := held_inv hC hn A (n - (E + 1)) (by omega)
  rwa [show E + 1 + (n - (E + 1)) = n by omega] at this

/-- **The rule on every frame after the castle entry.** From the condition at `E + 1`, with any inputs, the counters of the real machines follow `FlagStep` up to
the level change, and the frame of the level change begins with task 5. A frame that ends paused is a `lag` frame: it keeps the counters. The frames from the first
frame of task 5 on are counted as frames that do not run: the counters are held there. -/
def flagOf_after (hC : Checked c (dataOf c)) (hn : ∀ n, seq (n + 1) = frame (seq n) (inp n)) (A : After c seq inp E T ph L) :
    CastleToLevel.Flag c.lim c.w0 E T ph L where
  lag n := decide (E < n ∧ ((CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5 ∨ paused c (seq (n + 1)) = true))
  x n := CastleToLevel.flagOf c.sy c.nm (held c seq E n)
  t_E := by rw [held_E]; exact A.t_E
  ph_E := by rw [held_E]; exact A.ph_E
  task_E := by
    rw [held_E]
    show (peek (seq (E + 1)) c.sy.StarFlagTaskControl).toNat = 2
    show ((seq (E + 1)).ram.get! c.task).toNat = 2
    rw [A.task_E]
    rfl
  y_E := by
    rw [held_E, flagOf_cnt (quiet_start hC A.entry.at0)]
    show c.lim + 30 ≤ ((seq (E + 1)).ram.get! c.y).toNat
    rw [A.y_E]
    exact hC.y0
  after := A.after
  step := by
    intro n h1 h2
    unfold CastleToLevel.FlagStep
    by_cases h5 : (CastleToLevel.flagOf c.sy c.nm (held c seq E n)).task = 5
    · rw [if_pos (by simp [h1, h5]), held_five h1 h5]
    · rw [held_run h5]
      rcases held_inv' hC hn A h1 (by omega) with h | ⟨he, hg⟩
      · exact absurd h h5
      · have F := (frame_step hC hg (inp n)).2.2.2
        rw [← hn] at F
        by_cases hp : paused c (seq (n + 1)) = true
        · rw [if_pos (by simp [h1, hp]), he]
          rw [if_pos hp] at F
          exact F.1
        · rw [if_neg (by simp [h5, hp]), he]
          rw [if_neg hp] at F
          exact F.1
  task_L := by
    show (CastleToLevel.flagOf c.sy c.nm (held c seq E L)).task = 5
    rcases held_inv' hC hn A A.after (by omega) with h | ⟨he, hg⟩
    · exact h
    · by_cases h5 : (CastleToLevel.flagOf c.sy c.nm (held c seq E L)).task = 5
      · exact h5
      · have hl := (frame_step hC hg (inp L)).2.2.1
        rw [← hn, A.level] at hl
        cases hl

end

/-! ## The context of the check -/

/-- the bytes that the states of a frame's start know, by name and number of bytes from the name -/
def knownNames : List (String × Nat) :=
  [("ObjectOffset", 1), ("GameEngineSubroutine", 1), ("Enemy_Flag", 6), ("Enemy_ID", 6), ("Player_State", 1), ("Block_State", 2), ("Misc_State", 9),
   ("PlayerFacingDir", 1), ("SprObject_PageLoc", 1), ("SprObject_X_Position", 1), ("SprObject_Y_Speed", 1), ("SprObject_Y_HighPos", 1), ("SprObject_Y_Position", 1),
   ("EnemyData", 1), ("EnemyDataHigh", 1), ("NoteLenLookupTblOfs", 1), ("Square1SoundBuffer", 1), ("NoiseSoundBuffer", 1), ("AreaMusicBuffer", 1), ("MusicData", 1),
   ("MusicDataHigh", 1), ("PauseSoundQueue", 1), ("AreaMusicQueue", 1), ("EventMusicQueue", 1), ("NoiseSoundQueue", 1), ("Square1SoundQueue", 1),
   ("FlagpoleFNum_Y_Pos", 1), ("FlagpoleScore", 1), ("FloateyNum_Control", 6), ("DigitModifier", 6), ("VRAM_Buffer1", 1), ("VineFlagOffset", 1),
   ("Platform_X_Scroll", 1), ("SprObject_SprAttrib", 1), ("Block_RepFlag", 2), ("Cannon_PageLoc", 6), ("Cannon_X_Position", 6), ("Cannon_Y_Position", 4),
   ("SecondaryHardMode", 1), ("EnemyFrenzyQueue", 1), ("SprShuffleAmtOffset", 1), ("SprShuffleAmt", 3), ("SprDataOffset", 1), ("Enemy_SprDataOffset", 7),
   ("Block_SprDataOffset", 2), ("Bubble_SprDataOffset", 3), ("FBall_SprDataOffset", 2), ("SwimmingFlag", 1), ("PlayerChangeSizeFlag", 1),
   ("JumpspringAnimCtrl", 1), ("FireballThrowingTimer", 1), ("DisableCollisionDet", 1), ("ScreenEdge_PageLoc", 1), ("ScreenRight_PageLoc", 1),
   ("AreaParserTaskNum", 1), ("Sprite0HitDetectFlag", 1), ("ScrollLock", 1), ("EnemyDataOffset", 1), ("VerticalScroll", 1),
   ("LoopCommand", 1), ("TimerControl", 1), ("JoypadBitMask", 2), ("AreaType", 1), ("CurrentPlayer", 1), ("PlayerSize", 1), ("PlayerStatus", 1),
   ("LevelNumber", 1), ("WorldNumber", 1), ("OperMode", 1), ("OperMode_Task", 1), ("VRAM_Buffer_AddrCtrl", 1), ("DisableScreenFlag", 1),
   ("GamePauseStatus", 1), ("GamePauseTimer", 1), ("Mirror_PPU_CTRL_REG1", 1), ("Mirror_PPU_CTRL_REG2", 1), ("RunningTimer", 1), ("StarInvincibleTimer", 1),
   ("DAC_Counter", 1), ("NoteLengthTblAdder", 1), ("PauseModeFlag", 1)]

/-- the names the check reads -/
def nameList : List String :=
  ["Enemy_Y_Position", "EnemyIntervalTimer", "IntervalTimerControl", "GameTimerDisplay", "SprObject_X_Speed", "Player_X_MoveForce", "SprObject_X_MoveForce",
   "Player_XSpeedAbsolute", "Player_CollisionBits", "SideCollisionTimer", "SprObject_X_Position", "SprObject_PageLoc", "RunningSpeed", "Player_MovingDir",
   "FireworksCounter", "Enemy_ID", "Enemy_Flag", "VRAM_Buffer1_Offset", "VRAM_Buffer1", "ScreenRight_X_Pos", "ScreenEdge_X_Pos", "EventMusicBuffer",
   "Square2SoundQueue", "SprShuffleAmtOffset", "ScrollThirtyTwo", "EnemyFrenzyBuffer", "Squ1_NoteLenCounter", "Squ1_EnvelopeDataCtrl", "ObjectOffset",
   "MusicOffset_Square1", "AltRegContentFlag", "StarFlagObject", "Fireworks", "FrameCounter", "Block_Buffer_1", "Block_Buffer_2"] ++ knownNames.map (·.1)

/-- the values of the names, from the text of the disassembly -/
def namesFrom (text : String) : Names :=
  let ls := text.splitOn "\n"
  nameList.eraseDups.filterMap fun n => (asmValue ls n).map (n, ·)

/-- the known bytes as RAM indices: the bytes of `knownNames` and the first block buffer -/
def knownOf (nm : Names) : List Nat :=
  let i := fun (n : String) => ((nm.ad n) &&& 0x7FF).toNat
  knownNames.flatMap (fun p => (List.range p.2).map (i p.1 + ·)) ++ (List.range (i "Block_Buffer_2" - i "Block_Buffer_1")).map (i "Block_Buffer_1" + ·)

/-- the context of the check: `r` is a machine at the castle entry, `tmax` the largest value of the timer -/
def ctxOf (sy : Syms) (nm : Names) (r : Machine) (tmax : Nat) : Ctx :=
  { E := { prg := r.prg, mask := r.prgMask, pad := AB.top, D := [], splits := [(((nm.ad "FrameCounter") &&& 0x7FF).toNat, 7), (((nm.ad "GamePauseStatus") &&& 0x7FF).toNat, 0x81)] }, sy, nm, r, K := knownOf nm, tmax }

end Smbrta.FlagRule
