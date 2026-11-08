import Theorems.SideChangeEnd
import Theorems.PipeEntryRule

/-!
# The change into the room, from conditions at the entry, at places of the pipe's frames, and at the exit

`PipeChangeBound` proves the change into the room from a hypothesis on every frame: `left` falls by at most one. Here that hypothesis is proved on every frame of the change. The 48 frames of the pipe's timer come from one
condition on the state at the entry (`Entry`) and conditions on the machine at some places of each of these frames (`PlaceOK`). The 43 frames after the timer come from conditions at the exit: the sound's bytes (`Quiet`), the
song's bytes (`SongAt`) and the screen buffer, and no Start on the frames of the game core. The frame after the pipe clears RAM, and the frame ends inside that loop, as in the side pipe, and `SideChangeEnd` has what follows
such a frame. There is no game data in this file. Page: `1-1/b-3-2-PipeChangeEnd.md`.
-/

namespace Smbrta.PipeChangeEnd

open PipeTransition (frame run zeros)
open PipeTransitionAll (go Names asmValue)
open SideChangeBound
open SideChangeEnd
open PipeChangeBound (leftOf inPipe)

/-! ## The numbers of the change -/

/-- the frames of the pipe's timer, and the frames after it -/
def timerF : Nat := 48
def afterF : Nat := 43

/-! ## The search for the tables: no part of the proof -/

/-- the key of the search: a state at dot 0 stays apart, since the next tick decides the vblank flag -/
def ykey (E : Env) (keep : List Nat) (A : AS) : Nat := xkey E keep A * 2 + (if A.lo == 0 then 1 else 0)

def yroute (E : Env) (keep : List Nat) (X : Search) (B : AS) : Search :=
  let K := ykey E keep B
  match X.pending[K]? with
  | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- the search for a frame: one step at a time, in the order of `xprio` -/
partial def yloop (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (limit : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
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
      if n ≥ 2 || c % 64 == 0 then X := { X with out := X.out.push A }
      let rs := xsuccs E ops A
      X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
      if rs.any (·.isNone) then
        X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some A }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with ends := X.ends.push b }
        else X := yroute E keep X b
  return X

def ysearch (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (R : List AS) : Search :=
  yloop E ops keep 4000000 (R.foldl (yroute E keep) {})

/-- from `A` to the place `pl`, with no joins: the states at the place. A state that fails or ends the frame is left out here; the check finds it. -/
partial def toPlace (E : Env) (ops : Array (AM Unit)) (pl : UInt16) (A : AS) : List AS := Id.run do
  let mut todo := [A]
  let mut out : List AS := []
  let mut steps := 0
  while !todo.isEmpty && steps < 100000 do
    let cur := todo.head!
    todo := todo.tail!
    steps := steps + 1
    for r in xsuccs E ops cur do
      match r with
      | none => pure ()
      | some b =>
        if b.pc == pl then out := b :: out
        else if b.k == cur.k then todo := b :: todo
  return out

/-- join the states that have the same key -/
def joinByKey (E : Env) (keep : List Nat) (l : List AS) : List AS :=
  let m : Std.HashMap Nat AS := l.foldl (fun (h : Std.HashMap Nat AS) A =>
    let k := keyOf E keep A
    match h[k]? with
    | some B => h.insert k (B.join A)
    | none => h.insert k A) {}
  m.values

/-- the candidates of a table -/
def indexOf (E : Env) (keep : List Nat) (t : Array AS) : Std.HashMap Nat (List Nat) × ByteArray :=
  let P := t.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  (P.1, P.2.1)

/-- `left` on the first of some states -/
def leftHead (c : Ctx) (R : List AS) : Nat := (R.head?.map (fun S => c.left (mOf S))).getD 0

/-- the states after the frame's end: states that differ only in what the search may join are one state -/
def afterEnds (c : Ctx) (ends : Array AS) : List AS :=
  let R := nextStates c.E false ends.toList
  let m : Std.HashMap Nat AS := R.foldl (fun (h : Std.HashMap Nat AS) A =>
    let k := ykey c.E c.keep A
    match h[k]? with
    | some B => h.insert k (B.join A)
    | none => h.insert k A) {}
  m.values

/-- a row from the states `R`, by the search, and what comes next -/
def rowY (c : Ctx) (R : List AS) : Row × List AS :=
  let X := ysearch c.E (aRows c.E).toArray c.keep R
  let I := indexOf c.E c.keep X.out
  ({ core := false, R, v := leftHead c R, t := X.out, idx := I.1, cut := I.2 }, afterEnds c X.ends)

/-- every `n`-th of a list -/
def everyNth (n : Nat) (l : List α) : List α := (l.zipIdx.filter fun p => p.2 % n == 0).map (·.1)

/-- the row of the frame after the exit: each state goes on alone to the place `pl`. There the states of every `n`-th state of `R` join, without the bytes `B`, with the dots `dl`..`dh`, and the search goes on from them. The walk of the check starts from every state of `R`. -/
def rowSong (c : Ctx) (pl : UInt16) (B : List Nat) (dl dh n : Nat) (R : List AS) : Row × List AS :=
  let ops := (aRows c.E).toArray
  let widen1 := fun (A : AS) => (B.foldl (fun (S : AS) i => S.setK i TaintRun.AB.top) { A with lo := Nat.min A.lo dl, hi := Nat.max A.hi dh })
  let J := joinByKey c.E c.keep ((everyNth n R).flatMap (toPlace c.E ops pl)) |>.map widen1
  let X := ysearch c.E ops c.keep J
  let t := J.toArray ++ X.out
  let I := indexOf c.E c.keep t
  ({ core := false, R, v := leftHead c R, t, idx := I.1, cut := I.2 }, afterEnds c X.ends)

/-- the rows of the frames that clear RAM: from `R`, two frames, then the rows of `SideChangeEnd` -/
def rowsAfter (c : Ctx) (n : Nat) (r0 : Row × List AS) : List Row :=
  let r1 := rowY c r0.2
  r0.1 :: r1.1 :: rowsFrom c n r1.2

/-! ## The song -/

/-- the bytes of the song that move: the pointer, the offsets, the counters -/
def songNames : List (String × Nat × Nat) :=
  [("MusicData", 0, 2), ("MusicOffset_Square2", 0, 1), ("MusicOffset_Square1", 0, 1), ("MusicOffset_Triangle", 0, 1), ("MusicOffset_Noise", 0, 1), ("NoiseDataLoopbackOfs", 0, 1),
   ("Squ2_NoteLenCounter", 0, 1), ("Squ2_NoteLenBuffer", 0, 1), ("Squ1_NoteLenCounter", 0, 1), ("Tri_NoteLenCounter", 0, 1), ("Tri_NoteLenBuffer", 0, 1), ("Noise_BeatLenCounter", 0, 1)]

/-- the byte that says which part of the song comes next: only a frame that ends a part reads it -/
def partName : String := "GroundMusicHeaderOfs"

/-- the song's bytes as RAM indices, with the part -/
def bytesOfSong (nx : Names) : List Nat := adI nx partName :: bytesOf nx songNames

/-- the machine has a row -/
def SongAt (song : List (List (Nat × UInt8))) (m : Machine) : Prop := ∃ q ∈ song, Quiet q m

/-- the rows of the song from `m` and `n` frames with no input. A row has the bytes of the song, and on a frame that ends a part, the part. -/
def songRows (nx : Names) (m : Machine) : Nat → List (List (Nat × UInt8))
  | 0 => []
  | n + 1 =>
    let m' := frame m 0
    let B := bytesOf nx songNames
    let p := adI nx partName
    let row := B.map (fun i => (i, m.ram.get! i)) ++ (if m.ram.get! p != m'.ram.get! p then [(p, m.ram.get! p)] else [])
    row :: songRows nx m' n

/-- the same rows, each once -/
def songTable (nx : Names) (m : Machine) (n : Nat) : List (List (Nat × UInt8)) :=
  ((songRows nx m n).foldl (fun (s : Std.HashSet (List (Nat × UInt8))) r => s.insert r) {}).toList

/-! ## Conditions at places of a frame

A whole frame of the pipe's routine runs the screen update, the sound, the objects and the area parser, and their bytes differ from run to run. So a frame is followed from place to place in the code. At a place a machine has one row
of a table, and its dot is at most a bound. A place with no rows is a place that the frame does not reach. These are conditions on one machine, at one instruction of the frame (`PlaceOK`). -/

/-- a place in the code, the rows that a machine there has, and a bound on its dot -/
structure Place where
  pc : UInt16
  rows : List (List (Nat × UInt8))
  tmax : Nat

/-- **The condition at the places**, on one machine -/
def PlaceOK (P : List Place) (m : Machine) : Prop :=
  ∀ p ∈ P, m.pc = p.pc → m.fdot ≤ p.tmax ∧ ∃ q ∈ p.rows, Quiet q m

/-- the states for a machine at a place: one for each row -/
def placeSplit (P : List Place) (A : AS) : List AS :=
  match P.find? (fun p => p.pc == A.pc) with
  | some p => p.rows.map fun q => refine q { A with hi := Nat.min A.hi p.tmax }
  | none => [A]

/-- the accumulator, or an index register, by one bit -/
def bitA (b : UInt8) (A : AS) : List AS :=
  match A.a.bit b with
  | some _ => [A]
  | none => [{ A with a := A.a.or (TaintRun.AB.known b) }, { A with a := A.a.and (TaintRun.AB.known (~~~b)) }]
def bitX (b : UInt8) (A : AS) : List AS :=
  match A.x.bit b with
  | some _ => [A]
  | none => [{ A with x := A.x.or (TaintRun.AB.known b) }, { A with x := A.x.and (TaintRun.AB.known (~~~b)) }]
def bitY (b : UInt8) (A : AS) : List AS :=
  match A.y.bit b with
  | some _ => [A]
  | none => [{ A with y := A.y.or (TaintRun.AB.known b) }, { A with y := A.y.and (TaintRun.AB.known (~~~b)) }]

/-- the bits of a byte that are not known -/
def unkBits (b : TaintRun.AB) : Nat := (bitList.filter fun m => b.k &&& m == 0).length

/-- by all bits -/
def allBits (f : UInt8 → AS → List AS) (A : AS) : List AS := bitList.foldl (fun l b => l.flatMap (f b)) [A]

/-- the pieces this step needs: at the jump engine by the accumulator, at a read or write through a pointer by the low byte of the pointer, at a write with an index by the index -/
def zsplit (jump : UInt16) (E : Env) (A : AS) : List AS :=
  if A.nmi || A.pc < 0x8000 then [A] else
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  if A.pc == jump then (if decide (unkBits A.a ≤ 4) then allBits bitA A else [A])
  else if op == 0xB1 || op == 0x91 then
    let z := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
    if (A.getK (z + 1).toNat).isK && !(A.getK z.toNat).isK then allBits (splitBit z.toNat) A else [A]
  else if op == 0x9D then (if decide (unkBits A.x ≤ 4) then allBits bitX A else [A])
  else if op == 0x99 then (if decide (unkBits A.y ≤ 4) then allBits bitY A else [A])
  else [A]

/-- a step: the row, the pieces, the rules of `SideChangeEnd` -/
def zsuccs (P : List Place) (jump : UInt16) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  ((placeSplit P A).flatMap (zsplit jump E)).flatMap (xsuccs E ops)

section
variable {E : Env} {F : Nat × UInt8}

theorem refine_k (qs : List (Nat × UInt8)) (A : AS) : (refine qs A).k = A.k := by
  induction qs generalizing A with
  | nil => rfl
  | cons q t ih => exact ih _

/-- a machine at a place is in one of the states -/
theorem cov_place {P : List Place} {A : AS} {m : Machine} (hs : Sim E F A m) (hp : PlaceOK P m) : ∃ B ∈ placeSplit P A, Sim E F B m ∧ B.k = A.k := by
  unfold placeSplit
  cases e : P.find? (fun p => p.pc == A.pc) with
  | none => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | some p =>
    have hm := List.mem_of_find?_eq_some e
    have hq := List.find?_some e
    have hpc : m.pc = p.pc := by
      rw [hs.pc]
      exact (by simpa using hq : p.pc = A.pc).symm
    obtain ⟨h1, q, hq1, hq2⟩ := hp p hm hpc
    refine ⟨_, List.mem_map.2 ⟨q, hq1, rfl⟩, sim_refines hq2 { hs with hi := ?_, lim := ?_ }, refine_k _ _⟩
    · exact Nat.le_min.2 ⟨hs.hi, h1⟩
    · exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hs.lim

theorem cov_bitA {b : UInt8} (hb : b ∈ bitList) : Cov E F (bitA b) := by
  intro A m hs
  unfold bitA
  cases e : A.a.bit b with
  | some _ => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    obtain ⟨j, hj⟩ := bit_of_list b hb
    have hbb : ∀ i, i < 8 → TaintRun.bt b i = decide (i = j.1) := fun i hi => hj ⟨i, hi⟩
    by_cases hx : m.a &&& b = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with a := ?_ }, rfl⟩
      have := TaintRun.mem_and hs.a (TaintRun.mem_known_self (~~~b))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, { hs with a := ?_ }, rfl⟩
      have := TaintRun.mem_or hs.a (TaintRun.mem_known_self b)
      rwa [or_self_of hbb (bit_of_ne hbb hx)] at this

theorem cov_bitX {b : UInt8} (hb : b ∈ bitList) : Cov E F (bitX b) := by
  intro A m hs
  unfold bitX
  cases e : A.x.bit b with
  | some _ => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    obtain ⟨j, hj⟩ := bit_of_list b hb
    have hbb : ∀ i, i < 8 → TaintRun.bt b i = decide (i = j.1) := fun i hi => hj ⟨i, hi⟩
    by_cases hx : m.x &&& b = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with x := ?_ }, rfl⟩
      have := TaintRun.mem_and hs.x (TaintRun.mem_known_self (~~~b))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, { hs with x := ?_ }, rfl⟩
      have := TaintRun.mem_or hs.x (TaintRun.mem_known_self b)
      rwa [or_self_of hbb (bit_of_ne hbb hx)] at this

theorem cov_bitY {b : UInt8} (hb : b ∈ bitList) : Cov E F (bitY b) := by
  intro A m hs
  unfold bitY
  cases e : A.y.bit b with
  | some _ => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    obtain ⟨j, hj⟩ := bit_of_list b hb
    have hbb : ∀ i, i < 8 → TaintRun.bt b i = decide (i = j.1) := fun i hi => hj ⟨i, hi⟩
    by_cases hx : m.y &&& b = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with y := ?_ }, rfl⟩
      have := TaintRun.mem_and hs.y (TaintRun.mem_known_self (~~~b))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, { hs with y := ?_ }, rfl⟩
      have := TaintRun.mem_or hs.y (TaintRun.mem_known_self b)
      rwa [or_self_of hbb (bit_of_ne hbb hx)] at this

theorem cov_allBits {f : UInt8 → AS → List AS} (hf : ∀ b ∈ bitList, Cov E F (f b)) : Cov E F (allBits f) := by
  intro A m hs
  unfold allBits
  have key : ∀ (L : List UInt8) (l : List AS), (∀ b ∈ L, b ∈ bitList) → (∃ B ∈ l, Sim E F B m ∧ B.k = A.k) →
      ∃ B ∈ L.foldl (fun l b => l.flatMap (f b)) l, Sim E F B m ∧ B.k = A.k := by
    intro L
    induction L with
    | nil => exact fun l _ h => h
    | cons b L ih =>
      intro l hL h
      exact ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (cov_flat (hf b (hL b List.mem_cons_self)) h)
  exact key _ _ (fun _ h => h) ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem cov_zsplit (jump : UInt16) : Cov E F (zsplit jump E) := by
  intro A m hs
  have triv : ∃ B ∈ [A], Sim E F B m ∧ B.k = A.k := ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  unfold zsplit
  split
  · exact triv
  dsimp only
  split
  · split
    · exact cov_allBits (fun b hb => cov_bitA hb) A m hs
    · exact triv
  split
  · split
    · exact cov_allBits (fun b hb => cov_bit (Nat.lt_trans (UInt8.toNat_lt _) (by decide)) hb) A m hs
    · exact triv
  split
  · split
    · exact cov_allBits (fun b hb => cov_bitX hb) A m hs
    · exact triv
  split
  · split
    · exact cov_allBits (fun b hb => cov_bitY hb) A m hs
    · exact triv
  · exact triv

/-- a step of the machine is followed, when the machine meets the condition at the places -/
theorem s_zsuccs {P : List Place} {jump : UInt16} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hs : Sim E F A m) (hp : PlaceOK P m) :
    ∃ r ∈ zsuccs P jump E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨B0, h0, s0, k0⟩ := cov_place hs hp
  obtain ⟨B1, h1, s1, k1⟩ := cov_zsplit jump B0 m s0
  obtain ⟨r, hr, g⟩ := s_xsuccs hops hT s1
  refine ⟨r, List.mem_flatMap.2 ⟨B1, List.mem_flatMap.2 ⟨B0, h0, h1⟩, hr⟩, fun B hB => ?_⟩
  obtain ⟨g1, g2⟩ := g B hB
  refine ⟨g1, ?_⟩
  unfold StepRel at g2 ⊢
  rw [k1, k0] at g2
  exact g2

end

/-! ## One frame from place to place -/

/-- what the search is told: at these places what is listed is forgotten on arrival, and the registers too if the flag is set -/
structure Hint where
  pc : UInt16
  forget : List Nat
  dead : Bool
  /-- the register `Y`, the accumulator and the flags are dead here -/
  deadY : Bool := false

/-- a number from the state, for the search -/
def zhash (keep : List Nat) (A : AS) : UInt64 := Id.run do
  let mix := fun (h : UInt64) (x : UInt64) => (h ^^^ x) * 1099511628211
  let num := fun (b : TaintRun.AB) => b.k.toUInt64 * 256 + (b.v &&& b.k).toUInt64
  let mut h : UInt64 := 14695981039346656037
  h := mix h (num A.x)
  h := mix h (num A.y)
  for i in keep do
    h := mix h (num (A.getK i))
  let mut j := A.s.toNat + 1
  while j < 256 do
    h := mix h (num (A.getK (0x100 + j)))
    j := j + 1
  return h

/-- the key of the search: the stack pointer and the program counter come first, so that deep calls end first -/
def zskey (E : Env) (jump : UInt16) (keep : List Nat) (A : AS) : Nat :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let useA := op == 0x29 || op == 0xD0 || op == 0xF0 || (jump ≤ A.pc && A.pc < jump + 4)
  let num := fun (b : TaintRun.AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := (A.k * 256 + A.s.toNat) * 65536 + A.pc.toNat
  let n := n * 32 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0) + (if A.lo == 0 then 16 else 0)
  let n := n * 65536 + (if useA then num A.a else 0)
  n * 4294967296 + (zhash keep A).toNat % 4294967296

/-- what a state is turned into at a place, for the search -/
def hintNorm (H : List Hint) (B0 : AS) : AS :=
  match H.find? (fun h => h.pc == B0.pc) with
  | some h =>
    let b := h.forget.foldl (fun S i => S.setK i TaintRun.AB.top) B0
    if h.dead && !b.nmi then { b with x := TaintRun.AB.top, y := TaintRun.AB.top, a := TaintRun.AB.top, p := TaintRun.AB.top }
    else if h.deadY && !b.nmi then { b with y := TaintRun.AB.top, a := TaintRun.AB.top, p := TaintRun.AB.top } else b
  | none => B0

/-- what the walk uses -/
structure ZCfg where
  E : Env
  ops : Array (AM Unit)
  places : List Place
  jump : UInt16
  /-- what parts the candidates for a state: no part of the proof -/
  ckeys : List Nat
  keep : List Nat
  hints : List Hint
  /-- the states of the certificate -/
  t : Array AS
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

/-- the number under which the candidates of a state are kept -/
def zkey (ckeys : List Nat) (A : AS) : Nat :=
  let n := (A.k * 256 + A.s.toNat) * 65536 + A.pc.toNat
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0)
  ckeys.foldl (fun n i => n * 65536 + (A.getK i).k.toNat * 256 + ((A.getK i).v &&& (A.getK i).k).toNat) n

/-- the same number for a state that does not know these bytes -/
def zkeyTop (ckeys : List Nat) (A : AS) : Nat :=
  let n := (A.k * 256 + A.s.toNat) * 65536 + A.pc.toNat
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0)
  ckeys.foldl (fun n _ => n * 65536) n

/-- the table has a state that covers `B` -/
def zcover (C : ZCfg) (B : AS) : Bool :=
  (C.idx.getD (zskey C.E C.jump C.keep (hintNorm C.hints B)) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D
    | none => false

/-- from `A`, step by step until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def zwalk (C : ZCfg) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (zsuccs C.places C.jump C.E C.ops A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && zcover C B) || zwalk C fin n B
      else B.k == A.k + 1 && fin B

section
variable {C : ZCfg} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool}

open PipeEntryRule (trace trace_stop frame_trace nxt)

def ZLive (C : ZCfg) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, zwalk C fin n A = true

theorem cover_zlive (ht : C.t.all (zwalk C fin Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : zcover C B = true) :
    ∃ D, ZLive C fin F D m ∧ D.k = B.k := by
  unfold zcover at h
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
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

theorem zlive_step (ht : C.t.all (zwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : ZLive C fin F A m) (hp : PlaceOK C.places m) :
    (∃ A', ZLive C fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [zwalk] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_zsuccs (P := C.places) (jump := C.jump) hops hT hs hp
    simp only [zwalk, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_zlive ht h1 h3
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

theorem zframe_run (ht : C.t.all (zwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {m : Machine} {i : UInt8} (hP : ∀ j, PlaceOK C.places (trace m i j)) :
    ∀ (n j : Nat) (A : AS), ZLive C fin F A (trace m i j) → (trace m i j).frame = m.frame → dotsPerFrame ≤ (trace m i j).fdot + 3 * n →
      (trace m i (j + n)).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (trace m i (j + n)) := by
  intro n
  induction n with
  | zero =>
    intro j A hl _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro j A hl hf hd
    have hh := hl.1.halted
    have hnx : trace m i (j + 1) = (go step (trace m i j)).2 := by
      show nxt (m.frame + 1) (trace m i j) = _
      simp only [nxt]
      rw [if_neg]
      simp [hf, hh]
    have e : j + (n + 1) = (j + 1) + n := by omega
    rw [e]
    rcases zlive_step ht hops hT hl (hP j) with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
    · rw [← hnx] at h1 h3 h4
      have := ih (j + 1) A' h1 (h3.trans hf) (by omega)
      rw [h2] at this
      exact this
    · rw [← hnx] at h1 h4
      have hstop : ((trace m i (j + 1)).frame ≥ m.frame + 1 || (trace m i (j + 1)).halted) = true := by
        simp [h1, hf]
      rw [trace_stop hstop n]
      exact ⟨by rw [h1, hf], B, h2, h3, h4⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of a machine of `S`, when every instruction of the frame meets the condition at the places. -/
theorem zframe_of_walk (ht : C.t.all (zwalk C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hE : C.E.pad = TaintRun.AB.top)
    {S : AS} {m : Machine} (hw : zwalk C fin Fu S = true) (hs : Sim C.E F S m) (i : UInt8) (hP : ∀ j, PlaceOK C.places (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  rw [frame_trace]
  have hs0 : Sim C.E F S (trace m i 0) := { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  have hf : dotsPerFrame ≤ (trace m i 0).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  have := zframe_run ht hops hT hP fuelPerFrame 0 S ⟨hs0, Fu, hw⟩ rfl hf
  rw [Nat.zero_add] at this
  exact this

end

/-! ## The search for a table of the frame: no part of the proof -/

/-- the state of the search -/
structure ZS where
  pending : Std.TreeMap Nat AS compare := {}
  inN : Std.HashMap Nat Nat := {}
  out : Array AS := #[]
  /-- the keys under which the states of the table were found -/
  outK : Array Nat := #[]
  steps : Nat := 0
  fails : Nat := 0
  ends : Array AS := #[]
  /-- states that wait at a place until all the others have got there -/
  held : Std.TreeMap Nat AS compare := {}
  /-- some states where a step fails -/
  failed : Array AS := #[]

def zroute (E : Env) (jump : UInt16) (keep : List Nat) (H : List Hint) (X : ZS) (B0 : AS) : ZS :=
  let B := hintNorm H B0
  let K := zskey E jump keep B
  match H.findIdx? (fun h => h.pc == B0.pc) with
  | some st =>
    -- the place's number in the list comes first: the places are let go in their order
    let K2 := st * (2 ^ 128) + K
    match X.held[K2]? with
    | some P => { X with held := X.held.insert K2 (P.join B) }
    | none => { X with held := X.held.insert K2 B }
  | none =>
    match X.pending[K]? with
    | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
    | none => { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- the search for a table -/
partial def zloop (P : List Place) (jump : UInt16) (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (H : List Hint) (limit : Nat) (X0 : ZS) : ZS := Id.run do
  let mut X := X0
  let mut c := 0
  while true do
    if X.steps > limit then
      X := { X with fails := X.fails + 1 }
      break
    match X.pending.minEntry? with
    | none =>
      match X.held.minEntry? with
      | none => break
      | some (k0, _) =>
        -- the states that wait at the first place in the list go into the table, and on
        let st := k0 / (2 ^ 128)
        for (K2, A) in X.held.toList do
          if K2 / (2 ^ 128) == st then
            let K := K2 % (2 ^ 128)
            X := { X with pending := X.pending.insert K A, inN := X.inN.insert K 2, held := X.held.erase K2 }
    | some (key, A) =>
      let n := X.inN.getD key 1
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      c := c + 1
      if n ≥ 2 || c % 256 == 0 then X := { X with out := X.out.push A, outK := X.outK.push key }
      let rs := zsuccs P jump E ops A
      X := { X with steps := X.steps + rs.length }
      if rs.any (·.isNone) then X := { X with fails := X.fails + 1, failed := if X.failed.size < 40 then X.failed.push A else X.failed }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with ends := X.ends.push b }
        else X := zroute E jump keep H X b
  return X

/-- the configuration from the table found -/
def zcfgOf (P : List Place) (jump : UInt16) (E : Env) (ckeys keep : List Nat) (H : List Hint) (starts : List AS) : ZCfg :=
  let ops := (aRows E).toArray
  let X := zloop P jump E ops keep H 6000000 (starts.foldl (zroute E jump keep H) {})
  let I := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := X.outK.getD acc.2.2 0
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops, places := P, jump, ckeys, keep, hints := H, t := X.out, idx := I.1, cut := I.2.1 }

/-! ## The rows of the places, from real frames: no part of the proof -/

/-- the machine when the frame of `m` with the input `i` first comes to `pc`, if it does -/
def firstAtPlace (pc : UInt16) (m : Machine) (i : UInt8) : Option Machine := Id.run do
  let mut t : Machine := { m with pad := smbToPad i }
  for _ in [0:40000] do
    if t.frame != m.frame || t.halted then return none
    if t.pc == pc then return some t
    t := (go step t).2
  return none

/-- a name's byte -/
def nb (nx : Names) (n : String) (o : Nat := 0) : Nat := adI nx n + o

/-- the bytes a record of a screen buffer takes after its three first bytes, from its third byte: one byte when it repeats one byte, else its count. This is the form the NMI reads; it only makes rows. -/
def recordData (len : UInt8) : Nat := if len &&& 0x40 != 0 then 1 else (len &&& 0x3F).toNat

/-- the values that `UpdScrollVar` compares with, from the ROM: the value of `VRAM_Buffer_AddrCtrl` that skips the parser, and the scroll that starts a column -/
structure ParserK where
  ctl2 : UInt8
  thr : UInt8

def parserKOf (sy : Syms) (m : Machine) : ParserK :=
  let a := PipeEntryRule.findOp m sy.UpdScrollVar 0xC9 64
  let b := PipeEntryRule.findOp m (a + 2) 0xC9 64
  { ctl2 := romByte m (a + 1), thr := romByte m (b + 1) }

/-- the bytes that say the form of the screen buffer in use: the first byte of each record and its length -/
def shapeRow (nx : Names) (pk : ParserK) (m : Machine) : List (Nat × UInt8) := Id.run do
  let ctl := m.ram.get! (nb nx "VRAM_Buffer_AddrCtrl")
  let base := if ctl == pk.ctl2 then nb nx "VRAM_Buffer2" else nb nx "VRAM_Buffer1"
  let mut p := 0
  let mut out : List (Nat × UInt8) := [(nb nx "VRAM_Buffer_AddrCtrl", ctl)]
  for _ in [0:40] do
    let b0 := m.ram.get! (base + p)
    if b0 == 0 then
      out := (base + p, b0) :: out
      break
    let len := m.ram.get! (base + p + 2)
    out := (base + p, b0) :: (base + p + 2, len) :: out
    p := p + 3 + recordData len
  return out

/-- the bytes of the sprites' offsets -/
def shuffleBytes (nx : Names) : List Nat :=
  nb nx "SprShuffleAmtOffset" :: ((List.range 15).map (nb nx "SprDataOffset" ·) ++ (List.range 9).map (nb nx "Misc_SprDataOffset" ·))

/-- the bytes that the area parser reads -/
def parserBytes (nx : Names) : List Nat :=
  ["AreaData", "AreaDataHigh", "VRAM_Buffer2_Offset", "BlockBufferColumnPos", "CurrentPageLoc", "CurrentColumnPos", "TerrainControl", "BackloadingFlag", "AreaObjectPageLoc", "AreaDataOffset", "ForegroundScenery", "BackgroundScenery", "AreaType"].map (nb nx ·) ++
    (List.range 13).map (nb nx "MetatileBuffer" ·) ++ (List.range 3).map (nb nx "AreaObjectLength" ·) ++ (List.range 3).map (nb nx "AreaObjOffsetBuffer" ·) ++ [nb nx "AreaStyle"]

/-- the bytes that a new column does not read: the metatile buffer, and the offset of the second buffer -/
def deadAtStart (nx : Names) : List Nat := nb nx "VRAM_Buffer2_Offset" :: (List.range 13).map (nb nx "MetatileBuffer" ·)

/-- the row of the parser's place: while the parser waits, only what says so -/
def parserRow (nx : Names) (pk : ParserK) (m : Machine) : List (Nat × UInt8) :=
  let ac := nb nx "VRAM_Buffer_AddrCtrl"
  let tk := nb nx "AreaParserTaskNum"
  let sc := nb nx "ScrollThirtyTwo"
  let ctl := m.ram.get! ac
  let t := m.ram.get! tk
  let s := m.ram.get! sc
  if ctl == pk.ctl2 then [(ac, ctl)]
  else if t == 0 && s < pk.thr then [(ac, ctl), (tk, t), (sc, s)]
  else
    let row := [(ac, ctl), (tk, t), (sc, if t == 0 then s else 0)].filter (fun p => p.1 != sc || t == 0) ++ (parserBytes nx).map fun i => (i, m.ram.get! i)
    -- a column starts: the parser clears the metatile buffer before it reads it, and the offset of the second buffer is set to 0
    if t == 0 && m.ram.get! (nb nx "BackloadingFlag") == 0 then row.filter fun p => !(deadAtStart nx).contains p.1 else row

/-- a row at the parser's start, for each scroll value that starts it -/
def parserStarts (nx : Names) (pk : ParserK) (row : List (Nat × UInt8)) : List (List (Nat × UInt8)) :=
  let sc := nb nx "ScrollThirtyTwo"
  match row.find? (·.1 == sc) with
  | some (_, s) => if s ≥ pk.thr && row.length > 3 then (List.range 4).map fun k => row.map fun p => if p.1 == sc then (sc, pk.thr + k.toUInt8) else p else [row]
  | none => [row]

/-- the forms of the first screen buffer made from some records: each record is its first byte and its length -/
def shapesOf (nx : Names) (recs : List (UInt8 × UInt8)) (n : Nat) : List (List (Nat × UInt8)) :=
  let b := nb nx "VRAM_Buffer1"
  let ac := nb nx "VRAM_Buffer_AddrCtrl"
  let rec go : Nat → Nat → List (List (Nat × UInt8))
    | 0, p => [[(b + p, 0)]]
    | k + 1, p => [(b + p, 0)] :: recs.flatMap fun r =>
        let len := r.2
        let p' := p + 3 + recordData len
        (go k p').map fun t => (b + p, r.1) :: (b + p + 2, len) :: t
  (go n 0).map fun t => (ac, 0) :: t

/-- the rows that say the parser waits, for each value of the scroll -/
def parserWaitRows (nx : Names) (pk : ParserK) : List (List (Nat × UInt8)) :=
  let ac := nb nx "VRAM_Buffer_AddrCtrl"
  let tk := nb nx "AreaParserTaskNum"
  let sc := nb nx "ScrollThirtyTwo"
  [(ac, pk.ctl2)] :: (List.range pk.thr.toNat).map fun s => [(ac, 0), (tk, 0), (sc, s.toUInt8)]

/-! ## The frames of the pipe -/

/-- what the check of the pipe's frames says -/
structure ZOK (Cr Co : ZCfg) (E : Env) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Prop where
  ti : E.rkI < 2048
  er : Cr.E = E
  eo : Co.E = E
  or : Cr.ops = (aRows E).toArray
  oo : Co.ops = (aRows E).toArray
  pr : Cr.places = Co.places
  rkStarts : ∀ S ∈ starts, S.k = 0 ∧ S.rk = true ∧ S.spent = false
  tr : Cr.t.all (zwalk Cr (finRk starts) TaintRun.walkFuel) = true
  sr : ∀ S ∈ starts, zwalk Cr (finRk starts) TaintRun.walkFuel S = true
  to : Co.t.all (zwalk Co (finX (starts.map (toOne E)) base qs xb) TaintRun.walkFuel) = true
  so : ∀ S ∈ starts, zwalk Co (finX (starts.map (toOne E)) base qs xb) TaintRun.walkFuel (toOne E S) = true

def zcheck (Cr Co : ZCfg) (E : Env) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Bool :=
  let ones := starts.map (toOne E)
  let fr := finRk starts
  let fo := finX ones base qs xb
  decide (E.rkI < 2048) && starts.all (fun S => S.k == 0 && S.rk && !S.spent) &&
    Cr.t.all (zwalk Cr fr TaintRun.walkFuel) && starts.all (zwalk Cr fr TaintRun.walkFuel) &&
    Co.t.all (zwalk Co fo TaintRun.walkFuel) && starts.all (fun S => zwalk Co fo TaintRun.walkFuel (toOne E S))

section
variable {E : Env} {Cr Co : ZCfg} {starts base : List AS} {qs xb : List (Nat × UInt8)}

open PipeEntryRule (trace)

/-- **One frame of the pipe's routine, for any input, when every instruction of the frame meets the condition at the places.** The frame stays in the state during the pipe, with the counter falling by at most one, or the
counter was 1 and the frame leaves the routine: then the bytes `xb` have their values, and with the bytes `qs`, the state is in `base`. -/
theorem z_step (hc : ZOK Cr Co E starts base qs xb) (hp : E.pad = TaintRun.AB.top) {m : Machine} (h : InvAt E starts m) (i : UInt8) (hP : ∀ j, PlaceOK Cr.places (trace m i j)) :
    (InvAt E starts (frame m i) ∧ (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1) ∨
      (tm E m = 1 ∧ ExitAt xb (frame m i) ∧ (Quiet qs (frame m i) → ∃ D ∈ base, Sim E ((frame m i).frame, 2) D (frame m i))) := by
  have hE1 := hc.er
  have hE2 := hc.eo
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, hs⟩)⟩ := h
  · obtain ⟨k0, _, _⟩ := hc.rkStarts S hS
    have hsr : Sim Cr.E (m.frame, tm E m) S m := by rw [hE1]; exact hs
    obtain ⟨g1, B, g2, g3, g4⟩ := zframe_of_walk (C := Cr) (F := (m.frame, tm E m)) hc.tr (by rw [hE1]; exact hc.or) h2 (by rw [hE1]; exact hp) (hc.sr S hS) hsr i hP
    rw [hE1] at g4
    simp only [finRk, Bool.and_eq_true, List.any_eq_true] at g2
    obtain ⟨hr, S', hS', hle⟩ := g2
    have hv : (frame m i).ram.get! E.rkI = if B.spent then tm E m - 1 else tm E m := g4.rkv hr
    have hbase : Sim E ((frame m i).frame, tm E (frame m i)) ({ B with k := 0, spent := false } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro _
        rfl
    have hs' := sim_le hle hbase
    have hle2 : (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1 := by
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat + 1
      rw [hv]
      split
      · rw [u8_sub_one h2]
        omega
      · omega
    left
    refine ⟨⟨S', hS', ?_⟩, hle2⟩
    have hge : 1 ≤ (tm E (frame m i)).toNat := by omega
    by_cases h3 : 2 ≤ (tm E (frame m i)).toNat
    · exact Or.inl ⟨h3, hs'⟩
    · have he : tm E (frame m i) = 1 := by
        apply UInt8.toNat_inj.1
        have : (1 : UInt8).toNat = 1 := rfl
        omega
      exact Or.inr ⟨he, sim_toOne hc.ti hs' he _ rfl⟩
  · have hsr : Sim Co.E (m.frame, 2) (toOne E S) m := by rw [hE2]; exact hs
    have hP' : ∀ j, PlaceOK Co.places (trace m i j) := by
      rw [← hc.pr]
      exact hP
    obtain ⟨g1, B, g2, g3, g5⟩ := zframe_of_walk (C := Co) (F := (m.frame, 2)) hc.to (by rw [hE2]; exact hc.oo) (Nat.le_refl _) (by rw [hE2]; exact hp) (hc.so S hS) hsr i hP'
    rw [hE2] at g5
    have g4 : Sim E (m.frame, 2) B (frame m i) := g5
    simp only [finX, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at g2
    obtain ⟨hr, (⟨S', hS', hle⟩ | ⟨hx, D, hD, hle⟩)⟩ := g2
    · obtain ⟨S2, hS2, rfl⟩ := List.mem_map.1 hS'
      have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
        refine { g4 with fr := ?_, rkv := ?_ }
        · show (frame m i).frame = (frame m i).frame + 0
          rfl
        · intro hr2
          have : B.rk = true := hr2
          rw [hr] at this
          cases this
      have hs' := sim_le hle hbase
      have he := one_of_sim hc.ti hs'
      left
      refine ⟨⟨S2, hS2, Or.inr ⟨he, hs'⟩⟩, ?_⟩
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat + 1
      rw [h1, he]
      decide
    · right
      refine ⟨h1, fun p hq => sim_known g4 (hx p hq), fun hq => ⟨D, hD, ?_⟩⟩
      have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
        refine { g4 with fr := ?_, rkv := ?_ }
        · show (frame m i).frame = (frame m i).frame + 0
          rfl
        · intro hr2
          have : B.rk = true := hr2
          rw [hr] at this
          cases this
      exact sim_le hle (sim_refines hq hbase)

end

/-! ## The statement -/

/-- the bytes that the state at the exit knows. The values come from the reference machine when the timer has run out. -/
def exitNames : List (String × Nat × Nat) :=
  [("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("GameEngineSubroutine", 0, 1), ("ScreenRoutineTask", 0, 1), ("DisableScreenFlag", 0, 1),
   ("AreaPointer", 0, 1), ("EntrancePage", 0, 1), ("AltEntranceControl", 0, 1), ("HalfwayPage", 0, 1), ("CurrentPlayer", 0, 1), ("JoypadOverride", 0, 1), ("GameTimerExpiredFlag", 0, 1),
   ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1),
   ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("Square1SoundQueue", 0, 1), ("Square2SoundQueue", 0, 1), ("NoiseSoundQueue", 0, 1)]

/-- the bytes that the condition at the exit asks of a real run: the sound's pause, the sound effects, the screen buffer -/
def quietP : List (String × Nat × Nat) :=
  [("PauseSoundBuffer", 0, 1), ("PauseSoundQueue", 0, 1), ("Square1SoundBuffer", 0, 1), ("Square2SoundBuffer", 0, 1), ("NoiseSoundBuffer", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1)]

/-- **The bytes that the state at the entry knows**, besides the bytes of the exit. The values come from the reference entry. They are the bytes that no frame of the pipe's routine changes, and that the frames need:
the routine and the task, the objects' slots that stay empty, the sound's queues, the area, the scroll's other bytes. Found by a search, and checked on real entries. -/
def entryNames : List (String × Nat × Nat) :=
  [("Up_Down_Buttons", 0, 1), ("Left_Right_Buttons", 0, 1), ("GameEngineSubroutine", 0, 1), ("Enemy_Flag", 4, 3), ("Enemy_ID", 3, 4), ("Player_State", 0, 1), ("Enemy_State", 4, 2), ("Fireball_State", 0, 2), ("Block_State", 0, 4), ("Misc_State", 0, 9), ("Misc_Y_Position", 7, 1), ("EnemyData", 0, 1), ("EnemyDataHigh", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1), ("Square2SoundQueue", 0, 1), ("Square1SoundQueue", 1, 1), ("FlagpoleFNum_Y_Pos", 0, 1), ("FlagpoleFNum_YMFDummy", 0, 1), ("FlagpoleScore", 0, 1), ("FloateyNum_Control", 0, 7), ("FirebarSpinSpeed", 14, 2), ("VineFlagOffset", 0, 1), ("VineHeight", 0, 1), ("Block_RepFlag", 0, 2), ("SprDataOffset_Ctrl", 1, 1), ("MaximumRightSpeed", 18, 2), ("Cannon_Offset", 0, 1), ("Cannon_PageLoc", 0, 6), ("Cannon_X_Position", 0, 6), ("Cannon_Y_Position", 0, 5), ("Misc_Collision_Flag", 10, 3), ("EnemyFrenzyBuffer", 0, 1), ("SecondaryHardMode", 0, 1), ("EnemyFrenzyQueue", 0, 1), ("FireballCounter", 0, 1), ("DuplicateObj_Offset", 0, 1), ("WarpZoneControl", 0, 1), ("EnemyObjectPageLoc", 0, 1), ("EnemyObjectPageSel", 0, 1), ("ScreenRoutineTask", 0, 1), ("ScrollThirtyTwo", 1, 1), ("VerticalScroll", 0, 1), ("CloudTypeOverride", 0, 1), ("BackgroundColorCtrl", 0, 1), ("LoopCommand", 0, 1), ("AreaType", 0, 1), ("FetchNewGameTimerFlag", 0, 1), ("JoypadOverride", 0, 1), ("WorldSelectNumber", 2, 3), ("OperMode", 0, 2), ("OperMode_Task", 0, 1), ("DisableScreenFlag", 0, 1), ("StarInvincibleTimer", 0, 1), ("ScreenTimer", 0, 1), ("WorldEndTimer", 0, 1), ("DemoTimer", 0, 1)]

/-- the bytes that the state at the entry knows by a mask of bits: the objects' kinds and states as on a real entry, Mario's status below the fire flower, the pause bits other than the low bit and the top bit -/
def entryMasks : List (String × Nat × UInt8) :=
  [("Enemy_ID", 0, 249), ("Enemy_ID", 1, 249), ("Enemy_ID", 2, 249), ("Enemy_State", 0, 254), ("Enemy_State", 1, 254), ("Enemy_State", 2, 254), ("Enemy_State", 3, 254), ("Misc_Y_Position", 8, 156),
   ("Square1SoundQueue", 0, 239), ("SprDataOffset_Ctrl", 0, 254), ("PlayerStatus", 0, 254), ("GamePauseStatus", 0, 126)]

/-- the known bytes of the entry as RAM indices: the list, and the bytes of the exit -/
def entryKnown (nx : Names) : List Nat :=
  let masked := entryMasks.map fun p => adI nx p.1 + p.2.1
  ((bytesOf nx entryNames ++ bytesOf nx exitNames).eraseDups).filter fun i => !masked.contains i

/-- the masks as RAM indices -/
def entryBits (nx : Names) : List (Nat × UInt8) := entryMasks.map fun p => (adI nx p.1 + p.2.1, p.2.2)

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  let l := ((exitNames ++ quietP ++ songNames ++ entryNames).map (·.1)) ++ entryMasks.map (·.1) ++ ["PlayerStatus", "Player_X_Scroll", partName, "SprShuffleAmtOffset", "SprDataOffset", "Misc_SprDataOffset", "AreaData", "AreaDataHigh", "VRAM_Buffer2_Offset", "VRAM_Buffer2", "BlockBufferColumnPos", "CurrentPageLoc", "CurrentColumnPos", "TerrainControl", "BackloadingFlag", "AreaObjectPageLoc", "AreaDataOffset", "ForegroundScenery", "BackgroundScenery", "AreaType", "MetatileBuffer", "AreaObjectLength", "AreaObjOffsetBuffer", "AreaStyle", "AreaParserTaskNum", "ScrollThirtyTwo", "VRAM_Buffer_AddrCtrl", "VRAM_Buffer1", "VRAM_Buffer1_Offset", "EnemyDataOffset", "ObjectOffset", "MusicOffset_Square2", "MusicOffset_Noise", "Squ2_NoteLenCounter", "MusicOffset_Triangle"]
  SideChangeEnd.namesOf text ++ (l.eraseDups.filterMap fun n => (asmValue ls n).map (n, ·))

/-- the bytes of the condition at the exit -/
def exitKnown (nx : Names) : List Nat := bytesOf nx exitNames ++ bytesOf nx quietP

/-- the reference machine at the exit -/
abbrev refX (e : Machine) : Machine := run e (zeros timerF)

/-- what the check of the frames takes -/
structure Data where
  nx : Names
  /-- the rows of the song, and the rows of the screen buffer, for the state at the exit -/
  song : List (List (Nat × UInt8))
  xshape : List (List (Nat × UInt8))
  /-- where the song's frame joins, and its dots: the search only -/
  pl : UInt16
  dl : Nat
  dh : Nat
  /-- the bytes that the state at the entry knows, and the bytes it knows by a mask of bits -/
  known : List Nat
  bits : List (Nat × UInt8)
  /-- the places of the pipe's frames -/
  places : List Place
  /-- the jump engine -/
  jump : UInt16
  /-- the search only: the bytes that part candidates, the bytes that part states, and what is forgotten at places -/
  ckeys : List Nat
  keep : List Nat
  hints : List Hint

/-- the environment of the frames -/
abbrev envOf (d : Data) (e : Machine) : Env := rowsEnv d.nx d.nx e

/-- what the rows have in common -/
def ctxOf (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Ctx :=
  { E := envOf d e, sy, nm, eng := sy.EngVerticalPipe, tbl := PipeChangeBound.tableOf sy nm e timerF afterF, B := afterF, keep := [adI d.nx "VRAM_Buffer1_Offset"] }

/-- the number `left` of `Route` -/
abbrev leftP (sy : Syms) (nm : Names) (e : Machine) : Machine → Nat :=
  leftOf sy nm sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm e timerF afterF) afterF

/-- the start states of the rows, before the two cases of the flag -/
def baseOf (d : Data) (e : Machine) : List AS :=
  exitStarts (refX e) (exitKnown d.nx) (adI d.nx "GamePauseStatus")

/-- the first states when the sound's pause flag is 0: one state for each row of the song -/
def songStarts (d : Data) (e : Machine) : List AS :=
  (flagZero (adI d.nx "PauseModeFlag") (baseOf d e)).flatMap fun S => d.xshape.flatMap fun r => d.song.map fun q => refine q (refine r S)

/-- the rows of the two cases of the flag: if it is not 0 the sound routines do not run, and the song does not matter -/
def rowsA (c : Ctx) (d : Data) (e : Machine) : List Row := rowsAfter c (afterF - 2) (rowSong c d.pl (bytesOfSong d.nx) d.dl d.dh 32 (songStarts d e))
def rowsB (c : Ctx) (d : Data) (e : Machine) : List Row := rowsAfter c (afterF - 2) (rowSong c d.pl [] d.dl d.dh 1 ((flagNotZero (baseOf d e)).flatMap fun S => d.xshape.map fun r => refine r S))

/-- the bytes that the condition at the exit asks, with the reference's values -/
def quietQ (d : Data) (e : Machine) : List (Nat × UInt8) := (bytesOf d.nx quietP).map fun i => (i, (refX e).ram.get! i)

/-- the bytes known by a mask, from the reference machine -/
def maskOn (bits : List (Nat × UInt8)) (e : Machine) (S : AS) : AS :=
  bits.foldl (fun A b => A.setK b.1 ⟨e.ram.get! b.1, b.2⟩) S

/-- the machine has these bits of the reference machine -/
def BitsAt (bits : List (Nat × UInt8)) (e m : Machine) : Prop := ∀ b ∈ bits, b.1 < 2048 ∧ (⟨e.ram.get! b.1, b.2⟩ : TaintRun.AB).mem (m.ram.get! b.1)

/-- the reference machines at the entry -/
def refsP (d : Data) (e : Machine) : List (Machine × List Nat) := [(e, d.known)]

/-- the start states of the pipe's frames -/
def startsP (d : Data) (e : Machine) : List AS := (startsOf (refsP d e)).map (maskOn d.bits e)

/-- the two tables of the pipe's frames: the counter followed, and the counter at 1 -/
def cfgRp (d : Data) (e : Machine) : ZCfg := zcfgOf d.places d.jump (envOf d e) d.ckeys d.keep d.hints (startsP d e)
def cfgOp (d : Data) (e : Machine) : ZCfg :=
  zcfgOf d.places d.jump (envOf d e) d.ckeys (adI d.nx "GamePauseStatus" :: d.keep) d.hints ((startsP d e).map (toOne (envOf d e)))

/-- the whole check on the ROM -/
def endCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) (es : List Machine) : Bool :=
  let c := ctxOf sy nm d e
  let E := envOf d e
  let st := startsP d e
  let x := refX e
  exitStartsOK x (exitKnown d.nx) &&
    (baseOf d e).all (fun S => !S.dg && keyKnown c S && !inPipe c.sy c.eng (mOf S) && c.left (mOf S) == afterF) &&
    chainOK c (rowsA c d e) && chainOK c (rowsB c d e) &&
    startsOK (refsP d e) && decide (2 ≤ timerF) && d.bits.all (fun b => decide (b.1 < 2048)) &&
    leftCheck E sy nm sy.EngVerticalPipe (PipeChangeBound.tableOf sy nm e timerF afterF) afterF st x &&
    zcheck (cfgRp d e) (cfgOp d e) E st (baseOf d e) (quietQ d e) (exitBytes sy nm x) &&
    es.all (fun m => entryOK E (refsP d e) timerF m)

/-- **The condition on the state at the entry.** The frame has ended in the idle loop, the listed bytes are those of the reference, the timer is at least its first value, and some bytes have the reference's bits. All other bytes are free. -/
abbrev Entry (d : Data) (e : Machine) (m : Machine) : Prop :=
  SideChangeBound.EntryCond (envOf d e) (refsP d e) timerF m ∧ BitsAt d.bits e m

/-- **The condition on the state at the exit.** The frame has ended in the idle loop, the listed bytes are those of the reference, the game is not paused, and the song's bytes are a row of the table. All other bytes are free. -/
abbrev Exit (d : Data) (e : Machine) (m : Machine) : Prop :=
  ExitCond (envOf d e) (refX e) (exitKnown d.nx) (adI d.nx "GamePauseStatus") m ∧ SongAt d.song m ∧ SongAt d.xshape m

/-- the state during the pipe -/
abbrev During (d : Data) (e : Machine) : Machine → Prop := InvAt (envOf d e) (startsP d e)

/-- a machine is in the rows of one of the two cases -/
def InRows (sy : Syms) (nm : Names) (d : Data) (e : Machine) (m : Machine) : Prop :=
  InvL (ctxOf sy nm d e) (rowsA (ctxOf sy nm d e) d e) m ∨ InvL (ctxOf sy nm d e) (rowsB (ctxOf sy nm d e) d e) m

/-- the bytes that say where the change is, in the reference at the exit -/
abbrev exitQ (sy : Syms) (nm : Names) (e : Machine) : List (Nat × UInt8) := exitBytes sy nm (refX e)

/-- **The statement.** -/
structure EndStatement (sy : Syms) (nm : Names) (d : Data) (e : Machine) (es : List Machine) : Prop where
  /-- the entries that were run meet the part of the condition on the known bytes -/
  entries : ∀ m ∈ es, SideChangeBound.EntryCond (envOf d e) (refsP d e) timerF m
  /-- an entry is in the state during the pipe -/
  during : ∀ M, Entry d e M → During d e M
  /-- `left` at an entry -/
  atEntry : ∀ M, Entry d e M → timerF + afterF ≤ leftP sy nm e M
  /-- a state during the pipe has the pipe's routine -/
  inRoutine : ∀ m, During d e m → inPipe sy sy.EngVerticalPipe m = true
  /-- **one frame of the pipe**, for any input, when every instruction of the frame meets the condition at the places. It takes at most one off `left`. It stays in the state during the pipe, or it leaves the routine with the exit's bytes, and then with the bytes `quietQ` and a row of the song the machine is in the rows. -/
  step : ∀ m, During d e m → ∀ i, (∀ j, PlaceOK d.places (PipeEntryRule.trace m i j)) →
    leftP sy nm e m ≤ leftP sy nm e (frame m i) + 1 ∧
      (During d e (frame m i) ∨ (ExitAt (exitQ sy nm e) (frame m i) ∧ (Quiet (quietQ d e) (frame m i) → SongAt d.song (frame m i) → SongAt d.xshape (frame m i) → InRows sy nm d e (frame m i))))
  /-- a state with the condition at the exit is in the rows -/
  atExit : ∀ m, Exit d e m → InRows sy nm d e m
  /-- `left` at the exit -/
  leftExit : ∀ m, Exit d e m → leftP sy nm e m = afterF
  /-- a frame in the rows: `left` is 0 already, or the machine stays in the rows and `left` falls by at most one -/
  rows : ∀ m, InRows sy nm d e m → ∀ i, (coreFrame sy sy.EngVerticalPipe m = true → noStart i = true) →
    leftP sy nm e m = 0 ∨ (InRows sy nm d e (frame m i) ∧ leftP sy nm e m ≤ leftP sy nm e (frame m i) + 1)
  /-- control only where `left` is 0 -/
  atControl : ∀ m, controllable sy m = true → leftP sy nm e m = 0

/-- the first row of each case holds the states it is built from -/
theorem in_rows {sy : Syms} {nm : Names} {d : Data} {e : Machine} {m : Machine} (hq : SongAt d.song m) (hr : SongAt d.xshape m)
    (h : ∃ D ∈ baseOf d e, Sim (envOf d e) (m.frame, 2) D m) : InRows sy nm d e m := by
  obtain ⟨D, hD, hs⟩ := h
  obtain ⟨r, hr1, hr2⟩ := hr
  by_cases h0 : m.ram.get! (adI d.nx "PauseModeFlag") = 0
  · left
    obtain ⟨q, hq1, hq2⟩ := hq
    refine Or.inl ⟨refine q (refine r (D.setK (adI d.nx "PauseModeFlag") (TaintRun.AB.known 0))), ?_, sim_refines hq2 (sim_refines hr2 (sim_refine hs (by rw [h0]; exact TaintRun.mem_known_self _)))⟩
    exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨D, hD, rfl⟩, List.mem_flatMap.2 ⟨r, hr1, List.mem_map.2 ⟨q, hq1, rfl⟩⟩⟩
  · right
    have hdg : (envOf d e).D.any (fun i => m.ram.get! i != 0) = true := by
      show ([adI d.nx "PauseModeFlag"].any fun i => m.ram.get! i != 0) = true
      simp [h0]
    have hs1 : Sim (envOf d e) (m.frame, 2) { D with dg := true } m := { hs with dg := fun _ => hdg }
    refine Or.inl ⟨refine r { D with dg := true }, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨D, hD, rfl⟩, List.mem_map.2 ⟨r, hr1, rfl⟩⟩, sim_refines hr2 hs1⟩

section
variable {E : Env} {F : Nat × UInt8}

/-- a mask of bits goes into the state -/
theorem sim_mask {e m : Machine} : ∀ {bits : List (Nat × UInt8)} {A : AS}, BitsAt bits e m → Sim E F A m → Sim E F (maskOn bits e A) m := by
  intro bits
  induction bits with
  | nil => intro A _ hs; exact hs
  | cons b t ih =>
    intro A hb hs
    have h1 := hb b List.mem_cons_self
    exact ih (fun p hp => hb p (List.mem_cons_of_mem _ hp)) (sim_refine hs h1.2)

end

theorem endStatement_of_check {sy : Syms} {nm : Names} {d : Data} {e : Machine} {es : List Machine} (h : endCheck sy nm d e es = true) : EndStatement sy nm d e es := by
  simp only [endCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hE : (ctxOf sy nm d e).E.pad = TaintRun.AB.top := rfl
  have hEp : (envOf d e).pad = TaintRun.AB.top := rfl
  have hL := leftOK_of_check h8
  have hZ : ZOK (cfgRp d e) (cfgOp d e) (envOf d e) (startsP d e) (baseOf d e) (quietQ d e) (exitBytes sy nm (refX e)) := by
    simp only [zcheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h9
    obtain ⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩ := h9
    refine ⟨z1, rfl, rfl, rfl, rfl, rfl, fun S hS => ?_, z3, z4, z5, z6⟩
    have := z2 S hS
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hdur : ∀ M, Entry d e M → During d e M := by
    intro M hM
    obtain ⟨S, hS, hc⟩ := inv_of_entry h5 hEp h6 hM.1
    refine ⟨maskOn d.bits e S, List.mem_map.2 ⟨S, hS, rfl⟩, ?_⟩
    rcases hc with ⟨c1, c2⟩ | ⟨c1, _⟩
    · exact Or.inl ⟨c1, sim_mask hM.2 c2⟩
    · exfalso
      have a1 := hM.1.timer
      have a2 : (tm (envOf d e) M) = M.ram.get! (envOf d e).rkI := rfl
      rw [a2] at c1
      rw [c1] at a1
      exact absurd a1 (by decide)
  have hctl : ∀ m, controllable sy m = true → leftP sy nm e m = 0 := fun m hc => PipeChangeBound.left_zero_of_ctl hL.keys hc
  refine ⟨fun m hm => entryCond_of_ok (h10 m hm), hdur, ?_, fun m hm => inPipe_of_inv hL hm, ?_, fun m hm => in_rows hm.2.1 hm.2.2 (exit_cover h1 rfl hm.1), ?_, ?_, hctl⟩
  · intro M hM
    have a1 : leftP sy nm e M = (tm (envOf d e) M).toNat + afterF := left_of_inv hL (hdur M hM)
    rw [a1]
    have := hM.1.timer
    show timerF + afterF ≤ ((envOf d e).rkI |> M.ram.get!).toNat + afterF
    omega
  · intro m hm i hP
    rcases z_step hZ hEp hm i hP with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
    · refine ⟨?_, Or.inl g1⟩
      have a1 : leftP sy nm e m = (tm (envOf d e) m).toNat + afterF := left_of_inv hL hm
      have a2 : leftP sy nm e (frame m i) = (tm (envOf d e) (frame m i)).toNat + afterF := left_of_inv hL g1
      rw [a1, a2]
      omega
    · refine ⟨?_, Or.inr ⟨g2, fun hq hs hr => ?_⟩⟩
      · have a1 : leftP sy nm e m = (tm (envOf d e) m).toNat + afterF := left_of_inv hL hm
        have a2 : leftP sy nm e (frame m i) = afterF := left_of_exit hL g2
        rw [a1, a2, g1]
        have : (1 : UInt8).toNat = 1 := rfl
        omega
      · obtain ⟨D, hD, hs2⟩ := g3 hq
        have : Sim (envOf d e) ((frame m i).frame, 2) D (frame m i) := hs2
        exact in_rows hs hr ⟨D, hD, this⟩
  · intro m hm
    obtain ⟨D, hD1, hs⟩ := exit_cover h1 rfl hm.1
    obtain ⟨⟨⟨_, a2⟩, a3⟩, a4⟩ := h2 D hD1
    have : (ctxOf sy nm d e).left m = afterF := by
      rw [left_of_known hs a2 a3, a4]
    exact this
  · intro m hm i hi
    rcases hm with hm | hm
    · rcases chain_step hE _ h3 hm hi with g | ⟨g1, g2⟩
      · exact Or.inl g
      · exact Or.inr ⟨Or.inl g1, g2⟩
    · rcases chain_step hE _ h4 hm hi with g | ⟨g1, g2⟩
      · exact Or.inl g
      · exact Or.inr ⟨Or.inr g1, g2⟩

/-! ## A run -/

/-- **The change of a run.** The condition on the state at the entry, the condition at the places on the frames of the pipe's routine, the condition on the song and the bytes `quietQ` at the exit, no Start on the frames of the game core after the pipe. -/
structure PipeRun (sy : Syms) (nm : Names) (d : Data) (e : Machine) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  lag : Nat → Prop
  dec : DecidablePred lag
  cnt : Nat → Nat
  hcnt : ∀ n, cnt (n + 1) = cnt n + (@ite _ (lag n) (dec n) 0 1)
  a : Nat
  b : Nat
  order : a ≤ b
  /-- the condition on the state at the entry -/
  entry : Entry d e (seq a)
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame takes nothing off `left` -/
  lagKeeps : ∀ n, a ≤ n → n < b → lag n → leftP sy nm e (seq n) ≤ leftP sy nm e (seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places : ∀ n, a ≤ n → n < b → inPipe sy sy.EngVerticalPipe (seq n) = true → ∀ j, PlaceOK d.places (PipeEntryRule.trace (seq n) (inp n) j)
  /-- at the exit, the sound's bytes, the screen buffer and the song are as the condition says -/
  quiet : ∀ n, a ≤ n → n ≤ b → ExitAt (exitQ sy nm e) (seq n) → Quiet (quietQ d e) (seq n) ∧ SongAt d.song (seq n) ∧ SongAt d.xshape (seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart : ∀ n, a ≤ n → n < b → coreFrame sy sy.EngVerticalPipe (seq n) = true → SideChangeEnd.noStart (inp n) = true

section
variable {sy : Syms} {nm : Names} {d : Data} {e : Machine} {es : List Machine}

theorem cnt_mono (R : PipeRun sy nm d e) (n : Nat) : R.cnt n ≤ R.cnt (n + 1) := by
  rw [R.hcnt n]
  split <;> omega

/-- **The bound on the change.** This is `change₁` of `Route`. -/
theorem PipeRun.bound (T : EndStatement sy nm d e es) (R : PipeRun sy nm d e) : R.cnt R.a + (timerF + afterF) ≤ R.cnt R.b := by
  have key : ∀ k, R.a + k ≤ R.b → R.cnt R.a + (timerF + afterF) ≤ R.cnt (R.a + k) ∨
      ((During d e (R.seq (R.a + k)) ∨ InRows sy nm d e (R.seq (R.a + k))) ∧
        R.cnt R.a + (timerF + afterF) ≤ R.cnt (R.a + k) + leftP sy nm e (R.seq (R.a + k))) := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      refine ⟨Or.inl (T.during _ R.entry), ?_⟩
      have := T.atEntry _ R.entry
      simp only [Nat.add_zero]
      omega
    | succ k ih =>
      intro hk2
      have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
      rw [e1]
      have hn := R.next (R.a + k)
      rcases ih (by omega) with h | ⟨h1, h2⟩
      · left
        have := cnt_mono R (R.a + k)
        omega
      · have hc := R.hcnt (R.a + k)
        have hgap : R.a ≤ R.a + k := by omega
        have hlt : R.a + k < R.b := by omega
        rcases h1 with h1 | h1
        · right
          have hP := R.places _ hgap hlt (T.inRoutine _ h1)
          obtain ⟨g1, g2⟩ := T.step _ h1 (R.inp (R.a + k)) hP
          rw [hn]
          constructor
          · rcases g2 with g2 | ⟨g2, g3⟩
            · exact Or.inl g2
            · rw [← hn] at g2 g3 ⊢
              obtain ⟨q1, q2, q3⟩ := R.quiet _ (by omega) (by omega) g2
              exact Or.inr (g3 q1 q2 q3)
          · by_cases hl : R.lag (R.a + k)
            · rw [@if_pos _ (R.dec _) hl] at hc
              have hk3 := R.lagKeeps _ hgap hlt hl
              rw [hn] at hk3
              omega
            · rw [@if_neg _ (R.dec _) hl] at hc
              omega
        · have hi := R.noStart _ hgap hlt
          rcases T.rows _ h1 (R.inp (R.a + k)) hi with g | ⟨g1, g2⟩
          · left
            have := cnt_mono R (R.a + k)
            omega
          · right
            rw [hn]
            refine ⟨Or.inr g1, ?_⟩
            by_cases hl : R.lag (R.a + k)
            · rw [@if_pos _ (R.dec _) hl] at hc
              have hk3 := R.lagKeeps _ hgap hlt hl
              rw [hn] at hk3
              omega
            · rw [@if_neg _ (R.dec _) hl] at hc
              omega
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  rcases key (R.b - R.a) (by omega) with h | ⟨_, h⟩
  · rw [e2] at h
    exact h
  · have h0 := T.atControl _ R.atCtl
    rw [e2, h0] at h
    omega

/-- **No control, from a state at the exit.** From a state with the condition at the exit, with no Start on the frames of the game core, there is no control on the next `afterF - 1` frames. -/
theorem no_control_exit (T : EndStatement sy nm d e es) {seq : Nat → Machine} {inp : Nat → UInt8}
    (hn : ∀ n, seq (n + 1) = frame (seq n) (inp n)) (hx : Exit d e (seq 0)) (hi : ∀ n, coreFrame sy sy.EngVerticalPipe (seq n) = true → noStart (inp n) = true) :
    ∀ j, j < afterF → controllable sy (seq j) = false := by
  have key : ∀ k, afterF ≤ k + leftP sy nm e (seq k) ∧ InRows sy nm d e (seq k) ∨ afterF ≤ k := by
    intro k
    induction k with
    | zero => exact Or.inl ⟨by rw [T.leftExit _ hx]; omega, T.atExit _ hx⟩
    | succ k ih =>
      rcases ih with ⟨h1, h2⟩ | h1
      · rw [hn k]
        rcases T.rows _ h2 (inp k) (hi k) with g | ⟨g1, g2⟩
        · right
          omega
        · left
          exact ⟨by omega, g1⟩
      · right
        omega
  intro j hj
  cases hc : controllable sy (seq j) with
  | false => rfl
  | true =>
    exfalso
    have hz := T.atControl _ hc
    rcases key j with ⟨h1, _⟩ | h1
    · omega
    · omega

end

/-! ## The data of the check, from tables -/

/-- rows as text: a row is entries of five hex digits, three for the byte and two for the value; rows are parted by `|` -/
def encodeRows (rows : List (List (Nat × UInt8))) : String :=
  let hx := fun (n w : Nat) => String.ofList ((List.range w).reverse.map fun k => "0123456789ABCDEF".toList[(n / 16 ^ k) % 16]!)
  "|".intercalate (rows.map fun r => String.join (r.map fun p => hx p.1 3 ++ hx p.2.toNat 2))

def decodeRows (s : String) : List (List (Nat × UInt8)) :=
  let hv := fun (c : Char) => if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'A'.toNat + 10
  (s.splitOn "|").map fun r =>
    let cs := r.toList.toArray
    (List.range (cs.size / 5)).map fun k =>
      let d := fun j => hv cs[5 * k + j]!
      (((d 0 * 16 + d 1) * 16 + d 2), ((d 3 * 16 + d 4).toUInt8))

/-- the first instruction from `a` on, within `n` bytes, with this opcode, and the place after it -/
def afterOp (m : Machine) (a : UInt16) (op : UInt8) (len : Nat) : UInt16 := PipeEntryRule.findOp m a op 64 + len.toUInt16

/-- the bound on the dot at the places of the engine and the parser: no frame of the pipe runs so long -/
def dotBound : Nat := 50000

/-- **The data of the check.** The places, from the symbols: the frame's start (the screen buffer's rows), the song, the drawing of the objects and of Mario (the sprites' offsets), the parser, the colour rotation,
the places with a bound on the dot, and three places that the frames of the pipe do not reach: the write on a block being hit under an object, and the two steps that take the next object of the area. -/
def assemble (sy : Syms) (nx : Names) (m0 : Machine) (song xshape shapes shuf pars : List (List (Nat × UInt8))) (dl dh : Nat) : Data :=
  let known := entryKnown nx
  let bits := entryBits nx
  let o1 := nb nx "VRAM_Buffer1_Offset"
  let shapeB := (shapes.flatMap fun r => r.map (·.1)).eraseDups
  let songB := bytesOfSong nx
  let shufB := shuffleBytes nx
  let parB := [nb nx "AreaParserTaskNum", nb nx "ScrollThirtyTwo", nb nx "VRAM_Buffer_AddrCtrl"] ++ parserBytes nx
  let plain := fun (pc : UInt16) => ({ pc, rows := [[]], tmax := dotBound } : Place)
  let never := fun (pc : UInt16) => ({ pc, rows := [], tmax := 0 } : Place)
  let big := dotsPerFrame
  let places : List Place := [
    { pc := sy.NonMaskableInterrupt, rows := shapes, tmax := big },
    { pc := sy.MusicHandler, rows := song, tmax := big },
    { pc := sy.EnemyGfxHandler, rows := shuf, tmax := big },
    { pc := sy.PlayerGfxHandler, rows := shuf, tmax := big },
    { pc := sy.UpdScrollVar, rows := pars, tmax := dotBound },
    { pc := sy.ColorRotation, rows := (List.range 256).map fun v => [(o1, v.toUInt8)], tmax := dotBound },
    plain sy.ProcELoop, plain sy.FlagpoleRoutine, plain sy.BlockObjMT_Updater,
    never (afterOp m0 sy.HandleEToBGCollision 0x91 0),
    never (afterOp m0 sy.PositionEnemyObj 0xB0 2),
    never (afterOp m0 sy.CheckRightExtBounds 0x90 2) ]
  let kb := known ++ bits.map (·.1)
  let fgt := fun (l : List Nat) => l.filter fun i => !kb.contains i
  let hints : List Hint := ([
    { pc := sy.NonMaskableInterrupt, forget := shapeB, dead := false },
    { pc := sy.SoundEngine, forget := shapeB ++ [0, 1], dead := true },
    { pc := sy.MusicHandler, forget := songB, dead := true },
    { pc := sy.HandleSquare1Music, forget := [], dead := true },
    { pc := sy.HandleTriangleMusic, forget := [], dead := true },
    { pc := sy.HandleNoiseMusic, forget := [], dead := true },
    { pc := sy.SkipSoundSubroutines, forget := songB, dead := true },
    { pc := sy.ReadPortBits, forget := songB, dead := false, deadY := true },
    { pc := sy.GameEngine, forget := shufB, dead := true },
    { pc := sy.EnemyGfxHandler, forget := shufB, dead := false },
    { pc := sy.GetEnemyBoundBox, forget := shufB, dead := false },
    { pc := sy.PlayerGfxHandler, forget := shufB, dead := false },
    { pc := sy.BlockObjMT_Updater, forget := shufB, dead := false },
    { pc := sy.FlagpoleRoutine, forget := [], dead := true },
    { pc := sy.ColorRotation, forget := [o1], dead := true },
    { pc := sy.UpdScrollVar, forget := shufB ++ [o1] ++ parB ++ shapeB, dead := true },
    { pc := sy.ExitEng, forget := parB, dead := true } ] : List Hint).map fun h => { h with forget := fgt h.forget }
  let keep := [nb nx "SprShuffleAmtOffset", o1, nb nx "EnemyDataOffset", nb nx "ObjectOffset"] ++ parB ++ songB ++ shapeB
  let ckeys := [nb nx "MusicOffset_Square2", nb nx "MusicOffset_Noise", nb nx "Squ2_NoteLenCounter", nb nx "MusicOffset_Triangle"]
  { nx, song, xshape, pl := sy.ReadPortBits, dl, dh, known, bits, places, jump := sy.JumpEngine, ckeys, keep, hints }

/-- the frames the tables come from: the reference entry with no input, the same with `Player_X_Scroll` set to 3 and the timer set to 230 for 225 frames, and the real entries -/
def refFramesOf (sy : Syms) (nx : Names) (m0 : Machine) : List Machine :=
  let e := PipeTransition.entry m0
  let es := (List.range 47).map fun j => run e (zeros j)
  let s0 := poke (poke e (nx.ad "Player_X_Scroll") 3) (nx.ad "ChangeAreaTimer") 230
  let ss := (List.range 225).map fun j => run s0 (zeros j)
  let rs := (PipeTransitionAll.realEntries sy m0 25 13).flatMap fun p => (List.range 47).map fun j => run p.2 (zeros j)
  es ++ ss ++ rs

/-- the machines before the frames of the reference's way to the pipe, with each frame's input -/
def pathOf (m0 : Machine) : List (Machine × UInt8) :=
  (PipeTransition.witness.foldl (fun (acc : List (Machine × UInt8) × Machine) i => ((acc.2, i) :: acc.1, PipeTransition.frame acc.2 i)) ([], m0)).1

/-- the column of a parser's row, page and column as one number -/
def colOf (nx : Names) (r : List (Nat × UInt8)) : Option Nat :=
  (r.find? (·.1 == nb nx "CurrentPageLoc")).bind fun p => (r.find? (·.1 == nb nx "CurrentColumnPos")).map fun c => p.2.toNat * 16 + c.2.toNat

/-- the rows of the places, from frames: what the screen buffer holds at a frame's start, the sprites' offsets when Mario is drawn, the parser's bytes at its place -/
def tablesOf (sy : Syms) (nx : Names) (m0 : Machine) : List (List (Nat × UInt8)) × List (List (Nat × UInt8)) × List (List (Nat × UInt8)) × List (List (Nat × UInt8)) :=
  let frames := refFramesOf sy nx m0
  let pk := parserKOf sy m0
  let shapes0 := (frames.map fun m => shapeRow nx pk m).eraseDups
  let b1 := nb nx "VRAM_Buffer1"
  let ac := nb nx "VRAM_Buffer_AddrCtrl"
  -- the first bytes of the records seen in both buffers, each with every short length
  let firsts := (shapes0.flatMap fun r => (r.filter fun p => p.1 ≥ b1 && p.1 != ac && p.2 != 0 && r.any (·.1 == p.1 + 2)).map (·.2)).eraseDups
  let recs := firsts.flatMap fun f => (List.range 8).map fun l => (f, (l + 1).toUInt8)
  let shapes := (shapes0 ++ shapesOf nx recs 2).eraseDups
  let xshape := shapes0.filter fun r => r.length ≤ 4 && r.contains (ac, 0)
  let shuf := ((frames.filterMap fun m => firstAtPlace sy.PlayerGfxHandler m 0).map fun m => (shuffleBytes nx).map fun i => (i, m.ram.get! i)).eraseDups
  let pars0 := (frames.filterMap fun m => firstAtPlace sy.UpdScrollVar m 0).map (parserRow nx pk)
  -- the starts of the columns near those of the reference, on the reference's way to the pipe
  let cols := pars0.filterMap (colOf nx)
  let lo := cols.foldl Nat.min 4096 - 6
  let hi := cols.foldl Nat.max 0 + 6
  let tk := nb nx "AreaParserTaskNum"
  let starts := ((pathOf m0).filterMap fun p => firstAtPlace sy.UpdScrollVar p.1 p.2).map (parserRow nx pk) |>.filter fun r =>
    r.contains (tk, 0) && r.length > 3 && match colOf nx r with
      | some k => decide (lo ≤ k) && decide (k ≤ hi)
      | none => false
  let pars := ((pars0 ++ starts).flatMap (parserStarts nx pk) ++ parserWaitRows nx pk).eraseDups
  (shapes, xshape, shuf, pars)

/-- whether every instruction of the frame of `m` with the input `i` meets the condition at the places: for a program -/
def placesOK (P : List Place) (m : Machine) (i : UInt8) : Bool := Id.run do
  let mut t : Machine := { m with pad := smbToPad i }
  for _ in [0:40000] do
    if t.frame != m.frame || t.halted then return true
    match P.find? (fun p => p.pc == t.pc) with
    | some p => if !(decide (t.fdot ≤ p.tmax) && p.rows.any fun q => q.all fun b => t.ram.get! b.1 == b.2) then return false
    | none => pure ()
    t := (go step t).2
  return true

/-- `Entry` as a check, for a program -/
def entryOKp (d : Data) (e m : Machine) : Bool :=
  entryOK (envOf d e) (refsP d e) timerF m && d.bits.all fun b => (m.ram.get! b.1 &&& b.2) == (e.ram.get! b.1 &&& b.2)

/-- the dots at which the song's rows come to the place where they join, for the search -/
def dotsOf (d : Data) (e : Machine) : Nat × Nat :=
  let E := envOf d e
  let ops := (aRows E).toArray
  let st := (flagZero (adI d.nx "PauseModeFlag") (baseOf d e)).flatMap fun S => d.xshape.flatMap fun r => d.song.map fun q => refine q (refine r S)
  let ds := st.flatMap fun S => (toPlace E ops d.pl S).map fun B => (B.lo, B.hi)
  (ds.foldl (fun a p => Nat.min a p.1) dotsPerFrame, ds.foldl (fun a p => Nat.max a p.2) 0)

end Smbrta.PipeChangeEnd
