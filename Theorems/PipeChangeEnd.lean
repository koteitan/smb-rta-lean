import Theorems.SideChangeEnd
import Theorems.PipeEntryRule
import Theorems.SoundRows
import Theorems.SoundWalk

/-!
# The change into the room, from conditions at the entry, at places of the pipe's frames, and at the exit

`PipeChangeBound` proves the change into the room from a hypothesis on every frame: `left` falls by at most one. Here that hypothesis is proved on every frame of the change. The 48 frames of the pipe's timer come from one
condition on the state at the entry (`Entry`) and conditions on the machine at some places of each of these frames (`PlaceOK`). The 43 frames after the timer come from conditions at the exit: four bytes of the sound
(`Quiet`), the song's bytes (`SongAt`) and the screen buffer, and no Start on the frames of the game core. The frame after the pipe clears RAM, and the frame ends inside that loop, as in the side pipe, and `SideChangeEnd`
has what follows such a frame. A frame of the pipe that ends paused takes nothing off `left` (`EndStatement.paused`), and no machine in the rows is paused (`EndStatement.rowsGo`): so a `lag` frame that ends paused
keeps `left`. Rows of the time (`timeRowsO`) know that the game timer is not 000, and their last row has control only: so if the time is not up at the exit (`TimeOK`) and `b` is the first
control, `left` is not 0 before control (`PipeRun.first`) and the machine at control is in these rows (`PipeRun.inRowsT`). The rows with the sound's bytes in tables
(`rowsKc`, by the method of `SoundRows`) take a weaker condition at the exit: the pause sound silent or the unpause sound playing (`QuietP`), and the game timer not 000
(`TimerOK`). Their rows where `left` is 0, with their tables, are the rows `timeRows` that the room's checks read (`PipeRunK`). The walk of the pipe's frames with the pause's
class (`pipeCheckV`) has the game timer's digits as its bytes `D`: no path of the pipe's frames stores to them, so `PipeRunK` asks `TimerOK` at the entry, not at the exit.
There is no game data in this file. Pages: `1-1/b-3-2-PipeChangeEnd.md`, `1-1/b-3-3-LagPaused.md`, `1-1/b-3-7-1-SoundRows.md`, `1-1/b-3-7-2-PipePause.md`,
`1-1/b-3-9-1-PipeTime.md`.
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

/-- the states after the frame's end, as `afterEnds`, with `dg` from a known bit 1 of a byte of `D` (`normD`); states with `dg` and states without it are not put together -/
def afterEndsD (c : Ctx) (ends : Array AS) : List AS :=
  let R := nextStatesD c.E false ends.toList
  let m : Std.HashMap Nat AS := R.foldl (fun (h : Std.HashMap Nat AS) A =>
    let k := ykey c.E c.keep A * 2 + (if A.dg then 1 else 0)
    match h[k]? with
    | some B => h.insert k (B.join A)
    | none => h.insert k A) {}
  m.values

/-- `rowY`, with `afterEndsD` -/
def rowYD (c : Ctx) (R : List AS) : Row × List AS :=
  let X := ysearch c.E (aRows c.E).toArray c.keep R
  let I := indexOf c.E c.keep X.out
  ({ core := false, R, v := leftHead c R, t := X.out, idx := I.1, cut := I.2 }, afterEndsD c X.ends)

/-- `rowSong`, with `afterEndsD` -/
def rowSongD (c : Ctx) (pl : UInt16) (B : List Nat) (dl dh n : Nat) (R : List AS) : Row × List AS :=
  let ops := (aRows c.E).toArray
  let widen1 := fun (A : AS) => (B.foldl (fun (S : AS) i => S.setK i TaintRun.AB.top) { A with lo := Nat.min A.lo dl, hi := Nat.max A.hi dh })
  let J := joinByKey c.E c.keep ((everyNth n R).flatMap (toPlace c.E ops pl)) |>.map widen1
  let X := ysearch c.E ops c.keep J
  let t := J.toArray ++ X.out
  let I := indexOf c.E c.keep t
  ({ core := false, R, v := leftHead c R, t, idx := I.1, cut := I.2 }, afterEndsD c X.ends)

/-- `rowsAfter`, with `dg` kept: the rows of `SideChangeEnd.rowsFromD` -/
def rowsAfterD (c : Ctx) (n : Nat) (r0 : Row × List AS) : List Row :=
  let r1 := rowYD c r0.2
  r0.1 :: r1.1 :: rowsFromD c n r1.2

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

/-- the key of the search: the stack pointer and the program counter come first, so that deep calls end first. The bits `kb` of some bytes are in the key too: the pieces of a read by
these bits then stay apart, and so does what they decide. -/
def zskey (E : Env) (jump : UInt16) (keep : List Nat) (kb : List (Nat × UInt8)) (A : AS) : Nat :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let useA := op == 0x29 || op == 0xD0 || op == 0xF0 || (jump ≤ A.pc && A.pc < jump + 4)
  let num := fun (b : TaintRun.AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := (A.k * 256 + A.s.toNat) * 65536 + A.pc.toNat
  let n := n * 32 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0) + (if A.lo == 0 then 16 else 0)
  let n := n * 65536 + (if useA then num A.a else 0)
  let gb := kb.foldl (fun h p => let b := A.getK p.1; h * 65536 + (b.k &&& p.2).toNat * 256 + (b.v &&& b.k &&& p.2).toNat) 0
  (n * 4294967296 + (zhash keep A).toNat % 4294967296) * 65536 ^ kb.length + gb

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
  /-- the bits of bytes in the key -/
  kb : List (Nat × UInt8) := []
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
  (C.idx.getD (zskey C.E C.jump C.keep C.kb (hintNorm C.hints B)) []).any fun i =>
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

def zroute (E : Env) (jump : UInt16) (keep : List Nat) (kb : List (Nat × UInt8)) (H : List Hint) (X : ZS) (B0 : AS) : ZS :=
  let B := hintNorm H B0
  let K := zskey E jump keep kb B
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
partial def zloop (P : List Place) (jump : UInt16) (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (kb : List (Nat × UInt8)) (H : List Hint) (limit : Nat) (X0 : ZS) : ZS := Id.run do
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
        else X := zroute E jump keep kb H X b
  return X

/-- the configuration from the table found -/
def zcfgOf (P : List Place) (jump : UInt16) (E : Env) (ckeys keep : List Nat) (kb : List (Nat × UInt8)) (H : List Hint) (starts : List AS) : ZCfg :=
  let ops := (aRows E).toArray
  let X := zloop P jump E ops keep kb H 6000000 (starts.foldl (zroute E jump keep kb H) {})
  let I := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := X.outK.getD acc.2.2 0
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops, places := P, jump, ckeys, keep, kb, hints := H, t := X.out, idx := I.1, cut := I.2.1 }

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

/-- the state knows that the low bit of the byte `g` is 0: the game is not paused -/
def notPausedK (g : Nat) (B : AS) : Bool := decide (g < 2048) && (B.getK g).k &&& 1 == 1 && (B.getK g).v &&& 1 == 0

/-- a machine of such a state is not paused -/
theorem not_paused_of {E : Env} {F : Nat × UInt8} {g : Nat} {B : AS} {m : Machine} (hs : Sim E F B m) (h : notPausedK g B = true) : m.ram.get! g &&& 1 ≠ 1 := by
  simp only [notPausedK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hg, hk⟩, hv⟩ := h
  have e := TaintRun.bit_eq (hs.ram g hg) hk
  rw [e, hv]
  decide

/-- the state knows that bits 0 to 6 of the byte `g` are 0 -/
def low7K (g : Nat) (B : AS) : Bool := decide (g < 2048) && (B.getK g).k &&& 0x7F == 0x7F && (B.getK g).v &&& 0x7F == 0

/-- a machine of such a state has bits 0 to 6 of the byte `g` clear -/
theorem low7_of {E : Env} {F : Nat × UInt8} {g : Nat} {B : AS} {m : Machine} (hs : Sim E F B m) (h : low7K g B = true) : m.ram.get! g &&& 0x7F = 0 := by
  simp only [low7K, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hg, hk⟩, hv⟩ := h
  rw [TaintRun.bit_eq (hs.ram g hg) hk, hv]

/-- at the frame's end, with the counter followed: a start state; if the counter has fallen in the frame, the state knows that the game is not paused -/
def finRkP (g : Nat) (starts : List AS) (B : AS) : Bool := finRk starts B && (!B.spent || notPausedK g B)

/-- at the frame's end, with the counter at 1 before it: as `finX`; at the exit the state knows that the game is not paused -/
def finXP (g : Nat) (ones base : List AS) (qs xb : List (Nat × UInt8)) (B : AS) : Bool :=
  finX ones base qs xb B && (ones.any (fun S => ({ B with k := 0 } : AS).le S) || notPausedK g B)

/-- what the check of the pipe's frames says. `g` is the pause byte. -/
structure ZOK (Cr Co : ZCfg) (E : Env) (g : Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Prop where
  ti : E.rkI < 2048
  er : Cr.E = E
  eo : Co.E = E
  or : Cr.ops = (aRows E).toArray
  oo : Co.ops = (aRows E).toArray
  pr : Cr.places = Co.places
  rkStarts : ∀ S ∈ starts, S.k = 0 ∧ S.rk = true ∧ S.spent = false
  tr : Cr.t.all (zwalk Cr (finRkP g starts) TaintRun.walkFuel) = true
  sr : ∀ S ∈ starts, zwalk Cr (finRkP g starts) TaintRun.walkFuel S = true
  to : Co.t.all (zwalk Co (finXP g (starts.map (toOne E)) base qs xb) TaintRun.walkFuel) = true
  so : ∀ S ∈ starts, zwalk Co (finXP g (starts.map (toOne E)) base qs xb) TaintRun.walkFuel (toOne E S) = true

def zcheck (Cr Co : ZCfg) (E : Env) (g : Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Bool :=
  let ones := starts.map (toOne E)
  let fr := finRkP g starts
  let fo := finXP g ones base qs xb
  decide (E.rkI < 2048) && starts.all (fun S => S.k == 0 && S.rk && !S.spent) &&
    Cr.t.all (zwalk Cr fr TaintRun.walkFuel) && starts.all (zwalk Cr fr TaintRun.walkFuel) &&
    Co.t.all (zwalk Co fo TaintRun.walkFuel) && starts.all (fun S => zwalk Co fo TaintRun.walkFuel (toOne E S))

section
variable {E : Env} {g : Nat} {Cr Co : ZCfg} {starts base : List AS} {qs xb : List (Nat × UInt8)}

open PipeEntryRule (trace)

/-- **One frame of the pipe's routine, for any input, when every instruction of the frame meets the condition at the places.** The frame stays in the state during the pipe, with the counter falling by at most one,
and not at all if the game is paused at the frame's end; or the counter was 1 and the frame leaves the routine: then the bytes `xb` have their values, with the bytes `qs` the state is in `base`, and the
game is not paused. -/
theorem z_step (hc : ZOK Cr Co E g starts base qs xb) (hp : E.pad = TaintRun.AB.top) {m : Machine} (h : InvAt E starts m) (i : UInt8) (hP : ∀ j, PlaceOK Cr.places (trace m i j)) :
    (InvAt E starts (frame m i) ∧ (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1 ∧ ((frame m i).ram.get! g &&& 1 = 1 → (tm E m).toNat ≤ (tm E (frame m i)).toNat)) ∨
      (tm E m = 1 ∧ ExitAt xb (frame m i) ∧ (Quiet qs (frame m i) → ∃ D ∈ base, Sim E ((frame m i).frame, 2) D (frame m i)) ∧ (frame m i).ram.get! g &&& 1 ≠ 1) := by
  have hE1 := hc.er
  have hE2 := hc.eo
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, hs⟩)⟩ := h
  · obtain ⟨k0, _, _⟩ := hc.rkStarts S hS
    have hsr : Sim Cr.E (m.frame, tm E m) S m := by rw [hE1]; exact hs
    obtain ⟨g1, B, g2, g3, g4⟩ := zframe_of_walk (C := Cr) (F := (m.frame, tm E m)) hc.tr (by rw [hE1]; exact hc.or) h2 (by rw [hE1]; exact hp) (hc.sr S hS) hsr i hP
    rw [hE1] at g4
    simp only [finRkP, finRk, Bool.and_eq_true, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at g2
    obtain ⟨⟨hr, S', hS', hle⟩, hsp⟩ := g2
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
    have hkeep : (frame m i).ram.get! g &&& 1 = 1 → (tm E m).toNat ≤ (tm E (frame m i)).toNat := by
      intro hz
      have hns : B.spent = false := by
        rcases hsp with hsp | hsp
        · exact hsp
        · exact absurd hz (not_paused_of g4 hsp)
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat
      rw [hv, hns]
      simp
    left
    refine ⟨⟨S', hS', ?_⟩, hle2, hkeep⟩
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
    simp only [finXP, finX, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at g2
    obtain ⟨⟨hr, hx0⟩, hq0⟩ := g2
    have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro hr2
        have : B.rk = true := hr2
        rw [hr] at this
        cases this
    -- the counter stays at 1
    have stay : ∀ S', S' ∈ starts.map (toOne E) → ({ B with k := 0 } : AS).le S' = true →
        InvAt E starts (frame m i) ∧ (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1 ∧ ((frame m i).ram.get! g &&& 1 = 1 → (tm E m).toNat ≤ (tm E (frame m i)).toNat) := by
      intro S' hS' hle
      obtain ⟨S2, hS2, rfl⟩ := List.mem_map.1 hS'
      have hs' := sim_le hle hbase
      have he := one_of_sim hc.ti hs'
      have ht : (tm E m).toNat ≤ (tm E (frame m i)).toNat := by
        show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat
        rw [h1, he]
        decide
      exact ⟨⟨S2, hS2, Or.inr ⟨he, hs'⟩⟩, by omega, fun _ => ht⟩
    rcases hq0 with ⟨S', hS', hle⟩ | hnp
    · exact Or.inl (stay S' hS' hle)
    · rcases hx0 with ⟨S', hS', hle⟩ | ⟨hx, D, hD, hle⟩
      · exact Or.inl (stay S' hS' hle)
      · right
        exact ⟨h1, fun p hq => sim_known g4 (hx p hq), fun hq => ⟨D, hD, sim_le hle (sim_refines hq hbase)⟩, not_paused_of g4 hnp⟩

end

/-! ## The pause's class beside the walk

Start may be pressed on the pipe's frames. The six bytes of the pause (the queue, the buffer, the flag and the counter of the pause sound, the pause timer, the pause
byte) are then in one of a few classes at each frame's end. The walk above follows the pipe's timer with the bit `rk`, so these bytes cannot be carried in tables as
`StepWrites` does, and as known bytes of the walk's states they would multiply the walk. So the class is carried beside the walk (`Ph`). The frame's interrupt calls the
sound routine, the reading of the pads and the pause routine, one after the other; only these read or write the six bytes. From the first call to the return after the last
(`inR`) the walk knows them: at the first call a state is split into one piece for each class that agrees with it, and at the return the six bytes must be in a class and
are forgotten, but for the bits 0 to 6 of the pause byte, which the rest of the frame reads. Outside, no step may write them (`StepWrites.keepOK`). The bits `rk` and
`spent` are left as the step sets them, so the pipe's timer is still followed. There is no game data here. -/

open StepWrites (SState SIn soundLe)

/-- **The routine of the pause**: from the call of the sound routine in the frame's interrupt (`call`) to the return after the pause routine (`call + 9`). Inside the
three routines the body's return address is on the stack, at the body's stack pointer `sb`. `SB` are the six bytes, `g` the pause byte. -/
structure PR where
  call : UInt16
  sb : UInt8
  SB : List Nat
  g : Nat

/-- the return address that a call of the body left on the stack, if the state knows it -/
def retOf (R : PR) (A : AS) : Option UInt16 :=
  let hi := A.getK (0x100 + R.sb.toNat)
  let lo := A.getK (0x100 + R.sb.toNat - 1)
  if hi.isK && lo.isK then some (hi.v.toUInt16 * 256 + lo.v.toUInt16) else none

/-- **The state is in the routine**: at the second or the third call of the body, or below the body's stack with the return address of one of the three calls -/
def inR (R : PR) (A : AS) : Bool :=
  A.pc == R.call + 3 || A.pc == R.call + 6 ||
  (decide (A.s.toNat + 2 ≤ R.sb.toNat) && match retOf R A with
    | some r => r == R.call + 2 || r == R.call + 5 || r == R.call + 8
    | none => false)

/-- a byte with bit 7 forgotten -/
def low7 (b : TaintRun.AB) : TaintRun.AB := ⟨b.v &&& 0x7F, b.k &&& 0x7F⟩

/-- the state after the return: the six bytes forgotten, but for the bits 0 to 6 of the pause byte -/
def forgetP (R : PR) (B : AS) : AS := (StepWrites.forgetAll (R.SB.filter (· != R.g)) B).setK R.g (low7 (B.getK R.g))

/-- a step in the routine: at the return the six bytes must be in a class, and are forgotten; elsewhere the step must stay in the routine -/
def pret (R : PR) (T : List SState) (A B : AS) : Option AS :=
  if B.pc == R.call + 9 && B.s == R.sb && B.k == A.k then (if T.any (soundLe B) then some (forgetP R B) else none)
  else if inR R B then some B else none

/-- a step outside the routine: it must not write the six bytes -/
def pout (E : Env) (R : PR) (A B : AS) : Option AS :=
  if StepWrites.keepOK E (fun i => R.SB.contains i) A then some B else none

/-- **The step with the class beside the walk.** In the routine: the step `zsuccs`, and at the return the check and the forgetting; at the call of the pause routine
the state is split by bit 7 of the pause byte, which that routine adds to. At the first call: the pieces of the classes. Elsewhere: the step `zsuccs`, which must not
write the six bytes. -/
def psuccs (P : List Place) (jump : UInt16) (E : Env) (ops : Array (AM Unit)) (R : PR) (T : List SState) (A : AS) : List (Option AS) :=
  if inR R A then
    (if A.pc == R.call + 6 then TaintRun.splitBit R.g 0x80 A else [A]).flatMap fun A' => (zsuccs P jump E ops A').map fun o => o.bind (pret R T A)
  else if A.pc == R.call then
    if StepWrites.keepOK E (fun i => R.SB.contains i) A then
      T.flatMap fun t => if StepWrites.agrees t A then zsuccs P jump E ops (StepWrites.refineAll t A) else []
    else [none]
  else (zsuccs P jump E ops A).map fun o => o.bind (pout E R A)

/-- **The class beside the walk**: in the routine nothing is asked; elsewhere the machine's six bytes are in a class -/
def Ph (R : PR) (T : List SState) (A : AS) (m : Machine) : Prop := inR R A = true ∨ ∃ t ∈ T, SIn t m

/-- the table has a state that covers `B`, both in the routine or both outside -/
def pcover (C : ZCfg) (R : PR) (B : AS) : Bool :=
  (C.idx.getD (zskey C.E C.jump C.keep C.kb (hintNorm C.hints B)) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D && inR R B == inR R D
    | none => false

/-- `zwalk` with `psuccs`; the frame's end is outside the routine -/
def pwalk (C : ZCfg) (R : PR) (T : List SState) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (psuccs C.places C.jump C.E C.ops R T A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && pcover C R B) || pwalk C R T fin n B
      else B.k == A.k + 1 && fin B && !inR R B

section
variable {E : Env} {F : Nat × UInt8}

theorem mem_low7 {b : TaintRun.AB} {x : UInt8} (h : b.mem x) : (low7 b).mem x := by
  refine TaintRun.mem_iff.2 fun i hi => ?_
  have a1 := TaintRun.mem_iff.1 h i hi
  show (TaintRun.bt x i && TaintRun.bt (b.k &&& 0x7F) i) = (TaintRun.bt (b.v &&& 0x7F) i && TaintRun.bt (b.k &&& 0x7F) i)
  rw [TaintRun.bt_and, TaintRun.bt_and]
  revert a1
  generalize TaintRun.bt x i = p, TaintRun.bt b.v i = r, TaintRun.bt b.k i = s, TaintRun.bt 0x7F i = u
  revert p r s u
  decide

theorem forgetP_k (R : PR) (B : AS) : (forgetP R B).k = B.k := StepWrites.forgetAll_k _ _

theorem sim_forgetP (R : PR) (hg : R.g < 2048) {B : AS} {m : Machine} (hs : Sim E F B m) : Sim E F (forgetP R B) m :=
  SideChangeEnd.sim_refine (StepWrites.sim_forgetAll _ hs) (mem_low7 (hs.ram R.g hg))

variable {ops : Array (AM Unit)} {R : PR} {T : List SState} {P : List Place} {jump : UInt16}

/-- **One step**: `psuccs` follows the machine, when it meets the condition at the places, and the class beside the walk goes on -/
theorem s_psuccs (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hg : R.g < 2048) (h0 : StepWrites.tabOK R.SB T = true)
    {A : AS} {m : Machine} (hs : Sim E F A m) (hph : Ph R T A m) (hp : PlaceOK P m) :
    ∃ r ∈ psuccs P jump E ops R T A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 ∧ Ph R T B (go step m).2 := by
  have tab : ∀ t ∈ T, ∀ p ∈ t, R.SB.contains p.1 = true ∧ p.1 < 2048 := by
    intro t ht p hp
    simp only [StepWrites.tabOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0
    exact h0 t ht p hp
  unfold psuccs
  by_cases hin : inR R A = true
  · rw [if_pos hin]
    obtain ⟨A', hA', s', k'⟩ : ∃ A' ∈ (if A.pc == R.call + 6 then TaintRun.splitBit R.g 0x80 A else [A]), Sim E F A' m ∧ A'.k = A.k := by
      split
      · exact TaintRun.cov_bit hg (by decide) A m hs
      · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
    obtain ⟨r, hr, hB⟩ := s_zsuccs (P := P) (jump := jump) hops hT s' hp
    refine ⟨r.bind (pret R T A), List.mem_flatMap.2 ⟨A', hA', List.mem_map.2 ⟨r, hr, rfl⟩⟩, fun B hB' => ?_⟩
    cases r with
    | none => cases hB'
    | some B0 =>
      obtain ⟨g1, g2⟩ := hB B0 rfl
      have g2' : StepRel A B0 m (go step m).2 := StepWrites.stepRel_k k'.symm rfl g2
      have hB2 : pret R T A B0 = some B := hB'
      unfold pret at hB2
      split at hB2
      · split at hB2
        · rename_i _ hT1
          simp only [Option.some.injEq] at hB2
          subst hB2
          obtain ⟨t, ht, hle⟩ := List.any_eq_true.1 hT1
          exact ⟨sim_forgetP R hg g1, StepWrites.stepRel_k rfl (forgetP_k R B0) g2', Or.inr ⟨t, ht, StepWrites.sIn_of_le g1 hle⟩⟩
        · cases hB2
      · split at hB2
        · rename_i _ hin2
          simp only [Option.some.injEq] at hB2
          subst hB2
          exact ⟨g1, g2', Or.inl hin2⟩
        · cases hB2
  · rw [if_neg hin]
    have hgh : ∃ t ∈ T, SIn t m := by
      rcases hph with h | h
      · exact absurd h hin
      · exact h
    by_cases hc : (A.pc == R.call) = true
    · rw [if_pos hc]
      by_cases hk : StepWrites.keepOK E (fun i => R.SB.contains i) A = true
      · rw [if_pos hk]
        obtain ⟨t, ht, htm⟩ := hgh
        have hag : StepWrites.agrees t A = true := StepWrites.agrees_of hs (fun p hp => (tab t ht p hp).2) htm
        obtain ⟨r, hr, hB⟩ := s_zsuccs (P := P) (jump := jump) hops hT (StepWrites.sim_refineAll t hs htm) hp
        refine ⟨r, List.mem_flatMap.2 ⟨t, ht, by rw [if_pos hag]; exact hr⟩, fun B hB' => ?_⟩
        obtain ⟨g1, g2⟩ := hB B hB'
        exact ⟨g1, StepWrites.stepRel_k (StepWrites.refineAll_k t A).symm rfl g2,
          Or.inr ⟨t, ht, StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (StepWrites.keep_step hs hk)⟩⟩
      · rw [if_neg hk]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    · rw [if_neg hc]
      obtain ⟨r, hr, hB⟩ := s_zsuccs (P := P) (jump := jump) hops hT hs hp
      refine ⟨r.bind (pout E R A), List.mem_map.2 ⟨r, hr, rfl⟩, fun B hB' => ?_⟩
      cases r with
      | none => cases hB'
      | some B0 =>
        obtain ⟨g1, g2⟩ := hB B0 rfl
        have hB2 : pout E R A B0 = some B := hB'
        unfold pout at hB2
        split at hB2
        · rename_i hk
          simp only [Option.some.injEq] at hB2
          subst hB2
          obtain ⟨t, ht, htm⟩ := hgh
          exact ⟨g1, g2, Or.inr ⟨t, ht, StepWrites.sIn_keep (fun p hp => (tab t ht p hp).1) htm (StepWrites.keep_step hs hk)⟩⟩
        · cases hB2

end

section
variable {C : ZCfg} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool} {R : PR} {T : List SState}

open PipeEntryRule (trace trace_stop frame_trace nxt)

/-- a state of the walk: it covers the machine, the class beside it holds, and the walk from it succeeds -/
def PLive (C : ZCfg) (R : PR) (T : List SState) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ Ph R T A m ∧ ∃ n, pwalk C R T fin n A = true

theorem cover_plive (ht : C.t.all (pwalk C R T fin Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hp : Ph R T B m) (h : pcover C R B = true) :
    ∃ D, PLive C R T fin F D m ∧ D.k = B.k := by
  unfold pcover at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have h3 : B.le D = true ∧ inR R B = inR R D := by simpa only [Bool.and_eq_true, beq_iff_eq] using h2
    have hle : B.le D = true := h3.1
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    have hp' : Ph R T D m := by
      rcases hp with h4 | h4
      · exact Or.inl (h3.2 ▸ h4)
      · exact Or.inr h4
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, hp', Fu, hall⟩, hk⟩
  · cases h2

theorem plive_step (ht : C.t.all (pwalk C R T fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hg : R.g < 2048)
    (h0 : StepWrites.tabOK R.SB T = true) {A : AS} {m : Machine} (hl : PLive C R T fin F A m) (hp : PlaceOK C.places m) :
    (∃ A', PLive C R T fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ inR R B = false ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2 ∧ Ph R T B (go step m).2) := by
  obtain ⟨hs, hph, n, hw⟩ := hl
  cases n with
  | zero => simp [pwalk] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_psuccs (P := C.places) (jump := C.jump) hops hT hg h0 hs hph hp
    simp only [pwalk, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2, h3⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h4⟩ | h4
        · obtain ⟨D, hD, hk⟩ := cover_plive ht h1 h3 h4
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, h3, n, h4⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw2
        exact ⟨k2, B, hw2.1.2, hw2.2, k1, h1, h3⟩

theorem pframe_run (ht : C.t.all (pwalk C R T fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hg : R.g < 2048)
    (h0 : StepWrites.tabOK R.SB T = true) {m : Machine} {i : UInt8} (hP : ∀ j, PlaceOK C.places (trace m i j)) :
    ∀ (n j : Nat) (A : AS), PLive C R T fin F A (trace m i j) → (trace m i j).frame = m.frame → dotsPerFrame ≤ (trace m i j).fdot + 3 * n →
      (trace m i (j + n)).frame = m.frame + 1 ∧
        ∃ B, fin B = true ∧ inR R B = false ∧ B.k = A.k + 1 ∧ Sim C.E F B (trace m i (j + n)) ∧ Ph R T B (trace m i (j + n)) := by
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
    rcases plive_step ht hops hT hg h0 hl (hP j) with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, B, h2, h2', h3, h4, h5⟩
    · rw [← hnx] at h1 h3 h4
      have := ih (j + 1) A' h1 (h3.trans hf) (by omega)
      rw [h2] at this
      exact this
    · rw [← hnx] at h1 h4 h5
      have hstop : ((trace m i (j + 1)).frame ≥ m.frame + 1 || (trace m i (j + 1)).halted) = true := by
        simp [h1, hf]
      rw [trace_stop hstop n]
      exact ⟨by rw [h1, hf], B, h2, h2', h3, h4, h5⟩

/-- **One frame, with the class beside the walk.** A walk from `S` that succeeds covers the frame of a machine of `S` whose six bytes are in a class, when every
instruction of the frame meets the condition at the places; at the frame's end the six bytes are in a class again. -/
theorem pframe_of_walk (ht : C.t.all (pwalk C R T fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hg : R.g < 2048)
    (h0 : StepWrites.tabOK R.SB T = true) (hE : C.E.pad = TaintRun.AB.top)
    {S : AS} {m : Machine} (hw : pwalk C R T fin Fu S = true) (hs : Sim C.E F S m) (hph : Ph R T S m) (i : UInt8) (hP : ∀ j, PlaceOK C.places (trace m i j)) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) ∧ ∃ t ∈ T, SIn t (frame m i) := by
  rw [frame_trace]
  have hs0 : Sim C.E F S (trace m i 0) := { hs with pad := by rw [hE]; exact TaintRun.mem_top _ }
  have hph0 : Ph R T S (trace m i 0) := hph
  have hf : dotsPerFrame ≤ (trace m i 0).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  obtain ⟨g1, B, g2, g3, g4, g5, g6⟩ := pframe_run ht hops hT hg h0 hP fuelPerFrame 0 S ⟨hs0, hph0, Fu, hw⟩ rfl hf
  rw [Nat.zero_add] at g1 g5 g6
  refine ⟨g1, B, g2, g4, g5, ?_⟩
  rcases g6 with h | h
  · rw [g3] at h
    cases h
  · exact h

end

/-! ### The search for a table with the class beside the walk: no part of the proof -/

/-- the search of `zloop` with `psuccs` -/
partial def ploop (P : List Place) (jump : UInt16) (E : Env) (ops : Array (AM Unit)) (R : PR) (T : List SState) (keep : List Nat) (kb : List (Nat × UInt8))
    (H : List Hint) (limit : Nat) (X0 : ZS) : ZS := Id.run do
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
      let rs := psuccs P jump E ops R T A
      X := { X with steps := X.steps + rs.length }
      if rs.any (·.isNone) then X := { X with fails := X.fails + 1, failed := if X.failed.size < 40 then X.failed.push A else X.failed }
      for b in rs.filterMap id do
        if b.k != A.k then X := { X with ends := X.ends.push b }
        else X := zroute E jump keep kb H X b
  return X

/-- the configuration from the table found, with the six bytes kept apart -/
def pcfgOf (P : List Place) (jump : UInt16) (E : Env) (R : PR) (T : List SState) (ckeys keep : List Nat) (kb : List (Nat × UInt8)) (H : List Hint) (starts : List AS) :
    ZCfg :=
  let ops := (aRows E).toArray
  let keep := keep ++ R.SB
  let X := ploop P jump E ops R T keep kb H 12000000 (starts.foldl (zroute E jump keep kb H) {})
  let I := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := X.outK.getD acc.2.2 0
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops, places := P, jump, ckeys, keep, kb, hints := H, t := X.out, idx := I.1, cut := I.2.1 }

/-! ### The check of the pipe's frames with the class beside the walk -/

/-- what the check of the pipe's frames with the class beside the walk says. As `ZOK`, with the routine `R` and the classes `T`. -/
structure POK (Cr Co : ZCfg) (R : PR) (T : List SState) (E : Env) (g : Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Prop where
  ti : E.rkI < 2048
  tg : R.g < 2048
  tab : StepWrites.tabOK R.SB T = true
  er : Cr.E = E
  eo : Co.E = E
  or : Cr.ops = (aRows E).toArray
  oo : Co.ops = (aRows E).toArray
  pr : Cr.places = Co.places
  rkStarts : ∀ S ∈ starts, S.k = 0 ∧ S.rk = true ∧ S.spent = false ∧ inR R S = false ∧ inR R (toOne E S) = false
  tr : Cr.t.all (pwalk Cr R T (finRkP g starts) TaintRun.walkFuel) = true
  sr : ∀ S ∈ starts, pwalk Cr R T (finRkP g starts) TaintRun.walkFuel S = true
  to : Co.t.all (pwalk Co R T (finXP g (starts.map (toOne E)) base qs xb) TaintRun.walkFuel) = true
  so : ∀ S ∈ starts, pwalk Co R T (finXP g (starts.map (toOne E)) base qs xb) TaintRun.walkFuel (toOne E S) = true

/-- **the check of the pipe's frames with the class beside the walk** -/
def pcheck (Cr Co : ZCfg) (R : PR) (T : List SState) (E : Env) (g : Nat) (starts base : List AS) (qs xb : List (Nat × UInt8)) : Bool :=
  let ones := starts.map (toOne E)
  let fr := finRkP g starts
  let fo := finXP g ones base qs xb
  decide (E.rkI < 2048) && decide (R.g < 2048) && StepWrites.tabOK R.SB T && starts.all (fun S => S.k == 0 && S.rk && !S.spent && !inR R S && !inR R (toOne E S)) &&
    Cr.t.all (pwalk Cr R T fr TaintRun.walkFuel) && starts.all (pwalk Cr R T fr TaintRun.walkFuel) &&
    Co.t.all (pwalk Co R T fo TaintRun.walkFuel) && starts.all (fun S => pwalk Co R T fo TaintRun.walkFuel (toOne E S))

section
variable {E : Env} {g : Nat} {Cr Co : ZCfg} {R : PR} {T : List SState} {starts base : List AS} {qs xb : List (Nat × UInt8)}

open PipeEntryRule (trace)

/-- **One frame of the pipe's routine with the class beside the walk, for any input**, when every instruction of the frame meets the condition at the places: the frame
stays in the state during the pipe and the six bytes in a class; or it leaves the routine, the bytes `xb` have their values, with the bytes `qs` the state is in `base`,
the game is not paused, and the six bytes are in a class. -/
theorem p_step (hc : POK Cr Co R T E g starts base qs xb) (hp : E.pad = TaintRun.AB.top) {m : Machine} (h : InvAt E starts m) (hg : ∃ t ∈ T, SIn t m) (i : UInt8)
    (hP : ∀ j, PlaceOK Cr.places (trace m i j)) :
    (InvAt E starts (frame m i) ∧ ∃ t ∈ T, SIn t (frame m i)) ∨
      (ExitAt xb (frame m i) ∧ (Quiet qs (frame m i) → ∃ D ∈ base, Sim E ((frame m i).frame, 2) D (frame m i)) ∧ (frame m i).ram.get! g &&& 1 ≠ 1 ∧
        ∃ t ∈ T, SIn t (frame m i)) := by
  have hE1 := hc.er
  have hE2 := hc.eo
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, hs⟩)⟩ := h
  · obtain ⟨_, _, _, hn1, _⟩ := hc.rkStarts S hS
    have hsr : Sim Cr.E (m.frame, tm E m) S m := by rw [hE1]; exact hs
    obtain ⟨_, B, g2, _, g4, hgh⟩ := pframe_of_walk (C := Cr) (F := (m.frame, tm E m)) hc.tr (by rw [hE1]; exact hc.or) h2 hc.tg hc.tab
      (by rw [hE1]; exact hp) (hc.sr S hS) hsr (Or.inr hg) i hP
    rw [hE1] at g4
    simp only [finRkP, finRk, Bool.and_eq_true, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at g2
    obtain ⟨⟨hr, S', hS', hle⟩, _⟩ := g2
    have hv : (frame m i).ram.get! E.rkI = if B.spent then tm E m - 1 else tm E m := g4.rkv hr
    have hbase : Sim E ((frame m i).frame, tm E (frame m i)) ({ B with k := 0, spent := false } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro _
        rfl
    have hs' := sim_le hle hbase
    have hge : 1 ≤ (tm E (frame m i)).toNat := by
      show 1 ≤ ((frame m i).ram.get! E.rkI).toNat
      rw [hv]
      split
      · rw [u8_sub_one h2]
        omega
      · omega
    left
    refine ⟨⟨S', hS', ?_⟩, hgh⟩
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
    obtain ⟨_, B, g2, _, g5, hgh⟩ := pframe_of_walk (C := Co) (F := (m.frame, 2)) hc.to (by rw [hE2]; exact hc.oo) (Nat.le_refl _) hc.tg hc.tab
      (by rw [hE2]; exact hp) (hc.so S hS) hsr (Or.inr hg) i hP'
    rw [hE2] at g5
    have g4 : Sim E (m.frame, 2) B (frame m i) := g5
    simp only [finXP, finX, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at g2
    obtain ⟨⟨hr, hx0⟩, hq0⟩ := g2
    have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro hr2
        have : B.rk = true := hr2
        rw [hr] at this
        cases this
    have stay : ∀ S', S' ∈ starts.map (toOne E) → ({ B with k := 0 } : AS).le S' = true → InvAt E starts (frame m i) := by
      intro S' hS' hle
      obtain ⟨S2, hS2, rfl⟩ := List.mem_map.1 hS'
      have hs' := sim_le hle hbase
      exact ⟨S2, hS2, Or.inr ⟨one_of_sim hc.ti hs', hs'⟩⟩
    rcases hq0 with ⟨S', hS', hle⟩ | hnp
    · exact Or.inl ⟨stay S' hS' hle, hgh⟩
    · rcases hx0 with ⟨S', hS', hle⟩ | ⟨hx, D, hD, hle⟩
      · exact Or.inl ⟨stay S' hS' hle, hgh⟩
      · right
        exact ⟨fun p hq => sim_known g4 (hx p hq), fun hq => ⟨D, hD, sim_le hle (sim_refines hq hbase)⟩, not_paused_of g4 hnp, hgh⟩

end

/-! ## The statement -/

/-- the bytes that the state at the exit knows. The values come from the reference machine when the timer has run out. Round 16 added the level's number
(`AreaNumber`, last): the entry knows it (`entryNames`), no frame of the pipe stores to it, so the walk of the pipe's frames ends with it known, and the rows after the
exit carry it to the room's first control (`ScreenStart.area_of_rows`). -/
def exitNames : List (String × Nat × Nat) :=
  [("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("GameEngineSubroutine", 0, 1), ("ScreenRoutineTask", 0, 1), ("DisableScreenFlag", 0, 1),
   ("AreaPointer", 0, 1), ("EntrancePage", 0, 1), ("AltEntranceControl", 0, 1), ("HalfwayPage", 0, 1), ("CurrentPlayer", 0, 1), ("JoypadOverride", 0, 1), ("GameTimerExpiredFlag", 0, 1),
   ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1),
   ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("Square1SoundQueue", 0, 1), ("Square2SoundQueue", 0, 1), ("NoiseSoundQueue", 0, 1),
   ("WorldNumber", 0, 1), ("PrimaryHardMode", 0, 1), ("AreaNumber", 0, 1)]

/-- the bytes that the state at the exit knows by a mask of bits: Mario's status below the fire flower, the saved song but for the bit of the underground song. The room's condition asks these bits. -/
def exitMasks : List (String × Nat × UInt8) := [("PlayerStatus", 0, 254), ("AreaMusicBuffer_Alt", 0, 251)]

/-- the masks of the exit as RAM indices -/
def exitBits (nx : Names) : List (Nat × UInt8) := exitMasks.map fun p => (adI nx p.1 + p.2.1, p.2.2)

/-- the bytes of the sound's pause, the sound effects and the screen buffer's control that the state at the exit knows -/
def quietP : List (String × Nat × Nat) :=
  [("PauseSoundBuffer", 0, 1), ("PauseSoundQueue", 0, 1), ("Square1SoundBuffer", 0, 1), ("Square2SoundBuffer", 0, 1), ("NoiseSoundBuffer", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1)]

/-- **the bytes that the condition at the exit asks of a real run**: the sound's pause and two sound effects. The frames of the pipe give the other two bytes of `quietP`. -/
def quietA : List (String × Nat × Nat) :=
  [("PauseSoundBuffer", 0, 1), ("PauseSoundQueue", 0, 1), ("Square1SoundBuffer", 0, 1), ("Square2SoundBuffer", 0, 1)]

/-- **The bytes that the state at the entry knows**, besides the bytes of the exit. The values come from the reference entry. They are the bytes that no frame of the pipe's routine changes, and that the frames need:
the routine and the task, the objects' slots that stay empty, the sound's queues, the area, the scroll's other bytes. Found by a search, and checked on real entries. Round 12 took out
the bytes of `entryDropped`. Round 15 added the level's number (`AreaNumber`, last): the frames of the pipe do not need it, but the press of Start on the title and the
frames from control give it (`EntryKeep`), and the walks of `AreaKeep` carry it from here to the side pipe's entry (`Route.Run.area₁`, `Route.Run.area₂`). -/
def entryNames : List (String × Nat × Nat) :=
  [("Left_Right_Buttons", 0, 1), ("GameEngineSubroutine", 0, 1), ("Enemy_Flag", 4, 3), ("Enemy_ID", 3, 4), ("Enemy_State", 4, 1), ("Fireball_State", 0, 2), ("Block_State", 0, 4), ("Misc_State", 0, 9), ("Misc_Y_Position", 7, 1), ("EnemyData", 0, 1), ("EnemyDataHigh", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicBuffer", 0, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1), ("Square1SoundQueue", 1, 1), ("FlagpoleFNum_YMFDummy", 0, 1), ("FlagpoleScore", 0, 1), ("FloateyNum_Control", 0, 7), ("FirebarSpinSpeed", 14, 2), ("VineFlagOffset", 0, 1), ("Block_RepFlag", 0, 2), ("SprDataOffset_Ctrl", 1, 1), ("MaximumRightSpeed", 18, 2), ("Cannon_PageLoc", 0, 6), ("Cannon_X_Position", 0, 6), ("Cannon_Y_Position", 0, 5), ("Misc_Collision_Flag", 10, 3), ("EnemyFrenzyBuffer", 0, 1), ("SecondaryHardMode", 0, 1), ("EnemyFrenzyQueue", 0, 1), ("FireballCounter", 0, 1), ("WarpZoneControl", 0, 1), ("EnemyObjectPageSel", 0, 1), ("ScreenRoutineTask", 0, 1), ("ScrollThirtyTwo", 1, 1), ("VerticalScroll", 0, 1), ("CloudTypeOverride", 0, 1), ("AreaType", 0, 1), ("JoypadOverride", 0, 1), ("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("DisableScreenFlag", 0, 1), ("StarInvincibleTimer", 0, 1), ("WorldEndTimer", 0, 1), ("AreaNumber", 0, 1)]

/-- the bytes that the state at the entry knows by a mask of bits: the objects' kinds and states as on a real entry, Mario's status below the fire flower, the pause bits other than the low bit and the top bit -/
def entryMasks : List (String × Nat × UInt8) :=
  [("Enemy_ID", 0, 249), ("Enemy_ID", 1, 249), ("Enemy_ID", 2, 249), ("Enemy_State", 0, 254), ("Enemy_State", 1, 254), ("Enemy_State", 2, 254), ("Enemy_State", 3, 254),
   ("Square1SoundQueue", 0, 239), ("SprDataOffset_Ctrl", 0, 254), ("PlayerStatus", 0, 254), ("GamePauseStatus", 0, 126), ("AreaMusicBuffer_Alt", 0, 251)]

/-- **The bytes that the entry no longer asks** (round 12): with each alone not known at the entry, and with all of them together, both walks of the pipe's frames
(`zcheck`, `pcheck`) and `leftCheck` still pass (`entry-need`). The buttons up and down, the enemies' page, the screen's timer, the demo's timer, three bytes after the world's
number in the menu, the byte after the mode, the height of misc object 8, Mario's state, the state of enemy slot 5, the second square's effect queue (the sound routine clears it
on every frame, so the exit still knows it), the flagpole's number, the vine's height, the first cannon's offset, the duplicate, the colours, the loop, the flag of a new game timer. -/
def entryDropped : List (String × Nat × Nat) :=
  [("Up_Down_Buttons", 0, 1), ("EnemyObjectPageLoc", 0, 1), ("ScreenTimer", 0, 1), ("DemoTimer", 0, 1), ("WorldSelectNumber", 2, 3), ("OperMode", 1, 1),
   ("Misc_Y_Position", 8, 1), ("Player_State", 0, 1), ("Enemy_State", 5, 1), ("Square2SoundQueue", 0, 1), ("FlagpoleFNum_Y_Pos", 0, 1), ("VineHeight", 0, 1),
   ("Cannon_Offset", 0, 1), ("DuplicateObj_Offset", 0, 1), ("BackgroundColorCtrl", 0, 1), ("LoopCommand", 0, 1), ("FetchNewGameTimerFlag", 0, 1)]

/-- the known bytes of the entry as RAM indices: the list, and the bytes of the exit, but those of `entryDropped` -/
def entryKnown (nx : Names) : List Nat :=
  let masked := entryMasks.map fun p => adI nx p.1 + p.2.1
  let dropped := bytesOf nx entryDropped
  ((bytesOf nx entryNames ++ bytesOf nx exitNames).eraseDups).filter fun i => !masked.contains i && !dropped.contains i

/-- the masks as RAM indices -/
def entryBits (nx : Names) : List (Nat × UInt8) := entryMasks.map fun p => (adI nx p.1 + p.2.1, p.2.2)

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  let l := ((exitNames ++ quietP ++ songNames ++ entryNames ++ entryDropped).map (·.1)) ++ entryMasks.map (·.1) ++ exitMasks.map (·.1) ++ ["PlayerStatus", "Player_X_Scroll", partName, "SprShuffleAmtOffset", "SprDataOffset", "Misc_SprDataOffset", "AreaData", "AreaDataHigh", "VRAM_Buffer2_Offset", "VRAM_Buffer2", "BlockBufferColumnPos", "CurrentPageLoc", "CurrentColumnPos", "TerrainControl", "BackloadingFlag", "AreaObjectPageLoc", "AreaDataOffset", "ForegroundScenery", "BackgroundScenery", "AreaType", "MetatileBuffer", "AreaObjectLength", "AreaObjOffsetBuffer", "AreaStyle", "AreaParserTaskNum", "ScrollThirtyTwo", "VRAM_Buffer_AddrCtrl", "VRAM_Buffer1", "VRAM_Buffer1_Offset", "EnemyDataOffset", "ObjectOffset", "MusicOffset_Square2", "MusicOffset_Noise", "Squ2_NoteLenCounter", "MusicOffset_Triangle"] ++
    SoundWalk.soundNames.map (·.1)
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

/-- the bytes known by a mask, from the reference machine -/
def maskOn (bits : List (Nat × UInt8)) (e : Machine) (S : AS) : AS :=
  bits.foldl (fun A b => A.setK b.1 ⟨e.ram.get! b.1, b.2⟩) S

/-- the machine has these bits of the reference machine -/
def BitsAt (bits : List (Nat × UInt8)) (e m : Machine) : Prop := ∀ b ∈ bits, b.1 < 2048 ∧ (⟨e.ram.get! b.1, b.2⟩ : TaintRun.AB).mem (m.ram.get! b.1)

/-- the start states of the rows, before the two cases of the flag: the bytes of the exit, and the bits of its masks -/
def baseOf (d : Data) (e : Machine) : List AS :=
  (exitStarts (refX e) (exitKnown d.nx) (adI d.nx "GamePauseStatus")).map (maskOn (exitBits d.nx) (refX e))

/-- the first states when the sound's pause flag is 0: one state for each row of the song -/
def songStarts (d : Data) (e : Machine) : List AS :=
  (flagZero (adI d.nx "PauseModeFlag") (baseOf d e)).flatMap fun S => d.xshape.flatMap fun r => d.song.map fun q => refine q (refine r S)

/-- the rows of the two cases of the flag: if it is not 0 the sound routines do not run, and the song does not matter -/
def rowsA (c : Ctx) (d : Data) (e : Machine) : List Row := rowsAfter c (afterF - 2) (rowSong c d.pl (bytesOfSong d.nx) d.dl d.dh 32 (songStarts d e))
def rowsB (c : Ctx) (d : Data) (e : Machine) : List Row := rowsAfter c (afterF - 2) (rowSong c d.pl [] d.dl d.dh 1 ((flagNotZero (baseOf d e)).flatMap fun S => d.xshape.map fun r => refine r S))

/-! ## The time at the exit

The last row of `rowsA` holds the states with control and the states where the time is up, because the game timer's digits are free. If at the exit the sound's pause flag is 0 and the
game timer is not 000 (`SideChangeEnd.TimeOK`), the machine is in the rows `timeRowsO`, as those of `rowsA` but with `dg` saying that the timer is not 000. Their last row has only states
with control (`zeroCtl`). The entrance's setup may load the timer, on the flag `FetchNewGameTimerFlag`: the search keeps this flag apart, and the frame's ends keep `dg` apart. -/

/-- the environment of the rows of the time: `dg` says that the timer is not 000 -/
def timeEnv (d : Data) (e : Machine) : Env := { envOf d e with D := digitsOf d.nx }

/-- what the rows of the time have in common -/
def timeCtx (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Ctx :=
  { ctxOf sy nm d e with E := timeEnv d e, keep := (ctxOf sy nm d e).keep ++ [adI d.nx "FetchNewGameTimerFlag"] }

/-- the first states: those of `rowsA`, with `dg` -/
def timeStarts (d : Data) (e : Machine) : List AS := (songStarts d e).map fun S => { S with dg := true }

/-- the rows of the time -/
def timeRowsO (c : Ctx) (d : Data) (e : Machine) : List Row := rowsAfterD c (afterF - 2) (rowSongD c d.pl (bytesOfSong d.nx) d.dl d.dh 32 (timeStarts d e))

/-- a machine is in the rows of the time -/
def InRowsTO (sy : Syms) (nm : Names) (d : Data) (e : Machine) (m : Machine) : Prop :=
  InvL (timeCtx sy nm d e) (timeRowsO (timeCtx sy nm d e) d e) m

/-- the check of the rows of the time: a frame goes from a row to the next, and where `left` is 0 every state has control -/
def timeCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Bool :=
  let c := timeCtx sy nm d e
  let l := timeRowsO c d e
  chainOKD c l && zeroCtl sy l

/-- the bytes that the condition at the exit asks, with the reference's values -/
def quietQ (d : Data) (e : Machine) : List (Nat × UInt8) := (bytesOf d.nx quietA).map fun i => (i, (refX e).ram.get! i)

/-- the reference machines at the entry -/
def refsP (d : Data) (e : Machine) : List (Machine × List Nat) := [(e, d.known)]

/-- the start states of the pipe's frames -/
def startsP (d : Data) (e : Machine) : List AS := (startsOf (refsP d e)).map (maskOn d.bits e)

/-- the pause byte -/
abbrev pauseI (d : Data) : Nat := adI d.nx "GamePauseStatus"

/-- **The game is paused**: the low bit of the pause byte is set. At the end of a frame it says that the frame skipped the game's timers and routines. -/
def Paused (d : Data) (m : Machine) : Prop := m.ram.get! (pauseI d) &&& 1 = 1

/-- `Paused`, for a program -/
def pausedB (d : Data) (m : Machine) : Bool := m.ram.get! (pauseI d) &&& 1 == 1

/-! ## The rows with the sound's bytes in tables

The rows of the time know the sound's bytes, so the pause sound at the exit had to be silent (`quietQ`, and the flag 0 in `TimeOK`). Here the rows forget the sound's bytes
outside the sound routine and carry tables of them (`SoundRows`, the method of `SideChangeSound`). The first table holds the kinds of the pause sound at the exit: silent with the
flag 0 and the song's bytes a row of the song, or the sound of the unpause at a count from 1 to its length (`QuietP`). The rows of these frames where `left` is 0, each state
with the bytes of each state of its table, are the rows `timeRows` that the room's checks read. -/

open StepWrites (Rt SState SIn)

/-- the first call to `target` from `a` on, within `n` bytes -/
def jsrAt (m : Machine) (a target : UInt16) : Nat → UInt16
  | 0 => a
  | n + 1 => if romByte m a == 0x20 && romByte m (a + 1) == target.toUInt8 && romByte m (a + 2) == (target >>> 8).toUInt8 then a else jsrAt m (a + 1) target n

/-- **The sound routine**: its bytes, its call in the frame's interrupt and the return, and its code, from `SoundEngine` on -/
def rtOf (sy : Syms) (nx : Names) (e : Machine) : Rt :=
  let call := jsrAt e sy.NonMaskableInterrupt sy.SoundEngine 512
  { SB := SoundWalk.soundBytes nx, call, ret := call + 3, inR := fun pc => decide (sy.SoundEngine ≤ pc) }

/-- the four bytes of the pause sound: the queue, the buffer, the sound's pause flag, the counter of the first square's effect; and the buffers of the two squares' effects -/
structure PauseIx where
  q : Nat
  b : Nat
  f : Nat
  c : Nat
  s1 : Nat
  s2 : Nat

def pauseIx (nx : Names) : PauseIx :=
  ⟨adI nx "PauseSoundQueue", adI nx "PauseSoundBuffer", adI nx "PauseModeFlag", adI nx "Squ1_SfxLenCounter", adI nx "Square1SoundBuffer", adI nx "Square2SoundBuffer"⟩

/-- **The pause sound at the exit.** Silent: the queue and the buffer as at the reference machine `x`, the sound's pause flag 0, the two squares' effects as at `x`, and
the song's bytes one of the rows of the song. Or the sound of the unpause plays: the queue as at `x`, the buffer and the flag hold the unpause sound's value, and the counter
is from 1 to one less than the sound's length (the sound sets the length and counts one down on the same frame). -/
def QuietP (sy : Syms) (d : Data) (x m : Machine) : Prop :=
  (m.ram.get! (pauseIx d.nx).q = x.ram.get! (pauseIx d.nx).q ∧ m.ram.get! (pauseIx d.nx).b = x.ram.get! (pauseIx d.nx).b ∧ m.ram.get! (pauseIx d.nx).f = 0 ∧
    m.ram.get! (pauseIx d.nx).s1 = x.ram.get! (pauseIx d.nx).s1 ∧ m.ram.get! (pauseIx d.nx).s2 = x.ram.get! (pauseIx d.nx).s2 ∧ SongAt d.song m) ∨
  (m.ram.get! (pauseIx d.nx).q = x.ram.get! (pauseIx d.nx).q ∧ m.ram.get! (pauseIx d.nx).b = sy.UnpauseSfxValue.toUInt8 ∧
    m.ram.get! (pauseIx d.nx).f = sy.UnpauseSfxValue.toUInt8 ∧ 1 ≤ (m.ram.get! (pauseIx d.nx).c).toNat ∧ (m.ram.get! (pauseIx d.nx).c).toNat < sy.PauseSfxLength.toNat)

/-- `QuietP` as a check, for a program -/
def quietPB (sy : Syms) (d : Data) (x m : Machine) : Bool :=
  let ix := pauseIx d.nx
  (m.ram.get! ix.q == x.ram.get! ix.q && m.ram.get! ix.b == x.ram.get! ix.b && m.ram.get! ix.f == 0 && m.ram.get! ix.s1 == x.ram.get! ix.s1 &&
    m.ram.get! ix.s2 == x.ram.get! ix.s2 && d.song.any fun q => q.all fun p => m.ram.get! p.1 == p.2) ||
  (m.ram.get! ix.q == x.ram.get! ix.q && m.ram.get! ix.b == sy.UnpauseSfxValue.toUInt8 && m.ram.get! ix.f == sy.UnpauseSfxValue.toUInt8 &&
    decide (1 ≤ (m.ram.get! ix.c).toNat) && decide ((m.ram.get! ix.c).toNat < sy.PauseSfxLength.toNat))

/-- **The kinds of the pause sound at the exit**, as states of a table: silent with the flag 0 and the effects as at `x`, one for each row of the song; the unpause sound at each
count from 1 to one less than its length -/
def kindsP (sy : Syms) (d : Data) (x : Machine) : List SState :=
  let ix := pauseIx d.nx
  let q0 := (ix.q, TaintRun.AB.known (x.ram.get! ix.q))
  let b0 := (ix.b, TaintRun.AB.known (x.ram.get! ix.b))
  let U := TaintRun.AB.known sy.UnpauseSfxValue.toUInt8
  (d.song.map fun r => [q0, b0, (ix.f, TaintRun.AB.known 0), (ix.s1, TaintRun.AB.known (x.ram.get! ix.s1)), (ix.s2, TaintRun.AB.known (x.ram.get! ix.s2))] ++
    SoundRows.ofRow r) ++
    (List.range (sy.PauseSfxLength.toNat - 1)).map fun j => [q0, (ix.b, U), (ix.f, U), (ix.c, TaintRun.AB.known (j + 1).toUInt8)]

/-- the bytes that the states at the exit know (`baseK`): those of the exit's list, the noise effect's buffer and the screen buffer's control. The walk of the pipe's frames gives them. -/
def exitKnownK (nx : Names) : List Nat := bytesOf nx exitNames ++ bytesOf nx [("NoiseSoundBuffer", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1)]

/-- the masks of the states at the exit: those of the exit, and bits 0 to 6 of the pause byte. The pause routine writes the pause byte only with bit 0 flipped and
bit 7 set, or with bit 7 cleared, so the walk of the pipe's frames keeps the bits 1 to 6 that the entry knows. -/
def exitBitsK (nx : Names) : List (Nat × UInt8) := exitBits nx ++ [(adI nx "GamePauseStatus", 0x7F)]

/-- the states at the exit: the bytes of `exitKnownK`, and the bits of `exitBitsK` -/
def baseK (d : Data) (e : Machine) : List AS :=
  (exitStarts (refX e) (exitKnownK d.nx) (adI d.nx "GamePauseStatus")).map (maskOn (exitBitsK d.nx) (refX e))

/-- the sound's bytes that the states at the exit know, as a state of a table, with the reference's values and masks -/
def soundBaseP (R : Rt) (d : Data) (x : Machine) : SState :=
  let ix := pauseIx d.nx
  let K := exitKnownK d.nx
  ((R.SB.filter fun i => K.contains i && i != ix.q && i != ix.b && i != ix.f && i != ix.c && i != ix.s1 && i != ix.s2).map fun i => (i, TaintRun.AB.known (x.ram.get! i))) ++
    ((exitBits d.nx).filter fun p => R.SB.contains p.1).map fun p => (p.1, (⟨x.ram.get! p.1, p.2⟩ : TaintRun.AB))

/-- **the first table**: the kinds, each with the sound's bytes that the states at the exit know -/
def tableP (sy : Syms) (R : Rt) (d : Data) (x : Machine) : List SState := (kindsP sy d x).map (soundBaseP R d x ++ ·)

/-- the start states of the rows: the states at the exit with a form of the screen buffer, the sound's bytes forgotten, and the timer not 000 (`dg`) -/
def startsK (R : Rt) (d : Data) (e : Machine) : List AS :=
  ((baseK d e).flatMap fun S => d.xshape.map fun r => refine r S).map fun S => StepWrites.retag false ({ StepWrites.forgetAll R.SB S with dg := true } : AS)

/-- what the rows with tables have in common: the rows of the time, and the search keeps the sound's bytes apart -/
def soundCtx (c : Ctx) (R : Rt) : Ctx := { c with keep := c.keep ++ R.SB }

/-- the sound routine of the rows from `c` -/
def rtc (c : Ctx) (d : Data) (e : Machine) : Rt := rtOf c.sy d.nx e

/-- the context of the rows with tables -/
def ctxK (c : Ctx) (d : Data) (e : Machine) : Ctx := soundCtx c (rtc c d e)

/-- the second table of the frame with `k` frames left. On the first frame after the exit the states with the same bytes of the pause sound are joined: that frame and the
next clear the song's bytes of page 0, and the frames after them do not read the song's other bytes until a new song sets them. On the other frames, as the search finds it. -/
def grpP (ix : PauseIx) (k : Nat) (l : List SState) : List SState :=
  if k == afterF then StepWrites.groupJoin (fun u => u.filter fun p => p.1 == ix.q || p.1 == ix.b || p.1 == ix.f || p.1 == ix.c) l else l

/-- **the rows with tables**, from the states at the exit, one for each value of `left` -/
def rowsKc (c : Ctx) (d : Data) (e : Machine) : List SoundRows.SRow :=
  SoundRows.rowsFromS (ctxK c d e) (rtc c d e) (grpP (pauseIx d.nx)) afterF (startsK (rtc c d e) d e) (tableP c.sy (rtc c d e) d (refX e))

/-- a machine is in the rows with tables -/
def InRowsK (sy : Syms) (nm : Names) (d : Data) (e : Machine) (m : Machine) : Prop :=
  SoundRows.InvS (ctxK (timeCtx sy nm d e) d e) (rtc (timeCtx sy nm d e) d e) (rowsKc (timeCtx sy nm d e) d e) m

/-- **The rows that the room's checks read**: the rows with tables where `left` is 0, each state with the bytes of each state of its table -/
def timeRows (c : Ctx) (d : Data) (e : Machine) : List Row := SoundRows.zeroRows (rtc c d e) (rowsKc c d e)

/-- a machine with `left` 0 in the rows with tables is in these rows (`EndStatement.ctlK`) -/
def InRowsT (sy : Syms) (nm : Names) (d : Data) (e : Machine) (m : Machine) : Prop :=
  InvL (timeCtx sy nm d e) (timeRows (timeCtx sy nm d e) d e) m

/-- the states at the exit: they know the sound's bytes of the first table, as the reference -/
def baseOK (c : Ctx) (d : Data) (e : Machine) : Bool :=
  (baseK d e).all fun S => !S.dg && StepWrites.soundLe S (soundBaseP (rtc c d e) d (refX e))

/-- no state of the rows with tables is paused, and each knows that bits 0 to 6 of the pause byte are 0 -/
def goOK (c : Ctx) (d : Data) (e : Machine) : Bool :=
  (rowsKc c d e).all fun r => r.row.R.all fun S => notPausedK (pauseI d) S && low7K (pauseI d) S

/-- the check of the rows with tables from `c`: the states at the exit, the first table, the frames, control where `left` is 0, no paused state -/
def soundCheckC (c : Ctx) (d : Data) (e : Machine) : Bool :=
  baseOK c d e && SoundRows.headIncl (rowsKc c d e) (tableP c.sy (rtc c d e) d (refX e)) && SoundRows.chainS (ctxK c d e) (rtc c d e) (rowsKc c d e) &&
    zeroCtl c.sy ((rowsKc c d e).map (·.row)) && goOK c d e

/-- the check of the rows with tables -/
def soundCheck (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Bool := soundCheckC (timeCtx sy nm d e) d e

/-! ## The pause through the pipe's frames

The six bytes of the pause are in one of 88 classes at each frame's end of the pipe, for any input (`classesV`). At the entry this is a condition on one state (`PauseV`);
the walk carries it beside the pipe's frames (`pcheck`), and at the exit, which is not paused, it gives the pause part of `QuietP` (`QuietV`), but for the case where the
unpause was pressed on the frame of the exit. -/

/-- the pause timer -/
abbrev pauseTI (d : Data) : Nat := adI d.nx "GamePauseTimer"

/-- **The classes of the pause at a frame's end of the pipe.** Not paused: silent (the queue, the buffer and the flag 0; the counter and the timer any; the pause byte 0
or `0x80`, bit 7 not known); the sound of the unpause with the counter `c` from 1 to one less than the length and the timer `c + 1`; the unpause pressed on this frame
(the timer one more than the length). Paused: the pause pressed on this frame; the pause sound with the counter `c` and the timer `c + 1`; the pause sound over (the
timer 1, then 0). Bit 7 of the pause byte is set by a press and cleared when the timer is 0 and Start is not pressed; its bits 1 to 6 are 0. -/
def classesV (sy : Syms) (d : Data) : List SState :=
  let ix := pauseIx d.nx
  let t := pauseTI d
  let g := pauseI d
  let U := TaintRun.AB.known sy.UnpauseSfxValue.toUInt8
  let P := TaintRun.AB.known sy.PauseSfxValue.toUInt8
  let L := sy.PauseSfxLength.toNat
  let z := TaintRun.AB.known 0
  let gv := fun (v : UInt8) => (g, TaintRun.AB.known v)
  [[(ix.q, z), (ix.b, z), (ix.f, z), (g, ⟨0, 0x7F⟩)]] ++
    ((List.range (L - 1)).map fun j => [(ix.q, z), (ix.b, U), (ix.f, U), (ix.c, TaintRun.AB.known (j + 1).toUInt8), (t, TaintRun.AB.known (j + 2).toUInt8), gv 0x80]) ++
    [[(ix.q, U), (ix.b, z), (ix.f, P), (t, TaintRun.AB.known (L + 1).toUInt8), gv 0x80]] ++
    [[(ix.q, P), (ix.b, z), (t, TaintRun.AB.known (L + 1).toUInt8), gv 0x81]] ++
    ((List.range (L - 1)).map fun j => [(ix.q, z), (ix.b, P), (ix.f, P), (ix.c, TaintRun.AB.known (j + 1).toUInt8), (t, TaintRun.AB.known (j + 2).toUInt8), gv 0x81]) ++
    [[(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (t, TaintRun.AB.known 1), gv 0x81], [(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (t, z), gv 0x81],
     [(ix.q, z), (ix.b, z), (ix.f, P), (ix.c, z), (t, z), gv 1]]

/-- **The condition on the pause at the entry**: one of the classes that are not paused. Silent: the queue, the buffer and the flag 0, the pause byte 0 or `0x80`. Or the
sound of the unpause plays: the buffer and the flag hold the unpause sound's value, the counter is from 1 to one less than the length, the timer is one more than the
counter, the pause byte is `0x80`. Or the unpause was pressed on this frame: the queue holds the unpause sound's value, the buffer 0, the flag the pause sound's value,
the timer one more than the length, the pause byte `0x80`. -/
def PauseV (sy : Syms) (d : Data) (m : Machine) : Prop :=
  ((m.ram.get! (pauseI d) = 0 ∨ m.ram.get! (pauseI d) = 0x80) ∧ m.ram.get! (pauseIx d.nx).q = 0 ∧ m.ram.get! (pauseIx d.nx).b = 0 ∧ m.ram.get! (pauseIx d.nx).f = 0) ∨
  (m.ram.get! (pauseI d) = 0x80 ∧ m.ram.get! (pauseIx d.nx).q = 0 ∧ m.ram.get! (pauseIx d.nx).b = sy.UnpauseSfxValue.toUInt8 ∧
    m.ram.get! (pauseIx d.nx).f = sy.UnpauseSfxValue.toUInt8 ∧ 1 ≤ (m.ram.get! (pauseIx d.nx).c).toNat ∧ (m.ram.get! (pauseIx d.nx).c).toNat < sy.PauseSfxLength.toNat ∧
    (m.ram.get! (pauseTI d)).toNat = (m.ram.get! (pauseIx d.nx).c).toNat + 1) ∨
  (m.ram.get! (pauseI d) = 0x80 ∧ m.ram.get! (pauseIx d.nx).q = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! (pauseIx d.nx).b = 0 ∧
    m.ram.get! (pauseIx d.nx).f = sy.PauseSfxValue.toUInt8 ∧ (m.ram.get! (pauseTI d)).toNat = sy.PauseSfxLength.toNat + 1)

/-- `PauseV`, for a program -/
def pauseVB (sy : Syms) (d : Data) (m : Machine) : Bool :=
  let ix := pauseIx d.nx
  let L := sy.PauseSfxLength.toNat
  let U := sy.UnpauseSfxValue.toUInt8
  let g := m.ram.get! (pauseI d)
  let c := (m.ram.get! ix.c).toNat
  let t := (m.ram.get! (pauseTI d)).toNat
  ((g == 0 || g == 0x80) && m.ram.get! ix.q == 0 && m.ram.get! ix.b == 0 && m.ram.get! ix.f == 0) ||
  (g == 0x80 && m.ram.get! ix.q == 0 && m.ram.get! ix.b == U && m.ram.get! ix.f == U && decide (1 ≤ c) && decide (c < L) && t == c + 1) ||
  (g == 0x80 && m.ram.get! ix.q == U && m.ram.get! ix.b == 0 && m.ram.get! ix.f == sy.PauseSfxValue.toUInt8 && t == L + 1)

/-- **The pause at the exit**: silent with the flag 0; or the unpause sound with the counter from 1 to one less than the length; or the unpause pressed on this frame -/
def QuietV (sy : Syms) (d : Data) (m : Machine) : Prop :=
  (m.ram.get! (pauseIx d.nx).q = 0 ∧ m.ram.get! (pauseIx d.nx).b = 0 ∧ m.ram.get! (pauseIx d.nx).f = 0) ∨
  (m.ram.get! (pauseIx d.nx).q = 0 ∧ m.ram.get! (pauseIx d.nx).b = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! (pauseIx d.nx).f = sy.UnpauseSfxValue.toUInt8 ∧
    1 ≤ (m.ram.get! (pauseIx d.nx).c).toNat ∧ (m.ram.get! (pauseIx d.nx).c).toNat < sy.PauseSfxLength.toNat) ∨
  (m.ram.get! (pauseIx d.nx).q = sy.UnpauseSfxValue.toUInt8 ∧ m.ram.get! (pauseIx d.nx).b = 0 ∧ m.ram.get! (pauseIx d.nx).f = sy.PauseSfxValue.toUInt8)

/-- **What the exit still asks**: the queue of the pause sound as at the reference `x` (so the unpause was not pressed on the frame of the exit), and when the buffer of
the pause sound is as at `x` (silent), the two squares' effects as at `x` and the song's bytes a row of the song. With `QuietV` this gives `QuietP` (`quietP_of_V`). -/
def QuietRest (d : Data) (x m : Machine) : Prop :=
  m.ram.get! (pauseIx d.nx).q = x.ram.get! (pauseIx d.nx).q ∧
  (m.ram.get! (pauseIx d.nx).b = x.ram.get! (pauseIx d.nx).b →
    m.ram.get! (pauseIx d.nx).s1 = x.ram.get! (pauseIx d.nx).s1 ∧ m.ram.get! (pauseIx d.nx).s2 = x.ram.get! (pauseIx d.nx).s2 ∧ SongAt d.song m)

/-- `QuietRest`, for a program -/
def quietRestB (d : Data) (x m : Machine) : Bool :=
  let ix := pauseIx d.nx
  m.ram.get! ix.q == x.ram.get! ix.q && (m.ram.get! ix.b != x.ram.get! ix.b ||
    (m.ram.get! ix.s1 == x.ram.get! ix.s1 && m.ram.get! ix.s2 == x.ram.get! ix.s2 && d.song.any fun q => q.all fun p => m.ram.get! p.1 == p.2))

/-- the routine of the pause from the reference entry: the first call of the sound routine in the interrupt, and the body's stack pointer three below the idle loop's -/
def prOf (sy : Syms) (d : Data) (e : Machine) : PR :=
  let ix := pauseIx d.nx
  { call := jsrAt e sy.NonMaskableInterrupt sy.SoundEngine 512, sb := e.s - 3, SB := [ix.q, ix.b, ix.f, ix.c, pauseTI d, pauseI d], g := pauseI d }

/-- the two tables of the pipe's frames with the class beside the walk, without the game timer: the walk of round 10, for the programs only (`pipe-pause-check`,
`entry-need`); the check uses `cfgRqT` and `cfgOqT` -/
def cfgRq (sy : Syms) (d : Data) (e : Machine) : ZCfg :=
  pcfgOf d.places d.jump (envOf d e) (prOf sy d e) (classesV sy d) d.ckeys d.keep [(pauseI d, 1)] d.hints (startsP d e)
def cfgOq (sy : Syms) (d : Data) (e : Machine) : ZCfg :=
  pcfgOf d.places d.jump (envOf d e) (prOf sy d e) (classesV sy d) d.ckeys (pauseI d :: d.keep) [(pauseI d, 1)] d.hints ((startsP d e).map (toOne (envOf d e)))

/-- the state `S` with `dg`: in the environment of the time (`timeEnv`, the bytes `D` are the game timer's three digits), the game timer is not 000 -/
def withT (S : AS) : AS := { S with dg := true }

/-- the start states of the pipe's frames, with the game timer not 000 -/
def startsPT (d : Data) (e : Machine) : List AS := (startsP d e).map withT

/-- the states at the exit, with the game timer not 000 -/
def baseKT (d : Data) (e : Machine) : List AS := (baseK d e).map withT

/-- **the two tables of the pipe's frames with the class beside the walk and the game timer's digits as the walk's bytes `D`**: the counter followed, and the counter at 1 -/
def cfgRqT (sy : Syms) (d : Data) (e : Machine) : ZCfg :=
  pcfgOf d.places d.jump (timeEnv d e) (prOf sy d e) (classesV sy d) d.ckeys d.keep [(pauseI d, 1)] d.hints (startsPT d e)
def cfgOqT (sy : Syms) (d : Data) (e : Machine) : ZCfg :=
  pcfgOf d.places d.jump (timeEnv d e) (prOf sy d e) (classesV sy d) d.ckeys (pauseI d :: d.keep) [(pauseI d, 1)] d.hints ((startsPT d e).map (toOne (timeEnv d e)))

/-- the start states and the states at the exit do not have `dg` before `withT` sets it -/
def dgOff (d : Data) (e : Machine) : Bool := (startsP d e).all (fun S => !S.dg) && (baseK d e).all (fun S => !S.dg)

/-- **the check of the pipe's frames with the pause in a class and the game timer.** The walk has the game timer's digits as its bytes `D`, and `dg` in its start states
and in its states at the exit. A store to a digit clears `dg`, and a state without `dg` is under no start state and no state at the exit: so the check passes only if no
path of the pipe's frames stores to the digits. -/
def pipeCheckV (sy : Syms) (nm : Names) (d : Data) (e : Machine) : Bool :=
  dgOff d e &&
    pcheck (cfgRqT sy d e) (cfgOqT sy d e) (prOf sy d e) (classesV sy d) (timeEnv d e) (pauseI d) (startsPT d e) (baseKT d e) [] (exitBytes sy nm (refX e))

/-- the reference at the exit is silent, the unpause sound's value is not 0, and the length of the pause sound is below 256 -/
def exitVOK (sy : Syms) (d : Data) (e : Machine) : Bool :=
  (refX e).ram.get! (pauseIx d.nx).q == 0 && (refX e).ram.get! (pauseIx d.nx).b == 0 && sy.UnpauseSfxValue.toUInt8 != 0 && decide (sy.PauseSfxLength.toNat < 256)

section
variable {sy : Syms} {d : Data} {e m : Machine}

theorem and_ffV (x : UInt8) : x &&& 0xFF = x := by
  apply UInt8.toNat_inj.1
  rw [UInt8.toNat_and]
  have : (0xFF : UInt8).toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt x.toNat_lt

theorem eq_of_knownV {v x : UInt8} (h : (TaintRun.AB.known v).mem x) : x = v := by
  have h' : x &&& 0xFF = v &&& 0xFF := h
  rwa [and_ffV, and_ffV] at h'

theorem known_of_eqV {v x : UInt8} (h : x = v) : (TaintRun.AB.known v).mem x := by
  rw [h]
  exact TaintRun.mem_known_self v

theorem toUInt8_of_toNatV {x : UInt8} {n : Nat} (h : x.toNat = n) : x = n.toUInt8 := by
  rw [← h]
  exact (UInt8.ofNat_toNat).symm

theorem toNat_of_toUInt8V {x : UInt8} {n : Nat} (h : x = n.toUInt8) (hn : n < 256) : x.toNat = n := by
  rw [h]
  exact Nat.mod_eq_of_lt hn

/-- **A machine with the condition at the entry has the bytes of one of the classes** -/
theorem class_of_pauseV (h : PauseV sy d m) : ∃ t ∈ classesV sy d, SIn t m := by
  rcases h with ⟨hg, hq, hb, hf⟩ | ⟨hg, hq, hb, hf, hc1, hc2, ht⟩ | ⟨hg, hq, hb, hf, ht⟩
  · refine ⟨[((pauseIx d.nx).q, TaintRun.AB.known 0), ((pauseIx d.nx).b, TaintRun.AB.known 0), ((pauseIx d.nx).f, TaintRun.AB.known 0), (pauseI d, ⟨0, 0x7F⟩)],
      by simp [classesV], ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact known_of_eqV hq
    · exact known_of_eqV hb
    · exact known_of_eqV hf
    · show m.ram.get! (pauseI d) &&& 0x7F = 0 &&& 0x7F
      rcases hg with hg | hg <;> rw [hg] <;> decide
  · have hj : (m.ram.get! (pauseIx d.nx).c).toNat - 1 < sy.PauseSfxLength.toNat - 1 := by omega
    refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_map.2 ⟨(m.ram.get! (pauseIx d.nx).c).toNat - 1, List.mem_range.2 hj, rfl⟩)))))))))), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact known_of_eqV hq
    · exact known_of_eqV hb
    · exact known_of_eqV hf
    · exact known_of_eqV (x := m.ram.get! (pauseIx d.nx).c) (toUInt8_of_toNatV (by omega))
    · exact known_of_eqV (x := m.ram.get! (pauseTI d)) (toUInt8_of_toNatV (by omega))
    · exact known_of_eqV hg
  · refine ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr List.mem_cons_self))))))), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact known_of_eqV hq
    · exact known_of_eqV hb
    · exact known_of_eqV hf
    · exact known_of_eqV (x := m.ram.get! (pauseTI d)) (toUInt8_of_toNatV ht)
    · exact known_of_eqV hg

/-- **A machine that is not paused, with the bytes of a class, has the pause as `QuietV` says** (the length of the sound is below 256) -/
theorem quietV_of_class (hL : sy.PauseSfxLength.toNat < 256) {t : SState} (ht : t ∈ classesV sy d) (hm : SIn t m) (hnp : m.ram.get! (pauseI d) &&& 1 ≠ 1) :
    QuietV sy d m := by
  have paused : ∀ v : UInt8, v &&& 1 = 1 → (pauseI d, TaintRun.AB.known v) ∈ t → False := fun v hv hin => by
    have := eq_of_knownV (hm _ hin)
    rw [this] at hnp
    exact hnp hv
  unfold classesV at ht
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_map, List.mem_range] at ht
  rcases ht with (((((rfl | ⟨j, hj, rfl⟩) | rfl) | rfl) | ⟨j, hj, rfl⟩) | (rfl | rfl | rfl))
  · exact Or.inl ⟨eq_of_knownV (hm ((pauseIx d.nx).q, TaintRun.AB.known 0) (by simp)), eq_of_knownV (hm ((pauseIx d.nx).b, TaintRun.AB.known 0) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).f, TaintRun.AB.known 0) (by simp))⟩
  · have hc : m.ram.get! (pauseIx d.nx).c = (j + 1).toUInt8 := eq_of_knownV (hm ((pauseIx d.nx).c, TaintRun.AB.known (j + 1).toUInt8) (by simp))
    have hc' := toNat_of_toUInt8V hc (by omega)
    exact Or.inr (Or.inl ⟨eq_of_knownV (hm ((pauseIx d.nx).q, TaintRun.AB.known 0) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).b, TaintRun.AB.known sy.UnpauseSfxValue.toUInt8) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).f, TaintRun.AB.known sy.UnpauseSfxValue.toUInt8) (by simp)), by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨eq_of_knownV (hm ((pauseIx d.nx).q, TaintRun.AB.known sy.UnpauseSfxValue.toUInt8) (by simp)),
      eq_of_knownV (hm ((pauseIx d.nx).b, TaintRun.AB.known 0) (by simp)), eq_of_knownV (hm ((pauseIx d.nx).f, TaintRun.AB.known sy.PauseSfxValue.toUInt8) (by simp))⟩)
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 0x81 (by decide) (by simp)).elim
  · exact (paused 1 (by decide) (by simp)).elim

/-- **The pause at the exit and what the exit still asks give `QuietP`** -/
theorem quietP_of_V (hx : exitVOK sy d e = true) (hq : QuietV sy d m) (hr : QuietRest d (refX e) m) : QuietP sy d (refX e) m := by
  simp only [exitVOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨hxq, hxb⟩, hU⟩, _⟩ := hx
  rcases hq with ⟨hq0, hb0, hf0⟩ | ⟨hq0, hb0, hf0, hc1, hc2⟩ | ⟨hq0, _, _⟩
  · have hb : m.ram.get! (pauseIx d.nx).b = (refX e).ram.get! (pauseIx d.nx).b := by rw [hb0, hxb]
    obtain ⟨h1, h2, h3⟩ := hr.2 hb
    exact Or.inl ⟨hr.1, hb, hf0, h1, h2, h3⟩
  · exact Or.inr ⟨hr.1, hb0, hf0, hc1, hc2⟩
  · have := hr.1
    rw [hq0, hxq] at this
    exact absurd this hU

end

/-- the two tables of the pipe's frames: the counter followed, and the counter at 1. The low bit of the pause byte is in the key. -/
def cfgRp (d : Data) (e : Machine) : ZCfg := zcfgOf d.places d.jump (envOf d e) d.ckeys d.keep [(pauseI d, 1)] d.hints (startsP d e)
def cfgOp (d : Data) (e : Machine) : ZCfg :=
  zcfgOf d.places d.jump (envOf d e) d.ckeys (adI d.nx "GamePauseStatus" :: d.keep) [(pauseI d, 1)] d.hints ((startsP d e).map (toOne (envOf d e)))

/-- the states at the exit, with the bytes `quietQ`, are states of the rows of the time: the old condition at the exit still gives them -/
def baseIncl (d : Data) (e : Machine) : Bool := (baseK d e).all fun D => (baseOf d e).any fun D0 => (refine (quietQ d e) D).le D0

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
    zcheck (cfgRp d e) (cfgOp d e) E (pauseI d) st (baseK d e) [] (exitBytes sy nm x) &&
    es.all (fun m => entryOK E (refsP d e) timerF m) &&
    (rowsA c d e ++ rowsB c d e).all (fun r => r.R.all (notPausedK (pauseI d))) && timeCheck sy nm d e &&
    baseIncl d e && soundCheck sy nm d e && pipeCheckV sy nm d e && exitVOK sy d e

/-- **The condition on the state at the entry.** The frame has ended in the idle loop, the listed bytes are those of the reference, the timer is at least its first value, and some bytes have the reference's bits. All other bytes are free. -/
abbrev Entry (d : Data) (e : Machine) (m : Machine) : Prop :=
  SideChangeBound.EntryCond (envOf d e) (refsP d e) timerF m ∧ BitsAt d.bits e m

/-- **The condition at the entry, with the pause**: `Entry`, and the six bytes of the pause in one of the classes that are not paused (`PauseV`). The press of Start on
the title and the frames from control give it (`EntryKeep.entryV_of_title`). -/
structure EntryV (sy : Syms) (d : Data) (e : Machine) (m : Machine) : Prop where
  entry : Entry d e m
  pause : PauseV sy d m

/-- **The condition on the state at the exit.** The frame has ended in the idle loop, the listed bytes are those of the reference, the game is not paused, the song's bytes are a row of the table,
and some bytes have the reference's bits. All other bytes are free. -/
abbrev Exit (d : Data) (e : Machine) (m : Machine) : Prop :=
  ExitCond (envOf d e) (refX e) (exitKnown d.nx) (adI d.nx "GamePauseStatus") m ∧ SongAt d.song m ∧ SongAt d.xshape m ∧ BitsAt (exitBits d.nx) (refX e) m

/-- the state during the pipe -/
abbrev During (d : Data) (e : Machine) : Machine → Prop := InvAt (envOf d e) (startsP d e)

/-- a machine is in the rows of one of the two cases -/
def InRows (sy : Syms) (nm : Names) (d : Data) (e : Machine) (m : Machine) : Prop :=
  InvL (ctxOf sy nm d e) (rowsA (ctxOf sy nm d e) d e) m ∨ InvL (ctxOf sy nm d e) (rowsB (ctxOf sy nm d e) d e) m

/-- the bytes that say where the change is, in the reference at the exit -/
abbrev exitQ (sy : Syms) (nm : Names) (e : Machine) : List (Nat × UInt8) := exitBytes sy nm (refX e)

/-- **the state during the pipe, with the pause in a class and the game timer not 000** -/
abbrev DuringV (sy : Syms) (d : Data) (e : Machine) (m : Machine) : Prop := During d e m ∧ (∃ t ∈ classesV sy d, SIn t m) ∧ TimerOK d.nx m

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
  /-- **a frame of the pipe that ends paused takes nothing off `left`** -/
  paused : ∀ m, During d e m → ∀ i, (∀ j, PlaceOK d.places (PipeEntryRule.trace m i j)) → Paused d (frame m i) → leftP sy nm e m ≤ leftP sy nm e (frame m i)
  /-- no machine in the rows is paused -/
  rowsGo : ∀ m, InRows sy nm d e m → ¬ Paused d m
  /-- one frame of the pipe: a frame that leaves the pipe, with the conditions at the exit and the time not up, is in the rows of the time -/
  stepT : ∀ m, During d e m → ∀ i, (∀ j, PlaceOK d.places (PipeEntryRule.trace m i j)) →
    During d e (frame m i) ∨ (ExitAt (exitQ sy nm e) (frame m i) ∧
      (Quiet (quietQ d e) (frame m i) → SongAt d.song (frame m i) → SongAt d.xshape (frame m i) → TimeOK d.nx (frame m i) → InRowsTO sy nm d e (frame m i)))
  /-- a frame in the rows of the time: `left` is 0 already, or the machine stays in these rows -/
  rowsT : ∀ m, InRowsTO sy nm d e m → ∀ i, (coreFrame sy sy.EngVerticalPipe m = true → noStart i = true) → leftP sy nm e m = 0 ∨ InRowsTO sy nm d e (frame m i)
  /-- in the rows of the time, `left` is 0 only with control -/
  zeroT : ∀ m, InRowsTO sy nm d e m → leftP sy nm e m = 0 → controllable sy m = true
  /-- **one frame of the pipe, with the rows with tables**: a frame that leaves the pipe, with the pause sound of `QuietP`, a form of the screen buffer and the game timer
  not 000 at the exit, is in the rows with tables -/
  stepK : ∀ m, During d e m → ∀ i, (∀ j, PlaceOK d.places (PipeEntryRule.trace m i j)) →
    During d e (frame m i) ∨ (ExitAt (exitQ sy nm e) (frame m i) ∧
      (QuietP sy d (refX e) (frame m i) → SongAt d.xshape (frame m i) → TimerOK d.nx (frame m i) → InRowsK sy nm d e (frame m i)))
  /-- **a frame in the rows with tables**: `left` is 0 already, or the machine stays in the rows and `left` falls by at most one -/
  rowsK : ∀ m, InRowsK sy nm d e m → ∀ i, (coreFrame sy sy.EngVerticalPipe m = true → noStart i = true) →
    leftP sy nm e m = 0 ∨ (InRowsK sy nm d e (frame m i) ∧ leftP sy nm e m ≤ leftP sy nm e (frame m i) + 1)
  /-- in the rows with tables, `left` is 0 only with control -/
  zeroK : ∀ m, InRowsK sy nm d e m → leftP sy nm e m = 0 → controllable sy m = true
  /-- no machine in the rows with tables is paused -/
  goK : ∀ m, InRowsK sy nm d e m → ¬ Paused d m
  /-- a machine in the rows with tables where `left` is 0 is in the rows that the room's checks read -/
  ctlK : ∀ m, InRowsK sy nm d e m → leftP sy nm e m = 0 → InRowsT sy nm d e m
  /-- **one frame of the pipe with the pause in a class and the game timer not 000**, for any input, when every instruction of the frame meets the condition at the
  places: the machine stays in the pipe with the pause in a class and the timer not 000 (no step of the pipe's frames stores to the timer's digits), or it leaves the
  routine with the pause as `QuietV` says and the timer not 000, and then with `QuietP` and a form of the screen buffer it is in the rows with tables -/
  pauseStep : ∀ m, DuringV sy d e m → ∀ i, (∀ j, PlaceOK d.places (PipeEntryRule.trace m i j)) →
    DuringV sy d e (frame m i) ∨
    (ExitAt (exitQ sy nm e) (frame m i) ∧ QuietV sy d (frame m i) ∧ TimerOK d.nx (frame m i) ∧
      (QuietP sy d (refX e) (frame m i) → SongAt d.xshape (frame m i) → InRowsK sy nm d e (frame m i)))
  /-- the pause at the exit and what the exit still asks give `QuietP` -/
  pauseExit : ∀ m, QuietV sy d m → QuietRest d (refX e) m → QuietP sy d (refX e) m
  /-- **in the rows with tables, bits 0 to 6 of the pause byte are 0** -/
  bitsK : ∀ m, InRowsK sy nm d e m → m.ram.get! (pauseI d) &&& 0x7F = 0

/-- a machine in rows whose states know that the game is not paused is not paused -/
theorem not_paused_rows {c : Ctx} {g : Nat} : ∀ (l : List Row), (∀ r ∈ l, ∀ S ∈ r.R, notPausedK g S = true) → ∀ {m : Machine}, InvL c l m → m.ram.get! g &&& 1 ≠ 1
  | [], _, _, h => h.elim
  | r :: t, hl, _, h => by
    rcases h with ⟨S, hS, hs⟩ | h
    · exact not_paused_of hs (hl r List.mem_cons_self S hS)
    · exact not_paused_rows t (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) h

/-- the first row of the rows of the time holds the states it is built from -/
theorem in_rowsT {sy : Syms} {nm : Names} {d : Data} {e : Machine} {m : Machine} (hq : SongAt d.song m) (hr : SongAt d.xshape m) (ht : TimeOK d.nx m)
    (hb : ∀ D ∈ baseOf d e, D.dg = false) (h : ∃ D ∈ baseOf d e, Sim (envOf d e) (m.frame, 2) D m) : InRowsTO sy nm d e m := by
  obtain ⟨D, hD, hs⟩ := h
  obtain ⟨r, hr1, hr2⟩ := hr
  obtain ⟨q, hq1, hq2⟩ := hq
  have hs1 : Sim (timeEnv d e) (m.frame, 2) D m := sim_D hs (hb D hD)
  have hs2 := sim_refines hq2 (sim_refines hr2 (sim_refine hs1 (i := adI d.nx "PauseModeFlag") (v := TaintRun.AB.known 0) (by rw [ht.flag]; exact TaintRun.mem_known_self _)))
  have hdg : (timeEnv d e).D.any (fun j => m.ram.get! j != 0) = true := by
    obtain ⟨j, hj, hne⟩ := ht.timer
    exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
  have hs3 : Sim (timeEnv d e) (m.frame, 2) ({ refine q (refine r (D.setK (adI d.nx "PauseModeFlag") (TaintRun.AB.known 0))) with dg := true } : AS) m :=
    { hs2 with dg := fun _ => hdg }
  refine Or.inl ⟨_, ?_, hs3⟩
  exact List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨D, hD, rfl⟩, List.mem_flatMap.2 ⟨r, hr1, List.mem_map.2 ⟨q, hq1, rfl⟩⟩⟩, rfl⟩

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

/-- a machine with the condition at the exit is in a start state of the rows -/
theorem exit_base {d : Data} {e m : Machine} (hV : exitStartsOK (refX e) (exitKnown d.nx) = true) (h : Exit d e m) :
    ∃ D ∈ baseOf d e, Sim (envOf d e) (m.frame, 2) D m := by
  obtain ⟨S, hS, hs⟩ := exit_cover hV rfl h.1
  exact ⟨_, List.mem_map.2 ⟨S, hS, rfl⟩, sim_mask h.2.2.2 hs⟩

/-- with the bytes `quietQ`, a state at the exit of `baseK` is under a state of `baseOf` -/
theorem base_of_K {d : Data} {e m : Machine} (hI : baseIncl d e = true) (hq : Quiet (quietQ d e) m)
    (h : ∃ D ∈ baseK d e, Sim (envOf d e) (m.frame, 2) D m) : ∃ D ∈ baseOf d e, Sim (envOf d e) (m.frame, 2) D m := by
  obtain ⟨D, hD, hs⟩ := h
  obtain ⟨D0, hD0, hle⟩ := List.any_eq_true.1 (List.all_eq_true.1 hI D hD)
  exact ⟨D0, hD0, TaintRun.sim_le hle (sim_refines hq hs)⟩

/-- **A machine with `QuietP` has the bytes of one of the kinds** -/
theorem kinds_of_quietP {sy : Syms} {d : Data} {x m : Machine} (h : QuietP sy d x m) : ∃ kd ∈ kindsP sy d x, SIn kd m := by
  unfold kindsP
  rcases h with ⟨hq, hb, hf, h1, h2, r, hr, hm⟩ | ⟨hq, hb, hf, hc1, hc2⟩
  · refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨r, hr, rfl⟩), SoundRows.sIn_append ?_ (SoundRows.sIn_ofRow hm)⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact SoundRows.mem_eq hq
    · exact SoundRows.mem_eq hb
    · exact SoundRows.mem_eq hf
    · exact SoundRows.mem_eq h1
    · exact SoundRows.mem_eq h2
  · refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨(m.ram.get! (pauseIx d.nx).c).toNat - 1, List.mem_range.2 (by omega), rfl⟩), ?_⟩
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact SoundRows.mem_eq hq
    · exact SoundRows.mem_eq hb
    · exact SoundRows.mem_eq hf
    · refine SoundRows.mem_eq ?_
      have e : (m.ram.get! (pauseIx d.nx).c).toNat - 1 + 1 = (m.ram.get! (pauseIx d.nx).c).toNat := by omega
      rw [e]
      exact (UInt8.ofNat_toNat).symm

/-- **The old condition at the exit gives the new one**: the bytes `quietQ`, a row of the song and the sound's pause flag 0 (`TimeOK.flag`) give `QuietP` -/
theorem quietP_of_quiet {sy : Syms} {d : Data} {e m : Machine} (hq : Quiet (quietQ d e) m) (hs : SongAt d.song m)
    (hf : m.ram.get! (adI d.nx "PauseModeFlag") = 0) : QuietP sy d (refX e) m := by
  have key : ∀ n, n ∈ ["PauseSoundBuffer", "PauseSoundQueue", "Square1SoundBuffer", "Square2SoundBuffer"] →
      m.ram.get! (adI d.nx n) = (refX e).ram.get! (adI d.nx n) := by
    intro n hn
    refine hq (adI d.nx n, (refX e).ram.get! (adI d.nx n)) (List.mem_map.2 ⟨adI d.nx n, ?_, rfl⟩)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> simp [bytesOf, quietA, adI, UInt16.toNat_and]
  exact Or.inl ⟨key _ (by simp), key _ (by simp), hf, key _ (by simp), key _ (by simp), hs⟩

/-- rows read with a context of the same environment -/
theorem invL_congr {c c' : Ctx} (he : c.E = c'.E) : ∀ {L : List Row} {m : Machine}, InvL c L m → InvL c' L m
  | [], _, h => h.elim
  | r :: t, m, h => by
    rcases h with ⟨S, hS, hs⟩ | h
    · exact Or.inl ⟨S, hS, by rw [← he]; exact hs⟩
    · exact Or.inr (invL_congr he h)

/-- a state with the bytes `SB` forgotten and `dg` covers a machine whose game timer is not 000 -/
theorem sim_start {E : Env} {F : Nat × UInt8} (SB : List Nat) {D : AS} {m : Machine} (hs : Sim E F D m) (hdg : E.D.any (fun j => m.ram.get! j != 0) = true) :
    Sim E F (StepWrites.retag false ({ StepWrites.forgetAll SB D with dg := true } : AS)) m :=
  StepWrites.sim_retag false { StepWrites.sim_forgetAll SB hs with dg := fun _ => hdg }

/-- **A machine at the exit is in the rows with tables**: a state of `baseK` covers it, the pause sound is as `QuietP` says, the screen buffer has a form of the table, and the game
timer is not 000 -/
theorem inRowsK_of_exit {sy : Syms} {nm : Names} {d : Data} {e m : Machine} (hc : soundCheck sy nm d e = true)
    (h : ∃ D ∈ baseK d e, Sim (envOf d e) (m.frame, 2) D m) (hq : QuietP sy d (refX e) m) (hr : SongAt d.xshape m) (ht : TimerOK d.nx m) :
    InRowsK sy nm d e m := by
  unfold soundCheck soundCheckC at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hb, hh⟩, _⟩, _⟩, _⟩ := hc
  obtain ⟨D, hD, hs⟩ := h
  obtain ⟨r, hr1, hr2⟩ := hr
  have hbD : D.dg = false ∧ StepWrites.soundLe D (soundBaseP (rtc (timeCtx sy nm d e) d e) d (refX e)) = true := by
    have h2 := List.all_eq_true.1 hb D hD
    rw [Bool.and_eq_true] at h2
    refine ⟨?_, h2.2⟩
    cases hdd : D.dg with
    | false => rfl
    | true =>
      rw [hdd] at h2
      cases h2.1
  have hs1 : Sim (timeEnv d e) (m.frame, 2) D m := sim_D hs hbD.1
  have hs2 := sim_refines hr2 hs1
  have hdg : (timeEnv d e).D.any (fun j => m.ram.get! j != 0) = true := by
    obtain ⟨j, hj, hne⟩ := ht
    exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩
  have hs3 := sim_start (rtc (timeCtx sy nm d e) d e).SB hs2 hdg
  obtain ⟨kd, hkd, hkm⟩ := kinds_of_quietP hq
  have hS : StepWrites.retag false ({ StepWrites.forgetAll (rtc (timeCtx sy nm d e) d e).SB (refine r D) with dg := true } : AS) ∈
      startsK (rtc (timeCtx sy nm d e) d e) d e :=
    List.mem_map.2 ⟨refine r D, List.mem_flatMap.2 ⟨D, hD, List.mem_map.2 ⟨r, hr1, rfl⟩⟩, rfl⟩
  have hT : soundBaseP (rtc (timeCtx sy nm d e) d e) d (refX e) ++ kd ∈ tableP (timeCtx sy nm d e).sy (rtc (timeCtx sy nm d e) d e) d (refX e) :=
    List.mem_map.2 ⟨kd, hkd, rfl⟩
  unfold InRowsK
  unfold rowsKc at hh ⊢
  exact SoundRows.inv_headS (grpP (pauseIx d.nx)) afterF _ _ hh hS hs3 rfl hT (SoundRows.sIn_append (StepWrites.sIn_of_le hs hbD.2) hkm)

section
variable {d : Data} {e m : Machine} {F : Nat × UInt8}

/-- in the environment of the time, a state with `dg` covers only machines whose game timer is not 000 -/
theorem timerOK_of_simT {A : AS} (hs : Sim (timeEnv d e) F A m) (hd : A.dg = true) : TimerOK d.nx m := by
  obtain ⟨j, hj, hne⟩ := List.any_eq_true.1 (hs.dg hd)
  exact ⟨j, hj, by simpa using hne⟩

/-- a state of the time with `dg` set covers what the state without it covers in the walk's own environment -/
theorem sim_of_simT {S : AS} (hs : Sim (timeEnv d e) F (withT S) m) (hd : S.dg = false) : Sim (envOf d e) F S m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hs.pad, hs.padShift, hs.strobe, hs.halted,
    hs.trk, hs.size, hs.ram, (fun h => by rw [hd] at h; cases h), hs.szR, hs.szK, hs.fr, hs.rkv⟩

/-- and back, when the game timer is not 000 -/
theorem simT_of_sim {S : AS} (hs : Sim (envOf d e) F S m) (ht : TimerOK d.nx m) : Sim (timeEnv d e) F (withT S) m :=
  ⟨hs.a, hs.x, hs.y, hs.p, hs.s, hs.pc, hs.prg, hs.mask, hs.ppuCtrl, hs.ppuMask, hs.vb, hs.nmi, hs.s0, hs.lo, hs.hi, hs.lim, hs.pad, hs.padShift, hs.strobe, hs.halted,
    hs.trk, hs.size, hs.ram, (fun _ => by obtain ⟨j, hj, hne⟩ := ht; exact List.any_eq_true.2 ⟨j, hj, by simpa using hne⟩), hs.szR, hs.szK, hs.fr, hs.rkv⟩

theorem toOne_withT (S : AS) : toOne (timeEnv d e) (withT S) = withT (toOne (envOf d e) S) := rfl

/-- **The state during the pipe with the game timer not 000 is a state of the walk with the timer**: its start states have `dg` -/
theorem invT_of (h : During d e m) (ht : TimerOK d.nx m) : InvAt (timeEnv d e) (startsPT d e) m := by
  obtain ⟨S, hS, hc⟩ := h
  refine ⟨withT S, List.mem_map.2 ⟨S, hS, rfl⟩, ?_⟩
  rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact Or.inl ⟨c1, simT_of_sim c2 ht⟩
  · refine Or.inr ⟨c1, ?_⟩
    rw [toOne_withT]
    exact simT_of_sim c2 ht

/-- **and back**: a machine of the walk with the timer is in the state during the pipe, and its game timer is not 000 -/
theorem of_invT (h0 : ∀ S ∈ startsP d e, S.dg = false) (h : InvAt (timeEnv d e) (startsPT d e) m) : During d e m ∧ TimerOK d.nx m := by
  obtain ⟨S', hS', hc⟩ := h
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hS'
  rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · exact ⟨⟨S, hS, Or.inl ⟨c1, sim_of_simT c2 (h0 S hS)⟩⟩, timerOK_of_simT c2 rfl⟩
  · rw [toOne_withT] at c2
    exact ⟨⟨S, hS, Or.inr ⟨c1, sim_of_simT c2 (show S.dg = false from h0 S hS)⟩⟩, timerOK_of_simT c2 rfl⟩

end

theorem endStatement_of_check {sy : Syms} {nm : Names} {d : Data} {e : Machine} {es : List Machine} (h : endCheck sy nm d e es = true) : EndStatement sy nm d e es := by
  simp only [endCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, hI⟩, hK⟩, hV⟩, hX⟩ := h
  have hLen : sy.PauseSfxLength.toNat < 256 := by
    have hX' := hX
    simp only [exitVOK, Bool.and_eq_true, decide_eq_true_eq] at hX'
    exact hX'.2
  simp only [pipeCheckV, Bool.and_eq_true] at hV
  obtain ⟨hdO, hV⟩ := hV
  simp only [dgOff, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hdO
  obtain ⟨hdS, hdB⟩ := hdO
  have hZq : POK (cfgRqT sy d e) (cfgOqT sy d e) (prOf sy d e) (classesV sy d) (timeEnv d e) (pauseI d) (startsPT d e) (baseKT d e) [] (exitBytes sy nm (refX e)) := by
    simp only [pcheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at hV
    obtain ⟨⟨⟨⟨⟨⟨⟨z1, z1'⟩, z1''⟩, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩ := hV
    refine ⟨z1, z1', z1'', rfl, rfl, rfl, rfl, rfl, fun S hS => ?_, z3, z4, z5, z6⟩
    have := z2 S hS
    exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  simp only [timeCheck, Bool.and_eq_true] at h12
  obtain ⟨hTc, hTz⟩ := h12
  have hK' := hK
  unfold soundCheck soundCheckC at hK'
  simp only [Bool.and_eq_true] at hK'
  obtain ⟨⟨⟨⟨_, _⟩, hKc⟩, hKz⟩, hKn⟩ := hK'
  have hEt : (timeCtx sy nm d e).E.pad = TaintRun.AB.top := rfl
  have hE : (ctxOf sy nm d e).E.pad = TaintRun.AB.top := rfl
  have hEp : (envOf d e).pad = TaintRun.AB.top := rfl
  have hL := leftOK_of_check h8
  have hZ : ZOK (cfgRp d e) (cfgOp d e) (envOf d e) (pauseI d) (startsP d e) (baseK d e) [] (exitBytes sy nm (refX e)) := by
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
  refine ⟨fun m hm => entryCond_of_ok (h10 m hm), hdur, ?_, fun m hm => inPipe_of_inv hL hm, ?_, fun m hm => in_rows hm.2.1 hm.2.2.1 (exit_base h1 hm), ?_, ?_, hctl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, fun m hq hr => quietP_of_V hX hq hr, ?_⟩
  · intro M hM
    have a1 : leftP sy nm e M = (tm (envOf d e) M).toNat + afterF := left_of_inv hL (hdur M hM)
    rw [a1]
    have := hM.1.timer
    show timerF + afterF ≤ ((envOf d e).rkI |> M.ram.get!).toNat + afterF
    omega
  · intro m hm i hP
    rcases z_step hZ hEp hm i hP with ⟨g1, g2, _⟩ | ⟨g1, g2, g3, _⟩
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
      · obtain ⟨D, hD, hs2⟩ := g3 (fun _ h => by cases h)
        have : Sim (envOf d e) ((frame m i).frame, 2) D (frame m i) := hs2
        exact in_rows hs hr (base_of_K hI hq ⟨D, hD, this⟩)
  · intro m hm
    obtain ⟨D, hD1, hs⟩ := exit_base h1 hm
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
  · intro m hm i hP hz
    rcases z_step hZ hEp hm i hP with ⟨g1, _, g3⟩ | ⟨_, _, _, g4⟩
    · have a1 : leftP sy nm e m = (tm (envOf d e) m).toNat + afterF := left_of_inv hL hm
      have a2 : leftP sy nm e (frame m i) = (tm (envOf d e) (frame m i)).toNat + afterF := left_of_inv hL g1
      have := g3 hz
      rw [a1, a2]
      omega
    · exact absurd hz g4
  · intro m hm
    have hr := fun r (hr : r ∈ rowsA (ctxOf sy nm d e) d e ++ rowsB (ctxOf sy nm d e) d e) => h11 r hr
    rcases hm with hm | hm
    · exact not_paused_rows _ (fun r hr' => hr r (List.mem_append_left _ hr')) hm
    · exact not_paused_rows _ (fun r hr' => hr r (List.mem_append_right _ hr')) hm
  · intro m hm i hP
    rcases z_step hZ hEp hm i hP with ⟨g1, _, _⟩ | ⟨_, g2, g3, _⟩
    · exact Or.inl g1
    · refine Or.inr ⟨g2, fun hq hs hr ht => in_rowsT hs hr ht (fun D hD => (h2 D hD).1.1.1) ?_⟩
      obtain ⟨D, hD, hs2⟩ := g3 (fun _ h => by cases h)
      have : Sim (envOf d e) ((frame m i).frame, 2) D (frame m i) := hs2
      exact base_of_K hI hq ⟨D, hD, this⟩
  · intro m hm i hi
    rcases chain_stepD hEt _ hTc hm hi with g | ⟨g1, _⟩
    · exact Or.inl g
    · exact Or.inr g1
  · intro m hm h0
    exact ctl_of_zero (states_of_chainD _ hTc) hTz hm h0
  · intro m hm i hP
    rcases z_step hZ hEp hm i hP with ⟨g1, _, _⟩ | ⟨_, g2, g3, _⟩
    · exact Or.inl g1
    · refine Or.inr ⟨g2, fun hq hr ht => inRowsK_of_exit hK ?_ hq hr ht⟩
      obtain ⟨D, hD, hs2⟩ := g3 (fun _ h => by cases h)
      have : Sim (envOf d e) ((frame m i).frame, 2) D (frame m i) := hs2
      exact ⟨D, hD, this⟩
  · intro m hm i hi
    exact SoundRows.chain_stepS rfl _ hKc hm hi
  · intro m hm h0
    exact SoundRows.ctl_of_zeroS hKc hKz hm h0
  · intro m hm hP
    obtain ⟨r, hr, S, hS, hs, _⟩ := SoundRows.mem_of_invS hm
    exact not_paused_of hs ((Bool.and_eq_true _ _).mp (List.all_eq_true.1 (List.all_eq_true.1 hKn r hr) S hS)).1 hP
  · intro m hm h0
    unfold InRowsT timeRows
    exact invL_congr (c := ctxK (timeCtx sy nm d e) d e) (c' := timeCtx sy nm d e) rfl (SoundRows.invL_zero hKc hm h0)
  · intro m hm i hP
    have hEtp : (timeEnv d e).pad = TaintRun.AB.top := rfl
    rcases p_step hZq hEtp (invT_of hm.1 hm.2.2) hm.2.1 i hP with ⟨g1, g2⟩ | ⟨g1, g2, g3, ⟨t, ht, htm⟩⟩
    · obtain ⟨u1, u2⟩ := of_invT hdS g1
      exact Or.inl ⟨u1, g2, u2⟩
    · obtain ⟨D, hD, hs2⟩ := g2 (fun _ h => by cases h)
      obtain ⟨D0, hD0, rfl⟩ := List.mem_map.1 hD
      have hT : TimerOK d.nx (frame m i) := timerOK_of_simT hs2 rfl
      have hs0 : Sim (envOf d e) ((frame m i).frame, 2) D0 (frame m i) := sim_of_simT hs2 (hdB D0 hD0)
      exact Or.inr ⟨g1, quietV_of_class hLen ht htm g3, hT, fun hq hr => inRowsK_of_exit hK ⟨D0, hD0, hs0⟩ hq hr hT⟩
  · intro m hm
    obtain ⟨r, hr, S, hS, hs, _⟩ := SoundRows.mem_of_invS hm
    exact low7_of hs ((Bool.and_eq_true _ _).mp (List.all_eq_true.1 (List.all_eq_true.1 hKn r hr) S hS)).2

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
  /-- a lag frame ends paused -/
  lagPaused : ∀ n, a ≤ n → n < b → lag n → Paused d (seq (n + 1))
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
              have hz := R.lagPaused _ hgap hlt hl
              rw [hn] at hz
              have hk3 := T.paused _ h1 (R.inp (R.a + k)) hP hz
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
            · have hz := R.lagPaused _ hgap hlt hl
              rw [hn] at hz
              exact absurd hz (T.rowsGo _ g1)
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

/-- `left` is not 0 on a state of the pipe's frames: it is the timer and the frames after it -/
theorem during_left (T : EndStatement sy nm d e es) {m : Machine} (h : During d e m) : leftP sy nm e m ≠ 0 := by
  have hp := T.inRoutine _ h
  show leftOf sy nm sy.EngVerticalPipe _ afterF m ≠ 0
  unfold leftOf
  rw [if_pos hp]
  have : afterF = 43 := rfl
  omega

/-- on a run of the change, the machine is in the pipe or in the rows of the time, up to `b`: if the time is not up at the exit (`TimeOK`), and `b` is the first control after the entry -/
theorem PipeRun.timeWay (T : EndStatement sy nm d e es) (R : PipeRun sy nm d e)
    (ht : ∀ n, R.a ≤ n → n ≤ R.b → ExitAt (exitQ sy nm e) (R.seq n) → TimeOK d.nx (R.seq n))
    (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    ∀ k, R.a + k ≤ R.b → During d e (R.seq (R.a + k)) ∨ InRowsTO sy nm d e (R.seq (R.a + k)) := by
  intro k
  induction k with
  | zero => exact fun _ => Or.inl (T.during _ R.entry)
  | succ k ih =>
    intro hk
    have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
    rw [e1]
    have hn := R.next (R.a + k)
    have hgap : R.a ≤ R.a + k := by omega
    have hlt : R.a + k < R.b := by omega
    rcases ih (by omega) with h1 | h1
    · have hP := R.places _ hgap hlt (T.inRoutine _ h1)
      rcases T.stepT _ h1 (R.inp (R.a + k)) hP with g | ⟨g1, g2⟩
      · rw [hn]
        exact Or.inl g
      · right
        rw [← hn] at g1 g2
        obtain ⟨q1, q2, q3⟩ := R.quiet _ (by omega) (by omega) g1
        exact g2 q1 q2 q3 (ht _ (by omega) (by omega) g1)
    · rcases T.rowsT _ h1 (R.inp (R.a + k)) (R.noStart _ hgap hlt) with g | g
      · have := T.zeroT _ h1 g
        rw [hc _ hgap hlt] at this
        cases this
      · rw [hn]
        exact Or.inr g

/-- **`left` is not 0 before control**, on a run of the change: if the time is not up at the exit (`TimeOK`), and `b` is the first control after the entry. -/
theorem PipeRun.first (T : EndStatement sy nm d e es) (R : PipeRun sy nm d e)
    (ht : ∀ n, R.a ≤ n → n ≤ R.b → ExitAt (exitQ sy nm e) (R.seq n) → TimeOK d.nx (R.seq n))
    (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    ∀ n, R.a ≤ n → n < R.b → leftP sy nm e (R.seq n) ≠ 0 := by
  intro n h1 h2 h0
  obtain ⟨k, rfl⟩ : ∃ k, n = R.a + k := ⟨n - R.a, by omega⟩
  rcases PipeRun.timeWay T R ht hc k (by omega) with h | h
  · exact during_left T h h0
  · have := T.zeroT _ h h0
    rw [hc _ h1 h2] at this
    cases this

/-- **The machine at control is in the rows of the time**, under the same conditions -/
theorem PipeRun.inRowsT (T : EndStatement sy nm d e es) (R : PipeRun sy nm d e)
    (ht : ∀ n, R.a ≤ n → n ≤ R.b → ExitAt (exitQ sy nm e) (R.seq n) → TimeOK d.nx (R.seq n))
    (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) : InRowsTO sy nm d e (R.seq R.b) := by
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := PipeRun.timeWay T R ht hc (R.b - R.a) (by omega)
  rw [e2] at h
  rcases h with h | h
  · exact absurd (T.atControl _ R.atCtl) (during_left T h)
  · exact h

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

/-! ## A run, with the rows with tables

The condition at the exit is weaker: the pause sound may be silent with the flag 0 and the song in a row, or the unpause sound may play (`QuietP`). The pause part of it
comes from the condition on the pause at the entry (`PauseV`), by the pipe's frames with the pause in a class (`EndStatement.pauseStep`); the exit still asks `QuietRest`.
The screen buffer has a form of the table. The game timer is not 000 at the entry (`TimerOK`), and the same walk carries it to the exit. -/

/-- **The change of a run, with the conditions of the rows with tables.** As `PipeRun`, with the condition on the pause at the entry, `QuietRest` and the screen buffer
at the exit, and the game timer not 000 at the entry. -/
structure PipeRunK (sy : Syms) (nm : Names) (d : Data) (e : Machine) where
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
  /-- a lag frame ends paused -/
  lagPaused : ∀ n, a ≤ n → n < b → lag n → Paused d (seq (n + 1))
  /-- on a frame of the pipe's routine, each instruction meets the condition at the places -/
  places : ∀ n, a ≤ n → n < b → inPipe sy sy.EngVerticalPipe (seq n) = true → ∀ j, PlaceOK d.places (PipeEntryRule.trace (seq n) (inp n) j)
  /-- the condition on the pause at the entry: one of the classes that are not paused -/
  pause : PauseV sy d (seq a)
  /-- at the exit, the queue of the pause sound as at the reference, and when the pause sound is silent the two squares' effects and the song (`QuietRest`); the screen
  buffer has a form of the table -/
  quiet : ∀ n, a ≤ n → n ≤ b → ExitAt (exitQ sy nm e) (seq n) → QuietRest d (refX e) (seq n) ∧ SongAt d.xshape (seq n)
  /-- no Start on the frames of the game core after the pipe -/
  noStart : ∀ n, a ≤ n → n < b → coreFrame sy sy.EngVerticalPipe (seq n) = true → SideChangeEnd.noStart (inp n) = true
  /-- at the entry, the game timer is not 000. The pipe's frames do not store to its digits, so it is not 000 at the exit either (`EndStatement.pauseStep`); before
  round 13 this field asked it at the exit. -/
  time : TimerOK d.nx (seq a)

section
variable {sy : Syms} {nm : Names} {d : Data} {e : Machine} {es : List Machine}

theorem PipeRunK.cnt_mono (R : PipeRunK sy nm d e) (n : Nat) : R.cnt n ≤ R.cnt (n + 1) := by
  rw [R.hcnt n]
  split <;> omega

/-- the frame after `n` from a state of the pipe with the pause in a class: in the pipe with the pause in a class, or at the exit in the rows with tables -/
theorem PipeRunK.stepD (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) {n : Nat} (h1 : R.a ≤ n) (h2 : n < R.b) (h : DuringV sy d e (R.seq n)) :
    DuringV sy d e (R.seq (n + 1)) ∨ InRowsK sy nm d e (R.seq (n + 1)) := by
  have hP := R.places _ h1 h2 (T.inRoutine _ h.1)
  rw [R.next n]
  rcases T.pauseStep _ h (R.inp n) hP with g | ⟨g1, g2, _, g3⟩
  · exact Or.inl g
  · right
    rw [← R.next n] at g1 g2 g3 ⊢
    obtain ⟨q1, q2⟩ := R.quiet _ (by omega) (by omega) g1
    exact g3 (T.pauseExit _ g2 q1) q2

/-- the machine at the entry is in the pipe with the pause in a class and the game timer not 000 -/
theorem PipeRunK.atEntry (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) : DuringV sy d e (R.seq R.a) :=
  ⟨T.during _ R.entry, class_of_pauseV R.pause, R.time⟩

/-- **The bound on the change**, with the rows with tables -/
theorem PipeRunK.bound (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) : R.cnt R.a + (timerF + afterF) ≤ R.cnt R.b := by
  have key : ∀ k, R.a + k ≤ R.b → R.cnt R.a + (timerF + afterF) ≤ R.cnt (R.a + k) ∨
      ((DuringV sy d e (R.seq (R.a + k)) ∨ InRowsK sy nm d e (R.seq (R.a + k))) ∧
        R.cnt R.a + (timerF + afterF) ≤ R.cnt (R.a + k) + leftP sy nm e (R.seq (R.a + k))) := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      refine ⟨Or.inl (R.atEntry T), ?_⟩
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
        have := R.cnt_mono (R.a + k)
        omega
      · have hc := R.hcnt (R.a + k)
        have hgap : R.a ≤ R.a + k := by omega
        have hlt : R.a + k < R.b := by omega
        rcases h1 with h1 | h1
        · right
          have hP := R.places _ hgap hlt (T.inRoutine _ h1.1)
          obtain ⟨g1, _⟩ := T.step _ h1.1 (R.inp (R.a + k)) hP
          refine ⟨R.stepD T hgap hlt h1, ?_⟩
          rw [← hn] at g1
          by_cases hl : R.lag (R.a + k)
          · rw [@if_pos _ (R.dec _) hl] at hc
            have hz := R.lagPaused _ hgap hlt hl
            rw [hn] at hz
            have hk3 := T.paused _ h1.1 (R.inp (R.a + k)) hP hz
            rw [← hn] at hk3
            omega
          · rw [@if_neg _ (R.dec _) hl] at hc
            omega
        · have hi := R.noStart _ hgap hlt
          rcases T.rowsK _ h1 (R.inp (R.a + k)) hi with g | ⟨g1, g2⟩
          · left
            have := R.cnt_mono (R.a + k)
            omega
          · right
            rw [hn]
            refine ⟨Or.inr g1, ?_⟩
            by_cases hl : R.lag (R.a + k)
            · have hz := R.lagPaused _ hgap hlt hl
              rw [hn] at hz
              exact absurd hz (T.goK _ g1)
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

/-- on a run of the change, the machine is in the pipe or in the rows with tables, up to `b`, if `b` is the first control after the entry -/
theorem PipeRunK.way (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    ∀ k, R.a + k ≤ R.b → DuringV sy d e (R.seq (R.a + k)) ∨ InRowsK sy nm d e (R.seq (R.a + k)) := by
  intro k
  induction k with
  | zero => exact fun _ => Or.inl (R.atEntry T)
  | succ k ih =>
    intro hk
    have e1 : R.a + (k + 1) = R.a + k + 1 := rfl
    rw [e1]
    have hgap : R.a ≤ R.a + k := by omega
    have hlt : R.a + k < R.b := by omega
    rcases ih (by omega) with h1 | h1
    · exact R.stepD T hgap hlt h1
    · rcases T.rowsK _ h1 (R.inp (R.a + k)) (R.noStart _ hgap hlt) with g | ⟨g, _⟩
      · have := T.zeroK _ h1 g
        rw [hc _ hgap hlt] at this
        cases this
      · rw [R.next]
        exact Or.inr g

/-- **`left` is not 0 before control**, on a run of the change, if `b` is the first control after the entry -/
theorem PipeRunK.first (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    ∀ n, R.a ≤ n → n < R.b → leftP sy nm e (R.seq n) ≠ 0 := by
  intro n h1 h2 h0
  obtain ⟨k, rfl⟩ : ∃ k, n = R.a + k := ⟨n - R.a, by omega⟩
  rcases PipeRunK.way T R hc k (by omega) with h | h
  · exact during_left T h.1 h0
  · have := T.zeroK _ h h0
    rw [hc _ h1 h2] at this
    cases this

/-- **The machine at control is in the rows that the room's checks read**, if `b` is the first control after the entry -/
theorem PipeRunK.inRowsT (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    InRowsT sy nm d e (R.seq R.b) := by
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := PipeRunK.way T R hc (R.b - R.a) (by omega)
  rw [e2] at h
  have h0 := T.atControl _ R.atCtl
  rcases h with h | h
  · exact absurd h0 (during_left T h.1)
  · exact T.ctlK _ h h0

/-- **At control, bits 0 to 6 of the pause byte are 0**, if `b` is the first control after the entry: the machine is in the rows with tables (`EndStatement.bitsK`) -/
theorem PipeRunK.pauseBits (T : EndStatement sy nm d e es) (R : PipeRunK sy nm d e) (hc : ∀ n, R.a ≤ n → n < R.b → controllable sy (R.seq n) = false) :
    (R.seq R.b).ram.get! (pauseI d) &&& 0x7F = 0 := by
  have hb := R.order
  have e2 : R.a + (R.b - R.a) = R.b := by omega
  have h := PipeRunK.way T R hc (R.b - R.a) (by omega)
  rw [e2] at h
  have h0 := T.atControl _ R.atCtl
  rcases h with h | h
  · exact absurd h0 (during_left T h.1)
  · exact T.bitsK _ h

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

/-- the bound on the dot at the parser's place: no frame of the pipe runs so long. One such bound is needed: without any, the walk's dots of a frame reach the frame's end. -/
def dotBound : Nat := 50000

/-- **The data of the check.** The places, from the symbols: the frame's start (the screen buffer's rows), the song, the drawing of the objects and of Mario (the sprites' offsets), the parser with a bound on the dot,
the colour rotation (every value of the buffer's offset: it asks nothing), and three places that the frames of the pipe do not reach: the write on a block being hit under an object, and the two steps that take the
next object of the area. -/
def assemble (sy : Syms) (nx : Names) (m0 : Machine) (song xshape shapes shuf pars : List (List (Nat × UInt8))) (dl dh : Nat) : Data :=
  let known := entryKnown nx
  let bits := entryBits nx
  let o1 := nb nx "VRAM_Buffer1_Offset"
  let shapeB := (shapes.flatMap fun r => r.map (·.1)).eraseDups
  -- the NMI has set the buffer's control to 0 when the sound starts
  let ac := nb nx "VRAM_Buffer_AddrCtrl"
  let songB := bytesOfSong nx
  let shufB := shuffleBytes nx
  let parB := [nb nx "AreaParserTaskNum", nb nx "ScrollThirtyTwo", nb nx "VRAM_Buffer_AddrCtrl"] ++ parserBytes nx
  let never := fun (pc : UInt16) => ({ pc, rows := [], tmax := 0 } : Place)
  let big := dotsPerFrame
  let places : List Place := [
    { pc := sy.NonMaskableInterrupt, rows := shapes, tmax := big },
    { pc := sy.MusicHandler, rows := song, tmax := big },
    { pc := sy.EnemyGfxHandler, rows := shuf, tmax := big },
    { pc := sy.PlayerGfxHandler, rows := shuf, tmax := big },
    { pc := sy.UpdScrollVar, rows := pars, tmax := dotBound },
    { pc := sy.ColorRotation, rows := (List.range 256).map fun v => [(o1, v.toUInt8)], tmax := big },
    never (afterOp m0 sy.HandleEToBGCollision 0x91 0),
    never (afterOp m0 sy.PositionEnemyObj 0xB0 2),
    never (afterOp m0 sy.CheckRightExtBounds 0x90 2) ]
  let kb := known ++ bits.map (·.1)
  let fgt := fun (l : List Nat) => l.filter fun i => !kb.contains i
  let hints : List Hint := ([
    { pc := sy.NonMaskableInterrupt, forget := shapeB, dead := false },
    { pc := sy.SoundEngine, forget := shapeB.filter (· != ac) ++ [0, 1], dead := true },
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
