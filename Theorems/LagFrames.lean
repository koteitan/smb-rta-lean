import Theorems.PipeWrites

/-!
# Up to the vertical pipe: a frame not counted keeps the speed and the position

A frame on which no timer runs is not counted (`lag`). Before the pipe such a frame comes from the pause, or from the master timer control (growth, injury, death).
Here an abstract machine of `TaintRun` follows one whole frame, as in `PipeWrites`, from the idle loop in control (`FrameStart` of `guardOf`). One byte is followed as the
counter of `TaintRun` (`Env.rkI`): a walk that does not fail shows that no instruction writes it. The walk stops where the NMI calls the routine of the mode (`modeCall`),
the instruction before `SkipMainOper`: a paused frame skips that call. So, under `Clean` on each instruction before the call:

* `keeps_frame`: a frame from the idle loop in control either calls the routine of the mode, or it ends with the five bytes of the speed, the subspeed and the
  position (`vfpI`), the three bytes of control (`ctlI`: the routine, the mode, the task) and twenty more bytes (`moreI`: the rest of the horizontal state, the stored
  speed, the collision bits, the area's type, the swimming flag, the change of size, the player's state, the height, its high byte, the vertical speed and its fraction,
  the other vertical bytes of `vstep`, A and B, A and B of the frame before, the jump's halt value) as it began. One walk for each byte.
* `known_of_keep`: so such a frame ends in control (`known_ctl` of `StartRun` the other way: the known bytes of `guardOf`).

The five bytes of `V` are not in `prot` of `guardOf`: a store with a target not known makes the walk forget the followed byte, and then the walk fails at the frame's end.
So the check shows that no store before the frame's end, on a path that does not call the mode's routine, touches the five bytes: the walk knows the target of each such
store. (The three bytes of control are in `prot`.) There is no game data in this file. Page: `1-1/a-5-5-3-LagFrames.md`.
-/

namespace Smbrta.LagFrames

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites
open PipeEntryRule (trace)

/-! ## What the walk knows -/

/-- the RAM index of a byte -/
def I (a : UInt16) : Nat := (a &&& 0x7FF).toNat

/-- the bytes that a frame not counted keeps: the speed, the subspeed, the position (page, pixel, sub-pixel) -/
def vfpI (sy : Syms) : List Nat :=
  [I sy.Player_X_Speed, I sy.Player_X_MoveForce, I sy.Player_PageLoc, I sy.Player_X_Position, I sy.SprObject_X_MoveForce]

/-- the bytes that say that the game is in control: the routine, the mode, the task (the known bytes of `guardOf`) -/
def ctlI (sy : Syms) : List Nat := [I sy.GameEngineSubroutine, I sy.OperMode, I sy.OperMode_Task]

/-- the other bytes of the horizontal state (the facing and moving directions, the running speed), the stored speed, the collision bits, the area's type, the swimming flag,
the change of size, the player's state, and the height, its high byte, the vertical speed and its fraction; and the other vertical bytes of `vstep` (the height's
fraction, the two forces, the jump's origin), A and B, A and B of the frame before, and the jump's halt value: what the next counted frame needs at its start
(`OpenFrames`) -/
def moreI (sy : Syms) : List Nat :=
  [I sy.PlayerFacingDir, I sy.Player_MovingDir, I sy.RunningSpeed, I sy.Player_XSpeedAbsolute, I sy.Player_CollisionBits, I sy.AreaType, I sy.SwimmingFlag,
   I sy.PlayerChangeSizeFlag, I sy.Player_State, I sy.Player_Y_Position, I sy.Player_Y_HighPos, I sy.Player_Y_Speed, I sy.Player_Y_MoveForce,
   I sy.Player_YMF_Dummy, I sy.VerticalForce, I sy.VerticalForceDown, I sy.JumpOrigin_Y_Position, I sy.A_B_Buttons, I sy.PreviousA_B_Buttons, I sy.DiffToHaltJump]

/-- the bytes that the walk follows, one walk each -/
def lagI (sy : Syms) : List Nat := vfpI sy ++ ctlI sy ++ moreI sy

/-- the machine of the walk, with the byte `b` followed -/
def lagEnv (m0 : Machine) (b : Nat) : Env := { PipeEntryRule.envOf m0 with rkI := b }

/-- where the NMI calls the routine of the mode: the instruction before `SkipMainOper` -/
def modeCall (sy : Syms) : UInt16 := sy.SkipMainOper - 3

/-- the opcode at the state's `pc` -/
def opOf (E : Env) (A : AS) : UInt8 := E.prg.get! (A.pc &&& E.mask).toNat

/-- the pieces before a step: the time and the jump, as in `PipeWrites` -/
def preL (G : Guard) (A : AS) : List AS := jumpP G (capT G A)

/-- the state when the frame starts, with the byte followed -/
def startL (G : Guard) (late : Bool) : AS := { startG G late with rk := true }

/-- at the frame's end: the byte is still followed, and no instruction decremented it -/
def endOK (B : AS) : Bool := B.rk && !B.spent

/-- the table -/
structure CfgL where
  E : Env
  ops : Array (AM Unit)
  G : Guard
  /-- the walk stops at this `pc` -/
  cut : UInt16
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  /-- the `pc` of the states of the table -/
  tc : ByteArray

/-- states with the same key are joined, no part of the proof: the `pc`, the stack, the flags of the frame, the counter, both index registers, and `A` near the jump routine -/
def keyL (G : Guard) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0) + (if A.rk then 16 else 0) + (if A.spent then 32 else 0)
  let n := (n * 65536 + num A.x) * 65536 + num A.y
  let n := if G.je ≤ A.pc && A.pc ≤ G.je + 18 then n * 65536 + num A.a else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

def coverL (C : CfgL) (B : AS) : Bool :=
  match C.idx[keyL C.G B]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path ends at the frame's end with the byte kept, reaches the call of the mode's routine, or reaches a state of the table.
No step is `DEC abs` of the byte. -/
def walkL (C : CfgL) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preL C.G A).all fun A₁ => !isRkDec C.E A₁.pc (opOf C.E A₁) && (gsucc C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc == C.cut || (C.tc.get! B.pc.toNat != 0 && coverL C B) || walkL C n B
      else B.k == A.k + 1 && endOK B

/-! ## Finding the table: a search, no part of the proof

The guard is `guardOf`, the guard of a frame in control: its `prot` does not hold the five bytes of `V`. A store with a target not known makes the walk forget such a byte,
so the walk fails if such a store comes before the frame's end on a path that does not call the mode's routine. The stores before the call go through an index (the screen
buffer, the timers, the random bits), and the walk knows their targets only if it knows the index. So the search forgets no byte of RAM, and both index registers are in
the key, as the search of `CtrlKeep` does. -/

structure SL where
  pending : Std.TreeMap Nat AS compare := {}
  done : Std.HashMap Nat (AS × Option (List Nat)) := {}
  multi : Std.HashMap Nat Unit := {}
  arr : Std.HashMap Nat Nat := {}
  leaders : Std.HashMap Nat Unit := {}
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  cuts : Nat := 0
  ends : Nat := 0
  failPcs : Std.HashMap Nat Nat := {}

/-- what the search forgets: the stack below the stack pointer -/
def normL (G : Guard) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) A.kn
  { A with kn }

def routeL (G : Guard) (X : SL) (B0 : AS) : SL :=
  let B := normL G B0
  let K := keyL G B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runL (G : Guard) (E : Env) (ops : Array (AM Unit)) (cut : UInt16) (X0 : SL) (A0 : AS) : SL := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let pre := preL G cur
    let decBad := pre.any fun A₁ => isRkDec E A₁.pc (opOf E A₁)
    let rs := pre.flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := decBad || rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && !(B.k == cur.k + 1 && endOK B)
    if bad then
      X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let same := (rs.filterMap id).filter fun b => b.k == cur.k
    X := { X with cuts := X.cuts + (same.filter fun b => b.pc == cut).length, ends := X.ends + ((rs.filterMap id).filter fun b => b.k != cur.k).length }
    let good := same.filter fun b => b.pc != cut
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeL G X b
    break
  return X

partial def searchL (G : Guard) (E : Env) (cut : UInt16) : SL := Id.run do
  let ops := (aRows E).toArray
  let mut X : SL := [startL G false, startL G true].foldl (routeL G) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runL G E ops cut X A
  return X

/-- the table, from the search -/
def tableOfL (G : Guard) (X : SL) : Array AS × Std.HashMap Nat Nat × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat Nat := {}
  let mut tc := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (keyL G A) t.size
      tc := tc.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, tc)

/-- the walk of the byte `b`, with the guard of a frame in control (`guardOf`): its `prot` does not hold the five bytes of `V` -/
def cfgL (sy : Syms) (m0 : Machine) (b : Nat) : CfgL :=
  let G := guardOf sy m0
  let E := lagEnv m0 b
  let q := tableOfL G (searchL G E (modeCall sy))
  { E, ops := (aRows E).toArray, G, cut := modeCall sy, t := q.1, kl := q.1.map knownOf, idx := q.2.1, tc := q.2.2 }

/-- **The check of one byte.** -/
def lagCheck1 (C : CfgL) : Bool :=
  decide (C.G.late < dotsPerFrame) && C.cut != C.G.idle && C.t.all (walkL C fuelG) && walkL C fuelG (startL C.G false) && walkL C fuelG (startL C.G true)

/-- **The check**, for the five bytes and the three bytes of control -/
def lagCheck (sy : Syms) (m0 : Machine) : Bool := (lagI sy).all fun b => lagCheck1 (cfgL sy m0 b)


/-! ## A step that is not `DEC abs` of the byte

`TaintRun` follows the counter's `DEC abs` only when the counter is at least 2. Here the byte may have any value, and the walk asks that no step is `DEC abs` of it.
The next two theorems are those of `TaintRun` with this in place of the bound. -/

section
variable {E : Env} {F : Nat × UInt8}

set_option maxRecDepth 100000 in
/-- `TaintRun.s_astep1` with no bound on the counter: the step is not `DEC abs` of the counter -/
theorem s_astep1L {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) = false) (hs : Sim E F A m) :
    ∃ r ∈ astep1 E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold astep1
  by_cases hn : A.nmi = true
  · rw [if_pos hn]
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    have hmn : m.nmiPending = true := by rw [hs.nmi]; exact hn
    rw [step_nmi hmn]
    cases he : (anmi E) A with
    | none =>
      rw [he] at hB
      cases hB
    | some p =>
      rw [he] at hB
      obtain ⟨u, B1⟩ := p
      have hB1 : B1 = B := Option.some.inj hB
      subst hB1
      have h2 : (ainterrupt E A.pc ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)) 0xFFFA >>= fun _ => atick 7 7) { A with nmi := false } = some (u, B1) := he
      have hc : go nmi m = go (interrupt A.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA >>= fun _ => tick 7) { m with nmiPending := false } := by
        rw [← hs.pc]
        rfl
      have hs1 : Sim E F { A with nmi := false } { m with nmiPending := false } := { hs with nmi := rfl }
      have hv : ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)).mem ((m.p &&& 0xEF) ||| 0x20) :=
        mem_or (mem_and hs.p (mem_known_self _)) (mem_known_self _)
      obtain ⟨g1, g2, g3⟩ := snd_then_tick (s_interrupt A.pc hv 0xFFFA) hs1 h2
      rw [hc]
      refine ⟨g1, steprel_same hs g1 g2 ?_⟩
      have : m.fdot + 3 * 7 ≤ _ := g3
      omega
  · rw [if_neg hn]
    have hn2 : m.nmiPending = false := by
      rw [hs.nmi]
      simpa using hn
    by_cases hp : 0x8000 ≤ A.pc
    · rw [if_pos hp]
      have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
      rw [step_op hn2 hs.halted hpm]
      have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = E.prg.get! (A.pc &&& E.mask).toNat := by
        rw [hs.prg, hs.mask, hs.pc]
      rw [hop]
      simp only
      generalize E.prg.get! (A.pc &&& E.mask).toNat = op at hd
      have hidle : (op == 0x4C && m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat == m.pc.toUInt8
          && m.prg.get! ((m.pc + 2) &&& m.prgMask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = isIdle E A.pc op := by
        simp only [isIdle, hs.prg, hs.mask, hs.pc]
      unfold stepK
      simp only [hidle]
      by_cases hi : isIdle E A.pc op = true
      · rw [if_pos hi, if_pos hi]
        have e1 := PipeTransitionAll.go_bind (f := setPC m.pc) (g := fun _ => tick (cyclesToNextEvent m)) { m with pc := m.pc + 1 }
        have e2 : (go (setPC m.pc) { m with pc := m.pc + 1 }).2 = m := rfl
        rw [e1, e2]
        exact s_idle hs
      · rw [if_neg hi, if_neg hi]
        by_cases hd2 : (A.rk && isRkDec E A.pc op) = true
        · exfalso
          rw [hd, Bool.and_false] at hd2
          cases hd2
        rw [if_neg hd2]
        by_cases hc : (cycOf op == 0) = true
        · rw [if_pos hc]
          exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
        · rw [if_neg hc]
          refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
          have hc1 : 1 ≤ cycOf op := by
            have : cycOf op ≠ 0 := by simpa using hc
            omega
          cases he : (ops[op.toNat]?.getD aJAM >>= fun _ => atick (cycOf op) (cycOf op)) { A with pc := A.pc + 1 } with
          | none =>
            rw [he] at hB
            cases hB
          | some p =>
            rw [he] at hB
            obtain ⟨u, B1⟩ := p
            have hB1 : B1 = B := Option.some.inj hB
            subst hB1
            have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
              pc := by
                show m.pc + 1 = A.pc + 1
                rw [hs.pc] }
            rw [hops] at he
            have hso := s_op (E := E) (F := F) op.toNat
            have ee : (cycTable.get! op.toNat).toNat = cycOf op := rfl
            rw [ee]
            generalize (opTable[op.toNat]?.getD opJAM) = fop at hso ⊢
            generalize (aRows E).toArray[op.toNat]?.getD aJAM = aop at hso he
            generalize cycOf op = cc at he hc1 ⊢
            obtain ⟨g1, g2, g3⟩ := snd_then_tick hso hs1 he
            refine ⟨g1, steprel_same hs g1 g2 ?_⟩
            have g3' : m.fdot + 3 * cc ≤ (go (fop >>= fun _ => tick cc) { m with pc := m.pc + 1 }).2.fdot := g3
            omega
    · rw [if_neg hp]
      exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩

/-- `TaintRun.s_succs` with no bound on the counter -/
theorem s_succsL {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) = false) (hs : Sim E F A m) :
    ∃ r ∈ succs E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨P, hP, h1, h2⟩ := cov_pieces A m hs
  have hpc : P.pc = A.pc := h1.pc.symm.trans hs.pc
  obtain ⟨r, hr, h3⟩ := s_astep1L hops (by rw [hpc]; exact hd) h1
  refine ⟨r, List.mem_flatMap.2 ⟨P, hP, hr⟩, fun B hB => ?_⟩
  obtain ⟨h4, h5⟩ := h3 B hB
  refine ⟨h4, ?_⟩
  unfold StepRel at h5 ⊢
  rw [h2] at h5
  exact h5

/-- `PipeWrites.s_gsucc` with no bound on the counter -/
theorem s_gsuccL {G : Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (opOf E A) = false) (hc : Clean G m) (hs : Sim E F A m) :
    ∃ r ∈ gsucc G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold gsucc
  by_cases h : (A.nmi || decide (A.pc < 0x8000)) = true
  · rw [if_pos h]
    exact s_succsL hops hd hs
  · rw [if_neg h]
    simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only
    cases hco : customOf G.prot E A (E.prg.get! (A.pc &&& E.mask).toNat) with
    | none => exact s_succsL hops hd hs
    | some af =>
      obtain ⟨g1, g2, g3⟩ := custom_ok hc hs rfl hco
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      have hp : 0x8000 ≤ A.pc := by
        have h3 : ¬ (A.pc.toNat < (0x8000 : UInt16).toNat) := fun h4 => h2 (UInt16.lt_iff_toNat_lt.2 h4)
        apply UInt16.le_iff_toNat_le.2
        omega
      exact custom_step hs (by simpa using h1) hp rfl g1 g2 g3 B hB

/-- the pieces of the time and the jump cover the machine -/
theorem cov_preL {G : Guard} {A : AS} {m : Machine} (hc : Clean G m) (hs : Sim E F A m) : ∃ B ∈ preL G A, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨B, hB, h1⟩ := cov_jump hc (sim_cap hc hs)
  refine ⟨B, hB, h1, ?_⟩
  have a1 := h1.fr
  have a2 := hs.fr
  omega

/-- the byte followed from its value at the start -/
theorem sim_rk {A : AS} {m : Machine} (hs : Sim E F A m) (hsp : A.spent = false) : Sim E (F.1, m.ram.get! E.rkI) { A with rk := true } m :=
  { hs with rkv := fun _ => by simp [hsp] }

end

/-! ## The walk covers the frame -/

section
variable {C : CfgL} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveL (C : CfgL) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkL C n A = true

theorem cover_liveL (ht : C.t.all (walkL C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverL C B = true) : ∃ D, LiveL C F D m := by
  unfold coverL at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := le_k hle
        omega
      exact ⟨D, sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

/-- one step: the walk goes on, or the machine is at the call of the mode's routine, or the frame ends with the byte kept -/
theorem live_stepL (ht : C.t.all (walkL C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveL C F A m) (hc : Clean C.G m) :
    (∃ A', LiveL C F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ C.cut) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = C.cut) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, endOK B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkL] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preL hc hs
    simp only [walkL, List.all_eq_true, Bool.and_eq_true] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    have hd' : isRkDec C.E A₁.pc (opOf C.E A₁) = false := by simpa using hd
    obtain ⟨r, hr1, hB⟩ := s_gsuccL hops hd' hc hs1
    have hw3 := hw2 r hr1
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · by_cases hcut : B.pc = C.cut
        · exact Or.inr (Or.inl ⟨k2, by rw [h1.pc]; exact hcut⟩)
        have hcut' : (go step m).2.pc ≠ C.cut := by rw [h1.pc]; exact hcut
        rw [if_pos (by simp [k1, hk1])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hw3
        rcases hw3 with (h4 | ⟨_, h4⟩) | h4
        · exact absurd h4 hcut
        · obtain ⟨D, hD⟩ := cover_liveL ht hkl h1 (by omega) h4
          exact Or.inl ⟨D, hD, k2, k3, hcut'⟩
        · exact Or.inl ⟨B, ⟨h1, by omega, n, h4⟩, k2, k3, hcut'⟩
      · rw [if_neg (by simp [k1, hk1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact Or.inr (Or.inr ⟨k2, B, hw3.2, h1⟩)

/-- the instructions of the frame, from one that the walk covers -/
theorem frame_runL (ht : C.t.all (walkL C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) {M : Machine} {i : UInt8}
    (hcl : ∀ k, (trace M i k).frame = M.frame → (∀ j, j ≤ k → (trace M i j).pc ≠ C.cut) → Clean C.G (trace M i k)) :
    ∀ (n j : Nat) (A : AS), LiveL C F A (trace M i j) → (trace M i j).frame = M.frame → dotsPerFrame ≤ (trace M i j).fdot + 3 * n →
      (∀ j', j' ≤ j → (trace M i j').pc ≠ C.cut) →
      (∃ k, (trace M i k).frame = M.frame ∧ (trace M i k).pc = C.cut) ∨ ∃ B, endOK B = true ∧ Sim C.E F B (trace M i (j + n)) := by
  intro n
  induction n with
  | zero =>
    intro j A hl _ hd _
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro j A hl hf hd hn
    have hh := hl.1.halted
    have e : trace M i (j + 1) = (go step (trace M i j)).2 := by
      show PipeEntryRule.nxt (M.frame + 1) (trace M i j) = _
      have hn : ¬ ((trace M i j).frame ≥ M.frame + 1 || (trace M i j).halted) = true := by simp [hf, hh]
      simp only [PipeEntryRule.nxt, if_neg hn]
    rcases live_stepL ht hkl hops hl (hcl j hf hn) with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, B, h2, h3⟩
    · rw [← e] at h1 h2 h3 h4
      rw [show j + (n + 1) = j + 1 + n by omega]
      refine ih (j + 1) A' h1 (h2.trans hf) (by omega) fun j' hj' => ?_
      by_cases hj : j' = j + 1
      · rw [hj]
        exact h4
      · exact hn j' (by omega)
    · rw [← e] at h1 h2
      exact Or.inl ⟨j + 1, h1.trans hf, h2⟩
    · rw [← e] at h1 h3
      right
      have hst : ((trace M i (j + 1)).frame ≥ M.frame + 1 || (trace M i (j + 1)).halted) = true := by simp [h1, hf]
      rw [show j + (n + 1) = (j + 1) + n by omega, PipeEntryRule.trace_stop hst n]
      exact ⟨B, h2, h3⟩

end

/-! ## One frame -/

/-- what the check of one byte says -/
structure LagOK (C : CfgL) : Prop where
  late : C.G.late < dotsPerFrame
  cutIdle : C.cut ≠ C.G.idle
  table : C.t.all (walkL C fuelG) = true
  s0 : walkL C fuelG (startL C.G false) = true
  s1 : walkL C fuelG (startL C.G true) = true

theorem lagOK_of_check {C : CfgL} (h : lagCheck1 C = true) : LagOK C := by
  simp only [lagCheck1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h5⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h5, h2, h3, h4⟩

/-- **One byte.** A frame from the idle loop whose instructions before the call are `Clean` calls the mode's routine, or it ends with the followed byte as it began. -/
theorem keeps_one {C : CfgL} (hO : LagOK C) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m)
    (hcl : ∀ k, (trace m i k).frame = m.frame → (∀ j, j ≤ k → (trace m i j).pc ≠ C.cut) → Clean C.G (trace m i k)) :
    (∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = C.cut) ∨ (frame m i).ram.get! C.E.rkI = m.ram.get! C.E.rkI := by
  obtain ⟨b, hs⟩ := sim_startG hE h0
  have hs2 := sim_rk hs rfl
  have hs3 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := { hs2 with pad := by rw [hE]; exact mem_top _ }
  have hl : LiveL C (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := by
    refine ⟨hs3, rfl, fuelG, ?_⟩
    cases b
    · exact hO.s0
    · exact hO.s1
  have hd : dotsPerFrame ≤ (trace m i 0).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  have hn0 : ∀ j', j' ≤ 0 → (trace m i j').pc ≠ C.cut := by
    intro j' hj'
    rw [show j' = 0 by omega]
    show m.pc ≠ C.cut
    rw [h0.pc]
    exact fun h => hO.cutIdle h.symm
  rcases frame_runL hO.table hkl hops hcl fuelPerFrame 0 _ hl rfl hd hn0 with h | ⟨B, h1, h2⟩
  · exact Or.inl h
  · right
    rw [PipeEntryRule.frame_trace]
    rw [Nat.zero_add] at h2
    simp only [endOK, Bool.and_eq_true, Bool.not_eq_true'] at h1
    have h3 := h2.rkv h1.1
    simp only [h1.2] at h3
    exact h3

/-- **A frame that does not call the mode's routine keeps the speed, the subspeed, the position and the bytes of control.** The frame starts in the idle loop in
control (`FrameStart` of `guardOf`), and each of its instructions before the call is `Clean`. `hc` is the check on the ROM. -/
theorem keeps_frame {sy : Syms} {m0 : Machine} (hc : lagCheck sy m0 = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) m)
    (hcl : ∀ k, (trace m i k).frame = m.frame → (∀ j, j ≤ k → (trace m i j).pc ≠ modeCall sy) → Clean (guardOf sy m0) (trace m i k)) :
    (∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = modeCall sy) ∨ ∀ b ∈ lagI sy, (frame m i).ram.get! b = m.ram.get! b := by
  by_cases hx : ∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = modeCall sy
  · exact Or.inl hx
  · right
    intro b hb
    have h1 := lagOK_of_check ((List.all_eq_true.1 hc) b hb)
    have h0' : FrameStart (cfgL sy m0 b).G (cfgL sy m0 b).E m :=
      ⟨h0.pc, h0.s, h0.dot, h0.ctrl, h0.s0, h0.strobe, h0.halted, h0.trk, h0.prg, h0.mask, h0.size, h0.known⟩
    rcases keeps_one (C := cfgL sy m0 b) h1 rfl rfl rfl h0' hcl with h | h
    · exact absurd h hx
    · exact h

/-- **A frame that keeps the bytes of control ends in control**: the known bytes of `guardOf` at its end -/
theorem known_of_keep {sy : Syms} {m0 m m' : Machine} {E : Env} (h0 : FrameStart (guardOf sy m0) E m) (h : ∀ b ∈ lagI sy, m'.ram.get! b = m.ram.get! b) :
    ∀ p ∈ (guardOf sy m0).known, m'.ram.get! p.1 = p.2 := by
  have e : (guardOf sy m0).known = [(I sy.GameEngineSubroutine, sy.Eng_PlayerCtrl.toUInt8), (I sy.OperMode, sy.GameModeValue.toUInt8),
      (I sy.OperMode_Task, sy.Task_GameCore.toUInt8)] := rfl
  intro p hp
  have hm : p.1 ∈ lagI sy := by
    rw [e] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rcases hp with rfl | rfl | rfl <;> simp [ctlI]
  rw [h p.1 hm]
  exact h0.known p hp

end Smbrta.LagFrames
