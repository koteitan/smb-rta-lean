import Theorems.CtrlKeep
import Theorems.LagPause

/-!
# A frame in control keeps the phase exactly when it ends paused

The NMI runs the screen, the sound, the pad and the pause, then the timers: if the game is not paused and the master timer control (`TimerControl`) is 0, it decrements
the interval timer's control, the phase (`DecTimers`); from 0 it goes to the top of its cycle. Then come the frame timers' loop and the mode's routine.
Here three pieces of the abstract machine of `TaintRun` follow a frame that starts in the idle loop in control (`FrameKeep.StartK`), with the master timer control 0:

* walk `A`, from the frame's start to the first instruction of `DecTimers` (the cut). The phase is followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on
  any write to it and on its `DEC`. The low bit of the pause byte starts known. A path that does not come to the cut (a paused frame) goes on to the frame's end, and there
  the phase must still be followed and the low bit known to be 1.
* the timer's code, `T`: at the cut the phase is split into its 21 values; from each, the instructions up to the timers' loop (the target of the `BPL` after the `DEC`)
  must leave the phase known, with the value `(p + 20) % 21` of the clock's rule (`CastleToLevel.Step`).
* walk `B`, from the timers' loop to the frame's end: the phase followed again as the counter, from its new value, and at the end the low bit of the pause byte known to
  be 0.

So (`phase_frame`): a frame that ends paused ends with the phase it began with, and a frame that ends not paused ends with the phase `(p + 20) % 21` (`PhaseRule`). The
phase at the start is at most 20. The condition on each instruction is `FrameKeep.CleanK` of `guardPh`: the guard `FrameKeep.guardE` of `keep.cleanE`, with the phase and
the master timer control among the bytes that a store with a target not known does not touch (`KeepsPhase`, `cleanPh_of`).

A frame before the touch's frame keeps the master timer control 0 (`tc_frame`): the walk of `FrameKeep` with the stores of the routine, the mode and the task cut, with the
master timer control watched (`tcCheck`). So every frame of `FrameKeep.Frames` up to the touch's frame follows `PhaseRule` (`frames_phase`), from the machine at control with
the master timer control 0 and the phase at most 20.

The searches are no part of the proof: the check walks every state of its tables. There is no game data in this file. Page: `1-1/0-5-2-1-1-PhaseFrame.md`.
-/

namespace Smbrta.PhaseFrame

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites (Guard Clean FrameStart SG leK knownOf joinK startG)
open PipeEntryRule (trace)
open FrameKeep (Spot CleanK preK kstep)
open LagFrames (opOf)

/-! ## The bytes -/

/-- **The phase**: the operand of the `DEC abs` that follows the first instruction of `DecTimers` (`LDX #`) -/
def phaseA (sy : Syms) (m0 : Machine) : UInt16 :=
  (romByte m0 (sy.DecTimers + 3)).toUInt16 ||| ((romByte m0 (sy.DecTimers + 4)).toUInt16 <<< 8)

def phaseI (sy : Syms) (m0 : Machine) : Nat := (phaseA sy m0 &&& 0x7FF).toNat

/-- the master timer control -/
def tcI (sy : Syms) : Nat := (sy.TimerControl &&& 0x7FF).toNat

/-- the timers' loop: the target of the `BPL` after the `DEC` -/
def loopAt (sy : Syms) (m0 : Machine) : UInt16 := sy.DecTimers + 7 + (romByte m0 (sy.DecTimers + 6)).toUInt16

/-- the clock's rule for the phase on a frame on which the timers run (`CastleToLevel.Step`) -/
def next (p : Nat) : Nat := (p + 20) % 21

/-- the guard: `FrameKeep.guardE` with the phase and the master timer control among the bytes that a store with a target not known does not touch -/
def guardPh (sy : Syms) (m0 : Machine) : Guard := { FrameKeep.guardE sy m0 with prot := phaseI sy m0 :: tcI sy :: (FrameKeep.guardE sy m0).prot }

/-- the machine of the walks, with the phase as the counter -/
def envPh (sy : Syms) (m0 : Machine) : Env := { PipeEntryRule.envOf m0 with rkI := phaseI sy m0 }

/-! ## The walks -/

/-- a walk: its table, where it stops (`cut`), and what it asks there and at the frame's end -/
structure CfgW where
  E : Env
  ops : Array (AM Unit)
  S : Spot
  G : Guard
  cut : UInt16
  atCut : AS → Bool
  fin : AS → Bool
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  tc : ByteArray
  /-- the table's key: no part of the proof -/
  key : AS → Nat

def coverW (C : CfgW) (B : AS) : Bool :=
  match C.idx[C.key B]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step, until every path comes to the cut with `atCut`, reaches a state of the table, or ends the frame with `fin`. No step is the `DEC` of the counter. -/
def walkW (C : CfgW) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.S C.G A).all fun A₁ => !isRkDec C.E A₁.pc (opOf C.E A₁) && (kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (if B.pc == C.cut then C.atCut B else (C.tc.get! B.pc.toNat != 0 && coverW C B) || walkW C n B)
      else B.k == A.k + 1 && C.fin B

/-- the timer's code: from `A`, every path comes to `stop` in the frame, where `test` holds -/
def walkT (S : Spot) (G : Guard) (E : Env) (ops : Array (AM Unit)) (stop : UInt16) (test : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK S G A).all fun A₁ => (kstep S G E ops A₁).all fun r =>
    match r with
    | none => false
    | some B => B.k == A.k && (if B.pc == stop then test B else walkT S G E ops stop test n B)

/-- the phase known to be `p`, not followed -/
def ofRk (i : Nat) (p : UInt8) (B : AS) : AS := { B.setK i (AB.known p) with rk := false, spent := false }

/-- the phase followed from here on -/
def toRk (i : Nat) (B : AS) : AS := { B.setK i AB.top with rk := true, spent := false }

/-- the low bit of the pause byte is known to be `b` -/
def pauseIs (pz : Nat) (b : Bool) (B : AS) : Bool := (B.getK pz).bit 0x01 == some b

/-- the fuel of the timer's code -/
def fuelT : Nat := 32

/-- what walk `A` asks at the cut: the phase followed and not decremented; from each of its 21 values the timer's code comes to the loop with the phase `next p`, where walk
`B` goes on (`CB`) -/
def atCutA (i : Nat) (stop : UInt16) (CB : CfgW) (B : AS) : Bool :=
  B.rk && !B.spent && (List.range 21).all fun p =>
    walkT CB.S CB.G CB.E CB.ops stop (fun B' => (B'.getK i).isK && (B'.getK i).v.toNat == next p && (coverW CB (toRk i B') || walkW CB FrameKeep.fuelK (toRk i B')))
      fuelT (ofRk i p.toUInt8 B)

/-- the state when the frame starts: the phase followed, the low bit of the pause byte `b`, the master timer control 0 -/
def startA (G : Guard) (pz ti : Nat) (late b : Bool) : AS :=
  ((LagFrames.startL G late).setK pz ⟨if b then 1 else 0, 1⟩).setK ti (AB.known 0)

def startsA (G : Guard) (pz ti : Nat) : List AS := [startA G pz ti false false, startA G pz ti false true, startA G pz ti true false, startA G pz ti true true]

/-! ## Finding the tables: a search, no part of the proof -/

/-- walk `A`'s key: that of `CtrlKeep`, with the pause byte -/
def keyA (G : Guard) (pz : Nat) (A : AS) : Nat := CtrlKeep.keyR G pz true A

/-- walk `B`'s key: that of `FrameKeep`, with the low bit of the pause byte and the counter's flags -/
def keyB (S : Spot) (G : Guard) (pz : Nat) (A : AS) : Nat :=
  let b := A.getK pz
  FrameKeep.keyK S G [] A * 16 + (if A.rk then 1 else 0) + (if A.spent then 2 else 0) + (if b.k &&& 1 != 0 then 4 else 0) + (if b.v &&& b.k &&& 1 != 0 then 8 else 0)

/-- walk `B`'s search forgets as that of `FrameKeep`, and the pause byte but its low bit; it keeps the counter followed -/
def normB (S : Spot) (G : Guard) (pz : Nat) (A : AS) : AS :=
  let B := FrameKeep.normK S G A
  let b := B.getK pz
  { B.setK pz ⟨b.v &&& 1, b.k &&& 1⟩ with rk := A.rk, spent := A.spent }

def routeW (norm : AS → AS) (G : Guard) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := norm B0
  let K := key B
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

/-- the search's run from `A0`; a state at the cut is not followed: it is kept in the list of the cuts -/
partial def runW (S : Spot) (G : Guard) (E : Env) (norm : AS → AS) (key : AS → Nat) (ops : Array (AM Unit)) (cut : UInt16) (X0 : SG) (c0 : Array AS) (A0 : AS) :
    SG × Array AS := Id.run do
  let mut X := X0
  let mut cuts := c0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preK S G cur).flatMap fun A₁ => if isRkDec E A₁.pc (opOf E A₁) then [none] else kstep S G E ops A₁
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some _ => false
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let same := (rs.filterMap id).filter fun b => b.k == cur.k
    for b in same do
      if b.pc == cut then cuts := cuts.push b
    let good := same.filter fun b => b.pc != cut
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeW norm G key X b
    break
  return (X, cuts)

partial def searchW (S : Spot) (G : Guard) (E : Env) (norm : AS → AS) (key : AS → Nat) (cut : UInt16) (starts : List AS) : SG × Array AS := Id.run do
  let ops := (aRows E).toArray
  let mut X : SG := starts.foldl (routeW norm G key) {}
  let mut cuts : Array AS := #[]
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      let r := runW S G E norm key ops cut X cuts A
      X := r.1
      cuts := r.2
  return (X, cuts)

/-- the table, from the search: every state that was reached more than once -/
def tableOfW (key : AS → Nat) (X : SG) : Array AS × Std.HashMap Nat Nat × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat Nat := {}
  let mut tc := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (key A) t.size
      tc := tc.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, tc)

/-- the timer's code in the search: the states at `stop` -/
partial def runT (S : Spot) (G : Guard) (E : Env) (ops : Array (AM Unit)) (stop : UInt16) (n : Nat) (A : AS) : List AS :=
  if n == 0 then [] else
  (preK S G A).flatMap fun A₁ => (kstep S G E ops A₁).flatMap fun r =>
    match r with
    | none => []
    | some B => if B.k != A.k then [] else if B.pc == stop then [B] else runT S G E ops stop (n - 1) B

/-- the starts of walk `B`: from each state at the cut and each value of the phase, the state at the loop -/
def startsB (sy : Syms) (m0 : Machine) (cuts : Array AS) : List AS :=
  let G := guardPh sy m0
  let E := envPh sy m0
  let S := FrameKeep.spotOf sy m0
  let ops := (aRows E).toArray
  let i := phaseI sy m0
  cuts.toList.flatMap fun B => (List.range 21).flatMap fun p => (runT S G E ops (loopAt sy m0) fuelT (ofRk i p.toUInt8 B)).map (toRk i)

/-! ## The master timer control

The walk of `FrameKeep` with the stores of the routine, the mode and the task cut (`FrameKeep.ctlKeepCheck`), with one more watched byte: the master timer control, 0.
The game writes it by its address only when it frees the timers (0), when it halts them for a change of the player's state (right after a store of the routine byte, which the
cut stops) and in the NMI when it is not 0. So a frame before the touch's frame that starts with it 0 ends with it 0 (`tc_frame`). -/

/-- the guard of `FrameKeep`'s walk, with the master timer control protected -/
def guardTC (sy : Syms) (m0 : Machine) : Guard := { guardPh sy m0 with prot := tcI sy :: (FrameKeep.guardK sy m0).prot }

/-- the watched bytes: those of `FrameKeep`, and the master timer control 0 -/
def watchTC (sy : Syms) : List FrameKeep.Watch := FrameKeep.watchOf sy ++ [(tcI sy, 0xFF, 0)]

/-- **The check of the master timer control**: the walk with the stores of the three bytes of control cut -/
def tcCheck (sy : Syms) (m0 : Machine) : Bool :=
  FrameKeep.keepCheckC (FrameKeep.spotOf sy m0) (guardTC sy m0) (PipeEntryRule.envOf m0) (watchTC sy)
    (FrameKeep.keyK (FrameKeep.spotOf sy m0) (guardTC sy m0) (watchTC sy)) (FrameKeep.ctlI sy) (FrameKeep.knownAll (guardTC sy m0))

/-! ## The check -/

/-- walk `A`'s search -/
def searchA (sy : Syms) (m0 : Machine) : SG × Array AS :=
  let G := guardPh sy m0
  let pz := FrameKeep.pauseI sy m0
  searchW (FrameKeep.spotOf sy m0) G (envPh sy m0) (CtrlKeep.normR G) (keyA G pz) sy.DecTimers (startsA G pz (tcI sy))

/-- walk `B`, from the starts `st` -/
def cfgB (sy : Syms) (m0 : Machine) (st : List AS) : CfgW :=
  let G := guardPh sy m0
  let E := envPh sy m0
  let S := FrameKeep.spotOf sy m0
  let pz := FrameKeep.pauseI sy m0
  let key := keyB S G pz
  let q := tableOfW key (searchW S G E (normB S G pz) key 0 st).1
  { E, ops := (aRows E).toArray, S, G, cut := 0, atCut := fun _ => false,
    fin := fun B => B.rk && !B.spent && SideChangeEnd.notPausedK pz B, t := q.1, kl := q.1.map knownOf, idx := q.2.1, tc := q.2.2, key }

/-- walk `A`, with walk `B` at the cut -/
def cfgA (sy : Syms) (m0 : Machine) (X : SG) (CB : CfgW) : CfgW :=
  let G := guardPh sy m0
  let E := envPh sy m0
  let pz := FrameKeep.pauseI sy m0
  let key := keyA G pz
  let q := tableOfW key X
  { E, ops := (aRows E).toArray, S := FrameKeep.spotOf sy m0, G, cut := sy.DecTimers, atCut := atCutA (phaseI sy m0) (loopAt sy m0) CB,
    fin := fun B => B.rk && !B.spent && pauseIs pz true B, t := q.1, kl := q.1.map knownOf, idx := q.2.1, tc := q.2.2, key }

/-- the two walks -/
def cfgs (sy : Syms) (m0 : Machine) : CfgW × CfgW :=
  let r := searchA sy m0
  let CB := cfgB sy m0 (startsB sy m0 r.2)
  (cfgA sy m0 r.1 CB, CB)

/-- **The check.** -/
def phaseCheck (sy : Syms) (m0 : Machine) : Bool :=
  let C := cfgs sy m0
  decide ((guardPh sy m0).late < dotsPerFrame) && sy.DecTimers != (guardPh sy m0).idle && loopAt sy m0 != 0 &&
    C.2.t.all (walkW C.2 FrameKeep.fuelK) && C.1.t.all (walkW C.1 FrameKeep.fuelK) &&
    (startsA (guardPh sy m0) (FrameKeep.pauseI sy m0) (tcI sy)).all (walkW C.1 FrameKeep.fuelK)

/-! ## The steps follow the machine -/

section
variable {E : Env} {F : Nat × UInt8}

set_option maxRecDepth 100000 in
/-- `FrameKeep.s_kstep` with no bound on the counter: the step is not the counter's `DEC` -/
theorem s_kstepL {S : Spot} {G : Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray)
    (hd : isRkDec E A.pc (opOf E A) = false) (hc : CleanK G S.store m) (hs : Sim E F A m) :
    ∃ r ∈ kstep S G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold kstep
  by_cases h1 : (!A.nmi && A.pc == S.store) = true
  · rw [if_pos h1]
    by_cases h2 : (A.x.isK && E.prg.get! (A.pc &&& E.mask).toNat == 0x9D) = true
    · rw [if_pos h2]
      exact LagFrames.s_succsL hops hd hs
    · rw [if_neg h2]
      by_cases h3 : FrameKeep.nonZero A.x = true
      · rw [if_pos h3]
        have hx := FrameKeep.ne_of_nonZero h3 hs.x
        exact LagFrames.s_gsuccL hops hd (FrameKeep.clean_of hc fun h => hx h.2) hs
      · rw [if_neg h3]
        exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  · rw [if_neg h1]
    by_cases h4 : FrameKeep.lowAdc E A = true
    · rw [if_pos h4]
      simp only [FrameKeep.lowAdc, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at h4
      obtain ⟨⟨⟨⟨⟨⟨hn, hp⟩, hop⟩, _⟩, _⟩, _⟩, _⟩ := h4
      have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
        pc := by
          show m.pc + 1 = A.pc + 1
          rw [hs.pc] }
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      refine PipeWrites.custom_step hs hn hp hop (by decide) (by decide) (fun u A₂ he => ?_) B hB
      rw [FrameKeep.op_65]
      obtain ⟨_, g1, g2⟩ := FrameKeep.s_sumL _ _ hs1 _ _ he
      exact ⟨g1, g2⟩
    · rw [if_neg h4]
      by_cases hn : A.nmi = true
      · have e : PipeWrites.gsucc G E ops A = succs E ops A := by
          unfold PipeWrites.gsucc
          simp [hn]
        rw [e]
        exact LagFrames.s_succsL hops hd hs
      · have hq : A.pc ≠ S.store := by
          intro hq
          apply h1
          simp [hn, hq]
        exact LagFrames.s_gsuccL hops hd (FrameKeep.clean_of hc fun h => hq (hs.pc ▸ h.1)) hs

/-- the counter's value, while it is followed and not decremented -/
theorem rk_val {A : AS} {m : Machine} (hs : Sim E F A m) (hr : A.rk = true) (hsp : A.spent = false) : m.ram.get! E.rkI = F.2 := by
  have h := hs.rkv hr
  rw [hsp] at h
  exact h

/-- the counter made known, with its value: the pair of the frame and the counter can be any other with the same frame -/
theorem sim_ofRk {A : AS} {m : Machine} (hs : Sim E F A m) {p : UInt8} (hp : m.ram.get! E.rkI = p) (F' : Nat × UInt8) (hF : F'.1 = F.1) :
    Sim E F' (ofRk E.rkI p A) m := by
  have h1 : Sim E F (A.setK E.rkI (AB.known p)) m := PipeEntryRule.sim_setK' hs (by rw [hp]; exact mem_known_self p)
  exact { h1 with fr := by rw [hF]; exact h1.fr, rkv := fun h => by cases h }

/-- the counter followed again, from its value now -/
theorem sim_toRk {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E (F.1, m.ram.get! E.rkI) (toRk E.rkI A) m := by
  have h1 : Sim E F (A.setK E.rkI AB.top) m := PipeEntryRule.sim_setK' hs (mem_top _)
  exact { h1 with fr := h1.fr, rkv := fun _ => rfl }

end

/-! ## The walks cover the frame -/

section
variable {C : CfgW} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveW (C : CfgW) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkW C n A = true

theorem cover_liveW (ht : C.t.all (walkW C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : coverW C B = true) : ∃ D, LiveW C F D m ∧ D.k = B.k := by
  unfold coverW at h
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
      have hle := PipeWrites.leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
    · cases h
  · cases h

/-- one step: the walk goes on, or the machine comes to the cut with `atCut`, or the frame ends with `fin` -/
theorem live_stepW (ht : C.t.all (walkW C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveW C F A m) (hc : CleanK C.G C.S.store m) :
    (∃ A', LiveW C F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ (go step m).2.pc ≠ C.cut ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = C.cut ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ ∃ B, C.atCut B = true ∧ Sim C.E F B (go step m).2) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkW] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hc hs
    simp only [walkW, List.all_eq_true, Bool.and_eq_true] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    have hd' : isRkDec C.E A₁.pc (opOf C.E A₁) = false := by simpa using hd
    obtain ⟨r, hr, hB⟩ := s_kstepL hops hd' hc hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw3
        by_cases hcut : B.pc = C.cut
        · rw [if_pos (by simp [hcut])] at hw3
          exact Or.inr (Or.inl ⟨k2, by rw [h1.pc]; exact hcut, k3, B, hw3, h1⟩)
        · rw [if_neg (by simp [hcut])] at hw3
          have hcut' : (go step m).2.pc ≠ C.cut := by rw [h1.pc]; exact hcut
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
          rcases hw3 with ⟨_, h4⟩ | h4
          · obtain ⟨D, hD, hDk⟩ := cover_liveW ht hkl h1 h4
            exact Or.inl ⟨D, hD, by rw [hDk, k1], k2, hcut', k3⟩
          · exact Or.inl ⟨B, ⟨h1, n, h4⟩, k1, k2, hcut', k3⟩
      · rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact Or.inr (Or.inr ⟨k2, B, hw3.2, h1⟩)

/-- **A walk from the machine `k₀` instructions into the frame of `m`**, every instruction meeting `CleanK`: the frame comes to the cut a first time after `k₀`, in a state
with `atCut`, or it ends in a state with `fin` -/
theorem run_W (ht : C.t.all (walkW C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {m : Machine} {i : UInt8} (hcl : ∀ j, CleanK C.G C.S.store (trace m i j)) {k₀ : Nat} {A : AS}
    (hl : LiveW C F A (trace m i k₀)) (hf : (trace m i k₀).frame = m.frame) (hd : m.fdot + 3 * k₀ ≤ (trace m i k₀).fdot) (hp : (trace m i k₀).pc ≠ C.cut) :
    (∃ k, k₀ < k ∧ (trace m i k).pc = C.cut ∧ (trace m i k).frame = m.frame ∧ m.fdot + 3 * k ≤ (trace m i k).fdot ∧
      ∃ B, C.atCut B = true ∧ Sim C.E F B (trace m i k)) ∨
    ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) := by
  have key : ∀ d, (∃ A, LiveW C F A (trace m i (k₀ + d)) ∧ (trace m i (k₀ + d)).frame = m.frame ∧ m.fdot + 3 * (k₀ + d) ≤ (trace m i (k₀ + d)).fdot ∧
        (trace m i (k₀ + d)).pc ≠ C.cut) ∨
      (∃ k, k₀ < k ∧ (trace m i k).pc = C.cut ∧ (trace m i k).frame = m.frame ∧ m.fdot + 3 * k ≤ (trace m i k).fdot ∧
        ∃ B, C.atCut B = true ∧ Sim C.E F B (trace m i k)) ∨
      ((trace m i (k₀ + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i (k₀ + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, hl, hf, hd, hp⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, _⟩ | hcut | ⟨h1, B, h2, h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k₀ + d)).frame ≥ m.frame + 1 || (trace m i (k₀ + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k₀ + (d + 1)) = (go step (trace m i (k₀ + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k₀ + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepW ht hkl hops h1 (hcl (k₀ + d)) with ⟨A', a1, _, a2, a3, a4⟩ | ⟨a1, a2, a3, B, b1, b3⟩ | ⟨a1, B, a2, a3⟩
        · rw [← e] at a1 a2 a3 a4
          exact Or.inl ⟨A', a1, a2.trans h2, by omega, a3⟩
        · rw [← e] at a1 a2 a3 b3
          exact Or.inr (Or.inl ⟨k₀ + (d + 1), by omega, a2, a1.trans h2, by omega, B, b1, b3⟩)
        · rw [← e] at a1 a3
          exact Or.inr (Or.inr ⟨by rw [a1, h2], B, a2, a3⟩)
      · exact Or.inr (Or.inl hcut)
      · have hst : ((trace m i (k₀ + d)).frame ≥ m.frame + 1 || (trace m i (k₀ + d)).halted) = true := by simp [h1]
        rw [show k₀ + (d + 1) = k₀ + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr (Or.inr ⟨h1, B, h2, h3⟩)
  have a1 := hl.1.hi
  have a2 := hl.1.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k₀) with ⟨A', h1, _, h3, _⟩ | hcut | ⟨_, B, h2, h3⟩
  · exfalso
    have : k₀ + (fuelPerFrame - k₀) = fuelPerFrame := by omega
    rw [this] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · exact Or.inl hcut
  · right
    rw [PipeEntryRule.frame_trace, show fuelPerFrame = k₀ + (fuelPerFrame - k₀) by omega]
    exact ⟨B, h2, h3⟩

end

section
variable {E : Env} {F : Nat × UInt8}

/-- **The timer's code**: from the machine `k₀` instructions into the frame of `m`, a walk `walkT` that succeeds comes to `stop` in the frame, in a state with `test` -/
theorem run_T {S : Spot} {G : Guard} {ops : Array (AM Unit)} {stop : UInt16} {test : AS → Bool} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat)
    {m : Machine} {i : UInt8} (hcl : ∀ j, CleanK G S.store (trace m i j)) :
    ∀ (n k₀ : Nat) (A : AS), walkT S G E ops stop test n A = true → Sim E F A (trace m i k₀) → (trace m i k₀).frame = m.frame →
      m.fdot + 3 * k₀ ≤ (trace m i k₀).fdot →
      ∃ k, k₀ < k ∧ (trace m i k).pc = stop ∧ (trace m i k).frame = m.frame ∧ m.fdot + 3 * k ≤ (trace m i k).fdot ∧ ∃ B, test B = true ∧ Sim E F B (trace m i k) := by
  intro n
  induction n with
  | zero => intro k₀ A hw; simp [walkT] at hw
  | succ n ih =>
    intro k₀ A hw hs hf hd
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK (hcl k₀) hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT (hcl k₀) hs1
    simp only [walkT, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      simp only [Bool.and_eq_true, beq_iff_eq] at hw2
      obtain ⟨hk, hw3⟩ := hw2
      have hh := hs.halted
      have hn : ¬ (((trace m i k₀).frame ≥ m.frame + 1 || (trace m i k₀).halted) = true) := by simp [hf, hh]
      have e : trace m i (k₀ + 1) = (go step (trace m i k₀)).2 := by
        show PipeEntryRule.nxt (m.frame + 1) (trace m i k₀) = _
        simp only [PipeEntryRule.nxt, if_neg hn]
      rcases h2 with ⟨_, k2, k3⟩ | ⟨k1, _⟩
      · rw [← e] at h1 k2 k3
        by_cases hst : B.pc = stop
        · rw [if_pos (by simp [hst])] at hw3
          exact ⟨k₀ + 1, by omega, by rw [h1.pc]; exact hst, k2.trans hf, by omega, B, hw3, h1⟩
        · rw [if_neg (by simp [hst])] at hw3
          obtain ⟨k, a1, a2, a3, a4, a5⟩ := ih (k₀ + 1) B hw3 h1 (k2.trans hf) (by omega)
          exact ⟨k, by omega, a2, a3, a4, a5⟩
      · exfalso
        rw [hk1] at k1
        omega

end

/-! ## One frame on the ROM -/

section
variable {sy : Syms} {m0 : Machine}

/-- what the check says -/
structure PhaseOK (sy : Syms) (m0 : Machine) : Prop where
  late : (guardPh sy m0).late < dotsPerFrame
  cutIdle : sy.DecTimers ≠ (guardPh sy m0).idle
  loop0 : loopAt sy m0 ≠ 0
  tB : (cfgs sy m0).2.t.all (walkW (cfgs sy m0).2 FrameKeep.fuelK) = true
  tA : (cfgs sy m0).1.t.all (walkW (cfgs sy m0).1 FrameKeep.fuelK) = true
  starts : (startsA (guardPh sy m0) (FrameKeep.pauseI sy m0) (tcI sy)).all (walkW (cfgs sy m0).1 FrameKeep.fuelK) = true

theorem phaseOK_of_check (h : phaseCheck sy m0 = true) : PhaseOK sy m0 := by
  simp only [phaseCheck, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem phaseI_lt (sy : Syms) (m0 : Machine) : phaseI sy m0 < 2048 := PipeTransitionAll.mask_lt _
theorem tcI_lt (sy : Syms) : tcI sy < 2048 := PipeTransitionAll.mask_lt _

/-- the master timer control, known 0 -/
theorem tc_mem {m : Machine} (h : m.ram.get! (tcI sy) = 0) : (AB.known 0).mem (m.ram.get! (tcI sy)) := by
  rw [h]
  exact mem_known_self 0

/-- the start of walk `A` covers the machine when the frame starts -/
theorem start_A (hO : PhaseOK sy m0) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (htc : m.ram.get! (tcI sy) = 0) :
    ∃ A, LiveW (cfgs sy m0).1 (m.frame, m.ram.get! (phaseI sy m0)) A (trace m i 0) := by
  have h0' : FrameStart (guardPh sy m0) (envPh sy m0) m :=
    ⟨h0.pc, h0.s, h0.dot, h0.ctrl, h0.s0, h0.strobe, h0.halted, h0.trk, h0.prg, h0.mask, h0.size, h0.known⟩
  obtain ⟨b, hs⟩ := PipeWrites.sim_startG (G := guardPh sy m0) (E := envPh sy m0) rfl h0'
  have hs2 := LagFrames.sim_rk hs rfl
  have hs3 : Sim (envPh sy m0) (m.frame, m.ram.get! (phaseI sy m0)) (LagFrames.startL (guardPh sy m0) b) (trace m i 0) :=
    { hs2 with pad := mem_top _ }
  have hs4 := PipeEntryRule.sim_setK' hs3 (CtrlKeep.low_mem ((trace m i 0).ram.get! (FrameKeep.pauseI sy m0)))
  have hs5 := PipeEntryRule.sim_setK' hs4 (d := tcI sy) (tc_mem (m := trace m i 0) htc)
  have hst := List.all_eq_true.1 hO.starts
  generalize ((trace m i 0).ram.get! (FrameKeep.pauseI sy m0) &&& 1 != 0) = p at hs5
  refine ⟨_, hs5, FrameKeep.fuelK, ?_⟩
  exact hst _ (by cases b <;> cases p <;> simp [startsA, startA])

/-- the low bit of the pause byte, known to be 1 -/
theorem paused_of {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim E F B m) (h : pauseIs (FrameKeep.pauseI sy m0) true B = true) :
    ¬ FrameKeep.Unpaused sy m0 m := by
  have h1 : m.ram.get! (FrameKeep.pauseI sy m0) &&& 1 = 1 :=
    CtrlKeep.low_of_bit (by simpa [pauseIs] using h) (hs.ram (FrameKeep.pauseI sy m0) (PipeTransitionAll.mask_lt _))
  intro hu
  unfold FrameKeep.Unpaused at hu
  rw [hu] at h1
  exact absurd h1 (by decide)

/-- the low bit of the pause byte, known to be 0 -/
theorem unpaused_of {E : Env} {F : Nat × UInt8} {B : AS} {m : Machine} (hs : Sim E F B m) (h : SideChangeEnd.notPausedK (FrameKeep.pauseI sy m0) B = true) :
    FrameKeep.Unpaused sy m0 m := by
  have h1 := SideChangeEnd.not_paused_of hs h
  rcases LagPause.bit0_cases (m.ram.get! (FrameKeep.pauseI sy m0)) with e | e
  · exact e
  · exact absurd e h1

theorem toNat_toUInt8 {x : UInt8} : x.toNat.toUInt8 = x := by simp

/-- **One frame in control keeps the phase exactly when it ends paused.** The frame starts in the idle loop in control (`StartK`), with the master timer control 0 and the
phase at most 20, and each of its instructions meets `CleanK` of `guardPh`. Then either it ends paused with the phase it began with, or it ends not paused with the phase
`next p = (p + 20) % 21`, as in the clock's rule. `hc` is the check on the ROM. -/
theorem phase_frame (hc : phaseCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (htc : m.ram.get! (tcI sy) = 0)
    (hp : (m.ram.get! (phaseI sy m0)).toNat ≤ 20) (hcl : ∀ j, CleanK (guardPh sy m0) (FrameKeep.spotOf sy m0).store (trace m i j)) :
    (¬ FrameKeep.Unpaused sy m0 (frame m i) ∧ (frame m i).ram.get! (phaseI sy m0) = m.ram.get! (phaseI sy m0)) ∨
    (FrameKeep.Unpaused sy m0 (frame m i) ∧ ((frame m i).ram.get! (phaseI sy m0)).toNat = next (m.ram.get! (phaseI sy m0)).toNat) := by
  have hO := phaseOK_of_check hc
  obtain ⟨A0, hl0⟩ := start_A hO (i := i) h0 htc
  have hp0 : (trace m i 0).pc ≠ (cfgs sy m0).1.cut := by
    show m.pc ≠ sy.DecTimers
    rw [h0.pc]
    exact fun h => hO.cutIdle h.symm
  rcases run_W hO.tA rfl rfl hcl hl0 rfl (by show m.fdot + 3 * 0 ≤ m.fdot; omega) hp0 with ⟨k₁, _, hk₁, hf₁, hd₁, B, hB, hs₁⟩ | ⟨B, hB, hs⟩
  · -- the cut: the phase is as it began; the timer's code from its value
    simp only [cfgs, cfgA, atCutA, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hB
    obtain ⟨⟨hr, hsp⟩, hT⟩ := hB
    have hsp' : B.spent = false := by simpa using hsp
    have hv : (trace m i k₁).ram.get! (phaseI sy m0) = m.ram.get! (phaseI sy m0) := rk_val hs₁ hr hsp'
    have hTp := hT (m.ram.get! (phaseI sy m0)).toNat (by omega)
    rw [toNat_toUInt8] at hTp
    have hs₂ : Sim (envPh sy m0) (m.frame, 2) (ofRk (phaseI sy m0) (m.ram.get! (phaseI sy m0)) B) (trace m i k₁) := sim_ofRk hs₁ hv _ rfl
    obtain ⟨k₂, _, hk₂, hf₂, hd₂, B', hB', hs₃⟩ := run_T (E := envPh sy m0) (F := (m.frame, 2)) rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hcl fuelT k₁ _ hTp hs₂ hf₁ hd₁
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hB'
    obtain ⟨⟨hK, hN⟩, hW⟩ := hB'
    have hq : (trace m i k₂).ram.get! (phaseI sy m0) = (B'.getK (phaseI sy m0)).v :=
      CtrlKeep.eq_of_known hK (hs₃.ram _ (phaseI_lt sy m0))
    have hs₄ := sim_toRk (E := envPh sy m0) hs₃
    have hl₄ : ∃ D, LiveW (cfgs sy m0).2 (m.frame, (trace m i k₂).ram.get! (phaseI sy m0)) D (trace m i k₂) := by
      rcases hW with h | h
      · obtain ⟨D, hD, _⟩ := cover_liveW hO.tB rfl hs₄ h
        exact ⟨D, hD⟩
      · exact ⟨_, hs₄, FrameKeep.fuelK, h⟩
    obtain ⟨D, hD⟩ := hl₄
    have hp₂ : (trace m i k₂).pc ≠ (cfgs sy m0).2.cut := by
      show (trace m i k₂).pc ≠ 0
      rw [hk₂]
      exact hO.loop0
    rcases run_W hO.tB rfl rfl hcl hD hf₂ hd₂ hp₂ with ⟨_, _, _, _, _, B₂, hB₂, _⟩ | ⟨B₂, hB₂, hs₅⟩
    · exact absurd hB₂ (by simp [cfgs, cfgB])
    · simp only [cfgs, cfgB, Bool.and_eq_true] at hB₂
      obtain ⟨⟨hr₂, hsp₂⟩, hnp⟩ := hB₂
      have hsp₂' : B₂.spent = false := by simpa using hsp₂
      have he : (frame m i).ram.get! (phaseI sy m0) = (trace m i k₂).ram.get! (phaseI sy m0) := rk_val hs₅ hr₂ hsp₂'
      refine Or.inr ⟨unpaused_of hs₅ hnp, ?_⟩
      rw [he, hq, hN]
  · -- the frame ends before the cut: paused, the phase as it began
    simp only [cfgs, cfgA, Bool.and_eq_true] at hB
    obtain ⟨⟨hr, hsp⟩, hpz⟩ := hB
    have hsp' : B.spent = false := by simpa using hsp
    exact Or.inl ⟨paused_of hs hpz, rk_val hs hr hsp'⟩

end

/-! ## The condition on one instruction, and the frames up to the touch -/

section
variable {sy : Syms} {m0 : Machine}

/-- **What is asked of one instruction**, besides `CleanK` of `guardE`: a store through an index or a pointer writes neither the phase nor the master timer control -/
def KeepsPhase (sy : Syms) (m0 : Machine) (m : Machine) : Prop :=
  ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ phaseI sy m0 ∧ (t &&& 0x7FF).toNat ≠ tcI sy

/-- `KeepsPhase` as a check, for a program -/
def keepsPhaseB (sy : Syms) (m0 : Machine) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000)) || ((t &&& 0x7FF).toNat != phaseI sy m0 && (t &&& 0x7FF).toNat != tcI sy)
  | none => true

/-- two more protected bytes -/
theorem clean_two {G : Guard} {x y : Nat} {q : UInt16} {m : Machine} (h : CleanK G q m)
    (hk : ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ x ∧ (t &&& 0x7FF).toNat ≠ y) :
    CleanK { G with prot := x :: y :: G.prot } q m := by
  refine ⟨fun t ht hq => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · obtain ⟨k1, k2⟩ := hk t ht h1
    refine Or.inl ⟨h1, fun hm => ?_⟩
    rcases List.mem_cons.1 hm with e | hm
    · exact k1 e
    · rcases List.mem_cons.1 hm with e | hm
      · exact k2 e
      · exact h2 hm
  · exact Or.inr h1

/-- `CleanK` of `guardE` and `KeepsPhase` give `CleanK` of `guardPh` -/
theorem cleanPh_of {q : UInt16} {m : Machine} (h : CleanK (FrameKeep.guardE sy m0) q m) (hk : KeepsPhase sy m0 m) : CleanK (guardPh sy m0) q m :=
  clean_two h hk

/-- fewer protected bytes -/
theorem clean_sub {G : Guard} {l : List Nat} {q : UInt16} {m : Machine} (h : CleanK G q m) (hl : ∀ x ∈ l, x ∈ G.prot) : CleanK { G with prot := l } q m := by
  refine ⟨fun t ht hq => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht hq with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, fun hm => h2 (hl _ hm)⟩
  · exact Or.inr h1

/-- `CleanK` of `guardPh` gives `CleanK` of the guard of the walk of the master timer control -/
theorem cleanTC_of {q : UInt16} {m : Machine} (h : CleanK (guardPh sy m0) q m) : CleanK (guardTC sy m0) q m := by
  refine clean_sub h fun x hx => ?_
  rcases List.mem_cons.1 hx with e | hm
  · exact List.mem_cons_of_mem _ (List.mem_cons.2 (Or.inl e))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hm)))

/-- **A frame before the touch's frame keeps the master timer control 0.** It starts in the idle loop in control with the watched bits of `FrameKeep`, each instruction
meets `CleanK` of `guardPh` and does not write the routine, the mode or the task by its address. `hc` is the check on the ROM. -/
theorem tc_frame (hc : tcCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hw : FrameKeep.Watched (FrameKeep.watchOf sy) m)
    (htc : m.ram.get! (tcI sy) = 0) (hcl : ∀ j, CleanK (guardPh sy m0) (FrameKeep.spotOf sy m0).store (trace m i j))
    (hx : ∀ j, FrameKeep.CtlStore sy (trace m i j) = false) : (frame m i).ram.get! (tcI sy) = 0 := by
  have h0' : FrameStart (guardTC sy m0) (PipeEntryRule.envOf m0) m := StartRun.start_mono h0 rfl rfl fun _ hp => hp
  have hw' : FrameKeep.Watched (watchTC sy) m := by
    intro w hw2
    rcases List.mem_append.1 hw2 with h | h
    · exact hw w h
    · rw [List.mem_singleton.1 h]
      show m.ram.get! (tcI sy) &&& 0xFF = (0 : UInt8) &&& 0xFF
      rw [htc]
  obtain ⟨_, h2⟩ := FrameKeep.keep_frame_startC hc rfl h0' hw' (fun j => cleanTC_of (hcl j)) hx
  have h3 : (frame m i).ram.get! (tcI sy) &&& 0xFF = (0 : UInt8) &&& 0xFF := h2 _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
  rw [FrameKeep.and_ff] at h3
  exact h3

/-- **The phase's rule on one frame**, from `m` to `m'`: it ends paused with the phase it began with, or it ends not paused with the phase `next p` -/
def PhaseRule (sy : Syms) (m0 : Machine) (m m' : Machine) : Prop :=
  (¬ FrameKeep.Unpaused sy m0 m' ∧ m'.ram.get! (phaseI sy m0) = m.ram.get! (phaseI sy m0)) ∨
  (FrameKeep.Unpaused sy m0 m' ∧ (m'.ram.get! (phaseI sy m0)).toNat = next (m.ram.get! (phaseI sy m0)).toNat)

theorem next_lt (p : Nat) : next p < 21 := Nat.mod_lt _ (by decide)

theorem next_ne (p : Nat) : next p ≠ p := by
  unfold next
  omega

/-- the phase stays at most 20 -/
theorem le20_of_rule {m m' : Machine} (h : PhaseRule sy m0 m m') (hp : (m.ram.get! (phaseI sy m0)).toNat ≤ 20) : (m'.ram.get! (phaseI sy m0)).toNat ≤ 20 := by
  rcases h with ⟨_, e⟩ | ⟨_, e⟩
  · rw [e]
    exact hp
  · rw [e]
    have := next_lt (m.ram.get! (phaseI sy m0)).toNat
    omega

/-- **The frames of `FrameKeep.Frames` up to the touch's frame follow the phase's rule.** The frames begin at control (`seq 0`, frame `a` of the run) in the idle loop in
control with the watched bits, the master timer control 0 and the phase at most 20 there; each instruction meets `KeepsPhase` besides `cleanE`. Then each frame `n` up
to the touch's frame begins with the master timer control 0 and the phase at most 20, and follows `PhaseRule`. `hc`, `hP`, `hT` are the checks on the ROM. -/
theorem frames_phase {S : FrameKeep.RealRun} {a g : Nat} {seq : Nat → Machine} (hc : FrameKeep.keepCheckOf sy m0 = true) (hP : phaseCheck sy m0 = true)
    (hT : tcCheck sy m0 = true) (K : FrameKeep.Frames sy m0 S a g seq) (hs0 : FrameKeep.StartK sy m0 (seq 0)) (h0 : FrameKeep.Watched (FrameKeep.watchOf sy) (seq 0))
    (htc : (S.seq a).ram.get! (tcI sy) = 0) (hp : ((S.seq a).ram.get! (phaseI sy m0)).toNat ≤ 20)
    (hk : ∀ n, n < K.ix g → ∀ j, KeepsPhase sy m0 (trace (S.seq (a + n)) (S.inp (a + n)) j)) :
    ∀ n, n < K.ix g → (S.seq (a + n)).ram.get! (tcI sy) = 0 ∧ ((S.seq (a + n)).ram.get! (phaseI sy m0)).toNat ≤ 20 ∧
      PhaseRule sy m0 (S.seq (a + n)) (S.seq (a + n + 1)) := by
  have hcl : ∀ n, n < K.ix g → ∀ j, CleanK (guardPh sy m0) (FrameKeep.spotOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) j) :=
    fun n hn j => cleanPh_of (K.cleanE n hn j) (hk n hn j)
  have hrule : ∀ n, n < K.ix g → (S.seq (a + n)).ram.get! (tcI sy) = 0 → ((S.seq (a + n)).ram.get! (phaseI sy m0)).toNat ≤ 20 →
      PhaseRule sy m0 (S.seq (a + n)) (S.seq (a + n + 1)) := by
    intro n hn h1 h2
    obtain ⟨a1, _⟩ := K.all_start hc hs0 h0 n hn
    have e : S.seq (a + n + 1) = frame (S.seq (a + n)) (S.inp (a + n)) := S.next (a + n)
    rw [e]
    exact phase_frame hP a1 h1 h2 (hcl n hn)
  intro n
  induction n with
  | zero =>
    intro hn
    exact ⟨htc, hp, hrule 0 hn htc hp⟩
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2, i3⟩ := ih (by omega)
    obtain ⟨a1, a2⟩ := K.all_start hc hs0 h0 n (by omega)
    have e : S.seq (a + (n + 1)) = frame (S.seq (a + n)) (S.inp (a + n)) := S.next (a + n)
    have t1 : (S.seq (a + (n + 1))).ram.get! (tcI sy) = 0 := by
      rw [e]
      exact tc_frame hT a1 a2 i1 (hcl n (by omega)) (K.noStore n hn)
    have t2 : ((S.seq (a + (n + 1))).ram.get! (phaseI sy m0)).toNat ≤ 20 := le20_of_rule i3 i2
    exact ⟨t1, t2, hrule (n + 1) hn t1 t2⟩

end

end Smbrta.PhaseFrame
