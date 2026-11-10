import Theorems.LagFrames
import Theorems.FrameKeep
import Theorems.FrameModel

/-!
# A frame in control, up to the player's routine

A frame that starts in the idle loop in control (`FrameKeep.StartK`) runs the screen, the sound, the pad, the pause and the timers, then the mode's routine, which
calls the player's routine. Here the abstract machine of `TaintRun` follows the frame from its start to the first time it comes to the player's routine (the cut),
as `LagFrames` follows a frame to the call of the mode's routine. One byte is followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on any write to it.
At the cut the walk asks that the byte is still followed, so it has the value it had at the frame's start. There is one walk for each byte of `keepI`.
At the cut the walk also asks the stack pointer of the player's routine, no NMI pending, the NMI off in the PPU, and the routine byte of control.

The condition on each instruction before the cut is `FrameKeep.CleanK` (the condition of `PipeWrites.Clean`, but the move routine's store): the walk asks that no state
before the cut is at that store. A store with a target not known makes the walk forget the followed byte, so the walk fails if one comes before the cut.

The searches are no part of the proof: the check walks every state of its table. There is no game data in this file. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.CtrlKeep

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites
open PipeEntryRule (trace)
open LagFrames (preL opOf startL)

/-- the key: the `pc`, the stack, the flags of the frame, the counter, both index registers, and `A` and `Y` near the jump routine -/
def keyR (G : Guard) (A : AS) : Nat :=
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0) + (if A.rk then 16 else 0) + (if A.spent then 32 else 0)
  let n := (n * 65536 + num A.x) * 65536 + num A.y
  let n := if G.je ≤ A.pc && A.pc ≤ G.je + 18 then n * 65536 + num A.a else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

/-! ## The walk -/

/-- the table, and what the walk asks at the cut -/
structure CfgR where
  E : Env
  ops : Array (AM Unit)
  G : Guard
  /-- the walk stops at this `pc`: the player's routine -/
  cut : UInt16
  /-- the move routine's store: no state before the cut is there -/
  q : UInt16
  /-- the stack pointer at the cut -/
  S : UInt8
  /-- the routine byte, and its value at the cut -/
  engI : Nat
  eng : UInt8
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  /-- the `pc` of the states of the table -/
  tc : ByteArray

/-- what the walk asks at the cut: the byte still followed and not decremented, the stack pointer, no NMI pending, the NMI off, the routine byte -/
def atCut (C : CfgR) (B : AS) : Bool :=
  B.rk && !B.spent && B.s == C.S && !B.nmi && B.ppuCtrl.bit 0x80 == some false && (B.getK C.engI).isK && (B.getK C.engI).v == C.eng

def coverR (C : CfgR) (B : AS) : Bool :=
  match C.idx[keyR C.G B]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path comes to the cut with `atCut`, ends the frame, or reaches a state of the table. No state is at the move routine's store,
and no step is `DEC abs` of the byte. -/
def walkR (C : CfgR) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => A.pc != C.q && (preL C.G A).all fun A₁ => !isRkDec C.E A₁.pc (opOf C.E A₁) && (gsucc C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        (if B.pc == C.cut then atCut C B else (C.tc.get! B.pc.toNat != 0 && coverR C B) || walkR C n B)
      else B.k == A.k + 1

/-- **The check of one byte.** -/
def ctrlCheck1 (C : CfgR) : Bool :=
  decide (C.G.late < dotsPerFrame) && C.cut != C.G.idle && C.t.all (walkR C fuelG) && walkR C fuelG (startL C.G false) && walkR C fuelG (startL C.G true)

/-! ## On the ROM -/

/-- **The bytes that a frame in control keeps up to the player's routine**: the horizontal state and the position (`FrameModel.hBytes`), the collision bits, the stored
speed, the area's type, the jumpspring, the swimming flag, the change of size, the vertical bytes and the jump's halt value (`SurfaceFrames.vKeep`), A and B, and A and B
of the frame before. -/
def keepA (sy : Syms) : List UInt16 :=
  [sy.Player_X_Speed, sy.Player_X_MoveForce, sy.PlayerFacingDir, sy.Player_MovingDir, sy.RunningSpeed, sy.Player_X_Position, sy.Player_PageLoc, sy.SprObject_X_MoveForce,
   sy.Player_CollisionBits, sy.Player_XSpeedAbsolute, sy.AreaType, sy.JumpspringAnimCtrl, sy.SwimmingFlag, sy.PlayerChangeSizeFlag,
   sy.Player_Y_Position, sy.Player_Y_MoveForce, sy.Player_Y_Speed, sy.Player_YMF_Dummy, sy.VerticalForce, sy.VerticalForceDown, sy.JumpOrigin_Y_Position,
   sy.Player_State, sy.DiffToHaltJump, sy.A_B_Buttons, sy.PreviousA_B_Buttons]

def keepI (sy : Syms) : List Nat := (keepA sy).map fun a => (a &&& 0x7FF).toNat

/-- the machine of the walk, with the byte `b` followed -/
def envR (m0 : Machine) (b : Nat) : Env := { PipeEntryRule.envOf m0 with rkI := b }

/-! ## Finding the table: a search, no part of the proof

As the search of `LagFrames`, but it forgets no byte of RAM, and the index registers are in the key: the loops before the player's routine store through an index
(the timers, the random bits, the top score), and the check knows the target of such a store only if the index is known. -/

/-- what the search forgets: the stack below the stack pointer -/
def normR (G : Guard) (A0 : AS) : AS :=
  let A := { A0 with padShift := AB.top }
  if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
  let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) A.kn
  { A with kn }

def routeR (G : Guard) (X : LagFrames.SL) (B0 : AS) : LagFrames.SL :=
  let B := normR G B0
  let K := keyR G B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runR (G : Guard) (E : Env) (ops : Array (AM Unit)) (cut : UInt16) (X0 : LagFrames.SL) (A0 : AS) : LagFrames.SL := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preL G cur).flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (fun r => r.isNone) then X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
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
      X := routeR G X b
    break
  return X

partial def searchR (G : Guard) (E : Env) (cut : UInt16) : LagFrames.SL := Id.run do
  let ops := (aRows E).toArray
  let mut X : LagFrames.SL := [startL G false, startL G true].foldl (routeR G) {}
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runR G E ops cut X A
  return X

/-- the table, from the search -/
def tableOfR (G : Guard) (X : LagFrames.SL) : Array AS × Std.HashMap Nat Nat × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat Nat := {}
  let mut tc := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert (keyR G A) t.size
      tc := tc.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, tc)

/-- the table: one search serves every byte, since no step before the cut stores through a target not known -/
abbrev Table := Array AS × Std.HashMap Nat Nat × ByteArray

def cutTable (sy : Syms) (m0 : Machine) : Table :=
  let G := FrameKeep.guardK sy m0
  tableOfR G (searchR G (envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) sy.PlayerCtrlRoutine)

/-- the walk of the byte `b`, with the table `q` -/
def cfgOf (sy : Syms) (m0 : Machine) (q : Table) (b : Nat) : CfgR :=
  { E := envR m0 b, ops := (aRows (envR m0 b)).toArray, G := FrameKeep.guardK sy m0, cut := sy.PlayerCtrlRoutine, q := (FrameKeep.spotOf sy m0).store,
    S := FrameModel.ctrlStack sy m0, engI := (sy.GameEngineSubroutine &&& 0x7FF).toNat, eng := sy.Eng_PlayerCtrl.toUInt8, t := q.1, kl := q.1.map knownOf,
    idx := q.2.1, tc := q.2.2 }

/-- the walk of the byte `b`, as the program runs it -/
def cfgR (sy : Syms) (m0 : Machine) (b : Nat) : CfgR := cfgOf sy m0 (cutTable sy m0) b

/-- **The check**, for every byte of `keepI` -/
def ctrlCheck (sy : Syms) (m0 : Machine) : Bool :=
  let q := cutTable sy m0
  (keepI sy).all fun b => ctrlCheck1 (cfgOf sy m0 q b)

/-! ## The walk covers the frame up to the cut -/

section
variable {C : CfgR} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveR (C : CfgR) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkR C n A = true

theorem cover_liveR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0)
    (h : coverR C B = true) : ∃ D, LiveR C F D m := by
  unfold coverR at h
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

/-- one step: the walk goes on, or the machine comes to the cut with `atCut`, or the frame ends -/
theorem live_stepR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveR C F A m) (hc : FrameKeep.CleanK C.G C.q m) :
    (∃ A', LiveR C F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ (go step m).2.pc ≠ C.cut) ∨
    ((go step m).2.frame = m.frame ∧ (go step m).2.pc = C.cut ∧ ∃ B, atCut C B = true ∧ Sim C.E F B (go step m).2) ∨
    (go step m).2.frame = m.frame + 1 := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkR] at hw
  | succ n =>
    simp only [walkR, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hw
    obtain ⟨hq, hw⟩ := hw
    have hc' : Clean C.G m := FrameKeep.clean_of hc (fun h => hq (hs.pc ▸ h.1))
    obtain ⟨A₁, hA, hs1, hk1⟩ := LagFrames.cov_preL hc' hs
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    have hd' : isRkDec C.E A₁.pc (opOf C.E A₁) = false := by simpa using hd
    obtain ⟨r, hr1, hB⟩ := LagFrames.s_gsuccL hops hd' hc' hs1
    have hw3 := hw2 r hr1
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, _⟩ | ⟨_, k2⟩
      · rw [if_pos (by simp [k1, hk1])] at hw3
        by_cases hcut : B.pc = C.cut
        · rw [if_pos (by simp [hcut])] at hw3
          exact Or.inr (Or.inl ⟨k2, by rw [h1.pc]; exact hcut, B, hw3, h1⟩)
        · rw [if_neg (by simp [hcut])] at hw3
          have hcut' : (go step m).2.pc ≠ C.cut := by rw [h1.pc]; exact hcut
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw3
          rcases hw3 with ⟨_, h4⟩ | h4
          · obtain ⟨D, hD⟩ := cover_liveR ht hkl h1 (by omega) h4
            exact Or.inl ⟨D, hD, k2, hcut'⟩
          · exact Or.inl ⟨B, ⟨h1, by omega, n, h4⟩, k2, hcut'⟩
      · exact Or.inr (Or.inr k2)

/-- the instructions of the frame up to its first arrival at the cut -/
theorem frame_runR (ht : C.t.all (walkR C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) {M : Machine} {i : UInt8}
    (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace M i n)) {k : Nat} (hk : (trace M i k).pc = C.cut) (hf : (trace M i k).frame = M.frame)
    (hfirst : ∀ j, j < k → (trace M i j).pc ≠ C.cut) :
    ∀ (d j : Nat) (A : AS), j + d = k → LiveR C F A (trace M i j) → (trace M i j).frame = M.frame → (trace M i j).pc ≠ C.cut →
      ∃ B, atCut C B = true ∧ Sim C.E F B (trace M i k) := by
  intro d
  induction d with
  | zero =>
    intro j A hj _ _ hp
    rw [Nat.add_zero] at hj
    rw [hj] at hp
    exact absurd hk hp
  | succ d ih =>
    intro j A hj hl hfj _
    have hh := hl.1.halted
    have e : trace M i (j + 1) = (go step (trace M i j)).2 := by
      show PipeEntryRule.nxt (M.frame + 1) (trace M i j) = _
      have hn : ¬ ((trace M i j).frame ≥ M.frame + 1 || (trace M i j).halted) = true := by simp [hfj, hh]
      simp only [PipeEntryRule.nxt, if_neg hn]
    rcases live_stepR ht hkl hops hl (hcl j) with ⟨A', h1, h2, h3⟩ | ⟨h1, h2, B, h3, h4⟩ | h1
    · rw [← e] at h1 h2 h3
      exact ih (j + 1) A' (by omega) h1 (h2.trans hfj) h3
    · rw [← e] at h1 h2 h4
      have hjk : j + 1 = k := by
        by_cases h5 : j + 1 < k
        · exact absurd h2 (hfirst (j + 1) h5)
        · omega
      rw [← hjk]
      exact ⟨B, h3, h4⟩
    · rw [← e] at h1
      exfalso
      have hst : ((trace M i (j + 1)).frame ≥ M.frame + 1 || (trace M i (j + 1)).halted) = true := by simp [h1, hfj]
      have e2 := PipeEntryRule.trace_stop hst d
      rw [show j + 1 + d = k by omega] at e2
      rw [e2, h1, hfj] at hf
      omega

/-- **One byte.** A frame from the idle loop in control whose instructions meet `CleanK` comes to the cut, the first time, in a state that the walk covers with `atCut`:
the followed byte is as it began. -/
theorem at_cut (hO : ctrlCheck1 C = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hE : C.E.pad = AB.top)
    {m : Machine} {i : UInt8} (h0 : FrameStart C.G C.E m) (hcl : ∀ n, FrameKeep.CleanK C.G C.q (trace m i n))
    {k : Nat} (hk : (trace m i k).pc = C.cut) (hf : (trace m i k).frame = m.frame) (hfirst : ∀ j, j < k → (trace m i j).pc ≠ C.cut) :
    ∃ B, atCut C B = true ∧ Sim C.E (m.frame, m.ram.get! C.E.rkI) B (trace m i k) := by
  simp only [ctrlCheck1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hO
  obtain ⟨⟨⟨⟨_, hci⟩, ht⟩, hs0⟩, hs1⟩ := hO
  obtain ⟨b, hs⟩ := sim_startG hE h0
  have hs2 := LagFrames.sim_rk hs rfl
  have hs3 : Sim C.E (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := { hs2 with pad := by rw [hE]; exact mem_top _ }
  have hl : LiveR C (m.frame, m.ram.get! C.E.rkI) (startL C.G b) (trace m i 0) := by
    refine ⟨hs3, rfl, fuelG, ?_⟩
    cases b
    · exact hs0
    · exact hs1
  have hp0 : (trace m i 0).pc ≠ C.cut := by
    show m.pc ≠ C.cut
    rw [h0.pc]
    exact fun h => hci h.symm
  exact frame_runR ht hkl hops hcl hk hf hfirst k 0 _ (by omega) hl rfl hp0

end

/-! ## On the ROM -/

section
variable {sy : Syms} {m0 : Machine}

theorem bit80_false_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 0x80 != 0) = false → UInt8.ofNat n.val &&& 0x80 = 0 := by decide +kernel

/-- a known bit 7 that is 0 -/
theorem nmi_off_of {b : AB} {x : UInt8} (h : (b.bit 0x80 == some false) = true) (hm : b.mem x) : x &&& 0x80 = 0 := by
  unfold AB.bit at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq, Option.some.injEq] at h hk
    have e : (x &&& b.k) &&& 0x80 = (b.v &&& b.k) &&& 0x80 := by rw [show x &&& b.k = b.v &&& b.k from hm]
    rw [UInt8.and_assoc, UInt8.and_assoc, hk] at e
    rw [e]
    have h1 := bit80_false_all ⟨b.v.toNat, b.v.toNat_lt⟩
    simp only [UInt8.ofNat_toNat] at h1
    exact h1 (by rw [h])
  · simp at h

/-- a known byte -/
theorem eq_of_known {b : AB} {x : UInt8} (hk : b.isK = true) (hm : b.mem x) : x = b.v := by
  have e : b.k = 0xFF := by simpa [AB.isK] using hk
  have h1 : x &&& b.k = b.v &&& b.k := hm
  rw [e, FrameKeep.and_ff, FrameKeep.and_ff] at h1
  exact h1

/-- **The machine when a frame in control first comes to the player's routine**: it has the bytes of `keepA` of the frame's start, the stack pointer of the player's
routine, no NMI pending and the NMI off, and the routine byte of control. -/
structure AtCut (sy : Syms) (m0 m R : Machine) : Prop where
  keep : ∀ x ∈ keepA sy, peek R x = peek m x
  s : R.s = FrameModel.ctrlStack sy m0
  good : FrameModel.Good (FrameModel.Rom.of m0) R
  eng : peek R sy.GameEngineSubroutine = sy.Eng_PlayerCtrl.toUInt8

theorem cfg_start (q : Table) (b : Nat) {m : Machine} (h0 : FrameKeep.StartK sy m0 m) : FrameStart (cfgOf sy m0 q b).G (cfgOf sy m0 q b).E m :=
  ⟨h0.pc, h0.s, h0.dot, h0.ctrl, h0.s0, h0.strobe, h0.halted, h0.trk, h0.prg, h0.mask, h0.size, h0.known⟩

/-- **A frame in control, up to the player's routine.** The frame starts in the idle loop in control (`FrameKeep.StartK`) and each instruction meets `FrameKeep.CleanK`.
The first time it comes to the player's routine, in the same frame, it has the bytes of `keepA` it began with, and the state of `FrameModel.AtCtrl0` but the values.
`hc` is the check on the ROM. -/
theorem ctrl_keep (hc : ctrlCheck sy m0 = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) {k : Nat}
    (hk : (trace m i k).pc = sy.PlayerCtrlRoutine) (hf : (trace m i k).frame = m.frame)
    (hfirst : ∀ j, j < k → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) : AtCut sy m0 m (trace m i k) := by
  unfold ctrlCheck at hc
  generalize cutTable sy m0 = q at hc
  have one : ∀ b ∈ keepI sy, ∃ B, atCut (cfgOf sy m0 q b) B = true ∧ Sim (envR m0 b) (m.frame, m.ram.get! b) B (trace m i k) := by
    intro b hb
    exact at_cut (C := cfgOf sy m0 q b) ((List.all_eq_true.1 hc) b hb) rfl rfl rfl (cfg_start q b h0) hcl hk hf hfirst
  have hx : (sy.Player_X_Speed &&& 0x7FF).toNat ∈ keepI sy := List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩
  obtain ⟨B, hB, hs⟩ := one _ hx
  simp only [atCut, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hS⟩, hn⟩, hctl⟩, hek⟩, hev⟩ := hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxm
    obtain ⟨B', hB', hs'⟩ := one _ (List.mem_map.2 ⟨x, hxm, rfl⟩)
    simp only [atCut, Bool.and_eq_true, Bool.not_eq_true'] at hB'
    have h1 := hs'.rkv hB'.1.1.1.1.1.1
    rw [if_neg (by simp [hB'.1.1.1.1.1.2])] at h1
    exact h1
  · rw [hs.s]
    exact hS
  · exact ⟨hs.prg, hs.mask, by rw [hs.nmi]; exact hn, hs.halted, hs.trk, hs.size, nmi_off_of (by rw [hctl]; rfl) hs.ppuCtrl⟩
  · have hlt : (sy.GameEngineSubroutine &&& 0x7FF).toNat < 2048 := PipeTransitionAll.mask_lt _
    have h1 := hs.ram _ hlt
    have h2 := eq_of_known hek h1
    show (trace m i k).ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat = _
    rw [h2]
    exact hev

end

/-! ## A program: where the walk fails, no part of the proof -/

/-- the walk of `walkR`, returning where it fails first -/
def whyR (C : CfgR) : Nat → AS → Option (String × Nat)
  | 0, A => some ("fuel", A.pc.toNat)
  | n + 1, A => Id.run do
    if A.pc == C.q then return some ("store", A.pc.toNat)
    for A₁ in preL C.G A do
      if isRkDec C.E A₁.pc (opOf C.E A₁) then return some ("dec", A₁.pc.toNat)
      for r in gsucc C.G C.E C.ops A₁ do
        match r with
        | none => return some ("step", A₁.pc.toNat)
        | some B =>
          if A₁.rk && !B.rk then return some (s!"rkdrop x {A₁.x.v}/{A₁.x.k} y {A₁.y.v}/{A₁.y.k}", A₁.pc.toNat)
          if A₁.ppuCtrl.bit 0x80 != none && B.ppuCtrl.bit 0x80 == none then return some ("ctldrop", A₁.pc.toNat)
          if B.k == A.k then
            if B.pc == C.cut then
              if !atCut C B then
                return some (s!"cut rk {B.rk} spent {B.spent} s {B.s}/{C.S} nmi {B.nmi} ctl {B.ppuCtrl.v}/{B.ppuCtrl.k} eng {(B.getK C.engI).v}/{(B.getK C.engI).k}", A₁.pc.toNat)
            else if C.tc.get! B.pc.toNat != 0 && coverR C B then pure ()
            else
              match whyR C n B with
              | some w => return some w
              | none => pure ()
          else if B.k != A.k + 1 then return some ("end", A₁.pc.toNat)
    return none

end Smbrta.CtrlKeep
