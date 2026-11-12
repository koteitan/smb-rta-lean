import Theorems.StartRun

/-!
# A frame that ends paused does not call the routine of the mode

The NMI calls the routine of the mode (`LagFrames.modeCall`) only when the low bit of the pause byte is 0, and then nothing in the routine writes that byte. So a frame from the
idle loop in control that calls the routine ends with the low bit 0: a frame that ends paused does not call it. This file proves that with two walks of the abstract machine of
`TaintRun`, as `FrameKeep` walks a whole frame, under one condition on each instruction: `Clean` of the guard `guardP` (the guard of a frame in control, `guardOf`, with the pause byte
among the bytes that a store with a target not known does not touch).

* The first walk starts with the low bit of the pause byte known (0 or 1: two starts), and stops where the NMI calls the routine. There the bit must be known to be 0, and the
  state must be covered by a state of the second walk's table. A path that ends the frame before the call asks nothing.
* The second walk goes from there to the frame's end (`FrameKeep.walkK`), and asks that the bit is known to be 0 at the end (`fin`).

`ends_unpaused`: a frame that calls the routine ends with the low bit 0. `no_call_of_paused`: a frame that ends with the low bit 1 does not call it.
There is no game data in this file. Page: `1-1/a-5-5-3-3-LagPause.md`.
-/

namespace Smbrta.LagPause

open PipeTransition (frame)
open PipeTransitionAll (go)
open TaintRun
open PipeWrites (Guard Clean FrameStart guardOf SG leK knownOf)
open PipeEntryRule (trace nxt frame_trace trace_stop)
open FrameKeep (Spot CfgK CleanK walkK coverK startK preK kstep normK keyK routeKW searchKW tableOfKW LiveK Watch)
open SideChangeEnd (notPausedK not_paused_of)

/-! ## The walks -/

/-- a guard with the byte `g` among the bytes that a store with a target not known does not touch -/
def guardWith (G : Guard) (g : Nat) : Guard := { G with prot := g :: G.prot }

/-- the guard: that of a frame in control (`guardOf`), with the pause byte `g` among the bytes that a store with a target not known does not touch -/
def guardP (sy : Syms) (m0 : Machine) (g : Nat) : Guard := guardWith (guardOf sy m0) g

/-- a store of `A` to the pause byte (`STA abs`), read from the program -/
def storesP (E : Env) (g : Nat) (pc : UInt16) : Bool :=
  E.prg.get! (pc &&& E.mask).toNat == 0x8D && (E.prg.get! ((pc + 1) &&& E.mask).toNat).toNat + 256 * ((E.prg.get! ((pc + 2) &&& E.mask).toNat).toNat &&& 0x07) == g

/-- the key of both searches: that of `FrameKeep`, with the pause byte in it, and `A` at a store of `A` to the pause byte (no part of the proof) -/
def keyP (E : Env) (G : Guard) (g : Nat) (A : AS) : Nat :=
  let n := keyK StartRun.noSpot G [(g, 0x01, 0)] A
  if storesP E g A.pc then n * 65536 + A.a.k.toNat * 256 + (A.a.v &&& A.a.k).toNat else n

/-- the two walks: the first up to the call, the second from the call to the frame's end -/
structure CfgP where
  K1 : CfgK
  K2 : CfgK
  /-- the pause byte -/
  g : Nat
  /-- where the NMI calls the routine of the mode -/
  call : UInt16

/-- the first walk: from `A`, step by step, until each path reaches the call (with the low bit of the pause byte known 0 and a state of the second table that covers it),
reaches a state of the first table, or ends the frame -/
def walkC (C : CfgP) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preK C.K1.S C.K1.G A).all fun A₁ => (kstep C.K1.S C.K1.G C.K1.E C.K1.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then
        if B.pc == C.call then notPausedK C.g B && coverK C.K2 B
        else (C.K1.cut.get! B.pc.toNat != 0 && coverK C.K1 B) || walkC C n B
      else true

/-- the start of the first walk: the low bit of the pause byte known to be `v` -/
def startP (G : Guard) (g : Nat) (v : UInt8) (late : Bool) : AS := startK G [(g, 0x01, v)] late

/-! ## Finding the tables: a search, no part of the proof -/

/-- the first search, from `A0`: as `FrameKeep.runKW`, but a state at the call is not followed; it is kept in the list of the calls -/
partial def runC (G : Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (call : UInt16) (X0 : SG) (c0 : Array AS) (A0 : AS) : SG × Array AS := Id.run do
  let S := StartRun.noSpot
  let mut X := X0
  let mut cuts := c0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preK S G cur).flatMap (kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some _ => false
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let same := (rs.filterMap id).filter fun b => b.k == cur.k
    for b in same do
      if b.pc == call then cuts := cuts.push b
    let good := same.filter fun b => b.pc != call
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
      X := routeKW S G key X b
    break
  return (X, cuts)

/-- the first search -/
partial def searchC (G : Guard) (E : Env) (key : AS → Nat) (call : UInt16) (starts : List AS) : SG × Array AS := Id.run do
  let ops := (aRows E).toArray
  let mut X : SG := starts.foldl (routeKW StartRun.noSpot G key) {}
  let mut cuts : Array AS := #[]
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      X := { X with pending := X.pending.erase k }
      let r := runC G E key ops call X cuts A
      X := r.1
      cuts := r.2
  return (X, cuts)

/-- the four starts: the low bit 0 or 1, early or late in the frame -/
def startsP (G : Guard) (g : Nat) : List AS := [startP G g 0 false, startP G g 0 true, startP G g 1 false, startP G g 1 true]

/-- the second search, from the calls: every call's key is in the table -/
def search2 (G : Guard) (E : Env) (key : AS → Nat) (cuts : Array AS) : SG :=
  let S := StartRun.noSpot
  let X0 := cuts.foldl (routeKW S G key) {}
  let X := searchKW S G E [] key (aRows E).toArray X0
  cuts.foldl (fun X b => { X with multi := X.multi.insert (key (normK S G b)) () }) X

/-- the two tables -/
def cfgP (sy : Syms) (m0 : Machine) (g : Nat) : CfgP :=
  let G := guardP sy m0 g
  let E := PipeEntryRule.envOf m0
  let key := keyP E G g
  let S := StartRun.noSpot
  let r := searchC G E key (LagFrames.modeCall sy) (startsP G g)
  let q1 := tableOfKW key r.1
  let q2 := tableOfKW key (search2 G E key r.2)
  { K1 := { E, ops := (aRows E).toArray, S, G, W := [], t := q1.1, kl := q1.1.map knownOf, idx := q1.2.1, cut := q1.2.2, key, fin := fun _ => true }
    K2 := { E, ops := (aRows E).toArray, S, G, W := [], t := q2.1, kl := q2.1.map knownOf, idx := q2.2.1, cut := q2.2.2, key, fin := notPausedK g }
    g, call := LagFrames.modeCall sy }

/-- **The check.** -/
def pauseCheck (sy : Syms) (m0 : Machine) (g : Nat) : Bool :=
  let C := cfgP sy m0 g
  decide ((guardP sy m0 g).late < dotsPerFrame) && decide (g < 2048) && C.call != (guardP sy m0 g).idle &&
    C.K2.t.all (walkK C.K2 FrameKeep.fuelK) && C.K1.t.all (walkC C FrameKeep.fuelK) &&
    (startsP (guardP sy m0 g) g).all (walkC C FrameKeep.fuelK)


/-! ## The condition on one instruction -/

/-- **What is asked of one instruction**, besides `Clean` of `guardOf`: a store through an index or a pointer does not write the pause byte -/
def KeepsPause (g : Nat) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ g

/-- `Clean` and `KeepsPause` give `Clean` of the guard with the pause byte -/
theorem clean_with {G : Guard} {m : Machine} {g : Nat} (h : Clean G m) (hk : KeepsPause g m) : Clean (guardWith G g) m := by
  refine ⟨fun t ht => ?_, h.read, h.jump, h.time⟩
  rcases h.store t ht with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, fun hm => ?_⟩
    rcases List.mem_cons.1 hm with e | e
    · exact hk t ht h1 e
    · exact h2 e
  · exact Or.inr h1

/-- a frame that starts with the guard starts with the guard with the pause byte -/
theorem start_with {G : Guard} {E : Env} {m : Machine} {g : Nat} (h : FrameStart G E m) : FrameStart (guardWith G g) E m :=
  StartRun.start_mono h rfl rfl fun _ hp => hp

/-! ## The walks cover the frame -/

section
variable {C : CfgP} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a first walk from `A` succeeds -/
def LiveC (C : CfgP) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.K1.E F A m ∧ ∃ n, walkC C n A = true

theorem cover_liveC (ht : C.K1.t.all (walkC C Fu) = true) (hkl : C.K1.kl = C.K1.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.K1.E F B m)
    (h : coverK C.K1 B = true) : ∃ D, LiveC C F D m ∧ D.k = B.k := by
  unfold coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l = knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

/-- one step of the first walk: it goes on (not at the call), or the machine is at the call and the second walk covers it, or the frame ends -/
theorem live_stepC (ht1 : C.K1.t.all (walkC C Fu) = true) (hkl1 : C.K1.kl = C.K1.t.map knownOf)
    (ht2 : C.K2.t.all (walkK C.K2 Fu) = true) (hkl2 : C.K2.kl = C.K2.t.map knownOf) (hE2 : C.K2.E = C.K1.E)
    (hops : C.K1.ops = (aRows C.K1.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine}
    (hl : LiveC C F A m) (hh : CleanK C.K1.G C.K1.S.store m) :
    (∃ A', LiveC C F A' (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ C.call) ∨
    (∃ D, LiveK C.K2 F D (go step m).2 ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    (go step m).2.frame = m.frame + 1 := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkC] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkC, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨_, k2⟩
      · rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        by_cases hc : B.pc = C.call
        · rw [if_pos (by simp [hc])] at hw2
          simp only [Bool.and_eq_true] at hw2
          have h1' : Sim C.K2.E F B (go step m).2 := by rw [hE2]; exact h1
          obtain ⟨D, hD, _⟩ := FrameKeep.cover_liveK ht2 hkl2 h1' hw2.2
          exact Or.inr (Or.inl ⟨D, hD, k2, k3⟩)
        · rw [if_neg (by simp [hc])] at hw2
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
          have hpc : (go step m).2.pc ≠ C.call := by rw [h1.pc]; exact hc
          rcases hw2 with ⟨_, h3⟩ | h3
          · obtain ⟨D, hD, _⟩ := cover_liveC ht1 hkl1 h1 h3
            exact Or.inl ⟨D, hD, k2, k3, hpc⟩
          · exact Or.inl ⟨B, ⟨h1, n, h3⟩, k2, k3, hpc⟩
      · exact Or.inr (Or.inr k2)

/-- **One frame, through the two walks.** From a state of the first walk that covers the machine, every instruction meeting `CleanK` of the two guards: the frame does not
come to the call, or it ends in a state that meets `fin` of the second walk -/
theorem frame_runP (ht1 : C.K1.t.all (walkC C Fu) = true) (hkl1 : C.K1.kl = C.K1.t.map knownOf)
    (ht2 : C.K2.t.all (walkK C.K2 Fu) = true) (hkl2 : C.K2.kl = C.K2.t.map knownOf) (hE2 : C.K2.E = C.K1.E)
    (hops1 : C.K1.ops = (aRows C.K1.E).toArray) (hops2 : C.K2.ops = (aRows C.K2.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.K1.E.pad = AB.top)
    {S : AS} {m : Machine} {i : UInt8} (hw : walkC C Fu S = true) (hs : Sim C.K1.E F S m) (hpc : m.pc ≠ C.call)
    (hk1 : ∀ j, CleanK C.K1.G C.K1.S.store (trace m i j)) (hk2 : ∀ j, CleanK C.K2.G C.K2.S.store (trace m i j)) :
    (∀ j, (trace m i j).frame = m.frame → (trace m i j).pc ≠ C.call) ∨ ∃ B, C.K2.fin B = true ∧ Sim C.K2.E F B (frame m i) := by
  have hs0 : Sim C.K1.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  have key : ∀ j, ((∃ A, LiveC C F A (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∧
        (∀ j', j' ≤ j → (trace m i j').frame = m.frame → (trace m i j').pc ≠ C.call)) ∨
      (∃ D, LiveK C.K2 F D (trace m i j) ∧ (trace m i j).frame = m.frame ∧ m.fdot + 3 * j ≤ (trace m i j).fdot) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∀ j', j' ≤ j → (trace m i j').frame = m.frame → (trace m i j').pc ≠ C.call) ∨
      ((trace m i j).frame = m.frame + 1 ∧ ∃ B, C.K2.fin B = true ∧ Sim C.K2.E F B (trace m i j)) := by
    intro j
    induction j with
    | zero =>
      refine Or.inl ⟨⟨S, ⟨hs0, Fu, hw⟩, rfl, Nat.le_refl _⟩, fun j' hj' _ => ?_⟩
      rw [show j' = 0 by omega]
      exact hpc
    | succ j ih =>
      have e : trace m i (j + 1) = nxt (m.frame + 1) (trace m i j) := rfl
      rcases ih with ⟨⟨A, h1, h3, h4⟩, hh⟩ | ⟨D, h1, h3, h4⟩ | ⟨h1, hh⟩ | ⟨h1, B, h2, h3⟩
      · have hl := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [h3, hl]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rcases live_stepC ht1 hkl1 ht2 hkl2 hE2 hops1 hT h1 (hk1 j) with ⟨A', a1, a3, a4, a5⟩ | ⟨D, a1, a3, a4⟩ | a3
        · refine Or.inl ⟨⟨A', by rw [e2]; exact a1, by rw [e2, a3, h3], by rw [e2]; omega⟩, fun j' hj' hf => ?_⟩
          by_cases hj : j' ≤ j
          · exact hh j' hj hf
          · rw [show j' = j + 1 by omega, e2]
            exact a5
        · exact Or.inr (Or.inl ⟨D, by rw [e2]; exact a1, by rw [e2, a3, h3], by rw [e2]; omega⟩)
        · refine Or.inr (Or.inr (Or.inl ⟨by rw [e2, a3, h3], fun j' hj' hf => ?_⟩))
          by_cases hj : j' ≤ j
          · exact hh j' hj hf
          · rw [show j' = j + 1 by omega, e2, a3, h3] at hf
            omega
      · have hl := h1.1.halted
        have hc : ¬ (((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true) := by simp [h3, hl]
        have e2 : trace m i (j + 1) = (go step (trace m i j)).2 := by
          rw [e]
          simp only [nxt, if_neg hc]
        rcases FrameKeep.live_stepK ht2 hkl2 hops2 hT h1 (hk2 j) with ⟨D', a1, _, a3, a4⟩ | ⟨a1, B, _, _, a2, _, a4⟩
        · exact Or.inr (Or.inl ⟨D', by rw [e2]; exact a1, by rw [e2, a3, h3], by rw [e2]; omega⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨by rw [e2, a1, h3], B, a2, by rw [e2]; exact a4⟩))
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        refine Or.inr (Or.inr (Or.inl ⟨by rw [e2]; exact h1, fun j' hj' hf => ?_⟩))
        by_cases hj : j' ≤ j
        · exact hh j' hj hf
        · rw [show j' = j + 1 by omega, e2, h1] at hf
          omega
      · have hc : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [h1]
        have e2 : trace m i (j + 1) = trace m i j := by
          rw [e]
          simp only [nxt, if_pos hc]
        exact Or.inr (Or.inr (Or.inr ⟨by rw [e2]; exact h1, B, h2, by rw [e2]; exact h3⟩))
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key fuelPerFrame with ⟨⟨A, h1, _, h4⟩, _⟩ | ⟨D, h1, _, h4⟩ | ⟨h1, hh⟩ | ⟨h1, B, h2, h3⟩
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    omega
  · exfalso
    have a1 := h1.1.hi
    have a2 := h1.1.lim
    omega
  · left
    intro j hf
    by_cases hj : j ≤ fuelPerFrame
    · exact hh j hj hf
    · have hst : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [h1]
      have e := trace_stop hst (j - fuelPerFrame)
      rw [show fuelPerFrame + (j - fuelPerFrame) = j by omega] at e
      rw [e, h1] at hf
      omega
  · right
    rw [frame_trace]
    exact ⟨B, h2, h3⟩

end

/-! ## One frame on the ROM -/

/-- what the check says -/
structure PauseOK (sy : Syms) (m0 : Machine) (g : Nat) : Prop where
  late : (guardP sy m0 g).late < dotsPerFrame
  g2048 : g < 2048
  callIdle : LagFrames.modeCall sy ≠ (guardP sy m0 g).idle
  t2 : (cfgP sy m0 g).K2.t.all (walkK (cfgP sy m0 g).K2 FrameKeep.fuelK) = true
  t1 : (cfgP sy m0 g).K1.t.all (walkC (cfgP sy m0 g) FrameKeep.fuelK) = true
  starts : (startsP (guardP sy m0 g) g).all (walkC (cfgP sy m0 g) FrameKeep.fuelK) = true

theorem pauseOK_of_check {sy : Syms} {m0 : Machine} {g : Nat} (h : pauseCheck sy m0 g = true) : PauseOK sy m0 g := by
  simp only [pauseCheck, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem bit0_all : ∀ n : Fin 256, (UInt8.ofNat n.val &&& 1 = 0) ∨ (UInt8.ofNat n.val &&& 1 = 1) := by decide +kernel

theorem bit0_cases (x : UInt8) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h := bit0_all ⟨x.toNat, x.toNat_lt⟩
  simpa using h

/-- **A frame that calls the routine of the mode ends with the low bit of the pause byte 0.** The frame starts in the idle loop in control, and each of its instructions is
`Clean` (`guardOf`) and does not write the pause byte through an index or a pointer (`KeepsPause`). `hc` is the check on the ROM. -/
theorem ends_unpaused {sy : Syms} {m0 : Machine} {g : Nat} (hc : pauseCheck sy m0 g = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) m) (hcl : ∀ k, Clean (guardOf sy m0) (trace m i k)) (hkp : ∀ k, KeepsPause g (trace m i k))
    (hx : ∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = LagFrames.modeCall sy) : (frame m i).ram.get! g &&& 1 ≠ 1 := by
  have hO := pauseOK_of_check hc
  have h0' : FrameStart (guardWith (guardOf sy m0) g) (PipeEntryRule.envOf m0) m := start_with h0
  have hw : FrameKeep.Watched [(g, (0x01 : UInt8), m.ram.get! g &&& 1)] m := by
    intro w hw
    rw [List.mem_singleton.1 hw]
    show m.ram.get! g &&& 1 = (m.ram.get! g &&& 1) &&& 1
    rw [UInt8.and_assoc, UInt8.and_self]
  obtain ⟨b, hs⟩ := FrameKeep.sim_startK (G := guardP sy m0 g) rfl h0' hw
  have hst : walkC (cfgP sy m0 g) FrameKeep.fuelK (startP (guardP sy m0 g) g (m.ram.get! g &&& 1) b) = true := by
    have hall := List.all_eq_true.1 hO.starts
    rcases bit0_cases (m.ram.get! g) with e | e <;> rw [e] <;> cases b <;> exact hall _ (by simp [startsP])
  have hcl' : ∀ j, CleanK (guardP sy m0 g) StartRun.noSpot.store (trace m i j) := fun j => StartRun.cleanK_of_clean (clean_with (hcl j) (hkp j))
  rcases frame_runP (C := cfgP sy m0 g) (Fu := FrameKeep.fuelK) (F := (m.frame, 2)) hO.t1 rfl hO.t2 rfl rfl rfl rfl (show 2 ≤ (2 : UInt8).toNat by decide) rfl hst hs
      (by rw [h0.pc]; exact fun h => hO.callIdle h.symm) hcl' hcl' with h | ⟨B, h1, h2⟩
  · obtain ⟨k, hk1, hk2⟩ := hx
    exact absurd hk2 (h k hk1)
  · exact not_paused_of h2 h1

/-- **A frame that ends paused does not call the routine of the mode**, under the same conditions -/
theorem no_call_of_paused {sy : Syms} {m0 : Machine} {g : Nat} (hc : pauseCheck sy m0 g = true) {m : Machine} {i : UInt8}
    (h0 : FrameStart (guardOf sy m0) (PipeEntryRule.envOf m0) m) (hcl : ∀ k, Clean (guardOf sy m0) (trace m i k)) (hkp : ∀ k, KeepsPause g (trace m i k))
    (hp : (frame m i).ram.get! g &&& 1 = 1) : ¬ ∃ k, (trace m i k).frame = m.frame ∧ (trace m i k).pc = LagFrames.modeCall sy :=
  fun hx => ends_unpaused hc h0 hcl hkp hx hp

end Smbrta.LagPause
