import Theorems.CollKeep

/-!
# Above ground: the speed after the scroll handler

A frame in control comes to the player's routine (the cut of `CtrlKeep`), and from there to the scroll handler (`PlayerSubs`), as in `AfterKeep`. From the scroll handler
to the frame's end, the speed is written on four paths: the screen's left edge, the collision routine (`ImpedePlayerMove`) and the climbing routine store 0, and the
death stores a value that the walk does not know, but then writes the routine by its address (a path that `FrameKeep.Frames.noStore` cuts).

Here a walk follows the speed from the scroll handler to the frame's end as the counter of `TaintRun` (`Env.rkI`), as the second walk of `AfterKeep` does, but before a
store to it by its address it stops following it (`rkOff`). At the frame's end it asks (`finV`) that the speed is still followed, or that it is known to be 0. The guard
protects the speed: no store through an index or a pointer writes it. `FrameKeep.guardE` protects it (`FrameKeep.speedE`), so `CleanK` of `guardE` gives `CleanK` of the
walk's guard (`cleanV_of`), and the one-instruction condition `SpareV` (the old field `spareV` of the frames above ground) is a part of it (`spareV_of`).

So (`speed_end`): at the frame's end the speed is the speed at the scroll handler, or 0. This is `SurfaceRead.CollideE.v`.

The subspeed is in `FaceKeep`: the climbing routine sets it to 0 after the speed, so the same walk with the end "still followed, or the speed and the subspeed are known
to be 0" closes. With the end "still followed, or the player's state is not 0, 1 or 2" it does not (an experiment, `collide-keep-check`): the climbing routine sets the
player's state to climbing, and on one path of the walk a platform's collision then sets the state to normal in the same frame.

The searches are no part of the proof. No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.CollideKeep

open TaintRun
open PipeWrites (SG)

/-! ## The bytes -/

/-- the speed -/
def spI (sy : Syms) : Nat := (sy.Player_X_Speed &&& 0x7FF).toNat

/-- the subspeed (for the experiment only) -/
def sfI (sy : Syms) : Nat := (sy.Player_X_MoveForce &&& 0x7FF).toNat

/-- the player's state (for the experiment only) -/
def stI (sy : Syms) : Nat := (sy.Player_State &&& 0x7FF).toNat

/-- **A store through an index or a pointer does not write the speed** (one instruction): a part of `CleanK` of `FrameKeep.guardE` (`spareV_of`) -/
def SpareV (sy : Syms) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ [spI sy]

/-- `SpareV`, for a program -/
def spareVB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && (t &&& 0x7FF).toNat == spI sy)
  | none => true

/-- the guard of the walk: that of `FrameKeep.guardF`, with the speed protected too -/
def guardV (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := [spI sy] ++ (FrameKeep.guardF sy m0).prot }

/-! ## The walk -/

/-- **The byte is no longer followed** before an instruction that writes it by its address -/
def rkOff (E : Env) (A : AS) : List AS :=
  if A.rk && FrameKeep.storesTo [E.rkI] E.prg E.mask A.pc then [{ A with rk := false, spent := false }] else [A]

/-- the byte `b` is known to be 0 -/
def zeroAt (b : Nat) (B : AS) : Bool := (B.getK b).isK && (B.getK b).v == 0

/-- **What the walk asks at the frame's end**: the byte `b` is still followed, or it is known to be 0 -/
def finV (b : Nat) (B : AS) : Bool := (B.rk && !B.spent) || zeroAt b B

/-- the player's state is known, and not 0, 1 or 2 (for the experiment only) -/
def stateBad (sy : Syms) (B : AS) : Bool :=
  (B.getK (stI sy)).isK && !((B.getK (stI sy)).v == 0 || (B.getK (stI sy)).v == 1 || (B.getK (stI sy)).v == 2)

/-- **The walk**: `AfterKeep.walkKR` with the pieces of `sp` after those of `FrameKeep.preK` -/
def walkKV (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (Q : UInt16) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || ((FrameKeep.preK C.S C.G A).flatMap sp).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && ((C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKV C sp l Q n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- `PrevKeep.runP` with the pieces `sp`, the end asked by `fin`, and a failure at `Q` -/
partial def runV (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (fin : AS → Bool)
    (l : List Nat) (Q : UInt16) (P0 : PrevKeep.PS) (k0 : Nat) (A0 : AS) : PrevKeep.PS := Id.run do
  let ⟨X0, pred0, fa0, ch0, st0, dr0⟩ := P0
  let mut X := X0
  let mut pred := pred0
  let mut fa := fa0
  let mut ch := ch0
  let mut st := st0
  let mut dr := dr0
  let mut cur := A0
  let mut run := 0
  while true do
    if FrameKeep.storesTo l E.prg E.mask cur.pc then
      ch := ch.insert cur.pc.toNat (ch.getD cur.pc.toNat 0 + 1)
      break
    let ps := (FrameKeep.preK S G cur).flatMap sp
    let dec := ps.any fun A₁ => isRkDec E A₁.pc (LagFrames.opOf E A₁)
    let rs := ps.flatMap (FrameKeep.kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := dec || rs.any fun r => match r with
      | none => true
      | some B => (B.k != cur.k && (!FrameKeep.endOK G B || !fin B)) || (B.k == cur.k && B.pc == Q)
    if bad then
      fa := fa.push (k0, cur)
      X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k && b.pc != Q
    if cur.rk && ps.all (·.rk) && good.any (fun b => !b.rk) then dr := dr.insert cur.pc.toNat (dr.getD cur.pc.toNat 0 + 1)
    for b in good do
      if !b.rk && cur.rk then st := st.push b
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !FrameKeep.storesTo l E.prg E.mask b.pc &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      let K := key (PrevKeep.normP S G [] b)
      if !(pred.contains K) then pred := pred.insert K (k0, cur.pc)
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := PrevKeep.routeP S G [] key X b
    break
  return ⟨X, pred, fa, ch, st, dr⟩

partial def searchV (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (fin : AS → Bool)
    (l : List Nat) (Q : UInt16) (P0 : PrevKeep.PS) : PrevKeep.PS := Id.run do
  let mut P := P0
  while true do
    match P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P
      P := runV S G E key ops sp fin l Q ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩ k A
  return P

/-- the search of a walk for the byte `b` from the states at the scroll handler `starts`, with the bytes `prot` protected besides those of `FrameKeep.guardF` and
the end `fin`: no part of the proof -/
def searchWith (sy : Syms) (m0 : Machine) (prot : List Nat) (fin : AS → Bool) (b : Nat) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := prot ++ (FrameKeep.guardF sy m0).prot }
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let X := (starts.map AfterKeep.rkOn).foldl (PrevKeep.routeP S G [] key) {}
  searchV S G E key (aRows E).toArray (rkOff E) fin (FrameKeep.ctlI sy) sy.PlayerSubs { X }

/-- the search of the walk of the speed from the states at the scroll handler `starts`: no part of the proof -/
def searchOf (sy : Syms) (m0 : Machine) (starts : List AS) : PrevKeep.PS := searchWith sy m0 [spI sy] (finV (spI sy)) (spI sy) starts

/-- **The walk's table**, from the states at the scroll handler `starts` -/
def vCfg (sy : Syms) (m0 : Machine) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardV sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := spI sy }
  let key := PrevKeep.keyP S G []
  let q := FrameKeep.tableOfKW key (searchOf sy m0 starts).X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := finV (spI sy) }

/-- what the first walk asks at the scroll handler: the walk of the speed succeeds -/
def atQV (sy : Syms) (C2 : FrameKeep.CfgK) (B : AS) : Bool := walkKV C2 (rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK (AfterKeep.rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk of `AfterKeep`, then the walk of the speed -/
def cfgPV (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 C2 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQV sy C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from there the walk of the speed to the
frame's end -/
def vCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C2 := vCfg sy m0 P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPV sy m0 v q C1 C2) && C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQV sy C2) FrameKeep.fuelK) &&
    C2.t.all (walkKV C2 (rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs FrameKeep.fuelK)

/-! ## The pieces cover the machines -/

section
variable {E : Env} {F : Nat × UInt8}

/-- **The pieces of `rkOff` cover every machine**: a state that no longer follows the byte covers what the state covered -/
theorem cov_rkOff : Cov E F (rkOff E) := by
  intro B m hs
  unfold rkOff
  split
  · exact ⟨{ B with rk := false, spent := false }, List.mem_singleton.2 rfl, { hs with rkv := fun h => by simp at h }, rfl⟩
  · exact ⟨B, List.mem_singleton.2 rfl, hs, rfl⟩

end

/-! ## The walk covers the frame from the scroll handler to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {C : FrameKeep.CfgK} {sp : AS → List AS} {l : List Nat} {Q : UInt16} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveKV (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (Q : UInt16) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkKV C sp l Q n A = true

theorem cover_liveKV (ht : C.t.all (walkKV C sp l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveKV C sp l Q F D m ∧ D.k = B.k := by
  unfold FrameKeep.coverK at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D l' e1 e2
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
    have hl : l' = PipeWrites.knownOf D := by
      rw [hkl] at e2
      rw [Array.getElem?_map, e1] at e2
      exact (Option.some.inj e2).symm
    rw [hl] at h2
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm⟩
  · cases h2

theorem live_stepKV (hsp : Cov C.E F sp) (ht : C.t.all (walkKV C sp l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    {A : AS} {m : Machine} (hl : LiveKV C sp l Q F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveKV C sp l Q F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKV] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := CollKeep.cov_preKX hsp hh hs
    simp only [walkKV, hx', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw A₁ hA
    obtain ⟨r, hr, hB⟩ := AfterKeep.s_kstepL hops hd hh hs1
    have hw3 := hw2 r hr
    cases r with
    | none => simp at hw3
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw3
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw3
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw3
        obtain ⟨hq, hw4⟩ := hw3
        have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
        rcases hw4 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKV ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3, hq'⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3, hq'⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.1.1.2, hw3.1.2, hw3.2, k1, h1⟩

/-- **The walk: from the scroll handler to the frame's end** (`AfterKeep.endKR` with the pieces `sp`). The machine `k` instructions into the frame of `m`, covered by a
state from which the walk succeeds, comes to the frame's end in a state that meets `fin`, and the frame does not come to `Q` again. -/
theorem endKV (hsp : Cov C.E F sp) (ht : C.t.all (walkKV C sp l Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hQ : Q ≠ C.G.idle) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKV C sp l Q Fu' A = true) (hs : Sim C.E F A (trace m i k))
    (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∧ ∀ d, 1 ≤ d → (trace m i (k + d)).pc ≠ Q := by
  have key : ∀ d, ((∃ A, LiveKV C sp l Q F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ FrameKeep.endOK C.G B = true ∧ Sim C.E F B (trace m i (k + d)))) ∧
      (1 ≤ d → (trace m i (k + d)).pc ≠ Q) := by
    intro d
    induction d with
    | zero => exact ⟨Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩, fun h => absurd h (by omega)⟩
    | succ d ih =>
      obtain ⟨ih, _⟩ := ih
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h2', h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases live_stepKV hsp ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, a4, a5⟩ | ⟨a1, B, _, a2, a2', _, a3⟩
        · exact ⟨Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩, fun _ => a5⟩
        · refine ⟨Or.inr ⟨by rw [a1, h2], B, a2', a2, a3⟩, fun _ => ?_⟩
          rw [a3.pc]
          simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at a2
          rw [a2.1.1.1.1]
          exact fun h => hQ h.symm
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        refine ⟨Or.inr ⟨h1, B, h2, h2', h3⟩, fun _ => ?_⟩
        rw [h3.pc]
        simp only [FrameKeep.endOK, Bool.and_eq_true, beq_iff_eq] at h2'
        rw [h2'.1.1.1.1]
        exact fun h => hQ h.symm
  refine ⟨?_, fun d hd1 => (key d).2 hd1⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases (key (fuelPerFrame - k)).1 with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, _, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h3⟩

end

/-! ## On the ROM: one frame -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- the speed is protected by `FrameKeep.guardE` -/
theorem spI_mem : spI sy ∈ (FrameKeep.guardE sy m0).prot :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))

/-- **`CleanK` of the walk's guard from `CleanK` of `FrameKeep.guardE`**: each byte that the walk's guard protects, `guardE` protects (the speed is in
`FrameKeep.speedE`) -/
theorem cleanV_of {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) : FrameKeep.CleanK (guardV sy m0) q m := by
  refine FrameKeep.cleanK_sub hc (fun x hx => ?_) rfl rfl rfl rfl
  simp only [guardV, List.mem_append, List.mem_singleton] at hx
  rcases hx with rfl | hx
  · exact spI_mem
  · exact List.mem_append_right _ hx

/-- **`SpareV` is a part of `CleanK` of `FrameKeep.guardE`**, on every instruction but the player's own store of the fraction (the instruction at the store of the move
routine with the index 0), where `CleanK` asks nothing -/
theorem spareV_of {q : UInt16} {m : Machine} (h : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hq : ¬ (m.pc = q ∧ m.x = 0)) : SpareV sy m := by
  intro t ht hlt hm
  rcases h.store t ht hq with ⟨_, h2⟩ | ⟨h1, _⟩
  · simp only [List.mem_singleton] at hm
    exact h2 (hm ▸ spI_mem)
  · have a1 := UInt16.lt_iff_toNat_lt.1 hlt
    have a2 := UInt16.le_iff_toNat_le.1 h1
    simp at a1 a2
    omega

/-- **A frame in control ends with the speed of the scroll handler, or 0.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction meets
`CleanK` of `FrameKeep.guardE`, and writes neither the routine, nor the mode, nor the task by its address; the area's type is `v`, the swimming flag 0, the
change of size 0. It comes to the player's routine at `n₀`, the first time. Then at each instruction `k ≥ n₀` at the scroll handler (`PlayerSubs`) the speed is that
of the frame's end, or the frame's end has the speed 0. `hc`, `hh` are the checks on the ROM. -/
theorem speed_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hh : vCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs →
      peek (frame m i) sy.Player_X_Speed = peek (trace m i k) sy.Player_X_Speed ∨ peek (frame m i) sy.Player_X_Speed = 0 := by
  simp only [vCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  obtain ⟨⟨⟨⟨hne1, hne2⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPV sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (vCfg sy m0 P.stops.toList)) hp1 rfl rfl rfl
      (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd h1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (h4 n₀ h)
    subst hk0
    have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (CtrlKeep.valA sy v) (trace m i k₀) := by
      intro w hw
      simp only [CtrlKeep.valA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · show (trace m i k₀).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k₀).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k₀).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQV sy (vCfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    have hs2 : Sim (vCfg sy m0 P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (spI sy)) (AfterKeep.rkOn B₁) (trace m i k₁) :=
      AfterKeep.sim_rkOn hs₁
    have hclV : ∀ j, FrameKeep.CleanK (vCfg sy m0 P.stops.toList).G (vCfg sy m0 P.stops.toList).S.store (trace m i j) := fun j => cleanV_of (hcl j)
    obtain ⟨⟨B₂, hfin, hs₂⟩, hnoQ⟩ := endKV (C := vCfg sy m0 P.stops.toList) cov_rkOff hp3 rfl rfl hne2 hat hs2 hf1 hd1 hclV hx'
    intro k hk hpc
    have hkk : k = k₁ := by
      rcases Nat.lt_trichotomy k k₁ with h | h | h
      · exfalso
        by_cases e : k = k₀
        · subst e
          rw [h1] at hpc
          exact hne1 hpc
        · exact hbt k (by omega) h hpc
      · exact h
      · exfalso
        have := hnoQ (k - k₁) (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
    subst hkk
    change ((B₂.rk && !B₂.spent) || zeroAt (spI sy) B₂) = true at hfin
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hfin
    rcases hfin with ⟨hr, hsp⟩ | hz
    · left
      have e := hs₂.rkv hr
      rw [if_neg (by simp [hsp])] at e
      exact e
    · right
      simp only [zeroAt, Bool.and_eq_true, beq_iff_eq] at hz
      have hm := hs₂.ram (spI sy) (PipeTransitionAll.mask_lt _)
      exact (isK_eq hz.1 hm).trans hz.2
  · exact absurd harr (hno n₀ hf0)

end

end Smbrta.CollideKeep
