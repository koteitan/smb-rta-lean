import Theorems.GuardE

/-!
# Above ground: the collision bits at the end of a frame

The collision routine sets the player's collision bits to `FF` and `ImpedePlayerMove` clears one bit of a side: the bit given by `X` at its end. `X` there is 1 or 2 on
every path: it is the side check's counter (a byte of the zero page) minus 1, and the routine sets it to 1 when that is 0 and to 2 else. A walk does not know the counter
when it comes there from a state of its table: the counter is not protected, so the table forgets it. Then `dex` gives an `X` that is not known, the branch on the zero
flag is followed both ways, and the walk does not learn that `X` is 0 on the way where the zero flag is set. So the bit to clear is not known, and the walk fails at the
frame's end (program `coll-cut-check`: 4 failures, all there).

Here the walk splits `X` into its 256 values at the `dex` of `ImpedePlayerMove` (`splitXAt`): each value is one piece, and the pieces cover every machine (`cov_splitXAt`).
On each piece `X` is known, so the bit to clear is known. The rest is the walk of `PrevKeep` with one more split before each step (`walkKX`), and with the collision bits
watched under the mask `FC` (so one of the four values of `TopSpeed.collBits`) and protected (`collCheck`).

So (`coll_end`): a frame in control whose instructions meet `CleanK` of `FrameKeep.guardE` and `SpareC` (no store through an index or a pointer writes the collision bits),
and none of which writes the routine, the mode or the task by its address, keeps the collision bits under `FC`. A frame that does not come to the player's routine keeps
them (`CtrlKeep.keep_of_noCut`).

The searches are no part of the proof. No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.CollKeep

open TaintRun
open PipeWrites (SG)

/-! ## The split of `X` -/

/-- **`X` in its 256 values at the instruction at `p`**, if it is not known -/
def splitXAt (p : UInt16) (A : AS) : List AS :=
  if A.pc == p && !A.x.isK then (List.range 256).map fun v => { A with x := AB.known v.toUInt8 } else [A]

/-- **The walk with the split**: `FrameKeep.walkKC`, with `sp` after the pieces of `FrameKeep.preK` -/
def walkKX (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || ((FrameKeep.preK C.S C.G A).flatMap sp).all fun A₁ => (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKX C sp l n B
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B

/-! ## Finding the table: a search, no part of the proof -/

/-- `PrevKeep.runP` with the split `sp` -/
partial def runPX (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (W : List FrameKeep.Watch) (keep : List Nat) (key : AS → Nat) (ops : Array (AM Unit))
    (sp : AS → List AS) (l : List Nat) (stop : AS → Bool) (P0 : PrevKeep.PS) (k0 : Nat) (A0 : AS) : PrevKeep.PS := Id.run do
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
    let rs := ((FrameKeep.preK S G cur).flatMap sp).flatMap (FrameKeep.kstep S G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => B.k != cur.k && (!FrameKeep.watchOK W B || B.rk != cur.rk || B.spent)
    if bad then
      fa := fa.push (k0, cur)
      X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    if cur.rk && good.any (fun b => !b.rk) then dr := dr.insert cur.pc.toNat (dr.getD cur.pc.toNat 0 + 1)
    let good := good.filter fun b => b.rk == cur.rk
    for b in good do
      if stop b then st := st.push b
    let good := good.filter fun b => !stop b
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
      let K := key (PrevKeep.normP S G keep b)
      if !(pred.contains K) then pred := pred.insert K (k0, cur.pc)
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := PrevKeep.routeP S G keep key X b
    break
  return ⟨X, pred, fa, ch, st, dr⟩

partial def searchPX (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (W : List FrameKeep.Watch) (keep : List Nat) (key : AS → Nat) (ops : Array (AM Unit))
    (sp : AS → List AS) (l : List Nat) (stop : AS → Bool) (P0 : PrevKeep.PS) : PrevKeep.PS := Id.run do
  let mut P := P0
  while true do
    match P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P
      P := runPX S G E W keep key ops sp l stop ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩ k A
  return P

/-! ## On the ROM -/

/-- the collision bits -/
def bitsI (sy : Syms) : Nat := (sy.Player_CollisionBits &&& 0x7FF).toNat

/-- **Where the walk splits `X`**: the first `DEX` of `ImpedePlayerMove` -/
def splitPc (sy : Syms) (m0 : Machine) : UInt16 := PipeEntryRule.findOp m0 sy.ImpedePlayerMove 0xCA 16

/-- the split of the walk -/
def spOf (sy : Syms) (m0 : Machine) : AS → List AS := splitXAt (splitPc sy m0)

/-- what the walk sets at the cut: the area's values of `CtrlKeep.valA`, and the collision bits under `FC` -/
def valC (sy : Syms) (v : UInt8) : List FrameKeep.Watch := CtrlKeep.valA sy v ++ [(bitsI sy, 0xFC, 0xFC)]

/-- what the walk watches: the pause bit and the values of `valC` -/
def watchC (sy : Syms) (m0 : Machine) (v : UInt8) : List FrameKeep.Watch := CtrlKeep.pauseW sy m0 ++ valC sy v

/-- the guard of the walk: that of `FrameKeep.guardF`, with the collision bits protected too -/
def guardC (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := [bitsI sy] ++ (FrameKeep.guardF sy m0).prot }

/-- the table's key: that of `PrevKeep.keyP`, and `X` from the split to the end of `ImpedePlayerMove`, so that the pieces stay apart. No part of the proof. -/
def keyC (sy : Syms) (m0 : Machine) (S : FrameKeep.Spot) (G : PipeWrites.Guard) (W : List FrameKeep.Watch) (A : AS) : Nat :=
  let p := splitPc sy m0
  PrevKeep.keyP S G W A * 65536 + (if p ≤ A.pc && A.pc < p + 64 then A.x.k.toNat * 256 + (A.x.v &&& A.x.k).toNat else 0)

/-- the search after the cut from the states `starts`: no part of the proof -/
def searchC (sy : Syms) (m0 : Machine) (v : UInt8) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := CtrlKeep.guardP sy m0 ([bitsI sy] ++ CtrlKeep.spareI sy m0)
  let E := PipeEntryRule.envOf m0
  let W := watchC sy m0 v
  let key := keyC sy m0 S G W
  let X := (starts.map (CtrlKeep.toA W (valC sy v))).foldl (PrevKeep.routeP S G [] key) {}
  searchPX S G E W [] key (aRows E).toArray (spOf sy m0) (FrameKeep.ctlI sy) (fun _ => false) { X }

/-- **The walk's table**, from the states at the cut `starts` -/
def collCfg (sy : Syms) (m0 : Machine) (v : UInt8) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardC sy m0
  let E := PipeEntryRule.envOf m0
  let W := watchC sy m0 v
  let key := keyC sy m0 S G W
  let q := FrameKeep.tableOfKW key (searchC sy m0 v starts).X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the walk of the pause bit up to the cut, and from there the walk after the cut -/
def cfgPC (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with after := fun B => walkKX C (spOf sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK (CtrlKeep.toA (watchC sy m0 v) (valC sy v) B) }

/-- **The check of the collision bits**: the walk of the pause bit up to the cut; from there the walk to the frame's end with `X` split at the `DEX` of
`ImpedePlayerMove`, with the stores to the routine, the mode and the task by address cut; at the frame's end it asks the collision bits under `FC`, and the bits of
`CtrlKeep.watchA` -/
def collCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let C := collCfg sy m0 v cuts
  CtrlKeep.ctrlCheck1 (cfgPC sy m0 v q C) && C.t.all (walkKX C (spOf sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK)

/-- **A store through an index or a pointer does not write the collision bits** (one instruction) -/
def SpareC (sy : Syms) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ bitsI sy

/-- `SpareC`, for a program -/
def spareCB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && (t &&& 0x7FF).toNat == bitsI sy)
  | none => true

/-- **The collision bits are under the mask `FC`**: one of the four values of `TopSpeed.collBits` (`collCheck`) -/
def CollOK (sy : Syms) (m : Machine) : Prop := peek m sy.Player_CollisionBits &&& 0xFC = 0xFC

/-- the bytes under the mask `FC` are the values of `TopSpeed.collBits` -/
def collBitsOK (sy : Syms) : Bool := (List.range 256).all fun n => n.toUInt8 &&& 0xFC != 0xFC || (TopSpeed.collBits sy).contains n.toUInt8

/-- **The check**: the walks, and that the bytes under the mask `FC` are the values of `TopSpeed.collBits` -/
def collCheckAll (sy : Syms) (m0 : Machine) (v : UInt8) : Bool := collCheck sy m0 v && collBitsOK sy

/-! ## The split covers the machines -/

section
variable {E : Env} {F : Nat × UInt8}

/-- **The pieces of `X` cover every machine**: the piece of its own value -/
theorem cov_splitXAt (p : UInt16) : Cov E F (splitXAt p) := by
  intro B m hs
  unfold splitXAt
  split
  · refine ⟨{ B with x := AB.known m.x.toNat.toUInt8 }, List.mem_map.2 ⟨m.x.toNat, List.mem_range.2 m.x.toNat_lt, rfl⟩, { hs with x := ?_ }, rfl⟩
    have e4 : m.x.toNat.toUInt8 = m.x := by simp
    show (AB.known m.x.toNat.toUInt8).mem m.x
    rw [e4]
    exact mem_known_self _
  · exact ⟨B, List.mem_singleton.2 rfl, hs, rfl⟩

/-- **The pieces of `FrameKeep.preK` and then of `sp` cover the machine** -/
theorem cov_preKX {S : FrameKeep.Spot} {G : PipeWrites.Guard} {sp : AS → List AS} (hsp : Cov E F sp) {A : AS} {m : Machine} (hc : FrameKeep.CleanK G S.store m)
    (hs : Sim E F A m) : ∃ B ∈ (FrameKeep.preK S G A).flatMap sp, Sim E F B m ∧ B.k = A.k := by
  obtain ⟨A₁, hA, hs1, hk1⟩ := FrameKeep.cov_preK hc hs
  obtain ⟨A₂, hA2, hs2, hk2⟩ := hsp A₁ m hs1
  exact ⟨A₂, List.mem_flatMap.2 ⟨A₁, hA, hA2⟩, hs2, hk2.trans hk1⟩

end

/-! ## The walk covers the frame from the cut to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {C : FrameKeep.CfgK} {sp : AS → List AS} {l : List Nat} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m`, and a walk with the split from `A` succeeds -/
def LiveKX (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkKX C sp l n A = true

theorem cover_liveKX (ht : C.t.all (walkKX C sp l Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m)
    (h : FrameKeep.coverK C B = true) : ∃ D, LiveKX C sp l F D m ∧ D.k = B.k := by
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

/-- **One step of the walk with the split** -/
theorem live_stepKX (hsp : Cov C.E F sp) (ht : C.t.all (walkKX C sp l Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveKX C sp l F A m) (hh : FrameKeep.CleanK C.G C.S.store m) (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveKX C sp l F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKX] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := cov_preKX hsp hh hs
    obtain ⟨r, hr, hB⟩ := FrameKeep.s_kstep hops hT hh hs1
    simp only [walkKX, hx', Bool.false_or, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [hk1] at k1
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveKX ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.1.1.2, hw2.1.2, hw2.2, k1, h1⟩

/-- **From the cut to the frame's end**: `PrevKeep.after_endC` for the walk with the split -/
theorem after_endCX (hsp : Cov C.E F sp) (ht : C.t.all (walkKX C sp l Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) (hops : C.ops = (aRows C.E).toArray)
    (hT : 2 ≤ F.2.toNat) {Fu' : Nat} {m : Machine} {i : UInt8} {k : Nat} {A : AS}
    (hw : walkKX C sp l Fu' A = true) (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ B, FrameKeep.watchOK C.W B = true ∧ Sim C.E F B (frame m i) := by
  have key : ∀ d, (∃ A, LiveKX C sp l F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ Sim C.E F B (trace m i (k + d))) := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3⟩ | ⟨h1, B, h2, h3⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases live_stepKX hsp ht hkl hops hT h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, a4⟩ | ⟨a1, B, a2, _, _, _, a3⟩
        · exact Or.inl ⟨A', a1, by rw [a3, h2], by omega⟩
        · exact Or.inr ⟨by rw [a1, h2], B, a2, a3⟩
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr ⟨h1, B, h2, h3⟩
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3⟩ | ⟨_, B, h2, h3⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h3
    rw [PipeEntryRule.frame_trace]
    exact ⟨B, h2, h3⟩

end

/-! ## A frame in control keeps the collision bits under `FC` -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

theorem collCheck_parts {v : UInt8} (h : collCheck sy m0 v = true) :
    CtrlKeep.ctrlCheck1 (cfgPC sy m0 v (CtrlKeep.cutTable sy m0 true) (collCfg sy m0 v (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true))))) = true ∧
    (collCfg sy m0 v (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))).t.all
      (walkKX (collCfg sy m0 v (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))) (spOf sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK) = true := by
  unfold collCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- **Under the mask `FC` the collision bits are one of the four values of `TopSpeed.collBits`** -/
theorem mem_of_collOK (hb : collBitsOK sy = true) {m : Machine} (h : CollOK sy m) : peek m sy.Player_CollisionBits ∈ TopSpeed.collBits sy := by
  have e := List.all_eq_true.1 hb (peek m sy.Player_CollisionBits).toNat (List.mem_range.2 (peek m sy.Player_CollisionBits).toNat_lt)
  have e1 : (peek m sy.Player_CollisionBits).toNat.toUInt8 = peek m sy.Player_CollisionBits := by simp
  rw [e1] at e
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at e
  rcases e with e | e
  · exact absurd h e
  · exact List.contains_iff_mem.1 e

/-- `CleanK` of the walk's guard: `CleanK` of `FrameKeep.guardE` and `SpareC` -/
theorem cleanC_of {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hs : SpareC sy m) : FrameKeep.CleanK (guardC sy m0) q m :=
  CtrlKeep.cleanK_prot (G := FrameKeep.guardF sy m0) (l := [bitsI sy]) (FrameKeep.cleanK_of_E hc) (fun t ht hlt hm => hs t ht hlt (List.mem_singleton.1 hm))

theorem valC_lt (v : UInt8) : ∀ w ∈ watchC sy m0 v, w.1 < 2048 := by
  intro w hw
  unfold watchC valC at hw
  rcases List.mem_append.1 hw with h | h
  · exact CtrlKeep.watchA_lt v w (List.mem_append_left _ h)
  · rcases List.mem_append.1 h with h | h
    · exact CtrlKeep.watchA_lt (m0 := m0) v w (List.mem_append_right (CtrlKeep.pauseW sy m0) h)
    · rw [List.mem_singleton.1 h]
      exact PipeTransitionAll.mask_lt _

/-- **A frame in control keeps the collision bits under `FC`.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each instruction meets `CleanK` of
`FrameKeep.guardE` and `SpareC`, and writes neither the routine, nor the mode, nor the task by its address; the area's type is `v`, the swimming flag 0, the change of
size 0. If the frame comes to the player's routine, the walk after the cut with `X` split at `ImpedePlayerMove` keeps the bits under `FC`; if it does not, it keeps the
bits (`CtrlKeep.keep_of_noCut`). `hc`, `hp` are the checks on the ROM. -/
theorem coll_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : collCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hsc : ∀ n, SpareC sy (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) (h : CollOK sy m) : CollOK sy (frame m i) := by
  obtain ⟨hp1, hp2⟩ := collCheck_parts hp
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) :=
    fun n => FrameKeep.cleanK_of_F (FrameKeep.cleanK_of_E (hcl n))
  have hclC : ∀ n, FrameKeep.CleanK (guardC sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => cleanC_of (hcl n) (hsc n)
  rcases CtrlKeep.cut_or_end2 (C := cfgPC sy m0 v q (collCfg sy m0 v cuts)) hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hV : FrameKeep.Watched (valC sy v) (trace m i k) := by
      intro w hw
      simp only [valC, CtrlKeep.valA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · show (trace m i k).ram.get! (sy.AreaType &&& 0x7FF).toNat &&& 0xFF = v &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.1
      · show (trace m i k).ram.get! (sy.SwimmingFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.1
      · show (trace m i k).ram.get! (sy.PlayerChangeSizeFlag &&& 0x7FF).toNat &&& 0xFF = 0 &&& 0xFF
        rw [FrameKeep.and_ff, FrameKeep.and_ff]
        exact (A.keep _ (by simp [CtrlKeep.keepA])).trans hv.2.2
      · show peek (trace m i k) sy.Player_CollisionBits &&& 0xFC = 0xFC &&& 0xFC
        rw [A.keep _ (by simp [CtrlKeep.keepA])]
        exact h
    have hhs : Sim (CtrlKeep.envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) (m.frame, m.ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat) B (trace m i k) := hs
    have hsA := CtrlKeep.sim_toA (W := watchC sy m0 v) hhs (valC_lt v) hV
    have hw : walkKX (collCfg sy m0 v cuts) (spOf sy m0) (FrameKeep.ctlI sy) FrameKeep.fuelK (CtrlKeep.toA (watchC sy m0 v) (valC sy v) B) = true := hB2
    have hcov : Cov (collCfg sy m0 v cuts).E (m.frame, 2) (spOf sy m0) := cov_splitXAt (splitPc sy m0)
    obtain ⟨B', hB', hs'⟩ := after_endCX (C := collCfg sy m0 v cuts) (F := (m.frame, 2)) hcov hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclC hx
    have hW := FrameKeep.watched_of hB' hs'
    have e : (frame m i).ram.get! (bitsI sy) &&& 0xFC = 0xFC &&& 0xFC := hW _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
    exact e
  · unfold CollOK
    rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
    exact h

end

end Smbrta.CollKeep
