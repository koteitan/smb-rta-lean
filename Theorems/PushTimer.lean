import Theorems.EdgeStep
import Theorems.CollideKeep

/-!
# Above ground: a push that moves him leaves the side collision's timer at 16 to the frame's end

The push (`ImpedePlayerMove`) moves him by 1 px only on its path that first stores 16 to the side collision's timer (`ScrollRule.places.sideB`) and 0 to his
speed. The timer falls only in the timers' routine, at the start of a frame. So when a frame ends with the timer at most 1, no push after the scroll handler has
moved him, and his pixel and his page at the frame's end are those after the scroll handler's call (`pix_end`).

The proof is a walk from the instruction after the scroll handler's call (`EdgeStep.rPc`) to the frame's end, for each of the two bytes of his pixel and his page
(`pixI`): the walk follows the byte (TaintRun's counter), stops following it just before an instruction that writes it by its address (`CollideKeep.rkOff`), and
asks at the frame's end that the byte is still followed or the timer is known to be at least 2 (`finS`; round 33: known to be the value the push stores,
`pushT`). A path stops at a store to his position by its address
outside the push and the clamp (`EdgeStep.cutPos`, which the field `posW` excludes). Its guard protects the timer, his pixel and his page (`guardS`). For his
pixel and his page that is what `posW` says outside the push and the clamp (`posW_plain`), and the walk meets no store through an index or a pointer inside
them (`okS`); for the timer the walk needs one more condition on each instruction from the scroll handler to the frame's end: a store through an index or a
pointer does not write the timer (`SideW`). The walks before are those of `EdgeStep.keep_r`: the walk of `CtrlKeep` to the cut, the first walk of `AfterKeep` to the scroll handler, the middle walk
to the instruction after its call. The check on the ROM is `sCheck`. No game data. Page: `1-1/e-2-10-3-20-PushTimer.md`.

Round 33: the walks follow his speed too (`pvI`), and the guard protects his speed and his state (`FrameKeep.guardE` protects them), so a frame that ends with
the timer at most 1 also ends with the speed of the instruction after the call (`SurfaceFrames.OnFrames.stopRight` uses it). And `SideW` is asked only at a store
that may reach the timer (`NearW`: a store to an absolute address plus an index from whose base some index reaches the timer, or a store through a pointer); at
every other instruction it is a theorem (`sideW_far`: a store through `X` to the zero page stays below the timer, and from the other bases no index reaches it).
Page: `1-1/e-2-10-3-22-SideNear.md`.
-/

namespace Smbrta.PushTimer
open TaintRun
open AfterKeep (walkQ1 tableBut rkOn)

variable {sy : Syms}

/-- his pixel and his page, the two bytes the walks follow -/
def pixI (sy : Syms) (m0 : Machine) : List Nat := [(ScrollRule.places sy m0).x, (ScrollRule.places sy m0).page]

/-- **The side collision's timer, his pixel and his page**, as indices of RAM, the bytes the walks' guard protects besides those of `FrameKeep.guardF` (the
timer's index is the operand of the scroll handler's load of it, `ScrollRule.places`) -/
def sideP (sy : Syms) (m0 : Machine) : List Nat := (ScrollRule.places sy m0).sideB :: pixI sy m0

/-- round 33: **the bytes the walks follow**: his pixel, his page and his speed -/
def pvI (sy : Syms) (m0 : Machine) : List Nat := pixI sy m0 ++ FrameKeep.speedE sy

/-- **The condition on one instruction** (the field `OnFrames.sideW`, from the scroll handler to the frame's end): a store through an index or a pointer does
not write the side collision's timer -/
def SideW (sy : Syms) (m0 : Machine) (m : Machine) : Prop :=
  ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ≠ (ScrollRule.places sy m0).sideB

/-- `SideW`, for a program -/
def sideWB (sy : Syms) (m0 : Machine) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !decide (t < 0x2000) || (t &&& 0x7FF).toNat != (ScrollRule.places sy m0).sideB
  | none => true

/-- the opcodes that store through an index or a pointer (those of `PipeWrites.wTarget`) -/
def wOps : List UInt8 := [0x95, 0x94, 0xD6, 0xF6, 0x9D, 0xDE, 0xFE, 0x7E, 0x99, 0x91]

/-- the opcodes of `wOps` that store to an absolute address plus an index -/
def absWOps : List UInt8 := [0x9D, 0xDE, 0xFE, 0x7E, 0x99]

/-- **A store that may reach the side collision's timer** (round 33), for a program: a store to an absolute address plus an index, from whose base some index
reaches the timer (`PositionKeep.farB` fails), or a store through a pointer -/
def nearWB (sy : Syms) (m0 : Machine) (m : Machine) : Bool :=
  (absWOps.contains (PipeWrites.opAt m) && !PositionKeep.farB [(ScrollRule.places sy m0).sideB] (PositionKeep.operandAt m.prg m.prgMask m.pc)) ||
    PipeWrites.opAt m == 0x91

/-- **A store that may reach the side collision's timer** (round 33: the field `OnFrames.sideW` asks `SideW` only at such a store) -/
def NearW (sy : Syms) (m0 : Machine) (m : Machine) : Prop := nearWB sy m0 m = true

/-- **What the walk asks at a state**: at a store through an index or a pointer, no interrupt pending, the instruction and its two next bytes in the program's half
of the address space, and the place not inside the push or the clamp (`PositionWriters.innerP`) -/
def okS (sy : Syms) (m0 : Machine) (E : Env) (A : AS) : Bool :=
  !wOps.contains (E.prg.get! (A.pc &&& E.mask).toNat) ||
    (!A.nmi && decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) && !PositionWriters.innerP sy m0 A.pc)

/-- **The walks' guard**: `FrameKeep.guardF` with the three bytes of `sideP` protected too, and (round 33) his speed and his state (`FrameKeep.guardE` protects
them) -/
def guardS (sy : Syms) (m0 : Machine) : PipeWrites.Guard :=
  { FrameKeep.guardF sy m0 with prot := sideP sy m0 ++ (FrameKeep.speedE sy ++ FrameKeep.stateE sy) ++ (FrameKeep.guardF sy m0).prot }

/-- the byte `s` is known, and it is at least 2 -/
def highAt (s : Nat) (B : AS) : Bool := (B.getK s).isK && decide (2 ≤ (B.getK s).v)

/-- round 33: **the value the push stores to the side collision's timer**, read from the push (`ImpedePlayerMove`): the operand of the instruction before its
store to the timer (`STY` absolute to the address of the scroll handler's load of the timer) -/
def pushT (sy : Syms) (m0 : Machine) : UInt8 :=
  let E := FrameModel.Rom.of m0
  let a := E.w ((ScrollRule.places sy m0).side + 1)
  E.b (FrameModel.findPat E sy.ImpedePlayerMove [0x8C, a.toUInt8, (a >>> 8).toUInt8] 64 - 1)

/-- round 33: the byte `s` is known, and it is `t` -/
def eqAt (s : Nat) (t : UInt8) (B : AS) : Bool := (B.getK s).isK && (B.getK s).v == t

/-- **What the walk asks at the frame's end**: the followed byte is still followed, or the timer `s` is known to be `t` (round 33: the push's value `pushT`;
round 32: at least 2) -/
def finS (s : Nat) (t : UInt8) (B : AS) : Bool := (B.rk && !B.spent) || eqAt s t B

/-- **The target of a store through an index, when the walk knows the index** (`STA`, `STY`, `DEC`, `INC` zero page with `X`; `STA`, `DEC`, `INC`, `ROR` absolute
with `X`; `STA` absolute with `Y`), as `PipeWrites.wTarget` computes it on the machine -/
def tgtK (E : Env) (A : AS) : Option UInt16 :=
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let z1 := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
  let z2 := E.prg.get! ((A.pc + 2) &&& E.mask).toNat
  if (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) && A.x.isK then some (z1 + A.x.v).toUInt16
  else if (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) && A.x.isK then some ((z1.toUInt16 ||| (z2.toUInt16 <<< 8)) + A.x.v.toUInt16)
  else if op == 0x99 && A.y.isK then some ((z1.toUInt16 ||| (z2.toUInt16 <<< 8)) + A.y.v.toUInt16)
  else none

/-- **A state that no machine under `SideW` meets**: at a store through an index whose target the walk knows, and the target is one of the bytes `pl` -/
def cutS (pl : List Nat) (E : Env) (A : AS) : Bool :=
  decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1) &&
    match tgtK E A with
    | some t => decide (t < 0x2000) && pl.contains (t &&& 0x7FF).toNat
    | none => false

/-- **The walk**: `CollideKeep.walkKV` (the pieces of `sp` after those of `FrameKeep.preK`) that stops a path at a place of `cutP`, as `EdgeStep.walkKP` -/
def walkKS (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (cutP : UInt16 → Bool) (ok : AS → Bool) (pl : List Nat) (Q : UInt16) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => FrameKeep.storesTo l C.E.prg C.E.mask A.pc || cutP A.pc || (ok A && (cutS pl C.E A || ((FrameKeep.preK C.S C.G A).flatMap sp).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && ((C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKS C sp l cutP ok pl Q n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B))

/-! ## Finding the table: a search, no part of the proof -/

/-- `CollideKeep.runV` that also stops a path at a place of `cutP` -/
partial def runS (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (fin : AS → Bool)
    (l : List Nat) (cutP : UInt16 → Bool) (ok : AS → Bool) (pl : List Nat) (Q : UInt16) (P0 : PrevKeep.PS) (k0 : Nat) (A0 : AS) : PrevKeep.PS := Id.run do
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
    if FrameKeep.storesTo l E.prg E.mask cur.pc || cutP cur.pc then
      ch := ch.insert cur.pc.toNat (ch.getD cur.pc.toNat 0 + 1)
      break
    if !ok cur then
      fa := fa.push (k0, cur)
      X := { X with fails := X.fails + 1, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
      break
    if cutS pl E cur then
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
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && b.pc != G.je && b.pc != S.entry && !FrameKeep.storesTo l E.prg E.mask b.pc && !cutP b.pc && !cutS pl E b &&
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

partial def searchS (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (key : AS → Nat) (ops : Array (AM Unit)) (sp : AS → List AS) (fin : AS → Bool)
    (l : List Nat) (cutP : UInt16 → Bool) (ok : AS → Bool) (pl : List Nat) (Q : UInt16) (P0 : PrevKeep.PS) : PrevKeep.PS := Id.run do
  let mut P := P0
  while true do
    match P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P
      P := runS S G E key ops sp fin l cutP ok pl Q ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩ k A
  return P

/-- the search of the walk for the byte `b` from the states after the scroll handler's call `starts`: no part of the proof -/
def searchSide (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : PrevKeep.PS :=
  let S := FrameKeep.spotOf sy m0
  let G := guardS sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let X := (starts.map rkOn).foldl (PrevKeep.routeP S G [] key) {}
  searchS S G E key (aRows E).toArray (CollideKeep.rkOff E) (finS (ScrollRule.places sy m0).sideB (pushT sy m0)) (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0)
    (okS sy m0 E) (sideP sy m0) (EdgeStep.rPc sy) { X }

/-- **The walk's table** for the byte `b`, from the states after the scroll handler's call `starts` -/
def sCfg (sy : Syms) (m0 : Machine) (b : Nat) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardS sy m0
  let E := { PipeEntryRule.envOf m0 with rkI := b }
  let key := PrevKeep.keyP S G []
  let q := FrameKeep.tableOfKW key (searchSide sy m0 b starts).X
  { E, ops := (aRows E).toArray, S, G, W := [], t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key,
    fin := finS (ScrollRule.places sy m0).sideB (pushT sy m0) }

/-- what the middle walk asks after the scroll handler's call: the walk succeeds for each byte -/
def atRS (sy : Syms) (m0 : Machine) (C2 : List FrameKeep.CfgK) (B : AS) : Bool :=
  C2.all fun C => walkKS C (CollideKeep.rkOff C.E) (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (okS sy m0 C.E) (sideP sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK (rkOn B)

/-- what the first walk asks at the scroll handler: the middle walk succeeds -/
def atSS (sy : Syms) (m0 : Machine) (Cs : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) (B : AS) : Bool :=
  walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRS sy m0 C2) FrameKeep.fuelK B

/-- the walk of the pause bit up to the cut, then the first walk to the scroll handler, the middle walk to the instruction after its call, the walks of this file -/
def cfgPS (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C1 Cs : FrameKeep.CfgK) (C2 : List FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSS sy m0 Cs C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- **The check on the ROM**: the walk of the pause bit up to the cut; from there the first walk of `AfterKeep` to the scroll handler; from there the middle walk of
`EdgeStep` to the instruction after the call; from there, for his pixel and his page, the walk of this file to the frame's end -/
def sCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let Ps := EdgeStep.qsSearch sy m0 v P.stops.toList
  let Cs := EdgeStep.qsCfg sy m0 v Ps
  let C2 := (pvI sy m0).map fun b => sCfg sy m0 b Ps.stops.toList
  decide (2 ≤ pushT sy m0) && decide (256 ≤ (ScrollRule.places sy m0).sideB) && sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop && EdgeStep.rPc sy != sy.EndlessLoop &&
    CtrlKeep.ctrlCheck1 (cfgPS sy m0 v q C1 Cs C2) && C1.t.all (walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atSS sy m0 Cs C2) FrameKeep.fuelK) &&
    Cs.t.all (walkQ1 Cs (FrameKeep.ctlI sy) (EdgeStep.rPc sy) (atRS sy m0 C2) FrameKeep.fuelK) &&
    C2.all fun C => C.t.all (walkKS C (CollideKeep.rkOff C.E) (FrameKeep.ctlI sy) (EdgeStep.cutPos sy m0) (okS sy m0 C.E) (sideP sy m0) (EdgeStep.rPc sy) FrameKeep.fuelK)

/-- the search's failures, for a program: for each byte, the number of failures and the places (no part of the proof) -/
def sFails (sy : Syms) (m0 : Machine) (v : UInt8) : List (Nat × Nat × List Nat) :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let Ps := EdgeStep.qsSearch sy m0 v P.stops.toList
  (pvI sy m0).map fun b =>
    let R := searchSide sy m0 b Ps.stops.toList
    (b, R.X.fails, R.X.failPcs.toList.map (·.1))

/-! ## The state cut: what the walk's known index says of the machine -/

section
open PipeTransitionAll (go)

theorem zpx_t {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) :
    (go Smbrta.mZpx { m with pc := m.pc + 1 }).1 = (m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat + m.x).toUInt16 := by
  have e : go Smbrta.mZpx { m with pc := m.pc + 1 } = go (fetch >>= fun b => get >>= fun s => pure ((b + s.x).toUInt16)) { m with pc := m.pc + 1 } := rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 }) hp1]
  rfl

theorem abx_t {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAbx { m with pc := m.pc + 1 }).1 = PositionKeep.operandAt m.prg m.prgMask m.pc + m.x.toUInt16 := by
  have e : go Smbrta.mAbx { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.x.toUInt16)) { m with pc := m.pc + 1 } := rfl
  have e2 : m.pc + 1 + 1 = m.pc + 2 := by rw [UInt16.add_assoc]; rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 }) hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  dsimp only
  rw [e2]
  rfl

theorem aby_t {m : Machine} (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1) :
    (go Smbrta.mAby { m with pc := m.pc + 1 }).1 = PositionKeep.operandAt m.prg m.prgMask m.pc + m.y.toUInt16 := by
  have e : go Smbrta.mAby { m with pc := m.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => get >>= fun s =>
      pure ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + s.y.toUInt16)) { m with pc := m.pc + 1 } := rfl
  have e2 : m.pc + 1 + 1 = m.pc + 2 := by rw [UInt16.add_assoc]; rfl
  rw [e, PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 }) hp1]
  dsimp only
  rw [PipeTransitionAll.go_bind, PositionWriters.fetchP (m := { m with pc := m.pc + 1 + 1 }) hp2]
  dsimp only
  rw [e2]
  rfl

/-- **A state of `cutS` covers no machine that meets the condition**: the machine stores through an index to one of the bytes `pl` -/
theorem cutS_spec {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} {pl : List Nat} (hs : Sim E F A m) (h : cutS pl E A = true) :
    ∃ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t ∧ t < 0x2000 ∧ (t &&& 0x7FF).toNat ∈ pl := by
  unfold cutS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hp1⟩, hp2⟩, ht⟩ := h
  have hpc : m.pc = A.pc := hs.pc
  have hprg : m.prg = E.prg := hs.prg
  have hmask : m.prgMask = E.mask := hs.mask
  have q1 : 0x8000 ≤ m.pc + 1 := by rw [hpc]; exact hp1
  have q2 : 0x8000 ≤ m.pc + 1 + 1 := by rw [hpc]; exact hp2
  have hop : PipeWrites.opAt m = E.prg.get! (A.pc &&& E.mask).toNat := by unfold PipeWrites.opAt; rw [hprg, hmask, hpc]
  have hz1 : m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat = E.prg.get! ((A.pc + 1) &&& E.mask).toNat := by rw [hprg, hmask, hpc]
  have hoa : PositionKeep.operandAt m.prg m.prgMask m.pc =
      (E.prg.get! ((A.pc + 1) &&& E.mask).toNat).toUInt16 ||| ((E.prg.get! ((A.pc + 2) &&& E.mask).toNat).toUInt16 <<< 8) := by
    unfold PositionKeep.operandAt; rw [hprg, hmask, hpc]
  have hex : ∃ t, tgtK E A = some t ∧ t < 0x2000 ∧ (t &&& 0x7FF).toNat ∈ pl := by
    cases e : tgtK E A with
    | none => rw [e] at ht; simp at ht
    | some t =>
      rw [e] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at ht
      exact ⟨t, rfl, ht⟩
  obtain ⟨t, et, ht1, ht2⟩ := hex
  refine ⟨t, ?_, ht1, ht2⟩
  unfold tgtK at et
  generalize hop' : E.prg.get! (A.pc &&& E.mask).toNat = op at et hop
  dsimp only at et
  unfold PipeWrites.wTarget
  rw [hop]
  by_cases c1 : ((op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) && A.x.isK) = true
  · rw [if_pos c1] at et
    simp only [Bool.and_eq_true] at c1
    have hx : m.x = A.x.v := isK_eq c1.2 hs.x
    rw [if_pos c1.1, zpx_t q1, hz1, hx]
    exact et
  · rw [if_neg c1] at et
    by_cases c2 : ((op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) && A.x.isK) = true
    · rw [if_pos c2] at et
      simp only [Bool.and_eq_true] at c2
      have hx : m.x = A.x.v := isK_eq c2.2 hs.x
      have hb0 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = false := by
        have := c2.1
        simp only [Bool.or_eq_true, beq_iff_eq] at this
        rcases this with ((h | h) | h) | h <;> subst h <;> rfl
      rw [if_neg (by simp [hb0]), if_pos c2.1, abx_t q1 q2, hoa, hx]
      exact et
    · rw [if_neg c2] at et
      by_cases c3 : (op == 0x99 && A.y.isK) = true
      · rw [if_pos c3] at et
        simp only [Bool.and_eq_true, beq_iff_eq] at c3
        have hy : m.y = A.y.v := isK_eq c3.2 hs.y
        rw [c3.1]
        rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), aby_t q1 q2, hoa, hy]
        exact et
      · rw [if_neg c3] at et
        cases et

end

/-! ## The walk covers the frame from the instruction after the scroll handler's call to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {C : FrameKeep.CfgK} {sp : AS → List AS} {l : List Nat} {cutP : UInt16 → Bool} {ok : AS → Bool} {pl : List Nat} {Q : UInt16} {Fu : Nat}
  {F : Nat × UInt8}

/-- **The bytes `pl` are not written through an index or a pointer**, at one instruction -/
def SideWL (pl : List Nat) (m : Machine) : Prop :=
  ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ pl

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveKS (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (cutP : UInt16 → Bool) (ok : AS → Bool) (pl : List Nat) (Q : UInt16) (F : Nat × UInt8)
    (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkKS C sp l cutP ok pl Q n A = true

theorem cover_liveKS (ht : C.t.all (walkKS C sp l cutP ok pl Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine}
    (hs : Sim C.E F B m) (h : FrameKeep.coverK C B = true) : ∃ D, LiveKS C sp l cutP ok pl Q F D m ∧ D.k = B.k := by
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

/-- one step of the walk; `CleanK` of the walk's guard and the condition on the bytes `pl` are asked of the machine only where the walk's state meets `ok` -/
theorem live_stepKS (hsp : Cov C.E F sp) (ht : C.t.all (walkKS C sp l cutP ok pl Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) {A : AS} {m : Machine} (hl : LiveKS C sp l cutP ok pl Q F A m)
    (hok : ok A = true → FrameKeep.CleanK C.G C.S.store m ∧ SideWL pl m)
    (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) (hp : cutP m.pc = false) :
    (∃ A', LiveKS C sp l cutP ok pl Q F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧ (go step m).2.pc ≠ Q) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw0⟩ := hl
  cases n with
  | zero => simp [walkKS] at hw0
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    have hp' : cutP A.pc = false := by rw [← hs.pc]; exact hp
    simp only [walkKS, hx', hp', Bool.false_or, Bool.and_eq_true] at hw0
    obtain ⟨hokA, hw1⟩ := hw0
    obtain ⟨hh, hw⟩ := hok hokA
    have hc' : cutS pl C.E A = false := by
      cases e : cutS pl C.E A with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨t, h1, h2, h3⟩ := cutS_spec hs e
        exact hw t h1 h2 h3
    obtain ⟨A₁, hA, hs1, hk1⟩ := CollKeep.cov_preKX hsp hh hs
    simp only [hc', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw1
    obtain ⟨hd, hw2⟩ := hw1 A₁ hA
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
        · obtain ⟨D, hD, hk⟩ := cover_liveKS ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3, hq'⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3, hq'⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq] at hw3
        exact ⟨k2, B, hw3.1.1.2, hw3.1.2, hw3.2, k1, h1⟩

/-- **The walk: from `k` to the frame's end** (`CollideKeep.endKV` with the two cuts). The conditions on each instruction are asked only from `k` on, in the frame,
and `CleanK` and the condition on the bytes `pl` only where a state of the walk that covers the machine meets `ok`. -/
theorem endKS (hsp : Cov C.E F sp) (ht : C.t.all (walkKS C sp l cutP ok pl Q Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) (hQ : Q ≠ C.G.idle) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKS C sp l cutP ok pl Q Fu' A = true)
    (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, k ≤ j → (trace m i j).frame = m.frame → ∀ A, Sim C.E F A (trace m i j) → ok A = true →
      FrameKeep.CleanK C.G C.S.store (trace m i j) ∧ SideWL pl (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false)
    (hp : ∀ j, k ≤ j → (trace m i j).frame = m.frame → cutP (trace m i j).pc = false) :
    (∃ B, C.fin B = true ∧ Sim C.E F B (frame m i)) ∧ ∀ d, 1 ≤ d → (trace m i (k + d)).pc ≠ Q := by
  have key : ∀ d, ((∃ A, LiveKS C sp l cutP ok pl Q F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧
      m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
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
        rcases live_stepKS hsp ht hkl hops h1 (hcl (k + d) (by omega) h2 A h1.1) (hx (k + d)) (hp (k + d) (by omega) h2) with
          ⟨A', a1, _, a3, a4, a5⟩ | ⟨a1, B, _, a2, a2', _, a3⟩
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

/-! ## His pixel and his page: what `posW` says of a store through an index -/

section
open PipeTransitionAll (go)

/-- `PipeWrites.wTarget` has a target only for the opcodes of `wOps` -/
theorem wTarget_ops {op : UInt8} {m : Machine} {t : UInt16} (h : PipeWrites.wTarget op m = some t) : op ∈ wOps := by
  unfold PipeWrites.wTarget at h
  simp only [wOps, List.mem_cons, List.not_mem_nil, or_false]
  by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
  · simp only [Bool.or_eq_true, beq_iff_eq] at c1
    rcases c1 with ((h | h) | h) | h <;> simp [h]
  · rw [if_neg c1] at h
    by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
    · simp only [Bool.or_eq_true, beq_iff_eq] at c2
      rcases c2 with ((h | h) | h) | h <;> simp [h]
    · rw [if_neg c2] at h
      by_cases c3 : (op == 0x99) = true
      · simp only [beq_iff_eq] at c3
        simp [c3]
      · rw [if_neg c3] at h
        by_cases c4 : (op == 0x91) = true
        · simp only [beq_iff_eq] at c4
          simp [c4]
        · rw [if_neg c4] at h
          cases h

/-- the opcodes of `wOps` are not plain (`PositionWriters.plainOp`) -/
theorem plainOp_w {op : UInt8} (h : op ∈ wOps) : PositionWriters.plainOp op = false := by
  simp only [wOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- each opcode of `wOps` writes through its mode, at the target that `PipeWrites.wTarget` computes -/
theorem w_md : ∀ op ∈ wOps, ∀ m : Machine, ∃ c a, StepWrites.wOf op = .md c a ∧ PipeWrites.wTarget op m = some (go c { m with pc := m.pc + 1 }).1 := by
  intro op h m
  simp only [wOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩

/-- **the target of a store through an index or a pointer is a place that the step writes** -/
theorem loc_of_target {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : 0x8000 ≤ m.pc) {t : UInt16}
    (ht : PipeWrites.wTarget (PipeWrites.opAt m) m = some t) (hlt : t < 0x2000) : (t &&& 0x7FF).toNat ∈ StepWrites.stepLocs m := by
  have hop := wTarget_ops ht
  obtain ⟨c, a, hw, hwt⟩ := w_md _ hop m
  rw [hwt] at ht
  have et : (go c { m with pc := m.pc + 1 }).1 = t := Option.some.inj ht
  unfold StepWrites.stepLocs
  rw [if_neg (by simp [hn]), if_neg (by simp [hh]), PositionWriters.fetchP hp]
  dsimp only
  have e1 : m.prg.get! (m.pc &&& m.prgMask).toNat = PipeWrites.opAt m := rfl
  rw [e1, hw]
  simp only [StepWrites.Wr.locs, StepWrites.ramIdx, et, if_pos hlt, List.mem_singleton]

/-- **`posW` protects his pixel and his page from a store through an index or a pointer outside the push and the clamp** (`PositionKeep.PosW`, and
`PositionKeep.ordinary_absFar` for a store from a base that no index takes to them) -/
theorem posW_plain {R : Machine} (hW : PositionKeep.PosW sy m0 R) (hst : PositionWriters.offStack sy = true) (hn : R.nmiPending = false)
    (hh : R.halted = false) (hp : 0x8000 ≤ R.pc) (hp1 : 0x8000 ≤ R.pc + 1) (hp2 : 0x8000 ≤ R.pc + 1 + 1)
    (hi : PositionWriters.innerP sy m0 R.pc = false) {t : UInt16} (ht : PipeWrites.wTarget (PipeWrites.opAt R) R = some t) (hlt : t < 0x2000) :
    (t &&& 0x7FF).toNat ∉ pixI sy m0 := by
  have hop := wTarget_ops ht
  have hord : PositionDispatch.Ordinary sy R := by
    have hpl : PositionWriters.plainOp (R.prg.get! (R.pc &&& R.prgMask).toNat) = false := plainOp_w hop
    cases hf : PositionKeep.absFar sy R with
    | true => exact PositionKeep.ordinary_absFar hst hp hp1 hp2 hf
    | false =>
      rcases hW.2 hpl hf with h | h
      · rw [hi] at h; cases h
      · exact h
  have hloc := loc_of_target hn hh hp ht hlt
  intro hm
  simp only [pixI, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e
  · rw [e] at hloc
    exact hord sy.Player_X_Position (by simp) hloc
  · rw [e] at hloc
    exact hord sy.Player_PageLoc (by simp) hloc

/-- what `okS` says of a machine that a state covers, at a store through an index or a pointer -/
theorem okS_spec {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : okS sy m0 E A = true) (hop : PipeWrites.opAt m ∈ wOps) :
    m.nmiPending = false ∧ 0x8000 ≤ m.pc ∧ 0x8000 ≤ m.pc + 1 ∧ 0x8000 ≤ m.pc + 1 + 1 ∧ PositionWriters.innerP sy m0 m.pc = false := by
  have e : PipeWrites.opAt m = E.prg.get! (A.pc &&& E.mask).toNat := by unfold PipeWrites.opAt; rw [hs.prg, hs.mask, hs.pc]
  unfold okS at h
  rw [← e, List.contains_iff_mem.2 hop] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [hs.nmi, hs.pc]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **`SideW` away from the stores that may reach the timer** (round 33): a store through `X` to the zero page stays below the timer (the timer is not in the zero
page or the stack's page); a store to an absolute address plus an index, from whose base no index reaches the timer, misses it; a store through a pointer is near -/
theorem sideW_far {m : Machine} (h256 : 256 ≤ (ScrollRule.places sy m0).sideB) (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1)
    (hn : nearWB sy m0 m = false) : SideW sy m0 m := by
  intro t ht hlt heq
  have hn' := Bool.or_eq_false_iff.1 hn
  have hfar : PipeWrites.opAt m ∈ absWOps →
      PositionKeep.farB [(ScrollRule.places sy m0).sideB] (PositionKeep.operandAt m.prg m.prgMask m.pc) = true := by
    intro hm
    have h1 := hn'.1
    rw [List.contains_iff_mem.2 hm] at h1
    simpa using h1
  have hmiss : ∀ r : UInt8, PositionKeep.operandAt m.prg m.prgMask m.pc + r.toUInt16 = t → PipeWrites.opAt m ∈ absWOps → False := by
    intro r e hm
    have hi : (t &&& 0x7FF).toNat ∈ StepWrites.ramIdx (PositionKeep.operandAt m.prg m.prgMask m.pc + r.toUInt16) := by
      rw [e]; simp [StepWrites.ramIdx, hlt]
    exact PositionKeep.farB_spec (hfar hm) r _ hi (by rw [heq]; exact List.mem_singleton_self _)
  have h91 := hn'.2
  unfold PipeWrites.wTarget at ht
  generalize hop : PipeWrites.opAt m = op at ht hmiss h91
  by_cases c1 : (op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6) = true
  · rw [if_pos c1, zpx_t hp1] at ht
    have e := Option.some.inj ht
    have h1 : t.toNat < 256 := by rw [← e, UInt8.toNat_toUInt16]; exact UInt8.toNat_lt _
    have h2 : (t &&& 0x7FF).toNat ≤ t.toNat := by rw [UInt16.toNat_and]; exact Nat.and_le_left
    omega
  · rw [if_neg c1] at ht
    by_cases c2 : (op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E) = true
    · rw [if_pos c2, abx_t hp1 hp2] at ht
      refine hmiss m.x (Option.some.inj ht) ?_
      simp only [Bool.or_eq_true, beq_iff_eq] at c2
      simp only [absWOps, List.mem_cons, List.not_mem_nil, or_false]
      rcases c2 with ((h | h) | h) | h <;> simp [h]
    · rw [if_neg c2] at ht
      by_cases c3 : (op == 0x99) = true
      · rw [if_pos c3, aby_t hp1 hp2] at ht
        refine hmiss m.y (Option.some.inj ht) ?_
        simp only [beq_iff_eq] at c3
        simp [absWOps, c3]
      · rw [if_neg c3, if_neg (by simp [h91])] at ht
        cases ht

/-- **`SideW` from the field** (round 33): at a state of the walk that meets `okS`, `SideW` holds when it holds at the stores that may reach the timer -/
theorem sideW_of_near {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine} (h256 : 256 ≤ (ScrollRule.places sy m0).sideB) (hs : Sim E F A m)
    (hok : okS sy m0 E A = true) (hn : NearW sy m0 m → SideW sy m0 m) : SideW sy m0 m := by
  intro t ht hlt
  obtain ⟨_, _, p1, p2, _⟩ := okS_spec hs hok (wTarget_ops ht)
  cases e : nearWB sy m0 m with
  | true => exact hn e t ht hlt
  | false => exact sideW_far h256 p1 p2 e t ht hlt

end

/-! ## On the ROM: one frame -/

section Frames
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {m0 : Machine}

/-- **`CleanK` of the walks' guard**, from `CleanK` of `FrameKeep.guardE`, `SideW`, and the protection of his pixel and his page (`hpx`) -/
theorem cleanS_of {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK (FrameKeep.guardE sy m0) q m) (hw : SideW sy m0 m)
    (hpx : ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ pixI sy m0) :
    FrameKeep.CleanK (guardS sy m0) q m := by
  refine ⟨fun t ht hq => ?_, hc.read, hc.jump, hc.time⟩
  rcases hc.store t ht hq with ⟨h1, h2⟩ | h1
  · refine Or.inl ⟨h1, fun h3 => ?_⟩
    simp only [guardS, sideP, List.mem_append, List.mem_cons] at h3
    rcases h3 with ((h3 | h3) | h3) | h3
    · exact hw t ht h1 h3
    · exact hpx t ht h1 h3
    · rcases h3 with h3 | h3
      · exact h2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h3)))
      · exact h2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ h3))))))))
    · exact h2 (List.mem_append_right _ h3)
  · exact Or.inr h1

/-- the three bytes of `sideP` from `SideW` and the protection of his pixel and his page -/
theorem sideWL_of {m : Machine} (hw : SideW sy m0 m)
    (hpx : ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ pixI sy m0) : SideWL (sideP sy m0) m := by
  intro t ht hlt hm
  simp only [sideP, List.mem_cons] at hm
  rcases hm with h | h
  · exact hw t ht hlt h
  · exact hpx t ht hlt h

theorem pixI_x : (ScrollRule.places sy m0).x ∈ pixI sy m0 := List.mem_cons_self

/-- round 33: the push's value for the timer is at least 2 (a part of `sCheck`), so a frame that ends with the timer at most 1 does not end with it -/
theorem pushT_ne {v : UInt8} (hr : sCheck sy m0 v = true) {t : UInt8} (ht : t ≤ 1) : t ≠ pushT sy m0 := by
  simp only [sCheck, Bool.and_eq_true, decide_eq_true_eq] at hr
  have h2 := hr.1.1.1.1.1.1.1.1
  intro e
  rw [e] at ht
  have t1 := UInt8.le_iff_toNat_le.1 h2
  have t2 := UInt8.le_iff_toNat_le.1 ht
  have : (2 : UInt8).toNat = 2 := rfl
  have : (1 : UInt8).toNat = 1 := rfl
  omega

theorem pvI_x : (ScrollRule.places sy m0).x ∈ pvI sy m0 := List.mem_cons_self
theorem pvI_page : (ScrollRule.places sy m0).page ∈ pvI sy m0 := List.mem_cons_of_mem _ List.mem_cons_self
theorem pvI_speed : (sy.Player_X_Speed &&& 0x7FF).toNat ∈ pvI sy m0 := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **His pixel, his page and (round 33) his speed at the frame's end, when the frame does not end with the side collision's timer at the push's value**
(`OnFrames.nearStepAt`,
`OnFrames.stopRight`): with the hypotheses of
`EdgeStep.keep_r`, the frame comes to the scroll handler at `kq`; if from there each instruction of the frame meets `PositionKeep.PosW` (the field `posW`) and
`SideW` at the stores that may reach the timer (`NearW`; the field `sideW`; round 33: elsewhere a theorem, `sideW_far`), then at the instruction after the scroll handler's call his pixel, his page and his speed are those of the frame's end, when the frame does not end with
the timer at `pushT` (round 32: at most 1). `hc`, `hr`, `hst` are checks on the ROM. -/
theorem pix_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hr : sCheck sy m0 v = true) (hst : PositionWriters.offStack sy = true) {m : Machine}
    {i : UInt8} (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∃ kq, n₀ < kq ∧ (trace m i kq).pc = sy.PlayerSubs ∧ (trace m i kq).frame = m.frame ∧ (∀ j, n₀ < j → j < kq → (trace m i j).pc ≠ sy.PlayerSubs) ∧
      ((∀ j, kq ≤ j → (trace m i j).frame = m.frame → PositionKeep.PosW sy m0 (trace m i j) ∧ (NearW sy m0 (trace m i j) → SideW sy m0 (trace m i j))) →
        ∀ n, kq < n → (trace m i n).pc = EdgeStep.rPc sy → (frame m i).ram.get! (ScrollRule.places sy m0).sideB ≠ pushT sy m0 →
          ∀ b ∈ pvI sy m0, (frame m i).ram.get! b = (trace m i n).ram.get! b) := by
  simp only [sCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h256⟩, _⟩, _⟩, hne3⟩, hp1⟩, hp2⟩, hp3⟩, hp4⟩ := hr
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3 hp4
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3 hp4
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3 hp4
  generalize EdgeStep.qsSearch sy m0 v P.stops.toList = Ps at hp1 hp2 hp3 hp4
  rcases CtrlKeep.cut_or_end2 (C := cfgPS sy m0 v q (AfterKeep.q1Cfg sy m0 v P) (EdgeStep.qsCfg sy m0 v Ps) ((pvI sy m0).map fun b => sCfg sy m0 b Ps.stops.toList))
      hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with ⟨k₀, a1, a2, _, a4, a5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have hk0 : k₀ = n₀ := by
      rcases Nat.lt_trichotomy k₀ n₀ with h | h | h
      · exact absurd a1 (hfirst k₀ h)
      · exact h
      · exact absurd harr (a4 n₀ h)
    subst hk0
    have hV := EdgeStep.watched_at hc h0 hclK hv a1 a2 a4
    have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchA sy m0 v) hs (CtrlKeep.watchA_lt v) hV
    have hw : walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs
        (atSS sy m0 (EdgeStep.qsCfg sy m0 v Ps) ((pvI sy m0).map fun b => sCfg sy m0 b Ps.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨kq, hkq, hqq, hfq, hdq, hbq, Bq, hatq, hsq⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA a2 a5 hclF hx'
    refine ⟨kq, hkq, hqq, hfq, hbq, fun hp => ?_⟩
    have hcp : ∀ j, kq ≤ j → (trace m i j).frame = m.frame → EdgeStep.cutPos sy m0 (trace m i j).pc = false := by
      intro j hj hfj
      have W := (hp j hj hfj).1.1
      have hpg := StepPrg.trace_prg m i j
      have e1 : (trace m i j).prg = m0.prg := hpg.1.trans h0.prg
      have e2 : (trace m i j).prgMask = m0.prgMask := hpg.2.trans h0.mask
      rw [e1, e2] at W
      unfold EdgeStep.cutPos
      cases hs : FrameKeep.storesTo (PositionWriters.posI sy) m0.prg m0.prgMask (trace m i j).pc with
      | false => rfl
      | true => rw [W hs]; rfl
    have hw1 : walkQ1 (EdgeStep.qsCfg sy m0 v Ps) (FrameKeep.ctlI sy) (EdgeStep.rPc sy)
        (atRS sy m0 ((pvI sy m0).map fun b => sCfg sy m0 b Ps.stops.toList)) FrameKeep.fuelK Bq = true := hatq
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hb1, B₁, hat1, hs1⟩ :=
      AfterKeep.q1_run (C := EdgeStep.qsCfg sy m0 v Ps) hp3 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw1 hsq hfq hdq hclF hx'
    have hend : ∀ x ∈ pvI sy m0, (∃ B₂, (sCfg sy m0 x Ps.stops.toList).fin B₂ = true ∧
        Sim (sCfg sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) B₂ (frame m i)) ∧
        ∀ d, 1 ≤ d → (trace m i (k₁ + d)).pc ≠ EdgeStep.rPc sy := by
      intro x hxI
      have hmem : sCfg sy m0 x Ps.stops.toList ∈ (pvI sy m0).map fun b => sCfg sy m0 b Ps.stops.toList := List.mem_map.2 ⟨x, hxI, rfl⟩
      have hw2 := List.all_eq_true.1 hat1 _ hmem
      have ht2 := List.all_eq_true.1 hp4 _ hmem
      have hs2 : Sim (sCfg sy m0 x Ps.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! x) (rkOn B₁) (trace m i k₁) := AfterKeep.sim_rkOn hs1
      refine endKS (C := sCfg sy m0 x Ps.stops.toList) CollideKeep.cov_rkOff ht2 rfl rfl hne3 hw2 hs2 hf1 hd1 ?_ hx' (fun j hj hfj => hcp j (by omega) hfj)
      intro j hj hfj A hsA' hokA
      have W := hp j (by omega) hfj
      have hpx : ∀ t, PipeWrites.wTarget (PipeWrites.opAt (trace m i j)) (trace m i j) = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ pixI sy m0 := by
        intro t ht hlt
        obtain ⟨n1, p1, p2, p3, i1⟩ := okS_spec hsA' hokA (wTarget_ops ht)
        exact posW_plain W.1 hst n1 hsA'.halted p1 p2 p3 i1 ht hlt
      have hW := sideW_of_near h256 hsA' hokA W.2
      exact ⟨cleanS_of (hcl j) hW hpx, sideWL_of hW hpx⟩
    intro n hn hrp hside b hb
    have hnn : n = k₁ := by
      rcases Nat.lt_trichotomy n k₁ with h | h | h
      · exact absurd hrp (hb1 n hn h)
      · exact h
      · exfalso
        have := (hend _ pvI_x).2 (n - k₁) (by omega)
        rw [show k₁ + (n - k₁) = n by omega] at this
        exact this hrp
    subst hnn
    obtain ⟨B₂, hfin, hs₂⟩ := (hend b hb).1
    change ((B₂.rk && !B₂.spent) || eqAt (ScrollRule.places sy m0).sideB (pushT sy m0) B₂) = true at hfin
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hfin
    rcases hfin with ⟨hr1, hr2⟩ | hh
    · have e := hs₂.rkv hr1
      rw [if_neg (by simp [hr2])] at e
      exact e
    · exfalso
      simp only [eqAt, Bool.and_eq_true, beq_iff_eq] at hh
      have hlt : (ScrollRule.places sy m0).sideB < 2048 := FrameModel.I_lt _
      have hm := hs₂.ram _ hlt
      have e0 := isK_eq hh.1 hm
      rw [hh.2] at e0
      exact hside e0
  · exact absurd harr (hno n₀ hf0)

end Frames

end Smbrta.PushTimer
