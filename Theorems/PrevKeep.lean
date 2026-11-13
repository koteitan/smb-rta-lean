import Theorems.CtrlKeep

/-!
# Above ground: A and B of the frame before

The player's routine writes A and B (`A_B_Buttons`) from the pad's bits, and at its end the game engine copies them into A and B of the frame before
(`PreviousA_B_Buttons`, the routine `SaveAB`). The vertical model needs bit 7 of the two to be equal at the start of a frame (`PrevOK`).

The walk of the pause bit of `CtrlKeep` comes to the player's routine (the cut). There, for each value `b` of bit 7 of the pad's bits, a walk of `FrameKeep.walkKC` follows the
frame to its end (`prevCfg`): it protects A and B and A and B of the frame before (`abP`), it stops a path at a store to the routine, the mode or the task by its address
(no frame before the touch's frame has one: `FrameKeep.Frames.noStore`), and at the frame's end it asks bit 7 of both to be `b`. The paths that write the task by its address
(the axe, the change of area) return from the game core before the game engine and skip `SaveAB`; without the cut the walk fails there.

So (`prev_end`): a frame in control whose instructions meet `CleanK` of `FrameKeep.guardF` and `SpareAB` (no store through an index or a pointer writes the two bytes), and
none of which writes the routine, the mode or the task by its address, keeps `PrevOK`. A frame that does not come to the player's routine keeps both bytes
(`CtrlKeep.keep_of_noCut`).

The searches are no part of the proof: the check walks every state of its tables. No game data. Page: `1-1/e-2-SurfaceFrames.md`.
-/

namespace Smbrta.PrevKeep

open TaintRun
open PipeWrites (SG)

/-! ## A search that remembers where it came from: no part of the proof -/

/-- the search, with for each key of the table the key and the `pc` it was reached from, the failing states, the paths cut at a store, the states where a path stops
(`stop`), and where a followed byte is dropped -/
structure PS where
  X : SG := {}
  pred : Std.HashMap Nat (Nat × UInt16) := {}
  failAt : Array (Nat × AS) := #[]
  cutHits : Std.HashMap Nat Nat := {}
  stops : Array AS := #[]
  drops : Std.HashMap Nat Nat := {}

/-- what the search forgets: as `FrameKeep.normK`, but the bytes `keep` stay, and the followed byte stays followed -/
def normP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (keep : List Nat) (A0 : AS) : AS :=
  let B := FrameKeep.normK S G A0
  let B := keep.foldl (fun B i => B.setK i (A0.getK i)) B
  { B with rk := A0.rk, spent := A0.spent }

/-- the key: that of `FrameKeep.keyK`, and whether the byte is followed -/
def keyP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (W : List FrameKeep.Watch) (A : AS) : Nat :=
  FrameKeep.keyK S G W A * 4 + (if A.rk then 1 else 0) + (if A.spent then 2 else 0)

/-- `FrameKeep.routeKW` with `normP` -/
def routeP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (keep : List Nat) (key : AS → Nat) (X : SG) (B0 : AS) : SG :=
  let B := normP S G keep B0
  let K := key B
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (PipeWrites.knownOf D)
      let J := PipeWrites.joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (PipeWrites.knownOf D)
      if PipeWrites.leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := PipeWrites.joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (W : List FrameKeep.Watch) (keep : List Nat) (key : AS → Nat) (ops : Array (AM Unit))
    (l : List Nat) (stop : AS → Bool) (P0 : PS) (k0 : Nat) (A0 : AS) : PS := Id.run do
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
    let rs := (FrameKeep.preK S G cur).flatMap (FrameKeep.kstep S G E ops)
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
      let K := key (normP S G keep b)
      if !(pred.contains K) then pred := pred.insert K (k0, cur.pc)
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeP S G keep key X b
    break
  return ⟨X, pred, fa, ch, st, dr⟩

partial def searchP (S : FrameKeep.Spot) (G : PipeWrites.Guard) (E : Env) (W : List FrameKeep.Watch) (keep : List Nat) (key : AS → Nat) (ops : Array (AM Unit))
    (l : List Nat) (stop : AS → Bool) (P0 : PS) : PS := Id.run do
  let mut P := P0
  while true do
    match P.X.pending.minEntry? with
    | none => break
    | some (k, A) =>
      let ⟨X, pr, fa, ch, st, dr⟩ := P
      P := runP S G E W keep key ops l stop ⟨{ X with pending := X.pending.erase k }, pr, fa, ch, st, dr⟩ k A
  return P

/-- the search after the cut from the states `starts` (with `toA W V`), with the bytes `prot` protected too, the watched bits `W`, the paths cut at a store
to a byte of `l` by its address, stopped at `stop`, and the bytes `keep` kept by the search; `E` the machine (its followed byte) -/
def searchFrom (sy : Syms) (m0 : Machine) (E : Env) (prot keep : List Nat) (W : List FrameKeep.Watch) (l : List Nat) (stop : AS → Bool) (starts : List AS) : PS :=
  let S := FrameKeep.spotOf sy m0
  let G := CtrlKeep.guardP sy m0 prot
  let key := keyP S G W
  let X := starts.foldl (routeP S G keep key) {}
  searchP S G E W keep key (aRows E).toArray l stop { X }

/-- the search after the cut for A and B (`ctrl-prev-check`), from the states at the cut -/
def afterSearchP (sy : Syms) (m0 : Machine) (prot : List Nat) (W V : List FrameKeep.Watch) (l : List Nat) (starts : List AS) : PS :=
  searchFrom sy m0 (PipeEntryRule.envOf m0) prot [] W l (fun _ => false) (starts.map (CtrlKeep.toA W V))

/-- the path of `pc`s from the cut to a key -/
partial def pathOf (P : PS) (k : Nat) (acc : List UInt16) (fuel : Nat) : List UInt16 :=
  match fuel, P.pred[k]? with
  | 0, _ => acc
  | _, none => acc
  | f + 1, some (k', pc) => pathOf P k' (pc :: acc) f

/-! ## The check -/

/-- **A and B of this frame and of the frame before**: the bytes that the walk protects besides those of `CtrlKeep.spareI` -/
def abP (sy : Syms) : List Nat := [(sy.A_B_Buttons &&& 0x7FF).toNat, (sy.PreviousA_B_Buttons &&& 0x7FF).toNat]

/-- the pad's bits: the search keeps them from the cut to where the player's routine reads them (no part of the proof) -/
def savedI (sy : Syms) : Nat := (sy.SavedJoypadBits &&& 0x7FF).toNat

/-- **A store through an index or a pointer does not write A and B, or A and B of the frame before** (one instruction) -/
def SpareAB (sy : Syms) (m : Machine) : Prop := ∀ t, PipeWrites.wTarget (PipeWrites.opAt m) m = some t → t < 0x2000 → (t &&& 0x7FF).toNat ∉ abP sy

/-- `SpareAB`, for a program -/
def spareABB (sy : Syms) (m : Machine) : Bool :=
  match PipeWrites.wTarget (PipeWrites.opAt m) m with
  | some t => !(decide (t < 0x2000) && (abP sy).contains (t &&& 0x7FF).toNat)
  | none => true

/-- **Bit 7 of A and B of the frame before is that of A and B** on the machine `m` -/
def PrevOK (sy : Syms) (m : Machine) : Prop := peek m sy.PreviousA_B_Buttons &&& 0x80 = peek m sy.A_B_Buttons &&& 0x80

/-- `PrevOK`, for a program -/
def prevOKB (sy : Syms) (m : Machine) : Bool := peek m sy.PreviousA_B_Buttons &&& 0x80 == peek m sy.A_B_Buttons &&& 0x80

/-- the guard of the walk after the cut: that of `FrameKeep`, with the bytes of `abP` and of `CtrlKeep.spareI` protected -/
def guardAB (sy : Syms) (m0 : Machine) : PipeWrites.Guard := { FrameKeep.guardF sy m0 with prot := abP sy ++ (FrameKeep.guardF sy m0).prot }

/-- the walk after the cut with bit 7 of the pad's bits `b` at the cut: its table, from the states at the cut `starts`; the paths are cut at a store to the routine,
the mode or the task by address -/
def prevCfg (sy : Syms) (m0 : Machine) (v : UInt8) (b : Bool) (starts : List AS) : FrameKeep.CfgK :=
  let S := FrameKeep.spotOf sy m0
  let G := guardAB sy m0
  let E := PipeEntryRule.envOf m0
  let W := CtrlKeep.watchP sy m0 v b
  let key := keyP S G W
  let P := searchFrom sy m0 E (abP sy ++ CtrlKeep.spareI sy m0) [savedI sy] W (FrameKeep.ctlI sy) (fun _ => false) (starts.map (CtrlKeep.toA W (CtrlKeep.valP sy v b)))
  let q := FrameKeep.tableOfKW key P.X
  { E, ops := (aRows E).toArray, S, G, W, t := q.1, kl := q.1.map PipeWrites.knownOf, idx := q.2.1, cut := q.2.2, key, fin := fun _ => true }

/-- the walk of the pause bit up to the cut, and from there the two walks after the cut, one for each value of bit 7 of the pad's bits -/
def afterPB (sy : Syms) (m0 : Machine) (v : UInt8) (C0 C1 : FrameKeep.CfgK) (B : AS) : Bool :=
  FrameKeep.walkKC C0 (FrameKeep.ctlI sy) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchP sy m0 v false) (CtrlKeep.valP sy v false) B) &&
  FrameKeep.walkKC C1 (FrameKeep.ctlI sy) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchP sy m0 v true) (CtrlKeep.valP sy v true) B)

def cfgPB (sy : Syms) (m0 : Machine) (v : UInt8) (q : CtrlKeep.Table) (C0 C1 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with after := afterPB sy m0 v C0 C1 }

/-- **The check of A and B of the frame before**: the walk of the pause bit up to the cut; from there, for each value `b` of bit 7 of the pad's bits, the walk to the
frame's end, with the stores to the routine, the mode and the task by address cut; at the frame's end it asks bit 7 of A and B and of A and B of the frame before to be
`b`, and the bits of `CtrlKeep.watchA` -/
def prevCheck (sy : Syms) (m0 : Machine) (v : UInt8) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let C0 := prevCfg sy m0 v false cuts
  let C1 := prevCfg sy m0 v true cuts
  CtrlKeep.ctrlCheck1 (cfgPB sy m0 v q C0 C1) && C0.t.all (FrameKeep.walkKC C0 (FrameKeep.ctlI sy) FrameKeep.fuelK) &&
    C1.t.all (FrameKeep.walkKC C1 (FrameKeep.ctlI sy) FrameKeep.fuelK)

/-! ## The walk covers the frame from the cut to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

/-- **From the cut to the frame's end, with the stores of `l` cut**: as `CtrlKeep.after_end`, by the walk `FrameKeep.walkKC`, if no instruction writes a byte of `l`
by its address -/
theorem after_endC {CA : FrameKeep.CfgK} {l : List Nat} {Fu Fu' : Nat} {F : Nat × UInt8} (ht : CA.t.all (FrameKeep.walkKC CA l Fu) = true)
    (hkl : CA.kl = CA.t.map PipeWrites.knownOf) (hops : CA.ops = (aRows CA.E).toArray) (hT : 2 ≤ F.2.toNat) {m : Machine} {i : UInt8} {k : Nat} {A : AS}
    (hw : FrameKeep.walkKC CA l Fu' A = true) (hs : Sim CA.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK CA.G CA.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∃ B, FrameKeep.watchOK CA.W B = true ∧ Sim CA.E F B (frame m i) := by
  have key : ∀ d, (∃ A, FrameKeep.LiveKC CA l F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK CA.W B = true ∧ Sim CA.E F B (trace m i (k + d))) := by
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
        rcases FrameKeep.live_stepKC ht hkl hops hT h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, a4⟩ | ⟨a1, B, a2, _, _, _, a3⟩
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

variable {sy : Syms} {m0 : Machine}

theorem prevCheck_parts {v : UInt8} (h : prevCheck sy m0 v = true) :
    CtrlKeep.ctrlCheck1 (cfgPB sy m0 v (CtrlKeep.cutTable sy m0 true) (prevCfg sy m0 v false (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true))))
        (prevCfg sy m0 v true (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true))))) = true ∧
    (prevCfg sy m0 v false (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))).t.all
      (FrameKeep.walkKC (prevCfg sy m0 v false (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))) (FrameKeep.ctlI sy) FrameKeep.fuelK) = true ∧
    (prevCfg sy m0 v true (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))).t.all
      (FrameKeep.walkKC (prevCfg sy m0 v true (CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 (CtrlKeep.cutTable sy m0 true)))) (FrameKeep.ctlI sy) FrameKeep.fuelK) = true := by
  unfold prevCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem bit7_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0x80 = CtrlKeep.bit7 (UInt8.ofNat n.val &&& 0x80 != 0) &&& 0x80 := by decide +kernel

/-- bit 7 of a byte -/
theorem bit7_eq (x : UInt8) : x &&& 0x80 = CtrlKeep.bit7 (x &&& 0x80 != 0) &&& 0x80 := by
  have h := bit7_all ⟨x.toNat, x.toNat_lt⟩
  simpa using h

/-- `CleanK` of the walk's guard: `CleanK` of `FrameKeep.guardF` and `SpareAB` -/
theorem cleanAB_of {q : UInt16} {m : Machine} (hc : FrameKeep.CleanK (FrameKeep.guardF sy m0) q m) (hs : SpareAB sy m) : FrameKeep.CleanK (guardAB sy m0) q m :=
  CtrlKeep.cleanK_prot (G := FrameKeep.guardF sy m0) (l := abP sy) hc hs

theorem watchP_lt (v : UInt8) (b : Bool) : ∀ w ∈ CtrlKeep.watchP sy m0 v b, w.1 < 2048 := by
  intro w hw
  simp only [CtrlKeep.watchP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact CtrlKeep.watchA_lt v w hw
  · exact PipeTransitionAll.mask_lt _
  · exact PipeTransitionAll.mask_lt _

/-- **One frame from the cut, for a value `b` of bit 7 of the pad's bits at the cut**: the walk `prevCfg` gives bit 7 of A and B and of A and B of the frame before `b` at the
frame's end -/
theorem prev_of_walk {v : UInt8} {b : Bool} {starts : List AS} (ht : (prevCfg sy m0 v b starts).t.all (FrameKeep.walkKC (prevCfg sy m0 v b starts) (FrameKeep.ctlI sy) FrameKeep.fuelK) = true)
    {m : Machine} {i : UInt8} {k : Nat} {B : AS} {bI : Nat}
    (hw : FrameKeep.walkKC (prevCfg sy m0 v b starts) (FrameKeep.ctlI sy) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchP sy m0 v b) (CtrlKeep.valP sy v b) B) = true)
    (hs : Sim (CtrlKeep.envR m0 bI) (m.frame, m.ram.get! bI) B (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hV : FrameKeep.Watched (CtrlKeep.valP sy v b) (trace m i k))
    (hcl : ∀ j, FrameKeep.CleanK (guardAB sy m0) (FrameKeep.spotOf sy m0).store (trace m i j)) (hx : ∀ j, FrameKeep.CtlStore sy (trace m i j) = false) :
    peek (frame m i) sy.A_B_Buttons &&& 0x80 = CtrlKeep.bit7 b &&& 0x80 ∧ peek (frame m i) sy.PreviousA_B_Buttons &&& 0x80 = CtrlKeep.bit7 b &&& 0x80 := by
  have hsA := CtrlKeep.sim_toA (W := CtrlKeep.watchP sy m0 v b) hs (watchP_lt v b) hV
  obtain ⟨B', hB', hs'⟩ := after_endC (CA := prevCfg sy m0 v b starts) (F := (m.frame, 2)) ht rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA hf hd hcl hx
  have hW := FrameKeep.watched_of hB' hs'
  have e1 := hW _ (List.mem_append_right _ (List.mem_cons_self (a := ((sy.A_B_Buttons &&& 0x7FF).toNat, (0x80 : UInt8), CtrlKeep.bit7 b))))
  have e2 := hW _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))
  exact ⟨e1, e2⟩

/-- **A frame in control keeps bit 7 of A and B of the frame before equal to that of A and B.** The frame starts in the idle loop in control (`FrameKeep.StartK`), each
instruction meets `CleanK` of `FrameKeep.guardF` and `SpareAB`, and writes neither the routine, nor the mode, nor the task by its address; the area's type is `v`, the
swimming flag 0, the change of size 0. If the frame comes to the player's routine, the routine writes A and B from the pad's bits and the game engine copies them
(`SaveAB`): the walk after the cut. If it does not, it keeps both bytes (`CtrlKeep.keep_of_noCut`). `hc`, `hp` are the checks on the ROM. -/
theorem prev_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} (hp : prevCheck sy m0 v = true) {m : Machine} {i : UInt8} (h0 : FrameKeep.StartK sy m0 m)
    (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n)) (hab : ∀ n, SpareAB sy (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) (h : PrevOK sy m) : PrevOK sy (frame m i) := by
  obtain ⟨hp1, hp2, hp3⟩ := prevCheck_parts hp
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hcl n)
  have hclA : ∀ n, FrameKeep.CleanK (guardAB sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => cleanAB_of (hcl n) (hab n)
  rcases CtrlKeep.cut_or_end2 (C := cfgPB sy m0 v q (prevCfg sy m0 v false cuts) (prevCfg sy m0 v true cuts)) hp1 rfl rfl rfl (CtrlKeep.cfg_start q _ true h0) hclK with
    ⟨k, h1, h2, _, h4, h5, B, _, hB2, hs⟩ | ⟨hno, _⟩
  · have A := CtrlKeep.ctrl_keep hc h0 hclK h1 h2 h4
    have hB2' : afterPB sy m0 v (prevCfg sy m0 v false cuts) (prevCfg sy m0 v true cuts) B = true := hB2
    simp only [afterPB, Bool.and_eq_true] at hB2'
    replace hB2 := hB2'
    have hA : ∀ b : Bool, (trace m i k).ram.get! (savedI sy) &&& 0x80 = CtrlKeep.bit7 b &&& 0x80 → FrameKeep.Watched (CtrlKeep.valP sy v b) (trace m i k) := by
      intro b hb w hw
      simp only [CtrlKeep.valP, CtrlKeep.valA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
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
      · exact hb
    have hb := bit7_eq ((trace m i k).ram.get! (savedI sy))
    generalize ((trace m i k).ram.get! (savedI sy) &&& 0x80 != 0) = b at hb
    have hhs : Sim (CtrlKeep.envR m0 (sy.Player_X_Speed &&& 0x7FF).toNat) (m.frame, m.ram.get! (sy.Player_X_Speed &&& 0x7FF).toNat) B (trace m i k) := hs
    have hx' : ∀ j, FrameKeep.CtlStore sy (trace m i j) = false := hx
    cases b with
    | false =>
      obtain ⟨e1, e2⟩ := prev_of_walk hp2 hB2.1 hhs h2 h5 (hA false hb) hclA hx'
      show (frame m i).ram.get! _ &&& 0x80 = (frame m i).ram.get! _ &&& 0x80
      exact e2.trans e1.symm
    | true =>
      obtain ⟨e1, e2⟩ := prev_of_walk hp3 hB2.2 hhs h2 h5 (hA true hb) hclA hx'
      show (frame m i).ram.get! _ &&& 0x80 = (frame m i).ram.get! _ &&& 0x80
      exact e2.trans e1.symm
  · unfold PrevOK
    rw [CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA]), CtrlKeep.keep_of_noCut hc h0 hclK hno _ (by simp [CtrlKeep.keepA])]
    exact h

end

end Smbrta.PrevKeep
