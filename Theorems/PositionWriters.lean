import Theorems.CollideKeep
import Theorems.PositionDispatch

/-!
# Above ground: the instructions that write the position after the scroll handler

A frame in control comes to the scroll handler (`PlayerSubs`, the machine `Q`), as in `CollideKeep`. From there to the frame's end the walk of the speed
(`CollideKeep.vCfg`) covers every machine. Here the same walk asks more things at each of its states (`okW`) and at each of its steps (`walkKW`):

* an instruction that writes the position's pixel, page or fraction by its address is one of the list `w`;
* at the entry of the push (`ImpedePlayerMove`) and of the clamp at the screen's edge (`ScreenClamp.places`): no interrupt pending and bit 7 of the
  PPU's control known 0; the speed (the byte that the walk follows) still followed or known 0; the return address on the stack known, and outside the two
  calls (`innerP`);
* at the clamp's entry the bits 1 to 7 of `Y` are known to be 0;
* the instruction is in the program's half of the address space, and the followed byte is never marked spent;
* a step into the inside of the two calls comes from the inside or from an entry, and a step never starts to follow the speed again;
* whether the call of the scroll handler is open (`Ph0`: the stack two bytes or more below that at `Q`, the four stack bytes `phQ` of that call and of the routine
  it is in): at the clamp's entry it is open and the stack is two bytes below that at `Q`; at the push's entry it is not; a step into a machine where it is open
  comes from one where it is open, or from `Q` (`phK`, `phN`; `AtW.phC`, `AtW.phI`, `FrameW.ph`; used by `PositionOrder`).

So (`writers_end`, `FrameW`): each machine of the frame from the scroll handler on meets `AtW`, and a step into the inside of the calls comes from the inside or
an entry. Each machine from `Q` on is in the frame or the next one, the frame ends within `fuelPerFrame` instructions, and a machine at the scroll handler from
the player's routine on is in the frame or is its end (`subs_frame`). From this and four conditions on single instructions (none of the instructions of `outside` runs; an instruction that is not `plainOp` does not write the
position; the margins at the push; `Y = 0` at the clamp) every reached cut of `PositionDispatch` is `Ready` (`ready_all`), so the frame is a chain whose effects
add up (`chain_of`). If the frame ends with the speed of the scroll handler and that speed is not 0, the speed stays on every machine (`FrameW.kept`,
`speedKW`); so on a frame that moves right and keeps its speed, with the clamp's target the position, the position stays (`keep_of`: the field `AfterP.keep`
from conditions).

The private check takes for `w` the list `writersIn`: nine instructions, two of the clamp, two of the push, and five of three other routines (the horizontal
platforms, the climbing routine, the loop of a castle). The walk asks nothing of a store through an index or a pointer: there it does not know the index (402
places), and `FrameKeep.guardE` does not protect the position. The searches are no part of the proof. No game data. Page: `1-1/e-2-10-3-7-PositionWriters.md`.
-/

namespace Smbrta.PositionWriters

open TaintRun

/-- the position's pixel, page and fraction -/
def posI (sy : Syms) : List Nat := [FrameModel.I sy.Player_X_Position, FrameModel.I sy.Player_PageLoc, FrameModel.I sy.SprObject_X_MoveForce]

/-- **The inside of the two calls**: an instruction after the push's entry, up to its return, or after the clamp's entry, before its tail (the clamp's pixel and
page stores). The walk asks that no other instruction steps into it, and that the two calls return outside it -/
def innerP (sy : Syms) (m0 : Machine) (p : UInt16) : Bool :=
  let D := ImpedePosition.sites sy m0
  let P := ScreenClamp.places sy m0
  (decide (D.entry < p) && decide (p ≤ D.ret)) || (decide (P.entry < p) && decide (p < P.tail))

/-- the return address on the stack is known, and the instruction after it is not in `inn` -/
def retOK (inn : UInt16 → Bool) (A : AS) : Bool :=
  let lo := A.getK (FrameModel.stkI (A.s + 1))
  let hi := A.getK (FrameModel.stkI (A.s + 1 + 1))
  lo.k == 0xFF && hi.k == 0xFF && !inn ((lo.v.toUInt16 ||| (hi.v.toUInt16 <<< 8)) + 1)

/-- **The bytes of an open call of the scroll handler**: on the stack's page, at `sQ − 1` and `sQ` the return address `rt` that the call at the scroll handler
pushes, and at `sQ + 1` and `sQ + 2` the return address `rc` of the routine that the scroll handler is in (as the stack holds it at the player's routine) -/
def phL (sQ : UInt8) (rt rc : UInt16) : List (UInt8 × UInt8) :=
  [(sQ - 1, rt.toUInt8), (sQ, (rt >>> 8).toUInt8), (sQ + 1, rc.toUInt8), (sQ + 2, (rc >>> 8).toUInt8)]

/-- **The scroll handler's call is open, as the walk knows it**: the stack is at least two bytes below `sQ` (the stack at the scroll handler), and the bytes of `L`
on the stack's page are known and have their values -/
def phK (sQ : UInt8) (L : List (UInt8 × UInt8)) (A : AS) : Bool :=
  decide (A.s.toNat + 2 ≤ sQ.toNat) && L.all fun p => (A.getK (FrameModel.stkI p.1)).k == 0xFF && (A.getK (FrameModel.stkI p.1)).v == p.2

/-- **The scroll handler's call is not open, as the walk knows it**: the stack is above `sQ − 2`, or a known bit of a byte of `L` differs from its value -/
def phN (sQ : UInt8) (L : List (UInt8 × UInt8)) (A : AS) : Bool :=
  decide (sQ.toNat < A.s.toNat + 2) || L.any fun p => FrameKeep.excl (A.getK (FrameModel.stkI p.1)) p.2

/-- **The scroll handler's call is open, on the machine** -/
def Ph0 (sQ : UInt8) (L : List (UInt8 × UInt8)) (m : Machine) : Prop :=
  m.s.toNat + 2 ≤ sQ.toNat ∧ ∀ p ∈ L, m.ram.get! (FrameModel.stkI p.1) = p.2

/-- the return address of the routine that the player's routine is in, as the stack holds it when the frame first comes to the player's routine -/
def callerRet (sy : Syms) (m0 : Machine) : UInt16 :=
  match PipeEntryRule.firstAt sy.PlayerCtrlRoutine 100000 { m0 with pad := 0x01 } with
  | some m => (m.ram.get! (FrameModel.stkI (m.s + 1))).toUInt16 ||| ((m.ram.get! (FrameModel.stkI (m.s + 1 + 1))).toUInt16 <<< 8)
  | none => 0

/-- the bytes of an open call of the scroll handler, on the ROM -/
def phQ (sy : Syms) (m0 : Machine) : List (UInt8 × UInt8) := phL (FrameModel.ctrlStack sy m0) (sy.PlayerSubs + 2) (callerRet sy m0)

theorem stkI_lt0 (s : UInt8) : FrameModel.stkI s < 2048 := by
  have h : ∀ n : Fin 256, FrameModel.stkI (UInt8.ofNat n.val) < 2048 := by decide +kernel
  simpa using h ⟨s.toNat, s.toNat_lt⟩

/-- `phK` of a state gives `Ph0` of the machines it covers -/
theorem ph0_of {sQ : UInt8} {L : List (UInt8 × UInt8)} {A : AS} {m : Machine} (h : phK sQ L A = true) (hs : m.s = A.s)
    (hr : ∀ i, i < 2048 → (A.getK i).mem (m.ram.get! i)) : Ph0 sQ L m := by
  simp only [phK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  refine ⟨by rw [hs]; exact h.1, fun p hp => ?_⟩
  obtain ⟨h2, h3⟩ := h.2 p hp
  rw [isK_eq (by simp [AB.isK, h2]) (hr _ (stkI_lt0 _)), h3]

theorem excl_ne {b : AB} {x v : UInt8} (h : FrameKeep.excl b v = true) (hm : b.mem x) : x ≠ v := by
  intro e
  subst e
  simp only [FrameKeep.excl, bne_iff_ne, ne_eq] at h
  exact h hm

/-- `phN` of a state gives that the machines it covers are not `Ph0` -/
theorem not_ph0_of {sQ : UInt8} {L : List (UInt8 × UInt8)} {A : AS} {m : Machine} (h : phN sQ L A = true) (hs : m.s = A.s)
    (hr : ∀ i, i < 2048 → (A.getK i).mem (m.ram.get! i)) : ¬ Ph0 sQ L m := by
  intro ⟨p1, p2⟩
  simp only [phN, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨p, hp, he⟩
  · rw [hs] at p1; omega
  · exact excl_ne he (hr _ (stkI_lt0 _)) (p2 p hp)

/-- **What the walk asks at each state**: a store of the position by its address only at `w`; at `ip` and `cp` no interrupt pending and bit 7 of the PPU's control
known 0; at `cp` the bits 1 to 7 of `Y` known 0; at `ip` and `cp` the followed byte (the speed) still followed, or known 0; the instruction and its two
next bytes in the program's half of the address space -/
def okW (E : Env) (pl : List Nat) (w : List UInt16) (ip cp : UInt16) (inn : UInt16 → Bool) (sQ : UInt8) (L : List (UInt8 × UInt8)) (A : AS) : Bool :=
  (!FrameKeep.storesTo pl E.prg E.mask A.pc || w.contains A.pc) &&
  ((A.pc != ip && A.pc != cp) || (!A.nmi && A.ppuCtrl.k &&& 0x80 == 0x80 && A.ppuCtrl.v &&& 0x80 == 0)) &&
  (A.pc != cp || (A.y.k &&& 0xFE == 0xFE && A.y.v &&& 0xFE == 0)) &&
  ((A.pc != ip && A.pc != cp) || (A.rk && !A.spent) || CollideKeep.zeroAt E.rkI A) &&
  (decide (0x8000 ≤ A.pc) && decide (0x8000 ≤ A.pc + 1) && decide (0x8000 ≤ A.pc + 1 + 1)) &&
  ((A.pc != ip && A.pc != cp) || retOK inn A) && (A.pc != cp || (phK sQ L A && A.s + 2 == sQ)) && (A.pc != ip || phN sQ L A) && !A.spent

/-- **The walk**: `CollideKeep.walkKV` that asks `okW` at each state -/
def walkKW (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (Q : UInt16) (pl : List Nat) (w : List UInt16) (ip cp : UInt16) (inn : UInt16 → Bool)
    (sQ : UInt8) (L : List (UInt8 × UInt8)) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => okW C.E pl w ip cp inn sQ L A && (FrameKeep.storesTo l C.E.prg C.E.mask A.pc || ((FrameKeep.preK C.S C.G A).flatMap sp).all fun A₁ =>
    !isRkDec C.E A₁.pc (LagFrames.opOf C.E A₁) && (FrameKeep.kstep C.S C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then B.pc != Q && (!inn B.pc || inn A.pc || A.pc == ip || A.pc == cp) && (!B.rk || A.rk) &&
        (phN sQ L B || phK sQ L A || A.pc == Q) &&
        ((C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) || walkKW C sp l Q pl w ip cp inn sQ L n B)
      else B.k == A.k + 1 && FrameKeep.watchOK C.W B && FrameKeep.endOK C.G B && C.fin B && (!B.rk || A.rk))

/-- what the first walk asks at the scroll handler: this walk succeeds -/
def atQW (sy : Syms) (m0 : Machine) (w : List UInt16) (C2 : FrameKeep.CfgK) (B : AS) : Bool :=
  walkKW C2 (CollideKeep.rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs (posI sy) w sy.ImpedePlayerMove (ScreenClamp.places sy m0).entry (innerP sy m0)
    (FrameModel.ctrlStack sy m0) (phQ sy m0) FrameKeep.fuelK (AfterKeep.rkOn B)

/-- the walk of the pause bit up to the cut, then the first walk of `AfterKeep`, then this walk -/
def cfgPW (sy : Syms) (m0 : Machine) (v : UInt8) (w : List UInt16) (q : CtrlKeep.Table) (C1 C2 : FrameKeep.CfgK) : CtrlKeep.CfgR :=
  { CtrlKeep.cfgPz sy m0 q with
    after := fun B => AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQW sy m0 w C2) FrameKeep.fuelK (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) }

/-- the position's bytes are not on the stack's page -/
def offStack (sy : Syms) : Bool := (posI sy).all fun i => i < 256 || 512 ≤ i

/-- **The check**: as `CollideKeep.vCheck`, on the same table, with `okW` at each state of the last walk; and the clamp's amount for `Y = 0` is 0 -/
def wCheck (sy : Syms) (m0 : Machine) (v : UInt8) (w : List UInt16) : Bool :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C1 := AfterKeep.q1Cfg sy m0 v P
  let C2 := CollideKeep.vCfg sy m0 P.stops.toList
  sy.PlayerCtrlRoutine != sy.PlayerSubs && sy.PlayerSubs != sy.EndlessLoop &&
    sy.ImpedePlayerMove != (ScreenClamp.places sy m0).entry &&
    ScreenClamp.amount (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) 0 == 0 && offStack sy &&
    CtrlKeep.ctrlCheck1 (cfgPW sy m0 v w q C1 C2) && C1.t.all (AfterKeep.walkQ1 C1 (FrameKeep.ctlI sy) sy.PlayerSubs (atQW sy m0 w C2) FrameKeep.fuelK) &&
    C2.t.all (walkKW C2 (CollideKeep.rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs (posI sy) w sy.ImpedePlayerMove (ScreenClamp.places sy m0).entry (innerP sy m0)
      (FrameModel.ctrlStack sy m0) (phQ sy m0) FrameKeep.fuelK)

/-- **The instructions that store the position by its address, as the walk meets them** (from the states of the table and of the scroll handler): the list
that the private check takes for `w` -/
def collectW (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (Q : UInt16) (pl : List Nat) : Nat → AS → List UInt16
  | 0, _ => []
  | n + 1, A => (if FrameKeep.storesTo pl C.E.prg C.E.mask A.pc then [A.pc] else []) ++
    (if FrameKeep.storesTo l C.E.prg C.E.mask A.pc then [] else
      ((FrameKeep.preK C.S C.G A).flatMap sp).flatMap fun A₁ => (FrameKeep.kstep C.S C.G C.E C.ops A₁).flatMap fun r =>
        match r with
        | none => []
        | some B =>
          if B.k == A.k && B.pc != Q && !(C.cut.get! B.pc.toNat != 0 && FrameKeep.coverK C B) then collectW C sp l Q pl n B else [])

/-- the list of `collectW` over the walk's table and the states at the scroll handler, without repeats -/
def writersIn (sy : Syms) (m0 : Machine) (v : UInt8) : List UInt16 :=
  let q := CtrlKeep.cutTable sy m0 true
  let cuts := CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q)
  let P := AfterKeep.q1Search sy m0 v cuts
  let C2 := CollideKeep.vCfg sy m0 P.stops.toList
  let f := collectW C2 (CollideKeep.rkOff C2.E) (FrameKeep.ctlI sy) sy.PlayerSubs (posI sy) FrameKeep.fuelK
  ((C2.t.toList.flatMap f) ++ (P.stops.toList.flatMap fun B => f (AfterKeep.rkOn B))).eraseDups

/-- the instructions of `w` outside the push (`ImpedePosition.sites`, from its entry to its return) and outside the clamp (`ScreenClamp.places`, from its entry to
its return) -/
def outside (sy : Syms) (m0 : Machine) (w : List UInt16) : List UInt16 :=
  let D := ImpedePosition.sites sy m0
  let P := ScreenClamp.places sy m0
  w.filter fun p => !(decide (D.entry ≤ p) && decide (p ≤ D.ret)) && !(decide (P.entry ≤ p) && decide (p ≤ P.ret))

/-! ## The machines: what `okW` gives -/

/-- **What the theorem says of one machine** after the scroll handler: it writes the position by its address only at `w`; at the entry of the push and of the clamp it
is `Good`, and its speed is `s0` or 0; at the clamp's entry `Y` is 0 or 1 -/
structure AtW (sy : Syms) (m0 : Machine) (w : List UInt16) (s0 : UInt8) (R : Machine) : Prop where
  writes : FrameKeep.storesTo (posI sy) R.prg R.prgMask R.pc = true → R.pc ∈ w
  good : R.pc = sy.ImpedePlayerMove ∨ R.pc = (ScreenClamp.places sy m0).entry → FrameModel.Good (FrameModel.Rom.of m0) R
  sel : R.pc = (ScreenClamp.places sy m0).entry → R.y ∈ [0, (1 : UInt8)]
  /-- at both entries the speed is `s0` (the speed at the scroll handler) or 0 -/
  speed : R.pc = sy.ImpedePlayerMove ∨ R.pc = (ScreenClamp.places sy m0).entry → peek R sy.Player_X_Speed = s0 ∨ peek R sy.Player_X_Speed = 0
  /-- the instruction and its two next bytes are in the program's half of the address space -/
  rom : 0x8000 ≤ R.pc ∧ 0x8000 ≤ R.pc + 1 ∧ 0x8000 ≤ R.pc + 1 + 1
  /-- at both entries, the call returns outside the inside of the two calls (`innerP`) -/
  ret : R.pc = sy.ImpedePlayerMove ∨ R.pc = (ScreenClamp.places sy m0).entry → innerP sy m0 (ImpedePosition.returnPc R) = false
  /-- at the clamp's entry the scroll handler's call is open (`Ph0`), and the stack is two bytes below the stack at the scroll handler -/
  phC : R.pc = (ScreenClamp.places sy m0).entry → Ph0 (FrameModel.ctrlStack sy m0) (phQ sy m0) R ∧ R.s + 2 = FrameModel.ctrlStack sy m0
  /-- at the push's entry the scroll handler's call is not open -/
  phI : R.pc = sy.ImpedePlayerMove → ¬ Ph0 (FrameModel.ctrlStack sy m0) (phQ sy m0) R

/-- a byte that agrees with `v` on the known bits `k`, with bit 7 of `k` set and of `v` clear, has bit 7 clear -/
theorem and80 {x k v : UInt8} (h : x &&& k = v &&& k) (hk : k &&& 0x80 = 0x80) (hv : v &&& 0x80 = 0) : x &&& 0x80 = 0 := by
  have e1 : x &&& 0x80 = (x &&& k) &&& 0x80 := by rw [UInt8.and_assoc, hk]
  have e2 : (v &&& k) &&& 0x80 = (v &&& 0x80) &&& k := by
    rw [UInt8.and_assoc, UInt8.and_assoc, UInt8.and_comm k]
  rw [e1, h, e2, hv]
  exact UInt8.zero_and

theorem fe_all : ∀ n : Fin 256, UInt8.ofNat n.val &&& 0xFE = 0 → UInt8.ofNat n.val ∈ [0, (1 : UInt8)] := by decide +kernel

/-- the same with the bits 1 to 7: the byte is 0 or 1 -/
theorem andFE {x k v : UInt8} (h : x &&& k = v &&& k) (hk : k &&& 0xFE = 0xFE) (hv : v &&& 0xFE = 0) : x ∈ [0, (1 : UInt8)] := by
  have e1 : x &&& 0xFE = (x &&& k) &&& 0xFE := by rw [UInt8.and_assoc, hk]
  have e2 : (v &&& k) &&& 0xFE = (v &&& 0xFE) &&& k := by
    rw [UInt8.and_assoc, UInt8.and_assoc, UInt8.and_comm k]
  have h0 : x &&& 0xFE = 0 := by
    rw [e1, h, e2, hv]
    exact UInt8.zero_and
  have := fe_all ⟨x.toNat, x.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h0

theorem stkI_all : ∀ n : Fin 256, FrameModel.stkI (UInt8.ofNat n.val) < 2048 := by decide +kernel

theorem stkI_lt (s : UInt8) : FrameModel.stkI s < 2048 := by
  have := stkI_all ⟨s.toNat, s.toNat_lt⟩
  simpa using this

/-- **`okW` of a state gives `AtW` of each machine it covers** -/
theorem atW_of {sy : Syms} {m0 : Machine} {w : List UInt16} {E : Env} {F : Nat × UInt8} {A : AS} {m : Machine}
    (hE : E.prg = m0.prg) (hM : E.mask = m0.prgMask) (hrk : E.rkI = CollideKeep.spI sy) (hs : Sim E F A m)
    (h : okW E (posI sy) w sy.ImpedePlayerMove (ScreenClamp.places sy m0).entry (innerP sy m0) (FrameModel.ctrlStack sy m0) (phQ sy m0) A = true) :
    AtW sy m0 w F.2 m := by
  simp only [okW, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, _⟩ := h
  refine ⟨fun hw => ?_, fun he => ?_, fun he => ?_, fun he => ?_, ?_, fun he => ?_, fun he => ?_, fun he => ?_⟩
  · rw [hs.prg, hs.mask, hs.pc] at hw
    rcases h1 with h1 | h1
    · rw [h1] at hw; cases hw
    · rw [hs.pc]; exact h1
  · rw [hs.pc] at he
    rcases h2 with ⟨n1, n2⟩ | ⟨⟨hn, hk⟩, hv⟩
    · rcases he with e | e
      · exact absurd e n1
      · exact absurd e n2
    · exact ⟨hs.prg.trans hE, hs.mask.trans hM, hs.nmi.trans hn, hs.halted, hs.trk, hs.size, and80 hs.ppuCtrl hk hv⟩
  · rw [hs.pc] at he
    rcases h3 with h3 | ⟨hk, hv⟩
    · exact absurd he h3
    · exact andFE hs.y hk hv
  · rw [hs.pc] at he
    rcases h4 with (⟨n1, n2⟩ | ⟨hr, hsp⟩) | hz
    · rcases he with e | e
      · exact absurd e n1
      · exact absurd e n2
    · left
      have e := hs.rkv hr
      rw [if_neg (by simp [hsp]), hrk] at e
      exact e
    · right
      simp only [CollideKeep.zeroAt, Bool.and_eq_true, beq_iff_eq] at hz
      have hm := hs.ram E.rkI (by rw [hrk]; exact PipeTransitionAll.mask_lt _)
      have e := (isK_eq hz.1 hm).trans hz.2
      rw [hrk] at e
      exact e
  · rw [hs.pc]
    simp only [decide_eq_true_eq] at h5 h6 h7
    exact ⟨h5, h6, h7⟩
  · rw [hs.pc] at he
    rcases h8 with ⟨n1, n2⟩ | hr
    · rcases he with e | e
      · exact absurd e n1
      · exact absurd e n2
    · simp only [retOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hr
      obtain ⟨⟨k1, k2⟩, k3⟩ := hr
      have m1 := hs.ram (FrameModel.stkI (A.s + 1)) (stkI_lt _)
      have m2 := hs.ram (FrameModel.stkI (A.s + 1 + 1)) (stkI_lt _)
      have e1 : m.ram.get! (FrameModel.stkI (A.s + 1)) = (A.getK (FrameModel.stkI (A.s + 1))).v := isK_eq (by simp [AB.isK, k1]) m1
      have e2 : m.ram.get! (FrameModel.stkI (A.s + 1 + 1)) = (A.getK (FrameModel.stkI (A.s + 1 + 1))).v := isK_eq (by simp [AB.isK, k2]) m2
      unfold ImpedePosition.returnPc
      rw [hs.s, e1, e2]
      exact k3
  · rw [hs.pc] at he
    rcases h9 with h9 | ⟨hk, hs2⟩
    · exact absurd he h9
    · exact ⟨ph0_of hk hs.s hs.ram, by rw [hs.s]; exact hs2⟩
  · rw [hs.pc] at he
    rcases h10 with h10 | hn
    · exact absurd he h10
    · exact not_ph0_of hn hs.s hs.ram

/-! ## The walk covers the frame from the scroll handler to its end -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)
open PipeTransitionAll (go)

variable {C : FrameKeep.CfgK} {sp : AS → List AS} {l : List Nat} {Q : UInt16} {pl : List Nat} {w : List UInt16} {ip cp : UInt16} {inn : UInt16 → Bool} {Fu : Nat}
  {F : Nat × UInt8} {sQ : UInt8} {L : List (UInt8 × UInt8)}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveKW (C : FrameKeep.CfgK) (sp : AS → List AS) (l : List Nat) (Q : UInt16) (pl : List Nat) (w : List UInt16) (ip cp : UInt16) (inn : UInt16 → Bool)
    (sQ : UInt8) (L : List (UInt8 × UInt8)) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop :=
  Sim C.E F A m ∧ ∃ n, walkKW C sp l Q pl w ip cp inn sQ L n A = true

theorem LiveKW.ok {A : AS} {m : Machine} (h : LiveKW C sp l Q pl w ip cp inn sQ L F A m) : okW C.E pl w ip cp inn sQ L A = true := by
  obtain ⟨_, n, hw⟩ := h
  cases n with
  | zero => simp [walkKW] at hw
  | succ n =>
    simp only [walkKW, Bool.and_eq_true] at hw
    exact hw.1

theorem cover_liveKW (ht : C.t.all (walkKW C sp l Q pl w ip cp inn sQ L Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf) {B : AS} {m : Machine}
    (hs : Sim C.E F B m) (h : FrameKeep.coverK C B = true) : ∃ D, LiveKW C sp l Q pl w ip cp inn sQ L F D m ∧ D.k = B.k ∧ D.rk = B.rk := by
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
    have h2' := h2
    unfold PipeWrites.leK at h2'
    simp only [Bool.and_eq_true, beq_iff_eq] at h2'
    have hle := PipeWrites.leK_le h2
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, (PipeWrites.le_k hle).symm, h2'.1.2.symm⟩
  · cases h2

theorem live_stepKW (hsp : Cov C.E F sp) (ht : C.t.all (walkKW C sp l Q pl w ip cp inn sQ L Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) {A : AS} {m : Machine} (hl : LiveKW C sp l Q pl w ip cp inn sQ L F A m) (hh : FrameKeep.CleanK C.G C.S.store m)
    (hx : FrameKeep.storesTo l m.prg m.prgMask m.pc = false) :
    (∃ A', LiveKW C sp l Q pl w ip cp inn sQ L F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot ∧
      (go step m).2.pc ≠ Q ∧ (inn (go step m).2.pc = true → inn m.pc = true ∨ m.pc = ip ∨ m.pc = cp) ∧ (A'.rk = true → A.rk = true) ∧
      (Ph0 sQ L (go step m).2 → Ph0 sQ L m ∨ m.pc = Q)) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, FrameKeep.watchOK C.W B = true ∧ FrameKeep.endOK C.G B = true ∧ C.fin B = true ∧ B.k = A.k + 1 ∧
      Sim C.E F B (go step m).2 ∧ (B.rk = true → A.rk = true)) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkKW] at hw
  | succ n =>
    have hx' : FrameKeep.storesTo l C.E.prg C.E.mask A.pc = false := by rw [← hs.prg, ← hs.mask, ← hs.pc]; exact hx
    obtain ⟨A₁, hA, hs1, hk1⟩ := CollKeep.cov_preKX hsp hh hs
    simp only [walkKW, hx', Bool.false_or, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hd, hw2⟩ := hw.2 A₁ hA
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
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq] at hw3
        obtain ⟨⟨⟨⟨hq, hin⟩, hrk⟩, hph⟩, hw4⟩ := hw3
        have hq' : (go step m).2.pc ≠ Q := by rw [h1.pc]; exact hq
        have hin' : inn (go step m).2.pc = true → inn m.pc = true ∨ m.pc = ip ∨ m.pc = cp := by
          intro hb
          rw [h1.pc] at hb
          rw [hs.pc]
          rcases hin with ((e | e) | e) | e
          · rw [e] at hb; cases hb
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
          · exact Or.inr (Or.inr e)
        have hrk' : B.rk = true → A.rk = true := by
          intro hb
          rcases hrk with e | e
          · rw [e] at hb; cases hb
          · exact e
        have hph' : Ph0 sQ L (go step m).2 → Ph0 sQ L m ∨ m.pc = Q := by
          intro hP
          rcases hph with (e | e) | e
          · exact absurd hP (not_ph0_of e h1.s h1.ram)
          · exact Or.inl (ph0_of e hs.s hs.ram)
          · exact Or.inr (by rw [hs.pc]; exact e)
        rcases hw4 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk, hDr⟩ := cover_liveKW ht hkl h1 h3
          exact ⟨D, hD, by rw [hk, k1], k2, k3, hq', hin', fun hd => hrk' (hDr ▸ hd), hph'⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3, hq', hin', hrk', hph'⟩
      · right
        rw [hk1] at k1
        rw [if_neg (by simp [k1])] at hw3
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hw3
        refine ⟨k2, B, hw3.1.1.1.2, hw3.1.1.2, hw3.1.2, k1, h1, fun hb => ?_⟩
        rcases hw3.2 with e | e
        · rw [e] at hb; cases hb
        · exact e

/-- **The walk, from the scroll handler to the frame's end.** The machine `k` instructions into the frame of `m`, covered by a state from which the walk succeeds:
every machine of the same frame from there on is covered by a state that meets `okW` -/
theorem okKW (hsp : Cov C.E F sp) (ht : C.t.all (walkKW C sp l Q pl w ip cp inn sQ L Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKW C sp l Q pl w ip cp inn sQ L Fu' A = true)
    (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    ∀ d, ((trace m i (k + d)).frame = m.frame ∧ (∃ B, Sim C.E F B (trace m i (k + d)) ∧ okW C.E pl w ip cp inn sQ L B = true) ∧ (1 ≤ d → (trace m i (k + d)).pc ≠ Q) ∧
        ((trace m i (k + d + 1)).frame = m.frame → inn (trace m i (k + d + 1)).pc = true →
          inn (trace m i (k + d)).pc = true ∨ (trace m i (k + d)).pc = ip ∨ (trace m i (k + d)).pc = cp) ∧
        ((trace m i (k + d + 1)).frame = m.frame → Ph0 sQ L (trace m i (k + d + 1)) → Ph0 sQ L (trace m i (k + d)) ∨ (trace m i (k + d)).pc = Q)) ∨
      (trace m i (k + d)).frame = m.frame + 1 := by
  have key : ∀ d, (∃ A, LiveKW C sp l Q pl w ip cp inn sQ L F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧ (1 ≤ d → (trace m i (k + d)).pc ≠ Q)) ∨
      (trace m i (k + d)).frame = m.frame + 1 := by
    intro d
    induction d with
    | zero => exact Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, fun h => absurd h (by omega)⟩
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, _⟩ | h1
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rw [e]
        rcases live_stepKW hsp ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, _, a5, _, _, _⟩ | ⟨a1, _⟩
        · exact Or.inl ⟨A', a1, by rw [a3, h2], fun _ => a5⟩
        · exact Or.inr (by rw [a1, h2])
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        exact Or.inr h1
  intro d
  rcases key d with ⟨B, hB, hf, hq⟩ | h
  · have hh := hB.1.halted
    have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [hf, hh]
    have e : trace m i (k + d + 1) = (go step (trace m i (k + d))).2 := by
      show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
      simp only [PipeEntryRule.nxt, if_neg hn]
    refine Or.inl ⟨hf, ⟨B, hB.1, hB.ok⟩, hq, fun hf1 hin => ?_, fun hf1 hP => ?_⟩
    · rw [e] at hf1 hin
      rcases live_stepKW hsp ht hkl hops hB (hcl (k + d)) (hx (k + d)) with ⟨_, _, _, _, _, _, a6, _, _⟩ | ⟨a1, _⟩
      · exact a6 hin
      · rw [a1, hf] at hf1; omega
    · rw [e] at hf1 hP
      rcases live_stepKW hsp ht hkl hops hB (hcl (k + d)) (hx (k + d)) with ⟨_, _, _, _, _, _, _, _, a8⟩ | ⟨a1, _⟩
      · exact a8 hP
      · rw [a1, hf] at hf1; omega
  · exact Or.inr h


/-- **The followed byte along the walk**: the frame of `m` ends, and if the state at its end still follows the byte, the byte was `F.2` at every machine of the frame
from `k` on (a step of the walk never starts to follow the byte again, and the walk never marks it spent) -/
theorem speedKW (hsp : Cov C.E F sp) (ht : C.t.all (walkKW C sp l Q pl w ip cp inn sQ L Fu) = true) (hkl : C.kl = C.t.map PipeWrites.knownOf)
    (hops : C.ops = (aRows C.E).toArray) {m : Machine} {i : UInt8} {k Fu' : Nat} {A : AS} (hw : walkKW C sp l Q pl w ip cp inn sQ L Fu' A = true)
    (hs : Sim C.E F A (trace m i k)) (hf : (trace m i k).frame = m.frame) (hd : m.fdot + 3 * k ≤ (trace m i k).fdot)
    (hcl : ∀ j, FrameKeep.CleanK C.G C.S.store (trace m i j))
    (hx : ∀ j, FrameKeep.storesTo l (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (frame m i) ∧
      (B.rk = true → ∀ d, (trace m i (k + d)).frame = m.frame → (trace m i (k + d)).ram.get! C.E.rkI = F.2) := by
  have spentF : ∀ {A : AS} {m' : Machine}, LiveKW C sp l Q pl w ip cp inn sQ L F A m' → A.spent = false := by
    intro A m' h
    have := h.ok
    simp only [okW, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2
  have key : ∀ d, (∃ A, LiveKW C sp l Q pl w ip cp inn sQ L F A (trace m i (k + d)) ∧ (trace m i (k + d)).frame = m.frame ∧
        m.fdot + 3 * (k + d) ≤ (trace m i (k + d)).fdot ∧
        (A.rk = true → ∀ j, j ≤ d → (trace m i (k + j)).frame = m.frame → (trace m i (k + j)).ram.get! C.E.rkI = F.2)) ∨
      ((trace m i (k + d)).frame = m.frame + 1 ∧ ∃ B, C.fin B = true ∧ Sim C.E F B (trace m i (k + d)) ∧
        (B.rk = true → ∀ j, j ≤ d → (trace m i (k + j)).frame = m.frame → (trace m i (k + j)).ram.get! C.E.rkI = F.2)) := by
    intro d
    induction d with
    | zero =>
      refine Or.inl ⟨A, ⟨hs, Fu', hw⟩, hf, hd, fun hr j hj _ => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      have e := hs.rkv hr
      rw [spentF ⟨hs, Fu', hw⟩] at e
      simpa using e
    | succ d ih =>
      rcases ih with ⟨A, h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
      · have hh := h1.1.halted
        have hn : ¬ (((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true) := by simp [h2, hh]
        have e : trace m i (k + (d + 1)) = (go step (trace m i (k + d))).2 := by
          show PipeEntryRule.nxt (m.frame + 1) (trace m i (k + d)) = _
          simp only [PipeEntryRule.nxt, if_neg hn]
        rcases live_stepKW hsp ht hkl hops h1 (hcl (k + d)) (hx (k + d)) with ⟨A', a1, _, a3, a4, _, _, a7, _⟩ | ⟨a1, B, _, _, a2, _, a3, a4⟩
        · refine Or.inl ⟨A', by rw [e]; exact a1, by rw [e, a3, h2], by rw [e]; omega, fun hr j hj hfj => ?_⟩
          rcases Nat.lt_or_ge j (d + 1) with hj' | hj'
          · exact h4 (a7 hr) j (by omega) hfj
          · have hj0 : j = d + 1 := by omega
            subst hj0
            have ee := a1.1.rkv hr
            rw [spentF a1] at ee
            rw [e]
            simpa using ee
        · refine Or.inr ⟨by rw [e, a1, h2], B, a2, by rw [e]; exact a3, fun hr j hj hfj => ?_⟩
          rcases Nat.lt_or_ge j (d + 1) with hj' | hj'
          · exact h4 (a4 hr) j (by omega) hfj
          · have hj0 : j = d + 1 := by omega
            subst hj0
            rw [e, a1, h2] at hfj
            omega
      · have hst : ((trace m i (k + d)).frame ≥ m.frame + 1 || (trace m i (k + d)).halted) = true := by simp [h1]
        have e : trace m i (k + (d + 1)) = trace m i (k + d) := by
          rw [show k + (d + 1) = k + d + 1 by omega, PipeEntryRule.trace_stop hst 1]
        refine Or.inr ⟨by rw [e]; exact h1, B, h2, by rw [e]; exact h3, fun hr j hj hfj => ?_⟩
        rcases Nat.lt_or_ge j (d + 1) with hj' | hj'
        · exact h4 hr j (by omega) hfj
        · have hj0 : j = d + 1 := by omega
          subst hj0
          rw [e, h1] at hfj
          omega
  have a1 := hs.hi
  have a2 := hs.lim
  have a3 : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
  rcases key (fuelPerFrame - k) with ⟨A, h1, _, h3, _⟩ | ⟨h1, B, h2, h3, h4⟩
  · exfalso
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    have b1 := h1.1.hi
    have b2 := h1.1.lim
    omega
  · have hk : k ≤ fuelPerFrame := by
      have := hs.hi
      omega
    rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at h1 h3
    rw [PipeEntryRule.frame_trace]
    refine ⟨h1, B, h2, h3, fun hr d hfd => h4 hr d ?_ hfd⟩
    by_cases hc : d ≤ fuelPerFrame - k
    · exact hc
    · exfalso
      have hst : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [h1]
      have ee := PipeEntryRule.trace_stop hst (k + d - fuelPerFrame)
      rw [show fuelPerFrame + (k + d - fuelPerFrame) = k + d by omega] at ee
      rw [ee, h1] at hfd
      omega
end

/-! ## On the ROM: one frame -/

section
open PipeEntryRule (trace)
open PipeTransition (frame)

variable {sy : Syms} {m0 : Machine}

/-- **What the theorem says of the frame from the scroll handler `k` on**: each machine of the frame `f` from `k` on meets `AtW`; and a step into the inside of the
two calls (`innerP`) comes from the inside or from one of the two entries -/
structure FrameW (sy : Syms) (m0 : Machine) (w : List UInt16) (s0 : UInt8) (T : Nat → Machine) (k f : Nat) : Prop where
  atW : ∀ j, k ≤ j → (T j).frame = f → AtW sy m0 w s0 (T j)
  step : ∀ j, k ≤ j → (T (j + 1)).frame = f → innerP sy m0 (T (j + 1)).pc = true →
    innerP sy m0 (T j).pc = true ∨ (T j).pc = sy.ImpedePlayerMove ∨ (T j).pc = (ScreenClamp.places sy m0).entry
  /-- if the frame ends (at `e`) with the speed `s0` and `s0 ≠ 0`, then every machine of the frame from `k` on has the speed `s0` -/
  kept : ∀ e, (T e).frame = f + 1 → peek (T e) sy.Player_X_Speed = s0 → s0 ≠ 0 → ∀ j, k ≤ j → (T j).frame = f → peek (T j) sy.Player_X_Speed = s0
  /-- every machine from `k` on is in the frame or in the next one -/
  two : ∀ j, k ≤ j → (T j).frame = f ∨ (T j).frame = f + 1
  /-- the frame ends within `fuelPerFrame` instructions -/
  ends : (T fuelPerFrame).frame = f + 1
  /-- a machine of the frame after `k` where the scroll handler's call is open (`Ph0`) comes after one where it is open, or right after `k` -/
  ph : ∀ j, k ≤ j → (T (j + 1)).frame = f → Ph0 (FrameModel.ctrlStack sy m0) (phQ sy m0) (T (j + 1)) →
    Ph0 (FrameModel.ctrlStack sy m0) (phQ sy m0) (T j) ∨ j = k

/-- **A frame in control, from the scroll handler to its end, writes the position by its address only at `w`; it is `Good` at the entries of the push and of the
clamp, and `Y` is 0 or 1 at the clamp's entry.** The hypotheses are those of `CollideKeep.speed_end`: the frame starts in the idle loop in control
(`FrameKeep.StartK`), each instruction meets `CleanK` of `FrameKeep.guardE` and writes neither the routine, nor the mode, nor the task by its address; the area's
type is `v`, the swimming flag 0, the change of size 0; it comes to the player's routine at `n₀`, the first time. `hc`, `hh` are the checks on the ROM. -/
theorem writers_end (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → (trace m i k).frame = m.frame →
      FrameW sy m0 w (peek (trace m i k) sy.Player_X_Speed) (trace m i) k m.frame := by
  simp only [wCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hh
  obtain ⟨⟨⟨⟨⟨⟨⟨hne1, hne2⟩, _⟩, _⟩, _⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPW sy m0 v w q (AfterKeep.q1Cfg sy m0 v P) (CollideKeep.vCfg sy m0 P.stops.toList)) hp1 rfl rfl rfl
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
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQW sy m0 w (CollideKeep.vCfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    have hs2 : Sim (CollideKeep.vCfg sy m0 P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (CollideKeep.spI sy)) (AfterKeep.rkOn B₁)
        (trace m i k₁) := AfterKeep.sim_rkOn hs₁
    have hclV : ∀ j, FrameKeep.CleanK (CollideKeep.vCfg sy m0 P.stops.toList).G (CollideKeep.vCfg sy m0 P.stops.toList).S.store (trace m i j) :=
      fun j => CollideKeep.cleanV_of (hcl j)
    have hok := okKW (C := CollideKeep.vCfg sy m0 P.stops.toList) CollideKeep.cov_rkOff hp3 rfl rfl hat hs2 hf1 hclV hx'
    have hsk := speedKW (C := CollideKeep.vCfg sy m0 P.stops.toList) CollideKeep.cov_rkOff hp3 rfl rfl hat hs2 hf1 hd1 hclV hx'
    intro k hk hpc hfk
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
        rcases hok (k - k₁) with ⟨_, _, hq, _⟩ | hst
        · have := hq (by omega)
          rw [show k₁ + (k - k₁) = k by omega] at this
          exact this hpc
        · rw [show k₁ + (k - k₁) = k by omega, hfk] at hst
          omega
    subst hkk
    refine ⟨fun j hj hfj => ?_, fun j hj hf1 hin => ?_, fun e he hve hnz j hj hfj => ?_, fun j hj => ?_, ?_, fun j hj hf1 hP => ?_⟩
    · rcases hok (j - k) with ⟨_, ⟨B, hB, hokB⟩, _⟩ | hst
      · rw [show k + (j - k) = j by omega] at hB
        exact atW_of rfl rfl rfl hB hokB
      · rw [show k + (j - k) = j by omega, hfj] at hst
        omega
    · rcases hok (j - k) with ⟨_, _, _, hs4, _⟩ | hst
      · rw [show k + (j - k) = j by omega] at hs4
        exact hs4 hf1 hin
      · rw [show k + (j - k) = j by omega] at hst
        have hs' : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [hst]
        have e := PipeEntryRule.trace_stop hs' 1
        rw [e, hst] at hf1
        omega
    · obtain ⟨hfe, B, hfin, hsB, hkeep⟩ := hsk
      have hend : PipeTransition.frame m i = trace m i e := by
        rw [PipeEntryRule.frame_trace] at hfe ⊢
        have s1 : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [hfe]
        have s2 : ((trace m i e).frame ≥ m.frame + 1 || (trace m i e).halted) = true := by simp [he]
        rcases Nat.lt_or_ge e fuelPerFrame with hl | hl
        · have := PipeEntryRule.trace_stop s2 (fuelPerFrame - e)
          rw [show e + (fuelPerFrame - e) = fuelPerFrame by omega] at this
          exact this
        · have := PipeEntryRule.trace_stop s1 (e - fuelPerFrame)
          rw [show fuelPerFrame + (e - fuelPerFrame) = e by omega] at this
          exact this.symm
      change ((B.rk && !B.spent) || CollideKeep.zeroAt (CollideKeep.spI sy) B) = true at hfin
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hfin
      rcases hfin with ⟨hr, _⟩ | hz
      · have := hkeep hr (j - k) (by rw [show k + (j - k) = j by omega]; exact hfj)
        rw [show k + (j - k) = j by omega] at this
        exact this
      · exfalso
        simp only [CollideKeep.zeroAt, Bool.and_eq_true, beq_iff_eq] at hz
        have hm := hsB.ram (CollideKeep.spI sy) (PipeTransitionAll.mask_lt _)
        have e0 := (isK_eq hz.1 hm).trans hz.2
        rw [hend] at e0
        exact hnz (hve.symm.trans e0)
    · rcases hok (j - k) with ⟨hf, _⟩ | hst
      · rw [show k + (j - k) = j by omega] at hf
        exact Or.inl hf
      · rw [show k + (j - k) = j by omega] at hst
        exact Or.inr hst
    · have hfe := hsk.1
      rw [PipeEntryRule.frame_trace] at hfe
      exact hfe
    · rcases hok (j - k) with ⟨_, _, hq, _, hs5⟩ | hst
      · rw [show k + (j - k) = j by omega] at hs5 hq
        rcases hs5 hf1 hP with h | h
        · exact Or.inl h
        · by_cases hjk : j = k
          · exact Or.inr hjk
          · exact absurd h (hq (by omega))
      · rw [show k + (j - k) = j by omega] at hst
        have hs' : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true := by simp [hst]
        have e := PipeEntryRule.trace_stop hs' 1
        rw [e, hst] at hf1
        omega
  · exact absurd harr (hno n₀ hf0)

/-- **The scroll handler's machine is in the frame, or it is the frame's end**: with the hypotheses of `writers_end`, a machine from the player's routine on at the
scroll handler is in the frame of `m`, or the trace has stopped there and it is the machine at the frame's end -/
theorem subs_frame (hc : CtrlKeep.ctrlCheck sy m0 = true) {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) {m : Machine} {i : UInt8}
    (h0 : FrameKeep.StartK sy m0 m) (hcl : ∀ n, FrameKeep.CleanK (FrameKeep.guardE sy m0) (FrameKeep.spotOf sy m0).store (trace m i n))
    (hx : ∀ n, FrameKeep.CtlStore sy (trace m i n) = false) (hv : CtrlKeep.AreaOK sy v m) {n₀ : Nat}
    (harr : (trace m i n₀).pc = sy.PlayerCtrlRoutine) (hf0 : (trace m i n₀).frame = m.frame) (hfirst : ∀ j, j < n₀ → (trace m i j).pc ≠ sy.PlayerCtrlRoutine) :
    ∀ k, n₀ ≤ k → (trace m i k).pc = sy.PlayerSubs → (trace m i k).frame = m.frame ∨ trace m i k = PipeTransition.frame m i := by
  simp only [wCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hh
  obtain ⟨⟨⟨⟨⟨⟨⟨hne1, hne2⟩, _⟩, _⟩, _⟩, hp1⟩, hp2⟩, hp3⟩ := hh
  generalize CtrlKeep.cutTable sy m0 true = q at hp1 hp2 hp3
  generalize CtrlKeep.cutsOf (CtrlKeep.cfgPz sy m0 q) = cuts at hp1 hp2 hp3
  generalize AfterKeep.q1Search sy m0 v cuts = P at hp1 hp2 hp3
  have hclF : ∀ n, FrameKeep.CleanK (FrameKeep.guardF sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_E (hcl n)
  have hclK : ∀ n, FrameKeep.CleanK (FrameKeep.guardK sy m0) (FrameKeep.spotOf sy m0).store (trace m i n) := fun n => FrameKeep.cleanK_of_F (hclF n)
  have hx' : ∀ j, FrameKeep.storesTo (FrameKeep.ctlI sy) (trace m i j).prg (trace m i j).prgMask (trace m i j).pc = false := hx
  rcases CtrlKeep.cut_or_end2 (C := cfgPW sy m0 v w q (AfterKeep.q1Cfg sy m0 v P) (CollideKeep.vCfg sy m0 P.stops.toList)) hp1 rfl rfl rfl
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
    have hw : AfterKeep.walkQ1 (AfterKeep.q1Cfg sy m0 v P) (FrameKeep.ctlI sy) sy.PlayerSubs (atQW sy m0 w (CollideKeep.vCfg sy m0 P.stops.toList)) FrameKeep.fuelK
        (CtrlKeep.toA (CtrlKeep.watchA sy m0 v) (CtrlKeep.valA sy v) B) = true := hB2
    obtain ⟨k₁, hk1, hq1, hf1, hd1, hbt, B₁, hat, hs₁⟩ :=
      AfterKeep.q1_run (C := AfterKeep.q1Cfg sy m0 v P) hp2 rfl rfl (by show 2 ≤ (2 : UInt8).toNat; decide) hw hsA h2 h5 hclF hx'
    have hs2 : Sim (CollideKeep.vCfg sy m0 P.stops.toList).E ((m.frame, (2 : UInt8)).1, (trace m i k₁).ram.get! (CollideKeep.spI sy)) (AfterKeep.rkOn B₁)
        (trace m i k₁) := AfterKeep.sim_rkOn hs₁
    have hclV : ∀ j, FrameKeep.CleanK (CollideKeep.vCfg sy m0 P.stops.toList).G (CollideKeep.vCfg sy m0 P.stops.toList).S.store (trace m i j) :=
      fun j => CollideKeep.cleanV_of (hcl j)
    have hok := okKW (C := CollideKeep.vCfg sy m0 P.stops.toList) CollideKeep.cov_rkOff hp3 rfl rfl hat hs2 hf1 hclV hx'
    have hsk := speedKW (C := CollideKeep.vCfg sy m0 P.stops.toList) CollideKeep.cov_rkOff hp3 rfl rfl hat hs2 hf1 hd1 hclV hx'
    intro k hk hpc
    rcases Nat.lt_trichotomy k k₁ with h | h | h
    · exfalso
      by_cases e : k = k₀
      · subst e
        rw [h1] at hpc
        exact hne1 hpc
      · exact hbt k (by omega) h hpc
    · rw [h]
      exact Or.inl hf1
    · rcases hok (k - k₁) with ⟨_, _, hq, _⟩ | hst
      · exfalso
        have := hq (by omega)
        rw [show k₁ + (k - k₁) = k by omega] at this
        exact this hpc
      · right
        rw [show k₁ + (k - k₁) = k by omega] at hst
        have s1 : ((trace m i k).frame ≥ m.frame + 1 || (trace m i k).halted) = true := by simp [hst]
        have hfe := hsk.1
        rw [PipeEntryRule.frame_trace] at hfe ⊢
        have s2 : ((trace m i fuelPerFrame).frame ≥ m.frame + 1 || (trace m i fuelPerFrame).halted) = true := by simp [hfe]
        rcases Nat.lt_or_ge k fuelPerFrame with hl | hl
        · have := PipeEntryRule.trace_stop s1 (fuelPerFrame - k)
          rw [show k + (fuelPerFrame - k) = fuelPerFrame by omega] at this
          exact this.symm
        · have := PipeEntryRule.trace_stop s2 (k - fuelPerFrame)
          rw [show fuelPerFrame + (k - fuelPerFrame) = k by omega] at this
          exact this
  · exact absurd harr (hno n₀ hf0)

end

/-! ## What this gives of `PositionDispatch.Ready` -/

section
variable {sy : Syms} {m0 : Machine}

/-- the small facts of `wCheck`: the push's entry is not the clamp's, the clamp's amount for `Y = 0` is 0, the position is off the stack's page -/
theorem wCheck_facts {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) :
    sy.ImpedePlayerMove ≠ (ScreenClamp.places sy m0).entry ∧ ScreenClamp.amount (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) 0 = 0 ∧
      offStack sy = true := by
  simp only [wCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hh
  exact ⟨hh.1.1.1.1.1.2, hh.1.1.1.1.2, hh.1.1.1.2⟩

theorem posOf_range (p x f : UInt8) : 0 ≤ FrameModel.posOf p x f ∧ FrameModel.posOf p x f < 0x1000000 := by
  unfold FrameModel.posOf
  have h1 := p.toNat_lt
  have h2 := x.toNat_lt
  have h3 := f.toNat_lt
  omega

/-- **`Ready` at the clamp's entry with `Y = 0`** (the left edge): `Good` and the selector are `AtW`, and the target is in the position's range because the clamp's
amount for `Y = 0` is 0 -/
theorem ready_clamp {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) {s0 : UInt8} {R : Machine} (h : AtW sy m0 w s0 R)
    (hpc : R.pc = (ScreenClamp.places sy m0).entry) (hy : R.y = 0) : PositionDispatch.Ready sy m0 R := by
  obtain ⟨hne, ha, _⟩ := wCheck_facts hh
  have hpi : R.pc ≠ sy.ImpedePlayerMove := by rw [hpc]; exact fun e => hne e.symm
  unfold PositionDispatch.Ready
  rw [if_neg hpi, if_pos hpc]
  refine ⟨h.good (Or.inr hpc), h.sel hpc, ?_⟩
  have hr := posOf_range (peek R ((ScreenClamp.places sy m0).edgeP + R.y.toUInt16)) (peek R ((ScreenClamp.places sy m0).edgeX + R.y.toUInt16))
    (R.ram.get! (ScreenClamp.places sy m0).frac)
  have hz : (ScreenClamp.amount (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) R.y).toNat = 0 := by rw [hy, ha]; rfl
  unfold ScreenClamp.target
  rw [hz]
  omega

/-- **`Ready` at the push's entry**, from `AtW` and the margins of the position against its ends -/
theorem ready_impede {w : List UInt16} {s0 : UInt8} {R : Machine} (h : AtW sy m0 w s0 R) (hpc : R.pc = sy.ImpedePlayerMove)
    (hl : 256 ≤ posP sy R) (hr : posP sy R + 256 < 0x1000000) : PositionDispatch.Ready sy m0 R := by
  unfold PositionDispatch.Ready
  rw [if_pos hpc]
  exact ⟨h.good (Or.inl hpc), hl, hr⟩

end

/-! ## `Ordinary` at an instruction that writes nothing, the stack, or a byte by its address -/

section
open PipeTransitionAll (go)

/-- the write entry of an opcode writes nothing, or only on the stack -/
def quietW : StepWrites.Wr → Bool
  | .no => true
  | .st _ => true
  | .md _ _ => false

/-- **A plain opcode**: it writes nothing, or only the stack, or it is a store or a read-modify-write by a zero page or absolute address (the opcodes of
`FrameKeep.storesTo`). Every other opcode writes through an index or a pointer (or is not one that the game uses) -/
def plainOp (op : UInt8) : Bool := quietW (StepWrites.wOf op) || FrameKeep.zpWrites.contains op || FrameKeep.absWrites.contains op

theorem fetchP {m : Machine} (hp : 0x8000 ≤ m.pc) : go fetch m = (m.prg.get! (m.pc &&& m.prgMask).toNat, { m with pc := m.pc + 1 }) := by
  show go (rd m.pc) { m with pc := m.pc + 1 } = _
  rw [FrameModel.rd_rom hp]

theorem stk_all : ∀ n : Fin 256, (0x100 ||| (UInt8.ofNat n.val).toUInt16) < 0x2000 ∧
    256 ≤ ((0x100 ||| (UInt8.ofNat n.val).toUInt16) &&& 0x7FF).toNat ∧ ((0x100 ||| (UInt8.ofNat n.val).toUInt16) &&& 0x7FF).toNat < 512 := by decide +kernel

theorem stk_range : ∀ (k : Nat) (s : UInt8) (i : Nat), i ∈ StepWrites.stk s k → 256 ≤ i ∧ i < 512
  | 0, _, _, h => by simp [StepWrites.stk] at h
  | k + 1, s, i, h => by
    simp only [StepWrites.stk, List.mem_append] at h
    rcases h with h | h
    · have hs := stk_all ⟨s.toNat, s.toNat_lt⟩
      simp only [UInt8.ofNat_toNat] at hs
      simp only [StepWrites.ramIdx, if_pos hs.1, List.mem_singleton] at h
      subst h
      exact hs.2
    · exact stk_range k (s - 1) i h

theorem zp_all : ∀ n : Fin 256, ((UInt8.ofNat n.val).toUInt16 &&& 0x7FF).toNat = (UInt8.ofNat n.val).toNat := by decide +kernel

theorem zp_idx (b : UInt8) : StepWrites.ramIdx b.toUInt16 = [b.toNat] := by
  have h := zp_all ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  simp only [StepWrites.ramIdx, if_pos (FrameModel.zp_lt b), h]

theorem wOf_zp : ∀ op ∈ FrameKeep.zpWrites, StepWrites.wOf op = StepWrites.wZp := by
  intro op h
  simp only [FrameKeep.zpWrites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem wOf_abs : ∀ op ∈ FrameKeep.absWrites, StepWrites.wOf op = StepWrites.wAbs := by
  intro op h
  simp only [FrameKeep.absWrites, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **`Ordinary` of a plain instruction that does not write the position by its address**, away from the end of the address space -/
theorem ordinary_plain {sy : Syms} {R : Machine} (hst : offStack sy = true) (hp : 0x8000 ≤ R.pc) (hp1 : 0x8000 ≤ R.pc + 1) (hp2 : 0x8000 ≤ R.pc + 1 + 1)
    (hplain : plainOp (R.prg.get! (R.pc &&& R.prgMask).toNat) = true) (hw : FrameKeep.storesTo (posI sy) R.prg R.prgMask R.pc = false) :
    PositionDispatch.Ordinary sy R := by
  have hoff : ∀ i ∈ posI sy, i < 256 ∨ 512 ≤ i := by
    intro i hi
    have := List.all_eq_true.1 hst i hi
    simpa [Bool.or_eq_true, decide_eq_true_eq] using this
  intro a ha hloc
  have hmem : FrameModel.I a ∈ posI sy := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [posI, List.mem_cons, List.not_mem_nil, or_false]
    rcases ha with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hstk : ∀ k s, FrameModel.I a ∉ StepWrites.stk s k := by
    intro k s hk
    have := stk_range k s _ hk
    rcases hoff _ hmem with h | h <;> omega
  unfold StepWrites.stepLocs at hloc
  split at hloc
  · exact hstk 3 _ hloc
  split at hloc
  · simp at hloc
  rw [fetchP hp] at hloc
  dsimp only at hloc
  generalize hop : R.prg.get! (R.pc &&& R.prgMask).toNat = op at hloc hplain
  simp only [plainOp, Bool.or_eq_true, List.contains_iff_mem] at hplain
  unfold FrameKeep.storesTo at hw
  rw [hop] at hw
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hw
  rcases hplain with (hq | hz) | ha'
  · revert hq hloc
    cases StepWrites.wOf op with
    | no => intro h _; simp [StepWrites.Wr.locs] at h
    | st k => intro h _; exact hstk k _ h
    | md c f => intro _ hq; simp [quietW] at hq
  · rw [wOf_zp op hz] at hloc
    simp only [StepWrites.Wr.locs] at hloc
    have e : go Smbrta.mZp { R with pc := R.pc + 1 } = go (fetch >>= fun b => pure b.toUInt16) { R with pc := R.pc + 1 } := rfl
    rw [e, PipeTransitionAll.go_bind, fetchP hp1] at hloc
    dsimp only at hloc
    rw [show (go (pure (R.prg.get! ((R.pc + 1) &&& R.prgMask).toNat).toUInt16 : M UInt16) { R with pc := R.pc + 1 + 1 }).1 =
      (R.prg.get! ((R.pc + 1) &&& R.prgMask).toNat).toUInt16 from rfl, zp_idx] at hloc
    simp only [List.mem_singleton] at hloc
    have hc := List.contains_iff_mem.2 hmem
    rw [hloc] at hc
    rcases hw.1 with h | h
    · rw [List.contains_iff_mem.2 hz] at h; cases h
    · rw [hc] at h; cases h
  · rw [wOf_abs op ha'] at hloc
    simp only [StepWrites.Wr.locs] at hloc
    have e : go Smbrta.mAbs { R with pc := R.pc + 1 } = go (fetch >>= fun lo => fetch >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) { R with pc := R.pc + 1 } := rfl
    rw [e, PipeTransitionAll.go_bind, fetchP hp1] at hloc
    dsimp only at hloc
    rw [PipeTransitionAll.go_bind, fetchP (m := { R with pc := R.pc + 1 + 1 }) hp2] at hloc
    dsimp only at hloc
    have e2 : R.pc + 1 + 1 = R.pc + 2 := by rw [UInt16.add_assoc]; rfl
    rw [e2] at hloc
    generalize hwd : (R.prg.get! ((R.pc + 1) &&& R.prgMask).toNat).toUInt16 ||| ((R.prg.get! ((R.pc + 2) &&& R.prgMask).toNat).toUInt16 <<< 8) = wd at hloc hw
    rw [show (go (pure wd : M UInt16) { R with pc := R.pc + 2 + 1 }).1 = wd from rfl] at hloc
    unfold StepWrites.ramIdx at hloc
    split at hloc
    · rename_i hlt
      simp only [List.mem_singleton] at hloc
      have hc := List.contains_iff_mem.2 hmem
      rw [hloc] at hc
      rcases hw.2 with h | h
      · rw [List.contains_iff_mem.2 ha'] at h; cases h
      · rcases h with h | h
        · rw [decide_eq_true hlt] at h; cases h
        · rw [hc] at h; cases h
    · simp at hloc

end

/-- **`Ready` at a plain instruction that is not one of `w` and not an entry**: from `AtW` and `ordinary_plain` -/
theorem ready_ordinary {sy : Syms} {m0 : Machine} {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) {s0 : UInt8} {R : Machine}
    (h : AtW sy m0 w s0 R) (hi : R.pc ≠ sy.ImpedePlayerMove) (hc : R.pc ≠ (ScreenClamp.places sy m0).entry) (hw : R.pc ∉ w)
    (hplain : plainOp (R.prg.get! (R.pc &&& R.prgMask).toNat) = true) : PositionDispatch.Ready sy m0 R := by
  obtain ⟨_, _, hst⟩ := wCheck_facts hh
  have hs : FrameKeep.storesTo (posI sy) R.prg R.prgMask R.pc = false := by
    cases e : FrameKeep.storesTo (posI sy) R.prg R.prgMask R.pc with
    | false => rfl
    | true => exact absurd (h.writes e) hw
  unfold PositionDispatch.Ready
  rw [if_neg hi, if_neg hc]
  exact ordinary_plain hst h.rom.1 h.rom.2.1 h.rom.2.2 hplain hs

/-! ## Every reached cut is `Ready`, from conditions on single instructions -/

/-- **The small check of the cover**: the scroll handler is not inside the two calls, and each instruction of `w` is inside them or one of `outside` -/
def wCover (sy : Syms) (m0 : Machine) (w : List UInt16) : Bool :=
  !innerP sy m0 sy.PlayerSubs && w.all fun p => innerP sy m0 p || (outside sy m0 w).contains p

section
variable {sy : Syms} {m0 : Machine}

theorem Reached.le {T : Nat → Machine} {q n : Nat} (h : PositionDispatch.Reached sy m0 T q n) : q ≤ n := by
  induction h with
  | start => exact Nat.le_refl _
  | next _ e ih => have := e.forward; omega

/-- **A reached cut is not inside the two calls**: the start is the scroll handler, an ordinary step from outside does not step into the inside (`FrameW.step`),
and both calls return outside it (`AtW.ret`) -/
theorem reached_outside {w : List UInt16} {s0 : UInt8} {T : Nat → Machine} {q b f : Nat} (hcv : wCover sy m0 w = true) (F : FrameW sy m0 w s0 T q f)
    (hq : (T q).pc = sy.PlayerSubs) (live : ∀ n, q ≤ n → n < b → (T n).frame = f) :
    ∀ n, PositionDispatch.Reached sy m0 T q n → n < b → innerP sy m0 (T n).pc = false := by
  have hs : innerP sy m0 sy.PlayerSubs = false := by
    simp only [wCover, Bool.and_eq_true, Bool.not_eq_true'] at hcv
    exact hcv.1
  intro n hr
  induction hr with
  | start => intro _; rw [hq]; exact hs
  | @next a c e ha edge ih =>
    intro hc
    have hac := edge.forward
    have hqa := Reached.le ha
    have ia := ih (by omega)
    cases edge with
    | ordinary ni nc _ _ =>
      cases hin : innerP sy m0 (T (a + 1)).pc with
      | false => rfl
      | true =>
        rcases F.step a hqa (live (a + 1) (by omega) hc) hin with h | h | h
        · rw [ia] at h; cases h
        · exact absurd h ni
        · exact absurd h nc
    | impede _ en ret _ _ =>
      rw [ret]
      exact (F.atW a hqa (live a hqa (by omega))).ret (Or.inl en)
    | clamp _ en ret _ _ =>
      rw [ret]
      exact (F.atW a hqa (live a hqa (by omega))).ret (Or.inr en)

/-- **`Ready` at every reached cut** of the frame from the scroll handler `q` to the frame's end `b`, from `FrameW` (`writers_end`) and four conditions on single
instructions of that part of the frame: none of the instructions `outside` runs; an instruction that is not plain (a store through an index or a pointer) does not
write the position (`Ordinary`); at the push's entry the position has its margins; at the clamp's entry `Y = 0` -/
theorem ready_all {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true) (hcv : wCover sy m0 w = true) {s0 : UInt8} {T : Nat → Machine} {q b f : Nat}
    (F : FrameW sy m0 w s0 T q f) (hq : (T q).pc = sy.PlayerSubs) (live : ∀ n, q ≤ n → n < b → (T n).frame = f)
    (hout : ∀ n, q ≤ n → n < b → (T n).pc ∉ outside sy m0 w)
    (hidx : ∀ n, q ≤ n → n < b → plainOp ((T n).prg.get! ((T n).pc &&& (T n).prgMask).toNat) = false → PositionDispatch.Ordinary sy (T n))
    (hmar : ∀ n, q ≤ n → n < b → (T n).pc = sy.ImpedePlayerMove → 256 ≤ posP sy (T n) ∧ posP sy (T n) + 256 < 0x1000000)
    (hy : ∀ n, q ≤ n → n < b → (T n).pc = (ScreenClamp.places sy m0).entry → (T n).y = 0) :
    ∀ n, q ≤ n → n < b → PositionDispatch.Reached sy m0 T q n → PositionDispatch.Ready sy m0 (T n) := by
  intro n hqn hnb hr
  have A := F.atW n hqn (live n hqn hnb)
  by_cases hi : (T n).pc = sy.ImpedePlayerMove
  · exact ready_impede A hi (hmar n hqn hnb hi).1 (hmar n hqn hnb hi).2
  by_cases hc : (T n).pc = (ScreenClamp.places sy m0).entry
  · exact ready_clamp hh A hc (hy n hqn hnb hc)
  have hin := reached_outside hcv F hq live n hr hnb
  have hw : (T n).pc ∉ w := by
    intro hm
    simp only [wCover, Bool.and_eq_true, List.all_eq_true] at hcv
    have h2 := hcv.2 _ hm
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h2
    rcases h2 with h2 | h2
    · rw [hin] at h2; cases h2
    · exact hout n hqn hnb h2
  cases hp : plainOp ((T n).prg.get! ((T n).pc &&& (T n).prgMask).toNat) with
  | true => exact ready_ordinary hh A hi hc hw hp
  | false =>
    unfold PositionDispatch.Ready
    rw [if_neg hi, if_neg hc]
    exact hidx n hqn hnb hp

end

section
open PipeEntryRule (trace)
variable {sy : Syms} {m0 : Machine}

/-- **The frame from the scroll handler to its end is a chain of ordinary steps, pushes and clamps whose effects add up** (`PositionDispatch.partition`), from
`FrameW` and the four conditions of `ready_all` on single instructions -/
theorem chain_of (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true)
    (hcv : wCover sy m0 w = true) {M : Machine} {input : UInt8} {q b : Nat} {s0 : UInt8}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (qb : q ≤ b) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : FrameW sy m0 w s0 (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hout : ∀ n, q ≤ n → n < b → (trace M input n).pc ∉ outside sy m0 w)
    (hidx : ∀ n, q ≤ n → n < b → plainOp ((trace M input n).prg.get! ((trace M input n).pc &&& (trace M input n).prgMask).toNat) = false →
      PositionDispatch.Ordinary sy (trace M input n))
    (hmar : ∀ n, q ≤ n → n < b → (trace M input n).pc = sy.ImpedePlayerMove → 256 ≤ posP sy (trace M input n) ∧ posP sy (trace M input n) + 256 < 0x1000000)
    (hy : ∀ n, q ≤ n → n < b → (trace M input n).pc = (ScreenClamp.places sy m0).entry → (trace M input n).y = 0) :
    ∃ es, PositionDispatch.Chain sy m0 (trace M input) q b es ∧ posP sy (trace M input b) = posP sy (trace M input q) + es.sum :=
  PositionDispatch.partition hi hcC idle time finish qb live (ready_all hh hcv F hq live hout hidx hmar hy)

end

/-! ## A frame that moves right at the scroll handler and keeps its speed -/

section
open PipeEntryRule (trace)
variable {sy : Syms} {m0 : Machine}

theorem chain_le {T : Nat → Machine} {a c : Nat} {es : List Int} (h : PositionDispatch.Chain sy m0 T a c es) : a ≤ c := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons e _ ih => have := e.forward; omega

/-- **The effects of a chain are all 0** when every machine of the frame from `q` on has the speed `s0 ≠ 0` (no push moves him, since a push that moves sets the
speed to 0: `ImpedePosition.routine_return`) and every clamp's target is its entry's position -/
theorem chain_zero (hi : ImpedePosition.check sy m0 = true) (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true)
    {w : List UInt16} {M : Machine} {input : UInt8} {q b : Nat} {s0 : UInt8}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame) (F : FrameW sy m0 w s0 (trace M input) q M.frame)
    (hall : ∀ j, q ≤ j → (trace M input j).frame = M.frame → peek (trace M input j) sy.Player_X_Speed = s0) (hnz : s0 ≠ 0)
    (hclamp : ∀ n, q ≤ n → n < b → (trace M input n).pc = (ScreenClamp.places sy m0).entry →
      ScreenClamp.target (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) (trace M input n) (trace M input n).y = posP sy (trace M input n)) :
    ∀ {a c : Nat} {es : List Int}, PositionDispatch.Chain sy m0 (trace M input) a c es → q ≤ a → c ≤ b → es.sum = 0 := by
  intro a c es ch
  induction ch with
  | nil => intro _ _; rfl
  | @cons a' b' c' e es' edge tail ih =>
    intro hqa hcb
    have hab := edge.forward
    have hbc : b' ≤ c' := chain_le tail
    have hrest := ih (by omega) hcb
    simp only [List.sum_cons, hrest, Int.add_zero]
    cases edge with
    | ordinary => rfl
    | impede _ en _ _ _ =>
      have la := live a' hqa (by omega)
      have g := (F.atW a' hqa la).good (Or.inl en)
      cases hp : ImpedePosition.pushes ((trace M input a').ram.get! (ImpedePosition.sites sy m0).side) (peek (trace M input a') sy.Player_X_Speed) with
      | false => simp [ImpedePosition.delta, hp]
      | true =>
        exfalso
        obtain ⟨k, _, _, _, _, vel, _, _, _, ifr⟩ := ImpedePosition.routine_return hi g en
        have eq := FrameModel.trace_inFrame idle la ifr time k (Nat.le_refl _)
        rw [hp, if_pos rfl] at vel
        rw [← eq.1] at vel
        have := hall (a' + k) (by omega) eq.2
        exact hnz (this.symm.trans vel)
    | clamp _ en _ _ _ =>
      have := hclamp a' hqa (by omega) en
      rw [this]
      omega

/-- **A frame that moves right at the scroll handler and ends with the same speed keeps the position** (the field `AfterP.keep`, here from conditions): from
`chain_of`'s conditions, `FrameW` (with its field `kept`), and at each clamp's entry the target is the position there -/
theorem keep_of (hi : ImpedePosition.check sy m0 = true) (hcC : ScreenClamp.check sy m0 = true)
    (idle : FrameModel.idleAt (FrameModel.Rom.of m0) sy.EndlessLoop = true) {v : UInt8} {w : List UInt16} (hh : wCheck sy m0 v w = true)
    (hcv : wCover sy m0 w = true) {M : Machine} {input : UInt8} {q b : Nat}
    (time : ∀ j, (trace M input j).pc ≠ sy.EndlessLoop → (trace M input j).fdot ≤ dotsPerFrame - 64)
    (finish : (trace M input b).frame = M.frame + 1) (qb : q ≤ b) (live : ∀ n, q ≤ n → n < b → (trace M input n).frame = M.frame)
    (F : FrameW sy m0 w (peek (trace M input q) sy.Player_X_Speed) (trace M input) q M.frame) (hq : (trace M input q).pc = sy.PlayerSubs)
    (hout : ∀ n, q ≤ n → n < b → (trace M input n).pc ∉ outside sy m0 w)
    (hidx : ∀ n, q ≤ n → n < b → plainOp ((trace M input n).prg.get! ((trace M input n).pc &&& (trace M input n).prgMask).toNat) = false →
      PositionDispatch.Ordinary sy (trace M input n))
    (hmar : ∀ n, q ≤ n → n < b → (trace M input n).pc = sy.ImpedePlayerMove → 256 ≤ posP sy (trace M input n) ∧ posP sy (trace M input n) + 256 < 0x1000000)
    (hy : ∀ n, q ≤ n → n < b → (trace M input n).pc = (ScreenClamp.places sy m0).entry → (trace M input n).y = 0)
    (hpos : 0 < sbyte (peek (trace M input q) sy.Player_X_Speed))
    (hsame : peek (trace M input b) sy.Player_X_Speed = peek (trace M input q) sy.Player_X_Speed)
    (hclamp : ∀ n, q ≤ n → n < b → (trace M input n).pc = (ScreenClamp.places sy m0).entry →
      ScreenClamp.target (FrameModel.Rom.of m0) (ScreenClamp.places sy m0) (trace M input n) (trace M input n).y = posP sy (trace M input n)) :
    posP sy (trace M input b) = posP sy (trace M input q) := by
  obtain ⟨es, ch, hsum⟩ := chain_of hi hcC idle hh hcv time finish qb live F hq hout hidx hmar hy
  have hnz : peek (trace M input q) sy.Player_X_Speed ≠ 0 := by
    intro e
    rw [e] at hpos
    have : sbyte (0 : UInt8) = 0 := by decide
    omega
  have hall := F.kept b finish hsame hnz
  have hz := chain_zero hi idle time live F hall hnz hclamp ch (Nat.le_refl _) (Nat.le_refl _)
  rw [hsum, hz]
  omega

end

end Smbrta.PositionWriters
