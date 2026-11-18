import Theorems.ImpedePosition

namespace Smbrta.ScreenClamp
open FrameModel ImpedePosition

/-- A stack-independent piece with a known Y register, kept at the end. -/
def startY (c : Cut) (y : UInt8) : TS := {start0 c with y := Tag.kn y y}
def goalY (c : Cut) (watch : List Nat) (y : UInt8) (Q : TS) : Bool := goal0 c watch Q && Q.y.same == some y
def pieceY (E : Rom) (c c' : Cut) (watch : List Nat) (y : UInt8) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (goalY c' watch y) fuel (startY c y)

theorem pieceY_spec {E : Rom} {c c' : Cut} {watch : List Nat} {y : UInt8} {fuel : Nat} {m : Machine}
    (hc : pieceY E c c' watch y fuel = true) (h : At E {c with s := m.s} m) (hy : m.y = y) :
    ∃ k, k ≤ fuel ∧ At E {c' with s := m.s} (stepN k m) ∧ (stepN k m).y = y ∧
      (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ InFrameN E m k := by
  have H := lk_start0 h
  have HY : Lk E m m (startY c y) m m := by
    refine ⟨H.gl,H.gr,H.pcl,H.pcr,⟨H.regs.a,H.regs.x,?_,H.regs.c,H.regs.z,H.regs.nf⟩,H.s,H.s0,H.ram,H.fixl,H.fixr⟩
    rw [hy]
    exact Tag.R_kn _ _
  obtain ⟨k,Q,hk,_,hg,H1,hh⟩ := walkT_spec fuel (startY c y) m m hc HY
  have hg0 : goal0 c' watch Q = true ∧ Q.y.same = some y := by simpa only [goalY,Bool.and_eq_true,beq_iff_eq] using hg
  have hg1 : Q.s.isNone = true ∧ goalC {c' with s := 0} watch {Q with s := some 0} = true := by
    simpa only [goal0,Bool.and_eq_true] using hg0.1
  have hn := Option.isNone_iff_eq_none.1 hg1.1
  have hs := H1.s0 hn
  have H2 : Lk E m m {Q with s := some m.s} (stepN k m) (stepN k m) := by
    refine ⟨H1.gl,H1.gr,H1.pcl,H1.pcr,⟨H1.regs.a,H1.regs.x,H1.regs.y,H1.regs.c,H1.regs.z,H1.regs.nf⟩,?_,?_,H1.ram,H1.fixl,H1.fixr⟩
    · intro v hv; have e := Option.some.inj hv; simpa only [← e] using hs
    · intro hv; cases hv
  have hg2 : goalC {c' with s := m.s} watch {Q with s := some m.s} = true := by
    simpa only [goalC,beq_self_eq_true] using hg1.2
  obtain ⟨ha,hw,_⟩ := at_of_goal hg2 H2
  exact ⟨k,hk,ha,(Tag.same_spec hg0.2 H1.regs.y).1,hw,
    fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩

structure Places where
  entry : UInt16
  pg : UInt16
  tail : UInt16
  ret : UInt16
  edgeX : UInt16
  edgeP : UInt16
  table : UInt16
  x : Nat
  page : Nat
  frac : Nat
  deriving Inhabited

/-- Decode the clamp reached from the scroll-handler call at PlayerSubs.
Every decoded cut and operand is validated by the piece checks. -/
def places (sy : Syms) (m0 : Machine) : Places :=
  let E := Rom.of m0
  let scroll := E.w (sy.PlayerSubs + 1)
  let entry := PipeEntryRule.findOp m0 scroll 0xB9 256
  let pg := PipeEntryRule.findOp m0 (entry + 1) 0xB9 32
  let tail := pg + 7
  { entry,pg,tail,ret := PipeEntryRule.findOp m0 tail 0x60 32,
    edgeX := E.w (entry+1),edgeP := E.w (pg+1),table := E.w (entry+5),
    x := I sy.Player_X_Position,page := I sy.Player_PageLoc,frac := I sy.SprObject_X_MoveForce }

def amount (E : Rom) (P : Places) (y : UInt8) : UInt8 := E.b (P.table+y.toUInt16)
def cX (P : Places) (y x : UInt8) : Cut :=
  {pc := P.entry,s := 0,K := [(I (P.edgeX+y.toUInt16),x)]}
def cP (E : Rom) (P : Places) (y x : UInt8) : Cut :=
  {pc := P.pg,s := 0,K := [(P.x,(adcC x (~~~ amount E P y) true).1)],cf := some (adcC x (~~~ amount E P y) true).2}
def cPage (P : Places) (y p : UInt8) (c : Bool) : Cut :=
  {pc := P.pg,s := 0,K := [(I (P.edgeP+y.toUInt16),p)],cf := some c}
def cTail (P : Places) (p : UInt8) (c : Bool) : Cut :=
  {pc := P.tail,s := 0,K := [(P.page,(adcC p 0xFF c).1)]}
def cT (P : Places) : Cut := {pc := P.tail,s := 0,K := []}
def cR (P : Places) : Cut := {pc := P.ret,s := 0,K := []}
def pixelCheck (E : Rom) (P : Places) (y x : UInt8) : Bool :=
  pieceY E (cX P y x) (cP E P y x) ([I (P.edgeP+y.toUInt16),P.page,P.frac] ++ stackI) y 12
def pageCheck (E : Rom) (P : Places) (y p : UInt8) (c : Bool) : Bool :=
  pieceY E (cPage P y p c) (cTail P p c) ([P.x,P.frac] ++ stackI) y 8
def tailCheck (E : Rom) (P : Places) (y : UInt8) : Bool :=
  pieceY E (cT P) (cR P) ([P.x,P.page,P.frac] ++ stackI) y 16

def returnCheck (E : Rom) (P : Places) : Bool := decide (0x8000 ≤ P.ret) && E.b P.ret == 0x60 && !idleAt E P.ret

def checkParts (E : Rom) (P : Places) : Bool :=
  [P.x,P.page,P.frac].all (fun i => decide (i < 2048)) &&
  ([0,(1 : UInt8)].all fun y =>
    (List.range 256).all (fun x => pixelCheck E P y x.toUInt8) &&
    (List.range 256).all (fun p => [false,true].all fun c => pageCheck E P y p.toUInt8 c) && tailCheck E P y) && returnCheck E P

def check (sy : Syms) (m0 : Machine) : Bool := checkParts (Rom.of m0) (places sy m0)

structure Facts (E : Rom) (P : Places) : Prop where
  x_lt : P.x < 2048
  page_lt : P.page < 2048
  frac_lt : P.frac < 2048
  pixel : ∀ y, y ∈ [0,(1 : UInt8)] → ∀ x, pixelCheck E P y x = true
  page : ∀ y, y ∈ [0,(1 : UInt8)] → ∀ p c, pageCheck E P y p c = true
  tail : ∀ y, y ∈ [0,(1 : UInt8)] → tailCheck E P y = true
  ret : 0x8000 ≤ P.ret ∧ lookupOp (E.b P.ret) insList = some .rts ∧ idleAt E P.ret = false

theorem facts_of_check {E : Rom} {P : Places} (h : checkParts E P = true) : Facts E P := by
  simp only [checkParts,Bool.and_eq_true] at h
  have hb : P.x < 2048 ∧ P.page < 2048 ∧ P.frac < 2048 := by simpa using h.1.1
  have HY := fun (y : UInt8) (hy : y ∈ [0,(1 : UInt8)]) => List.all_eq_true.1 h.1.2 y hy
  refine ⟨hb.1,hb.2.1,hb.2.2,?_,?_,?_,?_⟩
  · intro y hy x
    have H := HY y hy
    simp only [Bool.and_eq_true] at H
    have hx := H.1.1
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 hx x.toNat (List.mem_range.2 x.toNat_lt)
  · intro y hy p c
    have H := HY y hy
    simp only [Bool.and_eq_true] at H
    have hp := List.all_eq_true.1 H.1.2 p.toNat (List.mem_range.2 p.toNat_lt)
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 hp c (by cases c <;> simp)
  · intro y hy
    have H := HY y hy
    simp only [Bool.and_eq_true] at H
    exact H.2
  · have hr := h.2
    simp only [returnCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true'] at hr
    exact ⟨hr.1.1,by rw [hr.1.2]; exact lookup_rts,hr.2⟩

theorem complement_sum : ∀ n : Fin 256, (~~~ n.val.toUInt8).toNat + n.val = 255 := by decide +kernel

/-- Bytewise subtraction of the clamp amount, including the borrow into the page. -/
theorem sub_pos_mod (p x f d : UInt8) :
    (posOf (adcC p 0xFF (adcC x (~~~d) true).2).1 (adcC x (~~~d) true).1 f - posOf p x f + 256 * (d.toNat : Int)) % 0x1000000 = 0 := by
  have hl := adcC_nat x (~~~d) true
  have hp := adcC_nat p 0xFF (adcC x (~~~d) true).2
  have hd := complement_sum ⟨d.toNat,d.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at hd
  generalize hq : adcC x (~~~d) true = q at hl hp ⊢
  generalize hr : adcC p 0xFF q.2 = r at hp ⊢
  obtain ⟨qx,qc⟩ := q
  obtain ⟨rp,rc⟩ := r
  cases qc <;> cases rc <;> simp [posOf] at hl hp ⊢ <;> omega

/-- The edge coordinate minus the ROM-selected clamp amount, with the old fraction. -/
def target (E : Rom) (P : Places) (R : Machine) (y : UInt8) : Int :=
  posOf (peek R (P.edgeP+y.toUInt16)) (peek R (P.edgeX+y.toUInt16)) (R.ram.get! P.frac) - 256 * (amount E P y).toNat

/-- The clamp's real-machine position result. The only selector condition is Y=0 or Y=1. -/
theorem run {E : Rom} {P : Places} {R : Machine} {y : UInt8} (F : Facts E P)
    (hg : Good E R) (hpc : R.pc = P.entry) (hy : R.y = y) (hys : y ∈ [0,(1 : UInt8)]) :
    ∃ k, k ≤ 36 ∧ Good E (stepN k R) ∧ (stepN k R).pc = P.ret ∧ (stepN k R).s = R.s ∧
      (stepN k R).ram.get! P.frac = R.ram.get! P.frac ∧
      (posOf ((stepN k R).ram.get! P.page) ((stepN k R).ram.get! P.x) ((stepN k R).ram.get! P.frac) - target E P R y) % 0x1000000 = 0 ∧
      (∀ i ∈ stackI, (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN E R k := by
  let x := peek R (P.edgeX+y.toUInt16)
  let p := peek R (P.edgeP+y.toUInt16)
  let d := amount E P y
  have A0 : At E {cX P y x with s := R.s} R := by
    apply mkAt hg hpc
    · intro q hq; obtain rfl := List.mem_singleton.1 hq; rfl
    · intro u h; cases h
    · intro b h; cases h
  obtain ⟨k1,hk1,A1,y1,W1,C1⟩ := pieceY_spec (F.pixel y hys x) A0 hy
  generalize hR1 : stepN k1 R = R1 at A1 y1 W1
  have p1 : R1.ram.get! (I (P.edgeP+y.toUInt16)) = p := W1 _ (by simp) (I_lt _)
  have AP : At E {cPage P y p (adcC x (~~~d) true).2 with s := R1.s} R1 := by
    apply mkAt A1.good A1.pc
    · intro q hq; obtain rfl := List.mem_singleton.1 hq; exact p1
    · intro u h; cases h
    · exact A1.cf
  obtain ⟨k2,hk2,A2,y2,W2,C2⟩ := pieceY_spec (F.page y hys p _) AP y1
  generalize hR2 : stepN k2 R1 = R2 at A2 y2 W2
  have AT : At E {cT P with s := R2.s} R2 := by
    apply mkAt A2.good A2.pc <;> intro u h <;> cases h
  obtain ⟨k3,hk3,A3,_,W3,C3⟩ := pieceY_spec (F.tail y hys) AT y2
  have px : (stepN k3 R2).ram.get! P.x = (adcC x (~~~d) true).1 :=
    (W3 _ (by simp) F.x_lt).trans ((W2 _ (by simp) F.x_lt).trans (A1.K _ (.head _)))
  have pg : (stepN k3 R2).ram.get! P.page = (adcC p 0xFF (adcC x (~~~d) true).2).1 :=
    (W3 _ (by simp) F.page_lt).trans (A2.K _ (.head _))
  have pf : (stepN k3 R2).ram.get! P.frac = R.ram.get! P.frac :=
    (W3 _ (by simp) F.frac_lt).trans ((W2 _ (by simp) F.frac_lt).trans (W1 _ (by simp) F.frac_lt))
  refine ⟨k1+(k2+k3),by omega,?_⟩
  have eq : stepN (k1+(k2+k3)) R = stepN k3 R2 := by rw [stepN_add,hR1,stepN_add,hR2]
  rw [eq]
  refine ⟨A3.good,A3.pc,A3.s.trans (A2.s.trans A1.s),pf,?_,?_,InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 C3)⟩
  · rw [px,pg,pf]
    let A := posOf (adcC p 0xFF (adcC x (~~~d) true).2).1 (adcC x (~~~d) true).1 (R.ram.get! P.frac)
    let B := posOf p x (R.ram.get! P.frac)
    change (A - (B - 256 * (d.toNat : Int))) % 0x1000000 = 0
    have eq : A - (B - 256 * (d.toNat : Int)) = A - B + 256 * (d.toNat : Int) := by omega
    rw [eq]
    exact sub_pos_mod p x (R.ram.get! P.frac) d
  · intro i hi
    have hb := stack_bound hi
    exact (W3 i (List.mem_append_right _ hi) hb).trans ((W2 i (List.mem_append_right _ hi) hb).trans (W1 i (List.mem_append_right _ hi) hb))

/-- If the one-state target is within the position range, the modular clamp is exact. -/
theorem exact_target {sy : Syms} {Q : Machine} {t : Int} (ht : 0 ≤ t ∧ t < 0x1000000)
    (hm : (posP sy Q - t) % 0x1000000 = 0) : posP sy Q = t := by
  have hb := ImpedePosition.pos_range sy Q
  omega

/-- The screen clamp on actual player coordinates, before its return instruction. -/
theorem clamp {sy : Syms} {m0 R : Machine} (hc : check sy m0 = true)
    (hg : Good (Rom.of m0) R) (hpc : R.pc = (places sy m0).entry) (hy : R.y ∈ [0,(1 : UInt8)]) :
    ∃ k, k ≤ 36 ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = (places sy m0).ret ∧
      (stepN k R).s = R.s ∧ peek (stepN k R) sy.SprObject_X_MoveForce = peek R sy.SprObject_X_MoveForce ∧
      (posP sy (stepN k R) - target (Rom.of m0) (places sy m0) R R.y) % 0x1000000 = 0 ∧
      (∀ i ∈ stackI, (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN (Rom.of m0) R k := by
  exact run (facts_of_check hc) hg hpc rfl hy

/-- The complete clamp and RTS to the original caller. The target-range condition
is needed only to turn the modular conclusion into an exact coordinate. -/
theorem clamp_return {sy : Syms} {m0 R : Machine} (hc : check sy m0 = true)
    (hg : Good (Rom.of m0) R) (hpc : R.pc = (places sy m0).entry) (hy : R.y ∈ [0,(1 : UInt8)]) :
    ∃ k, k ≤ 37 ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = returnPc R ∧ (stepN k R).s = R.s+1+1 ∧
      peek (stepN k R) sy.SprObject_X_MoveForce = peek R sy.SprObject_X_MoveForce ∧
      (posP sy (stepN k R) - target (Rom.of m0) (places sy m0) R R.y) % 0x1000000 = 0 ∧ InFrameN (Rom.of m0) R k := by
  obtain ⟨k,hk,g,pc,sp,f,hm,stk,ih⟩ := clamp hc hg hpc hy
  have F := facts_of_check hc
  have hr1 : 0x8000 ≤ (stepN k R).pc := by rw [pc]; exact F.ret.1
  have hr2 : lookupOp ((Rom.of m0).b (stepN k R).pc) insList = some .rts := by rw [pc]; exact F.ret.2.1
  have hr3 : idleAt (Rom.of m0) (stepN k R).pc = false := by rw [pc]; exact F.ret.2.2
  obtain ⟨rp,rs,rm,rg⟩ := step_rts g hr1 hr2 hr3
  rw [← stepN_one] at rp rs rm rg
  have rpc : (stepN 1 (stepN k R)).pc = returnPc R := by
    rw [rp,sp,stk _ (stack_mem _),stk _ (stack_mem _)]
    rfl
  have wp : ∀ a, peek (stepN 1 (stepN k R)) a = peek (stepN k R) a := by
    intro a; unfold peek; rw [rm]
  have pe : posP sy (stepN 1 (stepN k R)) = posP sy (stepN k R) := by
    unfold posP; rw [wp,wp,wp]
  have ic : InFrameN (Rom.of m0) (stepN k R) 1 := by
    intro j hj
    have e : j=0 := by omega
    subst j
    exact inFrame_rts g hr1 hr2 hr3
  refine ⟨k+1,by omega,?_⟩
  rw [stepN_add]
  exact ⟨rg,rpc,by rw [rs,sp],(wp _).trans f,by rw [pe]; exact hm,InFrameN.add' ih rfl ic⟩

end Smbrta.ScreenClamp
