import Theorems.FrameModel
import Theorems.CollKeep
import Theorems.StepWrites

namespace Smbrta.ImpedePosition
open FrameModel

/-- A checked piece that leaves the actual stack byte arbitrary and unchanged. -/
def start0 (c : Cut) : TS := { startQ c with s := none }
def goal0 (c : Cut) (watch : List Nat) (Q : TS) : Bool :=
  Q.s.isNone && goalC {c with s := 0} watch {Q with s := some 0}
def piece0 (E : Rom) (c c' : Cut) (watch : List Nat) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (goal0 c' watch) fuel (start0 c)

theorem lk_start0 {E : Rom} {c : Cut} {m : Machine} (h : At E {c with s := m.s} m) :
    Lk E m m (start0 c) m m := by
  have H := lk_self h
  refine ⟨H.gl, H.gr, H.pcl, H.pcr, ⟨H.regs.a, H.regs.x, H.regs.y, H.regs.c, H.regs.z, H.regs.nf⟩, ?_, ?_, H.ram, H.fixl, H.fixr⟩
  · intro v hv; cases hv
  · intro _; exact ⟨rfl, rfl⟩

theorem piece0_spec {E : Rom} {c c' : Cut} {watch : List Nat} {fuel : Nat} {m : Machine}
    (hc : piece0 E c c' watch fuel = true) (h : At E {c with s := m.s} m) :
    ∃ k, k ≤ fuel ∧ At E {c' with s := m.s} (stepN k m) ∧
      (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ InFrameN E m k := by
  obtain ⟨k, Q, hk, _, hg, H, hh⟩ := walkT_spec fuel (start0 c) m m hc (lk_start0 h)
  have hg0 : Q.s.isNone = true ∧ goalC {c' with s := 0} watch {Q with s := some 0} = true := by
    simpa only [goal0, Bool.and_eq_true] using hg
  have hn : Q.s = none := by
    have h1 := hg0.1
    exact Option.isNone_iff_eq_none.1 h1
  have hs := H.s0 hn
  have H' : Lk E m m {Q with s := some m.s} (stepN k m) (stepN k m) := by
    refine ⟨H.gl, H.gr, H.pcl, H.pcr, ⟨H.regs.a, H.regs.x, H.regs.y, H.regs.c, H.regs.z, H.regs.nf⟩, ?_, ?_, H.ram, H.fixl, H.fixr⟩
    · intro v hv
      have e := Option.some.inj hv
      simpa only [← e] using hs
    · intro hv; cases hv
  have hg' : goalC {c' with s := m.s} watch {Q with s := some m.s} = true := by
    have h1 := hg0.2
    simpa only [goalC, beq_self_eq_true] using h1
  obtain ⟨ha, hw, _⟩ := at_of_goal hg' H'
  exact ⟨k, hk, ha, hw, fun j hj => by obtain ⟨_, _, _, _, hi, _⟩ := hh j hj; exact hi⟩

structure Sites where
  entry : UInt16
  pix : UInt16
  pg : UInt16
  tail : UInt16
  ret : UInt16
  side : Nat
  temp : Nat
  speed : Nat
  x : Nat
  page : Nat
  frac : Nat
  sub : Nat
  deriving Inhabited

def sites (sy : Syms) (m0 : Machine) : Sites :=
  let E := Rom.of m0
  let pix := findPat E sy.ImpedePlayerMove [0x65, sy.Player_X_Position.toUInt8] 96
  let pg := findPat E sy.ImpedePlayerMove [0xA5, sy.Player_PageLoc.toUInt8] 96
  let tail := PipeEntryRule.findOp m0 sy.ImpedePlayerMove 0x8A 96
  { entry := sy.ImpedePlayerMove, pix, pg, tail, ret := PipeEntryRule.findOp m0 tail 0x60 32,
    side := (romByte m0 (CollKeep.splitPc sy m0 - 1)).toNat,
    temp := (romByte m0 (pg + 3)).toNat,
    speed := I sy.Player_X_Speed, x := I sy.Player_X_Position, page := I sy.Player_PageLoc,
    frac := I sy.SprObject_X_MoveForce, sub := I sy.Player_X_MoveForce }

def pushes (side v : UInt8) : Bool := if side == 1 then v &&& 0x80 == 0 else (v - 1) &&& 0x80 != 0
def low (side : UInt8) : UInt8 := if side == 1 then 0xFF else 1
def high (side : UInt8) : UInt8 := if side == 1 then 0xFF else 0
def delta (side v : UInt8) : Int := if pushes side v then (if side == 1 then -1 else 1) else 0

def posWatch (D : Sites) : List Nat := [D.x, D.page, D.frac, D.sub]
def c0 (D : Sites) (side v : UInt8) : Cut :=
  { pc := D.entry, s := 0, K := [(D.side, side), (D.speed, v)] }
def c1 (D : Sites) (side v : UInt8) : Cut :=
  if pushes side v then
    { pc := D.pix, s := 0, K := [(D.speed, 0), (D.temp, high side)], ra := some (low side), cf := some false }
  else { pc := D.tail, s := 0, K := [(D.speed, v)] }
def cx (D : Sites) (x d : UInt8) : Cut :=
  { pc := D.pix, s := 0, K := [(D.x, x)], ra := some d, cf := some false }
def cy (D : Sites) (x d : UInt8) : Cut :=
  { pc := D.pg, s := 0, K := [(D.x, (adcC d x false).1)], cf := some (adcC d x false).2 }
def cp (D : Sites) (p e : UInt8) (c : Bool) : Cut :=
  { pc := D.pg, s := 0, K := [(D.page, p), (D.temp, e)], cf := some c }
def cq (D : Sites) (p e : UInt8) (c : Bool) : Cut :=
  { pc := D.tail, s := 0, K := [(D.page, (adcC p e c).1)] }
def ct (D : Sites) : Cut := {pc := D.tail, s := 0, K := []}
def cr (D : Sites) : Cut := {pc := D.ret, s := 0, K := []}

/-- The 6502 stack addresses, independent of the current stack byte. -/
def stackI : List Nat := (List.range 256).map fun n => stkI n.toUInt8

theorem stack_mem (s : UInt8) : stkI s ∈ stackI := by
  apply List.mem_map.2
  exact ⟨s.toNat,List.mem_range.2 s.toNat_lt,by simp⟩

theorem stack_bound {i : Nat} (h : i ∈ stackI) : i < 2048 := by
  obtain ⟨n,_,rfl⟩ := List.mem_map.1 h
  exact mask_stk _

def prefixCheck (E : Rom) (D : Sites) (side v : UInt8) : Bool := piece0 E (c0 D side v) (c1 D side v) (posWatch D ++ stackI) 40
def pixelCheck (E : Rom) (D : Sites) (x d : UInt8) : Bool :=
  piece0 E (cx D x d) (cy D x d) ([D.page,D.temp,D.speed,D.frac,D.sub] ++ stackI) 8
def pageCheck (E : Rom) (D : Sites) (p e : UInt8) (c : Bool) : Bool :=
  piece0 E (cp D p e c) (cq D p e c) ([D.x,D.speed,D.frac,D.sub] ++ stackI) 8
def tailCheck (E : Rom) (D : Sites) : Bool := piece0 E (ct D) (cr D) ((D.speed :: posWatch D) ++ stackI) 8

/-- Separate the pixel, page, speed and side rather than enumerate their Cartesian product. -/
def returnCheck (E : Rom) (D : Sites) : Bool := decide (0x8000 ≤ D.ret) && E.b D.ret == 0x60 && !idleAt E D.ret

def indices (D : Sites) : List Nat := [D.side,D.temp,D.speed,D.x,D.page,D.frac,D.sub]

def checkParts (E : Rom) (D : Sites) : Bool :=
  (indices D).all (fun i => decide (i < 2048)) &&
  (List.range 256).all (fun side => (List.range 256).all fun v => prefixCheck E D side.toUInt8 v.toUInt8) &&
  (List.range 256).all (fun x => [1, (0xFF : UInt8)].all fun d => pixelCheck E D x.toUInt8 d) &&
  (List.range 256).all (fun p => [0, (0xFF : UInt8)].all fun e => [false,true].all fun c => pageCheck E D p.toUInt8 e c) &&
  tailCheck E D && returnCheck E D

def check (sy : Syms) (m0 : Machine) : Bool := checkParts (Rom.of m0) (sites sy m0)

structure Facts (E : Rom) (D : Sites) : Prop where
  bound : ∀ i ∈ indices D, i < 2048
  pre : ∀ side v, prefixCheck E D side v = true
  pixel : ∀ x d, d ∈ [1, (0xFF : UInt8)] → pixelCheck E D x d = true
  page : ∀ p e, e ∈ [0, (0xFF : UInt8)] → ∀ c, pageCheck E D p e c = true
  tail : tailCheck E D = true
  ret : 0x8000 ≤ D.ret ∧ lookupOp (E.b D.ret) insList = some .rts ∧ idleAt E D.ret = false

theorem facts_of_check {E : Rom} {D : Sites} (h : checkParts E D = true) : Facts E D := by
  simp only [checkParts, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hb,hpre⟩,hx⟩,hp⟩,ht⟩,hr⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ht, ?_⟩
  · intro i hi; exact of_decide_eq_true (List.all_eq_true.1 hb i hi)
  · intro side v
    have hs := List.all_eq_true.1 hpre side.toNat (List.mem_range.2 side.toNat_lt)
    have hv := List.all_eq_true.1 hs v.toNat (List.mem_range.2 v.toNat_lt)
    simpa only [UInt8.ofNat_toNat] using hv
  · intro x d hd
    have hh := List.all_eq_true.1 hx x.toNat (List.mem_range.2 x.toNat_lt)
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 hh d hd
  · intro p e he c
    have hh := List.all_eq_true.1 hp p.toNat (List.mem_range.2 p.toNat_lt)
    have hh' := List.all_eq_true.1 hh e he
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 hh' c (by cases c <;> simp)
  · simp only [returnCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true'] at hr
    exact ⟨hr.1.1,by rw [hr.1.2]; exact lookup_rts,hr.2⟩

theorem mkAt {E : Rom} {R : Machine} {pc : UInt16} {K : List (Nat × UInt8)} {ra : Option UInt8} {cf : Option Bool}
    (hg : Good E R) (hp : R.pc = pc) (hk : ∀ q ∈ K, R.ram.get! q.1 = q.2)
    (ha : ∀ v, ra = some v → R.a = v) (hc : ∀ b, cf = some b → TaintRun.bt R.p 0 = b) :
    At E {pc, s := R.s, K, ra, cf} R :=
  ⟨hg, hp, rfl, hk, (fun _ h => by cases h), ha, (fun _ h => by cases h), hc⟩

/-- Byte-level contract of the whole routine, for every initial stack byte and all
side/speed/position bytes. The cut is before RTS, so the caller's return address is untouched. -/
theorem run_bytes {E : Rom} {D : Sites} {R : Machine} (F : Facts E D) (hg : Good E R) (hpc : R.pc = D.entry) :
    ∃ k, k ≤ 64 ∧ Good E (stepN k R) ∧ (stepN k R).pc = D.ret ∧ (stepN k R).s = R.s ∧
      (stepN k R).ram.get! D.speed = (if pushes (R.ram.get! D.side) (R.ram.get! D.speed) then 0 else R.ram.get! D.speed) ∧
      (stepN k R).ram.get! D.frac = R.ram.get! D.frac ∧ (stepN k R).ram.get! D.sub = R.ram.get! D.sub ∧
      (stepN k R).ram.get! D.x = (if pushes (R.ram.get! D.side) (R.ram.get! D.speed) then
        (adcC (low (R.ram.get! D.side)) (R.ram.get! D.x) false).1 else R.ram.get! D.x) ∧
      (stepN k R).ram.get! D.page = (if pushes (R.ram.get! D.side) (R.ram.get! D.speed) then
        (adcC (R.ram.get! D.page) (high (R.ram.get! D.side)) (adcC (low (R.ram.get! D.side)) (R.ram.get! D.x) false).2).1 else R.ram.get! D.page) ∧
      (∀ i ∈ stackI, (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN E R k := by
  let side := R.ram.get! D.side
  let v := R.ram.get! D.speed
  let x := R.ram.get! D.x
  let p := R.ram.get! D.page
  have hs := F.bound D.speed (by simp [indices])
  have hx := F.bound D.x (by simp [indices])
  have hp := F.bound D.page (by simp [indices])
  have hf := F.bound D.frac (by simp [indices])
  have hu := F.bound D.sub (by simp [indices])
  have hz := F.bound D.temp (by simp [indices])
  have A0 : At E {c0 D side v with s := R.s} R := by
    apply mkAt hg hpc
    · intro q hq
      simp only [c0, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · intro u h; cases h
    · intro b h; cases h
  obtain ⟨k1, hk1, A1, W1, C1⟩ := piece0_spec (F.pre side v) A0
  generalize hR1 : stepN k1 R = R1 at A1 W1
  have w1 : ∀ i ∈ posWatch D, R1.ram.get! i = R.ram.get! i := by
    intro i hi
    apply W1 i (List.mem_append_left _ hi)
    simp only [posWatch, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  by_cases hpush : pushes side v = true
  · have hP : pushes (R.ram.get! D.side) (R.ram.get! D.speed) = true := hpush
    have A1' := A1
    simp only [c1, hpush, if_true] at A1'
    have sp1 : R1.ram.get! D.speed = 0 := A1'.K _ (.head _)
    have tmp1 : R1.ram.get! D.temp = high side := A1'.K _ (.tail _ (.head _))
    have AX : At E {cx D x (low side) with s := R1.s} R1 := by
      apply mkAt A1'.good A1'.pc
      · intro q hq; obtain rfl := List.mem_singleton.1 hq
        exact w1 _ (by simp [posWatch])
      · exact A1'.ra
      · exact A1'.cf
    obtain ⟨k2, hk2, A2, W2, C2⟩ := piece0_spec (F.pixel x (low side) (by by_cases h : side == 1 <;> simp [low,h])) AX
    generalize hR2 : stepN k2 R1 = R2 at A2 W2
    have x2 : R2.ram.get! D.x = (adcC (low side) x false).1 := A2.K _ (.head _)
    have pg2 : R2.ram.get! D.page = p := (W2 _ (by simp) hp).trans (w1 _ (by simp [posWatch]))
    have tmp2 : R2.ram.get! D.temp = high side := (W2 _ (by simp) hz).trans tmp1
    have sp2 : R2.ram.get! D.speed = 0 := (W2 _ (by simp) hs).trans sp1
    have AP : At E {cp D p (high side) (adcC (low side) x false).2 with s := R2.s} R2 := by
      apply mkAt A2.good A2.pc
      · intro q hq
        simp only [cp,List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl | rfl
        · exact pg2
        · exact tmp2
      · intro u h; cases h
      · exact A2.cf
    obtain ⟨k3, hk3, A3, W3, C3⟩ := piece0_spec (F.page p (high side) (by by_cases h : side == 1 <;> simp [high,h]) _) AP
    generalize hR3 : stepN k3 R2 = R3 at A3 W3
    have pg3 : R3.ram.get! D.page = (adcC p (high side) (adcC (low side) x false).2).1 := A3.K _ (.head _)
    have x3 : R3.ram.get! D.x = (adcC (low side) x false).1 := (W3 _ (by simp) hx).trans x2
    have sp3 : R3.ram.get! D.speed = 0 := (W3 _ (by simp) hs).trans sp2
    have AT : At E {ct D with s := R3.s} R3 := by
      apply mkAt A3.good A3.pc <;> intro u h <;> cases h
    obtain ⟨k4, hk4, A4, W4, C4⟩ := piece0_spec F.tail AT
    refine ⟨k1+(k2+(k3+k4)), by omega, ?_⟩
    have eq : stepN (k1+(k2+(k3+k4))) R = stepN k4 R3 := by
      rw [stepN_add, hR1, stepN_add, hR2, stepN_add, hR3]
    rw [eq]
    refine ⟨A4.good,A4.pc,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact A4.s.trans (A3.s.trans (A2.s.trans A1'.s))
    · simpa only [hP,side,v,x,p,if_true] using (W4 _ (by simp [posWatch]) hs).trans sp3
    · exact (W4 _ (by simp [posWatch]) hf).trans ((W3 _ (by simp) hf).trans ((W2 _ (by simp) hf).trans (w1 _ (by simp [posWatch]))))
    · exact (W4 _ (by simp [posWatch]) hu).trans ((W3 _ (by simp) hu).trans ((W2 _ (by simp) hu).trans (w1 _ (by simp [posWatch]))))
    · simpa only [hP,side,v,x,p,if_true] using (W4 _ (by simp [posWatch]) hx).trans x3
    · simpa only [hP,side,v,x,p,if_true] using (W4 _ (by simp [posWatch]) hp).trans pg3
    · intro i hi
      have hb := stack_bound hi
      exact (W4 i (List.mem_append_right _ hi) hb).trans ((W3 i (List.mem_append_right _ hi) hb).trans
        ((W2 i (List.mem_append_right _ hi) hb).trans (W1 i (List.mem_append_right _ hi) hb)))
    · exact InFrameN.add' C1 hR1 (InFrameN.add' C2 hR2 (InFrameN.add' C3 hR3 C4))
  · have hfalse : pushes side v = false := Bool.eq_false_iff.2 hpush
    have hF : pushes (R.ram.get! D.side) (R.ram.get! D.speed) = false := hfalse
    have A1' := A1
    simp only [c1,hfalse,Bool.false_eq_true,if_false] at A1'
    have AT : At E {ct D with s := R1.s} R1 := by
      apply mkAt A1'.good A1'.pc <;> intro u h <;> cases h
    obtain ⟨k2,hk2,A2,W2,C2⟩ := piece0_spec F.tail AT
    refine ⟨k1+k2,by omega,?_⟩
    have eq : stepN (k1+k2) R = stepN k2 R1 := by rw [stepN_add,hR1]
    rw [eq]
    refine ⟨A2.good,A2.pc,A2.s.trans A1'.s,?_,?_,?_,?_,?_,?_,InFrameN.add' C1 hR1 C2⟩
    · simpa only [hF,side,v,x,p,Bool.false_eq_true,if_false] using (W2 _ (by simp [posWatch]) hs).trans (A1'.K _ (.head _))
    · exact (W2 _ (by simp [posWatch]) hf).trans (w1 _ (by simp [posWatch]))
    · exact (W2 _ (by simp [posWatch]) hu).trans (w1 _ (by simp [posWatch]))
    · simpa only [hF,side,v,x,p,Bool.false_eq_true,if_false] using (W2 _ (by simp [posWatch]) hx).trans (w1 _ (by simp [posWatch]))
    · simpa only [hF,side,v,x,p,Bool.false_eq_true,if_false] using (W2 _ (by simp [posWatch]) hp).trans (w1 _ (by simp [posWatch]))
    · intro i hi
      have hb := stack_bound hi
      exact (W2 i (List.mem_append_right _ hi) hb).trans (W1 i (List.mem_append_right _ hi) hb)

/-- The two byte additions are a one-pixel signed displacement, modulo the position cycle. -/
theorem adc_pos_mod (side p x f : UInt8) :
    (posOf (adcC p (high side) (adcC (low side) x false).2).1 (adcC (low side) x false).1 f - posOf p x f -
      256 * (if side == 1 then (-1 : Int) else 1)) % 0x1000000 = 0 := by
  have hl := adcC_nat (low side) x false
  have hp := adcC_nat p (high side) (adcC (low side) x false).2
  generalize hq : adcC (low side) x false = q at hl hp ⊢
  generalize hr : adcC p (high side) q.2 = r at hp ⊢
  obtain ⟨qx,qc⟩ := q
  obtain ⟨rp,rc⟩ := r
  cases qc <;> cases rc <;> by_cases hs : side == 1 <;>
    simp [posOf,low,high,hs] at hl hp ⊢ <;> omega

theorem sign_sub_one : ∀ n : Fin 256,
    (((n.val.toUInt8 - 1) &&& 0x80) != 0) = decide (n.val = 0 ∨ 129 ≤ n.val) := by decide +kernel

/-- Positive displacement can only occur from a nonpositive signed speed. -/
theorem positive_only {side v : UInt8} (h : 0 < delta side v) : sbyte v ≤ 0 := by
  by_cases hs : side == 1
  · simp [delta,hs] at h
    split at h <;> omega
  · simp only [delta,hs,Bool.false_eq_true,if_false] at h
    split at h
    · rename_i hp
      have hv : (v - 1) &&& 0x80 != 0 := by simpa [pushes,hs] using hp
      change (if v.toNat < 128 then (v.toNat : Int) else (v.toNat : Int) - 256) ≤ 0
      have hb := v.toNat_lt
      have he := sign_sub_one ⟨v.toNat,v.toNat_lt⟩
      simp only [UInt8.ofNat_toNat] at he
      rw [he] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hv | hv <;> split <;> omega
    · omega

/-- The whole routine's signed position relation, on the actual machine. -/
theorem routine {sy : Syms} {m0 R : Machine} (hc : check sy m0 = true)
    (hg : Good (Rom.of m0) R) (hpc : R.pc = sy.ImpedePlayerMove) :
    ∃ k, k ≤ 64 ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = (sites sy m0).ret ∧
      (stepN k R).s = R.s ∧
      peek (stepN k R) sy.Player_X_Speed = (if pushes (R.ram.get! (sites sy m0).side) (peek R sy.Player_X_Speed) then 0 else peek R sy.Player_X_Speed) ∧
      peek (stepN k R) sy.SprObject_X_MoveForce = peek R sy.SprObject_X_MoveForce ∧
      peek (stepN k R) sy.Player_X_MoveForce = peek R sy.Player_X_MoveForce ∧
      (posP sy (stepN k R) - posP sy R - 256 * delta (R.ram.get! (sites sy m0).side) (peek R sy.Player_X_Speed)) % 0x1000000 = 0 ∧
      (∀ i ∈ stackI, (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN (Rom.of m0) R k := by
  obtain ⟨k,hk,g,pc,sp,vel,f,u,x,p,stk,ih⟩ := run_bytes (facts_of_check hc) hg hpc
  refine ⟨k,hk,g,pc,sp,vel,f,u,?_,stk,ih⟩
  rw [posP_eq,posP_eq]
  change (posOf ((stepN k R).ram.get! (sites sy m0).page) ((stepN k R).ram.get! (sites sy m0).x)
    ((stepN k R).ram.get! (sites sy m0).frac) -
    posOf (R.ram.get! (sites sy m0).page) (R.ram.get! (sites sy m0).x) (R.ram.get! (sites sy m0).frac) -
    256 * delta (R.ram.get! (sites sy m0).side) (R.ram.get! (sites sy m0).speed)) % 0x1000000 = 0
  rw [f,x,p]
  by_cases h : pushes (R.ram.get! (sites sy m0).side) (R.ram.get! (sites sy m0).speed) = true
  · simpa only [delta,h,if_true] using adc_pos_mod (R.ram.get! (sites sy m0).side) (R.ram.get! (sites sy m0).page)
      (R.ram.get! (sites sy m0).x) (R.ram.get! (sites sy m0).frac)
  · have hf : pushes (R.ram.get! (sites sy m0).side) (R.ram.get! (sites sy m0).speed) = false := Bool.eq_false_iff.2 h
    simp [hf,delta]

theorem delta_bounds (side v : UInt8) : -1 ≤ delta side v ∧ delta side v ≤ 1 := by
  unfold delta
  split
  · split <;> omega
  · omega

theorem pos_range (sy : Syms) (R : Machine) : 0 ≤ posP sy R ∧ posP sy R < 0x1000000 := by
  rw [posP_eq]
  unfold posOf
  have h1 := (peek R sy.Player_PageLoc).toNat_lt
  have h2 := (peek R sy.Player_X_Position).toNat_lt
  have h3 := (peek R sy.SprObject_X_MoveForce).toNat_lt
  omega

/-- Away from position wrap, the modular relation is exact. -/
theorem exact_of_mod {sy : Syms} {R Q : Machine} {side v : UInt8}
    (hl : 256 ≤ posP sy R) (hr : posP sy R + 256 < 0x1000000)
    (hm : (posP sy Q - posP sy R - 256 * delta side v) % 0x1000000 = 0) :
    posP sy Q = posP sy R + 256 * delta side v := by
  have hb := delta_bounds side v
  have hq := pos_range sy Q
  omega

/-- For a positive entry speed, an exact local call either keeps position with
that speed, or stops exactly one pixel to the left. -/
theorem positive_effect {sy : Syms} {R B : Machine} {side : UInt8}
    (hv : 0 < sbyte (peek R sy.Player_X_Speed))
    (hs : peek B sy.Player_X_Speed =
      if pushes side (peek R sy.Player_X_Speed) then 0 else peek R sy.Player_X_Speed)
    (hp : posP sy B = posP sy R + 256 * delta side (peek R sy.Player_X_Speed)) :
    (peek B sy.Player_X_Speed = peek R sy.Player_X_Speed → posP sy B = posP sy R) ∧
    (peek B sy.Player_X_Speed = 0 → posP sy B = posP sy R - 256) := by
  have nz : peek R sy.Player_X_Speed ≠ 0 := by
    intro e
    rw [e] at hv
    have : sbyte (0 : UInt8) = 0 := by decide
    omega
  by_cases h : pushes side (peek R sy.Player_X_Speed) = true
  · have hs0 : peek B sy.Player_X_Speed = 0 := by simpa [h] using hs
    have hd : delta side (peek R sy.Player_X_Speed) = -1 := by
      have hn : ¬ 0 < delta side (peek R sy.Player_X_Speed) := by
        intro hpos
        have := positive_only hpos
        omega
      by_cases he : side == 1
      · simp [delta,h,he]
      · have hd : delta side (peek R sy.Player_X_Speed) = 1 := by simp [delta,h,he]
        omega
    rw [hd] at hp
    exact ⟨fun e => False.elim (nz (e.symm.trans hs0)),fun _ => by omega⟩
  · have hf : pushes side (peek R sy.Player_X_Speed) = false := Bool.eq_false_iff.2 h
    have hs1 : peek B sy.Player_X_Speed = peek R sy.Player_X_Speed := by simpa [hf] using hs
    have hd : delta side (peek R sy.Player_X_Speed) = 0 := by simp [delta,hf]
    rw [hd] at hp
    exact ⟨fun _ => by omega,fun e => False.elim (nz (hs1.symm.trans e))⟩

/-- The 6502 return destination from the caller's original stack bytes. -/
def returnPc (R : Machine) : UInt16 :=
  ((R.ram.get! (stkI (R.s + 1))).toUInt16 ||| ((R.ram.get! (stkI (R.s + 1 + 1))).toUInt16 <<< 8)) + 1

/-- The complete routine, including RTS to the caller. No condition on the original
stack byte, flags, side byte or speed byte is omitted. -/
theorem routine_return {sy : Syms} {m0 R : Machine} (hc : check sy m0 = true)
    (hg : Good (Rom.of m0) R) (hpc : R.pc = sy.ImpedePlayerMove) :
    ∃ k, k ≤ 65 ∧ Good (Rom.of m0) (stepN k R) ∧ (stepN k R).pc = returnPc R ∧
      (stepN k R).s = R.s + 1 + 1 ∧
      peek (stepN k R) sy.Player_X_Speed = (if pushes (R.ram.get! (sites sy m0).side) (peek R sy.Player_X_Speed) then 0 else peek R sy.Player_X_Speed) ∧
      peek (stepN k R) sy.SprObject_X_MoveForce = peek R sy.SprObject_X_MoveForce ∧
      peek (stepN k R) sy.Player_X_MoveForce = peek R sy.Player_X_MoveForce ∧
      (posP sy (stepN k R) - posP sy R - 256 * delta (R.ram.get! (sites sy m0).side) (peek R sy.Player_X_Speed)) % 0x1000000 = 0 ∧
      InFrameN (Rom.of m0) R k := by
  obtain ⟨k,hk,g,pc,sp,vel,f,u,hm,stk,ih⟩ := routine hc hg hpc
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
    have e : j = 0 := by omega
    subst j
    exact inFrame_rts g hr1 hr2 hr3
  refine ⟨k+1,by omega,?_⟩
  rw [stepN_add]
  exact ⟨rg,rpc,by rw [rs,sp],(wp _).trans vel,(wp _).trans f,(wp _).trans u,by rw [pe]; exact hm,
    InFrameN.add' ih rfl ic⟩

/-- An ordinary CPU step preserves position when it writes none of the three
position bytes. This is a one-state condition for the steps outside a summarized call. -/
theorem ordinary_step {sy : Syms} {R : Machine}
    (h : ∀ a ∈ [sy.Player_X_Position,sy.Player_PageLoc,sy.SprObject_X_MoveForce], I a ∉ StepWrites.stepLocs R) :
    posP sy (PipeTransitionAll.go step R).2 = posP sy R := by
  have px := StepWrites.step_ram R (I sy.Player_X_Position) (h _ (by simp))
  have pg := StepWrites.step_ram R (I sy.Player_PageLoc) (h _ (by simp))
  have pf := StepWrites.step_ram R (I sy.SprObject_X_MoveForce) (h _ (by simp))
  unfold posP peek
  simp only [FrameModel.I] at px pg pf
  rw [px,pg,pf]

/-- A sound cut at a call on an actual frame trace. The call can be replaced by
its return and position relation; ordinary steps use `ordinary_step`. This does
not assert that the other post-scroll position writers are absent. -/
theorem trace_call {sy : Syms} {m0 M : Machine} {i : UInt8} {n : Nat}
    (hc : check sy m0 = true) (hg : Good (Rom.of m0) (PipeEntryRule.trace M i n))
    (hp : (PipeEntryRule.trace M i n).pc = sy.ImpedePlayerMove)
    (hidle : idleAt (Rom.of m0) sy.EndlessLoop = true)
    (hf : (PipeEntryRule.trace M i n).frame = M.frame)
    (ht : ∀ j, (PipeEntryRule.trace M i j).pc ≠ sy.EndlessLoop →
      (PipeEntryRule.trace M i j).fdot ≤ dotsPerFrame - 64) :
    ∃ d, d ≤ 65 ∧ (PipeEntryRule.trace M i (n+d)).pc = returnPc (PipeEntryRule.trace M i n) ∧
      (PipeEntryRule.trace M i (n+d)).s = (PipeEntryRule.trace M i n).s + 1 + 1 ∧
      peek (PipeEntryRule.trace M i (n+d)) sy.Player_X_Speed =
        (if pushes ((PipeEntryRule.trace M i n).ram.get! (sites sy m0).side) (peek (PipeEntryRule.trace M i n) sy.Player_X_Speed) then 0
         else peek (PipeEntryRule.trace M i n) sy.Player_X_Speed) ∧
      (posP sy (PipeEntryRule.trace M i (n+d)) - posP sy (PipeEntryRule.trace M i n) -
        256 * delta ((PipeEntryRule.trace M i n).ram.get! (sites sy m0).side) (peek (PipeEntryRule.trace M i n) sy.Player_X_Speed)) % 0x1000000 = 0 := by
  obtain ⟨d,hd,_,pc,sp,vel,_,_,hm,ih⟩ := routine_return hc hg hp
  have eq := (trace_inFrame hidle hf ih ht d (Nat.le_refl d)).1
  exact ⟨d,hd,by rw [eq]; exact pc,by rw [eq]; exact sp,by rw [eq]; exact vel,by rw [eq]; exact hm⟩

end Smbrta.ImpedePosition
