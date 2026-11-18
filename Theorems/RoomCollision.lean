import Theorems.RoomAddress

/-! The block-buffer read from coordinates, in small checked instruction pieces.
ROM operands and offsets are parameters; no map or ROM table bytes are embedded. -/
namespace Smbrta.RoomCollision
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


/-- Extra known Y/zero flag on entry; optional known Y on exit. -/
def regStart (c : Cut) (iy : Option UInt8) (iz : Option Bool) : TS :=
  {start0 c with
    y := match iy with | none => .eq | some y => Tag.kn y y
    z := match iz with | none => .eq | some z => .kn z z}

def yGoal (oy : Option UInt8) (Q : TS) : Bool :=
  match oy with | none => true | some y => Q.y.same == some y

def regPiece (E : Rom) (c c' : Cut) (watch : List Nat)
    (iy : Option UInt8) (iz : Option Bool) (oy : Option UInt8) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (fun Q => goal0 c' watch Q && yGoal oy Q) fuel (regStart c iy iz)

def YAt (y : Option UInt8) (m : Machine) : Prop := ∀ v, y = some v → m.y = v
def ZAt (z : Option Bool) (m : Machine) : Prop := ∀ v, z = some v → TaintRun.bt m.p 1 = v

theorem regPiece_spec {E : Rom} {c c' : Cut} {watch : List Nat}
    {iy oy : Option UInt8} {iz : Option Bool} {fuel : Nat} {m : Machine}
    (hc : regPiece E c c' watch iy iz oy fuel = true)
    (h : At E {c with s := m.s} m) (hy : YAt iy m) (hz : ZAt iz m) :
    ∃ k, k ≤ fuel ∧ At E {c' with s := m.s} (stepN k m) ∧ YAt oy (stepN k m) ∧
      (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ InFrameN E m k := by
  have H := lk_start0 h
  have HY : Lk E m m (regStart c iy iz) m m := by
    refine ⟨H.gl,H.gr,H.pcl,H.pcr,⟨H.regs.a,H.regs.x,?_,H.regs.c,?_,H.regs.nf⟩,H.s,H.s0,H.ram,H.fixl,H.fixr⟩
    · cases iy with
      | none => rfl
      | some v => rw [hy v rfl]; exact Tag.R_kn _ _
    · cases iz with
      | none => rfl
      | some v => exact ⟨hz v rfl,hz v rfl⟩
  obtain ⟨k,Q,hk,_,hg,H1,hh⟩ := walkT_spec fuel (regStart c iy iz) m m hc HY
  have hg0 : goal0 c' watch Q = true ∧ yGoal oy Q = true := by simpa only [Bool.and_eq_true] using hg
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
  refine ⟨k,hk,ha,?_,hw,fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩
  intro v hv
  have he : Q.y.same = some v := by simpa only [yGoal,hv,beq_iff_eq] using hg0.2
  exact (Tag.same_spec he H1.regs.y).1

structure Places where
  entry : UInt16
  xadc : UInt16
  page : UInt16
  call : UInt16
  afterCall : UInt16
  read : UInt16
  pull : UInt16
  tail : UInt16
  ret : UInt16
  xtable : UInt16
  ytable : UInt16
  x : Nat
  pg : Nat
  y : Nat
  saved : Nat
  tmp : Nat
  row : Nat
  tile : Nat
  ptr : UInt8
  mask : UInt8
  top : UInt8
  lowMask : UInt8
  deriving Inhabited

/-- Decode only the instruction layout; the checks below validate all pieces. -/
def places (sy : Syms) (m0 : Machine) : Places :=
  let E := Rom.of m0
  let entry := sy.BlockBufferCollision
  let call := PipeEntryRule.findOp m0 entry 0x20 64
  let read := PipeEntryRule.findOp m0 entry 0xB1 96
  {entry, xadc := entry+7,page := entry+11,call,afterCall := call+3,read,
   pull := read+6,tail := read+20,ret := read+22,
   xtable := E.w (entry+4),ytable := E.w (call+9),
   x := I sy.Player_X_Position,pg := I sy.Player_PageLoc,y := I sy.Player_Y_Position,
   saved := (E.b (entry+2)).toNat,tmp := (E.b (entry+10)).toNat,
   row := (E.b (read-2)).toNat,tile := (E.b (read+3)).toNat,ptr := E.b (read+1),
   mask := E.b (read-7),top := E.b (read-4),lowMask := E.b (read+17)}

def stackI : List Nat := (List.range 256).map fun n => stkI n.toUInt8

def coords (P : Places) : List Nat := [P.x,P.pg,P.y]
def keep (P : Places) : List Nat := coords P ++ stackI

def xadd (E : Rom) (P : Places) (i : UInt8) : UInt8 := E.b (P.xtable+i.toUInt16)
def yadd (E : Rom) (P : Places) (i : UInt8) : UInt8 := E.b (P.ytable+i.toUInt16)
def rowOf (P : Places) (y off : UInt8) : UInt8 := ((y+off) &&& P.mask) - P.top

def cPre (P : Places) : Cut := {pc := P.entry+1,s := 0,K := [],x := some 0}
def cX (E : Rom) (P : Places) (i x : UInt8) : Cut :=
  {pc := P.xadc,s := 0,K := [(P.x,x)],ra := some (xadd E P i),x := some 0,cf := some false}
def cPg (P : Places) (x : UInt8) (c : Bool) : Cut :=
  {pc := P.page,s := 0,K := [(P.tmp,x)],ra := some x,x := some 0,cf := some c}
def cSel (P : Places) (a : UInt8) : Cut := {pc := P.call,s := 0,K := [],ra := some a,x := some 0}
def cRow (P : Places) (i y : UInt8) : Cut :=
  {pc := P.afterCall,s := 0,K := [(P.saved,i),(P.y,y)],x := some 0}
def cRead (P : Places) (r : UInt8) : Cut := {pc := P.read,s := 0,K := [(P.row,r)],x := some 0}

def prefixCheck (E : Rom) (P : Places) (i : UInt8) : Bool :=
  regPiece E (cPre P) {pc := P.xadc,s := 0,K := [(P.saved,i)],ra := some (xadd E P i),x := some 0,cf := some false}
    (keep P) (some i) none none 8

def xCheck (E : Rom) (P : Places) (i x : UInt8) : Bool :=
  let v := adcC (xadd E P i) x false
  piece0 E (cX E P i x) (cPg P v.1 v.2) (P.saved :: keep P) 4

def pageCheck (E : Rom) (P : Places) (p x : UInt8) (c : Bool) : Bool :=
  let v := (x >>> 4) ||| (((p + if c then 1 else 0) &&& 1) <<< 4)
  piece0 E {cPg P x c with K := [(P.tmp,x),(P.pg,p)]} (cSel P v) (P.saved :: keep P) 16

def pointerCut (B : ScreenPage.Places) (P : Places) (s a : UInt8) : Cut :=
  let t := RoomAddress.target B a
  {pc := P.afterCall,s,K := [(I P.ptr.toUInt16,t.toUInt8),(I (P.ptr+1).toUInt16,(t >>> 8).toUInt8)],x := some 0}

def callCheck (E : Rom) (B : ScreenPage.Places) (P : Places) (s a : UInt8) : Bool :=
  pieceOK E {cSel P a with s} (pointerCut B P s a)
    (P.saved :: (coords P ++ [stkI (s+1),stkI (s+2),stkI (s+3)])) 48

def rowCheck (E : Rom) (P : Places) (i y : UInt8) : Bool :=
  regPiece E (cRow P i y) (cRead P (rowOf P y (yadd E P i)))
    ((I P.ptr.toUInt16) :: (I (P.ptr+1).toUInt16) :: P.saved :: keep P)
    none none (some (rowOf P y (yadd E P i))) 16

def prefixAll (E : Rom) (P : Places) : Bool :=
  (List.range 256).all fun i => prefixCheck E P i.toUInt8

def xAll (E : Rom) (P : Places) : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun x => xCheck E P i.toUInt8 x.toUInt8

def pageAll (E : Rom) (P : Places) : Bool :=
  (List.range 256).all fun p => (List.range 256).all fun x => [false,true].all fun c => pageCheck E P p.toUInt8 x.toUInt8 c

def callAll (E : Rom) (B : ScreenPage.Places) (P : Places) : Bool :=
  (List.range 256).all fun s => (List.range 32).all fun a => callCheck E B P s.toUInt8 a.toUInt8

def rowAll (E : Rom) (P : Places) : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun y => rowCheck E P i.toUInt8 y.toUInt8

def metaCheck (E : Rom) (P : Places) : Bool :=
  [P.entry,P.entry+1,P.entry+1+1,P.ret,P.read,P.read+1].all (fun pc => decide (0x8000 ≤ pc)) &&
  E.b P.entry == 0x48 && !idleAt E P.entry && E.b P.ret == 0x60 && !idleAt E P.ret &&
  (coords P ++ [P.saved,P.tmp,P.row,P.tile,I P.ptr.toUInt16,I (P.ptr+1).toUInt16]).all (fun i => decide (i < 256))

/-- The checked byte/carry expression is the selector of the full coordinate. -/
theorem adc_selector (p x d : UInt8) :
    let v := adcC d x false
    (v.1 >>> 4) ||| (((p + if v.2 then 1 else 0) &&& 1) <<< 4) = RoomAddress.selector p x d := by
  rw [← RoomAddress.encoded_eq_selector]
  unfold RoomAddress.encoded adcC cB
  bv_decide

/-- A push with all registers other than SP unchanged, independent of their values. -/
theorem push_step {E : Rom} {R : Machine} (g : Good E R)
    (hp : 0x8000 ≤ R.pc) (hd : lookupOp (E.b R.pc) insList = some .pha)
    (hi : idleAt E R.pc = false) :
    let B := {R with pc := R.pc+1,s := R.s-1,ram := R.ram.set! (stkI R.s) R.a}
    nt (PipeTransitionAll.go step R).2 = nt B ∧ Good E (PipeTransitionAll.go step R).2 := by
  intro B
  have gb : Good E B := ⟨g.prg,g.mask,g.nmi,g.halted,g.trk,by
    show (R.ram.set! _ _).size = 2048
    rw [PipeTransitionAll.ba_size_set]; exact g.size,g.ctl⟩
  have ef : PipeTransitionAll.go (sem .pha) {R with pc := R.pc+1} = ((),B) := by
    show PipeTransitionAll.go (Smbrta.push R.a) {R with pc := R.pc+1} = _
    rw [push_eff (g.pc (R.pc+1))]
  have he := step_nt g hp hd hi (by rw [ef]) gb
  exact ⟨he,Good.of_nt he gb⟩

def ptrK (B : ScreenPage.Places) (P : Places) (a : UInt8) : List (Nat × UInt8) :=
  let t := RoomAddress.target B a
  [(I P.ptr.toUInt16,t.toUInt8),(I (P.ptr+1).toUInt16,(t >>> 8).toUInt8)]

def restKeep (P : Places) : List Nat :=
  [I P.ptr.toUInt16,I (P.ptr+1).toUInt16,P.row,P.saved] ++ keep P

def rowValues (P : Places) : List UInt8 :=
  ((List.range 256).map fun n => rowOf P n.toUInt8 0).eraseDups

def tileCheck (E : Rom) (B : ScreenPage.Places) (P : Places) (a r v : UInt8) : Bool :=
  let ad := RoomAddress.target B a + r.toUInt16
  E.b P.read == 0xB1 && E.b (P.read+1) == P.ptr && decide (ad.toNat < 2048) &&
  regPiece E {pc := P.read,s := 0,K := (I ad,v) :: ptrK B P a,x := some 0}
    {pc := P.read+4,s := 0,K := [(P.tile,v)],ra := some v,x := some 0}
    (restKeep P) (some r) none none 4

def tileAll (E : Rom) (B : ScreenPage.Places) (P : Places) : Bool :=
  (List.range 32).all fun a => (rowValues P).all fun r =>
    (List.range 256).all fun v => tileCheck E B P a.toUInt8 r v.toUInt8

def restoreCheck (E : Rom) (P : Places) (i : UInt8) : Bool :=
  regPiece E {pc := P.read+4,s := 0,K := [(P.saved,i)],x := some 0}
    {pc := P.pull,s := 0,K := [],x := some 0}
    (P.tile :: restKeep P) none none (some i) 4

def zGoal (z : Bool) (Q : TS) : Bool :=
  match Q.z with | .kn u v => u == z && v == z | _ => false

def pullIn (P : Places) (s a : UInt8) : Cut :=
  {pc := P.pull,s,K := [(stkI (s+1),a)],x := some 0}
def pullOut (P : Places) (s a : UInt8) : Cut :=
  {pc := P.pull+1,s := s+1,K := [],ra := some a,x := some 0}
def pullCheck (E : Rom) (P : Places) (s a : UInt8) : Bool :=
  walkT E (fun Q => Q.pc == P.pull+1)
    (fun Q => goalC (pullOut P s a) (P.tile :: restKeep P) Q && zGoal (a == 0) Q) 2 (startQ (pullIn P s a))

def branchCheck (E : Rom) (P : Places) (zero : Bool) (v : UInt8) : Bool :=
  regPiece E {pc := P.pull+1,s := 0,K := [(if zero then P.y else P.x,v)],x := some 0}
    {pc := P.tail,s := 0,K := [(P.saved,v &&& P.lowMask)],x := some 0}
    ([I P.ptr.toUInt16,I (P.ptr+1).toUInt16,P.row,P.tile] ++ keep P)
    none (some zero) none 12

def loadCheck (E : Rom) (P : Places) (v : UInt8) : Bool :=
  piece0 E {pc := P.tail,s := 0,K := [(P.tile,v)],x := some 0}
    {pc := P.ret,s := 0,K := [],ra := some v,x := some 0}
    (P.tile :: restKeep P) 2

def restoreAll (E : Rom) (P : Places) : Bool := (List.range 256).all fun i => restoreCheck E P i.toUInt8
def pullAll (E : Rom) (P : Places) : Bool :=
  (List.range 256).all fun s => (List.range 256).all fun a => pullCheck E P s.toUInt8 a.toUInt8
def branchAll (E : Rom) (P : Places) : Bool :=
  [false,true].all fun z => (List.range 256).all fun v => branchCheck E P z v.toUInt8
def loadAll (E : Rom) (P : Places) : Bool := (List.range 256).all fun v => loadCheck E P v.toUInt8

def check (sy : Syms) (nm : PipeTransitionAll.Names) (m0 : Machine) : Bool :=
  let E := Rom.of m0
  let P := places sy m0
  let B := (EntryHeight.hpOf sy nm m0).P
  metaCheck E P && prefixAll E P && xAll E P && pageAll E P && callAll E B P && rowAll E P &&
    tileAll E B P && restoreAll E P && pullAll E P && branchAll E P && loadAll E P

theorem all256 {f : UInt8 → Bool} (h : (List.range 256).all (fun n => f n.toUInt8) = true) (a : UInt8) : f a = true := by
  simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 h a.toNat (List.mem_range.2 a.toNat_lt)

structure Facts (E : Rom) (B : ScreenPage.Places) (P : Places) : Prop where
  bounds : metaCheck E P = true
  pre : ∀ i, prefixCheck E P i = true
  x : ∀ i x, xCheck E P i x = true
  page : ∀ p x c, pageCheck E P p x c = true
  call : ∀ s a, a.toNat < 32 → callCheck E B P s a = true
  row : ∀ i y, rowCheck E P i y = true
  tile : ∀ a r v, a.toNat < 32 → r ∈ rowValues P → tileCheck E B P a r v = true
  restore : ∀ i, restoreCheck E P i = true
  pull : ∀ s a, pullCheck E P s a = true
  branch : ∀ z v, branchCheck E P z v = true
  load : ∀ v, loadCheck E P v = true

theorem facts_of_check {sy : Syms} {nm : PipeTransitionAll.Names} {m0 : Machine}
    (h : check sy nm m0 = true) :
    Facts (Rom.of m0) (EntryHeight.hpOf sy nm m0).P (places sy m0) := by
  change (_ && _ && _ && _ && _ && _ && _ && _ && _ && _ && _) = true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm,hp⟩,hx⟩,hpg⟩,hc⟩,hr⟩,ht⟩,hrs⟩,hpl⟩,hb⟩,hl⟩ := h
  refine ⟨hm,fun i => all256 hp i,fun i x => all256 (all256 (f := fun i => (List.range 256).all fun x => xCheck _ _ i x.toUInt8) hx i) x,?_,?_,
    fun i y => all256 (all256 (f := fun i => (List.range 256).all fun y => rowCheck _ _ i y.toUInt8) hr i) y,?_,fun i => all256 hrs i,
    fun s a => all256 (all256 (f := fun s => (List.range 256).all fun a => pullCheck _ _ s a.toUInt8) hpl s) a,?_,fun v => all256 hl v⟩
  · intro p x c
    have h1 : (List.range 256).all (fun x => [false,true].all (fun c => pageCheck (Rom.of m0) (places sy m0) p x.toUInt8 c)) = true :=
      all256 (f := fun p => (List.range 256).all fun x => [false,true].all fun c => pageCheck (Rom.of m0) (places sy m0) p x.toUInt8 c) hpg p
    have h2 : [false,true].all (fun c => pageCheck (Rom.of m0) (places sy m0) p x c) = true :=
      all256 (f := fun x => [false,true].all fun c => pageCheck (Rom.of m0) (places sy m0) p x c) h1 x
    exact List.all_eq_true.1 h2 c (by cases c <;> simp)
  · intro s a ha
    have h1 : (List.range 32).all (fun a => callCheck (Rom.of m0) (EntryHeight.hpOf sy nm m0).P (places sy m0) s a.toUInt8) = true :=
      all256 (f := fun s => (List.range 32).all fun a => callCheck (Rom.of m0) (EntryHeight.hpOf sy nm m0).P (places sy m0) s a.toUInt8) hc s
    simpa only [UInt8.ofNat_toNat] using List.all_eq_true.1 h1 a.toNat (List.mem_range.2 ha)
  · intro a r v ha hr
    have h1 := List.all_eq_true.1 ht a.toNat (List.mem_range.2 ha)
    have h2 := List.all_eq_true.1 h1 r hr
    simpa only [UInt8.ofNat_toNat] using all256 h2 v
  · intro z v
    exact all256 (List.all_eq_true.1 hb z (by cases z <;> simp)) v

theorem row_mem (P : Places) (y d : UInt8) : rowOf P y d ∈ rowValues P := by
  unfold rowValues
  rw [List.mem_eraseDups]
  apply List.mem_map.2
  refine ⟨(y+d).toNat,List.mem_range.2 (y+d).toNat_lt,?_⟩
  simp only [UInt8.ofNat_toNat,rowOf,UInt8.add_zero]

theorem stack_mem (s : UInt8) : stkI s ∈ stackI := by
  apply List.mem_map.2
  exact ⟨s.toNat,List.mem_range.2 s.toNat_lt,by simp⟩

theorem stk_index (s : UInt8) : stkI s = 256+s.toNat := by
  have h : (0x100 ||| s.toUInt16) &&& 0x7FF = 0x100 + s.toUInt16 := by bv_decide
  rw [stkI,h,UInt16.toNat_add]
  simp only [UInt16.toNat_ofNat,UInt8.toNat_toUInt16]
  have hs := s.toNat_lt
  omega

theorem stack_low (s : UInt8) {i : Nat} (hi : i < 256) : i ≠ stkI s := by
  rw [stk_index]; omega

theorem mkAt {E : Rom} {R : Machine} {pc : UInt16} {K : List (Nat × UInt8)}
    {ra : Option UInt8} {x : Option UInt8} {cf : Option Bool}
    (hg : Good E R) (hp : R.pc = pc) (hk : ∀ q ∈ K, R.ram.get! q.1 = q.2)
    (ha : ∀ v, ra = some v → R.a = v) (hx : ∀ v, x = some v → R.x = v)
    (hc : ∀ b, cf = some b → TaintRun.bt R.p 0 = b) :
    At E {pc,s := R.s,K,ra,x,cf} R :=
  ⟨hg,hp,rfl,hk,(fun _ h => by cases h),ha,hx,hc⟩

theorem pull_spec {E : Rom} {P : Places} {R : Machine} {s a : UInt8}
    (hc : pullCheck E P s a = true) (h : At E (pullIn P s a) R) :
    ∃ k, k ≤ 2 ∧ At E (pullOut P s a) (stepN k R) ∧ TaintRun.bt (stepN k R).p 1 = (a == 0) ∧
      (∀ i ∈ P.tile :: restKeep P, i < 2048 → (stepN k R).ram.get! i = R.ram.get! i) ∧ InFrameN E R k := by
  obtain ⟨k,Q,hk,_,hg,H,hh⟩ := walkT_spec 2 (startQ (pullIn P s a)) R R hc (lk_self h)
  have h0 : goalC (pullOut P s a) (P.tile :: restKeep P) Q = true ∧ zGoal (a == 0) Q = true := by
    simpa only [Bool.and_eq_true] using hg
  obtain ⟨ha,hw,_⟩ := at_of_goal h0.1 H
  refine ⟨k,hk,ha,?_,hw,fun j hj => by obtain ⟨_,_,_,_,hi,_⟩ := hh j hj; exact hi⟩
  have hz := h0.2
  cases he : Q.z with
  | any => simp [zGoal,he] at hz
  | eq => simp [zGoal,he] at hz
  | kn u v =>
    have e : u = (a == 0) ∧ v = (a == 0) := by simpa only [zGoal,he,Bool.and_eq_true,beq_iff_eq] using hz
    have hreg := H.regs.z
    rw [he,e.1,e.2] at hreg
    exact hreg.1

def ramI (P : Places) : List Nat :=
  coords P ++ [P.saved,P.tmp,P.row,P.tile,I P.ptr.toUInt16,I (P.ptr+1).toUInt16]

theorem Facts.ram_lt {E : Rom} {B : ScreenPage.Places} {P : Places} (F : Facts E B P)
    {i : Nat} (hi : i ∈ ramI P) : i < 2048 := by
  have h := F.bounds
  simp only [metaCheck,Bool.and_eq_true] at h
  have hb : i < 256 := of_decide_eq_true (List.all_eq_true.1 h.2 i hi)
  omega

theorem Facts.code_bound {E : Rom} {B : ScreenPage.Places} {P : Places} (F : Facts E B P)
    {pc : UInt16} (hi : pc ∈ [P.entry,P.entry+1,P.entry+1+1,P.ret,P.read,P.read+1]) : 0x8000 ≤ pc := by
  have h := F.bounds
  simp only [metaCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.1 h.1.1.1.1.1 pc hi)

def Kept (L : List Nat) (R Q : Machine) : Prop :=
  ∀ i ∈ L, i < 2048 → Q.ram.get! i = R.ram.get! i

theorem Kept.trans {L : List Nat} {R Q B : Machine} (h1 : Kept L R Q) (h2 : Kept L Q B) : Kept L R B :=
  fun i hi hb => (h2 i hi hb).trans (h1 i hi hb)

def watch (P : Places) (s : UInt8) : List Nat :=
  P.saved :: (coords P ++ [stkI (s+1),stkI (s+2),stkI (s+3)])

theorem watch_sub (P : Places) (s : UInt8) {i : Nat} (hi : i ∈ watch P s) : i ∈ P.saved :: keep P := by
  simp only [watch,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hi
  rcases hi with h | h | h | h | h
  · simp [h]
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  all_goals subst i; exact List.mem_cons_of_mem _ (List.mem_append_right _ (stack_mem _))

theorem kept_watch {P : Places} {s : UInt8} {R Q : Machine} (h : Kept (P.saved :: keep P) R Q) :
    Kept (watch P s) R Q := fun i hi hb => h i (watch_sub P s hi) hb

theorem Kept.coord {E : Rom} {B : ScreenPage.Places} {P : Places} {s : UInt8} {R Q : Machine}
    (F : Facts E B P) (h : Kept (watch P s) R Q) {i : Nat} (hi : i ∈ coords P) :
    Q.ram.get! i = R.ram.get! i := h i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
      (F.ram_lt (List.mem_append_left _ hi))

theorem Kept.saved {E : Rom} {B : ScreenPage.Places} {P : Places} {s : UInt8} {R Q : Machine}
    (F : Facts E B P) (h : Kept (watch P s) R Q) : Q.ram.get! P.saved = R.ram.get! P.saved :=
  h _ (List.mem_cons_self ..) (F.ram_lt (by simp [ramI]))

theorem ptr_known {T : Machine} {z : UInt8} {t : UInt16}
    (hl : T.ram.get! (I z.toUInt16) = t.toUInt8)
    (hh : T.ram.get! (I (z+1).toUInt16) = (t >>> 8).toUInt8) : RoomBlocks.ptrZ T z = t := by
  change (T.ram.get! (I z.toUInt16)).toUInt16 ||| ((T.ram.get! (I (z+1).toUInt16)).toUInt16 <<< 8) = t
  rw [hl,hh]
  exact RoomAddress.bytes16_eq t

/-- From the horizontal ADC to the actual tile-read instruction, with the
coordinates still symbolic and the offset index arbitrary. -/
theorem from_x {E : Rom} {B : ScreenPage.Places} {P : Places} {R : Machine} {i : UInt8}
    (F : Facts E B P)
    (h : At E {cX E P i (R.ram.get! P.x) with s := R.s} R)
    (hi : R.ram.get! P.saved = i) :
    ∃ k, k ≤ 84 ∧
      At E {cRead P (rowOf P (R.ram.get! P.y) (yadd E P i)) with s := R.s} (stepN k R) ∧
      (stepN k R).y = rowOf P (R.ram.get! P.y) (yadd E P i) ∧
      RoomBlocks.ptrZ (stepN k R) P.ptr = RoomAddress.target B
        (RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P i)) ∧
      Kept (watch P R.s) R (stepN k R) ∧ InFrameN E R k := by
  let v := adcC (xadd E P i) (R.ram.get! P.x) false
  let a := RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P i)
  let r := rowOf P (R.ram.get! P.y) (yadd E P i)
  obtain ⟨nx,hx,ax,wx,ix⟩ := piece0_spec (F.x i (R.ram.get! P.x)) h
  let X1 := stepN nx R
  have kx : Kept (watch P R.s) R X1 := kept_watch wx
  have ap : At E {{cPg P v.1 v.2 with K := [(P.tmp,v.1),(P.pg,R.ram.get! P.pg)]} with s := X1.s} X1 := by
    apply mkAt ax.good ax.pc _ ax.ra ax.x ax.cf
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact ax.K _ (List.mem_cons_self ..)
    · exact Kept.coord F kx (by simp [coords])
  obtain ⟨np,hp,apg,wp,ip⟩ := piece0_spec (F.page (R.ram.get! P.pg) v.1 v.2) ap
  let X2 := stepN np X1
  have kp : Kept (watch P R.s) X1 X2 := kept_watch wp
  have sa : X2.s = R.s := apg.s.trans ax.s
  have ea : (v.1 >>> 4) ||| (((R.ram.get! P.pg + if v.2 then 1 else 0) &&& 1) <<< 4) = a :=
    adc_selector _ _ _
  have acall : At E {cSel P a with s := X2.s} X2 := by
    rw [ea] at apg
    exact ⟨apg.good,apg.pc,rfl,apg.K,apg.B,apg.ra,apg.x,apg.cf⟩
  obtain ⟨nc,hc,ac,wc,ic⟩ := piece_specI (F.call X2.s a (RoomAddress.selector_lt ..)) acall
  let X3 := stepN nc X2
  have kc : Kept (watch P R.s) X2 X3 := by simpa only [watch,sa] using wc
  have k3 := (kx.trans kp).trans kc
  have s3 : X3.s = R.s := ac.s.trans sa
  have ar0 : At E {cRow P i (R.ram.get! P.y) with s := X3.s} X3 := by
    apply mkAt ac.good ac.pc _ (fun _ h => by cases h) ac.x (fun _ h => by cases h)
    intro q hq
    simp only [cRow,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact (Kept.saved F k3).trans hi
    · exact Kept.coord F k3 (by simp [coords])
  obtain ⟨nr,hr,ar,yr,wr,ir⟩ := regPiece_spec (F.row i (R.ram.get! P.y)) ar0
    (fun _ h => by cases h) (fun _ h => by cases h)
  let X4 := stepN nr X3
  have kr : Kept (watch P R.s) X3 X4 := kept_watch (fun j hj hb => wr j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)) hb)
  have po : RoomBlocks.ptrZ X4 P.ptr = RoomAddress.target B a := by
    apply ptr_known
    · have w := wr (I P.ptr.toUInt16) (List.mem_cons_self ..) (F.ram_lt (by simp [ramI]))
      exact w.trans (ac.K _ (List.mem_cons_self ..))
    · have w := wr (I (P.ptr+1).toUInt16) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (F.ram_lt (by simp [ramI]))
      exact w.trans (ac.K _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have eq : stepN (nx+np+nc+nr) R = X4 := by simp only [stepN_add]; rfl
  refine ⟨nx+np+nc+nr,by omega,?_⟩
  rw [eq]
  refine ⟨by simpa only [s3] using ar,yr _ rfl,po,k3.trans kr,?_⟩
  have ixp := InFrameN.add' ix rfl ip
  have ixpc := InFrameN.add' ixp (by simp only [stepN_add]; rfl) (fun j hj => (ic j hj).2.2)
  exact InFrameN.add' ixpc (by simp only [stepN_add]; rfl) ir

theorem Facts.low_lt {E : Rom} {B : ScreenPage.Places} {P : Places} (F : Facts E B P)
    {i : Nat} (hi : i ∈ ramI P) : i < 256 := by
  have h := F.bounds
  simp only [metaCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.1 h.2 i hi)

def outerStack (s : UInt8) : List Nat := [stkI s,stkI (s+1),stkI (s+2)]

theorem stack_offsets (s : UInt8) : s-1+1 = s ∧ s-1+2 = s+1 ∧ s-1+3 = s+2 := by bv_decide

theorem stack_ne (s : UInt8) : stkI (s+1) ≠ stkI s ∧ stkI (s+2) ≠ stkI s := by
  have h : ∀ n : Fin 256, stkI (n.val.toUInt8+1) ≠ stkI n.val.toUInt8 ∧ stkI (n.val.toUInt8+2) ≠ stkI n.val.toUInt8 := by decide +kernel
  simpa only [UInt8.ofNat_toNat] using h ⟨s.toNat,s.toNat_lt⟩

theorem outer_mem {s : UInt8} {j : Nat} (hj : j ∈ outerStack s) : j ∈ stackI := by
  simp only [outerStack,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact stack_mem _

theorem stack_bound {i : Nat} (hi : i ∈ stackI) : i < 2048 := by
  obtain ⟨n,_,rfl⟩ := List.mem_map.1 hi
  exact mask_stk _

/-- Facts at the actual read, tied to coordinates and the offset index at entry. -/
structure ReadAt (E : Rom) (B : ScreenPage.Places) (P : Places) (R T : Machine) : Prop where
  cut : At E {cRead P (rowOf P (R.ram.get! P.y) (yadd E P R.y)) with s := R.s-1} T
  y : T.y = rowOf P (R.ram.get! P.y) (yadd E P R.y)
  pointer : RoomBlocks.ptrZ T P.ptr = RoomAddress.target B
    (RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P R.y))
  saved : T.ram.get! P.saved = R.y
  coord : ∀ j ∈ coords P, T.ram.get! j = R.ram.get! j
  flag : T.ram.get! (stkI R.s) = R.a
  ret1 : T.ram.get! (stkI (R.s+1)) = R.ram.get! (stkI (R.s+1))
  ret2 : T.ram.get! (stkI (R.s+2)) = R.ram.get! (stkI (R.s+2))

/-- From an arbitrary player entry state to its real tile-read instruction. -/
theorem entry_read {E : Rom} {B : ScreenPage.Places} {P : Places} {R : Machine}
    (F : Facts E B P) (g : Good E R) (pc : R.pc = P.entry) (x : R.x = 0) :
    ∃ k, k ≤ 93 ∧ ReadAt E B P R (stepN k R) ∧ InFrameN E R k := by
  have hm := F.bounds
  simp only [metaCheck,Bool.and_eq_true] at hm
  have ph : E.b P.entry = 0x48 := beq_iff_eq.mp hm.1.1.1.1.2
  have idle : idleAt E P.entry = false := by simpa only [Bool.not_eq_true'] using hm.1.1.1.2
  have hp : 0x8000 ≤ R.pc := by rw [pc]; exact F.code_bound (by simp)
  have hd : lookupOp (E.b R.pc) insList = some .pha := by rw [pc,ph]; rfl
  have hidle : idleAt E R.pc = false := by rw [pc]; exact idle
  obtain ⟨he,g1⟩ := push_step g hp hd hidle
  let R1 := stepN 1 R
  have p1 : R1.pc = P.entry+1 := (congrArg Machine.pc he).trans (by simp only [nt,pc])
  have s1 : R1.s = R.s-1 := congrArg Machine.s he
  have x1 : R1.x = 0 := (congrArg Machine.x he).trans x
  have y1 : R1.y = R.y := by simpa only [nt] using (congrArg Machine.y he)
  have rm1 : R1.ram = R.ram.set! (stkI R.s) R.a := congrArg Machine.ram he
  have coord1 : ∀ j ∈ coords P, R1.ram.get! j = R.ram.get! j := by
    intro j hj
    rw [rm1]
    exact PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun eq => (stack_low R.s (F.low_lt (List.mem_append_left _ hj))) eq.symm)
  have pre : At E {cPre P with s := R1.s} R1 := by
    apply mkAt g1 p1 (fun _ h => by cases h) (fun _ h => by cases h) _ (fun _ h => by cases h)
    intro v hv; cases hv; exact x1
  obtain ⟨np,hp,ap,_,wp,ip⟩ := regPiece_spec (F.pre R.y) pre
    (by intro v hv; cases hv; exact y1) (fun _ h => by cases h)
  let R2 := stepN np R1
  have coord2 : ∀ j ∈ coords P, R2.ram.get! j = R.ram.get! j := by
    intro j hj
    exact (wp j (List.mem_append_left _ hj) (F.ram_lt (List.mem_append_left _ hj))).trans (coord1 j hj)
  have cX0 : At E {cX E P R.y (R2.ram.get! P.x) with s := R2.s} R2 := by
    apply mkAt ap.good ap.pc _ ap.ra ap.x ap.cf
    intro q hq
    have e : q = (P.x,R2.ram.get! P.x) := by simpa only [cX,List.mem_cons,List.not_mem_nil,or_false] using hq
    rw [e]
  have saved2 : R2.ram.get! P.saved = R.y := ap.K _ (List.mem_cons_self ..)
  obtain ⟨nx,hx,ar,yr,ptr,wx,ix⟩ := from_x F cX0 saved2
  let T := stepN nx R2
  have sp2 : R2.s = R.s-1 := ap.s.trans s1
  have stk : ∀ j ∈ outerStack R.s, T.ram.get! j = R1.ram.get! j := by
    intro j hj
    have hs : j ∈ stackI := outer_mem hj
    have hw : j ∈ watch P R2.s := by
      rw [sp2]
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      simpa only [(stack_offsets R.s).1,(stack_offsets R.s).2.1,(stack_offsets R.s).2.2] using hj
    exact (wx j hw (stack_bound hs)).trans (wp j (List.mem_append_right _ hs) (stack_bound hs))
  have rd : ReadAt E B P R T := by
    refine ⟨?_,?_,?_,(Kept.saved F wx).trans saved2,?_,?_,?_,?_⟩
    · simpa only [sp2,coord2 P.y (by simp [coords])] using ar
    · simpa only [coord2 P.y (by simp [coords])] using yr
    · simpa only [coord2 P.pg (by simp [coords]),coord2 P.x (by simp [coords])] using ptr
    · intro j hj
      exact (Kept.coord F wx hj).trans (coord2 j hj)
    · rw [stk _ (by simp [outerStack]),rm1]
      exact PipeTransitionAll.ba_get_set_self _ _ _ (by rw [g.size]; exact mask_stk _)
    · rw [stk _ (by simp [outerStack]),rm1]
      exact PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun eq => (stack_ne R.s).1 eq.symm)
    · rw [stk _ (by simp [outerStack]),rm1]
      exact PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun eq => (stack_ne R.s).2 eq.symm)
  have it : InFrame E R := by
    refine ⟨g.halted,hidle,fun hf => ?_⟩
    apply step_time g (by rw [pc]; exact F.code_bound (by simp))
      (by rw [pc]; exact F.code_bound (by simp))
      (by rw [pc]; exact F.code_bound (by simp)) hd hidle ?_ hf
    trivial
  have if1 : InFrameN E R 1 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    exact it
  refine ⟨1+np+nx,by omega,?_⟩
  have eq : stepN (1+np+nx) R = T := by simp only [stepN_add]; rfl
  rw [eq]
  exact ⟨rd,InFrameN.add' (InFrameN.add' if1 rfl ip) (by simp only [stepN_add]; rfl) ix⟩

def returnPc (R : Machine) : UInt16 :=
  ((R.ram.get! (stkI (R.s+1))).toUInt16 ||| ((R.ram.get! (stkI (R.s+1+1))).toUInt16 <<< 8))+1

theorem return_step {E : Rom} {R : Machine} (g : Good E R)
    (hp : 0x8000 ≤ R.pc) (hd : lookupOp (E.b R.pc) insList = some .rts)
    (hi : idleAt E R.pc = false) :
    let B := {R with pc := returnPc R,s := R.s+1+1}
    nt (PipeTransitionAll.go step R).2 = nt B ∧ Good E (PipeTransitionAll.go step R).2 := by
  intro B
  have gb : Good E B := ⟨g.prg,g.mask,g.nmi,g.halted,g.trk,g.size,g.ctl⟩
  have ef : PipeTransitionAll.go (sem .rts) {R with pc := R.pc+1} = ((),B) := by
    change PipeTransitionAll.go opRTS {R with pc := R.pc+1} = _
    rw [rts_eff (g.pc (R.pc+1))]
    rfl
  have he := step_nt g hp hd hi (by rw [ef]) gb
  exact ⟨he,Good.of_nt he gb⟩

theorem ptr_bytes {T : Machine} {z : UInt8} {v : UInt16} (hp : RoomBlocks.ptrZ T z = v) :
    T.ram.get! (I z.toUInt16) = v.toUInt8 ∧ T.ram.get! (I (z+1).toUInt16) = (v >>> 8).toUInt8 := by
  have arith (l h : UInt8) (v : UInt16) :
      (l.toUInt16 ||| (h.toUInt16 <<< 8)) = v → l = v.toUInt8 ∧ h = (v >>> 8).toUInt8 := by bv_decide
  exact arith _ _ _ hp

def readAddress (E : Rom) (B : ScreenPage.Places) (P : Places) (R : Machine) : UInt16 :=
  RoomAddress.target B (RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P R.y)) +
    (rowOf P (R.ram.get! P.y) (yadd E P R.y)).toUInt16

def lowCoord (P : Places) (R : Machine) : UInt8 :=
  (if R.a == 0 then R.ram.get! P.y else R.ram.get! P.x) &&& P.lowMask

structure Returned (E : Rom) (B : ScreenPage.Places) (P : Places) (R T Q : Machine) : Prop where
  good : Good E Q
  pc : Q.pc = returnPc R
  s : Q.s = R.s+1+1
  a : Q.a = T.ram.get! (I (readAddress E B P R))
  row : Q.ram.get! P.row = rowOf P (R.ram.get! P.y) (yadd E P R.y)
  tile : Q.ram.get! P.tile = T.ram.get! (I (readAddress E B P R))
  low : Q.ram.get! P.saved = lowCoord P R

def postKeep (P : Places) : List Nat := P.row :: keep P

theorem Kept.mono {L K : List Nat} {R Q : Machine} (h : Kept L R Q)
    (sub : ∀ j ∈ K, j ∈ L) : Kept K R Q := fun j hj hb => h j (sub j hj) hb

theorem post_in_rest (P : Places) {j : Nat} (hj : j ∈ postKeep P) : j ∈ restKeep P := by
  rcases List.mem_cons.1 hj with rfl | hj
  · simp [restKeep]
  · exact List.mem_append_right _ hj

theorem post_in_branch (P : Places) {j : Nat} (hj : j ∈ postKeep P) :
    j ∈ [I P.ptr.toUInt16,I (P.ptr+1).toUInt16,P.row,P.tile] ++ keep P := by
  rcases List.mem_cons.1 hj with rfl | hj
  · simp
  · exact List.mem_append_right _ hj

/-- The actual read value is stored and returned, together with its row and
selected coordinate nibble; the original arbitrary caller stack is respected. -/
theorem return_from_read {E : Rom} {B : ScreenPage.Places} {P : Places} {R T : Machine}
    (F : Facts E B P) (H : ReadAt E B P R T) :
    ∃ k, k ≤ 25 ∧ Returned E B P R T (stepN k T) ∧ InFrameN E T k := by
  let a := RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P R.y)
  let r := rowOf P (R.ram.get! P.y) (yadd E P R.y)
  let v := T.ram.get! (I (readAddress E B P R))
  have hc := F.tile a r v (RoomAddress.selector_lt ..) (row_mem ..)
  have hc0 := hc
  simp only [tileCheck,Bool.and_eq_true] at hc0
  have hi : At E
      {pc := P.read,s := T.s,K := (I (RoomAddress.target B a + r.toUInt16),v) :: ptrK B P a,x := some 0} T := by
    apply mkAt H.cut.good H.cut.pc _ (fun _ h => by cases h) H.cut.x (fun _ h => by cases h)
    intro q hq
    simp only [ptrK,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    · rfl
    · exact (ptr_bytes H.pointer).1
    · exact (ptr_bytes H.pointer).2
  obtain ⟨nt,ht,atT,_,wt,it⟩ := regPiece_spec hc0.2 hi
    (by intro y hy; cases hy; exact H.y) (fun _ h => by cases h)
  let T1 := stepN nt T
  have pt : Kept (postKeep P) T T1 := Kept.mono wt (fun _ hj => post_in_rest P hj)
  have bdTile := F.ram_lt (i := P.tile) (by simp [ramI])
  have bdRow := F.ram_lt (i := P.row) (by simp [ramI])
  have bdSaved := F.ram_lt (i := P.saved) (by simp [ramI])
  have tile1 : T1.ram.get! P.tile = v := atT.K _ (List.mem_cons_self ..)
  have saved1 : T1.ram.get! P.saved = R.y :=
    (wt _ (by simp [restKeep]) bdSaved).trans H.saved
  have ir0 : At E {pc := P.read+4,s := T1.s,K := [(P.saved,R.y)],x := some 0} T1 := by
    apply mkAt atT.good atT.pc _ (fun _ h => by cases h) atT.x (fun _ h => by cases h)
    intro q hq
    have eq : q = (P.saved,R.y) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
    rw [eq]; exact saved1
  obtain ⟨ny,hy,ay,_,wy,iy⟩ := regPiece_spec (F.restore R.y) ir0
    (fun _ h => by cases h) (fun _ h => by cases h)
  let T2 := stepN ny T1
  have py : Kept (postKeep P) T1 T2 := Kept.mono wy (fun _ hj => List.mem_cons_of_mem _ (post_in_rest P hj))
  have sp2 : T2.s = R.s-1 := ay.s.trans (atT.s.trans H.cut.s)
  have f2 : T2.ram.get! (stkI (T2.s+1)) = R.a := by
    rw [sp2,(stack_offsets R.s).1]
    exact ((pt.trans py) _ (List.mem_cons_of_mem _ (List.mem_append_right _ (stack_mem _))) (mask_stk _)).trans H.flag
  have ia : At E (pullIn P T2.s R.a) T2 := by
    apply mkAt ay.good ay.pc _ (fun _ h => by cases h) ay.x (fun _ h => by cases h)
    intro q hq
    have eq : q = (stkI (T2.s+1),R.a) := by simpa only [pullIn,List.mem_cons,List.not_mem_nil,or_false] using hq
    rw [eq]; exact f2
  obtain ⟨np,hp,ap,zp,wp,ip⟩ := pull_spec (F.pull T2.s R.a) ia
  let T3 := stepN np T2
  have pp : Kept (postKeep P) T2 T3 := Kept.mono wp (fun _ hj => List.mem_cons_of_mem _ (post_in_rest P hj))
  have sp3 : T3.s = R.s := by simpa only [pullOut,sp2,(stack_offsets R.s).1] using ap.s
  let c := if R.a == 0 then R.ram.get! P.y else R.ram.get! P.x
  have co3 : ∀ j ∈ coords P, T3.ram.get! j = R.ram.get! j := by
    intro j hj
    have hb := F.ram_lt (List.mem_append_left _ hj)
    exact (((pt.trans py).trans pp) _ (List.mem_cons_of_mem _ (List.mem_append_left _ hj)) hb).trans (H.coord j hj)
  have ib : At E {pc := P.pull+1,s := T3.s,K := [(if R.a == 0 then P.y else P.x,c)],x := some 0} T3 := by
    apply mkAt ap.good ap.pc _ (fun _ h => by cases h) ap.x (fun _ h => by cases h)
    intro q hq
    have eq : q = (if R.a == 0 then P.y else P.x,c) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
    rw [eq]
    dsimp only [c]
    split <;> exact co3 _ (by simp [coords])
  obtain ⟨nb,hb,ab,_,wb,ibf⟩ := regPiece_spec (F.branch (R.a == 0) c) ib
    (fun _ h => by cases h) (by intro z hz; cases hz; exact zp)
  let T4 := stepN nb T3
  have pb : Kept (postKeep P) T3 T4 := Kept.mono wb (fun _ hj => post_in_branch P hj)
  have sp4 : T4.s = R.s := ab.s.trans sp3
  have tile2 : T2.ram.get! P.tile = v := (wy _ (List.mem_cons_self ..) bdTile).trans tile1
  have tile3 : T3.ram.get! P.tile = v := (wp _ (List.mem_cons_self ..) bdTile).trans tile2
  have tile4 : T4.ram.get! P.tile = v := (wb _ (by simp) bdTile).trans tile3
  have il : At E {pc := P.tail,s := T4.s,K := [(P.tile,v)],ra := none,x := some 0} T4 := by
    apply mkAt ab.good ab.pc _ (fun _ h => by cases h) ab.x (fun _ h => by cases h)
    intro q hq
    have eq : q = (P.tile,v) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
    rw [eq]; exact tile4
  obtain ⟨nl,hl,al,wl,ifl⟩ := piece0_spec (F.load v) il
  let T5 := stepN nl T4
  have pl : Kept (postKeep P) T4 T5 := Kept.mono wl (fun _ hj => List.mem_cons_of_mem _ (post_in_rest P hj))
  have sp5 : T5.s = R.s := al.s.trans sp4
  have passive := (((pt.trans py).trans pp).trans pb).trans pl
  have c1 : T5.ram.get! (stkI (R.s+1)) = R.ram.get! (stkI (R.s+1)) :=
    (passive _ (List.mem_cons_of_mem _ (List.mem_append_right _ (stack_mem _))) (mask_stk _)).trans H.ret1
  have c2 : T5.ram.get! (stkI (R.s+2)) = R.ram.get! (stkI (R.s+2)) :=
    (passive _ (List.mem_cons_of_mem _ (List.mem_append_right _ (stack_mem _))) (mask_stk _)).trans H.ret2
  have aa : R.s+1+1 = R.s+2 := by bv_decide
  have rpc : returnPc T5 = returnPc R := by
    unfold returnPc
    rw [sp5,aa,c1,c2]
  have hm := F.bounds
  simp only [metaCheck,Bool.and_eq_true] at hm
  have cod : E.b P.ret = 0x60 := beq_iff_eq.mp hm.1.1.2
  have hid : idleAt E P.ret = false := by simpa only [Bool.not_eq_true'] using hm.1.2
  have hpc : 0x8000 ≤ T5.pc := by rw [al.pc]; exact F.code_bound (by simp)
  have hcode : lookupOp (E.b T5.pc) insList = some .rts := by rw [al.pc,cod]; rfl
  have hidle : idleAt E T5.pc = false := by rw [al.pc]; exact hid
  obtain ⟨he,gg⟩ := return_step al.good hpc hcode hidle
  have rram : (stepN 1 T5).ram = T5.ram := by simpa only [FrameModel.nt] using (congrArg Machine.ram he)
  have fin : Returned E B P R T (stepN 1 T5) := by
    refine ⟨gg,(congrArg Machine.pc he).trans rpc,?_,?_,?_,?_,?_⟩
    · have ee := congrArg Machine.s he
      change (stepN 1 T5).s = T5.s+1+1 at ee
      rw [sp5] at ee
      exact ee
    · exact (congrArg Machine.a he).trans (al.ra v rfl)
    · rw [rram]
      exact (passive _ (List.mem_cons_self ..) bdRow).trans (H.cut.K _ (List.mem_cons_self ..))
    · rw [rram]
      exact (wl _ (List.mem_cons_self ..) bdTile).trans tile4
    · rw [rram]
      exact (wl _ (by simp [restKeep]) bdSaved).trans (ab.K _ (List.mem_cons_self ..))
  have irts : InFrameN E T5 1 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    exact inFrame_rts al.good hpc hcode hidle
  have i1 := InFrameN.add' it rfl iy
  have i2 := InFrameN.add' i1 (by simp only [stepN_add]; rfl) ip
  have i3 := InFrameN.add' i2 (by simp only [stepN_add]; rfl) ibf
  have i4 := InFrameN.add' i3 (by simp only [stepN_add]; rfl) ifl
  have i5 := InFrameN.add' i4 (by simp only [stepN_add]; rfl) irts
  refine ⟨nt+ny+np+nb+nl+1,by omega,?_⟩
  have eq : stepN (nt+ny+np+nb+nl+1) T = stepN 1 T5 := by simp only [stepN_add]; rfl
  exact ⟨by rw [eq]; exact fin,i5⟩

/-- Complete player collision-buffer call, with an explicit cut at its tile read. -/
theorem routine {sy : Syms} {nm : PipeTransitionAll.Names} {m0 R : Machine}
    (hc : check sy nm m0 = true) (g : Good (Rom.of m0) R)
    (pc : R.pc = sy.BlockBufferCollision) (x : R.x = 0) :
    ∃ nr nt, nr ≤ 93 ∧ nt ≤ 25 ∧
      ReadAt (Rom.of m0) (EntryHeight.hpOf sy nm m0).P (places sy m0) R (stepN nr R) ∧
      Returned (Rom.of m0) (EntryHeight.hpOf sy nm m0).P (places sy m0) R
        (stepN nr R) (stepN (nr+nt) R) ∧ InFrameN (Rom.of m0) R (nr+nt) := by
  have F := facts_of_check hc
  obtain ⟨nr,hr,H,ir⟩ := entry_read F g pc x
  obtain ⟨nt,ht,Q,it⟩ := return_from_read F H
  refine ⟨nr,nt,hr,ht,H,?_,InFrameN.add' ir rfl it⟩
  simpa only [stepN_add] using Q

theorem Facts.read_meta {E : Rom} {B : ScreenPage.Places} {P : Places} (F : Facts E B P) :
    E.b P.read = 0xB1 ∧ E.b (P.read+1) = P.ptr := by
  have h := F.tile 0 (rowOf P 0 0) 0 (by decide) (row_mem P 0 0)
  simp only [tileCheck,Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.mp h.1.1.1,beq_iff_eq.mp h.1.1.2⟩

/-- The actual addressing-mode read uses the column and row of the entry position. -/
theorem actual_address {E : Rom} {B : ScreenPage.Places} {P : Places} {R T : Machine}
    (F : Facts E B P) (H : ReadAt E B P R T) : ScreenPage.readAddr T = readAddress E B P R := by
  rw [RoomBlocks.readAddr_eq (by rw [H.cut.pc]; exact F.code_bound (by simp [cRead]))]
  have op : RoomBlocks.operand T = P.ptr := by
    unfold RoomBlocks.operand
    rw [H.cut.pc,H.cut.good.prg,H.cut.good.mask]
    exact F.read_meta.2
  rw [op,H.pointer,H.y]
  rfl

theorem read_value {E : Rom} {B : ScreenPage.Places} {P : Places} {R T : Machine}
    (F : Facts E B P) (H : ReadAt E B P R T) :
    ScreenPage.readVal T = T.ram.get! (I (readAddress E B P R)) := by
  have h := F.tile (RoomAddress.selector (R.ram.get! P.pg) (R.ram.get! P.x) (xadd E P R.y))
    (rowOf P (R.ram.get! P.y) (yadd E P R.y)) 0 (RoomAddress.selector_lt ..) (row_mem ..)
  simp only [tileCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have hb : readAddress E B P R < 0x2000 := by
    apply UInt16.lt_iff_toNat_lt.2
    change (readAddress E B P R).toNat < 8192
    have hh := h.1.2
    change (readAddress E B P R).toNat < 2048 at hh
    omega
  rw [RoomBlocks.readVal_eq (by rw [actual_address F H]; exact hb),actual_address F H]
  rfl

/-- At a non-coin map cell, Solid identifies the returned tile with the map byte.
Buffer membership is explicit; arbitrary entry heights need not address the map. -/
theorem returned_map {E : Rom} {B : ScreenPage.Places} {P : Places} {R T Q M : Machine} {cs : List UInt8}
    (ret : Returned E B P R T Q) (solid : RoomBlocks.Solid B cs M T)
    (hl : B.bufLo ≤ I (readAddress E B P R))
    (hr : I (readAddress E B P R) < B.bufLo+B.bufN)
    (nc : M.ram.get! (I (readAddress E B P R)) ∉ cs) :
    Q.a = M.ram.get! (I (readAddress E B P R)) :=
  ret.a.trans (solid _ hl hr nc)

end Smbrta.RoomCollision
