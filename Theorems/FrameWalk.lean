import Theorems.TaintRun

/-!
# A walk over two machines

Two machines at the same place in the code run the same way if they agree on what the code reads. `walkT` follows a piece of code for two machines at once, knowing for each register and byte
only a `Tag`: nothing, the two are the same, both are zero or both are not, or known bits of each. Its cost is small because no value is enumerated. Time is not looked at: an instruction here does not read the clock.
Fed one machine twice, it says which bytes a piece of code leaves alone and what it reaches (`piece_spec`). Fed a real machine and the machine of `runSub`, it says that a routine does the same in both (`leaf_spec`).
Each instruction is proved once (`tstep_spec`). There is no game data in this file. Page: `0-0/0-3-2-FrameModel.md`.
-/

namespace Smbrta.FrameModel

open PipeTransitionAll (go)
open TaintRun (AB bt)

/-! ## One instruction, without its time -/

/-- the ROM -/
structure Rom where
  prg : ByteArray
  mask : UInt16

@[inline] def Rom.b (E : Rom) (a : UInt16) : UInt8 := E.prg.get! (a &&& E.mask).toNat
@[inline] def Rom.w (E : Rom) (a : UInt16) : UInt16 := (E.b a).toUInt16 ||| ((E.b (a + 1)).toUInt16 <<< 8)

/-- a machine without its clock -/
def nt (m : Machine) : Machine := { m with cyc := 0, fdot := 0, frame := 0, vblank := false, sprite0 := false }

/-- what every step keeps, away from the registers of the PPU -/
structure Good (E : Rom) (m : Machine) : Prop where
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  nmi : m.nmiPending = false
  halted : m.halted = false
  trk : m.trk = false
  size : m.ram.size = 2048
  ctl : m.ppuCtrl &&& 0x80 = 0

theorem Good.of_nt {E : Rom} {a b : Machine} (h : nt a = nt b) (g : Good E b) : Good E a where
  prg := (congrArg Machine.prg h).trans g.prg
  mask := (congrArg Machine.prgMask h).trans g.mask
  nmi := (congrArg Machine.nmiPending h).trans g.nmi
  halted := (congrArg Machine.halted h).trans g.halted
  trk := (congrArg Machine.trk h).trans g.trk
  size := (congrArg (fun m => m.ram.size) h).trans g.size
  ctl := by
    have : (nt a).ppuCtrl = (nt b).ppuCtrl := congrArg Machine.ppuCtrl h
    have e : a.ppuCtrl = b.ppuCtrl := this
    rw [e]
    exact g.ctl

theorem nt_tick (c : Nat) {m : Machine} (h1 : m.nmiPending = false) (h2 : m.ppuCtrl &&& 0x80 = 0) : nt (go (tick c) m).2 = nt m := by
  rw [PipeTransitionAll.tick_eq]
  have h3 : ((0 : UInt8) != 0) = false := by decide
  have e1 : ∀ (b : Bool) (n : Machine), n.nmiPending = false → n.ppuCtrl &&& 0x80 = 0 →
      nt (PipeTransitionAll.tick1 b n) = nt n ∧ (PipeTransitionAll.tick1 b n).nmiPending = false ∧ (PipeTransitionAll.tick1 b n).ppuCtrl = n.ppuCtrl := by
    intro b n h4 h5
    cases b
    · exact ⟨rfl, h4, rfl⟩
    · simp only [PipeTransitionAll.tick1, nt, h4, h5, h3, Bool.or_false, if_true]
      exact ⟨trivial, trivial, trivial⟩
  have e2 : ∀ (b : Bool) (n : Machine), nt (PipeTransitionAll.tick2 b n) = nt n ∧ (PipeTransitionAll.tick2 b n).nmiPending = n.nmiPending ∧ (PipeTransitionAll.tick2 b n).ppuCtrl = n.ppuCtrl := by
    intro b n
    cases b <;> exact ⟨rfl, rfl, rfl⟩
  have e3 : ∀ (b : Bool) (n : Machine), nt (PipeTransitionAll.tick3 b n) = nt n ∧ (PipeTransitionAll.tick3 b n).nmiPending = n.nmiPending ∧ (PipeTransitionAll.tick3 b n).ppuCtrl = n.ppuCtrl := by
    intro b n
    cases b <;> exact ⟨rfl, rfl, rfl⟩
  have e4 : ∀ (new len : Nat) (n : Machine), n.nmiPending = false → n.ppuCtrl &&& 0x80 = 0 → nt (PipeTransitionAll.tick4 new len n) = nt n := by
    intro new len n h4 h5
    unfold PipeTransitionAll.tick4
    split
    · split
      · simp only [nt, h4, h5, h3, Bool.or_false]
      · rfl
    · rfl
  show nt (PipeTransitionAll.tick4 _ _ _) = _
  generalize hn0 : ({ m with cyc := m.cyc + c } : Machine) = n0
  have hn0' : nt n0 = nt m := by rw [← hn0]; rfl
  have h6 : n0.nmiPending = false := by rw [← hn0]; exact h1
  have h7 : n0.ppuCtrl &&& 0x80 = 0 := by rw [← hn0]; exact h2
  obtain ⟨a1, a2, a3⟩ := e1 (decide (m.fdot < dotVblSet) && decide (dotVblSet ≤ m.fdot + 3 * c)) n0 h6 h7
  generalize PipeTransitionAll.tick1 _ n0 = n1 at a1 a2 a3 ⊢
  obtain ⟨b1, b2, b3⟩ := e2 (decide (m.fdot < dotVblClr) && decide (dotVblClr ≤ m.fdot + 3 * c)) n1
  generalize PipeTransitionAll.tick2 _ n1 = n2 at b1 b2 b3 ⊢
  obtain ⟨c1, c2, c3⟩ := e3 (decide (m.fdot < dotSpr0) && decide (dotSpr0 ≤ m.fdot + 3 * c)) n2
  generalize PipeTransitionAll.tick3 _ n2 = n3 at c1 c2 c3 ⊢
  rw [e4 _ _ n3 (by rw [c2, b2, a2]) (by rw [c3, b3, a3]; exact h7), c1, b1, a1, hn0']

/-! ### Reading and writing -/

theorem rd_ram {m : Machine} {a : UInt16} (h : a < 0x2000) (ht : m.trk = false) : go (rd a) m = (m.ram.get! (a &&& 0x7FF).toNat, m) := by
  unfold rd go
  rw [if_pos h]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem rd_rom {m : Machine} {a : UInt16} (h : 0x8000 ≤ a) : go (rd a) m = (m.prg.get! (a &&& m.prgMask).toNat, m) := by
  have h1 : ¬ a < 0x2000 := by
    intro h2
    have h3 : (0x8000 : UInt16).toNat ≤ a.toNat := UInt16.le_iff_toNat_le.1 h
    have h4 : a.toNat < (0x2000 : UInt16).toNat := UInt16.lt_iff_toNat_lt.1 h2
    simp at h3 h4
    omega
  unfold rd go
  rw [if_neg h1, if_pos h]
  rfl

theorem wr_ram {m : Machine} {a : UInt16} {v : UInt8} (h : a < 0x2000) (ht : m.trk = false) : go (wr a v) m = ((), { m with ram := m.ram.set! (a &&& 0x7FF).toNat v }) := by
  unfold wr go
  rw [if_pos h]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem fetch_eq {E : Rom} {m : Machine} (g : Good E m) (hp : 0x8000 ≤ m.pc) : go fetch m = (E.b m.pc, { m with pc := m.pc + 1 }) := by
  show go (rd m.pc) { m with pc := m.pc + 1 } = _
  rw [rd_rom hp]
  simp only [Rom.b, g.prg, g.mask]

/-! ### Addressing modes -/

theorem zp_lt (z : UInt8) : z.toUInt16 < 0x2000 := by
  apply UInt16.lt_iff_toNat_lt.2
  have := z.toNat_lt
  simp
  omega

/-- the addressing modes -/
inductive Md | imm | zp | zpx | zpy | abs | abx | aby | izy
  deriving DecidableEq, Repr

/-- the mode of an instruction that reads -/
def Md.r : Md → Mode
  | .imm => mImm | .zp => mZp | .zpx => mZpx | .zpy => mZpy | .abs => mAbs | .abx => mAbxR | .aby => mAbyR | .izy => mIzyR
/-- the mode of an instruction that writes -/
def Md.w : Md → Mode
  | .imm => mImm | .zp => mZp | .zpx => mZpx | .zpy => mZpy | .abs => mAbs | .abx => mAbx | .aby => mAby | .izy => mIzy

/-- the program counter after the operand -/
def Md.adv : Md → UInt16 → UInt16
  | .abs, pc | .abx, pc | .aby, pc => pc + 1 + 1
  | _, pc => pc + 1

/-- a pointer in zero page -/
def ptrAt (m : Machine) (z : UInt8) : UInt16 :=
  (m.ram.get! (z.toUInt16 &&& 0x7FF).toNat).toUInt16 ||| ((m.ram.get! ((z + 1).toUInt16 &&& 0x7FF).toNat).toUInt16 <<< 8)

/-- the address; `m.pc` is at the operand -/
def Md.ea (E : Rom) : Md → Machine → UInt16
  | .imm, m => m.pc
  | .zp, m => (E.b m.pc).toUInt16
  | .zpx, m => (E.b m.pc + m.x).toUInt16
  | .zpy, m => (E.b m.pc + m.y).toUInt16
  | .abs, m => E.w m.pc
  | .abx, m => E.w m.pc + m.x.toUInt16
  | .aby, m => E.w m.pc + m.y.toUInt16
  | .izy, m => ptrAt m (E.b m.pc) + m.y.toUInt16

theorem fetch16_eq {E : Rom} {m : Machine} (g : Good E m) (hp : 0x8000 ≤ m.pc) (hp2 : 0x8000 ≤ m.pc + 1) :
    go fetch16 m = (E.w m.pc, { m with pc := m.pc + 1 + 1 }) := by
  have g1 : Good E { m with pc := m.pc + 1 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  show go (fetch >>= fun lo => fetch >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m = _
  rw [PipeTransitionAll.go_bind, fetch_eq g hp]
  simp only
  rw [PipeTransitionAll.go_bind, fetch_eq g1 hp2]
  rfl

theorem penalty_nt {b e : UInt16} {n : Machine} (h1 : n.nmiPending = false) (h2 : n.ppuCtrl &&& 0x80 = 0) :
    (go (pagePenalty b e) n).1 = () ∧ nt (go (pagePenalty b e) n).2 = nt n := by
  unfold pagePenalty
  split
  · exact ⟨rfl, nt_tick 1 h1 h2⟩
  · exact ⟨rfl, rfl⟩

theorem rd16zp_eq {E : Rom} {m : Machine} (g : Good E m) (z : UInt8) : go (rd16zp z) m = (ptrAt m z, m) := by
  show go (rd z.toUInt16 >>= fun lo => rd (z + 1).toUInt16 >>= fun hi => pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) m = _
  rw [PipeTransitionAll.go_bind, rd_ram (zp_lt z) g.trk]
  simp only
  rw [PipeTransitionAll.go_bind, rd_ram (zp_lt (z + 1)) g.trk]
  rfl

theorem Md.w_spec {E : Rom} {m : Machine} (md : Md) (g : Good E m) (hp : 0x8000 ≤ m.pc) (hp2 : 0x8000 ≤ m.pc + 1) :
    go md.w m = (md.ea E m, { m with pc := md.adv m.pc }) := by
  have g1 : Good E { m with pc := m.pc + 1 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  cases md with
  | imm => rfl
  | zp =>
    show go (fetch >>= fun b => pure b.toUInt16) m = _
    rw [PipeTransitionAll.go_bind, fetch_eq g hp]
    rfl
  | zpx =>
    show go (fetch >>= fun b => get >>= fun n => pure (b + n.x).toUInt16) m = _
    rw [PipeTransitionAll.go_bind, fetch_eq g hp]
    rfl
  | zpy =>
    show go (fetch >>= fun b => get >>= fun n => pure (b + n.y).toUInt16) m = _
    rw [PipeTransitionAll.go_bind, fetch_eq g hp]
    rfl
  | abs =>
    show go fetch16 m = _
    rw [fetch16_eq g hp hp2]
    rfl
  | abx =>
    show go (fetch16 >>= fun b => get >>= fun n => pure (b + n.x.toUInt16)) m = _
    rw [PipeTransitionAll.go_bind, fetch16_eq g hp hp2]
    rfl
  | aby =>
    show go (fetch16 >>= fun b => get >>= fun n => pure (b + n.y.toUInt16)) m = _
    rw [PipeTransitionAll.go_bind, fetch16_eq g hp hp2]
    rfl
  | izy =>
    show go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun n => pure (b + n.y.toUInt16)) m = _
    rw [PipeTransitionAll.go_bind, fetch_eq g hp]
    simp only
    rw [PipeTransitionAll.go_bind, rd16zp_eq g1]
    rfl

theorem penalty_end {b e : UInt16} {n : Machine} (h1 : n.nmiPending = false) (h2 : n.ppuCtrl &&& 0x80 = 0) :
    (go (pagePenalty b e >>= fun _ => pure e) n).1 = e ∧ nt (go (pagePenalty b e >>= fun _ => pure e) n).2 = nt n := by
  rw [PipeTransitionAll.go_bind]
  exact ⟨rfl, (penalty_nt h1 h2).2⟩

theorem Md.r_spec {E : Rom} {m : Machine} (md : Md) (g : Good E m) (hp : 0x8000 ≤ m.pc) (hp2 : 0x8000 ≤ m.pc + 1) :
    (go md.r m).1 = md.ea E m ∧ nt (go md.r m).2 = nt { m with pc := md.adv m.pc } := by
  have g1 : Good E { m with pc := m.pc + 1 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  cases md with
  | imm => rw [show go (Md.r .imm) m = go (Md.w .imm) m from rfl, Md.w_spec .imm g hp hp2]; exact ⟨rfl, rfl⟩
  | zp => rw [show go (Md.r .zp) m = go (Md.w .zp) m from rfl, Md.w_spec .zp g hp hp2]; exact ⟨rfl, rfl⟩
  | zpx => rw [show go (Md.r .zpx) m = go (Md.w .zpx) m from rfl, Md.w_spec .zpx g hp hp2]; exact ⟨rfl, rfl⟩
  | zpy => rw [show go (Md.r .zpy) m = go (Md.w .zpy) m from rfl, Md.w_spec .zpy g hp hp2]; exact ⟨rfl, rfl⟩
  | abs => rw [show go (Md.r .abs) m = go (Md.w .abs) m from rfl, Md.w_spec .abs g hp hp2]; exact ⟨rfl, rfl⟩
  | abx =>
    have key : go (Md.r .abx) m = go (pagePenalty (E.w m.pc) (E.w m.pc + m.x.toUInt16) >>= fun _ => pure (E.w m.pc + m.x.toUInt16)) { m with pc := m.pc + 1 + 1 } := by
      show go (fetch16 >>= fun b => get >>= fun n => pagePenalty b (b + n.x.toUInt16) >>= fun _ => pure (b + n.x.toUInt16)) m = _
      rw [PipeTransitionAll.go_bind, fetch16_eq g hp hp2]
      rfl
    rw [key]
    exact penalty_end g.nmi g.ctl
  | aby =>
    have key : go (Md.r .aby) m = go (pagePenalty (E.w m.pc) (E.w m.pc + m.y.toUInt16) >>= fun _ => pure (E.w m.pc + m.y.toUInt16)) { m with pc := m.pc + 1 + 1 } := by
      show go (fetch16 >>= fun b => get >>= fun n => pagePenalty b (b + n.y.toUInt16) >>= fun _ => pure (b + n.y.toUInt16)) m = _
      rw [PipeTransitionAll.go_bind, fetch16_eq g hp hp2]
      rfl
    rw [key]
    exact penalty_end g.nmi g.ctl
  | izy =>
    have key : go (Md.r .izy) m = go (pagePenalty (ptrAt m (E.b m.pc)) (ptrAt m (E.b m.pc) + m.y.toUInt16) >>= fun _ => pure (ptrAt m (E.b m.pc) + m.y.toUInt16)) { m with pc := m.pc + 1 } := by
      show go (fetch >>= fun z => rd16zp z >>= fun b => get >>= fun n => pagePenalty b (b + n.y.toUInt16) >>= fun _ => pure (b + n.y.toUInt16)) m = _
      rw [PipeTransitionAll.go_bind, fetch_eq g hp]
      simp only
      rw [PipeTransitionAll.go_bind, rd16zp_eq g1]
      rfl
    rw [key]
    exact penalty_end g.nmi g.ctl

/-! ### The instructions -/

/-- flags: `(p, value)` as `setZN` leaves them -/
def znP (p v : UInt8) : UInt8 := (p &&& 0x7D) ||| (if v == 0 then 0x02 else 0) ||| (v &&& 0x80)
def setF (p mask : UInt8) (b : Bool) : UInt8 := if b then p ||| mask else p &&& ~~~mask

/-- `adc`, as a function -/
def adcS (a v p : UInt8) : UInt8 × UInt8 :=
  let s := a.toUInt16 + v.toUInt16 + (p &&& 1).toUInt16
  let r := s.toUInt8
  let ovf := (a ^^^ r) &&& (v ^^^ r) &&& 0x80 != 0
  (r, (p &&& 0x3C) ||| (if s > 0xFF then 0x01 else 0) ||| (if r == 0 then 0x02 else 0) ||| (r &&& 0x80) ||| (if ovf then 0x40 else 0))

/-- instructions that read a byte -/
inductive RF | lda | ldx | ldy | and' | ora | eor | adc | sbc | cmp | cpx | cpy
  deriving DecidableEq, Repr

/-- what an instruction does with the byte it reads -/
def rf : RF → UInt8 → M Unit
  | .lda, v => setA v
  | .ldx, v => setX v
  | .ldy, v => setY v
  | .and', v => andV v
  | .ora, v => oraV v
  | .eor, v => eorV v
  | .adc, v => adc v
  | .sbc, v => adc (~~~v)
  | .cmp, v => do cmpV (← get).a v
  | .cpx, v => do cmpV (← get).x v
  | .cpy, v => do cmpV (← get).y v

def cmpP (p r v : UInt8) : UInt8 := setF (znP p (r - v)) 0x01 (r ≥ v)

/-- the same, as a function of the machine -/
def rfE : RF → UInt8 → Machine → Machine
  | .lda, v, m => { m with a := v, p := znP m.p v }
  | .ldx, v, m => { m with x := v, p := znP m.p v }
  | .ldy, v, m => { m with y := v, p := znP m.p v }
  | .and', v, m => { m with a := m.a &&& v, p := znP m.p (m.a &&& v) }
  | .ora, v, m => { m with a := m.a ||| v, p := znP m.p (m.a ||| v) }
  | .eor, v, m => { m with a := m.a ^^^ v, p := znP m.p (m.a ^^^ v) }
  | .adc, v, m => { m with a := (adcS m.a v m.p).1, p := (adcS m.a v m.p).2 }
  | .sbc, v, m => { m with a := (adcS m.a (~~~v) m.p).1, p := (adcS m.a (~~~v) m.p).2 }
  | .cmp, v, m => { m with p := cmpP m.p m.a v }
  | .cpx, v, m => { m with p := cmpP m.p m.x v }
  | .cpy, v, m => { m with p := cmpP m.p m.y v }

theorem rf_eff (f : RF) (v : UInt8) (n : Machine) : (go (rf f v) n).2 = rfE f v n := by
  cases f <;> rfl

theorem nt_rfE (f : RF) (v : UInt8) (n : Machine) : nt (rfE f v n) = rfE f v (nt n) := by
  cases f <;> rfl

/-- shifts, increments -/
inductive UF | asl | lsr | rol | ror | inc | dec
  deriving DecidableEq, Repr

def uf : UF → UInt8 → M UInt8
  | .asl => aslV
  | .lsr => lsrV
  | .rol => rolV
  | .ror => rorV
  | .inc => incV
  | .dec => decV

/-- the result and the flags -/
def ufS : UF → UInt8 → UInt8 → UInt8 × UInt8
  | .asl, v, p => (v <<< 1, znP (setF p 0x01 (v &&& 0x80 != 0)) (v <<< 1))
  | .lsr, v, p => (v >>> 1, znP (setF p 0x01 (v &&& 1 != 0)) (v >>> 1))
  | .rol, v, p => ((v <<< 1) ||| (p &&& 1), znP (setF p 0x01 (v &&& 0x80 != 0)) ((v <<< 1) ||| (p &&& 1)))
  | .ror, v, p => ((v >>> 1) ||| ((p &&& 1) <<< 7), znP (setF p 0x01 (v &&& 1 != 0)) ((v >>> 1) ||| ((p &&& 1) <<< 7)))
  | .inc, v, p => (v + 1, znP p (v + 1))
  | .dec, v, p => (v - 1, znP p (v - 1))

theorem uf_eff (f : UF) (v : UInt8) (n : Machine) : go (uf f v) n = ((ufS f v n.p).1, { n with p := (ufS f v n.p).2 }) := by
  cases f <;> rfl

/-- instructions that write a register -/
inductive WF | sta | stx | sty
  deriving DecidableEq, Repr

def WF.val : WF → Machine → UInt8
  | .sta, m => m.a
  | .stx, m => m.x
  | .sty, m => m.y

/-- the branches -/
inductive BF | pl | mi | cc | cs | ne | eq
  deriving DecidableEq, Repr

/-- the bit of the flags it looks at -/
def BF.i : BF → Nat
  | .pl | .mi => 7
  | .cc | .cs => 0
  | .ne | .eq => 1

/-- it branches when the bit has this value -/
def BF.set : BF → Bool
  | .pl | .cc | .ne => false
  | .mi | .cs | .eq => true

/-- the instructions the walk knows -/
inductive Ins
  | rd (f : RF) (md : Md)
  | wr (f : WF) (md : Md)
  | rmw (f : UF) (md : Md)
  | acc (f : UF)
  | br (f : BF)
  | jmp | jmpi | jsr | rts | pha | pla | clc | sec | tax | tay | txa | tya | inx | iny | dex | dey
  deriving Repr

def WF.op (f : WF) (md : Mode) : M Unit :=
  match f with
  | .sta => opSTA md
  | .stx => opSTX md
  | .sty => opSTY md

def BF.op : BF → M Unit
  | .pl => opBPL | .mi => opBMI | .cc => opBCC | .cs => opBCS | .ne => opBNE | .eq => opBEQ

/-- what an instruction does, after its opcode was fetched -/
def sem : Ins → M Unit
  | .rd f md => md.r >>= fun a => rd a >>= rf f
  | .wr f md => f.op md.w
  | .rmw f md => rmw (uf f) md.w
  | .acc f => accOp (uf f)
  | .br f => f.op
  | .jmp => opJMP | .jmpi => opJMPi | .jsr => opJSR | .rts => opRTS | .pha => opPHA | .pla => opPLA
  | .clc => opCLC | .sec => opSEC | .tax => opTAX | .tay => opTAY | .txa => opTXA | .tya => opTYA
  | .inx => opINX | .iny => opINY | .dex => opDEX | .dey => opDEY

/-- the opcodes -/
def insList : List (UInt8 × Ins) :=
  [(0xA9, .rd .lda .imm), (0xA5, .rd .lda .zp), (0xB5, .rd .lda .zpx), (0xAD, .rd .lda .abs), (0xBD, .rd .lda .abx), (0xB9, .rd .lda .aby), (0xB1, .rd .lda .izy),
   (0xA2, .rd .ldx .imm), (0xA6, .rd .ldx .zp), (0xB6, .rd .ldx .zpy), (0xAE, .rd .ldx .abs), (0xBE, .rd .ldx .aby),
   (0xA0, .rd .ldy .imm), (0xA4, .rd .ldy .zp), (0xB4, .rd .ldy .zpx), (0xAC, .rd .ldy .abs), (0xBC, .rd .ldy .abx),
   (0x29, .rd .and' .imm), (0x25, .rd .and' .zp), (0x35, .rd .and' .zpx), (0x2D, .rd .and' .abs), (0x3D, .rd .and' .abx), (0x39, .rd .and' .aby), (0x31, .rd .and' .izy),
   (0x09, .rd .ora .imm), (0x05, .rd .ora .zp), (0x15, .rd .ora .zpx), (0x0D, .rd .ora .abs), (0x1D, .rd .ora .abx), (0x19, .rd .ora .aby), (0x11, .rd .ora .izy),
   (0x49, .rd .eor .imm), (0x45, .rd .eor .zp), (0x55, .rd .eor .zpx), (0x4D, .rd .eor .abs), (0x5D, .rd .eor .abx), (0x59, .rd .eor .aby), (0x51, .rd .eor .izy),
   (0x69, .rd .adc .imm), (0x65, .rd .adc .zp), (0x75, .rd .adc .zpx), (0x6D, .rd .adc .abs), (0x7D, .rd .adc .abx), (0x79, .rd .adc .aby), (0x71, .rd .adc .izy),
   (0xE9, .rd .sbc .imm), (0xE5, .rd .sbc .zp), (0xF5, .rd .sbc .zpx), (0xED, .rd .sbc .abs), (0xFD, .rd .sbc .abx), (0xF9, .rd .sbc .aby), (0xF1, .rd .sbc .izy),
   (0xC9, .rd .cmp .imm), (0xC5, .rd .cmp .zp), (0xD5, .rd .cmp .zpx), (0xCD, .rd .cmp .abs), (0xDD, .rd .cmp .abx), (0xD9, .rd .cmp .aby), (0xD1, .rd .cmp .izy),
   (0xE0, .rd .cpx .imm), (0xE4, .rd .cpx .zp), (0xEC, .rd .cpx .abs), (0xC0, .rd .cpy .imm), (0xC4, .rd .cpy .zp), (0xCC, .rd .cpy .abs),
   (0x85, .wr .sta .zp), (0x95, .wr .sta .zpx), (0x8D, .wr .sta .abs), (0x9D, .wr .sta .abx), (0x99, .wr .sta .aby), (0x91, .wr .sta .izy),
   (0x86, .wr .stx .zp), (0x96, .wr .stx .zpy), (0x8E, .wr .stx .abs), (0x84, .wr .sty .zp), (0x94, .wr .sty .zpx), (0x8C, .wr .sty .abs),
   (0x06, .rmw .asl .zp), (0x16, .rmw .asl .zpx), (0x0E, .rmw .asl .abs), (0x1E, .rmw .asl .abx),
   (0x46, .rmw .lsr .zp), (0x56, .rmw .lsr .zpx), (0x4E, .rmw .lsr .abs), (0x5E, .rmw .lsr .abx),
   (0x26, .rmw .rol .zp), (0x36, .rmw .rol .zpx), (0x2E, .rmw .rol .abs), (0x3E, .rmw .rol .abx),
   (0x66, .rmw .ror .zp), (0x76, .rmw .ror .zpx), (0x6E, .rmw .ror .abs), (0x7E, .rmw .ror .abx),
   (0xE6, .rmw .inc .zp), (0xF6, .rmw .inc .zpx), (0xEE, .rmw .inc .abs), (0xFE, .rmw .inc .abx),
   (0xC6, .rmw .dec .zp), (0xD6, .rmw .dec .zpx), (0xCE, .rmw .dec .abs), (0xDE, .rmw .dec .abx),
   (0x0A, .acc .asl), (0x4A, .acc .lsr), (0x2A, .acc .rol), (0x6A, .acc .ror),
   (0x10, .br .pl), (0x30, .br .mi), (0x90, .br .cc), (0xB0, .br .cs), (0xD0, .br .ne), (0xF0, .br .eq),
   (0x4C, .jmp), (0x6C, .jmpi), (0x20, .jsr), (0x60, .rts), (0x48, .pha), (0x68, .pla), (0x18, .clc), (0x38, .sec),
   (0xAA, .tax), (0xA8, .tay), (0x8A, .txa), (0x98, .tya), (0xE8, .inx), (0xC8, .iny), (0xCA, .dex), (0x88, .dey)]

def lookupOp (op : UInt8) : List (UInt8 × Ins) → Option Ins
  | [] => none
  | p :: l => if p.1 == op then some p.2 else lookupOp op l

theorem lookupOp_mem {op : UInt8} {I : Ins} : ∀ {l : List (UInt8 × Ins)}, lookupOp op l = some I → (op, I) ∈ l
  | [], h => by cases h
  | p :: l, h => by
    unfold lookupOp at h
    split at h
    · rename_i h1
      have e : p.1 = op := beq_iff_eq.1 h1
      cases h
      obtain ⟨a, b⟩ := p
      simp only at e
      subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupOp_mem h)

set_option maxRecDepth 100000 in
/-- the table of opcodes agrees -/
theorem sem_table : ∀ p ∈ insList, opTable[p.1.toNat]?.getD opJAM = sem p.2 := by
  simp only [insList, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  and_intros <;> rfl

/-! ## Flags -/

open TaintRun (bt_and bt_or bt_ext ne_zero_of_bit bt_zero mem_known_self known_eq mem_top isK_eq mem_and mem_or mem_xor mem_not mem_map1 TR TR_bit TR_isZero)

theorem bit_lits : ∀ i : Fin 8, bt 1 i.1 = decide (i.1 = 0) ∧ bt 2 i.1 = decide (i.1 = 1) ∧ bt 0x80 i.1 = decide (i.1 = 7) := by decide

theorem and_bit {x m : UInt8} {i : Nat} (hi : i < 8) (hm : ∀ j, j < 8 → bt m j = decide (j = i)) : (x &&& m != 0) = bt x i := by
  cases h : bt x i with
  | true =>
    have h2 : x &&& m ≠ 0 := ne_zero_of_bit (i := i) (by rw [bt_and, h, hm i hi]; simp)
    exact bne_iff_ne.2 h2
  | false =>
    have h2 : x &&& m = 0 := bt_ext (fun j hj => by
      rw [bt_and, hm j hj, bt_zero hj]
      by_cases hji : j = i
      · subst hji
        simp [h]
      · simp [hji])
    rw [h2]
    decide

theorem and1 (x : UInt8) : (x &&& 1 != 0) = bt x 0 := and_bit (by decide) fun j hj => (bit_lits ⟨j, hj⟩).1
theorem and2 (x : UInt8) : (x &&& 2 != 0) = bt x 1 := and_bit (by decide) fun j hj => (bit_lits ⟨j, hj⟩).2.1
theorem and80 (x : UInt8) : (x &&& 0x80 != 0) = bt x 7 := and_bit (by decide) fun j hj => (bit_lits ⟨j, hj⟩).2.2

theorem not_ne {a b : UInt8} : (a == b) = !(a != b) := by
  cases h : a == b <;> simp [bne, h]

/-- the low bit as a byte -/
def cB (c : Bool) : UInt8 := if c then 1 else 0

theorem and1_eq (x : UInt8) : x &&& 1 = cB (bt x 0) := by
  apply bt_ext
  intro j hj
  rw [bt_and, (bit_lits ⟨j, hj⟩).1]
  cases h : bt x 0
  · have e : bt (cB false) j = false := by show bt 0 j = false; exact bt_zero hj
    rw [e]
    by_cases hj0 : j = 0
    · subst hj0
      simp [h]
    · simp [hj0]
  · have e : bt (cB true) j = decide (j = 0) := (bit_lits ⟨j, hj⟩).1
    rw [e]
    by_cases hj0 : j = 0
    · subst hj0
      simp [h]
    · simp [hj0]

theorem znP_c (p v : UInt8) : bt (znP p v) 0 = bt p 0 := by
  unfold znP
  rw [bt_or, bt_or, bt_and, bt_and, show bt 0x7D 0 = true by decide, show bt 0x80 0 = false by decide]
  split <;> simp [show bt 2 0 = false by decide, show bt 0 0 = false by decide]

theorem znP_z (p v : UInt8) : bt (znP p v) 1 = (v == 0) := by
  unfold znP
  rw [bt_or, bt_or, bt_and, bt_and, show bt 0x7D 1 = false by decide, show bt 0x80 1 = false by decide]
  split
  · rename_i h
    simp [h, show bt 2 1 = true by decide]
  · rename_i h
    simp [h, show bt 0 1 = false by decide]

theorem znP_n (p v : UInt8) : bt (znP p v) 7 = (v &&& 0x80 != 0) := by
  rw [and80]
  unfold znP
  rw [bt_or, bt_or, bt_and, bt_and, show bt 0x7D 7 = false by decide, show bt 0x80 7 = true by decide]
  split <;> simp [show bt 2 7 = false by decide, show bt 0 7 = false by decide]

theorem setF_c (p : UInt8) (b : Bool) : bt (setF p 0x01 b) 0 = b := by
  unfold setF
  cases b
  · have h := TaintRun.bt_not (1 : UInt8) 0 (by decide)
    simp only [Bool.false_eq_true, if_false]
    rw [bt_and, h, show bt 1 0 = true by decide]
    simp
  · simp only [if_true]
    rw [bt_or, show bt 1 0 = true by decide]
    simp

theorem setF_o (p : UInt8) (b : Bool) {i : Nat} (hi : i < 8) (h0 : i ≠ 0) : bt (setF p 0x01 b) i = bt p i := by
  have e1 : bt 1 i = false := by
    rw [(bit_lits ⟨i, hi⟩).1]
    simp [h0]
  unfold setF
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [bt_and, TaintRun.bt_not 1 i hi, e1]
    simp
  · simp only [if_true]
    rw [bt_or, e1]
    simp

/-- addition with carry -/
def adcC (a v : UInt8) (c : Bool) : UInt8 × Bool :=
  let s := a.toUInt16 + v.toUInt16 + (cB c).toUInt16
  (s.toUInt8, decide (s > 0xFF))

theorem adcS_r (a v p : UInt8) : (adcS a v p).1 = (adcC a v (bt p 0)).1 := by
  simp only [adcS, adcC, and1_eq]

theorem adcS_c (a v p : UInt8) : bt (adcS a v p).2 0 = (adcC a v (bt p 0)).2 := by
  simp only [adcS, adcC, and1_eq]
  rw [bt_or, bt_or, bt_or, bt_or, bt_and, bt_and, show bt 0x3C 0 = false by decide, show bt 0x80 0 = false by decide]
  have e1 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x40 : UInt8) else 0) 0 = false := by
    intro c _
    split <;> decide
  have e2 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x02 : UInt8) else 0) 0 = false := by
    intro c _
    split <;> decide
  have e3 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x01 : UInt8) else 0) 0 = decide c := by
    intro c _
    split
    · rename_i h
      simp only [h, decide_true]
      decide
    · rename_i h
      simp only [h, decide_false]
      decide
  rw [e1, e2, e3]
  simp

theorem dec_beq (x : UInt8) : decide (x = 0) = (x == 0) := by
  cases h : x == 0 <;> simp_all

theorem adcS_z (a v p : UInt8) : bt (adcS a v p).2 1 = ((adcC a v (bt p 0)).1 == 0) := by
  simp only [adcS, adcC, and1_eq]
  rw [bt_or, bt_or, bt_or, bt_or, bt_and, bt_and, show bt 0x3C 1 = false by decide, show bt 0x80 1 = false by decide]
  have e1 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x40 : UInt8) else 0) 1 = false := by
    intro c _
    split <;> decide
  have e2 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x01 : UInt8) else 0) 1 = false := by
    intro c _
    split <;> decide
  have e3 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x02 : UInt8) else 0) 1 = decide c := by
    intro c _
    split
    · rename_i h
      simp only [h, decide_true]
      decide
    · rename_i h
      simp only [h, decide_false]
      decide
  rw [e1, e2, e3]
  simp
  exact dec_beq _

theorem adcS_n (a v p : UInt8) : bt (adcS a v p).2 7 = ((adcC a v (bt p 0)).1 &&& 0x80 != 0) := by
  rw [and80]
  simp only [adcS, adcC, and1_eq]
  rw [bt_or, bt_or, bt_or, bt_or, bt_and, bt_and, show bt 0x3C 7 = false by decide, show bt 0x80 7 = true by decide]
  have e1 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x40 : UInt8) else 0) 7 = false := by
    intro c _
    split <;> decide
  have e2 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x01 : UInt8) else 0) 7 = false := by
    intro c _
    split <;> decide
  have e3 : ∀ c : Prop, ∀ [Decidable c], bt (if c then (0x02 : UInt8) else 0) 7 = false := by
    intro c _
    split <;> decide
  rw [e1, e2, e3]
  simp

/-- shifts and increments -/
def ufC : UF → UInt8 → Bool → UInt8 × Bool
  | .asl, v, _ => (v <<< 1, v &&& 0x80 != 0)
  | .lsr, v, _ => (v >>> 1, v &&& 1 != 0)
  | .rol, v, c => ((v <<< 1) ||| cB c, v &&& 0x80 != 0)
  | .ror, v, c => ((v >>> 1) ||| (cB c <<< 7), v &&& 1 != 0)
  | .inc, v, c => (v + 1, c)
  | .dec, v, c => (v - 1, c)

theorem ufS_r (f : UF) (v p : UInt8) : (ufS f v p).1 = (ufC f v (bt p 0)).1 := by
  cases f <;> simp only [ufS, ufC, and1_eq]

theorem ufS_c (f : UF) (v p : UInt8) : bt (ufS f v p).2 0 = (ufC f v (bt p 0)).2 := by
  cases f <;> simp only [ufS, ufC, znP_c, setF_c]

theorem ufS_z (f : UF) (v p : UInt8) : bt (ufS f v p).2 1 = ((ufC f v (bt p 0)).1 == 0) := by
  cases f <;> simp only [ufS, ufC, znP_z, and1_eq]

theorem ufS_n (f : UF) (v p : UInt8) : bt (ufS f v p).2 7 = ((ufC f v (bt p 0)).1 &&& 0x80 != 0) := by
  cases f <;> simp only [ufS, ufC, znP_n, and1_eq]

/-- compare: carry, zero, negative -/
theorem cmpP_c (p r v : UInt8) : bt (cmpP p r v) 0 = decide (r ≥ v) := setF_c _ _
theorem cmpP_z (p r v : UInt8) : bt (cmpP p r v) 1 = (r - v == 0) := by
  unfold cmpP
  rw [setF_o _ _ (by decide) (by decide), znP_z]
theorem cmpP_n (p r v : UInt8) : bt (cmpP p r v) 7 = ((r - v) &&& 0x80 != 0) := by
  unfold cmpP
  rw [setF_o _ _ (by decide) (by decide), znP_n]

/-! ## What a walk knows of two machines -/

/-- what is known of a byte of the two machines -/
inductive Tag
  | any
  /-- the same -/
  | eq
  /-- both zero or both not -/
  | nz
  /-- known bits of each -/
  | ab (a b : AB)
  deriving Inhabited

def Tag.R : Tag → UInt8 → UInt8 → Prop
  | .any, _, _ => True
  | .eq, x, y => x = y
  | .nz, x, y => (x = 0 ↔ y = 0)
  | .ab a b, x, y => a.mem x ∧ b.mem y

/-- both known -/
abbrev Tag.kn (x y : UInt8) : Tag := .ab (AB.known x) (AB.known y)

theorem Tag.R_kn (x y : UInt8) : (Tag.kn x y).R x y := ⟨mem_known_self x, mem_known_self y⟩

/-- the two are surely the same -/
def Tag.eqL : Tag → Bool
  | .eq => true
  | .ab a b => a.isK && b.isK && a.v == b.v
  | _ => false

theorem Tag.eqL_spec {t : Tag} {x y : UInt8} (he : t.eqL = true) (h : t.R x y) : x = y := by
  cases t with
  | eq => exact h
  | ab a b =>
    simp only [Tag.eqL, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨h1, h2⟩, h3⟩ := he
    rw [isK_eq h1 h.1, isK_eq h2 h.2, h3]
  | any => cases he
  | nz => cases he

/-- both values, if known -/
def Tag.exact : Tag → Option (UInt8 × UInt8)
  | .ab a b => if a.isK && b.isK then some (a.v, b.v) else none
  | _ => none

theorem Tag.exact_spec {t : Tag} {x y u v : UInt8} (he : t.exact = some (u, v)) (h : t.R x y) : x = u ∧ y = v := by
  cases t with
  | ab a b =>
    simp only [Tag.exact] at he
    split at he
    · rename_i h1
      simp only [Bool.and_eq_true] at h1
      cases he
      exact ⟨isK_eq h1.1 h.1, isK_eq h1.2 h.2⟩
    · cases he
  | any => cases he
  | eq => cases he
  | nz => cases he

/-- one value, the same in both -/
def Tag.same (t : Tag) : Option UInt8 :=
  match t.exact with
  | some (u, v) => if u == v then some u else none
  | none => none

theorem Tag.same_spec {t : Tag} {x y u : UInt8} (he : t.same = some u) (h : t.R x y) : x = u ∧ y = u := by
  cases h1 : t.exact with
  | none => simp [Tag.same, h1] at he
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only [Tag.same, h1] at he
    split at he
    · rename_i h2
      have e : a = u := Option.some.inj he
      obtain ⟨h3, h4⟩ := t.exact_spec h1 h
      have h5 : a = b := beq_iff_eq.1 h2
      exact ⟨by rw [h3, e], by rw [h4, ← h5, e]⟩
    · cases he

/-- what is known of a flag -/
inductive FT
  | any
  | eq
  | kn (b c : Bool)
  deriving Inhabited

def FT.R : FT → Bool → Bool → Prop
  | .any, _, _ => True
  | .eq, x, y => x = y
  | .kn b c, x, y => x = b ∧ y = c

def FT.eqL : FT → Bool
  | .eq => true
  | .kn b c => b == c
  | .any => false

theorem FT.eqL_spec {t : FT} {x y : Bool} (he : t.eqL = true) (h : t.R x y) : x = y := by
  cases t with
  | eq => exact h
  | kn b c =>
    have e : b = c := beq_iff_eq.1 he
    rw [h.1, h.2, e]
  | any => cases he

/-- the zero flag from a tag -/
def zT : Tag → FT
  | .eq | .nz => .eq
  | .ab a b =>
    match a.isZero, b.isZero with
    | some u, some v => .kn u v
    | _, _ => .any
  | .any => .any

theorem zT_R {t : Tag} {x y : UInt8} (h : t.R x y) : (zT t).R (x == 0) (y == 0) := by
  cases t with
  | any => trivial
  | eq => cases h; rfl
  | nz =>
    show (x == 0) = (y == 0)
    have h1 : x = 0 ↔ y = 0 := h
    cases hx : x == 0 <;> cases hy : y == 0
    · rfl
    · exact absurd (h1.2 (beq_iff_eq.1 hy)) (by simp at hx; exact hx)
    · exact absurd (h1.1 (beq_iff_eq.1 hx)) (by simp at hy; exact hy)
    · rfl
  | ab a b =>
    show (match a.isZero, b.isZero with
      | some u, some v => FT.kn u v
      | _, _ => FT.any).R _ _
    split
    · rename_i h1 h2
      rcases TR_isZero h.1 with h3 | h3
      · rw [h3] at h1; cases h1
      · rcases TR_isZero h.2 with h4 | h4
        · rw [h4] at h2; cases h2
        · rw [h1] at h3
          rw [h2] at h4
          simp only [Option.some.injEq] at h3 h4
          exact ⟨h3.symm, h4.symm⟩
    · trivial

/-- the negative flag from a tag -/
def nT : Tag → FT
  | .eq => .eq
  | .ab a b =>
    match a.bit 0x80, b.bit 0x80 with
    | some u, some v => .kn u v
    | _, _ => .any
  | _ => .any

theorem nT_R {t : Tag} {x y : UInt8} (h : t.R x y) : (nT t).R (x &&& 0x80 != 0) (y &&& 0x80 != 0) := by
  cases t with
  | any => trivial
  | eq => cases h; rfl
  | nz => trivial
  | ab a b =>
    show (match a.bit 0x80, b.bit 0x80 with
      | some u, some v => FT.kn u v
      | _, _ => FT.any).R _ _
    split
    · rename_i h1 h2
      rcases TR_bit 0x80 h.1 with h3 | h3
      · rw [h3] at h1; cases h1
      · rcases TR_bit 0x80 h.2 with h4 | h4
        · rw [h4] at h2; cases h2
        · rw [h1] at h3
          rw [h2] at h4
          simp only [Option.some.injEq] at h3 h4
          exact ⟨h3.symm, h4.symm⟩
    · trivial

/-- a bitwise operation on tags -/
def binT (op : AB → AB → AB) (t u : Tag) : Tag :=
  match t, u with
  | .ab a b, .ab c d => .ab (op a c) (op b d)
  | _, _ => if t.eqL && u.eqL then .eq else .any

theorem binT_R {op : AB → AB → AB} {f : UInt8 → UInt8 → UInt8} (hop : ∀ a b x y, AB.mem a x → AB.mem b y → (op a b).mem (f x y))
    {t u : Tag} {x y x' y' : UInt8} (h1 : t.R x x') (h2 : u.R y y') : (binT op t u).R (f x y) (f x' y') := by
  have gen : (if t.eqL && u.eqL then Tag.eq else Tag.any).R (f x y) (f x' y') := by
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      show f x y = f x' y'
      rw [t.eqL_spec h.1 h1, u.eqL_spec h.2 h2]
    · trivial
  cases t <;> cases u <;> first | exact gen | exact ⟨hop _ _ _ _ h1.1 h2.1, hop _ _ _ _ h1.2 h2.2⟩

/-- the complement -/
def notT : Tag → Tag
  | .eq => .eq
  | .ab a b => .ab a.not b.not
  | _ => .any

theorem notT_R {t : Tag} {x y : UInt8} (h : t.R x y) : (notT t).R (~~~x) (~~~y) := by
  cases t with
  | any => trivial
  | eq => cases h; rfl
  | nz => trivial
  | ab a b => exact ⟨mem_not h.1, mem_not h.2⟩

/-- what an addition gives: result, carry, zero, negative -/
structure Alu where
  r : Tag
  c : FT
  z : FT
  n : FT

def adcG (t u : Tag) (c : FT) : Alu :=
  if t.eqL && u.eqL && c.eqL then { r := .eq, c := .eq, z := .eq, n := .eq } else { r := .any, c := .any, z := .any, n := .any }

def adcT (t u : Tag) (c : FT) : Alu :=
  match t.exact, u.exact, c with
  | some (x, x'), some (y, y'), .kn b b' =>
    let r := adcC x y b
    let r' := adcC x' y' b'
    { r := Tag.kn r.1 r'.1, c := .kn r.2 r'.2, z := .kn (r.1 == 0) (r'.1 == 0), n := .kn (r.1 &&& 0x80 != 0) (r'.1 &&& 0x80 != 0) }
  | _, _, _ => adcG t u c

/-- the four facts about results of a function of the inputs -/
structure AluR (A : Alu) (r r' : UInt8) (c c' : Bool) : Prop where
  r_ : A.r.R r r'
  c_ : A.c.R c c'
  z_ : A.z.R (r == 0) (r' == 0)
  n_ : A.n.R (r &&& 0x80 != 0) (r' &&& 0x80 != 0)

theorem adcT_R {t u : Tag} {cf : FT} {x x' y y' : UInt8} {b b' : Bool} (h1 : t.R x x') (h2 : u.R y y') (h3 : cf.R b b') :
    AluR (adcT t u cf) (adcC x y b).1 (adcC x' y' b').1 (adcC x y b).2 (adcC x' y' b').2 := by
  have gen : AluR (adcG t u cf) (adcC x y b).1 (adcC x' y' b').1 (adcC x y b).2 (adcC x' y' b').2 := by
    unfold adcG
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      rw [t.eqL_spec h.1.1 h1, u.eqL_spec h.1.2 h2, cf.eqL_spec h.2 h3]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨trivial, trivial, trivial, trivial⟩
  unfold adcT
  rcases he1 : t.exact with _ | ⟨a, a'⟩
  · exact gen
  rcases he2 : u.exact with _ | ⟨e, e'⟩
  · exact gen
  cases cf with
  | any => exact gen
  | eq => exact gen
  | kn c c' =>
    obtain ⟨e1, e2⟩ := t.exact_spec he1 h1
    obtain ⟨e3, e4⟩ := u.exact_spec he2 h2
    obtain ⟨e5, e6⟩ := h3
    subst e1 e2 e3 e4 e5 e6
    exact ⟨Tag.R_kn _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- what a compare gives; the result is not used -/
def cmpT (t u : Tag) : Alu :=
  match t.exact, u.exact with
  | some (x, x'), some (y, y') =>
    { r := .any, c := .kn (decide (x ≥ y)) (decide (x' ≥ y')), z := .kn (x - y == 0) (x' - y' == 0), n := .kn ((x - y) &&& 0x80 != 0) ((x' - y') &&& 0x80 != 0) }
  | _, _ =>
    if t.eqL && u.eqL then { r := .any, c := .eq, z := .eq, n := .eq } else { r := .any, c := .any, z := .any, n := .any }

theorem cmpT_R {t u : Tag} {x x' y y' : UInt8} (h1 : t.R x x') (h2 : u.R y y') :
    AluR (cmpT t u) (x - y) (x' - y') (decide (x ≥ y)) (decide (x' ≥ y')) := by
  unfold cmpT
  split
  · rename_i a a' e e' h4 h5
    obtain ⟨e1, e2⟩ := t.exact_spec h4 h1
    obtain ⟨e3, e4⟩ := u.exact_spec h5 h2
    subst e1 e2 e3 e4
    exact ⟨trivial, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      rw [t.eqL_spec h.1 h1, u.eqL_spec h.2 h2]
      exact ⟨trivial, rfl, rfl, rfl⟩
    · exact ⟨trivial, trivial, trivial, trivial⟩

/-- what a shift or an increment gives -/
def ufG (f : UF) (t : Tag) (c : FT) : Alu :=
  match f with
  | .asl | .lsr => if t.eqL then { r := .eq, c := .eq, z := .eq, n := .eq } else { r := .any, c := .any, z := .any, n := .any }
  | .inc | .dec => if t.eqL then { r := .eq, c := c, z := .eq, n := .eq } else { r := .any, c := c, z := .any, n := .any }
  | .rol | .ror => if t.eqL && c.eqL then { r := .eq, c := .eq, z := .eq, n := .eq } else { r := .any, c := .any, z := .any, n := .any }

/-- from known values -/
def ufX (f : UF) (x x' : UInt8) (b b' : Bool) : Alu :=
  let r := ufC f x b
  let r' := ufC f x' b'
  { r := Tag.kn r.1 r'.1, c := .kn r.2 r'.2, z := .kn (r.1 == 0) (r'.1 == 0), n := .kn (r.1 &&& 0x80 != 0) (r'.1 &&& 0x80 != 0) }

def ufT (f : UF) (t : Tag) (c : FT) : Alu :=
  match t.exact with
  | none => ufG f t c
  | some (x, x') =>
    match f with
    | .asl | .lsr => ufX f x x' false false
    | .inc | .dec => { ufX f x x' false false with c := c }
    | .rol | .ror =>
      match c with
      | .kn b b' => ufX f x x' b b'
      | _ => ufG f t c

theorem ufT_R {f : UF} {t : Tag} {cf : FT} {x x' : UInt8} {b b' : Bool} (h1 : t.R x x') (h3 : cf.R b b') :
    AluR (ufT f t cf) (ufC f x b).1 (ufC f x' b').1 (ufC f x b).2 (ufC f x' b').2 := by
  have gen : AluR (ufG f t cf) (ufC f x b).1 (ufC f x' b').1 (ufC f x b).2 (ufC f x' b').2 := by
    unfold ufG
    cases f with
    | asl =>
      simp only
      split
      · rename_i h
        rw [t.eqL_spec h h1]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨trivial, trivial, trivial, trivial⟩
    | lsr =>
      simp only
      split
      · rename_i h
        rw [t.eqL_spec h h1]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨trivial, trivial, trivial, trivial⟩
    | inc =>
      simp only
      split
      · rename_i h
        rw [t.eqL_spec h h1]
        exact ⟨rfl, h3, rfl, rfl⟩
      · exact ⟨trivial, h3, trivial, trivial⟩
    | dec =>
      simp only
      split
      · rename_i h
        rw [t.eqL_spec h h1]
        exact ⟨rfl, h3, rfl, rfl⟩
      · exact ⟨trivial, h3, trivial, trivial⟩
    | rol =>
      simp only
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        rw [t.eqL_spec h.1 h1, cf.eqL_spec h.2 h3]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨trivial, trivial, trivial, trivial⟩
    | ror =>
      simp only
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        rw [t.eqL_spec h.1 h1, cf.eqL_spec h.2 h3]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨trivial, trivial, trivial, trivial⟩
  have hx : ∀ {a a' : UInt8}, t.exact = some (a, a') → x = a ∧ x' = a' := fun h => t.exact_spec h h1
  unfold ufT
  rcases he1 : t.exact with _ | ⟨a, a'⟩
  · exact gen
  obtain ⟨e1, e2⟩ := hx he1
  subst e1 e2
  cases f with
  | asl => exact ⟨Tag.R_kn _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | lsr => exact ⟨Tag.R_kn _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | inc => exact ⟨Tag.R_kn _ _, h3, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | dec => exact ⟨Tag.R_kn _ _, h3, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | rol =>
    cases cf with
    | any => exact gen
    | eq => exact gen
    | kn c c' =>
      obtain ⟨e5, e6⟩ := h3
      subst e5 e6
      exact ⟨Tag.R_kn _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  | ror =>
    cases cf with
    | any => exact gen
    | eq => exact gen
    | kn c c' =>
      obtain ⟨e5, e6⟩ := h3
      subst e5 e6
      exact ⟨Tag.R_kn _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## The walk -/

/-- what a walk knows of two machines at the same place -/
structure TS where
  pc : UInt16
  a : Tag
  x : Tag
  y : Tag
  c : FT
  z : FT
  n : FT
  /-- the stack pointer, if known and the same in both -/
  s : Option UInt8
  ram : Nat → Tag
  /-- the bytes that may have been written since the start -/
  w : Nat → Bool

/-- the registers -/
structure Regs (Q : TS) (m n : Machine) : Prop where
  a : Q.a.R m.a n.a
  x : Q.x.R m.x n.x
  y : Q.y.R m.y n.y
  c : Q.c.R (bt m.p 0) (bt n.p 0)
  z : Q.z.R (bt m.p 1) (bt n.p 1)
  nf : Q.n.R (bt m.p 7) (bt n.p 7)

/-- `Q` holds of `m` and `n`, which started as `m₀` and `n₀` -/
structure Lk (E : Rom) (m₀ n₀ : Machine) (Q : TS) (m n : Machine) : Prop where
  gl : Good E m
  gr : Good E n
  pcl : m.pc = Q.pc
  pcr : n.pc = Q.pc
  regs : Regs Q m n
  s : ∀ v, Q.s = some v → m.s = v ∧ n.s = v
  /-- with no known stack pointer, no instruction moved it -/
  s0 : Q.s = none → m.s = m₀.s ∧ n.s = n₀.s
  ram : ∀ i, i < 2048 → (Q.ram i).R (m.ram.get! i) (n.ram.get! i)
  fixl : ∀ i, i < 2048 → Q.w i = false → m.ram.get! i = m₀.ram.get! i
  fixr : ∀ i, i < 2048 → Q.w i = false → n.ram.get! i = n₀.ram.get! i

section walk
variable {E : Rom} {m₀ n₀ : Machine} {Q : TS} {m n : Machine}

theorem Lk.of_nt {a b : Machine} (h : Lk E m₀ n₀ Q m n) (h1 : nt a = nt m) (h2 : nt b = nt n) : Lk E m₀ n₀ Q a b := by
  have ea : ∀ {u v : Machine} (_ : nt u = nt v), u.a = v.a ∧ u.x = v.x ∧ u.y = v.y ∧ u.p = v.p ∧ u.pc = v.pc ∧ u.s = v.s ∧ u.ram = v.ram := by
    intro u v e
    exact ⟨(congrArg Machine.a e : (nt u).a = (nt v).a), (congrArg Machine.x e : (nt u).x = (nt v).x), (congrArg Machine.y e : (nt u).y = (nt v).y),
      (congrArg Machine.p e : (nt u).p = (nt v).p), (congrArg Machine.pc e : (nt u).pc = (nt v).pc), (congrArg Machine.s e : (nt u).s = (nt v).s),
      (congrArg Machine.ram e : (nt u).ram = (nt v).ram)⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ea h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := ea h2
  refine ⟨Good.of_nt h1 h.gl, Good.of_nt h2 h.gr, by rw [a5]; exact h.pcl, by rw [b5]; exact h.pcr, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, b1]; exact h.regs.a
  · rw [a2, b2]; exact h.regs.x
  · rw [a3, b3]; exact h.regs.y
  · rw [a4, b4]; exact h.regs.c
  · rw [a4, b4]; exact h.regs.z
  · rw [a4, b4]; exact h.regs.nf
  · intro v hv
    rw [a6, b6]
    exact h.s v hv
  · intro hv
    rw [a6, b6]
    exact h.s0 hv
  · intro i hi
    rw [a7, b7]
    exact h.ram i hi
  · intro i hi hw
    rw [a7]
    exact h.fixl i hi hw
  · intro i hi hw
    rw [b7]
    exact h.fixr i hi hw

/-- the byte at an address in RAM or ROM -/
def memv (E : Rom) (m : Machine) (a : UInt16) : UInt8 := if a < 0x2000 then m.ram.get! (a &&& 0x7FF).toNat else E.b a

/-- an address of RAM or ROM -/
def okAd (a : UInt16) : Prop := a < 0x2000 ∨ 0x8000 ≤ a

theorem rd_ok {a : UInt16} (g : Good E m) (h : okAd a) : go (rd a) m = (memv E m a, m) := by
  rcases h with h | h
  · rw [rd_ram h g.trk]
    simp only [memv, if_pos h]
  · have h1 : ¬ a < 0x2000 := by
      intro h2
      have h3 : (0x8000 : UInt16).toNat ≤ a.toNat := UInt16.le_iff_toNat_le.1 h
      have h4 : a.toNat < (0x2000 : UInt16).toNat := UInt16.lt_iff_toNat_lt.1 h2
      simp at h3 h4
      omega
    rw [rd_rom h]
    simp only [memv, if_neg h1, Rom.b, g.prg, g.mask]

/-- what is known of the byte at an address -/
def memT (E : Rom) (Q : TS) (a : UInt16) : Option Tag :=
  if a < 0x2000 then some (Q.ram (a &&& 0x7FF).toNat)
  else if 0x8000 ≤ a then some (Tag.kn (E.b a) (E.b a))
  else none

theorem memT_spec {a : UInt16} {t : Tag} (h : Lk E m₀ n₀ Q m n) (he : memT E Q a = some t) : okAd a ∧ t.R (memv E m a) (memv E n a) := by
  unfold memT at he
  split at he
  · rename_i h1
    have e := Option.some.inj he
    subst e
    refine ⟨Or.inl h1, ?_⟩
    simp only [memv, if_pos h1]
    exact h.ram _ (PipeTransitionAll.mask_lt a)
  · rename_i h1
    split at he
    · rename_i h2
      have e := Option.some.inj he
      subst e
      refine ⟨Or.inr h2, ?_⟩
      simp only [memv, if_neg h1]
      exact Tag.R_kn _ _
    · cases he

/-- an index into ROM cannot leave it -/
def romSafe (b : UInt16) : Bool := decide (0x8000 ≤ b) && decide (b.toNat + 255 < 65536)

theorem romSafe_add {b : UInt16} (h : romSafe b = true) (c : UInt8) : 0x8000 ≤ b + c.toUInt16 := by
  simp only [romSafe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  apply UInt16.le_iff_toNat_le.2
  have h3 : (0x8000 : UInt16).toNat ≤ b.toNat := UInt16.le_iff_toNat_le.1 h1
  have h4 : c.toUInt16.toNat = c.toNat := by simp
  have h5 := c.toNat_lt
  rw [UInt16.toNat_add, h4, Nat.mod_eq_of_lt (by omega)]
  omega

/-- an index with a known value, or with the same value in ROM -/
def idxT (E : Rom) (Q : TS) (b : UInt16) (t : Tag) : Option Tag :=
  match t.same with
  | some c => memT E Q (b + c.toUInt16)
  | none => if t.eqL && romSafe b then some .eq else none

theorem idxT_spec {b : UInt16} {t u : Tag} {i j : UInt8} (h : Lk E m₀ n₀ Q m n) (hi : t.R i j) (he : idxT E Q b t = some u) :
    b + i.toUInt16 = b + j.toUInt16 ∧ okAd (b + i.toUInt16) ∧ u.R (memv E m (b + i.toUInt16)) (memv E n (b + i.toUInt16)) := by
  unfold idxT at he
  cases hs : t.same with
  | some c =>
    rw [hs] at he
    obtain ⟨e1, e2⟩ := t.same_spec hs hi
    subst e1 e2
    exact ⟨rfl, memT_spec h he⟩
  | none =>
    rw [hs] at he
    simp only at he
    split at he
    · rename_i h1
      simp only [Bool.and_eq_true] at h1
      have e := Option.some.inj he
      subst e
      have e2 := t.eqL_spec h1.1 hi
      subst e2
      have h2 := romSafe_add h1.2 i
      have h3 : ¬ b + i.toUInt16 < 0x2000 := by
        intro h4
        have h5 : (0x8000 : UInt16).toNat ≤ (b + i.toUInt16).toNat := UInt16.le_iff_toNat_le.1 h2
        have h6 : (b + i.toUInt16).toNat < (0x2000 : UInt16).toNat := UInt16.lt_iff_toNat_lt.1 h4
        simp at h5 h6
        omega
      refine ⟨rfl, Or.inr h2, ?_⟩
      show memv E m _ = memv E n _
      simp only [memv, if_neg h3]
    · cases he

/-- a pointer in zero page, if known -/
def ptrT (Q : TS) (z : UInt8) : Option UInt16 :=
  match (Q.ram (z.toUInt16 &&& 0x7FF).toNat).same, (Q.ram ((z + 1).toUInt16 &&& 0x7FF).toNat).same with
  | some lo, some hi => some (lo.toUInt16 ||| (hi.toUInt16 <<< 8))
  | _, _ => none

theorem ptrT_spec {z : UInt8} {p : UInt16} (h : Lk E m₀ n₀ Q m n) (he : ptrT Q z = some p) : ptrAt m z = p ∧ ptrAt n z = p := by
  unfold ptrT at he
  split at he
  · rename_i lo hi h1 h2
    have e := Option.some.inj he
    subst e
    obtain ⟨a1, a2⟩ := Tag.same_spec h1 (h.ram _ (PipeTransitionAll.mask_lt _))
    obtain ⟨b1, b2⟩ := Tag.same_spec h2 (h.ram _ (PipeTransitionAll.mask_lt _))
    simp only [ptrAt, a1, a2, b1, b2, and_self]
  · cases he

/-- what is known of the byte an instruction reads. The address is the same in both. -/
def srcT (E : Rom) (Q : TS) : Md → Option Tag
  | .imm => memT E Q (Q.pc + 1)
  | .zp => memT E Q (E.b (Q.pc + 1)).toUInt16
  | .zpx =>
    match Q.x.same with
    | some c => memT E Q (E.b (Q.pc + 1) + c).toUInt16
    | none => none
  | .zpy =>
    match Q.y.same with
    | some c => memT E Q (E.b (Q.pc + 1) + c).toUInt16
    | none => none
  | .abs => memT E Q (E.w (Q.pc + 1))
  | .abx => idxT E Q (E.w (Q.pc + 1)) Q.x
  | .aby => idxT E Q (E.w (Q.pc + 1)) Q.y
  | .izy =>
    match ptrT Q (E.b (Q.pc + 1)) with
    | some p => idxT E Q p Q.y
    | none => none

theorem srcT_spec {md : Md} {t : Tag} (h : Lk E m₀ n₀ Q m n) (he : srcT E Q md = some t) :
    let a := md.ea E { m with pc := m.pc + 1 }
    a = md.ea E { n with pc := n.pc + 1 } ∧ okAd a ∧ t.R (memv E m a) (memv E n a) := by
  have hl := h.pcl
  have hr := h.pcr
  cases md with
  | imm =>
    obtain ⟨h1, h2⟩ := memT_spec h he
    simp only [Md.ea, hl, hr]
    exact ⟨trivial, h1, h2⟩
  | zp =>
    obtain ⟨h1, h2⟩ := memT_spec h he
    simp only [Md.ea, hl, hr]
    exact ⟨trivial, h1, h2⟩
  | zpx =>
    simp only [srcT] at he
    split at he
    · rename_i c h3
      obtain ⟨e1, e2⟩ := Q.x.same_spec h3 h.regs.x
      obtain ⟨h1, h2⟩ := memT_spec h he
      simp only [Md.ea, hl, hr, e1, e2]
      exact ⟨trivial, h1, h2⟩
    · cases he
  | zpy =>
    simp only [srcT] at he
    split at he
    · rename_i c h3
      obtain ⟨e1, e2⟩ := Q.y.same_spec h3 h.regs.y
      obtain ⟨h1, h2⟩ := memT_spec h he
      simp only [Md.ea, hl, hr, e1, e2]
      exact ⟨trivial, h1, h2⟩
    · cases he
  | abs =>
    obtain ⟨h1, h2⟩ := memT_spec h he
    simp only [Md.ea, hl, hr]
    exact ⟨trivial, h1, h2⟩
  | abx =>
    obtain ⟨h0, h1, h2⟩ := idxT_spec h h.regs.x he
    simp only [Md.ea, hl, hr]
    exact ⟨h0, h1, h2⟩
  | aby =>
    obtain ⟨h0, h1, h2⟩ := idxT_spec h h.regs.y he
    simp only [Md.ea, hl, hr]
    exact ⟨h0, h1, h2⟩
  | izy =>
    simp only [srcT] at he
    split at he
    · rename_i p h3
      obtain ⟨e1, e2⟩ := ptrT_spec h h3
      obtain ⟨h0, h1, h2⟩ := idxT_spec h h.regs.y he
      have e3 : ptrAt { m with pc := Q.pc + 1 } = ptrAt m := rfl
      have e4 : ptrAt { n with pc := Q.pc + 1 } = ptrAt n := rfl
      simp only [Md.ea, hl, hr, e3, e4, e1, e2]
      exact ⟨h0, h1, h2⟩
    · cases he

/-! ### One step -/

/-- the idle loop -/
def idleAt (E : Rom) (pc : UInt16) : Bool :=
  E.b pc == 0x4C && E.b (pc + 1) == pc.toUInt8 && E.b (pc + 2) == (pc >>> 8).toUInt8 && decide (pc ≥ 0x8000)

theorem step_run {I : Ins} (g : Good E m) (hp : 0x8000 ≤ m.pc) (hd : lookupOp (E.b m.pc) insList = some I) (hi : idleAt E m.pc = false) :
    go step m = go (sem I >>= fun _ => tick (cycTable.get! (E.b m.pc).toNat).toNat) { m with pc := m.pc + 1 } := by
  have h0 : go step m = go (fetch >>= fun op =>
      if (op == 0x4C && m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat == m.pc.toUInt8
        && m.prg.get! ((m.pc + 2) &&& m.prgMask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = true then
        setPC m.pc >>= fun _ => tick (cyclesToNextEvent m)
      else
        (opTable[op.toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! op.toNat).toNat) m := by
    show (if m.nmiPending = true then nmi else if m.halted = true then (pure () : M Unit) else _) m = _
    rw [if_neg (by rw [g.nmi]; decide), if_neg (by rw [g.halted]; decide)]
    rfl
  rw [h0, PipeTransitionAll.go_bind, fetch_eq g hp]
  simp only [g.prg, g.mask]
  have hi2 : (E.b m.pc == 0x4C && E.prg.get! ((m.pc + 1) &&& E.mask).toNat == m.pc.toUInt8 && E.prg.get! ((m.pc + 2) &&& E.mask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = false := hi
  rw [hi2, if_neg (by decide)]
  rw [sem_table (E.b m.pc, I) (lookupOp_mem hd)]

/-- one step, when the instruction leaves a good machine `r` -/
theorem step_nt {I : Ins} {r : Machine} (g : Good E m) (hp : 0x8000 ≤ m.pc) (hd : lookupOp (E.b m.pc) insList = some I) (hi : idleAt E m.pc = false)
    (h : nt (go (sem I) { m with pc := m.pc + 1 }).2 = nt r) (gr : Good E r) : nt (go step m).2 = nt r := by
  rw [step_run g hp hd hi, PipeTransitionAll.go_bind]
  have g2 := Good.of_nt h gr
  rw [nt_tick _ g2.nmi g2.ctl]
  exact h

theorem Good.pc {m : Machine} (g : Good E m) (p : UInt16) : Good E { m with pc := p } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩

/-- an instruction that reads -/
theorem sem_rd {f : RF} {md : Md} (g : Good E m) (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1)
    (ha : okAd (md.ea E { m with pc := m.pc + 1 })) :
    nt (go (sem (.rd f md)) { m with pc := m.pc + 1 }).2 = nt (rfE f (memv E m (md.ea E { m with pc := m.pc + 1 })) { m with pc := md.adv (m.pc + 1) }) := by
  have g1 := g.pc (m.pc + 1)
  obtain ⟨h1, h2'⟩ := Md.r_spec md g1 hp1 hp2
  have h2 : nt (go md.r { m with pc := m.pc + 1 }).2 = nt { m with pc := md.adv (m.pc + 1) } := h2'
  have g2 : Good E (go md.r { m with pc := m.pc + 1 }).2 := Good.of_nt h2 (g.pc (md.adv (m.pc + 1)))
  show nt (go (md.r >>= fun a => rd a >>= rf f) _).2 = _
  rw [PipeTransitionAll.go_bind, h1, PipeTransitionAll.go_bind, rd_ok g2 ha]
  simp only
  rw [rf_eff, nt_rfE, h2, ← nt_rfE]
  have e : memv E (go md.r { m with pc := m.pc + 1 }).2 (md.ea E { m with pc := m.pc + 1 }) = memv E m (md.ea E { m with pc := m.pc + 1 }) := by
    have e1 : (go md.r { m with pc := m.pc + 1 }).2.ram = m.ram := (congrArg Machine.ram h2 : (nt _).ram = (nt _).ram)
    simp only [memv, e1]
  rw [e]

/-- what an instruction that reads does to the registers -/
def rfT : RF → Tag → TS → TS
  | .lda, t, Q => { Q with a := t, z := zT t, n := nT t }
  | .ldx, t, Q => { Q with x := t, z := zT t, n := nT t }
  | .ldy, t, Q => { Q with y := t, z := zT t, n := nT t }
  | .and', t, Q => let r := binT AB.and Q.a t; { Q with a := r, z := zT r, n := nT r }
  | .ora, t, Q => let r := binT AB.or Q.a t; { Q with a := r, z := zT r, n := nT r }
  | .eor, t, Q => let r := binT AB.xor Q.a t; { Q with a := r, z := zT r, n := nT r }
  | .adc, t, Q => let A := adcT Q.a t Q.c; { Q with a := A.r, c := A.c, z := A.z, n := A.n }
  | .sbc, t, Q => let A := adcT Q.a (notT t) Q.c; { Q with a := A.r, c := A.c, z := A.z, n := A.n }
  | .cmp, t, Q => let A := cmpT Q.a t; { Q with c := A.c, z := A.z, n := A.n }
  | .cpx, t, Q => let A := cmpT Q.x t; { Q with c := A.c, z := A.z, n := A.n }
  | .cpy, t, Q => let A := cmpT Q.y t; { Q with c := A.c, z := A.z, n := A.n }

/-- the registers after a load-like change -/
theorem regs_zn {Q : TS} {m n : Machine} {r r' : UInt8} {t : Tag} (h : Regs Q m n) (ht : t.R r r') :
    (zT t).R (bt (znP m.p r) 1) (bt (znP n.p r') 1) ∧ (nT t).R (bt (znP m.p r) 7) (bt (znP n.p r') 7) ∧ Q.c.R (bt (znP m.p r) 0) (bt (znP n.p r') 0) := by
  rw [znP_z, znP_z, znP_n, znP_n, znP_c, znP_c]
  exact ⟨zT_R ht, nT_R ht, h.c⟩

theorem rfT_R {f : RF} {t : Tag} {v v' : UInt8} (h : Regs Q m n) (ht : t.R v v') : Regs (rfT f t Q) (rfE f v m) (rfE f v' n) := by
  cases f with
  | lda =>
    obtain ⟨h1, h2, h3⟩ := regs_zn h ht
    exact ⟨ht, h.x, h.y, h3, h1, h2⟩
  | ldx =>
    obtain ⟨h1, h2, h3⟩ := regs_zn h ht
    exact ⟨h.a, ht, h.y, h3, h1, h2⟩
  | ldy =>
    obtain ⟨h1, h2, h3⟩ := regs_zn h ht
    exact ⟨h.a, h.x, ht, h3, h1, h2⟩
  | and' =>
    have hr := binT_R (f := fun x y => x &&& y) (op := AB.and) (fun _ _ _ _ h1 h2 => mem_and h1 h2) h.a ht
    obtain ⟨h1, h2, h3⟩ := regs_zn h hr
    exact ⟨hr, h.x, h.y, h3, h1, h2⟩
  | ora =>
    have hr := binT_R (f := fun x y => x ||| y) (op := AB.or) (fun _ _ _ _ h1 h2 => mem_or h1 h2) h.a ht
    obtain ⟨h1, h2, h3⟩ := regs_zn h hr
    exact ⟨hr, h.x, h.y, h3, h1, h2⟩
  | eor =>
    have hr := binT_R (f := fun x y => x ^^^ y) (op := AB.xor) (fun _ _ _ _ h1 h2 => mem_xor h1 h2) h.a ht
    obtain ⟨h1, h2, h3⟩ := regs_zn h hr
    exact ⟨hr, h.x, h.y, h3, h1, h2⟩
  | adc =>
    have hr := adcT_R h.a ht h.c
    refine ⟨?_, h.x, h.y, ?_, ?_, ?_⟩
    · show (adcT Q.a t Q.c).r.R (adcS m.a v m.p).1 (adcS n.a v' n.p).1
      rw [adcS_r, adcS_r]
      exact hr.r_
    · show (adcT Q.a t Q.c).c.R (bt (adcS m.a v m.p).2 0) (bt (adcS n.a v' n.p).2 0)
      rw [adcS_c, adcS_c]
      exact hr.c_
    · show (adcT Q.a t Q.c).z.R (bt (adcS m.a v m.p).2 1) (bt (adcS n.a v' n.p).2 1)
      rw [adcS_z, adcS_z]
      exact hr.z_
    · show (adcT Q.a t Q.c).n.R (bt (adcS m.a v m.p).2 7) (bt (adcS n.a v' n.p).2 7)
      rw [adcS_n, adcS_n]
      exact hr.n_
  | sbc =>
    have hr := adcT_R h.a (notT_R ht) h.c
    refine ⟨?_, h.x, h.y, ?_, ?_, ?_⟩
    · show (adcT Q.a (notT t) Q.c).r.R (adcS m.a (~~~v) m.p).1 (adcS n.a (~~~v') n.p).1
      rw [adcS_r, adcS_r]
      exact hr.r_
    · show (adcT Q.a (notT t) Q.c).c.R (bt (adcS m.a (~~~v) m.p).2 0) (bt (adcS n.a (~~~v') n.p).2 0)
      rw [adcS_c, adcS_c]
      exact hr.c_
    · show (adcT Q.a (notT t) Q.c).z.R (bt (adcS m.a (~~~v) m.p).2 1) (bt (adcS n.a (~~~v') n.p).2 1)
      rw [adcS_z, adcS_z]
      exact hr.z_
    · show (adcT Q.a (notT t) Q.c).n.R (bt (adcS m.a (~~~v) m.p).2 7) (bt (adcS n.a (~~~v') n.p).2 7)
      rw [adcS_n, adcS_n]
      exact hr.n_
  | cmp =>
    have hr := cmpT_R h.a ht
    refine ⟨h.a, h.x, h.y, ?_, ?_, ?_⟩
    · show (cmpT Q.a t).c.R (bt (cmpP m.p m.a v) 0) (bt (cmpP n.p n.a v') 0)
      rw [cmpP_c, cmpP_c]
      exact hr.c_
    · show (cmpT Q.a t).z.R (bt (cmpP m.p m.a v) 1) (bt (cmpP n.p n.a v') 1)
      rw [cmpP_z, cmpP_z]
      exact hr.z_
    · show (cmpT Q.a t).n.R (bt (cmpP m.p m.a v) 7) (bt (cmpP n.p n.a v') 7)
      rw [cmpP_n, cmpP_n]
      exact hr.n_
  | cpx =>
    have hr := cmpT_R h.x ht
    refine ⟨h.a, h.x, h.y, ?_, ?_, ?_⟩
    · show (cmpT Q.x t).c.R (bt (cmpP m.p m.x v) 0) (bt (cmpP n.p n.x v') 0)
      rw [cmpP_c, cmpP_c]
      exact hr.c_
    · show (cmpT Q.x t).z.R (bt (cmpP m.p m.x v) 1) (bt (cmpP n.p n.x v') 1)
      rw [cmpP_z, cmpP_z]
      exact hr.z_
    · show (cmpT Q.x t).n.R (bt (cmpP m.p m.x v) 7) (bt (cmpP n.p n.x v') 7)
      rw [cmpP_n, cmpP_n]
      exact hr.n_
  | cpy =>
    have hr := cmpT_R h.y ht
    refine ⟨h.a, h.x, h.y, ?_, ?_, ?_⟩
    · show (cmpT Q.y t).c.R (bt (cmpP m.p m.y v) 0) (bt (cmpP n.p n.y v') 0)
      rw [cmpP_c, cmpP_c]
      exact hr.c_
    · show (cmpT Q.y t).z.R (bt (cmpP m.p m.y v) 1) (bt (cmpP n.p n.y v') 1)
      rw [cmpP_z, cmpP_z]
      exact hr.z_
    · show (cmpT Q.y t).n.R (bt (cmpP m.p m.y v) 7) (bt (cmpP n.p n.y v') 7)
      rw [cmpP_n, cmpP_n]
      exact hr.n_

/-- a change of the registers only, on both machines -/
theorem Lk.regs_only {Q' : TS} {a b : Machine} (h : Lk E m₀ n₀ Q m n)
    (hq : Q'.pc = Q.pc ∧ Q'.s = Q.s ∧ Q'.ram = Q.ram ∧ Q'.w = Q.w)
    (ha : a.pc = m.pc ∧ a.s = m.s ∧ a.ram = m.ram) (hb : b.pc = n.pc ∧ b.s = n.s ∧ b.ram = n.ram)
    (gl : Good E a) (gr : Good E b) (hr : Regs Q' a b) : Lk E m₀ n₀ Q' a b := by
  obtain ⟨q1, q2, q3, q4⟩ := hq
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨gl, gr, by rw [a1, q1]; exact h.pcl, by rw [b1, q1]; exact h.pcr, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [a2, b2]
    exact h.s v (by rw [← q2]; exact hv)
  · intro hv
    rw [a2, b2]
    exact h.s0 (by rw [← q2]; exact hv)
  · intro i hi
    rw [a3, b3, q3]
    exact h.ram i hi
  · intro i hi hw
    rw [a3]
    exact h.fixl i hi (by rw [← q4]; exact hw)
  · intro i hi hw
    rw [b3]
    exact h.fixr i hi (by rw [← q4]; exact hw)

/-- both program counters move -/
theorem Lk.go_pc (h : Lk E m₀ n₀ Q m n) (p : UInt16) : Lk E m₀ n₀ { Q with pc := p } { m with pc := p } { n with pc := p } :=
  ⟨h.gl.pc p, h.gr.pc p, rfl, rfl, ⟨h.regs.a, h.regs.x, h.regs.y, h.regs.c, h.regs.z, h.regs.nf⟩, h.s, h.s0, h.ram, h.fixl, h.fixr⟩

theorem rfE_good (f : RF) (v : UInt8) {a : Machine} (g : Good E a) : Good E (rfE f v a) := by
  cases f <;> exact ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩

theorem rfE_keep (f : RF) (v : UInt8) (a : Machine) : (rfE f v a).pc = a.pc ∧ (rfE f v a).s = a.s ∧ (rfE f v a).ram = a.ram := by
  cases f <;> exact ⟨rfl, rfl, rfl⟩

theorem rfT_keep (f : RF) (t : Tag) (Q : TS) : (rfT f t Q).pc = Q.pc ∧ (rfT f t Q).s = Q.s ∧ (rfT f t Q).ram = Q.ram ∧ (rfT f t Q).w = Q.w := by
  cases f <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- the instruction at the operand `pc1` reads -/
theorem lk_rd {f : RF} {md : Md} {t : Tag} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some (.rd f md)) (hi : idleAt E Q.pc = false) (hs : srcT E Q md = some t) :
    Lk E m₀ n₀ (rfT f t { Q with pc := md.adv (Q.pc + 1) }) (go step m).2 (go step n).2 := by
  obtain ⟨h1, h2, h3⟩ := srcT_spec h hs
  have el := h.pcl
  have er := h.pcr
  have base := h.go_pc (md.adv (Q.pc + 1))
  have ga := rfE_good f (memv E m (md.ea E { m with pc := m.pc + 1 })) base.gl
  have gb := rfE_good f (memv E n (md.ea E { m with pc := m.pc + 1 })) base.gr
  have hnew : Lk E m₀ n₀ (rfT f t { Q with pc := md.adv (Q.pc + 1) }) (rfE f (memv E m (md.ea E { m with pc := m.pc + 1 })) { m with pc := md.adv (Q.pc + 1) })
      (rfE f (memv E n (md.ea E { m with pc := m.pc + 1 })) { n with pc := md.adv (Q.pc + 1) }) :=
    base.regs_only (rfT_keep _ _ _) (rfE_keep _ _ _) (rfE_keep _ _ _) ga gb (rfT_R base.regs h3)
  refine hnew.of_nt ?_ ?_
  · have hp0 : 0x8000 ≤ m.pc := by rw [el]; exact hp
    refine step_nt h.gl hp0 (by rw [el]; exact hd) (by rw [el]; exact hi) ?_ ga
    rw [sem_rd h.gl (by rw [el]; exact hp1) (by rw [el]; exact hp2) h2, el]
  · have hp0 : 0x8000 ≤ n.pc := by rw [er]; exact hp
    refine step_nt h.gr hp0 (by rw [er]; exact hd) (by rw [er]; exact hi) ?_ gb
    rw [sem_rd h.gr (by rw [er]; exact hp1) (by rw [er]; exact hp2) (by rw [← h1]; exact h2), h1, er]

/-- from the effects on both machines to a step -/
theorem lk_fin {I : Ins} {Q' : TS} {r r' : Machine} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc)
    (hd : lookupOp (E.b Q.pc) insList = some I) (hi : idleAt E Q.pc = false)
    (e1 : nt (go (sem I) { m with pc := m.pc + 1 }).2 = nt r) (e2 : nt (go (sem I) { n with pc := n.pc + 1 }).2 = nt r')
    (hn : Lk E m₀ n₀ Q' r r') : Lk E m₀ n₀ Q' (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  refine hn.of_nt ?_ ?_
  · exact step_nt h.gl (by rw [el]; exact hp) (by rw [el]; exact hd) (by rw [el]; exact hi) e1 hn.gl
  · exact step_nt h.gr (by rw [er]; exact hp) (by rw [er]; exact hd) (by rw [er]; exact hi) e2 hn.gr

/-- change one byte of what is known -/
def upd (f : Nat → Tag) (i : Nat) (t : Tag) : Nat → Tag := fun j => if j = i then t else f j
def updW (f : Nat → Bool) (i : Nat) : Nat → Bool := fun j => if j = i then true else f j

/-- a write of one byte, on both machines -/
theorem Lk.write {a : UInt16} {t : Tag} {v v' : UInt8} (h : Lk E m₀ n₀ Q m n) (ht : t.R v v') :
    Lk E m₀ n₀ { Q with ram := upd Q.ram (a &&& 0x7FF).toNat t, w := updW Q.w (a &&& 0x7FF).toNat }
      { m with ram := m.ram.set! (a &&& 0x7FF).toNat v } { n with ram := n.ram.set! (a &&& 0x7FF).toNat v' } := by
  have hi := PipeTransitionAll.mask_lt a
  have gl := h.gl
  have gr := h.gr
  refine ⟨⟨gl.prg, gl.mask, gl.nmi, gl.halted, gl.trk, ?_, gl.ctl⟩, ⟨gr.prg, gr.mask, gr.nmi, gr.halted, gr.trk, ?_, gr.ctl⟩, h.pcl, h.pcr,
    ⟨h.regs.a, h.regs.x, h.regs.y, h.regs.c, h.regs.z, h.regs.nf⟩, h.s, h.s0, ?_, ?_, ?_⟩
  · show (m.ram.set! _ _).size = 2048
    rw [PipeTransitionAll.ba_size_set]
    exact gl.size
  · show (n.ram.set! _ _).size = 2048
    rw [PipeTransitionAll.ba_size_set]
    exact gr.size
  · intro j hj
    show (upd Q.ram (a &&& 0x7FF).toNat t j).R ((m.ram.set! _ _).get! j) ((n.ram.set! _ _).get! j)
    by_cases e : j = (a &&& 0x7FF).toNat
    · subst e
      simp only [upd, if_true]
      rw [PipeTransitionAll.ba_get_set_self _ _ _ (by rw [gl.size]; exact hi), PipeTransitionAll.ba_get_set_self _ _ _ (by rw [gr.size]; exact hi)]
      exact ht
    · simp only [upd, if_neg e]
      have e' : (a &&& 0x7FF).toNat ≠ j := fun h3 => e h3.symm
      rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ e', PipeTransitionAll.ba_get_set_ne _ _ _ _ e']
      exact h.ram j hj
  · intro j hj hw
    have e : j ≠ (a &&& 0x7FF).toNat := by
      intro e
      simp [updW, e] at hw
    have e' : (a &&& 0x7FF).toNat ≠ j := fun h3 => e h3.symm
    show (m.ram.set! _ _).get! j = _
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ e']
    have hw2 : updW Q.w (a &&& 0x7FF).toNat j = false := hw
    simp only [updW, if_neg e] at hw2
    exact h.fixl j hj hw2
  · intro j hj hw
    have e : j ≠ (a &&& 0x7FF).toNat := by
      intro e
      simp [updW, e] at hw
    have e' : (a &&& 0x7FF).toNat ≠ j := fun h3 => e h3.symm
    show (n.ram.set! _ _).get! j = _
    rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ e']
    have hw2 : updW Q.w (a &&& 0x7FF).toNat j = false := hw
    simp only [updW, if_neg e] at hw2
    exact h.fixr j hj hw2

/-- the stack pointer becomes a known value -/
theorem Lk.set_s (h : Lk E m₀ n₀ Q m n) (v : UInt8) : Lk E m₀ n₀ { Q with s := some v } { m with s := v } { n with s := v } :=
  ⟨⟨h.gl.prg, h.gl.mask, h.gl.nmi, h.gl.halted, h.gl.trk, h.gl.size, h.gl.ctl⟩, ⟨h.gr.prg, h.gr.mask, h.gr.nmi, h.gr.halted, h.gr.trk, h.gr.size, h.gr.ctl⟩,
    h.pcl, h.pcr, ⟨h.regs.a, h.regs.x, h.regs.y, h.regs.c, h.regs.z, h.regs.nf⟩, (fun u hu => by
      have e : v = u := Option.some.inj hu
      subst e
      exact ⟨rfl, rfl⟩), (fun hu => by cases hu), h.ram, h.fixl, h.fixr⟩

/-! ### Writing a register -/

/-- the address of a write, the same in both -/
def dstT (E : Rom) (Q : TS) : Md → Option UInt16
  | .imm => none
  | .zp => some (E.b (Q.pc + 1)).toUInt16
  | .zpx => (Q.x.same).map fun c => (E.b (Q.pc + 1) + c).toUInt16
  | .zpy => (Q.y.same).map fun c => (E.b (Q.pc + 1) + c).toUInt16
  | .abs => some (E.w (Q.pc + 1))
  | .abx => (Q.x.same).map fun c => E.w (Q.pc + 1) + c.toUInt16
  | .aby => (Q.y.same).map fun c => E.w (Q.pc + 1) + c.toUInt16
  | .izy =>
    match ptrT Q (E.b (Q.pc + 1)), Q.y.same with
    | some p, some c => some (p + c.toUInt16)
    | _, _ => none

theorem dstT_spec {md : Md} {a : UInt16} (h : Lk E m₀ n₀ Q m n) (he : dstT E Q md = some a) :
    md.ea E { m with pc := m.pc + 1 } = a ∧ md.ea E { n with pc := n.pc + 1 } = a := by
  have hl := h.pcl
  have hr := h.pcr
  cases md with
  | imm => cases he
  | zp =>
    have e := Option.some.inj he
    subst e
    simp only [Md.ea, hl, hr, and_self]
  | abs =>
    have e := Option.some.inj he
    subst e
    simp only [Md.ea, hl, hr, and_self]
  | zpx =>
    simp only [dstT, Option.map_eq_some_iff] at he
    obtain ⟨c, h1, h2⟩ := he
    subst h2
    obtain ⟨e1, e2⟩ := Q.x.same_spec h1 h.regs.x
    simp only [Md.ea, hl, hr, e1, e2, and_self]
  | zpy =>
    simp only [dstT, Option.map_eq_some_iff] at he
    obtain ⟨c, h1, h2⟩ := he
    subst h2
    obtain ⟨e1, e2⟩ := Q.y.same_spec h1 h.regs.y
    simp only [Md.ea, hl, hr, e1, e2, and_self]
  | abx =>
    simp only [dstT, Option.map_eq_some_iff] at he
    obtain ⟨c, h1, h2⟩ := he
    subst h2
    obtain ⟨e1, e2⟩ := Q.x.same_spec h1 h.regs.x
    simp only [Md.ea, hl, hr, e1, e2, and_self]
  | aby =>
    simp only [dstT, Option.map_eq_some_iff] at he
    obtain ⟨c, h1, h2⟩ := he
    subst h2
    obtain ⟨e1, e2⟩ := Q.y.same_spec h1 h.regs.y
    simp only [Md.ea, hl, hr, e1, e2, and_self]
  | izy =>
    simp only [dstT] at he
    split at he
    · rename_i p c h1 h2
      have e := Option.some.inj he
      subst e
      obtain ⟨e1, e2⟩ := ptrT_spec h h1
      obtain ⟨e3, e4⟩ := Q.y.same_spec h2 h.regs.y
      show ptrAt m (E.b (m.pc + 1)) + m.y.toUInt16 = _ ∧ ptrAt n (E.b (n.pc + 1)) + n.y.toUInt16 = _
      rw [hl, hr, e1, e2, e3, e4]
      exact ⟨rfl, rfl⟩
    · cases he

def WF.tag : WF → TS → Tag
  | .sta, Q => Q.a
  | .stx, Q => Q.x
  | .sty, Q => Q.y

theorem WF.tag_R (f : WF) {Q : TS} {m n : Machine} (h : Regs Q m n) : (f.tag Q).R (f.val m) (f.val n) := by
  cases f
  · exact h.a
  · exact h.x
  · exact h.y

theorem sem_wr {f : WF} {md : Md} {a : UInt16} (g : Good E m) (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1)
    (ha : md.ea E { m with pc := m.pc + 1 } = a) (hl : a < 0x2000) :
    go (sem (.wr f md)) { m with pc := m.pc + 1 } = ((), { m with pc := md.adv (m.pc + 1), ram := m.ram.set! (a &&& 0x7FF).toNat (f.val m) }) := by
  have g1 := g.pc (m.pc + 1)
  have key : ∀ k : Machine → UInt8, sem (.wr f md) = (md.w >>= fun ad => get >>= fun s => wr ad (k s)) → k { m with pc := md.adv (m.pc + 1) } = f.val m →
      go (sem (.wr f md)) { m with pc := m.pc + 1 } = ((), { m with pc := md.adv (m.pc + 1), ram := m.ram.set! (a &&& 0x7FF).toNat (f.val m) }) := by
    intro k e1 e2
    rw [e1, PipeTransitionAll.go_bind, Md.w_spec md g1 hp1 hp2, ha]
    show go (wr a (k { m with pc := md.adv (m.pc + 1) })) { m with pc := md.adv (m.pc + 1) } = _
    have gk := g.pc (md.adv (m.pc + 1))
    rw [wr_ram hl gk.trk, e2]
  cases f
  · exact key (fun s => s.a) rfl rfl
  · exact key (fun s => s.x) rfl rfl
  · exact key (fun s => s.y) rfl rfl

/-- the bytes for a change of a machine's fields other than the registers -/
theorem lk_wr {f : WF} {md : Md} {a : UInt16} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some (.wr f md)) (hi : idleAt E Q.pc = false) (hs : dstT E Q md = some a) (hl : a < 0x2000) :
    Lk E m₀ n₀ { Q with pc := md.adv (Q.pc + 1), ram := upd Q.ram (a &&& 0x7FF).toNat (f.tag Q), w := updW Q.w (a &&& 0x7FF).toNat } (go step m).2 (go step n).2 := by
  obtain ⟨e1, e2⟩ := dstT_spec h hs
  have el := h.pcl
  have er := h.pcr
  have h1 := Lk.write (a := a) h (WF.tag_R f h.regs)
  have h2 := h1.go_pc (md.adv (Q.pc + 1))
  refine lk_fin h hp hd hi ?_ ?_ h2
  · rw [sem_wr h.gl (by rw [el]; exact hp1) (by rw [el]; exact hp2) e1 hl, el]
  · rw [sem_wr h.gr (by rw [er]; exact hp1) (by rw [er]; exact hp2) e2 hl, er]

/-! ### Shifts on memory and on A -/

theorem ufS_R {f : UF} {t : Tag} {v v' : UInt8} (h : Regs Q m n) (ht : t.R v v') :
    (ufT f t Q.c).r.R (ufS f v m.p).1 (ufS f v' n.p).1 ∧ (ufT f t Q.c).c.R (bt (ufS f v m.p).2 0) (bt (ufS f v' n.p).2 0) ∧
    (ufT f t Q.c).z.R (bt (ufS f v m.p).2 1) (bt (ufS f v' n.p).2 1) ∧ (ufT f t Q.c).n.R (bt (ufS f v m.p).2 7) (bt (ufS f v' n.p).2 7) := by
  have hr := ufT_R (f := f) ht h.c
  rw [ufS_r, ufS_r, ufS_c, ufS_c, ufS_z, ufS_z, ufS_n, ufS_n]
  exact ⟨hr.r_, hr.c_, hr.z_, hr.n_⟩

/-- the flags of a shift, on both machines -/
theorem Lk.flags {A : Alu} {p p' : UInt8} (h : Lk E m₀ n₀ Q m n) (h1 : A.c.R (bt p 0) (bt p' 0)) (h2 : A.z.R (bt p 1) (bt p' 1)) (h3 : A.n.R (bt p 7) (bt p' 7)) :
    Lk E m₀ n₀ { Q with c := A.c, z := A.z, n := A.n } { m with p := p } { n with p := p' } :=
  ⟨⟨h.gl.prg, h.gl.mask, h.gl.nmi, h.gl.halted, h.gl.trk, h.gl.size, h.gl.ctl⟩, ⟨h.gr.prg, h.gr.mask, h.gr.nmi, h.gr.halted, h.gr.trk, h.gr.size, h.gr.ctl⟩,
    h.pcl, h.pcr, ⟨h.regs.a, h.regs.x, h.regs.y, h1, h2, h3⟩, h.s, h.s0, h.ram, h.fixl, h.fixr⟩

theorem sem_rmw {f : UF} {md : Md} {a : UInt16} (g : Good E m) (hp1 : 0x8000 ≤ m.pc + 1) (hp2 : 0x8000 ≤ m.pc + 1 + 1)
    (ha : md.ea E { m with pc := m.pc + 1 } = a) (hl : a < 0x2000) :
    go (sem (.rmw f md)) { m with pc := m.pc + 1 } =
      ((), { m with pc := md.adv (m.pc + 1), p := (ufS f (m.ram.get! (a &&& 0x7FF).toNat) m.p).2, ram := m.ram.set! (a &&& 0x7FF).toNat (ufS f (m.ram.get! (a &&& 0x7FF).toNat) m.p).1 }) := by
  have g1 := g.pc (m.pc + 1)
  show go (md.w >>= fun ad => rd ad >>= fun v => uf f v >>= fun r => wr ad r) _ = _
  rw [PipeTransitionAll.go_bind, Md.w_spec md g1 hp1 hp2, ha]
  simp only
  have gk := g.pc (md.adv (m.pc + 1))
  rw [PipeTransitionAll.go_bind, rd_ram hl gk.trk]
  simp only
  rw [PipeTransitionAll.go_bind, uf_eff]
  simp only
  have gk2 : Good E { { m with pc := md.adv (m.pc + 1) } with p := (ufS f (m.ram.get! (a &&& 0x7FF).toNat) m.p).2 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  rw [wr_ram hl gk2.trk]

theorem lk_rmw {f : UF} {md : Md} {a : UInt16} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some (.rmw f md)) (hi : idleAt E Q.pc = false) (hs : dstT E Q md = some a) (hl : a < 0x2000) :
    Lk E m₀ n₀ { { Q with c := (ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c).c, z := (ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c).z, n := (ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c).n, ram := upd Q.ram (a &&& 0x7FF).toNat (ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c).r, w := updW Q.w (a &&& 0x7FF).toNat } with pc := md.adv (Q.pc + 1) } (go step m).2 (go step n).2 := by
  obtain ⟨e1, e2⟩ := dstT_spec h hs
  have el := h.pcl
  have er := h.pcr
  have hb := h.ram _ (PipeTransitionAll.mask_lt a)
  obtain ⟨u1, u2, u3, u4⟩ := ufS_R (f := f) h.regs hb
  have h1 := (Lk.write (a := a) h u1)
  have h2 := Lk.flags (A := ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c) h1 u2 u3 u4
  have h3 := h2.go_pc (md.adv (Q.pc + 1))
  refine lk_fin h hp hd hi ?_ ?_ h3
  · rw [sem_rmw h.gl (by rw [el]; exact hp1) (by rw [el]; exact hp2) e1 hl, el]
  · rw [sem_rmw h.gr (by rw [er]; exact hp1) (by rw [er]; exact hp2) e2 hl, er]

theorem sem_acc {f : UF} (m : Machine) : go (sem (.acc f)) m = ((), { m with a := (ufS f m.a m.p).1, p := (ufS f m.a m.p).2 }) := by
  show go (get >>= fun s => uf f s.a >>= fun r => modify fun m => { m with a := r }) m = _
  rw [PipeTransitionAll.go_bind]
  show go (uf f m.a >>= fun r => modify fun m => { m with a := r }) m = _
  rw [PipeTransitionAll.go_bind, uf_eff]
  rfl

theorem lk_acc {f : UF} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some (.acc f)) (hi : idleAt E Q.pc = false) :
    Lk E m₀ n₀ { Q with pc := Q.pc + 1, a := (ufT f Q.a Q.c).r, c := (ufT f Q.a Q.c).c, z := (ufT f Q.a Q.c).z, n := (ufT f Q.a Q.c).n } (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  obtain ⟨u1, u2, u3, u4⟩ := ufS_R (f := f) h.regs h.regs.a
  have gl := h.gl
  have gr := h.gr
  have hn : Lk E m₀ n₀ { Q with pc := Q.pc + 1, a := (ufT f Q.a Q.c).r, c := (ufT f Q.a Q.c).c, z := (ufT f Q.a Q.c).z, n := (ufT f Q.a Q.c).n }
      { m with pc := m.pc + 1, a := (ufS f m.a m.p).1, p := (ufS f m.a m.p).2 } { n with pc := n.pc + 1, a := (ufS f n.a n.p).1, p := (ufS f n.a n.p).2 } :=
    ⟨⟨gl.prg, gl.mask, gl.nmi, gl.halted, gl.trk, gl.size, gl.ctl⟩, ⟨gr.prg, gr.mask, gr.nmi, gr.halted, gr.trk, gr.size, gr.ctl⟩,
      by show m.pc + 1 = Q.pc + 1; rw [el], by show n.pc + 1 = Q.pc + 1; rw [er],
      ⟨u1, h.regs.x, h.regs.y, u2, u3, u4⟩, h.s, h.s0, h.ram, h.fixl, h.fixr⟩
  refine lk_fin h hp hd hi ?_ ?_ hn
  · rw [sem_acc]
  · rw [sem_acc]

/-! ### Branches and jumps -/

/-- where a branch goes; `pc` is at its operand -/
def brT (E : Rom) (pc : UInt16) : UInt16 := (pc + 1) + ((E.b pc).toUInt16 ||| (if E.b pc ≥ 0x80 then 0xFF00 else 0))

/-- the branch's test on a byte of flags -/
theorem BF.op_eq (f : BF) : f.op = branch (fun m => bt m.p f.i == f.set) := by
  have e1 : ∀ x : UInt8, (x &&& 0x80 == 0) = (bt x 7 == false) := fun x => by
    rw [not_ne, and80]
    cases bt x 7 <;> rfl
  have e2 : ∀ x : UInt8, (x &&& 0x80 != 0) = (bt x 7 == true) := fun x => by
    rw [and80]
    cases bt x 7 <;> rfl
  have e3 : ∀ x : UInt8, (x &&& 0x01 == 0) = (bt x 0 == false) := fun x => by
    rw [not_ne, and1]
    cases bt x 0 <;> rfl
  have e4 : ∀ x : UInt8, (x &&& 0x01 != 0) = (bt x 0 == true) := fun x => by
    rw [and1]
    cases bt x 0 <;> rfl
  have e5 : ∀ x : UInt8, (x &&& 0x02 == 0) = (bt x 1 == false) := fun x => by
    rw [not_ne, and2]
    cases bt x 1 <;> rfl
  have e6 : ∀ x : UInt8, (x &&& 0x02 != 0) = (bt x 1 == true) := fun x => by
    rw [and2]
    cases bt x 1 <;> rfl
  cases f
  · show branch _ = branch _
    congr 1
    funext m
    exact e1 m.p
  · show branch _ = branch _
    congr 1
    funext m
    exact e2 m.p
  · show branch _ = branch _
    congr 1
    funext m
    exact e3 m.p
  · show branch _ = branch _
    congr 1
    funext m
    exact e4 m.p
  · show branch _ = branch _
    congr 1
    funext m
    exact e5 m.p
  · show branch _ = branch _
    congr 1
    funext m
    exact e6 m.p

theorem sem_br {f : BF} (g : Good E m) (hp1 : 0x8000 ≤ m.pc + 1) :
    nt (go (sem (.br f)) { m with pc := m.pc + 1 }).2 =
      nt (if bt m.p f.i == f.set then { m with pc := brT E (m.pc + 1) } else { m with pc := m.pc + 1 + 1 }) := by
  have g1 := g.pc (m.pc + 1)
  show nt (go f.op _).2 = _
  rw [BF.op_eq]
  show nt (go (fetch >>= fun off => get >>= fun s => if (bt s.p f.i == f.set) = true then
      (setPC (s.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0))) >>= fun _ =>
        tick (if (s.pc ^^^ (s.pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0)))) &&& 0xFF00 != 0 then 2 else 1))
      else pure ()) _).2 = _
  rw [PipeTransitionAll.go_bind, fetch_eq g1 hp1]
  by_cases hc : (bt m.p f.i == f.set) = true
  · simp only [hc, if_true]
    show nt (go (if (bt m.p f.i == f.set) = true then _ else pure ()) _).2 = _
    rw [if_pos hc, PipeTransitionAll.go_bind]
    exact nt_tick _ g.nmi g.ctl
  · have hc2 : (bt m.p f.i == f.set) = false := by simpa using hc
    simp only [hc2]
    show nt (go (if (bt m.p f.i == f.set) = true then _ else pure ()) _).2 = _
    rw [if_neg hc]
    rfl

/-- the flag of a branch, in what is known -/
def BF.tag (f : BF) (Q : TS) : FT :=
  match f with
  | .pl | .mi => Q.n
  | .cc | .cs => Q.c
  | .ne | .eq => Q.z

/-- the flag is now known -/
def BF.setT (f : BF) (Q : TS) (b : Bool) : TS :=
  match f with
  | .pl | .mi => { Q with n := .kn b b }
  | .cc | .cs => { Q with c := .kn b b }
  | .ne | .eq => { Q with z := .kn b b }

theorem BF.tag_R (f : BF) (h : Regs Q m n) : (f.tag Q).R (bt m.p f.i) (bt n.p f.i) := by
  cases f
  · exact h.nf
  · exact h.nf
  · exact h.c
  · exact h.c
  · exact h.z
  · exact h.z

theorem BF.setT_R (f : BF) (h : Regs Q m n) {b : Bool} (h1 : bt m.p f.i = b) (h2 : bt n.p f.i = b) : Regs (f.setT Q b) m n := by
  cases f
  · exact ⟨h.a, h.x, h.y, h.c, h.z, ⟨h1, h2⟩⟩
  · exact ⟨h.a, h.x, h.y, h.c, h.z, ⟨h1, h2⟩⟩
  · exact ⟨h.a, h.x, h.y, ⟨h1, h2⟩, h.z, h.nf⟩
  · exact ⟨h.a, h.x, h.y, ⟨h1, h2⟩, h.z, h.nf⟩
  · exact ⟨h.a, h.x, h.y, h.c, ⟨h1, h2⟩, h.nf⟩
  · exact ⟨h.a, h.x, h.y, h.c, ⟨h1, h2⟩, h.nf⟩

theorem BF.setT_keep (f : BF) (Q : TS) (b : Bool) : (f.setT Q b).pc = Q.pc ∧ (f.setT Q b).s = Q.s ∧ (f.setT Q b).ram = Q.ram ∧ (f.setT Q b).w = Q.w := by
  cases f <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- the states after a branch -/
def brNext (E : Rom) (Q : TS) (f : BF) (taken : Bool) : TS :=
  if taken then { f.setT Q f.set with pc := brT E (Q.pc + 1) } else { f.setT Q (!f.set) with pc := Q.pc + 1 + 1 }

theorem lk_br {f : BF} {b : Bool} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1)
    (hd : lookupOp (E.b Q.pc) insList = some (.br f)) (hi : idleAt E Q.pc = false)
    (h1 : bt m.p f.i = b) (h2 : bt n.p f.i = b) :
    Lk E m₀ n₀ (brNext E Q f (b == f.set)) (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  have base : Lk E m₀ n₀ (f.setT Q b) m n := h.regs_only (BF.setT_keep f Q b) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ h.gl h.gr (BF.setT_R f h.regs h1 h2)
  by_cases hb : (b == f.set) = true
  · have e : b = f.set := beq_iff_eq.1 hb
    have h3 := base.go_pc (brT E (Q.pc + 1))
    have es : brNext E Q f (b == f.set) = { f.setT Q b with pc := brT E (Q.pc + 1) } := by
      rw [hb]
      simp only [brNext, if_true]
      rw [e]
    rw [es]
    refine lk_fin h hp hd hi ?_ ?_ h3
    · rw [sem_br h.gl (by rw [el]; exact hp1), h1, hb, el]
      rfl
    · rw [sem_br h.gr (by rw [er]; exact hp1), h2, hb, er]
      rfl
  · have hb2 : (b == f.set) = false := by simpa using hb
    have e : b = !f.set := by
      cases b <;> cases hs : f.set <;> simp_all
    have h3 := base.go_pc (Q.pc + 1 + 1)
    have es : brNext E Q f (b == f.set) = { f.setT Q b with pc := Q.pc + 1 + 1 } := by
      rw [hb2]
      simp only [brNext, Bool.false_eq_true, if_false]
      rw [e]
    rw [es]
    refine lk_fin h hp hd hi ?_ ?_ h3
    · rw [sem_br h.gl (by rw [el]; exact hp1), h1, hb2, el]
      rfl
    · rw [sem_br h.gr (by rw [er]; exact hp1), h2, hb2, er]
      rfl

theorem lk_jmp (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some .jmp) (hi : idleAt E Q.pc = false) :
    Lk E m₀ n₀ { Q with pc := E.w (Q.pc + 1) } (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  have key : ∀ {a : Machine}, Good E a → a.pc = Q.pc → go (sem .jmp) { a with pc := a.pc + 1 } = ((), { a with pc := E.w (Q.pc + 1) }) := by
    intro a ga ea
    show go (fetch16 >>= fun t => setPC t) _ = _
    have g1 := ga.pc (a.pc + 1)
    rw [PipeTransitionAll.go_bind, fetch16_eq g1 (by rw [ea]; exact hp1) (by rw [ea]; exact hp2), ea]
    rfl
  refine lk_fin h hp hd hi ?_ ?_ (h.go_pc _)
  · rw [key h.gl el]
  · rw [key h.gr er]

/-! ### The stack -/

/-- the RAM index of a byte of the stack -/
def stkI (sp : UInt8) : Nat := ((0x100 ||| sp.toUInt16) &&& 0x7FF).toNat

theorem stk_lt (sp : UInt8) : (0x100 ||| sp.toUInt16 : UInt16) < 0x2000 := by
  apply UInt16.lt_iff_toNat_lt.2
  have h1 := sp.toNat_lt
  have h2 : (0x100 ||| sp.toUInt16 : UInt16).toNat = 256 ||| sp.toNat := by
    simp [UInt16.toNat_or]
  rw [h2]
  have h3 : 256 ||| sp.toNat < 2 ^ 13 := Nat.or_lt_two_pow (by decide) (by omega)
  simpa using h3

theorem push_eff {v : UInt8} (g : Good E m) : go (push v) m = ((), { m with s := m.s - 1, ram := m.ram.set! (stkI m.s) v }) := by
  have g1 : Good E { m with s := m.s - 1 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  show go (wr (0x100 ||| m.s.toUInt16) v) { m with s := m.s - 1 } = _
  rw [wr_ram (stk_lt m.s) g1.trk]
  rfl

theorem pull_eff (g : Good E m) : go pull m = (m.ram.get! (stkI (m.s + 1)), { m with s := m.s + 1 }) := by
  have g1 : Good E { m with s := m.s + 1 } := ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  show go (rd (0x100 ||| (m.s + 1).toUInt16)) { m with s := m.s + 1 } = _
  rw [rd_ram (stk_lt (m.s + 1)) g1.trk]
  rfl

/-- a push, on both machines -/
theorem Lk.push {sp : UInt8} {t : Tag} {v v' : UInt8} (h : Lk E m₀ n₀ Q m n) (ht : t.R v v') :
    Lk E m₀ n₀ { { Q with ram := upd Q.ram (stkI sp) t, w := updW Q.w (stkI sp) } with s := some (sp - 1) }
      { { m with ram := m.ram.set! (stkI sp) v } with s := sp - 1 } { { n with ram := n.ram.set! (stkI sp) v' } with s := sp - 1 } :=
  (Lk.write (a := 0x100 ||| sp.toUInt16) h ht).set_s (sp - 1)

/-- a pull, on both machines -/
theorem Lk.pull {sp : UInt8} (h : Lk E m₀ n₀ Q m n) : Lk E m₀ n₀ { Q with s := some (sp + 1) } { m with s := sp + 1 } { n with s := sp + 1 } := h.set_s (sp + 1)

theorem lk_pha {sp : UInt8} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some .pha) (hi : idleAt E Q.pc = false) (hs : Q.s = some sp) :
    Lk E m₀ n₀ { { { Q with ram := upd Q.ram (stkI sp) Q.a, w := updW Q.w (stkI sp) } with s := some (sp - 1) } with pc := Q.pc + 1 } (go step m).2 (go step n).2 := by
  obtain ⟨e1, e2⟩ := h.s sp hs
  have el := h.pcl
  have er := h.pcr
  have h1 := (Lk.push (sp := sp) h h.regs.a).go_pc (Q.pc + 1)
  have key : ∀ {a : Machine}, Good E a → a.pc = Q.pc → a.s = sp → go (sem .pha) { a with pc := a.pc + 1 } = ((), { { { a with ram := a.ram.set! (stkI sp) a.a } with s := sp - 1 } with pc := Q.pc + 1 }) := by
    intro a ga ea es
    have g1 := ga.pc (a.pc + 1)
    show go (push a.a) { a with pc := a.pc + 1 } = _
    rw [push_eff g1]
    show (_, _) = _
    simp only [es, ea]
  refine lk_fin h hp hd hi ?_ ?_ h1
  · rw [key h.gl el e1]
  · rw [key h.gr er e2]

theorem lk_pla {sp : UInt8} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some .pla) (hi : idleAt E Q.pc = false) (hs : Q.s = some sp) :
    Lk E m₀ n₀ (rfT .lda (Q.ram (stkI (sp + 1))) { { Q with s := some (sp + 1) } with pc := Q.pc + 1 }) (go step m).2 (go step n).2 := by
  obtain ⟨e1, e2⟩ := h.s sp hs
  have el := h.pcl
  have er := h.pcr
  have h1 := (Lk.pull (sp := sp) h).go_pc (Q.pc + 1)
  have hb := h.ram (stkI (sp + 1)) (PipeTransitionAll.mask_lt _)
  have ga := rfE_good .lda (m.ram.get! (stkI (sp + 1))) h1.gl
  have gb := rfE_good .lda (n.ram.get! (stkI (sp + 1))) h1.gr
  have h2 := h1.regs_only (Q' := rfT .lda (Q.ram (stkI (sp + 1))) { { Q with s := some (sp + 1) } with pc := Q.pc + 1 }) (rfT_keep _ _ _) (rfE_keep _ _ _) (rfE_keep _ _ _) ga gb (rfT_R h1.regs hb)
  have key : ∀ {a : Machine}, Good E a → a.pc = Q.pc → a.s = sp → go (sem .pla) { a with pc := a.pc + 1 } =
      ((), rfE .lda (a.ram.get! (stkI (sp + 1))) { { a with s := sp + 1 } with pc := Q.pc + 1 }) := by
    intro a ga ea es
    have g1 := ga.pc (a.pc + 1)
    show go (Smbrta.pull >>= fun v => setA v) { a with pc := a.pc + 1 } = _
    rw [PipeTransitionAll.go_bind, pull_eff g1]
    show (_, _) = _
    simp only [es, ea]
    rfl
  refine lk_fin h hp hd hi ?_ ?_ h2
  · rw [key h.gl el e1]
  · rw [key h.gr er e2]

theorem lk_jsr {sp : UInt8} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some .jsr) (hi : idleAt E Q.pc = false) (hs : Q.s = some sp) :
    let ret := Q.pc + 1 + 1 + 1 - 1
    let Q1 : TS := { { Q with ram := upd Q.ram (stkI sp) (Tag.kn (ret >>> 8).toUInt8 (ret >>> 8).toUInt8), w := updW Q.w (stkI sp) } with s := some (sp - 1) }
    let Q2 : TS := { { Q1 with ram := upd Q1.ram (stkI (sp - 1)) (Tag.kn ret.toUInt8 ret.toUInt8), w := updW Q1.w (stkI (sp - 1)) } with s := some (sp - 1 - 1) }
    Lk E m₀ n₀ { Q2 with pc := E.w (Q.pc + 1) } (go step m).2 (go step n).2 := by
  intro ret Q1 Q2
  obtain ⟨e1, e2⟩ := h.s sp hs
  have el := h.pcl
  have er := h.pcr
  have h1 := Lk.push (sp := sp) (v := (ret >>> 8).toUInt8) (v' := (ret >>> 8).toUInt8) h (Tag.R_kn _ _)
  have h2 := Lk.push (Q := Q1) (sp := sp - 1) (v := ret.toUInt8) (v' := ret.toUInt8) h1 (Tag.R_kn _ _)
  have h3 := h2.go_pc (E.w (Q.pc + 1))
  have key : ∀ {a : Machine}, Good E a → a.pc = Q.pc → a.s = sp → go (sem .jsr) { a with pc := a.pc + 1 } =
      ((), { { { { { a with ram := a.ram.set! (stkI sp) (ret >>> 8).toUInt8 } with s := sp - 1 } with ram := (a.ram.set! (stkI sp) (ret >>> 8).toUInt8).set! (stkI (sp - 1)) ret.toUInt8 } with s := sp - 1 - 1 } with pc := E.w (Q.pc + 1) }) := by
    intro a ga ea es
    have g1 := ga.pc (a.pc + 1)
    show go (fetch16 >>= fun t => get >>= fun s => Smbrta.push ((s.pc - 1) >>> 8).toUInt8 >>= fun _ => Smbrta.push (s.pc - 1).toUInt8 >>= fun _ => setPC t) _ = _
    rw [PipeTransitionAll.go_bind, fetch16_eq g1 (by rw [ea]; exact hp1) (by rw [ea]; exact hp2)]
    have g2 := ga.pc (a.pc + 1 + 1 + 1)
    show go (Smbrta.push ((a.pc + 1 + 1 + 1 - 1) >>> 8).toUInt8 >>= fun _ => Smbrta.push (a.pc + 1 + 1 + 1 - 1).toUInt8 >>= fun _ => setPC (E.w (a.pc + 1))) { a with pc := a.pc + 1 + 1 + 1 } = _
    rw [PipeTransitionAll.go_bind, push_eff g2]
    have g3 : Good E { { a with pc := a.pc + 1 + 1 + 1 } with s := a.s - 1, ram := a.ram.set! (stkI a.s) ((a.pc + 1 + 1 + 1 - 1) >>> 8).toUInt8 } := by
      refine ⟨ga.prg, ga.mask, ga.nmi, ga.halted, ga.trk, ?_, ga.ctl⟩
      show (a.ram.set! _ _).size = 2048
      rw [PipeTransitionAll.ba_size_set]
      exact ga.size
    show go (Smbrta.push (a.pc + 1 + 1 + 1 - 1).toUInt8 >>= fun _ => setPC (E.w (a.pc + 1))) _ = _
    rw [PipeTransitionAll.go_bind, push_eff g3]
    simp only [es, ea]
    rfl
  refine lk_fin h hp hd hi ?_ ?_ h3
  · rw [key h.gl el e1]
  · rw [key h.gr er e2]

/-- the two bytes of a return address, the same and known -/
def retT (Q : TS) (sp : UInt8) : Option UInt16 :=
  match (Q.ram (stkI (sp + 1))).same, (Q.ram (stkI (sp + 1 + 1))).same with
  | some lo, some hi => some ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + 1)
  | _, _ => none

theorem rts_eff {a : Machine} (ga : Good E a) : go opRTS a =
    ((), { { a with s := a.s + 1 + 1 } with pc := ((a.ram.get! (stkI (a.s + 1))).toUInt16 ||| ((a.ram.get! (stkI (a.s + 1 + 1))).toUInt16 <<< 8)) + 1 }) := by
  have g2 : Good E { a with s := a.s + 1 } := ⟨ga.prg, ga.mask, ga.nmi, ga.halted, ga.trk, ga.size, ga.ctl⟩
  have e0 : go opRTS a = go (Smbrta.pull >>= fun lo => Smbrta.pull >>= fun hi => setPC ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + 1)) a := rfl
  rw [e0, PipeTransitionAll.go_bind, pull_eff ga, PipeTransitionAll.go_bind]
  simp only
  rw [pull_eff g2]
  rfl

theorem lk_rts {sp : UInt8} {t : UInt16} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some .rts) (hi : idleAt E Q.pc = false)
    (hs : Q.s = some sp) (hr : retT Q sp = some t) :
    Lk E m₀ n₀ { { Q with s := some (sp + 1 + 1) } with pc := t } (go step m).2 (go step n).2 := by
  obtain ⟨e1, e2⟩ := h.s sp hs
  have el := h.pcl
  have er := h.pcr
  have h1 := (h.set_s (sp + 1 + 1)).go_pc t
  unfold retT at hr
  split at hr
  · rename_i lo hi' h3 h4
    have e := Option.some.inj hr
    obtain ⟨a1, a2⟩ := Tag.same_spec h3 (h.ram _ (PipeTransitionAll.mask_lt _))
    obtain ⟨b1, b2⟩ := Tag.same_spec h4 (h.ram _ (PipeTransitionAll.mask_lt _))
    have key : ∀ {a : Machine}, Good E a → a.s = sp → a.ram.get! (stkI (sp + 1)) = lo → a.ram.get! (stkI (sp + 1 + 1)) = hi' → go (sem .rts) { a with pc := a.pc + 1 } =
        ((), { { a with s := sp + 1 + 1 } with pc := t }) := by
      intro a ga es u1 u2
      have g1 := ga.pc (a.pc + 1)
      have e5 := rts_eff g1
      have e6 : go (sem .rts) { a with pc := a.pc + 1 } = go opRTS { a with pc := a.pc + 1 } := rfl
      rw [e6, e5]
      show ((), { { { a with pc := a.pc + 1 } with s := a.s + 1 + 1 } with pc := ((a.ram.get! (stkI (a.s + 1))).toUInt16 ||| ((a.ram.get! (stkI (a.s + 1 + 1))).toUInt16 <<< 8)) + 1 }) = _
      rw [es, u1, u2, e]
    refine lk_fin h hp hd hi ?_ ?_ h1
    · rw [key h.gl e1 a1 b1]
    · rw [key h.gr e2 a2 b2]
  · cases hr

/-! ### The other instructions -/

/-- the known byte at an address of a jump's pointer -/
def memS (E : Rom) (Q : TS) (a : UInt16) : Option UInt8 :=
  match memT E Q a with
  | some t => t.same
  | none => none

theorem memS_spec {a : UInt16} {c : UInt8} (h : Lk E m₀ n₀ Q m n) (he : memS E Q a = some c) : okAd a ∧ memv E m a = c ∧ memv E n a = c := by
  unfold memS at he
  split at he
  · rename_i t h1
    obtain ⟨h2, h3⟩ := memT_spec h h1
    obtain ⟨h4, h5⟩ := t.same_spec he h3
    exact ⟨h2, h4, h5⟩
  · cases he

theorem lk_jmpi {lo hi' : UInt8} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hp1 : 0x8000 ≤ Q.pc + 1) (hp2 : 0x8000 ≤ Q.pc + 1 + 1)
    (hd : lookupOp (E.b Q.pc) insList = some .jmpi) (hi : idleAt E Q.pc = false)
    (h1 : memS E Q (E.w (Q.pc + 1)) = some lo)
    (h2 : memS E Q ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) = some hi') :
    Lk E m₀ n₀ { Q with pc := lo.toUInt16 ||| (hi'.toUInt16 <<< 8) } (go step m).2 (go step n).2 := by
  obtain ⟨u1, u2, u3⟩ := memS_spec h h1
  obtain ⟨v1, v2, v3⟩ := memS_spec h h2
  have el := h.pcl
  have er := h.pcr
  have key : ∀ {a : Machine}, Good E a → a.pc = Q.pc → memv E a (E.w (Q.pc + 1)) = lo → memv E a ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) = hi' →
      go (sem .jmpi) { a with pc := a.pc + 1 } = ((), { a with pc := lo.toUInt16 ||| (hi'.toUInt16 <<< 8) }) := by
    intro a ga ea w1 w2
    have g1 := ga.pc (a.pc + 1)
    have g2 := ga.pc (a.pc + 1 + 1 + 1)
    show go (fetch16 >>= fun ptr => rd ptr >>= fun lo => rd ((ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF)) >>= fun hi => setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) _ = _
    rw [PipeTransitionAll.go_bind, fetch16_eq g1 (by rw [ea]; exact hp1) (by rw [ea]; exact hp2), ea]
    show go (rd (E.w (Q.pc + 1)) >>= fun lo => rd ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) >>= fun hi => setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) { a with pc := Q.pc + 1 + 1 + 1 } = _
    have g3 := ga.pc (Q.pc + 1 + 1 + 1)
    have w3 : memv E { a with pc := Q.pc + 1 + 1 + 1 } (E.w (Q.pc + 1)) = lo := w1
    have w4 : memv E { a with pc := Q.pc + 1 + 1 + 1 } ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) = hi' := w2
    rw [PipeTransitionAll.go_bind, rd_ok g3 u1, w3]
    show go (rd ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) >>= fun hi => setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))) { a with pc := Q.pc + 1 + 1 + 1 } = _
    rw [PipeTransitionAll.go_bind, rd_ok g3 v1, w4]
    rfl
  refine lk_fin h hp hd hi ?_ ?_ (h.go_pc _)
  · rw [key h.gl el u2 v2]
  · rw [key h.gr er u3 v3]

/-- a load from a register -/
theorem lk_load {I : Ins} {f : RF} {t : Tag} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some I) (hi : idleAt E Q.pc = false)
    {val : Machine → UInt8} (hs : ∀ a : Machine, (go (sem I) a).2 = rfE f (val a) a) (hr : t.R (val m) (val n)) (hk : ∀ a p, val { a with pc := p } = val a) :
    Lk E m₀ n₀ (rfT f t { Q with pc := Q.pc + 1 }) (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  have base := h.go_pc (Q.pc + 1)
  have ga := rfE_good f (val m) base.gl
  have gb := rfE_good f (val n) base.gr
  have hn := base.regs_only (Q' := rfT f t { Q with pc := Q.pc + 1 }) (rfT_keep _ _ _) (rfE_keep _ _ _) (rfE_keep _ _ _) ga gb (rfT_R base.regs hr)
  refine lk_fin h hp hd hi ?_ ?_ hn
  · rw [hs, hk, el]
  · rw [hs, hk, er]

/-- a flag set or cleared -/
theorem lk_flag {I : Ins} {b : Bool} (h : Lk E m₀ n₀ Q m n) (hp : 0x8000 ≤ Q.pc) (hd : lookupOp (E.b Q.pc) insList = some I) (hi : idleAt E Q.pc = false)
    (hs : ∀ a : Machine, (go (sem I) a).2 = { a with p := setF a.p 0x01 b }) :
    Lk E m₀ n₀ { Q with pc := Q.pc + 1, c := .kn b b } (go step m).2 (go step n).2 := by
  have el := h.pcl
  have er := h.pcr
  have hn : Lk E m₀ n₀ { Q with pc := Q.pc + 1, c := .kn b b } { m with pc := Q.pc + 1, p := setF m.p 0x01 b } { n with pc := Q.pc + 1, p := setF n.p 0x01 b } :=
    ⟨⟨h.gl.prg, h.gl.mask, h.gl.nmi, h.gl.halted, h.gl.trk, h.gl.size, h.gl.ctl⟩, ⟨h.gr.prg, h.gr.mask, h.gr.nmi, h.gr.halted, h.gr.trk, h.gr.size, h.gr.ctl⟩, rfl, rfl,
      ⟨h.regs.a, h.regs.x, h.regs.y, ⟨setF_c _ _, setF_c _ _⟩,
        by show Q.z.R (bt (setF m.p 1 b) 1) (bt (setF n.p 1 b) 1); rw [setF_o _ _ (by decide) (by decide), setF_o _ _ (by decide) (by decide)]; exact h.regs.z,
        by show Q.n.R (bt (setF m.p 1 b) 7) (bt (setF n.p 1 b) 7); rw [setF_o _ _ (by decide) (by decide), setF_o _ _ (by decide) (by decide)]; exact h.regs.nf⟩,
      h.s, h.s0, h.ram, h.fixl, h.fixr⟩
  refine lk_fin h hp hd hi ?_ ?_ hn
  · rw [hs, el]
  · rw [hs, er]

/-! ### The step of the walk -/

/-- the states after an instruction; `none` when the walk cannot follow it -/
def exec (E : Rom) (Q : TS) : Ins → Option (List TS)
  | .rd f md =>
    match srcT E Q md with
    | some t => some [rfT f t { Q with pc := md.adv (Q.pc + 1) }]
    | none => none
  | .wr f md =>
    match dstT E Q md with
    | some a =>
      if a < 0x2000 then some [{ Q with pc := md.adv (Q.pc + 1), ram := upd Q.ram (a &&& 0x7FF).toNat (f.tag Q), w := updW Q.w (a &&& 0x7FF).toNat }] else none
    | none => none
  | .rmw f md =>
    match dstT E Q md with
    | some a =>
      if a < 0x2000 then
        let A := ufT f (Q.ram (a &&& 0x7FF).toNat) Q.c
        some [{ { Q with c := A.c, z := A.z, n := A.n, ram := upd Q.ram (a &&& 0x7FF).toNat A.r, w := updW Q.w (a &&& 0x7FF).toNat } with pc := md.adv (Q.pc + 1) }]
      else none
    | none => none
  | .acc f => some [{ Q with pc := Q.pc + 1, a := (ufT f Q.a Q.c).r, c := (ufT f Q.a Q.c).c, z := (ufT f Q.a Q.c).z, n := (ufT f Q.a Q.c).n }]
  | .br f =>
    match f.tag Q with
    | .any => none
    | .eq => some [brNext E Q f true, brNext E Q f false]
    | .kn b c => if b == c then some [brNext E Q f (b == f.set)] else none
  | .jmp => some [{ Q with pc := E.w (Q.pc + 1) }]
  | .jmpi =>
    match memS E Q (E.w (Q.pc + 1)), memS E Q ((E.w (Q.pc + 1) &&& 0xFF00) ||| ((E.w (Q.pc + 1) + 1) &&& 0x00FF)) with
    | some lo, some hi => some [{ Q with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8) }]
    | _, _ => none
  | .jsr =>
    match Q.s with
    | some sp =>
      let ret := Q.pc + 1 + 1 + 1 - 1
      let Q1 : TS := { { Q with ram := upd Q.ram (stkI sp) (Tag.kn (ret >>> 8).toUInt8 (ret >>> 8).toUInt8), w := updW Q.w (stkI sp) } with s := some (sp - 1) }
      let Q2 : TS := { { Q1 with ram := upd Q1.ram (stkI (sp - 1)) (Tag.kn ret.toUInt8 ret.toUInt8), w := updW Q1.w (stkI (sp - 1)) } with s := some (sp - 1 - 1) }
      some [{ Q2 with pc := E.w (Q.pc + 1) }]
    | none => none
  | .rts =>
    match Q.s with
    | some sp =>
      match retT Q sp with
      | some t => some [{ { Q with s := some (sp + 1 + 1) } with pc := t }]
      | none => none
    | none => none
  | .pha =>
    match Q.s with
    | some sp => some [{ { { Q with ram := upd Q.ram (stkI sp) Q.a, w := updW Q.w (stkI sp) } with s := some (sp - 1) } with pc := Q.pc + 1 }]
    | none => none
  | .pla =>
    match Q.s with
    | some sp => some [rfT .lda (Q.ram (stkI (sp + 1))) { { Q with s := some (sp + 1) } with pc := Q.pc + 1 }]
    | none => none
  | .clc => some [{ Q with pc := Q.pc + 1, c := .kn false false }]
  | .sec => some [{ Q with pc := Q.pc + 1, c := .kn true true }]
  | .tax => some [rfT .ldx Q.a { Q with pc := Q.pc + 1 }]
  | .tay => some [rfT .ldy Q.a { Q with pc := Q.pc + 1 }]
  | .txa => some [rfT .lda Q.x { Q with pc := Q.pc + 1 }]
  | .tya => some [rfT .lda Q.y { Q with pc := Q.pc + 1 }]
  | .inx => some [rfT .ldx (ufT .inc Q.x Q.c).r { Q with pc := Q.pc + 1 }]
  | .iny => some [rfT .ldy (ufT .inc Q.y Q.c).r { Q with pc := Q.pc + 1 }]
  | .dex => some [rfT .ldx (ufT .dec Q.x Q.c).r { Q with pc := Q.pc + 1 }]
  | .dey => some [rfT .ldy (ufT .dec Q.y Q.c).r { Q with pc := Q.pc + 1 }]

/-- one step of the walk -/
def tstep (E : Rom) (Q : TS) : Option (List TS) :=
  if decide (0x8000 ≤ Q.pc) && decide (0x8000 ≤ Q.pc + 1) && decide (0x8000 ≤ Q.pc + 1 + 1) && !idleAt E Q.pc then
    match lookupOp (E.b Q.pc) insList with
    | some I => exec E Q I
    | none => none
  else none

/-- `step` follows the walk -/
theorem tstep_spec {l : List TS} (he : tstep E Q = some l) (h : Lk E m₀ n₀ Q m n) : ∃ Q' ∈ l, Lk E m₀ n₀ Q' (go step m).2 (go step n).2 := by
  unfold tstep at he
  split at he
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨hp, hp1⟩, hp2⟩, hi⟩ := hc
    split at he
    · rename_i I hd
      have reg1 : (ufT .inc Q.x Q.c).r.R (m.x + 1) (n.x + 1) := (ufT_R h.regs.x h.regs.c).r_
      have reg2 : (ufT .inc Q.y Q.c).r.R (m.y + 1) (n.y + 1) := (ufT_R h.regs.y h.regs.c).r_
      have reg3 : (ufT .dec Q.x Q.c).r.R (m.x - 1) (n.x - 1) := (ufT_R h.regs.x h.regs.c).r_
      have reg4 : (ufT .dec Q.y Q.c).r.R (m.y - 1) (n.y - 1) := (ufT_R h.regs.y h.regs.c).r_
      cases I with
      | rd f md =>
        simp only [exec] at he
        split at he
        · rename_i t ht
          cases he
          exact ⟨_, List.mem_singleton.2 rfl, lk_rd h hp hp1 hp2 hd hi ht⟩
        · cases he
      | wr f md =>
        simp only [exec] at he
        split at he
        · rename_i a ha
          split at he
          · rename_i hl
            cases he
            exact ⟨_, List.mem_singleton.2 rfl, lk_wr h hp hp1 hp2 hd hi ha hl⟩
          · cases he
        · cases he
      | rmw f md =>
        simp only [exec] at he
        split at he
        · rename_i a ha
          split at he
          · rename_i hl
            cases he
            exact ⟨_, List.mem_singleton.2 rfl, lk_rmw h hp hp1 hp2 hd hi ha hl⟩
          · cases he
        · cases he
      | acc f =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_acc h hp hd hi⟩
      | br f =>
        have hF := BF.tag_R f h.regs
        simp only [exec] at he
        split at he
        · cases he
        · rename_i h1
          rw [h1] at hF
          cases he
          cases hb : bt m.p f.i
          · have h2 : bt n.p f.i = false := by rw [← hb]; exact hF.symm
            cases hs : (false == f.set)
            · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), by
                have := lk_br (b := false) h hp hp1 hd hi hb h2
                rwa [hs] at this⟩
            · exact ⟨_, List.mem_cons_self, by
                have := lk_br (b := false) h hp hp1 hd hi hb h2
                rwa [hs] at this⟩
          · have h2 : bt n.p f.i = true := by rw [← hb]; exact hF.symm
            cases hs : (true == f.set)
            · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), by
                have := lk_br (b := true) h hp hp1 hd hi hb h2
                rwa [hs] at this⟩
            · exact ⟨_, List.mem_cons_self, by
                have := lk_br (b := true) h hp hp1 hd hi hb h2
                rwa [hs] at this⟩
        · rename_i b c h1
          split at he
          · rename_i h3
            cases he
            rw [h1] at hF
            have e : b = c := beq_iff_eq.1 h3
            subst e
            exact ⟨_, List.mem_singleton.2 rfl, lk_br h hp hp1 hd hi hF.1 hF.2⟩
          · cases he
      | jmp =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_jmp h hp hp1 hp2 hd hi⟩
      | jmpi =>
        simp only [exec] at he
        split at he
        · rename_i lo hi' h1 h2
          cases he
          exact ⟨_, List.mem_singleton.2 rfl, lk_jmpi h hp hp1 hp2 hd hi h1 h2⟩
        · cases he
      | jsr =>
        simp only [exec] at he
        split at he
        · rename_i sp hs
          cases he
          exact ⟨_, List.mem_singleton.2 rfl, lk_jsr h hp hp1 hp2 hd hi hs⟩
        · cases he
      | rts =>
        simp only [exec] at he
        split at he
        · rename_i sp hs
          split at he
          · rename_i t ht
            cases he
            exact ⟨_, List.mem_singleton.2 rfl, lk_rts h hp hd hi hs ht⟩
          · cases he
        · cases he
      | pha =>
        simp only [exec] at he
        split at he
        · rename_i sp hs
          cases he
          exact ⟨_, List.mem_singleton.2 rfl, lk_pha h hp hd hi hs⟩
        · cases he
      | pla =>
        simp only [exec] at he
        split at he
        · rename_i sp hs
          cases he
          exact ⟨_, List.mem_singleton.2 rfl, lk_pla h hp hd hi hs⟩
        · cases he
      | clc =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_flag h hp hd hi (fun _ => rfl)⟩
      | sec =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_flag h hp hd hi (fun _ => rfl)⟩
      | tax =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.a) h hp hd hi (fun _ => rfl) h.regs.a (fun _ _ => rfl)⟩
      | tay =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.a) h hp hd hi (fun _ => rfl) h.regs.a (fun _ _ => rfl)⟩
      | txa =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.x) h hp hd hi (fun _ => rfl) h.regs.x (fun _ _ => rfl)⟩
      | tya =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.y) h hp hd hi (fun _ => rfl) h.regs.y (fun _ _ => rfl)⟩
      | inx =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.x + 1) h hp hd hi (fun _ => rfl) reg1 (fun _ _ => rfl)⟩
      | iny =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.y + 1) h hp hd hi (fun _ => rfl) reg2 (fun _ _ => rfl)⟩
      | dex =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.x - 1) h hp hd hi (fun _ => rfl) reg3 (fun _ _ => rfl)⟩
      | dey =>
        cases he
        exact ⟨_, List.mem_singleton.2 rfl, lk_load (val := fun a => a.y - 1) h hp hd hi (fun _ => rfl) reg4 (fun _ _ => rfl)⟩
    · cases he
  · cases he

/-! ### Many steps -/

/-- `k` instructions -/
def stepN : Nat → Machine → Machine
  | 0, m => m
  | k + 1, m => stepN k (go step m).2

theorem stepN_succ (k : Nat) (m : Machine) : stepN (k + 1) m = (go step (stepN k m)).2 := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    show stepN (k + 1) (go step m).2 = _
    rw [ih]
    rfl

theorem stepN_add (j k : Nat) (m : Machine) : stepN (j + k) m = stepN k (stepN j m) := by
  induction j generalizing m with
  | zero => simp [stepN]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega]
    show stepN (j + k) (go step m).2 = stepN k (stepN j (go step m).2)
    exact ih _

/-- from `Q`, step by step, until every path stops, and there `goal` holds -/
def walkT (E : Rom) (stop goal : TS → Bool) : Nat → TS → Bool
  | 0, _ => false
  | f + 1, Q =>
    if stop Q then goal Q
    else
      match tstep E Q with
      | some l => l.all (walkT E stop goal f)
      | none => false

/-- a walk that succeeds follows the two machines, whatever their other bytes are -/
theorem walkT_spec {stop goal : TS → Bool} : ∀ (f : Nat) (Q : TS) (m n : Machine), walkT E stop goal f Q = true → Lk E m₀ n₀ Q m n →
    ∃ k Q', k ≤ f ∧ stop Q' = true ∧ goal Q' = true ∧ Lk E m₀ n₀ Q' (stepN k m) (stepN k n) ∧
      ∀ j, j < k → ∃ Qj, stop Qj = false ∧ 0x8000 ≤ Qj.pc ∧ Lk E m₀ n₀ Qj (stepN j m) (stepN j n)
  | 0, _, _, _, h, _ => by cases h
  | f + 1, Q, m, n, h, hl => by
    unfold walkT at h
    split at h
    · rename_i h1
      exact ⟨0, Q, by omega, h1, h, hl, fun j hj => absurd hj (by omega)⟩
    · rename_i h1
      split at h
      · rename_i l h2
        obtain ⟨Q', h3, h4⟩ := tstep_spec h2 hl
        obtain ⟨k, R, h5, h6, h7, h8, h9⟩ := walkT_spec f Q' _ _ (List.all_eq_true.1 h Q' h3) h4
        refine ⟨k + 1, R, by omega, h6, h7, h8, ?_⟩
        intro j hj
        cases j with
        | zero =>
          refine ⟨Q, by simpa using h1, ?_, hl⟩
          unfold tstep at h2
          split at h2
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            exact hc.1.1.1
          · cases h2
        | succ j => exact h9 j (by omega)
      · cases h

/-! ## Pieces of one machine -/

/-- look a byte up in a list -/
def lookN {α : Type} (i : Nat) : List (Nat × α) → Option α
  | [] => none
  | p :: l => if p.1 == i then some p.2 else lookN i l

theorem lookN_mem {α : Type} {i : Nat} {a : α} : ∀ {l : List (Nat × α)}, lookN i l = some a → (i, a) ∈ l
  | [], h => by cases h
  | p :: l, h => by
    unfold lookN at h
    split at h
    · rename_i h1
      have e : p.1 = i := beq_iff_eq.1 h1
      have e2 := Option.some.inj h
      obtain ⟨u, v⟩ := p
      simp only at e e2
      subst e e2
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookN_mem h)

/-- what is known at a place in a run of one machine -/
structure Cut where
  pc : UInt16
  s : UInt8
  /-- bytes with known values -/
  K : List (Nat × UInt8)
  /-- bytes with some known bits -/
  B : List (Nat × AB) := []
  /-- A, X and the carry, if known -/
  ra : Option UInt8 := none
  x : Option UInt8 := none
  cf : Option Bool := none
  deriving Inhabited

/-- the machine is at the cut -/
structure At (E : Rom) (c : Cut) (m : Machine) : Prop where
  good : Good E m
  pc : m.pc = c.pc
  s : m.s = c.s
  K : ∀ p ∈ c.K, m.ram.get! p.1 = p.2
  B : ∀ p ∈ c.B, AB.mem p.2 (m.ram.get! p.1)
  ra : ∀ v, c.ra = some v → m.a = v
  x : ∀ v, c.x = some v → m.x = v
  cf : ∀ b, c.cf = some b → bt m.p 0 = b

/-- the walk's start at a cut; both machines are the same machine -/
def startQ (c : Cut) : TS :=
  { pc := c.pc, y := .eq, z := .eq, n := .eq,
    a := (match c.ra with | some v => Tag.kn v v | none => .eq),
    x := (match c.x with | some v => Tag.kn v v | none => .eq),
    c := (match c.cf with | some b => FT.kn b b | none => .eq),
    s := some c.s,
    ram := fun i =>
      match lookN i c.K with
      | some v => Tag.kn v v
      | none =>
        match lookN i c.B with
        | some a => .ab a a
        | none => .eq,
    w := fun _ => false }

theorem lk_self {c : Cut} {m : Machine} (h : At E c m) : Lk E m m (startQ c) m m := by
  refine ⟨h.good, h.good, h.pc, h.pc, ⟨?_, ?_, rfl, ?_, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (match c.ra with | some v => Tag.kn v v | none => Tag.eq).R m.a m.a
    cases hx : c.ra with
    | none => rfl
    | some v =>
      have e := h.ra v hx
      subst e
      exact Tag.R_kn _ _
  · show (match c.x with | some v => Tag.kn v v | none => Tag.eq).R m.x m.x
    cases hx : c.x with
    | none => rfl
    | some v =>
      have e := h.x v hx
      subst e
      exact Tag.R_kn _ _
  · show (match c.cf with | some b => FT.kn b b | none => FT.eq).R (bt m.p 0) (bt m.p 0)
    cases hx : c.cf with
    | none => rfl
    | some v =>
      have e := h.cf v hx
      subst e
      exact ⟨rfl, rfl⟩
  · intro v hv
    have e : c.s = v := Option.some.inj hv
    rw [h.s, e]
    exact ⟨rfl, rfl⟩
  · intro hv
    cases hv
  · intro i _
    show (match lookN i c.K with
      | some v => Tag.kn v v
      | none =>
        match lookN i c.B with
        | some a => .ab a a
        | none => .eq).R _ _
    cases h1 : lookN i c.K with
    | some v =>
      have e := h.K _ (lookN_mem h1)
      simp only at e
      rw [e]
      exact Tag.R_kn _ _
    | none =>
      cases h2 : lookN i c.B with
      | some a =>
        have e := h.B _ (lookN_mem h2)
        exact ⟨e, e⟩
      | none => rfl
  · intro _ _ _
    rfl
  · intro _ _ _
    rfl

/-- what the walk must know at the next cut, and the bytes it must not have written -/
def goalC (c' : Cut) (watch : List Nat) (Q : TS) : Bool :=
  Q.pc == c'.pc && Q.s == some c'.s && c'.B.isEmpty &&
    c'.K.all (fun p => decide (p.1 < 2048) && (Q.ram p.1).same == some p.2) && watch.all (fun i => !Q.w i) &&
    (match c'.ra with | some v => Q.a.same == some v | none => true) &&
    (match c'.x with | some v => Q.x.same == some v | none => true) &&
    (match c'.cf with
     | some b => (match Q.c with | .kn u v => u == b && v == b | _ => false)
     | none => true)

/-- the piece of the walk from one cut to the next -/
def pieceOK (E : Rom) (c c' : Cut) (watch : List Nat) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == c'.pc) (goalC c' watch) fuel (startQ c)

theorem mask_stk (sp : UInt8) : stkI sp < 2048 := PipeTransitionAll.mask_lt _

/-- what a walk's end says of the machine -/
theorem at_of_goal {c' : Cut} {watch : List Nat} {Q : TS} {m r : Machine} (hg : goalC c' watch Q = true) (h4 : Lk E m m Q r r) :
    At E c' r ∧ (∀ i ∈ watch, i < 2048 → r.ram.get! i = m.ram.get! i) ∧ (∀ p ∈ c'.K, p.1 < 2048) := by
  simp only [goalC, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨h6, h7⟩, h8⟩, h9⟩, h10⟩, h11a⟩, h11⟩, h12⟩ := hg
  refine ⟨⟨h4.gl, by rw [h4.pcl, h6], (h4.s _ h7).1, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun p hp => (h9 p hp).1⟩
  · intro p hp
    exact (Tag.same_spec (h9 p hp).2 (h4.ram _ (h9 p hp).1)).1
  · intro p hp
    simp only [List.isEmpty_iff] at h8
    rw [h8] at hp
    cases hp
  · intro v hv
    rw [hv] at h11a
    simp only [beq_iff_eq] at h11a
    exact (Tag.same_spec h11a h4.regs.a).1
  · intro v hv
    rw [hv] at h11
    simp only [beq_iff_eq] at h11
    exact (Tag.same_spec h11 h4.regs.x).1
  · intro b hb
    have h13 : (match Q.c with | .kn u v => u == b && v == b | _ => false) = true := by
      rw [hb] at h12
      exact h12
    have hr := h4.regs.c
    cases hq : Q.c with
    | kn u v =>
      rw [hq] at hr h13
      simp only [Bool.and_eq_true, beq_iff_eq] at h13
      rw [hr.1, h13.1]
    | any =>
      rw [hq] at h13
      cases h13
    | eq =>
      rw [hq] at h13
      cases h13
  · intro i hi hl
    exact h4.fixl i hl (h10 i hi)

/-- from one cut to the next, on a real machine -/
theorem piece_spec {c c' : Cut} {watch : List Nat} {fuel : Nat} {m : Machine} (hc : pieceOK E c c' watch fuel = true) (h : At E c m) :
    ∃ k, k ≤ fuel ∧ At E c' (stepN k m) ∧ (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ (∀ p ∈ c'.K, p.1 < 2048) := by
  obtain ⟨k, Q, h1, _, h3, h4, _⟩ := walkT_spec (m₀ := m) (n₀ := m) fuel (startQ c) m m hc (lk_self h)
  obtain ⟨a, b, d⟩ := at_of_goal h3 h4
  exact ⟨k, h1, a, b, d⟩

/-- the same, with something more that the walk's end says -/
theorem piece_specX {c c' : Cut} {watch : List Nat} {fuel : Nat} {extra : TS → Bool} {m : Machine}
    (hc : walkT E (fun Q => Q.pc == c'.pc) (fun Q => goalC c' watch Q && extra Q) fuel (startQ c) = true) (h : At E c m) :
    ∃ k Q, k ≤ fuel ∧ At E c' (stepN k m) ∧ (∀ i ∈ watch, i < 2048 → (stepN k m).ram.get! i = m.ram.get! i) ∧ (∀ p ∈ c'.K, p.1 < 2048) ∧
      extra Q = true ∧ Lk E m m Q (stepN k m) (stepN k m) := by
  obtain ⟨k, Q, h1, _, h3, h4, _⟩ := walkT_spec (m₀ := m) (n₀ := m) fuel (startQ c) m m hc (lk_self h)
  simp only [Bool.and_eq_true] at h3
  obtain ⟨a, b, d⟩ := at_of_goal h3.1 h4
  exact ⟨k, Q, h1, a, b, d, h3.2, h4⟩

/-! ## A routine of the game, next to `runSub` -/

/-- what the machine of the model keeps -/
structure GoodH (E : Rom) (h : Machine) : Prop where
  prg : h.prg = E.prg
  mask : h.prgMask = E.mask
  halted : h.halted = false
  trk : h.trk = false
  size : h.ram.size = 2048

/-- a known tag implies a tag at a cut -/
def tagImp (q t : Tag) : Bool :=
  match t with
  | .any => true
  | .eq => q.eqL
  | .nz =>
    match q with
    | .nz => true
    | _ => q.eqL
  | .ab _ _ => false

theorem tagImp_R {q t : Tag} {x y : UInt8} (h : tagImp q t = true) (r : q.R x y) : t.R x y := by
  cases t with
  | any => trivial
  | eq => exact q.eqL_spec h r
  | nz =>
    cases q with
    | nz => exact r
    | any => cases h
    | eq =>
      have e : x = y := r
      rw [e]
      exact Iff.rfl
    | ab a b =>
      have e := Tag.eqL_spec (t := .ab a b) h r
      rw [e]
      exact Iff.rfl
  | ab a b => cases h

/-- the start of a routine: only the listed bytes are related -/
def leafQ (entry : UInt16) (a : Tag) (L : List (Nat × Tag)) : TS :=
  { pc := entry, a, x := .any, y := .any, c := .any, z := .any, n := .any, s := none, ram := fun i => (lookN i L).getD .any, w := fun _ => false }

def goalL (r : UInt16) (Lo : List (Nat × Tag)) (watch : List Nat) (Q : TS) : Bool :=
  Q.pc == r && Q.s.isNone && Lo.all (fun p => decide (p.1 < 2048) && tagImp (Q.ram p.1) p.2) && watch.all (fun i => !Q.w i)

/-- the walk over a routine, on the two machines -/
def leafOK (E : Rom) (entry r : UInt16) (a : Tag) (L Lo : List (Nat × Tag)) (watch : List Nat) (fuel : Nat) : Bool :=
  walkT E (fun Q => Q.pc == r) (goalL r Lo watch) fuel (leafQ entry a L)

/-- the machine `runSub` starts from -/
def callM (H : Machine) (addr : UInt16) (a : UInt8) : Machine :=
  { H with a, x := 0, y := 0, ram := (H.ram.set! (stkI H.s) 0).set! (stkI (H.s - 1)) 0, s := H.s - 2, pc := addr, ppuCtrl := 0, nmiPending := false }

theorem runSub_eq (H : Machine) (addr : UInt16) (a : UInt8) : runSub H addr a 0 0 = callRange.go 1 (callM H addr a) 2000 := rfl

theorem crun : ∀ (k fuel : Nat) (n : Machine), k < fuel → (∀ j, j ≤ k → (stepN j n).pc ≠ 1 ∧ (stepN j n).halted = false) → (stepN (k + 1) n).pc = 1 →
    callRange.go 1 n fuel = stepN (k + 1) n := by
  intro k
  induction k with
  | zero =>
    intro fuel n h1 h2 h3
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨h4, h5⟩ := h2 0 (by omega)
    have h6 : (n.pc == 1 || n.halted) = false := by
      have h7 : n.pc ≠ 1 := h4
      have h8 : n.halted = false := h5
      simp [h7, h8]
    show (if (n.pc == 1 || n.halted) = true then n else callRange.go 1 (step.run n).2 f) = _
    rw [if_neg (by rw [h6]; decide)]
    have e : (step.run n).2 = stepN 1 n := rfl
    rw [e]
    cases f with
    | zero => rfl
    | succ f =>
      show (if ((stepN 1 n).pc == 1 || (stepN 1 n).halted) = true then stepN 1 n else _) = _
      rw [if_pos (by rw [h3]; rfl)]
  | succ k ih =>
    intro fuel n h1 h2 h3
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨h4, h5⟩ := h2 0 (by omega)
    have h6 : (n.pc == 1 || n.halted) = false := by
      have h7 : n.pc ≠ 1 := h4
      have h8 : n.halted = false := h5
      simp [h7, h8]
    show (if (n.pc == 1 || n.halted) = true then n else callRange.go 1 (step.run n).2 f) = _
    rw [if_neg (by rw [h6]; decide)]
    have e : (step.run n).2 = (go step n).2 := rfl
    rw [e]
    exact ih f _ (by omega) (fun j hj => h2 (j + 1) (by omega)) h3

set_option maxRecDepth 100000 in
theorem stack_two (sp : UInt8) : sp - 2 + 1 = sp - 1 ∧ sp - 2 + 1 + 1 = sp := by
  have h : ∀ n : Fin 256, n.val.toUInt8 - 2 + 1 = n.val.toUInt8 - 1 ∧ n.val.toUInt8 - 2 + 1 + 1 = n.val.toUInt8 := by decide
  have e := h ⟨sp.toNat, sp.toNat_lt⟩
  simpa using e

theorem step_rts {X : Machine} (g : Good E X) (hp : 0x8000 ≤ X.pc) (hd : lookupOp (E.b X.pc) insList = some .rts) (hi : idleAt E X.pc = false) :
    (go step X).2.pc = ((X.ram.get! (stkI (X.s + 1))).toUInt16 ||| ((X.ram.get! (stkI (X.s + 1 + 1))).toUInt16 <<< 8)) + 1 ∧
      (go step X).2.s = X.s + 1 + 1 ∧ (go step X).2.ram = X.ram ∧ Good E (go step X).2 := by
  have g1 := g.pc (X.pc + 1)
  have e6 : go (sem .rts) { X with pc := X.pc + 1 } = go opRTS { X with pc := X.pc + 1 } := rfl
  have e5 := rts_eff g1
  have g2 : Good E { { X with s := X.s + 1 + 1 } with pc := ((X.ram.get! (stkI (X.s + 1))).toUInt16 ||| ((X.ram.get! (stkI (X.s + 1 + 1))).toUInt16 <<< 8)) + 1 } :=
    ⟨g.prg, g.mask, g.nmi, g.halted, g.trk, g.size, g.ctl⟩
  have e7 : nt (go (sem .rts) { X with pc := X.pc + 1 }).2 = nt { { X with s := X.s + 1 + 1 } with pc := ((X.ram.get! (stkI (X.s + 1))).toUInt16 ||| ((X.ram.get! (stkI (X.s + 1 + 1))).toUInt16 <<< 8)) + 1 } := by
    rw [e6, e5]
  have e8 := step_nt g hp hd hi e7 g2
  exact ⟨(congrArg Machine.pc e8 : (nt _).pc = (nt _).pc), (congrArg Machine.s e8 : (nt _).s = (nt _).s), (congrArg Machine.ram e8 : (nt _).ram = (nt _).ram), Good.of_nt e8 g2⟩

theorem get_set2 {r : ByteArray} {i j p : Nat} {v w : UInt8} (h1 : p ≠ i) (h2 : p ≠ j) : ((r.set! i v).set! j w).get! p = r.get! p := by
  rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h2 e.symm), PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e => h1 e.symm)]

theorem size_set2 {r : ByteArray} {i j : Nat} {v w : UInt8} : ((r.set! i v).set! j w).size = r.size := by
  rw [PipeTransitionAll.ba_size_set, PipeTransitionAll.ba_size_set]

/-- a routine with a single return, on the real machine and in `runSub`: the listed bytes stay related -/
theorem leaf_spec {entry r : UInt16} {a : Tag} {ain : UInt8} {L Lo : List (Nat × Tag)} {watch : List Nat} {fuel : Nat} {R H : Machine}
    (hc : leafOK E entry r a L Lo watch fuel = true) (hfuel : fuel < 2000) (hr80 : 0x8000 ≤ r)
    (hop : lookupOp (E.b r) insList = some .rts) (hidle : idleAt E r = false)
    (gR : Good E R) (pcR : R.pc = entry) (ha : a.R R.a ain) (gH : GoodH E H)
    (hL : ∀ p ∈ L, p.1 < 2048 ∧ p.1 ≠ stkI H.s ∧ p.1 ≠ stkI (H.s - 1) ∧ p.2.R (R.ram.get! p.1) (H.ram.get! p.1))
    (hw1 : stkI H.s ∈ watch) (hw2 : stkI (H.s - 1) ∈ watch) :
    ∃ k, k ≤ fuel ∧ Good E (stepN k R) ∧ (stepN k R).pc = r ∧ (stepN k R).s = R.s ∧
      (∀ p ∈ Lo, p.2.R ((stepN k R).ram.get! p.1) ((runSub H entry ain 0 0).ram.get! p.1)) ∧
      (∀ i ∈ watch, i < 2048 → (stepN k R).ram.get! i = R.ram.get! i) ∧
      (∀ i ∈ watch, i < 2048 → i ≠ stkI H.s → i ≠ stkI (H.s - 1) → (runSub H entry ain 0 0).ram.get! i = H.ram.get! i) ∧
      GoodH E (runSub H entry ain 0 0) ∧ (runSub H entry ain 0 0).s = H.s := by
  have g1 : Good E (callM H entry ain) := by
    refine ⟨gH.prg, gH.mask, rfl, gH.halted, gH.trk, ?_, (by decide : (0 : UInt8) &&& 0x80 = 0)⟩
    show ((H.ram.set! _ _).set! _ _).size = 2048
    rw [size_set2]
    exact gH.size
  have hs1 : (callM H entry ain).ram.size = 2048 := g1.size
  have st : Lk E R (callM H entry ain) (leafQ entry a L) R (callM H entry ain) := by
    refine ⟨gR, g1, pcR, rfl, ⟨ha, trivial, trivial, trivial, trivial, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      cases hv
    · intro _
      exact ⟨rfl, rfl⟩
    · intro i _
      show ((lookN i L).getD .any).R _ _
      cases h1 : lookN i L with
      | none => trivial
      | some t =>
        obtain ⟨_, h3, h4, h5⟩ := hL _ (lookN_mem h1)
        show t.R _ ((H.ram.set! _ _).set! _ _ |>.get! i)
        rw [get_set2 h3 h4]
        exact h5
    · intro _ _ _
      rfl
    · intro _ _ _
      rfl
  obtain ⟨k, Q, h1, _, h3, h4, h5⟩ := walkT_spec fuel _ R _ hc st
  simp only [goalL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq, Option.isNone_iff_eq_none] at h3
  obtain ⟨⟨⟨h6, h7⟩, h8⟩, h9⟩ := h3
  have hX := h4.gr
  have hXpc : (stepN k (callM H entry ain)).pc = r := by rw [h4.pcr, h6]
  have hXs : (stepN k (callM H entry ain)).s = H.s - 2 := (h4.s0 h7).2
  have hb1 : (stepN k (callM H entry ain)).ram.get! (stkI (H.s - 1)) = 0 := by
    rw [h4.fixr _ (mask_stk _) (h9 _ hw2)]
    show ((H.ram.set! _ _).set! _ _).get! _ = 0
    rw [PipeTransitionAll.ba_get_set_self _ _ _ (by
      rw [PipeTransitionAll.ba_size_set, gH.size]
      exact mask_stk _)]
  have hb2 : (stepN k (callM H entry ain)).ram.get! (stkI H.s) = 0 := by
    rw [h4.fixr _ (mask_stk _) (h9 _ hw1)]
    show ((H.ram.set! _ _).set! _ _).get! _ = 0
    by_cases e : stkI H.s = stkI (H.s - 1)
    · rw [e, PipeTransitionAll.ba_get_set_self _ _ _ (by
        rw [PipeTransitionAll.ba_size_set, gH.size]
        exact mask_stk _)]
    · rw [PipeTransitionAll.ba_get_set_ne _ _ _ _ (fun e2 => e e2.symm), PipeTransitionAll.ba_get_set_self _ _ _ (by rw [gH.size]; exact mask_stk _)]
  obtain ⟨y1, y2, y3, y4⟩ := step_rts hX (by rw [hXpc]; exact hr80) (by rw [hXpc]; exact hop) (by rw [hXpc]; exact hidle)
  obtain ⟨sp1, sp2⟩ := stack_two H.s
  have hYpc : (stepN (k + 1) (callM H entry ain)).pc = 1 := by
    rw [stepN_succ, y1, hXs, sp2, sp1, hb1, hb2]
    decide
  have hrun : runSub H entry ain 0 0 = stepN (k + 1) (callM H entry ain) := by
    rw [runSub_eq]
    refine crun k 2000 _ (by omega) ?_ hYpc
    intro j hj
    have hne : ∀ u : UInt16, 0x8000 ≤ u → u ≠ 1 := by
      intro u hu e
      subst e
      exact absurd hu (by decide)
    by_cases hjk : j = k
    · subst hjk
      exact ⟨by rw [hXpc]; exact hne _ hr80, hX.halted⟩
    · obtain ⟨Qj, _, h10, h11⟩ := h5 j (by omega)
      exact ⟨by rw [h11.pcr]; exact hne _ h10, h11.gr.halted⟩
  have hram : (runSub H entry ain 0 0).ram = (stepN k (callM H entry ain)).ram := by
    rw [hrun, stepN_succ]
    exact y3
  refine ⟨k, h1, h4.gl, by rw [h4.pcl, h6], (h4.s0 h7).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hram]
    exact tagImp_R (h8 p hp).2 (h4.ram _ (h8 p hp).1)
  · intro i hi hl
    exact h4.fixl i hl (h9 i hi)
  · intro i hi hl h10 h11
    rw [hram, h4.fixr i hl (h9 i hi)]
    show ((H.ram.set! _ _).set! _ _).get! i = _
    rw [get_set2 h10 h11]
  · have g3 : Good E (runSub H entry ain 0 0) := by
      rw [hrun, stepN_succ]
      exact y4
    exact ⟨g3.prg, g3.mask, g3.halted, g3.trk, g3.size⟩
  · rw [hrun, stepN_succ, y2, hXs, sp2]

end walk

end Smbrta.FrameModel
