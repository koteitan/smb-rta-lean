import Smbrta.Machine

/-!
# 6502 (2A03) CPU

All official opcodes plus the stable unofficial ones that nestest checks
(NOP variants, LAX, SAX, SBC $EB, DCP, ISB, SLO, RLA, SRE, RRA).
The other unofficial opcodes stop the machine (`halted := true`).
The 2A03 has no decimal mode, so the D flag does not change ADC/SBC.
-/

namespace Smbrta

/-! ## Fetch and addressing modes -/

@[inline] def fetch : M UInt8 := do
  let m ← get
  let pc := m.pc
  set { m with pc := pc + 1 }
  rd pc

@[inline] def fetch16 : M UInt16 := do
  let lo ← fetch
  let hi ← fetch
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- read a 16-bit pointer from zero page; the high byte wraps inside page 0 -/
@[inline] def rd16zp (z : UInt8) : M UInt16 := do
  let lo ← rd z.toUInt16
  let hi ← rd (z + 1).toUInt16
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- An addressing mode computes the effective address. -/
abbrev Mode := M UInt16

def mImm : Mode := do
  let m ← get
  let pc := m.pc
  set { m with pc := pc + 1 }
  return pc
def mZp : Mode := return (← fetch).toUInt16
def mZpx : Mode := do let b ← fetch; return (b + (← get).x).toUInt16
def mZpy : Mode := do let b ← fetch; return (b + (← get).y).toUInt16
def mAbs : Mode := fetch16
/-- page-cross penalty: one extra cycle when `b` and `e` are on different pages -/
@[inline] def pagePenalty (b e : UInt16) : M Unit :=
  if (b ^^^ e) &&& 0xFF00 != 0 then tick 1 else pure ()
def mAbx : Mode := do let b ← fetch16; return b + (← get).x.toUInt16
def mAby : Mode := do let b ← fetch16; return b + (← get).y.toUInt16
def mAbxR : Mode := do
  let b ← fetch16; let e := b + (← get).x.toUInt16; pagePenalty b e; return e
def mAbyR : Mode := do
  let b ← fetch16; let e := b + (← get).y.toUInt16; pagePenalty b e; return e
def mIzx : Mode := do let z ← fetch; rd16zp (z + (← get).x)
def mIzy : Mode := do let z ← fetch; let b ← rd16zp z; return b + (← get).y.toUInt16
def mIzyR : Mode := do
  let z ← fetch; let b ← rd16zp z; let e := b + (← get).y.toUInt16; pagePenalty b e; return e

/-! ## Flags -/

@[inline] def setZN (v : UInt8) : M Unit := modify fun m =>
  { m with p := (m.p &&& 0x7D) ||| (if v == 0 then 0x02 else 0) ||| (v &&& 0x80) }

@[inline] def setFlag (mask : UInt8) (b : Bool) : M Unit := modify fun m =>
  { m with p := if b then m.p ||| mask else m.p &&& ~~~mask }

@[inline] def setA (v : UInt8) : M Unit := do modify (fun m => { m with a := v }); setZN v
@[inline] def setX (v : UInt8) : M Unit := do modify (fun m => { m with x := v }); setZN v
@[inline] def setY (v : UInt8) : M Unit := do modify (fun m => { m with y := v }); setZN v

/-! ## Stack -/

@[inline] def push (v : UInt8) : M Unit := do
  let m ← get
  let sp := m.s
  set { m with s := sp - 1 }
  wr (0x100 ||| sp.toUInt16) v

@[inline] def pull : M UInt8 := do
  let m ← get
  let sp := m.s + 1
  set { m with s := sp }
  rd (0x100 ||| sp.toUInt16)

@[inline] def setPC (pc : UInt16) : M Unit := modify fun m => { m with pc }

/-! ## ALU helpers -/

def adc (v : UInt8) : M Unit := modify fun m =>
  let s := m.a.toUInt16 + v.toUInt16 + (m.p &&& 1).toUInt16
  let r := s.toUInt8
  let ovf := (m.a ^^^ r) &&& (v ^^^ r) &&& 0x80 != 0
  let p := (m.p &&& 0x3C) ||| (if s > 0xFF then 0x01 else 0) ||| (if r == 0 then 0x02 else 0)
    ||| (r &&& 0x80) ||| (if ovf then 0x40 else 0)
  { m with a := r, p }

@[inline] def oraV (v : UInt8) : M Unit := do setA ((← get).a ||| v)
@[inline] def andV (v : UInt8) : M Unit := do setA ((← get).a &&& v)
@[inline] def eorV (v : UInt8) : M Unit := do setA ((← get).a ^^^ v)
@[inline] def cmpV (r v : UInt8) : M Unit := do setZN (r - v); setFlag 0x01 (r ≥ v)

def aslV (v : UInt8) : M UInt8 := do
  let r := v <<< 1; setFlag 0x01 (v &&& 0x80 != 0); setZN r; return r
def lsrV (v : UInt8) : M UInt8 := do
  let r := v >>> 1; setFlag 0x01 (v &&& 1 != 0); setZN r; return r
def rolV (v : UInt8) : M UInt8 := do
  let c := (← get).p &&& 1
  let r := (v <<< 1) ||| c; setFlag 0x01 (v &&& 0x80 != 0); setZN r; return r
def rorV (v : UInt8) : M UInt8 := do
  let c := (← get).p &&& 1
  let r := (v >>> 1) ||| (c <<< 7); setFlag 0x01 (v &&& 1 != 0); setZN r; return r
def incV (v : UInt8) : M UInt8 := do let r := v + 1; setZN r; return r
def decV (v : UInt8) : M UInt8 := do let r := v - 1; setZN r; return r

/-! ## Instructions -/

def opLDA (md : Mode) : M Unit := do setA (← rd (← md))
def opLDX (md : Mode) : M Unit := do setX (← rd (← md))
def opLDY (md : Mode) : M Unit := do setY (← rd (← md))
def opLAX (md : Mode) : M Unit := do
  let v ← rd (← md); modify (fun m => { m with a := v, x := v }); setZN v
def opSTA (md : Mode) : M Unit := do let ad ← md; wr ad (← get).a
def opSTX (md : Mode) : M Unit := do let ad ← md; wr ad (← get).x
def opSTY (md : Mode) : M Unit := do let ad ← md; wr ad (← get).y
def opSAX (md : Mode) : M Unit := do let ad ← md; let m ← get; wr ad (m.a &&& m.x)
def opADC (md : Mode) : M Unit := do adc (← rd (← md))
def opSBC (md : Mode) : M Unit := do adc (~~~(← rd (← md)))
def opORA (md : Mode) : M Unit := do oraV (← rd (← md))
def opAND (md : Mode) : M Unit := do andV (← rd (← md))
def opEOR (md : Mode) : M Unit := do eorV (← rd (← md))
def opCMP (md : Mode) : M Unit := do let v ← rd (← md); cmpV (← get).a v
def opCPX (md : Mode) : M Unit := do let v ← rd (← md); cmpV (← get).x v
def opCPY (md : Mode) : M Unit := do let v ← rd (← md); cmpV (← get).y v
def opBIT (md : Mode) : M Unit := do
  let v ← rd (← md)
  modify fun m => { m with p := (m.p &&& 0x3D) ||| (v &&& 0xC0) ||| (if m.a &&& v == 0 then 0x02 else 0) }

/-- read-modify-write on memory -/
@[inline] def rmw (f : UInt8 → M UInt8) (md : Mode) : M Unit := do
  let ad ← md; let v ← rd ad; let r ← f v; wr ad r
/-- read-modify-write on memory, then use the result -/
@[inline] def rmw2 (f : UInt8 → M UInt8) (g : UInt8 → M Unit) (md : Mode) : M Unit := do
  let ad ← md; let v ← rd ad; let r ← f v; wr ad r; g r
@[inline] def accOp (f : UInt8 → M UInt8) : M Unit := do
  let r ← f (← get).a; modify fun m => { m with a := r }

def opASL := rmw aslV
def opLSR := rmw lsrV
def opROL := rmw rolV
def opROR := rmw rorV
def opINC := rmw incV
def opDEC := rmw decV
def opSLO := rmw2 aslV oraV
def opRLA := rmw2 rolV andV
def opSRE := rmw2 lsrV eorV
def opRRA := rmw2 rorV adc
def opDCP := rmw2 (fun v => pure (v - 1)) (fun r => do cmpV (← get).a r)
def opISB := rmw2 (fun v => pure (v + 1)) (fun r => adc (~~~r))

def opNOPm (md : Mode) : M Unit := do let _ ← md; pure ()
def opNOP : M Unit := pure ()
def opJAM : M Unit := modify fun m => { m with halted := true, pc := m.pc - 1 }

def branch (cond : Machine → Bool) : M Unit := do
  let off ← fetch
  let m ← get
  if cond m then
    let pc := m.pc
    let t := pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0))
    setPC t
    tick (if (pc ^^^ t) &&& 0xFF00 != 0 then 2 else 1)

def opBPL := branch fun m => m.p &&& 0x80 == 0
def opBMI := branch fun m => m.p &&& 0x80 != 0
def opBVC := branch fun m => m.p &&& 0x40 == 0
def opBVS := branch fun m => m.p &&& 0x40 != 0
def opBCC := branch fun m => m.p &&& 0x01 == 0
def opBCS := branch fun m => m.p &&& 0x01 != 0
def opBNE := branch fun m => m.p &&& 0x02 == 0
def opBEQ := branch fun m => m.p &&& 0x02 != 0

def opCLC := setFlag 0x01 false
def opSEC := setFlag 0x01 true
def opCLI := setFlag 0x04 false
def opSEI := setFlag 0x04 true
def opCLV := setFlag 0x40 false
def opCLD := setFlag 0x08 false
def opSED := setFlag 0x08 true

def opTAX : M Unit := do setX (← get).a
def opTAY : M Unit := do setY (← get).a
def opTXA : M Unit := do setA (← get).x
def opTYA : M Unit := do setA (← get).y
def opTSX : M Unit := do setX (← get).s
def opTXS : M Unit := modify fun m => { m with s := m.x }
def opINX : M Unit := do setX ((← get).x + 1)
def opINY : M Unit := do setY ((← get).y + 1)
def opDEX : M Unit := do setX ((← get).x - 1)
def opDEY : M Unit := do setY ((← get).y - 1)

def opPHA : M Unit := do push (← get).a
def opPHP : M Unit := do push ((← get).p ||| 0x30)
def opPLA : M Unit := do setA (← pull)
def opPLP : M Unit := do let v ← pull; modify fun m => { m with p := (v &&& 0xEF) ||| 0x20 }

def opJMP : M Unit := do setPC (← fetch16)
def opJMPi : M Unit := do
  let ptr ← fetch16
  let lo ← rd ptr
  let hi ← rd ((ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF))  -- page-wrap bug
  setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))
def opJSR : M Unit := do
  let t ← fetch16
  let ret := (← get).pc - 1
  push (ret >>> 8).toUInt8; push ret.toUInt8; setPC t
def opRTS : M Unit := do
  let lo ← pull; let hi ← pull
  setPC ((lo.toUInt16 ||| (hi.toUInt16 <<< 8)) + 1)
def opRTI : M Unit := do
  opPLP
  let lo ← pull; let hi ← pull
  setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))

/-- push PC and P, set I, jump through `vector` -/
def interrupt (pc : UInt16) (pushedP : UInt8) (vector : UInt16) : M Unit := do
  push (pc >>> 8).toUInt8; push pc.toUInt8; push pushedP
  setFlag 0x04 true
  let lo ← rd vector; let hi ← rd (vector + 1)
  setPC (lo.toUInt16 ||| (hi.toUInt16 <<< 8))

def opBRK : M Unit := do
  let m ← get
  interrupt (m.pc + 1) (m.p ||| 0x30) 0xFFFE

def nmi : M Unit := do
  let m ← get
  let pc := m.pc; let p := m.p
  set { m with nmiPending := false }
  interrupt pc ((p &&& 0xEF) ||| 0x20) 0xFFFA
  tick 7

def reset : M Unit := do
  let lo ← rd 0xFFFC; let hi ← rd 0xFFFD
  modify fun m => { m with pc := lo.toUInt16 ||| (hi.toUInt16 <<< 8), s := 0xFD, p := 0x24 }
  tick 7

/-! ## Opcode tables -/

/-- base cycle count of each opcode (page-cross and branch cycles are added by the instruction) -/
def cycTable : ByteArray := ByteArray.mk #[
  7,6,2,8,3,3,5,5,3,2,2,2,4,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7,
  6,6,2,8,3,3,5,5,4,2,2,2,4,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7,
  6,6,2,8,3,3,5,5,3,2,2,2,3,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7,
  6,6,2,8,3,3,5,5,4,2,2,2,5,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7,
  2,6,2,6,3,3,3,3,2,2,2,2,4,4,4,4,
  2,6,2,6,4,4,4,4,2,5,2,5,5,5,5,5,
  2,6,2,6,3,3,3,3,2,2,2,2,4,4,4,4,
  2,5,2,5,4,4,4,4,2,4,2,4,4,4,4,4,
  2,6,2,8,3,3,5,5,2,2,2,2,4,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7,
  2,6,2,8,3,3,5,5,2,2,2,2,4,4,6,6,
  2,5,2,8,4,4,6,6,2,4,2,7,4,4,7,7]

/-- the action of each opcode (after the opcode byte has been fetched) -/
def opTable : Array (M Unit) := #[
  -- 0x00
  opBRK, opORA mIzx, opJAM, opSLO mIzx, opNOPm mZp, opORA mZp, opASL mZp, opSLO mZp,
  opPHP, opORA mImm, accOp aslV, opJAM, opNOPm mAbs, opORA mAbs, opASL mAbs, opSLO mAbs,
  -- 0x10
  opBPL, opORA mIzyR, opJAM, opSLO mIzy, opNOPm mZpx, opORA mZpx, opASL mZpx, opSLO mZpx,
  opCLC, opORA mAbyR, opNOP, opSLO mAby, opNOPm mAbxR, opORA mAbxR, opASL mAbx, opSLO mAbx,
  -- 0x20
  opJSR, opAND mIzx, opJAM, opRLA mIzx, opBIT mZp, opAND mZp, opROL mZp, opRLA mZp,
  opPLP, opAND mImm, accOp rolV, opJAM, opBIT mAbs, opAND mAbs, opROL mAbs, opRLA mAbs,
  -- 0x30
  opBMI, opAND mIzyR, opJAM, opRLA mIzy, opNOPm mZpx, opAND mZpx, opROL mZpx, opRLA mZpx,
  opSEC, opAND mAbyR, opNOP, opRLA mAby, opNOPm mAbxR, opAND mAbxR, opROL mAbx, opRLA mAbx,
  -- 0x40
  opRTI, opEOR mIzx, opJAM, opSRE mIzx, opNOPm mZp, opEOR mZp, opLSR mZp, opSRE mZp,
  opPHA, opEOR mImm, accOp lsrV, opJAM, opJMP, opEOR mAbs, opLSR mAbs, opSRE mAbs,
  -- 0x50
  opBVC, opEOR mIzyR, opJAM, opSRE mIzy, opNOPm mZpx, opEOR mZpx, opLSR mZpx, opSRE mZpx,
  opCLI, opEOR mAbyR, opNOP, opSRE mAby, opNOPm mAbxR, opEOR mAbxR, opLSR mAbx, opSRE mAbx,
  -- 0x60
  opRTS, opADC mIzx, opJAM, opRRA mIzx, opNOPm mZp, opADC mZp, opROR mZp, opRRA mZp,
  opPLA, opADC mImm, accOp rorV, opJAM, opJMPi, opADC mAbs, opROR mAbs, opRRA mAbs,
  -- 0x70
  opBVS, opADC mIzyR, opJAM, opRRA mIzy, opNOPm mZpx, opADC mZpx, opROR mZpx, opRRA mZpx,
  opSEI, opADC mAbyR, opNOP, opRRA mAby, opNOPm mAbxR, opADC mAbxR, opROR mAbx, opRRA mAbx,
  -- 0x80
  opNOPm mImm, opSTA mIzx, opNOPm mImm, opSAX mIzx, opSTY mZp, opSTA mZp, opSTX mZp, opSAX mZp,
  opDEY, opNOPm mImm, opTXA, opJAM, opSTY mAbs, opSTA mAbs, opSTX mAbs, opSAX mAbs,
  -- 0x90
  opBCC, opSTA mIzy, opJAM, opJAM, opSTY mZpx, opSTA mZpx, opSTX mZpy, opSAX mZpy,
  opTYA, opSTA mAby, opTXS, opJAM, opJAM, opSTA mAbx, opJAM, opJAM,
  -- 0xA0
  opLDY mImm, opLDA mIzx, opLDX mImm, opLAX mIzx, opLDY mZp, opLDA mZp, opLDX mZp, opLAX mZp,
  opTAY, opLDA mImm, opTAX, opJAM, opLDY mAbs, opLDA mAbs, opLDX mAbs, opLAX mAbs,
  -- 0xB0
  opBCS, opLDA mIzyR, opJAM, opLAX mIzyR, opLDY mZpx, opLDA mZpx, opLDX mZpy, opLAX mZpy,
  opCLV, opLDA mAbyR, opTSX, opJAM, opLDY mAbxR, opLDA mAbxR, opLDX mAbyR, opLAX mAbyR,
  -- 0xC0
  opCPY mImm, opCMP mIzx, opNOPm mImm, opDCP mIzx, opCPY mZp, opCMP mZp, opDEC mZp, opDCP mZp,
  opINY, opCMP mImm, opDEX, opJAM, opCPY mAbs, opCMP mAbs, opDEC mAbs, opDCP mAbs,
  -- 0xD0
  opBNE, opCMP mIzyR, opJAM, opDCP mIzy, opNOPm mZpx, opCMP mZpx, opDEC mZpx, opDCP mZpx,
  opCLD, opCMP mAbyR, opNOP, opDCP mAby, opNOPm mAbxR, opCMP mAbxR, opDEC mAbx, opDCP mAbx,
  -- 0xE0
  opCPX mImm, opSBC mIzx, opNOPm mImm, opISB mIzx, opCPX mZp, opSBC mZp, opINC mZp, opISB mZp,
  opINX, opSBC mImm, opNOP, opSBC mImm, opCPX mAbs, opSBC mAbs, opINC mAbs, opISB mAbs,
  -- 0xF0
  opBEQ, opSBC mIzyR, opJAM, opISB mIzy, opNOPm mZpx, opSBC mZpx, opINC mZpx, opISB mZpx,
  opSED, opSBC mAbyR, opNOP, opISB mAby, opNOPm mAbxR, opSBC mAbxR, opINC mAbx, opISB mAbx]

/-! ## Stepping -/

/-- Number of CPU cycles until the next PPU event, rounded up to a multiple of 3. -/
def cyclesToNextEvent (m : Machine) : Nat :=
  let f := m.fdot
  let next :=
    if f < dotVblSet then dotVblSet
    else if f < dotVblClr then dotVblClr
    else if f < dotSpr0 then dotSpr0
    else dotsPerFrame
  let c := (next - f + 2) / 3
  ((c + 2) / 3) * 3

/-- Execute one instruction (or take a pending NMI). -/
def step : M Unit := do
  let m ← get
  if m.nmiPending then nmi
  else if m.halted then pure ()
  else
    let pc := m.pc
    let op ← fetch
    -- idle loop `JMP *`: skip straight to the next PPU event
    if op == 0x4C && m.prg.get! ((pc + 1) &&& m.prgMask).toNat == pc.toUInt8
        && m.prg.get! ((pc + 2) &&& m.prgMask).toNat == (pc >>> 8).toUInt8 && pc ≥ 0x8000 then
      setPC pc
      tick (cyclesToNextEvent m)
    else
      (opTable[op.toNat]?.getD opJAM)
      tick (cycTable.get! op.toNat).toNat

/-- Run at most `fuel` instructions, until the frame counter reaches `target` or the CPU halts. -/
def runUntilFrame (target : Nat) : Nat → M Unit
  | 0 => pure ()
  | fuel + 1 => do
    let m ← get
    if m.frame ≥ target || m.halted then pure ()
    else
      step
      runUntilFrame target fuel

end Smbrta
