import Theorems.TaintRun
import Theorems.PipeChangeBound
import Theorems.SideTransition
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# The first frames of the change out of the side pipe, from one frame

`Route` assumes `change₂ : room.E + 282 ≤ Cs`. The change has `A` frames of the pipe's timer and `B` frames after it. Here the first `A` frames are proved for every entry state that meets
a condition on one state (`EntryCond`), for any inputs. The proof looks at one frame only: an abstract machine follows one frame with the pad not known and the timer free, and the table of
abstract states closes (`inv_step`). A number `left` is the timer and `B` during the pipe. So a frame of the pipe takes at most one off `left` (`fall_of_inv`). The frames after the pipe are not
proved here: `no_control_all` and `ChangeRun` keep a hypothesis on them.

The abstract machine is a copy of the one in `TaintRun.lean`, with these changes. `TaintRun.lean` proves the bits of a byte and the `AB` operations; this file imports them.
* The pad is a byte with bits that are not known (`Env.pad`, `AS.padShift`).
* The counter: `Env.rkI` is a RAM byte that is not known, but the instruction `DEC abs` of it is followed: `AS.rk`, `AS.spent`, `Sim.rkv`, `arkOp`. No other instruction may write it.
* A byte can be read in pieces, by some of its bits (`Env.splits`, `splitRead`).
* `Sim` takes the pair of the frame and the counter's value at the start of the frame.
* The search keeps a table state only where paths join, and a few others. The walk (`walkF`) stops at the end of the frame.

There is no game data in this file: the known bytes are given by their names, and their values come from a reference machine. Page: `1-1/d-2-2-SideChangeBound.md`.
-/

namespace Smbrta.SideChangeBound

open PipeTransition (frame run zeros)
open PipeTransitionAll (go)
open TaintRun

/-- what does not change: the ROM, and the buttons of every frame. `D` are the bytes that are not all zero while `dg` holds. -/
structure Env where
  prg : ByteArray
  mask : UInt16
  /-- the buttons of a frame: some bits may not be known -/
  pad : AB
  D : List Nat
  /-- the counter, as a RAM index -/
  rkI : Nat := 4096
  /-- bytes to be read in pieces, with the bits that decide the pieces -/
  splits : List (Nat × UInt8) := []
  /-- keep a list of the bytes read that are not known: only for the search of the set of known bytes -/
  track : Bool := false

structure AS where
  a : AB
  x : AB
  y : AB
  s : UInt8
  p : AB
  pc : UInt16
  ram : ByteArray
  kn : ByteArray
  ppuCtrl : AB
  ppuMask : AB
  vb : Bool
  nmi : Bool
  lo : Nat
  hi : Nat
  padShift : AB
  strobe : Bool
  dg : Bool
  /-- frames that have ended -/
  k : Nat
  /-- bytes read that are not known, if `track` -/
  log : List Nat := []
  /-- the counter is followed: only its fall is known, see `Sim` -/
  rk : Bool := false
  /-- the counter has fallen in this frame -/
  spent : Bool := false
  deriving Inhabited

abbrev AM := StateT AS Option

@[inline] def AS.getK (A : AS) (i : Nat) : AB := ⟨A.ram.get! i, A.kn.get! i⟩
@[inline] def AS.setK (A : AS) (i : Nat) (b : AB) : AS := { A with ram := A.ram.set! i b.v, kn := A.kn.set! i b.k }

/-- the sprite-0 flag as a function of the dot -/
def s0f (d : Nat) : Bool := decide (d < dotVblClr) || decide (dotSpr0 ≤ d)

/-! time -/

/-- `tick c` for a `c` in `c1..c2`, or nothing if `c1 = 0`. Inside a frame, away from its first dot and its end. -/
def atick (c1 c2 : Nat) : AM Unit := fun A =>
  let lo' := A.lo + 3 * c1
  let hi' := A.hi + 3 * c2
  if A.lo < dotVblSet || dotsPerFrame - 1 ≤ hi' then none
  else if A.hi < dotVblClr && dotVblClr ≤ lo' then some ((), { A with lo := lo', hi := hi', vb := false })
  else if dotVblClr ≤ A.lo || hi' < dotVblClr || !A.vb then some ((), { A with lo := lo', hi := hi' })
  else none

/-! bus -/

def s0tri (A : AS) : Option Bool :=
  if A.hi < dotVblClr || dotSpr0 ≤ A.lo then some true
  else if dotVblClr ≤ A.lo && A.hi < dotSpr0 then some false else none

def appuRead (reg : UInt16) : AM AB := fun A =>
  if reg == 2 then
    some ((AB.known (if A.vb then 0x80 else 0)).or (AB.ite (s0tri A) 0x40 0), { A with vb := false })
  else some (AB.known 0, A)

def apadRead (E : Env) : AM AB := fun A =>
  if A.strobe then some ((AB.known 0x40).or (E.pad.and (AB.known 1)), A)
  else some ((AB.known 0x40).or (A.padShift.and (AB.known 1)), { A with padShift := A.padShift.shr.or (AB.known 0x80) })

/-- note a byte read, if asked -/
@[inline] def AS.note (E : Env) (A : AS) (i : Nat) : AS :=
  if E.track && (A.kn.get! i != 0xFF) then { A with log := i :: A.log } else A

def ardK (E : Env) (addr : UInt16) : AM AB := fun A =>
  if addr < 0x2000 then some (A.getK (addr &&& 0x7FF).toNat, A.note E (addr &&& 0x7FF).toNat)
  else if addr ≥ 0x8000 then some (AB.known (E.prg.get! (addr &&& E.mask).toNat), A)
  else if addr < 0x4000 then appuRead (addr &&& 7) A
  else if addr == 0x4016 then apadRead E A
  else if addr == 0x4017 then some (AB.known 0x40, A)
  else some (AB.known 0, A)

/-- the byte at an address in RAM or ROM -/
def peekK (E : Env) (A : AS) (addr : UInt16) : AB :=
  if addr < 0x2000 then A.getK (addr &&& 0x7FF).toNat else AB.known (E.prg.get! (addr &&& E.mask).toNat)

/-- the join of the bytes from `addr` on -/
def rangeJoin (E : Env) (A : AS) (addr : UInt16) : Nat → AB
  | 0 => peekK E A addr
  | n + 1 => (rangeJoin E A addr n).join (peekK E A (addr + (n + 1).toUInt16))

def ard (E : Env) (ad : AAd) : AM AB := fun A =>
  if ad.lo == ad.hi then ardK E ad.lo A
  else if ad.lo ≤ ad.hi && (ad.hi < 0x2000 || 0x8000 ≤ ad.lo) then
    some (rangeJoin E A ad.lo (ad.hi - ad.lo).toNat,
      if E.track && ad.hi < 0x2000 then
        (List.range ((ad.hi - ad.lo).toNat + 1)).foldl (fun B j => B.note E ((ad.lo + j.toUInt16) &&& 0x7FF).toNat) A
      else A)
  else if ad.hi < ad.lo && ad.hi < 0x2000 && 0x8000 ≤ ad.lo then some (AB.top, A)
  else none

def appuWrite (reg : UInt16) (v : AB) : AM Unit := fun A =>
  if reg == 0 then
    if A.nmi || !A.vb then some ((), { A with ppuCtrl := v })
    else
      match v.bit 0x80, A.ppuCtrl.bit 0x80 with
      | some b1, some b2 => some ((), { A with ppuCtrl := v, nmi := b1 && !b2 })
      | _, _ => none
  else if reg == 1 then some ((), { A with ppuMask := v })
  else some ((), A)

def apadWrite (E : Env) (v : AB) : AM Unit := fun A =>
  match v.bit 1 with
  | some true => some ((), { A with strobe := true, padShift := E.pad })
  | some false => if A.strobe then some ((), { A with strobe := false, padShift := E.pad }) else some ((), A)
  | none => none

def awr (E : Env) (ad : AAd) (v : AB) : AM Unit := fun A =>
  if ad.lo == ad.hi then
    let addr := ad.lo
    if addr < 0x2000 then
      let i := (addr &&& 0x7FF).toNat
      if A.rk && i == E.rkI then none else
      some ((), { A.setK i v with dg := A.dg && !E.D.contains i })
    else if addr < 0x4000 then appuWrite (addr &&& 7) v A
    else if addr == 0x4014 then atick 513 514 A
    else if addr == 0x4016 then apadWrite E v A
    else some ((), A)
  else none

/-! fetch and modes -/

def afetch (E : Env) : AM UInt8 := fun A =>
  if 0x8000 ≤ A.pc then some (E.prg.get! (A.pc &&& E.mask).toNat, { A with pc := A.pc + 1 }) else none

def afetch16 (E : Env) : AM UInt16 := do
  let lo ← afetch E
  let hi ← afetch E
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

def ard16zp (E : Env) (z : UInt8) : AM (AB × AB) := do
  let lo ← ard E (AAd.exact z.toUInt16)
  let hi ← ard E (AAd.exact (z + 1).toUInt16)
  return (lo, hi)

/-- `b + i` as an interval -/
def addIdx (b : UInt16) (i : AB) : AAd :=
  if i.isK then AAd.exact (b + i.v.toUInt16)
  else if b.toNat + 255 < 65536 then ⟨b + i.minv.toUInt16, b + i.maxv.toUInt16⟩
  else ⟨b, b + 255⟩

/-- `pagePenalty b e` for an `e` in the interval -/
def apenalty (b : UInt16) (ad : AAd) : AM Unit :=
  if ad.lo == ad.hi then
    if (b ^^^ ad.lo) &&& 0xFF00 != 0 then atick 1 1 else pure ()
  else atick 0 1

abbrev AMode := AM AAd

/-- the pointer, known -/
def ptrOf (lo hi : AB) : Option UInt16 :=
  if lo.isK && hi.isK then some (lo.v.toUInt16 ||| (hi.v.toUInt16 <<< 8)) else none

def aImm : AMode := fun A => some (AAd.exact A.pc, { A with pc := A.pc + 1 })
def aZp (E : Env) : AMode := return AAd.exact (← afetch E).toUInt16
def aZpi (E : Env) (r : AS → AB) : AMode := do
  let b ← afetch E
  let i := r (← get)
  return if i.isK then AAd.exact (b + i.v).toUInt16 else ⟨0, 255⟩
def aAbs (E : Env) : AMode := return AAd.exact (← afetch16 E)
def aAbi (E : Env) (r : AS → AB) : AMode := do let b ← afetch16 E; return addIdx b (r (← get))
def aAbiR (E : Env) (r : AS → AB) : AMode := do
  let b ← afetch16 E
  let e := addIdx b (r (← get))
  apenalty b e
  return e
def aIzx (E : Env) : AMode := do
  let z ← afetch E
  let x := (← get).x
  if x.isK then
    let (lo, hi) ← ard16zp E (z + x.v)
    match ptrOf lo hi with
    | some b => return AAd.exact b
    | none => failure
  else failure
def aIzy (E : Env) : AMode := do
  let z ← afetch E
  let (lo, hi) ← ard16zp E z
  match ptrOf lo hi with
  | some b => return addIdx b (← get).y
  | none => failure
def aIzyR (E : Env) : AMode := do
  let z ← afetch E
  let (lo, hi) ← ard16zp E z
  match ptrOf lo hi with
  | some b =>
    let e := addIdx b (← get).y
    apenalty b e
    return e
  | none => failure

/-! flags -/

def asetZN (v : AB) : AM Unit := fun A =>
  some ((), { A with p := ((A.p.and (AB.known 0x7D)).or (AB.ite v.isZero 0x02 0)).or (v.and (AB.known 0x80)) })
def asetFlag (mask : UInt8) (t : Option Bool) : AM Unit := fun A =>
  match t with
  | some true => some ((), { A with p := A.p.or (AB.known mask) })
  | some false => some ((), { A with p := A.p.and (AB.known (~~~mask)) })
  | none => some ((), { A with p := (A.p.or (AB.known mask)).join (A.p.and (AB.known (~~~mask))) })
def asetA (v : AB) : AM Unit := do modify (fun A => { A with a := v }); asetZN v
def asetX (v : AB) : AM Unit := do modify (fun A => { A with x := v }); asetZN v
def asetY (v : AB) : AM Unit := do modify (fun A => { A with y := v }); asetZN v

def apush (E : Env) (v : AB) : AM Unit := do
  let A ← get
  set { A with s := A.s - 1 }
  awr E (AAd.exact (0x100 ||| A.s.toUInt16)) v
def apull (E : Env) : AM AB := do
  let A ← get
  set { A with s := A.s + 1 }
  ard E (AAd.exact (0x100 ||| (A.s + 1).toUInt16))
def asetPC (pc : UInt16) : AM Unit := modify fun A => { A with pc }

/-- `adc`: every bit known, or the result is not known -/
def aadc (v : AB) : AM Unit := fun A =>
  let c := A.p.and (AB.known 1)
  if A.a.isK && v.isK && c.isK then
    let s := A.a.v.toUInt16 + v.v.toUInt16 + c.v.toUInt16
    let r := s.toUInt8
    let ovf := (A.a.v ^^^ r) &&& (v.v ^^^ r) &&& 0x80 != 0
    let p := (((((A.p.and (AB.known 0x3C)).or (AB.known (if s > 0xFF then 0x01 else 0))).or (AB.known (if r == 0 then 0x02 else 0))).or
      (AB.known (r &&& 0x80))).or (AB.known (if ovf then 0x40 else 0)))
    some ((), { A with a := AB.known r, p })
  else
    let p := (((((A.p.and (AB.known 0x3C)).or (AB.ite none 0x01 0)).or (AB.ite none 0x02 0)).or
      (AB.top.and (AB.known 0x80))).or (AB.ite none 0x40 0))
    some ((), { A with a := AB.top, p })

def aoraV (v : AB) : AM Unit := do asetA ((← get).a.or v)
def aandV (v : AB) : AM Unit := do asetA ((← get).a.and v)
def aeorV (v : AB) : AM Unit := do asetA ((← get).a.xor v)

/-- `r ≥ v`, if known -/
def ageTri (r v : AB) : Option Bool :=
  if r.minv ≥ v.maxv then some true else if r.maxv < v.minv then some false else none
/-- `r - v == 0`, if known -/
def aeqTri (r v : AB) : Option Bool :=
  if r.isK && v.isK then some (r.v == v.v)
  else if (r.v ^^^ v.v) &&& r.k &&& v.k != 0 then some false else none

def acmpV (r v : AB) : AM Unit := fun A =>
  let d : AB := if r.isK && v.isK then AB.known (r.v - v.v) else AB.top
  let p := ((A.p.and (AB.known 0x7D)).or (AB.ite (aeqTri r v) 0x02 0)).or (d.and (AB.known 0x80))
  (asetFlag 0x01 (ageTri r v)) { A with p }

def aaslV (v : AB) : AM AB := do
  let r := v.shl
  asetFlag 0x01 (v.bit 0x80)
  asetZN r
  return r
def alsrV (v : AB) : AM AB := do
  let r := v.shr
  asetFlag 0x01 (v.bit 1)
  asetZN r
  return r
def arolV (v : AB) : AM AB := do
  let c := (← get).p.and (AB.known 1)
  let r := v.shl.or c
  asetFlag 0x01 (v.bit 0x80)
  asetZN r
  return r
def arorV (v : AB) : AM AB := do
  let c := (← get).p.and (AB.known 1)
  let r := v.shr.or c.shl7
  asetFlag 0x01 (v.bit 1)
  asetZN r
  return r
def aincV (v : AB) : AM AB := do
  let r := v.map1 (· + 1)
  asetZN r
  return r
def adecV (v : AB) : AM AB := do
  let r := v.map1 (· - 1)
  asetZN r
  return r

/-! instructions -/

section
variable (E : Env) (md : AMode)

def aLDA : AM Unit := do asetA (← ard E (← md))
def aLDX : AM Unit := do asetX (← ard E (← md))
def aLDY : AM Unit := do asetY (← ard E (← md))
def aLAX : AM Unit := do
  let v ← ard E (← md); modify (fun A => { A with a := v, x := v }); asetZN v
def aSTA : AM Unit := do let ad ← md; awr E ad (← get).a
def aSTX : AM Unit := do let ad ← md; awr E ad (← get).x
def aSTY : AM Unit := do let ad ← md; awr E ad (← get).y
def aSAX : AM Unit := do let ad ← md; let A ← get; awr E ad (A.a.and A.x)
def aADC : AM Unit := do aadc (← ard E (← md))
def aSBC : AM Unit := do aadc (← ard E (← md)).not
def aORA : AM Unit := do aoraV (← ard E (← md))
def aAND : AM Unit := do aandV (← ard E (← md))
def aEOR : AM Unit := do aeorV (← ard E (← md))
def aCMP : AM Unit := do let v ← ard E (← md); acmpV (← get).a v
def aCPX : AM Unit := do let v ← ard E (← md); acmpV (← get).x v
def aCPY : AM Unit := do let v ← ard E (← md); acmpV (← get).y v
def aBIT : AM Unit := do
  let v ← ard E (← md)
  modify fun A =>
    { A with p := ((A.p.and (AB.known 0x3D)).or (v.and (AB.known 0xC0))).or (AB.ite (A.a.and v).isZero 0x02 0) }
def armw (f : AB → AM AB) : AM Unit := do
  let ad ← md; let v ← ard E ad; let r ← f v; awr E ad r
def armw2 (f : AB → AM AB) (g : AB → AM Unit) : AM Unit := do
  let ad ← md; let v ← ard E ad; let r ← f v; awr E ad r; g r
def aNOPm : AM Unit := do let _ ← md; pure ()
end

section
variable (E : Env) (md : AMode)
def aASL := armw E md aaslV
def aLSR := armw E md alsrV
def aROL := armw E md arolV
def aROR := armw E md arorV
def aINC := armw E md aincV
def aDEC := armw E md adecV
def aSLO := armw2 E md aaslV aoraV
def aRLA := armw2 E md arolV aandV
def aSRE := armw2 E md alsrV aeorV
def aRRA := armw2 E md arorV aadc
def aDCP := armw2 E md (fun v => pure (v.map1 (· - 1))) (fun r => do acmpV (← get).a r)
def aISB := armw2 E md (fun v => pure (v.map1 (· + 1))) (fun r => aadc r.not)
end


def aaccOp (f : AB → AM AB) : AM Unit := do
  let r ← f (← get).a; modify fun A => { A with a := r }

def aPLP (E : Env) : AM Unit := do
  let v ← apull E
  modify fun A => { A with p := (v.and (AB.known 0xEF)).or (AB.known 0x20) }

def aPHP (E : Env) : AM Unit := do apush E ((← get).p.or (AB.known 0x30))
def aPLA (E : Env) : AM Unit := do asetA (← apull E)
def aTXS : AM Unit := fun A => if A.x.isK then some ((), { A with s := A.x.v }) else none
def aTSX : AM Unit := do asetX (AB.known (← get).s)

def aJMP (E : Env) : AM Unit := do asetPC (← afetch16 E)
def aJMPi (E : Env) : AM Unit := do
  let ptr ← afetch16 E
  let lo ← ard E (AAd.exact ptr)
  let hi ← ard E (AAd.exact ((ptr &&& 0xFF00) ||| ((ptr + 1) &&& 0x00FF)))
  match ptrOf lo hi with
  | some t => asetPC t
  | none => failure
def aJSR (E : Env) : AM Unit := do
  let t ← afetch16 E
  let ret := (← get).pc - 1
  apush E (AB.known (ret >>> 8).toUInt8); apush E (AB.known ret.toUInt8); asetPC t
def aRTS (E : Env) : AM Unit := do
  let lo ← apull E; let hi ← apull E
  match ptrOf lo hi with
  | some t => asetPC (t + 1)
  | none => failure
def aRTI (E : Env) : AM Unit := do
  aPLP E
  let lo ← apull E; let hi ← apull E
  match ptrOf lo hi with
  | some t => asetPC t
  | none => failure

def ainterrupt (E : Env) (pc : UInt16) (pushedP : AB) (vector : UInt16) : AM Unit := do
  apush E (AB.known (pc >>> 8).toUInt8); apush E (AB.known pc.toUInt8); apush E pushedP
  asetFlag 0x04 (some true)
  let lo ← ard E (AAd.exact vector); let hi ← ard E (AAd.exact (vector + 1))
  match ptrOf lo hi with
  | some t => asetPC t
  | none => failure
def aBRK (E : Env) : AM Unit := do
  let A ← get
  ainterrupt E (A.pc + 1) (A.p.or (AB.known 0x30)) 0xFFFE
def anmi (E : Env) : AM Unit := fun A =>
  (ainterrupt E A.pc ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)) 0xFFFA >>= fun _ => atick 7 7) { A with nmi := false }

/-- a branch on a flag: the flag must be known -/
def abranch (E : Env) (mask : UInt8) (neg : Bool) : AM Unit := do
  let off ← afetch E
  let A ← get
  match A.p.bit mask with
  | none => failure
  | some b =>
    if b == neg then
      let pc := A.pc
      let t := pc + (off.toUInt16 ||| (if off ≥ 0x80 then 0xFF00 else 0))
      asetPC t
      let c := if (pc ^^^ t) &&& 0xFF00 != 0 then 2 else 1
      atick c c
    else pure ()

def aJAM : AM Unit := failure
def aNOP : AM Unit := pure ()
def aPHA (E : Env) : AM Unit := do apush E (← get).a
def aTAX : AM Unit := do asetX (← get).a
def aTAY : AM Unit := do asetY (← get).a
def aTXA : AM Unit := do asetA (← get).x
def aTYA : AM Unit := do asetA (← get).y
def aINX : AM Unit := do asetX ((← get).x.map1 (· + 1))
def aINY : AM Unit := do asetY ((← get).y.map1 (· + 1))
def aDEX : AM Unit := do asetX ((← get).x.map1 (· - 1))
def aDEY : AM Unit := do asetY ((← get).y.map1 (· - 1))

/-! ## The table of opcodes -/

def arow0 (E : Env) : List (AM Unit) := [aBRK E, aORA E (aIzx E), aJAM, aSLO E (aIzx E), aNOPm (aZp E), aORA E (aZp E), aASL E (aZp E), aSLO E (aZp E), aPHP E, aORA E aImm, aaccOp aaslV, aJAM, aNOPm (aAbs E), aORA E (aAbs E), aASL E (aAbs E), aSLO E (aAbs E)]
def arow1 (E : Env) : List (AM Unit) := [abranch E 0x80 false, aORA E (aIzyR E), aJAM, aSLO E (aIzy E), aNOPm (aZpi E (·.x)), aORA E (aZpi E (·.x)), aASL E (aZpi E (·.x)), aSLO E (aZpi E (·.x)), asetFlag 0x01 (some false), aORA E (aAbiR E (·.y)), aNOP, aSLO E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aORA E (aAbiR E (·.x)), aASL E (aAbi E (·.x)), aSLO E (aAbi E (·.x))]
def arow2 (E : Env) : List (AM Unit) := [aJSR E, aAND E (aIzx E), aJAM, aRLA E (aIzx E), aBIT E (aZp E), aAND E (aZp E), aROL E (aZp E), aRLA E (aZp E), aPLP E, aAND E aImm, aaccOp arolV, aJAM, aBIT E (aAbs E), aAND E (aAbs E), aROL E (aAbs E), aRLA E (aAbs E)]
def arow3 (E : Env) : List (AM Unit) := [abranch E 0x80 true, aAND E (aIzyR E), aJAM, aRLA E (aIzy E), aNOPm (aZpi E (·.x)), aAND E (aZpi E (·.x)), aROL E (aZpi E (·.x)), aRLA E (aZpi E (·.x)), asetFlag 0x01 (some true), aAND E (aAbiR E (·.y)), aNOP, aRLA E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aAND E (aAbiR E (·.x)), aROL E (aAbi E (·.x)), aRLA E (aAbi E (·.x))]
def arow4 (E : Env) : List (AM Unit) := [aRTI E, aEOR E (aIzx E), aJAM, aSRE E (aIzx E), aNOPm (aZp E), aEOR E (aZp E), aLSR E (aZp E), aSRE E (aZp E), aPHA E, aEOR E aImm, aaccOp alsrV, aJAM, aJMP E, aEOR E (aAbs E), aLSR E (aAbs E), aSRE E (aAbs E)]
def arow5 (E : Env) : List (AM Unit) := [abranch E 0x40 false, aEOR E (aIzyR E), aJAM, aSRE E (aIzy E), aNOPm (aZpi E (·.x)), aEOR E (aZpi E (·.x)), aLSR E (aZpi E (·.x)), aSRE E (aZpi E (·.x)), asetFlag 0x04 (some false), aEOR E (aAbiR E (·.y)), aNOP, aSRE E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aEOR E (aAbiR E (·.x)), aLSR E (aAbi E (·.x)), aSRE E (aAbi E (·.x))]
def arow6 (E : Env) : List (AM Unit) := [aRTS E, aADC E (aIzx E), aJAM, aRRA E (aIzx E), aNOPm (aZp E), aADC E (aZp E), aROR E (aZp E), aRRA E (aZp E), aPLA E, aADC E aImm, aaccOp arorV, aJAM, aJMPi E, aADC E (aAbs E), aROR E (aAbs E), aRRA E (aAbs E)]
def arow7 (E : Env) : List (AM Unit) := [abranch E 0x40 true, aADC E (aIzyR E), aJAM, aRRA E (aIzy E), aNOPm (aZpi E (·.x)), aADC E (aZpi E (·.x)), aROR E (aZpi E (·.x)), aRRA E (aZpi E (·.x)), asetFlag 0x04 (some true), aADC E (aAbiR E (·.y)), aNOP, aRRA E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aADC E (aAbiR E (·.x)), aROR E (aAbi E (·.x)), aRRA E (aAbi E (·.x))]
def arow8 (E : Env) : List (AM Unit) := [aNOPm aImm, aSTA E (aIzx E), aNOPm aImm, aSAX E (aIzx E), aSTY E (aZp E), aSTA E (aZp E), aSTX E (aZp E), aSAX E (aZp E), aDEY, aNOPm aImm, aTXA, aJAM, aSTY E (aAbs E), aSTA E (aAbs E), aSTX E (aAbs E), aSAX E (aAbs E)]
def arow9 (E : Env) : List (AM Unit) := [abranch E 0x01 false, aSTA E (aIzy E), aJAM, aJAM, aSTY E (aZpi E (·.x)), aSTA E (aZpi E (·.x)), aSTX E (aZpi E (·.y)), aSAX E (aZpi E (·.y)), aTYA, aSTA E (aAbi E (·.y)), aTXS, aJAM, aJAM, aSTA E (aAbi E (·.x)), aJAM, aJAM]
def arowA (E : Env) : List (AM Unit) := [aLDY E aImm, aLDA E (aIzx E), aLDX E aImm, aLAX E (aIzx E), aLDY E (aZp E), aLDA E (aZp E), aLDX E (aZp E), aLAX E (aZp E), aTAY, aLDA E aImm, aTAX, aJAM, aLDY E (aAbs E), aLDA E (aAbs E), aLDX E (aAbs E), aLAX E (aAbs E)]
def arowB (E : Env) : List (AM Unit) := [abranch E 0x01 true, aLDA E (aIzyR E), aJAM, aLAX E (aIzyR E), aLDY E (aZpi E (·.x)), aLDA E (aZpi E (·.x)), aLDX E (aZpi E (·.y)), aLAX E (aZpi E (·.y)), asetFlag 0x40 (some false), aLDA E (aAbiR E (·.y)), aTSX, aJAM, aLDY E (aAbiR E (·.x)), aLDA E (aAbiR E (·.x)), aLDX E (aAbiR E (·.y)), aLAX E (aAbiR E (·.y))]
def arowC (E : Env) : List (AM Unit) := [aCPY E aImm, aCMP E (aIzx E), aNOPm aImm, aDCP E (aIzx E), aCPY E (aZp E), aCMP E (aZp E), aDEC E (aZp E), aDCP E (aZp E), aINY, aCMP E aImm, aDEX, aJAM, aCPY E (aAbs E), aCMP E (aAbs E), aDEC E (aAbs E), aDCP E (aAbs E)]
def arowD (E : Env) : List (AM Unit) := [abranch E 0x02 false, aCMP E (aIzyR E), aJAM, aDCP E (aIzy E), aNOPm (aZpi E (·.x)), aCMP E (aZpi E (·.x)), aDEC E (aZpi E (·.x)), aDCP E (aZpi E (·.x)), asetFlag 0x08 (some false), aCMP E (aAbiR E (·.y)), aNOP, aDCP E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aCMP E (aAbiR E (·.x)), aDEC E (aAbi E (·.x)), aDCP E (aAbi E (·.x))]
def arowE (E : Env) : List (AM Unit) := [aCPX E aImm, aSBC E (aIzx E), aNOPm aImm, aISB E (aIzx E), aCPX E (aZp E), aSBC E (aZp E), aINC E (aZp E), aISB E (aZp E), aINX, aSBC E aImm, aNOP, aSBC E aImm, aCPX E (aAbs E), aSBC E (aAbs E), aINC E (aAbs E), aISB E (aAbs E)]
def arowF (E : Env) : List (AM Unit) := [abranch E 0x02 true, aSBC E (aIzyR E), aJAM, aISB E (aIzy E), aNOPm (aZpi E (·.x)), aSBC E (aZpi E (·.x)), aINC E (aZpi E (·.x)), aISB E (aZpi E (·.x)), asetFlag 0x08 (some true), aSBC E (aAbiR E (·.y)), aNOP, aISB E (aAbi E (·.y)), aNOPm (aAbiR E (·.x)), aSBC E (aAbiR E (·.x)), aINC E (aAbi E (·.x)), aISB E (aAbi E (·.x))]

def aRows (E : Env) : List (AM Unit) := arow0 E ++ (arow1 E ++ (arow2 E ++ (arow3 E ++ (arow4 E ++ (arow5 E ++ (arow6 E ++ (arow7 E ++ (arow8 E ++ (arow9 E ++ (arowA E ++ (arowB E ++ (arowC E ++ (arowD E ++ (arowE E ++ (arowF E)))))))))))))))

/-! ## One step -/

/-- the next event after a dot -/
def nextEvent (f : Nat) : Nat :=
  if f < dotVblSet then dotVblSet
  else if f < dotVblClr then dotVblClr
  else if f < dotSpr0 then dotSpr0
  else dotsPerFrame

/-- the idle loop `JMP *`: on to the next event. At the frame's end, two states: dot 0 (the NMI comes one step later) or later. -/
def aidle (A : AS) : List (Option AS) :=
  let next := nextEvent A.lo
  if next ≤ A.hi then [none]
  else if next == dotVblSet then
    match A.ppuCtrl.bit 0x80 with
    | some b => [some { A with lo := next, hi := next + 8, vb := true, nmi := A.nmi || b }]
    | none => [none]
  else if next == dotVblClr then [some { A with lo := next, hi := next + 8, vb := false }]
  else if next == dotSpr0 then [some { A with lo := next, hi := next + 8 }]
  else
    match A.ppuCtrl.bit 0x80 with
    | some b =>
      [some { A with lo := 0, hi := 0, k := A.k + 1 },
       some { A with lo := 1, hi := 9, vb := true, nmi := A.nmi || b, k := A.k + 1 }]
    | none => [none]

def isIdle (E : Env) (pc : UInt16) (op : UInt8) : Bool :=
  op == 0x4C && E.prg.get! ((pc + 1) &&& E.mask).toNat == pc.toUInt8
    && E.prg.get! ((pc + 2) &&& E.mask).toNat == (pc >>> 8).toUInt8 && decide (pc ≥ 0x8000)

def cycOf (op : UInt8) : Nat := (cycTable.get! op.toNat).toNat

/-- the instruction `DEC abs` of the counter -/
def isRkDec (E : Env) (pc : UInt16) (op : UInt8) : Bool :=
  op == 0xCE && decide (E.rkI < 2048) &&
    (let lo := E.prg.get! ((pc + 1) &&& E.mask).toNat
     let hi := E.prg.get! ((pc + 2) &&& E.mask).toNat
     let ad : UInt16 := lo.toUInt16 ||| (hi.toUInt16 <<< 8)
     decide (ad < 0x2000) && (ad &&& 0x7FF).toNat == E.rkI)

/-- the flags after a fall of the counter: it was at least 2, so the result is not 0 -/
def rkFlags (p : AB) : AB := ((p.and (AB.known 0x7D)).or (AB.known 0)).or (AB.top.and (AB.known 0x80))

/-- `DEC abs` of the counter: it falls by one, at most once in a frame -/
def arkOp (E : Env) : AM Unit :=
  afetch16 E >>= fun ad A =>
    if A.rk && !A.spent && decide (ad < 0x2000) && (ad &&& 0x7FF).toNat == E.rkI then
      some ((), { A.setK E.rkI AB.top with spent := true, dg := A.dg && !E.D.contains E.rkI, p := rkFlags A.p })
    else none

/-- the abstract successors of a state: each is a state or a failure -/
def astep1 (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if A.nmi then [((anmi E) A).map (·.2)]
  else if 0x8000 ≤ A.pc then
    let op := E.prg.get! (A.pc &&& E.mask).toNat
    if isIdle E A.pc op then aidle A
    else if A.rk && isRkDec E A.pc op then [((arkOp E >>= fun _ => atick 6 6) { A with pc := A.pc + 1 }).map (·.2)]
    else
      let c := cycOf op
      if c == 0 then [none]
      else [((ops[op.toNat]?.getD aJAM >>= fun _ => atick c c) { A with pc := A.pc + 1 }).map (·.2)]
  else [none]

/-! ## Pieces: every machine of a state is in one of its pieces -/

/-- the dot before `e`, or from `e` on -/
def splitDot (e : Nat) (A : AS) : List AS :=
  if A.lo < e && e ≤ A.hi then [{ A with hi := e - 1 }, { A with lo := e }] else [A]

/-- the flag not known: set, or not set -/
def splitFlag (mask : UInt8) (A : AS) : List AS :=
  match A.p.bit mask with
  | some _ => [A]
  | none => [{ A with p := A.p.or (AB.known mask) }, { A with p := A.p.and (AB.known (~~~mask)) }]

def bitList : List UInt8 := [1, 2, 4, 8, 16, 32, 64, 128]

/-- the bytes `D` are not all zero: one bit of one of them is set -/
def splitDg (E : Env) (A : AS) : List AS :=
  if A.dg then E.D.flatMap fun d => bitList.map fun b => A.setK d ((A.getK d).or (AB.known b)) else [A]

/-- the flag of a branch, if the opcode is one -/
def branchMask (op : UInt8) : UInt8 :=
  match op with
  | 0x10 | 0x30 => 0x80
  | 0x50 | 0x70 => 0x40
  | 0x90 | 0xB0 => 0x01
  | 0xD0 | 0xF0 => 0x02
  | _ => 0

/-- a read of a PPU register by `LDA abs`, `LDX abs`, `LDY abs`, `BIT abs` -/
def readsPPU (E : Env) (pc : UInt16) (op : UInt8) : Bool :=
  (op == 0xAD || op == 0xAE || op == 0xAC || op == 0x2C) &&
    (let hi := E.prg.get! ((pc + 2) &&& E.mask).toNat; 0x20 ≤ hi && hi < 0x40)

/-- `LDA abs` of the first byte of `D` -/
def readsDg (E : Env) (pc : UInt16) (op : UInt8) : Bool :=
  op == 0xAD &&
    (let lo := E.prg.get! ((pc + 1) &&& E.mask).toNat
     let hi := E.prg.get! ((pc + 2) &&& E.mask).toNat
     let ad : UInt16 := lo.toUInt16 ||| (hi.toUInt16 <<< 8)
     ad < 0x2000 && E.D.head? == some (ad &&& 0x7FF).toNat)

/-- the bit `b` of the byte `d` is set, or not -/
def splitBit (d : Nat) (b : UInt8) (A : AS) : List AS :=
  match (A.getK d).bit b with
  | some _ => [A]
  | none => [A.setK d ((A.getK d).or (AB.known b)), A.setK d ((A.getK d).and (AB.known (~~~b)))]

/-- the byte an instruction `LDA` reads, in zero page or absolute -/
def ldaAddr (E : Env) (pc : UInt16) (op : UInt8) : Option Nat :=
  if op == 0xA5 then some (E.prg.get! ((pc + 1) &&& E.mask).toNat).toNat
  else if op == 0xAD then
    let lo := E.prg.get! ((pc + 1) &&& E.mask).toNat
    let hi := E.prg.get! ((pc + 2) &&& E.mask).toNat
    let ad : UInt16 := lo.toUInt16 ||| (hi.toUInt16 <<< 8)
    if ad < 0x2000 then some (ad &&& 0x7FF).toNat else none
  else none

/-- a byte of `splits` that is read here: one piece for each value of the listed bits -/
def splitRead (E : Env) (A : AS) (op : UInt8) : List AS :=
  match ldaAddr E A.pc op with
  | none => [A]
  | some d =>
    match E.splits.find? (fun p => p.1 == d) with
    | none => [A]
    | some p =>
      if d < 2048 then (bitList.filter (fun b => b &&& p.2 != 0)).foldl (fun l b => l.flatMap (splitBit d b)) [A] else [A]

/-- which pieces this step needs -/
def pieces (E : Env) (A : AS) : List AS :=
  if A.nmi || A.pc < 0x8000 then [A] else
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let l1 := if readsDg E A.pc op then splitDg E A else splitRead E A op
  let l2 :=
    if readsPPU E A.pc op || isIdle E A.pc op then
      ((l1.flatMap (splitDot dotVblSet)).flatMap (splitDot dotVblClr)).flatMap (splitDot dotSpr0)
    else l1
  let mask := branchMask op
  if mask != 0 then l2.flatMap (splitFlag mask) else l2

def succs (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  (pieces E A).flatMap (astep1 E ops)

/-! ## Order -/

def ramLeFrom (a b : AS) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => (a.getK i).le (b.getK i) && ramLeFrom a b n (i + 1)

/-- every machine of `a` is one of `b` -/
def AS.le (a b : AS) : Bool :=
  a.pc == b.pc && a.s == b.s && a.k == b.k && a.vb == b.vb && a.nmi == b.nmi && a.padShift.le b.padShift && a.strobe == b.strobe &&
  a.a.le b.a && a.x.le b.x && a.y.le b.y && a.p.le b.p && a.ppuCtrl.le b.ppuCtrl && a.ppuMask.le b.ppuMask &&
  decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi) && decide (b.hi < dotsPerFrame) && (!b.dg || a.dg) &&
  b.ram.size == 2048 && b.kn.size == 2048 && ramLeFrom a b 2048 0 && a.rk == b.rk && a.spent == b.spent

/-! ## Control, and the walk -/

/-- a known byte compared with a value -/
def eqTri (b : AB) (c : UInt16) : Option Bool := if b.isK then some (b.v.toUInt16 == c) else none

/-- `a && b && c`, if known -/
def tri3 : Option Bool → Option Bool → Option Bool → Option Bool
  | some false, _, _ => some false
  | _, some false, _ => some false
  | _, _, some false => some false
  | some true, some true, some true => some true
  | _, _, _ => none

/-- `controllable`, if known -/
def actl (sy : Syms) (A : AS) : Option Bool :=
  tri3 (eqTri (A.getK (sy.OperMode &&& 0x7FF).toNat) sy.GameModeValue)
    (eqTri (A.getK (sy.OperMode_Task &&& 0x7FF).toNat) sy.Task_GameCore)
    (eqTri (A.getK (sy.GameEngineSubroutine &&& 0x7FF).toNat) sy.Eng_PlayerCtrl)

/-- the live stack, as a number -/
def stackHash (A : AS) : Nat := Id.run do
  let mut h : UInt32 := 17
  let mut j := A.s.toNat + 1
  while j < 256 do
    let b := A.getK (0x100 + j)
    h := h * 31 + (b.v &&& b.k).toUInt32
    h := h * 31 + b.k.toUInt32
    j := j + 1
  return h.toNat

/-- states with the same key are joined; the bytes `keep` are never joined -/
def keyOf (E : Env) (keep : List Nat) (A : AS) : Nat :=
  let idle := isIdle E A.pc (E.prg.get! (A.pc &&& E.mask).toNat)
  let num := fun (b : AB) => if idle then 0 else b.k.toNat * 256 + (b.v &&& b.k).toNat
  let op := E.prg.get! (A.pc &&& E.mask).toNat
  let useA := op == 0x29 || op == 0xD0 || op == 0xF0
  let n := A.k * 256 + A.s.toNat
  let n := n * 65536 + A.pc.toNat
  let n := n * 65536 + num A.x
  let n := n * 65536 + num A.y
  let n := n * 65536 + (if useA then num A.a else 0)
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.rk then 4 else 0) + (if A.spent then 8 else 0)
  let n := keep.foldl (fun n i => n * 65536 + (A.getK i).k.toNat * 256 + ((A.getK i).v &&& (A.getK i).k).toNat) n
  -- the pieces of `splitDg` stay apart while the bytes `D` are put together and tested
  let useD := op == 0x0D || op == 0xF0
  let n := E.D.foldl (fun n i => n * 256 + (if useD then (A.getK i).k.toNat else 0)) n
  n * 4294967296 + stackHash A

/-- what the check uses -/
structure Cfg where
  E : Env
  ops : Array (AM Unit)
  sy : Syms
  /-- control comes after `K` frames -/
  K : Nat
  keep : List Nat
  /-- the states of the certificate -/
  t : Array AS
  /-- candidates for a state, and the program counters that have candidates: no part of the proof -/
  idx : Std.HashMap Nat (List Nat)
  cut : ByteArray

/-- the table has a state that covers `B` -/
def coverIn (C : Cfg) (B : AS) : Bool :=
  (C.idx.getD (keyOf C.E C.keep B) []).any fun i =>
    match C.t[i]? with
    | some D => B.le D
    | none => false

/-! ## Finding the table: a search, no part of the proof -/

/-- `LDA $2002`-like read followed by `AND #`: a wait for a flag -/
def isSpin (E : Env) (A : AS) : Bool :=
  readsPPU E A.pc (E.prg.get! (A.pc &&& E.mask).toNat) && E.prg.get! ((A.pc + 3) &&& E.mask).toNat == 0x29

/-- a wait goes on until the next event: go there at once -/
def widen (A : AS) : AS :=
  if A.hi < dotVblClr then { A with hi := dotVblClr - 1 }
  else if A.hi < dotSpr0 && A.lo ≥ dotVblClr then { A with hi := dotSpr0 - 1 }
  else A

def ramJoin (a b : AS) : AS := Id.run do
  let mut ram := a.ram
  let mut kn := a.kn
  for i in [0:2048] do
    let x : AB := ⟨ram.get! i, kn.get! i⟩
    let y : AB := ⟨b.ram.get! i, b.kn.get! i⟩
    let z := x.join y
    if z.k != x.k || z.v != x.v then
      ram := ram.set! i z.v
      kn := kn.set! i z.k
  return { a with ram, kn }

def AS.join (a b : AS) : AS :=
  let c := ramJoin a b
  { c with
    a := a.a.join b.a, x := a.x.join b.x, y := a.y.join b.y, p := a.p.join b.p,
    ppuCtrl := a.ppuCtrl.join b.ppuCtrl, ppuMask := a.ppuMask.join b.ppuMask,
    lo := Nat.min a.lo b.lo, hi := Nat.max a.hi b.hi, dg := a.dg && b.dg }

/-- the search -/
structure Search where
  pending : Std.TreeMap Nat AS compare := {}
  /-- how many paths came into a pending state -/
  inN : Std.HashMap Nat Nat := {}
  done : Std.HashMap Nat AS := {}
  leaders : Std.HashMap Nat Unit := {}
  out : Array AS := #[]
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  firstFail : Option AS := none
  /-- bytes read that were not known -/
  unk : Std.HashMap Nat Unit := {}
  /-- the states at the frame's end -/
  ends : Array AS := #[]

/-- a new state goes to the waiting list: it is joined with a state that waits with the same key -/
def route (E : Env) (keep : List Nat) (X : Search) (B : AS) : Search :=
  let K := keyOf E keep B
  match X.pending[K]? with
  | some P => { X with pending := X.pending.insert K (P.join B), inN := X.inN.insert K (X.inN.getD K 1 + 1) }
  | none =>
    if isSpin E B then
      match X.done[K]? with
      | some D =>
        if B.le D then X else
        let J := widen (D.join B)
        { X with pending := X.pending.insert K J, done := X.done.insert K J, inN := X.inN.insert K 2 }
      | none => { X with pending := X.pending.insert K B, done := X.done.insert K B, inN := X.inN.insert K 2 }
    else { X with pending := X.pending.insert K B, inN := X.inN.insert K 1 }

/-- follow one waiting state as far as no other path can join -/
partial def runFrom (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (K : Nat) (X0 : Search) (A0 : AS) : Search := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := succs E ops cur
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    if rs.any (·.isNone) then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur }
    let good := rs.filterMap id
    if E.track then
      X := { X with unk := good.foldl (fun h b => b.log.foldl (fun h i => h.insert i ()) h) X.unk }
    let good := if E.track then good.map (fun b => { b with log := [] }) else good
    match good with
    | [b] =>
      if b.k == cur.k && (X.leaders[b.pc.toNat]?).isNone && run < 128 &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      if b.k != cur.k && b.k ≥ K then X := { X with ends := X.ends.push b }
      else
        X := { X with leaders := X.leaders.insert b.pc.toNat () }
        X := route E keep X b
    break
  return X

/-- the table for these start states -/
partial def searchLoop (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (K : Nat) (X0 : Search) : Search := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      let n := X.inN.getD key 1
      -- a state that one path came into needs no entry: the walk goes through it, unless the path was long
      X := { X with pending := X.pending.erase key, inN := X.inN.erase key }
      if n ≥ 2 || A.k == 0 && (X.out.size % 16 == 0) then X := { X with out := X.out.push A }
      if isSpin E A then X := { X with done := X.done.insert key A }
      X := runFrom E ops keep K X A
  return X

def search (E : Env) (ops : Array (AM Unit)) (keep : List Nat) (K : Nat) (starts : List AS) : Search :=
  searchLoop E ops keep K (starts.foldl (route E keep) {})

/-- the configuration from the table found -/
def Cfg.of (E : Env) (sy : Syms) (K : Nat) (keep : List Nat) (starts : List AS) : Cfg :=
  let ops := (aRows E).toArray
  let X := search E ops keep K starts
  let P := X.out.foldl (fun (acc : Std.HashMap Nat (List Nat) × ByteArray × Nat) A =>
      let k := keyOf E keep A
      (acc.1.insert k (acc.2.2 :: acc.1.getD k []), acc.2.1.set! A.pc.toNat 1, acc.2.2 + 1))
    (({} : Std.HashMap Nat (List Nat)), ByteArray.mk (Array.replicate 65536 0), 0)
  { E, ops, sy, K, keep, t := X.out, idx := P.1, cut := P.2.1 }

/-! ## The relation between the abstract machine and machines -/

/-- `A` covers the machine `m` -/
structure Sim (E : Env) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop where
  a : A.a.mem m.a
  x : A.x.mem m.x
  y : A.y.mem m.y
  p : A.p.mem m.p
  s : m.s = A.s
  pc : m.pc = A.pc
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  ppuCtrl : A.ppuCtrl.mem m.ppuCtrl
  ppuMask : A.ppuMask.mem m.ppuMask
  vb : m.vblank = A.vb
  nmi : m.nmiPending = A.nmi
  s0 : m.sprite0 = s0f m.fdot
  lo : A.lo ≤ m.fdot
  hi : m.fdot ≤ A.hi
  lim : A.hi < dotsPerFrame
  pad : E.pad.mem m.pad
  padShift : A.padShift.mem m.padShift
  strobe : m.padStrobe = A.strobe
  halted : m.halted = false
  trk : m.trk = false
  size : m.ram.size = 2048
  ram : ∀ i, i < 2048 → (A.getK i).mem (m.ram.get! i)
  dg : A.dg = true → E.D.any (fun i => m.ram.get! i != 0) = true
  szR : A.ram.size = 2048
  szK : A.kn.size = 2048
  /-- `F.1` is the frame of the machine at the start -/
  fr : m.frame = F.1 + A.k
  /-- `F.2` is the value of the counter at the start of the frame -/
  rkv : A.rk = true → m.ram.get! E.rkI = (if A.spent then F.2 - 1 else F.2)

/-- what an action inside a frame does to the clock -/
def Adv (m m' : Machine) : Prop := m'.frame = m.frame ∧ m.fdot ≤ m'.fdot

theorem Adv.refl (m : Machine) : Adv m m := ⟨rfl, Nat.le_refl _⟩
theorem Adv.tr {a b c : Machine} (h : Adv a b) (g : Adv b c) : Adv a c :=
  ⟨g.1.trans h.1, Nat.le_trans h.2 g.2⟩

/-- `af` follows `f` on every machine it covers, as long as it does not fail -/
def Snd (E : Env) (F : Nat × UInt8) {α β : Type} (R : α → β → Prop) (af : AM α) (f : M β) : Prop :=
  ∀ A m, Sim E F A m → ∀ a A', af A = some (a, A') → R a (go f m).1 ∧ Sim E F A' (go f m).2 ∧ Adv m (go f m).2

/-- no relation on the values -/
abbrev TT {α β : Type} : α → β → Prop := fun _ _ => True

section
variable {E : Env} {F : Nat × UInt8}

theorem abind_some {α β : Type} {af : AM α} {ag : α → AM β} {A : AS} {b : β} {B : AS}
    (h : (af >>= ag) A = some (b, B)) : ∃ a A1, af A = some (a, A1) ∧ ag a A1 = some (b, B) := by
  cases h3 : af A with
  | none => simp [Bind.bind, StateT.bind, h3] at h
  | some p =>
    obtain ⟨a, A1⟩ := p
    simp only [Bind.bind, StateT.bind, h3] at h
    exact ⟨a, A1, rfl, h⟩

theorem Snd.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {af : AM α} {f : M β} {ag : α → AM γ} {g : β → M δ}
    (h : Snd E F R af f) (hg : ∀ a b, R a b → Snd E F S (ag a) (g b)) : Snd E F S (af >>= ag) (f >>= g) := by
  intro A m hs c C he
  obtain ⟨a, A1, h1, h2⟩ := abind_some he
  obtain ⟨hr, hs1, ha1⟩ := h A m hs a A1 h1
  obtain ⟨hr2, hs2, ha2⟩ := hg _ _ hr A1 _ hs1 c C h2
  exact ⟨hr2, hs2, ha1.tr ha2⟩

theorem Snd.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) : Snd E F R (Pure.pure a) (Pure.pure b) := by
  intro A m hs c C he
  have he2 : some (a, A) = some (c, C) := he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he2)
  exact ⟨h, hs, Adv.refl m⟩

theorem Snd.get {α β : Type} {R : α → β → Prop} {ak : AS → AM α} {k : Machine → M β}
    (h : ∀ A m, Sim E F A m → Snd E F R (ak A) (k m)) : Snd E F R (MonadState.get >>= ak) (MonadState.get >>= k) := by
  intro A m hs c C he
  exact h A m hs A m hs c C he

theorem Snd.fail {α β : Type} {R : α → β → Prop} {f : M β} : Snd E F R (failure : AM α) f := by
  intro A m hs c C he
  cases he

/-- `f` and `g` give the same -/
theorem Snd.congr {α β : Type} {R : α → β → Prop} {af : AM α} {f g : M β} (h : ∀ m, go f m = go g m) (hg : Snd E F R af g) : Snd E F R af f := by
  intro A m hs c C he
  rw [h]
  exact hg A m hs c C he

/-- no change of the frame or the dot, and `Sim` is kept -/
theorem snd_leaf {α β : Type} {R : α → β → Prop} {af : AM α} {f : M β}
    (h : ∀ A m, Sim E F A m → ∀ a A', af A = some (a, A') →
      R a (go f m).1 ∧ Sim E F A' (go f m).2 ∧ (go f m).2.frame = m.frame ∧ (go f m).2.fdot = m.fdot) : Snd E F R af f := by
  intro A m hs c C he
  obtain ⟨h1, h2, h3, h4⟩ := h A m hs c C he
  exact ⟨h1, h2, h3, Nat.le_of_eq h4.symm⟩

theorem some_pair {α β : Type} {a c : α} {b d : β} (h : some (a, b) = some (c, d)) : a = c ∧ b = d :=
  Prod.mk.inj (Option.some.inj h)

/-! flags -/

theorem s_setZN {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (asetZN v) (setZN x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  refine ⟨trivial, { hs with p := ?_ }, rfl, rfl⟩
  exact mem_or (mem_or (mem_and hs.p (mem_known_self _)) (mem_ite (TR_isZero h) _ _)) (mem_and h (mem_known_self _))

theorem s_setFlag (mask : UInt8) {t : Option Bool} {b : Bool} (h : TR t b) : Snd E F TT (asetFlag mask t) (setFlag mask b) := by
  refine snd_leaf fun A m hs a A' he => ?_
  have hp := hs.p
  rcases h with rfl | rfl
  · obtain ⟨rfl, rfl⟩ := some_pair he
    refine ⟨trivial, { hs with p := ?_ }, rfl, rfl⟩
    cases b
    · exact mem_join_r _ (mem_and hp (mem_known_self _))
    · exact mem_join_l _ (mem_or hp (mem_known_self _))
  · cases b
    · obtain ⟨rfl, rfl⟩ := some_pair he
      exact ⟨trivial, { hs with p := mem_and hp (mem_known_self _) }, rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := some_pair he
      exact ⟨trivial, { hs with p := mem_or hp (mem_known_self _) }, rfl, rfl⟩

theorem s_modA {v : AB} {x : UInt8} (h : v.mem x) :
    Snd E F TT (modify fun A => { A with a := v } : AM Unit) (modify fun m => { m with a := x }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with a := h }, rfl, rfl⟩
theorem s_modX {v : AB} {x : UInt8} (h : v.mem x) :
    Snd E F TT (modify fun A => { A with x := v } : AM Unit) (modify fun m => { m with x := x }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with x := h }, rfl, rfl⟩
theorem s_modY {v : AB} {x : UInt8} (h : v.mem x) :
    Snd E F TT (modify fun A => { A with y := v } : AM Unit) (modify fun m => { m with y := x }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with y := h }, rfl, rfl⟩

theorem s_setA {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (asetA v) (setA x) :=
  Snd.bind (s_modA h) fun _ _ _ => s_setZN h
theorem s_setX {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (asetX v) (setX x) :=
  Snd.bind (s_modX h) fun _ _ _ => s_setZN h
theorem s_setY {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (asetY v) (setY x) :=
  Snd.bind (s_modY h) fun _ _ _ => s_setZN h

end

/-! ## Time -/

section
variable {E : Env} {F : Nat × UInt8}

theorem vc : dotVblClr = 6821 := rfl
theorem vs : dotSpr0 = 17732 := rfl
theorem v1 : dotVblSet = 1 := rfl
theorem vd : dotsPerFrame = 89342 := rfl

/-- `tick` inside a frame, after dot 0 and before the frame's end -/
theorem tick_mid (c : Nat) (m : Machine) (h1 : dotVblSet ≤ m.fdot) (h2 : m.fdot + 3 * c < dotsPerFrame - 1) :
    (go (tick c) m).2 = { m with
      cyc := m.cyc + c,
      fdot := m.fdot + 3 * c,
      vblank := if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank,
      sprite0 := if m.fdot < dotSpr0 ∧ dotSpr0 ≤ m.fdot + 3 * c then true
        else if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.sprite0 } := by
  have hlen : ∀ n : Machine, m.fdot + 3 * c < PipeTransitionAll.tickLen n := by
    intro n
    unfold PipeTransitionAll.tickLen
    split <;> omega
  have h4 : ∀ (new len : Nat) (n : Machine), new < len → PipeTransitionAll.tick4 new len n = { n with fdot := new } := by
    intro new len n hl
    unfold PipeTransitionAll.tick4
    rw [if_neg (by omega)]
  rw [PipeTransitionAll.tick_eq]
  dsimp only
  rw [h4 _ _ _ (hlen _)]
  have e1 : (decide (m.fdot < dotVblSet) && decide (dotVblSet ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotVblSet := by omega
    simp [this]
  rw [e1]
  by_cases p1 : m.fdot < dotVblClr <;> by_cases p2 : dotVblClr ≤ m.fdot + 3 * c <;>
    by_cases p3 : m.fdot < dotSpr0 <;> by_cases p4 : dotSpr0 ≤ m.fdot + 3 * c <;>
    simp [p1, p2, p3, p4, PipeTransitionAll.tick1, PipeTransitionAll.tick2, PipeTransitionAll.tick3]

theorem s0f_step (d c : Nat) (h : d + 3 * c < dotsPerFrame - 1) (b : Bool) (hb : b = s0f d) :
    (if d < dotSpr0 ∧ dotSpr0 ≤ d + 3 * c then true else if d < dotVblClr ∧ dotVblClr ≤ d + 3 * c then false else b) = s0f (d + 3 * c) := by
  subst hb
  simp only [s0f, vc, vs]
  by_cases a1 : d < 6821 <;> by_cases a2 : d < 17732 <;> by_cases a3 : 6821 ≤ d + 3 * c <;> by_cases a4 : 17732 ≤ d + 3 * c <;>
    simp [a1, a2, a3, a4] <;> omega

theorem s_tick {c1 c2 c : Nat} (h1 : c1 ≤ c) (h2 : c ≤ c2) : Snd E F TT (atick c1 c2) (tick c) := by
  intro A m hs a A' he
  have hlo := hs.lo
  have hhi := hs.hi
  have hle : 3 * c1 ≤ 3 * c := by omega
  have hle2 : 3 * c ≤ 3 * c2 := by omega
  unfold atick at he
  simp only at he
  split at he
  · cases he
  · rename_i hn
    have hn' : ¬ (A.lo < dotVblSet ∨ dotsPerFrame - 1 ≤ A.hi + 3 * c2) := by simpa using hn
    have h3 : dotVblSet ≤ m.fdot := by omega
    have h4 : m.fdot + 3 * c < dotsPerFrame - 1 := by omega
    have ht := tick_mid c m h3 h4
    have hf : (go (tick c) m).2.frame = m.frame := by rw [ht]
    have hd : (go (tick c) m).2.fdot = m.fdot + 3 * c := by rw [ht]
    have base : ∀ (B : AS), B = { A with lo := A.lo + 3 * c1, hi := A.hi + 3 * c2 } ∨ B = { A with lo := A.lo + 3 * c1, hi := A.hi + 3 * c2, vb := false } →
        (go (tick c) m).2.vblank = B.vb → Sim E F B (go (tick c) m).2 := by
      intro B hB hv
      have hB1 : B.a = A.a ∧ B.x = A.x ∧ B.y = A.y ∧ B.p = A.p ∧ B.s = A.s ∧ B.pc = A.pc ∧ B.ppuCtrl = A.ppuCtrl ∧ B.ppuMask = A.ppuMask ∧ B.nmi = A.nmi ∧
          B.lo = A.lo + 3 * c1 ∧ B.hi = A.hi + 3 * c2 ∧ B.padShift = A.padShift ∧ B.strobe = A.strobe ∧ B.ram = A.ram ∧ B.kn = A.kn ∧ B.dg = A.dg ∧ B.k = A.k ∧ B.rk = A.rk ∧ B.spent = A.spent := by
        rcases hB with rfl | rfl <;> simp
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ := hB1
      have hk : ∀ i, B.getK i = A.getK i := by
        intro i
        simp only [AS.getK, b14, b15]
      rw [ht] at hv ⊢
      refine ⟨b1 ▸ hs.a, b2 ▸ hs.x, b3 ▸ hs.y, b4 ▸ hs.p, b5 ▸ hs.s, b6 ▸ hs.pc, hs.prg, hs.mask, b7 ▸ hs.ppuCtrl, b8 ▸ hs.ppuMask, hv,
        b9 ▸ hs.nmi, s0f_step _ _ h4 _ hs.s0, ?_, ?_, ?_, hs.pad, b12 ▸ hs.padShift, b13 ▸ hs.strobe, hs.halted, hs.trk, hs.size, ?_, ?_, b14 ▸ hs.szR, b15 ▸ hs.szK, b17 ▸ hs.fr, ?_⟩
      · show B.lo ≤ m.fdot + 3 * c
        omega
      · show m.fdot + 3 * c ≤ B.hi
        omega
      · rw [b11]
        have := vd
        omega
      · intro i hi
        rw [hk]
        exact hs.ram i hi
      · intro hg
        rw [b16] at hg
        exact hs.dg hg
      · intro hr
        rw [b19]
        exact hs.rkv (b18 ▸ hr)
    split at he
    · rename_i hc
      obtain ⟨_, rfl⟩ := some_pair he
      have hc' : A.hi < dotVblClr ∧ dotVblClr ≤ A.lo + 3 * c1 := by simpa using hc
      refine ⟨trivial, base _ (Or.inr rfl) ?_, hf, by omega⟩
      rw [ht]
      have : m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c := ⟨by omega, by omega⟩
      simp [this]
    · split at he
      · rename_i hc
        obtain ⟨_, rfl⟩ := some_pair he
        refine ⟨trivial, base _ (Or.inl rfl) ?_, hf, by omega⟩
        rw [ht]
        show (if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank) = A.vb
        have hc' : (dotVblClr ≤ A.lo ∨ A.hi + 3 * c2 < dotVblClr) ∨ A.vb = false := by simpa using hc
        by_cases hh : m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c
        · rw [if_pos hh]
          rcases hc' with (h5 | h5) | h5
          · omega
          · omega
          · exact h5.symm
        · rw [if_neg hh]
          exact hs.vb
      · cases he

theorem s_tick0 {c2 : Nat} : Snd E F TT (atick 0 c2) (Pure.pure ()) := by
  intro A m hs a A' he
  have hlo := hs.lo
  have hhi := hs.hi
  unfold atick at he
  simp only [Nat.mul_zero, Nat.add_zero] at he
  have hpm : (go (Pure.pure () : M Unit) m) = ((), m) := rfl
  rw [hpm]
  split at he
  · cases he
  · rename_i hn
    have hn' : ¬ (A.lo < dotVblSet ∨ dotsPerFrame - 1 ≤ A.hi + 3 * c2) := by simpa using hn
    have base : ∀ (B : AS), B = { A with hi := A.hi + 3 * c2 } ∨ B = { A with hi := A.hi + 3 * c2, vb := false } →
        m.vblank = B.vb → Sim E F B m := by
      intro B hB hv
      have hB1 : B.a = A.a ∧ B.x = A.x ∧ B.y = A.y ∧ B.p = A.p ∧ B.s = A.s ∧ B.pc = A.pc ∧ B.ppuCtrl = A.ppuCtrl ∧ B.ppuMask = A.ppuMask ∧ B.nmi = A.nmi ∧
          B.lo = A.lo ∧ B.hi = A.hi + 3 * c2 ∧ B.padShift = A.padShift ∧ B.strobe = A.strobe ∧ B.ram = A.ram ∧ B.kn = A.kn ∧ B.dg = A.dg ∧ B.k = A.k ∧ B.rk = A.rk ∧ B.spent = A.spent := by
        rcases hB with rfl | rfl <;> simp
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ := hB1
      have hk : ∀ i, B.getK i = A.getK i := by
        intro i
        simp only [AS.getK, b14, b15]
      refine ⟨b1 ▸ hs.a, b2 ▸ hs.x, b3 ▸ hs.y, b4 ▸ hs.p, b5 ▸ hs.s, b6 ▸ hs.pc, hs.prg, hs.mask, b7 ▸ hs.ppuCtrl, b8 ▸ hs.ppuMask, hv,
        b9 ▸ hs.nmi, hs.s0, by omega, by omega, ?_, hs.pad, b12 ▸ hs.padShift, b13 ▸ hs.strobe, hs.halted, hs.trk, hs.size, ?_, ?_, b14 ▸ hs.szR, b15 ▸ hs.szK, b17 ▸ hs.fr, ?_⟩
      · rw [b11]
        have := vd
        omega
      · intro i hi
        rw [hk]
        exact hs.ram i hi
      · intro hg
        rw [b16] at hg
        exact hs.dg hg
      · intro hr
        rw [b19]
        exact hs.rkv (b18 ▸ hr)
    split at he
    · rename_i hc
      have hc' : A.hi < dotVblClr ∧ dotVblClr ≤ A.lo := by simpa using hc
      omega
    · split at he
      · rename_i hc
        obtain ⟨_, rfl⟩ := some_pair he
        exact ⟨trivial, base _ (Or.inl rfl) hs.vb, Adv.refl m⟩
      · cases he

end

/-! ## The bus -/

section
variable {E : Env} {F : Nat × UInt8}

open PipeTransitionAll (mask_lt ba_size_set ba_get_set_self ba_get_set_ne)

theorem rd_ram {addr : UInt16} {m : Machine} (h1 : addr < 0x2000) (ht : m.trk = false) :
    go (rd addr) m = (m.ram.get! (addr &&& 0x7FF).toNat, m) := by
  unfold rd go
  rw [if_pos h1]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem rd_rom {addr : UInt16} (m : Machine) (h1 : ¬ addr < 0x2000) (h2 : addr ≥ 0x8000) :
    go (rd addr) m = (m.prg.get! (addr &&& m.prgMask).toNat, m) := by
  unfold rd go
  rw [if_neg h1, if_pos h2]
  rfl

theorem rd_ppu {addr : UInt16} {m : Machine} (h1 : ¬ addr < 0x2000) (h2 : ¬ addr ≥ 0x8000) (h3 : addr < 0x4000) (ht : m.trk = false) :
    go (rd addr) m = go (ppuRead (addr &&& 7)) m := by
  unfold rd go
  rw [if_neg h1, if_neg h2, if_pos h3]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem rd_pad {addr : UInt16} {m : Machine} (h1 : ¬ addr < 0x2000) (h2 : ¬ addr ≥ 0x8000) (h3 : ¬ addr < 0x4000) (h4 : (addr == 0x4016) = true) (ht : m.trk = false) :
    go (rd addr) m = go padRead m := by
  unfold rd go
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem rd_17 {addr : UInt16} (m : Machine) (h1 : ¬ addr < 0x2000) (h2 : ¬ addr ≥ 0x8000) (h3 : ¬ addr < 0x4000) (h4 : ¬ (addr == 0x4016) = true) (h5 : (addr == 0x4017) = true) :
    go (rd addr) m = (0x40, m) := by
  unfold rd go
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  rfl

theorem rd_else {addr : UInt16} (m : Machine) (h1 : ¬ addr < 0x2000) (h2 : ¬ addr ≥ 0x8000) (h3 : ¬ addr < 0x4000) (h4 : ¬ (addr == 0x4016) = true) (h5 : ¬ (addr == 0x4017) = true) :
    go (rd addr) m = (0, m) := by
  unfold rd go
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  rfl

theorem TR_s0 {A : AS} {d : Nat} (h1 : A.lo ≤ d) (h2 : d ≤ A.hi) : TR (s0tri A) (s0f d) := by
  unfold s0tri s0f
  split
  · rename_i h
    right
    have h' : A.hi < dotVblClr ∨ dotSpr0 ≤ A.lo := by simpa using h
    have : d < dotVblClr ∨ dotSpr0 ≤ d := by omega
    simp [this]
  · split
    · rename_i h h3
      right
      have h' : dotVblClr ≤ A.lo ∧ A.hi < dotSpr0 := by simpa using h3
      have a1 : ¬ d < dotVblClr := by omega
      have a2 : ¬ dotSpr0 ≤ d := by omega
      simp [a1, a2]
    · exact Or.inl rfl

theorem s_ppuRead (r : UInt16) : Snd E F AB.mem (appuRead r) (ppuRead r) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold appuRead at he
  by_cases h : (r == 2) = true
  · rw [if_pos h] at he
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hc : go (ppuRead r) m = (((if m.vblank then 0x80 else 0 : UInt8)) ||| (if m.sprite0 then 0x40 else 0 : UInt8), { m with vblank := false }) := by
      unfold ppuRead go
      rw [if_pos h]
      rfl
    rw [hc]
    refine ⟨?_, { hs with vb := rfl }, rfl, rfl⟩
    rw [hs.vb, hs.s0]
    exact mem_or (mem_known_self _) (mem_ite (TR_s0 hs.lo hs.hi) _ _)
  · rw [if_neg h] at he
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hc : go (ppuRead r) m = (0, m) := by
      unfold ppuRead go
      rw [if_neg h]
      rfl
    rw [hc]
    exact ⟨mem_known_self _, hs, rfl, rfl⟩

theorem s_padRead : Snd E F AB.mem (apadRead E) padRead := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold apadRead at he
  have hst := hs.strobe
  cases hb : A.strobe with
  | true =>
    rw [if_pos hb] at he
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hc : go padRead m = ((0x40 : UInt8) ||| (m.pad &&& 1), m) := by
      unfold padRead go
      rw [hb] at hst
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases hst
        rfl
    rw [hc]
    exact ⟨mem_or (mem_known_self _) (mem_and hs.pad (mem_known_self _)), hs, rfl, rfl⟩
  | false =>
    rw [if_neg (by simp [hb])] at he
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hc : go padRead m = ((0x40 : UInt8) ||| (m.padShift &&& 1), { m with padShift := (m.padShift >>> 1) ||| 0x80 }) := by
      unfold padRead go
      rw [hb] at hst
      cases m with
      | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
        cases hst
        rfl
    rw [hc]
    refine ⟨?_, { hs with padShift := ?_ }, rfl, rfl⟩
    · exact mem_or (mem_known_self _) (mem_and hs.padShift (mem_known_self _))
    · exact mem_or (mem_shr hs.padShift) (mem_known_self _)

/-- the note changes nothing else -/
theorem sim_note {A : AS} {m : Machine} (hs : Sim E F A m) (i : Nat) : Sim E F (A.note E i) m := by
  unfold AS.note
  split
  · exact { hs with }
  · exact hs

theorem s_ardK (addr : UInt16) : Snd E F AB.mem (ardK E addr) (rd addr) := by
  intro A m hs a A' he
  unfold ardK at he
  by_cases h1 : addr < 0x2000
  · rw [if_pos h1] at he
    obtain ⟨rfl, rfl⟩ := some_pair he
    rw [rd_ram h1 hs.trk]
    exact ⟨hs.ram _ (mask_lt addr), sim_note hs _, Adv.refl m⟩
  · rw [if_neg h1] at he
    by_cases h2 : addr ≥ 0x8000
    · rw [if_pos h2] at he
      obtain ⟨rfl, rfl⟩ := some_pair he
      rw [rd_rom m h1 h2, hs.prg, hs.mask]
      exact ⟨mem_known_self _, hs, Adv.refl m⟩
    · rw [if_neg h2] at he
      by_cases h3 : addr < 0x4000
      · rw [if_pos h3] at he
        rw [rd_ppu h1 h2 h3 hs.trk]
        exact s_ppuRead _ A m hs a A' he
      · rw [if_neg h3] at he
        by_cases h4 : (addr == 0x4016) = true
        · rw [if_pos h4] at he
          rw [rd_pad h1 h2 h3 h4 hs.trk]
          exact s_padRead A m hs a A' he
        · rw [if_neg h4] at he
          by_cases h5 : (addr == 0x4017) = true
          · rw [if_pos h5] at he
            obtain ⟨rfl, rfl⟩ := some_pair he
            rw [rd_17 m h1 h2 h3 h4 h5]
            exact ⟨mem_known_self _, hs, Adv.refl m⟩
          · rw [if_neg h5] at he
            obtain ⟨rfl, rfl⟩ := some_pair he
            rw [rd_else m h1 h2 h3 h4 h5]
            exact ⟨mem_known_self _, hs, Adv.refl m⟩

/-- the address is in the interval -/
def AdR (ad : AAd) (addr : UInt16) : Prop :=
  (ad.lo ≤ ad.hi ∧ ad.lo ≤ addr ∧ addr ≤ ad.hi) ∨ (ad.hi < ad.lo ∧ (ad.lo ≤ addr ∨ addr ≤ ad.hi))

theorem adR_exact (a : UInt16) : AdR (AAd.exact a) a :=
  Or.inl ⟨UInt16.le_refl _, UInt16.le_refl _, UInt16.le_refl _⟩

theorem adR_same {ad : AAd} {addr : UInt16} (h : AdR ad addr) (he : ad.lo = ad.hi) : addr = ad.lo := by
  rcases h with ⟨_, h2, h3⟩ | ⟨h1, _⟩
  · apply UInt16.toNat_inj.1
    have a1 := UInt16.le_iff_toNat_le.1 h2
    have a2 := UInt16.le_iff_toNat_le.1 h3
    rw [← he] at a2
    omega
  · rw [he] at h1
    exact absurd h1 (UInt16.lt_irrefl _)

theorem rd_ramrom {A : AS} {m : Machine} (hs : Sim E F A m) {addr : UInt16} (h : addr < 0x2000 ∨ 0x8000 ≤ addr) :
    (peekK E A addr).mem (go (rd addr) m).1 ∧ (go (rd addr) m).2 = m := by
  by_cases h1 : addr < 0x2000
  · rw [rd_ram h1 hs.trk]
    simp only [peekK, if_pos h1]
    exact ⟨hs.ram _ (mask_lt addr), trivial⟩
  · have h2 : addr ≥ 0x8000 := by
      rcases h with h | h
      · exact absurd h h1
      · exact h
    rw [rd_rom m h1 h2, hs.prg, hs.mask]
    simp only [peekK, if_neg h1]
    exact ⟨mem_known_self _, trivial⟩

theorem rangeJoin_mem {A : AS} {b : UInt16} {x : UInt8} : ∀ (n j : Nat), j ≤ n → (peekK E A (b + j.toUInt16)).mem x → (rangeJoin E A b n).mem x := by
  intro n
  induction n with
  | zero =>
    intro j hj h
    have : j = 0 := by omega
    subst this
    have h0 : b + (0 : Nat).toUInt16 = b := by simp
    rw [h0] at h
    exact h
  | succ n ih =>
    intro j hj h
    by_cases hc : j ≤ n
    · exact mem_join_l _ (ih j hc h)
    · have : j = n + 1 := by omega
      subst this
      exact mem_join_r _ h

theorem offset_of_le {lo addr : UInt16} (h : lo ≤ addr) : lo + (addr.toNat - lo.toNat).toUInt16 = addr := by
  have h1 := UInt16.le_iff_toNat_le.1 h
  have h2 := UInt16.toNat_lt addr
  apply UInt16.toNat_inj.1
  rw [UInt16.toNat_add]
  have h3 : (addr.toNat - lo.toNat).toUInt16.toNat = addr.toNat - lo.toNat := by
    simp only [Nat.toUInt16, UInt16.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    show addr.toNat - lo.toNat < 65536
    have : addr.toNat < 65536 := h2
    omega
  rw [h3]
  have : lo.toNat + (addr.toNat - lo.toNat) = addr.toNat := by omega
  rw [this]
  exact Nat.mod_eq_of_lt h2

theorem s_ard {ad : AAd} {addr : UInt16} (h : AdR ad addr) : Snd E F AB.mem (ard E ad) (rd addr) := by
  intro A m hs a A' he
  unfold ard at he
  by_cases h0 : (ad.lo == ad.hi) = true
  · rw [if_pos h0] at he
    have h00 : ad.lo = ad.hi := by simpa using h0
    rw [adR_same h h00]
    exact s_ardK _ A m hs a A' he
  · rw [if_neg h0] at he
    split at he
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := some_pair he
      have hc' : ad.lo ≤ ad.hi ∧ (ad.hi < 0x2000 ∨ 0x8000 ≤ ad.lo) := by simpa using hc
      have hfold : ∀ (l : List Nat) (B : AS), Sim E F B m → Sim E F (l.foldl (fun B j => B.note E ((ad.lo + j.toUInt16) &&& 0x7FF).toNat) B) m := by
        intro l
        induction l with
        | nil => exact fun B h => h
        | cons j l ih => exact fun B h => ih _ (sim_note h _)
      have hsn : Sim E F (if E.track && ad.hi < 0x2000 then
          (List.range ((ad.hi - ad.lo).toNat + 1)).foldl (fun B j => B.note E ((ad.lo + j.toUInt16) &&& 0x7FF).toNat) A else A) m := by
        split
        · exact hfold _ _ hs
        · exact hs
      rcases h with ⟨_, h2, h3⟩ | ⟨h1, _⟩
      · have hr : addr < 0x2000 ∨ 0x8000 ≤ addr := by
          rcases hc'.2 with h4 | h4
          · left
            have a1 := UInt16.lt_iff_toNat_lt.1 h4
            have a2 := UInt16.le_iff_toNat_le.1 h3
            exact UInt16.lt_iff_toNat_lt.2 (by omega)
          · right
            have a1 := UInt16.le_iff_toNat_le.1 h4
            have a2 := UInt16.le_iff_toNat_le.1 h2
            exact UInt16.le_iff_toNat_le.2 (by omega)
        obtain ⟨hm, hmm⟩ := rd_ramrom hs hr
        rw [hmm]
        refine ⟨?_, hsn, Adv.refl m⟩
        have hb := offset_of_le h2
        have hj : addr.toNat - ad.lo.toNat ≤ (ad.hi - ad.lo).toNat := by
          rw [UInt16.toNat_sub_of_le _ _ hc'.1]
          have a2 := UInt16.le_iff_toNat_le.1 h3
          omega
        refine rangeJoin_mem _ _ hj ?_
        rw [hb]
        exact hm
      · have a1 := UInt16.lt_iff_toNat_lt.1 h1
        have a2 := UInt16.le_iff_toNat_le.1 hc'.1
        omega
    · split at he
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := some_pair he
        have hc' : (ad.hi < ad.lo ∧ ad.hi < 0x2000) ∧ 0x8000 ≤ ad.lo := by simpa using hc
        rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
        · have a1 := UInt16.lt_iff_toNat_lt.1 hc'.1.1
          have a2 := UInt16.le_iff_toNat_le.1 h1
          omega
        · have hr : addr < 0x2000 ∨ 0x8000 ≤ addr := by
            rcases h2 with h4 | h4
            · right
              have a1 := UInt16.le_iff_toNat_le.1 hc'.2
              have a2 := UInt16.le_iff_toNat_le.1 h4
              exact UInt16.le_iff_toNat_le.2 (by omega)
            · left
              have a1 := UInt16.lt_iff_toNat_lt.1 hc'.1.2
              have a2 := UInt16.le_iff_toNat_le.1 h4
              exact UInt16.lt_iff_toNat_lt.2 (by omega)
          obtain ⟨_, hmm⟩ := rd_ramrom hs hr
          rw [hmm]
          exact ⟨mem_top _, hs, Adv.refl m⟩
      · cases he

/-! writes -/

theorem wr_ram {addr : UInt16} {m : Machine} (v : UInt8) (h1 : addr < 0x2000) (ht : m.trk = false) :
    go (wr addr v) m = ((), { m with ram := m.ram.set! (addr &&& 0x7FF).toNat v }) := by
  unfold wr go
  rw [if_pos h1]
  cases m with
  | mk a x y s p pc cyc ram prg prgMask ppuCtrl ppuMask vblank sprite0 nmiPending fdot frame pad padShift padStrobe halted trk trkRead trkWrite trkIO =>
    cases ht
    rfl

theorem s_ppuWrite (r : UInt16) {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (appuWrite r v) (ppuWrite r x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold appuWrite at he
  by_cases h0 : (r == 0) = true
  · rw [if_pos h0] at he
    have hc : go (ppuWrite r x) m = ((), { m with
        ppuCtrl := x
        nmiPending := m.nmiPending || (m.vblank && (x &&& 0x80 != 0) && (m.ppuCtrl &&& 0x80 == 0)) }) := by
      unfold ppuWrite go
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h0, if_true]
      rfl
    rw [hc]
    split at he
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := some_pair he
      refine ⟨trivial, { hs with ppuCtrl := h, nmi := ?_ }, rfl, rfl⟩
      have hb' : A.nmi = true ∨ A.vb = false := by simpa using hb
      show (m.nmiPending || (m.vblank && (x &&& 0x80 != 0) && (m.ppuCtrl &&& 0x80 == 0))) = A.nmi
      rw [hs.nmi, hs.vb]
      rcases hb' with hb' | hb' <;> simp [hb']
    · rename_i hb
      have hb' : A.nmi = false ∧ A.vb = true := by simpa using hb
      split at he
      · rename_i b1 b2 e1 e2
        obtain ⟨rfl, rfl⟩ := some_pair he
        have t1 := TR_bit 0x80 h
        have t2 := TR_bit 0x80 hs.ppuCtrl
        rw [e1] at t1
        rw [e2] at t2
        have t1' : b1 = (x &&& 0x80 != 0) := by
          rcases t1 with t | t
          · cases t
          · exact Option.some.inj t
        have t2' : b2 = (m.ppuCtrl &&& 0x80 != 0) := by
          rcases t2 with t | t
          · cases t
          · exact Option.some.inj t
        refine ⟨trivial, { hs with ppuCtrl := h, nmi := ?_ }, rfl, rfl⟩
        show (m.nmiPending || (m.vblank && (x &&& 0x80 != 0) && (m.ppuCtrl &&& 0x80 == 0))) = (b1 && !b2)
        rw [hs.nmi, hs.vb, hb'.1, hb'.2, t1', t2']
        cases (x &&& 0x80 != 0) <;> cases hh : (m.ppuCtrl &&& 0x80 == 0) <;> simp [bne, hh]
      · cases he
  · rw [if_neg h0] at he
    by_cases h1 : (r == 1) = true
    · rw [if_pos h1] at he
      obtain ⟨rfl, rfl⟩ := some_pair he
      have hc : go (ppuWrite r x) m = ((), { m with ppuMask := x }) := by
        unfold ppuWrite go
        simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h0, h1, if_true, if_false]
        rfl
      rw [hc]
      exact ⟨trivial, { hs with ppuMask := h }, rfl, rfl⟩
    · rw [if_neg h1] at he
      obtain ⟨rfl, rfl⟩ := some_pair he
      have hc : go (ppuWrite r x) m = ((), m) := by
        unfold ppuWrite go
        simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, h0, h1, if_false]
        rfl
      rw [hc]
      exact ⟨trivial, hs, rfl, rfl⟩

theorem and1 (x : UInt8) : (x &&& 1 == 1) = (x &&& 1 != 0) := by
  cases hb : bt x 0 with
  | true =>
    have h : x &&& 1 = 1 := by
      apply bt_ext
      intro i hi
      simp only [bt_and, bt_one hi]
      by_cases h0 : i = 0
      · subst h0
        simp [hb]
      · simp [h0]
    rw [h]
    decide
  | false =>
    have h : x &&& 1 = 0 := by
      apply bt_ext
      intro i hi
      simp only [bt_and, bt_one hi, bt_zero hi]
      by_cases h0 : i = 0
      · subst h0
        simp [hb]
      · simp [h0]
    rw [h]
    decide

theorem s_padWrite {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (apadWrite E v) (padWrite x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold apadWrite at he
  have t := TR_bit 1 h
  rw [← and1] at t
  split at he
  · rename_i e1
    rw [e1] at t
    obtain ⟨rfl, rfl⟩ := some_pair he
    have t' : (x &&& 1 == 1) = true := by
      rcases t with t | t
      · cases t
      · exact (Option.some.inj t).symm
    have hc : go (padWrite x) m = ((), { m with padStrobe := true, padShift := m.pad }) := by
      unfold padWrite go
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, t', if_true]
      rfl
    rw [hc]
    exact ⟨trivial, { hs with padShift := hs.pad, strobe := rfl }, rfl, rfl⟩
  · rename_i e1
    rw [e1] at t
    have t' : ¬ (x &&& 1 == 1) = true := by
      rcases t with t | t
      · cases t
      · rw [← Option.some.inj t]
        simp
    split at he
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := some_pair he
      have hb2 : m.padStrobe = true := by rw [hs.strobe]; exact hb
      have hc : go (padWrite x) m = ((), { m with padStrobe := false, padShift := m.pad }) := by
        unfold padWrite go
        simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, t', if_false, hb2, if_true]
        rfl
      rw [hc]
      exact ⟨trivial, { hs with padShift := hs.pad, strobe := rfl }, rfl, rfl⟩
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := some_pair he
      have hb2 : m.padStrobe = false := by rw [hs.strobe]; simpa using hb
      have hc : go (padWrite x) m = ((), m) := by
        unfold padWrite go
        simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, t', if_false, hb2]
        rfl
      rw [hc]
      exact ⟨trivial, hs, rfl, rfl⟩
  · cases he

theorem sim_setK {A : AS} {m : Machine} (hs : Sim E F A m) {i : Nat} {v : AB} {x : UInt8} (hi : i < 2048) (h : v.mem x) (hrk : A.rk = true → i ≠ E.rkI) :
    Sim E F { A.setK i v with dg := A.dg && !E.D.contains i } { m with ram := m.ram.set! i x } := by
  refine { hs with
    size := by show (m.ram.set! i x).size = 2048; rw [ba_size_set]; exact hs.size
    szR := by show (A.ram.set! i v.v).size = 2048; rw [ba_size_set]; exact hs.szR
    szK := by show (A.kn.set! i v.k).size = 2048; rw [ba_size_set]; exact hs.szK
    ram := ?_
    dg := ?_
    rkv := ?_ }
  · intro j hj
    show AB.mem ⟨(A.ram.set! i v.v).get! j, (A.kn.set! i v.k).get! j⟩ ((m.ram.set! i x).get! j)
    by_cases hij : i = j
    · subst hij
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi),
        ba_get_set_self _ _ _ (by rw [hs.size]; exact hi)]
      exact h
    · rw [ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij]
      exact hs.ram j hj
  · intro hg
    have hg' : A.dg = true ∧ E.D.contains i = false := by simpa using hg
    have hany := hs.dg hg'.1
    obtain ⟨d, hd, hd2⟩ := List.any_eq_true.1 hany
    refine List.any_eq_true.2 ⟨d, hd, ?_⟩
    have hne : i ≠ d := by
      intro he
      subst he
      have : E.D.contains i = true := by simpa using hd
      rw [this] at hg'
      simp at hg'
    show ((m.ram.set! i x).get! d != 0) = true
    rw [ba_get_set_ne _ _ _ _ hne]
    exact hd2
  · intro hr
    show (m.ram.set! i x).get! E.rkI = _
    rw [ba_get_set_ne _ _ _ _ (hrk hr)]
    exact hs.rkv hr

theorem s_wr {ad : AAd} {addr : UInt16} {v : AB} {x : UInt8} (h : AdR ad addr) (hv : v.mem x) : Snd E F TT (awr E ad v) (wr addr x) := by
  intro A m hs a A' he
  unfold awr at he
  by_cases h0 : (ad.lo == ad.hi) = true
  · rw [if_pos h0] at he
    have h00 : ad.lo = ad.hi := by simpa using h0
    have hadr := adR_same h h00
    simp only at he
    rw [← hadr] at he
    by_cases h1 : addr < 0x2000
    · rw [if_pos h1] at he
      split at he
      · cases he
      · rename_i hg
        obtain ⟨rfl, rfl⟩ := some_pair he
        rw [wr_ram x h1 hs.trk]
        have hrk : A.rk = true → (addr &&& 0x7FF).toNat ≠ E.rkI := by
          intro hr hq
          apply hg
          simp [hr, hq]
        exact ⟨trivial, sim_setK hs (mask_lt addr) hv hrk, rfl, Nat.le_refl _⟩
    · rw [if_neg h1] at he
      by_cases h2 : addr < 0x4000
      · rw [if_pos h2] at he
        have hc : go (wr addr x) m = go (ppuWrite (addr &&& 7) x) m := by
          unfold wr go
          rw [if_neg h1, if_pos h2]
        rw [hc]
        exact s_ppuWrite _ hv A m hs a A' he
      · rw [if_neg h2] at he
        by_cases h3 : (addr == 0x4014) = true
        · rw [if_pos h3] at he
          have hc : go (wr addr x) m = go oamDma m := by
            unfold wr go
            rw [if_neg h1, if_neg h2, if_pos h3]
          rw [hc, PipeTransitionAll.oamDma_eq]
          have h5 : 513 ≤ PipeTransitionAll.dmaLen m ∧ PipeTransitionAll.dmaLen m ≤ 514 := by
            unfold PipeTransitionAll.dmaLen
            split <;> omega
          exact s_tick h5.1 h5.2 A m hs a A' he
        · rw [if_neg h3] at he
          by_cases h4 : (addr == 0x4016) = true
          · rw [if_pos h4] at he
            have hc : go (wr addr x) m = go (padWrite x) m := by
              unfold wr go
              rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
            rw [hc]
            exact s_padWrite hv A m hs a A' he
          · rw [if_neg h4] at he
            obtain ⟨rfl, rfl⟩ := some_pair he
            have hc : go (wr addr x) m = ((), m) := by
              unfold wr go
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
              rfl
            rw [hc]
            exact ⟨trivial, hs, Adv.refl m⟩
  · rw [if_neg h0] at he
    cases he

end

/-! ## The instructions -/

section
variable {E : Env} {F : Nat × UInt8}

theorem s_fetch : Snd E F Eq (afetch E) fetch := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold afetch at he
  split at he
  · rename_i hp
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hpc : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
    have h1 : ¬ m.pc < 0x2000 := by
      intro h
      have a1 := UInt16.lt_iff_toNat_lt.1 h
      have a2 := UInt16.le_iff_toNat_le.1 hpc
      revert a1 a2
      simp
      omega
    have hc : go fetch m = (m.prg.get! (m.pc &&& m.prgMask).toNat, { m with pc := m.pc + 1 }) := by
      have : go fetch m = go (rd m.pc) { m with pc := m.pc + 1 } := rfl
      rw [this, rd_rom _ h1 hpc]
    have hv : E.prg.get! (A.pc &&& E.mask).toNat = m.prg.get! (m.pc &&& m.prgMask).toNat := by
      rw [hs.prg, hs.mask, hs.pc]
    rw [hc]
    refine ⟨hv, { hs with pc := ?_ }, rfl, rfl⟩
    show m.pc + 1 = A.pc + 1
    rw [hs.pc]
  · cases he

theorem s_fetch16 : Snd E F Eq (afetch16 E) fetch16 :=
  Snd.bind s_fetch fun _ _ h1 => Snd.bind s_fetch fun _ _ h2 => by
    subst h1 h2
    exact Snd.pure rfl

theorem s_rd16zp (z : UInt8) : Snd E F (fun (p : AB × AB) (q : UInt16) => ∃ a b : UInt8, q = a.toUInt16 ||| (b.toUInt16 <<< 8) ∧ p.1.mem a ∧ p.2.mem b) (ard16zp E z) (rd16zp z) :=
  Snd.bind (s_ard (adR_exact _)) fun _ _ h1 => Snd.bind (s_ard (adR_exact _)) fun _ _ h2 => Snd.pure ⟨_, _, rfl, h1, h2⟩

theorem toUInt16_le (x : UInt8) : x.toUInt16.toNat ≤ 255 := by
  have := UInt8.toNat_lt x
  simp
  omega

theorem addIdx_ok (b : UInt16) {i : AB} {x : UInt8} (h : i.mem x) : AdR (addIdx b i) (b + x.toUInt16) := by
  unfold addIdx
  split
  · rename_i hk
    rw [isK_eq hk h]
    exact adR_exact _
  · have a1 := minv_le h
    have a2 := le_maxv h
    have h1 : i.minv.toNat ≤ 255 := by have := UInt8.toNat_lt i.minv; omega
    have h2 : i.maxv.toNat ≤ 255 := by have := UInt8.toNat_lt i.maxv; omega
    have h3 : x.toNat ≤ 255 := by have := UInt8.toNat_lt x; omega
    have hb : b.toNat < 65536 := UInt16.toNat_lt b
    split
    · rename_i hn
      have e1 : (b + i.minv.toUInt16).toNat = b.toNat + i.minv.toNat := by
        rw [UInt16.toNat_add]
        simp only [UInt8.toNat_toUInt16]
        exact Nat.mod_eq_of_lt (by omega)
      have e2 : (b + i.maxv.toUInt16).toNat = b.toNat + i.maxv.toNat := by
        rw [UInt16.toNat_add]
        simp only [UInt8.toNat_toUInt16]
        exact Nat.mod_eq_of_lt (by omega)
      have e3 : (b + x.toUInt16).toNat = b.toNat + x.toNat := by
        rw [UInt16.toNat_add]
        simp only [UInt8.toNat_toUInt16]
        exact Nat.mod_eq_of_lt (by omega)
      left
      refine ⟨?_, ?_, ?_⟩
      · apply UInt16.le_iff_toNat_le.2
        show (b + i.minv.toUInt16).toNat ≤ (b + i.maxv.toUInt16).toNat
        omega
      · apply UInt16.le_iff_toNat_le.2
        show (b + i.minv.toUInt16).toNat ≤ (b + x.toUInt16).toNat
        omega
      · apply UInt16.le_iff_toNat_le.2
        show (b + x.toUInt16).toNat ≤ (b + i.maxv.toUInt16).toNat
        omega
    · rename_i hn
      have e4 : (b + (255 : UInt16)).toNat = b.toNat + 255 - 65536 := by
        rw [UInt16.toNat_add]
        have h255 : (255 : UInt16).toNat = 255 := rfl
        rw [h255]
        rw [Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      right
      refine ⟨?_, ?_⟩
      · apply UInt16.lt_iff_toNat_lt.2
        show (b + (255 : UInt16)).toNat < b.toNat
        omega
      · by_cases ho : b.toNat + x.toNat < 65536
        · left
          apply UInt16.le_iff_toNat_le.2
          show b.toNat ≤ (b + x.toUInt16).toNat
          rw [UInt16.toNat_add]
          simp only [UInt8.toNat_toUInt16]
          have hh : (b.toNat + x.toNat) % 65536 = b.toNat + x.toNat := Nat.mod_eq_of_lt ho
          show b.toNat ≤ (b.toNat + x.toNat) % 65536
          omega
        · right
          apply UInt16.le_iff_toNat_le.2
          show (b + x.toUInt16).toNat ≤ (b + (255 : UInt16)).toNat
          rw [e4, UInt16.toNat_add]
          simp only [UInt8.toNat_toUInt16]
          show (b.toNat + x.toNat) % 65536 ≤ _
          rw [Nat.mod_eq_sub_mod (by omega)]
          have hh : (b.toNat + x.toNat - 65536) % 65536 = b.toNat + x.toNat - 65536 := Nat.mod_eq_of_lt (by omega)
          omega

theorem s_mImm : Snd E F AdR aImm mImm := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  have hc : go mImm m = (m.pc, { m with pc := m.pc + 1 }) := rfl
  rw [hc]
  refine ⟨?_, { hs with pc := ?_ }, rfl, rfl⟩
  · show AdR (AAd.exact A.pc) m.pc
    rw [hs.pc]
    exact adR_exact _
  · show m.pc + 1 = A.pc + 1
    rw [hs.pc]

theorem s_mZp : Snd E F AdR (aZp E) mZp :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.pure (adR_exact _)

theorem zpi_ok (b : UInt8) {i : AB} {x : UInt8} (h : i.mem x) :
    AdR (if i.isK then AAd.exact (b + i.v).toUInt16 else ⟨0, 255⟩) (b + x).toUInt16 := by
  split
  · rename_i hk
    rw [isK_eq hk h]
    exact adR_exact _
  · left
    refine ⟨by decide, ?_, ?_⟩
    · exact UInt16.le_iff_toNat_le.2 (Nat.zero_le _)
    · apply UInt16.le_iff_toNat_le.2
      exact toUInt16_le _

theorem s_mZpx : Snd E F AdR (aZpi E (·.x)) mZpx :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.pure (zpi_ok _ hs.x)
theorem s_mZpy : Snd E F AdR (aZpi E (·.y)) mZpy :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.pure (zpi_ok _ hs.y)
theorem s_mAbs : Snd E F AdR (aAbs E) mAbs :=
  Snd.congr (g := fetch16 >>= fun x => Pure.pure x) (fun _ => rfl) <| Snd.bind s_fetch16 fun _ _ h => by
    subst h
    exact Snd.pure (adR_exact _)
theorem s_mAbx : Snd E F AdR (aAbi E (·.x)) mAbx :=
  Snd.bind s_fetch16 fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.pure (addIdx_ok _ hs.x)
theorem s_mAby : Snd E F AdR (aAbi E (·.y)) mAby :=
  Snd.bind s_fetch16 fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.pure (addIdx_ok _ hs.y)

theorem s_penalty {b : UInt16} {ad : AAd} {e : UInt16} (h : AdR ad e) : Snd E F TT (apenalty b ad) (pagePenalty b e) := by
  unfold apenalty
  by_cases h0 : (ad.lo == ad.hi) = true
  · rw [if_pos h0]
    have h00 : ad.lo = ad.hi := by simpa using h0
    have he := adR_same h h00
    subst he
    unfold pagePenalty
    split
    · exact s_tick (Nat.le_refl _) (Nat.le_refl _)
    · exact Snd.pure trivial
  · rw [if_neg h0]
    unfold pagePenalty
    split
    · exact s_tick (Nat.zero_le _) (Nat.le_refl _)
    · exact s_tick0

theorem s_mAbxR : Snd E F AdR (aAbiR E (·.x)) mAbxR :=
  Snd.bind s_fetch16 fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.bind (s_penalty (addIdx_ok _ hs.x)) fun _ _ _ => Snd.pure (addIdx_ok _ hs.x)
theorem s_mAbyR : Snd E F AdR (aAbiR E (·.y)) mAbyR :=
  Snd.bind s_fetch16 fun _ _ h => by
    subst h
    exact Snd.get fun _ _ hs => Snd.bind (s_penalty (addIdx_ok _ hs.y)) fun _ _ _ => Snd.pure (addIdx_ok _ hs.y)

theorem ptrOf_ok {lo hi : AB} {a b : UInt8} {t : UInt16} (h : ptrOf lo hi = some t) (h1 : lo.mem a) (h2 : hi.mem b) :
    a.toUInt16 ||| (b.toUInt16 <<< 8) = t := by
  unfold ptrOf at h
  split at h
  · rename_i hk
    simp only [Bool.and_eq_true] at hk
    rw [isK_eq hk.1 h1, isK_eq hk.2 h2]
    exact Option.some.inj h
  · cases h

theorem s_mIzx : Snd E F AdR (aIzx E) mIzx :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.get fun A m hs => ?_
    by_cases hk : A.x.isK = true
    · simp only [hk, if_true]
      rw [isK_eq hk hs.x]
      refine Snd.congr (g := rd16zp _ >>= fun q => Pure.pure q) (fun _ => rfl) (Snd.bind (s_rd16zp _) fun p q hr => ?_)
      obtain ⟨lo, hi⟩ := p
      obtain ⟨u, v, rfl, h1, h2⟩ := hr
      cases hp : ptrOf lo hi with
      | none =>
        simp only [hp]
        exact Snd.fail
      | some t =>
        simp only [hp]
        rw [ptrOf_ok hp h1 h2]
        exact Snd.pure (adR_exact _)
    · simp only [hk, if_false]
      exact Snd.fail

theorem s_mIzy : Snd E F AdR (aIzy E) mIzy :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.bind (s_rd16zp _) fun p q hr => ?_
    obtain ⟨lo, hi⟩ := p
    obtain ⟨u, v, rfl, h1, h2⟩ := hr
    cases hp : ptrOf lo hi with
    | none =>
      simp only [hp]
      exact Snd.fail
    | some t =>
      simp only [hp]
      rw [ptrOf_ok hp h1 h2]
      exact Snd.get fun _ _ hs => Snd.pure (addIdx_ok _ hs.y)

theorem s_mIzyR : Snd E F AdR (aIzyR E) mIzyR :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.bind (s_rd16zp _) fun p q hr => ?_
    obtain ⟨lo, hi⟩ := p
    obtain ⟨u, v, rfl, h1, h2⟩ := hr
    cases hp : ptrOf lo hi with
    | none =>
      simp only [hp]
      exact Snd.fail
    | some t =>
      simp only [hp]
      rw [ptrOf_ok hp h1 h2]
      exact Snd.get fun _ _ hs => Snd.bind (s_penalty (addIdx_ok _ hs.y)) fun _ _ _ => Snd.pure (addIdx_ok _ hs.y)

/-! ALU -/

theorem s_setPC (t : UInt16) : Snd E F TT (asetPC t) (setPC t) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with pc := rfl }, rfl, rfl⟩

end

section
variable {E : Env} {F : Nat × UInt8}

theorem mem_iteN (c : Prop) [Decidable c] (t e : UInt8) : (AB.ite none t e).mem (if c then t else e) := by
  by_cases h : c
  · rw [if_pos h]
    exact mem_join_l _ (mem_known_self _)
  · rw [if_neg h]
    exact mem_join_r _ (mem_known_self _)

theorem s_push {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (apush E v) (push x) := by
  intro A m hs a A' he
  have hc : go (push x) m = go (wr (0x100 ||| A.s.toUInt16) x) { m with s := m.s - 1 } := by
    rw [← hs.s]
    rfl
  have he2 : awr E (AAd.exact (0x100 ||| A.s.toUInt16)) v { A with s := A.s - 1 } = some (a, A') := he
  have hs1 : Sim E F { A with s := A.s - 1 } { m with s := m.s - 1 } := { hs with
    s := by
      show m.s - 1 = A.s - 1
      rw [hs.s] }
  rw [hc]
  obtain ⟨h1, h2, h3⟩ := s_wr (adR_exact _) h _ _ hs1 _ _ he2
  exact ⟨h1, h2, h3⟩

theorem s_pull : Snd E F AB.mem (apull E) pull := by
  intro A m hs a A' he
  have hc : go pull m = go (rd (0x100 ||| (A.s + 1).toUInt16)) { m with s := m.s + 1 } := by
    rw [← hs.s]
    rfl
  have he2 : ard E (AAd.exact (0x100 ||| (A.s + 1).toUInt16)) { A with s := A.s + 1 } = some (a, A') := he
  have hs1 : Sim E F { A with s := A.s + 1 } { m with s := m.s + 1 } := { hs with
    s := by
      show m.s + 1 = A.s + 1
      rw [hs.s] }
  rw [hc]
  obtain ⟨h1, h2, h3⟩ := s_ard (adR_exact _) _ _ hs1 _ _ he2
  exact ⟨h1, h2, h3⟩

theorem s_adc {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aadc v) (adc x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold aadc at he
  simp only at he
  have hcm : (A.p.and (AB.known 1)).mem (m.p &&& 1) := mem_and hs.p (mem_known_self _)
  split at he
  · rename_i hk
    simp only [Bool.and_eq_true] at hk
    obtain ⟨⟨k1, k2⟩, k3⟩ := hk
    obtain ⟨rfl, rfl⟩ := some_pair he
    have e1 := isK_eq k1 hs.a
    have e2 := isK_eq k2 h
    have e3 := isK_eq k3 hcm
    have hp := hs.p
    refine ⟨trivial, { hs with a := ?_, p := ?_ }, rfl, rfl⟩
    · show (AB.known _).mem _
      show (AB.known _).mem (m.a.toUInt16 + x.toUInt16 + (m.p &&& 1).toUInt16).toUInt8
      rw [e1, e2, e3]
      exact mem_known_self _
    · show AB.mem _ ((m.p &&& 0x3C) ||| _ ||| _ ||| _ ||| _)
      rw [e1, e2, e3]
      exact mem_or (mem_or (mem_or (mem_or (mem_and hp (mem_known_self _)) (mem_known_self _)) (mem_known_self _)) (mem_known_self _)) (mem_known_self _)
  · obtain ⟨rfl, rfl⟩ := some_pair he
    have hp := hs.p
    refine ⟨trivial, { hs with a := mem_top _, p := ?_ }, rfl, rfl⟩
    exact mem_or (mem_or (mem_or (mem_or (mem_and hp (mem_known_self _)) (mem_iteN _ _ _)) (mem_iteN _ _ _)) (mem_and (mem_top _) (mem_known_self _))) (mem_iteN _ _ _)

theorem s_oraV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aoraV v) (oraV x) :=
  Snd.get fun _ _ hs => s_setA (mem_or hs.a h)
theorem s_andV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aandV v) (andV x) :=
  Snd.get fun _ _ hs => s_setA (mem_and hs.a h)
theorem s_eorV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aeorV v) (eorV x) :=
  Snd.get fun _ _ hs => s_setA (mem_xor hs.a h)

theorem s_cmpV {r v : AB} {x y : UInt8} (h1 : r.mem x) (h2 : v.mem y) : Snd E F TT (acmpV r v) (cmpV x y) := by
  intro A m hs a A' he
  have hd : (if r.isK && v.isK then AB.known (r.v - v.v) else AB.top : AB).mem (x - y) := by
    split
    · rename_i hk
      simp only [Bool.and_eq_true] at hk
      rw [isK_eq hk.1 h1, isK_eq hk.2 h2]
      exact mem_known_self _
    · exact mem_top _
  have hc : go (cmpV x y) m = go (setFlag 0x01 (decide (x ≥ y))) { m with p := (m.p &&& 0x7D) ||| (if x - y == 0 then 0x02 else 0) ||| ((x - y) &&& 0x80) } := rfl
  have hs1 : Sim E F { A with p := ((A.p.and (AB.known 0x7D)).or (AB.ite (aeqTri r v) 0x02 0)).or ((if r.isK && v.isK then AB.known (r.v - v.v) else AB.top : AB).and (AB.known 0x80)) }
      { m with p := (m.p &&& 0x7D) ||| (if x - y == 0 then 0x02 else 0) ||| ((x - y) &&& 0x80) } := { hs with
    p := mem_or (mem_or (mem_and hs.p (mem_known_self _)) (mem_ite (TR_eqSub h1 h2) _ _)) (mem_and hd (mem_known_self _)) }
  rw [hc]
  obtain ⟨g1, g2, g3⟩ := s_setFlag 0x01 (TR_ge h1 h2) _ _ hs1 a A' he
  exact ⟨g1, g2, g3⟩

theorem s_aslV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (aaslV v) (aslV x) :=
  Snd.bind (s_setFlag 0x01 (TR_bit 0x80 h)) fun _ _ _ => Snd.bind (s_setZN (mem_shl h)) fun _ _ _ => Snd.pure (mem_shl h)
theorem s_lsrV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (alsrV v) (lsrV x) :=
  Snd.bind (s_setFlag 0x01 (TR_bit 1 h)) fun _ _ _ => Snd.bind (s_setZN (mem_shr h)) fun _ _ _ => Snd.pure (mem_shr h)
theorem s_rolV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (arolV v) (rolV x) :=
  Snd.get fun _ _ hs =>
    have hr := mem_or (mem_shl h) (mem_and hs.p (mem_known_self 1))
    Snd.bind (s_setFlag 0x01 (TR_bit 0x80 h)) fun _ _ _ => Snd.bind (s_setZN hr) fun _ _ _ => Snd.pure hr
theorem s_rorV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (arorV v) (rorV x) :=
  Snd.get fun _ _ hs =>
    have hr := mem_or (mem_shr h) (mem_shl7 (mem_and hs.p (mem_known_self 1)))
    Snd.bind (s_setFlag 0x01 (TR_bit 1 h)) fun _ _ _ => Snd.bind (s_setZN hr) fun _ _ _ => Snd.pure hr
theorem s_incV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (aincV v) (incV x) :=
  Snd.bind (s_setZN (mem_map1 _ h)) fun _ _ _ => Snd.pure (mem_map1 _ h)
theorem s_decV {v : AB} {x : UInt8} (h : v.mem x) : Snd E F AB.mem (adecV v) (decV x) :=
  Snd.bind (s_setZN (mem_map1 _ h)) fun _ _ _ => Snd.pure (mem_map1 _ h)

section
variable {amd : AMode} {md : Mode}

theorem s_LDA (h : Snd E F AdR amd md) : Snd E F TT (aLDA E amd) (opLDA md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_setA hv
theorem s_LDX (h : Snd E F AdR amd md) : Snd E F TT (aLDX E amd) (opLDX md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_setX hv
theorem s_LDY (h : Snd E F AdR amd md) : Snd E F TT (aLDY E amd) (opLDY md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_setY hv
theorem s_modAX {v : AB} {x : UInt8} (h : v.mem x) :
    Snd E F TT (modify fun A => { A with a := v, x := v } : AM Unit) (modify fun m => { m with a := x, x := x }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with a := h, x := h }, rfl, rfl⟩
theorem s_LAX (h : Snd E F AdR amd md) : Snd E F TT (aLAX E amd) (opLAX md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.bind (s_modAX hv) fun _ _ _ => s_setZN hv
theorem s_STA (h : Snd E F AdR amd md) : Snd E F TT (aSTA E amd) (opSTA md) :=
  Snd.bind h fun _ _ ha => Snd.get fun _ _ hs => s_wr ha hs.a
theorem s_STX (h : Snd E F AdR amd md) : Snd E F TT (aSTX E amd) (opSTX md) :=
  Snd.bind h fun _ _ ha => Snd.get fun _ _ hs => s_wr ha hs.x
theorem s_STY (h : Snd E F AdR amd md) : Snd E F TT (aSTY E amd) (opSTY md) :=
  Snd.bind h fun _ _ ha => Snd.get fun _ _ hs => s_wr ha hs.y
theorem s_SAX (h : Snd E F AdR amd md) : Snd E F TT (aSAX E amd) (opSAX md) :=
  Snd.bind h fun _ _ ha => Snd.get fun _ _ hs => s_wr ha (mem_and hs.a hs.x)
theorem s_ADC (h : Snd E F AdR amd md) : Snd E F TT (aADC E amd) (opADC md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_adc hv
theorem s_SBC (h : Snd E F AdR amd md) : Snd E F TT (aSBC E amd) (opSBC md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_adc (mem_not hv)
theorem s_ORA (h : Snd E F AdR amd md) : Snd E F TT (aORA E amd) (opORA md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_oraV hv
theorem s_AND (h : Snd E F AdR amd md) : Snd E F TT (aAND E amd) (opAND md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_andV hv
theorem s_EOR (h : Snd E F AdR amd md) : Snd E F TT (aEOR E amd) (opEOR md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_eorV hv
theorem s_CMP (h : Snd E F AdR amd md) : Snd E F TT (aCMP E amd) (opCMP md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.get fun _ _ hs => s_cmpV hs.a hv
theorem s_CPX (h : Snd E F AdR amd md) : Snd E F TT (aCPX E amd) (opCPX md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.get fun _ _ hs => s_cmpV hs.x hv
theorem s_CPY (h : Snd E F AdR amd md) : Snd E F TT (aCPY E amd) (opCPY md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.get fun _ _ hs => s_cmpV hs.y hv
theorem s_bitFlags {v : AB} {x : UInt8} (hv : v.mem x) :
    Snd E F TT (modify fun A => { A with p := ((A.p.and (AB.known 0x3D)).or (v.and (AB.known 0xC0))).or (AB.ite (A.a.and v).isZero 0x02 0) } : AM Unit)
      (modify fun m => { m with p := (m.p &&& 0x3D) ||| (x &&& 0xC0) ||| (if m.a &&& x == 0 then 0x02 else 0) }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with p := mem_or (mem_or (mem_and hs.p (mem_known_self _)) (mem_and hv (mem_known_self _))) (mem_ite (TR_isZero (mem_and hs.a hv)) _ _) }, rfl, rfl⟩
theorem s_BIT (h : Snd E F AdR amd md) : Snd E F TT (aBIT E amd) (opBIT md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_bitFlags hv

theorem s_rmw {af : AB → AM AB} {f : UInt8 → M UInt8} (hf : ∀ v x, v.mem x → Snd E F AB.mem (af v) (f x)) (h : Snd E F AdR amd md) :
    Snd E F TT (armw E amd af) (rmw f md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.bind (hf _ _ hv) fun _ _ hr => s_wr ha hr
theorem s_rmw2 {af : AB → AM AB} {f : UInt8 → M UInt8} {ag : AB → AM Unit} {g : UInt8 → M Unit}
    (hf : ∀ v x, v.mem x → Snd E F AB.mem (af v) (f x)) (hg : ∀ v x, v.mem x → Snd E F TT (ag v) (g x)) (h : Snd E F AdR amd md) :
    Snd E F TT (armw2 E amd af ag) (rmw2 f g md) :=
  Snd.bind h fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => Snd.bind (hf _ _ hv) fun _ _ hr =>
    Snd.bind (s_wr ha hr) fun _ _ _ => hg _ _ hr

theorem s_ASL (h : Snd E F AdR amd md) : Snd E F TT (aASL E amd) (opASL md) := s_rmw (fun _ _ => s_aslV) h
theorem s_LSR (h : Snd E F AdR amd md) : Snd E F TT (aLSR E amd) (opLSR md) := s_rmw (fun _ _ => s_lsrV) h
theorem s_ROL (h : Snd E F AdR amd md) : Snd E F TT (aROL E amd) (opROL md) := s_rmw (fun _ _ => s_rolV) h
theorem s_ROR (h : Snd E F AdR amd md) : Snd E F TT (aROR E amd) (opROR md) := s_rmw (fun _ _ => s_rorV) h
theorem s_INC (h : Snd E F AdR amd md) : Snd E F TT (aINC E amd) (opINC md) := s_rmw (fun _ _ => s_incV) h
theorem s_DEC (h : Snd E F AdR amd md) : Snd E F TT (aDEC E amd) (opDEC md) := s_rmw (fun _ _ => s_decV) h
theorem s_SLO (h : Snd E F AdR amd md) : Snd E F TT (aSLO E amd) (opSLO md) := s_rmw2 (fun _ _ => s_aslV) (fun _ _ => s_oraV) h
theorem s_RLA (h : Snd E F AdR amd md) : Snd E F TT (aRLA E amd) (opRLA md) := s_rmw2 (fun _ _ => s_rolV) (fun _ _ => s_andV) h
theorem s_SRE (h : Snd E F AdR amd md) : Snd E F TT (aSRE E amd) (opSRE md) := s_rmw2 (fun _ _ => s_lsrV) (fun _ _ => s_eorV) h
theorem s_RRA (h : Snd E F AdR amd md) : Snd E F TT (aRRA E amd) (opRRA md) := s_rmw2 (fun _ _ => s_rorV) (fun _ _ => s_adc) h
theorem s_DCP (h : Snd E F AdR amd md) : Snd E F TT (aDCP E amd) (opDCP md) :=
  s_rmw2 (fun _ _ hv => Snd.pure (mem_map1 _ hv)) (fun _ _ hv => Snd.get fun _ _ hs => s_cmpV hs.a hv) h
theorem s_ISB (h : Snd E F AdR amd md) : Snd E F TT (aISB E amd) (opISB md) :=
  s_rmw2 (fun _ _ hv => Snd.pure (mem_map1 _ hv)) (fun _ _ hv => s_adc (mem_not hv)) h
theorem s_NOPm (h : Snd E F AdR amd md) : Snd E F TT (aNOPm amd) (opNOPm md) :=
  Snd.bind h fun _ _ _ => Snd.pure trivial
end

theorem s_NOP : Snd E F TT aNOP opNOP := Snd.pure trivial
theorem s_JAM : Snd E F TT aJAM opJAM := Snd.fail

theorem s_accOp {af : AB → AM AB} {f : UInt8 → M UInt8} (hf : ∀ {v x}, v.mem x → Snd E F AB.mem (af v) (f x)) : Snd E F TT (aaccOp af) (accOp f) :=
  Snd.get fun _ _ hs => Snd.bind (hf hs.a) fun _ _ hr => s_modA hr

theorem s_branch (mask : UInt8) (neg : Bool) {cond : Machine → Bool} (hc : ∀ m, cond m = ((m.p &&& mask != 0) == neg)) :
    Snd E F TT (abranch E mask neg) (branch cond) :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.get fun A m hs => ?_
    have t := TR_bit mask hs.p
    cases e : A.p.bit mask with
    | none =>
      simp only [e]
      exact Snd.fail
    | some b =>
      rw [e] at t
      have hb : b = (m.p &&& mask != 0) := by
        rcases t with t | t
        · cases t
        · exact Option.some.inj t
      simp only [e, hc, ← hb, ← hs.pc]
      by_cases hn : (b == neg) = true
      · simp only [hn, if_true]
        exact Snd.bind (s_setPC _) fun _ _ _ => s_tick (Nat.le_refl _) (Nat.le_refl _)
      · simp only [hn, if_false]
        exact Snd.pure trivial

theorem s_BPL : Snd E F TT (abranch E 0x80 false) opBPL := s_branch _ _ fun m => by cases h : (m.p &&& 0x80 == 0) <;> simp [bne, h]
theorem s_BMI : Snd E F TT (abranch E 0x80 true) opBMI := s_branch _ _ fun m => by simp
theorem s_BVC : Snd E F TT (abranch E 0x40 false) opBVC := s_branch _ _ fun m => by cases h : (m.p &&& 0x40 == 0) <;> simp [bne, h]
theorem s_BVS : Snd E F TT (abranch E 0x40 true) opBVS := s_branch _ _ fun m => by simp
theorem s_BCC : Snd E F TT (abranch E 0x01 false) opBCC := s_branch _ _ fun m => by cases h : (m.p &&& 0x01 == 0) <;> simp [bne, h]
theorem s_BCS : Snd E F TT (abranch E 0x01 true) opBCS := s_branch _ _ fun m => by simp
theorem s_BNE : Snd E F TT (abranch E 0x02 false) opBNE := s_branch _ _ fun m => by cases h : (m.p &&& 0x02 == 0) <;> simp [bne, h]
theorem s_BEQ : Snd E F TT (abranch E 0x02 true) opBEQ := s_branch _ _ fun m => by simp

theorem s_flag (mask : UInt8) (b : Bool) : Snd E F TT (asetFlag mask (some b)) (setFlag mask b) := s_setFlag mask (TR_some b)
theorem s_CLC : Snd E F TT (asetFlag 0x01 (some false)) opCLC := s_flag _ _
theorem s_SEC : Snd E F TT (asetFlag 0x01 (some true)) opSEC := s_flag _ _
theorem s_CLI : Snd E F TT (asetFlag 0x04 (some false)) opCLI := s_flag _ _
theorem s_SEI : Snd E F TT (asetFlag 0x04 (some true)) opSEI := s_flag _ _
theorem s_CLV : Snd E F TT (asetFlag 0x40 (some false)) opCLV := s_flag _ _
theorem s_CLD : Snd E F TT (asetFlag 0x08 (some false)) opCLD := s_flag _ _
theorem s_SED : Snd E F TT (asetFlag 0x08 (some true)) opSED := s_flag _ _

theorem s_TAX : Snd E F TT aTAX opTAX := Snd.get fun _ _ hs => s_setX hs.a
theorem s_TAY : Snd E F TT aTAY opTAY := Snd.get fun _ _ hs => s_setY hs.a
theorem s_TXA : Snd E F TT aTXA opTXA := Snd.get fun _ _ hs => s_setA hs.x
theorem s_TYA : Snd E F TT aTYA opTYA := Snd.get fun _ _ hs => s_setA hs.y
theorem s_TSX : Snd E F TT aTSX opTSX := Snd.get fun A m hs => by
  rw [hs.s]
  exact s_setX (mem_known_self _)
theorem s_TXS : Snd E F TT aTXS opTXS := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold aTXS at he
  split at he
  · rename_i hk
    obtain ⟨rfl, rfl⟩ := some_pair he
    refine ⟨trivial, { hs with s := isK_eq hk hs.x }, rfl, rfl⟩
  · cases he
theorem s_INX : Snd E F TT aINX opINX := Snd.get fun _ _ hs => s_setX (mem_map1 _ hs.x)
theorem s_INY : Snd E F TT aINY opINY := Snd.get fun _ _ hs => s_setY (mem_map1 _ hs.y)
theorem s_DEX : Snd E F TT aDEX opDEX := Snd.get fun _ _ hs => s_setX (mem_map1 _ hs.x)
theorem s_DEY : Snd E F TT aDEY opDEY := Snd.get fun _ _ hs => s_setY (mem_map1 _ hs.y)
theorem s_PHA : Snd E F TT (aPHA E) opPHA := Snd.get fun _ _ hs => s_push hs.a
theorem s_PHP : Snd E F TT (aPHP E) opPHP := Snd.get fun _ _ hs => s_push (mem_or hs.p (mem_known_self _))
theorem s_PLA : Snd E F TT (aPLA E) opPLA := Snd.bind s_pull fun _ _ hv => s_setA hv
theorem s_modP {v : AB} {x : UInt8} (hv : v.mem x) :
    Snd E F TT (modify fun A => { A with p := (v.and (AB.known 0xEF)).or (AB.known 0x20) } : AM Unit)
      (modify fun m => { m with p := (x &&& 0xEF) ||| 0x20 }) := by
  refine snd_leaf fun A m hs a A' he => ?_
  obtain ⟨rfl, rfl⟩ := some_pair he
  exact ⟨trivial, { hs with p := mem_or (mem_and hv (mem_known_self _)) (mem_known_self _) }, rfl, rfl⟩
theorem s_PLP : Snd E F TT (aPLP E) opPLP := Snd.bind s_pull fun _ _ hv => s_modP hv

theorem s_JMP : Snd E F TT (aJMP E) opJMP := Snd.bind s_fetch16 fun _ _ h => by
  subst h
  exact s_setPC _

theorem s_ptrPC {lo hi : AB} {u v : UInt8} (h1 : lo.mem u) (h2 : hi.mem v) (g : UInt16 → UInt16) :
    Snd E F TT (match ptrOf lo hi with
      | some t => asetPC (g t)
      | none => failure) (setPC (g (u.toUInt16 ||| (v.toUInt16 <<< 8)))) := by
  cases hp : ptrOf lo hi with
  | none =>
    simp only
    exact Snd.fail
  | some t =>
    simp only
    rw [ptrOf_ok hp h1 h2]
    exact s_setPC _

theorem s_JMPi : Snd E F TT (aJMPi E) opJMPi := Snd.bind s_fetch16 fun _ _ h => by
  subst h
  exact Snd.bind (s_ard (adR_exact _)) fun _ _ h1 => Snd.bind (s_ard (adR_exact _)) fun _ _ h2 => s_ptrPC h1 h2 id
theorem s_JSR : Snd E F TT (aJSR E) opJSR := Snd.bind s_fetch16 fun _ _ h => by
  subst h
  refine Snd.get fun A m hs => ?_
  rw [hs.pc]
  exact Snd.bind (s_push (mem_known_self _)) fun _ _ _ => Snd.bind (s_push (mem_known_self _)) fun _ _ _ => s_setPC _
theorem s_RTS : Snd E F TT (aRTS E) opRTS :=
  Snd.bind s_pull fun _ _ h1 => Snd.bind s_pull fun _ _ h2 => s_ptrPC h1 h2 (· + 1)
theorem s_RTI : Snd E F TT (aRTI E) opRTI :=
  Snd.bind s_PLP fun _ _ _ => Snd.bind s_pull fun _ _ h1 => Snd.bind s_pull fun _ _ h2 => s_ptrPC h1 h2 id
theorem s_interrupt (pc : UInt16) {v : AB} {x : UInt8} (h : v.mem x) (vector : UInt16) : Snd E F TT (ainterrupt E pc v vector) (interrupt pc x vector) :=
  Snd.bind (s_push (mem_known_self _)) fun _ _ _ => Snd.bind (s_push (mem_known_self _)) fun _ _ _ => Snd.bind (s_push h) fun _ _ _ =>
    Snd.bind (s_setFlag _ (TR_some true)) fun _ _ _ => Snd.bind (s_ard (adR_exact _)) fun _ _ h1 => Snd.bind (s_ard (adR_exact _)) fun _ _ h2 =>
      s_ptrPC h1 h2 id
theorem s_BRK : Snd E F TT (aBRK E) opBRK := Snd.get fun A m hs => by
  rw [hs.pc]
  exact s_interrupt _ (mem_or hs.p (mem_known_self _)) _

theorem s_nmi : Snd E F TT (anmi E) nmi := by
  intro A m hs a A' he
  have h2 : (ainterrupt E A.pc ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)) 0xFFFA >>= fun _ => atick 7 7) { A with nmi := false } = some (a, A') := he
  have hc : go nmi m = go (interrupt A.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA >>= fun _ => tick 7) { m with nmiPending := false } := by
    rw [← hs.pc]
    rfl
  have hs1 : Sim E F { A with nmi := false } { m with nmiPending := false } := { hs with nmi := rfl }
  have hv : ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)).mem ((m.p &&& 0xEF) ||| 0x20) :=
    mem_or (mem_and hs.p (mem_known_self _)) (mem_known_self _)
  rw [hc]
  obtain ⟨g1, g2, g3⟩ := (Snd.bind (s_interrupt A.pc hv 0xFFFA) fun _ _ _ => s_tick (Nat.le_refl 7) (Nat.le_refl 7)) _ _ hs1 a A' h2
  exact ⟨g1, g2, g3⟩

/-! ## The table of opcodes -/

/-- two tables of the same length, entry by entry -/
def AllS (E : Env) (F : Nat × UInt8) : List (AM Unit) → List (M Unit) → Prop
  | [], [] => True
  | a :: l, f :: r => Snd E F TT a f ∧ AllS E F l r
  | _, _ => False

theorem AllS.append {a b : List (AM Unit)} {f g : List (M Unit)} (h1 : AllS E F a f) (h2 : AllS E F b g) : AllS E F (a ++ b) (f ++ g) := by
  induction a generalizing f with
  | nil =>
    cases f with
    | nil => simpa using h2
    | cons _ _ => exact absurd h1 (by simp [AllS])
  | cons x l ih =>
    cases f with
    | nil => exact absurd h1 (by simp [AllS])
    | cons y r => exact ⟨h1.1, ih h1.2⟩

theorem AllS.get {a : List (AM Unit)} {f : List (M Unit)} (h : AllS E F a f) (n : Nat) :
    Snd E F TT (a[n]?.getD aJAM) (f[n]?.getD opJAM) := by
  induction a generalizing f n with
  | nil =>
    cases f with
    | nil => simpa using s_JAM
    | cons _ _ => exact absurd h (by simp [AllS])
  | cons x l ih =>
    cases f with
    | nil => exact absurd h (by simp [AllS])
    | cons y r =>
      cases n with
      | zero => simpa using h.1
      | succ n => simpa using ih h.2 n

open PipeTransitionAll (row0 row1 row2 row3 row4 row5 row6 row7 row8 row9 rowA rowB rowC rowD rowE rowF allRows opTable_eq)

theorem s_row0 : AllS E F (arow0 E) row0 := ⟨s_BRK, (s_ORA s_mIzx), s_JAM, (s_SLO s_mIzx), (s_NOPm s_mZp), (s_ORA s_mZp), (s_ASL s_mZp), (s_SLO s_mZp), s_PHP, (s_ORA s_mImm), (s_accOp s_aslV), s_JAM, (s_NOPm s_mAbs), (s_ORA s_mAbs), (s_ASL s_mAbs), (s_SLO s_mAbs), trivial⟩
theorem s_row1 : AllS E F (arow1 E) row1 := ⟨s_BPL, (s_ORA s_mIzyR), s_JAM, (s_SLO s_mIzy), (s_NOPm s_mZpx), (s_ORA s_mZpx), (s_ASL s_mZpx), (s_SLO s_mZpx), s_CLC, (s_ORA s_mAbyR), s_NOP, (s_SLO s_mAby), (s_NOPm s_mAbxR), (s_ORA s_mAbxR), (s_ASL s_mAbx), (s_SLO s_mAbx), trivial⟩
theorem s_row2 : AllS E F (arow2 E) row2 := ⟨s_JSR, (s_AND s_mIzx), s_JAM, (s_RLA s_mIzx), (s_BIT s_mZp), (s_AND s_mZp), (s_ROL s_mZp), (s_RLA s_mZp), s_PLP, (s_AND s_mImm), (s_accOp s_rolV), s_JAM, (s_BIT s_mAbs), (s_AND s_mAbs), (s_ROL s_mAbs), (s_RLA s_mAbs), trivial⟩
theorem s_row3 : AllS E F (arow3 E) row3 := ⟨s_BMI, (s_AND s_mIzyR), s_JAM, (s_RLA s_mIzy), (s_NOPm s_mZpx), (s_AND s_mZpx), (s_ROL s_mZpx), (s_RLA s_mZpx), s_SEC, (s_AND s_mAbyR), s_NOP, (s_RLA s_mAby), (s_NOPm s_mAbxR), (s_AND s_mAbxR), (s_ROL s_mAbx), (s_RLA s_mAbx), trivial⟩
theorem s_row4 : AllS E F (arow4 E) row4 := ⟨s_RTI, (s_EOR s_mIzx), s_JAM, (s_SRE s_mIzx), (s_NOPm s_mZp), (s_EOR s_mZp), (s_LSR s_mZp), (s_SRE s_mZp), s_PHA, (s_EOR s_mImm), (s_accOp s_lsrV), s_JAM, s_JMP, (s_EOR s_mAbs), (s_LSR s_mAbs), (s_SRE s_mAbs), trivial⟩
theorem s_row5 : AllS E F (arow5 E) row5 := ⟨s_BVC, (s_EOR s_mIzyR), s_JAM, (s_SRE s_mIzy), (s_NOPm s_mZpx), (s_EOR s_mZpx), (s_LSR s_mZpx), (s_SRE s_mZpx), s_CLI, (s_EOR s_mAbyR), s_NOP, (s_SRE s_mAby), (s_NOPm s_mAbxR), (s_EOR s_mAbxR), (s_LSR s_mAbx), (s_SRE s_mAbx), trivial⟩
theorem s_row6 : AllS E F (arow6 E) row6 := ⟨s_RTS, (s_ADC s_mIzx), s_JAM, (s_RRA s_mIzx), (s_NOPm s_mZp), (s_ADC s_mZp), (s_ROR s_mZp), (s_RRA s_mZp), s_PLA, (s_ADC s_mImm), (s_accOp s_rorV), s_JAM, s_JMPi, (s_ADC s_mAbs), (s_ROR s_mAbs), (s_RRA s_mAbs), trivial⟩
theorem s_row7 : AllS E F (arow7 E) row7 := ⟨s_BVS, (s_ADC s_mIzyR), s_JAM, (s_RRA s_mIzy), (s_NOPm s_mZpx), (s_ADC s_mZpx), (s_ROR s_mZpx), (s_RRA s_mZpx), s_SEI, (s_ADC s_mAbyR), s_NOP, (s_RRA s_mAby), (s_NOPm s_mAbxR), (s_ADC s_mAbxR), (s_ROR s_mAbx), (s_RRA s_mAbx), trivial⟩
theorem s_row8 : AllS E F (arow8 E) row8 := ⟨(s_NOPm s_mImm), (s_STA s_mIzx), (s_NOPm s_mImm), (s_SAX s_mIzx), (s_STY s_mZp), (s_STA s_mZp), (s_STX s_mZp), (s_SAX s_mZp), s_DEY, (s_NOPm s_mImm), s_TXA, s_JAM, (s_STY s_mAbs), (s_STA s_mAbs), (s_STX s_mAbs), (s_SAX s_mAbs), trivial⟩
theorem s_row9 : AllS E F (arow9 E) row9 := ⟨s_BCC, (s_STA s_mIzy), s_JAM, s_JAM, (s_STY s_mZpx), (s_STA s_mZpx), (s_STX s_mZpy), (s_SAX s_mZpy), s_TYA, (s_STA s_mAby), s_TXS, s_JAM, s_JAM, (s_STA s_mAbx), s_JAM, s_JAM, trivial⟩
theorem s_rowA : AllS E F (arowA E) rowA := ⟨(s_LDY s_mImm), (s_LDA s_mIzx), (s_LDX s_mImm), (s_LAX s_mIzx), (s_LDY s_mZp), (s_LDA s_mZp), (s_LDX s_mZp), (s_LAX s_mZp), s_TAY, (s_LDA s_mImm), s_TAX, s_JAM, (s_LDY s_mAbs), (s_LDA s_mAbs), (s_LDX s_mAbs), (s_LAX s_mAbs), trivial⟩
theorem s_rowB : AllS E F (arowB E) rowB := ⟨s_BCS, (s_LDA s_mIzyR), s_JAM, (s_LAX s_mIzyR), (s_LDY s_mZpx), (s_LDA s_mZpx), (s_LDX s_mZpy), (s_LAX s_mZpy), s_CLV, (s_LDA s_mAbyR), s_TSX, s_JAM, (s_LDY s_mAbxR), (s_LDA s_mAbxR), (s_LDX s_mAbyR), (s_LAX s_mAbyR), trivial⟩
theorem s_rowC : AllS E F (arowC E) rowC := ⟨(s_CPY s_mImm), (s_CMP s_mIzx), (s_NOPm s_mImm), (s_DCP s_mIzx), (s_CPY s_mZp), (s_CMP s_mZp), (s_DEC s_mZp), (s_DCP s_mZp), s_INY, (s_CMP s_mImm), s_DEX, s_JAM, (s_CPY s_mAbs), (s_CMP s_mAbs), (s_DEC s_mAbs), (s_DCP s_mAbs), trivial⟩
theorem s_rowD : AllS E F (arowD E) rowD := ⟨s_BNE, (s_CMP s_mIzyR), s_JAM, (s_DCP s_mIzy), (s_NOPm s_mZpx), (s_CMP s_mZpx), (s_DEC s_mZpx), (s_DCP s_mZpx), s_CLD, (s_CMP s_mAbyR), s_NOP, (s_DCP s_mAby), (s_NOPm s_mAbxR), (s_CMP s_mAbxR), (s_DEC s_mAbx), (s_DCP s_mAbx), trivial⟩
theorem s_rowE : AllS E F (arowE E) rowE := ⟨(s_CPX s_mImm), (s_SBC s_mIzx), (s_NOPm s_mImm), (s_ISB s_mIzx), (s_CPX s_mZp), (s_SBC s_mZp), (s_INC s_mZp), (s_ISB s_mZp), s_INX, (s_SBC s_mImm), s_NOP, (s_SBC s_mImm), (s_CPX s_mAbs), (s_SBC s_mAbs), (s_INC s_mAbs), (s_ISB s_mAbs), trivial⟩
theorem s_rowF : AllS E F (arowF E) rowF := ⟨s_BEQ, (s_SBC s_mIzyR), s_JAM, (s_ISB s_mIzy), (s_NOPm s_mZpx), (s_SBC s_mZpx), (s_INC s_mZpx), (s_ISB s_mZpx), s_SED, (s_SBC s_mAbyR), s_NOP, (s_ISB s_mAby), (s_NOPm s_mAbxR), (s_SBC s_mAbxR), (s_INC s_mAbx), (s_ISB s_mAbx), trivial⟩

theorem s_all : AllS E F (aRows E) allRows :=
  AllS.append s_row0 (AllS.append s_row1 (AllS.append s_row2 (AllS.append s_row3 (AllS.append s_row4 (AllS.append s_row5 (AllS.append s_row6 (AllS.append s_row7 (AllS.append s_row8 (AllS.append s_row9 (AllS.append s_rowA (AllS.append s_rowB (AllS.append s_rowC (AllS.append s_rowD (AllS.append s_rowE s_rowF))))))))))))))

/-- the abstract table follows the table of the CPU -/
theorem s_op (n : Nat) : Snd E F TT ((aRows E).toArray[n]?.getD aJAM) (opTable[n]?.getD opJAM) := by
  rw [opTable_eq, List.getElem?_toArray, List.getElem?_toArray]
  exact s_all.get n

end

/-! ## One step of a machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem tick_adv {A B : AS} {m : Machine} {c : Nat} {u : Unit} (hs : Sim E F A m) (he : atick c c A = some (u, B)) :
    (go (tick c) m).2.fdot = m.fdot + 3 * c := by
  have hlo := hs.lo
  have hhi := hs.hi
  unfold atick at he
  simp only at he
  split at he
  · cases he
  · rename_i hn
    have hn' : ¬ (A.lo < dotVblSet ∨ dotsPerFrame - 1 ≤ A.hi + 3 * c) := by simpa using hn
    have ht := tick_mid c m (by omega) (by omega)
    rw [ht]

/-- the machine and the abstract state after one step -/
def StepRel (A B : AS) (m m' : Machine) : Prop :=
  (B.k = A.k ∧ m'.frame = m.frame ∧ m.fdot + 3 ≤ m'.fdot) ∨ (B.k = A.k + 1 ∧ m'.frame = m.frame + 1)

theorem step_nmi {m : Machine} (hn : m.nmiPending = true) : go step m = go nmi m := by
  unfold step go
  show (if m.nmiPending = true then nmi else _) m = _
  rw [if_pos hn]

theorem fetch_rom {m : Machine} (hp : m.pc ≥ 0x8000) : go fetch m = (m.prg.get! (m.pc &&& m.prgMask).toNat, { m with pc := m.pc + 1 }) := by
  have h1 : ¬ m.pc < 0x2000 := by
    intro h
    have a1 := UInt16.lt_iff_toNat_lt.1 h
    have a2 := UInt16.le_iff_toNat_le.1 hp
    revert a1 a2
    simp
    omega
  have : go fetch m = go (rd m.pc) { m with pc := m.pc + 1 } := rfl
  rw [this, rd_rom _ h1 hp]

/-- the rest of a step, after the opcode -/
def stepK (m : Machine) (pc : UInt16) (op : UInt8) : M Unit :=
  if op == 0x4C && m.prg.get! ((pc + 1) &&& m.prgMask).toNat == pc.toUInt8
      && m.prg.get! ((pc + 2) &&& m.prgMask).toNat == (pc >>> 8).toUInt8 && pc ≥ 0x8000 then
    setPC pc >>= fun _ => tick (cyclesToNextEvent m)
  else
    (opTable[op.toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! op.toNat).toNat

theorem step_op {m : Machine} (hn : m.nmiPending = false) (hh : m.halted = false) (hp : m.pc ≥ 0x8000) :
    go step m = go (stepK m m.pc (m.prg.get! (m.pc &&& m.prgMask).toNat)) { m with pc := m.pc + 1 } := by
  have h1 : go step m = go (fetch >>= fun op => stepK m m.pc op) m := by
    unfold step go
    show (if m.nmiPending = true then nmi else if m.halted = true then _ else _) m = _
    rw [if_neg (by simp [hn]), if_neg (by simp [hh])]
    rfl
  rw [h1]
  have h2 : go (fetch >>= fun op => stepK m m.pc op) m = go (stepK m m.pc (go fetch m).1) (go fetch m).2 := rfl
  rw [h2, fetch_rom hp]

theorem nextEvent_cases (f : Nat) : (f < dotVblSet ∧ nextEvent f = dotVblSet) ∨ (dotVblSet ≤ f ∧ f < dotVblClr ∧ nextEvent f = dotVblClr) ∨
    (dotVblClr ≤ f ∧ f < dotSpr0 ∧ nextEvent f = dotSpr0) ∨ (dotSpr0 ≤ f ∧ nextEvent f = dotsPerFrame) := by
  unfold nextEvent
  by_cases a : f < dotVblSet
  · left
    simp [a]
  · by_cases b : f < dotVblClr
    · right; left
      simp [a, b]
      omega
    · by_cases c : f < dotSpr0
      · right; right; left
        simp [a, b, c]
        omega
      · right; right; right
        simp [a, b, c]
        omega

theorem nextEvent_same {a f : Nat} (h1 : a ≤ f) (h2 : f < nextEvent a) : nextEvent f = nextEvent a := by
  have hv1 := v1
  have hvc := vc
  have hvs := vs
  have hvd := vd
  rcases nextEvent_cases a with ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2⟩ <;>
  rcases nextEvent_cases f with ⟨y1, y2⟩ | ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩ | ⟨y1, y2⟩ <;> omega

theorem cyc_range (m : Machine) (hf : m.fdot < nextEvent m.fdot) :
    nextEvent m.fdot ≤ m.fdot + 3 * cyclesToNextEvent m ∧ m.fdot + 3 * cyclesToNextEvent m ≤ nextEvent m.fdot + 8 := by
  have e : cyclesToNextEvent m = (((nextEvent m.fdot - m.fdot + 2) / 3 + 2) / 3) * 3 := rfl
  rw [e]
  omega

theorem tick_first (c : Nat) (m : Machine) (h1 : m.fdot = 0) (h2 : 1 ≤ c) (h3 : 3 * c ≤ 9) :
    (go (tick c) m).2 = { m with
      cyc := m.cyc + c
      fdot := 3 * c
      vblank := true
      nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) } := by
  have hlen : ∀ n : Machine, 3 * c < PipeTransitionAll.tickLen n := by
    intro n
    unfold PipeTransitionAll.tickLen
    have := vd
    split <;> omega
  have h4 : ∀ (new len : Nat) (n : Machine), new < len → PipeTransitionAll.tick4 new len n = { n with fdot := new } := by
    intro new len n hl
    unfold PipeTransitionAll.tick4
    rw [if_neg (by omega)]
  rw [PipeTransitionAll.tick_eq]
  dsimp only
  rw [h1]
  simp only [Nat.zero_add]
  rw [h4 _ _ _ (hlen _)]
  have a1 : (decide (0 < dotVblSet) && decide (dotVblSet ≤ 3 * c)) = true := by
    simp only [v1]
    simp
    omega
  have a2 : (decide (0 < dotVblClr) && decide (dotVblClr ≤ 3 * c)) = false := by
    have : ¬ dotVblClr ≤ 3 * c := by simp only [vc]; omega
    simp [this]
  have a3 : (decide (0 < dotSpr0) && decide (dotSpr0 ≤ 3 * c)) = false := by
    have : ¬ dotSpr0 ≤ 3 * c := by simp only [vs]; omega
    simp [this]
  rw [a1, a2, a3]
  rfl

theorem tick_wrap (c : Nat) (m : Machine) (h1 : dotSpr0 ≤ m.fdot) (h2 : dotsPerFrame ≤ m.fdot + 3 * c) (h3 : m.fdot + 3 * c ≤ dotsPerFrame + 8) (h4 : m.sprite0 = true) :
    ∃ d, d ≤ 9 ∧ (go (tick c) m).2.fdot = d ∧ (go (tick c) m).2.frame = m.frame + 1 ∧ (go (tick c) m).2.sprite0 = true ∧
      (go (tick c) m).2.a = m.a ∧ (go (tick c) m).2.x = m.x ∧ (go (tick c) m).2.y = m.y ∧ (go (tick c) m).2.p = m.p ∧ (go (tick c) m).2.s = m.s ∧
      (go (tick c) m).2.pc = m.pc ∧ (go (tick c) m).2.ram = m.ram ∧ (go (tick c) m).2.prg = m.prg ∧ (go (tick c) m).2.prgMask = m.prgMask ∧
      (go (tick c) m).2.ppuCtrl = m.ppuCtrl ∧ (go (tick c) m).2.ppuMask = m.ppuMask ∧ (go (tick c) m).2.pad = m.pad ∧
      (go (tick c) m).2.padShift = m.padShift ∧ (go (tick c) m).2.padStrobe = m.padStrobe ∧ (go (tick c) m).2.halted = m.halted ∧ (go (tick c) m).2.trk = m.trk ∧
      (if 1 ≤ d then (go (tick c) m).2.vblank = true ∧ (go (tick c) m).2.nmiPending = (m.nmiPending || (m.ppuCtrl &&& 0x80 != 0))
       else (go (tick c) m).2.vblank = m.vblank ∧ (go (tick c) m).2.nmiPending = m.nmiPending) := by
  have a1 : (decide (m.fdot < dotVblSet) && decide (dotVblSet ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotVblSet := by simp only [vs, v1] at *; omega
    simp [this]
  have a2 : (decide (m.fdot < dotVblClr) && decide (dotVblClr ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotVblClr := by simp only [vs, vc] at *; omega
    simp [this]
  have a3 : (decide (m.fdot < dotSpr0) && decide (dotSpr0 ≤ m.fdot + 3 * c)) = false := by
    have : ¬ m.fdot < dotSpr0 := by omega
    simp [this]
  have e0 : go (tick c) m = ((), PipeTransitionAll.tick4 (m.fdot + 3 * c) (PipeTransitionAll.tickLen { m with cyc := m.cyc + c }) { m with cyc := m.cyc + c }) := by
    rw [PipeTransitionAll.tick_eq]
    dsimp only
    rw [a1, a2, a3]
    rfl
  rw [e0]
  generalize hL : PipeTransitionAll.tickLen { m with cyc := m.cyc + c } = L
  have hL2 : L = dotsPerFrame ∨ L = dotsPerFrame - 1 := by
    rw [← hL]
    unfold PipeTransitionAll.tickLen
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hv := vd
  have hge : L ≤ m.fdot + 3 * c := by omega
  by_cases hd : dotVblSet ≤ m.fdot + 3 * c - L
  · have e1 : PipeTransitionAll.tick4 (m.fdot + 3 * c) L { m with cyc := m.cyc + c } = { m with
        cyc := m.cyc + c
        frame := m.frame + 1
        fdot := m.fdot + 3 * c - L
        vblank := true
        nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) } := by
      unfold PipeTransitionAll.tick4
      rw [if_pos hge, if_pos hd]
    rw [e1]
    have hd2 : 1 ≤ m.fdot + 3 * c - L := hd
    refine ⟨m.fdot + 3 * c - L, by omega, rfl, rfl, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [if_pos hd2]
    exact ⟨rfl, rfl⟩
  · have e1 : PipeTransitionAll.tick4 (m.fdot + 3 * c) L { m with cyc := m.cyc + c } = { m with
        cyc := m.cyc + c
        frame := m.frame + 1
        fdot := m.fdot + 3 * c - L } := by
      unfold PipeTransitionAll.tick4
      rw [if_pos hge, if_neg hd]
    rw [e1]
    have hd2 : ¬ 1 ≤ m.fdot + 3 * c - L := hd
    refine ⟨m.fdot + 3 * c - L, by omega, rfl, rfl, h4, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [if_neg hd2]
    exact ⟨rfl, rfl⟩

theorem s0f_small {d : Nat} (h : d ≤ 9) : s0f d = true := by
  have : d < dotVblClr := by simp only [vc]; omega
  simp [s0f, this]

/-- the idle loop -/
theorem s_idle {A : AS} {m : Machine} (hs : Sim E F A m) :
    ∃ r ∈ aidle A, ∀ B, r = some B → Sim E F B (go (tick (cyclesToNextEvent m)) m).2 ∧ StepRel A B m (go (tick (cyclesToNextEvent m)) m).2 := by
  have hlo := hs.lo
  have hhi := hs.hi
  have hlim := hs.lim
  unfold aidle
  simp only
  by_cases h0 : nextEvent A.lo ≤ A.hi
  · rw [if_pos h0]
    exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  rw [if_neg h0]
  have hsame : nextEvent m.fdot = nextEvent A.lo := nextEvent_same hlo (by omega)
  have hf : m.fdot < nextEvent m.fdot := by omega
  obtain ⟨c1, c2⟩ := cyc_range m hf
  rw [hsame] at c1 c2
  generalize hc : cyclesToNextEvent m = c at c1 c2 ⊢
  have hv1 := v1
  have hvc := vc
  have hvs := vs
  have hvd := vd
  by_cases h1 : (nextEvent A.lo == dotVblSet) = true
  · rw [if_pos h1]
    have h1' : nextEvent A.lo = dotVblSet := by simpa using h1
    have hA : A.lo < dotVblSet := by
      rcases nextEvent_cases A.lo with ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2⟩ <;> omega
    have hd0 : m.fdot = 0 := by omega
    have hb := TR_bit 0x80 hs.ppuCtrl
    cases e : A.ppuCtrl.bit 0x80 with
    | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
    | some b =>
      rw [e] at hb
      have hb' : b = (m.ppuCtrl &&& 0x80 != 0) := by
        rcases hb with t | t
        · cases t
        · exact Option.some.inj t
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      rw [h1'] at c1 c2 ⊢
      have hc3 : 1 ≤ c := by omega
      have hc4 : 3 * c ≤ 9 := by omega
      rw [tick_first c m hd0 hc3 hc4]
      refine ⟨{ hs with
        vb := rfl
        nmi := ?_
        s0 := ?_
        lo := ?_
        hi := ?_
        lim := ?_ }, Or.inl ⟨rfl, rfl, ?_⟩⟩
      · show (m.nmiPending || (m.ppuCtrl &&& 0x80 != 0)) = (A.nmi || b)
        rw [hs.nmi, hb']
      · show m.sprite0 = s0f (3 * c)
        rw [hs.s0, hd0, s0f_small (by omega), s0f_small (by omega)]
      · show dotVblSet ≤ 3 * c
        omega
      · show 3 * c ≤ dotVblSet + 8
        omega
      · show dotVblSet + 8 < dotsPerFrame
        omega
      · show m.fdot + 3 ≤ 3 * c
        omega
  rw [if_neg h1]
  by_cases h2 : (nextEvent A.lo == dotVblClr) = true
  · rw [if_pos h2]
    have h2' : nextEvent A.lo = dotVblClr := by simpa using h2
    have hA : dotVblSet ≤ A.lo ∧ A.lo < dotVblClr := by
      rcases nextEvent_cases A.lo with ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2⟩ <;> omega
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    obtain rfl := Option.some.inj hB
    rw [h2'] at c1 c2 ⊢
    have ht := tick_mid c m (by omega) (by omega)
    rw [ht]
    have hcr : m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c := ⟨by omega, c1⟩
    refine ⟨{ hs with
      vb := ?_
      s0 := ?_
      lo := ?_
      hi := ?_
      lim := ?_ }, Or.inl ⟨rfl, rfl, ?_⟩⟩
    · show (if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank) = false
      rw [if_pos hcr]
    · exact s0f_step _ _ (by omega) _ hs.s0
    · show dotVblClr ≤ m.fdot + 3 * c
      omega
    · show m.fdot + 3 * c ≤ dotVblClr + 8
      omega
    · show dotVblClr + 8 < dotsPerFrame
      omega
    · show m.fdot + 3 ≤ m.fdot + 3 * c
      omega
  rw [if_neg h2]
  by_cases h3 : (nextEvent A.lo == dotSpr0) = true
  · rw [if_pos h3]
    have h3' : nextEvent A.lo = dotSpr0 := by simpa using h3
    have hA : dotVblClr ≤ A.lo ∧ A.lo < dotSpr0 := by
      rcases nextEvent_cases A.lo with ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2⟩ <;> omega
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    obtain rfl := Option.some.inj hB
    rw [h3'] at c1 c2 ⊢
    have ht := tick_mid c m (by omega) (by omega)
    rw [ht]
    have hcr : ¬ (m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c) := by omega
    refine ⟨{ hs with
      vb := ?_
      s0 := ?_
      lo := ?_
      hi := ?_
      lim := ?_ }, Or.inl ⟨rfl, rfl, ?_⟩⟩
    · show (if m.fdot < dotVblClr ∧ dotVblClr ≤ m.fdot + 3 * c then false else m.vblank) = A.vb
      rw [if_neg hcr]
      exact hs.vb
    · exact s0f_step _ _ (by omega) _ hs.s0
    · show dotSpr0 ≤ m.fdot + 3 * c
      omega
    · show m.fdot + 3 * c ≤ dotSpr0 + 8
      omega
    · show dotSpr0 + 8 < dotsPerFrame
      omega
    · show m.fdot + 3 ≤ m.fdot + 3 * c
      omega
  rw [if_neg h3]
  have h1' : nextEvent A.lo ≠ dotVblSet := by simpa using h1
  have h2' : nextEvent A.lo ≠ dotVblClr := by simpa using h2
  have h3' : nextEvent A.lo ≠ dotSpr0 := by simpa using h3
  have h4 : nextEvent A.lo = dotsPerFrame ∧ dotSpr0 ≤ A.lo := by
    rcases nextEvent_cases A.lo with ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2⟩
    · exact absurd x2 h1'
    · exact absurd x3 h2'
    · exact absurd x3 h3'
    · exact ⟨x2, x1⟩
  have hA := h4.2
  replace h4 := h4.1
  rw [h4] at c1 c2
  have hb := TR_bit 0x80 hs.ppuCtrl
  have hs0 : m.sprite0 = true := by
    rw [hs.s0]
    have : dotSpr0 ≤ m.fdot := by omega
    simp [s0f, this]
  obtain ⟨d, hd9, f1, f2, f3, fa, fx, fy, fp, fs, fpc, fram, fprg, fmask, fctrl, fmask2, fpad, fps, fstr, fh, ftrk, fv⟩ := tick_wrap c m (by omega) c1 c2 hs0
  cases e : A.ppuCtrl.bit 0x80 with
  | none => exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
  | some b =>
    rw [e] at hb
    have hb' : b = (m.ppuCtrl &&& 0x80 != 0) := by
      rcases hb with t | t
      · cases t
      · exact Option.some.inj t
    generalize hm' : (go (tick c) m).2 = m' at f1 f2 f3 fa fx fy fp fs fpc fram fprg fmask fctrl fmask2 fpad fps fstr fh ftrk fv ⊢
    have common : ∀ B : AS, B.a = A.a → B.x = A.x → B.y = A.y → B.p = A.p → B.s = A.s → B.pc = A.pc → B.ppuCtrl = A.ppuCtrl → B.ppuMask = A.ppuMask →
        B.padShift = A.padShift → B.strobe = A.strobe → B.ram = A.ram → B.kn = A.kn → B.dg = A.dg → B.lo ≤ d → d ≤ B.hi → B.hi < dotsPerFrame →
        m'.vblank = B.vb → m'.nmiPending = B.nmi → B.k = A.k + 1 → B.rk = A.rk → B.spent = A.spent → Sim E F B m' := by
      intro B b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 l1 l2 l3 l4 l5 l6 l7 l8
      have hk : ∀ i, B.getK i = A.getK i := by
        intro i
        simp only [AS.getK, b11, b12]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, l4, l5, ?_, ?_, ?_, l3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [fa, b1]; exact hs.a
      · rw [fx, b2]; exact hs.x
      · rw [fy, b3]; exact hs.y
      · rw [fp, b4]; exact hs.p
      · rw [fs, b5]; exact hs.s
      · rw [fpc, b6]; exact hs.pc
      · rw [fprg]; exact hs.prg
      · rw [fmask]; exact hs.mask
      · rw [fctrl, b7]; exact hs.ppuCtrl
      · rw [fmask2, b8]; exact hs.ppuMask
      · rw [f3, f1, s0f_small hd9]
      · rw [f1]; exact l1
      · rw [f1]; exact l2
      · rw [fpad]; exact hs.pad
      · rw [fps, b9]; exact hs.padShift
      · rw [fstr, b10]; exact hs.strobe
      · rw [fh]; exact hs.halted
      · rw [ftrk]; exact hs.trk
      · rw [fram]; exact hs.size
      · intro i hi
        rw [hk, fram]
        exact hs.ram i hi
      · intro hg
        rw [b13] at hg
        rw [fram]
        exact hs.dg hg
      · rw [b11]; exact hs.szR
      · rw [b12]; exact hs.szK
      · rw [f2, l6, hs.fr]; omega
      · intro hr
        rw [fram, l8]
        exact hs.rkv (l7 ▸ hr)
    by_cases hd1 : 1 ≤ d
    · rw [if_pos hd1] at fv
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      refine ⟨common _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd1 hd9 ?_ fv.1 ?_ rfl rfl rfl, Or.inr ⟨rfl, f2⟩⟩
      · show 9 < dotsPerFrame
        omega
      · rw [fv.2, hs.nmi, hb']
    · rw [if_neg hd1] at fv
      refine ⟨_, List.mem_cons_self, fun B hB => ?_⟩
      obtain rfl := Option.some.inj hB
      refine ⟨common _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.zero_le _) (by show d ≤ 0; omega) ?_ ?_ ?_ rfl rfl rfl, Or.inr ⟨rfl, f2⟩⟩
      · show 0 < dotsPerFrame
        omega
      · rw [fv.1]; exact hs.vb
      · rw [fv.2]; exact hs.nmi

/-- an action and then `tick c`: the dot goes on by `3 c` -/
theorem snd_then_tick {af : AM Unit} {f : M Unit} {c : Nat} (h : Snd E F TT af f) {A B : AS} {m : Machine} {u : Unit} (hs : Sim E F A m)
    (he : (af >>= fun _ => atick c c) A = some (u, B)) :
    Sim E F B (go (f >>= fun _ => tick c) m).2 ∧ (go (f >>= fun _ => tick c) m).2.frame = m.frame ∧ m.fdot + 3 * c ≤ (go (f >>= fun _ => tick c) m).2.fdot := by
  obtain ⟨v, A2, h3, h4⟩ := abind_some he
  obtain ⟨_, h5, h6⟩ := h A m hs _ _ h3
  obtain ⟨_, h7, h8⟩ := s_tick (E := E) (F := F) (Nat.le_refl c) (Nat.le_refl c) A2 _ h5 _ _ h4
  have h9 := tick_adv h5 h4
  have e := PipeTransitionAll.go_bind (f := f) (g := fun _ => tick c) m
  rw [e]
  refine ⟨h7, h8.1.trans h6.1, ?_⟩
  rw [h9]
  have := h6.2
  omega

theorem steprel_same {A B : AS} {m m' : Machine} (h1 : Sim E F A m) (h2 : Sim E F B m') (hf : m'.frame = m.frame) (hd : m.fdot + 3 ≤ m'.fdot) : StepRel A B m m' := by
  have a1 := h1.fr
  have a2 := h2.fr
  exact Or.inl ⟨by omega, hf, hd⟩

theorem go_dec {m : Machine} {ad : UInt16} (h1 : ad < 0x2000) (ht : m.trk = false) :
    go (rd ad >>= fun v => decV v >>= fun r => wr ad r) m = ((), { m with
      p := (m.p &&& 0x7D) ||| (if (m.ram.get! (ad &&& 0x7FF).toNat - 1) == 0 then 0x02 else 0) ||| ((m.ram.get! (ad &&& 0x7FF).toNat - 1) &&& 0x80)
      ram := m.ram.set! (ad &&& 0x7FF).toNat (m.ram.get! (ad &&& 0x7FF).toNat - 1) }) := by
  rw [PipeTransitionAll.go_bind, rd_ram h1 ht]
  exact wr_ram (m := { m with p := (m.p &&& 0x7D) ||| (if (m.ram.get! (ad &&& 0x7FF).toNat - 1) == 0 then 0x02 else 0) ||| ((m.ram.get! (ad &&& 0x7FF).toNat - 1) &&& 0x80) }) _ h1 ht

theorem u8_sub_one {T : UInt8} (h : 2 ≤ T.toNat) : (T - 1).toNat = T.toNat - 1 := by
  rw [UInt8.toNat_sub]
  have h1 : (1 : UInt8).toNat = 1 := rfl
  rw [h1]
  have := UInt8.toNat_lt T
  show (256 - 1 + T.toNat) % 256 = _
  omega

open PipeTransitionAll (mask_lt ba_size_set ba_get_set_self ba_get_set_ne) in
/-- `DEC abs` of the counter -/
theorem s_rkOp (hT : 2 ≤ F.2.toNat) : Snd E F TT (arkOp E) (opDEC mAbs) := by
  refine Snd.congr (g := fetch16 >>= fun ad => rd ad >>= fun v => decV v >>= fun r => wr ad r) (fun _ => rfl) ?_
  refine Snd.bind s_fetch16 fun ad ad2 h => ?_
  subst h
  refine snd_leaf fun A m hs a A' he => ?_
  have he2 : (if A.rk && !A.spent && decide (ad < 0x2000) && (ad &&& 0x7FF).toNat == E.rkI then
      some ((), { A.setK E.rkI AB.top with spent := true, dg := A.dg && !E.D.contains E.rkI, p := rkFlags A.p }) else none) = some (a, A') := he
  split at he2
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := some_pair he2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨hr, hsp⟩, h1⟩, hi⟩ := hc
    rw [go_dec h1 hs.trk]
    have hlt : E.rkI < 2048 := by
      rw [← hi]
      exact mask_lt ad
    have hv : m.ram.get! (ad &&& 0x7FF).toNat = F.2 := by
      rw [hi, hs.rkv hr, hsp]
      rfl
    rw [hv, hi]
    have hne : (F.2 - 1) ≠ 0 := by
      intro h0
      have := u8_sub_one hT
      rw [h0] at this
      have h00 : (0 : UInt8).toNat = 0 := rfl
      omega
    refine ⟨trivial, { hs with
      p := ?_
      size := by show (m.ram.set! E.rkI (F.2 - 1)).size = 2048; rw [ba_size_set]; exact hs.size
      szR := by show (A.ram.set! E.rkI AB.top.v).size = 2048; rw [ba_size_set]; exact hs.szR
      szK := by show (A.kn.set! E.rkI AB.top.k).size = 2048; rw [ba_size_set]; exact hs.szK
      ram := ?_
      dg := ?_
      rkv := ?_ }, rfl, rfl⟩
    · have e0 : ((F.2 - 1) == 0) = false := beq_eq_false_iff_ne.2 hne
      simp only [e0]
      exact mem_or (mem_or (mem_and hs.p (mem_known_self _)) (mem_ite (TR_some false) 0x02 0)) (mem_and (mem_top _) (mem_known_self _))
    · intro j hj
      show AB.mem ⟨(A.ram.set! E.rkI AB.top.v).get! j, (A.kn.set! E.rkI AB.top.k).get! j⟩ ((m.ram.set! E.rkI (F.2 - 1)).get! j)
      by_cases hij : E.rkI = j
      · subst hij
        rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hj), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hj)]
        exact mem_top _
      · rw [ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij, ba_get_set_ne _ _ _ _ hij]
        exact hs.ram j hj
    · intro hg
      have hg' : A.dg = true ∧ E.D.contains E.rkI = false := by simpa using hg
      have hany := hs.dg hg'.1
      obtain ⟨d, hd, hd2⟩ := List.any_eq_true.1 hany
      refine List.any_eq_true.2 ⟨d, hd, ?_⟩
      have hne2 : E.rkI ≠ d := by
        intro he3
        subst he3
        have : E.D.contains E.rkI = true := by simpa using hd
        rw [this] at hg'
        simp at hg'
      show ((m.ram.set! E.rkI (F.2 - 1)).get! d != 0) = true
      rw [ba_get_set_ne _ _ _ _ hne2]
      exact hd2
    · intro _
      show (m.ram.set! E.rkI (F.2 - 1)).get! E.rkI = (if true = true then F.2 - 1 else F.2)
      rw [ba_get_set_self _ _ _ (by rw [hs.size]; exact hlt)]
      rfl
  · cases he2

set_option maxRecDepth 100000 in
theorem op_CE : opTable[(0xCE : UInt8).toNat]?.getD opJAM = opDEC mAbs := by
  rw [PipeTransitionAll.opTable_eq]
  rfl

set_option maxRecDepth 100000 in
theorem cyc_CE : (cycTable.get! (0xCE : UInt8).toNat).toNat = 6 := by decide

/-- a step of the machine is followed by a step of the abstract machine -/
theorem s_astep1 {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hs : Sim E F A m) :
    ∃ r ∈ astep1 E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold astep1
  by_cases hn : A.nmi = true
  · rw [if_pos hn]
    refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
    have hmn : m.nmiPending = true := by rw [hs.nmi]; exact hn
    rw [step_nmi hmn]
    cases he : (anmi E) A with
    | none =>
      rw [he] at hB
      cases hB
    | some p =>
      rw [he] at hB
      obtain ⟨u, B1⟩ := p
      have hB1 : B1 = B := Option.some.inj hB
      subst hB1
      have h2 : (ainterrupt E A.pc ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)) 0xFFFA >>= fun _ => atick 7 7) { A with nmi := false } = some (u, B1) := he
      have hc : go nmi m = go (interrupt A.pc ((m.p &&& 0xEF) ||| 0x20) 0xFFFA >>= fun _ => tick 7) { m with nmiPending := false } := by
        rw [← hs.pc]
        rfl
      have hs1 : Sim E F { A with nmi := false } { m with nmiPending := false } := { hs with nmi := rfl }
      have hv : ((A.p.and (AB.known 0xEF)).or (AB.known 0x20)).mem ((m.p &&& 0xEF) ||| 0x20) :=
        mem_or (mem_and hs.p (mem_known_self _)) (mem_known_self _)
      obtain ⟨g1, g2, g3⟩ := snd_then_tick (s_interrupt A.pc hv 0xFFFA) hs1 h2
      rw [hc]
      refine ⟨g1, steprel_same hs g1 g2 ?_⟩
      have : m.fdot + 3 * 7 ≤ _ := g3
      omega
  · rw [if_neg hn]
    have hn2 : m.nmiPending = false := by
      rw [hs.nmi]
      simpa using hn
    by_cases hp : 0x8000 ≤ A.pc
    · rw [if_pos hp]
      have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
      rw [step_op hn2 hs.halted hpm]
      have hop : m.prg.get! (m.pc &&& m.prgMask).toNat = E.prg.get! (A.pc &&& E.mask).toNat := by
        rw [hs.prg, hs.mask, hs.pc]
      rw [hop]
      simp only
      generalize E.prg.get! (A.pc &&& E.mask).toNat = op
      have hidle : (op == 0x4C && m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat == m.pc.toUInt8
          && m.prg.get! ((m.pc + 2) &&& m.prgMask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = isIdle E A.pc op := by
        simp only [isIdle, hs.prg, hs.mask, hs.pc]
      unfold stepK
      simp only [hidle]
      by_cases hi : isIdle E A.pc op = true
      · rw [if_pos hi, if_pos hi]
        have e1 := PipeTransitionAll.go_bind (f := setPC m.pc) (g := fun _ => tick (cyclesToNextEvent m)) { m with pc := m.pc + 1 }
        have e2 : (go (setPC m.pc) { m with pc := m.pc + 1 }).2 = m := rfl
        rw [e1, e2]
        exact s_idle hs
      · rw [if_neg hi, if_neg hi]
        by_cases hd : (A.rk && isRkDec E A.pc op) = true
        · rw [if_pos hd]
          refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
          have hop : op = 0xCE := by
            simp only [isRkDec, Bool.and_eq_true, beq_iff_eq] at hd
            exact hd.2.1.1
          subst hop
          cases he : (arkOp E >>= fun _ => atick 6 6) { A with pc := A.pc + 1 } with
          | none =>
            rw [he] at hB
            cases hB
          | some p =>
            rw [he] at hB
            obtain ⟨u, B1⟩ := p
            have hB1 : B1 = B := Option.some.inj hB
            subst hB1
            have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
              pc := by
                show m.pc + 1 = A.pc + 1
                rw [hs.pc] }
            rw [op_CE, cyc_CE]
            obtain ⟨g1, g2, g3⟩ := snd_then_tick (s_rkOp hT) hs1 he
            refine ⟨g1, steprel_same hs g1 g2 ?_⟩
            have g3' : m.fdot + 3 * 6 ≤ (go (opDEC mAbs >>= fun _ => tick 6) { m with pc := m.pc + 1 }).2.fdot := g3
            omega
        rw [if_neg hd]
        by_cases hc : (cycOf op == 0) = true
        · rw [if_pos hc]
          exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩
        · rw [if_neg hc]
          refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
          have hc1 : 1 ≤ cycOf op := by
            have : cycOf op ≠ 0 := by simpa using hc
            omega
          cases he : (ops[op.toNat]?.getD aJAM >>= fun _ => atick (cycOf op) (cycOf op)) { A with pc := A.pc + 1 } with
          | none =>
            rw [he] at hB
            cases hB
          | some p =>
            rw [he] at hB
            obtain ⟨u, B1⟩ := p
            have hB1 : B1 = B := Option.some.inj hB
            subst hB1
            have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
              pc := by
                show m.pc + 1 = A.pc + 1
                rw [hs.pc] }
            rw [hops] at he
            have hso := s_op (E := E) (F := F) op.toNat
            have ee : (cycTable.get! op.toNat).toNat = cycOf op := rfl
            rw [ee]
            generalize (opTable[op.toNat]?.getD opJAM) = fop at hso ⊢
            generalize (aRows E).toArray[op.toNat]?.getD aJAM = aop at hso he
            generalize cycOf op = cc at he hc1 ⊢
            obtain ⟨g1, g2, g3⟩ := snd_then_tick hso hs1 he
            refine ⟨g1, steprel_same hs g1 g2 ?_⟩
            have g3' : m.fdot + 3 * cc ≤ (go (fop >>= fun _ => tick cc) { m with pc := m.pc + 1 }).2.fdot := g3
            omega
    · rw [if_neg hp]
      exact ⟨none, List.mem_singleton.2 rfl, fun B hB => by cases hB⟩

end

/-! ## Pieces -/

section
variable {E : Env} {F : Nat × UInt8}

open PipeTransitionAll (ba_size_set ba_get_set_self ba_get_set_ne)

/-- every machine of a state is in one of its pieces -/
def Cov (E : Env) (F : Nat × UInt8) (f : AS → List AS) : Prop := ∀ A m, Sim E F A m → ∃ B ∈ f A, Sim E F B m ∧ B.k = A.k

theorem cov_flat {f : AS → List AS} (hf : Cov E F f) {l : List AS} {m : Machine} {k : Nat} (h : ∃ B ∈ l, Sim E F B m ∧ B.k = k) :
    ∃ B ∈ l.flatMap f, Sim E F B m ∧ B.k = k := by
  obtain ⟨B, hB, h1, h2⟩ := h
  obtain ⟨D, hD, h3, h4⟩ := hf B m h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h3, h4.trans h2⟩

theorem cov_dot (e : Nat) : Cov E F (splitDot e) := by
  intro A m hs
  unfold splitDot
  by_cases h : (decide (A.lo < e) && decide (e ≤ A.hi)) = true
  · rw [if_pos h]
    have h' : A.lo < e ∧ e ≤ A.hi := by simpa using h
    have hl := hs.lim
    by_cases hd : m.fdot < e
    · refine ⟨_, List.mem_cons_self, { hs with
        hi := ?_
        lim := ?_ }, rfl⟩
      · show m.fdot ≤ e - 1
        omega
      · show e - 1 < dotsPerFrame
        omega
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with
        lo := ?_ }, rfl⟩
      show e ≤ m.fdot
      omega
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem or_self_of {x mask : UInt8} {j : Nat} (hb : ∀ i, i < 8 → bt mask i = decide (i = j)) (h : bt x j = true) : x ||| mask = x := by
  apply bt_ext
  intro i hi
  simp only [bt_or, hb i hi]
  by_cases hij : i = j
  · subst hij
    simp [h]
  · simp [hij]

theorem bit_of_ne {x mask : UInt8} {j : Nat} (hb : ∀ i, i < 8 → bt mask i = decide (i = j)) (h : x &&& mask ≠ 0) : bt x j = true := by
  cases hx : bt x j with
  | true => rfl
  | false =>
    exfalso
    apply h
    apply bt_ext
    intro i hi
    simp only [bt_and, hb i hi, bt_zero hi]
    by_cases hij : i = j
    · subst hij
      simp [hx]
    · simp [hij]

theorem and_not_self_of {x mask : UInt8} (h : x &&& mask = 0) : x &&& ~~~mask = x := by
  apply bt_ext
  intro i hi
  have a1 := bt_eq h i
  simp only [bt_and, bt_zero hi] at a1
  simp only [bt_and, bt_not _ _ hi]
  revert a1
  generalize bt x i = p, bt mask i = q
  revert p q
  decide

theorem cov_flag {mask : UInt8} {j : Nat} (hb : ∀ i, i < 8 → bt mask i = decide (i = j)) : Cov E F (splitFlag mask) := by
  intro A m hs
  unfold splitFlag
  cases e : A.p.bit mask with
  | some b =>
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    by_cases hx : m.p &&& mask = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), { hs with p := ?_ }, rfl⟩
      have := mem_and hs.p (mem_known_self (~~~mask))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, { hs with p := ?_ }, rfl⟩
      have := mem_or hs.p (mem_known_self mask)
      rwa [or_self_of hb (bit_of_ne hb hx)] at this

theorem bits_80 : ∀ i : Fin 8, bt 0x80 i.1 = decide (i.1 = 7) := by decide
theorem bits_40 : ∀ i : Fin 8, bt 0x40 i.1 = decide (i.1 = 6) := by decide
theorem bits_01 : ∀ i : Fin 8, bt 0x01 i.1 = decide (i.1 = 0) := by decide
theorem bits_02 : ∀ i : Fin 8, bt 0x02 i.1 = decide (i.1 = 1) := by decide

theorem bit_list : ∀ j : Fin 8, ∃ b ∈ bitList, ∀ i : Fin 8, bt b i.1 = decide (i.1 = j.1) := by decide

theorem cov_dg : Cov E F (splitDg E) := by
  intro A m hs
  unfold splitDg
  cases hd : A.dg with
  | false => exact ⟨A, by simp, hs, rfl⟩
  | true =>
    simp only [if_true]
    obtain ⟨d, hdm, hx⟩ := List.any_eq_true.1 (hs.dg hd)
    have hx0 : m.ram.get! d ≠ 0 := by simpa using hx
    have hj : ∃ j, j < 8 ∧ bt (m.ram.get! d) j = true := by
      apply Classical.byContradiction
      intro hno
      apply hx0
      apply bt_ext
      intro i hi
      rw [bt_zero hi]
      cases hc : bt (m.ram.get! d) i with
      | true => exact absurd ⟨i, hi, hc⟩ hno
      | false => rfl
    obtain ⟨j, hj8, hjb⟩ := hj
    obtain ⟨b, hbm, hbb⟩ := bit_list ⟨j, hj8⟩
    have hbb' : ∀ i, i < 8 → bt b i = decide (i = j) := fun i hi => hbb ⟨i, hi⟩
    refine ⟨_, List.mem_flatMap.2 ⟨d, hdm, List.mem_map.2 ⟨b, hbm, rfl⟩⟩, { hs with
      ram := ?_
      szR := ?_
      szK := ?_ }, rfl⟩
    · intro i hi
      show AB.mem ⟨(A.ram.set! d ((A.getK d).or (AB.known b)).v).get! i, (A.kn.set! d ((A.getK d).or (AB.known b)).k).get! i⟩ (m.ram.get! i)
      by_cases hdi : d = i
      · subst hdi
        rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi)]
        have := mem_or (hs.ram d hi) (mem_known_self b)
        rwa [or_self_of hbb' hjb] at this
      · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
        exact hs.ram i hi
    · show (A.ram.set! d _).size = 2048
      rw [ba_size_set]
      exact hs.szR
    · show (A.kn.set! d _).size = 2048
      rw [ba_size_set]
      exact hs.szK

theorem bit_of_list : ∀ b ∈ bitList, ∃ j : Fin 8, ∀ i : Fin 8, bt b i.1 = decide (i.1 = j.1) := by decide

theorem cov_bit {d : Nat} {b : UInt8} (hd : d < 2048) (hb : b ∈ bitList) : Cov E F (splitBit d b) := by
  intro A m hs
  unfold splitBit
  cases e : (A.getK d).bit b with
  | some x => exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  | none =>
    simp only
    obtain ⟨j, hj⟩ := bit_of_list b hb
    have hbb : ∀ i, i < 8 → bt b i = decide (i = j.1) := fun i hi => hj ⟨i, hi⟩
    have base : ∀ v : AB, v.mem (m.ram.get! d) → Sim E F (A.setK d v) m := by
      intro v hv
      refine { hs with
        ram := ?_
        szR := ?_
        szK := ?_ }
      · intro i hi
        show AB.mem ⟨(A.ram.set! d v.v).get! i, (A.kn.set! d v.k).get! i⟩ (m.ram.get! i)
        by_cases hdi : d = i
        · subst hdi
          rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hi), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hi)]
          exact hv
        · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
          exact hs.ram i hi
      · show (A.ram.set! d _).size = 2048
        rw [ba_size_set]
        exact hs.szR
      · show (A.kn.set! d _).size = 2048
        rw [ba_size_set]
        exact hs.szK
    by_cases hx : m.ram.get! d &&& b = 0
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), base _ ?_, rfl⟩
      have := mem_and (hs.ram d hd) (mem_known_self (~~~b))
      rwa [and_not_self_of hx] at this
    · refine ⟨_, List.mem_cons_self, base _ ?_, rfl⟩
      have := mem_or (hs.ram d hd) (mem_known_self b)
      rwa [or_self_of hbb (bit_of_ne hbb hx)] at this

theorem cov_read (op : UInt8) : Cov E F (fun A => splitRead E A op) := by
  intro A m hs
  show ∃ B ∈ splitRead E A op, Sim E F B m ∧ B.k = A.k
  unfold splitRead
  split
  · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · rename_i d _
    split
    · exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
    · rename_i p _
      by_cases hd : d < 2048
      · rw [if_pos hd]
        have key : ∀ (L : List UInt8) (l : List AS), (∀ b ∈ L, b ∈ bitList) → (∃ B ∈ l, Sim E F B m ∧ B.k = A.k) →
            ∃ B ∈ L.foldl (fun l b => l.flatMap (splitBit d b)) l, Sim E F B m ∧ B.k = A.k := by
          intro L
          induction L with
          | nil => exact fun l _ h => h
          | cons b L ih =>
            intro l hL h
            exact ih _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (cov_flat (cov_bit hd (hL b List.mem_cons_self)) h)
        exact key _ _ (fun x hx => (List.mem_filter.1 hx).1) ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
      · rw [if_neg hd]
        exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩

theorem branchMask_cases (op : UInt8) : branchMask op = 0 ∨ branchMask op = 0x80 ∨ branchMask op = 0x40 ∨ branchMask op = 0x01 ∨ branchMask op = 0x02 := by
  unfold branchMask
  split <;> simp

theorem cov_pieces : Cov E F (pieces E) := by
  intro A m hs
  unfold pieces
  by_cases h : (A.nmi || decide (A.pc < 0x8000)) = true
  · rw [if_pos h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · rw [if_neg h]
    simp only
    generalize E.prg.get! (A.pc &&& E.mask).toNat = op
    have h1 : ∃ B ∈ (if readsDg E A.pc op then splitDg E A else splitRead E A op), Sim E F B m ∧ B.k = A.k := by
      split
      · exact cov_dg A m hs
      · exact cov_read op A m hs
    generalize (if readsDg E A.pc op then splitDg E A else splitRead E A op) = l1 at h1
    have h2 : ∃ B ∈ (if readsPPU E A.pc op || isIdle E A.pc op then
        ((l1.flatMap (splitDot dotVblSet)).flatMap (splitDot dotVblClr)).flatMap (splitDot dotSpr0) else l1), Sim E F B m ∧ B.k = A.k := by
      split
      · exact cov_flat (cov_dot _) (cov_flat (cov_dot _) (cov_flat (cov_dot _) h1))
      · exact h1
    generalize (if readsPPU E A.pc op || isIdle E A.pc op then
        ((l1.flatMap (splitDot dotVblSet)).flatMap (splitDot dotVblClr)).flatMap (splitDot dotSpr0) else l1) = l2 at h2
    by_cases h3 : (branchMask op != 0) = true
    · rw [if_pos h3]
      have h3' : branchMask op ≠ 0 := by simpa using h3
      rcases branchMask_cases op with e | e | e | e | e
      · exact absurd e h3'
      · rw [e]
        exact cov_flat (cov_flag (j := 7) fun i hi => bits_80 ⟨i, hi⟩) h2
      · rw [e]
        exact cov_flat (cov_flag (j := 6) fun i hi => bits_40 ⟨i, hi⟩) h2
      · rw [e]
        exact cov_flat (cov_flag (j := 0) fun i hi => bits_01 ⟨i, hi⟩) h2
      · rw [e]
        exact cov_flat (cov_flag (j := 1) fun i hi => bits_02 ⟨i, hi⟩) h2
    · rw [if_neg h3]
      exact h2

/-- a step of the machine, with the pieces -/
theorem s_succs {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hs : Sim E F A m) :
    ∃ r ∈ succs E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  obtain ⟨P, hP, h1, h2⟩ := cov_pieces A m hs
  obtain ⟨r, hr, h3⟩ := s_astep1 hops hT h1
  refine ⟨r, List.mem_flatMap.2 ⟨P, hP, hr⟩, fun B hB => ?_⟩
  obtain ⟨h4, h5⟩ := h3 B hB
  refine ⟨h4, ?_⟩
  unfold StepRel at h5 ⊢
  rw [h2] at h5
  exact h5

/-! ## Order and control -/

theorem ramLeFrom_spec {a b : AS} : ∀ (n i : Nat), ramLeFrom a b n i = true → ∀ j, i ≤ j → j < i + n → (a.getK j).le (b.getK j) = true := by
  intro n
  induction n with
  | zero =>
    intro i _ j h1 h2
    omega
  | succ n ih =>
    intro i h j h1 h2
    simp only [ramLeFrom, Bool.and_eq_true] at h
    by_cases hj : j = i
    · subst hj
      exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

theorem sim_le {B D : AS} {m : Machine} (h : B.le D = true) (hs : Sim E F B m) : Sim E F D m := by
  simp only [AS.le, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  refine ⟨le_mem h8 hs.a, le_mem h9 hs.x, le_mem h10 hs.y, le_mem h11 hs.p, hs.s.trans h2, hs.pc.trans h1, hs.prg, hs.mask,
    le_mem h12 hs.ppuCtrl, le_mem h13 hs.ppuMask, hs.vb.trans h4, hs.nmi.trans h5, hs.s0, Nat.le_trans h14 hs.lo, Nat.le_trans hs.hi h15, h16,
    hs.pad, le_mem h6 hs.padShift, hs.strobe.trans h7, hs.halted, hs.trk, hs.size, ?_, ?_, h18, h19, ?_, ?_⟩
  · intro i hi
    exact le_mem (ramLeFrom_spec 2048 0 h20 i (Nat.zero_le _) (by omega)) (hs.ram i hi)
  · intro hg
    rcases h17 with h0 | h0
    · rw [h0] at hg
      cases hg
    · exact hs.dg h0
  · rw [hs.fr, h3]
  · intro hr
    rw [← h22]
    exact hs.rkv (h21 ▸ hr)

theorem TR_eqTri {b : AB} {x : UInt8} (c : UInt16) (h : b.mem x) : TR (eqTri b c) (x.toUInt16 == c) := by
  unfold eqTri
  split
  · rename_i hk
    right
    rw [isK_eq hk h]
  · exact Or.inl rfl

theorem tri3_ok {a b c : Option Bool} {x y z r : Bool} (t1 : TR a x) (t2 : TR b y) (t3 : TR c z) (h : tri3 a b c = some r) : (x && y && z) = r := by
  rcases t1 with rfl | rfl <;> rcases t2 with rfl | rfl <;> rcases t3 with rfl | rfl <;>
    cases x <;> cases y <;> cases z <;> simp [tri3] at h ⊢ <;> exact h

theorem actl_ok (sy : Syms) {B : AS} {m : Machine} {r : Bool} (hs : Sim E F B m) (h : actl sy B = some r) : controllable sy m = r :=
  tri3_ok (TR_eqTri _ (hs.ram _ (PipeTransitionAll.mask_lt _))) (TR_eqTri _ (hs.ram _ (PipeTransitionAll.mask_lt _)))
    (TR_eqTri _ (hs.ram _ (PipeTransitionAll.mask_lt _))) h

end


/-! ## One frame, from a table -/

/-- from `A`, step by step until every path ends in a state of the table, or at the frame's end in a state that `fin` accepts -/
def walkF (C : Cfg) (fin : AS → Bool) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (succs C.E C.ops A).all fun r =>
    match r with
    | none => false
    | some B =>
      if B.k == A.k then (C.cut.get! B.pc.toNat != 0 && coverIn C B) || walkF C fin n B
      else B.k == A.k + 1 && fin B

section
variable {C : Cfg} {Fu : Nat} {F : Nat × UInt8} {fin : AS → Bool}

/-- `A` covers `m`, and a walk from `A` succeeds -/
def LiveF (C : Cfg) (fin : AS → Bool) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ ∃ n, walkF C fin n A = true

theorem cover_liveF (ht : C.t.all (walkF C fin Fu) = true) {B : AS} {m : Machine} (hs : Sim C.E F B m) (h : coverIn C B = true) :
    ∃ D, LiveF C fin F D m ∧ D.k = B.k := by
  unfold coverIn at h
  obtain ⟨i, _, h2⟩ := List.any_eq_true.1 h
  split at h2
  · rename_i D e
    have hle : B.le D = true := h2
    have hk : D.k = B.k := by
      simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at hle
      exact hle.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2.symm
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e
    have hall := (Array.all_eq_true.1 ht) i hi
    rw [he] at hall
    exact ⟨D, ⟨sim_le hle hs, Fu, hall⟩, hk⟩
  · cases h2

theorem live_stepF (ht : C.t.all (walkF C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {A : AS} {m : Machine} (hl : LiveF C fin F A m) :
    (∃ A', LiveF C fin F A' (go step m).2 ∧ A'.k = A.k ∧ (go step m).2.frame = m.frame ∧ m.fdot + 3 ≤ (go step m).2.fdot) ∨
    ((go step m).2.frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go step m).2) := by
  obtain ⟨hs, n, hw⟩ := hl
  cases n with
  | zero => simp [walkF] at hw
  | succ n =>
    obtain ⟨r, hr, hB⟩ := s_succs hops hT hs
    simp only [walkF, List.all_eq_true] at hw
    have hw2 := hw r hr
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, h2⟩ := hB B rfl
      dsimp only at hw2
      rcases h2 with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
      · left
        rw [if_pos (by simp [k1])] at hw2
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hw2
        rcases hw2 with ⟨_, h3⟩ | h3
        · obtain ⟨D, hD, hk⟩ := cover_liveF ht h1 h3
          exact ⟨D, hD, hk.trans k1, k2, k3⟩
        · exact ⟨B, ⟨h1, n, h3⟩, k1, k2, k3⟩
      · right
        rw [if_neg (by simp [k1])] at hw2
        simp only [Bool.and_eq_true, beq_iff_eq] at hw2
        exact ⟨k2, B, hw2.2, k1, h1⟩

theorem ruf_doneF {t : Nat} {m : Machine} (h : m.frame ≥ t) : ∀ n, (go (runUntilFrame t n) m).2 = m := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    rw [PipeTransitionAll.ruf_eq, if_pos (by simp [h])]

theorem frame_runF (ht : C.t.all (walkF C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) {f : Nat} :
    ∀ (n : Nat) (A : AS) (m : Machine), LiveF C fin F A m → m.frame = f → dotsPerFrame ≤ m.fdot + 3 * n →
      (go (runUntilFrame (f + 1) n) m).2.frame = f + 1 ∧ ∃ B, fin B = true ∧ B.k = A.k + 1 ∧ Sim C.E F B (go (runUntilFrame (f + 1) n) m).2 := by
  intro n
  induction n with
  | zero =>
    intro A m hl _ hd
    have h1 := hl.1.hi
    have h2 := hl.1.lim
    omega
  | succ n ih =>
    intro A m hl hf hd
    have hh := hl.1.halted
    rw [PipeTransitionAll.ruf_eq, if_neg (by simp [hf, hh])]
    rcases live_stepF ht hops hT hl with ⟨A', h1, h2, h3, h4⟩ | ⟨h1, B, h2, h3, h4⟩
    · have := ih A' _ h1 (h3.trans hf) (by omega)
      rw [h2] at this
      exact this
    · rw [ruf_doneF (by rw [h1, hf]; exact Nat.le_refl _) n]
      exact ⟨by rw [h1, hf], B, h2, h3, h4⟩

/-- **One frame.** A walk from `S` that succeeds covers the frame of every machine of `S`, with any input. -/
theorem frame_of_walk (ht : C.t.all (walkF C fin Fu) = true) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat) (hp : C.E.pad = AB.top)
    {S : AS} {m : Machine} (hw : walkF C fin Fu S = true) (hs : Sim C.E F S m) (i : UInt8) :
    (frame m i).frame = m.frame + 1 ∧ ∃ B, fin B = true ∧ B.k = S.k + 1 ∧ Sim C.E F B (frame m i) := by
  have hs1 : Sim C.E F S { m with pad := smbToPad i } := { hs with pad := by rw [hp]; exact mem_top _ }
  rw [PipeTransitionAll.frame_eq]
  have hf : dotsPerFrame ≤ ({ m with pad := smbToPad i } : Machine).fdot + 3 * fuelPerFrame := by
    have : dotsPerFrame ≤ 3 * fuelPerFrame := by decide
    show dotsPerFrame ≤ m.fdot + 3 * fuelPerFrame
    omega
  exact frame_runF ht hops hT (f := m.frame) fuelPerFrame S _ ⟨hs1, Fu, hw⟩ rfl hf

end

/-! ## The counter: a rank on the frames -/

/-- the value of the counter -/
def tm (E : Env) (m : Machine) : UInt8 := m.ram.get! E.rkI

/-- the state `S` with the counter known to be 1, so that the frame on which it runs out can be followed -/
def toOne (E : Env) (S : AS) : AS := { S.setK E.rkI (AB.known 1) with rk := false }

/-- at the frame's end, with the counter followed: a start state -/
def finRk (starts : List AS) (B : AS) : Bool := B.rk && starts.any fun S => ({ B with k := 0, spent := false } : AS).le S

/-- `B` knows that the byte `p.1` has the value `p.2` -/
def knownIs (B : AS) (p : Nat × UInt8) : Bool := decide (p.1 < 2048) && (B.getK p.1).isK && (B.getK p.1).v == p.2

/-- at the frame's end, with the counter at 1 before it: the counter has not moved, or the bytes `xb` have these values -/
def finOne (ones : List AS) (xb : List (Nat × UInt8)) (B : AS) : Bool :=
  !B.rk && (ones.any (fun S => ({ B with k := 0 } : AS).le S) || xb.all (knownIs B))

/-- **The state during the pipe.** The counter is at least 2 and it is followed, or it is 1 and known. -/
def InvAt (E : Env) (starts : List AS) (m : Machine) : Prop :=
  ∃ S ∈ starts, (2 ≤ (tm E m).toNat ∧ Sim E (m.frame, tm E m) S m) ∨ (tm E m = 1 ∧ Sim E (m.frame, 2) (toOne E S) m)

/-- **The state after the pipe.** The listed bytes have the listed values. -/
def ExitAt (xb : List (Nat × UInt8)) (m : Machine) : Prop := ∀ p ∈ xb, m.ram.get! p.1 = p.2

/-- the two tables: the frames with the counter followed, and the frames with the counter at 1 -/
def cfgR (E : Env) (sy : Syms) (keep : List Nat) (starts : List AS) : Cfg := Cfg.of E sy 1 keep starts
def cfgO (E : Env) (sy : Syms) (keep : List Nat) (starts : List AS) : Cfg := Cfg.of E sy 1 keep (starts.map (toOne E))

/-- what the check of one frame says -/
structure FrameOK (E : Env) (sy : Syms) (keep : List Nat) (starts : List AS) (xb : List (Nat × UInt8)) : Prop where
  ti : E.rkI < 2048
  rkStarts : ∀ S ∈ starts, S.k = 0 ∧ S.rk = true ∧ S.spent = false
  tr : (cfgR E sy keep starts).t.all (walkF (cfgR E sy keep starts) (finRk starts) TaintRun.walkFuel) = true
  sr : ∀ S ∈ starts, walkF (cfgR E sy keep starts) (finRk starts) TaintRun.walkFuel S = true
  to : (cfgO E sy keep starts).t.all (walkF (cfgO E sy keep starts) (finOne (starts.map (toOne E)) xb) TaintRun.walkFuel) = true
  so : ∀ S ∈ starts, walkF (cfgO E sy keep starts) (finOne (starts.map (toOne E)) xb) TaintRun.walkFuel (toOne E S) = true

/-- the check of one frame -/
def frameCheck (E : Env) (sy : Syms) (keep : List Nat) (starts : List AS) (xb : List (Nat × UInt8)) : Bool :=
  let ones := starts.map (toOne E)
  let Cr := cfgR E sy keep starts
  let Co := cfgO E sy keep starts
  let fr := finRk starts
  let fo := finOne ones xb
  decide (E.rkI < 2048) && starts.all (fun S => S.k == 0 && S.rk && !S.spent) &&
    Cr.t.all (walkF Cr fr TaintRun.walkFuel) && starts.all (walkF Cr fr TaintRun.walkFuel) &&
    Co.t.all (walkF Co fo TaintRun.walkFuel) && starts.all (fun S => walkF Co fo TaintRun.walkFuel (toOne E S))

theorem frameOK_of_check {E : Env} {sy : Syms} {keep : List Nat} {starts : List AS} {xb : List (Nat × UInt8)} (h : frameCheck E sy keep starts xb = true) :
    FrameOK E sy keep starts xb := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, fun S hS => ?_, h3, h4, h5, h6⟩
  have := h2 S hS
  exact ⟨this.1.1, this.1.2, this.2⟩

section
variable {E : Env} {sy : Syms} {keep : List Nat} {starts : List AS} {xb : List (Nat × UInt8)}

open PipeTransitionAll (ba_get_set_self ba_get_set_ne ba_size_set)

theorem sim_known {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) {p : Nat × UInt8} (h : knownIs A p = true) : m.ram.get! p.1 = p.2 := by
  simp only [knownIs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [isK_eq h2 (hs.ram p.1 h1), h3]

/-- the counter at 1 is known -/
theorem sim_toOne {F : Nat × UInt8} {A : AS} {m : Machine} (hi : E.rkI < 2048) (hs : Sim E F A m) (h1 : m.ram.get! E.rkI = 1) (G : Nat × UInt8) (hG : G.1 = F.1) :
    Sim E G (toOne E A) m := by
  refine { hs with
    ram := ?_
    szR := ?_
    szK := ?_
    fr := ?_
    rkv := ?_ }
  · intro i hh
    show AB.mem ⟨(A.ram.set! E.rkI (AB.known 1).v).get! i, (A.kn.set! E.rkI (AB.known 1).k).get! i⟩ (m.ram.get! i)
    by_cases hdi : E.rkI = i
    · subst hdi
      rw [ba_get_set_self _ _ _ (by rw [hs.szR]; exact hh), ba_get_set_self _ _ _ (by rw [hs.szK]; exact hh), h1]
      exact mem_known_self _
    · rw [ba_get_set_ne _ _ _ _ hdi, ba_get_set_ne _ _ _ _ hdi]
      exact hs.ram i hh
  · show (A.ram.set! _ _).size = 2048
    rw [ba_size_set]
    exact hs.szR
  · show (A.kn.set! _ _).size = 2048
    rw [ba_size_set]
    exact hs.szK
  · show m.frame = G.1 + A.k
    rw [hG]
    exact hs.fr
  · intro hr
    cases hr

/-- the counter in `toOne` -/
theorem one_of_sim {F : Nat × UInt8} {S : AS} {m : Machine} (hi : E.rkI < 2048) (hs : Sim E F (toOne E S) m) : m.ram.get! E.rkI = 1 := by
  have hm := hs.ram E.rkI hi
  have h1 : (toOne E S).getK E.rkI = AB.known 1 := by
    show (⟨(S.ram.set! E.rkI (AB.known 1).v).get! E.rkI, (S.kn.set! E.rkI (AB.known 1).k).get! E.rkI⟩ : AB) = AB.known 1
    have hR : (S.ram.set! E.rkI (AB.known 1).v).size = 2048 := hs.szR
    have hK : (S.kn.set! E.rkI (AB.known 1).k).size = 2048 := hs.szK
    rw [ba_size_set] at hR hK
    rw [ba_get_set_self _ _ _ (by rw [hR]; exact hi), ba_get_set_self _ _ _ (by rw [hK]; exact hi)]
  rw [h1] at hm
  exact known_eq hm

/-- **One frame of the pipe, for any input.** The counter falls by at most one. When it was 1, the frame may also leave the pipe. -/
theorem inv_step (hc : FrameOK E sy keep starts xb) (hp : E.pad = AB.top) {m : Machine} (h : InvAt E starts m) (i : UInt8) :
    (InvAt E starts (frame m i) ∧ (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1) ∨ (tm E m = 1 ∧ ExitAt xb (frame m i)) := by
  obtain ⟨S, hS, (⟨h2, hs⟩ | ⟨h1, hs⟩)⟩ := h
  · -- the counter is at least 2: the first table
    obtain ⟨k0, _, _⟩ := hc.rkStarts S hS
    obtain ⟨g1, B, g2, g3, g4⟩ := frame_of_walk (C := cfgR E sy keep starts) (F := (m.frame, tm E m)) hc.tr rfl h2 hp (hc.sr S hS) hs i
    simp only [finRk, Bool.and_eq_true, List.any_eq_true] at g2
    obtain ⟨hr, S', hS', hle⟩ := g2
    have hv : (frame m i).ram.get! E.rkI = if B.spent then tm E m - 1 else tm E m := g4.rkv hr
    have hbase : Sim E ((frame m i).frame, tm E (frame m i)) ({ B with k := 0, spent := false } : AS) (frame m i) := by
      refine { g4 with fr := ?_, rkv := ?_ }
      · show (frame m i).frame = (frame m i).frame + 0
        rfl
      · intro _
        rfl
    have hs' := sim_le hle hbase
    have hle2 : (tm E m).toNat ≤ (tm E (frame m i)).toNat + 1 := by
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat + 1
      rw [hv]
      split
      · rw [u8_sub_one h2]
        omega
      · omega
    left
    refine ⟨?_, hle2⟩
    refine ⟨S', hS', ?_⟩
    have hge : 1 ≤ (tm E (frame m i)).toNat := by omega
    by_cases h3 : 2 ≤ (tm E (frame m i)).toNat
    · exact Or.inl ⟨h3, hs'⟩
    · have he : tm E (frame m i) = 1 := by
        apply UInt8.toNat_inj.1
        have : (1 : UInt8).toNat = 1 := rfl
        omega
      exact Or.inr ⟨he, sim_toOne hc.ti hs' he _ rfl⟩
  · -- the counter is 1: the second table
    have hS1 : toOne E S ∈ starts.map (toOne E) := List.mem_map.2 ⟨S, hS, rfl⟩
    obtain ⟨g1, B, g2, g3, g4⟩ := frame_of_walk (C := cfgO E sy keep starts) (F := (m.frame, 2)) hc.to rfl (Nat.le_refl _) hp (hc.so S hS) hs i
    simp only [finOne, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at g2
    obtain ⟨hr, (⟨S', hS', hle⟩ | hx)⟩ := g2
    · obtain ⟨S2, hS2, rfl⟩ := List.mem_map.1 hS'
      have hbase : Sim E ((frame m i).frame, 2) ({ B with k := 0 } : AS) (frame m i) := by
        refine { g4 with fr := ?_, rkv := ?_ }
        · show (frame m i).frame = (frame m i).frame + 0
          rfl
        · intro hr2
          rw [hr] at hr2
          cases hr2
      have hs' := sim_le hle hbase
      have he := one_of_sim hc.ti hs'
      left
      refine ⟨⟨S2, hS2, Or.inr ⟨he, hs'⟩⟩, ?_⟩
      show (tm E m).toNat ≤ ((frame m i).ram.get! E.rkI).toNat + 1
      rw [he, h1]
      decide
    · right
      exact ⟨h1, fun p hq => sim_known g4 (hx p hq)⟩

end

/-! ## Many frames, for any inputs -/

section
variable {E : Env} {sy : Syms} {keep : List Nat} {starts : List AS} {xb : List (Nat × UInt8)}

open PipeChangeBound (seqOf seqOf_succ)

theorem seq_zero (M : Machine) (w : List UInt8) : seqOf M w 0 = M := by
  simp [seqOf, PipeTransition.run]

/-- while the counter has not had time to run out, the state is the state during the pipe, and the counter has fallen by at most the number of frames -/
theorem inv_seq (hc : FrameOK E sy keep starts xb) (hp : E.pad = AB.top) {M : Machine} (hM : InvAt E starts M) (w : List UInt8) :
    ∀ j, j ≤ w.length → j < (tm E M).toNat → InvAt E starts (seqOf M w j) ∧ (tm E M).toNat ≤ (tm E (seqOf M w j)).toNat + j := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [seq_zero]
    exact ⟨hM, by omega⟩
  | succ j ih =>
    intro h1 h2
    obtain ⟨i1, i2⟩ := ih (by omega) (by omega)
    have hj : j < w.length := by omega
    rw [seqOf_succ M w hj]
    rcases inv_step (sy := sy) (keep := keep) hc hp i1 w[j] with ⟨h3, h4⟩ | ⟨h3, _⟩
    · exact ⟨h3, by omega⟩
    · exfalso
      have : (tm E (seqOf M w j)).toNat = 1 := by rw [h3]; rfl
      omega

/-- **The first frames, for any inputs.** Up to the frame on which the counter can first run out, the state is during the pipe or after it. -/
theorem state_seq (hc : FrameOK E sy keep starts xb) (hp : E.pad = AB.top) {M : Machine} (hM : InvAt E starts M) (w : List UInt8) :
    ∀ j, j ≤ w.length → j ≤ (tm E M).toNat → InvAt E starts (seqOf M w j) ∨ ExitAt xb (seqOf M w j) := by
  intro j h1 h2
  by_cases h3 : j < (tm E M).toNat
  · exact Or.inl (inv_seq hc hp hM w j h1 h3).1
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := by
      cases j with
      | zero =>
        exfalso
        have : 0 < (tm E M).toNat := by
          obtain ⟨S, _, (⟨h, _⟩ | ⟨h, _⟩)⟩ := hM
          · omega
          · rw [h]; decide
        omega
      | succ n => exact ⟨n, rfl⟩
    have hj : n < w.length := by omega
    obtain ⟨i1, _⟩ := inv_seq hc hp hM w n (by omega) (by omega)
    rw [seqOf_succ M w hj]
    rcases inv_step (sy := sy) (keep := keep) hc hp i1 w[n] with ⟨h4, _⟩ | ⟨_, h4⟩
    · exact Or.inl h4
    · exact Or.inr h4

end

/-! ## The number of frames left -/

section
open PipeChangeBound (inPipe leftOf keysOK)
open PipeTransitionAll (Names)

/-- the bytes that say where the change is, with the values in the reference machine `x` -/
def exitBytes (sy : Syms) (nm : Names) (x : Machine) : List (Nat × UInt8) :=
  [sy.OperMode_Task, nm.ad "ScreenRoutineTask", sy.GameEngineSubroutine, nm.ad "DisableScreenFlag"].map fun a => ((a &&& 0x7FF).toNat, peek x a)

/-- the state `A` knows that the pipe's routine `eng` runs in the game core -/
def pipeOK (sy : Syms) (eng : UInt16) (A : AS) : Bool :=
  knownIs A ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8) && sy.Task_GameCore.toUInt8.toUInt16 == sy.Task_GameCore &&
  knownIs A ((sy.GameEngineSubroutine &&& 0x7FF).toNat, eng.toUInt8) && eng.toUInt8.toUInt16 == eng

/-- what links the frames to the number `left`. `x` is the reference machine when the timer has run out. -/
def leftCheck (E : Env) (sy : Syms) (nm : Names) (eng : UInt16) (tbl : List (List UInt8 × Nat)) (B : Nat) (starts : List AS) (x : Machine) : Bool :=
  E.rkI == ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat && keysOK sy eng tbl &&
  starts.all (pipeOK sy eng) && (starts.map (toOne E)).all (pipeOK sy eng) &&
  (peek x sy.OperMode_Task).toUInt16 != sy.Task_GameCore && tbl.lookup (PipeChangeBound.keyOf sy nm x) == some B

variable {E : Env} {sy : Syms} {nm : Names} {eng : UInt16} {tbl : List (List UInt8 × Nat)} {B : Nat} {keep : List Nat} {starts : List AS} {x : Machine}

structure LeftOK (E : Env) (sy : Syms) (nm : Names) (eng : UInt16) (tbl : List (List UInt8 × Nat)) (B : Nat) (starts : List AS) (x : Machine) : Prop where
  timer : E.rkI = ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat
  keys : keysOK sy eng tbl = true
  s1 : ∀ S ∈ starts, pipeOK sy eng S = true
  s2 : ∀ S ∈ starts, pipeOK sy eng (toOne E S) = true
  notCore : (peek x sy.OperMode_Task).toUInt16 ≠ sy.Task_GameCore
  look : tbl.lookup (PipeChangeBound.keyOf sy nm x) = some B

theorem leftOK_of_check (h : leftCheck E sy nm eng tbl B starts x = true) : LeftOK E sy nm eng tbl B starts x := by
  simp only [leftCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, fun S hS => h4 _ (List.mem_map.2 ⟨S, hS, rfl⟩), h5, h6⟩

theorem inPipe_of_sim {F : Nat × UInt8} {A : AS} {m : Machine} (hs : Sim E F A m) (h : pipeOK sy eng A = true) : inPipe sy eng m = true := by
  simp only [pipeOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := sim_known hs h1
  have e2 := sim_known hs h3
  simp only [inPipe, Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · show (m.ram.get! (sy.OperMode_Task &&& 0x7FF).toNat).toUInt16 = _
    rw [e1]
    exact h2
  · show (m.ram.get! (sy.GameEngineSubroutine &&& 0x7FF).toNat).toUInt16 = _
    rw [e2]
    exact h4

theorem inPipe_of_inv (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : InvAt E starts m) : inPipe sy eng m = true := by
  obtain ⟨S, hS, (⟨_, hs⟩ | ⟨_, hs⟩)⟩ := h
  · exact inPipe_of_sim hs (hl.s1 S hS)
  · exact inPipe_of_sim hs (hl.s2 S hS)

/-- during the pipe, `left` is the counter and `B` -/
theorem left_of_inv (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : InvAt E starts m) :
    leftOf sy nm eng tbl B m = (tm E m).toNat + B := by
  simp only [leftOf, inPipe_of_inv hl h, if_true]
  have : peek m (nm.ad "ChangeAreaTimer") = tm E m := by
    show m.ram.get! _ = m.ram.get! E.rkI
    rw [hl.timer]
  rw [this]

theorem key_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) :
    PipeChangeBound.keyOf sy nm m = PipeChangeBound.keyOf sy nm x := by
  have e : ∀ a, a ∈ [sy.OperMode_Task, nm.ad "ScreenRoutineTask", sy.GameEngineSubroutine, nm.ad "DisableScreenFlag"] → peek m a = peek x a := by
    intro a ha
    exact h ((a &&& 0x7FF).toNat, peek x a) (List.mem_map.2 ⟨a, ha, rfl⟩)
  have e1 := e _ List.mem_cons_self
  have e2 := e _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have e3 := e _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have e4 := e _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hn : ((peek x sy.OperMode_Task).toUInt16 == sy.Task_GameCore) = false := beq_eq_false_iff_ne.2 hl.notCore
  have hn2 : ((peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore) = false := by rw [e1]; exact hn
  unfold PipeChangeBound.keyOf
  simp only [hn, hn2, Bool.false_eq_true, if_false]
  rw [e1, e2, e3, e4]

/-- after the pipe, `left` is `B` -/
theorem left_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) :
    leftOf sy nm eng tbl B m = B := by
  have e1 : peek m sy.OperMode_Task = peek x sy.OperMode_Task := h ((sy.OperMode_Task &&& 0x7FF).toNat, peek x sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  have hnp : inPipe sy eng m = false := by
    cases hq : inPipe sy eng m with
    | false => rfl
    | true =>
      exfalso
      simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at hq
      rw [e1] at hq
      exact hl.notCore hq.1
  simp only [leftOf, hnp, if_false]
  rw [key_of_exit hl h, hl.look]
  rfl

/-- **A frame of the pipe takes at most one off `left`, for any input.** -/
theorem fall_of_inv (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine}
    (h : InvAt E starts m) (i : UInt8) : leftOf sy nm eng tbl B m ≤ leftOf sy nm eng tbl B (frame m i) + 1 := by
  rw [left_of_inv hl h]
  rcases inv_step hc hp h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [left_of_inv hl h1]
    omega
  · rw [left_of_exit hl h2, h1]
    have : (1 : UInt8).toNat = 1 := rfl
    omega

theorem ctl_of_inPipe {m : Machine} (hk : keysOK sy eng tbl = true) (h : inPipe sy eng m = true) : controllable sy m = false := by
  simp only [keysOK, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hk
  simp only [inPipe, Bool.and_eq_true, beq_iff_eq] at h
  cases hc : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    exact hk.1 (h.2.symm.trans hc.2)

theorem ctl_of_exit (hl : LeftOK E sy nm eng tbl B starts x) {m : Machine} (h : ExitAt (exitBytes sy nm x) m) : controllable sy m = false := by
  have e1 : peek m sy.OperMode_Task = peek x sy.OperMode_Task := h ((sy.OperMode_Task &&& 0x7FF).toNat, peek x sy.OperMode_Task) (List.mem_map.2 ⟨_, List.mem_cons_self, rfl⟩)
  cases hc : controllable sy m with
  | false => rfl
  | true =>
    exfalso
    simp only [controllable, Bool.and_eq_true, beq_iff_eq] at hc
    rw [e1] at hc
    exact hl.notCore hc.1.2

open PipeChangeBound (seqOf seqOf_succ)

/-- **No control on the first frames, for any inputs.** The whole statement comes from the state `M` alone. `c` is at most the counter's value in `M`. -/
theorem no_control_first (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {M : Machine}
    (hM : InvAt E starts M) {c : Nat} (hT : c ≤ (tm E M).toNat) (w : List UInt8) : ∀ j, j ≤ w.length → j ≤ c → controllable sy (seqOf M w j) = false := by
  intro j h1 h2
  rcases state_seq hc hp hM w j h1 (by omega) with h3 | h3
  · exact ctl_of_inPipe hl.keys (inPipe_of_inv hl h3)
  · exact ctl_of_exit hl h3

/-- **No control on the whole change, for any inputs.** The frames in the state during the pipe are proved. The other frames keep the hypothesis `hf`: `left` falls by at most one on them. -/
theorem no_control_all (hc : FrameOK E sy keep starts (exitBytes sy nm x)) (hp : E.pad = AB.top) (hl : LeftOK E sy nm eng tbl B starts x) {M : Machine}
    (hM : InvAt E starts M) (w : List UInt8)
    (hf : ∀ j (h : j < w.length), ¬ InvAt E starts (seqOf M w j) → leftOf sy nm eng tbl B (seqOf M w j) ≤ leftOf sy nm eng tbl B (frame (seqOf M w j) w[j]) + 1) :
    ∀ j, j ≤ w.length → j < (tm E M).toNat + B → controllable sy (seqOf M w j) = false := by
  intro j h1 h2
  refine PipeChangeBound.no_control (controllable sy) (left := leftOf sy nm eng tbl B) M w ?_ (fun i _ hq => PipeChangeBound.left_zero_of_ctl hl.keys hq) j h1 ?_
  · intro i hi
    by_cases hin : InvAt E starts (seqOf M w i)
    · exact fall_of_inv hc hp hl hin _
    · exact hf i hi hin
  · rw [left_of_inv hl hM]
    exact h2

/-- **The bound on the change, counted.** `seq` lists all the frames of a run, `cnt` counts the frames that are not lag frames. Each counted frame takes at most one off `left`, a lag frame takes nothing off.
Then the change from `a` to `b` has at least `left (seq a)` counted frames, if `left` is 0 at `b`. -/
theorem change_counted {left : Machine → Nat} {seq : Nat → Machine} {cnt : Nat → Nat} {lag : Nat → Prop} [DecidablePred lag]
    (hc : ∀ n, cnt (n + 1) = cnt n + (if lag n then 0 else 1)) {a b : Nat} (hab : a ≤ b)
    (hf : ∀ n, a ≤ n → n < b → left (seq n) ≤ left (seq (n + 1)) + (if lag n then 0 else 1)) (hb : left (seq b) = 0) :
    cnt a + left (seq a) ≤ cnt b := by
  have key : ∀ d, a + d ≤ b → cnt a + left (seq a) ≤ cnt (a + d) + left (seq (a + d)) := by
    intro d
    induction d with
    | zero => intro _; exact Nat.le_refl _
    | succ d ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hf (a + d) (by omega) (by omega)
      have h3 := hc (a + d)
      have e : a + (d + 1) = a + d + 1 := rfl
      rw [e, h3]
      omega
  have := key (b - a) (by omega)
  have e : a + (b - a) = b := by omega
  rw [e, hb] at this
  omega

end

/-! ## The state at the entry -/

/-- the known bytes as a mask -/
def knOf (K : List Nat) : ByteArray := K.foldl (fun b i => b.set! i 0xFF) (ByteArray.mk (Array.replicate 2048 0))

/-- the abstract start state from the reference machine `r`, for dot 0 (`low`) or dots `1..9`. Only the bytes `K` are known. The registers are not known. The counter is followed. -/
def startOf (r : Machine) (K : List Nat) (low : Bool) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := r.s, p := AB.top, pc := r.pc, ram := r.ram, kn := knOf K, ppuCtrl := ⟨0x80, 0x80⟩, ppuMask := AB.top,
    vb := !low, nmi := !low, lo := if low then 0 else 1, hi := if low then 0 else 9, padShift := AB.top, strobe := false, dg := false, k := 0, rk := true, spent := false }

/-- the start states: each reference machine with its known bytes, two kinds of dots -/
def startsOf (V : List (Machine × List Nat)) : List AS :=
  V.flatMap fun v => [startOf v.1 v.2 true, startOf v.1 v.2 false]

/-- **The condition on the state at the end of the entry frame.** It is on one state. All bytes that are not listed are free. -/
structure EntryCond (E : Env) (V : List (Machine × List Nat)) (c : Nat) (m : Machine) : Prop where
  /-- the frame has ended in the idle loop, with the next NMI to come or pending -/
  dot : m.fdot < 10
  flags : (m.fdot = 0 ∧ m.vblank = false ∧ m.nmiPending = false) ∨ (1 ≤ m.fdot ∧ m.vblank = true ∧ m.nmiPending = true)
  s0 : m.sprite0 = true
  ctrl : m.ppuCtrl &&& 0x80 = 0x80
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048
  /-- the program counter, the stack pointer and the listed bytes are those of a reference machine -/
  ref : ∃ v ∈ V, m.pc = v.1.pc ∧ m.s = v.1.s ∧ ∀ i ∈ v.2, m.ram.get! i = v.1.ram.get! i
  /-- the counter -/
  timer : c ≤ (m.ram.get! E.rkI).toNat

/-- `EntryCond` as a check, for a program -/
def entryOK (E : Env) (V : List (Machine × List Nat)) (c : Nat) (m : Machine) : Bool :=
  decide (m.fdot < 10) && ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && m.vblank && m.nmiPending)) && m.sprite0 &&
  m.ppuCtrl &&& 0x80 == 0x80 && !m.padStrobe && !m.halted && !m.trk && decide (m.prg.data = E.prg.data) && m.prgMask == E.mask && m.ram.size == 2048 &&
  V.any (fun v => m.pc == v.1.pc && m.s == v.1.s && v.2.all fun i => m.ram.get! i == v.1.ram.get! i) && decide (c ≤ (m.ram.get! E.rkI).toNat)

theorem entryCond_of_ok {E : Env} {V : List (Machine × List Nat)} {c : Nat} {m : Machine} (h : entryOK E V c m = true) : EntryCond E V c m := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, ?_, h3, h4, h5, h6, h7, SideTransition.byteArray_eq h8, h9, h10, ?_, h12⟩
  · rcases h2 with ⟨⟨a1, a2⟩, a3⟩ | ⟨⟨a1, a2⟩, a3⟩
    · exact Or.inl ⟨a1, a2, a3⟩
    · exact Or.inr ⟨a1, a2, a3⟩
  · obtain ⟨v, hv, ⟨a1, a2⟩, a3⟩ := h11
    exact ⟨v, hv, a1, a2, a3⟩

/-- the masks of the start states are what the list says -/
def startsOK (V : List (Machine × List Nat)) : Bool :=
  V.all fun v => v.1.ram.size == 2048 && (knOf v.2).size == 2048 && (List.range 2048).all fun i => (knOf v.2).get! i == 0 || ((knOf v.2).get! i == 0xFF && v.2.contains i)

section
variable {E : Env} {V : List (Machine × List Nat)} {c : Nat}

theorem inv_of_entry (hV : startsOK V = true) (hp : E.pad = AB.top) (hc : 2 ≤ c) {m : Machine} (h : EntryCond E V c m) : InvAt E (startsOf V) m := by
  obtain ⟨v, hv, h1, h2, h3⟩ := h.ref
  simp only [startsOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hV
  obtain ⟨⟨s1, s2⟩, s3⟩ := hV v hv
  have hT : 2 ≤ (tm E m).toNat := Nat.le_trans hc h.timer
  have key : ∀ low : Bool, (low = true ↔ m.fdot = 0) → Sim E (m.frame, tm E m) (startOf v.1 v.2 low) m := by
    intro low hl
    have hvb : m.vblank = !low ∧ m.nmiPending = !low := by
      rcases h.flags with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
      · have : low = true := hl.2 a1
        subst this
        exact ⟨a2, a3⟩
      · have : low = false := by
          cases low with
          | false => rfl
          | true =>
            have := hl.1 rfl
            omega
        subst this
        exact ⟨a2, a3⟩
    have hlo : (if low = true then 0 else 1) ≤ m.fdot := by
      cases low with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have : m.fdot ≠ 0 := fun h0 => by
          have := hl.2 h0
          cases this
        omega
    have hhi : m.fdot ≤ (if low = true then 0 else 9) := by
      have hd := h.dot
      cases low with
      | true =>
        have := hl.1 rfl
        simp only [if_true]
        omega
      | false =>
        simp only [Bool.false_eq_true, if_false]
        omega
    refine ⟨mem_top _, mem_top _, mem_top _, mem_top _, h2, h1, h.prg, h.mask, ?_, mem_top _, hvb.1, hvb.2, ?_, hlo, hhi, ?_, by rw [hp]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, ?_, ?_, s1, s2, ?_, ?_⟩
    · show m.ppuCtrl &&& 0x80 = (0x80 : UInt8) &&& 0x80
      rw [h.ctrl]
      decide
    · rw [h.s0]
      have : m.fdot ≤ 9 := by have := h.dot; omega
      exact (s0f_small this).symm
    · show (if low = true then 0 else 9) < dotsPerFrame
      split <;> decide
    · intro i hi
      show AB.mem ⟨v.1.ram.get! i, (knOf v.2).get! i⟩ (m.ram.get! i)
      have h5 := s3 i (List.mem_range.2 hi)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h5
      rcases h5 with h5 | ⟨h5, h6⟩
      · apply bt_ext
        intro j hj
        simp [bt_and, h5, bt_zero hj]
      · rw [h3 i (by simpa using h6)]
        exact rfl
    · intro hd
      cases hd
    · show m.frame = m.frame + 0
      rfl
    · intro _
      rfl
  by_cases hd : m.fdot = 0
  · exact ⟨_, List.mem_flatMap.2 ⟨v, hv, List.mem_cons_self⟩, Or.inl ⟨hT, key true ⟨fun _ => hd, fun _ => rfl⟩⟩⟩
  · refine ⟨_, List.mem_flatMap.2 ⟨v, hv, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)⟩, Or.inl ⟨hT, key false ⟨fun h0 => (by cases h0), fun h0 => absurd h0 hd⟩⟩⟩

end

/-! ## The statement for the side pipe -/

section
open PipeTransitionAll (Names asmValue)
open PipeChangeBound (leftOf seqOf)

/-- the table of `left`: `n` frames with no input from `m`, each key with the frames left -/
def tableFrom (sy : Syms) (nm : Names) : Nat → Machine → List (List UInt8 × Nat)
  | 0, _ => []
  | n + 1, m => (PipeChangeBound.keyOf sy nm m, n + 1) :: tableFrom sy nm n (frame m 0)

/-- the bytes that the state at the entry knows: a name, an offset and a number of bytes. The values come from the reference machine. -/
def knownNames : List (String × Nat × Nat) :=
  [("OperMode", 0, 1), ("OperMode_Task", 0, 1), ("GameEngineSubroutine", 0, 1), ("ScreenRoutineTask", 0, 1), ("DisableScreenFlag", 0, 1), ("WorldNumber", 0, 1),
   ("AreaType", 0, 1), ("SecondaryHardMode", 0, 1),
   ("Player_State", 0, 1), ("Player_Y_HighPos", 0, 1), ("Player_Y_Position", 0, 1), ("Player_SprDataOffset", 0, 1), ("JumpspringAnimCtrl", 0, 1),
   ("Enemy_Flag", 0, 6), ("Enemy_ID", 5, 1), ("Fireball_State", 0, 2), ("Block_State", 0, 2), ("Block_RepFlag", 0, 2), ("Misc_State", 0, 9), ("FloateyNum_Timer", 0, 6),
   ("VineFlagOffset", 0, 1), ("Cannon_PageLoc", 0, 6), ("Cannon_X_Position", 0, 6), ("Cannon_Y_Position", 0, 4),
   ("EnemyData", 0, 2), ("EnemyDataOffset", 0, 1), ("EnemyObjectPageLoc", 0, 1), ("EnemyFrenzyBuffer", 0, 1), ("EnemyFrenzyQueue", 0, 1), ("StarInvincibleTimer", 0, 1),
   ("ScreenRight_PageLoc", 0, 1), ("ScreenRight_X_Pos", 0, 1), ("ScrollLock", 0, 1), ("ScrollThirtyTwo", 0, 1), ("AreaParserTaskNum", 0, 1), ("VRAM_Buffer_AddrCtrl", 0, 1),
   ("VRAM_Buffer1_Offset", 0, 1), ("VRAM_Buffer1", 0, 1),
   ("AreaMusicBuffer", 0, 1), ("EventMusicBuffer", 0, 1), ("MusicData", 0, 2), ("MusicOffset_Square1", 0, 1), ("NoiseSoundBuffer", 0, 1), ("AreaMusicQueue", 0, 1), ("EventMusicQueue", 0, 1), ("NoiseSoundQueue", 0, 1)]

/-- the bytes that the state knows besides, when the buffer of the screen holds a record -/
def recordNames : List (String × Nat × Nat) := [("VRAM_Buffer1", 1, 2), ("VRAM_Buffer1", 7, 1)]

/-- the names this file needs -/
def namesOf (text : String) : Names :=
  let ls := text.splitOn "\n"
  let l := (knownNames ++ recordNames).map (·.1) ++ ["ChangeAreaTimer", "FrameCounter"]
  l.eraseDups.filterMap fun n => (asmValue ls n).map (n, ·)

/-- the list of bytes of a list of names, as RAM indices -/
def bytesOf (nm : Names) (l : List (String × Nat × Nat)) : List Nat :=
  l.flatMap fun p => (List.range p.2.2).map fun j => ((nm.ad p.1).toNat + p.2.1 + j) &&& 0x7FF

/-- the environment of the abstract run: the pad is not known; the counter is the pipe's timer; the frame counter is read in pieces by its low bits -/
def sideEnv (nm : Names) (e : Machine) : Env :=
  { prg := e.prg, mask := e.prgMask, pad := AB.top, D := [], rkI := ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat, splits := [(((nm.ad "FrameCounter") &&& 0x7FF).toNat, 7)] }

/-- the reference machines from the entry `e`: one frame with the buffer of the screen empty, one with a record in it -/
def refsOf (nm : Names) (e : Machine) : List (Machine × List Nat) :=
  let ms := (List.range 9).map fun j => run e (zeros j)
  let off := fun (m : Machine) => peek m (nm.ad "VRAM_Buffer1_Offset")
  [((ms.find? (off · == 0)).getD e, bytesOf nm knownNames), ((ms.find? (off · != 0)).getD e, bytesOf nm (knownNames ++ recordNames))]

/-- the bytes whose values are kept apart in the search -/
def keepOf (nm : Names) : List Nat := [((nm.ad "VRAM_Buffer1_Offset") &&& 0x7FF).toNat, ((nm.ad "ChangeAreaTimer") &&& 0x7FF).toNat]

/-- `EntryCond` for the entry `e`, with the timer at least `A` -/
abbrev Entry (nm : Names) (e : Machine) (A : Nat) (m : Machine) : Prop := EntryCond (sideEnv nm e) (refsOf nm e) A m

/-- the number of frames left, with the table from `e` from frame `A` on -/
abbrev leftAt (sy : Syms) (nm : Names) (e : Machine) (A B : Nat) : Machine → Nat :=
  leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (run e (zeros A))) B

/-- the state during the pipe -/
abbrev During (nm : Names) (e : Machine) : Machine → Prop := InvAt (sideEnv nm e) (startsOf (refsOf nm e))

/-- the whole check on the ROM -/
def allCheck (sy : Syms) (nm : Names) (e : Machine) (es : List Machine) (A B : Nat) : Bool :=
  let E := sideEnv nm e
  let V := refsOf nm e
  let st := startsOf V
  let x := run e (zeros A)
  decide (2 ≤ A) && startsOK V && frameCheck E sy (keepOf nm) st (exitBytes sy nm x) &&
    leftCheck E sy nm sy.EngSidePipe (tableFrom sy nm B x) B st x && es.all (entryOK E V A)

/-- **The statement.** `A` is the pipe's timer and `B` the frames after it. -/
structure Statement (sy : Syms) (nm : Names) (e : Machine) (es : List Machine) (A B : Nat) : Prop where
  /-- the entries that were run meet the condition -/
  entries : ∀ m ∈ es, Entry nm e A m
  /-- an entry is in the state during the pipe -/
  during : ∀ M, Entry nm e A M → During nm e M
  /-- one frame of the pipe, for any input -/
  step : ∀ m, During nm e m → ∀ i, (During nm e (frame m i) ∧ (tm (sideEnv nm e) m).toNat ≤ (tm (sideEnv nm e) (frame m i)).toNat + 1) ∨
    (tm (sideEnv nm e) m = 1 ∧ ExitAt (exitBytes sy nm (run e (zeros A))) (frame m i))
  /-- one frame of the pipe takes at most one off `left`, for any input -/
  fall : ∀ m, During nm e m → ∀ i, leftAt sy nm e A B m ≤ leftAt sy nm e A B (frame m i) + 1
  /-- `left` at an entry -/
  atEntry : ∀ M, Entry nm e A M → A + B ≤ leftAt sy nm e A B M
  /-- control only where `left` is 0 -/
  atControl : ∀ m, controllable sy m = true → leftAt sy nm e A B m = 0
  /-- no control on the first `A` frames, for any inputs, from the condition on the entry alone -/
  noFirst : ∀ M, Entry nm e A M → ∀ w, ∀ j, j ≤ w.length → j ≤ A → controllable sy (seqOf M w j) = false
  /-- no control on the whole change, for any inputs, if `left` falls by at most one on the frames out of the state during the pipe -/
  noAll : ∀ M, Entry nm e A M → ∀ w, (∀ j (h : j < w.length), ¬ During nm e (seqOf M w j) → leftAt sy nm e A B (seqOf M w j) ≤ leftAt sy nm e A B (frame (seqOf M w j) w[j]) + 1) →
    ∀ j, j ≤ w.length → j < A + B → controllable sy (seqOf M w j) = false

theorem statement_of_check {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (h : allCheck sy nm e es A B = true) : Statement sy nm e es A B := by
  simp only [allCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hV⟩, hf⟩, hl⟩, hes⟩ := h
  have hF := frameOK_of_check hf
  have hL := leftOK_of_check hl
  have hp : (sideEnv nm e).pad = AB.top := rfl
  have hd : ∀ M, Entry nm e A M → During nm e M := fun M hM => inv_of_entry hV hp hA hM
  refine ⟨fun m hm => entryCond_of_ok (hes m hm), hd, fun m hm i => inv_step hF hp hm i, fun m hm i => fall_of_inv hF hp hL hm i, ?_, fun m hc => PipeChangeBound.left_zero_of_ctl hL.keys hc, ?_, ?_⟩
  · intro M hM
    show A + B ≤ leftOf sy nm sy.EngSidePipe (tableFrom sy nm B (run e (zeros A))) B M
    rw [left_of_inv hL (hd M hM)]
    have := hM.timer
    show A + B ≤ ((sideEnv nm e).rkI |> M.ram.get!).toNat + B
    omega
  · intro M hM w j h1 h2
    exact no_control_first hF hp hL (hd M hM) hM.timer w j h1 h2
  · intro M hM w hff j h1 h2
    have := hM.timer
    exact no_control_all hF hp hL (hd M hM) w hff j h1 (by
      show j < ((sideEnv nm e).rkI |> M.ram.get!).toNat + B
      omega)

/-! ## A run -/

/-- with no input, the frames of `seqOf` are the frames of `run` -/
theorem seq_zeros (M : Machine) {n k : Nat} (h : k ≤ n) : seqOf M (zeros n) k = run M (zeros k) := by
  simp only [seqOf, zeros]
  rw [List.take_replicate, Nat.min_eq_left h]

/-- `(H1)` of `SideTransitionAll.every_entry` follows from the condition on the entry -/
theorem Statement.no_input {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (S : Statement sy nm e es A B) {M : Machine} (hM : Entry nm e A M) :
    ∀ k, 1 ≤ k → k ≤ A → controllable sy (run M (zeros k)) = false := by
  intro k _ h2
  have := S.noFirst M hM (zeros A) k (by simpa [zeros] using h2) h2
  rwa [seq_zeros M h2] at this

/-- **The change of a run.** `seq` lists all the frames of a run, `a` is the entry, `b` is control. `cnt` counts the frames that are not lag frames. -/
structure ChangeRun (sy : Syms) (nm : Names) (e : Machine) (A B : Nat) where
  seq : Nat → Machine
  inp : Nat → UInt8
  next : ∀ n, seq (n + 1) = frame (seq n) (inp n)
  lag : Nat → Prop
  dec : DecidablePred lag
  cnt : Nat → Nat
  hcnt : ∀ n, cnt (n + 1) = cnt n + (if lag n then 0 else 1)
  a : Nat
  b : Nat
  order : a ≤ b
  /-- the condition on the state at the entry -/
  entry : Entry nm e A (seq a)
  /-- control at `b` -/
  atCtl : controllable sy (seq b) = true
  /-- a lag frame takes nothing off `left` -/
  lagKeeps : ∀ n, a ≤ n → n < b → lag n → leftAt sy nm e A B (seq n) ≤ leftAt sy nm e A B (seq (n + 1))
  /-- out of the state during the pipe, a frame takes at most one off `left` -/
  fallAfter : ∀ n, a ≤ n → n < b → ¬ During nm e (seq n) → leftAt sy nm e A B (seq n) ≤ leftAt sy nm e A B (seq (n + 1)) + 1

/-- **The bound on the change follows.** This is `change₂` of `Route`, with `A + B = 282`. -/
theorem ChangeRun.bound {sy : Syms} {nm : Names} {e : Machine} {es : List Machine} {A B : Nat} (S : Statement sy nm e es A B) (R : ChangeRun sy nm e A B) :
    R.cnt R.a + (A + B) ≤ R.cnt R.b := by
  have hf : ∀ n, R.a ≤ n → n < R.b → leftAt sy nm e A B (R.seq n) ≤ leftAt sy nm e A B (R.seq (n + 1)) + (@ite _ (R.lag n) (R.dec n) 0 1) := by
    intro n h1 h2
    by_cases hl : R.lag n
    · rw [if_pos hl]
      exact R.lagKeeps n h1 h2 hl
    · rw [if_neg hl]
      by_cases hd : During nm e (R.seq n)
      · rw [R.next n]
        exact S.fall _ hd _
      · exact R.fallAfter n h1 h2 hd
  have h := @change_counted (leftAt sy nm e A B) R.seq R.cnt R.lag R.dec R.hcnt R.a R.b R.order hf (S.atControl _ R.atCtl)
  have h2 := S.atEntry _ R.entry
  omega

end

end Smbrta.SideChangeBound
