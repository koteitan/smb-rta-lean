import Theorems.PipeEntryRule
import Std.Data.HashMap
import Std.Data.TreeMap

/-!
# Who writes the routine byte: one whole frame

`PipeEntryRule` proves one pass of the foot check, and assumes the rest of the frame (`Pass`). Here an abstract machine follows the whole frame, from the idle loop before the NMI, through the screen, the sound,
the player's routine, the enemies, to the frame's end. The result: an instruction that makes the routine byte the pipe's is the end of a foot check whose right foot was at or right of the window's left end.

The machine is the one of `TaintRun`. It does not fail on four things that it cannot decide. Each of them is a condition on one state (`Clean`), asked of every instruction of the frame up to the write:
* a store through an index or a pointer whose target is not known: it does not touch the bytes the walk needs (`Plain`); the walk then forgets the other bytes (`AS.forgetW`).
  A byte followed as the counter of `TaintRun` stays followed when it is among these bytes (`AS.forgetK`, used by `LagFrames`; this walk has no counter);
* `LDA (zp),Y` through a pointer that is not known: it does not read a register;
* the indirect jump: the index is in its table;
* the time: the instruction runs before the frame's last dots.

The frame must start in the idle loop, in control (`FrameStart`). The block buffer's tile stays as `TilesOK` on the frame that enters (`tiles_of_steps` reduces it to single instructions). The row of a read is no hypothesis here: the walk knows it.
There is no game data in this file. Page: `1-1/a-5-2-PipeWrites.md`.
-/

namespace Smbrta.PipeWrites

open PipeTransition (frame)
open PipeTransitionAll (go ba_get_set_self ba_get_set_ne ba_size_set)
open SideChangeBound
open TaintRun (AB AAd mem_known_self mem_top bt bt_and bt_not bt_ext bt_zero)
open PipeEntryRule

/-! ## What the walk knows of the game -/

/-- places and bytes, from the symbols and the ROM -/
structure Guard where
  P : Spots
  /-- the routine byte, and the pipe's routine -/
  rtI : Nat
  ev : UInt8
  /-- the bytes known when the frame starts: the frame is in control -/
  known : List (Nat × UInt8)
  /-- the bytes that a store with a target not known does not touch -/
  prot : List Nat
  /-- the jump routine, and its tables: the first entry and the number of entries -/
  je : UInt16
  jumps : List (Nat × Nat)
  /-- the idle loop, and the stack pointer there -/
  idle : UInt16
  s0 : UInt8
  /-- the lowest byte of the stack that the walk keeps -/
  stackLo : Nat
  /-- no instruction before the write runs later than this dot -/
  late : Nat
  /-- the vertical position, and where the block buffer routine loads it -/
  yI : Nat
  loadY : UInt16
  /-- the return address of the collision routine, on the stack -/
  zLo : UInt8
  zHi : UInt8
  deriving Inhabited

/-! ## The conditions on one state -/

/-- the opcode at the machine's `pc` -/
def opAt (m : Machine) : UInt8 := m.prg.get! (m.pc &&& m.prgMask).toNat

/-- the target of a store through an index or a pointer, for the opcodes the walk meets -/
def wTarget (op : UInt8) (m : Machine) : Option UInt16 :=
  let m₁ : Machine := { m with pc := m.pc + 1 }
  if op == 0x95 || op == 0x94 || op == 0xD6 || op == 0xF6 then some (go mZpx m₁).1
  else if op == 0x9D || op == 0xDE || op == 0xFE || op == 0x7E then some (go mAbx m₁).1
  else if op == 0x99 then some (go mAby m₁).1
  else if op == 0x91 then some (go mIzy m₁).1
  else none

/-- the target of `LDA (zp),Y` -/
def rTarget (m : Machine) : UInt16 := (go mIzyR { m with pc := m.pc + 1 }).1

/-- a store here changes no byte of `prot` and has no other effect on the machine: RAM outside `prot`, or a place that keeps nothing -/
def Plain (prot : List Nat) (t : UInt16) : Prop :=
  (t < 0x2000 ∧ (t &&& 0x7FF).toNat ∉ prot) ∨ (0x4000 ≤ t ∧ t ≠ 0x4014 ∧ t ≠ 0x4016)

/-- the first entry of the table of a jump: the return address on the stack, plus one -/
def tableOf (m : Machine) : UInt16 :=
  ((m.ram.get! (0x100 + m.s.toNat + 1)).toUInt16 ||| ((m.ram.get! (0x100 + m.s.toNat + 2)).toUInt16 <<< 8)) + 1

/-- **What stays assumed of one instruction.** -/
structure Clean (G : Guard) (m : Machine) : Prop where
  /-- a store through an index or a pointer is `Plain` -/
  store : ∀ t, wTarget (opAt m) m = some t → Plain G.prot t
  /-- `LDA (zp),Y` does not read a register -/
  read : opAt m = 0xB1 → rTarget m < 0x2000 ∨ 0x8000 ≤ rTarget m
  /-- the index of the jump is in its table -/
  jump : m.pc = G.je → ∀ n, G.jumps.lookup (tableOf m).toNat = some n → m.a.toNat < n
  /-- the time -/
  time : m.pc ≠ G.idle → m.fdot ≤ G.late

/-- what the pass asks: left of the window at the entry for the right foot, `TilesOK` at its read -/
def HypG (P : Spots) (m : Machine) : Prop := (AtEntry P m → px P m < P.left) ∧ (AtRead P m → TilesOK P m)

/-- **The frame starts** in the idle loop, just before or just after the frame's first event, with the player's routine. -/
structure FrameStart (G : Guard) (E : Env) (m : Machine) : Prop where
  pc : m.pc = G.idle
  s : m.s = G.s0
  dot : (m.fdot = 0 ∧ m.vblank = false ∧ m.nmiPending = false) ∨ (1 ≤ m.fdot ∧ m.fdot ≤ 9 ∧ m.vblank = true ∧ m.nmiPending = true)
  ctrl : m.ppuCtrl &&& 0x80 = 0x80
  s0 : m.sprite0 = s0f m.fdot
  strobe : m.padStrobe = false
  halted : m.halted = false
  trk : m.trk = false
  prg : m.prg = E.prg
  mask : m.prgMask = E.mask
  size : m.ram.size = 2048
  known : ∀ p ∈ G.known, m.ram.get! p.1 = p.2

/-! ## Forgetting -/

def zeros : ByteArray := ByteArray.mk (Array.replicate 2048 0)

/-- the known bits of the bytes of `prot`, and no others -/
def keepKn (prot : List Nat) (kn : ByteArray) : ByteArray := prot.foldl (fun k i => k.set! i (kn.get! i)) zeros

/-- after a store with a target not known: only the bytes of `prot` stay known -/
def AS.forgetW (prot : List Nat) (A : AS) : AS := { A with kn := keepKn prot A.kn, dg := false, rk := false }

/-- the same, but the counter `r` stays followed when it is in `prot`: such a store does not touch it -/
def AS.forgetK (prot : List Nat) (r : Nat) (A : AS) : AS := { AS.forgetW prot A with rk := A.rk && prot.contains r }

/-! ## The steps that do not know their target -/

def aforget (prot : List Nat) (r : Nat) : AM Unit := fun A => some ((), AS.forgetK prot r A)

/-- `(zp),Y` with the pointer not known: the bytes of the pointer are read -/
def aIzyT (E : Env) : AM Unit := do
  let z ← afetch E
  let _ ← ard16zp E z
  let _ ← (get : AM AS)
  pure ()

/-- the same, when the instruction may take a cycle more -/
def aIzyRT (E : Env) : AM Unit := do
  let z ← afetch E
  let _ ← ard16zp E z
  let _ ← (get : AM AS)
  atick 0 1
  pure ()

/-- `ADC` of a known byte with no low bits, with the carry clear: the high bits of the sum come from the high bits of `A` -/
def aadcH (v : AB) : AM Unit := fun A =>
  if v.isK && v.v &&& 0x0F == 0 && (A.p.and (AB.known 1)).isK && (A.p.and (AB.known 1)).v == 0 && A.a.k &&& 0xF0 == 0xF0 then
    some ((), { A with a := ⟨(A.a.v &&& 0xF0) + v.v, 0xF0⟩, p := AB.top })
  else none

/-- an instruction that the walk does not follow with its usual step -/
def customOf (prot : List Nat) (E : Env) (A : AS) (op : UInt8) : Option (AM Unit) :=
  let zx := aZpi E (·.x)
  let ax := aAbi E (·.x)
  let ay := aAbi E (·.y)
  let f := aforget prot E.rkI
  let unkP := fun (z : UInt8) => !((A.getK z.toNat).isK && (A.getK (z + 1).toNat).isK)
  let z1 := E.prg.get! ((A.pc + 1) &&& E.mask).toNat
  if op == 0x95 || op == 0x94 then if A.x.isK then none else some (zx >>= fun _ => f)
  else if op == 0xD6 then if A.x.isK then none else some (zx >>= fun _ => adecV AB.top >>= fun _ => f)
  else if op == 0xF6 then if A.x.isK then none else some (zx >>= fun _ => aincV AB.top >>= fun _ => f)
  else if op == 0x9D then if A.x.isK then none else some (ax >>= fun _ => f)
  else if op == 0xDE then if A.x.isK then none else some (ax >>= fun _ => adecV AB.top >>= fun _ => f)
  else if op == 0xFE then if A.x.isK then none else some (ax >>= fun _ => aincV AB.top >>= fun _ => f)
  else if op == 0x7E then if A.x.isK then none else some (ax >>= fun _ => arorV AB.top >>= fun _ => f)
  else if op == 0x99 then if A.y.isK then none else some (ay >>= fun _ => f)
  else if op == 0x91 then if A.y.isK && !unkP z1 then none else some (aIzyT E >>= fun _ => f)
  else if op == 0xB1 then if unkP z1 then some (aIzyRT E >>= fun _ => asetA AB.top) else none
  else if op == 0x79 then
    if A.y.isK && !A.a.isK && A.a.k &&& 0xF0 == 0xF0 then some (aAbiR E (·.y) >>= fun ad => ard E ad >>= aadcH) else none
  else none

/-- the abstract successors -/
def gsucc (G : Guard) (E : Env) (ops : Array (AM Unit)) (A : AS) : List (Option AS) :=
  if A.nmi || decide (A.pc < 0x8000) then succs E ops A
  else
    let op := E.prg.get! (A.pc &&& E.mask).toNat
    match customOf G.prot E A op with
    | none => succs E ops A
    | some af => [((af >>= fun _ => atick (cycOf op) (cycOf op)) { A with pc := A.pc + 1 }).map (·.2)]

/-! ## The pieces -/

/-- the time, by `Clean.time` -/
def capT (G : Guard) (A : AS) : AS :=
  if A.pc != G.idle && decide (G.late < A.hi) then { A with hi := G.late } else A

/-- at the jump: one piece for each entry of the table -/
def jumpP (G : Guard) (A : AS) : List AS :=
  if A.pc == G.je && !A.a.isK then
    match ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | some r =>
      match G.jumps.lookup (r + 1).toNat with
      | some n => (List.range n).map fun i => { A with a := AB.known i.toUInt8 }
      | none => [A]
    | none => [A]
  else [A]

/-- at the start of the foot check: the vertical position by its top bits, as far as the check's `CMP` needs -/
def footP (G : Guard) (A : AS) : List AS :=
  (splitBit G.yI 128 A).flatMap fun B =>
    if (B.getK G.yI).v &&& 128 == 0 then [B]
    else (splitBit G.yI 64 B).flatMap fun C =>
      if (C.getK G.yI).v &&& 64 == 0 then [C]
      else (splitBit G.yI 32 C).flatMap (splitBit G.yI 16)

/-- where the block buffer routine loads the vertical position for the right foot: its high bits -/
def highP (G : Guard) (A : AS) : List AS :=
  (splitBit G.yI 128 A).flatMap fun B => (splitBit G.yI 64 B).flatMap fun C => (splitBit G.yI 32 C).flatMap (splitBit G.yI 16)

/-- the RAM index a read takes, if the pointer and `Y` are known -/
def readI (P : Spots) (A : AS) : Nat := ((ptrAt P A + A.y.v.toUInt16) &&& 0x7FF).toNat

/-- this byte is in the block buffers, and it is not the tile's place unless the tile cannot be there yet -/
def safeI (P : Spots) (i : Nat) (pa : AB) : Bool :=
  decide (pa.maxv.toNat ≤ P.pg) && decide (P.bufLo ≤ i) && decide (i < P.bufLo + P.bufBytes) && (i != P.dR || decide (pa.maxv.toNat + 1 < P.pg))

/-- the pieces for the pass -/
def zoneP (G : Guard) (A : AS) : List AS :=
  let P := G.P
  if A.pc == P.foot then footP G A
  else if A.pc == G.loadY then
    if (A.getK P.saveI).isK && P.idx2.contains (A.getK P.saveI).v then highP G A else [A]
  else if A.pc == P.entry && A.y.isK && P.idx2.contains A.y.v then
    (List.range P.left).map fun n => (A.setK P.xI (AB.known (n % 256).toUInt8)).setK P.pI (AB.known (n / 256).toUInt8)
  else if A.pc == P.read then
    if (A.getK P.saveI).isK && P.idx2.contains (A.getK P.saveI).v && (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && A.y.isK && safeI P (readI P A) (A.getK P.pI) then
      bitList.map fun b => A.setK (readI P A) (neBit P.tile b)
    else [A]
  else [A]

/-- all the pieces before a step -/
def preG (G : Guard) (A : AS) : List AS := (jumpP G (capT G A)).flatMap (zoneP G)

/-! ## The walk -/

/-- the routine byte is not the pipe's -/
def okRt (G : Guard) (B : AS) : Bool :=
  let b := B.getK G.rtI
  G.ev &&& b.k != b.v &&& b.k

/-- inside the collision routine: its return address is on the stack -/
def inZone (G : Guard) (A : AS) : Bool :=
  let i := 0x100 + G.P.stack.toNat
  decide (A.s.toNat ≤ G.P.stack.toNat) && (let a := A.getK (i + 1); let b := A.getK (i + 2); a.isK && a.v == G.zLo && b.isK && b.v == G.zHi)

/-- once the routine byte has another known value, only one bit that differs from the pipe's stays known: no part of the proof -/
def normRt (G : Guard) (A : AS) : AS :=
  let b := A.getK G.rtI
  match G.known.head? with
  | some (_, r0) =>
    if b.isK && b.v != r0 then
      let d := b.v ^^^ G.ev
      let bit : UInt8 := if d &&& 1 != 0 then 1 else if d &&& 2 != 0 then 2 else if d &&& 4 != 0 then 4 else if d &&& 8 != 0 then 8 else if d &&& 16 != 0 then 16 else if d &&& 32 != 0 then 32 else if d &&& 64 != 0 then 64 else 128
      A.setK G.rtI ⟨b.v &&& bit, bit⟩
    else A
  | none => A

/-- what the search forgets: no part of the proof -/
def normG (G : Guard) (A0 : AS) : AS :=
  let P := G.P
  let A := normRt G { A0 with padShift := AB.top }
  if !inZone G A then
    if G.je ≤ A.pc && A.pc ≤ G.je + 18 then A else
    let B := AS.forgetW G.prot A
    let kn := (List.range (0x100 + A.s.toNat + 1 - G.stackLo)).foldl (fun k j => k.set! (G.stackLo + j) 0) B.kn
    { B with kn }
  else if P.exits.contains A.pc || A.pc == P.foot then { AS.forgetW G.prot A with a := AB.top, x := AB.top, y := AB.top, p := AB.top }
  else if A.pc == P.afterSum then
    if (A.getK P.xI).isK then
      { (forget [P.xI] A).setK P.sumI ⟨(A.getK P.sumI).v, (A.getK P.sumI).k &&& 0xF0⟩ with a := AB.top }
    else A
  else if A.pc == P.entry then { A with p := AB.top }
  else if A.pc == P.read then
    let sv := A.getK P.saveI
    if sv.isK && P.idx2.contains sv.v then
      let C := forget [P.xI, G.yI] A
      if (A.getK P.ptrI).isK && (A.getK (P.ptrI + 1)).isK && readI P A != P.dR then
        C.setK P.pI ((List.range (P.pg + 1)).foldl (fun b n => b.join (AB.known n.toUInt8)) (AB.known 0))
      else C
    else A
  else if A.pc == P.read + 2 then
    let sv := A.getK P.saveI
    if sv.isK && P.idx2.contains sv.v then { AS.forgetW G.prot A with y := AB.top }
    else { forget [P.ptrI, P.ptrI + 1] A with y := AB.top }
  else A

/-- states with the same key are joined: no part of the proof. The low bits of the number vary, for the hash table. -/
def keyG (G : Guard) (A : AS) : Nat :=
  let P := G.P
  let num := fun (b : AB) => b.k.toNat * 256 + (b.v &&& b.k).toNat
  let n := num (A.getK G.rtI)
  let n := n * 16 + (if A.nmi then 1 else 0) + (if A.vb then 2 else 0) + (if A.strobe then 4 else 0) + (if A.lo == 0 then 8 else 0)
  let n :=
    if inZone G A then
      let n := n * 65536 + num A.x
      let n := n * 65536 + num A.y
      let n := n * 65536 + num A.a
      let n := n * 65536 + num (A.p.and (AB.known 1))
      (G.yI :: keepR P).foldl (fun n i => n * 65536 + num (A.getK i)) n
    else if G.je ≤ A.pc && A.pc ≤ G.je + 18 then
      let n := n * 65536 + num A.a
      n * 65536 + num A.y
    else n
  let n := n * 16777216 + A.s.toNat * 65536 + A.pc.toNat
  n * 18446744073709551616 + (n % 4294967291) * 4294967296 + stackHash A

/-- the bytes of which some bit is known -/
def knownOf (A : AS) : List Nat := (List.range 2048).filter fun i => A.kn.get! i != 0

/-- `AS.le`, looking only at the bytes in `l` -/
def leK (a b : AS) (l : List Nat) : Bool :=
  a.pc == b.pc && a.s == b.s && a.k == b.k && a.vb == b.vb && a.nmi == b.nmi && a.padShift.le b.padShift && a.strobe == b.strobe &&
  a.a.le b.a && a.x.le b.x && a.y.le b.y && a.p.le b.p && a.ppuCtrl.le b.ppuCtrl && a.ppuMask.le b.ppuMask &&
  decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi) && decide (b.hi < dotsPerFrame) && (!b.dg || a.dg) &&
  b.ram.size == 2048 && b.kn.size == 2048 && l.all (fun i => (a.getK i).le (b.getK i)) && a.rk == b.rk && a.spent == b.spent

/-- the table -/
structure CfgG where
  E : Env
  ops : Array (AM Unit)
  G : Guard
  t : Array AS
  kl : Array (List Nat)
  idx : Std.HashMap Nat Nat
  cut : ByteArray

def coverG (C : CfgG) (B : AS) : Bool :=
  match C.idx[keyG C.G (if inZone C.G B then normG C.G B else normRt C.G B)]? with
  | some i =>
    match C.t[i]?, C.kl[i]? with
    | some D, some l => leK B D l
    | _, _ => false
  | none => false

/-- from `A`, step by step until every path ends at the frame's end or in a state of the table. Everywhere the routine byte is not the pipe's. -/
def walkG (C : CfgG) : Nat → AS → Bool
  | 0, _ => false
  | n + 1, A => (preG C.G A).all fun A₁ => (gsucc C.G C.E C.ops A₁).all fun r =>
    match r with
    | none => false
    | some B => okRt C.G B && (B.k != A.k || (C.cut.get! B.pc.toNat != 0 && coverG C B) || walkG C n B)

/-! ## Finding the table: a search, no part of the proof -/

/-- `AS.join`, looking only at the bytes in `l`: every other byte of `a` is not known -/
def joinK (a b : AS) (l : List Nat) : AS := Id.run do
  let mut ram := a.ram
  let mut kn := a.kn
  for i in l do
    let x : AB := ⟨ram.get! i, kn.get! i⟩
    let y : AB := ⟨b.ram.get! i, b.kn.get! i⟩
    let z := x.join y
    if z.k != x.k || z.v != x.v then
      ram := ram.set! i z.v
      kn := kn.set! i z.k
  return { a with
    ram, kn, a := a.a.join b.a, x := a.x.join b.x, y := a.y.join b.y, p := a.p.join b.p,
    ppuCtrl := a.ppuCtrl.join b.ppuCtrl, ppuMask := a.ppuMask.join b.ppuMask,
    lo := Nat.min a.lo b.lo, hi := Nat.max a.hi b.hi, dg := a.dg && b.dg }

structure SG where
  pending : Std.TreeMap Nat AS compare := {}
  done : Std.HashMap Nat (AS × Option (List Nat)) := {}
  multi : Std.HashMap Nat Unit := {}
  /-- how many times a key was joined -/
  arr : Std.HashMap Nat Nat := {}
  leaders : Std.HashMap Nat Unit := {}
  steps : Nat := 0
  forks : Nat := 0
  fails : Nat := 0
  firstFail : Option AS := none
  failPcs : Std.HashMap Nat Nat := {}

def isCutPc (P : Spots) (pc : UInt16) : Bool :=
  pc == P.read || pc == P.read + 2 || pc == P.afterSum || pc == P.foot || P.exits.contains pc

def routeG (G : Guard) (X : SG) (B0 : AS) : SG :=
  let B := normG G B0
  let K := keyG G B
  let X := if isCutPc G.P B.pc then { X with multi := X.multi.insert K () } else X
  match X.pending[K]? with
  | some Q =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      let J := joinK Q B l
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K () }
    | none => X
  | none =>
    match X.done[K]? with
    | some (D, l0) =>
      let l := l0.getD (knownOf D)
      if leK B D l then { X with multi := X.multi.insert K (), done := X.done.insert K (D, some l) } else
      let J0 := joinK D B l
      let c := X.arr.getD K 0
      let J := if c < 2 || G.late < J0.hi || J0.pc == G.idle || J0.vb then J0 else { J0 with hi := G.late }
      let l' := l.filter fun i => J.kn.get! i != 0
      { X with pending := X.pending.insert K J, done := X.done.insert K (J, some l'), multi := X.multi.insert K (), arr := X.arr.insert K (c + 1) }
    | none => { X with pending := X.pending.insert K B, done := X.done.insert K (B, none) }

partial def runG (G : Guard) (E : Env) (ops : Array (AM Unit)) (X0 : SG) (A0 : AS) : SG := Id.run do
  let mut X := X0
  let mut cur := A0
  let mut run := 0
  while true do
    let rs := (preG G cur).flatMap (gsucc G E ops)
    X := { X with steps := X.steps + rs.length, forks := X.forks + (rs.length - 1) }
    let bad := rs.any fun r => match r with
      | none => true
      | some B => !okRt G B
    if bad then
      X := { X with fails := X.fails + 1, firstFail := X.firstFail <|> some cur, failPcs := X.failPcs.insert cur.pc.toNat (X.failPcs.getD cur.pc.toNat 0 + 1) }
    let good := (rs.filterMap id).filter fun b => b.k == cur.k
    match good with
    | [b] =>
      if (X.leaders[b.pc.toNat]?).isNone && run < 64 && !isCutPc G.P b.pc && b.pc != G.je &&
          (b.pc.toNat == cur.pc.toNat + 1 || b.pc.toNat == cur.pc.toNat + 2 || b.pc.toNat == cur.pc.toNat + 3) then
        cur := b
        run := run + 1
        continue
      else pure ()
    | _ => pure ()
    for b in good do
      X := { X with leaders := X.leaders.insert b.pc.toNat () }
      X := routeG G X b
    break
  return X

partial def searchG (G : Guard) (E : Env) (ops : Array (AM Unit)) (X0 : SG) : SG := Id.run do
  let mut X := X0
  while true do
    match X.pending.minEntry? with
    | none => break
    | some (key, A) =>
      X := { X with pending := X.pending.erase key }
      X := runG G E ops X A
  return X

/-- the abstract state when the frame starts -/
def startG (G : Guard) (late : Bool) : AS :=
  { a := AB.top, x := AB.top, y := AB.top, s := G.s0, p := AB.top, pc := G.idle,
    ram := G.known.foldl (fun r p => r.set! p.1 p.2) zeros,
    kn := G.known.foldl (fun r p => r.set! p.1 0xFF) zeros,
    ppuCtrl := ⟨0x80, 0x80⟩, ppuMask := AB.top, vb := late, nmi := late, lo := if late then 1 else 0, hi := if late then 9 else 0, padShift := AB.top, strobe := false, dg := false, k := 0 }

def searchOf (G : Guard) (E : Env) : SG :=
  let ops := (aRows E).toArray
  searchG G E ops ([startG G false, startG G true].foldl (routeG G) {})

/-- the table, from the search -/
def tableOfS (X : SG) : Array AS × Std.HashMap Nat Nat × ByteArray := Id.run do
  let mut t : Array AS := #[]
  let mut idx : Std.HashMap Nat Nat := {}
  let mut cut := ByteArray.mk (Array.replicate 65536 0)
  for (k, _) in X.multi.toList do
    match X.done[k]? with
    | some (A, _) =>
      idx := idx.insert k t.size
      cut := cut.set! A.pc.toNat 1
      t := t.push A
    | none => pure ()
  return (t, idx, cut)

def cfgOf (G : Guard) (E : Env) : CfgG :=
  let q := tableOfS (searchOf G E)
  { E, ops := (aRows E).toArray, G, t := q.1, kl := q.1.map knownOf, idx := q.2.1, cut := q.2.2 }

/-- the fuel of a walk -/
def fuelG : Nat := 20000

/-- **The check.** -/
def frameCheck (G : Guard) (E : Env) : Bool :=
  let C := cfgOf G E
  decide (G.rtI < 2048) && decide (G.yI < 2048) && decide (G.P.xI < 2048) && decide (G.P.pI < 2048) && decide (G.P.ptrI < 2048) && decide (G.P.saveI < 2048) &&
  decide (G.late < dotsPerFrame) && okRt G (startG G false) && okRt G (startG G true) &&
  C.t.all (walkG C fuelG) && walkG C fuelG (startG G false) && walkG C fuelG (startG G true)

/-- the number of entries of the table at `t`: the words go on while they point into the ROM, up to the first word that is itself the target of an entry before it -/
def tableLen (m0 : Machine) (t : UInt16) : Nat :=
  let rec go (fuel : Nat) (k : Nat) (seen : List UInt16) : Nat :=
    match fuel with
    | 0 => k
    | fuel + 1 =>
      let here := t + (2 * k).toUInt16
      let w := (romByte m0 here).toUInt16 ||| ((romByte m0 (here + 1)).toUInt16 <<< 8)
      if seen.contains here || w < 0x8000 then k else go fuel (k + 1) (w :: seen)
  go 128 0 []

/-- the jump tables: each comes after a `JSR` of the jump routine -/
def jumpTables (m0 : Machine) (je : UInt16) : List (Nat × Nat) :=
  (List.range 32765).filterMap fun i =>
    let a := (0x8000 + i).toUInt16
    if romByte m0 a == 0x20 && romByte m0 (a + 1) == je.toUInt8 && romByte m0 (a + 2) == (je >>> 8).toUInt8 then
      some ((a + 3).toNat, tableLen m0 (a + 3))
    else none

/-- the check on the ROM -/
def guardOf (sy : Syms) (m0 : Machine) : Guard :=
  let P := spots sy m0
  let f := firstAt sy.DoFootCheck 100000 { m0 with pad := 0x01 }
  let i := 0x100 + P.stack.toNat
  { P
    rtI := (sy.GameEngineSubroutine &&& 0x7FF).toNat
    ev := vp sy
    known := [((sy.GameEngineSubroutine &&& 0x7FF).toNat, sy.Eng_PlayerCtrl.toUInt8), ((sy.OperMode &&& 0x7FF).toNat, sy.GameModeValue.toUInt8), ((sy.OperMode_Task &&& 0x7FF).toNat, sy.Task_GameCore.toUInt8)]
    prot := (sy.GameEngineSubroutine &&& 0x7FF).toNat :: (sy.OperMode &&& 0x7FF).toNat :: (sy.OperMode_Task &&& 0x7FF).toNat :: P.adI :: (List.range (0x200 - (i - 32))).map (i - 32 + ·)
    je := sy.JumpEngine
    jumps := jumpTables m0 sy.JumpEngine
    idle := sy.EndlessLoop
    s0 := m0.s
    stackLo := i - 32
    late := dotsPerFrame - 64
    yI := (sy.Player_Y_Position &&& 0x7FF).toNat
    loadY := findOp m0 (findOp m0 sy.BlockBufferCollision 0x20 64) 0xB5 64
    zLo := match f with
      | some m => m.ram.get! (i + 1)
      | none => 0
    zHi := match f with
      | some m => m.ram.get! (i + 2)
      | none => 0 }

def ruleCheckG (sy : Syms) (m0 : Machine) : Bool := frameCheck (guardOf sy m0) (envOf m0)

/-! ## Forgetting follows the machine -/

section
variable {E : Env} {F : Nat × UInt8}

theorem keepKn_size (prot : List Nat) (kn : ByteArray) : (keepKn prot kn).size = 2048 := by
  unfold keepKn
  have key : ∀ (l : List Nat) (k : ByteArray), k.size = 2048 → (l.foldl (fun k i => k.set! i (kn.get! i)) k).size = 2048 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a l ih =>
      intro k h
      exact ih _ (by rw [ba_size_set]; exact h)
  exact key prot zeros (zeros_size 2048)

/-- a byte outside `prot` has no known bit; a byte in it has its known bits or none -/
theorem keepKn_get (prot : List Nat) (kn : ByteArray) (i : Nat) :
    (i ∉ prot → (keepKn prot kn).get! i = 0) ∧ ((keepKn prot kn).get! i = kn.get! i ∨ (keepKn prot kn).get! i = 0) := by
  unfold keepKn
  have key : ∀ (l : List Nat) (k : ByteArray), (k.get! i = kn.get! i ∨ k.get! i = 0) →
      (i ∉ l → (l.foldl (fun k j => k.set! j (kn.get! j)) k).get! i = k.get! i) ∧
      ((l.foldl (fun k j => k.set! j (kn.get! j)) k).get! i = kn.get! i ∨ (l.foldl (fun k j => k.set! j (kn.get! j)) k).get! i = 0) := by
    intro l
    induction l with
    | nil =>
      intro k h
      exact ⟨fun _ => rfl, h⟩
    | cons a l ih =>
      intro k h
      simp only [List.foldl_cons]
      by_cases hai : a = i
      · subst hai
        have hk : (k.set! a (kn.get! a)).get! a = kn.get! a ∨ (k.set! a (kn.get! a)).get! a = k.get! a := by
          by_cases hs : a < k.size
          · exact Or.inl (ba_get_set_self _ _ _ hs)
          · right
            cases k with
            | mk d =>
              simp only [ByteArray.size] at hs
              simp [ByteArray.set!, ByteArray.get!, hs]
        refine ⟨fun hn => absurd List.mem_cons_self hn, (ih _ ?_).2⟩
        rcases hk with hk | hk
        · exact Or.inl hk
        · rw [hk]
          exact h
      · have hk : (k.set! a (kn.get! a)).get! i = k.get! i := ba_get_set_ne _ _ _ _ hai
        have h2 := ih (k.set! a (kn.get! a)) (by rw [hk]; exact h)
        refine ⟨fun hn => ?_, h2.2⟩
        rw [h2.1 (fun hl => hn (List.mem_cons_of_mem _ hl)), hk]
  have h0 : zeros.get! i = 0 := zeros_get 2048 i
  have h := key prot zeros (Or.inr h0)
  exact ⟨fun hn => by rw [h.1 hn]; exact h0, h.2⟩

theorem mem_of_k0 {b : AB} {x : UInt8} (hk : b.k = 0) : b.mem x := by
  show x &&& b.k = b.v &&& b.k
  rw [hk]
  apply bt_ext
  intro j hj
  rw [bt_and, bt_and, bt_zero hj, Bool.and_false, Bool.and_false]

/-- the same value, or a byte with no known bit: still a member -/
theorem sim_forgetW {prot : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E F (AS.forgetW prot A) m := by
  refine { hs with
    ram := ?_
    dg := ?_
    szK := keepKn_size _ _
    rkv := ?_ }
  · intro i hi
    show AB.mem ⟨A.ram.get! i, (keepKn prot A.kn).get! i⟩ (m.ram.get! i)
    rcases (keepKn_get prot A.kn i).2 with h | h
    · rw [h]
      exact hs.ram i hi
    · exact mem_of_k0 h
  · intro h
    cases h
  · intro h
    cases h

/-- a write outside `prot`: the state with only `prot` known follows -/
theorem sim_forget_write {prot : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) {d : Nat} (hd : d ∉ prot) (v : UInt8) :
    Sim E F (AS.forgetW prot A) { m with ram := m.ram.set! d v } := by
  have h0 := sim_forgetW (prot := prot) hs
  refine { h0 with
    size := ?_
    ram := ?_
    dg := ?_
    rkv := ?_ }
  · show (m.ram.set! d v).size = 2048
    rw [ba_size_set]
    exact hs.size
  · intro i hi
    show AB.mem ⟨A.ram.get! i, (keepKn prot A.kn).get! i⟩ ((m.ram.set! d v).get! i)
    by_cases hdi : d = i
    · subst hdi
      exact mem_of_k0 ((keepKn_get prot A.kn d).1 hd)
    · rw [ba_get_set_ne _ _ _ _ hdi]
      exact h0.ram i hi
  · intro h
    cases h
  · intro h
    cases h

/-- forgetting with the counter kept -/
theorem sim_forgetK {prot : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) : Sim E F (AS.forgetK prot E.rkI A) m := by
  have h0 := sim_forgetW (prot := prot) hs
  refine { h0 with rkv := ?_ }
  intro h
  have h1 : A.rk = true := by
    simp only [AS.forgetK, Bool.and_eq_true] at h
    exact h.1
  exact hs.rkv h1

/-- a write outside `prot`, with the counter kept if it is in `prot` -/
theorem sim_forget_writeK {prot : List Nat} {A : AS} {m : Machine} (hs : Sim E F A m) {d : Nat} (hd : d ∉ prot) (v : UInt8) :
    Sim E F (AS.forgetK prot E.rkI A) { m with ram := m.ram.set! d v } := by
  have h0 := sim_forget_write (prot := prot) hs hd v
  refine { h0 with rkv := ?_ }
  intro h
  simp only [AS.forgetK, Bool.and_eq_true] at h
  have hm : E.rkI ∈ prot := by simpa using h.2
  have hne : d ≠ E.rkI := fun e => hd (e ▸ hm)
  show (m.ram.set! d v).get! E.rkI = _
  rw [ba_get_set_ne _ _ _ _ hne]
  exact hs.rkv h.1

/-! ## A store with a target not known -/

theorem rd_plain {prot : List Nat} {t : UInt16} {m : Machine} (ht : Plain prot t) (hk : m.trk = false) : (go (rd t) m).2 = m := by
  rcases ht with ⟨h1, _⟩ | ⟨h1, h2, h3⟩
  · rw [rd_ram h1 hk]
  · have a1 : ¬ t < 0x2000 := by
      intro h
      have b1 := UInt16.lt_iff_toNat_lt.1 h
      have b2 := UInt16.le_iff_toNat_le.1 h1
      revert b1 b2
      simp <;> omega
    by_cases a2 : t ≥ 0x8000
    · rw [rd_rom _ a1 a2]
    · have a3 : ¬ t < 0x4000 := by
        intro h
        have b1 := UInt16.lt_iff_toNat_lt.1 h
        have b2 := UInt16.le_iff_toNat_le.1 h1
        revert b1 b2
        simp <;> omega
      have a4 : ¬ (t == 0x4016) = true := by simpa using h3
      by_cases a5 : (t == 0x4017) = true
      · rw [rd_17 _ a1 a2 a3 a4 a5]
      · rw [rd_else _ a1 a2 a3 a4 a5]

theorem wr_plain {prot : List Nat} {t : UInt16} {x : UInt8} {A : AS} {m : Machine} (ht : Plain prot t) (hs : Sim E F A m) :
    Sim E F (AS.forgetK prot E.rkI A) (go (wr t x) m).2 ∧ (go (wr t x) m).2.frame = m.frame ∧ (go (wr t x) m).2.fdot = m.fdot := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [wr_ram x h1 hs.trk]
    exact ⟨sim_forget_writeK hs h2 x, rfl, rfl⟩
  · have a1 : ¬ t < 0x2000 := by
      intro h
      have b1 := UInt16.lt_iff_toNat_lt.1 h
      have b2 := UInt16.le_iff_toNat_le.1 h1
      revert b1 b2
      simp <;> omega
    have a2 : ¬ t < 0x4000 := by
      intro h
      have b1 := UInt16.lt_iff_toNat_lt.1 h
      have b2 := UInt16.le_iff_toNat_le.1 h1
      revert b1 b2
      simp <;> omega
    have e : go (wr t x) m = ((), m) := by
      unfold wr go
      rw [if_neg a1, if_neg a2, if_neg (by simpa using h2), if_neg (by simpa using h3)]
      rfl
    rw [e]
    exact ⟨sim_forgetK hs, rfl, rfl⟩

/-- `md`, then a store of a value of the machine -/
theorem w_store {α : Type} {R : α → UInt16 → Prop} {prot : List Nat} {amd : AM α} {md : Mode} (hmd : Snd E F R amd md) (val : Machine → UInt8) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hp : Plain prot (go md m).1) {u : Unit} {B : AS} (he : (amd >>= fun _ => aforget prot E.rkI) A = some (u, B)) :
    Sim E F B (go (md >>= fun ad => (get : M Machine) >>= fun n => wr ad (val n)) m).2 ∧ Adv m (go (md >>= fun ad => (get : M Machine) >>= fun n => wr ad (val n)) m).2 := by
  obtain ⟨a, A2, h1, h2⟩ := abind_some he
  obtain ⟨_, h3, h4⟩ := hmd A m hs a A2 h1
  obtain ⟨rfl, rfl⟩ := some_pair h2
  have e : go (md >>= fun ad => (get : M Machine) >>= fun n => wr ad (val n)) m = go (wr (go md m).1 (val (go md m).2)) (go md m).2 := rfl
  rw [e]
  obtain ⟨g1, g2, g3⟩ := wr_plain (x := val (go md m).2) hp h3
  refine ⟨g1, ?_⟩
  exact h4.tr ⟨g2, Nat.le_of_eq g3.symm⟩

/-- `md`, then a change of the byte -/
theorem w_rmw {α : Type} {R : α → UInt16 → Prop} {prot : List Nat} {amd : AM α} {md : Mode} {af : AB → AM AB} {f : UInt8 → M UInt8} (hmd : Snd E F R amd md)
    (hf : ∀ v x, v.mem x → Snd E F AB.mem (af v) (f x)) {A : AS} {m : Machine} (hs : Sim E F A m)
    (hp : Plain prot (go md m).1) {u : Unit} {B : AS} (he : (amd >>= fun _ => af AB.top >>= fun _ => aforget prot E.rkI) A = some (u, B)) :
    Sim E F B (go (rmw f md) m).2 ∧ Adv m (go (rmw f md) m).2 := by
  obtain ⟨a, A2, h1, h2⟩ := abind_some he
  obtain ⟨_, h3, h4⟩ := hmd A m hs a A2 h1
  obtain ⟨b, A3, h5, h6⟩ := abind_some h2
  obtain ⟨rfl, rfl⟩ := some_pair h6
  have e1 : (go (rd (go md m).1) (go md m).2).2 = (go md m).2 := rd_plain hp h3.trk
  have e : go (rmw f md) m = go (f (go (rd (go md m).1) (go md m).2).1 >>= fun r => wr (go md m).1 r) (go (rd (go md m).1) (go md m).2).2 := rfl
  rw [e, e1]
  obtain ⟨_, h7, h8⟩ := hf AB.top _ (mem_top _) A2 _ h3 b A3 h5
  have e2 := PipeTransitionAll.go_bind (f := f (go (rd (go md m).1) (go md m).2).1) (g := fun r => wr (go md m).1 r) (go md m).2
  rw [e2]
  obtain ⟨g1, g2, g3⟩ := wr_plain (x := (go (f (go (rd (go md m).1) (go md m).2).1) (go md m).2).1) hp h7
  refine ⟨g1, ?_⟩
  exact (h4.tr h8).tr ⟨g2, Nat.le_of_eq g3.symm⟩

theorem s_izyT : Snd E F (fun (_ : Unit) (_ : UInt16) => True) (aIzyT E) mIzy :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    exact Snd.bind (s_rd16zp _) fun _ _ _ => Snd.get fun _ _ _ => Snd.pure trivial

theorem s_izyRT : Snd E F (fun (_ : Unit) (_ : UInt16) => True) (aIzyRT E) mIzyR :=
  Snd.bind s_fetch fun _ _ h => by
    subst h
    refine Snd.bind (s_rd16zp _) fun _ _ _ => Snd.get fun _ _ _ => ?_
    have hp : ∀ b e : UInt16, Snd E F TT (atick 0 1) (pagePenalty b e) := by
      intro b e
      unfold pagePenalty
      split
      · exact s_tick (Nat.zero_le _) (Nat.le_refl _)
      · exact s_tick0
    exact Snd.bind (hp _ _) fun _ _ _ => Snd.pure trivial

/-- `LDA (zp),Y` with a pointer not known -/
theorem w_read {A : AS} {m : Machine} (hs : Sim E F A m) (hp : (go mIzyR m).1 < 0x2000 ∨ 0x8000 ≤ (go mIzyR m).1) {u : Unit} {B : AS}
    (he : (aIzyRT E >>= fun _ => asetA AB.top) A = some (u, B)) :
    Sim E F B (go (opLDA mIzyR) m).2 ∧ Adv m (go (opLDA mIzyR) m).2 := by
  obtain ⟨a, A2, h1, h2⟩ := abind_some he
  obtain ⟨_, h3, h4⟩ := s_izyRT A m hs a A2 h1
  have e1 : (go (rd (go mIzyR m).1) (go mIzyR m).2).2 = (go mIzyR m).2 := (rd_ramrom h3 hp).2
  have e : go (opLDA mIzyR) m = go (setA (go (rd (go mIzyR m).1) (go mIzyR m).2).1) (go (rd (go mIzyR m).1) (go mIzyR m).2).2 := rfl
  rw [e, e1]
  obtain ⟨_, h5, h6⟩ := s_setA (E := E) (F := F) (mem_top _) A2 _ h3 u B h2
  exact ⟨h5, h4.tr h6⟩

end

/-! ## A step that may not know its target -/

section
variable {E : Env} {F : Nat × UInt8}

set_option maxRecDepth 100000 in
/-- the opcodes the walk treats itself, in the table of the machine -/
theorem op_95 : opTable[(0x95 : UInt8).toNat]?.getD opJAM = opSTA mZpx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_94 : opTable[(0x94 : UInt8).toNat]?.getD opJAM = opSTY mZpx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_D6 : opTable[(0xD6 : UInt8).toNat]?.getD opJAM = opDEC mZpx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_F6 : opTable[(0xF6 : UInt8).toNat]?.getD opJAM = opINC mZpx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_9D : opTable[(0x9D : UInt8).toNat]?.getD opJAM = opSTA mAbx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_DE : opTable[(0xDE : UInt8).toNat]?.getD opJAM = opDEC mAbx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_FE : opTable[(0xFE : UInt8).toNat]?.getD opJAM = opINC mAbx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_7E : opTable[(0x7E : UInt8).toNat]?.getD opJAM = opROR mAbx := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_99 : opTable[(0x99 : UInt8).toNat]?.getD opJAM = opSTA mAby := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_91 : opTable[(0x91 : UInt8).toNat]?.getD opJAM = opSTA mIzy := by rw [PipeTransitionAll.opTable_eq]; rfl
set_option maxRecDepth 100000 in
theorem op_B1 : opTable[(0xB1 : UInt8).toNat]?.getD opJAM = opLDA mIzyR := by rw [PipeTransitionAll.opTable_eq]; rfl

set_option maxRecDepth 100000 in
theorem op_79 : opTable[(0x79 : UInt8).toNat]?.getD opJAM = opADC mAbyR := by rw [PipeTransitionAll.opTable_eq]; rfl

set_option maxRecDepth 100000 in
theorem and_F0 : ∀ n : Fin 256, ((n.val.toUInt8) &&& 0xF0).toNat = n.val / 16 * 16 := by decide

set_option maxRecDepth 100000 in
theorem and_0F : ∀ n : Fin 256, ((n.val.toUInt8) &&& 0x0F).toNat = n.val % 16 := by decide

theorem and_F0' (y : UInt8) : (y &&& 0xF0).toNat = y.toNat / 16 * 16 := by
  have h := and_F0 ⟨y.toNat, y.toNat_lt⟩
  simpa using h

/-- the high bits of a sum, when the second byte has no low bits -/
theorem add_high {a b x : UInt8} (hab : a &&& 0xF0 = b &&& 0xF0) (hx : x &&& 0x0F = 0) : (a + x) &&& 0xF0 = ((b &&& 0xF0) + x) &&& 0xF0 := by
  have h1 := and_F0' a
  have h2 := and_F0' b
  have h3 : x.toNat % 16 = 0 := by
    have h : ((x.toNat.toUInt8) &&& 0x0F).toNat = x.toNat % 16 := and_0F ⟨x.toNat, x.toNat_lt⟩
    have e' : x.toNat.toUInt8 = x := by simp
    rw [e', hx] at h
    simpa using h.symm
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hxl := x.toNat_lt
  have h5 : (a &&& 0xF0).toNat = (b &&& 0xF0).toNat := by rw [hab]
  rw [h1, h2] at h5
  apply UInt8.toNat_inj.1
  rw [and_F0', and_F0', UInt8.toNat_add, UInt8.toNat_add, h2]
  omega

/-- the sum's high bits -/
theorem s_adcH {v : AB} {x : UInt8} (h : v.mem x) : Snd E F TT (aadcH v) (adc x) := by
  refine snd_leaf fun A m hs a A' he => ?_
  unfold aadcH at he
  split at he
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    obtain ⟨rfl, rfl⟩ := some_pair he
    have hx : x = v.v := TaintRun.isK_eq h1 h
    have hcm : (A.p.and (AB.known 1)).mem (m.p &&& 1) := TaintRun.mem_and hs.p (mem_known_self _)
    have hc0 : m.p &&& 1 = 0 := by
      have := TaintRun.isK_eq h3 hcm
      rw [this, h4]
    have ha1 : m.a &&& 0xF0 = A.a.v &&& 0xF0 := by
      have e := hs.a
      have e2 : (m.a &&& A.a.k) &&& 0xF0 = (A.a.v &&& A.a.k) &&& 0xF0 := by rw [show (m.a &&& A.a.k) = (A.a.v &&& A.a.k) from e]
      rw [UInt8.and_assoc, UInt8.and_assoc, h5] at e2
      exact e2
    refine ⟨trivial, ?_, rfl, rfl⟩
    have hr : (m.a.toUInt16 + x.toUInt16 + (m.p &&& 1).toUInt16).toUInt8 = m.a + x := by
      rw [hc0]
      apply UInt8.toNat_inj.1
      have a1 := m.a.toNat_lt
      have a2 := x.toNat_lt
      simp [UInt8.toNat_add]
    refine { hs with
      a := ?_
      p := mem_top _ }
    show ((m.a.toUInt16 + x.toUInt16 + (m.p &&& 1).toUInt16).toUInt8) &&& 0xF0 = (((A.a.v &&& 0xF0) + v.v) &&& 0xF0)
    rw [hr, ← hx]
    exact add_high ha1 (by rw [hx]; exact h2)
  · cases he

/-- what a step with its own abstract action needs -/
theorem custom_step {A : AS} {m : Machine} {op : UInt8} {af : AM Unit} (hs : Sim E F A m) (hn : A.nmi = false) (hp : 0x8000 ≤ A.pc)
    (hop : E.prg.get! (A.pc &&& E.mask).toNat = op) (hne : op ≠ 0x4C) (hc1 : 1 ≤ cycOf op)
    (hf : ∀ u A₂, af { A with pc := A.pc + 1 } = some (u, A₂) →
      Sim E F A₂ (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2 ∧ Adv { m with pc := m.pc + 1 } (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2)
    (B : AS) (he : ((af >>= fun _ => atick (cycOf op) (cycOf op)) { A with pc := A.pc + 1 }).map (·.2) = some B) :
    Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  have hn2 : m.nmiPending = false := by rw [hs.nmi]; exact hn
  have hpm : m.pc ≥ 0x8000 := by rw [hs.pc]; exact hp
  rw [step_op hn2 hs.halted hpm]
  have hop2 : m.prg.get! (m.pc &&& m.prgMask).toNat = op := by rw [hs.prg, hs.mask, hs.pc]; exact hop
  rw [hop2]
  have hne2 : ¬ (op == 0x4C && m.prg.get! ((m.pc + 1) &&& m.prgMask).toNat == m.pc.toUInt8
      && m.prg.get! ((m.pc + 2) &&& m.prgMask).toNat == (m.pc >>> 8).toUInt8 && decide (m.pc ≥ 0x8000)) = true := by
    simp [hne]
  have hk : stepK m m.pc op = (opTable[op.toNat]?.getD opJAM) >>= fun _ => tick (cycTable.get! op.toNat).toNat := by
    unfold stepK
    exact if_neg hne2
  rw [hk]
  have ee : (cycTable.get! op.toNat).toNat = cycOf op := rfl
  rw [ee]
  cases hE : (af >>= fun _ => atick (cycOf op) (cycOf op)) { A with pc := A.pc + 1 } with
  | none =>
    rw [hE] at he
    cases he
  | some p =>
    rw [hE] at he
    obtain ⟨u, B1⟩ := p
    have hB1 : B1 = B := Option.some.inj he
    subst hB1
    obtain ⟨v, A2, h3, h4⟩ := abind_some hE
    obtain ⟨h5, h6⟩ := hf _ _ h3
    obtain ⟨_, h7, h8⟩ := s_tick (E := E) (F := F) (Nat.le_refl (cycOf op)) (Nat.le_refl (cycOf op)) A2 _ h5 _ _ h4
    have h9 := tick_adv h5 h4
    have e := PipeTransitionAll.go_bind (f := opTable[op.toNat]?.getD opJAM) (g := fun _ => tick (cycOf op)) { m with pc := m.pc + 1 }
    rw [e]
    have hf1 : (go (tick (cycOf op)) (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2).2.frame = m.frame := h8.1.trans h6.1
    refine ⟨h7, steprel_same hs h7 hf1 ?_⟩
    rw [h9]
    have h10 : m.fdot ≤ (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2.fdot := h6.2
    omega

set_option maxRecDepth 100000 in
/-- what `customOf` gives follows the machine -/
theorem custom_ok {G : Guard} {A : AS} {m : Machine} {op : UInt8} {af : AM Unit} (hc : Clean G m) (hs : Sim E F A m)
    (hop : E.prg.get! (A.pc &&& E.mask).toNat = op)
    (h : customOf G.prot E A op = some af) :
    op ≠ 0x4C ∧ 1 ≤ cycOf op ∧ ∀ u A₂, af { A with pc := A.pc + 1 } = some (u, A₂) →
      Sim E F A₂ (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2 ∧ Adv { m with pc := m.pc + 1 } (go (opTable[op.toNat]?.getD opJAM) { m with pc := m.pc + 1 }).2 := by
  have hs1 : Sim E F { A with pc := A.pc + 1 } { m with pc := m.pc + 1 } := { hs with
    pc := by
      show m.pc + 1 = A.pc + 1
      rw [hs.pc] }
  have hat : opAt m = op := by
    show m.prg.get! (m.pc &&& m.prgMask).toNat = op
    rw [hs.prg, hs.mask, hs.pc]
    exact hop
  have hst := hc.store
  rw [hat] at hst
  have hrd := hc.read
  rw [hat] at hrd
  unfold customOf at h
  simp only at h
  by_cases o1 : op = 0x95
  · subst o1
    have : (if A.x.isK = true then none else some (aZpi E (·.x) >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_95]
      exact w_store s_mZpx (·.a) hs1 (hst _ rfl) he
  by_cases o2 : op = 0x94
  · subst o2
    have : (if A.x.isK = true then none else some (aZpi E (·.x) >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_94]
      exact w_store s_mZpx (·.y) hs1 (hst _ rfl) he
  by_cases o3 : op = 0xD6
  · subst o3
    have : (if A.x.isK = true then none else some (aZpi E (·.x) >>= fun _ => adecV AB.top >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_D6]
      exact w_rmw s_mZpx (fun _ _ => s_decV) hs1 (hst _ rfl) he
  by_cases o4 : op = 0xF6
  · subst o4
    have : (if A.x.isK = true then none else some (aZpi E (·.x) >>= fun _ => aincV AB.top >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_F6]
      exact w_rmw s_mZpx (fun _ _ => s_incV) hs1 (hst _ rfl) he
  by_cases o5 : op = 0x9D
  · subst o5
    have : (if A.x.isK = true then none else some (aAbi E (·.x) >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_9D]
      exact w_store s_mAbx (·.a) hs1 (hst _ rfl) he
  by_cases o6 : op = 0xDE
  · subst o6
    have : (if A.x.isK = true then none else some (aAbi E (·.x) >>= fun _ => adecV AB.top >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_DE]
      exact w_rmw s_mAbx (fun _ _ => s_decV) hs1 (hst _ rfl) he
  by_cases o7 : op = 0xFE
  · subst o7
    have : (if A.x.isK = true then none else some (aAbi E (·.x) >>= fun _ => aincV AB.top >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_FE]
      exact w_rmw s_mAbx (fun _ _ => s_incV) hs1 (hst _ rfl) he
  by_cases o8 : op = 0x7E
  · subst o8
    have : (if A.x.isK = true then none else some (aAbi E (·.x) >>= fun _ => arorV AB.top >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_7E]
      exact w_rmw s_mAbx (fun _ _ => s_rorV) hs1 (hst _ rfl) he
  by_cases o9 : op = 0x99
  · subst o9
    have : (if A.y.isK = true then none else some (aAbi E (·.y) >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_99]
      exact w_store s_mAby (·.a) hs1 (hst _ rfl) he
  by_cases o10 : op = 0x91
  · subst o10
    have : (if _ then none else some (aIzyT E >>= fun _ => aforget G.prot E.rkI)) = some af := h
    split at this
    · cases this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_91]
      exact w_store s_izyT (·.a) hs1 (hst _ rfl) he
  by_cases o11 : op = 0xB1
  · subst o11
    have : (if _ then some (aIzyRT E >>= fun _ => asetA AB.top) else none) = some af := h
    split at this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_B1]
      exact w_read hs1 (hrd rfl) he
    · cases this
  by_cases o12 : op = 0x79
  · subst o12
    have : (if _ then some (aAbiR E (·.y) >>= fun ad => ard E ad >>= aadcH) else none) = some af := h
    split at this
    · obtain rfl := Option.some.inj this
      refine ⟨by decide, by decide, fun u A₂ he => ?_⟩
      rw [op_79]
      have hk : Snd E F TT (aAbiR E (·.y) >>= fun ad => ard E ad >>= aadcH) (opADC mAbyR) :=
        Snd.bind s_mAbyR fun _ _ ha => Snd.bind (s_ard ha) fun _ _ hv => s_adcH hv
      obtain ⟨_, g1, g2⟩ := hk _ _ hs1 _ _ he
      exact ⟨g1, g2⟩
    · cases this
  exfalso
  have e1 : (op == 0x95 || op == 0x94) = false := by simp [o1, o2]
  have e2 : (op == 0xD6) = false := by simpa using o3
  have e3 : (op == 0xF6) = false := by simpa using o4
  have e4 : (op == 0x9D) = false := by simpa using o5
  have e5 : (op == 0xDE) = false := by simpa using o6
  have e6 : (op == 0xFE) = false := by simpa using o7
  have e7 : (op == 0x7E) = false := by simpa using o8
  have e8 : (op == 0x99) = false := by simpa using o9
  have e9 : (op == 0x91) = false := by simpa using o10
  have e10 : (op == 0xB1) = false := by simpa using o11
  have e11 : (op == 0x79) = false := by simpa using o12
  simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h

/-- a step of the machine, with the steps that do not know their target -/
theorem s_gsucc {G : Guard} {A : AS} {m : Machine} {ops : Array (AM Unit)} (hops : ops = (aRows E).toArray) (hT : 2 ≤ F.2.toNat) (hc : Clean G m) (hs : Sim E F A m) :
    ∃ r ∈ gsucc G E ops A, ∀ B, r = some B → Sim E F B (go step m).2 ∧ StepRel A B m (go step m).2 := by
  unfold gsucc
  by_cases h : (A.nmi || decide (A.pc < 0x8000)) = true
  · rw [if_pos h]
    exact s_succs hops hT hs
  · rw [if_neg h]
    simp only [Bool.or_eq_true, not_or, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only
    cases hco : customOf G.prot E A (E.prg.get! (A.pc &&& E.mask).toNat) with
    | none => exact s_succs hops hT hs
    | some af =>
      obtain ⟨g1, g2, g3⟩ := custom_ok hc hs rfl hco
      refine ⟨_, List.mem_singleton.2 rfl, fun B hB => ?_⟩
      have hp : 0x8000 ≤ A.pc := by
        have h3 : ¬ (A.pc.toNat < (0x8000 : UInt16).toNat) := fun h4 => h2 (UInt16.lt_iff_toNat_lt.2 h4)
        apply UInt16.le_iff_toNat_le.2
        omega
      exact custom_step hs (by simpa using h1) hp rfl g1 g2 g3 B hB

/-! ## The pieces cover the machine -/

theorem sim_cap {G : Guard} {A : AS} {m : Machine} (hc : Clean G m) (hs : Sim E F A m) : Sim E F (capT G A) m := by
  unfold capT
  by_cases h : (A.pc != G.idle && decide (G.late < A.hi)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hl := hs.lim
    exact { hs with
      hi := hc.time (by rw [hs.pc]; exact h1)
      lim := by
        show G.late < dotsPerFrame
        omega }
  · rw [if_neg h]
    exact hs

theorem cov_jump {G : Guard} {A : AS} {m : Machine} (hc : Clean G m) (hs : Sim E F A m) : ∃ B ∈ jumpP G A, Sim E F B m := by
  unfold jumpP
  by_cases h : (A.pc == G.je && !A.a.isK) = true
  · rw [if_pos h]
    have hpc : m.pc = G.je := by
      rw [hs.pc]
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1
    cases hp : ptrOf (A.getK (0x100 + A.s.toNat + 1)) (A.getK (0x100 + A.s.toNat + 2)) with
    | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
    | some r =>
      simp only
      cases hl : G.jumps.lookup (r + 1).toNat with
      | none => exact ⟨A, List.mem_singleton.2 rfl, hs⟩
      | some n =>
        simp only
        have hsz : A.s.toNat < 256 := A.s.toNat_lt
        have e1 := hs.ram (0x100 + A.s.toNat + 1) (by omega)
        have e2 := hs.ram (0x100 + A.s.toNat + 2) (by omega)
        have e3 := TaintRun.ptrOf_ok hp e1 e2
        have ht : tableOf m = r + 1 := by
          unfold tableOf
          rw [hs.s, e3]
        have hlt := hc.jump hpc n (by rw [ht]; exact hl)
        refine ⟨_, List.mem_map.2 ⟨m.a.toNat, List.mem_range.2 hlt, rfl⟩, ?_⟩
        refine { hs with a := ?_ }
        have e4 : m.a.toNat.toUInt8 = m.a := by simp
        show (AB.known m.a.toNat.toUInt8).mem m.a
        rw [e4]
        exact mem_known_self _
  · rw [if_neg h]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

theorem cov_then {f g : AS → List AS} (hf : Cov E F f) (hg : Cov E F g) : Cov E F (fun A => (f A).flatMap g) :=
  fun A m hs => cov_flat hg (hf A m hs)

theorem cov_ifSelf {c : AS → Bool} {g : AS → List AS} (hg : Cov E F g) : Cov E F (fun A => if c A = true then [A] else g A) := by
  intro A m hs
  by_cases h : c A = true
  · simp only [if_pos h]
    exact ⟨A, List.mem_singleton.2 rfl, hs, rfl⟩
  · simp only [if_neg h]
    exact hg A m hs

theorem cov_foot {G : Guard} (hy : G.yI < 2048) : Cov E F (footP G) := by
  have c1 : Cov E F (splitBit G.yI 128) := cov_bit hy (by decide)
  have c2 : Cov E F (splitBit G.yI 64) := cov_bit hy (by decide)
  have c3 : Cov E F (splitBit G.yI 32) := cov_bit hy (by decide)
  have c4 : Cov E F (splitBit G.yI 16) := cov_bit hy (by decide)
  exact cov_then c1 (cov_ifSelf (cov_then c2 (cov_ifSelf (cov_then c3 c4))))

theorem cov_high {G : Guard} (hy : G.yI < 2048) : Cov E F (highP G) := by
  have c1 : Cov E F (splitBit G.yI 128) := cov_bit hy (by decide)
  have c2 : Cov E F (splitBit G.yI 64) := cov_bit hy (by decide)
  have c3 : Cov E F (splitBit G.yI 32) := cov_bit hy (by decide)
  have c4 : Cov E F (splitBit G.yI 16) := cov_bit hy (by decide)
  exact cov_then c1 (cov_then c2 (cov_then c3 c4))

theorem cov_zone {G : Guard} {A : AS} {m : Machine} (hb : G.yI < 2048 ∧ G.P.xI < 2048 ∧ G.P.pI < 2048 ∧ G.P.saveI < 2048) (hh : HypG G.P m) (hs : Sim E F A m) :
    ∃ B ∈ zoneP G A, Sim E F B m := by
  obtain ⟨hy, hx, hp, hsv⟩ := hb
  unfold zoneP
  simp only
  by_cases h1 : (A.pc == G.P.foot) = true
  · rw [if_pos h1]
    obtain ⟨B, hB, h3, _⟩ := cov_foot hy A m hs
    exact ⟨B, hB, h3⟩
  rw [if_neg h1]
  by_cases h2 : (A.pc == G.loadY) = true
  · rw [if_pos h2]
    by_cases h3 : ((A.getK G.P.saveI).isK && G.P.idx2.contains (A.getK G.P.saveI).v) = true
    · rw [if_pos h3]
      obtain ⟨B, hB, h4, _⟩ := cov_high hy A m hs
      exact ⟨B, hB, h4⟩
    · rw [if_neg h3]
      exact ⟨A, List.mem_singleton.2 rfl, hs⟩
  rw [if_neg h2]
  by_cases h3 : (A.pc == G.P.entry && A.y.isK && G.P.idx2.contains A.y.v) = true
  · rw [if_pos h3]
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨⟨h4, h5⟩, h6⟩ := h3
    have hyy : m.y = A.y.v := known_eq h5 hs.y
    have ha : AtEntry G.P m := ⟨by rw [hs.pc, h4], by
      rw [hyy]
      exact List.mem_of_elem_eq_true h6⟩
    have hlt := hh.1 ha
    obtain ⟨d1, d2⟩ := pos_digits (n := px G.P m) (p := m.ram.get! G.P.pI) (x := m.ram.get! G.P.xI) rfl
    refine ⟨_, List.mem_map.2 ⟨px G.P m, List.mem_range.2 hlt, rfl⟩, ?_⟩
    refine sim_setK' (sim_setK' hs ?_) ?_
    · rw [d1]
      exact mem_known_self _
    · rw [d2]
      exact mem_known_self _
  rw [if_neg h3]
  by_cases h4 : (A.pc == G.P.read) = true
  · rw [if_pos h4]
    by_cases h5 : ((A.getK G.P.saveI).isK && G.P.idx2.contains (A.getK G.P.saveI).v && (A.getK G.P.ptrI).isK && (A.getK (G.P.ptrI + 1)).isK && A.y.isK && safeI G.P (readI G.P A) (A.getK G.P.pI)) = true
    · rw [if_pos h5]
      simp only [Bool.and_eq_true] at h5
      obtain ⟨⟨⟨⟨⟨h6, h7⟩, _⟩, _⟩, _⟩, h9⟩ := h5
      have hpc : m.pc = G.P.read := by rw [hs.pc]; exact beq_iff_eq.1 h4
      have hsv2 : m.ram.get! G.P.saveI = (A.getK G.P.saveI).v := known_eq h6 (hs.ram _ hsv)
      have hat : AtRead G.P m := ⟨hpc, by rw [hsv2]; exact List.mem_of_elem_eq_true h7⟩
      have htiles := hh.2 hat
      have hpage : (m.ram.get! G.P.pI).toNat ≤ (A.getK G.P.pI).maxv.toNat := TaintRun.le_maxv (hs.ram _ hp)
      simp only [safeI, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne] at h9
      obtain ⟨⟨⟨h10, h11⟩, h12⟩, h13⟩ := h9
      have hnot : m.ram.get! (readI G.P A) ≠ G.P.tile := by
        intro he
        have ht := htiles (by omega) _ h11 h12 he
        rcases h13 with h14 | h14
        · exact h14 ht.1
        · have := ht.2
          omega
      obtain ⟨b, hb1, hb2⟩ := ne_bit hnot
      exact ⟨_, List.mem_map.2 ⟨b, hb1, rfl⟩, sim_setK' hs hb2⟩
    · rw [if_neg h5]
      exact ⟨A, List.mem_singleton.2 rfl, hs⟩
  · rw [if_neg h4]
    exact ⟨A, List.mem_singleton.2 rfl, hs⟩

/-- every machine that meets the conditions is in a piece -/
theorem cov_pre {G : Guard} {A : AS} {m : Machine} (hb : G.yI < 2048 ∧ G.P.xI < 2048 ∧ G.P.pI < 2048 ∧ G.P.saveI < 2048) (hc : Clean G m) (hh : HypG G.P m) (hs : Sim E F A m) :
    ∃ B ∈ preG G A, Sim E F B m := by
  obtain ⟨B, hB, h1⟩ := cov_jump hc (sim_cap hc hs)
  obtain ⟨D, hD, h2⟩ := cov_zone hb hh h1
  exact ⟨D, List.mem_flatMap.2 ⟨B, hB, hD⟩, h2⟩

end

/-! ## The order -/

theorem ramLe_of {a b : AS} : ∀ (n i : Nat), (∀ j, i ≤ j → j < i + n → (a.getK j).le (b.getK j) = true) → ramLeFrom a b n i = true := by
  intro n
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro i h
    simp only [ramLeFrom, Bool.and_eq_true]
    exact ⟨h i (Nat.le_refl _) (by omega), ih (i + 1) fun j h1 h2 => h j (by omega) (by omega)⟩

theorem le_of_k0 (x : AB) {b : AB} (hk : b.k = 0) : x.le b = true := by
  simp only [AB.le, hk, Bool.and_eq_true, beq_iff_eq]
  constructor
  · apply bt_ext
    intro j hj
    rw [bt_and, bt_zero hj, Bool.false_and]
  · apply bt_ext
    intro j hj
    rw [bt_and, bt_zero hj, Bool.and_false]

/-- `leK` on the known bytes of `b` is `AS.le` -/
theorem leK_le {a b : AS} (h : leK a b (knownOf b) = true) : a.le b = true := by
  simp only [leK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hh, hj⟩, h1⟩, h2⟩ := h
  simp only [AS.le, Bool.and_eq_true]
  refine ⟨⟨⟨hh, ?_⟩, h1⟩, h2⟩
  apply ramLe_of
  intro j _ h4
  by_cases hk : b.kn.get! j = 0
  · exact le_of_k0 _ hk
  · have hm : j ∈ knownOf b := by
      unfold knownOf
      refine List.mem_filter.2 ⟨List.mem_range.2 (by omega), ?_⟩
      simpa using hk
    exact (List.all_eq_true.1 hj) j hm

theorem le_k {a b : AS} (h : a.le b = true) : a.k = b.k := by
  simp only [AS.le, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  exact h3

/-! ## The walk covers the machine -/

section
variable {C : CfgG} {Fu : Nat} {F : Nat × UInt8}

/-- `A` covers `m` in the frame of the start, and a walk from `A` succeeds -/
def LiveG (C : CfgG) (F : Nat × UInt8) (A : AS) (m : Machine) : Prop := Sim C.E F A m ∧ A.k = 0 ∧ ∃ n, walkG C n A = true

theorem cover_liveG (ht : C.t.all (walkG C Fu) = true) (hkl : C.kl = C.t.map knownOf) {B : AS} {m : Machine} (hs : Sim C.E F B m) (hk : B.k = 0) (h : coverG C B = true) : ∃ D, LiveG C F D m := by
  unfold coverG at h
  split at h
  · rename_i i _
    split at h
    · rename_i D l e1 e2
      obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 e1
      have hl : l = knownOf D := by
        rw [hkl] at e2
        rw [Array.getElem?_map, e1] at e2
        exact (Option.some.inj e2).symm
      rw [hl] at h
      have hle := leK_le h
      have hall := (Array.all_eq_true.1 ht) i hi
      rw [he] at hall
      have hDk : D.k = 0 := by
        have e3 := le_k hle
        omega
      exact ⟨D, sim_le hle hs, hDk, Fu, hall⟩
    · cases h
  · cases h

/-- the byte is not the pipe's -/
theorem ne_of_okRt {G : Guard} {B : AS} {x : UInt8} (h : okRt G B = true) (hm : (B.getK G.rtI).mem x) : x ≠ G.ev := by
  intro he
  subst he
  simp only [okRt, bne_iff_ne, ne_eq] at h
  exact h hm

theorem live_stepG (ht : C.t.all (walkG C Fu) = true) (hkl : C.kl = C.t.map knownOf) (hops : C.ops = (aRows C.E).toArray) (hT : 2 ≤ F.2.toNat)
    (hb : C.G.yI < 2048 ∧ C.G.P.xI < 2048 ∧ C.G.P.pI < 2048 ∧ C.G.P.saveI < 2048) (hr : C.G.rtI < 2048) {A : AS} {m : Machine} (hl : LiveG C F A m) (hc : Clean C.G m) (hh : HypG C.G.P m) :
    (go step m).2.ram.get! C.G.rtI ≠ C.G.ev ∧ (F.1 < (go step m).2.frame ∨ ∃ A', LiveG C F A' (go step m).2) := by
  obtain ⟨hs, hk, n, hw⟩ := hl
  cases n with
  | zero => simp [walkG] at hw
  | succ n =>
    obtain ⟨A₁, hA, hs1⟩ := cov_pre hb hc hh hs
    obtain ⟨r, hr1, hB⟩ := s_gsucc hops hT hc hs1
    simp only [walkG, List.all_eq_true] at hw
    have hw2 := hw A₁ hA r hr1
    cases r with
    | none => simp at hw2
    | some B =>
      obtain ⟨h1, _⟩ := hB B rfl
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hw2
      obtain ⟨h2, h3⟩ := hw2
      refine ⟨ne_of_okRt h2 (h1.ram _ hr), ?_⟩
      by_cases hk2 : B.k = 0
      · right
        rcases h3 with (h4 | ⟨_, h4⟩) | h4
        · rw [hk, hk2] at h4
          exact absurd rfl h4
        · exact cover_liveG ht hkl h1 hk2 h4
        · exact ⟨B, h1, hk2, n, h4⟩
      · left
        rw [h1.fr]
        omega

end

/-! ## The frame -/

theorem zeros_size' : zeros.size = 2048 := zeros_size 2048

theorem known_fold_size (l : List (Nat × UInt8)) (f : Nat × UInt8 → UInt8) : ∀ r : ByteArray, r.size = 2048 → (l.foldl (fun r p => r.set! p.1 (f p)) r).size = 2048 := by
  induction l with
  | nil => exact fun _ h => h
  | cons a l ih =>
    intro r h
    exact ih _ (by rw [ba_size_set]; exact h)

theorem known_fold_mem (l : List (Nat × UInt8)) {x : UInt8} {i : Nat} (hi : i < 2048) (hl : ∀ p ∈ l, p.1 = i → x = p.2) :
    ∀ r k : ByteArray, r.size = 2048 → k.size = 2048 → AB.mem ⟨r.get! i, k.get! i⟩ x →
      AB.mem ⟨(l.foldl (fun r p => r.set! p.1 p.2) r).get! i, (l.foldl (fun r p => r.set! p.1 0xFF) k).get! i⟩ x := by
  induction l with
  | nil => exact fun _ _ _ _ h => h
  | cons a l ih =>
    intro r k h1 h2 h3
    simp only [List.foldl_cons]
    refine ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) _ _ (by rw [ba_size_set]; exact h1) (by rw [ba_size_set]; exact h2) ?_
    by_cases hai : a.1 = i
    · have hx := hl a List.mem_cons_self hai
      rw [← hai] at hi ⊢
      rw [ba_get_set_self _ _ _ (by rw [h1]; exact hi), ba_get_set_self _ _ _ (by rw [h2]; exact hi), hx]
      exact mem_known_self _
    · rw [ba_get_set_ne _ _ _ _ hai, ba_get_set_ne _ _ _ _ hai]
      exact h3

/-- the state when the frame starts covers the machine -/
theorem sim_startG {G : Guard} {E : Env} (hE : E.pad = AB.top) {m : Machine} (h : FrameStart G E m) :
    ∃ b : Bool, Sim E (m.frame, 2) (startG G b) m := by
  have hsmall : (9 : Nat) < dotsPerFrame := by decide
  have hctrl : (⟨0x80, 0x80⟩ : AB).mem m.ppuCtrl := by
    show m.ppuCtrl &&& 0x80 = 0x80 &&& 0x80
    rw [h.ctrl]
    decide
  have hsz1 : (G.known.foldl (fun r p => r.set! p.1 p.2) zeros).size = 2048 := known_fold_size G.known (·.2) zeros zeros_size'
  have hsz2 : (G.known.foldl (fun r p => r.set! p.1 0xFF) zeros).size = 2048 := known_fold_size G.known (fun _ => 0xFF) zeros zeros_size'
  have hram : ∀ i, i < 2048 → AB.mem ⟨(G.known.foldl (fun r p => r.set! p.1 p.2) zeros).get! i, (G.known.foldl (fun r p => r.set! p.1 0xFF) zeros).get! i⟩ (m.ram.get! i) := by
    intro i hi
    refine known_fold_mem G.known hi (fun p hp he => ?_) zeros zeros zeros_size' zeros_size' ?_
    · rw [← he]
      exact h.known p hp
    · exact mem_of_k0 (zeros_get 2048 i)
  rcases h.dot with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3, d4⟩
  · refine ⟨false, ?_⟩
    exact ⟨mem_top _, mem_top _, mem_top _, mem_top _, h.s, h.pc, h.prg, h.mask, hctrl, mem_top _, d2, d3, h.s0, by show 0 ≤ m.fdot; omega, by show m.fdot ≤ 0; omega, by show 0 < dotsPerFrame; omega, by rw [hE]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, hram, (by intro hd; cases hd), hsz1, hsz2, (by show m.frame = m.frame + 0; rfl), (by intro hd; cases hd)⟩
  · refine ⟨true, ?_⟩
    exact ⟨mem_top _, mem_top _, mem_top _, mem_top _, h.s, h.pc, h.prg, h.mask, hctrl, mem_top _, d3, d4, h.s0, d1, d2, by show 9 < dotsPerFrame; exact hsmall, by rw [hE]; exact mem_top _, mem_top _, h.strobe, h.halted, h.trk, h.size, hram, (by intro hd; cases hd), hsz1, hsz2, (by show m.frame = m.frame + 0; rfl), (by intro hd; cases hd)⟩

/-- what the check says -/
structure FrameOK (G : Guard) (E : Env) : Prop where
  bytes : G.rtI < 2048 ∧ G.yI < 2048 ∧ G.P.xI < 2048 ∧ G.P.pI < 2048 ∧ G.P.ptrI < 2048 ∧ G.P.saveI < 2048
  late : G.late < dotsPerFrame
  ok0 : okRt G (startG G false) = true
  ok1 : okRt G (startG G true) = true
  table : (cfgOf G E).t.all (walkG (cfgOf G E) fuelG) = true
  s0 : walkG (cfgOf G E) fuelG (startG G false) = true
  s1 : walkG (cfgOf G E) fuelG (startG G true) = true

theorem frameOK_of_check {G : Guard} {E : Env} (h : frameCheck G E = true) : FrameOK G E := by
  simp only [frameCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10, h11, h12⟩

/-- **The frame.** From a `FrameStart`, while each instruction is `Clean` and meets `HypG`, the routine byte does not become the pipe's. -/
theorem no_write_frame {G : Guard} {E : Env} (hc : frameCheck G E = true) (hE : E.pad = AB.top) {s : Nat → Machine} {n : Nat}
    (hs : ∀ j, j ≤ n → s (j + 1) = (go step (s j)).2) (hf : ∀ j, j ≤ n → (s j).frame ≤ (s 0).frame) (h0 : FrameStart G E (s 0))
    (hh : ∀ j, j ≤ n → Clean G (s j) ∧ HypG G.P (s j)) : (s (n + 1)).ram.get! G.rtI ≠ G.ev := by
  have hC := frameOK_of_check hc
  obtain ⟨b, hsim⟩ := sim_startG hE h0
  have hb : (cfgOf G E).G.yI < 2048 ∧ (cfgOf G E).G.P.xI < 2048 ∧ (cfgOf G E).G.P.pI < 2048 ∧ (cfgOf G E).G.P.saveI < 2048 :=
    ⟨hC.bytes.2.1, hC.bytes.2.2.1, hC.bytes.2.2.2.1, hC.bytes.2.2.2.2.2⟩
  have hkl : (cfgOf G E).kl = (cfgOf G E).t.map knownOf := rfl
  have hstart : ∃ A, LiveG (cfgOf G E) ((s 0).frame, 2) A (s 0) := by
    cases b with
    | false => exact ⟨_, hsim, rfl, fuelG, hC.s0⟩
    | true => exact ⟨_, hsim, rfl, fuelG, hC.s1⟩
  have live : ∀ j, j ≤ n → ∃ A, LiveG (cfgOf G E) ((s 0).frame, 2) A (s j) := by
    intro j
    induction j with
    | zero => exact fun _ => hstart
    | succ j ih =>
      intro hj
      obtain ⟨A, hA⟩ := ih (by omega)
      obtain ⟨hh1, hh2⟩ := hh j (by omega)
      obtain ⟨_, h2⟩ := live_stepG hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hb hC.bytes.1 hA hh1 hh2
      rw [← hs j (by omega)] at h2
      rcases h2 with h2 | h2
      · have h3 := hf (j + 1) hj
        have h4 : (s 0).frame < (s (j + 1)).frame := h2
        omega
      · exact h2
  obtain ⟨A, hA⟩ := live n (Nat.le_refl n)
  obtain ⟨hh1, hh2⟩ := hh n (Nat.le_refl n)
  obtain ⟨h1, _⟩ := live_stepG hC.table hkl rfl (show 2 ≤ (2 : UInt8).toNat by decide) hb hC.bytes.1 hA hh1 hh2
  rw [← hs n (Nat.le_refl n)] at h1
  exact h1

/-- before the write the frame goes on -/
theorem frame_before {sy : Syms} {m : Machine} {i : UInt8} {n : Nat} (h : WriteStep sy m i n) : ∀ j, j ≤ n → (trace m i j).frame ≤ m.frame := by
  intro j hj
  by_cases hg : ((trace m i j).frame ≥ m.frame + 1 || (trace m i j).halted) = true
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
    have e1 := trace_stop hg k
    have e2 := trace_stop hg (k + 1)
    apply h.1
    rw [e1, ← e2]
    exact h.2
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hg
    omega

/-- the state of `FrameStart` with another pad -/
theorem FrameStart.pad {G : Guard} {E : Env} {m : Machine} (h : FrameStart G E m) (p : UInt8) : FrameStart G E { m with pad := p } :=
  ⟨h.pc, h.s, h.dot, h.ctrl, h.s0, h.strobe, h.halted, h.trk, h.prg, h.mask, h.size, h.known⟩

/-- **The entry on a real frame.** If the frame enters, it starts in control, its instructions up to the write are `Clean`, and each read of the right foot up to the write meets `TilesOK`, then at the entry
for the right foot, before the write, the position is at or right of the window's left end. -/
theorem entry_right_of_left {sy : Syms} {m0 m : Machine} {i : UInt8} (hc : ruleCheckG sy m0 = true) (he : Enters sy m i)
    (h0 : FrameStart (guardOf sy m0) (envOf m0) m)
    (hp : ∀ n, WriteStep sy m i n → ∀ j, j ≤ n → Clean (guardOf sy m0) (trace m i j) ∧ (AtRead (guardOf sy m0).P (trace m i j) → TilesOK (guardOf sy m0).P (trace m i j))) :
    ∃ n j, WriteStep sy m i n ∧ j ≤ n ∧ AtEntry (guardOf sy m0).P (trace m i j) ∧ (guardOf sy m0).P.left ≤ px (guardOf sy m0).P (trace m i j) := by
  obtain ⟨n, _, hw⟩ := writeStep_of_enters he
  by_cases hx : ∃ j, j ≤ n ∧ AtEntry (guardOf sy m0).P (trace m i j) ∧ (guardOf sy m0).P.left ≤ px (guardOf sy m0).P (trace m i j)
  · obtain ⟨j, a, b, c⟩ := hx
    exact ⟨n, j, hw, a, b, c⟩
  · exfalso
    have hn := no_write_frame (s := trace m i) (n := n) hc rfl (fun j hj => step_before hw j hj)
      (fun j hj => frame_before hw j hj) (h0.pad _)
      (fun j hj => ⟨(hp n hw j hj).1, fun ha => by
        by_cases hl : (guardOf sy m0).P.left ≤ px (guardOf sy m0).P (trace m i j)
        · exact absurd ⟨j, hj, ha, hl⟩ hx
        · omega, (hp n hw j hj).2⟩)
    exact hn hw.2

/-- **The rule on frames.** `fm t` is the machine when frame `t` begins and `inp t` its input. This is what `PipeEntry.no_entry_by` needs: an entering frame is at or right of the window's left end. -/
theorem rule_on_frames {top amax : Int} {sy : Syms} {m0 : Machine} (hc : ruleCheckG sy m0 = true) (fr : Nat → TopSpeed.Frame top amax)
    (fm : Nat → Machine) (inp : Nat → UInt8)
    (h0 : ∀ t, Enters sy (fm t) (inp t) → FrameStart (guardOf sy m0) (envOf m0) (fm t))
    (hcl : ∀ t, Enters sy (fm t) (inp t) → ∀ n, WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n → Clean (guardOf sy m0) (trace (fm t) (inp t) j))
    (ht : ∀ t, Enters sy (fm t) (inp t) → ∀ n, WriteStep sy (fm t) (inp t) n → ∀ j, j ≤ n → AtRead (guardOf sy m0).P (trace (fm t) (inp t) j) → TilesOK (guardOf sy m0).P (trace (fm t) (inp t) j))
    (hpos : ∀ t, Enters sy (fm t) (inp t) → ∀ n j, WriteStep sy (fm t) (inp t) n → j ≤ n → AtEntry (guardOf sy m0).P (trace (fm t) (inp t) j) →
      ∃ f : Int, 0 ≤ f ∧ (fr t).P₂ = 256 * (px (guardOf sy m0).P (trace (fm t) (inp t) j) : Int) + f) :
    ∀ t, Enters sy (fm t) (inp t) → PipeEntry.windowP sy (PipeEntry.pipePage sy m0) ≤ (fr t).P₂ := by
  intro t he
  obtain ⟨n, j, h1, h2, h3, h4⟩ := entry_right_of_left hc he (h0 t he) (fun n hw j hj => ⟨hcl t he n hw j hj, ht t he n hw j hj⟩)
  obtain ⟨f, hf, h5⟩ := hpos t he n j h1 h2 h3
  rw [h5]
  have h6 : (guardOf sy m0).P.left = 256 * PipeEntry.pipePage sy m0 + PipeEntry.xLo sy := rfl
  rw [h6] at h4
  unfold PipeEntry.windowP
  omega

/-! ## The tile, by single instructions

`TilesOK` stays assumed. Here it is reduced to one instruction at a time, on any sequence of machines. This is not used by `Route`, which keeps `TilesOK` on the frame that enters. -/

/-- the pipe's right tile is in the block buffers only at its place, and only from the page before the pipe's on -/
def TilesAll (P : Spots) (m : Machine) : Prop :=
  ∀ i, P.bufLo ≤ i → i < P.bufLo + P.bufBytes → m.ram.get! i = P.tile → i = P.dR ∧ P.pg ≤ (m.ram.get! P.pI).toNat + 1

/-- one instruction: it writes the tile into the block buffers only at its place, from the page before the pipe's on, and with the tile there the page stays so -/
structure TileStep (P : Spots) (m m' : Machine) : Prop where
  write : ∀ i, P.bufLo ≤ i → i < P.bufLo + P.bufBytes → m'.ram.get! i = P.tile → m.ram.get! i ≠ P.tile → i = P.dR ∧ P.pg ≤ (m'.ram.get! P.pI).toNat + 1
  page : m.ram.get! P.dR = P.tile → P.pg ≤ (m.ram.get! P.pI).toNat + 1 → P.pg ≤ (m'.ram.get! P.pI).toNat + 1

/-- `TilesOK` from the start of a sequence and from each instruction -/
theorem tiles_of_steps {P : Spots} {s : Nat → Machine} {N : Nat} (h0 : TilesAll P (s 0)) (hs : ∀ k, k < N → TileStep P (s k) (s (k + 1))) :
    ∀ k, k ≤ N → TilesOK P (s k) := by
  have all : ∀ k, k ≤ N → TilesAll P (s k) := by
    intro k
    induction k with
    | zero => exact fun _ => h0
    | succ k ih =>
      intro hk i h1 h2 h3
      have hk' := hs k (by omega)
      by_cases he : (s k).ram.get! i = P.tile
      · obtain ⟨h4, h5⟩ := ih (by omega) i h1 h2 he
        refine ⟨h4, hk'.page (by rw [← h4]; exact he) h5⟩
      · exact hk'.write i h1 h2 h3 he
  intro k hk _ i h1 h2 h3
  exact all k hk i h1 h2 h3

/-! ## On real frames: a program, no part of the proof -/

def plainB (prot : List Nat) (t : UInt16) : Bool :=
  (decide (t < 0x2000) && !prot.contains (t &&& 0x7FF).toNat) || (decide (0x4000 ≤ t) && t != 0x4014 && t != 0x4016)

def startB (G : Guard) (E : Env) (m : Machine) : Bool :=
  m.pc == G.idle && m.s == G.s0 &&
  ((m.fdot == 0 && !m.vblank && !m.nmiPending) || (decide (1 ≤ m.fdot) && decide (m.fdot ≤ 9) && m.vblank && m.nmiPending)) &&
  m.ppuCtrl &&& 0x80 == 0x80 && m.sprite0 == s0f m.fdot && !m.padStrobe && !m.halted && !m.trk && m.prgMask == E.mask && m.ram.size == 2048 &&
  G.known.all fun p => m.ram.get! p.1 == p.2

/-- the conditions of one instruction: store, read, jump, time -/
def cleanB (G : Guard) (m : Machine) : Bool × Bool × Bool × Bool :=
  let op := opAt m
  (match wTarget op m with
   | some t => plainB G.prot t
   | none => true,
   op != 0xB1 || decide (rTarget m < 0x2000) || decide (0x8000 ≤ rTarget m),
   m.pc != G.je || (match G.jumps.lookup (tableOf m).toNat with
     | some n => decide (m.a.toNat < n)
     | none => false),
   m.pc == G.idle || decide (m.fdot ≤ G.late))

def tilesB (P : Spots) (m : Machine) : Bool := tilesOK P m

/-- what real frames say about the hypotheses -/
structure Report where
  frames : Nat := 0
  /-- frames in control, and how many do not meet `FrameStart` -/
  ctl : Nat := 0
  startBad : Nat := 0
  /-- instructions of frames in control, how many are stores with an index or a pointer, reads through a pointer, jumps; how many fail the condition, and the last dot seen -/
  instrs : Nat := 0
  stores : Nat := 0
  storeBad : Nat := 0
  reads : Nat := 0
  readBad : Nat := 0
  jumps : Nat := 0
  jumpBad : Nat := 0
  timeBad : Nat := 0
  maxDot : Nat := 0
  badPcs : List (UInt16 × Nat) := []
  /-- reads of the right foot on the pipe's page or before, and how many do not meet `TilesOK` -/
  footReads : Nat := 0
  tilesBad : Nat := 0
  /-- frames that enter; of them: not `FrameStart`, an instruction up to the write not `Clean`, a read not `TilesOK`, the write at another instruction, no entry for the right foot before it, left of the window, right of it, the position at the entries for the right foot differ, the position changes after the foot check -/
  entries : Nat := 0
  eStart : Nat := 0
  eClean : Nat := 0
  eTiles : Nat := 0
  writeBad : Nat := 0
  noFoot : Nat := 0
  leftBad : Nat := 0
  rightOut : Nat := 0
  posDiff : Nat := 0
  moved : Nat := 0
  /-- the largest dot of the write -/
  writeDot : Nat := 0
  /-- stores of the tile into the block buffers, and how many do not meet `TileStep`; instructions that leave the page too far back with the tile there -/
  tileWrites : Nat := 0
  tileBad : Nat := 0
  pageBad : Nat := 0
  pxs : List Nat := []
  deriving Inhabited

def Report.show (r : Report) : String :=
  s!"frames {r.frames}, in control {r.ctl} (not FrameStart: {r.startBad}); instructions {r.instrs}: stores {r.stores} (bad {r.storeBad}), pointer reads {r.reads} (bad {r.readBad}), jumps {r.jumps} (bad {r.jumpBad}), late {r.timeBad}, largest dot {r.maxDot}, bad pcs {r.badPcs.take 6}; right foot reads {r.footReads} (not TilesOK: {r.tilesBad}); entries {r.entries} (not FrameStart: {r.eStart}, not Clean: {r.eClean}, not TilesOK: {r.eTiles}, not the write: {r.writeBad}, no foot: {r.noFoot}, left of the window: {r.leftBad}, right of it: {r.rightOut}, positions differ: {r.posDiff}, moved after: {r.moved}, largest dot of a write: {r.writeDot}), positions {r.pxs.eraseDups}; stores of the tile {r.tileWrites} (bad {r.tileBad}), page back with the tile {r.pageBad}"

/-- one real frame with the bits `pad` of the controller -/
def scanFrame (sy : Syms) (G : Guard) (E : Env) (m : Machine) (pad : UInt8) (r0 : Report) : Report × Machine := Id.run do
  let P := G.P
  let t := m.frame + 1
  let mut c : Machine := { m with pad }
  let ctl := controllable sy m
  let startOk := startB G E c
  let mut r := { r0 with frames := r0.frames + 1, ctl := r0.ctl + (if ctl then 1 else 0), startBad := r0.startBad + (if ctl && !startOk then 1 else 0) }
  let mut clean := true
  let mut tiles := true
  let mut firstPx : Option Nat := none
  let mut lastPx : Option Nat := none
  let mut diff := false
  let mut entered : Option Nat := none
  let mut n := 0
  while n < fuelPerFrame && !(decide (c.frame ≥ t) || c.halted) do
    let (a, b, j, d) := cleanB G c
    let op := opAt c
    if ctl then
      r := { r with
        instrs := r.instrs + 1
        stores := r.stores + (if (wTarget op c).isSome then 1 else 0)
        storeBad := r.storeBad + (if a then 0 else 1)
        reads := r.reads + (if op == 0xB1 then 1 else 0)
        readBad := r.readBad + (if b then 0 else 1)
        jumps := r.jumps + (if c.pc == G.je then 1 else 0)
        jumpBad := r.jumpBad + (if j then 0 else 1)
        timeBad := r.timeBad + (if d then 0 else 1)
        maxDot := if c.pc == G.idle then r.maxDot else Nat.max r.maxDot c.fdot }
      if !(a && b && j && d) && r.badPcs.length < 8 then r := { r with badPcs := (c.pc, c.frame) :: r.badPcs }
    if !(a && b && j && d) then clean := false
    if c.pc == P.entry && P.idx2.contains c.y && entered.isNone then
      let q := px P c
      if firstPx.isSome && firstPx != some q then diff := true
      firstPx := firstPx <|> some q
      lastPx := some q
    if c.pc == P.read && P.idx2.contains (c.ram.get! P.saveI) then
      let x := tilesB P c
      r := { r with footReads := r.footReads + 1, tilesBad := r.tilesBad + (if x then 0 else 1) }
      if !x && entered.isNone then tiles := false
    let before := rt sy c
    let pc := c.pc
    let dot := c.fdot
    let tg := wTarget op c
    let c0 := c
    c := (go step c).2
    match tg with
    | some a =>
      let i := (a &&& 0x7FF).toNat
      if decide (a < 0x2000) && decide (P.bufLo ≤ i) && decide (i < P.bufLo + P.bufBytes) && c.ram.get! i == P.tile && c0.ram.get! i != P.tile then
        r := { r with tileWrites := r.tileWrites + 1, tileBad := r.tileBad + (if i == P.dR && decide (P.pg ≤ (c.ram.get! P.pI).toNat + 1) then 0 else 1) }
    | none => pure ()
    if c0.ram.get! P.dR == P.tile && decide (P.pg ≤ (c0.ram.get! P.pI).toNat + 1) && !decide (P.pg ≤ (c.ram.get! P.pI).toNat + 1) then
      r := { r with pageBad := r.pageBad + 1 }
    if before != vp sy && rt sy c == vp sy && entered.isNone then
      r := { r with
        entries := r.entries + 1
        eStart := r.eStart + (if startOk then 0 else 1)
        eClean := r.eClean + (if clean then 0 else 1)
        eTiles := r.eTiles + (if tiles then 0 else 1)
        writeBad := r.writeBad + (if pc == P.write then 0 else 1)
        noFoot := r.noFoot + (if lastPx.isSome then 0 else 1)
        posDiff := r.posDiff + (if diff then 1 else 0)
        writeDot := Nat.max r.writeDot dot }
      match lastPx with
      | some q =>
        r := { r with leftBad := r.leftBad + (if q < P.left then 1 else 0), pxs := q :: r.pxs,
                      rightOut := r.rightOut + (if q > 256 * P.pg + PipeEntry.xHi sy then 1 else 0) }
        entered := some q
      | none => entered := some 0
    n := n + 1
  match entered with
  | some q => if px P c != q then r := { r with moved := r.moved + 1 }
  | none => pure ()
  return (r, c)

end Smbrta.PipeWrites
