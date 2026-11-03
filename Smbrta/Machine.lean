/-!
# NES machine state and bus

A minimal NES model aimed at running game logic (no rendering):

* 6502 registers
* 2 KiB internal RAM (mirrored over $0000-$1FFF)
* NROM PRG-ROM (16 or 32 KiB) at $8000-$FFFF
* PPU: only the timing of the vblank flag, NMI, and the sprite-0 hit flag
* Standard controller on $4016

PPU time is counted in dots inside the current frame. `fdot = 0` is
scanline 241 dot 0 (the start of vblank), so one frame runs from one vblank
start to the next.  This matches how FCEUX splits frames.
-/

namespace Smbrta

/-- PPU dot (inside the frame) at which the vblank flag is set (scanline 241, dot 1). -/
def dotVblSet : Nat := 1
/-- PPU dot at which vblank and sprite-0 flags are cleared (pre-render line 261, dot 1). -/
def dotVblClr : Nat := 20 * 341 + 1
/-- PPU dot at which the sprite-0 hit flag is set (approximate scanline 31). -/
def dotSpr0 : Nat := (21 + 31) * 341
/-- Dots per frame (262 scanlines × 341 dots). -/
def dotsPerFrame : Nat := 262 * 341

structure Machine where
  a : UInt8 := 0
  x : UInt8 := 0
  y : UInt8 := 0
  s : UInt8 := 0xFD
  p : UInt8 := 0x24
  pc : UInt16 := 0
  /-- total CPU cycles since power-on -/
  cyc : Nat := 0
  ram : ByteArray := ByteArray.mk (Array.replicate 2048 0)
  prg : ByteArray := ByteArray.empty
  prgMask : UInt16 := 0x7FFF
  ppuCtrl : UInt8 := 0
  ppuMask : UInt8 := 0
  vblank : Bool := false
  sprite0 : Bool := false
  nmiPending : Bool := false
  /-- PPU dot inside the current frame -/
  fdot : Nat := 0
  /-- number of finished frames -/
  frame : Nat := 0
  /-- buttons held this frame, bit0..7 = A B Select Start Up Down Left Right -/
  pad : UInt8 := 0
  padShift : UInt8 := 0
  padStrobe : Bool := false
  /-- set when the CPU executes a JAM / unsupported opcode -/
  halted : Bool := false
  /-- access tracking (off in normal runs): RAM bytes read before being written,
  RAM bytes written, and whether any I/O register ($2000-$5FFF) was read -/
  trk : Bool := false
  trkRead : ByteArray := ByteArray.empty
  trkWrite : ByteArray := ByteArray.empty
  trkIO : Bool := false
  deriving Inhabited

abbrev M := StateM Machine

/-! ## PPU timing -/

/-- Advance PPU time by `c` CPU cycles (3 dots each) and fire the PPU events. -/
def tick (c : Nat) : M Unit := modify fun m =>
  let old := m.fdot
  let new := old + 3 * c
  let m := { m with cyc := m.cyc + c }
  let m := if old < dotVblSet && dotVblSet ≤ new then
      { m with vblank := true, nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) }
    else m
  let m := if old < dotVblClr && dotVblClr ≤ new then
      { m with vblank := false, sprite0 := false } else m
  let m := if old < dotSpr0 && dotSpr0 ≤ new then { m with sprite0 := true } else m
  -- odd frames are one dot shorter when rendering is on
  let len := if m.frame % 2 == 1 && (m.ppuMask &&& 0x18 != 0) then dotsPerFrame - 1 else dotsPerFrame
  if new ≥ len then
    let new := new - len
    let m := { m with frame := m.frame + 1, fdot := new }
    if dotVblSet ≤ new then
      { m with vblank := true, nmiPending := m.nmiPending || (m.ppuCtrl &&& 0x80 != 0) }
    else m
  else { m with fdot := new }

/-! ## Bus -/

def ppuRead (reg : UInt16) : M UInt8 := do
  if reg == 2 then
    let m ← get
    let v : UInt8 := (if m.vblank then 0x80 else 0) ||| (if m.sprite0 then 0x40 else 0)
    set { m with vblank := false }
    return v
  else return 0

def padRead : M UInt8 := do
  let m ← get
  if m.padStrobe then return 0x40 ||| (m.pad &&& 1)
  else
    set { m with padShift := (m.padShift >>> 1) ||| 0x80 }
    return 0x40 ||| (m.padShift &&& 1)

/-- record a tracked RAM read: it counts only if the byte was not written before -/
def trackRead (i : Nat) : M Unit := modify fun m =>
  if m.trkWrite.get! i == 0 then
    let r := m.trkRead
    let m := { m with trkRead := ByteArray.empty }
    { m with trkRead := r.set! i 1 }
  else m

@[inline] def rd (addr : UInt16) : M UInt8 := do
  if addr < 0x2000 then
    let m ← get
    let i := (addr &&& 0x7FF).toNat
    if m.trk then trackRead i
    return (← get).ram.get! i
  else if addr ≥ 0x8000 then
    let m ← get
    return m.prg.get! (addr &&& m.prgMask).toNat
  else if addr < 0x4000 then
    if (← get).trk then modify fun m => { m with trkIO := true }
    ppuRead (addr &&& 7)
  else if addr == 0x4016 then
    if (← get).trk then modify fun m => { m with trkIO := true }
    padRead
  else if addr == 0x4017 then return 0x40
  else return 0

def ppuWrite (reg : UInt16) (v : UInt8) : M Unit := modify fun m =>
  if reg == 0 then
    let nmi := m.nmiPending ||
      (m.vblank && (v &&& 0x80 != 0) && (m.ppuCtrl &&& 0x80 == 0))
    { m with ppuCtrl := v, nmiPending := nmi }
  else if reg == 1 then { m with ppuMask := v }
  else m

def padWrite (v : UInt8) : M Unit := modify fun m =>
  if v &&& 1 == 1 then { m with padStrobe := true, padShift := m.pad }
  else if m.padStrobe then { m with padStrobe := false, padShift := m.pad }
  else m

/-- OAM DMA: the CPU stalls 513 cycles (514 on an odd cycle). OAM is not modelled. -/
def oamDma : M Unit := do
  let m ← get
  tick (if m.cyc % 2 == 1 then 514 else 513)

@[inline] def wr (addr : UInt16) (v : UInt8) : M Unit := do
  if addr < 0x2000 then
    modify fun m =>
      let i := (addr &&& 0x7FF).toNat
      let ram := m.ram
      let m := { m with ram := ByteArray.empty }
      let m := { m with ram := ram.set! i v }
      if m.trk then
        let w := m.trkWrite
        let m := { m with trkWrite := ByteArray.empty }
        { m with trkWrite := w.set! i 1 }
      else m
  else if addr < 0x4000 then ppuWrite (addr &&& 7) v
  else if addr == 0x4014 then oamDma
  else if addr == 0x4016 then padWrite v
  else pure ()

/-! ## Loading -/

/-- Parse an iNES file with mapper 0 (NROM). -/
def Machine.ofINes (file : ByteArray) : Except String Machine := do
  if file.size < 16 || file.get! 0 != 0x4E || file.get! 1 != 0x45 || file.get! 2 != 0x53 then
    throw "not an iNES file"
  let mapper := (file.get! 6 >>> 4) ||| (file.get! 7 &&& 0xF0)
  if mapper != 0 then throw s!"unsupported mapper {mapper}"
  let banks := (file.get! 4).toNat
  if banks != 1 && banks != 2 then throw s!"unsupported PRG size {banks}x16KiB"
  let trainer := if file.get! 6 &&& 4 != 0 then 512 else 0
  let prg := file.extract (16 + trainer) (16 + trainer + banks * 16384)
  return { prg, prgMask := if banks == 1 then 0x3FFF else 0x7FFF }

end Smbrta
