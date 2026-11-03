import Smbrta.Cpu
import Smbrta.Syms

/-!
# Movies (FCEUX .fm2) and the runner

Each movie frame gives the buttons of controller 1 for one frame.
Frame `k` of the movie is the time between vblank start `k` and `k+1`.
-/

namespace Smbrta

/-- Convert an fm2 port string `RLDUTSBA` to the byte the game reads
(bit0..7 = A B Select Start Up Down Left Right). -/
def fm2PadByte (s : String) : UInt8 := Id.run do
  let cs := s.toList
  let mut v : UInt8 := 0
  for i in [0:8] do
    let c := cs.getD i '.'
    if c != '.' && c != ' ' then
      v := v ||| ((1 : UInt8) <<< (7 - i).toUInt8)
  return v

/-- Parse the controller-1 bytes of every frame of an fm2 file. -/
def parseFm2 (text : String) : Array UInt8 := Id.run do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "|" then
      let fields := line.splitOn "|"
      -- fields = ["", cmd, port0, port1, ...]
      out := out.push (fm2PadByte (fields.getD 2 ""))
  return out

def peek (m : Machine) (addr : UInt16) : UInt8 := m.ram.get! (addr &&& 0x7FF).toNat

/-- instructions allowed per frame before we give up (a real frame has far fewer) -/
def fuelPerFrame : Nat := 100000

/-- Power on: load the cartridge, set the PPU position, run the reset sequence. -/
def powerOn (cart : Machine) (startDot : Nat) : Machine :=
  (reset.run { cart with fdot := startDot }).2

/-- Run one movie frame with the given buttons. -/
def runFrame (m : Machine) (buttons : UInt8) : Machine :=
  let m := { m with pad := buttons }
  (runUntilFrame (m.frame + 1) fuelPerFrame |>.run m).2

/-- Run the movie; return the first movie frame index after which `stop` holds. -/
def firstFrameWhere (m : Machine) (inputs : Array UInt8) (stop : Machine → Bool) :
    Option Nat × Machine := Id.run do
  let mut m := m
  for h : k in [0:inputs.size] do
    m := runFrame m inputs[k]
    if stop m then return (some k, m)
  return (none, m)

end Smbrta

namespace Smbrta

/-! ## Hex strings (used to embed the ROM and the movie in a generated Lean file) -/

def hexDigit (c : Char) : UInt8 :=
  if '0' ≤ c && c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'A' ≤ c && c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else if 'a' ≤ c && c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else 0

def hexDecode (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    out := out.push ((hexDigit cs[2*i]!) <<< 4 ||| hexDigit cs[2*i+1]!)
  return out

def hexEncode (b : ByteArray) : String := Id.run do
  let d := "0123456789ABCDEF".toList.toArray
  let mut out := ""
  for v in b.toList do
    out := out.push d[(v >>> 4).toNat]!
    out := out.push d[(v &&& 15).toNat]!
  return out

end Smbrta

namespace Smbrta

/-- Movie frames to drop so that our frame 0 lines up with FCEUX.
Found by experiment: with 2 the HappyLee "warps" movie clears the game;
with 0, ±1, 3 (and -1..-3 meaning extra blank frames) Mario desyncs in 1-1.
Our power-on reaches the first input poll two vblanks later than FCEUX. -/
def fceuxSkip : Nat := 2

/-- Movie inputs as our emulator consumes them. -/
def alignInputs (movie : Array UInt8) (skip : Nat := fceuxSkip) : Array UInt8 :=
  movie.extract skip movie.size

end Smbrta
