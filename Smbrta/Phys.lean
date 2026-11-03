import Smbrta.Movie
import Std.Data.HashMap
import Std.Data.HashSet
import Smbrta.Cert

/-!
# Mario's horizontal ground physics, defined by the game code itself

The model state `PState` holds the RAM bytes that the horizontal ground physics uses.
One model step does not re-implement anything: it writes the state into a real RAM
snapshot of the game (`ctx`), runs the game's own code of `PlayerCtrlRoutine` from its
entry up to `PlayerSubs` (just before it calls `ScrollHandler`), and reads the bytes back.
All addresses come from a symbol table (`Syms`).

Scope (assumptions, not proved in Lean):
* Mario stays on flat ground (A is never pressed, so he never jumps),
* nothing else touches these bytes during the frame (no walls, no screen edge, no enemies),
* Start and Select are not pressed.
`phys-validate` compares the model with the full emulator to test these assumptions.
-/

namespace Smbrta

/-! ## Running a piece of game code -/

/-- Run from `start` until the PC reaches `stop` (at most `fuel` instructions). NMIs are off. -/
def callRange (m : Machine) (start stop : UInt16) (fuel : Nat := 100000) : Machine :=
  go { m with pc := start, ppuCtrl := 0, nmiPending := false } fuel
where
  go (m : Machine) : Nat → Machine
    | 0 => m
    | n + 1 => if m.pc == stop || m.halted then m else go (step.run m).2 n

def poke (m : Machine) (addr : UInt16) (v : UInt8) : Machine :=
  let ram := m.ram
  let m := { m with ram := ByteArray.empty }
  { m with ram := ram.set! (addr &&& 0x7FF).toNat v }

/-! ## Model state -/

structure PState where
  speed : UInt8      -- Player_X_Speed (signed; pixels per frame × 16)
  fricMF : UInt8     -- Player_X_MoveForce (fraction used by the friction adder)
  posMF : UInt8      -- SprObject_X_MoveForce of the player (position fraction)
  absSpd : UInt8     -- Player_XSpeedAbsolute
  movDir : UInt8     -- Player_MovingDir
  faceDir : UInt8    -- PlayerFacingDir
  runSpd : UInt8     -- RunningSpeed
  runTmr : UInt8     -- RunningTimer
  deriving DecidableEq, Hashable, Repr, Inhabited

def PState.read (sy : Syms) (m : Machine) : PState where
  speed := peek m sy.Player_X_Speed
  fricMF := peek m sy.Player_X_MoveForce
  posMF := peek m sy.SprObject_X_MoveForce
  absSpd := peek m sy.Player_XSpeedAbsolute
  movDir := peek m sy.Player_MovingDir
  faceDir := peek m sy.PlayerFacingDir
  runSpd := peek m sy.RunningSpeed
  runTmr := peek m sy.RunningTimer

def PState.write (sy : Syms) (s : PState) (m : Machine) : Machine :=
  let m := poke m sy.Player_X_Speed s.speed
  let m := poke m sy.Player_X_MoveForce s.fricMF
  let m := poke m sy.SprObject_X_MoveForce s.posMF
  let m := poke m sy.Player_XSpeedAbsolute s.absSpd
  let m := poke m sy.Player_MovingDir s.movDir
  let m := poke m sy.PlayerFacingDir s.faceDir
  let m := poke m sy.RunningSpeed s.runSpd
  poke m sy.RunningTimer s.runTmr

/-- signed value of the speed byte -/
def PState.speedInt (s : PState) : Int :=
  if s.speed < 0x80 then s.speed.toNat else (s.speed.toNat : Int) - 256

/-- position (page:x) of the player in pixels -/
def playerX (sy : Syms) (m : Machine) : Int :=
  (peek m sy.Player_PageLoc).toNat * 256 + (peek m sy.Player_X_Position).toNat

/-- Prepare one frame: the state, the frame timer decremented (as the NMI does before the
game logic), and the input in `SavedJoypadBits` (A B Sel St U D L R = bit7..0). -/
def prepare (sy : Syms) (ctx : Machine) (s : PState) (inp : UInt8) : Machine :=
  let m := s.write sy ctx
  let t := s.runTmr
  let m := poke m sy.RunningTimer (if t == 0 then 0 else t - 1)
  poke m sy.SavedJoypadBits inp

/-- The game's horizontal step for one frame on top of `ctx`. Also returns the position delta. -/
def stepFull (sy : Syms) (ctx : Machine) (s : PState) (inp : UInt8) : PState × Int :=
  let m := prepare sy ctx s inp
  let x0 := playerX sy m
  let m := callRange m sy.PlayerCtrlRoutine sy.PlayerSubs
  (PState.read sy m, playerX sy m - x0)

def stepP (sy : Syms) (ctx : Machine) (s : PState) (inp : UInt8) : PState :=
  (stepFull sy ctx s inp).1

/-- Inputs without A, Start, Select: all subsets of {B, Up, Down, Left, Right}. -/
def groundInputs : List UInt8 :=
  (List.range 32).map fun (n : Nat) =>
    let i : UInt8 := n.toUInt8
    ((i &&& 16) <<< 2) ||| (i &&& 15)   -- bit4 of i -> B (0x40); bits0-3 -> R L D U

/-- Inputs a real controller can make: like `groundInputs` but never Left+Right or Up+Down
together (a D-pad cannot press opposite directions). -/
def padInputs : List UInt8 :=
  groundInputs.filter fun i => (i &&& 0x03) != 0x03 && (i &&& 0x0C) != 0x0C

/-- Forget the position fraction. The speed bytes do not depend on it (checked by
`phys-indep` on every search step). -/
def dropPos (s : PState) : PState := { s with posMF := 0 }

/-! ## Breadth-first search -/

open Std in
/-- Smallest number of frames after which some input sequence reaches a state with
`goal`, searching at most `maxDepth` frames. Returns the depth and one input sequence. -/
def bfs (step : PState → UInt8 → PState) (s0 : PState) (inputs : List UInt8)
    (goal : PState → Bool) (maxDepth : Nat) : Option (Nat × List UInt8) := Id.run do
  let mut parent : HashMap PState (PState × UInt8) := {}
  let mut visited : HashSet PState := HashSet.emptyWithCapacity 1024 |>.insert s0
  let mut layer : Array PState := #[s0]
  if goal s0 then return some (0, [])
  for d in [1:maxDepth + 1] do
    let mut next : Array PState := #[]
    for s in layer do
      for i in inputs do
        let t := step s i
        if !visited.contains t then
          visited := visited.insert t
          parent := parent.insert t (s, i)
          next := next.push t
          if goal t then
            let mut path : List UInt8 := []
            let mut cur := t
            for _ in [0:d] do
              match parent.get? cur with
              | some (p, inp) => path := inp :: path; cur := p
              | none => pure ()
            return some (d, path)
    layer := next
  return none

/-! ## The 1-1 starting context -/

/-- game layout (A B Sel St U D L R = bit7..0) to our controller byte (bit0..7 = A B Sel St U D L R) -/
def smbToPad (b : UInt8) : UInt8 := Id.run do
  let mut v : UInt8 := 0
  for i in [0:8] do
    if (b >>> i.toUInt8) &&& 1 == 1 then v := v ||| ((1 : UInt8) <<< (7 - i).toUInt8)
  return v

/-- the player is controllable: game mode, game core task, and the player control routine -/
def controllable (sy : Syms) (m : Machine) : Bool :=
  (peek m sy.OperMode).toUInt16 == sy.GameModeValue &&
  (peek m sy.OperMode_Task).toUInt16 == sy.Task_GameCore &&
  (peek m sy.GameEngineSubroutine).toUInt16 == sy.Eng_PlayerCtrl

/-- Power on, press Start on frame 39, then wait (no input) until the player is controllable
in 1-1. Returns the machine at that frame boundary. -/
def smb11Start (sy : Syms) (cart : Machine) : Machine := Id.run do
  let mut m := powerOn cart 0
  for k in [0:600] do
    m := runFrame m (if k == 39 then 0x08 else 0)
    if k > 39 && controllable sy m then return m
  return m

/-- the game is cleared: victory mode in the last world (world 8) -/
def smbCleared (sy : Syms) (m : Machine) : Bool :=
  (peek m sy.OperMode).toUInt16 == sy.VictoryModeValue && peek m sy.WorldNumber == 7

/-! ## Which RAM bytes does the step use? -/

/-- `stepFull` with access tracking. Returns the new state, the RAM bytes read before being
written, the RAM bytes written, and whether an I/O register was read. The bytes injected
before the run (the state, the timer, the input) are not counted as writes. -/
def stepTracked (sy : Syms) (ctx : Machine) (s : PState) (inp : UInt8) :
    PState × ByteArray × ByteArray × Bool :=
  let m := prepare sy ctx s inp
  let z := ByteArray.mk (Array.replicate 2048 0)
  let m := { m with trk := true, trkRead := z, trkWrite := z, trkIO := false }
  let m := callRange m sy.PlayerCtrlRoutine sy.PlayerSubs
  (PState.read sy m, m.trkRead, m.trkWrite, m.trkIO)

/-- RAM addresses whose flag is set in `b` -/
def flagged (b : ByteArray) : List Nat :=
  (List.range 2048).filter fun i => b.get! i != 0

end Smbrta
