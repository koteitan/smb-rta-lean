import Smbrta.Phys

/-!
# A model of Mario's movement with jumping, defined by the game code

The state is the list of values of a set of RAM bytes (`Model.vars`). One frame:
1. the NMI's `DecTimers`: every frame timer in `vars` is decremented if not 0,
2. the input is stored in `SavedJoypadBits` (A B Sel St U D L R = bit7..0),
3. the whole `PlayerCtrlRoutine` runs, called like a subroutine
   (it includes scrolling and the background collision, so landing is the game's own),
4. the end of `GameEngine` (`SaveAB`): `PreviousA_B_Buttons` := `A_B_Buttons`,
   `Left_Right_Buttons` := 0.
Everything else in the frame (enemies, blocks, timers outside `vars`) is left out.
The set `vars` is not written down: `discoverCarried` finds it by access tracking.
-/

namespace Smbrta

abbrev GState := Array UInt8

structure Model where
  sy : Syms
  ctx : Machine
  vars : Array UInt16
  deriving Inhabited

/-- frame timers: `Timers` .. `Timers + FrameTimersLast` (decremented every frame) -/
def isFrameTimer (sy : Syms) (a : UInt16) : Bool :=
  sy.Timers ≤ a && a ≤ sy.Timers + sy.FrameTimersLast

def Model.read (md : Model) (m : Machine) : GState := md.vars.map (peek m ·)

def Model.write (md : Model) (s : GState) (m : Machine) : Machine := Id.run do
  let mut m := m
  for h : k in [0:md.vars.size] do
    m := poke m md.vars[k] (s[k]?.getD 0)
  return m

/-- Call the subroutine at `addr` (JSR with a sentinel return address) and run it to its RTS. -/
def callSub (m : Machine) (addr : UInt16) (fuel : Nat := 200000) : Machine :=
  -- push $0000 as the return address; RTS then sets PC = $0001
  let sp := m.s
  let m := poke m (0x0100 ||| sp.toUInt16) 0x00
  let m := poke m (0x0100 ||| (sp - 1).toUInt16) 0x00
  let m := { m with s := sp - 2 }
  callRange m addr 0x0001 fuel

/-- one frame on the machine `m` (all of its RAM is the state); `track` records accesses -/
def frameOn (sy : Syms) (m : Machine) (inp : UInt8) (timers : List UInt16)
    (track : Bool := false) : Machine := Id.run do
  let mut m := m
  for a in timers do
    let t := peek m a
    if t != 0 then m := poke m a (t - 1)
  m := poke m sy.SavedJoypadBits inp
  if track then
    let z := ByteArray.mk (Array.replicate 2048 0)
    m := { m with trk := true, trkRead := z, trkWrite := z, trkIO := false }
  m := callSub m sy.PlayerCtrlRoutine
  m := { m with trk := false }
  m := poke m sy.PreviousA_B_Buttons (peek m sy.A_B_Buttons)
  poke m sy.Left_Right_Buttons 0

def Model.stepM (md : Model) (s : GState) (inp : UInt8) (track : Bool := false) : Machine :=
  frameOn md.sy (md.write s md.ctx) inp ((md.vars.filter (isFrameTimer md.sy)).toList) track

def Model.step (md : Model) (s : GState) (inp : UInt8) : GState := md.read (md.stepM s inp)

/-- Inputs a real controller can make, now with A: `padInputs` × {A not pressed, A pressed}. -/
def padInputsA : List UInt8 := padInputs ++ padInputs.map (· ||| 0x80)

/-- All inputs without Start/Select, Left+Right and Up+Down allowed (TAS rules). -/
def lrInputsA : List UInt8 := groundInputs ++ groundInputs.map (· ||| 0x80)

/-! ## Finding the carried bytes -/

/-- Random walks from `ctx` with every RAM byte carried; returns the bytes the frame reads
before writing and that are written by the frame or by the emulated parts outside it
(frame timers, `PreviousA_B_Buttons`), and whether an I/O register was read. Walks stop
when Mario leaves the open area `x ∈ [lo, hi]`. -/
def discoverCarried (sy : Syms) (ctx : Machine) (walks len : Nat) (lo hi : Int) :
    List UInt16 × Bool := Id.run do
  let allTimers := (List.range 2048).map (·.toUInt16) |>.filter (isFrameTimer sy)
  let mut rdAny := ByteArray.mk (Array.replicate 2048 0)
  let mut wrAny := ByteArray.mk (Array.replicate 2048 0)
  let mut io := false
  let ins := padInputsA.toArray
  let mut seed : Nat := 777
  for _ in [0:walks] do
    let mut m := ctx
    let mut inp : UInt8 := 0
    for _ in [0:len] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      if (seed / 65536) % 4 == 0 then inp := ins[(seed / 256) % ins.size]!
      m := frameOn sy m inp allTimers true
      for k in [0:2048] do
        if m.trkRead.get! k != 0 then rdAny := rdAny.set! k 1
        if m.trkWrite.get! k != 0 then wrAny := wrAny.set! k 1
      io := io || m.trkIO
      let x := playerX sy m
      if x > hi || x < lo then break
  let ext := fun (k : UInt16) => k == sy.PreviousA_B_Buttons || isFrameTimer sy k
  let carried := (List.range 2048).filter fun k =>
    rdAny.get! k != 0 && (wrAny.get! k != 0 || ext k.toUInt16)
  return (carried.map (·.toUInt16), io)

/-- carried bytes without the position, the platform scroll, and the sprite attribute -/
def movementVars (sy : Syms) (carried : List UInt16) : Array UInt16 :=
  (carried.filter fun a => ![sy.Player_X_Position, sy.Player_PageLoc, sy.SprObject_X_MoveForce,
    sy.Platform_X_Scroll, sy.Player_SprAttrib].contains a).toArray

/-! ## Relaxed model: vertical motion replaced by a free choice

In the air the horizontal code reads none of the vertical bytes: only `Player_State`
(ground or not) matters. So the relaxed state is the horizontal state plus a flag `air`.
A jump starts exactly as in the game (A newly pressed on the ground); in the air the
player may land at the end of any frame (`land`), which every real jump also does at
some frame. So every real run is a run of the relaxed model, and a lower bound for the
relaxed model is a lower bound for the real game (in the open area, where
`Player_CollisionBits` does not change). -/

structure RState where
  h : PState
  air : Bool
  deriving DecidableEq, Hashable, Repr, Inhabited

def stepRelax (sy : Syms) (ctx : Machine) (s : RState) (c : UInt8 × Bool) : RState :=
  let (inp, land) := c
  let m := poke ctx sy.Player_State (if s.air then 1 else 0)
  let m := poke m sy.PreviousA_B_Buttons 0   -- A in `inp` is a new press
  let m := prepare sy m s.h inp
  let m := callRange m sy.PlayerCtrlRoutine sy.PlayerSubs
  let air' := if s.air then !land else peek m sy.Player_State != 0
  { h := dropPos (PState.read sy m), air := air' }

/-- relaxed inputs: real-controller inputs with A, and the landing choice -/
def relaxInputs : List (UInt8 × Bool) :=
  padInputsA.flatMap fun i => [(i, false), (i, true)]

/-- relaxed inputs with Left+Right allowed -/
def relaxInputsLR : List (UInt8 × Bool) :=
  lrInputsA.flatMap fun i => [(i, false), (i, true)]

/-- project a state of the exact model to the relaxed state -/
def Model.toRelax (md : Model) (s : GState) : RState :=
  let g := fun (a : UInt16) => match md.vars.findIdx? (· == a) with
    | some k => s[k]?.getD 0
    | none => 0
  let sy := md.sy
  { h := { speed := g sy.Player_X_Speed, fricMF := g sy.Player_X_MoveForce, posMF := 0,
           absSpd := g sy.Player_XSpeedAbsolute, movDir := g sy.Player_MovingDir,
           faceDir := g sy.PlayerFacingDir, runSpd := g sy.RunningSpeed,
           runTmr := g sy.RunningTimer },
    air := g sy.Player_State != 0 }

/-- Play `path` (game layout inputs) on the full emulator. -/
def playFull (m : Machine) (path : List UInt8) : Machine :=
  path.foldl (fun m i => runFrame m (smbToPad i)) m

end Smbrta
