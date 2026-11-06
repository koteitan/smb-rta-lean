/-!
# Game symbols

Addresses and values of the game that the model needs: RAM variables, two points in the
code, and a few values. The repository contains only their names (taken from the
community disassembly). Their values are read at run time from a symbol file made by
`tools/extract_syms.py` from the ROM and the disassembly, and generated proof files
embed them.
-/

namespace Smbrta

structure Syms where
  Player_X_Speed : UInt16
  Player_X_MoveForce : UInt16
  SprObject_X_MoveForce : UInt16
  Player_XSpeedAbsolute : UInt16
  Player_MovingDir : UInt16
  PlayerFacingDir : UInt16
  RunningSpeed : UInt16
  RunningTimer : UInt16
  SavedJoypadBits : UInt16
  Player_X_Position : UInt16
  Player_PageLoc : UInt16
  OperMode : UInt16
  OperMode_Task : UInt16
  WorldNumber : UInt16
  LevelNumber : UInt16
  NumberofLives : UInt16
  GameEngineSubroutine : UInt16
  Player_State : UInt16
  PreviousA_B_Buttons : UInt16
  A_B_Buttons : UInt16
  Left_Right_Buttons : UInt16
  Timers : UInt16
  Player_Y_Position : UInt16
  Player_Y_HighPos : UInt16
  Player_Y_Speed : UInt16
  Player_YMF_Dummy : UInt16
  Player_Y_MoveForce : UInt16
  JumpOrigin_Y_Position : UInt16
  DiffToHaltJump : UInt16
  VerticalForce : UInt16
  VerticalForceDown : UInt16
  Platform_X_Scroll : UInt16
  Player_SprAttrib : UInt16
  Player_CollisionBits : UInt16
  PlayerCtrlRoutine : UInt16
  PlayerSubs : UInt16
  GameModeValue : UInt16
  VictoryModeValue : UInt16
  Task_GameCore : UInt16
  Eng_PlayerCtrl : UInt16
  FrameTimersLast : UInt16
  RunTopSpeed : UInt16
  PlayerSize : UInt16
  AreaType : UInt16
  SwimmingFlag : UInt16
  PlayerChangeSizeFlag : UInt16
  JumpspringAnimCtrl : UInt16
  TimerControl : UInt16
  Up_Down_Buttons : UInt16
  JoypadBitMask : UInt16
  StarFlagTaskControl : UInt16
  X_Physics : UInt16
  ImposeFriction : UInt16
  MoveObjectHorizontally : UInt16
  ImpedePlayerMove : UInt16
  MaximumRightSpeed : UInt16
  MaximumLeftSpeed : UInt16
  FrictionAdderLow : UInt16
  FrictionAdderHigh : UInt16
  SideCollisionTimer : UInt16
  MaxRightXSpdData : UInt16
  MaxLeftXSpdData : UInt16
  FrictionData : UInt16
  GetPlayerAnimSpeed : UInt16
  RunTimerReset : UInt16
  RunSpeedMin : UInt16
  AirFastSpeed : UInt16
  MaxFallSpeed : UInt16
  PlayerBGCollision : UInt16
  Block_Buffer_1 : UInt16
  MetatileBuffer : UInt16
  FlagColumnByte : UInt16
  FlagBallTile : UInt16
  FlagShaftTile : UInt16
  FlagBaseTile : UInt16
  FlagBaseOperand : UInt16
  GroundTile : UInt16
  FeetAdderX : UInt16
  SideAdderX : UInt16
  FeetAdderY : UInt16
  SideAdderY : UInt16
  BlockBufferTopY : UInt16
  LandDepth : UInt16
  ClimbLowNybble : UInt16
  ClimbHighNybble : UInt16
  FastJumpSpeed : UInt16
  PlayerMovementSubs : UInt16
  FlagGrabY : UInt16
  PipeRightTile : UInt16
  PipeLeftTile : UInt16
  EngVerticalPipe : UInt16
  PipeColumnByte : UInt16
  RoomBlockLeftByte : UInt16
  RoomBlockRightByte : UInt16
  RoomStartX : UInt16
  L_GroundArea6 : UInt16
  SidePipeTile : UInt16
  SidePipeTopTile : UInt16
  EngSidePipe : UInt16
  RoomPipeByte : UInt16
  deriving Repr, Inhabited

/-- every field with its name, in the order of `tools/smb-symbols.txt` -/
def Syms.fields : List (String × (Syms → UInt16)) := [
  ("Player_X_Speed", fun s => s.Player_X_Speed),
  ("Player_X_MoveForce", fun s => s.Player_X_MoveForce),
  ("SprObject_X_MoveForce", fun s => s.SprObject_X_MoveForce),
  ("Player_XSpeedAbsolute", fun s => s.Player_XSpeedAbsolute),
  ("Player_MovingDir", fun s => s.Player_MovingDir),
  ("PlayerFacingDir", fun s => s.PlayerFacingDir),
  ("RunningSpeed", fun s => s.RunningSpeed),
  ("RunningTimer", fun s => s.RunningTimer),
  ("SavedJoypadBits", fun s => s.SavedJoypadBits),
  ("Player_X_Position", fun s => s.Player_X_Position),
  ("Player_PageLoc", fun s => s.Player_PageLoc),
  ("OperMode", fun s => s.OperMode),
  ("OperMode_Task", fun s => s.OperMode_Task),
  ("WorldNumber", fun s => s.WorldNumber),
  ("LevelNumber", fun s => s.LevelNumber),
  ("NumberofLives", fun s => s.NumberofLives),
  ("GameEngineSubroutine", fun s => s.GameEngineSubroutine),
  ("Player_State", fun s => s.Player_State),
  ("PreviousA_B_Buttons", fun s => s.PreviousA_B_Buttons),
  ("A_B_Buttons", fun s => s.A_B_Buttons),
  ("Left_Right_Buttons", fun s => s.Left_Right_Buttons),
  ("Timers", fun s => s.Timers),
  ("Player_Y_Position", fun s => s.Player_Y_Position),
  ("Player_Y_HighPos", fun s => s.Player_Y_HighPos),
  ("Player_Y_Speed", fun s => s.Player_Y_Speed),
  ("Player_YMF_Dummy", fun s => s.Player_YMF_Dummy),
  ("Player_Y_MoveForce", fun s => s.Player_Y_MoveForce),
  ("JumpOrigin_Y_Position", fun s => s.JumpOrigin_Y_Position),
  ("DiffToHaltJump", fun s => s.DiffToHaltJump),
  ("VerticalForce", fun s => s.VerticalForce),
  ("VerticalForceDown", fun s => s.VerticalForceDown),
  ("Platform_X_Scroll", fun s => s.Platform_X_Scroll),
  ("Player_SprAttrib", fun s => s.Player_SprAttrib),
  ("Player_CollisionBits", fun s => s.Player_CollisionBits),
  ("PlayerCtrlRoutine", fun s => s.PlayerCtrlRoutine),
  ("PlayerSubs", fun s => s.PlayerSubs),
  ("GameModeValue", fun s => s.GameModeValue),
  ("VictoryModeValue", fun s => s.VictoryModeValue),
  ("Task_GameCore", fun s => s.Task_GameCore),
  ("Eng_PlayerCtrl", fun s => s.Eng_PlayerCtrl),
  ("FrameTimersLast", fun s => s.FrameTimersLast),
  ("RunTopSpeed", fun s => s.RunTopSpeed),
  ("PlayerSize", fun s => s.PlayerSize),
  ("AreaType", fun s => s.AreaType),
  ("SwimmingFlag", fun s => s.SwimmingFlag),
  ("PlayerChangeSizeFlag", fun s => s.PlayerChangeSizeFlag),
  ("JumpspringAnimCtrl", fun s => s.JumpspringAnimCtrl),
  ("TimerControl", fun s => s.TimerControl),
  ("Up_Down_Buttons", fun s => s.Up_Down_Buttons),
  ("JoypadBitMask", fun s => s.JoypadBitMask),
  ("StarFlagTaskControl", fun s => s.StarFlagTaskControl),
  ("X_Physics", fun s => s.X_Physics),
  ("ImposeFriction", fun s => s.ImposeFriction),
  ("MoveObjectHorizontally", fun s => s.MoveObjectHorizontally),
  ("ImpedePlayerMove", fun s => s.ImpedePlayerMove),
  ("MaximumRightSpeed", fun s => s.MaximumRightSpeed),
  ("MaximumLeftSpeed", fun s => s.MaximumLeftSpeed),
  ("FrictionAdderLow", fun s => s.FrictionAdderLow),
  ("FrictionAdderHigh", fun s => s.FrictionAdderHigh),
  ("SideCollisionTimer", fun s => s.SideCollisionTimer),
  ("MaxRightXSpdData", fun s => s.MaxRightXSpdData),
  ("MaxLeftXSpdData", fun s => s.MaxLeftXSpdData),
  ("FrictionData", fun s => s.FrictionData),
  ("GetPlayerAnimSpeed", fun s => s.GetPlayerAnimSpeed),
  ("RunTimerReset", fun s => s.RunTimerReset),
  ("RunSpeedMin", fun s => s.RunSpeedMin),
  ("AirFastSpeed", fun s => s.AirFastSpeed),
  ("MaxFallSpeed", fun s => s.MaxFallSpeed),
  ("PlayerBGCollision", fun s => s.PlayerBGCollision),
  ("Block_Buffer_1", fun s => s.Block_Buffer_1),
  ("MetatileBuffer", fun s => s.MetatileBuffer),
  ("FlagColumnByte", fun s => s.FlagColumnByte),
  ("FlagBallTile", fun s => s.FlagBallTile),
  ("FlagShaftTile", fun s => s.FlagShaftTile),
  ("FlagBaseTile", fun s => s.FlagBaseTile),
  ("FlagBaseOperand", fun s => s.FlagBaseOperand),
  ("GroundTile", fun s => s.GroundTile),
  ("FeetAdderX", fun s => s.FeetAdderX),
  ("SideAdderX", fun s => s.SideAdderX),
  ("FeetAdderY", fun s => s.FeetAdderY),
  ("SideAdderY", fun s => s.SideAdderY),
  ("BlockBufferTopY", fun s => s.BlockBufferTopY),
  ("LandDepth", fun s => s.LandDepth),
  ("ClimbLowNybble", fun s => s.ClimbLowNybble),
  ("ClimbHighNybble", fun s => s.ClimbHighNybble),
  ("FastJumpSpeed", fun s => s.FastJumpSpeed),
  ("PlayerMovementSubs", fun s => s.PlayerMovementSubs),
  ("FlagGrabY", fun s => s.FlagGrabY),
  ("PipeRightTile", fun s => s.PipeRightTile),
  ("PipeLeftTile", fun s => s.PipeLeftTile),
  ("EngVerticalPipe", fun s => s.EngVerticalPipe),
  ("PipeColumnByte", fun s => s.PipeColumnByte),
  ("RoomBlockLeftByte", fun s => s.RoomBlockLeftByte),
  ("RoomBlockRightByte", fun s => s.RoomBlockRightByte),
  ("RoomStartX", fun s => s.RoomStartX),
  ("L_GroundArea6", fun s => s.L_GroundArea6),
  ("SidePipeTile", fun s => s.SidePipeTile),
  ("SidePipeTopTile", fun s => s.SidePipeTopTile),
  ("EngSidePipe", fun s => s.EngSidePipe),
  ("RoomPipeByte", fun s => s.RoomPipeByte)]

/-- Parse a symbol file (`key value` per line, decimal). -/
def Syms.parse (text : String) : Except String Syms := do
  let mut tbl : List (String × Nat) := []
  for line in text.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [k, v] => tbl := (k, v.toNat!) :: tbl
    | _ => pure ()
  let get := fun (k : String) => match tbl.lookup k with
    | some v => Except.ok v.toUInt16
    | none => Except.error s!"symbol {k} missing"
  return {
    Player_X_Speed := ← get "Player_X_Speed"
    Player_X_MoveForce := ← get "Player_X_MoveForce"
    SprObject_X_MoveForce := ← get "SprObject_X_MoveForce"
    Player_XSpeedAbsolute := ← get "Player_XSpeedAbsolute"
    Player_MovingDir := ← get "Player_MovingDir"
    PlayerFacingDir := ← get "PlayerFacingDir"
    RunningSpeed := ← get "RunningSpeed"
    RunningTimer := ← get "RunningTimer"
    SavedJoypadBits := ← get "SavedJoypadBits"
    Player_X_Position := ← get "Player_X_Position"
    Player_PageLoc := ← get "Player_PageLoc"
    OperMode := ← get "OperMode"
    OperMode_Task := ← get "OperMode_Task"
    WorldNumber := ← get "WorldNumber"
    LevelNumber := ← get "LevelNumber"
    NumberofLives := ← get "NumberofLives"
    GameEngineSubroutine := ← get "GameEngineSubroutine"
    Player_State := ← get "Player_State"
    PreviousA_B_Buttons := ← get "PreviousA_B_Buttons"
    A_B_Buttons := ← get "A_B_Buttons"
    Left_Right_Buttons := ← get "Left_Right_Buttons"
    Timers := ← get "Timers"
    Player_Y_Position := ← get "Player_Y_Position"
    Player_Y_HighPos := ← get "Player_Y_HighPos"
    Player_Y_Speed := ← get "Player_Y_Speed"
    Player_YMF_Dummy := ← get "Player_YMF_Dummy"
    Player_Y_MoveForce := ← get "Player_Y_MoveForce"
    JumpOrigin_Y_Position := ← get "JumpOrigin_Y_Position"
    DiffToHaltJump := ← get "DiffToHaltJump"
    VerticalForce := ← get "VerticalForce"
    VerticalForceDown := ← get "VerticalForceDown"
    Platform_X_Scroll := ← get "Platform_X_Scroll"
    Player_SprAttrib := ← get "Player_SprAttrib"
    Player_CollisionBits := ← get "Player_CollisionBits"
    PlayerCtrlRoutine := ← get "PlayerCtrlRoutine"
    PlayerSubs := ← get "PlayerSubs"
    GameModeValue := ← get "GameModeValue"
    VictoryModeValue := ← get "VictoryModeValue"
    Task_GameCore := ← get "Task_GameCore"
    Eng_PlayerCtrl := ← get "Eng_PlayerCtrl"
    FrameTimersLast := ← get "FrameTimersLast"
    RunTopSpeed := ← get "RunTopSpeed"
    PlayerSize := ← get "PlayerSize"
    AreaType := ← get "AreaType"
    SwimmingFlag := ← get "SwimmingFlag"
    PlayerChangeSizeFlag := ← get "PlayerChangeSizeFlag"
    JumpspringAnimCtrl := ← get "JumpspringAnimCtrl"
    TimerControl := ← get "TimerControl"
    Up_Down_Buttons := ← get "Up_Down_Buttons"
    JoypadBitMask := ← get "JoypadBitMask"
    StarFlagTaskControl := ← get "StarFlagTaskControl"
    X_Physics := ← get "X_Physics"
    ImposeFriction := ← get "ImposeFriction"
    MoveObjectHorizontally := ← get "MoveObjectHorizontally"
    ImpedePlayerMove := ← get "ImpedePlayerMove"
    MaximumRightSpeed := ← get "MaximumRightSpeed"
    MaximumLeftSpeed := ← get "MaximumLeftSpeed"
    FrictionAdderLow := ← get "FrictionAdderLow"
    FrictionAdderHigh := ← get "FrictionAdderHigh"
    SideCollisionTimer := ← get "SideCollisionTimer"
    MaxRightXSpdData := ← get "MaxRightXSpdData"
    MaxLeftXSpdData := ← get "MaxLeftXSpdData"
    FrictionData := ← get "FrictionData"
    GetPlayerAnimSpeed := ← get "GetPlayerAnimSpeed"
    RunTimerReset := ← get "RunTimerReset"
    RunSpeedMin := ← get "RunSpeedMin"
    AirFastSpeed := ← get "AirFastSpeed"
    MaxFallSpeed := ← get "MaxFallSpeed"
    PlayerBGCollision := ← get "PlayerBGCollision"
    Block_Buffer_1 := ← get "Block_Buffer_1"
    MetatileBuffer := ← get "MetatileBuffer"
    FlagColumnByte := ← get "FlagColumnByte"
    FlagBallTile := ← get "FlagBallTile"
    FlagShaftTile := ← get "FlagShaftTile"
    FlagBaseTile := ← get "FlagBaseTile"
    FlagBaseOperand := ← get "FlagBaseOperand"
    GroundTile := ← get "GroundTile"
    FeetAdderX := ← get "FeetAdderX"
    SideAdderX := ← get "SideAdderX"
    FeetAdderY := ← get "FeetAdderY"
    SideAdderY := ← get "SideAdderY"
    BlockBufferTopY := ← get "BlockBufferTopY"
    LandDepth := ← get "LandDepth"
    ClimbLowNybble := ← get "ClimbLowNybble"
    ClimbHighNybble := ← get "ClimbHighNybble"
    FastJumpSpeed := ← get "FastJumpSpeed"
    PlayerMovementSubs := ← get "PlayerMovementSubs"
    FlagGrabY := ← get "FlagGrabY"
    PipeRightTile := ← get "PipeRightTile"
    PipeLeftTile := ← get "PipeLeftTile"
    EngVerticalPipe := ← get "EngVerticalPipe"
    PipeColumnByte := ← get "PipeColumnByte"
    RoomBlockLeftByte := ← get "RoomBlockLeftByte"
    RoomBlockRightByte := ← get "RoomBlockRightByte"
    RoomStartX := ← get "RoomStartX"
    L_GroundArea6 := ← get "L_GroundArea6"
    SidePipeTile := ← get "SidePipeTile"
    SidePipeTopTile := ← get "SidePipeTopTile"
    EngSidePipe := ← get "EngSidePipe"
    RoomPipeByte := ← get "RoomPipeByte"
  }

def Syms.load (path : String) : IO Syms := do
  match Syms.parse (← IO.FS.readFile path) with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Lean source of this symbol table (for generated proof files) -/
def Syms.toLean (s : Syms) : String :=
  "{ " ++ ", ".intercalate (Syms.fields.map fun (k, f) => s!"{k} := {(f s).toNat}") ++ " }"

end Smbrta
