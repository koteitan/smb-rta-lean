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
  Eng_PlayerEntrance : UInt16
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
  EngFlagpole : UInt16
  EngEndLevel : UInt16
  DoFootCheck : UInt16
  DoPlayerSideCheck : UInt16
  AwardTouchedCoin : UInt16
  HandleAxeMetatile : UInt16
  BlockBufferCollision : UInt16
  HandlePipeEntry : UInt16
  BlockBufferAdderData : UInt16
  Block_Buffer_2 : UInt16
  Left_Dir : UInt16
  Right_Dir : UInt16
  PipeColumnByte : UInt16
  RoomBlockLeftByte : UInt16
  RoomBlockRightByte : UInt16
  RoomStartX : UInt16
  L_GroundArea6 : UInt16
  SidePipeTile : UInt16
  SidePipeTopTile : UInt16
  EngSidePipe : UInt16
  RoomPipeByte : UInt16
  StarFlagTopY : UInt16
  StarFlagDelay : UInt16
  NonMaskableInterrupt : UInt16
  SoundEngine : UInt16
  MusicHandler : UInt16
  HandleSquare1Music : UInt16
  HandleTriangleMusic : UInt16
  HandleNoiseMusic : UInt16
  SkipSoundSubroutines : UInt16
  PauseSfxValue : UInt16
  UnpauseSfxValue : UInt16
  PauseSfxLength : UInt16
  ReadPortBits : UInt16
  GameEngine : UInt16
  ProcELoop : UInt16
  EnemyGfxHandler : UInt16
  GetEnemyBoundBox : UInt16
  PlayerGfxHandler : UInt16
  BlockObjMT_Updater : UInt16
  FlagpoleRoutine : UInt16
  ColorRotation : UInt16
  UpdScrollVar : UInt16
  ExitEng : UInt16
  HandleEToBGCollision : UInt16
  PositionEnemyObj : UInt16
  CheckRightExtBounds : UInt16
  JumpEngine : UInt16
  ReadJoypads : UInt16
  DecTimers : UInt16
  NoDecTimers : UInt16
  PlayerEndLevel : UInt16
  GetPlayerOffscreenBits : UInt16
  RunStarFlagObj : UInt16
  FloateyNumbersRoutine : UInt16
  RunGameTimer : UInt16
  XLdBData : UInt16
  GetXOffscreenBits : UInt16
  FetchSqu1MusicData : UInt16
  MiscSqu1MusicTasks : UInt16
  ExXOfsBS : UInt16
  SideTimerBump : UInt16
  CollisionInit : UInt16
  EndlessLoop : UInt16
  SetVRAMOffset : UInt16
  GetPlayerColors : UInt16
  UpdateScreen : UInt16
  OutputToVRAM : UInt16
  RepeatByte : UInt16
  OutputNumbers : UInt16
  ExitOutputN : UInt16
  UpdateNumber : UInt16
  NoZSup : UInt16
  ExitColorRot : UInt16
  ProcMove : UInt16
  MoveSubs : UInt16
  SideCheckLoop : UInt16
  BHalf : UInt16
  ErACM : UInt16
  PlyrPipe : UInt16
  AreaChangeTimerData : UInt16
  SkipMainOper : UInt16
  CoinTile : UInt16
  RunFR : UInt16
  ExSCH : UInt16
  ExCSM : UInt16
  ExHC : UInt16
  ContSChk : UInt16
  VineCollision : UInt16
  OnGroundStateSub : UInt16
  LRAir : UInt16
  PJumpSnd : UInt16
  MovePlayerVertically : UInt16
  NoJSChk : UInt16
  RghtFrict : UInt16
  AreaParserCore : UInt16
  GetBlockBufferAddr : UInt16
  PlayerHeadCollision : UInt16
  BlockObjectsCore : UInt16
  CRendLoop : UInt16
  ChkCFloor : UInt16
  BlockBufferColumnPos : UInt16
  SprDataOffset_Ctrl : UInt16
  CheckTopOfBlock : UInt16
  CoinTile2 : UInt16
  ExecGameLoopback : UInt16
  SpriteShuffler : UInt16
  RenderUnderPart : UInt16
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
  ("Eng_PlayerEntrance", fun s => s.Eng_PlayerEntrance),
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
  ("EngFlagpole", fun s => s.EngFlagpole),
  ("EngEndLevel", fun s => s.EngEndLevel),
  ("DoFootCheck", fun s => s.DoFootCheck),
  ("DoPlayerSideCheck", fun s => s.DoPlayerSideCheck),
  ("AwardTouchedCoin", fun s => s.AwardTouchedCoin),
  ("HandleAxeMetatile", fun s => s.HandleAxeMetatile),
  ("BlockBufferCollision", fun s => s.BlockBufferCollision),
  ("HandlePipeEntry", fun s => s.HandlePipeEntry),
  ("BlockBufferAdderData", fun s => s.BlockBufferAdderData),
  ("Block_Buffer_2", fun s => s.Block_Buffer_2),
  ("Left_Dir", fun s => s.Left_Dir),
  ("Right_Dir", fun s => s.Right_Dir),
  ("PipeColumnByte", fun s => s.PipeColumnByte),
  ("RoomBlockLeftByte", fun s => s.RoomBlockLeftByte),
  ("RoomBlockRightByte", fun s => s.RoomBlockRightByte),
  ("RoomStartX", fun s => s.RoomStartX),
  ("L_GroundArea6", fun s => s.L_GroundArea6),
  ("SidePipeTile", fun s => s.SidePipeTile),
  ("SidePipeTopTile", fun s => s.SidePipeTopTile),
  ("EngSidePipe", fun s => s.EngSidePipe),
  ("RoomPipeByte", fun s => s.RoomPipeByte),
  ("StarFlagTopY", fun s => s.StarFlagTopY),
  ("StarFlagDelay", fun s => s.StarFlagDelay),
  ("NonMaskableInterrupt", fun s => s.NonMaskableInterrupt),
  ("SoundEngine", fun s => s.SoundEngine),
  ("MusicHandler", fun s => s.MusicHandler),
  ("HandleSquare1Music", fun s => s.HandleSquare1Music),
  ("HandleTriangleMusic", fun s => s.HandleTriangleMusic),
  ("HandleNoiseMusic", fun s => s.HandleNoiseMusic),
  ("SkipSoundSubroutines", fun s => s.SkipSoundSubroutines),
  ("PauseSfxValue", fun s => s.PauseSfxValue),
  ("UnpauseSfxValue", fun s => s.UnpauseSfxValue),
  ("PauseSfxLength", fun s => s.PauseSfxLength),
  ("ReadPortBits", fun s => s.ReadPortBits),
  ("GameEngine", fun s => s.GameEngine),
  ("ProcELoop", fun s => s.ProcELoop),
  ("EnemyGfxHandler", fun s => s.EnemyGfxHandler),
  ("GetEnemyBoundBox", fun s => s.GetEnemyBoundBox),
  ("PlayerGfxHandler", fun s => s.PlayerGfxHandler),
  ("BlockObjMT_Updater", fun s => s.BlockObjMT_Updater),
  ("FlagpoleRoutine", fun s => s.FlagpoleRoutine),
  ("ColorRotation", fun s => s.ColorRotation),
  ("UpdScrollVar", fun s => s.UpdScrollVar),
  ("ExitEng", fun s => s.ExitEng),
  ("HandleEToBGCollision", fun s => s.HandleEToBGCollision),
  ("PositionEnemyObj", fun s => s.PositionEnemyObj),
  ("CheckRightExtBounds", fun s => s.CheckRightExtBounds),
  ("JumpEngine", fun s => s.JumpEngine),
  ("ReadJoypads", fun s => s.ReadJoypads),
  ("DecTimers", fun s => s.DecTimers),
  ("NoDecTimers", fun s => s.NoDecTimers),
  ("PlayerEndLevel", fun s => s.PlayerEndLevel),
  ("GetPlayerOffscreenBits", fun s => s.GetPlayerOffscreenBits),
  ("RunStarFlagObj", fun s => s.RunStarFlagObj),
  ("FloateyNumbersRoutine", fun s => s.FloateyNumbersRoutine),
  ("RunGameTimer", fun s => s.RunGameTimer),
  ("XLdBData", fun s => s.XLdBData),
  ("GetXOffscreenBits", fun s => s.GetXOffscreenBits),
  ("FetchSqu1MusicData", fun s => s.FetchSqu1MusicData),
  ("MiscSqu1MusicTasks", fun s => s.MiscSqu1MusicTasks),
  ("ExXOfsBS", fun s => s.ExXOfsBS),
  ("SideTimerBump", fun s => s.SideTimerBump),
  ("CollisionInit", fun s => s.CollisionInit),
  ("EndlessLoop", fun s => s.EndlessLoop),
  ("SetVRAMOffset", fun s => s.SetVRAMOffset),
  ("GetPlayerColors", fun s => s.GetPlayerColors),
  ("UpdateScreen", fun s => s.UpdateScreen),
  ("OutputToVRAM", fun s => s.OutputToVRAM),
  ("RepeatByte", fun s => s.RepeatByte),
  ("OutputNumbers", fun s => s.OutputNumbers),
  ("ExitOutputN", fun s => s.ExitOutputN),
  ("UpdateNumber", fun s => s.UpdateNumber),
  ("NoZSup", fun s => s.NoZSup),
  ("ExitColorRot", fun s => s.ExitColorRot),
  ("ProcMove", fun s => s.ProcMove),
  ("MoveSubs", fun s => s.MoveSubs),
  ("SideCheckLoop", fun s => s.SideCheckLoop),
  ("BHalf", fun s => s.BHalf),
  ("ErACM", fun s => s.ErACM),
  ("PlyrPipe", fun s => s.PlyrPipe),
  ("AreaChangeTimerData", fun s => s.AreaChangeTimerData),
  ("SkipMainOper", fun s => s.SkipMainOper),
  ("CoinTile", fun s => s.CoinTile),
  ("RunFR", fun s => s.RunFR),
  ("ExSCH", fun s => s.ExSCH),
  ("ExCSM", fun s => s.ExCSM),
  ("ExHC", fun s => s.ExHC),
  ("ContSChk", fun s => s.ContSChk),
  ("VineCollision", fun s => s.VineCollision),
  ("OnGroundStateSub", fun s => s.OnGroundStateSub),
  ("LRAir", fun s => s.LRAir),
  ("PJumpSnd", fun s => s.PJumpSnd),
  ("MovePlayerVertically", fun s => s.MovePlayerVertically),
  ("NoJSChk", fun s => s.NoJSChk),
  ("RghtFrict", fun s => s.RghtFrict),
  ("AreaParserCore", fun s => s.AreaParserCore),
  ("GetBlockBufferAddr", fun s => s.GetBlockBufferAddr),
  ("PlayerHeadCollision", fun s => s.PlayerHeadCollision),
  ("BlockObjectsCore", fun s => s.BlockObjectsCore),
  ("CRendLoop", fun s => s.CRendLoop),
  ("ChkCFloor", fun s => s.ChkCFloor),
  ("BlockBufferColumnPos", fun s => s.BlockBufferColumnPos),
  ("SprDataOffset_Ctrl", fun s => s.SprDataOffset_Ctrl),
  ("CheckTopOfBlock", fun s => s.CheckTopOfBlock),
  ("CoinTile2", fun s => s.CoinTile2),
  ("ExecGameLoopback", fun s => s.ExecGameLoopback),
  ("SpriteShuffler", fun s => s.SpriteShuffler),
  ("RenderUnderPart", fun s => s.RenderUnderPart)]

set_option maxRecDepth 100000 in
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
    Eng_PlayerEntrance := ← get "Eng_PlayerEntrance"
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
    EngFlagpole := ← get "EngFlagpole"
    EngEndLevel := ← get "EngEndLevel"
    DoFootCheck := ← get "DoFootCheck"
    DoPlayerSideCheck := ← get "DoPlayerSideCheck"
    AwardTouchedCoin := ← get "AwardTouchedCoin"
    HandleAxeMetatile := ← get "HandleAxeMetatile"
    BlockBufferCollision := ← get "BlockBufferCollision"
    HandlePipeEntry := ← get "HandlePipeEntry"
    BlockBufferAdderData := ← get "BlockBufferAdderData"
    Block_Buffer_2 := ← get "Block_Buffer_2"
    Left_Dir := ← get "Left_Dir"
    Right_Dir := ← get "Right_Dir"
    PipeColumnByte := ← get "PipeColumnByte"
    RoomBlockLeftByte := ← get "RoomBlockLeftByte"
    RoomBlockRightByte := ← get "RoomBlockRightByte"
    RoomStartX := ← get "RoomStartX"
    L_GroundArea6 := ← get "L_GroundArea6"
    SidePipeTile := ← get "SidePipeTile"
    SidePipeTopTile := ← get "SidePipeTopTile"
    EngSidePipe := ← get "EngSidePipe"
    RoomPipeByte := ← get "RoomPipeByte"
    StarFlagTopY := ← get "StarFlagTopY"
    StarFlagDelay := ← get "StarFlagDelay"
    NonMaskableInterrupt := ← get "NonMaskableInterrupt"
    SoundEngine := ← get "SoundEngine"
    MusicHandler := ← get "MusicHandler"
    HandleSquare1Music := ← get "HandleSquare1Music"
    HandleTriangleMusic := ← get "HandleTriangleMusic"
    HandleNoiseMusic := ← get "HandleNoiseMusic"
    SkipSoundSubroutines := ← get "SkipSoundSubroutines"
    PauseSfxValue := ← get "PauseSfxValue"
    UnpauseSfxValue := ← get "UnpauseSfxValue"
    PauseSfxLength := ← get "PauseSfxLength"
    ReadPortBits := ← get "ReadPortBits"
    GameEngine := ← get "GameEngine"
    ProcELoop := ← get "ProcELoop"
    EnemyGfxHandler := ← get "EnemyGfxHandler"
    GetEnemyBoundBox := ← get "GetEnemyBoundBox"
    PlayerGfxHandler := ← get "PlayerGfxHandler"
    BlockObjMT_Updater := ← get "BlockObjMT_Updater"
    FlagpoleRoutine := ← get "FlagpoleRoutine"
    ColorRotation := ← get "ColorRotation"
    UpdScrollVar := ← get "UpdScrollVar"
    ExitEng := ← get "ExitEng"
    HandleEToBGCollision := ← get "HandleEToBGCollision"
    PositionEnemyObj := ← get "PositionEnemyObj"
    CheckRightExtBounds := ← get "CheckRightExtBounds"
    JumpEngine := ← get "JumpEngine"
    ReadJoypads := ← get "ReadJoypads"
    DecTimers := ← get "DecTimers"
    NoDecTimers := ← get "NoDecTimers"
    PlayerEndLevel := ← get "PlayerEndLevel"
    GetPlayerOffscreenBits := ← get "GetPlayerOffscreenBits"
    RunStarFlagObj := ← get "RunStarFlagObj"
    FloateyNumbersRoutine := ← get "FloateyNumbersRoutine"
    RunGameTimer := ← get "RunGameTimer"
    XLdBData := ← get "XLdBData"
    GetXOffscreenBits := ← get "GetXOffscreenBits"
    FetchSqu1MusicData := ← get "FetchSqu1MusicData"
    MiscSqu1MusicTasks := ← get "MiscSqu1MusicTasks"
    ExXOfsBS := ← get "ExXOfsBS"
    SideTimerBump := ← get "SideTimerBump"
    CollisionInit := ← get "CollisionInit"
    EndlessLoop := ← get "EndlessLoop"
    SetVRAMOffset := ← get "SetVRAMOffset"
    GetPlayerColors := ← get "GetPlayerColors"
    UpdateScreen := ← get "UpdateScreen"
    OutputToVRAM := ← get "OutputToVRAM"
    RepeatByte := ← get "RepeatByte"
    OutputNumbers := ← get "OutputNumbers"
    ExitOutputN := ← get "ExitOutputN"
    UpdateNumber := ← get "UpdateNumber"
    NoZSup := ← get "NoZSup"
    ExitColorRot := ← get "ExitColorRot"
    ProcMove := ← get "ProcMove"
    MoveSubs := ← get "MoveSubs"
    SideCheckLoop := ← get "SideCheckLoop"
    BHalf := ← get "BHalf"
    ErACM := ← get "ErACM"
    PlyrPipe := ← get "PlyrPipe"
    AreaChangeTimerData := ← get "AreaChangeTimerData"
    SkipMainOper := ← get "SkipMainOper"
    CoinTile := ← get "CoinTile"
    RunFR := ← get "RunFR"
    ExSCH := ← get "ExSCH"
    ExCSM := ← get "ExCSM"
    ExHC := ← get "ExHC"
    ContSChk := ← get "ContSChk"
    VineCollision := ← get "VineCollision"
    OnGroundStateSub := ← get "OnGroundStateSub"
    LRAir := ← get "LRAir"
    PJumpSnd := ← get "PJumpSnd"
    MovePlayerVertically := ← get "MovePlayerVertically"
    NoJSChk := ← get "NoJSChk"
    RghtFrict := ← get "RghtFrict"
    AreaParserCore := ← get "AreaParserCore"
    GetBlockBufferAddr := ← get "GetBlockBufferAddr"
    PlayerHeadCollision := ← get "PlayerHeadCollision"
    BlockObjectsCore := ← get "BlockObjectsCore"
    CRendLoop := ← get "CRendLoop"
    ChkCFloor := ← get "ChkCFloor"
    BlockBufferColumnPos := ← get "BlockBufferColumnPos"
    SprDataOffset_Ctrl := ← get "SprDataOffset_Ctrl"
    CheckTopOfBlock := ← get "CheckTopOfBlock"
    CoinTile2 := ← get "CoinTile2"
    ExecGameLoopback := ← get "ExecGameLoopback"
    SpriteShuffler := ← get "SpriteShuffler"
    RenderUnderPart := ← get "RenderUnderPart"
  }

def Syms.load (path : String) : IO Syms := do
  match Syms.parse (← IO.FS.readFile path) with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Lean source of this symbol table (for generated proof files) -/
def Syms.toLean (s : Syms) : String :=
  "{ " ++ ", ".intercalate (Syms.fields.map fun (k, f) => s!"{k} := {(f s).toNat}") ++ " }"

/-- the collision bits with the Left side blocked -/
def Syms.noLeft (s : Syms) : UInt8 := ~~~s.Left_Dir.toUInt8

/-- the collision bits with the Right side blocked -/
def Syms.noRight (s : Syms) : UInt8 := ~~~s.Right_Dir.toUInt8

/-- the routine is the flagpole's slide or the end of the level -/
def Syms.inFlag (s : Syms) (eng : UInt8) : Bool := eng == s.EngFlagpole.toUInt8 || eng == s.EngEndLevel.toUInt8

end Smbrta
