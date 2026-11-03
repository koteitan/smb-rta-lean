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
  ("TimerControl", fun s => s.TimerControl)]

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
  }

def Syms.load (path : String) : IO Syms := do
  match Syms.parse (← IO.FS.readFile path) with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Lean source of this symbol table (for generated proof files) -/
def Syms.toLean (s : Syms) : String :=
  "{ " ++ ", ".intercalate (Syms.fields.map fun (k, f) => s!"{k} := {(f s).toNat}") ++ " }"

end Smbrta
