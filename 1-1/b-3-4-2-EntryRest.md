[Back to stage 1-1](README.md)

# The remaining entry bytes

This audits the 36 bytes of the previous `Rest`. The first square channel's effect queue is removed from `Entry` itself, leaving 35 bytes in `Rest`. The guard, press condition and kept bytes do not grow.

The three steps are knowledge at frame 0, protection from indexed stores by the guard, and preservation by the frame walk. Initial knowledge is insufficient when a direct store changes the byte. A changing byte cannot be proved by keeping one reference value.

| Byte | Initial states knowing it | Blocker | Writer |
|---|---|---|---|
| `GameEngineSubroutine+0` | 8/8 | control uses another routine; the entry kind stays assumed | `HandlePipeEntry / SetPRout` |
| `EnemyObjectPageSel+0` | 8/8 | changes with the enemy parser and position | `CheckRightBounds / CheckPageCtrlRow` |
| `AreaMusicBuffer_Alt+0` | 0/8 | unknown at frame 0; the sound engine writes it | `NoStopSfx` |
| `Block_State+0` | 8/8 | changes on real frames; indexed stores | `DBlockSte / ChkBrick / UpdSte` |
| `Block_State+1` | 8/8 | changes on real frames; indexed stores | `DBlockSte / ChkBrick / UpdSte` |
| `Block_RepFlag+0` | 8/8 | changes on real frames; indexed stores | `BouncingBlockHandler / ReplaceBlockMetatile` |
| `Block_RepFlag+1` | 8/8 | changes on real frames; indexed stores | `BouncingBlockHandler / ReplaceBlockMetatile` |
| `Misc_State+8` | 8/8 | changes on real frames; coin processing | `JCoinC / ProcJumpCoin` |
| `FloateyNum_Control+0` | 8/8 | changes on real frames; floating score processing | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+1` | 8/8 | changes on real frames; floating score processing | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+2` | 8/8 | changes on real frames; floating score processing | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `FloateyNum_Control+3` | 8/8 | changes on real frames; floating score processing | `SetupFloateyNumber / FloateyNumbersRoutine` |
| `Enemy_State+0` | 8/8 | changes on real frames; collisions and object updates | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Enemy_State+1` | 8/8 | changes on real frames; collisions and object updates | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Enemy_State+2` | 8/8 | changes on real frames; collisions and object updates | `SetDBSte / EraseEnemyObject / HandlePECollisions` |
| `Square1SoundQueue+0` | 8/8 | removed from Entry; no guard or press cost | `sound engine` |
| `Enemy_Flag+4` | 8/8 | object routines write it; map/object facts needed | `EraseEnemyObject / KillELoop / FinishFlame` |
| `Enemy_Flag+5` | 8/8 | changes on real frames; power-up and flagpole routines write it directly | `PwrUpJmp / FlagpoleObject` |
| `Enemy_ID+0` | 8/8 | indexed enemy loading stores; a larger guard fails real runs | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+1` | 8/8 | indexed enemy loading stores; a larger guard fails real runs | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+2` | 8/8 | indexed enemy loading stores; a larger guard fails real runs | `StrID / StrFre / EraseEnemyObject` |
| `Enemy_ID+3` | 8/8 | indexed enemy loading stores; a larger guard fails real runs | `StrID / StrFre / EraseEnemyObject` |
| `AreaMusicQueue+0` | 8/8 | power-up collision writes it; map/collision facts needed | `HandlePowerUpCollision / StoreMusic` |
| `EventMusicQueue+0` | 8/8 | death and timer processing write it | `HoleDie / RunGameTimer / FlagpoleCollision` |
| `NoiseSoundQueue+0` | 8/8 | object and brick processing write it | `BrickShatter / InitBowserFlame` |
| `NoiseSoundBuffer+0` | 8/8 | the sound engine needs facts about the queue | `NoiseSfxHandler / DecrementSfx3Length` |
| `AreaMusicBuffer+0` | 8/8 | the sound engine needs facts about music queues | `HandleAreaMusicLoopB / NotTRO` |
| `EventMusicBuffer+0` | 8/8 | the sound engine needs facts about music queues | `LoadEventMusic / HandleAreaMusicLoopB` |
| `VineFlagOffset+0` | 8/8 | vine processing writes it; map/object facts needed | `NextVO / KillVine` |
| `EnemyFrenzyBuffer+0` | 8/8 | enemy routines write it; map/object facts needed | `InitEnemyFrenzy / BowserControl / SetoffF` |
| `EnemyFrenzyQueue+0` | 8/8 | the area parser writes it | `ExitAFrenzy / ChkEnemyFrenzy` |
| `WarpZoneControl+0` | 8/8 | the area parser writes it; a map fact is needed | `WarpNum / WarpZoneObject` |
| `AreaPointer+0` | 8/8 | an enemy-data command writes it; position/data facts needed | `ParseRow0e / GetWNum` |
| `EntrancePage+0` | 8/8 | an enemy-data command writes it; position/data facts needed | `ParseRow0e / GetWNum` |
| `StarInvincibleTimer+0` | 8/8 | power-up collision writes it; timer and collision facts needed | `HandlePowerUpCollision / timer updates` |
| `WorldNumber+0` | 8/8 | warp entry writes it; warp/map facts needed | `GetWNum` |

The initial-state column counts the near states of `TitleStart` knowing the byte. It does not say that its value matches the reference entry. The routine and enemy page selection have different control values. No near state knows the saved song byte. Proving that byte may require a stronger press condition; this job does not change it.

Keeping a candidate absent from the existing entry guard adds one protected byte. The union guard adds none if it already protects that byte. `entry-rest-audit` prints the exact counts. That change alone proves nothing when direct writes, changing values, or real indexed stores remain.

## Removing the effect queue

`Square1SoundQueue` loses its entry mask and joins `entryDropped`. This also prevents the exit list from adding it back as a fully known entry byte. The pipe walk starts without knowing this byte. All inputs remain allowed.

`entry-need 15` in the old list passed the position check, original walk and pause-class walk. The pause-class tables had 158,808 and 143,194 states and took about 54 s. The hypothesis loses one byte, while checking the pipe becomes slower. In the proof build `Proof.PipeChangeEnd` takes about 270 s (233 s before), and `pipe-end-check` uses about 1.6 GB of memory (0.5 GB before). `entry-keep-check` (221,490 frames) finds no frame that loses a kept byte, and each of its 40 entries meets `Rest` and `Entry`.

## What remains

The saved song, map and object processing, and bytes depending on timers or position remain hypotheses. Both direct and indexed stores need treatment. `time₁` is unchanged.

The current entry guard protects 125 bytes and the union guard 143. Of the 35 remaining bytes, the routine is already protected by both. Each of the other 34 candidates would add one byte to each guard. This change actually adds none.
