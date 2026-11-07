[← Back](README.md) | [English](d-2-3-SideChangeEnd.md) | [Japanese](d-2-3-SideChangeEnd-ja.md)

# The last frames of the change out of the side pipe

**Claim.** This is a partial result. A machine that meets a condition on one state at the exit has no control on the next 121 frames, for any inputs with no Start on the frames of the game core. With the first frames of the change, this removes the hypothesis `fallAfter`: a run with these inputs takes at least 282 counted frames from the entry to control.

`m₀`, `run`, `ctl`, `0^k`, `E` and `T = run(E, 0^160)` are those of [What decides the change out of the side pipe](d-2-1-SideTransitionAll.md). `EntryCond`, `During`, `left` and `frame(m, i)` are those of [The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md). `m[b]` is the byte `b` of `m`.

**The condition at the exit.** `ExitCond(m)` is a condition on the state `m` at the end of a frame.

* The frame has ended in the idle loop: the program counter and the stack pointer are those of `T`, the dot is at most 9, the vblank and NMI flags fit the dot, the sprite-0 flag is set, NMI is on in the PPU control, the controller is not strobed.
* The 29 bytes `Kx` have the values they have in `T`. They are listed below.
* The game is not paused: the low bit of `GamePauseStatus` is 0.

All other bytes are free: Mario's `x`, size, status and speed, the coins, the score, the digits of the game timer, the frame counter, the interval timer, the random bytes, the sound's pause flag `PauseModeFlag`, the rest of the sound state, the sprites, the temporary bytes.

**The list `Kx`**, by name:

| group | bytes |
|---|---|
| mode | `OperMode`, `OperMode_Task`, `GameEngineSubroutine`, `ScreenRoutineTask`, `DisableScreenFlag`, `Sprite0HitDetectFlag` |
| area | `WorldNumber`, `AreaNumber`, `AreaPointer`, `EntrancePage`, `AltEntranceControl`, `PrimaryHardMode`, `CurrentPlayer`, `JoypadOverride`, `GameTimerExpiredFlag` |
| screen | `VRAM_Buffer1`, `VRAM_Buffer_AddrCtrl` |
| sound | `NoiseSoundBuffer`, `AreaMusicBuffer`, `EventMusicBuffer`, `MusicData` (2), `MusicOffset_Square1`, `NoteLengthTblAdder`, `AreaMusicQueue`, `EventMusicQueue`, `NoiseSoundQueue` |
| sound's pause | `PauseSoundBuffer`, `PauseSoundQueue` |

**How the end of `During` meets this condition.** `Entry2(M)` is `EntryCond(M)` and 8 more bytes `X` with the values of `E`: `AreaPointer`, `EntrancePage`, `CurrentPlayer`, `JoypadOverride`, `GameTimerExpiredFlag`, `AreaNumber`, `PrimaryHardMode`, `NoteLengthTblAdder`. `During2(m)` is `During(m)` with these bytes known too. The check shows that the frames of the pipe keep them. The frame on which the timer runs out then gives every byte of `Kx` except the two bytes of the sound's pause, and the low bit of `GamePauseStatus`. `Quiet(m)` says that these two bytes have the values of `T`, which are 0. A press of Start changes them while the pause sound plays. `Quiet` is not proved. It is a hypothesis on the state at the exit.

`NoStart(m, i)` says: if `m` is in the game core with a routine other than the pipe's, the input `i` has no Start. `InRows(m)` says that `m` is covered by one of the abstract states of the rows, below.

```
entry      :  ∀ M,  Entry2(M) → EntryCond(M)
during     :  ∀ M,  Entry2(M) → During2(M)
toDuring   :  ∀ m,  During2(m) → During(m)
step       :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))  ∨  ( Exit(frame(m, i))  ∧  ( Quiet(frame(m, i)) → InRows(frame(m, i)) ) )
atExit     :  ∀ m,  ExitCond(m) → InRows(m)
leftExit   :  ∀ m,  ExitCond(m) → left(m) = 122
rows       :  ∀ m, InRows(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRows(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
no_control_exit :  ExitCond(s₀)  ∧  (∀ n, s₍ₙ₊₁₎ = frame(sₙ, iₙ)  ∧  NoStart(sₙ, iₙ))  →  ∀ j < 122, ¬ctl(sⱼ)
EndRun.fall     :  a run with the fields of `EndRun`, frames before the first `left = 0` :  left(seq n) ≤ left(seq (n+1)) + 1
EndRun.bound    :  a run with the fields of `EndRun` :  cnt(a) + 282 ≤ cnt(b)
```

`Exit(m)` is the same as on the page of the first frames. The fields of `EndRun` are those of `ChangeRun` without `fallAfter`, with `Entry2` for the entry, and two more: `noStart` and `quiet`. `lagKeeps` stays.

Lean: `Theorems/SideChangeEnd.lean` (`s_xtick`, `s_xbr`, `s_xstep1`, `xframe_of_walk`, `link_frame`, `chain_step`, `exit_cover`, `during_step`, `EndStatement`, `endStatement_of_check`, `no_control_exit`, `EndRun`, `EndRun.fall`, `EndRun.bound`), private `side_end_checks` (`native_decide`), `side_end`, `side_exit_no_control`, `side_change_end`.

## How it works

**A tick that crosses the end of a frame.** The frame after the pipe clears RAM, and the frame ends inside that loop. The abstract machine of [the first frames](d-2-2-SideChangeBound.md) fails there. `xtick` adds three cases to its tick: the first dot of a frame, the end of a frame, and the clear of the vblank flag when the dot's interval is on both sides of it. At the end of a frame there are up to three states: the frame goes on, it ends at dot 0, or it ends at a later dot. A branch may cross too (`xbr`). `xtick` and `xbr` are proved against `tick` and `branch` (`s_xtick`, `s_xbr`).

**The frames of the clear.** From the state at the exit, the frame reaches the clear with a dot known only in an interval, because the sound routines take a time that depends on bytes not known. So the frame can end at 1,904 places of the loop (774 if the flag is not 0). At all of them the key of `left` has the value of the row: the loop has cleared `ScreenRoutineTask` and has not reached `GameEngineSubroutine`. The next frame starts from all these places. The search goes through the loop in the order of its turns, so the paths join: the frame takes 6,905 steps.

**The rows.** After the clear 1,769 of the 2,048 bytes are known. The bytes that the clear leaves come from `ExitCond`, or they are free. Each frame goes from the states of one row to those of the next: 123 rows in all, with `left` from 122 to 0. The last row holds the states with control, and the states of the time-up path, because the digits of the game timer are free: `left` is 0 in both.

**The two cases of the sound's pause flag.** The clear does not touch `PauseModeFlag`. If it is not 0, the sound routines do not run until the next Start, and the song does not start. So there are two sets of rows. The second one uses the fact that the flag is not 0 (`dg`).

**The size of the check.**

| frames | abstract steps |
|---|---|
| a frame of the pipe, timer ≥ 2 | 106,156 |
| a frame of the pipe, timer = 1 | 90,308 |
| rows, flag 0 | 682,944 |
| rows, flag not 0 | 691,797 |

About 5 s in a program, about 13 s in the private proof build.

## Why Start is excluded

Start on a frame of the game core pauses the game. The song stops while the pause sound plays, and the game does not. So after a pause the song is behind the game by any number of frames, and there would be about one state for each row and each delay. If frames that stay in a row are joined with frames that go on, the song's pointer and offsets are not known: with Start allowed, the check fails on the first frame of the game core, with 4 failures in the music routine (23,695 steps). So this is not proved.

## Measured but not a theorem

From entries with `Entry2`: `E`, the TAS entry, 42 real entries of `side-all-real`, 21 random runs, and 7 random runs started big. From each entry, inputs of five kinds.

| inputs | runs | frames | `Quiet` fails at the exit | `ExitCond` holds | after the exit, frames that do not take exactly one off `left` | frames where `left` falls by more than one | least frames to control |
|---|---|---|---|---|---|---|---|
| none | 72 | 20,304 | 0 | 72 | 0 | 0 | 282 |
| random, no Start | 72 | 20,304 | 0 | 72 | 0 | 0 | 282 |
| random, Start only on the first 80 frames | 72 | 23,774 | 0 | 72 | 0 | 0 | 327 |
| random, Start on the pipe's frames only | 72 | 34,132 | 71 | 1 | 0 | 0 | 424 |
| random, Start on all frames | 72 | 40,994 | 72 | 0 | not counted | 0 | 519 |

* From `T` with every free byte overwritten at random, and half of them with random inputs without Start: all 300 states meet `ExitCond`, and all get control after exactly 122 frames. Nearly all of them have the sound's pause flag not 0. No real run with `Quiet` had that flag not 0.
* Random runs where the digits were overwritten near 100: 4 of 5 meet `EntryCond`, none meets `Entry2`: the hurry-up music has set `NoteLengthTblAdder`. Such a run has used far more than 1748 frames (arithmetic on the timer, not in Lean).
* `fallAfter` of `ChangeRun` is false for some states: with the game timer overwritten to 000 at `E`, `EntryCond` holds, and before control comes at frame 800, `left` falls by more than one on 4 frames (for example from 116 to 0). That is why `EndRun.fall` stops at the first `left = 0`, and `EndRun.bound` does not need the frames after it.
* The only frame after the exit where the timers do not run is the frame after the clear, the `setup` frame of `Frames`. This is a reading of the count: one per run.

**The vertical pipe's last frames.** The same tool, measured on the change into the room.

| from | known | result |
|---|---|---|
| exit, frame 48 | the side pipe's list `Kx` + `X`, values of that exit | fails on the frame of the clear: 149 failures. The song is playing, and its pointers are not known. Real runs differ here |
| same, flag not 0 | same | the frame of the clear goes (21,781 steps). The next one fails: a join gives a state with dots from 0 to 10,254, and the tick has no rule for that |
| frame 50 | everything the clear sets, and all bytes it leaves | goes in both cases of the flag: 41 rows, about 148,000 steps, 100 ms natively |

So the rows would serve the last 41 frames from frame 50. The state at frame 50 and the two frames of the clear need a statement about the song.

## Assumptions (not proved in Lean)

* `Entry2` on the state at the entry of a real run, or `ExitCond` at the exit. The bytes `X` are read from the code: nothing in the room writes them once the room is set up. `NoteLengthTblAdder` does not hold after the hurry-up music. Item 1-1-d-2-5.
* `Quiet`: no pause sound is running at the exit. On the runs measured it fails when Start was pressed in the last frames of the pipe. `left` still falls by exactly one on those runs, measured only.
* `NoStart`: no Start on the frames of the game core after the pipe.
* `lagKeeps`: a `lag` frame takes nothing off `left`. In the rows every frame goes to the next row, so `lagKeeps` says that no frame in the rows is a `lag` frame. The link between `lag` and the real frames is in `Route`. Item 1-1-d-3-2.
* [The whole route](0-1-Route.md) uses this theorem: `Changes.run₂` is an `EndRun`.

**Files.** `Theorems/SideChangeEnd.lean`, private `Proof/SideChangeEnd.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta side-end-check FM2    # the check, the conditions on real entries and exits, left on real frames, about 20 s
```
