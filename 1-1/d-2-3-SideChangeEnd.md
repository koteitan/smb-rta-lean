[← Back](README.md) | [English](d-2-3-SideChangeEnd.md) | [Japanese](d-2-3-SideChangeEnd-ja.md)

# The last frames of the change out of the side pipe

**Claim.** This is a partial result. A machine that meets a condition on one state at the exit has no control on the next 121 frames, for any inputs with no Start on the frames of the game core. With the first frames of the change, this removes the hypothesis `fallAfter`: a run with these inputs takes at least 282 counted frames from the entry to control. During the change, a frame that ends paused takes nothing off `left`. If at the exit the game timer is not 000, whatever the sound's pause flag is, `left` is not 0 before the first control after the entry.

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

`NoStart(m, i)` says: if `m` is in the game core with a routine other than the pipe's, the input `i` has no Start. `InRows(m)` says that `m` is covered by one of the abstract states of the rows, below. `InRowsT(m)` says that `m` is covered by one of the abstract states of the rows of the time, below. `InRowsTF(m)` says that `m` is covered by one of the abstract states of the rows of the time with the flag not 0, below. `InTime(m) := InRowsT(m) ∨ InRowsTF(m)`.

```
Timer(m)   :=  ( m[GameTimerDisplay], m[GameTimerDisplay + 1], m[GameTimerDisplay + 2] ) ≠ ( 0, 0, 0 )
Time(m)    :=  m[PauseModeFlag] = 0  ∧  Timer(m)
Paused(m)  :=  m[GamePauseStatus] & 1 = 1
```

`Timer` says that the game timer is not 000 at the exit. `Time` adds that the sound's pause flag is 0. `Paused` says that the frame ends paused.

```
entry      :  ∀ M,  Entry2(M) → EntryCond(M)
during     :  ∀ M,  Entry2(M) → During2(M)
toDuring   :  ∀ m,  During2(m) → During(m)
step       :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))  ∨  ( Exit(frame(m, i))  ∧  ( Quiet(frame(m, i)) → InRows(frame(m, i)) ) )
atExit     :  ∀ m,  ExitCond(m) → InRows(m)
leftExit   :  ∀ m,  ExitCond(m) → left(m) = 122
rows       :  ∀ m, InRows(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRows(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
duringLeft :  ∀ m,  During2(m) → left(m) ≠ 0
stepT      :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))  ∨  ( Exit(frame(m, i))  ∧  ( Quiet(frame(m, i)) ∧ Time(frame(m, i)) → InRowsT(frame(m, i)) ) )
rowsT      :  ∀ m, InRowsT(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  InRowsT(frame(m, i))
zeroT      :  ∀ m,  InRowsT(m) ∧ left(m) = 0 → ctl(m)
pauseKeeps :  ∀ m, During2(m) → ∀ i,  Paused(frame(m, i)) ∧ During2(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsNotPaused :  ∀ m,  InRows(m) → ¬Paused(m)
stepTT     :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))  ∨  ( Exit(frame(m, i))  ∧  ( Quiet(frame(m, i)) ∧ Timer(frame(m, i)) → InTime(frame(m, i)) ) )
rowsTF     :  ∀ m, InRowsTF(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  InRowsTF(frame(m, i))
zeroTF     :  ∀ m,  InRowsTF(m) ∧ left(m) = 0 → ctl(m)
no_control_exit :  ExitCond(s₀)  ∧  (∀ n, s₍ₙ₊₁₎ = frame(sₙ, iₙ)  ∧  NoStart(sₙ, iₙ))  →  ∀ j < 122, ¬ctl(sⱼ)
EndRun.fall     :  a run with the fields of `EndRun`, frames before the first `left = 0` :  left(seq n) ≤ left(seq (n+1)) + 1
EndRun.bound    :  a run with the fields of `EndRun` :  cnt(a) + 282 ≤ cnt(b)
EndRun.first    :  a run with the fields of `EndRun`, (∀ n ∈ [a, b],  Exit(seq n) → Time(seq n))  ∧  (∀ n ∈ [a, b),  ¬ctl(seq n))
                   →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
EndRun.firstF   :  a run with the fields of `EndRun`, (∀ n ∈ [a, b],  Exit(seq n) → Timer(seq n))  ∧  (∀ n ∈ [a, b),  ¬ctl(seq n))
                   →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
```

`Exit(m)` is the same as on the page of the first frames. The fields of `EndRun` are those of `ChangeRun` without `fallAfter`, with `Entry2` for the entry, and two more: `noStart` and `quiet`. `lagKeeps` is now `lagPaused`:

```
lagPaused  :  ∀ n ∈ [a, b),  lag(n) → Paused(seq (n + 1))
```

The two hypotheses of `EndRun.firstF` are `chg.time₂` (`Timer`) and `Changes.ctlFirst₂` of `Route`. The second is a theorem: `Route` defines `chg.b₂` as the first state with control from the entry on. `EndRun.firstF` takes the place of `chg.first₂` (`left` is not 0 before control). `EndRun.first` is as before, with `Time`.

Lean: `Theorems/SideChangeEnd.lean` (`s_xtick`, `s_xbr`, `s_xstep1`, `xframe_of_walk`, `link_frame`, `chain_step`, `exit_cover`, `during_step`, `sim_normD`, `link_frameD`, `chain_stepD`, `ctl_of_zero`, `TimeOK`, `timeRows`, `InRowsT`, `TimerOK`, `timeRowsF`, `InRowsTF`, `flagCheck`, `InTime`, `Paused`, `pause_keeps`, `not_paused_rows`, `EndStatement`, `endStatement_of_check`, `no_control_exit`, `EndRun`, `st_step_paused`, `EndRun.fall`, `EndRun.bound`, `EndRun.first`, `EndRun.firstF`, `aIzyHi`, `wide_ok`, `s_aIzyHi`), private `side_end_checks` (`native_decide`), `side_end`, `side_exit_no_control`, `side_change_end`.

## How it works

**A tick that crosses the end of a frame.** The frame after the pipe clears RAM, and the frame ends inside that loop. The abstract machine of [the first frames](d-2-2-SideChangeBound.md) fails there. `xtick` adds three cases to its tick: the first dot of a frame, the end of a frame, and the clear of the vblank flag when the dot's interval is on both sides of it. At the end of a frame there are up to three states: the frame goes on, it ends at dot 0, or it ends at a later dot. A branch may cross too (`xbr`). `xtick` and `xbr` are proved against `tick` and `branch` (`s_xtick`, `s_xbr`).

**The frames of the clear.** From the state at the exit, the frame reaches the clear with a dot known only in an interval, because the sound routines take a time that depends on bytes not known. So the frame can end at 1,904 places of the loop (774 if the flag is not 0). At all of them the key of `left` has the value of the row: the loop has cleared `ScreenRoutineTask` and has not reached `GameEngineSubroutine`. The next frame starts from all these places. The search goes through the loop in the order of its turns, so the paths join: the frame takes 6,905 steps.

**The rows.** After the clear 1,769 of the 2,048 bytes are known. The bytes that the clear leaves come from `ExitCond`, or they are free. Each frame goes from the states of one row to those of the next: 123 rows in all, with `left` from 122 to 0. The last row holds the states with control, and the states of the time-up path, because the digits of the game timer are free: `left` is 0 in both.

**The rows of the time.** To remove the time-up states from the last row, there is one more set of rows, `timeRows`. They start from the states of the rows with the flag 0, and `dg` says that the three digits of the game timer are not all 0. On the last frame, the instruction that tests the time splits into 24 pieces, each with one bit of one digit at 1. So the time-up path is gone. The frame of the entrance's setup loads the timer from the level if `FetchNewGameTimerFlag` is not 0. That path writes the digits, so it loses `dg`. The search keeps this flag apart. At the frame's end, a digit with a bit known to be 1 gives `dg` back (`normD`, `sim_normD`), so the two paths join again. The check of these rows is `chainOKD`. Every state of a row where `left` is 0 has control (`zeroCtl`). A state at the exit with `Quiet` and `Time` is in these rows (`stepT`).

**The rows of the time with the flag not 0.** If the flag is not 0, one of its bits is 1. While the two pause bytes are 0, the sound routine takes the pause path and does not write the flag. So the bit stays 1, and the song does not start. For each bit there is one more set of rows of the time (`timeRowsF`, 8 sets). They start from the states of `timeBase`, with this bit of the flag 1 in place of the flag 0. Such a state is a piece of `TaintRun.splitDg` with the flag as the byte of `D` (`cov_dg`). In all 8 sets every state of a row where `left` is 0 has control (`flagCheck`). A state at the exit with `Quiet` and `Timer` is in `timeRows` if the flag is 0, and in the set of a bit that is 1 if not (`stepTT`). So `EndRun.firstF` does not assume the flag.

**Frames that end paused.** A frame that ends paused runs neither the timers nor the mode's routine. The frames of the pipe are walked once more, with the pause bit read in pieces and the pause byte kept apart (`pauseCheck`). Every state at a frame's end where the counter has fallen knows that the bit is 0 (`finRkP`). So a frame of the pipe that ends paused does not move the counter, and takes nothing off `left` (`pause_keeps`). Every state of the rows knows that the bit is 0 (`notPausedRows`), so no frame in the rows ends paused. If the `lag` frames end paused, they take nothing off `left` (`st_step_paused`).

**A read through a pointer that is not known.** An `LDA (zp),Y` through a pointer that the state does not know fails in the machine of `TaintRun`. If the known bits of the pointer's high byte show that it is at most `0x1E`, or at least `0x80`, then every address `p + y` is in the RAM or the ROM, not at a register (past the end of memory the address goes round to the zero page and the stack). Then the read gives a byte that is not known and changes nothing else (`aIzyHi`, `wide_ok`, `s_aIzyHi`). `xstep1` uses this rule only where its other rules fail. The checks here and those of the other files that use `xstep1` pass as before, and `rows0` takes 682,944 steps, as before.

**The two cases of the sound's pause flag.** The clear does not touch `PauseModeFlag`. If it is not 0, the sound routines do not run until the next Start, and the song does not start. So there are two sets of rows. The second one uses the fact that the flag is not 0 (`dg`).

**The size of the check.**

| frames | abstract steps |
|---|---|
| a frame of the pipe, timer ≥ 2 | 106,156 |
| a frame of the pipe, timer = 1 | 90,308 |
| rows, flag 0 | 682,944 |
| rows, flag not 0 | 691,797 |
| rows of the time | 684,535 |
| rows of the time, one bit of the flag 1 (8 sets, each) | 691,694 |
| a frame of the pipe, timer ≥ 2, the pause bit in pieces | 252,566 |

The rows of the time with the flag not 0 take about 1.6 s a set, about 12 s for the 8 sets. About 21 s in a program (before: about 9 s), about 29 s in the private proof build (before: about 11 s; measured while other proofs were built).

## Why Start is excluded

Start on a frame of the game core pauses the game. The song stops while the pause sound plays, and the game does not. So after a pause the song is behind the game by any number of frames, and there would be about one state for each row and each delay. If frames that stay in a row are joined with frames that go on, the song's pointer and offsets are not known: with Start allowed, the check fails on the first frame of the game core, with 4 failures in the music routine (23,695 steps). So this is not proved.

Measured, with temporary programs (not kept), with the read through a pointer above:

* The rows of `rows0` up to `left` 62, then 23 bytes of the song made not known (the pointer's low byte, the offsets, the note counters and buffers, the counters of the sound effects; the pointer's high byte kept known). The rule now applies, but each of the next 7 frames still fails 22 to 116 times and takes 126,000 to 405,000 steps (the rows now take about 5,500 steps a frame). When a phrase of the song ends, the routine loads the next pointer from a table at an index that is not known, so the high byte is not known any more, and `LDA (MusicData),Y` fails again. And the loop that finds the area music's header (`iny`, `lsr`, `bcc`) runs with a byte that may be 0, so it never ends.
* Rows from the exit with `PauseModeFlag`, `PauseSoundBuffer` and `PauseSoundQueue` not known, in place of the two cases of the flag and `Quiet`: the same loop fails from the fourth frame on. From the frame where the song starts, the frames end at up to 207,531 places and reach the limit of 4,000,000 steps.
* Rows of the time with only the flag not known (the pause bytes as `Quiet` says): the same failures.

The reason is the same in all three. The abstract machine joins a state where the song has started with one where it has not. After the join it does not keep "the queue is not 0" past the branch on it. So the rows fail as soon as the song is not known. Rows that keep the cases apart need one set of rows per case. The 8 sets of the rows of the time for the flag not 0 (one known bit each) are made (above, "The rows of the time with the flag not 0"). The delay of the song after an unpause needs 41 sets (below). This is not done. The attempt to take the sound routine as one step is in the next section.

## The sound routine as one step: an attempt

**The idea.** Show once, on the ROM, that one call of the sound routine, from its entry to its return, writes only the sound's bytes and the APU's registers, keeps every other RAM byte, returns to its caller with the stack as it was, and takes a number of dots in an interval `[lo, hi]`. If this held for any values of the sound's bytes, the walks of the rows could step over the call in one step and run with the song not known.

**The sound's bytes.** 38 bytes (`SoundWalk.soundNames`): the queues, the buffers, the song's pointer, offsets and counters, the counters of the effects, the three pause bytes. The only other byte the routine reads is `OperMode`. Every write to RAM is to a fixed address (zero page or absolute). A write with an index added goes only to an APU register. The Lean machine has no APU, so such a write changes nothing.

**Measured** (`sound-check`, from the real place of the call 200 frames after the exit; the other bytes are those of that machine):

| state at the call | abstract steps | failures | dots of the call |
|---|---|---|---|
| the song known | 115 | 0 | 1,179 |
| the 38 sound bytes not known | 260,322 | 2,025 | 240 to 87,237 (up to the frame's end) |
| the same, the queues and buffers read in pieces by the lowest bit that is 1 | 294,803 | 2,136 | the same |
| the same, and bit 7 of the high byte of `MusicData` at 1 | the limit, 2,000,000 | 15,630 | the same |

The failures are the four reads `LDA (MusicData),Y` of the four voices (the pointer is not known), the loop that finds the song's header, and the ticks that reach the frame's end. Pieces by the lowest bit that is 1: a byte `x` is split into the piece `x & mask = 0` and, for each bit `j` of `mask`, the piece where the bits of `mask` below `j` are 0 and bit `j` is 1 (`SoundWalk.ctzPieces`; used only by the program, not proved). With them the header's loop ends, but the loops that read the song's data do not, since the pointer and the offsets are not known.

**"For any values" is false.** Checked on the Lean machine, from the real place of the call:

* A call that does not return. With the pointer in the ROM and the noise's loop-back offset at a place where the song's data is 0, the loop that looks for the noise's data (`FetchNoiseBeatData`) comes back to the same place forever. It does not return in 200,000 steps.
* A call that reads a register. With the high byte of the pointer in the range of the PPU's registers, the read `LDA (MusicData),Y` of the second square voice reads the PPU's status register. That read clears the vblank flag.

So a summary can hold only on a set of values of the sound's bytes. That set is a set of pairs of the pointer and the offsets, and known bits byte by byte cannot express it.

**The table of real song states.** From the exit, 123 frames with no input, for 44 states at the exit: with `Quiet`, with the unpause sound at each count from 1 to 42, and with the unpause pressed on the frame of the exit. There were 5,412 calls and 207 states of the sound's bytes. From each state, the abstract walk closes at the return: 16,940 steps in all, no failure, 303 to 3,291 dots a call. The real calls took 101 to 1,097 cycles.

**Why the rows cannot use it as they are.** The states of the rows do not know the sound's bytes. So "the machine's sound bytes are in the table" has to be carried from frame to frame outside the abstract state. That needs a lemma on the machine: a step does not change the bytes it does not write. `Sim` relates one abstract state to one machine, and it does not give it. This lemma is now proved, with a step that splits the call by a table and forgets the sound's bytes after the return: see [Where one step of the CPU writes RAM](d-3-4-1-StepWrites.md). Measured there, not a theorem: rows that forget the sound's bytes close for 52 kinds of the pause sound at the exit (2,740,068 steps, no failure). Rows built that way are not proved yet. `Quiet` (1-1-d-3-4) and `NoStart` (1-1-d-3-3) stay.

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
* On the 132 runs above (no input, random, Start only on the first 80 frames) `Time` holds at the exit. No frame before control has `left` 0.
* From the 44 entries, Start pressed at random on the frames of the pipe, then no Start up to control (264 runs). At 189 exits the sound's pause flag is not 0, and none of these meets `ExitCond`. At the 75 exits with `ExitCond`, `Time` holds. On the frames of the pipe, the timers do not run on 46,829 frames, and all of them end paused. No frame of the pipe that ends paused takes anything off `left`. After the exit the timers do not run on 75 frames (one `setup` frame per run), and none of them ends paused.
* With the game timer written to 000 at the entry, `Time` fails at the exit, and at frame 282, where `left` is 0, there is no control (the routine is the death). Written to 001, `Time` holds, and there is control at frame 282.

**The vertical pipe's last frames.** The same tool, measured on the change into the room.

| from | known | result |
|---|---|---|
| exit, frame 48 | the side pipe's list `Kx` + `X`, values of that exit | fails on the frame of the clear: 149 failures. The song is playing, and its pointers are not known. Real runs differ here |
| same, flag not 0 | same | the frame of the clear goes (21,781 steps). The next one fails: a join gives a state with dots from 0 to 10,254, and the tick has no rule for that |
| frame 50 | everything the clear sets, and all bytes it leaves | goes in both cases of the flag: 41 rows, about 148,000 steps, 100 ms natively |

So the rows would serve the last 41 frames from frame 50. The state at frame 50 and the two frames of the clear need a statement about the song.

## Assumptions (not proved in Lean)

* `Entry2` on the state at the entry of a real run, or `ExitCond` at the exit. The route gets `Entry2` from the frames in the room and 16 bytes at the entry ([The screen's page in the room](d-2-4-ScreenPage.md), `ScreenPage.entry_rest`). `NoteLengthTblAdder`, one of these 16 bytes, does not hold after the hurry-up music. Item 1-1-d-2-5.
* `Quiet`: no pause sound is running at the exit. On the runs measured it fails when Start was pressed in the last frames of the pipe. `left` still falls by exactly one on those runs, measured only. It does not follow from the rows and the entry: the conditions allow Start on the frames of the pipe, so the states during the pipe do not know the bytes of the pause sound, and the sound of a press on the last frames of the pipe still plays at the exit. It needs rows that run with the song not known (see "Why Start is excluded"). On 880 runs with Start at random on the frames of the pipe (44 entries, 20 runs each), the exits were: 280 with `Quiet`; 584 with the sound of the unpause still playing (in `PauseSoundBuffer`, with `PauseModeFlag` not 0); 16 with the unpause pressed on the frame of the exit (in `PauseSoundQueue`, with the flag not 0). None was paused. In the second kind the song starts 1 to 41 frames late, by the counter of the pause sound, so rows for it need one set per delay. The third kind alone would need one more set of rows: 16 of the 600 exits without `Quiet`. Item 1-1-d-3-4.
* `NoStart`: no Start on the frames of the game core after the pipe.
* `lagPaused`: a `lag` frame ends paused. `lag` is a label of `Frames`, and this field is its only link to the machine. On the real runs, every frame of the pipe where the timers do not run ended paused. After the exit the only such frame is the `setup` frame, which is not a `lag` frame. A `lag` frame where the timers do not run for another reason does not meet this field: a frame with `TimerControl` not 0, or the frame after a handler that runs past its frame. For the frames of the pipe the check shows that every frame ends in the idle loop, so none runs past. Neither kind was seen on the runs measured. It does not follow from the rows: they show that no state after the exit is paused and that a frame of the pipe that ends paused keeps `left`, but nothing ties the label `lag` to the machine. Item 1-1-d-3-2.
* `Timer`: at the exit the game timer is not 000. The sound's pause flag is no longer assumed (the rows of the time with the flag not 0). A run with 000 has used 400 seconds. It does not follow from the change and the room alone (read from the code). The frames of the pipe do not run the game timer, so its digits at the exit are those at the entry. But the timer can show 000 at the entry: on a frame in control it falls from 001 to 000, and the time-up comes only when `GameTimerCtrlTimer` has run out again, 24 frames later. On these frames the player can enter the pipe. So it needs the count of the timer over the route. Item 1-1-d-3-5.
* `b` is the first state with control after the entry. In the route this holds by the definition of `chg.b₂` (`Changes.ctlFirst₂`).
* [The whole route](0-1-Route.md) uses this theorem: `Changes.run₂` is an `EndRun`.

**Files.** `Theorems/SideChangeEnd.lean`, private `Proof/SideChangeEnd.lean`. The measurements of the sound routine: `Theorems/SoundWalk.lean` (program only, no theorem).

**To reproduce.**
```
.lake/build/bin/smbrta side-end-check FM2    # the check, the conditions on real entries and exits, left on real frames, the time and the pauses on real frames, about 60 s
.lake/build/bin/smbrta sound-check           # one call of the sound routine: the walk with the 38 sound bytes not known, real calls with the bytes at random
.lake/build/bin/smbrta sound-check "ctz;MusicDataHigh=80/80"   # the walk with the reads in pieces and the pointer's high bit 1
.lake/build/bin/smbrta sound-check table     # the table of real song states, and the walk from each
.lake/build/bin/smbrta sound-check flagrows  # the rows of the time, and the 8 sets with the flag not 0, about 30 s
```
