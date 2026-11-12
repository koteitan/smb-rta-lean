[← Back](README.md) | [English](b-3-2-PipeChangeEnd.md) | [Japanese](b-3-2-PipeChangeEnd-ja.md)

# The change into the room without `fall`

**Claim.** This is a partial result. Take a run that meets a condition on the state at the entry, a condition at some places of the pipe's frames, and a condition at the exit, and that has no Start on the frames of the game core after the pipe. Then it takes at least 91 counted frames from the entry to control. This removes the hypothesis `fall₁` from [the whole route](0-1-Route.md). `Changes` has the fields `places₁`, `quiet₁` and `noStart₁` in its place. The condition at the entry, `Entry`, is now proved in part from the press of Start on the title and the frames from control: see [the state at the vertical pipe's entry, from the title](b-3-4-EntryKeep.md). `keep₁` is gone too: see [A `lag` frame of the change into the room](b-3-3-LagPaused.md). If also the time is not up at the exit (`TimeOK`) and `b` is the first control after the entry, `left` is not 0 before control (`PipeRun.first`), and the machine at control is in the rows of the time (`PipeRun.inRowsT`). This removes `first₁` from the route: `Changes` has `time₁` and `ctlFirst₁` in its place (item 1-1-b-3-9).

`m₀`, `run`, `ctl`, `0^k` and `E` are those of [What decides the length of the change](b-2-1-PipeTransitionAll.md). `left` is that of [A bound from single frames](b-2-2-PipeChangeBound.md): `timer + 43` while the pipe's routine runs, then a table of 43 rows. `frame(m, i)` is the frame from `m` with the input `i`. `trace(m, i, j)` is the machine after `j` steps of that frame. `T = run(E, 0^48)` is the reference at the exit. `m[b]` is the byte `b` of `m`. A name with `+k` is the byte `k` after the name. `Paused(m)` says that the low bit of `GamePauseStatus` is set: `m[GamePauseStatus] & 1 = 1`. `TimeOK(m)` says that the time is not up: `m[PauseModeFlag] = 0 ∧ (m[GameTimerDisplay], m[GameTimerDisplay+1], m[GameTimerDisplay+2]) ≠ (0, 0, 0)`.

**The condition at the entry.** `Entry(M)` is a condition on the state `M` at the end of the entry frame.

* The frame has ended in the idle loop, as in [the side pipe's first frames](d-2-2-SideChangeBound.md): the program counter and the stack pointer are those of `E`, the dot is at most 9, the vblank and NMI flags fit the dot, the sprite-0 flag is set, NMI is on in the PPU control, the controller is not strobed.
* The 115 bytes `K` have the values of `E`. They are listed below.
* 13 bytes have the bits of `E` under a mask, below.
* `timer(M) ≥ 48`.

All other bytes are free: Mario's position, speed and size, the score, the coins, the digits of the game timer, the frame counter, the random bytes, the song, the sprites, the screen buffers, the area parser, the enemies in their slots.

**The list `K`**, by name:

| group | bytes |
|---|---|
| game | `WorldNumber`, `PrimaryHardMode` |
| mode | `OperMode` (2), `OperMode_Task`, `GameEngineSubroutine`, `ScreenRoutineTask`, `DisableScreenFlag`, `JoypadOverride`, `WorldSelectNumber+2` … `+4` |
| area | `AreaPointer`, `EntrancePage`, `AltEntranceControl`, `HalfwayPage`, `WarpZoneControl`, `CurrentPlayer`, `AreaType`, `LoopCommand`, `CloudTypeOverride`, `BackgroundColorCtrl`, `ScrollThirtyTwo+1`, `VerticalScroll` |
| timers | `GameTimerExpiredFlag`, `FetchNewGameTimerFlag`, `StarInvincibleTimer`, `ScreenTimer`, `WorldEndTimer`, `DemoTimer` |
| input | `Up_Down_Buttons`, `Left_Right_Buttons` |
| Mario | `Player_State` |
| slots that stay empty | `Enemy_Flag+4` … `+6`, `Enemy_ID+3` … `+6`, `Enemy_State+4`, `+5`, `Fireball_State` (2), `Block_State` (4), `Block_RepFlag` (2), `Misc_State` (9), `Misc_Y_Position+7`, `Misc_Collision_Flag+10` … `+12`, `FloateyNum_Control` (7), `FirebarSpinSpeed+14`, `+15`, `MaximumRightSpeed+18`, `+19`, `SprDataOffset_Ctrl+1`, `Cannon_Offset`, `Cannon_PageLoc` (6), `Cannon_X_Position` (6), `Cannon_Y_Position` (5), `FireballCounter`, `DuplicateObj_Offset`, `VineFlagOffset`, `VineHeight`, `FlagpoleFNum_Y_Pos`, `FlagpoleFNum_YMFDummy`, `FlagpoleScore` |
| enemy data | `EnemyData`, `EnemyDataHigh`, `EnemyObjectPageLoc`, `EnemyObjectPageSel`, `EnemyFrenzyBuffer`, `EnemyFrenzyQueue`, `SecondaryHardMode` |
| sound | `NoiseSoundBuffer`, `AreaMusicBuffer`, `EventMusicBuffer`, `AreaMusicQueue`, `EventMusicQueue`, `NoiseSoundQueue`, `Square2SoundQueue`, `Square1SoundQueue+1` |

**The bytes with a mask.**

| bytes | free bits | what it allows |
|---|---|---|
| `Enemy_ID` (first 3 slots) | bits 1, 2 | some kinds of enemy |
| `Enemy_State` (first 4 slots) | bit 0 | |
| `Misc_Y_Position+8` | bits 0, 1, 5, 6 | |
| `Square1SoundQueue` | bit 4 | one sound |
| `SprDataOffset_Ctrl` | bit 0 | |
| `PlayerStatus` | bit 0 | small or big Mario. Fire Mario does not meet `Entry` |
| `GamePauseStatus` | bits 0, 7 | |
| `AreaMusicBuffer_Alt` | bit 2 | the underground song in the saved song |

**The places.** `Places(t)` says: if the program counter of `t` is one of these places, then the dot of `t` is at most the bound, and `t` has the values of one row of the place.

| place | rows | dot at most |
|---|---|---|
| `NonMaskableInterrupt` | 1,061 forms of the screen buffers: the first byte and the length of each record | no bound |
| `MusicHandler` | 1,607 rows of the song | no bound |
| `EnemyGfxHandler`, `PlayerGfxHandler` | 3 rows of the sprites' offsets | no bound |
| `UpdScrollVar` | 67 rows of the area parser | 50,000 |
| `ColorRotation` | all 256 values of `VRAM_Buffer1_Offset` | no bound |
| the store into the block buffer in `HandleEToBGCollision` | none: not reached | |
| after the first `BCS` of `PositionEnemyObj` | none: not reached | |
| after the first `BCC` of `CheckRightExtBounds` | none: not reached | |

So on the pipe's frames: no enemy stands on a block that is being bumped, the next enemy of the level's data is not loaded, the frame reaches the parser's place before dot 50,000, and the song, the screen buffers, the sprites' offsets and the area parser are in one of the rows. A frame has 89,342 dots.

**The condition at the exit.** `ExitAt(m)` says that `OperMode_Task`, `ScreenRoutineTask`, `GameEngineSubroutine` and `DisableScreenFlag` have the values of `T`. At such a state the run must have:

* `Quiet(m)`: `PauseSoundBuffer`, `PauseSoundQueue`, `Square1SoundBuffer` and `Square2SoundBuffer` have the values of `T`. `NoiseSoundBuffer` and `VRAM_Buffer_AddrCtrl` have them too, but the run need not say so: the check proves it on the exit frame. `NoiseSoundBuffer` is in `K` and no frame of the pipe changes it. The NMI sets `VRAM_Buffer_AddrCtrl` to 0, and the exit frame does not run the game engine after the pipe's routine.
* `Song(m)`: the 12 bytes of the song (`MusicData` (2), the four offsets, `NoiseDataLoopbackOfs`, the note counters and buffers) have the values of one of the 1,607 rows. On a frame that ends a part of the song, `GroundMusicHeaderOfs` is in the row too.
* `Shape(m)`: the first screen buffer is empty, or it holds one record of 4 bytes of the palette.

`Exit(m)` is `ExitCond(m)` of [the side pipe's last frames](d-2-3-SideChangeEnd.md) with the 21 bytes of the exit (`OperMode`, `OperMode_Task`, `GameEngineSubroutine`, `ScreenRoutineTask`, `DisableScreenFlag`, `AreaPointer`, `EntrancePage`, `AltEntranceControl`, `HalfwayPage`, `CurrentPlayer`, `JoypadOverride`, `GameTimerExpiredFlag`, `AreaMusicBuffer`, `EventMusicBuffer`, `AreaMusicQueue`, `EventMusicQueue`, `Square1SoundQueue`, `Square2SoundQueue`, `NoiseSoundQueue`, `WorldNumber`, `PrimaryHardMode`) and the 6 bytes `PauseSoundBuffer`, `PauseSoundQueue`, `Square1SoundBuffer`, `Square2SoundBuffer`, `NoiseSoundBuffer`, `VRAM_Buffer_AddrCtrl`, with the values of `T`, the bits of `PlayerStatus` (bits 1 to 7) and of `AreaMusicBuffer_Alt` (all but bit 2) as in `T`, and `Song(m) ∧ Shape(m)`. The walk of the pipe's frames gives all of these from `Entry`, but `Quiet`, `Song` and `Shape`.

`NoStart(m, i)` says: if `m` is in the game core with a routine other than the pipe's, the input `i` has no Start.

**The statement.** `During(m)` says that `m` is covered by one of the abstract start states of the pipe's frames. `InRows(m)` says that `m` is covered by the states of one of the rows, below. `InRowsT(m)` says the same of the rows of the time.

```
during     :  ∀ M,  Entry(M) → During(M)
atEntry    :  ∀ M,  Entry(M) → 91 ≤ left(M)
inRoutine  :  ∀ m,  During(m) → the pipe's routine runs in m
step       :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                left(m) ≤ left(frame(m, i)) + 1  ∧
                ( During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( Quiet ∧ Song ∧ Shape at frame(m, i)  →  InRows(frame(m, i)) ) ) )
atExit     :  ∀ m,  Exit(m) → InRows(m)
leftExit   :  ∀ m,  Exit(m) → left(m) = 43
rows       :  ∀ m, InRows(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRows(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
atControl  :  ∀ m,  ctl(m) → left(m) = 0
paused     :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) → Paused(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsGo     :  ∀ m,  InRows(m) → ¬Paused(m)
stepT      :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( Quiet ∧ Song ∧ Shape ∧ TimeOK at frame(m, i)  →  InRowsT(frame(m, i)) ) )
rowsT      :  ∀ m, InRowsT(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  InRowsT(frame(m, i))
zeroT      :  ∀ m,  InRowsT(m) → left(m) = 0 → ctl(m)

no_control_exit :  Exit(s₀)  ∧  (∀ n, s₍ₙ₊₁₎ = frame(sₙ, iₙ)  ∧  NoStart(sₙ, iₙ))  →  ∀ j < 43, ¬ctl(sⱼ)
PipeRun.bound   :  a run with the fields below  →  cnt(a) + 91 ≤ cnt(b)
Changes.bound₁  :  e₁ + 91 ≤ c₂
PipeRun.first   :  a run with the fields below  ∧  time  ∧  ctlFirst  →  ∀ n, a ≤ n < b,  left(seq n) ≠ 0
PipeRun.inRowsT :  the same  →  InRowsT(seq b)
Changes.first₁  :  ∀ n, a₁ ≤ n < b₁,  left(seq n) ≠ 0        (PipeRun.first with chg.time₁ and Changes.ctlFirst₁)
```

The fields of `PipeRun`, and of the first change in `Changes` (there `atCtl` is the theorem `Changes.ctl₁`):

```
entry    :  Entry(seq a)
atCtl    :  ctl(seq b)
lagPaused:  ∀ n, a ≤ n < b,  lag(n)  →  Paused(seq (n+1))
places   :  ∀ n, a ≤ n < b,  the pipe's routine runs in seq n  →  ∀ j, Places(trace(seq n, inp n, j))
quiet    :  ∀ n, a ≤ n ≤ b,  ExitAt(seq n)  →  Quiet(seq n) ∧ Song(seq n) ∧ Shape(seq n)
noStart  :  ∀ n, a ≤ n < b,  NoStart(seq n, inp n)
```

and, for `PipeRun.first` (in `Changes`: the field `time₁` and the theorem `Changes.ctlFirst₁`):

```
time     :  ∀ n, a ≤ n ≤ b,  ExitAt(seq n)  →  TimeOK(seq n)
ctlFirst :  ∀ n, a ≤ n < b,  ¬ctl(seq n)
```

`cnt` counts the frames that are not `lag`. `left` falls by at most one on every frame from the entry to control, and is 0 at control. A `lag` frame ends paused, and then `left` does not fall ([b-3-3](b-3-3-LagPaused.md)). So `91 ≤ left(seq a) ≤ cnt(b) − cnt(a)`. For `PipeRun.first`, by induction every machine from the entry to `b` is in the pipe's frames or in the rows of the time. In those rows `left` is 0 only with control (`zeroT`), and there is no control before `b`.

Lean: `Theorems/PipeChangeEnd.lean` (`cov_place`, `cov_zsplit`, `s_zsuccs`, `zlive_step`, `zframe_run`, `zframe_of_walk`, `z_step`, `in_rows`, `in_rowsT`, `exit_base`, `EndStatement`, `endStatement_of_check`, `PipeRun`, `PipeRun.bound`, `during_left`, `PipeRun.timeWay`, `PipeRun.first`, `PipeRun.inRowsT`, `no_control_exit`), `Theorems/Route.lean` (`Changes.run₁`, `Changes.bound₁`, `Changes.first₁`), private `pipe_end_checks` (`native_decide`), `pipe_end`, `pipe_exit_no_control`, `pipe_change_end`. The theorems without ROM use only `propext`, `Classical.choice` and `Quot.sound`.

## How it works

**The frames of the pipe.** The abstract machine of [the side pipe's first frames](d-2-2-SideChangeBound.md) fails here when the song, the screen buffers, the sprites' offsets and the area parser are free: there are too many paths. So the statement asks for `Places`, and the abstract machine uses it. At a place a state splits into one state for each row (`placeSplit`). A state that fits no row goes no further. This is sound because the real machine fits a row there (`cov_place`). An instruction that reads or writes through a value known in all but at most 4 bits splits the state into one state for each value of those bits (`zsplit`): the accumulator at `JumpEngine`, the low byte of the pointer at an indirect load or store, `X` or `Y` at an indexed store. `s_zsuccs` proves these steps against the real step. `zframe_run` follows the real frame step by step with `trace`: at each step a state of the walk covers the machine.

**The check of the frames.** From the start states of `Entry`, a search makes a table of states. The check walks from each state of the table. Each state it reaches at a place of the table is covered by a state of the table, and each frame's end is covered by a start state again, or is the exit.

| frames | search steps | states in the table |
|---|---|---|
| the timer ≥ 2 | 902,238 | 36,062 |
| the timer = 1 | 527,799 | 23,135 |

The search holds states at some places until the others are done, and forgets some bytes there. This only makes the table small. The check does not depend on it. The low bit of `GamePauseStatus` is in the search's key ([b-3-3](b-3-3-LagPaused.md)).

**After the exit.** Frame 48 is the exit. Frames 49 and 50 clear RAM, and the clear crosses the end of frame 49. Then 41 frames come before control. These frames use the rows of [the side pipe's last frames](d-2-3-SideChangeEnd.md), in two cases of `PauseModeFlag`.

* Flag 0: one state for each form of the screen buffer and each row of the song, 6,428 states. Each goes alone to the place after the sound routines. There every 32nd one is joined, without the song's bytes, and the search goes on from them. The check walks from all 6,428.
* Flag not 0: the sound routines do not run. One state for each form, each alone to the same place.

Each case has 44 rows, with `left` from 43 to 0.

**The rows of the time.** In the case of flag 0, the last row holds the states with control and the states where the time is up, because the game timer's digits are free there. The rows of the time are the rows of this case where `dg` says that the three digits are not all 0, as in [the side pipe's last frames](d-2-3-SideChangeEnd.md): a state that knows a bit 1 in a digit gets `dg` back at a frame's end (`normD`), and the states with `dg` and those without it are not put together. The entrance's setup may load the timer on `FetchNewGameTimerFlag`, so the search keeps this flag apart. They have 44 rows and 8,118 states. The last row has 2 states, both with control (`zeroCtl`). At these 2 states every bit of the room's condition `Room` is known as in its reference ([d-2-4-1](d-2-4-1-ScreenStart.md)).

**The rows of the places.** They come from frames of reference runs: `E` with no input for 47 frames, `E` with `Player_X_Scroll` set to 3 and the timer set to 230, for 225 frames, the 13 real entries of [b-2-1](b-2-1-PipeTransitionAll.md) for 47 frames each, and the frames of the way from `m₀` to `E`, for the starts of the parser's columns near those of `E`. At the start of a column the parser clears the metatile buffer before it reads it, so those rows leave the metatile buffer free. The forms of the screen buffer add every form with up to 2 records, made from the first bytes seen, with lengths 1 to 8. The song's rows are the song played from `m₀` with no input for 5,327 frames: its period is 5,184 frames, after 143 frames of the start.

**The size of the check.** About 49 s in a program on a loaded machine, where the same check without the rows of the time took 36 s; 57 s in the private proof build.

## Facts that are false

* `fall₁` is false on states that meet the condition of [A bound from single frames](b-2-2-PipeChangeBound.md). With `HalfwayPage` set to 1 at `E`, control comes after 75 frames, and `left` falls from 18 to 0 on frame 73. With `WarpZoneControl` set to 1, control comes after 228 frames, and `left` falls from 36 to 0 on frame 55. With `GameTimerExpiredFlag` set to 1, control comes after 229 frames, and `left` falls from 37 to 0 on frame 54. These bytes are in `K`, so `Entry` does not hold on these states. Measured with no input.
* `Quiet` is false on real runs when Start is pressed on the pipe's frames. Below, it fails on 129 of 437 runs with random Start on the pipe's frames. These runs asked the 6 bytes. With the 4 bytes asked now, `pipe-end-check` gives the same: 6 of 15 runs fail with Start on the pipe's frames, 0 without Start.

## Measured but not a theorem

**The time at the exit.** `pipe-end-check`: from `E`, the TAS entry and the 13 real entries, with the three kinds of inputs, every exit with the condition at the exit has `TimeOK`, and no frame before control has `left` 0. `room-start-check` gives the same on 615 runs, and `changes-check` on the TAS. With the game timer written to 000 at `E` and no input, `TimeOK` fails at the exit; at frame 91 `left` is 0, and the routine there is the death's, with no control. With 001, control comes at frame 91. So `time₁` is needed.

**Entries.** The table below was measured before `WorldNumber`, `PrimaryHardMode` and the bits of `AreaMusicBuffer_Alt` were added to `Entry`. With them, `Entry` holds on the 15 entries of `pipe-end-check` and on the TAS (`changes-check`).

Entries: `E`, the TAS entry, the 13 real entries, and 422 entries of runs of my own from `m₀`. These are random play to the pipe: plain, with stomps, started big, big with stomps, after waiting 1,000, 2,500 or 4,000 frames, after going past `x` = 980 and back. They are in two sets made with other seeds. From each entry, inputs of three kinds until control.

| inputs | runs | `Entry` holds | frames of the pipe | frames against `Places` | `Quiet ∧ Song ∧ Shape` at the exit | frames where `left` falls by more than one | least frames to control |
|---|---|---|---|---|---|---|---|
| none | 437 | 437 | 20,976 | 0 | 437 | 0 | 91 |
| random, no Start | 437 | 437 | 20,976 | 0 | 437 | 0 | 91 |
| random, Start on the pipe's frames only | 437 | 437 | 48,044 | 0 | 308 | 0 | 136 |

`Song ∧ Shape` held at all 437 exits of each kind. Only `Quiet` failed, and only with Start. These runs asked the 6 bytes of `Quiet` as it was then. The 4 bytes asked now hold wherever the 6 bytes held. Before the rows of the parser's column starts were added, 11 of 1,920 frames of the plain runs were against `Places`.

## Assumptions (not proved in Lean)

* `Entry` on the state at the entry of a real run. Item 1-1-b-3-4. It is no longer a field: `Run.entry₁` proves it from the press of Start on the title, the frames from control to the entry (`upClean₁`; that each starts in control is proved, `Run.upStart₁`) and `Rest` (`entryRest₁`: 56 of the 128 bytes; the pipe's timer is proved). See [the state at the vertical pipe's entry, from the title](b-3-4-EntryKeep.md).
* `Places` on every step of the pipe's frames (`chg.places₁`). The rows come from the frames of a few runs. A run where an enemy is loaded, or where the parser has a column not in the rows, is outside. Item 1-1-b-3-5:
  * With all 256 values of `VRAM_Buffer1_Offset` and no bound, the place `ColorRotation` asks nothing of a run. The state splits there by the offset, and the check needs that.
  * `ProcELoop`, `FlagpoleRoutine`, `BlockObjMT_Updater` and `ColorRotation` had a bound of 50,000 on the dot. They are gone. The check holds with any 4 of the 5 bounds dropped (`UpdScrollVar` and these 4), and it fails with all 5 dropped. So one bound stays, at the parser's place. On 14 entries with the three kinds of inputs, the 1,974 frames of the pipe come to the parser's place at dot 37,603 at most.
* `Quiet ∧ Song ∧ Shape` at the exit (`chg.quiet₁`). It fails after Start on the pipe's frames. `Shape` and `Song` do not follow from the walk of the exit frame: none of the 36 end states of that walk at the exit knows the form of the first screen buffer or the song's bytes. When the exit frame's NMI writes from the second buffer, the first buffer keeps what the frame before wrote, and the walk of one frame does not know it.
* `NoStart` on the frames of the game core after the pipe (`chg.noStart₁`).
* `TimeOK` at the exit (`chg.time₁`). Item 1-1-b-3-9. That `b` is the first control after the entry is no longer a field (the field `ctlFirst₁` is gone): `b₁` is the first frame with control from the entry on, within `dB` frames (the definition `Base.b₁`: `b₁ = firstCtl(seq, a₁, dB)`), and `ctlBy₁ : ctl(seq (a₁ + dB))`. Then `Changes.order₁ : a₁ ≤ b₁`, `Changes.ctl₁ : ctl(seq b₁)` and `Changes.ctlFirst₁ : ∀ n, a₁ ≤ n < b₁ → ¬ctl(seq n)` are theorems, as for `b₂`. `TimeOK` fails with a pause in the pipe (`changes-check FM2 pause 380 60` and `pause 416 60`), on the same exit where `Quiet` fails.
* `lagPaused` (`chg.paused₁`): a `lag` frame ends paused. See [b-3-3](b-3-3-LagPaused.md).

**Files.** `Theorems/PipeChangeEnd.lean`, private `Proof/PipeChangeEnd.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta pipe-end-check FM2    # the check, the conditions on E, the TAS entry and 13 real entries with three kinds of inputs, the time at the exits, about 2 min
.lake/build/bin/smbrta changes-check FM2     # the fields of Changes on the TAS run
```
