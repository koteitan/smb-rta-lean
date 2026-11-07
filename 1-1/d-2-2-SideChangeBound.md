[← Back](README.md) | [English](d-2-2-SideChangeBound.md) | [Japanese](d-2-2-SideChangeBound-ja.md)

# The first frames of the change out of the side pipe, from one frame

**Claim.** This is a partial result. Every machine that meets a condition on one state has no control on the first 160 frames after the entry, for any inputs. The proof looks at one frame only, and the 160 frames follow by a formula. The frames after the pipe's timer are not proved here. That a real run meets the condition is not proved either.

`m₀`, `run`, `ctl`, `0^k` and `E` are those of [What decides the change out of the side pipe](d-2-1-SideTransitionAll.md). `w[..j]` is the first `j` inputs of `w`. `timer(m)` is `ChangeAreaTimer`. `frame(m, i)` is one real frame with the input `i`.

**The condition.** `EntryCond(M)` is a condition on the state `M` at the end of the entry frame.

* The frame has ended in the idle loop: the program counter and the stack pointer are those of `E`, the dot is at most 9, the vblank and NMI flags fit the dot, the sprite-0 flag is set, NMI is on in the PPU control, the controller is not strobed.
* `timer(M) ≥ 160`. This excludes the states with the screen on another page (174 frames) and the states where the entry frame did not write the timer: their timer is smaller.
* `K`, 82 bytes, have the values they have in `E`. They are listed below.
* The buffer of the screen is empty, or it holds the one record of the colour rotation. This adds 3 bytes in the second case. These two cases are taken from `E` 0 and 6 frames later.

All other bytes are free: Mario's `x`, speed, size and status, the coins, the score, the digits of the game timer, the pause bytes, the frame counter, the random bytes, the rest of the music and sound state, the sprites, the block buffer, and the temporary bytes.

**The list `K`**, by name:

| group | bytes |
|---|---|
| the mode | `OperMode`, `OperMode_Task`, `GameEngineSubroutine`, `ScreenRoutineTask`, `DisableScreenFlag`, `WorldNumber`, `AreaType`, `SecondaryHardMode` |
| Mario | `Player_State`, `Player_Y_HighPos`, `Player_Y_Position`, `Player_SprDataOffset`, `JumpspringAnimCtrl` |
| objects | `Enemy_Flag` (6), `Enemy_ID+5`, `Fireball_State` (2), `Block_State` (2), `Block_RepFlag` (2), `Misc_State` (9), `FloateyNum_Timer` (6), `VineFlagOffset`, `Cannon_PageLoc` (6), `Cannon_X_Position` (6), `Cannon_Y_Position` (4), `StarInvincibleTimer` |
| the area's enemies | `EnemyData` (2), `EnemyDataOffset`, `EnemyObjectPageLoc`, `EnemyFrenzyBuffer`, `EnemyFrenzyQueue` |
| the screen | `ScreenRight_PageLoc`, `ScreenRight_X_Pos`, `ScrollLock`, `ScrollThirtyTwo`, `AreaParserTaskNum`, `VRAM_Buffer_AddrCtrl`, `VRAM_Buffer1_Offset`, `VRAM_Buffer1` |
| music | `AreaMusicBuffer`, `EventMusicBuffer`, `MusicData` (2), `MusicOffset_Square1`, `NoiseSoundBuffer`, `AreaMusicQueue`, `EventMusicQueue`, `NoiseSoundQueue` |

**The state during the pipe.** `During(m)` says that `m` is covered by an abstract start state, with the same `K`. In one form the timer is at least 2 and not known. In the other it is known to be 1. `Exit(m)` says that `m` has the values of `T = run(E, 0^160)` in `OperMode_Task`, `ScreenRoutineTask`, `GameEngineSubroutine`, `DisableScreenFlag`.

**The number `left`.** During the pipe's routine in the game core, `left(m) = timer(m) + 122`. Otherwise it comes from a table of 122 rows: `T` run with no input, each key with the frames left. A key not in the table has `left = 0`. This is the `left` of [A bound from single frames](b-2-2-PipeChangeBound.md), with another table.

```
during       :  ∀ M,  EntryCond(M) → During(M)
step         :  ∀ m, During(m) → ∀ i :
                  ( During(frame(m, i)) ∧ timer(m) ≤ timer(frame(m, i)) + 1 )  ∨  ( timer(m) = 1 ∧ Exit(frame(m, i)) )
noFirst      :  ∀ M,  EntryCond(M) → ∀ w, ∀ j ≤ |w|, j ≤ 160 → ¬ctl(run(M, w[..j]))
fall         :  ∀ m, During(m) → ∀ i,  left(m) ≤ left(frame(m, i)) + 1
atEntry      :  ∀ M,  EntryCond(M) → 282 ≤ left(M)
atControl    :  ∀ m,  ctl(m) → left(m) = 0
noAll        :  ∀ M,  EntryCond(M) → ∀ w,
                  (∀ j < |w|, ¬During(run(M, w[..j])) → left(run(M, w[..j])) ≤ left(run(M, w[..j+1])) + 1)
                  → ∀ j ≤ |w|, j < 282 → ¬ctl(run(M, w[..j]))
no_input     :  ∀ M,  EntryCond(M) → ∀ k, 1 ≤ k ≤ 160 → ¬ctl(run(M, 0^k))
ChangeRun.bound :  for a run with the fields of `ChangeRun` :  cnt(a) + 282 ≤ cnt(b)
```

`no_input` is `(H1)` of `SideTransitionAll.every_entry`. `(H2)` and `(H3)` do not follow: the pause bytes are free, so the timer can be later than the frame count, and the condition does not fix the place of the state at frame 160. The route does not need them for a lower bound.

Lean: `Theorems/SideChangeBound.lean` (`frame_of_walk`, `inv_step`, `inv_seq`, `state_seq`, `fall_of_inv`, `no_control_first`, `no_control_all`, `inv_of_entry`, `entryCond_of_ok`, `Statement`, `statement_of_check`, `Statement.no_input`, `change_counted`, `ChangeRun`, `ChangeRun.bound`), private `side_bound_checks` (`native_decide`), `side_bound`, `side_no_control`, `side_change_bound`. The theorems with no ROM use only `propext`, `Classical.choice` and `Quot.sound`.

## How it works

**The abstract machine.** It is the machine of [A run with unknown bytes](b-2-3-TaintRun.md), copied into this file with three changes. The pad is a byte with unknown bits. The pipe's timer is a followed counter: its value is not known, but `Sim` says that it has fallen by at most one in this frame, and no instruction other than its `DEC` may write it. A byte can be read in pieces by some of its bits: the frame counter is read by its low 3 bits, because `ColorRotation` uses them as an index.

**One frame.** From the start states, one frame of the abstract machine ends only in the start states. So every frame of the pipe stays in `During`. With the timer at 1, the frame ends in `During` (a pause) or in `Exit`. The check follows 106,824 abstract steps with the timer free and 52,701 with the timer at 1. The tables have 4,584 and 2,519 states. The program takes about 1 s; the private proof takes about 33 s to build, because `Theorems` is not precompiled.

**Why it closes here.** In the pipe's routine the code does not run the collision with the level (`PlayerBGCollision` leaves on this routine) and does not run the game timer (`RunGameTimer` leaves). So the timer is not written again, and no hurry-up music can start in these frames. The room's song has no square-1 part (`MusicOffset_Square1` says so), so the music loop that can hang on zeros does not run.

**Why the slots stay empty.** With `K`, the check shows that the listed object bytes keep their values on every frame of the pipe. In the rest of the room, this is read from the code and the map, and is not in Lean. The room's enemy data has no enemy on this page: `EnemyDataOffset` stands at an entry beyond the locked screen's right edge, so `ProcessEnemyData` adds nothing. The frenzy queue is not set in this area. No cannon is set up in this area, so none fires. The block buffer has no block with an item. A fireball needs two power-ups, and 1-1 has one power-up before this pipe.

**Inputs.** A pause keeps the timer. It is covered, because the pad and the pause bytes are not known. `Start` held from the first frame gives no control in 1,500 frames on real entries.

**What is not covered by the method.** The frame after the pipe clears the RAM, and the frame ends inside that loop. The abstract machine fails on a frame that ends outside the idle loop, so the last 122 frames are not proved. [Item 1-1-d-2-3](../README.md) does not go.

## Measured, not a theorem

The program ran real frames from these entries.

| entries | number | with the condition |
|---|---|---|
| `E` and the TAS's entry | 2 | 2 |
| real entries of `side-all-real` | 42 | 42 |
| random runs to the room, then random play | 21 | 21 |
| the same, with big Mario overwritten at the start of 1-1 (5 still big at the entry) | 7 | 7 |
| the same, with the digits of the game timer overwritten near 100 in the room | 5 | 4 |
| the same, with fire Mario overwritten at the start of 1-1 | 3 | 0 |

* From each of the 76 entries with the condition, with no input, random inputs without `Start`, random inputs, and `Start` held: 199,995 frames. `left` never falls by more than one. Control comes only at `left = 0`. `left = 282` at each entry. The least number of frames to control is 282. With `Start` held, no run has control in 1,500 frames.
* The one entry with the game timer near 100 that fails has the hurry-up music playing: `AreaMusicBuffer`, `EventMusicBuffer`, `MusicData`, `MusicOffset_Square1` differ. The 3 entries of fire Mario fail on `Fireball_State`.
* The overwritten states with a shorter change, 174, 174 and 127 frames, do not meet the condition.
* On the 44 entries of the program, in one run, the frames where the timers do not run and `left` falls number 0 (`Start` held) or 1.

## Assumptions (not proved in Lean)

* `EntryCond` on the state at the entry of a real run. The bytes of `K` are constant in the room on the runs sampled. That they hold on every run is read from the code. In particular:
  * `timer ≥ 160` means that the screen is on the first page on the entry frame ([item 1-1-d-2-4](../README.md)).
  * `Player_Y_Position` is the floor's, because the mouth's tile is only at the floor.
  * The object bytes are as above. `Block_State` needs that no brick breaks just before the entry.
  * The music bytes do not hold while the hurry-up music plays, that is, when the game timer has just passed 100. Such a run has used far more than 1748 frames.
* On the frames out of `During`, `left` falls by at most one (`fallAfter` of `ChangeRun`, the hypothesis of `noAll`). This is the last 122 frames.
* A lag frame takes nothing off `left` (`lagKeeps` of `ChangeRun`). On real runs measured, the one frame where the timers do not run and `left` falls is the `setup` frame of the change.
* `Route` does not use this theorem yet. `ChangeRun` lists the fields that make `change₂` a consequence.

**Files.** `Theorems/SideChangeBound.lean`, private `Proof/SideChangeBound.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-bound-check FM2    # the check, the condition on real entries, left on real frames, about 30 s
```
