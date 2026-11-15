[← Back](README.md) | [English](b-3-7-2-PipePause.md) | [Japanese](b-3-7-2-PipePause-ja.md)

# The pause through the vertical pipe's frames

**Claim.** Suppose that at the vertical pipe's entry the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed on that frame (`PauseV`). Then on the frames of the pipe, for any input, Start included, the six bytes of the pause stay in one of 88 classes, and at the exit the pause is as `QuietV` says. This is proved, with a check on the ROM. So the route asks less at the exit: `chg.quiet₁` (item 1-1-b-3-7) no longer asks the pause sound's buffer, flag and counter, only that the pause sound's queue is as at the reference and, when the pause sound is silent, the two squares' effects and the song (`QuietRest`). `chg.pause₁` (the condition `PauseV` at the entry) was new; it is now proved ([1-1-b-3-7-3](b-3-7-3-EntryPause.md)). On real runs with Start at random, `PauseV` held at all 334 entries, every one of 90,963 frames of the pipe was in a class, and `QuietV` held at all 1,002 exits.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `trace(m, i, j)` is the machine after `j` steps of that frame. `x = run(E, 0^48)` is the reference machine at the exit. `During`, `ExitAt`, `Places` and `left` are those of [the change into the room without `fall`](b-3-2-PipeChangeEnd.md). `QuietP`, `SongAt`, `song`, `shape`, `TimerOK` and `InRowsK` are those of [the change into the room, with the sound's bytes in tables](b-3-7-1-SoundRows.md). `SIn(t, m)` says that the bytes of `m` are in the state `t` of a table.

## The six bytes of the pause

`q`, `b`, `f`, `c` are the queue, the buffer, the flag and the counter of the pause sound (`PauseSoundQueue`, `PauseSoundBuffer`, `PauseModeFlag`, `Squ1_SfxLenCounter`). `t` is the pause timer (`GamePauseTimer`), `g` the pause byte (`GamePauseStatus`). `s₁`, `s₂` are the buffers of the two squares' effects. `U` is the value of the unpause sound, `P` that of the pause sound, `L` the length of the sound; they are read from the ROM through symbols. How the game uses the six bytes is told on [the pause through the side pipe's frames](d-3-4-3-SidePause.md): while a pause sound plays, `t = c + 1`, and Start does nothing.

## The classes

| class | `g` | `q` | `b` | `f` | `c` | `t` | number |
|---|---|---|---|---|---|---|---|
| silent | 0 or bit 7 | 0 | 0 | 0 | any | any | 1 |
| the unpause sound | bit 7 | 0 | `U` | `U` | `k` | `k + 1` | `k` = 1 … `L − 1`: 41 |
| the unpause pressed | bit 7 | `U` | 0 | `P` | any | `L + 1` | 1 |
| the pause pressed (paused) | bits 0 and 7 | `P` | 0 | any | any | `L + 1` | 1 |
| the pause sound (paused) | bits 0 and 7 | 0 | `P` | `P` | `k` | `k + 1` | `k` = 1 … `L − 1`: 41 |
| the pause sound over (paused) | bits 0 and 7 | 0 | 0 | `P` | 0 | 1 | 1 |
| | bit 0, with or without bit 7 | 0 | 0 | `P` | 0 | 0 | 2 |

The bits of `g` not named are 0. These are the classes of the side pipe with three changes: the flag is 0 when silent, the two silent classes are one (bit 7 of `g` not known), and the counter of the unpause sound stops at `L − 1`. The sound sets the counter to `L` and takes one off on the same frame, so `L` is never seen at a frame's end.

```
PauseV(m)     :=  ( m[g] ∈ {0, 0x80}  ∧  m[q] = 0  ∧  m[b] = 0  ∧  m[f] = 0 )
               ∨  ( m[g] = 0x80  ∧  m[q] = 0  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] < L  ∧  m[t] = m[c] + 1 )
               ∨  ( m[g] = 0x80  ∧  m[q] = U  ∧  m[b] = 0  ∧  m[f] = P  ∧  m[t] = L + 1 )

QuietV(m)     :=  ( m[q] = 0  ∧  m[b] = 0  ∧  m[f] = 0 )
               ∨  ( m[q] = 0  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] < L )
               ∨  ( m[q] = U  ∧  m[b] = 0  ∧  m[f] = P )

QuietRest(m)  :=  m[q] = x[q]  ∧  ( m[b] = x[b]  →  m[s₁] = x[s₁]  ∧  m[s₂] = x[s₂]  ∧  SongAt(song, m) )
```

`PauseV` says that `m` is in one of the first three rows of the table. At the exit the frame is not paused, so the machine is in one of these three rows: that is `QuietV`. The check asks `x[q] = 0`, `x[b] = 0` and `U ≠ 0` (`exitVOK`). Then

```
QuietV(m)  ∧  QuietRest(m)   →   QuietP(m)                     (quietP_of_V)
```

`QuietRest` excludes the third row of `QuietV`: its queue is `U`, not `x[q]`.

## The statement

`DuringV(m) := During(m) ∧ (∃ t ∈ classesV, SIn(t, m)) ∧ TimerOK(m)` (`TimerOK` since round 13). `EndStatement` has two new fields; the check `endCheck` now also runs `pipeCheckV` and `exitVOK` (`endStatement_of_check`). The first line below needs no ROM.

```
class_of_pauseV :  PauseV(M)  →  ∃ t ∈ classesV, SIn(t, M)
pauseStep       :  ∀ m, DuringV(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                     DuringV(frame(m, i))
                   ∨ ( ExitAt(frame(m, i))  ∧  QuietV(frame(m, i))  ∧  TimerOK(frame(m, i))  ∧  ( QuietP ∧ SongAt(shape) at frame(m, i)  →  InRowsK(frame(m, i)) ) )
pauseExit       :  ∀ m,  QuietV(m) ∧ QuietRest(m)  →  QuietP(m)
```

Since round 13, `DuringV` also has `TimerOK`, the walk has the game timer's digits as its bytes `D`, and `pauseStep` gives `TimerOK` at the exit with no premise: see [the game timer at the vertical pipe](b-3-9-1-PipeTime.md). Before, the last line asked `TimerOK` at the exit as a premise of `InRowsK`.

**A run.** `PipeRunK` has the new field `pause : PauseV(seq a)`, and its field `quiet` asks `QuietRest ∧ SongAt(shape)` at the exit in place of `QuietP ∧ SongAt(shape)`. Its theorems are as before, with the same arguments. In their induction every machine from the entry is `DuringV` or in the rows with tables (`PipeRunK.stepD`, `PipeRunK.atEntry`):

```
PipeRunK.bound   :  cnt(a) + 91 ≤ cnt(b)
PipeRunK.first   :  hc  →  ∀ n, a ≤ n < b,  left(seq n) ≠ 0
PipeRunK.inRowsT :  hc  →  InRowsT(seq b)
```

`Route` takes the first change from `ChangesK.run₁`, which takes `pause` from the condition at the entry. That was the field `chg.pause₁`; since round 11 it is proved ([the pause at the vertical pipe's entry, from the title](b-3-7-3-EntryPause.md)):

```
chg.pause₁ :  PauseV(seq a₁)                                                          (new in round 10; proved in round 11, Run.entry₁)
chg.quiet₁ :  a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  QuietRest(seq n) ∧ SongAt(shape, seq n)    (was QuietP ∧ SongAt(shape))
```

`QuietP ∧ SongAt(shape) → QuietRest ∧ SongAt(shape)`, so the new `quiet₁` is weaker than the old one.

Lean: `Theorems/PipeChangeEnd.lean` (`PR`, `retOf`, `inR`, `low7`, `forgetP`, `pret`, `pout`, `psuccs`, `Ph`, `pcover`, `pwalk`, `mem_low7`, `forgetP_k`, `sim_forgetP`, `s_psuccs`, `PLive`, `cover_plive`, `plive_step`, `pframe_run`, `pframe_of_walk`, `ploop`, `pcfgOf`, `POK`, `pcheck`, `p_step`, `pauseTI`, `classesV`, `PauseV`, `QuietV`, `QuietRest`, `prOf`, `cfgRq`, `cfgOq`, `pipeCheckV`, `exitVOK`, `class_of_pauseV`, `quietV_of_class`, `quietP_of_V`, `EndStatement.pauseStep`, `EndStatement.pauseExit`, `DuringV`, `PipeRunK.pause`, `PipeRunK.atEntry`), `Theorems/Route.lean` (`ChangesK.pause₁`, `ChangesK.quiet₁`, `ChangesK.run₁`). The private check is still `pipe_end_checks` in `Proof/PipeChangeEnd.lean`. There is no game data in these files.

## How it works

**Why the class is carried beside the walk.** The walk of the pipe's frames ([b-2-2](b-2-2-PipeChangeBound.md), [b-3-2](b-3-2-PipeChangeEnd.md)) follows the pipe's timer with the bit `rk` of the abstract state, and the bit `spent` says whether the timer has fallen on this frame. The tables of [`StepWrites`](d-3-4-1-StepWrites.md) use `spent` for another purpose, so the six bytes cannot be carried in such tables here. As known bytes of the walk's states, as on the side pipe, the classes would multiply the walk of about 60,000 states.

**The routine.** The frame's interrupt calls the sound routine, the reading of the pads and the pause routine, one after the other. Only these read or write the six bytes. The call of the sound routine is found as in [b-3-7-1](b-3-7-1-SoundRows.md) (`rtOf`); the return after the pause routine is 9 bytes after it. A state is in the routine (`inR`) if it is at the second or the third call, or if the stack holds one of the three return addresses at the stack pointer of the interrupt's body (three below the idle loop's).

**The step (`psuccs`).** At the first call, a state is split into one piece for each class that agrees with it, and the walk then knows the six bytes. At the call of the pause routine the state is split by bit 7 of `g`, because that routine adds 1 to `g`. At the return the six bytes must be in a class, and they are forgotten, but for bits 0 to 6 of `g`: the rest of the frame reads bit 0. Outside the routine no step may write the six bytes (`keepOK`). So `Ph(A, m) := inR(A) ∨ ∃ t ∈ classesV, SIn(t, m)` holds for each state `A` of the walk that covers the machine `m` (`s_psuccs`). A state of the table covers a state of the walk only if both are in the routine or both are outside (`pcover`). The frame's end is outside the routine. The bits `rk` and `spent` are as the step of [b-3-2](b-3-2-PipeChangeEnd.md) sets them, so the pipe's timer is still followed.

**Why one silent class.** With two silent classes (`g` = 0 and `g` = `0x80`) each one walks the song through the sound routine: 81,021 of the 97,062 states of the table were in the sound routine. With one class and the split of bit 7 at the call of the pause routine there are 40,781.

**The search** makes the tables of the walk with the same step, the six bytes kept apart (`ploop`, `pcfgOf`). The check does not depend on it.

**The size of the check.** 88 classes. The tables have 56,816 states (the timer at 2 or more) and 43,120 (the timer at 1); the old walk's have 36,062 and 23,135. In a program the new walk takes about 25 s (the search 12 s, the check 11 to 13 s), the old walk 13 s. The old walk stays: `EndStatement.step` without a class is used by `HurryStart`. The private build of `Proof/PipeChangeEnd.lean` takes 232 s (about 200 s before). This is more than a few seconds.

## Facts that are false

* **The unpause pressed on the frame of the exit** is allowed by `QuietV`, not by `QuietRest`: the queue holds `U`. Below it happened at 41 of 1,002 exits, and on the TAS with a pause at frame 416 for 60 frames (`changes-check FM2 pause 416 60`). As on [b-3-7-1](b-3-7-1-SoundRows.md), the room's condition fails at control on such runs, because the new song has not started. So `chg.quiet₁` still excludes runs that pause in the pipe and unpause on the frame of the exit.

## Measured, not a theorem

Program: `pipe-pause-real FM2 3 7`. 334 entries: the reference, the movie's, 26 real entries standing on the pipe and pressing Down, 180 entries on the reference's way with a pause of 44, 45 or 60 frames pressed 0 to 59 frames before its last frame, and 78 real entries after standing with Start at random. From each, the pipe's frames with random inputs and Start about once in 3, 9 and 40 frames.

| entries | `Entry` | `PauseV` | silent / unpause sound / unpause pressed | frames of the pipe | in a class | classes seen | exits | `QuietV` (silent / unpause sound / unpause pressed) | `QuietRest` and the screen buffer | `QuietP` |
|---|---|---|---|---|---|---|---|---|---|---|
| 334 | 334 | 334 | 113 / 134 / 87 | 90,963 | 90,963 | 88 of 88 | 1,002 | 1,002 (448 / 513 / 41) | 961 | 961 |

`changes-check FM2`: `pause₁` and the new `quiet₁` hold on the TAS. With a pause of 60 frames at 380, they hold too (the old `quiet₁` failed there); at 416 the new `quiet₁` fails, as above. At 545 they hold.

**The pause at the entry.** In round 10 the walk of [the state at the vertical pipe's entry, from the title](b-3-4-EntryKeep.md) knew none of the six bytes, so `chg.pause₁` was a new condition on one state. In round 11 the class is carried beside that walk too, and frame 0 gives a class at control: `PauseV` at the entry is proved ([1-1-b-3-7-3](b-3-7-3-EntryPause.md)).

## What the exit still asks, measured in round 12

The pause at the entry is now proved, so the pipe's frames give `QuietV` at the exit for any run. Each part of `QuietRest` was measured against the classes and the rows with tables. None of them follows; each stays, for these reasons.

* `m[q] = x[q]`: the classes allow `q = U` at the exit (the unpause pressed on the exit's frame). This happens on real runs (41 of 1,002 exits above), and then the room's condition `Room` fails at control, because the new song has not started (see [b-3-7-1](b-3-7-1-SoundRows.md)). So it stays as long as `Room` asks the area music's queue.
* `m[b] = x[b] → m[s₁] = x[s₁] ∧ m[s₂] = x[s₂]` (the two squares' effects when silent): no class knows them. The rows need them. With the first table of the rows without `s₁`, without `s₂`, or without both, the search of the first frame after the exit passes its limit of 8,000,000 steps; with both known it ends in 4.8 s with 1,111 states (`pipe-rows-fx none`, `s1`, `s2`, `both`). In the silent case the sound routine plays the effects and the song on that frame, so each value of an effect goes with each of the 1,607 rows of the song.
* `m[b] = x[b] → SongAt(song, m)` (the song's row when silent): no class knows the song, and the first frame after the exit plays it. A summary of the sound routine for any values of the song's bytes is false (round 6). The condition at the places (`chg.places₁`) gives a row of the song where the music handler starts on each frame of the pipe. To use it, a walk of the pipe's frames would have to carry the song's bytes after the music handler, as the pause's class is carried, and to count frames: when the unpause sound ends on the exit's frame, that frame does not run the music. The last frame that does is then the frame where the pause was pressed, a frame of the pipe, unless the unpause sound began before the entry; the pause timer shows that such a sound ends at most `L + 1` frames after the entry, fewer than the pipe's 48 counted frames. The walk of the pipe's frames does not count frames. Also a row asks the part's byte (`GroundMusicHeaderOfs`) only on a frame that ends a part, and the walk does not know it after the step. Not done.

## Assumptions (not proved in Lean)

* `PauseV` at the entry (`chg.pause₁`) is no longer assumed: [1-1-b-3-7-3](b-3-7-3-EntryPause.md) proves it, under `upClean₁` with the six bytes in the guard.
* `QuietRest ∧ SongAt(shape)` at the exit (`chg.quiet₁`, item 1-1-b-3-7): the queue of the pause sound as at the reference, and when silent the two effects and the song's row. Before, also the buffer, the flag and the counter of the pause sound.
* `NoStart` on the frames of the game core after the pipe (`chg.noStart₁`, item 1-1-b-3-6). Not done here; the paused rows of [d-3-4-3](d-3-4-3-SidePause.md) were measured and did not end.

**Files.** `Theorems/PipeChangeEnd.lean`, `Theorems/Route.lean`; the private check is `pipe_end_checks` in `Proof/PipeChangeEnd.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta pipe-pause-check              # the walk with the class beside it as a program, about 50 s; "old" also runs the old walk
.lake/build/bin/smbrta pipe-pause-real FM2 3 7       # the classes on real runs, about 2 min
.lake/build/bin/smbrta changes-check FM2 pause 416 60   # the fields on the TAS with a pause of 60 frames at 416
.lake/build/bin/smbrta pipe-rows-fx both              # the rows after the exit with the effects known (none, s1, s2: without them), about 1 min
```
