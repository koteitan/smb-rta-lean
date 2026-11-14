[← Back](README.md) | [English](d-3-4-3-SidePause.md) | [Japanese](d-3-4-3-SidePause-ja.md)

# The pause through the side pipe's frames

**Claim.** Suppose that at the side pipe's entry the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed on that frame (`PauseE`). Then on the frames of the pipe, for any input, Start included, the six bytes of the pause stay in one of 90 classes, and at the exit the pause sound is as `QuietK` says. This is proved, with a check on the ROM. So the route no longer assumes `QuietK` at the exit: `chg.quiet₂` is gone, and `chg.pause₂` (the condition `PauseE` at the entry) is new (1-1-d-3-4). On real runs with Start at random, `PauseE` held at all 636 entries, every one of 205,016 frames of the pipe was in a class (89 of the 90 classes were seen), and `QuietK` held at all 636 exits. `PauseE` at the entry is now proved from the room's first control ([The pause through the room's frames](d-3-4-4-RoomPause.md)): `chg.pause₂` is a theorem, and the route asks only that bits 1 to 6 of the pause byte are 0 there (`chg.pauseBits₂`).

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `Entry2`, `During2`, `Exit` and `TimerOK` are those of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). `QuietK`, `InRowsK`, `EndStatementK` and `EndRunK` are those of [The change out of the side pipe, with the sound's bytes in tables](d-3-4-2-SideChangeSound.md).

## The six bytes of the pause

`q`, `b`, `f`, `c` are the queue, the buffer, the flag and the counter of the pause sound (`PauseSoundQueue`, `PauseSoundBuffer`, `PauseModeFlag`, `Squ1_SfxLenCounter`). `t` is the pause timer (`GamePauseTimer`), `g` the pause byte (`GamePauseStatus`). `U` is the value of the unpause sound, `P` that of the pause sound, `L` the length of the sound; they are read from the ROM through symbols.

How the game uses them, on a frame of the game core:

* Start counts only when `t = 0` and bit 7 of `g` is 0. A press toggles bit 0 of `g` (paused or not), sets bit 7 of `g`, puts `P` (pause) or `U` (unpause) in `q`, and sets `t = L + 1`.
* While `t ≠ 0`, each frame takes one off `t`. When `t = 0` and Start is not pressed, bit 7 of `g` is cleared.
* On the next frame the sound routine takes `q` into `b` and `f`, and starts the sound with `c = L`, at once one less. Each frame takes one off `c`. When `c` reaches 0, `b` becomes 0; after the unpause sound `f` becomes 0 too.

So while a pause sound plays, `t = c + 1`, and Start does nothing.

## The classes

| class | `g` | `q` | `b` | `f` | `c` | `t` | number |
|---|---|---|---|---|---|---|---|
| silent | 0 or bit 7 | 0 | 0 | any | any | any | 2 |
| the unpause sound | bit 7 | 0 | `U` | `U` | `k` | `k + 1` | `k` = 1 … `L`: 42 |
| the unpause pressed | bit 7 | `U` | 0 | `P` | any | `L + 1` | 1 |
| the pause pressed (paused) | bits 0 and 7 | `P` | 0 | any | any | `L + 1` | 1 |
| the pause sound (paused) | bits 0 and 7 | 0 | `P` | `P` | `k` | `k + 1` | `k` = 1 … `L − 1`: 41 |
| the pause sound over (paused) | bits 0 and 7 | 0 | 0 | `P` | 0 | 1 | 1 |
| | bit 0, with or without bit 7 | 0 | 0 | `P` | 0 | 0 | 2 |

The bits of `g` not named are 0. `PauseE(m)` says that `m` is in one of the first three rows:

```
PauseE(m)  :=  ( m[g] ∈ {0, 0x80}  ∧  m[q] = 0  ∧  m[b] = 0 )
            ∨  ( m[g] = 0x80  ∧  m[q] = 0  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] ≤ L  ∧  m[t] = m[c] + 1 )
            ∨  ( m[g] = 0x80  ∧  m[q] = U  ∧  m[b] = 0  ∧  m[f] = P  ∧  m[t] = L + 1 )
```

At the exit the frame is not paused, so the machine is in one of the first three rows. These give `QuietK` (`quietK_of_kind`; the reference's `q` and `b` at the exit are 0).

## The statement

`During2C(m)`: `m` is covered by a start state of the pipe's frames with the six bytes of a class (as `During2`, with the pipe's timer followed). `PipeQ` has these fields; the check `pipeCheck` and the check `endCheckK` of the rows give them (`pipeQ_of_check`).

```
during    :  ∀ M,  Entry2(M) ∧ PauseE(M) → During2C(M)
toDuring2 :  ∀ m,  During2C(m) → During2(m)
step      :  ∀ m, During2C(m) → ∀ i :  During2C(frame(m, i))
               ∨  ( Exit(frame(m, i))  ∧  QuietK(frame(m, i))  ∧  ( TimerOK(frame(m, i)) → InRowsK(frame(m, i)) ) )
```

**A run.** `EndRunQ` has the fields of `EndRunK`, with `pause : PauseE(seq a)` at the entry in place of `quiet` at the exit. `b` is the first control after the entry `a` (`hc`). The theorems are those of `EndRunK`, with `PipeQ` as one more argument:

```
EndRunQ.bound  :  cnt(a) + 282 ≤ cnt(b)
EndRunQ.first  :  hc  →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
EndRunQ.inRows :  hc  →  InRowsK(seq b)
EndRunQ.start  :  hc  ∧  startCheckK  →  Start(PA, seq b)
EndRunQ.atCtl' :  hc  ∧  ctlCheckK    →  AtCtl(seq b)
EndRunQ.last   :  hc  →  a + 1 ≤ b  ∧  seq(b − 1) is in the rows  ∧  left(seq(b − 1)) = 1
```

Lean: `Theorems/SidePause.lean` (`PauseBytes`, `pauseBytesOf`, `classesP`, `PauseE`, `kindsX`, `withClass`, `pauseKeep`, `startsC`, `baseX`, `During2C`, `pipeCheck`, `class_of_pauseE`, `quietK_of_kind`, `sim_withClass`, `PipeQ`, `inRows_of_base`, `pipeQ_of_check`, `EndRunQ`, `StQ`, `st_stepQ`, `st_step_pausedQ`, `EndRunQ.bound`, `EndRunQ.way`, `EndRunQ.first`, `EndRunQ.inRows`, `EndRunQ.last`, `EndRunQ.start`, `EndRunQ.atCtl'`), private `side_pause_check` (`native_decide`, in `Proof/SidePause.lean`), `side_pause` (in `Proof/Route.lean`). There is no game data in the public file.

## How it works

**The classes as start states.** The pipe's frames of `SideChangeEnd` start from 4 states (two reference machines, two kinds of dots). Here each of them is taken with the six bytes of each class: 360 start states. The search keeps the six bytes apart. The check `duringCheck` of `SideChangeEnd` is used as it is: every frame from a start state ends in a start state, or, on the frame where the pipe's timer runs out, at the exit. The states at the exit are split by the 44 kinds of `QuietK` (`kindsX`), so the end of the walk at the exit has the bytes of a kind. A class and a kind only add known bytes to a state (`withClass(t, S) ≤ S`, checked), so `During2C` gives `During2`, and what `SideChangeEnd` and `SideChangeSound` prove of `During2` still holds.

**Why the timer is in the classes.** Without `t`, the walk lets Start count while the unpause sound plays. Then the pause comes while `b = U`, the pause sound does not start, and when the unpause sound ends `f` becomes 0 while the game is paused: the song would run during the pause. With `t = c + 1` in the class this does not happen.

**Why bit 7 of `g` is known.** A press puts `g + 1` in `q`. With bit 7 of `g` not known, the abstract machine does not know `q` after the addition. The first try had this, and the silent class did not close. Bit 7 is now known in each class; bits 1 to 6 are 0.

**Why classes and not tables.** The tables of [`StepWrites`](d-3-4-1-StepWrites.md) use the bit `spent` of the abstract state. The pipe's frames follow the pipe's timer with the same bit (`rk`). So the six bytes are known bytes of the states here.

**The size of the check.** 90 classes, 360 start states, 211,898 states in the table of the frames. The check `pipeCheck` takes about 45 s in a program. This is more than a few seconds.

## Measured, not a theorem

Program: `side-pause-real FM2 5 R`. Walks to the side pipe from 42 states in the room (on the block or on the floor, after 0 to 20 frames), 5 per state, with Start at random about once in `R` frames, then the pipe's frames with random inputs and Start about once in `R` frames. Also the reference entry and the movie's entry.

| `R` | entries | `Entry2` | `PauseE` | silent / unpause sound / unpause pressed at the entry | frames of the pipe | in a class | classes seen | exits with `QuietK` |
|---|---|---|---|---|---|---|---|---|
| 7 | 212 | 212 | 212 | 66 / 136 / 10 | 66,541 | 66,541 | 89 | 212 |
| 20 | 212 | 212 | 212 | 135 / 67 / 10 | 69,051 | 69,051 | 89 | 212 |
| 60 | 212 | 212 | 212 | 162 / 49 / 1 | 69,424 | 69,424 | 89 | 212 |

On the movie (`changes-check FM2`, and with a pause of 60 frames at 380, 416, 450, 545, 575, 730 or 845), `PauseE` held at the side pipe's entry each time. The pauses at 380 and 416 fail `quiet₁` of the first change, as before this change.

## What this does not do: Start after the pipe

`chg.noStart₂` (1-1-d-3-3) stays. Paused rows were tried and measured, with no result in Lean. A frame that pauses leads to a paused row with the same `left`, which leads to itself and to the next row. The timer must be in the tables, so the routine of the tables was made the sound routine, the reading of the pads and the pause routine together, with the timer and the pause byte as bytes of the tables. The rows up to the game core then took about 0.7 s each (0.13 s before). The search of the first paused row did not end in 10 minutes: its table is about 255 states of the song and the other effects, each with the 44 states of the pause sound and timer. After a pause the song is late, so the rows after it need songs late by any number of frames. This needs another form of the tables (the song apart from the pause) before it can work.

## Assumptions (not proved in Lean)

* `PauseE` at the entry is no longer assumed. [The pause through the room's frames](d-3-4-4-RoomPause.md) proves it from the room's first control, where bits 1 to 6 of the pause byte are 0 by a theorem (`ChangesK.pauseBits₂`, 1-1-b-3-10).
* The others are as on [The change out of the side pipe, with the sound's bytes in tables](d-3-4-2-SideChangeSound.md): `Entry2`, `lagPaused`, `NoStart` after the pipe, `TimerOK`.

**Files.** `Theorems/SidePause.lean`; the private check is in `Proof/SidePause.lean` (`genSidePause` in `Main.lean`), and `side_pause` in `Proof/Route.lean`. The name `GamePauseTimer` was added to `SideChangeEnd.namesOf`.

**To reproduce.**
```
.lake/build/bin/smbrta side-pause-check            # the check as a program, about 47 s
.lake/build/bin/smbrta side-pause-real FM2 5 20    # the classes on real runs, about 30 s (also with 7 and 60)
```
