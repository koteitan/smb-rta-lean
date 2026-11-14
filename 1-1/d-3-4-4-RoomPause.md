[← Back](README.md) | [English](d-3-4-4-RoomPause.md) | [Japanese](d-3-4-4-RoomPause-ja.md)

# The pause through the room's frames

**Claim.** Suppose that at the room's first control bits 1 to 6 of the pause byte are 0. Then at the side pipe's entry the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed on that frame (`PauseE`). This holds for any input in the room, Start included. It is proved, with two checks on the ROM. So the route no longer assumes `PauseE` at the entry: `chg.pause₂` is gone, and `chg.pauseBits₂` (the 6 bits at the room's first control) is new (1-1-d-3-4-4). On real runs with Start at random, the 6 bits were 0 at all 195 first controls, the six bytes of the pause were in a class at the start of all 203,345 frames in the room, and `PauseE` held at all 630 entries.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `tr(j)` the machine `j` instructions into it. `seq(n)` is the machine when frame `n` begins. `rt(m)` is the routine byte (`GameEngineSubroutine`), and `r` the reference machine of the room. `Room` and `SiteOK` are those of [The screen's page in the room, and the long timer of the side pipe](d-2-4-ScreenPage.md). `InRowsT` is the rows of the time of [the change into the room, with the sound's bytes in tables](b-3-7-1-SoundRows.md). The six bytes of the pause, the 90 classes and `PauseE` are those of [The pause through the side pipe's frames](d-3-4-3-SidePause.md): `q`, `b`, `f`, `c` the queue, the buffer, the flag and the counter of the pause sound, `t` the pause timer, `g` the pause byte.

```
InCls(m)  :=  ∃ t ∈ classes,  the six bytes of m are as t says
```

## The statement

```
pause_step      :  Room(m) ∧ (∀ j, SiteOK(tr(j))) ∧ InCls(m)
                     →  InCls(frame(m, i))  ∧  ( Room(frame(m, i))  ∨  ( rt(frame(m, i)) ≠ rt(r)  ∧  g(frame(m, i)) & 1 = 0 ) )
pause_run       :  Room(seq c) ∧ InCls(seq c),   ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),   rt(seq e) ≠ rt(r)
                     →  InCls(seq e)  ∧  g(seq e) & 1 = 0
class_of_rows   :  InRowsT(m) ∧ ctl(m) ∧ g(m) & 0x7E = 0  →  InCls(m)
pauseE_of_class :  t ∈ classes,  the six bytes of m as t says,  g(m) & 1 = 0  →  PauseE(m)
pauseE_run      :  all of these from c = b₁ to e = a₂  →  PauseE(seq a₂)
```

`pause_step` and `pause_run` follow from the check `roomCheck` (`PauseOK`), `class_of_rows` from the check `startCheck`. `pauseE_of_class` needs no check: the classes with `g & 1 = 0` are the three kinds of `PauseE`.

In the route (`Route.ChangesK.pause₂`):

```
pauseBits₂ : g(seq b₁) & 0x7E = 0                    (the theorem ChangesK.pauseBits₂, 1-1-b-3-10)
Room(seq b₁)                                            (ChangesK.roomAt, as before)
InRowsT(seq b₁), ctl(seq b₁)                            (the rows of the first change, as before)
∀ n ∈ [b₁, a₂):  ∀ j, SiteOK(trₙ(j))                    (chg.roomSites, as before)
∀ n ∈ [b₁, a₂):  rt(seq n) = rt(r)                       (ChangesK.roomStay: the definition of a₂)
rt(seq a₂) = e_s ≠ rt(r)                                 (ChangesK.rt₂: chg.entry₂ and the check RoomChecks.rt)
ChangesK.pause₂ : PauseE(seq a₂)                        (theorem; it was the field pause₂)
```

Lean: `Theorems/RoomPause.lean` (`Reg`, `keep0`, `baseS`, `eraseKeeps`, `keepP`, `inP`, `pstep`, `Ph`, `finP`, `walkP`, `walkCheck`, `regOf`, `cfgR`, `roomCheck`, `rowP`, `startCheck`, `mem_low`, `low_of_mem`, `sim_keep0`, `s_baseS`, `keepP_ok`, `s_pstep`, `LiveP`, `cover_liveP`, `live_stepP`, `frame_of_walkP`, `InCls`, `PauseOK`, `pauseOK_of_check`, `pause_step`, `pause_run`, `pauseE_of_class`, `class_of_silent`, `class_of_rows`, `Facts`, `factsOf`, `pauseE_run`), `Theorems/Route.lean` (`ChangesK.pauseBits₂`, `RoomChecks.pause`, `ChangesK.rt₂`, `ChangesK.pause₂`), private `room_pause_walk`, `room_pause_start`, `room_pause` (in `Proof/RoomPause.lean`). There is no game data in the public files.

## How it works

**Where the six bytes are written.** Only the sound routine (the pause sound, and the counter by the first square's effects) and the pause routine write them. The handler calls the sound routine, the reading of the pads and the pause routine one after another. These three calls are the region of the walk: from the call of the sound routine to the place after the third call. The places come from the ROM: the first call of `SoundEngine` from `NonMaskableInterrupt`, and 9 bytes after it.

**One frame.** The walk is the walk of one frame in the room of [The screen's page](d-2-4-ScreenPage.md), with a table carried outside the abstract state: the 90 classes (`pstep`).

* Outside the region every step must keep the six bytes (`keepP`): the step's abstract state says that its store does not reach them (`StepWrites.keepOK`), or it is the erase of a coin, which `SiteOK` puts into the block buffers, and the six bytes are not there (checked).
* At the call of the sound routine the state is split into one piece for each class that agrees with it. The pieces are marked (`spent`: in the region).
* In the region every step is the step of the room's walk, with the six bytes known in each piece.
* At the place after the region the six bytes must be in a class. Then they are forgotten, but for bit 0 of the pause byte (`keep0`: paused or not), and the mark is taken off.

`Ph(A, m) := spent(A) ∨ InCls(m)`. Each step follows the machine and keeps `Ph` (`s_pstep`). At the frame's end the walk asks that the state is out of the region, and that it is under a start state of `Room`, or that the routine is known and is not the reference's and bit 0 of the pause byte is known to be 0 (`finP`).

**Why bit 0 of the pause byte is kept.** The frame that enters the side pipe has run the game's routine, so it was not paused. The walk knows this only if the bit is known after the region. Then at the entry the class is one of the three that are not paused, and these are `PauseE`.

**The first control.** The rows of the first change know at control: the queue, the buffer and the flag of the pause sound are 0, and bit 0 of the pause byte is 0. They do not know the timer, nor bits 1 to 7 of the pause byte (2 kinds of states, 14,224 states with control). With bits 1 to 6 of the pause byte 0, the pause byte is 0 or `0x80`, and the machine is in one of the two silent classes (`class_of_silent`).

**The search.** It is a program that makes the table; the check does not depend on it. It is the search of the room's walk with three changes. The six bytes are bytes of the key, so the pieces of different classes are not joined. The waiting states are ordered by the whole key: the search of [The screen's page](d-2-4-ScreenPage.md) uses the key modulo 2^200, and with the six bytes the place and the registers lie above bit 200, so the waiting states of different places took each other's place, and some were never walked (the walk of the table then grew without end). A `Nat` is hashed by its low 64 bits, so all the bits of the key are mixed into them (`keyP`); without this the search took 57 s.

**The size of the check.** 90 classes. The search has 529,736 steps, 25,753 forks, 0 failures and a table of 25,264 states; in a program the search takes about 3.7 s and the whole check `roomCheck` about 6.5 s. `startCheck` makes the rows of the time again and takes about 24 s in a program. Both are more than a few seconds.

## Measured, not a theorem

Program: `room-pause-real FM2 5 R`. The first controls in the room: 13 real entries into the vertical pipe, 5 runs each (the first with no input, the others with Start at random on the pipe's frames, once in `R` frames), then no input up to control. From each first control 600 frames of random inputs with Start at random. Also 42 states near the side pipe (on the block or on the floor), 5 walks each into the pipe with Start at random. Also the movie's room.

| `R` | first controls | 6 bits 0 | in a class | frame starts in the room | paused | in a class | classes seen | entries | `PauseE` | bit 0 of `g` is 0 |
|---|---|---|---|---|---|---|---|---|---|---|
| 7 | 65 | 65 | 65 | 70,253 | 38,366 | 70,253 | 89 | 210 | 210 | 210 |
| 20 | 65 | 65 | 65 | 67,505 | 34,707 | 67,505 | 89 | 210 | 210 | 210 |
| 60 | 65 | 65 | 65 | 65,587 | 32,474 | 65,587 | 89 | 210 | 210 | 210 |

The pause byte at the first controls was 0 or `0x80`. On the movie the 6 bits are 0 at the room's first control, every frame of the room is in a class, and `PauseE` holds at the entry (movie frame 764).

## What changed in the route

* `chg.pause₂` is gone: `ChangesK.pause₂` is a theorem with the same statement, and `ChangesK.run₂` uses it.
* `chg.pauseBits₂` is new: `g(seq b₁) & 0x7E = 0`.
* `RoomChecks` has a new field `pause : RoomPause.Facts` (the two checks). `RoomChecks` is built in the private files of the route and of the hurry-up music.

## Assumptions (not proved in Lean)

* Bits 1 to 6 of the pause byte at the room's first control are no longer assumed. In round 11 the first change's exit states keep bits 0–6, and the field became the theorem `ChangesK.pauseBits₂` ([The pause byte at the room's first control](b-3-10-PauseBits.md), 1-1-b-3-10).
* `SiteOK` on each instruction in the room (`chg.roomSites`) and the conditions of the first change's rows (part b), as before.

**Round 11.** The region `Reg` has two more fields with defaults, used by [the music bytes through the room's frames](d-2-5-1-RoomMusic.md): `keepB` (bits of the table's bytes kept after the forgetting, because the room's condition knows them) and `needG` (a frame that leaves the room must end with bit 0 of the pause byte known to be 0). A step outside the region may also write the table's bytes if every state of the table, so written, is in a state of the table (`StepWrites.writeOK`). With the defaults the pause's check is the same; it still passes.

**Files.** `Theorems/RoomPause.lean`; the private checks are in `Proof/RoomPause.lean` (`genRoomMusic` in `Main.lean`, which also writes the checks of the music; `startCheck` comes from `RoomMusic.startBoth`, which makes the rows of the time once for both).

**To reproduce.**
```
.lake/build/bin/smbrta room-pause-check -r                # the walk's check, the six bytes at control in the rows, and startCheck, about 35 s
.lake/build/bin/smbrta room-pause-real FM2 5 20           # the classes on real runs, about 22 s (also with 7 and 60)
.lake/build/bin/smbrta room-pause-walks 20000             # the walk of each state of the table with a budget of steps
```
