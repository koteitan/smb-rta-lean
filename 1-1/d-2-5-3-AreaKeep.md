[← Back](README.md) | [English](d-2-5-3-AreaKeep.md) | [Japanese](d-2-5-3-AreaKeep-ja.md)

# The level's number from the vertical pipe to the side pipe

**Claim.** If the level's number (`AreaNumber`) at the vertical pipe's entry has the value of the reference entry, it has this value at the side pipe's entry. This is proved, with three walks on the ROM. So `Route.Run` asks 9 bytes at the side pipe's entry, not 10 (`chg.entry₂`, 1-1-d-2-5), and one new byte at the vertical pipe's entry (`area₁`). The hypothesis moves from the side pipe's entry to the vertical pipe's entry. It is not removed.

This page also says what was measured for the two other candidates of this round: the added note length (`NoteLengthTblAdder`) and the game timer at the side pipe's entry (`chg.time₂`). Neither goes through the room's frames.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `trₙ(j)` the machine `j` instructions into frame `n`. `seq(n)` is the machine when frame `n` begins. `a₁`, `b₁`, `a₂` are the vertical pipe's entry, the room's first control and the side pipe's entry (`Route.Base`). `i` is the index of the level's number, `e` the reference entry of the vertical pipe and `v := e[i]`. `S[i ↦ v]` is the abstract state `S` that also knows `i` with the value `v`. `rt(m)` is the routine byte and `r` the reference machine of the room.

## The statement

`startsP` and `baseK` are the start states of the walk of the vertical pipe's frames and the states at its exit ([the change into the room](b-3-2-PipeChangeEnd.md)). `rowsKc` are the rows with tables from the exit to the room's first control ([the sound's bytes in tables](b-3-7-1-SoundRows.md)). `DuringV`, `InRowsK`, `QuietP`, `SongAt`, `TimerOK` are part b's.

```
startsA  :=  { S[i ↦ v] : S ∈ startsP }           baseA  :=  { S[i ↦ v] : S ∈ baseK }
DuringA(m)  :=  m is covered by the walk of the pipe's frames from startsA
InRowsA(m)  :=  m is in the rows with tables from baseA

PipeRunK.areaB :  part b's run of the change from a to b,  b the first control after a,  seq(a)[i] = v   →   seq(b)[i] = v
area_run       :  Room(seq c),  seq(c)[i] = v,
                  ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),     rt(seq e) ≠ rt(r)
                  →  seq(e)[i] = v

Run.area₁       :  seq(a₁)[i] = v                                         (a theorem since round 15, 1-1-b-3-4-5; a field in round 14)
Run.area₂       :  seq(a₂)[i] = v                                         (theorem)
entryAt_of_area :  m[i] = v  ∧  EntryAt(R₉, m)  →  EntryAt(R₁₀, m)
chg.entry₂      :  EntryAt(R₉, seq a₂)                                    (9 bytes; it was R₁₀)
```

`R₁₀` is the 10 bytes of `restIdxR` and `R₉ := R₁₀ \ {i}` (`restIdxA`). `EntryAt` is that of [the routine at the side pipe's entry](d-2-5-2-EntryRoutine.md).

**`PipeRunK.areaB`** is an induction over the frames of the change, with the invariant, for `n = a + k ≤ b`:

```
( DuringV(seq n) ∧ DuringA(seq n) )  ∨  ( InRowsK(seq n) ∧ InRowsA(seq n) )
```

Part b's walks give the left half of each side (`EndStatement.pauseStep`, `rowsK`, `zeroK`), the walks with the byte the right half. In the pipe both walks must agree on whether the frame leaves the pipe: a state of `DuringA` is in the pipe's routine (the check `pipeOK` of its start states), and a machine at the exit is not (the exit's task is not the game core). At the exit `QuietP`, `SongAt` and `TimerOK` come from part b's run, and they put the machine into the first row from `baseA` (`rowsA_of_exit`, as `PipeChangeEnd.inRowsK_of_exit`). In the rows `left` is not 0 before `b`, since part b's rows have control where `left` is 0 and `b` is the first control. At `b` the machine is in the rows from `baseA`, and every state of every row knows the byte with the value `v` (`knowsRows`).

**`area_run`** is `RoomPause.pause_run` with a table of one state: `[(i, v)]`. In the region of the sound routine the walk knows the byte from the table; outside, a step that may write it fails.

**`Run.area₂`.** `area₁`, part b's run of the first change (`ChangesK.run₁`), `PipeRunK.areaB` give the byte at `b₁`; `area_run` from `b₁` to `a₂` (the room's condition at `b₁`, `roomSites`, `roomStay`, and `Run.rt₂` for the other routine at `a₂`) gives it at `a₂`.

Lean: `Theorems/AreaKeep.lean` (`areaI`, `setA`, `startsA`, `baseA`, `cfgRa`, `cfgOa`, `pipeCheckA`, `startsKA`, `rowsA`, `InRowsA`, `knowsRows`, `rowsCheckA`, `regA`, `cfgA`, `roomCheckA`, `smallCheck`, `zok_of_check`, `sim_setA`, `duringA_of_entry`, `inPipe_of_A`, `not_inPipe_of_exit`, `rowsA_of_exit`, `rowsA_step`, `area_of_rowsA`, `PipeRunK.areaB`, `roomOK_of_check`, `area_run`, `Facts`, `factsOf`, `small_parts`), `Theorems/Route.lean` (`restIdxA`, `RoomChecks.area`, `Run.area₁`, `Run.area₂`, `entryAt_of_area`, `Run.chgK`), private `Proof/AreaKeep.lean` (`area_pipe`, `area_rows`, `area_room`, `area_small`, `area_factsA`) and `Proof/AreaJoin.lean` (`area_facts`). There is no game data in the public files.

## The checks

| check | what it walks | time (native) |
|---|---|---|
| `pipeCheckA` | the vertical pipe's frames from `startsA` (the walk `zcheck` of part b), ending in `baseA` | 15–18 s |
| `rowsCheckA` | the rows with tables from `baseA`: 44 rows, 1,906 states; `chainS`, and every state knows the byte | 120–136 s |
| `roomCheckA` | the room's frames with the byte in a table of one state | 2.3–2.5 s |
| `smallCheck` | the byte is a byte of the 11 and not the routine's, the exit's task is not the game core, each reference of the side pipe's entry has `v` | — |

The rows check takes about 2 minutes: it is the frame-by-frame check of part b's rows (`soundCheck`, about 200 s on the same 44 rows and 1,906 states) for the rows with the byte. So that it does not wait for part b's long check, `Proof/AreaKeep.lean` takes copies of the names and of the data of the change from the files that `gen-proofs` wrote and imports only `Proof.Rom`; `Proof/AreaJoin.lean` states the facts for the route's names and data, which are the same terms (`rfl`, 0.2 s).

## Measured: where the two bytes are known

A program, not a theorem (`area-links-check`). The level's number and the added note length are 0 in the vertical pipe's reference entry, at the exit and in the room's reference.

| link | the level's number | the added note length |
|---|---|---|
| the vertical pipe's entry (`Entry`, `Rest`), its exit, the room's condition | not known | not known (a byte of the sound's table of the rows, not known at its start) |
| frame 0 (`TitleStart`'s near states, `EntryKeep.nearCheck`) | not known | known: 0 |
| the frames from control to the vertical pipe's entry (`EntryKeep.keepCheck` with the byte kept, and protected by the guard) | kept: 0 walks fail of 53,438 | 4 walks fail |
| the vertical pipe's frames (`zcheck` with the byte at the start and asked at the exit) | kept | kept |
| the rows of the time from the exit (a copy of the start with the byte) | known at control | known at control |
| the room's frames | kept (`roomCheckA`) | not kept: the hurry-up music sets it to 8 (round 12: 2 of the 6 states of the table with the reference's area music have 8) |

So the level's number fails only at frame 0, and the frames before the vertical pipe's entry would need it in the guard of `upClean₁` (part b). The added note length fails twice, and both times on the timer: the code of the event music (`LoadEventMusic`) sets it to 8 for the hurry-up music, and the walks do not know the game timer, so they do not know whether the hurry-up music is queued.

## Measured: the game timer at the side pipe's entry (`time₂`)

A program, not a theorem (`side-time-low FM2`, about 5 s). It runs the movie to the room's first control (after movie frame 653; the timer shows 384 and its control timer is 24). There it sets the timer to `0 0 v` and the control timer to `c`, for `v` = 1 … 6 and `c` = 0 … 24, and plays the movie's inputs to the frame that leaves the player's routine.

| timer at the room's first control | result |
|---|---|
| 001, 002, 003, and 004 with `c` ≤ 14 | the time-up: the death routine after 25 to 110 frames, with the timer 000 (90 starts) |
| 004 with `c` = 15 … 24, and 005 with `c` = 0 … 14 | the side pipe's entry after 111 frames, **with the timer 000** (25 of the 150 starts) |
| 005 with `c` ≥ 15, and 006 | the side pipe's entry with the timer 001 or 002 |

So `TimerOK(seq b₁)` does not give `TimerOK(seq a₂)`: the room's frames lower the timer, and the entry can come in the 24 frames between the timer's 000 and the time-up. No condition on single frames of the room can carry the timer, because the room may last any number of frames. The timer at `a₂` needs the number of frames since frame 0, where the timer is known (`Route.Run.read₀`). The walks would have to follow the timer as a number (`24 · T + C` falls by at most 1 on a frame that ends not paused), which the abstract machine does not do: a step of `DigitsMathRoutine` stores every digit, and a store to a digit clears `dg`.

## On real frames

`area-real FM2 N R` (a program): on the movie, at every frame up to the byte's first change after the side pipe, and at the two entries and the room's first control; from the real entries into the vertical pipe of `PipeTransitionAll.realEntries`, `N` runs each with Start at random on the pipe's frames (one frame in `R`), at the room's first control, and then with the movie's inputs from its first control in the room to the side pipe's entry.

| run | vertical pipe's entries | room's first controls | side pipe's entries | the byte not 0 |
|---|---|---|---|---|
| the movie | 1 (frame 562) | 1 (frame 653) | 1 (frame 764) | none: 0 on every frame from power-on to frame 1941; it changes at frame 1942, the change to 1-2 |
| `area-real FM2 10 7` | 13 real entries (`PipeTransitionAll.realEntries`) | 130 (10 runs each, Start at random on the pipe's frames) | 130 (the movie's inputs from its first control in the room) | none |

## What changed in the route

* `Run.chg : ChangesK … (restIdxA sy nmS m0)`: 9 bytes at the side pipe's entry (it was `restIdxR`, 10 bytes). `Run.chgK` gives the changes with the 11 bytes from `Run.area₂` and `Run.rt₂`, as before for `Run.change₂`, `Run.start`, `Run.atCtl₀`.
* `Run` had a new field `area₁` in round 14. Since round 15 it is the theorem `Run.area₁`: the condition at the vertical pipe's entry lists the byte (1-1-b-3-4-5).
* `RoomChecks` has a new field `area : AreaKeep.Facts …`. It is built in the private files of the route (5 times) and of the hurry-up music (once), from `area_facts`.

Removed from the assumptions: the level's number of `entry₂`. Added in round 14: `area₁`, the level's number at the vertical pipe's entry; removed in round 15.

## Assumptions (not proved in Lean)

* `area₁` is no longer assumed (round 15): the press of Start on the title now asks the byte (`title.boot`), the guard of `upCleanU` protects it, and `EntryKeep`'s walk keeps it up to the entry. So these two assumptions each ask one more byte.
* `chg.entry₂`: 9 bytes at the side pipe's entry: the player's height, the screen's buffer (5 bytes), the area music's buffer, the event music's queue, the added note length. Since round 15 the height and the five bytes of the screen's buffer come from the entering frame, when it starts with a small player and with the control of the screen's buffers at 0 ([1-1-d-2-5-4](d-2-5-4-EntryHeight.md), [1-1-d-2-5-5](d-2-5-5-EntryBuffer.md)): `chg.entry₂` asks 3 bytes, and `Run` has the two fields `height₂`, `buffer₂` for the other runs.
* `chg.time₂`: the game timer is not 000 at the side pipe's entry.

**Files.** `Theorems/AreaKeep.lean`, `Theorems/Route.lean`; the private checks are `Proof/AreaKeep.lean` and `Proof/AreaJoin.lean` (`genAreaKeep` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta area-keep-check                 # the four checks, about 3 min 30 s
.lake/build/bin/smbrta area-links-check all            # the table above (both bytes), about 4 min
.lake/build/bin/smbrta side-time-low FM2               # the timer set low at the room's first control, about 5 s
.lake/build/bin/smbrta area-real FM2 10 7              # the byte on real runs, about 20 s
```
