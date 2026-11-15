[← Back](README.md) | [English](b-3-9-1-PipeTime.md) | [Japanese](b-3-9-1-PipeTime-ja.md)

# The game timer at the vertical pipe

**Claim.** The frames of the vertical pipe do not change the game timer's digits. So if the timer is not 000 at the vertical pipe's entry, it is not 000 at the exit. This is proved, with a check on the ROM: the walk of [the pause through the vertical pipe's frames](b-3-7-2-PipePause.md) carries it. So the route now asks "the timer is not 000" at the entry `seq(a₁)`, not at the exit (`chg.time₁`, item 1-1-b-3-9; this page is 1-1-b-3-9-1). This moves the hypothesis to the state where `entryRest₁` is asked. It does not remove it. The same was done for the side pipe in round 12 ([the game timer at the side pipe](d-3-5-1-SideTime.md)).

This page also says what was measured about removing `time₁`: the frames from control to the entry cannot give it by a condition on single frames, because a run in control can reach the entry with the timer at 000. Round 14 measured whether the saved song in `Rest` gives it: an invariant that links the timer to the saved song holds on every measured frame, but the walk of the frames from control cannot carry it under `upClean₁` (the section "Measured in round 14").

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `trace(m, i, j)` is the machine after `j` steps of that frame. `seq(n)` is the machine when frame `n` begins. `a₁` is the vertical pipe's entry and `b₁` the first control after it (`Route.Base.a₁`, `Route.Base.b₁`). `digits` are the three bytes of `GameTimerDisplay`. `During`, `ExitAt`, `Places`, `classesV`, `SIn`, `QuietV`, `QuietP`, `SongAt`, `shape` and `InRowsK` are those of [the pause through the vertical pipe's frames](b-3-7-2-PipePause.md) and [the change into the room, with the sound's bytes in tables](b-3-7-1-SoundRows.md).

## The statement

```
TimerOK(m)  :=  ∃ i ∈ digits,  m[i] ≠ 0
DuringV(m)  :=  During(m)  ∧  ( ∃ t ∈ classesV,  SIn(t, m) )  ∧  TimerOK(m)

pauseStep   :  ∀ m, DuringV(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                 DuringV(frame(m, i))
               ∨ ( ExitAt(frame(m, i))  ∧  QuietV(frame(m, i))  ∧  TimerOK(frame(m, i))  ∧
                   ( QuietP ∧ SongAt(shape) at frame(m, i)  →  InRowsK(frame(m, i)) ) )

PipeRunK.time :  TimerOK(seq a)                         (field; it was  ∀ n ∈ [a, b],  ExitAt(seq n) → TimerOK(seq n))
chg.time₁     :  TimerOK(seq a₁)                        (field; it was  ∀ n ∈ [a₁, b₁],  ExitAt(seq n) → TimerOK(seq n))
```

Before, `DuringV` did not have `TimerOK`, and `pauseStep` asked `TimerOK` at the exit as a premise of `InRowsK`. Now `pauseStep` gives `TimerOK` at the exit with no premise. `PipeRunK.atEntry` gives `DuringV(seq a)` from `Entry`, `PauseV` and `TimerOK` at the entry. `PipeRunK.bound`, `PipeRunK.first`, `PipeRunK.inRowsT` and `PipeRunK.pauseBits` are as before, with the same arguments.

Lean: `Theorems/PipeChangeEnd.lean` (`withT`, `startsPT`, `baseKT`, `cfgRqT`, `cfgOqT`, `dgOff`, `pipeCheckV`, `DuringV`, `EndStatement.pauseStep`, `timerOK_of_simT`, `sim_of_simT`, `simT_of_sim`, `toOne_withT`, `invT_of`, `of_invT`, `PipeRunK.time`, `PipeRunK.stepD`, `PipeRunK.atEntry`), `Theorems/Route.lean` (`ChangesK.time₁`), `Theorems/HurryStart.lean` (`Chg₁.time₁`). The private check is still `pipe_end_checks` in `Proof/PipeChangeEnd.lean`. There is no game data in the public files.

## How it works

The walk of the pipe's frames with the pause's class beside it (`pcheck`, [b-3-7-2](b-3-7-2-PipePause.md)) now runs in the environment `timeEnv`: its bytes `D` are the three digits. Every start state and every state at the exit has `dg` (`startsPT`, `baseKT`). In the abstract machine a store to a byte of `D` clears `dg`. A state at a frame's end must lie under a start state (or a state at the exit), and `A ≤ B` needs `dg` in `A` when `B` has it. So the check passes only if no path of the pipe's frames stores to a digit. It passes. The game timer is lowered only by `RunGameTimer`, and it leaves at once while the routine is the vertical pipe's (a routine number below that of the player's control).

Two small lemmas join the two walks of the pipe's frames. The old walk (`zcheck`, no digits) still gives `left` and the paused frames (`EndStatement.step`, `EndStatement.paused`); `HurryStart` uses it as before.

```
invT_of  :  During(m) ∧ TimerOK(m)  →  m is covered by a start state of the walk with dg          (no ROM)
of_invT  :  m is covered by a start state of the walk with dg  →  During(m) ∧ TimerOK(m)           (the start states have no dg before withT: dgOff)
```

**The size.** The tables are 58,850 and 43,229 states, the same as without the digits. In a program the search takes 7.4 s and 4.2 s, and the check 10.5 s (`pipe-time-check`). The private build of `Proof/PipeChangeEnd.lean` took 226 s (232 s before). No new check was added: it is the same check with more knowledge.

## On real frames

`pipe-time-real FM2 3 7 0 0`: the 334 entries of `pipe-pause-real` (the reference, the movie's, real entries standing on the pipe, entries on the reference's way with a pause, entries after standing with Start at random). From each, the pipe's frames with random inputs and Start about once in 3, 9 and 40 frames.

| entries | timer not 000 at the entry | frames of the pipe | the digits of the entry | exits | the digits of the entry at the exit | timer not 000 at the exit |
|---|---|---|---|---|---|---|
| 334 | 334 (the least is 368) | 88,769 | 88,769 | 1,002 | 1,002 | 1,002 |

## Measured: why `time₁` does not come from the frames from control

A program, not a theorem (`pipe-time-real FM2 0 7 9160 9186`).

* **The walk from control cannot keep `dg`.** On the frames in control `RunGameTimer` lowers the digits (`DigitsMathRoutine`), so a store to a digit clears `dg`. The walk of [the state at the entry](b-3-4-EntryKeep.md) knows none of the digits.
* **A frame that makes the timer 000 does not go to the time-up.** It sets the timer's control byte to 24 (`ResGTCtrl`). The time-up (`TimeUpOn`) comes only on a later frame where that byte is 0. Standing still from `m0`, the digits are 000 after frame 9,600, with control, and control ends after frame 9,624 (the routine of death). So for 24 frames the player has control with the timer at 000.
* **Such a run enters the pipe with 000.** Standing `k` frames from `m0` and then the reference's way, for `k` from 9,160 to 9,185: 12 runs enter the pipe with the timer 000 (after frames 9,602 to 9,624). On all 12 every frame before the entry has control and the kept bytes of [b-3-4](b-3-4-EntryKeep.md), and `PauseV` holds at the entry. So a condition on single frames from control does not give `TimerOK` at the entry. After the entry there is no control within 100 frames; at frame 91 the routine is the death's.
* **These runs fail `Entry` at one byte.** On all 12 the only byte of `Entry` that differs from the reference is the saved song (`AreaMusicBuffer_Alt`), which is in `Rest` (`entryRest₁`): the hurry-up music changed it at timer 100. So the route's hypotheses already exclude these runs, but through an assumed byte. To prove `TimerOK` at the entry, a walk would have to link the timer's value to the saved song, or count the frames since frame 0 (the timer is 400 there, `Route.Run.read₀`). Neither is done.

## Measured in round 14: the saved song and the timer

Programs, not theorems (`timer-song`, `timer-store-y`, and `entry-writers` of round 12, run again). `time₁` is not removed.

`h` is the hundreds digit of the timer, and `H(m) := m[h] ≠ 0`: the timer is at least 100. `S` is the saved song (`AreaMusicBuffer_Alt`), `A` the area music's buffer, `Q` the event music's queue, and `hurry` the value of the hurry-up music. At the reference entry `e` no event music is queued and no song is saved: `e[Q] = 0` and `e[S] = 0`. `A` holds the area's song there.

```
I0(m)  :=  m[S] = e[S]  →  H(m)
I1(m)  :=  H(m)  ∨  m[S] ≠ e[S]  ∨  m[Q] = hurry
```

* **The game.** When `RunGameTimer` lowers the timer from 100, it first puts the hurry-up music in `Q`. The sound routine of the next frame loads it, and `NoStopSfx` then copies `A` into `S`. This is the only store to `S`. So `S` changes one frame after the timer goes below 100.
* **`I0` is false on real runs.** It fails on the frame right after each crossing of 100: the hurry-up music is in `Q`, and `S` has not changed yet. With "above 100" in place of `H` it also fails at the 24 frames with the timer at 100.
* **`I1` holds on every measured frame.** 65 runs: from control, `k` frames of A, B, up, down and a rare pause (inputs that keep the player's place), then the reference's way, for `k` from 7,150 to 9,131. They have 594,878 frames in control (68,714 paused); 90,704 of them start below 100.

| frame starts against `I0` | with the timer at 100 and `e[S]` | against `I1` | crossings of 100 | with `hurry` in `Q` at the end | with `A ≠ 0` at the end | loads of `hurry` | with `S ≠ e[S]` after |
|---|---|---|---|---|---|---|---|
| 47 | 1,128 | 0 | 47 | 47 | 47 | 47 | 47 |

* **At the entries.** 27 of the 65 runs enter the pipe: 18 below 100, 6 of them with 000. None of the 18 has `Rest`, and none is against `I1`. The other runs die on the way, or their inputs end first.
* **`I1` would give `time₁`.** `Rest` at the entry asks `S = e[S]` and `Q = e[Q] = 0`, and `0 ≠ hurry`. So `I1(seq a₁) ∧ Rest(seq a₁) → H(seq a₁) → TimerOK(seq a₁)`.
* **The walk of [b-3-4](b-3-4-EntryKeep.md) cannot carry `I1`.** After a store with a target not known it keeps only the bytes of the guard of `upClean₁` (`EntryKeep.guardOf`), and its search keeps only these bytes at each state of the table. The three digits, `S`, `A`, `Q`, the event music's buffer, the area music's queue and the timer's control byte are not among them. None of the 53,438 states of the table knows a bit of them. This is not a choice of the search: under `upClean₁` a store through an index or a pointer may write any byte outside the guard, and the walk has 710 places of such a store with a target not known.
* **The guard cannot simply protect the digits.** Real frames store each digit through `Y` at one place of `DigitsMathRoutine` (21,881 times for each digit in the 594,878 frames). With the digits protected, `Clean` would be false there on every 24th frame. No store through an index or a pointer wrote `S`, `A` or `Q` on these frames.
* **The walk's addition needs every bit.** `TaintRun.aadc` gives a result only when every bit is known. So the walk cannot keep `H` by known bits through the timer's decrement. Where `RunGameTimer` decides, the three digits would have to be split into exact values: at most 16³ = 4,096 states for each state there. The table has 62 states in the first 96 bytes of `RunGameTimer`, at 14 places.

What a later round would need (not done):

* the condition on the instructions from control to the entry (part a makes one union condition in this round) protects the three digits, with an exception for that one store of `DigitsMathRoutine` (as `CleanK` leaves out the move routine's store), and protects `S`, `A` and `Q`;
* at that store the walk knows `Y`. Now the search knows it with 3 values (the timer's and two scores'). On 230 visits it does not, from 5 calls; one of them is the timer's own call, where `Y` is known before the loop: the search joins the loop's states, because `Y` is not in its key;
* a walk that splits the digits where `RunGameTimer` decides and afterwards keeps only `H` and the high bits of the digits, with the music bytes beside it. With each of the five music bytes protected and kept alone, the walk changes it at 1 to 4 places and fails at 4 or 5 ends of a frame (`entry-writers`, run again in round 14): `S` only at `NoStopSfx`, `Q` at 4 places, one of them the hurry-up store in `RunGameTimer`.

The invariant to carry would be `I1`, with `A ≠ 0` while `H` holds, so that the load of `hurry` writes a song that is not 0 into `S`. Then `time₁` would follow from `Rest`.

## What changed in the route

* `chg.time₁` asks `TimerOK(seq a₁)`, at the entry. Before, it asked `TimerOK` at every state from `a₁` to `b₁` that has the bytes of the exit.
* `ChangesK.run₁` gives `PipeRunK.time := chg.time₁`. `HurryStart.Chg₁.time₁` changed the same way.

## Assumptions (not proved in Lean)

* `chg.time₁`: the game timer is not 000 at the vertical pipe's entry (1-1-b-3-9). It holds on every real run above. Round 14: it would follow from `Rest` and the invariant `I1`, which holds on all 594,878 measured frames; carrying `I1` needs the digits and three music bytes protected by the condition on the instructions (not done).

**Files.** `Theorems/PipeChangeEnd.lean`, `Theorems/Route.lean`, `Theorems/HurryStart.lean`; the private check is `Proof/PipeChangeEnd.lean` (not changed).

**To reproduce.**
```
.lake/build/bin/smbrta pipe-time-check                          # the walk with the digits as a program, about 65 s with the tables of the places
.lake/build/bin/smbrta pipe-time-real FM2 3 7 0 0               # the timer at 334 real entries and through the pipe, about 1 min 30 s
.lake/build/bin/smbrta pipe-time-real FM2 0 7 9160 9186         # standing to the timer 000 and then the reference's way, a few minutes
.lake/build/bin/smbrta timer-song 0 1 1 table                    # the bytes, the guard, the table, the reference's way, about 25 s
.lake/build/bin/smbrta timer-song 9095 9113 1                    # I0 and I1 on 18 runs that enter near the timer 000, about 2 min (also 9113 9131 1, 9000 9095 5, 7150 7350 20)
.lake/build/bin/smbrta timer-store-y                             # Y at the store of the digits in the search, about 25 s
.lake/build/bin/smbrta entry-writers AreaMusicBuffer_Alt AreaMusicBuffer EventMusicQueue EventMusicBuffer AreaMusicQueue   # about 40 s
```
