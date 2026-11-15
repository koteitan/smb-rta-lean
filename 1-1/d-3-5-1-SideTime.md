[← Back](README.md) | [English](d-3-5-1-SideTime.md) | [Japanese](d-3-5-1-SideTime-ja.md)

# The game timer at the side pipe

**Claim.** The frames of the side pipe do not change the game timer's digits. So if the timer is not 000 at the side pipe's entry, it is not 000 at the exit. This is proved, with a check on the ROM: the walk of [The pause through the side pipe's frames](d-3-4-3-SidePause.md) carries it. So the route now asks "the timer is not 000" at the entry `seq(a₂)`, not at the exit (`chg.time₂`, item 1-1-d-3-5; this page is 1-1-d-3-5-1). This moves the hypothesis to the state where `entry₂` is asked. It does not remove it.

This page also says what was measured about removing `time₂`: the room's frames cannot give it, because the rows of the change into the room do not know the timer at the room's first control, and the room's frames lower the timer.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `seq(n)` is the machine when frame `n` begins. `a₂` is the side pipe's entry and `b₂` the first control after it (`Route.Base.a₂`, `Route.Base.b₂`). `digits` are the three bytes of `GameTimerDisplay`. `Entry2`, `Exit`, `PauseE`, `QuietK`, `InRowsK`, `During2C` are those of [The pause through the side pipe's frames](d-3-4-3-SidePause.md).

## The statement

```
TimerOK(m)    :=  ∃ i ∈ digits,  m[i] ≠ 0

PipeQ.during  :  Entry2(M) ∧ PauseE(M) ∧ TimerOK(M)  →  During2C(M)
PipeQ.step    :  During2C(m)  →  During2C(frame(m, i))  ∨  ( Exit(frame(m, i)) ∧ QuietK(frame(m, i)) ∧ InRowsK(frame(m, i)) )
EndRunQ.timeE :  TimerOK(seq a)                                         (field; it was  time : ∀ n ∈ [a, b],  Exit(seq n) → TimerOK(seq n))

chg.time₂     :  TimerOK(seq a₂)                                        (field; it was  ∀ n ∈ [a₂, b₂],  Exit(seq n) → TimerOK(seq n))
```

`During2C(m)` now includes `TimerOK(m)`: its start states have `dg`, the flag of the abstract machine that says the bytes `D` are not all 0, and `D` is `digits`. `InRowsK` at the exit needs `TimerOK` there (the rows of the time of [the last frames of the change](d-2-3-SideChangeEnd.md)); `step` now gives it with no premise.

Lean: `Theorems/SidePause.lean` (`sideEnvT`, `withT`, `startsCT`, `baseXT`, `During2C`, `pipeCheck`, `sim_withT`, `any_of_timerOK`, `timerOK_of_sim`, `sim_of_simT`, `toOne_dg`, `PipeQ`, `pipeQ_of_check`, `EndRunQ.timeE`), `Theorems/Route.lean` (`ChangesBase.time₂`, `ChangesK.run₂`), private `side_pause_check` (`Proof/SidePause.lean`). There is no game data in the public files.

## How it works

The walk of the pipe's frames in `SidePause.pipeCheck` gets the three digits as its bytes `D` (`sideEnvT`). Every start state and every state at the exit has `dg` (`withT`). In the abstract machine a store to a byte of `D` clears `dg`. A state at a frame's end must lie under a start state (or a state at the exit), and `A ≤ B` needs `dg` in `A` when `B` has it. So the check passes only if no path of the pipe's frames stores to a digit. It passes. The game timer is lowered only by `RunGameTimer`, and it leaves at once while the routine is the side pipe's (a routine number below that of the player's control). The check takes about 66 s in a program (62 s without the digits). It is the same check as before with more knowledge; no new check was added.

## On real frames

`room-music-real FM2 5 20` (the runs of [The music bytes through the room's frames](d-2-5-1-RoomMusic.md)): first controls in the room from 13 real entries into the vertical pipe, random inputs with Start at random, walks into the side pipe from 42 states near it. After each entry, the pipe's frames with random inputs (Start included) up to control.

| side pipe entries | timer not 000 at the entry | the same digits on every frame from the entry to the one before control |
|---|---|---|
| 210 | 210 | 210 |

The movie: the timer is 380 at the entry (movie frame 764), and the digits are the same on every frame up to control (movie frame 1046).

## Measured: why `time₂` does not come from the room

A program, not a theorem (`entry-bytes-check`).

* **The timer at the room's first control.** In the rows of the time of the change into the room there are 14,224 states with control. None of them knows any bit of the three digits, and none has `dg`. The rows start at the vertical pipe's exit with `dg`, but on the last frame of the change the player's routine starts and `RunGameTimer` runs: it lowers the digits (`ResGTCtrl`, `DigitsMathRoutine`), and a store to a digit clears `dg`. In all 14,224 states the timer's control byte `GameTimerCtrlTimer` has the value that `ResGTCtrl` writes, which shows this. So at the room's first control the timer may be 000 even when it was not 000 at the vertical pipe's exit (`chg.time₁`).
* **The room's frames lower the timer.** The room's walk ([The screen's page in the room](d-2-4-ScreenPage.md)) has 14 frame ends. 2 of them have the side pipe's routine, 6 the player's control, 2 the routine of losing a life (a fall into a hole), and 4 the routines of the injury or of death with `GameTimerExpiredFlag` set, which only the time-up code (`TimeUpOn`) sets. So the room's frames can lower the timer to 000 and end the room by it. A condition on single frames cannot carry a lower bound on the timer through the room. A bound needs the number of frames since frame 0, where the timer is known (`Route.Run.read₀`, the press of Start on the title).
* **When the timer is 000 at the exit.** On the frame that would give control after the exit, the entrance routine hands over to the player's routine, and `RunGameTimer` runs on the same frame (read from the code). With the digits at 000 it takes `TimeUpOn` and kills the player, so the frame ends without control. This was run on [the last frames of the change](d-2-3-SideChangeEnd.md): with the timer written to 000 at the entry, there is no control at frame 282 (the routine is the death). Such a run has a death, which the route does not cover (1-1-0-6-3). On real runs the timer falls by one every 24 frames of play, so this needs about 9,600 frames (not proved for the machine).

* **Round 14: the timer at the room's first control does not give it at the entry.** On the real machine (`side-time-low FM2`, see [the level's number from the vertical pipe to the side pipe](d-2-5-3-AreaKeep.md)): from the movie's room's first control with the timer set to 004 (control timer 15 … 24) or 005 (control timer 0 … 14), the movie's inputs enter the side pipe after 111 frames with the timer 000 (25 of 150 starts). So carrying `dg` through the room's frames cannot give `time₂`, with or without the path of the time-up.

## What changed in the route

* `chg.time₂` asks `TimerOK(seq a₂)`, at the entry. Before, it asked `TimerOK` at every state from `a₂` to `b₂` that has the bytes of the exit.
* `ChangesK.run₂` gives `EndRunQ.timeE := chg.time₂`. `SidePause.PipeQ` keeps its name; `HurryStart` and `HurryMusic` use it as before.

## Assumptions (not proved in Lean)

* `chg.time₂`: the game timer is not 000 at the side pipe's entry (1-1-d-3-5). It holds on every real run above.

**Files.** `Theorems/SidePause.lean`, `Theorems/Route.lean`; the private check is `Proof/SidePause.lean` (`genSidePause` in `Main.lean`, not changed).

**To reproduce.**
```
.lake/build/bin/smbrta side-pause-check              # the check as a program, about 66 s
.lake/build/bin/smbrta side-time-check               # the same walk built by hand in the program, about 66 s
.lake/build/bin/smbrta room-music-real FM2 5 20      # the timer at real entries and through the pipe, about 2 min 20 s
.lake/build/bin/smbrta entry-bytes-check             # the timer at the room's first control and the room's frame ends, about 51 s
```
