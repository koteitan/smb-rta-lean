[← Back](../README.md) | [English](README.md) | [Japanese](README-ja.md)

# 1-1

Theorems toward a lower bound on the frame 1-2 starts. The work in progress by part is in [The 1-1 route](../docs/route-1-1.md).

A label is `<world>-<stage>-<part>-<number>[-<sub>]`. `0-0` is what several stages share, and part `0` is what no single part owns.

## Part 0 (the whole stage)

Joins all the parts into a lower bound on the frame 1-2 starts.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-0-1 | [The whole of 1-1](0-1-Route.md) | If a run satisfies every assumption of `Run`, 1-2 does not start before frame 1748. | a Lean theorem joining the parts; the assumptions are listed as the fields of `Run`, not proved for every run |

## Part a

Frames 0 → 368. From the start of 1-1 to entering the vertical pipe. The bound on the distance of the opening and the condition to enter the pipe decide it.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-a-1 | [Fast accel](a-1-FastAccel.md) | If small Mario stands still on the ground at the start of a level, in a land area with nothing around him, the least number of frames to reach the running top speed with a real controller is 34. | 34 frames: theorem. 33 or fewer impossible: theorem on a relaxed model |
| 1-1-a-2 | [TAS fast accel](a-2-TasFastAccel.md) | If small Mario stands still on the ground at the start of a level, in a land area with nothing around him, the least number of frames to reach the running top speed with Left+Right allowed is 32. | 32 frames: theorem. 30 or fewer impossible: theorem on a relaxed model. 31 impossible: exhaustive search |
| 1-1-a-3 | [The opening](a-3-Opening.md) | From the start of 1-1, on open flat ground, Mario moves right at most 2.5·n − 41.94 px in n ≥ 32 frames. | theorem under the assumptions of the horizontal frame and of the jump lengths (search of about 4 s) |
| 1-1-a-4 | [Entering the vertical pipe](a-4-PipeEntry.md) | With frame 0 the first controllable frame of 1-1, Mario does not enter the vertical pipe before frame 368. | theorem about frames that follow the entry rule; the rule is checked against the collision routine on every state near the pipe's top (about 3 s); that frame 368 is reached is the TAS on the emulator |
| 1-1-a-5-1 | [Entering the pipe on real frames](a-5-1-PipeEntryRule.md) | On a real frame whose routine write ends one pass of the foot check, the position when the right foot is read is at or right of the window's left end. | one pass of the foot check by an abstract machine; the check by `native_decide` (about 3 s in the proof build). `Route` uses the whole frame of 1-1-a-5-2 in place of `Pass` |
| 1-1-a-5-2 | [One whole frame: who writes the routine byte](a-5-2-PipeWrites.md) | On a real frame that starts in control and whose instructions meet `Clean`, the position at the right foot's entry before the routine's write is at or right of the window's left end. | one whole frame in control by an abstract machine, 0 failures; the check by `native_decide` (about 5 s in a program, 59 s in the proof build). Not proved: `FrameStart`, `Clean`, `TilesOK`, `pos` |

## Part b

Frames 368 → 459. From entering the vertical pipe to control in the bonus room. This change takes 91 frames.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-b-1 | [The change into the bonus room](b-1-PipeTransition.md) | From the entry states listed on the page, control in the bonus room comes exactly 91 frames after Mario enters the vertical pipe. | shown on one real entry state for every input on every frame except Start and Select, and with no input for other positions, speeds, a big Mario and 21 consecutive entry frames; one state per frame checked on the emulator by `native_decide` (about 4 s); for arbitrary inputs it assumes that states equal except for the bytes echoing the buttons behave the same |
| 1-1-b-2-1 | [What decides the change into the bonus room](b-2-1-PipeTransitionAll.md) | Every machine equal to a machine whose pipe timer has just run out on its registers and similar state and on a list of RAM bytes gets control exactly 43 frames later with no input, whatever its other bytes are. | the theorem on tracked runs is proved for every instruction of the CPU, with no ROM; the checks by `native_decide` (about 5 s); with the first 48 frames, 77 entry states have length 91; every entry state only under four assumptions. Not proved: the first 48 frames for an arbitrary entry, and the values of the listed bytes that differ from run to run |
| 1-1-b-2-2 | [A bound from single frames](b-2-2-PipeChangeBound.md) | If the number of frames left falls by at most one per frame, there is no control on the first 90 frames after the entry, for any inputs. | the theorem, and the check on the reference and 13 real entry states (about 4 s). The hypothesis on single frames, `fall`, is only checked, on 140,160 real frames, and not proved |
| 1-1-b-2-3 | [A run with unknown bytes](b-2-3-TaintRun.md) | A machine that meets the conditions at frame 50 gets control exactly 41 frames later with no input, whatever its other bytes are. | the theorem on runs with unknown bytes is proved with no ROM; the check by `native_decide` (about 7 s in the proof build). From frame 48 it is false: some music states stop the game. The conditions are not proved for every run |
| 1-1-b-3-2 | [The change into the room without `fall`](b-3-2-PipeChangeEnd.md) | A run that meets a condition on the state at the entry, conditions at some places of the pipe's frames and a condition at the exit, with no Start on the frames of the game core after the pipe, takes at least 91 counted frames from the entry to control. | the check by `native_decide` (about 21 s in a program, 42 s in the proof build); it removes `chg.fall₁` from the route. Not proved: the conditions at the places and at the exit (the latter fails after Start on the pipe's frames) |

## Part c

Frames 459 → 570. From control in the bonus room, over the brick block, to entering the side pipe. The least is 111 frames.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-c-1 | [The air speed cap](c-1-AirCap.md) | Moving slower than 1.5625 px/frame, Mario moves at most 1.5·K px plus a bound that depends only on n in K air frames and the n frames after them. | theorem under the assumptions of the horizontal frame (check of about 4 s) |
| 1-1-c-2, 1-1-f-2 | [The height of a jump](c-2-Jump.md) | Over all takeoff speeds and ways of pressing A, the frames on which Mario rises at the height of a direct grab of the flagpole, the earliest frame he can land on a block and the earliest frame he can fall to the ground are those in the page's table. | theorem on the game's movement routine, without collisions (about 6 s) |
| 1-1-c-3 | [A fast takeoff](c-3-FastTakeoff.md) | With control in the bonus room at frame 459, over all inputs, Mario jumping from the floor at 1.5625 px/frame or more and staying left of the brick block's corner while his feet are low does not reach the block's right end at frame 557. | theorem on the horizontal frame model; the start state, the fall and the 8 low frames are assumptions. |
| 1-1-c-4 | [Entering the side pipe](c-4-SidePipe.md) | Mario enters the side pipe ⇔ he is not rising ∧ his feet are in the landing depth of the ground ∧ he faces right ∧ his right side is in the pipe's mouth. | theorem about frames that follow the rule; the rule is checked against the collision routine on every state near the mouth (about 3 s) |
| 1-1-c-5 | [Joining the bonus room](c-5-RoomJoin.md) | With C the first controllable frame in the bonus room and E the frame Mario enters the side pipe, E ≥ C + 111. | a theorem on the frames of a run; the assumptions are mostly about one frame; that real frames satisfy them is assumed, and holds on the TAS and 4501 real runs; runs that stand on the left wall and never touch the floor are covered |

## Part d

Frames 570 → 852. From entering the side pipe to control above ground. This change takes 282 frames.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-d-1 | [The change out of the side pipe](d-1-SideTransition.md) | From the entry states listed on the page, control above ground comes exactly 282 frames after Mario enters the side pipe. | shown on one real entry state for every input on every frame except Start and Select, and with no input for other pixels, fractions and speeds, a big Mario, real entries at three pixels and on 21 consecutive frames; an entry frame ending with x a multiple of 16 takes longer; one state per frame checked on the emulator by `native_decide` (about 11 s); for arbitrary inputs it assumes that states equal except for the bytes echoing the buttons behave the same |
| 1-1-d-2-1 | [What decides the change out of the side pipe](d-2-1-SideTransitionAll.md) | Every machine equal to a machine whose side pipe timer has just run out on its registers and similar state and on a list of RAM bytes gets control exactly 122 frames later with no input, whatever its other bytes are. | the checks by `native_decide` (about 5 s); with the first 160 frames, 20 entry states have length 282; every entry state only under four assumptions. Overwritten states with the screen not on the first page take 174 frames. Not proved: the first 160 frames for an arbitrary entry, the values of the listed bytes that differ from run to run, and that a run keeps the screen on the first page |
| 1-1-d-2-2 | [The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md) | A machine that meets a condition on one state at the entry has no control on the first 160 frames, for any inputs. | one frame of an abstract machine, with the pad not known and the timer free, closes; the check by `native_decide` (about 3 s in the proof build). Not proved: that a real run meets the condition |
| 1-1-d-2-3 | [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md) | A machine that meets a condition on one state at the exit has no control on the next 121 frames, for any inputs with no Start on the frames of the game core. | an abstract run with a tick across the frame's end, 123 rows in two cases of the sound's pause flag; the check by `native_decide` (about 13 s in the proof build). Not proved: a pause after the pipe, a pause sound running at the exit, that a real run meets the condition |
| 1-1-d-2-4 | [The screen's page in the room, and the long timer](d-2-4-ScreenPage.md) | If the state at the first control in the room meets a condition on one state and each instruction up to the side pipe meets a condition on one machine, the screen stays on the first page and the entry has the long timer. | one whole frame in the room by the abstract machine; the check by `native_decide` (about 4 s in a program, 8 s in the proof build). Not proved: the condition at the first control, `SiteOK` |

## Part e

Frames 852 → 1085. From control above ground, running to the flag. Mario does not reach the pole's range by frame 1085.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-e-1 | [Above ground: not at the pole by frame 1085](e-1-SurfaceRun.md) | With control above ground at frame 852, over all inputs, Mario does not reach the pole's range by frame 1085. | proved in a model with ground or air chosen freely on every frame, for runs of the horizontal frame and of `TopSpeed.Frame` (about 3 s); that real frames follow them is assumed, and the frame agrees with the TAS on every frame from 853 to 1085 |
| 1-1-e-2 | [Above ground: the frames from control, one by one](e-2-SurfaceFrames.md) | The state at control comes from the last row of the change, and the position up to the first hit, the hit and the first 8 frames come from facts on one frame. | proved from `OnFrames` and `chg`; the checks by `native_decide` (about 5 s in the proof build). Not proved: that real frames meet `step`, `vert`, `box` |

## Part f

Frames 1085 → 1218. Touching the pole and entering the castle. The castle does not come before 366 frames after control above ground.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-c-2, 1-1-f-2 | [The height of a jump](c-2-Jump.md) | Over all takeoff speeds and ways of pressing A, the frames on which Mario rises at the height of a direct grab of the flagpole, the earliest frame he can land on a block and the earliest frame he can fall to the ground are those in the page's table. | theorem on the game's movement routine, without collisions (about 6 s) |
| 1-1-f-1 | [Grabbing the pole from below](f-1-PoleGrab.md) | If, moving at top speed from where his feet enter the height above the flagpole's base, Mario is still more than 32/256 px short of the pole's range on some frame no earlier than 3 frames before landing, he cannot grab the pole by a jump after landing. | theorem about frames that follow the collision rules; the conditions on the numbers of frames to landing and beside the block are on the page; the rules are checked against the routine on every state near the block (about 4 s) |
| 1-1-f-3 | [The fast hop beside the flagpole](f-3-FastHop.md) | Mario stopped by a hit beside the flagpole's base does not reach the pole's range by a fast jump from the stored speed. | check of the movement routine (about 1 s) and a theorem about frames that follow it; the push back on frames with his feet inside the base is an assumption |
| 1-1-f-4 | [From touching the pole to the castle](f-4-CastleWalk.md) | From the touch states listed on the page, Mario does not enter the castle earlier than 126 frames after touching the pole. | real frames on the emulator (about 5 s); all inputs from one touch state, assuming that states equal except for the bytes echoing the buttons behave the same |
| 1-1-f-5 | [From control to the castle](f-5-PoleJoin.md) | With frame 0 the first controllable frame above ground, Mario does not enter the castle before frame 366. | theorem on named assumptions about real frames (`Run`); the fast jump, the 3-frame fall and the first hit are derived from single-frame assumptions and checks; checked as a program on the TAS and other real runs |
| 1-1-f-6-1 | [Touching the pole on real frames](f-6-1-PoleEntryRule.md) | On a real frame whose routine write ends one pass of the side check, the position when the page is read is at or right of the left end of the pole's range. | one pass of the side check by an abstract machine; the check by `native_decide` (about 3 s in a program, 7 s in the proof build). Not proved: that a real touch is such a pass (`Pass`), and `pos` |

## Part g

Frames 1218 → 1748. From the castle to the start of 1-2. The timer, the fireworks and the 21-frame grid decide it.

| label | theorem | statement | status |
|---|---|---|---|
| 1-1-g-1 | [From the castle to 1-2](g-1-CastleToLevel.md) | If the lower bounds of the parts, the rule of the timer and the grid on each frame, and the rule of the star flag on each frame hold, 1-2 does not start before frame 1748. | the arithmetic is a theorem; checks on real frames of about 18 s: the formula at 21 phases, fireworks, the frame rule on 6 runs and a run with pauses, the star flag's rule at 21 phases, with fireworks and with pauses, every input from one state under `GMerge` |
| 1-1-g-2-1 | [The star flag's rule after the castle entry](g-2-1-FlagRule.md) | If the machine just after the castle entry meets the condition Good and Start is not pressed after it, the star flag's rule holds on every frame up to the level change, and the level changes on a frame of task 5. | proved by a check of the ROM (about 37 s in a program, 47 s in the proof build). Not proved: Good at the castle entry |
