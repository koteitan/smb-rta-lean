[English](README.md) | [Japanese](README-ja.md)

# smb-rta-lean

Super Mario Bros. speedrun facts, checked in Lean 4.

Theorems by stage: [1-1](1-1/README.md)

## Common

Theorems that several stages use.

| label | theorem | statement | status |
|---|---|---|---|
| 0-0-0-1 | [Top speed bound](0-0/0-1-TopSpeed.md) | Away from platforms, vines, pipes and similar objects, Mario never moves right by more than 2.5 px per frame. | per-routine checks: theorems; the routines being the only writers: from the disassembly |
| 0-0-0-2 | [Reach](0-0/0-2-Reach.md) | From the start of 1-1, in the open area, Mario moves right at most 2.5·n − 38.375 px in n ≥ 28 frames. | theorems under the assumptions of the top speed bound and of the horizontal frame; the TAS inputs move 2.5·n − 41.94 px |
| 0-0-0-3-2 | [A real frame and the horizontal and vertical models](0-0/0-3-2-FrameModel.md) | From the player's routine to the scroll handler, a real frame changes the horizontal state as `hstep` says, moves the position by 16·v', and changes the vertical state as `vstep` says. | the movement by a walk of two machines, the vertical part with detours where the two run apart; Also with the pressed side masked (`move_masked`: `hstep`, or the speed 0; check about 0.1 s). the checks by `native_decide` (about 2 s and 0.1 s). Not proved: the rest of the frame (`Clean`, `ReadFrame`), and for `vstep` two conditions at the player's routine |

Each page gives the statement, what Lean proves, the assumptions and how they were checked,
and how to reproduce it. A theorem is `Theorems/Name.lean` (the statement and how it follows from a computation) and the pages `<stage>/<part>-<number>-Name.md`, `<stage>/<part>-<number>-Name-ja.md`.

* [Setup](docs/setup.md) — write `smbrta.json`, put the ROM in place, run `python3 prove.py` (the ROM is not included).
* [Emulator](docs/emulator.md) — the NES in Lean and how it was checked.
* [Method](docs/method.md) — models that run the game code, reachability certificates,
  relaxed models, pruned exact search.

## Layout

```
Smbrta/      the library: NES (Machine, Cpu), movies, symbols, certificates, models
Theorems/    one statement (Lean) per theorem
0-0/         pages of the theorems several stages share (English, Japanese)
1-1/         the table and pages of stage 1-1 (English, Japanese)
docs/        common pages, and the 1-1 route
tools/       symbol extraction, test data, a separate place for each worker
Config.lean  where the files outside the repository are (smbrta.json; template smbrta-tmpl.json)
Main.lean    command line (`smbrta`)
prove.py     runs everything, from smbrta.json to the checked theorems
```

## Progress

A label is `<world>-<stage>-<part>-<number>[-<sub>]`. `0-0` is what several stages share, and part `0` is what no single part owns.

- 🚨 1-1-0 The whole stage (0 → 1748)
  - ✅ 1-1-0-1 The theorem from the assumptions to 1748
  - ✅ 1-1-0-2 The timer and the grid from the rule on one frame
  - ✅ 1-1-0-3 The fireworks and the level change from the rule on one frame
  - ✅ 1-1-0-4 Joining the assumptions of the parts (`pipeAt`, `roomCtl`, `roomEnter`, `atCtl` removed: the parts take their machines from one sequence `base`)
  - 🚨 1-1-0-5 Assumptions of the whole
    - 🚨 1-1-0-5-1 Each frame follows the rule of its kind (`step`)
    - 🚨 1-1-0-5-2 The kinds of frame come in the order of the parts (`plan`)
    - ✅ 1-1-0-5-3 The timer and the phase at frame 0 (`zero` removed; from one state after the press on the title)
    - 🚨 1-1-0-5-4 The machine after Start on the title meets the condition (`title.press`; with the pause sound's buffer)
    - ✅ 1-1-0-5-5 Start before control (`title.noPause` removed; a search closed under any input, and `frame0Check`)
  - 🚨 1-1-0-6 Runs not in the theorem
    - 🚨 1-1-0-6-1 Runs that do not go through the two pipes
    - 🚨 1-1-0-6-2 Runs with a power-up
    - 🚨 1-1-0-6-3 Runs that die and start again
    - 🚨 1-1-0-6-4 Runs with the hurry-up music
      - ✅ 1-1-0-6-4-1 1-2 does not start before frame 1748 (under `start`, `ctl`, `clean`, `below`)
      - 🚨 1-1-0-6-4-2 The frame that starts the music (`start`, `ctl`, `clean`, `below`)
        - ✅ 1-1-0-6-4-2-1 It ends with the timer at 100 or less (`music` removed; by a walk of one whole frame)
        - 🚨 1-1-0-6-4-2-2 It is a real frame in control
          - ✅ 1-1-0-6-4-2-2-1 It begins in control (induction over the frames in control; none from frame 1)
          - 🚨 1-1-0-6-4-2-2-2 The start of frame `b`, `ctl` and `clean` on each frame
            - ✅ 1-1-0-6-4-2-2-2-1 The start of frame `b` (no state in `start`: frame 1, or the last frame of a change, from the change's rows)
            - 🚨 1-1-0-6-4-2-2-2-2 `ctl` and `clean` on each frame
        - 🚨 1-1-0-6-4-2-3 On the next frame the digits of `clock` are not above the machine's (`below`; one frame, was every frame)
- 🚨 1-1-a To the pipe (0 → 368)
  - ✅ 1-1-a-1 Fast accel
  - ✅ 1-1-a-2 TAS fast accel
  - ✅ 1-1-a-3 The opening
  - ✅ 1-1-a-4 The condition to enter the pipe
  - 🚨 1-1-a-5 Assumptions of part a
    - ✅ 1-1-a-5-1 The entry on real frames: one pass of the foot check
    - 🚨 1-1-a-5-2 One whole frame: only that instruction writes the pipe's routine
      - ✅ 1-1-a-5-2-1 The state when an entering frame starts (`start` removed; from the induction of 1-1-a-5-5-3-2)
      - 🚨 1-1-a-5-2-2 Each instruction up to the write meets `Clean` (`clean`)
    - 🚨 1-1-a-5-3 The pipe's right tile is only at its place (`tiles`)
    - 🚨 1-1-a-5-4 The bound on the opening's position (`openP`, `openB` gone)
      - ✅ 1-1-a-5-4-1 No bound up to frame N is needed (position at control, top speed)
      - ✅ 1-1-a-5-4-2 The bound at the end of frame N (if each frame is a model step)
      - 🚨 1-1-a-5-4-3 The first 32 frames are steps of the model (`opening`; holds 1-1-a-5-6, 1-1-a-5-7)
    - 🚨 1-1-a-5-5 The frames after: read from the machines (`own`, `lags`)
      - ✅ 1-1-a-5-5-1 The frames follow each other, with the top speed (`next`, `speed` are theorems)
      - ✅ 1-1-a-5-5-2 The speed at control is 0 (`still` removed; from `title`)
      - 🚨 1-1-a-5-5-3 Frames not counted keep the speed and the position (`lags`)
        - ✅ 1-1-a-5-5-3-1 A frame that does not call the mode's routine (a pause) keeps them (`keeps_frame`)
        - 🚨 1-1-a-5-5-3-2 It starts in the idle loop; its instructions before the call are `Clean`
          - ✅ 1-1-a-5-5-3-2-1 It starts in the idle loop (`lags.start` removed; induction from control)
          - 🚨 1-1-a-5-5-3-2-2 Each counted frame up to the entry ends in control, each instruction `Clean` (`lags.ctl`, `lags.clean`; `one_le` a theorem; a frame not counted without the call: by the check)
          - ✅ 1-1-a-5-5-3-2-3 Stores before the call do not touch the speed and the position (`lags.store` removed; the walk knows each store's target)
        - 🚨 1-1-a-5-5-3-3 Frames not counted do not call the routine (`lags.game` gone)
          - ✅ 1-1-a-5-5-3-3-1 A frame that ends paused does not call it (two walks)
          - 🚨 1-1-a-5-5-3-3-2 Frames not counted end paused and do not write the pause byte through an index (`lags.paused`, `lags.keeps`)
    - 🚨 1-1-a-5-6 Open flat ground, in the air only during a jump
    - 🚨 1-1-a-5-7 A jump's length depends only on the takeoff speed
    - 🚨 1-1-a-5-8 The gain bound of the relaxed model (`GainBound`)
    - 🚨 1-1-a-5-9 The position at the foot check is the position at the end of the move (`edge`, `moved`)
      - ✅ 1-1-a-5-9-1 From the end of the move to the foot check the position does not change (`rule_on_framesS`)
      - 🚨 1-1-a-5-9-2 Up to the write: no store of the position at the screen's edge, no bump of a block with the head (`edge`)
      - 🚨 1-1-a-5-9-3 `P₂` is the position at the end of the move (`moved`, part of 0-0-0-3-1)
- 🚨 1-1-b Into the room (368 → 459)
  - ✅ 1-1-b-1 The length of the change (listed entry states)
  - ✅ 1-1-b-2-1 The bytes that decide the last 43 frames
  - ✅ 1-1-b-2-2 No control on the first 90 frames after the entry (under `fall`, any inputs)
  - ✅ 1-1-b-2-3 The last 41 frames, for the bytes that differ from run to run
  - 🚨 1-1-b-3 Assumptions of part b
    - ✅ 1-1-b-3-1 `change₁` proved from `chg`
    - ✅ 1-1-b-3-2 `chg.fall₁` removed: the change from conditions at the entry, the pipe's frames and the exit
    - ✅ 1-1-b-3-3 `chg.keep₁` removed: a frame that ends paused keeps the frames left
    - 🚨 1-1-b-3-4 The condition at the entry (`chg.entry₁` is gone)
      - ✅ 1-1-b-3-4-1 The idle loop, the pipe's timer and 72 bytes from the title and the frames from control
      - 🚨 1-1-b-3-4-2 The other 56 bytes (`chg.entryRest₁`)
      - ✅ 1-1-b-3-4-3 Each frame from control to the entry starts in control (`chg.upStart₁` is gone: by induction; `a₁` is the first frame without control)
      - 🚨 1-1-b-3-4-4 Each of its instructions is `Clean` (`chg.upClean₁`)
    - 🚨 1-1-b-3-5 The conditions at places of the pipe's frames (`chg.places₁`)
    - 🚨 1-1-b-3-6 No pause after the pipe (`chg.noStart₁`)
    - 🚨 1-1-b-3-7 No pause sound or square sound effects, and the song and the screen buffer in the tables, at the exit (`chg.quiet₁`)
    - 🚨 1-1-b-3-8 A `lag` frame ends paused (`chg.paused₁`)
    - 🚨 1-1-b-3-9 The time is not up at the exit (`chg.time₁`); `b₁` is defined as the first control (`chg.ctlFirst₁` is gone); `left₁` not 0 before control is proved
  - 🚨 1-1-b-4 Assumptions of the exact lengths (the route does not need them)
    - 🚨 1-1-b-4-1 The same for every input (`Merge`)
    - 🚨 1-1-b-4-2 The bytes, size and timer at frame 50 (`Cond`)
    - 🚨 1-1-b-4-3 Six objects do not gather close together
- 🚨 1-1-c The bonus room (459 → 570)
  - ✅ 1-1-c-1 The air speed cap
  - ✅ 1-1-c-2 The height of a jump
  - ✅ 1-1-c-3 A fast takeoff
  - ✅ 1-1-c-4 The condition to enter the side pipe
  - ✅ 1-1-c-5 Joining the room
  - ✅ 1-1-c-6 Runs that reach the block without touching the floor
  - 🚨 1-1-c-7 Assumptions of part c
    - ✅ 1-1-c-7-1 Each frame follows `hstep` or stops him (from `clean`)
    - ✅ 1-1-c-7-2 The state at first control (`start`, `startP0`, `startP1`, `v_start`, `ab_start`): from the change's rows
    - ✅ 1-1-c-7-3 The entry on real frames: one pass of the side check
    - 🚨 1-1-c-7-4 How the left wall stops him (`wall`, `late`, `stop_run`)
    - 🚨 1-1-c-7-5 The fall and the height of the feet (`air_in`, `stand_wall`, `fall_long`, `stand_row`, `vfall`, `floor_at`, `vframes`, `low_at`; `vframes` only before the entry, on frames with no head's collision)
    - 🚨 1-1-c-7-6 The stored speed: proved on frames that follow the model; other frames before `C + 37` assumed (`ab_early`)
    - 🚨 1-1-c-7-7 Takeoff and landing (`Approach`)
    - 🚨 1-1-c-7-8 The ways off the block (`Off`)
    - 🚨 1-1-c-7-9 A jump over the whole block (`Over`)
    - ✅ 1-1-c-7-10 He does not bump his head: no frame of the room comes to the head's two places (`RoomMap`)
    - 🚨 1-1-c-7-11 Only the takeoff speed links the vertical motion to the horizontal
    - 🚨 1-1-c-7-12 The block map: bits that are 0 in the map stay 0 on every frame (proved, `RoomMap`); the 1 bits and the numbers of the other fields assumed
    - 🚨 1-1-c-7-13 Standing during the fall (`facing`, `stand_fast`, `stand_P`)
    - 🚨 1-1-c-7-14 No run jumps from the wall and clears the block with no landing (`way`)
    - ✅ 1-1-c-7-15 The first machine is the change's (`roomCtl` removed: by definition)
    - ✅ 1-1-c-7-16 The write ends the side check (`pass`): proved by one whole frame (`SideFrame`)
    - ✅ 1-1-c-7-17 The pipe's tiles only in its column: `RoomMap` and the theorem `roomEnter`
    - ✅ 1-1-c-7-18 `P(E)` is at the mouth
      - ✅ 1-1-c-7-18-1 The edge store and the head up to the write (`edgeE` gone)
      - ✅ 1-1-c-7-18-2 The position at the frame's end (two walks; `movedE` removed)
- 🚨 1-1-d Back above ground (570 → 852)
  - ✅ 1-1-d-1 The length of the change (listed entry states)
  - ✅ 1-1-d-2-1 The bytes that decide the last 122 frames
  - ✅ 1-1-d-2-2 The first 160 frames (under the condition at the entry, any inputs)
  - ✅ 1-1-d-2-3 The last 122 frames (under the condition at the exit, no Start on the game core's frames)
  - 🚨 1-1-d-2-4 The screen stays on the first page, the entry has the long timer
    - ✅ 1-1-d-2-4-1 `Room` at the first control in the room: from the change's rows of the time (`chg.roomRest` removed)
    - 🚨 1-1-d-2-4-2 Each instruction in the room meets `SiteOK` (`chg.roomSites`)
    - ✅ 1-1-d-2-4-3 Each frame up to the entry starts in the player's routine (from the definition of `a₂`)
  - 🚨 1-1-d-2-5 16 bytes at the entry (`chg.entry₂`); the rest from the room's walk and the change's rows
  - 🚨 1-1-d-3 Assumptions of part d
    - ✅ 1-1-d-3-1 `change₂` proved from `chg`
    - 🚨 1-1-d-3-2 A `lag` frame ends paused (`chg.paused₂`); that it keeps `left` is proved
    - 🚨 1-1-d-3-3 No pause after the pipe (`chg.noStart₂`)
    - 🚨 1-1-d-3-4 No pause sound at the exit (`chg.quiet₂`)
      - ✅ 1-1-d-3-4-1 One CPU step writes only where its instruction stores (`StepWrites`; a walk carries the sound's bytes in a table)
    - 🚨 1-1-d-3-5 The game timer is not 000 at the exit (`chg.time₂`; the sound's pause flag is proved); `left` not 0 before control is proved; `b₂` is the first control by definition
  - 🚨 1-1-d-4 Assumptions of the exact lengths (the route does not need them)
    - 🚨 1-1-d-4-1 The same for every input (`GMerge`)
    - 🚨 1-1-d-4-2 The bytes when the timer has run out (H3)
    - 🚨 1-1-d-4-3 `x` at the entry is not a multiple of 16
    - 🚨 1-1-d-4-4 Six objects do not gather close together
- 🚨 1-1-e Speeding up above ground (852 → 1085)
  - ✅ 1-1-e-1 The bound on the speed-up
  - 🚨 1-1-e-2 Assumptions of part e
    - ✅ 1-1-e-2-1 Stopped at control (from the change's last row)
    - ✅ 1-1-e-2-2 `hstep` up to the first hit (from `step`)
    - ✅ 1-1-e-2-3 A hit leaves the speed at 0 or below (from `step`)
    - ✅ 1-1-e-2-4 Frames 1 to 8 stay in the checked box (from `vert_of`, `box`)
    - ✅ 1-1-e-2-5 He leaves the model only by a collision (from `step`)
    - ✅ 1-1-e-2-6 The frames follow each other (from `reads`)
    - ✅ 1-1-e-2-7 The left edge of the screen stopping him (`Frame`, `Hit`)
    - 🚨 1-1-e-2-8 One frame is `hstep` and the collision routine
      - ✅ 1-1-e-2-8-1 The movement is `hstep` (`move_model`, `one_of_moves`)
      - 🚨 1-1-e-2-8-2 The frame outside the movement (`moves`)
        - ✅ 1-1-e-2-8-2-1 The state at the player's routine (`at_ctrl`, `before`, `bits` gone; the walk of `CtrlKeep`)
        - 🚨 1-1-e-2-8-2-2 The frame's ends and after the scroll handler
          - ✅ 1-1-e-2-8-2-2-1 It comes to the routine (`arrive` gone; from `unpaused` and the walk)
          - ✅ 1-1-e-2-8-2-2-2 Frames not counted keep the 25 bytes (`lag` gone; from `lagPaused` and the walks)
          - 🚨 1-1-e-2-8-2-2-3 The values at the end of the frame before (`state`; area type, swimming, change of size from the walk of the whole frame)
          - 🚨 1-1-e-2-8-2-2-4 After the scroll handler (`after`, `longer`, `far`)
          - 🚨 1-1-e-2-8-2-2-5 A counted frame ends not paused, a frame not counted ends paused (`unpaused`, `lagPaused`; `lagNo` a theorem)
          - 🚨 1-1-e-2-8-2-2-6 Stores through an index do not write 4 bytes (`spare`)
      - ✅ 1-1-e-2-8-3 Frames whose pressed side is masked (`move_masked`, `one_of_movesM`)
    - 🚨 1-1-e-2-9 Frames 1 to 8 are `vstep` and the machine at control
      - ✅ 1-1-e-2-9-1 The movement routine is `vstep` (`vert_model`, `vert_of`)
      - 🚨 1-1-e-2-9-2 The rest of the frame keeps the vertical bytes
        - ✅ 1-1-e-2-9-2-1 Before the routine (`vBefore` gone; the walk and `moves`)
        - 🚨 1-1-e-2-9-2-2 After the scroll handler (`vAfter`)
      - 🚨 1-1-e-2-9-3 The collision routine as on the machine at control (`box`)
    - 🚨 1-1-e-2-10 Frames are read from machines (`reads`; `atCtl` a theorem, `ends` from `keep`)
- 🚨 1-1-f The flag (1085 → 1218)
  - ✅ 1-1-f-1 The bound on the push back
  - ✅ 1-1-f-2 The height of a jump
  - ✅ 1-1-f-3 The condition for a fast jump
  - ✅ 1-1-f-4 The length from the touch to the castle
  - ✅ 1-1-f-5 Joining parts e and f
  - 🚨 1-1-f-6 Assumptions of part f
    - ✅ 1-1-f-6-1 The touch on real frames: one pass of the side check
    - ✅ 1-1-f-6-2 No castle flag up to the touch (`noCastle` removed; from the change's rows and the walk)
    - 🚨 1-1-f-6-3 The path of the jump (`path`, `atY`, `atRising`)
    - 🚨 1-1-f-6-4 He comes from the left and falls below the base's top (`order`, `left`, `air`)
    - 🚨 1-1-f-6-5 One frame of the fall (`fall`)
    - 🚨 1-1-f-6-6 The map near the flag (the premise of `fall`)
    - 🚨 1-1-f-6-7 Frames beside the base follow the collision (`land`, `hop`)
    - 🚨 1-1-f-6-8 The speed after a push to the right (`mask`)
    - 🚨 1-1-f-6-9 The frames before a fast jump (`reads`, `stopped`, `onGround`)
    - 🚨 1-1-f-6-10 The length after a slow jump's grab (`flagAny`, `flagTight`)
    - 🚨 1-1-f-6-11 The length after another touch (`other`)
    - 🚨 1-1-f-6-12 The same for every input after the touch (`GMerge`)
    - ✅ 1-1-f-6-13 The position's fraction is a multiple of 1/16 px (from `fracStep`)
    - 🚨 1-1-f-6-14 No enemy near the flag
    - 🚨 1-1-f-6-15 He does not go over the flag and come back
    - ✅ 1-1-f-6-16 Only that instruction writes the routine (`pass` removed; the walk of the whole touch frame, `PoleFrame`)
    - 🚨 1-1-f-6-17 The pole's tiles are read only in its column (`tiles`, `TileRead`)
    - 🚨 1-1-f-6-18 `P₂(g)` is the position at the end of the move (`moved`); the edge store and the head bump do not bring him into the range (`edge`)
    - ✅ 1-1-f-6-19 Each frame moves the position by a multiple of 1/16 px (one whole frame by the walk, from `keep`)
    - 🚨 1-1-f-6-20 The frames up to the touch are real frames in control
      - ✅ 1-1-f-6-20-1 Each frame starts in control (`start` removed; from the walk and `ctl`)
      - 🚨 1-1-f-6-20-2 The frames before the touch write no routine, mode or task byte by its address (`noStore`, the `lag` frames too; ending in control is the theorem `Frames.ctlAll`)
      - ✅ 1-1-f-6-20-3 The link of the frames, and the `lag` frames (`ends`, `lag`, `lagStart` removed; from the list of all frames and the walk)
    - 🚨 1-1-f-6-21 Each instruction of those frames (`keep.clean`, `CleanK`, the `lag` frames too)
- 🚨 1-1-g From the castle to 1-2 (1218 → 1748)
  - ✅ 1-1-g-1 The timer and the grid
  - 🚨 1-1-g-2 Assumptions of part g
    - ✅ 1-1-g-2-1 Each frame follows the star flag's rule (`step`)
    - 🚨 1-1-g-2-2 The condition at the entry (`Good`, task 2, flag height)
    - 🚨 1-1-g-2-3 The same for every input (`GMerge`)
    - ✅ 1-1-g-2-4 The level changes on a frame with task 5 (`task_L`)
    - 🚨 1-1-g-2-5 No pause after the castle entry (`flag.noStart`)
- 🚨 0-0-0 Common
  - ✅ 0-0-0-1 The top speed bound
  - ✅ 0-0-0-2 Reach
  - 🚨 0-0-0-3 Common assumptions
    - 🚨 0-0-0-3-1 Real frames have the form of `Frame`: `frame_read` (`ReadFrame` remains)
    - ✅ 0-0-0-3-2 `hstep` and `vstep` are the horizontal and vertical parts of one frame (`move_model`, `vert_model`)
    - 🚨 0-0-0-3-3 Only the 5 checked routines write the speed and position: proved in the movement (`before`, `after`, `collide` remain)
    - 🚨 0-0-0-3-4 Each routine depends only on the checked bytes: proved in the movement, not for `ImpedePlayerMove`
    - 🚨 0-0-0-3-5 Runs that press Start or Select
    - 🚨 0-0-0-3-6 The emulator is the same as the real machine
