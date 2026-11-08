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
| 0-0-0-3-2 | [A real frame and the horizontal model](0-0/0-3-2-FrameModel.md) | From the player's routine to the scroll handler, a real frame changes the horizontal state as `hstep` says and moves the position by 16·v'. | the movement by a walk of two machines; the check by `native_decide` (about 2 s). Not proved: the rest of the frame (`Clean`, `ReadFrame`) |

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
  - 🚨 1-1-0-4 Joining the assumptions of the parts
  - 🚨 1-1-0-5 Assumptions of the whole
    - 🚨 1-1-0-5-1 Each frame follows the rule of its kind (`step`)
    - 🚨 1-1-0-5-2 The kinds of frame come in the order of the parts (`plan`)
    - 🚨 1-1-0-5-3 The timer and the phase at frame 0 (`s_zero`, `ph_zero`)
  - 🚨 1-1-0-6 Runs not in the theorem
    - 🚨 1-1-0-6-1 Runs that do not go through the two pipes
    - 🚨 1-1-0-6-2 Runs with a power-up
    - 🚨 1-1-0-6-3 Runs that die and start again
    - 🚨 1-1-0-6-4 Runs with the hurry-up music
- 🚨 1-1-a To the pipe (0 → 368)
  - ✅ 1-1-a-1 Fast accel
  - ✅ 1-1-a-2 TAS fast accel
  - ✅ 1-1-a-3 The opening
  - ✅ 1-1-a-4 The condition to enter the pipe
  - 🚨 1-1-a-5 Assumptions of part a
    - ✅ 1-1-a-5-1 The entry on real frames: one pass of the foot check
    - 🚨 1-1-a-5-2 One whole frame: only that instruction writes the pipe's routine
      - 🚨 1-1-a-5-2-1 The state when an entering frame starts (`start`)
      - 🚨 1-1-a-5-2-2 Each instruction up to the write meets `Clean` (`clean`)
    - 🚨 1-1-a-5-3 The pipe's right tile is only at its place (`tiles`)
    - 🚨 1-1-a-5-4 The bound on the opening's position (`openP`, `openB`)
    - 🚨 1-1-a-5-5 The frames after it follow each other (`speed`, `next`)
    - 🚨 1-1-a-5-6 Open flat ground, in the air only during a jump
    - 🚨 1-1-a-5-7 A jump's length depends only on the takeoff speed
    - 🚨 1-1-a-5-8 The gain bound of the relaxed model (`GainBound`)
    - 🚨 1-1-a-5-9 The position at the foot check is the frame's (`pos`)
- 🚨 1-1-b Into the room (368 → 459)
  - ✅ 1-1-b-1 The length of the change (listed entry states)
  - ✅ 1-1-b-2-1 The bytes that decide the last 43 frames
  - ✅ 1-1-b-2-2 No control on the first 90 frames after the entry (under `fall`, any inputs)
  - ✅ 1-1-b-2-3 The last 41 frames, for the bytes that differ from run to run
  - 🚨 1-1-b-3 Assumptions of part b
    - ✅ 1-1-b-3-1 `change₁` proved from `chg`
    - ✅ 1-1-b-3-2 `chg.fall₁` removed: the change from conditions at the entry, the pipe's frames and the exit
    - 🚨 1-1-b-3-3 A `lag` frame keeps the frames left (`chg.keep₁`)
    - 🚨 1-1-b-3-4 A real entry meets the condition (`chg.entry₁`)
    - 🚨 1-1-b-3-5 The conditions at places of the pipe's frames (`chg.places₁`)
    - 🚨 1-1-b-3-6 No pause after the pipe (`chg.noStart₁`)
    - 🚨 1-1-b-3-7 No pause sound, and the song and the screen buffer in the tables, at the exit (`chg.quiet₁`)
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
    - 🚨 1-1-c-7-2 The state at first control (`start`, `startP0`, `startP1`)
    - 🚨 1-1-c-7-3 The entry frame follows the routine (`entry`, `entered`)
    - 🚨 1-1-c-7-4 How the left wall stops him (`wall`, `late`, `stop_run`)
    - 🚨 1-1-c-7-5 The fall and the height of the feet (`v_start`, `air_in`, `stand_wall`, `fall_long`, `stand_row`, `vfall`, `floor_at`, `vframes`, `low_at`)
    - 🚨 1-1-c-7-6 The stored speed (`ab_start`, `ab_ge`, `ab_follow`)
    - 🚨 1-1-c-7-7 Takeoff and landing (`Approach`)
    - 🚨 1-1-c-7-8 The ways off the block (`Off`)
    - 🚨 1-1-c-7-9 A jump over the whole block (`Over`)
    - 🚨 1-1-c-7-10 He does not bump his head
    - 🚨 1-1-c-7-11 Only the takeoff speed links the vertical motion to the horizontal
    - 🚨 1-1-c-7-12 The block map is the one written by hand
    - 🚨 1-1-c-7-13 Standing during the fall (`facing`, `stand_fast`, `stand_P`)
    - 🚨 1-1-c-7-14 No run jumps from the wall and clears the block with no landing (`way`)
- 🚨 1-1-d Back above ground (570 → 852)
  - ✅ 1-1-d-1 The length of the change (listed entry states)
  - ✅ 1-1-d-2-1 The bytes that decide the last 122 frames
  - ✅ 1-1-d-2-2 The first 160 frames (under the condition at the entry, any inputs)
  - ✅ 1-1-d-2-3 The last 122 frames (under the condition at the exit, no Start on the game core's frames)
  - 🚨 1-1-d-2-4 The screen stays on the first page, the entry has the long timer
    - 🚨 1-1-d-2-4-1 The condition at the first control in the room (`chg.roomStart`)
    - 🚨 1-1-d-2-4-2 Each instruction in the room meets `SiteOK` (`chg.roomSites`)
    - 🚨 1-1-d-2-4-3 Each frame before the entry starts in the player's routine (`chg.roomStay`)
  - 🚨 1-1-d-2-5 A real entry meets the condition (`chg.entry₂`)
  - 🚨 1-1-d-3 Assumptions of part d
    - ✅ 1-1-d-3-1 `change₂` proved from `chg`
    - 🚨 1-1-d-3-2 A `lag` frame keeps the frames left (`chg.keep₂`)
    - 🚨 1-1-d-3-3 No pause after the pipe (`chg.noStart₂`)
    - 🚨 1-1-d-3-4 No pause sound at the exit (`chg.quiet₂`)
    - 🚨 1-1-d-3-5 `left` is not 0 before control (`chg.first₂`)
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
    - ✅ 1-1-e-2-4 Frames 1 to 8 stay in the checked box (from `vert`, `box`)
    - ✅ 1-1-e-2-5 He leaves the model only by a collision (from `step`)
    - ✅ 1-1-e-2-6 The frames follow each other (from `reads`)
    - ✅ 1-1-e-2-7 The left edge of the screen stopping him (`Frame`, `Hit`)
    - 🚨 1-1-e-2-8 One frame is `hstep` and the collision routine (`step`)
    - 🚨 1-1-e-2-9 Frames 1 to 8 are `vstep` and the machine at control (`vert`, `box`)
    - 🚨 1-1-e-2-10 Frames are read from machines (`reads`, `atCtl`)
- 🚨 1-1-f The flag (1085 → 1218)
  - ✅ 1-1-f-1 The bound on the push back
  - ✅ 1-1-f-2 The height of a jump
  - ✅ 1-1-f-3 The condition for a fast jump
  - ✅ 1-1-f-4 The length from the touch to the castle
  - ✅ 1-1-f-5 Joining parts e and f
  - 🚨 1-1-f-6 Assumptions of part f
    - ✅ 1-1-f-6-1 The touch on real frames: one pass of the side check
    - 🚨 1-1-f-6-2 The castle comes after the touch (`atCastle`, `afterTouch`)
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
    - 🚨 1-1-f-6-13 The position's fraction is a multiple of 1/16 px
    - 🚨 1-1-f-6-14 No enemy near the flag
    - 🚨 1-1-f-6-15 He does not go over the flag and come back
    - 🚨 1-1-f-6-16 Only that instruction writes the routine, at the end of a pass (`pass`)
    - 🚨 1-1-f-6-17 The pole's tiles are only in its column (`TilesOK`)
    - 🚨 1-1-f-6-18 The position at the side check is the frame's (`pos`)
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
    - ✅ 0-0-0-3-2 `hstep` is the horizontal part of one frame (`move_model`)
    - 🚨 0-0-0-3-3 Only the 5 checked routines write the speed and position: proved in the movement (`before`, `after`, `collide` remain)
    - 🚨 0-0-0-3-4 Each routine depends only on the checked bytes: proved in the movement, not for `ImpedePlayerMove`
    - 🚨 0-0-0-3-5 Runs that press Start or Select
    - 🚨 0-0-0-3-6 The emulator is the same as the real machine
