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

A label is `<world>-<stage>-<part>-<number>[-<sub>]`. `0-0` is what several stages share, and part `0` is what no single part owns. Where every child of a parent is ✅, the children are folded (open them with ▶). Under a 🚨 parent the folded lines are the proved parts, and the parent's own assumptions remain.

- 🚨 1-1-0 The whole stage (0 → 1748)
  - ✅ 1-1-0-1 The theorem from the assumptions to 1748
  - ✅ 1-1-0-2 The timer and the grid from the rule on one frame
  - ✅ 1-1-0-3 The fireworks and the level change from the rule on one frame
  - ✅ 1-1-0-4 Joining the assumptions of the parts (`pipeAt`, `roomCtl`, `roomEnter`, `atCtl` removed: the parts take their machines from one sequence `base`)
  - 🚨 1-1-0-5 Assumptions of the whole
    - 🚨 1-1-0-5-1 Each frame follows the rule of its kind (`step`)
    - 🚨 1-1-0-5-2 The kinds of frame come in the order of the parts (`plan`)
      <details><summary>3 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-0-5-2-1 Above ground, `lag` = ends paused gives `E` = `pole`'s `c` (`LagUp`, not a field; follows from `PhaseUp` and the phase's rule)
        - ✅ 1-1-0-5-2-1-1 A frame in control keeps the phase exactly when it ends paused (`PhaseFrame`, three walks)
        - ✅ 1-1-0-5-2-1-2 With `FirstCastle`, `E` is the first frame with the castle flag (not a field; proved up to the touch's end)

      </details>
    - ✅ 1-1-0-5-3 The timer and the phase at frame 0 (`zero` removed; from one state after the press on the title)
    - 🚨 1-1-0-5-4 The machine after Start on the title meets the condition (`title.press` gone: proved from the machine at power-on and the inputs up to the press, for a press on frames 31 to 508 with no Start and no Select before it, for the first exit with earlier Start, and for the window after the first demo; new `title.boot`)
      - 🚨 1-1-0-5-4-1 Runs outside the class (Select before the press, a press after frame 2123, a reset) keep the condition (`press` of `title.boot`)
        <details><summary>3 lines of proved parts (the parent's own assumptions remain)</summary>

        - ✅ 1-1-0-5-4-1-1 A press on the menu's first frame (frame 31)
        - ✅ 1-1-0-5-4-1-2 The first exit from the title, with earlier Start (`menu`)
        - ✅ 1-1-0-5-4-1-3 The window after the first demo (frames 1657 to 2123, `later`)

        </details>
    - ✅ 1-1-0-5-5 Start before control (`title.noPause` removed; a search closed under any input, and `frame0Check`)
  - 🚨 1-1-0-6 Runs not in the theorem
    - 🚨 1-1-0-6-1 Runs that do not go through the two pipes
    - 🚨 1-1-0-6-2 Runs with a power-up
    - 🚨 1-1-0-6-3 Runs that die and start again
    - 🚨 1-1-0-6-4 Runs with the hurry-up music (not pursued further: the timer takes 300 × 24 = 7,200 frames from 400 to 100, far later than 1748)
      <details><summary>11 lines, not pursued further</summary>

      - ✅ 1-1-0-6-4-1 1-2 does not start before frame 1748 (under `start`, `bLe`, `noStore`, `clean`, `below`)
      - 🚨 1-1-0-6-4-2 The frame that starts the music (`start`, `bLe`, `noStore`, `clean`, `below`)
        - ✅ 1-1-0-6-4-2-1 It ends with the timer at 100 or less (`music` removed; by a walk of one whole frame)
        - 🚨 1-1-0-6-4-2-2 It is a real frame in control
          - ✅ 1-1-0-6-4-2-2-1 It begins in control (induction over the frames in control; none from frame 1)
          - 🚨 1-1-0-6-4-2-2-2 The start of frame `b`, `ctl` and `clean` on each frame
            - ✅ 1-1-0-6-4-2-2-2-1 The start of frame `b` (from the rows with tables; `start` asks exactly `ChangesK`)
            - 🚨 1-1-0-6-4-2-2-2-2 `ctl` and `clean` on each frame
              - ✅ 1-1-0-6-4-2-2-2-2-1 Each frame ends with control (`ctl` removed; a walk with the stores of the three bytes cut)
              - 🚨 1-1-0-6-4-2-2-2-2-2 `noStore` and `clean` on each instruction
        - 🚨 1-1-0-6-4-2-3 On the next frame the digits of `clock` are not above the machine's (`below`; one frame, was every frame)

      </details>
- 🚨 1-1-a To the pipe (0 → 368)
  - ✅ 1-1-a-1 Fast accel
  - ✅ 1-1-a-2 TAS fast accel
  - ✅ 1-1-a-3 The opening
  - ✅ 1-1-a-4 The condition to enter the pipe
  - 🚨 1-1-a-5 Assumptions of part a
    - ✅ 1-1-a-5-1 The entry on real frames: one pass of the foot check
    - ✅ 1-1-a-5-2 One whole frame: only that instruction writes the pipe's routine (the condition on each instruction: 1-1-a-5-10)
      <details><summary>2 lines of children, all ✅</summary>

      - ✅ 1-1-a-5-2-1 The state when an entering frame starts (`start` removed; from the induction of 1-1-a-5-5-3-2)
      - ✅ 1-1-a-5-2-2 Each instruction up to the write meets `Clean` (`clean` gone; from 1-1-a-5-10)

      </details>
    - 🚨 1-1-a-5-3 The pipe's right tile is only at its place (`tiles`)
    - 🚨 1-1-a-5-4 The bound on the opening's position (`openP`, `openB` gone)
      - ✅ 1-1-a-5-4-1 No bound up to frame N is needed (position at control, top speed)
      - ✅ 1-1-a-5-4-2 The bound at the end of frame N (if each frame is a model step)
      - 🚨 1-1-a-5-4-3 The first 32 frames are steps of the model
        - ✅ 1-1-a-5-4-3-1 `hstep` and the 16·v move (`move_model`, walk of `CtrlKeep`; `opening` gone)
        - ✅ 1-1-a-5-4-3-2 Air frames read from the player's state (`air` gone)
        - 🚨 1-1-a-5-4-3-3 Conditions on single frames (`map`, `after`, `afterV`; `noStore`, `longer`, `spare`, `st`, `spring` gone; `cleanK` from 1-1-a-5-10; `page` only at counted frame 33)
          - ✅ 1-1-a-5-4-3-3-1 No frame ends during the movement (`longer` gone; walk and `CleanK` time)
          - ✅ 1-1-a-5-4-3-3-2 The opening to the left (not left of position 0 in 31 frames)
          - ✅ 1-1-a-5-4-3-3-3 The jumpspring and the player's state (`spring`, `st` gone; a walk that knows the buffers, and `map` on each instruction)
          - 🚨 1-1-a-5-4-3-3-4 After the scroll handler and after the collision routine (`after`: 3 bytes, 2 more when the frame ends with the speed and the subspeed 0, the speed, the collision bits; `afterV`: 6 bytes; frame 32 may end at the left end)
          - ✅ 1-1-a-5-4-3-3-5 A frame that ends in control does not store the routine, the mode or the task (`noStore` gone; from `lags.ctl`)
        - ✅ 1-1-a-5-4-3-4 The ground's height and the jump lengths (`ground`, `jump` gone; new field `afterV`)
          <details><summary>1 lines of children, all ✅</summary>

          - ✅ 1-1-a-5-4-3-4-1 Flat ground (`flat`, `ground` gone; new field `afterV`; the read in the first buffer)

          </details>
    - 🚨 1-1-a-5-5 The frames after: read from the machines (`own`, `lags`)
      - ✅ 1-1-a-5-5-1 The frames follow each other, with the top speed (`next`, `speed` are theorems)
      - ✅ 1-1-a-5-5-2 The speed at control is 0 (`still` removed; from `title`)
      - 🚨 1-1-a-5-5-3 Frames not counted keep the speed and the position (`lags`)
        - ✅ 1-1-a-5-5-3-1 A frame that does not call the mode's routine (a pause) keeps them (`keeps_frame`)
        - 🚨 1-1-a-5-5-3-2 It starts in the idle loop; its instructions before the call are `Clean`
          - ✅ 1-1-a-5-5-3-2-1 It starts in the idle loop (`lags.start` removed; induction from control)
          - 🚨 1-1-a-5-5-3-2-2 Each counted frame up to the entry ends in control (`lags.ctl`; `lags.clean` gone: from 1-1-a-5-10; `one_le` a theorem; a frame not counted without the call: by the check)
          - ✅ 1-1-a-5-5-3-2-3 Stores before the call do not touch the speed and the position (`lags.store` removed; the walk knows each store's target)
        - ✅ 1-1-a-5-5-3-3 Frames not counted do not call the routine (`lags.game` gone)
          <details><summary>2 lines of children, all ✅</summary>

          - ✅ 1-1-a-5-5-3-3-1 A frame that ends paused does not call it (two walks)
          - ✅ 1-1-a-5-5-3-3-2 Frames not counted do not write the pause byte through an index (`lags.keeps` gone; part of `upCleanU` of 1-1-a-5-10)

          </details>
    - 🚨 1-1-a-5-6 Open flat ground, in the air only during a jump
    - 🚨 1-1-a-5-7 A jump's length depends only on the takeoff speed
      <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-a-5-7-1 Every jump of the model lands on the ground between the two lengths (`open_jump_check`)
      - ✅ 1-1-a-5-7-2 The vertical model on real frames (`vert` gone; `noStore` from 1-1-a-5-4-3-3-5)

      </details>
    - 🚨 1-1-a-5-8 The gain bound of the relaxed model (`GainBound`)
    - 🚨 1-1-a-5-9 The position at the foot check is the position at the end of the move (`edge`, `moved`)
      - ✅ 1-1-a-5-9-1 From the end of the move to the foot check the position does not change (`rule_on_framesS`)
      - 🚨 1-1-a-5-9-2 Up to the write: no store of the position at the screen's edge, no bump of a block with the head (`edge`)
      - 🚨 1-1-a-5-9-3 `P₂` is the position at the end of the move (`moved`, part of 0-0-0-3-1)
    - 🚨 1-1-a-5-10 One condition on each instruction from control to the entry (`chg.upCleanU`: `CleanK` of the union of the four guards, no `if`)
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
      - ✅ 1-1-b-3-4-1 The idle loop, the pipe's timer and 74 bytes from the title and the frames from control
      - 🚨 1-1-b-3-4-2 The other 35 bytes (`chg.entryRest₁`; the pause's bits, 19 bytes the pipe's frames do not use and the first square channel's effect queue gone)
        <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

        - ✅ 1-1-b-3-4-2-1 19 bytes the pipe's frames do not use (out of `Entry`, `entryDropped`)
        - ✅ 1-1-b-3-4-2-2 The first square channel's effect queue (out of `Entry`, `entryDropped`)

        </details>
      - ✅ 1-1-b-3-4-3 Each frame from control to the entry starts in control (`chg.upStart₁` is gone: by induction; `a₁` is the first frame without control)
      - ✅ 1-1-b-3-4-4 Each of its instructions is `Clean` (`chg.upClean₁` gone; from `upCleanU` of 1-1-a-5-10)
      - ✅ 1-1-b-3-4-5 The level's number at the entry (`area₁` gone; the press condition and the guard of `upCleanU` have one more byte)
    - 🚨 1-1-b-3-5 The conditions at places of the pipe's frames (`chg.places₁`)
    - 🚨 1-1-b-3-6 No pause after the pipe (`chg.noStart₁`)
    - 🚨 1-1-b-3-7 At the exit the pause queue is as the reference's, with the song and effects when silent, and the screen buffer is in the table (`chg.quiet₁`, `QuietRest`)
      <details><summary>3 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-b-3-7-1 Rows with the sound's bytes in tables (`Quiet ∧ Song` weakened to `QuietP`)
      - ✅ 1-1-b-3-7-2 The pause through the pipe's frames in 88 classes (`QuietP`'s pause part from `chg.pause₁`)
      - ✅ 1-1-b-3-7-3 At the entry the pause is not paused (`chg.pause₁` gone; the class is carried beside the frames from the title)

      </details>
    - 🚨 1-1-b-3-8 A `lag` frame ends paused (`chg.paused₁`)
    - 🚨 1-1-b-3-9 At the entry the game timer is not 000 (`chg.time₁`, `TimerOK`; at the exit it is proved); `b₁` is defined as the first control (`chg.ctlFirst₁` is gone); `left₁` not 0 before control is proved
      - ✅ 1-1-b-3-9-1 The pipe's frames do not change the game timer (`PipePause`'s walk with the digits)
      - 🚨 1-1-b-3-9-2 From `Rest` (measured: an invariant with the saved song holds; the guard must protect the digits and three music bytes)
    - ✅ 1-1-b-3-10 Bits 0–6 of the pause byte at the room's first control (`chg.pauseBits₂` gone; from the first change's rows)
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
      <details><summary>4 lines of children, all ✅</summary>

      - ✅ 1-1-c-7-1-1 `before`, `longer`, upper half of `far` in `clean` are theorems (the lower half of `far` is 1-1-c-7-1-3)
      - ✅ 1-1-c-7-1-2 The state at the player's routine (`at_ctrl`, `at_frame` but the values)
      - ✅ 1-1-c-7-1-3 The position stays at 8 px or more (`far` gone; new field `farNear`)
      - ✅ 1-1-c-7-1-4 A run that pauses in the room (`unpaused` gone; new field `roomLag`)

      </details>
    - ✅ 1-1-c-7-2 The state at first control (`start`, `startP0`, `startP1`, `v_start`, `ab_start`): from the change's rows
    - ✅ 1-1-c-7-3 The entry on real frames: one pass of the side check
    - 🚨 1-1-c-7-4 How the left wall stops him (`wall`, `late`, `stop_run`)
    - 🚨 1-1-c-7-5 The fall and the height of the feet (`stand_wall`, `low_at`, `read_stop`)
      <details><summary>20 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-c-7-5-1 A jump's first 8 frames follow `vstep` (the air part of `vframes`: two walks of the room's frames)
      - ✅ 1-1-c-7-5-2 The halt value and A of the frame before (`halt`, `prevA` gone: two walks of the room and the rows of the change)
      - ✅ 1-1-c-7-5-3 A landing is on a whole row with no speed (`stand_row` gone; the falling walk)
      - ✅ 1-1-c-7-5-4 The first fall (`fall_long`, `vfall`, `floor_at` gone)
      - ✅ 1-1-c-7-5-5 Frames that start standing (`vfall_stand`, `air_in` gone; `fall_stand` → `fall_jump`; new field `read_stop`)
      - ✅ 1-1-c-7-5-6 A jump from a stand during the fall (`fall_jump` gone: from `stand_first`, `stand_wall` and `wall`)
      - ✅ 1-1-c-7-5-7 The block buffer's column pointer (`RoomAddress`)
      - ✅ 1-1-c-7-5-8 The tile read and the return from the entry position (`RoomCollision`; the map at the read: 1-1-c-7-12-2; the link to the position after the move remains)
      - ✅ 1-1-c-7-5-9 The state before the landing is in the fall's layer, and the last step is the move or the landing (`RoomLanding`, without `land_at`; the link to the foot calls' entries remains)
      - ✅ 1-1-c-7-5-10 A foot call's entry and its map byte under a local check (`RoomFootPrefix`; `BIT` added to the walk)
      - ✅ 1-1-c-7-5-11 A small foot cut from the end of the move, and the room walk's control values (`RoomFootCut`)
      - ✅ 1-1-c-7-5-12 The landing frame of the first fall (`land_at` gone; the page and x at the end of the move are proved)
      - ✅ 1-1-c-7-5-13 The collision-disable flag and the vertical page in the first fall (`landQ` gone: the flag from the room's walk, the vertical page frame by frame)
      - ✅ 1-1-c-7-5-14 The floor frames after the fall (`vfloor` gone: the takeoff from the floor, and the stay on the floor from the foot check)
      - ✅ 1-1-c-7-5-15 A stand away from the floor ends with the speed 0 (`RoomWall`; conditions at the end of the move)
      - ✅ 1-1-c-7-5-16 The first stand of the fall does not follow `hstep` (`stand_first`; `stand_wall` only after an earlier frame in the state 0)
      - ✅ 1-1-c-7-5-17 On the floor the block's left side pushes him back (`low_floor_of`; `low_at` only off the floor past the corner)
      - ✅ 1-1-c-7-5-18 The vertical page through a jump (`low_jump_of`; `low_at` only at the heights 136 to 151 px)
      - ✅ 1-1-c-7-5-19 A frame above 152 px after a frame left of the corner (`move_top`; `low_at` only after a frame at or past the corner)
      - ✅ 1-1-c-7-5-20 A bound for each low frame (`lowB`; `low_at` only when every frame from C + 40 is at or past the corner)

      </details>
    - 🚨 1-1-c-7-6 The stored speed: proved on frames that follow the model; other frames before `C + 37` assumed (`ab_early`)
    - 🚨 1-1-c-7-7 Takeoff and landing (`Approach`)
    - 🚨 1-1-c-7-8 The ways off the block (`Off`)
    - 🚨 1-1-c-7-9 A jump over the whole block (`Over`)
    - ✅ 1-1-c-7-10 He does not bump his head: no frame of the room comes to the head's two places (`RoomMap`)
    - 🚨 1-1-c-7-11 Only the takeoff speed links the vertical motion to the horizontal: proved on every frame of a jump from the floor up to the landing (`vert_air`)
      <details><summary>1 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-c-7-11-1 A frame in the air follows `vstep` up to the landing (a third walk of the room)

      </details>
    - 🚨 1-1-c-7-12 The block map: the bits that are 0 in the map are 0 on every frame (proved, `RoomMap`); the numbers of the other fields are assumed
      <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-c-7-12-1 The bytes that are not coins in the map keep the map's value (`RoomBlocks`)
      - ✅ 1-1-c-7-12-2 The map's bytes stay at every instruction, and a real collision call returns them (`RoomCollisionMap`)

      </details>
    - 🚨 1-1-c-7-13 Standing during the fall (`facing`, `stand_fast`, `stand_P`)
    - 🚨 1-1-c-7-14 No run jumps from the wall and clears the block with no landing (`way`)
      <details><summary>3 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-c-7-14-1 A big player at the block's corner (`Approach.low` true for a big player too; his fast and later slow takeoffs proved)
      - ✅ 1-1-c-7-14-2 A big player's slow takeoff on C + 35 (`Approach.slowBig` gone: a table after the landing and a search from the room's first frame)
      - ✅ 1-1-c-7-14-3 The low frames of the first jump (`low_jump`; `Approach.low` only at or past the corner, off those frames)

      </details>
    - ✅ 1-1-c-7-15 The first machine is the change's (`roomCtl` removed: by definition)
    - ✅ 1-1-c-7-16 The write ends the side check (`pass`): proved by one whole frame (`SideFrame`)
    - ✅ 1-1-c-7-17 The pipe's tiles only in its column: `RoomMap` and the theorem `roomEnter`
    - ✅ 1-1-c-7-18 `P(E)` is at the mouth
      <details><summary>2 lines of children, all ✅</summary>

      - ✅ 1-1-c-7-18-1 The edge store and the head up to the write (`edgeE` gone)
      - ✅ 1-1-c-7-18-2 The position at the frame's end (two walks; `movedE` removed)

      </details>
- 🚨 1-1-d Back above ground (570 → 852)
  - ✅ 1-1-d-1 The length of the change (listed entry states)
  - ✅ 1-1-d-2-1 The bytes that decide the last 122 frames
  - ✅ 1-1-d-2-2 The first 160 frames (under the condition at the entry, any inputs)
  - ✅ 1-1-d-2-3 The last 122 frames (under the condition at the exit, no Start on the game core's frames)
  - 🚨 1-1-d-2-4 The screen stays on the first page, the entry has the long timer
    - ✅ 1-1-d-2-4-1 `Room` at the first control in the room: from the change's rows of the time (`chg.roomRest` removed)
    - 🚨 1-1-d-2-4-2 Each instruction in the room meets `SiteOK` (round 27: six fields; left: `roomLate`, `roomRead`, `roomErase`, `roomXbit`, `roomReads` through the screen pointer, `roomOff₆`)
      <details><summary>1 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-d-2-4-2-1 The parts of `SiteOK`: the offset from control 0 and the reads but the screen pointer's proved (`SiteParts`; `roomSites` gone)

      </details>
    - ✅ 1-1-d-2-4-3 Each frame up to the entry starts in the player's routine (from the definition of `a₂`)
  - 🚨 1-1-d-2-5 The 3 bytes at the entry (`chg.entry₂`; from 16). The rest are 3 music bytes that need the timer
    <details><summary>13 lines of proved parts (the parent's own assumptions remain)</summary>

    - ✅ 1-1-d-2-5-1 Five music bytes from the room's walk (the music bytes in a table)
    - ✅ 1-1-d-2-5-2 The routine at the entry, from the room's entering frame (out of `entry₂`; new field `dR_pos`)
    - ✅ 1-1-d-2-5-3 The level's number from the vertical pipe's entry (out of `entry₂`; `area₁` a theorem: 1-1-b-3-4-5)
    - ✅ 1-1-d-2-5-4 The height from the entering frame (a small and a big player; the size from the rows and the room's frames)
      - ✅ 1-1-d-2-5-4-1 A read near the mouth returns no coin, and the map's byte at a head read is in `SiteOK`'s head class (`EntryCollisionNear`; the eight ends at 192 px remain)
      - ✅ 1-1-d-2-5-4-2 A side read of the pipe at 192 px makes the head read break `SiteOK` (`EntryHeadHeight`; the link to the entering frame remains)
      - ✅ 1-1-d-2-5-4-3 The height for a big player (`EntryHeightBig`)
      - ✅ 1-1-d-2-5-4-4 The size through the room (`SizeKeep`; `height₂` gone)
    - ✅ 1-1-d-2-5-5 The screen buffer's 5 bytes from the entering frame (its field `buffer₂` is gone since round 26)
      - ✅ 1-1-d-2-5-5-1 The control through the room is 0 or 6 (`BufferControl`; `buffer₂` has to exclude only 6)
      - ✅ 1-1-d-2-5-5-2 From the control at 6 at 16 to 180 px no entry (`BufferCoin`; `buffer₂` asks only where a coin frame before the entry ends)
      - ✅ 1-1-d-2-5-5-3 A coin frame ends at 16 to 180 px (`BufferEnd`; `buffer₂` asks only page 0)
      - ✅ 1-1-d-2-5-5-4 A coin frame ends on page 0 (`BufferPage`; `buffer₂` gone)

    </details>
  - 🚨 1-1-d-3 Assumptions of part d
    - ✅ 1-1-d-3-1 `change₂` proved from `chg`
    - 🚨 1-1-d-3-2 A `lag` frame ends paused (`chg.paused₂`); that it keeps `left` is proved
    - 🚨 1-1-d-3-3 No pause after the pipe (`chg.noStart₂`; the song tables as unions of earlier rows would hold 920 states, measured)
    - ✅ 1-1-d-3-4 Bits 1–6 of the pause byte are 0 at the room's first control (`chg.pauseBits₂` gone, 1-1-b-3-10); `PauseE` at the entry (`pause₂` removed) and `QuietK` at the exit are proved
      <details><summary>4 lines of children, all ✅</summary>

      - ✅ 1-1-d-3-4-1 One CPU step writes only where its instruction stores (`StepWrites`; a walk carries the sound's bytes in a table)
      - ✅ 1-1-d-3-4-2 Rows that carry the sound's bytes in tables (`SideChangeSound`; `Quiet` weakened to `QuietK`)
      - ✅ 1-1-d-3-4-3 The pause through the pipe's frames, in 90 classes (`SidePause`; `chg.quiet₂` removed)
      - ✅ 1-1-d-3-4-4 The pause through the room's frames (`RoomPause`; `chg.pause₂` removed)

      </details>
    - 🚨 1-1-d-3-5 The game timer is not 000 at the side pipe's entry (`chg.time₂`; at the exit it is proved; it does not follow from the timer at the room's first control: measured); `left` not 0 before control is proved; `b₂` is the first control by definition
      <details><summary>1 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-d-3-5-1 The pipe's frames do not change the game timer (`SidePause`'s walk with the digits)

      </details>
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
    - ✅ 1-1-e-2-6 The frames follow each other (from `OnFrames.reads`)
    - ✅ 1-1-e-2-7 The left edge of the screen stopping him (`Frame`, `Hit`)
    - 🚨 1-1-e-2-8 One frame is `hstep` and the collision routine
      - ✅ 1-1-e-2-8-1 The movement is `hstep` (`move_model`, `one_of_moves`)
      - 🚨 1-1-e-2-8-2 The frame outside the movement (`moves`)
        - ✅ 1-1-e-2-8-2-1 The state at the player's routine (`at_ctrl`, `before`, `bits` gone; the walk of `CtrlKeep`)
        - 🚨 1-1-e-2-8-2-2 The frame's ends and after the scroll handler
          - ✅ 1-1-e-2-8-2-2-1 It comes to the routine (`arrive` gone; from `unpaused` and the walk)
          - ✅ 1-1-e-2-8-2-2-2 Frames not counted keep the 25 bytes (`lag` gone; from `lagPaused` and the walks)
          - 🚨 1-1-e-2-8-2-2-3 The values at the end of the frame before (`state`; area type, swimming, change of size, A of the frame before from the walk of the whole frame)
            - 🚨 1-1-e-2-8-2-2-3-2 The player's state and the jumpspring (every frame; map-dependent)
            - ✅ 1-1-e-2-8-2-2-3-1 A of the frame before (`prevA` gone; a walk with the paths cut at stores to the routine, mode, task)
          - 🚨 1-1-e-2-8-2-2-4 After the scroll handler (`after`; `longer`, `far` are theorems)
            - ✅ 1-1-e-2-8-2-2-4-1 The frame does not end during the movement (`longer` gone; from the walks and the time of `CleanK`)
            - ✅ 1-1-e-2-8-2-2-4-2 The position is far from the ends of its range (`far` gone; from the frames before and the position at control)
            - 🚨 1-1-e-2-8-2-2-4-3 After the scroll handler (`after`, the position moving right)
              - ✅ 1-1-e-2-8-2-2-4-3-1 Moving direction, running speed, stored speed (`md`, `rs` gone; `stored` is now `storedQ`)
              - 🚨 1-1-e-2-8-2-2-4-3-2 The position moving right (`AfterP.stop`), and the facing on frames 1 to 8 that end with speed 0 and subspeed 0 (`faceJ`)
                <details><summary>3 lines of proved parts (the parent's own assumptions remain)</summary>

                - ✅ 1-1-e-2-8-2-2-4-3-2-1 The stored speed at the scroll handler (`storedQ` gone; the friction's walk and one arrival)
                - ✅ 1-1-e-2-8-2-2-4-3-2-2 The facing (`AfterR.fd` gone; a walk that follows it, and `OneFrame` with a hit of its own; new `faceE`)
                - ✅ 1-1-e-2-8-2-2-4-3-2-3 The collision bits moving right (a walk that splits `X` and `Y`)

                </details>
          - ✅ 1-1-e-2-8-2-2-5 A counted frame ends not paused, a frame not counted ends paused (`unpaused`, `lagPaused` gone: the definition of the counted frames)
          - ✅ 1-1-e-2-8-2-2-6 Stores through an index do not write 4 bytes (`spare` gone: a part of `keep.cleanE`, 1-1-f-6-21)
          - ✅ 1-1-e-2-8-2-2-7 Stores through an index do not write 5 bytes (`spareE` gone: a part of `keep.cleanE`, 1-1-f-6-21)
      - ✅ 1-1-e-2-8-3 Frames whose pressed side is masked (`move_masked`, `one_of_movesM`)
    - 🚨 1-1-e-2-9 Frames 1 to 8 are `vstep` and the machine at control
      - ✅ 1-1-e-2-9-1 The movement routine is `vstep` (`vert_model`, `vert_of`)
      - 🚨 1-1-e-2-9-2 The rest of the frame keeps the vertical bytes
        - ✅ 1-1-e-2-9-2-1 Before the routine (`vBefore` gone; the walk and `moves`)
        - 🚨 1-1-e-2-9-2-2 After the scroll handler (`vAfter`, five vertical bytes)
          <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

          - ✅ 1-1-e-2-9-2-2-1 Four vertical bytes (out of `vAfter`; a walk that follows each; `vertE`)
          - ✅ 1-1-e-2-9-2-2-2 The vertical force (out of `vAfter`; a walk that follows it, and a model that allows the jumpspring's value on the ground; new `stateE`)

          </details>
      - 🚨 1-1-e-2-9-3 The collision routine as on the machine at control (`box`)
    - 🚨 1-1-e-2-10 Frames are read from machines (`reads`, `fr` gone; `fr` is the definition `frOf`)
      - ✅ 1-1-e-2-10-1 Each frame is a `TopSpeed.Frame` (`frame_readE`)
      - ✅ 1-1-e-2-10-2 The collision bits are one of four values (`coll` gone: a walk with `X` split at `ImpedePlayerMove`; new `spareC`)
      - 🚨 1-1-e-2-10-3 The position after the scroll handler, and the subspeed on frames that end with speed 0 and subspeed 0 (`collide`, `CollideS`, `posW`, `clampR`, `OnFrames.near` (`NearX`))
        <details><summary>14 lines of proved parts (the parent's own assumptions remain)</summary>

        - ✅ 1-1-e-2-10-3-1 The speed after the scroll handler (a walk that follows the speed; `spareV` is a part of `keep.cleanE`)
        - ✅ 1-1-e-2-10-3-2 The subspeed on the other frames (a walk that follows it)
        - ✅ 1-1-e-2-10-3-3 The position and the return of one collision push (`ImpedePosition`; the link to the whole frame remains)
        - ✅ 1-1-e-2-10-3-4 The screen edge's clamp and its return (`ScreenClamp`; the relation of the screen's edge to the position at the frame's start remains)
        - ✅ 1-1-e-2-10-3-5 The sum of the effects on the position (`PositionPieces`; the frame's cuts and the clamp's bound remain)
        - ✅ 1-1-e-2-10-3-6 Position cuts from local entry conditions (`PositionDispatch`; coverage and the screen edge's relation remain)
        - ✅ 1-1-e-2-10-3-7 The position's writers and `Ready` at every cut (`PositionWriters`; conditions on single instructions remain)
        - ✅ 1-1-e-2-10-3-8 Position on frames that keep a right speed or make no call (`AfterP.keep` gone; new `posW`, `clampR`)
        - ✅ 1-1-e-2-10-3-9 The clamp comes before the pushes, at most once (the number of pushes remains)
        - ✅ 1-1-e-2-10-3-11 The screen's left edge at control (`edge₀` is gone)
        - ✅ 1-1-e-2-10-3-12 The scroll's rule (used by the route since round 26)
        - ✅ 1-1-e-2-10-3-13 The edge's step of a frame (`edge` is gone; new `near`)
        - ✅ 1-1-e-2-10-3-14 The platforms' force on the scroll (`near` asks `NearX`)
        - ✅ 1-1-e-2-10-3-15 His place at the player's routine (not used by the route yet)

        </details>
        - 🚨 1-1-e-2-10-3-10 The push's bound from the screen's left edge (`collide` fixed in round 24 after it was found false, assumed; `edge₀` is a theorem since round 25 and `OnFrames.edge` since round 26)
      - ✅ 1-1-e-2-10-4 A touch after frame 745 (`farLate` gone: the bound from the count of frames, `SurfaceLate`)
      - ✅ 1-1-e-2-10-5 No instruction writes the collision bits through an index (`spareC` gone: a part of `keep.cleanE`, 1-1-f-6-21)
      - ✅ 1-1-e-2-10-6 No instruction writes the speed through an index (`spareV` gone; a part of `keep.cleanE`, 1-1-f-6-21)
- 🚨 1-1-f The flag (1085 → 1218)
  - ✅ 1-1-f-1 The bound on the push back
  - ✅ 1-1-f-2 The height of a jump
  - ✅ 1-1-f-3 The condition for a fast jump
  - ✅ 1-1-f-4 The length from the touch to the castle
  - ✅ 1-1-f-5 Joining parts e and f
  - 🚨 1-1-f-6 Assumptions of part f
    - ✅ 1-1-f-6-1 The touch on real frames: one pass of the side check
    - ✅ 1-1-f-6-2 No castle flag up to the touch (`noCastle` removed; from the change's rows and the walk)
    - 🚨 1-1-f-6-3 The path of the jump (`path`, `atY`, `atRising`; the machine's takeoff and air steps proved under `VEnd`, `PoleJump`)
    - 🚨 1-1-f-6-4 He comes from the left and falls below the base's top (`order`, `left`, `air`)
    - 🚨 1-1-f-6-5 One frame of the fall (`fall`)
    - 🚨 1-1-f-6-6 The map near the flag (the premise of `fall`)
    - 🚨 1-1-f-6-7 Frames beside the base follow the collision (`land`, `hop`)
    - 🚨 1-1-f-6-8 The speed after a push to the right (`mask`)
    - 🚨 1-1-f-6-9 The frames before a fast jump (`reads`; `stopped`, `onGround`, `ground` gone)
      <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-f-6-9-1 The stored speed read from the machines (`stopped`, `onGround` gone)
      - ✅ 1-1-f-6-9-2 The frames between the landing and a fast jump (`ground` gone; no new field)

      </details>
    - 🚨 1-1-f-6-10 The length after a slow jump's grab (`flagAny`, `flagTight`)
    - 🚨 1-1-f-6-11 The length after another touch (`other`)
    - 🚨 1-1-f-6-12 The same for every input after the touch (`GMerge`)
    - ✅ 1-1-f-6-13 The position's fraction is a multiple of 1/16 px (from `fracStep`)
    - 🚨 1-1-f-6-14 No enemy near the flag
    - 🚨 1-1-f-6-15 He does not go over the flag and come back
    - ✅ 1-1-f-6-16 Only that instruction writes the routine (`pass` removed; the walk of the whole touch frame, `PoleFrame`)
    - 🚨 1-1-f-6-17 The pole's tiles: stores and reads (`bufAll`, `keepB`, `tilesCol`; `tiles`, `tilesRead`, `ySide`, `tilesFar`, `yKeep` gone)
      <details><summary>8 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-f-6-17-1 `TileRead` at an actual load from a frame-start tile condition (`PoleTiles`; the write checks and the read range remain)
      - ✅ 1-1-f-6-17-2 `TileRead` from the map at control (`PoleTileWalk`; `tiles` gone; new fields `bufAll`, `tilesRead`)
      - ✅ 1-1-f-6-17-3 The reads near the pole are in the block buffers (`PoleTileRead`; `tilesRead` gone; new fields `ySide`, `tilesFar`)
      - ✅ 1-1-f-6-17-4 The height at the side check (`PoleTileHeight`; `ySide` gone; new field `yKeep`)
      - ✅ 1-1-f-6-17-5 The reads far from the pole are in the block buffers (`PoleTileFar`; `tilesFar` gone; new field `tilesCol`)
      - ✅ 1-1-f-6-17-6 The height kept inside the collision routine (`PoleTileKeep`; `yKeep` gone; new field `keepB`)
      - ✅ 1-1-f-6-17-7 The stores that `keepB` and `bufAll` still speak of (`PoleKeepFar`; the same condition per instruction)
      - ✅ 1-1-f-6-17-8 The area parser against the screen's left edge (`PoleParser`; the invariant at control and the first half of a frame)

      </details>
    - 🚨 1-1-f-6-18 The edge store does not bring him into the range (`edge`); `P₂(g)` is the position at the end of the move (`moved` removed: 1-1-f-6-18-2)
      <details><summary>2 lines of proved parts (the parent's own assumptions remain)</summary>

      - ✅ 1-1-f-6-18-1 The walk follows the head bump with the position kept (the head is gone from `edge`; new field `posKeep`: only the player's move writes the position through an index)
      - ✅ 1-1-f-6-18-2 A frame in control comes to the end of the move at most once (`moved` removed; two walks that do not cut the write)

      </details>
    - ✅ 1-1-f-6-19 Each frame moves the position by a multiple of 1/16 px (one whole frame by the walk, from `keep`)
    - 🚨 1-1-f-6-20 The frames up to the touch are real frames in control
      - ✅ 1-1-f-6-20-1 Each frame starts in control (`start` removed; from the walk and `ctl`)
      - 🚨 1-1-f-6-20-2 The frames before the touch write no routine, mode or task byte by its address (`noStore`, the `lag` frames too; ending in control is the theorem `Frames.ctlAll`)
      - ✅ 1-1-f-6-20-3 The link of the frames, and the `lag` frames (`ends`, `lag`, `lagStart` removed; from the list of all frames and the walk)
    - 🚨 1-1-f-6-21 Each instruction of those frames (`keep.cleanE`, `CleanK` with 18 more bytes, the `lag` frames too)
    - ✅ 1-1-f-6-22 The frames from the touch to the castle are real frames too (`seq`, `seqAt` removed; `c` is a counted frame: `toCastle`)
- 🚨 1-1-g From the castle to 1-2 (1218 → 1748)
  - ✅ 1-1-g-1 The timer and the grid
  - 🚨 1-1-g-2 Assumptions of part g
    - ✅ 1-1-g-2-1 Each frame follows the star flag's rule (`step`)
    - 🚨 1-1-g-2-2 The condition at the entry (`Good` at the frame `G` where the area parser is done, task 2, flag height)
      - ✅ 1-1-g-2-2-1 Runs touching at other heights are in `Good` too (the floating number, the score, Mario's x and the screen's x widened)
      - 🚨 1-1-g-2-2-2 Rows from the touch's end to the castle (measured only; 295 s with Start)
      - 🚨 1-1-g-2-2-3 The castle entry with the parser at work (`G`, `pre`; `pre` is a hypothesis)
    - 🚨 1-1-g-2-3 The same for every input (`GMerge`)
    - ✅ 1-1-g-2-4 The level changes on a frame with task 5 (`task_L`)
    - ✅ 1-1-g-2-5 The pause after the castle entry (`flag.noStart` is gone: a frame that ends paused keeps the counters)
- 🚨 0-0-0 Common
  - ✅ 0-0-0-1 The top speed bound
  - ✅ 0-0-0-2 Reach
  - 🚨 0-0-0-3 Common assumptions
    - 🚨 0-0-0-3-1 Real frames have the form of `Frame`: `frame_read` (`ReadFrame` remains)
    - ✅ 0-0-0-3-2 `hstep` and `vstep` are the horizontal and vertical parts of one frame (`move_model`, `vert_model`)
    - 🚨 0-0-0-3-3 Only the 5 checked routines write the speed and position: proved in the movement (`before`, `after`, `collide` remain)
    - 🚨 0-0-0-3-4 Each routine depends only on the checked bytes: proved in the movement; for `ImpedePlayerMove` from the call to the return (1-1-e-2-10-3-3), the link to the whole frame remains
    - 🚨 0-0-0-3-5 Runs that press Start or Select
    - 🚨 0-0-0-3-6 The emulator is the same as the real machine
