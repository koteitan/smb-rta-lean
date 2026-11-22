[← Back](README.md) | [English](0-1-Route.md) | [Japanese](0-1-Route-ja.md)

# The whole of 1-1: 1-2 does not start before frame 1748

**Statement.** If a run satisfies every assumption of `Run`, the frame `L` on which 1-2 starts has `L ≥ 1748 + j`. `j` counts the frames on which no timer runs, other than one in each change of area. The TAS has `j = 0` and `L = 1748`.

**This is a theorem with assumptions.** The assumptions of `Run` are not proved for every run. This page is the list of them.

Frames are numbered from the first controllable frame of 1-1. `E` counts all frames. `E_a`, `C_r`, `E_b`, `C_s`, `g`, `c` count frames without the `lag` frames (the frames counted by `j`).

```
P₁ = E_a                 the frame he enters the vertical pipe
X₁ = C_r − E_a           the change into the room
P₂ = E_b − C_r           control in the room to the side pipe
X₂ = C_s − E_b           the change above ground
P₃ = g                   control above ground to the touch of the pole
W  = c − g               the touch to the castle
E  = C_s + c + j         the frame he enters the castle
T                        the timer at E
c_E                      the interval timer's phase at E
```

How the theorems join:

```
P₁ ≥ 368                                                       pipe_no_entry (part a)
X₁ ≥ 91                                                        Run.change₁ (part b, from single frames)
P₂ ≥ 111                                                       room_join (part c)
X₂ ≥ 282                                                       Run.change₂ (part d, from single frames)
(g ≥ 234 ∧ W ≥ 132) ∨ (240 ≤ g ≤ 241 ∧ W ≥ 126) ∨ (g ≥ 242 ∧ W ≥ 125)    pole_touch_castle (parts e, f)
E = P₁ + X₁ + P₂ + X₂ + P₃ + W + j                             Run.hE (from the rule of clock)
401 ≤ T + ⌈P₁/24⌉ + ⌈P₂/24⌉ + ⌈P₃/24⌉                          Run.hT (from the rule of clock)
─────────────────────────────────────────
E + T ≥ 1588 + j                                               sum_ge
(c_E + E) mod 21 = (3 + j) mod 21                              Run.hc (from the rule of clock)
E + T + D + 107 + ((c_E − T − D) mod 21) ≤ L,  D ≥ 33          Run.hD, Run.hL (from the rule of flag)
─────────────────────────────────────────
L ≥ 1748 + j                                                   level_ge_of_parts
```

Lean: `Run`, `Base`, `Changes`, `Run.pipeStart₁`, `Run.pipeKeep₁`, `Run.pipeOne`, `Run.roomCtl`, `Run.roomEnter`, `Run.atCtl`, `Changes.b₁_lt_a₂`, `Run.change₁`, `Run.change₂`, `Run.hE`, `Run.hT`, `Run.hc`, `Run.zero`, `Run.still`, `Run.s_zero`, `Run.ph_zero`, `Run.hD`, `Run.hL`, `Run.start`, `Run.atCtl₀`, `Run.entry₁`, `Run.upStart₁`, `Run.pipeStart₁`, `Run.roomStart`, `Run.inRoom`, `Changes.roomAt`, `RoomChecks` and `level_ge_of_parts` in `Theorems/Route.lean`, and the private `route_1_1`. `#print axioms route_1_1` shows no `sorryAx`; it shows the axioms of `native_decide`.

## The assumptions

All are fields of `Run`, so none is hidden. The page of each part explains its fields.

| part | field | what it says | checked on |
|---|---|---|---|
| a | `pipe.enter`, `tiles`, `edge`, `moved` | an entering frame is on real machines, those of `base` (the counted frame `t` is the `t`-th frame of `base` that ends not paused, a definition; that it starts in control is proved: `Pipe.startE`, `Run.pipeStart₁`); each instruction up to the write is `Clean` (`Run.pipeClean`, from `chg.upCleanU`), each read of the right foot `TilesOK`; up to the write it neither stores the position at the screen's edge nor bumps a block with the head; `P₂` is the position at the end of the move (`PlayerSubs`) | 68,311 real frames, 177 entries ([One whole frame: who writes the routine byte](a-5-2-PipeWrites.md), [The position at the end of the move](a-5-9-MoveEnd.md)) |
| a | `pipe.opening` | conditions on each of the first 32 counted frames (`RealB`: `map`, `after`, `afterV`, `page`; `noStore` is the theorem `Real.noStore`, from `lags.ctl`; `after` asks 3 bytes, the facing and the subspeed when the frame ends with the speed and the subspeed 0, the speed not set to 0 and the collision bits, or on frame 32 the screen's left end; `afterV` asks 6 bytes; `CleanK` of `guardE` on each instruction is `Run.pipeReal`, from `chg.upCleanU`; the vertical model, the flat ground, the ground's height and the jump lengths are the theorems `Real.vertOK`, `Real.flat`, `Real.ground_all`, `Real.jumpV`); that each is a step of the opening's model is proved from them (`move_model`, the walk of `CtrlKeep`), and the bound at the end of frame 32 too (`Run.pipeOpenB`) | 32 TAS frames, 9,600 frames of 300 own runs, 1,856 frames of 60 runs that pause early ([The opening on real frames](a-5-4-OpenFrames.md)) |
| a | `pipe.own` | the frames 1 to `E` are read from their own machines; the speed at control is 0 is proved (`Run.still`) | 434,206 real frames ([The frames up to the pipe, read from the machines](a-5-5-PipeFrames.md)) |
| a | `pipe.lags` | the counted frames are the frames of `base` that end not paused (a definition), and no pause from frame 1 to the entry lasts `dP` frames (`lags.resume`); each counted frame ends in control. Each instruction of every frame from control to the entry, counted or not, is `Clean` and does not write the pause byte through an index or a pointer: `Run.lagsClean`, from `chg.upCleanU`. Proved: each frame starts in the idle loop (`Lags.starts`), and a frame not counted does not call the mode's routine, keeps the three values and ends in control (`lag_check`, `pause_check`) | 193,149 real frames, 134 entries ([Every frame from control to the pipe starts in the idle loop](a-5-5-3-2-StartRun.md)), 167,271 real frames not counted in scope ([Frames not counted, up to the pipe](a-5-5-3-LagFrames.md)), 51,711 frames not counted ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)) |
| b | `base.dA`, `dB`, `chg.ha₁`, `hb₁`, `ctlBy₁` | which machines of `base.seq` are the entry and control; `a₁` is the first machine from frame 1 on without control (a definition, `Base.a₁`; `dA` bounds it); `b₁` is the first machine from `a₁` on with control (a definition, `Base.b₁`; `dB` bounds it; `ctlBy₁`: control at `a₁ + dB`); `ha₁`, `hb₁`: the counts without `lag` at `a₁`, `b₁` | `route-check` on the two runs below |
| b | `chg.entryRest₁` | at the entry: the 35 bytes of `EntryKeep.restNames` (the idle loop, the pipe's timer and the other 74 bytes come from `title`, `Run.upClean₁`: `Run.entry₁`; that each frame starts in control is proved by `Run.upStart₁`) | 437 entries ([The change into the room without `fall`](b-3-2-PipeChangeEnd.md), [The state at the vertical pipe's entry, from the title](b-3-4-EntryKeep.md)) |
| a, b | `chg.upCleanU` | each instruction of the frames from control to the vertical pipe's entry meets `CleanK` of one guard, the union of four: `EntryKeep`'s (the 73 bytes of `EntryKeep.held`, the level's number and the size's bits among them, the pipe's timer and the six bytes of the pause), `guardP` and `guardE`; 147 bytes in all (round 26: the screen's left edge; round 27: the platforms' force on the scroll). It is a plain `CleanK` (the ROM fact `qCheck` is one of `EntryKeep.Checks`). The four old conditions are theorems: `Run.upClean₁`, `Run.lagsClean`, `Run.pipeClean`, `Run.pipeReal` ([One condition on each instruction up to the pipe](a-5-10-UpClean.md)) | 221,490 real frames, 40 entries; a run that fills some object slots through an index before the entry is outside the theorem |
| b | `chg.places₁` | on the pipe's frames, at each place of the table, the dot is under the bound and the machine has a row of the place | every frame of the pipe of 437 runs, three kinds of inputs. Not proved |
| b | `chg.quiet₁` | at the exit the pause sound's queue is as at the reference, and when silent the two effects and the song's row (`QuietRest`); the screen buffer has a form of the table; the pause sound's kind comes from `PauseV` at the entry (the theorem `Run.entry₁`) ([The pause through the vertical pipe's frames](b-3-7-2-PipePause.md)) | 1,002 exits with Start at random: 961 (the other 41 unpause on the exit's frame) |
| b | `chg.noStart₁` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| b | `chg.paused₁` | a `lag` frame of the change ends paused (the low bit of `GamePauseStatus` is set) | 995 + 823 `lag` frames with Start, pauses on the TAS ([A `lag` frame of the change into the room](b-3-3-LagPaused.md)). Not proved |
| b | `chg.time₁` | at the vertical pipe's entry the game timer is not 000 (`TimerOK`; the pipe's frames keep it to the exit: [The game timer at the vertical pipe](b-3-9-1-PipeTime.md)); `b₁` is the first control by its definition; that `left₁` is not 0 before control is proved | 15 entries × 3 kinds, 615 runs, the TAS ([The change into the room without `fall`](b-3-2-PipeChangeEnd.md)); it fails with a pause in the pipe, where `quiet₁` fails too |
| c | `room` | the frames in the room: each frame is `CleanW` (at the player's routine the stored speed is `\|v\|` and the side is not masked; `after`), or stops him and is `ReadW` (the collision bits in `collBits`; `Collide`); the rest of `CleanR`/`ReadR` is proved (the room's walks, the frame's time, the position's range); a frame between them that ends paused keeps the bytes the model reads (`Run.roomKeep`, proved); the first fall up to the first stand and the frames that start standing are proved (`fall_long`, `vfall`, `floor_at`, `vfall_stand`, `air_in` are gone), a jump from a stand during the fall is proved from the first stand (`stand_first`) and `wall`, and `stand_wall` asks only a stand after an earlier frame in the state 0, from `C + 34` on only with no jump since (1-1-c-7-5-22), `stand_P` is gone and `stand_fast` is asked only on a stand that follows `hstep` or after an earlier stand (1-1-c-7-13-3, 1-1-c-7-13-4); `stop_run` only from `C + 34` with `RunningSpeed` 0 at the start, `late` only after an earlier wall hit (1-1-c-7-4-1) (`fall_jump` is gone), and the frame that lands on the floor is proved: the collision-disable flag and the vertical page at the end of its move too (`landQ` and `land_at` are gone); the floor frames after the fall are proved: a takeoff from the floor, or a stay on the floor that the foot check at the end of the move gives (`vfloor` is gone); the input of a frame where a side stops is read at the player's routine (`read_stop`); the floor frames at the block's left side are proved (`low_floor_of`), so are the jump frames at or below 152 px (`low_jump_of`) and, since round 28, those from 136 to 151 px (`push_one`, the least slack `lowT`, `riseCheck`): `low_at` is gone (1-1-c-7-5-19, 1-1-c-7-5-20, 1-1-c-7-5-21); `facing` is gone: a walk of the room's whole frame that follows the facing from the player's routine proves it on every frame (`InRoom.face`, `Run.roomFace`; 1-1-c-7-13-1, 1-1-c-7-13-2); `Approach.low` lets a big player's last low frame be past the corner and is asked only at or past the corner, off the frames that `low_jump` proves (1-1-c-7-14-3); his fast and slow takeoffs are proved (1-1-c-7-14-1, 1-1-c-7-14-2); a frame that starts between 8 px and 11.5 px ends at 8 px or more (`farNear`); the frames, the vertical state and the stored speed are read from machines (`read_vs`, `read_ab`); the entry frame enters on the real machines (`enters`); `P(E)` is read at the frame's end (`read_PE`); the position there comes from the walks `SideEntryEnd`, `SideEntryRest`; its start (with the screen's bytes), `Clean`, tiles and no head's collision come from `RoomMap` through `Run.roomEnter`. The room's machines are those of `base` from frame `b₁` on (a definition: frame `n` ends at `seq(b₁ + ix(n − C))`, where `ix(j)` is the `j`-th `k ≥ 1` with `seq(b₁ + k)` not paused), so its first machine is the machine at control in the room (`Run.roomCtl`), and its entering frame is the frame `b₁ + ix(E − C) − 1` of `base` (`Run.roomEnter`) | the TAS and real runs ([Joining the bonus room](c-5-RoomJoin.md), [A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md)) ([The block map in the room](c-7-12-RoomMap.md), [The side pipe's entry: one whole frame](c-7-16-SideFrame.md)) |
| c | `roomLag` | in the room (`b₁ ≤ n < a₂`) a frame that ends paused is a `lag` frame of `clock` | 57 movie runs with a pause in the room (3,268 frames), 40 runs of own inputs ([A run that pauses in the room](c-7-1-4-RoomLag.md)) |
| d | `base.dR`, `d₂`, `chg.ha₂`, `hb₂`, `ctlBy₂` | `a₂` is the first machine after `b₁` that has left the player's routine, `b₂` the first with control after it (definitions, `Base.a₂`, `Base.b₂`); bounds on the frames to them (`dR_pos : 1 ≤ dR`); the counts without `lag` at `a₂`, `b₂` | `route-check` on the two runs below |
| d | `chg.entry₂` | 3 bytes at the entry are as in a reference (the area music's buffer, the event music's queue, the added note length); the level's number comes from the vertical pipe's entry (`Run.area₂`, from the theorem `Run.area₁`); the height and the five bytes of the screen's buffer come from the entering frame (`Run.y₂` with the size of `SizeKeep`, `Run.buf₂` from `Run.ctl₂`, `Run.coin₂` and `Run.end₂`: the field `buffer₂` is gone since round 26, 1-1-d-2-5-5-4); five music bytes come from the room's frames (`RoomMusic.entryRest_of`); the routine comes from the room's entering frame (`Run.rt₂`); the room gives the rest (`ScreenPage.entry_rest`) | the walk of every frame in the room knows 78 of the 90 bytes of `Entry2` at the end of the entry frame ([The screen's page in the room, and the long timer](d-2-4-ScreenPage.md)) |
| d | `chg.roomLateU`, `roomLateS`, `roomRead`, `roomErase`, `roomXbit`, `roomReads`, `roomOff₆` | three parts of `SiteOK` on each instruction in the room (the tile read, that a coin's erase writes before the block buffers' end, the position's low bits at the side pipe's read; round 30: that the erase writes in the RAM at or past the block buffers' start is proved); for the time (`Late`) only that the loops' back jumps run at dot 9,000 or earlier: those of the screen update's loop over the records and of the sound routine on the room's first frame and the frames after a frame from the control of the screen's buffers at 6, those of the sound routine on the other frames (round 29: [The time of the room's frames](d-2-4-2-3-RoomLate.md); round 30: [The time from the loops' back jumps](d-2-4-2-4-LoopTime.md)); `Reads` only through the screen update's pointer into the screen's buffer and only on the room's first frame and the frames after a frame from the control of the screen's buffers at 6, and `Off` only on the frames that start with the control at 6 after a frame that starts with it at 6: the rest of `SiteOK` is proved (`Run.roomSites`, round 27: [The parts of `SiteOK`](d-2-4-2-1-SiteParts.md); round 28: [The screen buffers' records](d-2-4-2-2-BufferRecords.md)); `Room` comes from the rows of the time of the first change (`Changes.roomAt`), and that he stays in the player's routine up to the entry from the definition of `a₂` | 130,030 real frames and overwritten runs ([The screen's page in the room, and the long timer](d-2-4-ScreenPage.md)); own runs ([The parts of `SiteOK`](d-2-4-2-1-SiteParts.md)); `LateS`: 107,546 own frames and the movie's 111, the sound routine done by dot 7,159 ([The time of the room's frames](d-2-4-2-3-RoomLate.md)); the back jumps: 1,156,371 own frames and the movie's 111, by dot 7,463 ([The time from the loops' back jumps](d-2-4-2-4-LoopTime.md)) |
| d | `chg.noStart₂` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| d | `chg.paused₂` | a `lag` frame of the change ends paused | 46,829 frames of 264 runs with Start on the pipe's frames ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)). Not proved |
| d | `chg.time₂` | the game timer is not 000 at the side pipe's entry (the pipe's frames keep it to the exit: [The game timer at the side pipe](d-3-5-1-SideTime.md)) | 210 real entries, 132 real runs and 75 with Start ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)); that `left₂` is not 0 before control is proved |
| e, f | `pole` | the one-frame form above ground (`frames`), the collisions near the base, the frame that touches the pole (`touches`, `posKeep`, `bufAll`, `keepB`, `tilesCol` (`tiles` is gone: 1-1-f-6-17-2; `tilesRead` is gone: 1-1-f-6-17-3; `ySide` is gone: 1-1-f-6-17-4; `tilesFar` is gone: 1-1-f-6-17-5; `yKeep` is gone: 1-1-f-6-17-6; `keepB` and `bufAll` are stated only for the stores the program does not settle: 1-1-f-6-17-7; round 29: `tilesCol` asks `TileSlot` in place of `TileCol` (it asks more where no pole's tile is read), and `TileCol` is a theorem from the area parser's invariant on the frames, with the new field `parWrap`; the edge's bound there is a theorem: 1-1-f-6-17-10; round 30: `TileSlot` asks the column of the read only on the page two before the pole's, and `parWrap` is asked only of a frame that comes to the player's routine: 1-1-f-6-17-11), `edge`; `moved` is the theorem `Run.moved`; `keep.noStore`: the frames before the touch write no routine, mode or task byte by its address; the last frame of `keep`, the walk of the whole frame `PoleFrame`), the castle flag; the frames up to the castle are counted frames of `base` by definition (`toCastle`); `keep.cleanE`: each instruction meets `CleanK` of `guardE` (`frames.spareE` is gone; round 26: `guardE` also protects the screen's left edge; round 27: and the platforms' force on the scroll; round 29: and the area parser's four bytes). The frames above ground are the definition `frOf` on the machines (`fr` and `frames.reads` are gone), with the fields `state`, `collide` (`CollideS`; its third case bounds a push to the right from the base, the larger of the frame's start and the screen's left edge, with the fields `OnFrames.rightRel` and `OnFrames.endKeep` (round 30: at the routine of the offscreen bits the right edge is 255 px right of the left edge; after the scroll handler's return his pixel stays on frames that call the push or the clamp, and the drawing writes his place byte; `OnFrames.nearStep` is the theorem `OnFrames.nearStepAt`: 1-1-e-2-10-3-18; round 29: each counted frame keeps `NearM` from its start to its end; `OnFrames.nearA` is the theorem `OnFrames.nearAAt`: 1-1-e-2-10-3-17; round 28: the old field `OnFrames.near` is the theorem `OnFrames.nearAt`: 1-1-e-2-10-3-16; round 27: the platforms' force is 0, 1-1-e-2-10-3-14; the old fields `OnFrames.edge₀` and `OnFrames.edge` are the theorems `SurfaceFrames.edge_zero`: 1-1-e-2-10-3-11, and `OnFrames.edgeAt`: 1-1-e-2-10-3-13); round 23 found the old form, from the frame's start, false on a real frame that starts 1 px left of the screen's left edge, and round 24 fixed it: 1-1-e-2-10-3-10; the position is asked only of a frame that calls the push or the clamp; on a frame that moves right and keeps its speed, and on a frame with no call, it is the theorem `OnFrames.keepAt`, `OnFrames.stillAt`), `posW`, `clampR` (conditions on single instructions after the scroll handler: the position is stored by its address only inside the push and the clamp, and outside them a store through an index or a pointer writes no byte of the position; on a frame that moves right and keeps its speed, when he moves right at the clamp, the clamp's target is his position), `moves` (`Moves.stop`, only on a frame that ends at P(Q) since round 28; `AfterP.stop` is the theorem `Moves.stopP`; `AfterP.keep` is the theorem `OnFrames.keepAt`: 1-1-e-2-10-3-8), `faceJ`, `vAfter` (five vertical bytes), `box` of `frames` (`coll` and `farLate` are gone; `spareC` and `spareV` are parts of `keep.cleanE`; four bytes of `vAfter` are the theorem `OnFrames.kAt` and the vertical force is `OnFrames.vfAt`; the facing, the subspeed and the collision bits moving right after the scroll handler are theorems of `FaceKeep`; a touch after frame 745 is bounded by the count of frames: `SurfaceLate`). Its frames up to the touch are those of `base` from frame `b₂` on (a definition in `keep`: `all n = seq(b₂ + n)`), so its first machine is the machine at control (`Run.atCtl`). Before a fast jump the stored speed is read from the machines (`Run.stop_step`, `Run.stored_step`; `stopped`, `onGround`, `ground` are gone); `reads` stays | real runs ([Above ground: the frames from control, one by one](e-2-SurfaceFrames.md), [Touching the pole on real frames](f-6-1-PoleEntryRule.md), [From control to the castle](f-5-PoleJoin.md)) |
| all | `clock`, `z₁`, `z₂` | the kind and the counters of every frame: the rule on one frame, and which frame is in which part | every frame of 7 runs, one with pauses, and of the TAS ([From the castle to 1-2](g-1-CastleToLevel.md)) |
| all | `title` | the press of Start on the title (`title.boot`): the run comes from power-on (one state: the machine at power-on, its RAM not known, without the mark of a warm boot or with two bytes 0; no Start and no Select before the press; Start, with A or not, on a frame from 31 to 508; `power`), or the first exit from the title on a frame from 31 to 508 with Start allowed before it and no Select (`menu`), or a press on a frame from 1657 to 2123 after the first demo (`later`), or the machine after the frame of the press is in the idle loop with 51 bytes that the run reads before it writes them, the pause sound's buffer and the level's number, those of a reference machine, and the flag that makes the game load the timer not 0 (`press`). In the first three cases that condition is proved (`TitleStart.Begin.press`). No Start on frame 0 in the game core (Start before it may pause the game). Frame 0 is the frame before the first control. From these, frame 0 begins with the timer at `t0` and the phase 2, and the speed at control is 0 (`Run.zero`, `Run.still`; these two do not use the condition on frame 0) | the TAS and 339 real runs: Start after any frames of the title, any buttons on the title, A with Start, pauses in the game core, the title after a game over, a reset during a game (`title-check`); from power-on 566 runs of the first class, 600 with Start before the exit, 100 after the first demo (`title-boot-check`, `title-menu-check`) ([From Start on the title to control](0-5-3-TitleStart.md), [From power-on to the press of Start](0-5-4-TitleBoot.md)) |
| all | `read₀` | the counters of `clock` before frame 0 are those of the machine when frame 0 begins | how the sequences are made |
| all | `base` (`seq`, `inp`, `next`) | one sequence of real machines for the whole run, numbered as `clock` numbers the frames; `pipe`, `room`, `pole` and `chg` take their machines from it | holds for any run by how the sequence is made |
| all | `flag`, `L` | the condition `Good` on the real machine of the first frame `G` after the castle entry where the area parser is done, the rule on the frames before it (`pre`), task 2, the flag's height, `T`, `c` just after the castle entry, the level number changed after frame `L` | the rule on every frame from `G` and task 5 are proved, with any inputs: a frame that ends paused is a `lag` frame and keeps the counters (`flag.noStart` is gone; [The star flag's rule after the castle entry](g-2-1-FlagRule.md), [The pause after the castle entry](g-2-5-FlagPause.md)); the condition was checked on the TAS, the late touch, real fireworks, random inputs with and without Start, pauses, and set timers. Of 193 runs with random inputs that reach the castle (51 heights of the touch), 176 have `G = E + 1` ([A wider condition at the castle entry](g-2-2-1-FlagWide.md)); on the other 17 the parser is at work and `G = E + 1 + k` with `k` from 1 to 9; `pre` holds on those frames, and on 20 more such runs of seeds 1001 to 3000 ([The castle entry with the area parser at work](g-2-2-3-FlagParser.md)) |

`E = C_s + c + j`, the timer's formula and the grid's formula are no longer fields of `Run`. They are proved from `clock` (`Run.hE`, `Run.hT`, `Run.hc`), with the timer and the phase before frame 0 from `title` and `read₀` (`Run.zero`, `Run.s_zero`, `Run.ph_zero`). `D ≥ 33` and the formula of the level change are proved from `flag` (`Run.hD`, `Run.hL`). `change₁` and `change₂` are no longer fields either. They are proved from `chg` (`Run.change₁`, `Run.change₂`). `level_ge_of_parts` also uses `2 ≤ q`, computed from the game's value, and the checks on the ROM `pipe_end`, `side_bound`, `side_end`, `side_start`, `side_ctl`, `room_start`, `RoomChecks` (`screen_facts`, `screen_timer_same`, `screen_rt`, `pipe_end`, `screen_start`), `flag_checked` and `title_check`, and that the star flag's delay is at least 6, which are private theorems and not assumptions.

`route_1_1` does not use `Merge`, `GMerge`, `Cond` or H3: they are neither fields of `Run` nor arguments of the theorem. It does not use that six objects stay apart either. These belong to the theorems on the exact length. But a `lag` frame is assumed to end paused (`paused₁`, `paused₂`), so a run with a `lag` frame in a change that is not a pause (such as the frame after one that runs over) is outside the theorem. On real runs the only frame of a change that runs over is the RAM clear, and the frame after it is the counted `setup` frame.

By the form of `Run`, these runs are not in the theorem:

* A run that does not take the two pipes. That walking is slower is outside this theorem.
* A big Mario, or a run with a power-up. A power-up stops the game for 59 frames, and the arithmetic is in `level_ge_of_late`; it is not joined yet.
* A run with an enemy near the pole, or one that goes over the pole and comes back.
* A run whose entering frame, up to the write, stores the position at the screen's edge or bumps a block with the head (`pipe.edge`).
* A run where a frame above ground before the touch writes the routine, the mode or the task: a power-up, an injury, a death, a pipe, the vine, the axe, an area change, or an earlier touch (`pole.keep.noStore`).
* A run whose touching frame, before the write, comes into the pole's range by the edge store (`pole.edge`).
* A run whose touching frame, before the write, writes the position through an index or a pointer other than by the move routine's stores with the index 0 (`pole.posKeep`).
* A run with a counted frame between control and the vertical pipe that ends out of control: a growth, an injury, a death (`pipe.lags.ctl`).
* A run that, before the vertical pipe, fills some object slots through an index (enemy slots 3 and 6, the fireballs, blocks 2 and 3, and others; `chg.upCleanU`).
* A run with Start on the frames of the game core after the vertical pipe (`chg.noStart₁`), with the unpause pressed on the exit's frame, or a song or screen buffer not in the tables, at its exit (`chg.quiet₁`), with an enemy loaded or a parser column not in the rows during the pipe's frames (`chg.places₁`), or with fire Mario at the entry (`chg.entry₁`, `chg.roomStart`).
* A run with Start on the frames of the game core after the side pipe (`chg.noStart₂`). A pause there only delays control on the runs measured, but that is not in Lean.
* A run with a `lag` frame in a change that does not end paused (`chg.paused₁`, `chg.paused₂`).
* A run whose machine on the first frame after the castle entry where the area parser is done is not in `Good`, or whose frames before it do not follow the rule (`flag.entry`, `flag.pre`). None of the 583 measured runs (the movie, pauses, random inputs from seeds 1 to 3000) is one. `pre` is not proved.
* A run whose machine after the press does not meet the condition (the case `press` of `title.boot`), when it is not a run from power-on of [From power-on to the press of Start](0-5-4-TitleBoot.md). Start and pauses before control are in.
* A run that does not meet `chg.entry₂` at the side pipe: the hurry-up music plays, a fireball is alive, a block object is alive, or the entry frame runs over. For the music, a theorem of its own shows that 1-2 does not start before frame 1748 ([Runs with the hurry-up music](0-6-4-HurryMusic.md), under the hypotheses `start`, `bLe`, `noStore`, `clean` and `below` on the first frame that starts the music and the frames in control before it). 1-1 has only one power-up before this pipe, but that is not in Lean.

## The two changes (`chg`)

`base` has one sequence of real machines. `seq n` is the machine when frame `n` begins, so `seq (n + 1)` is what frame `n` leaves, as in `clock`. `r(n)` counts the frames before `n` that are not `lag` frames (`seen`).

```
seq(n + 1) = frame(seq n, inp n)
r(a₁) = E_a + 1,   r(b₁) = C_r + 1,   r(a₂) = E_b + 1,   r(b₂) = C_s + 1
entryRest₁ : Rest(seq a₁)                 b₁ = firstCtl(seq, a₁, dB)   ctlBy₁ : ctl(seq (a₁ + dB))
a₁ = the first n with 1 ≤ n ≤ 1 + dA and ¬ctl(seq n)      upCleanU : 1 ≤ n < a₁ → ∀ j, CleanK(GU, q, trₙ(j))
a₂ = the first n ≥ b₁ with rt(seq n) ≠ rt(r)      b₂ = the first n ≥ a₂ with ctl(seq n)      ctlBy₂ : ctl(seq(a₂ + d₂))
entry₂ : EntryRestM(seq a₂)
roomRead, roomErase, roomXbit : b₁ ≤ n < a₂ → ∀ j, Read ∧ EraseEnd ∧ Xbit (trₙ(j))      (EraseEnd(m) := pc(m) = the erase → addr(m) & 0x7FF < the block buffers' end)
roomLateU : b₁ ≤ n < a₂ ∧ U(n) → ∀ j, LateS(scrQ, trₙ(j))      roomLateS : b₁ ≤ n < a₂ ∧ ¬U(n) → ∀ j, LateS(sndQ, trₙ(j))
      (U(n) := n = b₁ ∨ (b₁ < n ∧ c(seq(n − 1)) = 6); LateS(q, m) := q(pc(m)) → dot(m) ≤ 9,000; sndQ(p) := SoundEngine ≤ p ∧ back(p);
       scrQ(p) := sndQ(p) ∨ (RepeatByte ≤ p < UpdateScreen + 16 ∧ back(p)); back(p) := the instruction at p is a branch with a negative offset or a JMP to an address ≤ p)
roomReads : b₁ ≤ n < a₂ ∧ (n = b₁ ∨ (b₁ < n ∧ c(seq(n − 1)) = 6)) → ∀ j, ReadsAt(Z₁, trₙ(j))      roomOff₆ : b₁ < n < a₂ ∧ c(seq n) = 6 ∧ c(seq(n − 1)) = 6 → ∀ j, Off(trₙ(j))
paused₁ : a₁ ≤ n < b₁ ∧ kind(n) = lag  →  Paused(seq(n + 1))
time₁ : Timer(seq a₁)
places₁ : a₁ ≤ n < b₁ ∧ inPipe(seq n)  →  ∀ j, Places(trₙ(j))
noStart₁ : a₁ ≤ n < b₁ ∧ coreFrame(seq n)  →  inp n has no Start
quiet₁ : a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  QuietRest ∧ Shape (seq n)
paused₂ : a₂ ≤ n < b₂ ∧ kind(n) = lag  →  Paused(seq(n + 1))
noStart₂ : a₂ ≤ n < b₂ ∧ coreFrame(seq n)  →  inp n has no Start
time₂ : Timer(seq a₂)
```

The parts take their machines from `base`, so the old links of `Run` are theorems:

```
the bytes at frame 1 are those at the pipe's counted frame 1   Run.pipeKeep₁   (the frames before it end paused and keep them)
room.fe C_r = seq b₁                                         Run.roomCtl     (room.fe n = seq(b₁ + ix(n − C_r)), a definition)
b₁ < a₂                                                      Run.b₁_lt_a₂ (Room(seq b₁), dR_pos)
1 ≤ n < a₁ → ∀ j, Clean(trₙ(j))                             Run.upClean₁ (from upCleanU)
area(seq a₁) = area(e₁)                                      Run.area₁ (from Run.entry₁; e₁ = the reference machine at the vertical pipe's entry)
area(seq a₂) = area(e₁)                                      Run.area₂ (Run.areaB₁ from part b's rows, and the room's walk of AreaKeep)
y(seq a₂) = y(e₂),  Buffer(seq a₂)                            Run.y₂, Run.buf₂ (the size of SizeKeep, Run.ctl₂, Run.coin₂, Run.end₂ and the walks of the entering frame)
rt(seq a₂) = e_s                                             Run.rt₂ (room.enters, Run.roomEnter, EntryRoutine.rt_of_rows)
k = b₁ + ix(E_b − C_r) − 1,  b₁ ≤ k < a₂,  room.fm(E_b − 1) = seq k     Run.roomEnter   (E_b − C_r ≤ ups: Run.roomMany, from roomLag)
pole.seq 0 = seq b₂                                          Run.atCtl       (keep.all n = seq(b₂ + n), a definition)
1 ≤ E_a                                                      Run.pipeOne     (pipe.fm 0 = seq 0; frame 0 ends in control, an entry ends with the pipe's routine)
```

From these:

```
E_a + 91 ≤ C_r                                               Run.change₁, by PipeRun.bound with pipe_end
a₁ ≤ n < b₁ → left₁(seq n) ≠ 0                              Changes.first₁, from time₁ and the theorem Changes.ctlFirst₁
Room(seq b₁)                                                 Changes.roomAt, from the rows of the time and screen_start
PauseV(seq a₁)                                               Run.entry₁ (EntryKeep.entryV_of_title)
g(seq b₁) & 0x7E = 0                                         ChangesK.pauseBits₂, from the first change's rows and pause_index
EntryRest(seq a₂)                                            ChangesK.entryRest₂, from the room's walk with the music table and entry₂
Entry2(seq a₂)                                               ScreenPage.entry_rest, from Room, SiteOK and EntryRest
timer(seq a₂) ≥ 160                                          ScreenPage.entry_long, from Room and RoomChecks
StartAt(room.fe room.C)                                      Run.roomStart, from pipe_end and room_start
vsOf(room.fe C_r) ∈ rN.vStart                                Run.roomV0, from pipe_end and the rows of room_vert
─────────────────────────────────────────
a₂ ≤ n < b₂ → left₂(seq n) ≠ 0                              EndRun.firstF, from time₂ and the definition of b₂
E_b + 282 ≤ C_s                                              Run.change₂, by EndRun.bound with side_bound and side_end
```

`left` is read at the frame boundary. A frame whose routine runs over ends in the middle of the routine, and the next frame is the `lag` frame.

**What a `lag` frame does to `left`: nothing.** `keep₁` and `keep₂` are no longer assumed: from a `lag` frame ending paused (`paused₁`, `paused₂`) the check on the ROM proves that `left` does not fall. The measurements below are the earlier ones. In each change, among the frames where the interval timer's phase stays, `left` falls on one frame only, and that frame is `setup`. It is counted, and `z₁`, `z₂` are its number. On every other such frame `left` stays. `change-scenes` shows this from real entries, for no input, random inputs, Start pressed twice, and six objects written at a frame so that frames run over:

| change | runs | frames | runs that ran over | `lag` frames | `lag` frames where `left` falls | frames where `left` falls by 2 or more | least frames to control, without `lag` |
|---|---|---|---|---|---|---|---|
| into the room | 237 | 24,767 | 67 | 3,200 | 0 | 0 | 91 |
| out of the side pipe | 356 | 125,628 | 54 | 26,176 | 0 | 0 | 282 |

Not covered:

* Frames ran over only on states with objects written in. On the runs without written states, the only such frame in a change is `setup`, apart from pauses.
* Six objects written during the last 122 frames of the change out of the side pipe did not make a frame run over. There the `lag` rule was seen only with pauses.

These fields are hypotheses on single frames, and they are not proved. `pipe`, `room`, `pole` and `chg` take their machines from `base`, so they are tied by definition. Not tied: the kinds of `clock` meet the machines only at frame 0 (`read₀`), after the castle entry (`flag`), in `paused₁`, `paused₂`, and through the counts `ha₁`, `hb₁`, `ha₂`, `hb₂`. So the castle entry `E` of `clock` (where `flag` reads the machine) is not known to be the castle entry `c` of `pole` (where `atCastle` reads it); `pole.seq` itself is read from `base` (`FrameKeep.Keep.seq`). [Above ground](0-5-2-1-CastleJoin.md): if each frame from `b₂` to `E` is a `lag` frame exactly when it ends paused (`Run.LagUp`, not a field), then `E` is the counted frame `c` of `pole` (`Run.castle_join`), and `atCastle` follows from `flag` (`Run.atCastle_of_flag`). This holds on 646 runs to the castle, 276,544 frames above ground.

## The assumptions are not empty

`route-check` reads the numbers of `Run` from real frames.

| run | control changes | touch | castle | T | E + T | 1-2 |
|---|---|---|---|---|---|---|
| the TAS | 368, 459, 570, 852 | 1092 | 1218 | 370 | 1588 | 1748 |
| the TAS to 1089, then Left, A, A, A | 368, 459, 570, 852 | 1093 | 1219 | 369 | 1588 | 1748 |

Both satisfy every numeric assumption, and `L` equals the formula. `route-check` also reads `chg`: `a₁, b₁, a₂, b₂` = 369, 460, 571, 853; without `lag`, less one, they are 368, 459, 570, 852; `left` at the entries is 91 and 282, and both conditions hold; `z₁, z₂` = 418, 732; no other frame has the phase still; no frame takes 2 or more off `left`. It also checks the links: frame 1 is counted, and the room's entering frame `b₁ + (E_b − 1 − C_r)` is 570 = `a₂ − 1` on both runs. With pauses at 100 (before the vertical pipe), 380, 416, 450, 575, 730 and 845 it is `a₂ − 1` too. `changes-check FM2 pause F D` gives the same counts for pauses at 380, 416, 450, 575, 730 and 845, with 50 or 60 `lag` frames. Start is ignored on some frames of a change; there the movie goes out of step, and the check ends with exit 1 before the second change is done. The rule of `clock` holds on every frame of both (a working program). The structure above ground was checked on these runs by `pole-join-check`. The room's structure was checked on the TAS by a working program that is not in the repository. No Lean term of every field was built from the TAS.

## The closest case

The sum `E + T` has no slack: 1 less gives 1-2 at 1727. Exactly one case lowers it by 1.

```
g = 241,  W = 125   →   E = 1218,  T = 369,  sum 1587
```

`W = 125` does occur: a slow jump not moving left, with a fraction of 176/256 px or more (real frames, position overwritten). `slow_tight` excludes it: for `g ≤ 241` he moved left on the frame before, with a fraction below 176/256 px. That `W ≥ 126` then holds is the assumption `flagTight`, which is measured.

That a fall through the base's rows takes at most 3 frames (`fall`, `fallCheck`) is used here too.

From the TAS's state at 1085 with the position moved by 16/256 to 160/256 px in 10 steps, over every input of A, B, Left and Right up to 1093: every touch on 1092 and 1093 had `W ≥ 126`.

## Reproduce

```
python3 prove.py                                      # checks every theorem
.lake/build/bin/smbrta route-check FM2                # the whole route's numbers
.lake/build/bin/smbrta route-check FM2 1089 02808080  # a touch one frame later
.lake/build/bin/smbrta changes-check FM2 pause 380 60 # the fields of chg with a pause
.lake/build/bin/smbrta change-scenes FM2              # left with random inputs, pauses and frames that run over
.lake/build/bin/smbrta frames-check FM2                # the rules of clock and flag on every frame
.lake/build/bin/smbrta pipe-rule-check FM2             # the fields of pipe on real frames
.lake/build/bin/smbrta side-end-check FM2              # the condition at the exit and left after it, on real frames
.lake/build/bin/smbrta pole-join-check FM2 1089 02808080
.lake/build/bin/smbrta touch-search-at FM2 1085 80 8  # the position moved: touch to castle per frame
```
