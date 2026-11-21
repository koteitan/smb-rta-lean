[← Back](README.md) | [English](f-6-17-6-PoleTileKeep.md) | [Japanese](f-6-17-6-PoleTileKeep-ja.md)

# The pole's tiles at the touch: the height kept inside the collision routine, from two bytes the frames keep

The field `yKeep` of `PoleJoin.Run` is gone. It asked that up to the routine's write, inside the collision routine, no store through an index or a pointer writes the height. Now the walk of the touch's frame tests every such store inside the routine and shows that it writes neither the height nor two more bytes that it protects there. For that the walk needs two bytes that the frames keep from control on: the block objects' offset and the player's number. What is assumed in place of `yKeep` is the new field `keepB`: on every frame up to the touch's frame, no store through an index or a pointer writes those two bytes. It is a condition on single instructions of the same kind as the guard of `keep.cleanE`.

## Why the walk could not show `yKeep`

Inside the collision routine there were 20 places of stores whose target the walk could not keep off the height (round 24, `pole-far-stores`):

* 16 stores of the block objects through `X` (`STA zp,X`, `STY zp,X`, the head's bump and the bricks). `X` is the block objects' offset. The game changes that byte only by flipping its lowest bit (an `EOR #1`), so it is 0 or 1, but the walk did not know it.
* 3 stores `STA (zp),Y` into the block buffers (the blank tile of a bumped block, a coin above it, a touched coin). The high byte of the pointer is the same for both block buffers, but the walk had forgotten it at stores through an index it does not know.
* the store of a score digit `STA abs,Y`. `Y` comes from the player's number. With `Y` not known the range of the target wraps around to the height's place.

## The two bytes

Write `spr` for the block objects' offset and `cur` for the player's number. Their places are read from the program: `spr` is the operand of the first `LDX abs` of the floatey numbers' routine (`sprI`), `cur` the operand of the `LDY abs` six bytes before the routine that prints a number (`curI`). The watched bits are (`watchB`)

```
spr & 0xFE = 0,   cur = 0
```

* At control both hold: in every state with control of the rows of the change out of the side pipe the two bytes are known with these values (`PoleTileCtl.watchCheckK`, checked in one pass over the rows with the map's check `mapCheckK`: `mapWatchK`). So `Watched(watchB, seq 0)` (`PoleTileCtl.watch₀`).
* Every frame in control keeps them. The walk of the frames with the test `okSK` (`PoleTileWalk.keepCheckS`) is run with the two bytes protected (`GK`) and watched (`watchY` = the watched bits of `FrameKeep` and these). With `CleanK` of `FrameKeep` and `KeepB` on each instruction (`cleanK_GK`), every frame up to the touch's frame starts with the map and with the two bytes' values (`frames_keepY`). That walk is a walk of `FrameKeep` too (`walkK_of_KS`), so `FrameKeep.keep_frameW` gives the watched bits at each frame's end.

## The new field

* `keepB` (`KeepB`): on each instruction of each frame up to the touch's frame, counted or not: if a store through an index or a pointer has a target `t < 0x2000`, then `t mod 2048 ∉ {spr, cur}`.

## The walk of the touch's frame

The walk is that of `PoleTileFar` with these changes (`walkZ`):

* it starts with the two bytes' watched bits (`startY`) and protects them on the whole frame (`poleY`: the guard of `PoleFrame` with the two bytes);
* inside the collision routine its guard `GZ` protects the height, the high byte of the block buffer's pointer and the objects' offset (`zoneB`), where `PoleTileHeight` protected the height only;
* **the zone's test** (`zoneTest`), on every piece inside the routine whose step is a store through an index or a pointer: the store writes none of these three bytes. Either the walk's address of the store avoids them (`StepWrites.keepOK`), or the range of the target from what the piece knows avoids them (`rangeOK`, `rangeW`):
  * `STA`/`STY`/`DEC`/`INC zp,X`: the operand `z` plus `X`, with `z + max X < 256`: the range `[z + min X, z + max X]`;
  * `STA (zp),Y`: the range `[min lo + 256·min hi + min Y, max lo + 256·max hi + max Y]`, where `lo` and `hi` are the pointer's bytes, and `min`, `max` take each unknown bit as 0 and as 1;
  * the range must lie in one copy of the RAM (below `0x2000`, one block of 2048), or past the RAM.

The proofs: `range_spec` (a covered machine stores in the range: `RoomBlocks.writeAddr_eq`, `SideChangeEnd.ptr_toNat`), `target_of_range`, `keep_target` (the walk's address of a store through an index or a pointer is the one of `PipeWrites.wTarget`: `wOf_of_target`), `zone_of_test`. With them `CleanK` of `GZ` follows from `CleanK`, `PosAt` and the test (`cleanK_GZ`), so the step of the walk follows the machine without `YAt` (`s_kstepZ`). The theorem (`no_write_frameZ`):

```
frameCheckZ ∧ FrameStart(s₀) ∧ Watched(watchB, s₀) ∧ ColMap(s₀) ∧ (∀ j ≤ n, CleanK ∧ PosAt ∧ HypR ∧ BufAt ∧ TileCol at s_j)
  ⇒ rt(s_{n+1}) ≠ the pole's routine
```

`YAt` is not among the hypotheses. `touch_right_of_leftZ` and `inRange_of_frameZ` are the theorems of `PoleTileFar` with `Watched(watchB)` at the frame's start and `CleanK` of `GK` (from `CleanK` and `KeepB`) in place of `YKeep`. The check `poleCheckZ` = `ptrOK ∧ frameCheckZ ∧ subsCheck ∧ keepCheckOfY` is proved natively (private `pole_check_z` in `Proof/PoleTiles.lean`, in place of `pole_check_f`). `PoleJoin.Run.inRange` uses `inRange_of_frameZ` with the fields `keepB`, `posKeep`, `bufAll`, `tilesCol`, `edge`, and with the map and the two bytes at the touch's frame's start (`Run.tilesStart`).

The search for the table keeps the zone's bytes in the routine at every normalization, and it forgets the registers inside the routine in the two routines that print a number (`normZ`, `rangesZ`): with the player's number known, they would make a state for each digit. These are search choices only. The walk checks every state.

## Measured

The walk's search (`pole-keep search`): 10,775,682 steps, 498,138 states in the table, 0 failures (the walk of `PoleTileFar`: 9,680,248 steps, 434,249 states). The search takes 50 to 62 s natively, and the whole check `poleCheckZ` is true natively in 77 to 100 s (the larger numbers with a load of about 9); the walk of the frames with the two bytes (`keepCheckOfY`) is true in 4 to 5 s. In a probe the search peaked at about 4.3 GB. The private `Proof/PoleTiles.lean` (`pole_check_z` and the rows' check `pole_rows`) built in 150 s and 113 s in two full builds (round 24: 162 s with `pole_check_f`).

**Too big or false at first** (search choices only, no false statement):

* With the two bytes known, the routines that print a number were followed digit by digit: the first search passed 5.9 GB and was stopped. The search now forgets the registers inside the collision routine in those two routines.
* The search kept the pointer's high byte and the objects' offset only at some places; 28 of its states then failed the test at the store that erases a touched coin. It keeps them at every place inside the routine now.
* The first check was false: the walk could not cover its states in the loop of the routine that prints a number, because the search had forgotten the registers there but not the carry, which is part of the table's key inside the routine. 240 states of the table ran out of steps. The search forgets the flags there too now; then every state of the table and both starts pass.

`pole-keep check FM2 N` (every instruction of every frame, in control or not, from the first control on): a store through an index or a pointer that writes one of the two bytes, the two bytes' watched bits at each start of a frame in control, and the stores through an index or a pointer inside the collision routine that write the height, the pointer's high byte or the objects' offset:

| run | frames (start in control) | instructions | `KeepB` fails on frames in control | such stores on the other frames (the area's setup) | frame starts off the watched bits | stores inside the collision routine (on the three bytes) |
|---|---|---|---|---|---|---|
| the TAS, frames 1 to 1239 after the first control | 1,239 (719) | 5,561,241 | 0 | 4 | 0 | 867 (0) |
| the TAS from frame 1089, then other inputs | 20 (4) | 79,380 | 0 | 0 | 0 | 0 (0) |
| own random inputs from frames 900 to 1089 of the TAS, 200 runs, no Start | 27,783 (27,783) | 122,677,764 | 0 | 0 | 0 | 666 (0) |
| own random inputs with Start, 200 runs | 32,000 (30,804) | 95,485,622 | 0 | 0 | 0 | 444 (0) |
| own random inputs from the first control, 100 runs of 1,300 frames, half with Start | 130,000 (103,703) | 458,438,266 | 0 | 84 | 0 | 2,631 (0) |

(`N = 400`; with `N = 96` the same, with 0 failures too.) The stores on the frames that do not start in control are the area's setup clearing the RAM, on the frames of the two area changes (frames 417, 441, 731 and 755 of the TAS). `keepB` asks nothing there: every frame of `keep` starts in control (`FrameKeep.Frames.all_start`).

## What is not proved

* `keepB` itself: no store through an index or a pointer writes the block objects' offset or the player's number. The game writes them only by their addresses (the offset by an `EOR #1`, the player's number when two players change). It is checked on real frames above.
* Round 26: `keepB` and `bufAll` now ask only of the stores that the program alone (and, for `bufAll`, the byte of an `STA`) does not settle: [The stores that `keepB` and `bufAll` still speak of](f-6-17-7-PoleKeepFar.md).
* `tilesCol` and `bufAll` are unchanged.
  * `tilesCol` needs the area parser's column against the screen and him across frames. Measured (`pole-keep parser FM2 N`, with the parser's bytes found from the code of `UpdScrollVar`), at every start of a frame in control: `16·col + 16·p(N) + S − edge = 384`, where `col` is the parser's column (16 per page), `N` its tasks left in the current set, `p(N) = [N ≥ 1] + [N ≥ 5]` the column steps among them, `S` the scroll counter of 32 px, and `edge` the screen's left edge in px; the block buffers' column of the parser is `col mod 32`; and every store of a pole's tile into the block buffers is made with the parser's column at the pole's column. With `N = 400`: 163,009 starts of frames in control (the TAS, 400 runs of own random inputs from its frames 900 to 1089, half with Start, and 100 runs of 1,300 frames from the first control, half with Start), each with the value 384 and the block buffers' column `col mod 32`, and 620 stores of a pole's tile, all at the pole's column. At control the rows of the change know all of these bytes (the parser at 2944 px, the edge at 2560 px, `N = 0`, `S = 0`). So the parser draws the pole's column only when the edge is 384 px or less before it, and he is right of the edge. But the walks keep known bits of single bytes, not such a sum, so this is not proved.
  * `bufAll` needs a bound of the objects' index at 36 stores into the objects' tables just below the block buffers. Measured with a probe: with the objects' offset protected and watched as the two bytes are, the walk of the frames grows from 46,576 to 182,120 states in the table, its check is false, and at the 36 stores `X` is still not known, although the objects' offset is known exactly there (0 to 5): `X` comes there in registers that the walk forgets at its cuts.

**Files:** `Theorems/PoleTileKeep.lean`; `Theorems/PoleTileCtl.lean` (the rows' check of the two bytes, `watch₀`); `Theorems/PoleJoin.lean` (`keepB`). Private `Proof/PoleTiles.lean` (`pole_check_z`, `pole_rows`). The programs `pole-keep search` (the search and the checks) and `pole-keep check FM2 [N]` (the real frames above).
