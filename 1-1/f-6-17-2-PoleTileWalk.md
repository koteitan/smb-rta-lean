[← Back](README.md) | [English](f-6-17-2-PoleTileWalk.md) | [Japanese](f-6-17-2-PoleTileWalk-ja.md)

# The pole's tiles at the touch: the map of the frame's start

The field `tiles` of `PoleJoin.Run` is gone. It asked `TileRead` on every instruction of the touch's frame up to the routine's write: if a read of the side check gives one of the pole's tiles, the read was in the pole's column, with the page at most one before the pole's. It is now a theorem. In its place there are two fields. Each is a condition on single instructions that says nothing about what the block buffers hold.

## The new fields

Write `tile(v)` for "the byte `v` is one of the pole's two tiles", `B` for the RAM indices of the two block buffers, and `col(i)` for "the index `i` is in the pole's column". `m'` is the machine one step after `m`.

* `bufAll`: on every instruction of every frame from control to the touch's frame, counted or not, the touch's frame too: if the instruction is a store through an index or a pointer, then `∀ i ∈ B, m'.ram[i] ≠ m.ram[i] ∧ tile(m'.ram[i]) → col(i)` (`BufAt`).
* `tilesRead`: up to the write, at a read of the side check (`pc = read`, the offset of the side check), with `a` = the pointer + `Y` and `i = a mod 2048`: `a < 0x2000 ∧ i ∈ B ∧ (tile(m.ram[i]) ∧ col(i) → pg ≤ page + 1)` (`ReadPre`).

## What is proved

The map `ColMap(m) := ∀ i ∈ B, tile(m.ram[i]) → col(i)` is proved at three places: at control, at the start of the touch's frame, and at every instruction of the touch's frame up to the write.

The walk of `PoleFrame` runs again on the same table, with two more tests on every state on the way (`walkP`):

* `okS`: the step writes no byte of the block buffers (`StepWrites.keepOK`), or it is a store through an index or a pointer;
* `pairOK`: a state right after the read of the side check comes from the read itself, with no NMI pending.

The check `poleCheckP` (the walk with these tests, the facts of the ROM at the read, the check of `SubsOnce`, and the walk of the frames below) is proved natively. It gives the old check `poleFrameCheck` too.

`no_write_frameP` proves, by induction over the instructions of the frame, that every instruction `j` up to the write has `ColMap(s_j)` and `TileRead(s_j)`:

* `ColMap` goes from `s_j` to `s_{j+1}`: a step that `okS` allows writes no byte of `B`, or it is a store through an index or a pointer, and `BufAt` says it writes a pole's tile there only in the pole's column (`colMap_step`).
* `TileRead(s_{j+1})`: by `pairOK`, `s_j` is at the `LDA (zp),Y` of the side check with no NMI pending. That instruction puts `m.ram[i]` in `A`, keeps the RAM and keeps `Y` (`RoomBlocks.step_lda_izy`, `step_lda_izy_y`). So the place of the read after it is `i` (`readAt_after`). If `A` is a pole's tile, `ColMap(s_j)` gives `col(i)`, and `ReadPre` gives the page (`tileRead_after`).

With these, the walk closes as before: if he is left of the pole's range at the end of the move, the routine byte never becomes the pole's. So a touch needs him in the range (`inRange_of_frameP`, used by `PoleJoin.Run.inRange`).

`ColMap` at the start of the touch's frame comes from control. The walk of one whole frame in control of `FrameKeep` runs again with the test `okSK` (the step writes no byte of `B`, or it is a store through an index or a pointer) on every state on the way (`walkKS`, `keepCheckOfS`, about 5 s natively). So a frame in control that starts with `ColMap`, whose instructions meet `CleanK` and `BufAt`, ends with `ColMap` (`frame_colMap`). The frames from control to the touch's frame start in control (`FrameKeep.Frames.all_start`), so each of them keeps the map (`frames_colMap`). The theorem `PoleJoin.Run.tilesStart` gives `ColMap` at the start of the touch's frame from the map at control and `bufAll`. The area parser draws the pole's column with the pole's tiles in one of these frames; `BufAt` allows it, because the tiles go into the pole's column.

The map at control is proved too (`PoleTileCtl.colMap₀`). The rows of the change out of the side pipe (`SideChangeSound`) cover the machine at control. In every state of these rows that has control, all the bytes of `B` are known, and none is a pole's tile out of the pole's column (`mapCheckK`, about 20 s natively; 2 such states in each of the two sets of rows). So the machine at control has `ColMap` (`PoleTileCtl.EndRunQ.colMap`, as `Route.Run.atCtl₀`).

## Measured

Before proving, on every frame in control (not only the touches), from the start of the frame to the write or the frame's end:

| run | frames | touches | instructions | stores into `B` | reads of the side check | failures |
|---|---|---|---|---|---|---|
| the TAS | 718 | 1 | 3,547,037 | 161 | 2,793 | 0 |
| own random inputs, 48 runs from frames 930 to 1089 of the TAS | 6,020 | 11 | 25,928,104 | 309 | 23,298 | 0 |
| own random inputs with Start, 48 runs from frames 930 to 1089 of the TAS (2,106 frames start paused) | 5,772 | 14 | 20,120,574 | 292 | 13,981 | 0 |

`ColMap` held at the start of every frame (so at control too), `BufAt` at every instruction (on the touch's frames also after the write: 1,416 and 17,702 instructions in the TAS and in the runs with Start), `ReadPre` at every read, and `TileRead` after every read. Every state right after the read came from the read. The first random inputs press neither Start nor Select; the second press Start, so many frames are paused. The runs of `pole-frame-check` and `pole-rule-check` also passed (bad 0).

**False:** the first form of `BufAt`, "a store through an index or a pointer writes no pole's tile into `B`", was false on 10 instructions of the TAS and 90 of the random runs. These are the area parser's stores that draw the pole's column. They come after the player's routine, so never before the write of a touch, but the condition was false as a condition on one instruction. The condition now allows a pole's tile in the pole's column, and then it held everywhere.

The walk could not prove `BufAt` itself. At 36 places a store goes through an index into a table just below the block buffers, and the abstract states do not know the index. At 2 places a store goes through the block buffers' pointer, and the abstract states do not know the byte.

## What is not proved

* `bufAll`: assumed for each store through an index or a pointer.
* `tilesRead`: that the read is in the block buffers needs the caller's check of the height, which the walk does not keep: at the reads of the side check the walk also has row offsets past the last of the 13 rows, which are out of the block buffers. That the read is in the RAM was tried with a third test (the pointer's high byte known to be below the registers); it failed at 4 states of the read (61 of 64,065 visits) where the walk knows neither the pointer's high byte nor the offset of the routine. The page part needs where he is when the pole's column is drawn. All three stay assumed. Later the field `tilesRead` was taken out: with a new walk the first two parts are proved for every read near the pole, and two one-state fields remain (`ySide`, `tilesFar`): [The reads near the pole are in the block buffers](f-6-17-3-PoleTileRead.md).

**Files:** `Theorems/PoleTileWalk.lean`, `Theorems/PoleTileCtl.lean`; private `Proof/PoleTiles.lean` (`pole_check_p`, about 90 s natively, and `pole_row_map`, about 20 s). `route_1_1` used `pole_check_p` in place of `pole_frame_check`; since round 22 it uses `pole_check_u` of [the reads near the pole](f-6-17-3-PoleTileRead.md), and `pole_frame_check` is not generated; since round 23 `pole_check_h` of [the height at the side check](f-6-17-4-PoleTileHeight.md).
