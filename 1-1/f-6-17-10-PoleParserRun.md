[← Back](README.md) | [English](f-6-17-10-PoleParserRun.md) | [Japanese](f-6-17-10-PoleParserRun-ja.md)

# The pole's tiles: the area parser on the route's frames

[The area parser against the screen's left edge](f-6-17-8-PoleParser.md) and [its second half of a frame](f-6-17-9-PoleParserEnd.md) proved the parser's invariant at control and that every frame keeps it, under conditions on each frame. Nothing in the route used them. This page takes the invariant to the route's frames up to the touch, and uses it at the touch's frame. The old field `tilesCol` is now a theorem from a new field `TileSlot` and the parser's invariant. It is not weaker than the old one: at every far read in the pole's column it also asks the (near) and (read) parts, where the old field asked nothing unless a pole's tile was read. All three parts held on the 3,477 measured far reads.

## The words

`col` is the parser's column with its page (16 columns a page), `N` the tasks left, `p(N) = [N ≥ 1] + [N ≥ 5]`, `S` the scroll counter of 32 px, `edge` the screen's left edge in px. The invariant:

```
Inv(L, m)  :=  N ≤ 8  ∧  16·col + 16·p(N) + S = edge + L
```

`colPole = 16·pg + c` is the pole's column (its page `pg`, its column `c` in the page). `pix = 256·page + x` is his pixel.

## The conditions of each frame, from the route

`PoleParser.inv_onFrames` asks, for each frame before the touch's frame:

* **No store through an index or a pointer writes the parser's four bytes.** `FrameKeep.guardE` now protects them (`FrameKeep.parE`, found from the code of `UpdScrollVar` as the parser's places are; `pI_eq`). So the field `keep.cleanE` gives it (`cleanPI_of_E`). `keep.cleanE` and `chg.upCleanU` ask a little more: 4 more protected bytes.
* **The area's type, the swimming flag and the change of size**: `SurfaceFrames.AreaRun` (`frames.areaRun`).
* **`posW` from the scroll handler on.** The field `frames.posW` holds only on counted frames. A frame before the touch's frame that comes to the player's routine is a counted frame (`counted_of`): a frame that is not counted ends paused and does not come there (`OnFrames.lagNo`). Its first arrival there is not before `CtrlKeep.arrAt` (`arrAt_le`). So `posW` gives what the walks need (`cut_of_posW`). The walks of `PoleParser` now ask it only from the first arrival on (`frame_toU`, `rule_frame`, `inv_onFrames`).
* **No wrap of the scroll** at `UpdScrollVar`: a new field `parWrap` (below).
* **The edge below 64,896 px** at the frame's start: a theorem (`edgeLow_run`). Part e bounds the larger of his position and the edge at the end of each counted frame `d` before the touch by `posP(B.m) + 16·top·d` (in 1/256 px), when the touch is not later than `farN` frames after control (`OnFrames.readAllB`; a later touch is `SurfaceLate`). The frames not counted keep the edge's bytes (`lag_edge`). One number on the ROM closes it: `posP(B.m) + 16·top·farN < 64896·256` (checked natively in the route's private proof).

`noWrap_of` makes `PoleParser.NoWrap` from `parWrap` and the edge's bound.

At control the invariant with `L = 384` and the column below 16 come from the rows of the change out of the side pipe (`PoleParser.inv₀`, `PoleParser.col₀`). So:

```
inv_run :  ∀ n < ix(g),  Inv(384, all n) ∧ col_in_page(all n) < 16
```

at every frame's start up to the touch's frame, counted or not. With `col_le`, at the start of the touch's frame:

```
16·col ≤ edge + 384
```

## The touch's frame: `TileCol` from `TileSlot`

The old field `tilesCol` asked `TileCol` up to the routine's write: right after a read of the side check with his page two or more before the pole's, at the pole's column, the byte read is not one of the pole's tiles. Now it is a theorem (`tilesCol_run`, on the route `tilesCol_route`) from the invariant and the new one-state condition `TileSlot` (`PoleTileFar.TileSlot`). With `c₀` and `e₀` the parser's column and the edge at the start of the touch's frame, right after such a read:

```
(slot)  byte read ∈ {ball, shaft}  ⇒  colPole ≤ c₀
(near)  e₀ ≤ pix + 112
(read)  ∃ a < 16,  ⌊(pix + a)/16⌋ mod 32 = colPole mod 32
```

`tileCol_of_slot` is arithmetic. If a pole's tile were read: `16·colPole ≤ 16·c₀ ≤ e₀ + 384 ≤ pix + 496`. His page is at most `pg − 2`, so the read's column `r = ⌊(pix + a)/16⌋` is at most `16·pg − 16`, below `colPole`. It is `colPole` mod 32, so `r ≤ colPole − 32`, and `pix < 16·(r + 1) ≤ 16·colPole − 496`. The two bounds contradict each other.

So the parser is at most 24 columns ahead of the edge, and it has not come to the pole's column while he reads 32 columns or more before it.

## The fields

| field | was | now |
|---|---|---|
| `tilesCol` | `TileCol` at each state up to the write | `TileSlot` with the parser's column and the edge of the frame's start |
| `parWrap` (new) | — | each frame before the touch's frame, at `UpdScrollVar`: if the edge moved by `Y`, then `S + Y < 256` (`PoleJoin.NoWrapP`) |
| `keep.cleanE` | `CleanK` of `guardE` | the same, and `guardE` protects the parser's four bytes too |

`Run.inRange`, `touch_ge`, `direct_castle`, `castle_ge` and `touch_castle` take `(hT : R.TileColAll)` (the old field's statement) after `hgN`. The route's private proof gives it by `tilesCol_route`, in the case of a touch not later than `farN` frames after control.
`tilesCol_route` asks the checks of the parser (`pole_parser_rows`, `pole_parser_col`, `pole_parser_q`, `pole_parser_e`, `pole_parser_s`), the area's type 1 at control and the number of the edge's bound (both native, in the route's private proof).

## Measured

`pole-keep parser FM2 96` (1 min 53 s natively, 71 MB). The runs are the TAS, own random inputs from the TAS's frames 900 to 1089 (96 runs, half with Start), and own random inputs from the first control (24 runs of 1300 frames, half with Start). Every frame that starts in control is checked, not only the touch's frame:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| far reads at the pole's column (`TileSlot` asked) | 101 | 0 | 3,376 |
| `TileSlot` false | 0 | 0 | 0 |
| least `pix − e₀` at a side read (asks ≥ −112) | 23 px | 0 px | 0 px |
| visits of `UpdScrollVar` (`parWrap` asked) | 719 | 10,086 | 18,682 |
| `NoWrapP` false | 0 | 0 | 0 |
| largest edge at a frame's start (now a theorem: below 64,896 px) | 3,046 px | 3,055 px | 616 px |

Round 28's measure with `N = 400` also found no store through an index or a pointer on a parser's byte, which the larger `guardE` asks. With the parser's bytes in `guardE` (74 bytes, was 70; the union guard of `chg.upCleanU` 151 bytes):

* `keep-frames-check FM2 100` (`keep.cleanE` and the other conditions of the frames above ground): 224,813 frames of the TAS and own runs (with and without a pause), bad 0;
* `up-clean-u FM2` (`chg.upCleanU`, from frame 1 to the vertical pipe's entry): 221,490 frames, against the union guard 0.

## What is not proved

* `TileSlot` itself: (`slot`) the parser draws a pole's tile only once it has come to the pole's column; (`near`) he is not far left of the edge; (`read`) the read's column is that of his pixel plus the adder. On real runs no far read at the pole's column reads a pole's tile, so (`slot`) is never used there.
* `parWrap` (measured above). The parser may skip its tasks on a frame (the control byte 6), so the weak rule does not bound `S`.
* `bufAll` (7 places) and `keepB` (66 places): not attempted in this round.

**Files.** `Theorems/PoleParserRun.lean` (`edgeLow_run`, `lag_edge`, `surf_edge` too); `FrameKeep.parRt`, `FrameKeep.parE` and `guardE` in `Theorems/FrameKeep.lean`; `TileSlot`, `tileCol_of_slot` in `Theorems/PoleTileFar.lean`; the fields and `parColOf`, `parSOf`, `NoWrapP`, `Run.TileColAll` in `Theorems/PoleJoin.lean`; `hp` from the first arrival in `PoleParser.lean` and `PoleParserEnd.lean`; the private Route block and the round 29 line of `pole-keep parser` in `Main.lean`.
