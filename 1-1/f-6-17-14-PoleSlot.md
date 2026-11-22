[← Back](README.md) | [English](f-6-17-14-PoleSlot.md) | [Japanese](f-6-17-14-PoleSlot-ja.md)

# The pole's tiles: the slot of the area parser is a theorem

Round 29 gave the field `tilesCol` three parts ([the area parser on the route's frames](f-6-17-10-PoleParserRun.md), [`TileSlot` on one page](f-6-17-11-PoleWrap.md)). They speak of a read of the side check far from the pole (his page two or more before the pole's), at the pole's column, on the touch's frame up to the routine's write:

* (slot) if the byte read is one of the pole's tiles, then the area parser's column at the start of the touch's frame had come to the pole's column;
* (near) he is at most 112 px left of the screen's left edge of the frame's start;
* (read) with his page two before the pole's, the read is in the column of his pixel plus less than 16 px, mod 32.

This round removes (slot): the walk of the touch's frame proves it, from a map that every frame keeps from control on. In its place the field `bufAll` asks one more thing, at the stores that it already speaks of. After that, (near) and (read) are needed only to show that at such a read the parser's column has not come to the pole's. So `tilesCol` now asks just that. With the parser's invariant, which the route proves, (near) and (read) give it, so the new `tilesCol` asks less than the old (near) and (read).

## The words

* A pole's tile is the ball's tile or the shaft's tile.
* `colP = 16·pg + c` is the pole's column, counted as the parser's column is counted (16 columns a page).
* `c(n)` is the parser's column at the start of frame `n` from control (`PoleJoin.parColOf`). `c₀` and `e₀` are the parser's column and the screen's left edge in px at the start of the touch's frame.
* `pix = 256·page + x` is his pixel right after a read.
* A far read at the pole's column: right after a read of the side check, with `page + 1 < pg`, at the pole's column (the state's `pc` is the read's next instruction and the offset is one of the side check's).

```
SlotMap(c, m)  :=  colP ≤ c   ∨   no byte of the block buffers of m holds a pole's tile
```

## The new condition of `bufAll` (`PoleSlot.BufVS`)

Round 26 made `bufAll` ask `PoleKeepFar.BufV` of each instruction of each frame up to the touch's frame: a store through an index or a pointer that `farBuf` does not settle, and for an `STA` from the ROM only when A holds a pole's tile, writes a pole's tile into the block buffers only in the pole's column. Now, on frame `n`, it asks `BufVS(c(n))`:

```
BufVS(c, m)  :=  farBuf(m) = false  →  (an STA from the ROM with no NMI pending  →  A is a pole's tile)  →  (a store through an index or a pointer)  →
                 for each byte i of the block buffers that the step changes to a pole's tile:   i is in the pole's column   ∧   colP ≤ c
```

The part `colP ≤ c` is new. The new field asks more than the old one: at a store of a pole's tile it also asks that the parser's column at the frame's start has come to the pole's. It gives `BufAt` (`bufAt_of_VS`) and, on every instruction, `BufC(c)`: a step that changes a byte of the block buffers to a pole's tile has `colP ≤ c` (`bufC_of_VS`: a store that `farBuf` settles writes no byte of the block buffers; an `STA` of another byte writes no pole's tile).

The parser stores a column of the block buffers in its task `AreaParserCore`, at its own column, and each frame runs at most one task. So on the frame that stores the pole's tiles the parser's column at the frame's start is the pole's column. On real frames that difference was 0 at every store of a pole's tile (below).

## The frames from control (`PoleSlot.frames_slot`)

* At control no byte of the block buffers holds a pole's tile. This is a theorem from the rows of the change out of the side pipe (`PoleParser.inv₀`, with the check `pole_parser_rows` that the proof already has). So `SlotMap(c(0), all 0)` holds.
* One frame (`frame_slot`). If `colP ≤ c(n)`, the map holds for every later column. Else, by `BufC(c(n))`, no step of the frame writes a pole's tile into the block buffers, and the walk of the frames keeps "no pole's tile". The walk is the walk of the frames of `PoleTileKeep` (`keepCheckOfY`), with the places `noCol Q`: these are `Q` with the pole's column moved past the RAM, so `ColMap (noCol Q)` holds when no byte of the block buffers holds a pole's tile. The walk's test `okSK` looks at the places only through the block buffers' bytes, so the check for `noCol Q` is the check for `Q` (`keepCheckS_noCol`). So `SlotMap(c(n), all(n+1))`.
* The column does not go back: `c(n) ≤ c(n+1)` (`PoleParserRun.colMono_run`). Each frame follows the weak rule `RuleW` of the parser (`PoleStrict.ruleW_onFrames`: `step_strict` on a frame that comes to the player's routine, `PoleParser.step_noCut` on the others, under the conditions of `invJ_onFrames`), and the weak rule keeps the column or adds one (`PoleStrict.col_of_ruleW`). So `SlotMap(c(n+1), all(n+1))`.

So `SlotMap(c₀, start of the touch's frame)`.

## The touch's frame (`PoleSlot.no_write_frameZS`)

This is the walk of round 25 (`PoleTileKeep.no_write_frameZ`), with the slot's map carried from step to step as the map `ColMap` is (with `BufC(c₀)` on each instruction of the touch's frame). Right after a far read at the pole's column that the walk knows (its tests `pairOK` and `readPF`), the field gives `c₀ < colP`. So by the slot's map no byte of the block buffers holds a pole's tile, and the byte read is a byte of the block buffers (`noTile_after`: `PoleTileFar.tileRead_afterF` with the places `noCol Q`). So it is not a pole's tile: `TileCol` holds there, and that is all the walk used `tilesCol` for. The rest of the walk is unchanged.

## The fields

`tilesCol` before (round 30) and now, at a far read at the pole's column:

```
before:  TileSlot(c₀, e₀, m)  :=  (slot) byte read is a pole's tile ⇒ colP ≤ c₀   ∧   (near) e₀ ≤ pix + 112   ∧   (read) page + 2 = pg ⇒ ∃ a < 16, ⌊(pix + a)/16⌋ mod 32 = colP mod 32
now:     TileSlotC(c₀, m)     :=  c₀ < colP
```

`tileSlotC_of_N`: (near) ∧ (read) ∧ `16·c₀ ≤ e₀ + 384` ⇒ `TileSlotC` (the arithmetic of round 30, `PoleTileFar.tileCol_of_slot`). The bound `16·c₀ ≤ e₀ + 384` is the parser's invariant at the touch's frame, a theorem on the route (`PoleParserRun.colEdge_run`). So on the route the old field gives the new one: `tilesCol` asks less. `bufAll` asks more (above). The part (slot) moved from the player's reads to the parser's stores, at the places that `bufAll` already speaks of; the parts (near) and (read) became the one fact that they were used for.

`PoleJoin.Run.TileColAll` keeps its name (the private files use it) but now says what the touch's frame needs of the parser: `c(n) ≤ c(n+1)` for `n + 1 < ix(g)`, and `SlotMap(c(0), all 0)`. It is a theorem (`PoleParserRun.tilesCol_run`, `tilesCol_route`).

Signatures that changed, exactly:

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleSlot.BufVS (spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (trace (S.seq (a + n)) (S.inp (a + n)) k)` (was `PoleKeepFar.BufV (spotsF sy m0) (…)`).
* `PoleJoin.Run.tilesCol : ∀ n, WriteStep … n → ∀ j ≤ n, PoleSlot.TileSlotC (spotsF sy m0) (parColOf sy m0 (keep.fm g)) (trace (keep.fm g) (keep.pad g) j)` (was `PoleTileFar.TileSlot (spotsF sy m0) (parColOf sy m0 (keep.fm g)) (left16 (keep.fm g)) (…)`).
* `PoleJoin.Run.TileColAll R := (∀ n, n + 1 < ix g → parColOf(all n) ≤ parColOf(all (n+1))) ∧ PoleSlot.SlotMap (spotsF sy m0) (parColOf(all 0)) (all 0)` (was `TileCol` at each state up to the write).
* `PoleParserRun.tilesCol_run` takes `(hNT : PoleParser.NoTiles (spotsF sy m0) (R.seq 0))` after `hJ`. `tilesCol_route` has the same signature (it passes `(PoleParser.inv₀ …).2`).
* New: `PoleJoin.Run.bufC₁`, `PoleJoin.Run.slotStart`, `PoleStrict.col_of_ruleW`, `PoleStrict.ruleW_onFrames`, `PoleParserRun.colMono_run`, `PoleParserRun.colEdge_run` (not used by the route), and the file `Theorems/PoleSlot.lean`.
* `Run.inRange` has the same signature; it now uses `PoleSlot.inRange_of_frameZS`. `route_1_1` still concludes `1748 + j ≤ L`.

No new check on the ROM: the walks are those of rounds 25 and 31, and the map at control comes from `pole_parser_rows`.

## Measured

`pole-keep parser FM2 96` and `pole-keep check FM2 96`; the runs are the TAS, own random inputs from the TAS's frames 900 to 1089 (half with Start), and own random inputs from the first control:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frames that start in control | 719 | 14,318 | 25,980 |
| stores of a pole's tile into the block buffers | 10 | 150 | 0 |
| at them, the parser's column of the frame's start minus `colP` | 0 | 0 | – |
| of them where `BufVS` is false | 0 | 0 | 0 |
| frame starts in control where `SlotMap(c(n), all n)` is false | 0 | 0 | 0 |
| far reads at the pole's column (where `tilesCol` asks) | 101 | 0 | 3,376 |
| of them where `TileSlotC` is false (`c ≥ colP` at the frame's start) | 0 | 0 | 0 |
| of them where (near) or (read) of round 30 is false | 0 | 0 | 0 |

The far reads are counted on every frame in control, a superset of the touch's frame, where the field asks.

`pole-keep check FM2 96` (3 min 44 s, 73 MB) runs every instruction of 41,021 frames that start in control (167,758,026 instructions; the TAS, its frame 1089 then `02808080`, own random inputs from frames 900 to 1089 with and without Start, own random inputs from the first control). It found 160 stores that change a byte of the block buffers to a pole's tile (10 on the TAS, 150 on the random runs from frames 900 to 1089), all at a parser's column of the frame's start equal to `colP`, so `BufVS` false 0 times, and `SlotMap` false at 0 frame starts. Its exit code now asks both counts above ground to be 0 (exit 0).

## What is not proved

* `bufAll` at its 7 places: a store of a pole's tile only in the pole's column, and now also only when the parser's column at the frame's start has come to the pole's. A proof needs a walk of the parser's task `AreaParserCore` that follows its column to its store.
* `tilesCol` (`TileSlotC`): at a far read at the pole's column on the touch's frame, the parser has not yet come to the pole's column. (near) and (read) give it with the proved invariant. A proof of (near) needs his pixel on the touch's frame after the clamp of the scroll handler: part e proves the clamp's result only for the frames before the touch's frame, because its walks ask that no instruction of the frame writes the routine by its address, and the touch's frame does (the pole's write). (read) needs the read's address from his pixel; round 25 found that splitting the sum's high bits there passed 5.8 GB.
* `ctlU` is narrowed by the next step ([the area parser's lag may grow up to 157 px](f-6-17-15-PoleLag.md)). `keepB`: not changed this round.

**Files.** `Theorems/PoleSlot.lean` (new); `Theorems/PoleJoin.lean` (`bufAll`, `tilesCol`, `Run.TileColAll`, `Run.bufC₁`, `Run.slotStart`, `Run.inRange`); `Theorems/PoleStrict.lean` (`col_of_ruleW`, `ruleW_onFrames`); `Theorems/PoleParserRun.lean` (`colMono_run`, `colEdge_run`, `tilesCol_run`, `tilesCol_route`); `Main.lean` (the round 33 counters of `pole-keep check` and `pole-keep parser`).
