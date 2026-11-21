[← Back](README.md) | [English](f-6-17-5-PoleTileFar.md) | [Japanese](f-6-17-5-PoleTileFar-ja.md)

# The pole's tiles at the touch: the reads far from the pole are in the block buffers

The field `tilesFar` of `PoleJoin.Run` is gone. It asked that right after each read of the side check with the page two or more before the pole's, up to the routine's write, the byte read is not one of the pole's tiles. Now the walk of the touch's frame knows that such a read is in the RAM and in the block buffers, and the map of the frame's start (`ColMap`, a theorem) says that a pole's tile there is in the pole's column. So only the reads at the pole's column stay assumed: the new field `tilesCol`, the same condition on fewer reads.

## The new field

Write `pg` for the pole's page, `page` for the player's page, `save` for the block buffer routine's offset byte, `read` for the routine's read of the block buffer (`LDA (zp),Y`), and `readAt(m)` for the RAM index of that read (its pointer plus `Y`, `PoleFrame.readAt`). `onCol(i)` says that the index `i` is in the pole's column of the block buffers (`PoleEntryRule.onCol`).

* `tilesCol` (`TileCol`): up to the write, if `pc(m) = read + 2`, `save(m)` is an offset of the side check, `page(m) + 1 < pg`, and `onCol(readAt(m))`, then `A(m)` is neither the pole's ball nor its shaft.

The old field `tilesFar` (`PoleTileRead.TileFar`) was the same without `onCol(readAt(m))`, so `TileFar(m) ⇒ TileCol(m)` (`tileCol_of_far`).

## What is proved

Theorem `no_write_frameF` (file `Theorems/PoleTileFar.lean`) is `PoleTileHeight.no_write_frameH` with `TileCol` in place of `TileFar`:

```
frameCheckF ∧ FrameStart(s₀) ∧ ColMap(s₀) ∧ (∀ j ≤ n, CleanK ∧ PosAt ∧ YAt ∧ HypR ∧ BufAt ∧ TileCol at s_j)
  ⇒ rt(s_{n+1}) ≠ the pole's routine
```

The walk is the walk of `PoleTileHeight` with these changes (`walkF`):

* **The page's bit, far from the pole.** In a side check with the page two or more before the pole's, right before the block buffer routine moves the page's lowest bit into the carry (the instruction before its `ORA` of the sum, `parAt`), that bit of the accumulator is split into its two values (`PipeChangeEnd.bitA 1`). The bit chooses the block buffer. Then the walk knows the pointer's high byte and the high 4 bits of its low byte: the routine adds a byte with no low bits to the column, which the walk's special addition `PipeWrites.aadcH` follows. The walk does not know the column itself, and it does not need to.
* **The height on every page.** The splits of `PoleTileHeight` that were made only near the pole are now made on every page: the height at the collision routine's first load of it (5 pieces that hold every value), at the start of the side check (the 7 pieces below 208 px, after the walk's test that the height's piece is below 208 px), and the accumulator at the addition of the height's adder (bit by bit, `fullA`).
* **The test at the read** (`readPF`), on every page: on a step from a piece at the read to a state right after it that knows the offset to be the side check's, `Y` is known at the read, and every address that the known bits of the pointer allow is in the block buffers: `bufLo ≤ readMin` and `readMax < bufLo + bufBytes ≤ 2048`, where `readMin` and `readMax` take each unknown bit of the pointer's two bytes as 0 and as 1 (`AB.minv`, `AB.maxv`). With the address of the read `lo + 256·hi + Y` (`SideChangeEnd.ptr_toNat`), this puts the read in the RAM and in the block buffers.

All the new splits are covers with no hypothesis (`cov_zoneTF`, `cov_zoneHF`, `cov_preF`). Right after a read the walk proves `TileRead` (`tileRead_afterF`): the read is in the block buffers (`readPF`), so if the byte read is a pole's tile, the map gives `onCol(readAt)`; if the page is two or more before the pole's, `TileCol` says the byte is not a pole's tile; so the page is at most one before the pole's.

The check `poleCheckF` (the checks of `PoleFrame` before its walk, the covers of the pieces, this walk, the facts of the ROM at the read, the check of `SubsOnce`, the walk of the frames of `PoleTileWalk`) is proved natively (private `pole_check_f` in `Proof/PoleTiles.lean`, in place of `pole_check_h`). `touch_right_of_leftF` and `inRange_of_frameF` are the theorems of `PoleTileHeight` with `TileCol`. `PoleJoin.Run.inRange` uses `inRange_of_frameF` with the field `tilesCol`.

The search for the table keeps the height's piece at the start of the side check on every page (`normF`), and it keeps no state right after the read in the table (`isCutF`: the walk does not cover there). These are search choices only. The walk checks every state.

## Measured

The walk's search (`pole-far-search`): 9,680,248 steps, 434,249 states in the table, 0 failures (the walk of `PoleTileHeight`: 8,196,666 steps, 376,976 states). The search takes 45 to 49 s natively with a load of about 4, and the program `pole-far-search` peaks at 2.97 GB. The whole check `poleCheckF` is true natively in 135 s with that load, and in 148 s with a load of 7 to 10; `poleCheckH` took 106 to 113 s, and 126 s with a load of 7 to 10. Every start of the side check inside the collision routine had the height's piece below 208 px, and every step to a state right after a read passed `readPF`.

**Too big at first:** a first form of the walk also split the horizontal sum's high 4 bits at its store far from the pole, so that the pointer was known exactly. Its search passed 5.8 GB after about 100 s and was stopped. The pointer's column is not needed: with the page's bit split, the walk knows the pointer's high byte and the high 4 bits of its low byte. A second form split the low byte into its 16 values at the read and asked the exact address there: its search took 10,837,288 steps (table 438,423 states, 0 failures) and the whole check 189 s, against 126 s for `poleCheckH` under the same load. The present form asks the range of the address instead, with no split at the read: 9,680,248 steps, 434,249 states in the table, 0 failures.

`pole-far-check FM2 96` (every instruction of every frame, in control or not, from the first control on; a read is *far* when the page at the read is two or more before the pole's):

| run | frames | instructions | far side reads | out of the RAM or the block buffers | at the pole's column | a pole's tile read |
|---|---|---|---|---|---|---|
| the TAS, frames 1 to 1239 after the first control | 1,239 | 5,561,241 | 2,326 | 0 | 101 | 0 |
| the TAS from frame 1089, then other inputs | 20 | 79,380 | 0 | 0 | 0 | 0 |
| own random inputs from frames 900 to 1089 of the TAS, 48 runs, no Start | 6,917 | 30,419,655 | 2,124 | 0 | 0 | 0 |
| own random inputs with Start, 48 runs | 7,680 | 23,030,036 | 2,136 | 0 | 0 | 0 |
| own random inputs from the first control, 24 runs of 1,300 frames, half with Start | 31,200 | 108,667,714 | 74,575 | 0 | 3,376 | 0 |
| own random inputs from the 177 frames of the TAS 384 to 640 px before the pole's range, 96 runs of 120 frames | 11,520 | 58,114,073 | 26,107 | 0 | 1,980 | 0 |

`TileCol` (and the old `TileFar`) held on every instruction of every frame (bad 0). With `N = 400` (200 runs without and 200 with Start, 100 runs of 1,300 frames from the first control, 400 runs from the frames before the pole's range): 239,042 frames, 924,723,135 instructions, 434,286 far side reads, 19,111 of them at the pole's column, none out of the block buffers, and again 0 failures. Every far read was in the RAM and in the block buffers, as the walk now proves for the touch's frame. The far reads at the pole's column came about 512 px (two pages) before it or further left: the nearest was 515 px left of the left end of the pole's range.

## What is not proved

* `tilesCol` itself: right after a read of the side check two or more pages before the pole's, at the pole's column, the byte read is not one of the pole's tiles. Such a read is about 512 px (two pages) or more before the pole's column. It reads the byte of the block buffers that will hold the pole's column when the area parser draws it. Why the parser has not drawn it yet needs the screen's scroll and the area parser across frames (the measurements of the page `f-6-17-4-PoleTileHeight.md`: the parser's column is at most 384 px right of the screen's left edge). Round 27: the parser's invariant at control, that its rule of one frame keeps it, the first half of that rule on a real frame, and the arithmetic from which `tilesCol` would follow: [The area parser against the screen's left edge](f-6-17-8-PoleParser.md); `tilesCol` is unchanged.
* `yKeep` is unchanged in this round (round 25: it is gone, [The height kept inside the collision routine](f-6-17-6-PoleTileKeep.md)). Measured in this walk (`pole-far-stores`): inside the collision routine there are 20 places of stores through an index or a pointer whose target the walk cannot keep off the height. 16 are the block objects' `STA zp,X` and `STY zp,X` (the head's bump and the bricks): their index is the block objects' offset, which the walk does not know. The game changes that offset only by flipping its lowest bit, but that it stays 0 or 1 is a fact across frames (not measured here). 3 are `STA (zp),Y` into the block buffers with a pointer the walk does not know (the head's bump, and two places that erase a coin). One is the score's `STA abs,Y`, whose range wraps around to the height's place when `Y` is not known. The height cannot simply be left to the side check's own compares of it: for a small or crouching player the upper side read adds 24 px, so a height from 216 px up to 227 px would read the 14th row, past the block buffers. The collision routine's own bound (207 px) is needed.
* `bufAll` is unchanged. Measured in the walk of the frames from control (`pole-far-stores`, table 46,576 states): at 76 places the walk cannot show that a step writes no byte of the block buffers. At 38 of them the walk knows enough bits of the stored byte to say it is not one of the pole's tiles. The other 38: 27 `STA abs,X` and 9 `STA abs,Y` into the objects' tables just below the block buffers, with an index of which the walk knows no bit; the area parser's `STA (zp),Y`, which draws the pole's column; and the block objects' `STA (zp),Y` that puts a bumped block's tile back. The statement of `bufAll` would not get smaller by proving the 38: a store of a byte that is not a pole's tile meets it anyway.

**Files:** `Theorems/PoleTileFar.lean`; private `Proof/PoleTiles.lean` (`pole_check_f` in place of `pole_check_h`, since round 25 replaced by `pole_check_z` of `PoleTileKeep`: `poleCheckF`, its search included, 135 to 148 s natively; the whole file 162 s in the last full build, with other places building on the machine, and a peak of about 4.3 GB; with `pole_check_h` it took 196 s under load and 127 s on a quieter machine). The programs `pole-far-search` (the search and the check) and `pole-far-check FM2 [N]` (the real frames above).
