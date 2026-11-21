[← Back](README.md) | [English](f-6-17-3-PoleTileRead.md) | [Japanese](f-6-17-3-PoleTileRead-ja.md)

# The pole's tiles at the touch: the reads near the pole are in the block buffers

The field `tilesRead` of `PoleJoin.Run` is gone. It asked `ReadPre` at every read of the side check up to the routine's write: the read is in the RAM, it is in the block buffers, and a pole's tile in the pole's column is read only with the page at most one before the pole's. The first two parts are now proved for every read near the pole. Two smaller fields take its place. Each is a condition on one state.

## The new fields

Write `y` for the player's height, `page` for his page, `pg` for the pole's page, `tile(v)` for "the byte `v` is one of the pole's two tiles", and `idx` for the offsets of the side check's four reads. `h` is the bound of the collision routine's own check of the height (its first compare of the height, read from the ROM).

* `ySide` (`YSide`): up to the write, at the start of the side check, `y < h`.
* `tilesFar` (`TileFar`): up to the write, right after a read of the side check (`pc = read + 2`, `save ∈ idx`), if `page + 1 < pg` then `¬ tile(A)`.

Both are true on real frames for a plain reason. The collision routine leaves at once when `y ≥ h`, and between that check and the side check the height is stored only by the landing, which clears its low 4 bits. The walk does not show this (see the end of this page). When he is two or more pages before the pole, the pole's column has not been drawn (see "Measured" below).

## What is proved

Theorem `no_write_frameU` (file `Theorems/PoleTileRead.lean`) is `PoleTileWalk.no_write_frameP` with `YSide` and `TileFar` in place of `ReadPre`:

```
frameCheckU ∧ FrameStart(s₀) ∧ ColMap(s₀) ∧ (∀ j ≤ n, CleanK ∧ PosAt ∧ HypR ∧ BufAt ∧ YSide ∧ TileFar at s_j)
  ⇒ rt(s_{n+1}) ≠ the pole's routine
```

Inside its induction, every `j ≤ n` has `ColMap(s_j)` and a live state `A_j` of the walk with `TR(A_j, s_j)`: if `A_j` is right after the read (`pc = read + 2`) and knows that the offset is one of `idx`, then `TileRead(s_j)`. This is where the walk uses `TileRead` (the split after the read, `PoleFrame.zoneT`), so `cov_zoneTW` and `cov_preTW` are `PoleFrame`'s lemmas with `TR` in place of `TileRead`. The pieces before a step keep the RAM (`preK_same`), so they know what `A_j` knows of the offset.

The walk is the walk of `PoleTileWalk` with two more splits and one more test (`walkU`):

* At the start of the side check, when the page may be the pole's or the one before (`nearP`): the height, in 7 pieces of known high bits that cover `[0, h)` (`yPieces`, `splitY`). The pieces are cut where the side check's own compares of the height cut, so each compare has one result on each piece. The pieces cover `y < h` by the check `yCover`, and `YSide` says `y < h` there (`cov_splitY`).
* At the addition of the height's adder in the block buffer routine, in a side check near the pole: the accumulator, bit by bit (`fullA`, `cov_fullA`). The abstract addition knows its result only when both sides are known, so this makes the sum and the row known.
* On a step from a piece `A` to a state `B` (`readP`): if `B` is right after the read and knows that the offset is one of `idx`, and at `A` the page may be the pole's or the one before, then at `A` the pointer and `Y` are known, `pointer + Y < 0x2000`, and `(pointer + Y) mod 2048 ∈ B`. A state right after the read is never covered by a state of the table, so the next live state there is `B` itself.

Then `TileRead` right after a read follows (`tileRead_afterU`). Let `m` be the machine at the read and `m'` the one after it.

* If `page + 1 < pg`, then `TileFar(m')` says the byte is not a pole's tile.
* Otherwise the page at `A` may be the pole's or the one before. So `readP` gives the pointer and `Y`. The read is in the RAM and in `B`. The byte read is `m.ram[i]` with `i = (pointer + Y) mod 2048` (`RoomBlocks.step_lda_izy`, `readVal_eq`). If it is a pole's tile, `ColMap(m)` gives `col(i)`. And `pg ≤ page + 1` is the case itself.

The check `poleCheckU` (the checks of `PoleFrame` before its walk, `yCover`, this walk, the facts of the ROM at the read, the check of `SubsOnce`, the walk of the frames of `PoleTileWalk`) is proved natively (private `pole_check_u`). `touch_right_of_leftU` and `inRange_of_frameU` are the theorems of `PoleTileWalk` with the new conditions. `PoleJoin.Run.inRange` uses `inRange_of_frameU`.

The search for the table keeps the height's piece through the side check. At the store of the horizontal sum and at the load of the height it keeps only what the pointer needs (the sum's high 4 bits, the position's piece), as `PoleFrame` does at the mask of the sum, unless the sum is in the pole's column on its page. At the mask it forgets the accumulator's low 4 bits (the mask clears them). These are search choices only. The walk checks every state.

## Measured

`pole-read-check FM2 96` (every instruction of every frame, in control or not, from the first control on):

| run | frames | instructions | starts of the side check (largest height) | side reads near the pole (out of the RAM or `B`) | after a side read far from the pole (a pole's tile) | pole's tiles written into `B` (smallest page, smallest `P − left`) |
|---|---|---|---|---|---|---|
| the TAS, frames 1 to 1239 after the first control | 1,239 | 5,561,241 | 871 (176) | 1,048 (0) | 2,326 (0) | 10 (11, −230 px) |
| the TAS from frame 1089, then other inputs | 20 | 79,380 | 20 (176) | 77 (0) | 0 | 0 |
| own random inputs from frames 900 to 1089 of the TAS, 48 runs, no Start | 6,917 | 30,419,655 | 6,861 (176) | 24,832 (0) | 2,124 (0) | 90 (11, −238 px) |
| own random inputs with Start, 48 runs | 7,680 | 23,030,036 | 3,222 (176) | 10,481 (0) | 2,136 (0) | 60 (11, −230 px) |

`YSide` and `TileFar` held everywhere (bad 0). The bound `h` is 207 px; the largest height at the start of the side check was 176 px.

For the page part (`TileFar`): every write of a pole's tile into `B` came when he was on the page before the pole's or later, at most 238 px left of the left end of the pole's range. Of the 2,770 frames that started with him two or more pages before the pole's, none had a pole's tile anywhere in `B`, and at none of the 6,586 far side reads was there a pole's tile anywhere in `B`. So a smaller fact would do: "two or more pages before the pole's, `B` holds no pole's tile" at the start of a frame, if the far reads were known to be in `B`. The walk does not know the address of a far read (it does not split the position there), so this is not used.

The walk's search: 7,681,437 steps, 345,444 states in the table, about 42 s natively (the walk of `PoleTileWalk`: 8,490,979 steps, 352,579 states, about 46 s).

**False in the walk:** a first form of the test at the read asked the pointer and `Y` at every read whose offset may be one of `idx`. It failed at 454 visits: reads of the block buffer routine for other objects (an enemy's side check, a vine), where the walk knows neither the offset nor the page. Keeping the offset in the search brought this to 89, in a loop of the enemies' side check whose counter the walk forgets. The test is now asked only where the walk uses `TileRead`: right after the read, on a piece that knows the offset. With it there are 0 failures. Also, a first search that kept the whole position and the whole sum through the block buffer routine near the pole needed 5.4 GB and 27 million steps; the search above needs 2.7 GB.

## What is not proved

* `ySide`: in the walk, a store through an index that the walk does not know forgets every byte that the guard does not protect, and the height is not protected. The routine of the head's collision has such stores (the block object's slot, the offset in the screen's buffer). Measured: a walk that splits the height at the collision routine's own first load of it (9 pieces, no hypothesis) and keeps it to the side check had 315 starts of the side check near the pole with the height not known, and 10,368 visits of the read failed the test (its table grew to 764,530 states, 5.1 GB). So `ySide` stayed here. It is gone since: the walk of [The height at the side check](f-6-17-4-PoleTileHeight.md) protects the height, with the new condition `yKeep` on single instructions.
* `tilesFar`: why the pole's column is not drawn while he is two or more pages before the pole needs the screen's scroll and the area parser across frames.
* `bufAll` is unchanged.

**Files:** `Theorems/PoleTileRead.lean`; private `Proof/PoleTiles.lean` (`pole_check_u` in place of `pole_check_p`: the search about 45 s and the walk about 50 s natively, 2.8 GB; the whole file 104 to 123 s, about as before; since round 23 the file holds `pole_check_h` of [the height at the side check](f-6-17-4-PoleTileHeight.md) in place of `pole_check_u`). The programs `pole-read-search` (the search and the check) and `pole-read-check FM2 [N]` (the real frames above).
