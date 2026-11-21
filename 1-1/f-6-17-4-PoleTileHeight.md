[← Back](README.md) | [English](f-6-17-4-PoleTileHeight.md) | [Japanese](f-6-17-4-PoleTileHeight-ja.md)

# The pole's tiles at the touch: the height at the side check, from the collision routine's own check

The field `ySide` of `PoleJoin.Run` is gone. It asked that at each start of the side check, up to the routine's write, the height is below the bound of the collision routine's own check of it. Now the walk of the touch's frame keeps the height from that check to the side check. A field of the same kind as `posKeep` and `keep.cleanE` takes its place: a condition on single instructions.

## The new field

Write `y` for the player's height and `yI` for its place in the RAM. A machine is *inside the collision routine* (`InZone`) when its stack pointer is at most the one of the routine's foot check and the stack holds the routine's return address there (as the walk's `PipeWrites.inZone`). For an instruction at `m`, `t` is the target of its store through an index or a pointer (`wTarget`).

* `yKeep` (`YAt`): up to the write, if `m` is inside the collision routine and the instruction is a store through an index or a pointer with `t < 0x2000`, then `t mod 2048 ≠ yI`.

In words: inside the collision routine, no store through an index or a pointer writes the height. The player's own vertical move writes the height through an index (the gravity routine's `STA zp,X` with `X = 0`), but it comes before the collision routine.

## What is proved

Theorem `no_write_frameH` (file `Theorems/PoleTileHeight.lean`) is `PoleTileRead.no_write_frameU` with `YAt` in place of `YSide`:

```
frameCheckH ∧ FrameStart(s₀) ∧ ColMap(s₀) ∧ (∀ j ≤ n, CleanK ∧ PosAt ∧ YAt ∧ HypR ∧ BufAt ∧ TileFar at s_j)
  ⇒ rt(s_{n+1}) ≠ the pole's routine
```

The walk is the walk of `PoleTileRead` with these changes (`walkH`):

* **Inside the collision routine the guard protects the height** (`GY`): it is `PoleFrame.Pole.GP` (which protects the position's pixel and page) with `yI` too. At a store through an index that the walk does not know, the walk forgets every byte that the guard does not protect; inside the routine it now keeps the height. Outside the routine the guard is `GP`, as before. So the steps (`kstepH`) are: at the move routine's stores of the position, those of `PoleFrame.kstepT`; inside the routine, those of `FrameKeep.kstep` with `GY`; elsewhere with `GP`. A state of the walk inside the routine covers only machines inside it (`inZone_of`), and there `CleanK` of `GY` follows from `CleanK`, `PosAt` and `YAt` (`cleanK_GY`). `s_kstepH` is the step lemma.
* **The height at the collision routine's first load of it** (`HP.band`, `PoleTileRead.bandAt`), when the page may be the pole's or the one before: the height is split into 5 pieces of known high bits that hold every value `0 ≤ y < 256` (`bandPieces`, cut at `hiR` = 208 px, the bound up to a whole row). No hypothesis: the pieces cover every byte (`coverN`, `cov_splitP`). The routine's compare that follows leaves on the two pieces at or above 208 px.
* **At the start of the side check**, near the pole: the walk tests that the largest value of the height's piece is below `hiR`. If the test passes, the height is split into the 7 pieces of `PoleTileRead` (`yPieces`), which cover `[0, hiR)`; the cover needs only `y ≤ maxv < hiR` (`cov_zoneH`). If the test fails, nothing is split, and the test at the read (`readP`) would fail.
* At the two additions to the height with `ADC abs,Y` (the block buffer routine's and the head routine's, `HP.wk`), an accumulator with only its high 4 bits known is forgotten when the addition is not the side check's near the pole. Without this the walk's special addition (`PipeWrites.aadcH`) fails when the table byte has low bits. Forgetting a byte is always a cover.

So `YSide` is not assumed: on every path from the collision routine's check to the side check, the walk knows the piece of the height. `PoleTileRead.tileRead_afterU` gives `TileRead` right after a read as before.

The check `poleCheckH` (the checks of `PoleFrame` before its walk, the covers of the pieces, this walk, the facts of the ROM at the read, the check of `SubsOnce`, the walk of the frames of `PoleTileWalk`) is proved natively (private `pole_check_h` in `Proof/PoleTiles.lean`, in place of `pole_check_u`). `touch_right_of_leftH` and `inRange_of_frameH` are the theorems of `PoleTileRead` with `YAt`. `PoleJoin.Run.inRange` uses `inRange_of_frameH` with the field `yKeep`.

The search for the table keeps the height's piece at the start of the side check near the pole (`normH`); elsewhere it is `PoleTileRead`'s. This is a search choice only. The walk checks every state.

## Measured

The walk's search (`pole-height-search`): 8,196,666 steps, 376,976 states in the table, 0 failures, about 41 s natively (the walk of `PoleTileRead`: 7,681,437 steps, 345,444 states). The whole check `poleCheckH` is true natively in about 106 to 113 s (`pole-height-search`: the search 43 s, the check 106 s).

**False in the walk:** the first search failed 15 times at the block buffer routine's addition to the height, and, with that fixed, 810 times at the head routine's addition to the height. There the accumulator held a piece of the height with its high 4 bits known, so the walk took its special addition (`PipeWrites.aadcH`), which fails when the table byte has low bits. Forgetting such an accumulator at these two additions (`HP.wk`) gave 0 failures.

`pole-height-check FM2 96` (every instruction of every frame, in control or not, from the first control on):

| run | frames | instructions | inside the collision routine | stores through an index or a pointer that write the height (inside the routine) | touches: instructions up to the write |
|---|---|---|---|---|---|
| the TAS, frames 1 to 1239 after the first control | 1,239 | 5,561,241 | 353,730 | 646 (0) | 1: 2,924 |
| the TAS from frame 1089, then other inputs | 20 | 79,380 | 2,141 | 3 (0) | 1: 2,922 |
| own random inputs from frames 900 to 1089 of the TAS, 48 runs, no Start | 6,917 | 30,419,655 | 3,424,305 | 3,196 (0) | 9: 26,805 |
| own random inputs with Start, 48 runs | 7,680 | 23,030,036 | 1,616,763 | 1,650 (0) | 4: 11,958 |
| own random inputs from the first control, 24 runs of 1,300 frames, half with Start | 31,200 | 108,667,714 | 9,354,428 | 10,737 (0) | 0 |

`YAt` held on every instruction of every frame (bad 0), not only up to the write on the 15 touches. With `N = 400` (200 runs without and 200 with Start, and 100 runs of 1,300 frames from the first control): 191,042 frames, 682,242,273 instructions, 58,789,122 of them inside the collision routine, 81 touches with 240,912 instructions up to the write, and again 0 failures. At the 29,648 starts of the side check the height was below the bound (207 px) every time; the largest was 176 px.

**False on real frames:** a first form of the field said "a store through an index or a pointer that writes the height is the gravity routine's store of it, with the index 0". It held up to the write on every touch, but on other frames it was false at 12 instructions, all one store: the store through a pointer of the routine that clears the RAM when an area is set up (on the TAS, the frames 418 and 732 after the first control: the two changes of area; the other 10 in the random runs from the first control). That store is outside the collision routine, so the present form holds there. Neither form can go into the guard of `keep.cleanE`: the gravity routine writes the height through an index on every frame in control.

## What is not proved

* `yKeep` itself: that inside the collision routine no store through an index or a pointer writes the height. It held on every measured instruction of every frame (above). Round 25: `yKeep` is gone; the walk now tests every such store inside the routine, with two bytes that the frames keep. In its place is the new field `keepB` ([The height kept inside the collision routine](f-6-17-6-PoleTileKeep.md)).
* `tilesFar` (since round 24 it is gone: the reads far from the pole are in the block buffers too, and only the reads at the pole's column stay assumed, as the field `tilesCol`: [The reads far from the pole are in the block buffers](f-6-17-5-PoleTileFar.md)): why the pole's column is not drawn while he is two or more pages before the pole needs the screen's scroll and the area parser across frames. A far read on the page two before the pole's, in the pole's column on that page, reads the same byte of the block buffers as the pole's column, so the map `ColMap` alone does not settle it. Measured on the TAS and 48 random runs (5,331 frames): the area parser's column is at most 384 px (one and a half screens) right of the screen's left edge; a pole's tile is in the block buffers only once the parser's column has come to the pole's column; near the pole he is at least 56 px right of the screen's left edge. A side read reaches the pole's column two pages before the pole's only when he is within 32 px of it, and then, if he is right of the screen's left edge, the parser's column is at least 96 px short of the pole's column. So `tilesFar` would follow from these three facts across frames. They need the bytes of the screen's edge and of the parser's column as symbols, and walks of the frames that keep them.
* `bufAll` is unchanged. Measured in the walk of the frames from control (table 46,576 states): at 76 places, all stores of `A` through an index or a pointer (`STA abs,X`, `STA abs,Y`, `STA (zp),Y`), the walk cannot show that the step writes no byte of the block buffers. With the objects' offset protected too, 75 places remain; the walk of the touch's frame has the same 76 and 75. So protecting that byte does not bound these indexes.

**Files:** `Theorems/PoleTileHeight.lean`; private `Proof/PoleTiles.lean` (since round 24 it holds `pole_check_f` of `PoleTileFar` in place of `pole_check_h`, and since round 25 `pole_check_z` of `PoleTileKeep`; `pole_check_h` in place of `pole_check_u`: `poleCheckH`, its search included, about 106 to 113 s natively; the whole file 196 s in the last full build, with other places building on the machine, and a peak of 3.1 GB; a first version of this walk took 127 s on a quieter machine; `pole_check_u` took 104 to 123 s). The programs `pole-height-search` (the search and the check) and `pole-height-check FM2 [N]` (the real frames above).
