[← Back](README.md) | [English](f-6-17-16-PoleRing.md) | [Japanese](f-6-17-16-PoleRing-ja.md)

# The pole's tiles: the parser stores a column at its own place in the ring

Round 33 ([the slot of the area parser](f-6-17-14-PoleSlot.md)) made the field `bufAll` ask one more thing at each store of a pole's tile into the block buffers (`PoleSlot.NoTileC`): the area parser's column at the frame's start has come to the pole's column. This round asks less there. The store must be in the parser's own column of the block buffers, or the parser must be at the pole. The rest is proved.

## The words

* A pole's tile is the ball's tile or the shaft's tile.
* `colP = 16·pg + c` is the pole's column, counted as the parser's column is counted (16 columns a page).
* `c(n)` is the parser's column at the start of frame `n` from control above ground (`PoleJoin.parColOf`).
* The block buffers hold 32 columns: two buffers of 16 columns each, 16 bytes a row. They are a ring: the column `x` of the level goes into the ring's column `x mod 32`.
* `ringCol(i)` is the ring's column of the RAM byte `i` in the block buffers: 16 for each buffer before it, and its place in its row (`PoleRing.ringCol`).

## The new condition of `bufAll` (`PoleRing.BufVM`)

```
before (round 33):  NoTileC(c, m)  :=  each byte i of the block buffers that the step changes to a pole's tile:   colP ≤ c
now:                NoTileM(c, m)  :=  each byte i of the block buffers that the step changes to a pole's tile:   colP ≤ c   ∨   ringCol(i) = c mod 32
```

`BufVM(c, m)` is `PoleKeepFar.BufV(m)` and, at the same stores, `NoTileM(c, m)`, with `c = c(n)` on frame `n`. `NoTileC ⇒ NoTileM`, so the new field asks less (`bufVM_of_VS`).

In words: a store of a pole's tile into the block buffers is in the parser's own column of the ring, or the parser's column has come to the pole's. The parser stores a column of the block buffers in its task `AreaParserCore`. Each frame runs at most one task, and that task does not move the column. So at the parser's store the parser's column is that of the frame's start.

## Why this is enough (`PoleRing.noTileC_of_M`)

* `BufV` (asked since round 26) puts a pole's tile only in the pole's column. Every byte of the pole's column is in the ring's column `colP mod 32` (`RingOK`, from the check `ringCheck` on the places).
* So a store of a pole's tile with `ringCol(i) = c mod 32` has `c ≡ colP (mod 32)`.
* If also `colP < c + 32`, then `colP ≤ c`. This is `NoTileC(c)`, which is all the walk of round 33 used (`PoleSlot.frames_slot`, `no_write_frameZS`).

```
NoTile(m) ∧ NoTileM(c, m) ∧ RingOK ∧ colP < c + 32   ⇒   NoTileC(c, m)
```

## The bound `colP < c(n) + 32` (`PoleParserRun.low₀`, `PoleJoin.Run.low`)

* At control above ground, `colP < c(0) + 32`. This is a check on the rows of the change out of the side pipe (`PoleParserRun.lowCheckK`, the private `pole_parser_low`), as round 28 checked the column below 16 there (`PoleParser.col₀`).
* The parser's column does not go back from frame to frame (`PoleParserRun.colMono_run`, round 33). So `colP < c(n) + 32` at every frame's start up to the touch's frame (`PoleRing.low_mono`).

`PoleJoin.Run.TileColAll` (what the touch's frame needs of the parser) has two more parts: `colP < c(0) + 32` and `RingOK`. Both are theorems on the route (`PoleParserRun.tilesCol_run`, `tilesCol_route`).

## Signatures that changed, exactly

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleRing.BufVM (spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (trace (S.seq (a + n)) (S.inp (a + n)) k)` (was `PoleSlot.BufVS`).
* `PoleJoin.Run.TileColAll R := (∀ n, n + 1 < ix g → parColOf(all n) ≤ parColOf(all (n+1))) ∧ SlotMap (spotsF sy m0) (parColOf(all 0)) (all 0) ∧ colP (spotsF sy m0) < parColOf(all 0) + 32 ∧ RingOK (spotsF sy m0)`.
* `PoleJoin.Run.bufC₁` takes `(hT : R.TileColAll)` before `j`. New: `PoleJoin.Run.low`.
* `PoleParserRun.tilesCol_run` takes `(hL : colP (spotsF sy m0) < parColOf sy m0 (R.seq 0) + 32) (hRg : PoleRing.RingOK (spotsF sy m0))` after `hNT`.
* `PoleParserRun.tilesCol_route` takes `(hmL : lowCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)` after `hmJ`.
* New in `PoleParserRun`: `rowLow`, `lowCheckK`, `low_of_state`, `low_of_invL`, `EndRunQ.low`, `ring_of_low`, `low₀`. New file `Theorems/PoleRing.lean`: `ringCol`, `RingOK`, `ringCheck`, `ringOK_of_check`, `NoTileM`, `BufVM`, `noTileM_of_C`, `bufVM_of_VS`, `bufV_of_VM`, `bufAt_of_VM`, `noTileC_of_M`, `bufVS_of_VM`, `bufC_of_VM`, `low_mono`.
* `route_1_1` still concludes `1748 + j ≤ L`. One new check on the ROM: `pole_parser_low` (`native_decide`, in the new private file `Proof/PoleRing.lean`).

## Measured

`pole-keep check FM2 96` (4 min 32 s, 3.6 GB peak with the other checks beside it) runs every instruction of 41,021 frames that start in control (167,758,026 instructions; the TAS, its frame 1089 then `02808080`, own random inputs from frames 900 to 1089 with and without Start, own random inputs from the first control):

| | TAS | frame 1089, then `02808080` | random 900–1089, no Start | random 900–1089, with Start | random from the first control |
|---|---|---|---|---|---|
| stores that change a byte of the block buffers to a pole's tile | 10 | 0 | 90 | 60 | 0 |
| of them where `NoTileM` is false | 0 | 0 | 0 | 0 | 0 |
| the ring's column of the byte minus the parser's column mod 32, at them | 0 | – | 0 | 0 | – |
| the least `c + 32 − colP` at a frame start above ground after the room | 18 | 47 | 19 | 18 | – (no such frame) |

All 160 stores of a pole's tile are made by one instruction, the parser's store of a column. `pole-keep parser FM2 96`: on every frame that starts in control (719 on the TAS, 14,318 and 25,980 on the random runs) the block buffer's column equals the parser's column mod 32. The exit code of `pole-keep check` now also asks `NoTileM` above ground and the least bound after the room above 0 (exit 0).

## What is not proved

* `bufAll` at its 7 places: a store of a pole's tile only in the pole's column (`BufV`, round 26), and in the ring's column of the parser's column or with the parser at the pole (`NoTileM`).
* The second part is true of the parser's own store, but a proof needs one more byte. `AreaParserCore` does not compute the store's address from the parser's column. It reads a third byte, the block buffer's column, and stores at that column of the ring. The column's step (`IncrementColumnPos`) adds one to that byte (mod 32) together with the column. So `B ≡ c (mod 32)` holds on real frames (round 27 measured it: 0 frames with `B ≠ c mod 32`), but the parser's walks do not follow `B`. A proof needs walks of each frame that follow `B` as they follow the column (split by its value on the frames of the column's step), and a walk of the end of `AreaParserCore` that knows the pointer of the store from `B`.
* `tilesCol` (`TileSlotC`) and `ctlU`: not changed this round. `keepB`: not changed.

**Files.** `Theorems/PoleRing.lean` (new); `Theorems/PoleJoin.lean` (`bufAll`, `TileColAll`, `Run.low`, `Run.bufC₁`, `Run.slotStart`, `Run.inRange`, `Run.tilesStart`, `Run.bufAt₁`); `Theorems/PoleParserRun.lean` (the rows check, `low₀`, `tilesCol_run`, `tilesCol_route`); `Main.lean` (`genPoleRing`, the Route block, the round 34 counters of `pole-keep check`).
