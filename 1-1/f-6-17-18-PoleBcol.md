[← Back](README.md) | [English](f-6-17-18-PoleBcol.md) | [Japanese](f-6-17-18-PoleBcol-ja.md)

# The pole's tiles: the parser stores its column at the block buffer's column

Round 34 ([the parser stores a column at its own place in the ring](f-6-17-16-PoleRing.md)) made the field `bufAll` ask, at each store of a pole's tile into the block buffers, that the store is in the ring's column of the area parser's column of the frame's start, or that the parser's column has come to the pole's (`PoleRing.NoTileM`). On real frames every such store is made by one instruction, the parser's store of a column. This round proves that part at that instruction, so `bufAll` asks it only of the other stores, where no measured store of a pole's tile happens.

## What the code does

* The parser's store of a column (in `AreaParserCore`) does not compute its place from the parser's column. It reads a third byte, the block buffer's column `B`, takes the address of that column of the block buffers (`GetBlockBufferAddr`), and stores the 13 rows through a pointer.
* The column's step (`IncrementColumnPos`) adds one to the parser's column (with its page) and one to `B`, mod 32.
* The loop command's step back (`ExecGameLoopback`) subtracts four pages from the parser's page. Four is even, so the column mod 32 stays.

## The words

* `c = 16·page + col` is the parser's column (`PoleJoin.parColOf`), `col` its column in the page.
* `BInv(m)`: `B = c mod 32` and `col < 16` (`PoleBcol.BInv`).
* `StoreRing(b, m)`: every byte of the block buffers that the step of `m` changes is in the ring's column `b` (`PoleRing.ringCol`).

## The walk (`Theorems/PoleBcol.lean`)

`walkB` is the walk of one whole frame in control of `FrameKeep`, in one of 32 pieces `b`:

* The frame starts with `B = b`, `col = b mod 16`, and the page's lowest bit `b / 16` known (`startB`). This is the case `B = b` of `BInv`.
* Its guard protects `B`, the column and the page (`guardB`). The field `keep.cleanE` protects the column and the page already (they are bytes of `FrameKeep.parE`); the new field `bKeep` says that a store through an index or a pointer does not write `B`.
* At the column step's `INC` of the page and at the entry of the loop command's step back, a page that is not known is split into its values that agree with its known bits (`prePage`). So the page's lowest bit stays known through them.
* At the parser's store with no NMI pending, the store's target is known, and if it is in the block buffers it is in the ring's column `b` (`storeOK`).
* At the frame's end, `B`, the column and the page's lowest bit are known and meet `BInv` (`endB`).

The tables come from 32 searches (no part of the proof). On the ROM: about 47,000 states for each piece. The check of all 32 pieces takes 119 s natively (`pole-keep bcol`, peak 0.5 GB). It is the longest check of this round.

## What it proves

`frame_bcol`: a frame in control that starts with `BInv`, whose instructions meet `CleanK` of the walk's guard, ends with `BInv`, and at each of its parser's stores:

```
StoreRing(B at the frame's start, trace(m, k))
```

`frames_bcol`: with `BInv` at control (a check on the rows of the change out of the side pipe, `PoleParserRun.bInv₀`), on every frame `n` up to the touch's frame (`n < ix g`):

```
BInv(all n)   ∧   ∀ k,  pc(trace(all n, k)) = the parser's store  →  StoreRing(c(n) mod 32, trace(all n, k))
```

`StoreRing(c mod 32, m)` gives `NoTileM(c, m)` (`noTileM_of_ring`). So at the parser's store `NoTileM` is a theorem, on the frames before the touch and on the touch's frame.

## The fields

Changed:

```
bufAll :  PoleRing.BufVR(spotsF, c(n), the parser's store, trace(all n, k))
          (round 34's BufVM, but NoTileM only at an instruction that is not the parser's store; BufVM ⇒ BufVR: bufVR_of_VM)
```

Added, on every instruction of every frame up to the touch's frame (`n < ix g`):

```
bKeep :  farStore([B]) = false  →  a store through an index or a pointer does not write B
```

`bufAll` asks less than before. `bKeep` is new; it is the kind of `keepB`.

Signatures that changed, exactly:

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleRing.BufVR (PoleFrame.spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (PoleBcol.bcOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k)`.
* New field `PoleJoin.Run.bKeep : ∀ n, n < ixOf … g → ∀ k, PoleBcol.BcR (PoleBcol.bcOf sy m0) (trace (S.seq (a + n)) (S.inp (a + n)) k)`.
* `PoleJoin.Run.TileColAll` has one more part at its end: `∀ n, n < ix g → ∀ k, pc(trace(all n, k)) = (bcOf sy m0).store → PoleRing.NoTileM (spotsF sy m0) (parColOf sy m0 (all n)) (trace (all n) (inp n) k)`.
* `PoleParserRun.tilesCol_run` takes `(hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0))` after `hRg`.
* `PoleParserRun.tilesCol_route` takes `(hmB : bInvK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcB : PoleBcol.bcolCheck sy m0 = true)` after `hcC`.
* New in `PoleRing`: `BufVR`, `bufVR_of_VM`, `bufVM_of_R`, `bufAt_of_VR`. New in `PoleParserRun`: `rowB`, `bInvK`, `bInv_of_state`, `bInv_of_invL`, `EndRunQ.bInv`, `bInv₀`.
* One new symbol: `ExecGameLoopback`.
* `route_1_1` still concludes `1748 + j ≤ L`. Two new checks on the ROM: `pole_bcol_walk` and `pole_bcol_rows` (`native_decide`, in the new private file `Proof/PoleBcol.lean`).

## Measured

`pole-keep parser FM2 96`, on the frames that start in control (719 on the TAS, 14,318 and 25,980 on the random runs):

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frame starts in control with `BInv` false (any area) | 0 | 0 | 0 |
| instructions where `bKeep` is false (any area) | 0 | 0 | 0 |
| stores of a pole's tile into the block buffers | 10 | 150 | 0 |
| of them away from the parser's store (where `bufAll` still asks `NoTileM`) | 0 | 0 | 0 |
| at the parser's store, bytes changed out of the ring's column of `B` | 0 | 0 | 0 |

## What is not proved

* `bufAll`: `BufV` (a pole's tile goes only into the pole's column, round 26), and `NoTileM` at the stores other than the parser's store of a column (no measured store of a pole's tile is there).
* `bKeep`: no store through an index or a pointer writes `B` (0 measured).
* `BufV` at the parser's store is still asked: that its rows hold a pole's tile only in the pole's column. A proof needs the metatiles that the parser draws.

**Files.** `Theorems/PoleBcol.lean` (new); `Theorems/PoleRing.lean` (`BufVR`); `Theorems/PoleJoin.lean` (`bufAll`, `bKeep`, `TileColAll`, `Run.bufC₁`, `Run.slotStart`, `Run.tilesStart`, `Run.bufAt₁`); `Theorems/PoleParserRun.lean` (the rows check, `bInv₀`, `tilesCol_run`, `tilesCol_route`); `Smbrta/Syms.lean`, `tools/smb-symbols.txt` (`ExecGameLoopback`); `Main.lean` (`genPoleBcol`, the Route block, `pole-keep bcol`, the counters of `pole-keep parser`).
