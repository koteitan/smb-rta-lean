[← Back](README.md) | [English](f-6-17-17-PoleCoin.md) | [Japanese](f-6-17-17-PoleCoin-ja.md)

# The pole's tiles: no coin in the block buffers, so the control byte is not 6

Round 33 left the field `ctlU` ([the area parser's lag may grow up to 157 px](f-6-17-15-PoleLag.md)): on each frame before the touch's frame that comes to the player's routine, at each `UpdScrollVar`, the screen buffers' control byte is not 6, or the parser's lag `S + 3·N` is below 157 there. This round removes `ctlU`. A walk of the whole frame follows the control byte and proves it is not 6 at every `UpdScrollVar` of these frames. In its place come three conditions of the same kinds as `bufAll` and `keepB`: on stores into the block buffers, on reads of them, and on stores to the control byte.

## What the code does with the control byte

* The screen update at the start of each frame sets the control byte to 0.
* In the game core, before `UpdScrollVar`, only `RemoveCoin_Axe` writes the control byte, and it writes 6. It runs when the player's collision routine finds a coin's tile (with the head, a foot or a side), when the axe is touched, and when the check above a bumped block finds a coin's tile (`CheckTopOfBlock`).
* The axe's code also writes the mode by its address. The frames before the touch's frame write no mode by its address (`FrameKeep.Frames.noStore`).

So the control byte is 6 at `UpdScrollVar` only on a frame where he takes a coin. Above ground in 1-1 the block buffers hold no coin's tile.

## The words

* A coin's tile is one of the two tiles that the coin's check compares with (`sy.CoinTile`, `sy.CoinTile2`: the operands of the two comparisons of `CheckForCoinMTiles`).
* `ctl` is the screen buffers' control byte (the operand of the first load of `UpdScrollVar`).
* The coin's map of a machine `m`: no byte of the block buffers holds a coin's tile. It is `PoleTileWalk.ColMap` of the places `PoleCoin.Coin.Q`: the places of the pole's map with the two coin's tiles in place of the pole's, and with no column.
* The two reads: the collision routine's read of the block buffers (its `LDA (zp),Y`, `Spots.read`) and the read of the check above a bumped block (the `LDA (zp),Y` of `CheckTopOfBlock`).

## The walk (`Theorems/PoleCoin.lean`)

`walkC` is the walk of one whole frame in control of `FrameKeep` with more tests and pieces on the way:

* Its guard is `FrameKeep.guardK` with `ctl` protected too (`guardC`). So a store whose target the walk does not know keeps `ctl`. The screen update's store of 0 makes `ctl` known.
* Right after the player's read (the index `X` known 0) and right after the read above a bumped block, the byte read is split into pieces, one for each bit at which the two coin's tiles agree: in each piece that bit is known and differs from the first coin's tile (`pieceC`). A check on the ROM's values shows that these pieces hold every byte that is not a coin's tile (`PoleEntryRule.tilesCover`). With them the coin's check does not branch to the coin's code.
* A path stops at an instruction that writes the routine, the mode or the task by its address (as `FrameKeep.walkKC`).
* On every state of the way: at `UpdScrollVar`, `ctl` is known and not 6 (`ctlOK`); the step writes no byte of the block buffers, or it is a store through an index or a pointer (`PoleTileWalk.okSK`); a state right after one of the two reads comes from the read, with no NMI pending (`pairC`).

The table of the walk comes from a search (no part of the proof). On the ROM: 5,854 states, and the check takes 0.4 s natively (`pole-keep coin`).

## Why the pieces are right (`coinRead_after`, `frame_of_walkC`)

The walk carries the coin's map from step to step: a step that `okSK` allows writes no byte of the block buffers, or it is a store through an index or a pointer, which writes no coin's tile there (`BufAt`). At one of the two reads, if the byte read is a coin's tile, the read is in the block buffers (`ReadC`). The map says that no byte there is a coin's tile. So the byte read is not a coin's tile:

```
ColMap(m) ∧ ReadC(m) ∧ m at one of the two reads with no NMI pending   ⇒   ¬ coin(A after the step)
```

## One frame, and the frames before the touch's frame

`frame_coin`: a frame from `FrameStart` whose instructions meet `CleanK` of the walk's guard, write no routine, mode or task by their addresses, and meet `BufAt` and `ReadC`, keeps the coin's map, and at each `UpdScrollVar` of the frame `ctl ≠ 6`.

`frames_coin`: with the coin's map at control, on each frame `n` before the touch's frame (`n + 1 < ix g`):

```
ColMap(all n)   ∧   ∀ k,  pc(trace(all n, k)) = UpdScrollVar  →  frame(trace(all n, k)) = frame(all n)  →  ctl(trace(all n, k)) ≠ 6
```

`PoleJoin.Run.ctl6` reads this on the route's frames. It gives the condition that `ctlU` gave to `PoleStrict.invJ_onFrames` (its first case, `ctl ≠ 6`), so the parser's invariant, `JY` and the column's step need no field on the control byte (`PoleParserRun.invJ_run`, `colMono_run`).

## The map at control (`PoleParserRun.coinMap₀`)

In every state with control of the rows of the change out of the side pipe, every byte of the block buffers is known and none is a coin's tile (`coinMapK`, the private `pole_coin_rows`). As for the pole's map (`PoleTileCtl.colMap₀`), the machine at control is in these rows.

## The fields

Removed: `ctlU`.

Added, each on every instruction of each frame `n` before the touch's frame (`n + 1 < ix g`):

```
coinBuf :  PoleKeepFar.BufV(Coin.Q, trace(all n, k))
           (a store through an index or a pointer leaves no coin's tile in the block buffers; asked only of a store that farBuf does not settle,
            and of an STA abs,X, STA abs,Y or STA (zp),Y only when A holds a coin's tile)
readC   :  (pc = read ∧ X = 0)  ∨  pc = top   →   coin(the byte read)  →  the read is in the RAM, in the block buffers
ctlKeep :  farStore([ctl]) = false  →  a store through an index or a pointer does not write ctl
```

`coinBuf` asks of coins what `bufAll` asks of the pole's tiles. `ctlKeep` is the kind of `keepB`. `readC` asks a read of the player (or above a bumped block) that finds a coin's tile to be in the block buffers; the reads of the other objects are not asked (an `LDA (zp),Y` keeps `X`: `PoleCoin.step_lda_izy_x`, so the state right after the read knows that it was the player's).

The new fields are not weaker than `ctlU`: `ctlU` asked something only where the lag was 157 px or more (no measured visit), and the new fields ask something on every frame. But each of them is a condition on one instruction, and none speaks of the parser's lag.

Signatures that changed, exactly:

* `PoleJoin.Run`: no field `ctlU`; new fields `coinBuf`, `readC`, `ctlKeep` (above).
* New: `PoleJoin.Run.ctl6 (R) (hk : FrameKeep.keepCheckOf sy m0 = true) (hcC : PoleCoin.coinCheck sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (R.seq 0)) (hw0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.seq 0)) (hm0 : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))`.
* `PoleParserRun.invJ_run`, `inv_run`, `colMono_run`, `colEdge_run`, `tilesCol_run` take `(hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))` after `hJ`.
* `PoleParserRun.tilesCol_route` takes `(hmK : coinMapK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcC : PoleCoin.coinCheck sy m0 = true)` after `hmL`.
* New in `PoleParserRun`: `coinMapK`, `EndRunQ.coinMap`, `coinMap₀`.
* Two new symbols: `CheckTopOfBlock` and `CoinTile2` (the second coin's tile, `byte:CheckForCoinMTiles+5`), in `tools/smb-symbols.txt` and `Smbrta/Syms.lean`.
* `route_1_1` still concludes `1748 + j ≤ L`. Two new checks on the ROM: `pole_coin_walk` and `pole_coin_rows` (`native_decide`, in the new private file `Proof/PoleCoin.lean`).

## Measured

`pole-keep parser FM2 96`, on every instruction of the frames that start in control (the TAS, own random inputs from frames 900 to 1089 with and without Start, own random inputs from the first control; 719, 14,318 and 25,980 frames):

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| `ctl` at `UpdScrollVar` above ground | always 0 | always 0 | always 0 |
| stores through an index or a pointer to `ctl` (any area) | 0 | 0 | 0 |
| the player's reads of the collision routine | 4,943 | 69,356 | 130,621 |
| reads above a bumped block | 2 | 4 | 11 |
| of these reads, out of the block buffers (any area) | 0 | 0 | 0 |
| a coin's tile read above ground | 0 | 0 | 0 |
| frame starts above ground with a coin's tile in the block buffers | 0 | 0 | 0 |
| stores through an index or a pointer that leave a coin's tile in the block buffers above ground | 0 | 0 | 0 |
| instructions where `readC` is false (any area) | 0 | 0 | 0 |
| instructions where `ctlKeep` is false (any area) | 0 | 0 | 0 |

The exit code of `pole-keep parser` now asks these facts above ground (exit 0). The TAS takes coins only in the room below ground.

## What is not proved

* `coinBuf`: that no store through an index or a pointer leaves a coin's tile in the block buffers above ground. The area parser draws the columns from the level's data; above ground in 1-1 they hold no coin. A proof needs the parser's walk to follow the metatiles it stores.
* `readC`: that a read that finds a coin's tile is in the block buffers. The collision routine's checks of the height keep every one of his reads in the 13 rows (measured: no read out of the block buffers), but the walk does not know his height there.
* `ctlKeep`: no store through an index or a pointer writes the control byte (0 measured). Round 36: asked only at the places of `PoleNear.ResidC`; the walk of `PoleNear` proves it elsewhere ([the stores that may reach the control byte or the block buffer's column](f-6-17-19-PoleNear.md)). Round 37: at the head's collision only on a frame that does not start with the block objects' offset 0 or 1 ([the head's collision with the block objects' offset known](f-6-17-20-PoleOffset.md)).
* `tilesCol` (`TileSlotC`), `bufAll`, `keepB`: not changed by this step.

**Files.** `Theorems/PoleCoin.lean` (new); `Theorems/PoleJoin.lean` (the fields, `Run.ctl6`); `Theorems/PoleParserRun.lean` (`coinMapK`, `EndRunQ.coinMap`, `coinMap₀`, the new hypotheses); `Smbrta/Syms.lean`, `tools/smb-symbols.txt` (two symbols); `Main.lean` (`genPoleCoin`, the Route block, `pole-keep coin`, the round 35 counters of `pole-keep parser`).
