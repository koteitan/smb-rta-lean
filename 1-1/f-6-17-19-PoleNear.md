[← Back](README.md) | [English](f-6-17-19-PoleNear.md) | [Japanese](f-6-17-19-PoleNear-ja.md)

# The stores that may reach the control byte or the block buffer's column

Round 35 added two fields on every instruction of the frames from control ([no coin in the block buffers](f-6-17-17-PoleCoin.md), [the parser's store at the block buffer's column](f-6-17-18-PoleBcol.md)):

* `ctlKeep`: a store through an index or a pointer does not write the screen buffers' control byte `ctl` (on the frames before the touch's frame);
* `bKeep`: a store through an index or a pointer does not write the block buffer's column `B` (on the frames up to the touch's frame).

This round proves both at almost every instruction, by one walk of each whole frame that knows where each store through an index or a pointer may go. The two fields stay asked only at a few places.

## The words

* `NoW(s, m)`: the instruction of `m` is not a store through an index or a pointer whose target is the RAM byte `s` (`PoleBcol.NoW`). For an instruction that is not such a store it holds at once.
* `CtlStore(m)`: the instruction of `m` writes the routine, the mode or the task byte by its address (`FrameKeep.CtlStore`). No frame before the touch's frame has one (`keep.noStore`).
* `store`: the area parser's store of a column (an `STA (zp),Y`, the first one from `AreaParserCore` on).
* `ResidC(m)` (`PoleNear.ResidC`), the places where `ctlKeep` stays:
  * a store through a pointer in the code of the head's collision with a block (from `PlayerHeadCollision` to `BlockObjectsCore`);
  * the castle's loop of rows (from `CRendLoop` to `ChkCFloor`);
  * the store of `RenderUnderPart` (its first `STA abs,X`).
* `ResidB(m)` (`PoleNear.ResidB`), the places where `bKeep` stays: every store through a pointer (`STA (zp),Y`) but `store`.

## The walk (`Theorems/PoleNear.lean`)

The walk is part e's walk of `SideRange` (`SideRange.walkR`). Its table's states carry bounds on `X` and `Y`, and a walk from a table's state starts from its values of `X` and `Y` inside the bounds. It also splits `X` or `Y` before some instructions. Here it starts at the frame's start, not at the scroll handler, so it covers the whole frame:

* the guard is `FrameKeep.guardE`, whose `CleanK` is the field `keep.cleanE`;
* a path stops at an instruction that writes the routine, the mode or the task by its address, so on the touch's frame the walk covers the instructions up to the first such store;
* at each store through an index or a pointer (the opcodes of `PushTimer.wOps`) but `store`, for each of the two bytes: the store is one that `PoleKeepFar.farStore` settles (no index reaches the byte from the base), or every target that the state allows misses the byte (`SideRange.missK`), or the store is one of `ResidC` (for `ctl`) or `ResidB` (for `B`) (`PoleNear.okN`);
* at `store` it asks nothing.

The table's key holds `X`, `Y` and the zero page byte 0 in the code of `SideRange.residB` and in the sprites' shuffle (`SpriteShuffler`), so that the states of a loop with a counter are not joined. The key is no part of the proof: a state is covered by a table's state only when its known bits and its bounds say so.

At `store` the walk of `PoleBcol` knows `B`, so it knows the target. Its new test `missS`: at `store` the target is known and it is neither `B` nor `ctl`.

On the ROM the table has 66,996 states. The search takes 19 s, and the check `PoleNear.nCheck` 23 s natively (`pole-keep near-check`, 0.5 GB). With the new test the check of `PoleBcol` takes 131 s (it was 119 s).

## What it proves

`near_frame`: a frame `m` in control, whose instructions meet `CleanK` of `guardE`. For each `k`:

```
(∀ j < k, ¬CtlStore(trace(m, j)))  ∧  frame(trace(m, k)) = frame(m)  ∧  pc(trace(m, k)) ≠ store  →
    (¬ResidC(trace(m, k)) → NoW(ctl, trace(m, k)))  ∧  (¬ResidB(trace(m, k)) → NoW(B, trace(m, k)))
```

`near_frames`: the same on every frame `n < ix g` (each starts in control: `FrameKeep.Frames.all_start`).

`PoleBcol.frames_bcol` (changed): it asks `NoW(B)` only on the frame's instructions other than `store` (round 35 asked `BcR` on every instruction), and it gives at `store`, on every frame `n < ix g`:

```
StoreRing(c(n) mod 32, trace(all n, k))  ∧  NoW(B, trace(all n, k))  ∧  NoW(ctl, trace(all n, k))
```

The walk of `PoleBcol` needs `NoW(B)` at each of its steps. At `store` it takes it from its own state at that step (`live_stepB`), so there is no cycle.

`PoleJoin.Run.bNoW`: on every frame `n < ix g`, at every instruction of the frame but `store`, `NoW(B)`: from `near_frames` up to the first `CtlStore` and away from `ResidB`, from `bKeep` at the rest.

`PoleJoin.Run.ctlR`: on every frame `n` with `n + 1 < ix g`, at every instruction of the frame, `CtlR` (round 35's form): at `store` from `frames_bcol`, at `ResidC` from `ctlKeep`, elsewhere from `near_frames` (no `CtlStore` before the touch's frame). `Run.ctl6` uses it.

## The fields

Narrowed (both ask less than before):

```
ctlKeep :  ∀ n, n + 1 < ix g → ∀ k,  ResidC(trace(all n, k)) → CtlR(trace(all n, k))
bKeep   :  ∀ n, n < ix g → ∀ k,  (ResidB(trace(all n, k)) ∨ ∃ j < k, CtlStore(trace(all n, j))) → BcR(trace(all n, k))
```

`CtlR` and `BcR` are round 35's: a store through an index or a pointer that `farStore` does not settle does not write `ctl` (`B`). Before the touch's frame no `CtlStore` happens, so there `bKeep` asks only at `ResidB`. On the touch's frame it asks also after the first store of the routine, the mode or the task (the walk stops there).

No field is added.

Signatures that changed, exactly:

* `PoleJoin.Run.ctlKeep : ∀ n, n + 1 < ixOf … g → ∀ k, PoleNear.ResidC sy m0 (trace (S.seq (a + n)) (S.inp (a + n)) k) → PoleCoin.CtlR (PoleCoin.coinOf sy m0) (trace (S.seq (a + n)) (S.inp (a + n)) k)`.
* `PoleJoin.Run.bKeep : ∀ n, n < ixOf … g → ∀ k, (PoleNear.ResidB sy m0 (trace … k) ∨ ∃ j, j < k ∧ FrameKeep.CtlStore sy (trace … j) = true) → PoleBcol.BcR (PoleBcol.bcOf sy m0) (trace … k)`.
* `PoleJoin.Run.ctl6` takes `(hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0))` after `hm0`.
* `PoleParserRun.invJ_run`, `inv_run`, `colMono_run`, `colEdge_run` take `(hcN) (hcB) (hIB)` (the same types) after `hmK`. `tilesCol_run` takes `(hcN : PoleNear.nCheck sy m0 = true)` after `hmK`. `tilesCol_route` takes `(hcN : PoleNear.nCheck sy m0 = true)` after `hcB`.
* `PoleBcol.frames_bcol`: `hct` is `∀ n, n < Fr.ix g → ∀ k, frame(trace k) = frame(all n) → pc(trace k) ≠ store → NoW B (trace k)`, and the conclusion at `store` has `∧ NoW B ∧ NoW ctl`. `frame_bcol`, `frame_of_walkB`, `live_stepB` take `CleanK` of the guard without its protected bytes, `NoW B → CleanK`, and `NoW B` away from `store`, on the frame's instructions. `cleanK_B` takes `NoW` in place of `BcR`. `Bc` has the new field `ctlI`.
* `PoleCoin.frames_coin`: `hct` is asked only on the frame's instructions; `frame_coin` and `frame_of_walkC` ask `CleanK` only on them.
* Two new symbols: `SpriteShuffler`, `RenderUnderPart`.
* `route_1_1` still concludes `1748 + j ≤ L`. One new check on the ROM: `pole_near_walk` (`native_decide`, in the new private file `Proof/PoleNear.lean`).

## What the walk does not know

At the places of `ResidC` and `ResidB` the search failed:

* the head's collision's stores through a pointer: the pointer comes from his position;
* the castle's loop of rows and `RenderUnderPart`: they draw rows from a row read from the area's data, and the loop's end is a test the walk does not use to bound `X` (it reached `X` with `MetatileBuffer + X = ctl`);
* for `B`, every store through a pointer into the block buffers but `store`: the last byte of the block buffers is right before `B`, and the walk does not know that the row is in the buffers there.

## Measured

`pole-keep parser FM2 96` (the TAS, random runs from 900 to 1089, random runs from the first control); every count below was 0 on all three:

* instructions where round 35's `ctlKeep` or `bKeep` (on every instruction) is false, in any area;
* instructions at the places of `ResidC` or `ResidB` where the narrowed field is false;
* parser's stores that write `ctl` or `B`.

The frames: 719 on the TAS, 14,318 and 25,980 on the random runs (the frames that start in control). The instructions at the places where the fields stay:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| instructions at the places of `ResidC` (any area) | 354 | 3,742 | 181 |
| instructions at the places of `ResidB` (any area) | 17 | 16 | 22 |

## `coinBuf` and `readC`: tried, not proved

* `coinBuf`. The same walk with a third test (`PoleNear.missB`: the store is one that `farBuf` settles, or an `STA` with no interrupt pending of a byte that is not a coin's tile, or every target misses the block buffers) gives `BufAt` of the coin's places at a store (`bufAt_of_missB`, proved). But the search fails at more than 30 stores (993 failures at 24 places, then 662 more at 9 places of the same routines). They are stores through an absolute address and an index into the object arrays in the 256 bytes before the block buffers, where the walk knows neither the index after a join nor the byte stored, and the stores through a pointer whose byte comes from the RAM. One of them is the store of an object's box (`BoundingBoxCore`, at the object's offset times 4): the walk's bounds allow the offsets 9 to 24 there, so the store may reach the buffers as far as it knows; by the code the largest offset is 17 (a misc object, offset at most 8, plus 9), so the box's last byte is 13 bytes before the buffers. No measured store leaves a coin's tile in the buffers. `coinBuf` stays.
* `readC`. With a test at the two reads (every address that the state allows is in the block buffers), the search fails at the player's read of the collision routine (105 failures, `X` known 0): there the walk knows the pointer's high byte, but neither its low byte nor `Y`, so as far as it knows the read may go past the buffers' end. The code's checks of the height before the read are branches that the walk does not use. `readC` stays.

## What is not proved

* `ctlKeep` at the places of `ResidC`, `bKeep` at the places of `ResidB` and on the touch's frame after its first store of the routine, the mode or the task (0 measured where they are false).
* `coinBuf`, `readC`, `bufAll`, `keepB`, `tilesCol`: unchanged.

**Files.** `Theorems/PoleNear.lean` (new); `Theorems/PoleBcol.lean` (`NoW`, `Bc.ctlI`, `missS`, `store_target`, `store_miss`, `cov_preB0`, the walk and its theorems); `Theorems/PoleCoin.lean` (`CleanK` and `CtlR` on the frame's instructions); `Theorems/PoleJoin.lean` (`ctlKeep`, `bKeep`, `Run.bNoW`, `Run.ctlR`, `Run.ctl6`); `Theorems/PoleParserRun.lean` (signatures); `Smbrta/Syms.lean`, `tools/smb-symbols.txt` (`SpriteShuffler`, `RenderUnderPart`); `Main.lean` (`genPoleNear`, the Route block, `pole-keep near-check`, `near-search`, `near`, the counters of `pole-keep parser`).
