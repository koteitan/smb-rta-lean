[← Back](README.md) | [English](f-6-17-20-PoleOffset.md) | [Japanese](f-6-17-20-PoleOffset-ja.md)

# The head's collision with the block objects' offset known

Round 36 ([the stores that may reach the control byte or the block buffer's column](f-6-17-19-PoleNear.md)) asked the field `ctlKeep` (a store through an index or a pointer does not write the screen buffers' control byte `ctl`, on the frames before the touch's frame) only at three kinds of place (`PoleNear.ResidC`):

* the two stores through a pointer in the code of the head's collision with a block;
* the castle's loop of rows;
* the store of `RenderUnderPart`.

This round proves the field at the first kind, on every frame that starts with the block objects' offset 0 or 1.

## Why the walk of round 36 failed at the head's collision

The head's collision stores through the zero page with the block objects' offset (`SprDataOffset_Ctrl`) as the index. The walk of round 36 does not know the offset. So, as far as it knows, such a store may write the pointer of the block buffer, and the walk loses the pointer's high byte. Then a store through that pointer may go anywhere, also to `ctl`.

## The words

* `InvS(m)` (`PoleOffset.InvS`): bits 1 to 7 of the block objects' offset are 0 in the state `m`. It is a condition on one state.
* `ResidC(m)` (`PoleOffset.ResidC`), the places where `ctlKeep` stays: the castle's loop of rows (from `CRendLoop` to `ChkCFloor`) and the store of `RenderUnderPart`. They are two of the three kinds of `PoleNear.ResidC`.
* `NoW(s, m)`, `CtlStore(m)`, `store` are those of round 36.

## The walk (`Theorems/PoleOffset.lean`)

It is the walk of round 36 with three changes:

* the guard `guardO` is `FrameKeep.guardE` with the offset protected. Its `CleanK` comes from the field `keep.cleanE` and the field `keepB` (`PoleTileKeep.KeepB`: no store through an index or a pointer writes the offset) (`cleanK_O`, `noW_of_keepB`);
* the frame's start state `startO` knows bits 1 to 7 of the offset to be 0. It covers a machine that meets `InvS` (`sim_startO`);
* after each step, `SideAcross.fixP` takes back each zero page byte that a store through a pointer cannot reach (part e's walk `SideAcross.walkP`).

At each store through an index or a pointer but `store`, the walk asks that the store misses `ctl` (`PoleNear.missT`), or that it is a place of `ResidC` (`okO`). A path stops at a `CtlStore`.

On the ROM the table has 67,672 states. The search takes 14 s and the check `PoleOffset.oCheck` 16 s natively (0.5 GB, `pole-keep offset-check`). From this round `PoleNear.nCheck` is round 36's check (`PoleNear.nCheckN`) and this one; both take 33 s.

## What it proves

`off_frame`: a frame `m` in control that starts with `InvS(m)`, whose instructions meet `CleanK` of `guardE` and `KeepB`. For each `k`:

```
(∀ j < k, ¬CtlStore(trace(m, j)))  ∧  frame(trace(m, k)) = frame(m)  ∧  pc(trace(m, k)) ≠ store  ∧  ¬ResidC(trace(m, k))
    →  NoW(ctl, trace(m, k))
```

`off_frames`: the same on every frame `n < ix g` that starts with `InvS`. `invS_frames`: with the facts at control (`PoleTileCtl.watch₀`, `PoleTileCtl.colMap₀`), every frame `n < ix g` starts with `InvS` (`PoleTileKeep.frames_keepY`).

`PoleJoin.Run.ctlR` (same signature): on every frame `n` with `n + 1 < ix g`, at every instruction of the frame, `CtlR`:

* at `store`, from `PoleBcol.frames_bcol`;
* at `ResidC`, from `ctlKeep`;
* on a frame that starts with `InvS`, elsewhere from `off_frames`;
* on a frame that does not start with `InvS`: at `PoleNear.ResidC` from `ctlKeep`, elsewhere from round 36's `PoleNear.near_frames`.

## The field

Narrowed (it asks less than before):

```
ctlKeep :  ∀ n, n + 1 < ix g → ∀ k,
    (ResidC(trace(all n, k))  ∨  (¬InvS(all n) ∧ PoleNear.ResidC(trace(all n, k))))  →  CtlR(trace(all n, k))
```

Round 36 asked `PoleNear.ResidC(trace(all n, k)) → CtlR(trace(all n, k))`. The new field asks the same at the castle's loop and at `RenderUnderPart`, and at the head's collision only on a frame that does not start with `InvS`. Every frame of the route starts with `InvS` (`invS_frames`), but the theorems that use `ctlKeep` (`Run.ctlR`, `Run.ctl6`, the theorems of `PoleParserRun`) take only `PoleNear.nCheck`, not the facts at control, so the field keeps that case. No field is added; no other field changes.

Signatures: none of a theorem changed. `PoleNear.nCheck` is now defined in `PoleOffset` as `PoleNear.nCheckN && PoleOffset.oCheck`; the old check is `PoleNear.nCheckN`, and `PoleNear.near_frame`, `near_frames` take it. The private proof `pole_near_walk : PoleNear.nCheck sy ctx = true` imports `Theorems.PoleOffset`. `route_1_1` still concludes `1748 + j ≤ L`.

## What the walk does not know at the places left

* the castle's loop starts at a row that the castle object's data gives. With a start row of 11 or more the loop would run over the whole page.
* `RenderUnderPart` draws from a row that its caller gives. The search reached `X` with `MetatileBuffer + X = ctl` from the staircase: it reads its row from a table at the index `StaircaseControl`, a byte that lives across frames and that the walk does not know.

## Measured

`pole-keep parser FM2 96` (the TAS, random runs from 900 to 1089, random runs from the first control; the frames that start in control):

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frames that start in control | 719 | 14,318 | 25,980 |
| of them without `InvS` | 0 | 0 | 0 |
| instructions where round 36's `ctlKeep` was asked (`PoleNear.ResidC`, any area) | 354 | 3,742 | 181 |
| instructions where the narrowed `ctlKeep` is asked | 352 | 3,738 | 170 |
| of them where it is false | 0 | 0 | 0 |

So on these runs the field is now asked only at the castle's loop and at `RenderUnderPart`; the instructions at the head's collision (2, 4 and 11) are proved.

## Tried, not kept: the player's height in the walk

A finer walk followed the player's height through his collision routine: at each load of his height in the routine it split the height into blocks of known bits between the heights the routine compares it with, and in the block buffer's routine it split `A` and `Y` into their values at the two additions, with keys for the height, the zero page byte 2 and the pointer's low byte inside the routine and the routines it calls. Measured with the search (no part of the proof):

* it proves `bKeep` at the store of the head's collision (the bumped block), with 143,692 states and 42 s, more than twice the table of this round;
* at the store above a bumped block (`CheckTopOfBlock`) it fails: there the walk needs the player's size to be 0 or 1 (the table of the head's upper extent is read at the size), and nothing proves that yet;
* at the store of `ErACM` it fails: the walk loses the height in the routines that the collision routine calls (a store through the zero page and an index that the walk does not know forgets the zero page), and the foot check splits it again without the check of the bottom of the screen;
* `readC` (the player's collision read) needs the same size, the crouching and the swimming flags read twice in one path to agree, and the index of an enemy's read not 0.

So `bKeep`, `readC` and `coinBuf` stay as they were. The table of the finer walk grew to 717,085 states when the keys held the flags.

## What is not proved

* `ctlKeep` at the castle's loop and at `RenderUnderPart`, and at the head's collision on a frame that does not start with `InvS` (none on the route).
* `bKeep`, `coinBuf`, `readC`, `bufAll`, `keepB`, `tilesCol`: unchanged.

**Files.** `Theorems/PoleOffset.lean` (new); `Theorems/PoleNear.lean` (the old check renamed `nCheckN`); `Theorems/PoleJoin.lean` (`ctlKeep`, `Run.ctlR`, `Run.bNoW`'s use of the check); `Main.lean` (`genPoleNear` imports `Theorems.PoleOffset`, `pole-keep offset-check`, `offset-search`, the counters of `pole-keep parser`).
