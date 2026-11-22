[← Back](README.md) | [English](f-6-17-13-PoleLate.md) | [Japanese](f-6-17-13-PoleLate-ja.md)

# The pole's tiles: the control byte 6 on a frame where the parser is not late

Round 31 left the field `ctlU` ([the strict rule of each frame](f-6-17-12-PoleStrict.md)). It asked, on each frame before the touch's frame that comes to the player's routine, at each `UpdScrollVar`: the screen buffers' control byte is not 6. This round asks it only where the area parser is late there. On the other frames a frame with the control byte 6 keeps `JV` too.

## The words

`N` is the area parser's tasks left, `S` the scroll counter of 32 px, `ctl` the screen buffers' control byte. For a frame from `m`, `k₂` is its `UpdScrollVar` after the scroll handler and `e` its end. At `k₂` the counter already has the scroll's amount.

```
JV(v)    :=  N ≤ 7  ∧  S + 3·N < 32
late(k)  :=  S(k) + 3·N(k) ≥ 32
```

## Where the code sets the control byte

From the code (the community disassembly's names):

* the screen update at the start of each frame sets it to 0;
* in the game's core, before `UpdScrollVar`, only `RemoveCoin_Axe` sets it, to 6. It runs when he takes a coin with his head, a foot or a side (`HandleCoinMetatile`), when he touches the axe (`HandleAxeMetatile`), and when a block he bumps has a coin on top (`CheckTopOfBlock`);
* after `UpdScrollVar` the parser's tasks set it to 6, for the next frame's screen update.

So `ctl(k₂) = 6` only on a frame where he takes a coin. Then `UpdScrollVar` runs no task: `N` and `S` stay as they are at `k₂`.

## The step (`Theorems/PoleLate.lean`, `Theorems/PoleStrict.lean`)

`PoleParser.frame_six` gives weak forms of the frame's end for every value of `ctl`: with `N ≥ 1`, `N(e) = N` or `N(e) = N − 1`, and `S(e) = S(k₂)` (`colEnd_n` for the column's step); with `N = 0`, the bytes kept, or a new column, which needs `S(k₂) ≥ 32`.

`jv_weak`: from `N ≤ 7`, `S(k₂) + 3·N < 32`, `N(e) ≤ N` and `S(e) = S(k₂)`,

```
N(e) ≤ 7   ∧   S(e) + 3·N(e) < 32
```

With `N = 0` the new column cannot start, since `S(k₂) < 32`. So `step_strict` now takes, at each `UpdScrollVar` `k`:

```
ctl(k) ≠ 6   ∨   S(k) + 3·N(k) < 32
```

With `ctl(k₂) ≠ 6` the proof is that of round 31 (the strict forms). Else `S(k₂) + 3·N < 32`, and `jv_weak` gives `JV(e)`. `invJ_onFrames` takes the same condition on each frame that comes to the player's routine.

## The field

Before (round 31), on each frame `n` before the touch's frame that comes to the player's routine:

```
ctlU :  at each UpdScrollVar k of it,   ctl(trace(all n, k)) ≠ 6
```

Now:

```
ctlU :  at each UpdScrollVar k of it,   ctl(trace(all n, k)) ≠ 6   ∨   S(trace(all n, k)) + 3·N(trace(all n, k)) < 32
```

`S` is `PoleJoin.parSOf` and `N` is the new `PoleJoin.parNOf` (the operand of the load of the task count in `UpdScrollVar`). The new field is weaker than the old one: it asks nothing where the parser is not late. It is still a condition on one state. No signature of a theorem changed except the type of `hk6` in `PoleStrict.step_strict` and `PoleStrict.invJ_onFrames`. `route_1_1` still concludes `1748 + j ≤ L`.

## Measured

`pole-keep parser FM2 96` (the runs as in round 30: the TAS, own random inputs from the TAS's frames 900 to 1089, own random inputs from the first control; 1 min 31 s, 73 MB), at each `UpdScrollVar` of a frame that starts in control:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| above ground | 608 | 10,086 | 18,682 |
| of them late (where `ctlU` asks `ctl ≠ 6`) | 40 | 242 | 205 |
| of them where the new `ctlU` is false | 0 | 0 | 0 |
| of the late ones, with `N = 0` (a new column starts) | 40 | 242 | 205 |
| any area, with `ctl = 6` | 13 | 0 | 0 |
| of them late | 0 | 0 | 0 |
| instructions at `RemoveCoin_Axe` above ground | 0 | 0 | 0 |
| instructions at `RemoveCoin_Axe`, any area | 13 | 0 | 0 |
| frame starts above ground with a coin's tile in the block buffers | 0 | 0 | 0 |
| stores of a coin's tile into the block buffers above ground | 0 | 0 | 0 |

So above ground the field now asks the control byte on 40 of 608 visits of the TAS, and every late visit was a frame where the parser starts a new column. The 13 visits of the TAS with `ctl = 6` are in the room below ground, where he takes coins (13 runs of `RemoveCoin_Axe`); none of them is late. (`RemoveCoin_Axe` is found from the code: the target of the jump at the end of `HandleAxeMetatile`; the coin's tile is the symbol `CoinTile`.)

With these numbers a way to remove `ctlU` is: the map "no coin's tile in the block buffers" at control (from the rows of the change, as `PoleTileCtl.colMap₀`), carried from frame to frame as `PoleTileWalk.frames_colMap` carries the pole's map, with a store condition at the places of `bufAll`; then a walk of the frame that follows `ctl` with the coin's branch cut.

## What is not proved

* `ctlU`: that he takes no coin above ground on a frame where the parser is late. A proof needs the block buffers' contents at his reads on every frame (no coin there). That is the same kind of fact as (slot) of `TileSlot`.
* A walk of the frame that follows `ctl` from the frame's start to `UpdScrollVar` would give only "`ctl = 0` unless the frame erases a coin". It needs `ctl` among the bytes that a store through an index or a pointer may not write (stores through a pointer run before `UpdScrollVar`, for example the block objects' update), so `guardE` would change, and with it the union guard of parts a and b. Not done.
* `TileSlot` (slot, near, read on the page two before the pole's), `bufAll` (7 places), `keepB` (66 places): not changed.

**Files.** `Theorems/PoleLate.lean` (new: `colEnd_n`, `jv_weak`); `Theorems/PoleStrict.lean` (imports `PoleLate`; `step_strict` and `invJ_onFrames`: `hk6`); `Theorems/PoleJoin.lean` (`parNOf`, `ctlU`); `Main.lean` (the round 32 line of `pole-keep parser`).
