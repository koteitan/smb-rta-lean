[← Back](README.md) | [English](c-7-8-4-OffLand.md) | [Japanese](c-7-8-4-OffLand-ja.md)

# Past the block's right end: a landing at any height

In round 34 the field `offFloor` of [Joining the bonus room](c-5-RoomJoin.md) said: from `t0`, the first frame past the block's right end, to the frame before the entry, a frame that ends standing ends on the floor's height or one row above it. With it the walk of the frames past the block's right end (`offNext`, [Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md)) left the stands at other heights out. The field is false on real runs. Since round 35 it is gone, and `offNext` is `anyNext`: a landing may be at any height.

## False on real runs

`room-off-back FM2 400` (measured only). From the room's first control: random input with A in a rhythm (as the kinds 2 and 6 of `room-off-ways`) until he stands on the block's top; then Right alone (walking) up to `t0`; then Left with A to turn back (for a quarter of the seeds a new press of A every 6 frames); then Right to the side pipe, and later Left and Right in turns, so that he walks off the pipe again.

| | |
|---|---|
| seeds | 400 |
| of them standing on the block's top, then past its right end | 225 |
| of them entering the side pipe | 225 |
| of them with a stand from `t0` on that is neither on the floor nor one row above it (against `offFloor`) | 29 |
| such stands | 1,348, all at 144 px |
| entries whose frame before is not near the floor (against `offNear`) | 0 of 225 |
| frames from `t0` on in the jump state with a slow fall force | 6,532 |
| of them moving more than 1.5 px (against `offSlow`) | 0 |

144 px is two rows above the floor: he stands on the side pipe's top. For example, one run has `t0 = C + 158`, stands at 144 px from `t0 + 64` on, and enters at `t0 + 227`. The measurement of round 34 (`room-off-ways`, 216 stands from `t0` on) had none at 144 px: its inputs did not climb onto the pipe.

## What is proved

```
RoomRun.next_E     :  C ≤ n  ∧  n + 1 < E  →  vE(n + 1) ∈ anyNext(vE(n))
RoomRun.land_bound :  a landing above the floor of a jump from the block's top, n frames after t0 − 1  →  t0 + aboveF ≤ E + 1
landS_spec         :  1 ≤ d  ∧  s ∈ landsAt(d)  ∧  d + i ≤ aboveF − 2  →  no state i frames of anyNext after s is near the floor
```

* **Each frame before the entry goes to a state of `anyNext`** (`next_E`), with no field. A stand is on a whole row (`stand_ok`), so a takeoff is one of its row's. In the air the frame is `vstepR` or its landing, at any height.
* **The descent** (`descend_k`). From a state of a jump from the block's top at `t0 − 1`, `k` frames later the jump has come to the floor, or he has landed above the floor at any height (in round 34: one row above it), or he is still on the jump.
* **A landing above the floor** (`land_bound`). It comes `n` frames after `t0 − 1` with `n ≥ max(above, 1)`: `above` counts the frames since he was last above the block's top (`OffDrop.above_after`), and the landing is after `t0 − 1`. From the landing no state of `anyNext` is near the floor for `aboveF − 2 − max(above, 1)` frames (the check `landS`). So the frame before the entry, which is near the floor (`offNear`), is later, and `t0 + aboveF ≤ E + 1`.
* **The search** (`OffDrop.visS`, `visS_spec`). It keeps a set of the states seen. A state seen before is not followed again: it was seen at a smaller depth, so it was followed for more frames. The landings of the states with `max(above, 1) = d` join the search at the layer `d` (`landsAt d`), so each is followed for `aboveF − 2 − d` frames. The check `standB` (from the stands of `standFam`, [A stand on the block's top](c-7-8-3-OffStand.md)) uses the same search with no later starts.

## The fields

Removed:

* `offFloor` (a field of `RoomRun`).

Added: no field. ROM checks of `RoomJoin.Checks`: `pipeAc` and `pipeBc` are gone, with the numbers `pipeA = 8`, `pipeB = 4` and the fact `pipe_sum`. The new check `landC` (`landS`) takes their place. `standB` now searches `anyNext`.

## Measured

`room-off-stand`: the landings of the jumps from the block's top (7,069 states, 6,049 of them falling above the floor's height), by height.

| landing at | states | landings | least `max(above, 1)` | frames checked | first frame near the floor |
|---|---|---|---|---|---|
| 32 px | 38 | 24 | 1 | 10 | 11 |
| 48, 64, 80, 96, 112, 128 px | 401 to 878 each | 182 to 280 each | 1 | 10 | none up to 13 |
| 144 px | 768 | 174 | 4 | 7 | 12 |
| 160 px | 764 | 172 | 8 | 3 | 8 |

| check | result | time (native) |
|---|---|---|
| `landS` | true | 8.3 s |
| `standB` (2,048 stands, 12 frames, a landing at any height) | true | 7.9 s (39.7 s without the set of the states seen) |

In round 34 `pipeAc`, `pipeBc` and `standB` took 0.2 s, 1.0 s and 14.5 s.

A stand at 32 px can jump past the top of the screen. There the height wraps to the floor's values, because the vertical state does not hold the vertical page. Such a state counts as near the floor. This only makes the check stricter. It is why the landings at 32 px come near the floor after 11 frames; they must be checked for 10.

## What remains (not proved)

* `offTop`, `offSlow` ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md) says how each could be proved). `offNear` is proved in round 36 ([The entering frame](c-7-8-5-EntryVert.md)).

**Files.** `Theorems/OffDrop.lean` (`visS`, `visS_spec`). `Theorems/RoomJoin.lean` (`offNext`, `offStep`, `offRunV`, `offB`, `landsAt`, `landS`, `offRunV_eq`, `offB_spec`, `landS_spec`, `mem_landsAt`, `RoomRun.next_E`, `RoomRun.real_reach`, `RoomRun.descend_k`, `RoomRun.land_bound`; gone: `offFloor`, `offLand`, `pipeLands`, `pipeAOk`, `pipe_bound`, `pipeAc`, `pipeBc`, `pipeA`, `pipeB`, `pipe_sum`). `Main.lean`: `room-off-back` (measured only), `room-off-stand`; the private `Proof/RoomJoin.lean` gets `landC`.

**Reproduce.**
```
.lake/build/bin/smbrta room-off-back FM2 400     # runs against the round-34 field offFloor (about 1 min)
.lake/build/bin/smbrta room-off-stand            # the checks, with the table by height (about 2 min)
```
