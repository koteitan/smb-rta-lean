[← Back](README.md) | [English](c-7-8-2-OffDrop.md) | [Japanese](c-7-8-2-OffDrop-ja.md)

# Off the block's top: the frames to the floor

The field `Off` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-8) said how a run gets from the block's top to the floor after `t0`, the first frame past the block's right end: a jump from the block's top whose arc reaches the floor by the entering frame `E`, or stepping off. Its arcs, its frame `F` and the frames after `t0` were not read from the machines: `read_vs` reads the vertical state only up to `t0`. From round 34 `Off` is gone. `RoomRun.off_gap_of` proves what the route took from it, on the real frames after `t0`. In its place there are five fields, each about one frame or one state.

## What is proved

`vE(n)` is the vertical state at the end of the room's frame `n`, read from the machine (`RoomRun.vE`): the height `y`, the state `st` (0 standing, 1 in a jump, 2 falling), the vertical speed and its fraction, the two forces `vf`, `vfd`, the jump's origin. `y_top` is the standing height on the block's top, 48 px above the floor's `y_floor`.

```
RoomRun.off_gap_of :  t0 < E  ∧  t0 + aboveF ≤ E + 1          (aboveF = 13: the entry comes at least 12 frames after t0)
RoomCore.off_gap   :  the same, a fact of RoomCore in place of the field Off of way
entry_ge           :  C + goalF + aboveF ≤ E                  (from past_late: C + goalF < t0; unchanged: E ≥ C + 111)
```

The walks of the room's frames hold up to the frame before the entry, not only up to `t0`. So the vertical bytes after `t0` are followed on the real frames:

* a frame in the air is `vstepR` of the state before, or its landing (`RoomRun.air_E`, from `InRoom.air`);
* a frame that starts standing with no jump ends as `StandNext` allows (`stand_E`, from `InRoom.stand`);
* a frame with a jump ends on the takeoff of its height (`jump_E`, from `InRoom.jump`).

The proof has two cases, by the last frame `T` before `t0` that ends standing (the field `offTop` puts it on the block's top).

* `T + 1 < t0`: frame `T + 1` takes off. With no jump it would keep the height `y_top`, but it ends above the block's top. The takeoff is the first state of a jump from the block's top (`OffDrop.offAt`, the check `offT`). Up to `t0 − 1` the real frames are the jump's states: they do not land, since they end in the air, and `vstepR` is `vstep` on every state of these jumps (`VertAir.bridgeAll` from the block's top, the check `bridgeB`). From `t0 − 1`, where he is above the block's top, `descend_k` follows the jump to one of three ends:
  * the jump reaches the floor's height on a frame `F ≤ E`;
  * he lands one row above the floor, on the side pipe;
  * he is still on the jump at `E − 1`, and one more frame reaches the floor (the field `offNear`).

  Then:
  * a fast jump reaches the floor at least `aboveF` frames after `t0 − 1` (the check `drop`, `dropOk`: it counts the frames since he was above the block's top, `OffDrop.above_after`);
  * a slow jump reaches it at least `aboveS = 12` frames after `t0 − 1`;
  * a landing one row above the floor comes at least `pipeA = 8` frames after `t0 − 1` (`pipeAOk`). From there no state is near the floor for `pipeB = 4` frames (`offB` on `pipeLands`), and `aboveF ≤ pipeA + pipeB + 1`;
  * if a slow jump entered exactly `aboveS` frames after `t0 − 1`, every frame from `t0 − 1` to `E − 1` would be a state of that slow jump: in the jump state, with the fall force of a slow takeoff (`OffDrop.slowArcs`, the check `slowB`). The field `offSlow` then moves him at most `A − 1` sixteenths of a pixel (1.5 px) a frame, and `P(E) ≤ P(t0 − 1) + 16·(A − 1)·aboveS < goal + 16·(A − 1)·aboveS ≤ mouth ≤ P(E)` (`slow_mouth`, `mouth`, `first`): impossible.
* `T + 1 = t0`: frame `t0 − 1` ends standing on the block's top. The field `offStand` makes its state one of `standFam`, and the check `standB` goes `aboveF − 1` frames of `offNext` from those states with no state near the floor. Frame `t0` may walk off, jump, or stay standing (only on the floor or one row above it, by `offFloor`). So the frame before the entry is more than 12 frames after `t0 − 1` (`offB_path`, `offB_gap`).

`offNext` is `anyNext` past the block's right end: in the air `vstepR` with A or not, and its landing only on the floor or one row above it; standing, the states of `noJumpNext` that are in the air or stand at those heights, and the takeoffs of the row. `near(s)` (`OffDrop.nearB`) is: standing at `y_floor`, or in the air with one frame of `vstepR`, with A or not, falling to `y_floor` or below.

## The fields

Removed:

* `Off` (inside `way`): the jump off the block or the step off it, with `F ≤ E` and `slowJ`. `Way.onto` now holds only `Approach`. `RoomCore.t0_le_E` and `t0_lt_E` (from `Off`) are gone; `past_late` takes `t0 < E` from `off_gap`.

Added (fields of `RoomRun`, each about one frame or one state):

```
offTop   :  ∃ T,  C ≤ T < t0  ∧  st(vE T) = 0  ∧  y(vE T) = y_top  ∧  ∀ j ∈ (T, t0),  st(vE j) ≠ 0  ∧  y(vE j) < y_top
offFloor :  ∀ n ∈ [t0, E),  st(vE n) = 0  →  y(vE n) = y_floor  ∨  y(vE n) + 16 = y_floor
offNear  :  near(vE(E − 1))
offSlow  :  ∀ n ∈ [t0 − 1, E),  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  P(n + 1) ≤ P(n) + 16·(A − 1)
offStand :  st(vE(t0 − 1)) = 0  →  vf = vfd  ∧  vfd ∈ forces  ∧  origin ∈ {y_top, y_floor, y_floor − 16, y_floor − 32}
```

That such a stand has no vertical speed is proved (`RoomRun.stand_ok`): every stand of the room before the entry has no vertical speed and is on a whole row. At first control he falls (the check `startAir`), a landing has no speed, a frame that starts standing with no jump keeps the height and the speed or lands (`StandNext`), and no takeoff from a whole row stands (`jumpAirCheck`, the check `jumpAir`).

`F_slow` (`OffDrop.slowF`) is the fall forces of the takeoffs from the block's top below the air threshold; `forces` those of every takeoff. `P(n)` is the position at the end of frame `n`, read from the machine.

These five are not weaker than `Off` in every way: `Off` asked only for a timing, and its frames after `t0` were free data. They ask facts of the real frames, and the timing is proved from them.

New ROM checks (`native_decide` in the private `Proof/RoomJoin.lean`, `room_checks`): `bridgeB`, `offT`, `slowB`, `pipeAc`, `pipeBc`, `standB`, `startAir`, `jumpAir`. Together they add about 30 s to the private build (`Proof.RoomJoin` 145 s on a quiet machine, 193 s with other runs, was 116 s); `standB` takes 15 to 28 s natively. New numbers: `pipeA = 8`, `pipeB = 4`, with the facts `off_two : 2 ≤ aboveF` and `pipe_sum : aboveF ≤ pipeA + pipeB + 1`.

## Measured

`room-off-ways FM2 300` (measured only): the TAS and 1,800 own runs from the room's first control (six kinds of input that go right, with B, with jumps at random times or in a rhythm, and a few presses of Left), each up to the entry or 400 frames. It also runs the six checks.

| | |
|---|---|
| runs | 1,801 |
| past the block's right end before the entry | 333 |
| of them the last stand before `t0` on the block's top (`offTop`) | 333 |
| of them that stand at `t0 − 1` | 34 |
| of them a jump on `T + 1`, every frame up to `t0 − 1` above the block's top (`offTop`) | 299 |
| runs that enter | 65 |
| stands from `t0` to `E − 1` | 216 |
| of them neither on the floor nor one row above it (against `offFloor`) | 0 |
| of them one row above it (on the side pipe) | 2 |
| state at `E − 1` near the floor (`offNear`) | 65 of 65 |
| frames in the jump state with the fall force of a slow takeoff, in the whole room | 496,014 |
| of them moving more than 1.5 px (against `offSlow`) | 0 |
| stands at `T` with `vf ≠ vfd`, or (at `t0 − 1`) a vertical speed, a fall force not of a takeoff, or an origin not of those heights (against `offStand`) | 0 |
| stands of the whole room with a vertical speed or off a whole row | 0 of 133,484 |

The least `E − t0` was 12 (the TAS); after a stand at `t0 − 1` it was 19, after a slow jump 14. On the TAS the last stand before `t0` is at `C + 78` on the block's top, the jump is fast, and `t0 = C + 99`, `E = C + 111`.

The first version of `offFloor` asked the floor's height only. It was false on 2 measured frames, where he stood one row above the floor on the side pipe at `t0 + 13` and `t0 + 14` (`E = t0 + 27`). So it allows that height, and the proof handles a landing there.

## What remains (not proved)

* The five new fields. Ways to prove them later:
  * `offTop`: the block's right column. At `t0 − 1` his left foot is over it, so he is on or above its top.
  * `offFloor`: a walk of the frames past the block's end that knows the cells between the block and the side pipe, as `RoomWall.wall_frameX` does near the left wall.
  * `offNear`: the entering frame. Its side check enters only in the state 0, which a walk of frame `E` would show.
  * `offSlow`: the air speed cap after `t0`, by the horizontal model on the frames after `t0`.
  * `offStand`: the vertical bytes through the room. A walk that shows that `vstepR` keeps the fall force and the origin would give it, as `stand_ok` gives the vertical speed.
* `Approach`, `Over` and the choice of the case of `way` (items 1-1-c-7-7, 1-1-c-7-9, 1-1-c-7-14) stay as they were.

**Files.** `Theorems/OffDrop.lean` (`nearB`, `offAt`, `slowF`, `slowArcs`, the counter `above`, `allLayers`, paths). `Theorems/RoomJoin.lean` (`offNext`, `offB`, `standFam`, `pipeLands`, `pipeAOk`, `RoomRun.off_gap_of` and its lemmas, the five fields, `RoomCore.off_gap`). `Main.lean`: `room-off-ways`; the private `Proof/RoomJoin.lean` gets the eight checks, `pipeA`, `pipeB`, `off_two`, `pipe_sum`, `stop_cap`, `hit_three`.

**Reproduce.**
```
.lake/build/bin/smbrta room-off-ways FM2 300     # the fields of this page on real frames, and the six checks (about 15 min)
```
