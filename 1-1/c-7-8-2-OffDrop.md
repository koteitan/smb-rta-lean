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
  * he lands one row above the floor, on the side pipe (since round 35: above the floor at any height, `land_bound`);
  * he is still on the jump at `E − 1`, and one more frame reaches the floor (the field `offNear`; since round 36 `RoomRun.offNear_of`, [The entering frame](c-7-8-5-EntryVert.md)).

  Then:
  * a fast jump reaches the floor at least `aboveF` frames after `t0 − 1` (the check `drop`, `dropOk`: it counts the frames since he was above the block's top, `OffDrop.above_after`);
  * a slow jump reaches it at least `aboveS = 12` frames after `t0 − 1`;
  * a landing one row above the floor comes at least `pipeA = 8` frames after `t0 − 1` (`pipeAOk`). From there no state is near the floor for `pipeB = 4` frames (`offB` on `pipeLands`), and `aboveF ≤ pipeA + pipeB + 1`. Since round 35 a landing at any height above the floor comes `n ≥ max(above, 1)` frames after `t0 − 1`, and from it no state is near the floor for `aboveF − 2 − max(above, 1)` frames (the check `landS`, [Past the block's right end: a landing at any height](c-7-8-4-OffLand.md));
  * if a slow jump entered exactly `aboveS` frames after `t0 − 1`, every frame from `t0 − 1` to `E − 1` would be a state of that slow jump: in the jump state, with the fall force of a slow takeoff (`OffDrop.slowArcs`, the check `slowB`). The field `offSlow` then moves him at most `A − 1` sixteenths of a pixel (1.5 px) a frame (since round 37 this is proved, `slow_run`, from the field `offCollide` after the end of the move: [The air speed cap after `t0`](c-7-8-6-AirMove.md)), and `P(E) ≤ P(t0 − 1) + 16·(A − 1)·aboveS < goal + 16·(A − 1)·aboveS ≤ mouth ≤ P(E)` (`slow_mouth`, `mouth`, `first`): impossible.
* `T + 1 = t0`: frame `t0 − 1` ends standing on the block's top. Until round 34 the field `offStand` made its state one of `standFam`. Since round 35 its state, with the jump force put to the fall force and the origin to the block's top, is one of `standFam`, and a stand or a fall does not read those two bytes (`SimV`, [A stand on the block's top: the bytes that a fall does not read](c-7-8-3-OffStand.md)). The check `standB` goes `aboveF − 1` frames of `offNext` from those states with no state near the floor. Frame `t0` may walk off, jump, or stay standing (until round 34 only on the floor or one row above it, by `offFloor`; since round 35 at any height). So the frame before the entry is more than 12 frames after `t0 − 1` (`offB_path_sim`, `offB_gap_sim`).

`offNext` was `anyNext` past the block's right end with the landings only on the floor or one row above it: in the air `vstepR` with A or not, and its landing at those heights; standing, the states of `noJumpNext` that are in the air or stand at those heights, and the takeoffs of the row. Since round 35 `offNext` is `anyNext`, with a landing at any height. `near(s)` (`OffDrop.nearB`) is: standing at `y_floor`, or in the air with one frame of `vstepR`, with A or not, falling to `y_floor` or below.

## The fields

Removed:

* `Off` (inside `way`): the jump off the block or the step off it, with `F ≤ E` and `slowJ`. `Way.onto` now holds only `Approach`. `RoomCore.t0_le_E` and `t0_lt_E` (from `Off`) are gone; `past_late` takes `t0 < E` from `off_gap`.

Added (fields of `RoomRun`, each about one frame or one state):

```
offTop   :  ∃ T,  C ≤ T < t0  ∧  st(vE T) = 0  ∧  y(vE T) = y_top  ∧  ∀ j ∈ (T, t0),  st(vE j) ≠ 0  ∧  y(vE j) < y_top
offFloor :  ∀ n ∈ [t0, E),  st(vE n) = 0  →  y(vE n) = y_floor  ∨  y(vE n) + 16 = y_floor          (false on real runs; gone in round 35)
offNear  :  near(vE(E − 1))                                                         (proved in round 36; gone)
offSlow  :  ∀ n ∈ [t0 − 1, E),  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  P(n + 1) ≤ P(n) + 16·(A − 1)          (gone in round 37: offCollide in its place)
offStand :  st(vE(t0 − 1)) = 0  →  vf = vfd  ∧  vfd ∈ forces  ∧  origin ∈ {y_top, y_floor, y_floor − 16, y_floor − 32}        (gone in round 35)
```

`offStand` is gone since round 35 (item 1-1-c-7-8-3, [A stand on the block's top: the bytes that a fall does not read](c-7-8-3-OffStand.md)). `offFloor` is false on real runs: from `t0` on he can stand on the side pipe's top, two rows above the floor, and then enter. It is gone since round 35 (item 1-1-c-7-8-4, [Past the block's right end: a landing at any height](c-7-8-4-OffLand.md)). `offNear` is proved in round 36 (item 1-1-c-7-8-5, [The entering frame](c-7-8-5-EntryVert.md)). `offSlow` is gone in round 37 (item 1-1-c-7-8-6, [The air speed cap after `t0`](c-7-8-6-AirMove.md)), with the field `offCollide` on the same frames in its place: the position after each frame's end of the move. So `offTop` and `offCollide` remain.

**Round 36: a narrowing that was not kept.** A form of the two fields with the premises `E + 1 < t0 + aboveF` (`offTop`) and `E = t0 − 1 + aboveS` (`offSlow`) was enough for `off_gap_of`, by contradiction. But with the facts that are proved, those two forms together say exactly `t0 + aboveF ≤ E + 1`, the conclusion of `off_gap_of`: they would assume the result, not a fact of single frames. So the fields keep their form of round 34. No measured run enters fewer than 12 frames after `t0` (`room-off-back FM2 400`, `room-off-ways FM2 300`; the least `E − t0` is 12, the movie's).

That such a stand has no vertical speed is proved (`RoomRun.stand_ok`): every stand of the room before the entry has no vertical speed and is on a whole row. At first control he falls (the check `startAir`), a landing has no speed, a frame that starts standing with no jump keeps the height and the speed or lands (`StandNext`), and no takeoff from a whole row stands (`jumpAirCheck`, the check `jumpAir`).

`F_slow` (`OffDrop.slowF`) is the fall forces of the takeoffs from the block's top below the air threshold; `forces` those of every takeoff. `P(n)` is the position at the end of frame `n`, read from the machine.

These five are not weaker than `Off` in every way: `Off` asked only for a timing, and its frames after `t0` were free data. They ask facts of the real frames, and the timing is proved from them.

New ROM checks (`native_decide` in the private `Proof/RoomJoin.lean`, `room_checks`): `bridgeB`, `offT`, `slowB`, `pipeAc`, `pipeBc`, `standB`, `startAir`, `jumpAir` (since round 35 `landC` in place of `pipeAc` and `pipeBc`). Together they add about 30 s to the private build (`Proof.RoomJoin` 145 s on a quiet machine, 193 s with other runs, was 116 s); `standB` takes 15 to 28 s natively. New numbers: `pipeA = 8`, `pipeB = 4`, with the facts `off_two : 2 ≤ aboveF` and `pipe_sum : aboveF ≤ pipeA + pipeB + 1` (since round 35 `pipeA`, `pipeB` and `pipe_sum` are gone; `off_two` stays; the checks `keepA` and `offVfd` are added: [A stand on the block's top](c-7-8-3-OffStand.md)).

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
| of them neither on the floor nor one row above it (against `offFloor`) | 0 (but 29 of 225 runs of `room-off-back` in round 35) |
| of them one row above it (on the side pipe) | 2 |
| state at `E − 1` near the floor (`offNear`) | 65 of 65 |
| frames in the jump state with the fall force of a slow takeoff, in the whole room | 496,014 |
| of them moving more than 1.5 px (against `offSlow`) | 0 |
| stands at `T` with `vf ≠ vfd`, or (at `t0 − 1`) a vertical speed, a fall force not of a takeoff, or an origin not of those heights (against `offStand`) | 0 |
| stands of the whole room with a vertical speed or off a whole row | 0 of 133,484 |

The least `E − t0` was 12 (the TAS); after a stand at `t0 − 1` it was 19, after a slow jump 14. On the TAS the last stand before `t0` is at `C + 78` on the block's top, the jump is fast, and `t0 = C + 99`, `E = C + 111`.

The first version of `offFloor` asked the floor's height only. It was false on 2 measured frames, where he stood one row above the floor on the side pipe at `t0 + 13` and `t0 + 14` (`E = t0 + 27`). So it allows that height, and the proof handles a landing there. In round 35 the field was false at 144 px, two rows above the floor, on runs that climb onto the side pipe ([Past the block's right end: a landing at any height](c-7-8-4-OffLand.md)).

**Round 36: the frames of `offSlow`** (`room-off-slow FM2 400`, measured only; runs as `room-off-back`, half of them with jumps from the block's top). For each frame that starts in a slow jump: the speed `v` and the stored speed `s` at the player's routine `R` and at the end of the move `Q`.

| | before `t0 − 1` | from `t0 − 1` on |
|---|---|---|
| frames | 12,401 | 20,886 |
| `\|v\| > A − 1` or `s > A − 1` at `R` | 0 | 0 |
| `\|v\| > A − 1` at `Q` | 0 | 0 |
| `s` at `Q` neither that of `R` nor `\|v\|` | 0 | 0 |
| the move to `Q` not `16·v` | 0 | 0 |
| the rest of the frame not `Collide` | 0 | 0 |
| the stored speed at the frame's end not that of `Q` | 0 | 0 |
| `s ≠ \|v\|` at `R` (a stale stored speed) | 428 | 2,160 |
| a move of more than `16·(A − 1)` (against `offSlow`) | 0 | 0 |

The largest speed is 24, the largest stored speed 24, the largest move 384 = `16·(A − 1)`: no margin.

## What remains (not proved)

* Three of the five new fields. Ways to prove them later:
  * `offTop`: the block's right column. At `t0 − 1` his left foot is over it, so he is on or above its top. A proof also needs where the stands before `t0` can be, and that a jump that passes over the block's right end without landing on its top does not happen (as `no_landing` shows for `Over` from the fields of `way`).
  * `offFloor`: false on real runs, gone in round 35 (item 1-1-c-7-8-4): the proof allows a landing at any height.
  * `offNear`: proved in round 36 (item 1-1-c-7-8-5, [The entering frame: the frame before the entry is near the floor](c-7-8-5-EntryVert.md)), no longer a field: the walks of the room's frames follow the entering frame too.
  * `offSlow`: gone in round 37 (item 1-1-c-7-8-6, [The air speed cap after `t0`: the frames of a slow jump](c-7-8-6-AirMove.md)). The caps of `X_Physics` and `ImposeFriction` in the air below the threshold are proved from ROM checks (`FrameModel.airOK`), and the stored speed is followed from the slow takeoff (`slowAbs`, `absOr0`). The speed after the end of the move is kept or 0 (a walk of the room's frames, `RoomSpeedKeep`). What remains is the field `offCollide`: on the frames after `t0` in a slow jump, the position after the end of the move moves at most one pixel (`CollideP`). Before round 37: the air speed cap after `t0`, by the horizontal model on the frames after `t0`. Measured in round 36 (`room-off-slow FM2 400`, below): on every frame that starts in a slow jump, at the player's routine `|v| ≤ A − 1` and the stored speed `s ≤ A − 1`; at the end of the move `|v| ≤ A − 1`, `s` is that of the player's routine or `|v|`, and the position moved by `16·v`; and the rest of the frame is `FrameModel.Collide` (the speed kept or 0, the position kept or one pixel back, or one pixel forward from a speed at most 0). But the stored speed is not `|v|` at the player's routine on 2,160 of these frames from `t0 − 1` on (after a hit), so the model `hstep` (`FrameModel.move_model`) does not cover them. A proof needs: the caps of `X_Physics` in the air with the stored speed below the threshold, through the case walks of `FrameModel` (whose walk of `X_Physics` leaves the stored speed free); and `Collide` on these frames, which no walk of the room gives yet (the screen's edge clamp and `ImpedePlayerMove` write the position after the move). The general bound of a frame does not do: one frame at the top speed moves 2.5 px, 12 such frames 30 px (7,680), and the mouth is only 22 px (5,632) past the goal; the slow bound gives 18 px (4,608).
  * `offStand`: proved in round 35 (item 1-1-c-7-8-3), no longer a field.
* `Approach`, `Over` and the choice of the case of `way` (items 1-1-c-7-7, 1-1-c-7-9, 1-1-c-7-14) stay as they were.

**Files.** `Theorems/OffDrop.lean` (`nearB`, `offAt`, `slowF`, `slowArcs`, the counter `above`, `allLayers`, paths). `Theorems/RoomJoin.lean` (`offNext`, `offB`, `standFam`, `pipeLands`, `pipeAOk`, `RoomRun.off_gap_of` and its lemmas, the five fields, `RoomCore.off_gap`). `Main.lean`: `room-off-ways`; the private `Proof/RoomJoin.lean` gets the eight checks, `pipeA`, `pipeB`, `off_two`, `pipe_sum`, `stop_cap`, `hit_three`. Since round 35 `pipeLands`, `pipeAOk`, `pipeA`, `pipeB`, `pipe_sum` and the checks `pipeAc`, `pipeBc` are gone, `landS` and `landC` replace them, and the checks `keepA` and `offVfd` are added. Since round 36 `Main.lean` has `room-off-slow` (measured only), and `room-off-back` counts the entries with `E + 1 < t0 + aboveF` and with `E = t0 − 1 + aboveS`.

**Reproduce.**
```
.lake/build/bin/smbrta room-off-ways FM2 300     # the fields of this page on real frames, and the six checks (about 15 min)
.lake/build/bin/smbrta room-off-slow FM2 400     # round 36: the frames of offSlow (about 2 min)
```
