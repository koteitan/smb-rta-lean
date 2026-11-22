[← Back](README.md) | [English](c-7-4-1-StopRun.md) | [Japanese](c-7-4-1-StopRun-ja.md)

# How the left wall stops him: measured, and `stop_run`, `late` narrowed

The item 1-1-c-7-4 of [Joining the bonus room](c-5-RoomJoin.md) has three fields about the frames that do not follow `hstep`. This round measures all three on real runs and narrows `stop_run` and `late` to the frames that their users need.

## Statements

`P(n)` is the position at the end of frame `n` (in 1/256 px), `rs(n)` is `RunningSpeed` there (0 or not), `Follow(n)`: frame `n + 1` follows `hstep`. `wallP = 3968` (15.5 px), `c_P = 13056` the block's corner, `top = 40`. The numbers of the room: `fall = 34`, `hitF = 37`, `runF = 40`.

```
wall (field, unchanged):
  C ≤ n,  n + 1 < C + 37,  ¬Follow(n)   →   P(n) ≤ wallP ∧ P(n + 1) ≤ wallP ∧ rs(n + 1) = 0

late (field, narrowed):
  C + 37 ≤ n + 1,  n ≤ C + 40,  (∃ h, C ≤ h < n ∧ h + 1 < C + 37 ∧ ¬Follow(h)),  ¬Follow(n)
    →   (P(n) ≤ wallP ∧ P(n + 1) ≤ wallP ∧ rs(n + 1) = 0) ∨ c_P ≤ P(n) + 16·top
  (before: the same without the third premise)

stop_run (field, narrowed):
  C + 34 ≤ n,  n < C + 40,  rs(n) = 0,  ¬Follow(n)   →   rs(n + 1) = 0
  (before: C ≤ n,  n < C + 40,  ¬Follow(n)  →  rs(n + 1) = 0)
```

`stop_run` is used only by `rs_of_safe` and `no_wall_back`. Both use it on a frame from the end of the fall on (`C + fall + d`), and both know there that `RunningSpeed` is 0 at the frame's start (the step before of `rs_of_safe`). So the field asks: after the fall, a frame that does not follow `hstep` does not set `RunningSpeed`.

`late` is used only by `anchor_at`, which follows the frames after the first frame `h` that does not follow `hstep`, with `h + 1 < C + 37`. So it is asked only after such a frame: a run with no wall hit before `C + 36` (for example a hit at the corner on the floor) is out of the field.

## Measured

`room-approach-check FM2 300 1` and `… 300 0` (this round; the TAS and 2,701 own runs each, a big player and the size as it is):

- `wall`: 8,123 and 8,154 frames before `C + 37` that do not follow `hstep`. All are `WallAt`: the largest `P` before the frame 3888 and 3904, after it 3824, against `wallP = 3968`.
- `late`: 3,215 and 3,226 frames from `C + 37` to `C + 41` that do not follow `hstep` (the old field), false on none. The narrowed field has 1,479 and 1,490 of them (after an earlier frame off `hstep` by `C + 36`), false on none.
- `stop_run`: 10,627 and 10,675 frames by `C + 40` that do not follow `hstep` (the old field), false on none. The narrowed field has 3,132 and 3,153 of them (from `C + 34` on, starting with `RunningSpeed` 0), false on none.

## What remains (not proved)

- `wall`: a frame before `C + 37` that does not follow `hstep` is stopped at the left wall. A proof needs the reason why a frame does not follow `hstep` (a side push or a stand at the wall, a stale stored speed after one, a masked side) and the position at each.
- `late` (narrowed): the same from `C + 37` to `C + 41` after a wall hit, or at the corner.
- `stop_run` (narrowed): `RunningSpeed` is written only by `GetPlayerAnimSpeed`, on the ground, from the stored speed. A proof needs a walk of the frame that follows `RunningSpeed`, and the stored speed below the running threshold at the frame's start. Round 31 did this: `stop_run` is proved and no longer a field; what is left is the smaller field `ab_run` ([`RunningSpeed` on the frames of the room: `stop_run` proved](c-7-4-2-RunWalk.md), item 1-1-c-7-4-2).

**Files.** `Theorems/RoomJoin.lean`: `RoomFields.stop_run`, `RoomFields.late`, `RoomCore.rs_of_safe`, `RoomCore.no_wall_back`, `RoomCore.anchor_at`, `RoomRun.anchor_atR`. Program `room-approach-check` (counters 46 to 51, 55 to 58).
