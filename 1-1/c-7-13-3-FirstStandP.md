[← Back](README.md) | [English](c-7-13-3-FirstStandP.md) | [Japanese](c-7-13-3-FirstStandP-ja.md)

# The position before the first stand

The field `stand_P` of [Joining the bonus room](c-5-RoomJoin.md) says that on the frame before a stand in the fall (before `C + 34`) he is at or left of `standP = 3712` (14.5 px). This round asks it only on the frame before the first stand of the fall: the two theorems that use it, `stand_first` and `wall_turn`, use no other frame.

## Statements

`P(n)` is the position at the end of frame `n` (in 1/256 px), `st(n)` the player's state there.

```
stand_P (field, narrowed):
  C ≤ n,  n + 1 < C + 34,  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0   →   P(n) ≤ standP
  (before: the same without the third premise)
```

- `stand_first` is about the first stand of the fall: its premise `∀ j, C < j ≤ n → st(j) ≠ 0` is the new premise.
- `wall_turn` uses it on its stand `i` on the wall when that stand's frame is the first one that does not follow `hstep`; `i` is the first stand (`hfirst`).

## Why the bound is what it is (numbers, not proved)

- `standP = 3712 = 13·256 + 384`. Every measured stand at the wall has `x = 12` at the end of its move (round 21). From `x ≤ 12` after a move of at most 24/16 px left (the air speed with `RunningSpeed` 0), `P(n) ≤ 3327 + 384 = 3711`.
- The model of a frame that stops (`TopSpeed.Frame`) bounds the speed after the move only by `top = 40`: `3327 + 640 = 3967`.
- `wall_turn` needs `P(n) < P0 − leftDist(Φ₀, 14) = 3904` (`stand_far`, margin 192): this pushes the first stand from `C + 15` (what `wall_far` gives with `wallP = 3968` and `P0 − leftDist(Φ₀, 13) = 4192`) to `C + 16`. So 3967 is not enough.

## Measured

- `room-stand-first FM2 300` (this round, the TAS and 2,100 own runs, 126,060 frames): 49 stands away from the floor before frame 51, all first stands of the fall at frames 18 to 30. So the old field and the narrowed one ask the same measured frames.
- `room-approach-check FM2 300 1` and `… 300 0` (this round): 44 (big) and 50 (small) stands before `C + 34`, `P ≤ standP` on the frame before each (largest `P` 3632; least `−V` 3952 and 4256 against `standV = 3584`).

## What remains

Round 30 ([The position before the first stand, proved](c-7-13-4-StandHit.md)): `stand_P` is gone. `wall_turn`'s case is proved (`RoomCore.stand_hit`), and `stand_first` takes the position from `RoomRun.fall_left` and the walks of `InRoom.wall` (`WallX`, `WallF`). The text below is the state of round 29.

The field on the frame before the first stand. A proof needs: a stand at the wall has `x ≤ 12` at the end of its move (a walk from the end of the move as `RoomWall`'s, for `x` from 13 on), and the frame's move left is at most 24/16 px (the model of the movement at the end of the move for a frame that stops).

**Files.** `Theorems/RoomJoin.lean`: `RoomFields.stand_P`, `stand_first`, `wall_turn`.
