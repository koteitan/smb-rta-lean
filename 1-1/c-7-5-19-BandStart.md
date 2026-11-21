[← Back](README.md) | [English](c-7-5-19-BandStart.md) | [Japanese](c-7-5-19-BandStart-ja.md)

# A frame above 152 px after a frame left of the corner

The field `low_at` of [Joining the bonus room](c-5-RoomJoin.md) is left for the frames of a jump that end from 136 to 151 px (above `cornerY + 16`), at or past the corner, from `C + 37` to `C + 43`, with no wall hit ([The vertical page through a jump](c-7-5-18-RoomHigh.md)). There the walk of the block's left side does not pass with the size not known, and a big player is not pushed back on the frame that takes the coin above the block's left column ([A big player at the block's corner](c-7-14-1-BigApproach.md)).

This page does not prove the collision there. It shows that the theorems need less: at most one frame at the top speed past the corner. So a frame whose frame before is left of the corner is proved by the top speed alone, and the field asks only the frames whose frame before is at or past the corner.

## Statements

`P(n)`, `y(n)` are the position (in 1/256 px) and the height at the end of frame `n`. `c_P` is the corner (51 px), `S_low = 415/256` px, `top` the top speed: one frame moves at most `16·top = 640/256` px (2.5 px, `move_top`). `cy = cornerY` (136 px).

```
low_at (field, narrowed):
  NoWall → C + 37 ≤ n ≤ C + 43 → n ≤ t₀ → cy ≤ y(n) → ¬OnFloor(n) → c_P ≤ P(n) → y(n) < cy + 16
    → c_P ≤ P(n − 1)                                   (new premise)
    → P(n) ≤ c_P + 16·top − 1                          (was  P(n) ≤ c_P + S_low)

low_by (proved; was  P(n) ≤ c_P + S_low):
  C ≤ n ≤ C + 43 → n ≤ t₀ → P(n) ≤ c_P + 16·top − 1
  new case, y(n) < cy + 16 and P(n − 1) < c_P:   P(n) ≤ P(n − 1) + 16·top ≤ c_P − 1 + 16·top   (move_top)

NumFacts (numbers of the ROM, native_decide in room_nums):
  low_top (new):   S_low ≤ 16·top − 1
  hit_J:           c_P + (16·top − 1) + dbound(stopPhi, 98 − 37) < G_P          (was with S_low)
  hit_F:           c_P + (16·top − 1) + fastDist(stopPhi, 98 − 41) < G_P        (was with S_low)
  hit_late:        for 43 < j ≤ 98:  min(c_P + (16·top − 1) + 16·top·(j − 43), c_P + stopSlack) + fastDist(stopPhi, 98 − j) < G_P
```

`low_by`'s other cases give `P(n) ≤ c_P + S_low` (the floor frames, `low_floor_at`; the jump frames at 152 px or below, `low_jump`; the wall, `wall_low`) or `P(n) < c_P` (before `C + 37`), and `low_top` makes them `≤ c_P + 16·top − 1`. Its only user, `stop_short`, reads it at a stop by `C + 43` (`hit_J`, `hit_F`) and at `C + 43` before a later stop (`hit_late`).

Margins at `C + 98`, in 1/256 px short of the goal, with `S_low` and now with `16·top − 1` (639): `hit_J` 225 and 1, `hit_F` 241 and 17, `hit_late` at least 1521 and at least 1297.

## Measured

`room-approach-check FM2 300 1` (big, the size byte set to big at first control: an artificial state) and `… 300 0` (small): the TAS and 2,700 own runs, the frames of the old `low_at` that end from 136 to 151 px:

| size | frames of the old `low_at` | of them from 136 to 151 px | the frame before left of the corner (proved) | the frame before at or past the corner (the field) |
|---|---|---|---|---|
| big | 103 | 55 | 48 | 7 |
| small | 50 | 3 | 2 | 1 |

None of them is more than `16·top − 1` past the corner, and the old, stronger statement (`P ≤ c_P + S_low` on every such frame) holds on all of them too.

## What remains

- `low_at` for a frame from 136 to 151 px whose frame before is also at or past the corner. It needs the collision at the block's left side at those heights: the size byte at the end of the move (the walk of `SizeKeep` gives it only at the frame's start and end), cells that are a coin or empty, and the walk of `RoomCorner` there.

**Files.** `Theorems/RoomJoin.lean`: `RoomFields.low_at` narrowed, `NumFacts.low_top` new, `hit_J`, `hit_F`, `hit_late` with `16·top − 1`, `low_by`'s conclusion, `stop_short`. Private: `low_top` in `room_nums` (`Proof/RoomJoin.lean`). Program `room-approach-check` (the counts above).

**Reproduce.**
```
.lake/build/bin/smbrta room-approach-check FM2 300 1      # big; with 0 at the end, small
```
