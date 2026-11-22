[← Back](README.md) | [English](c-7-5-20-LowBound.md) | [Japanese](c-7-5-20-LowBound-ja.md)

# A bound for each low frame

The field `low_at` of [Joining the bonus room](c-5-RoomJoin.md) was left for the frames of a jump that end from 136 to 151 px, at or past the corner, from `C + 37` to `C + 43`, after a frame at or past the corner ([A frame above 152 px after a frame left of the corner](c-7-5-19-BandStart.md)). On measured runs there were 8 such frames (7 of a big player, 1 of a small one).

This page does not prove the collision at those heights either. It gives `low_by` a bound for each frame in place of one bound for all. The numbers of the stops after the low frames lose exactly one frame at the top speed per frame, so a later frame may be one frame at the top speed further right. With that, the field is asked only after `runF` (`C + 40`), and only when every frame from `C + 40` on is at or past the corner. None of the 8 measured frames is of this kind: each has a frame left of the corner at `C + 41`.

## Statements

`P(n)`, `y(n)` are the position (in 1/256 px) and the height at the end of frame `n`. `c_P` is the corner (51 px), `G_P` the goal, `S_low = 415/256` px, `top` the top speed: one frame moves at most `16·top = 640/256` px (2.5 px, `move_top`). `cy = cornerY` (136 px). `hitF = 37`, `runF = 40`, `fall + 1 + rise = 43`, `goalF = 98`.

```
lowB(j) =  c_P − 1 + 16·top·(j − (hitF − 1))   for j ≤ runF      (j − 36)
           c_P − 1 + 16·top·(j − runF)          for j > runF      (j − 40)

low_by (proved; was  P(n) ≤ c_P + 16·top − 1):
  C ≤ n ≤ C + 43 → n ≤ t₀ → P(n) ≤ lowB(n − C)

low_at (field, narrowed):
  NoWall → C + runF + 1 ≤ n ≤ C + 43 → n ≤ t₀ → cy ≤ y(n) < cy + 16 → ¬OnFloor(n) → c_P ≤ P(n)
    → (∀ k, C + runF ≤ k < n → c_P ≤ P(k))                 (was  c_P ≤ P(n − 1), and n from C + hitF)
    → P(n) ≤ c_P − 1 + 16·top·(n − (C + runF))             (was  P(n) ≤ c_P + 16·top − 1)

NumFacts (numbers of the ROM, native_decide in room_nums; each was one inequality with c_P + 16·top − 1):
  hit_J:     ∀ j, hitF ≤ j ≤ runF:        lowB(j) + dbound(stopPhi, goalF − j) < G_P
  hit_F:     ∀ j, runF < j ≤ 43:          lowB(j) + fastDist(stopPhi, goalF − j) < G_P
  hit_late:  ∀ j, 43 < j ≤ goalF:  min(lowB(43) + 16·top·(j − 43), c_P + stopSlack) + fastDist(stopPhi, goalF − j) < G_P
```

The new field is implied by the old one: it asks fewer frames, and on them less.

How `low_by` gets its bound:

- `n < C + hitF`: he is left of the corner (`corner_late`).
- `n ≤ C + runF`: from `C + hitF − 1`, where he is left of the corner, one frame at the top speed per frame (`move_top`). No field is used, and no condition on a wall.
- `n > C + runF`, and some frame `k` from `C + runF` to `n − 1` is left of the corner: from `k` the same.
- otherwise, with no wall: the frames that end on the floor and the jump frames at 152 px or below are `LowAt` (`low_floor_at`, `low_jump`), so `P ≤ c_P + S_low ≤ c_P + 16·top − 1 ≤ lowB`; a frame from 136 to 151 px is the field.
- with a wall hit: the potential from the wall, `P ≤ c_P + 16·top − 1` as before.

Its only user, `stop_short`, reads it at the last stop `h` by `C + 43` (`hit_J` up to `runF`, `hit_F` after it) and at `C + 43` before a later stop (`hit_late`). `dbound` and `fastDist` are the potential's bounds of the rest of the run from a stop. From `C + 36` to `C + 43` each of them is exactly `16·top` less per frame later: so `lowB` may grow by `16·top` per frame.

Margins at `C + 98`, in 1/256 px short of the goal (evaluated, and checked by `native_decide`):

| check | frames | margin |
|---|---|---|
| `hit_J` | 37 to 40 | 1 each |
| `hit_F` | 41 to 43 | 17 each |
| `hit_late` | 44 to 98 | 17 at 44 to 46, then 400, 1040, 1680, … |

Before this round the same checks had the margins 1, 17 and at least 1297 with `c_P + 16·top − 1` at every frame.

## Measured

`room-approach-check FM2 300 1` (big: the size byte set to big at first control, an artificial state) and `… 300 0` (small): the TAS and 2,700 own runs each.

| size | frames of round 26's field (from 136 to 151 px, the frame before at or past the corner) | of them in the new field (every frame from `C + 40` at or past the corner) | past the new bound |
|---|---|---|---|
| big | 7 | 0 | 0 |
| small | 1 | 0 | 0 |

All 8 frames are at `C + 43`, with `P(C + 41) < c_P` (from 16/256 to 288/256 px left of the corner).

On the runs that are at or past the corner at `C + 40` in a jump (12 shown), that frame ends at 152 px or below, pushed back with the speed 0, and `C + 41` is left of the corner (176/256 to 256/256 px). A climb toward the new field's frames (`room-big band FM2 3000 BIG`: 3,000 changes of own inputs for each takeoff on `C + 35` and `C + 36`, each size; right with B, then A, B and right) found none: its best score was −64 (`min(P(C + 40), P(C + 41)) − c_P − 64·max(0, y(C + 41) − 151)`).

Why the field is not gone. At `C + 40` he can be past the corner: the largest `P(C + 40) − c_P` on runs with no wall hit is 80/256 px, on the floor and also in a jump from a takeoff by `C + 38`. So a bound at `C + 40` alone does not empty the field. After a frame at or past the corner that is `LowAt`, the summary of one frame (`TopSpeed.Frame`; `FrameModel.Collide` lets a frame end one pixel right of its end of the move when the speed there is 0 or less) bounds the next frame only by `c_P + S_low + 256`, 671/256 px past the corner: 16/256 px more than the margin of `hit_F` allows at `C + 41` (655). This bound is an argument here, not a theorem of the project.

## What remains

- Round 28: the case below is proved, and the field `low_at` is gone ([One pixel after a frame at the corner](c-7-5-21-PushOne.md)).
- `low_at` for a frame from `C + 41` to `C + 43` that ends from 136 to 151 px when every frame from `C + 40` on is at or past the corner (0 measured frames). It needs the collision at the block's left side at those heights: the size byte at the end of the move, cells that are a coin or empty, and the walk of `RoomCorner` there.

**Files.** `Theorems/RoomJoin.lean`: `lowB` new, `NumFacts.hit_J`, `hit_F`, `hit_late` for each frame, `low_by`'s conclusion, `stop_short`, `RoomFields.low_at` narrowed. Private: `hit_J`, `hit_F`, `hit_late` in `room_nums` (`Proof/RoomJoin.lean`, unchanged text). Program `room-approach-check` (the counts above).

**Reproduce.**
```
.lake/build/bin/smbrta room-approach-check FM2 300 1      # big; with 0 at the end, small
.lake/build/bin/smbrta room-big band FM2 3000 1          # the climb; with 0 at the end, small
```
