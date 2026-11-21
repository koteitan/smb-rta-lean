[← Back](README.md) | [English](c-7-14-3-ApproachJump.md) | [Japanese](c-7-14-3-ApproachJump-ja.md)

# The low frames of the first jump

The field `way` of [Joining the bonus room](c-5-RoomJoin.md) gives, with no wall hit and no stop from `C + 37` to `t₀`, the last takeoff from the floor before a landing on the block (`Approach`). Its part `low` asks the collision routine on every low frame of that jump: `LowAt`, or for a big player's last low frame only `P ≤ c_P + S_low` ([A big player at the block's corner](c-7-14-1-BigApproach.md)).

Some of these frames are proved already, for another use: the frames of a jump from the floor since the end of the fall, by `C + 43`, while every frame of the jump ends at the height 152 or below (`RoomCore.low_jump`, [The vertical page through a jump](c-7-5-18-RoomHigh.md)). This page uses that in `landed_short`. Also, a frame left of the corner is `LowAt` by the definition (`P < c_P ≤ c_P + S_low`). So `low` asks only the other frames at or past the corner.

## Statements

`P(n)`, `y(n)` are the position (in 1/256 px) and the height at the end of frame `n`. `c_P` is the corner (51 px), `S_low = 415/256` px. `T1 + 1` is the takeoff frame, `s = T1 + 1 + u.low` the last low frame, `sz` the size byte at first control (0: big). `fall = 34`, `lastG = 6`, `rise = 8`, `cy = cornerY` (136 px). `LowAt(n) := P(n) ≤ c_P + S_low ∧ (Stop(n) ∨ P(n) < c_P ∨ v(n) < 0)`.

```
Approach.low (field, narrowed):
  ∀ n ∈ [T1 + 1, s],  c_P ≤ P(n)  →                                                            (new premise)
    (C + fall + lastG < T1  ∨  C + fall + 1 + rise < n  ∨  ∃ j, T1 < j ≤ n ∧ y(j) < cy + 16)     (new premise)
    →  LowAt(n)  ∨  (sz = 0  ∧  n = s  ∧  P(n) ≤ c_P + S_low)

in landed_short (proved), with no wall hit, no stop, T1 ≤ C + fall + lastG (C + 40):
  ∀ n ∈ [T1 + 1, s],  n ≤ C + fall + 1 + rise  ∧  (∀ j, T1 < j ≤ n → cy + 16 ≤ y(j))  →  LowAt(n)
```

The proof of the second line:

- `T1` is on the floor since `C + fall` (`floor_all`), and `LowAt(T1)`: left of the corner before `C + 37` (`corner_late`), else on the floor (`floor_low`).
- the frames from `T1 + 1` to `n` are on the jump from `T1` (`arc_from`: at most `rise` frames after the takeoff frame, since `n ≤ C + 43` and `C + 34 ≤ T1`).
- then `RoomCore.low_jump` gives `LowAt(n)`.

`landed_short` uses `low` in three places: at `T1 + 1 + rise` after a takeoff after `C + 40` (only `P ≤ c_P + S_low`), on the low frames before `s`, and at `s`. Left of the corner the frame is `LowAt`. With a takeoff after `C + 40` it asks the field (the first case of the premise); otherwise it takes the line above where it applies and the field where it does not.

## Measured

`room-approach-check FM2 300 1` (big: the size byte set to big at first control, an artificial state) and `… 300 0` (small): the TAS and 2,700 own runs each, the runs with no wall hit, no stop and a landing on the block by `t₀`.

| size | runs | low frames of the last takeoff | in the narrowed field (at or past the corner) | proved (left of the corner, or by `low_jump`) | the field false | a proved frame not `LowAt` |
|---|---|---|---|---|---|---|
| big | 38 | 437 | 3 | 434 | 0 | 0 |
| small | 37 | 428 | 0 | 428 | 0 | 0 |

The 3 frames of a big player are the frames that take the coin above the block's left column: not `LowAt`, and the field's second case holds (the last low frame, at most 336/256 px past the corner).

## What remains

- `low` on the low frames at or past the corner after a takeoff after `C + 40`, after `C + 43`, or after a frame of the jump that ends from 136 to 151 px (3 measured frames, all of a big player). `RoomCore.low_floor` and `low_jump` are proved only up to `C + 43` (the vertical states are followed from the end of the fall for one jump), and the walks of the block's left side only at 152 px or below ([A bound for each low frame](c-7-5-20-LowBound.md) says what the heights from 136 to 151 need).

**Files.** `Theorems/RoomJoin.lean`: `Approach.low` narrowed; in `landed_short` the low frames of the first jump by `low_jump` (`alow`). Program `room-approach-check` (the counts above).

**Reproduce.**
```
.lake/build/bin/smbrta room-approach-check FM2 300 1      # big; with 0 at the end, small
```
