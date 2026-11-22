[← Back](README.md) | [English](c-7-5-21-PushOne.md) | [Japanese](c-7-5-21-PushOne-ja.md)

# One pixel after a frame at the corner

The field `low_at` of [Joining the bonus room](c-5-RoomJoin.md) is gone. Since round 27 it was asked only for a frame from `C + 41` to `C + 43` that ends from 136 to 151 px at or past the corner, when every frame from `C + 40` on is at or past the corner ([A bound for each low frame](c-7-5-20-LowBound.md)). On measured runs no frame was of this kind.

Now `low_by` proves these frames from three facts:

1. The frames that `low_floor` and `low_jump` prove are at most `lowT = 383/256` px past the corner, not only `S_low = 415/256` px.
2. After such a frame at or past the corner, a frame that starts in the air moves him at most 1 px right (`push_one`).
3. Frame `C + 40` ends at 152 px or below on every jump from the floor after the fall (`riseCheck`, with the stored speed that the takeoff reads, `off_ab`).

## Statements

`P(n)`, `y(n)`, `v(n)` are the position (in 1/256 px), the height and the speed at the end of frame `n`. `c_P` is the corner (51 px). `top` is the top speed: one frame moves at most `16·top = 640/256` px (`move_top`). `cy = cornerY` (136 px), so `cy + 16` is 152 px. `fall = 34`, `hitF = 37`, `runF = 40`, `fall + 1 + rise = 43`. `ab(n)` is the stored speed that frame `n + 1` reads. `v_A = 25` is the air threshold of the speed.

```
LowS(s, n)   ⇔  P(n) ≤ c_P + s ∧ (Stop(n) ∨ P(n) < c_P ∨ v(n) < 0)          LowAt(n) = LowS(S_low, n)
SlackOK(s)   ⇔  255 ≤ s ∧ 16·top − 257 ≤ s ∧ s + 16·top < 1280
lowT         =  16·top − 257 = 383                                           (S_low = 415)

RoomCore.low_floor, low_jump (proved, now for every s with SlackOK(s)):
  LowS(s, ·) goes on along the floor frames after the fall, and along a jump from the floor while it ends at cy + 16 or below

RoomCore.push_one (proved, new):
  C ≤ n < t₀ ∧ n < C + standF ∧ st(n) ≠ 0 ∧ (Stop(n) ∨ v(n) < 0)  →  P(n + 1) ≤ P(n) + 256

RoomCore.off_ab (proved, new):
  C ≤ n < t₀ ∧ n + 1 < E ∧ jump(n + 1)  →  vs(n + 1) = jumpOff(y(n), ab(n)) ∧ ab(n) < 256

low_by (proved; no field is used any more on these frames):
  C ≤ n ≤ C + 43 ∧ n ≤ t₀  →  P(n) ≤ lowB(n − C)
```

Two checks on the ROM, by `native_decide` in the private `room_corner_facts`:

```
gainCheck:  ∀ s in the domain with v(s) < 0, ∀ input i in the air:  V(hstep(s, i)) ≤ g_fast        (V = 256·v + subspeed, g_fast = 456)
riseCheck:  ∀ v < 256, ∀ A on each frame:  every frame of the jump from jumpOff(groundY, v) ends at cy + 16 or below
            for 5 frames after the takeoff frame when v < v_A, for 4 frames when v ≥ v_A
```

and `CornerFacts.tight` (`255 ≤ lowT`), `off16` (the takeoff frames from the floor end at 152 px or below), `floor16` (so does the floor), `fall2` (`fall + 2 ≤ hitF`).

## How `low_by` proves the frames of the old field

The case: no wall hit, `n` from `C + 41` to `C + 43`, `n` ends from 136 to 151 px off the floor, and every frame from `C + 40` to `n` is at or past the corner. By `v_chain2` the frames from `C + 34` are on the floor up to a frame `T'`, and then frames of the jump from `T'`. On the first frames of a jump the height does not grow (`arc_down`).

**Frame `C + 40` ends at 152 px or below.** By induction over `d`, each frame `C + 40 + d` up to `n` that ends above 152 px has

```
P(C + 40 + d) ≤ c_P − 1 + 16·top·d
```

- `d = 0`: frame `C + 40` does not end above 152 px.
- The frame before ends above 152 px: one frame at the top speed (`move_top`).
- The frame before, `k`, ends at 152 px or below: it is a frame of the jump (the floor ends at 176 px, the takeoff frame at 171 or 172 px). Every frame of the jump up to `k` ends at 152 px or below (`arc_down`), so `LowS(lowT, k)` (`low_jump` from the floor frame `T'`, which is `LowS(lowT)` by `low_floor` or left of the corner). `k` is at or past the corner, so `Stop(k)` or `v(k) < 0`. Then `push_one`: `P(k + 1) ≤ c_P + 383 + 256 = c_P − 1 + 16·top`.

With `d = n − (C + 40)` this is `lowB(n − C)`.

**Frame `C + 40` ends above 152 px: impossible.** It is a frame of the jump from `T'`, with `C + 34 ≤ T' < C + 40`, and the takeoff frame `T' + 1` has a jump in its input (`vfloor`: a floor frame stays on the floor or takes off). So `vs(T' + 1) = jumpOff(groundY, ab(T'))` (`off_ab`), and each later frame of the jump is `vstep` (`varc`). Frame `C + 40` is `C + 40 − (T' + 1)` frames after the takeoff frame.

- If `T' = C + 34`, the takeoff comes right after the fall. The frames of the fall are air frames with no wall hit, so the speed stays below the air threshold (`capped_along`), and the stored speed that the takeoff reads is below it (`ab_of`, `fall2`). So frame `C + 40` is 5 frames after the takeoff frame of a slow takeoff.
- If `T' ≥ C + 35`, it is at most 4 frames after the takeoff frame.

`riseCheck` covers both: frame `C + 40` ends at 152 px or below.

The least height of the jumps from the floor, by frames after the takeoff frame (evaluated on the ROM):

| frames after the takeoff frame | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| slow (stored speed below 25) | 172 | 168 | 164 | 160 | 157 | 153 | 150 | 147 | 144 |
| fast (25 or more) | 171 | 166 | 161 | 156 | 152 | 148 | 144 | 140 | 136 |

## Why the slack is not changed

`push_one` needs the frame before within `lowT = 383/256` px of the corner. `low_step` (the step of `low_floor_of` and `low_jump_of`) gives it: in each of its cases the next frame is at most `max(c_P + 16·top − 257, P(n))` (pushed back one pixel after one frame at the top speed from left of the corner, or moving left, or less than 17 of speed from a stop). So `low_floor` and `low_jump` hold for every slack of `SlackOK`. `lowSlack` itself stays 415: with 383 the check `NumFacts.wall_low` (after a wall hit, on the low frames) fails by 1/256 px (margin −1; with 415 it is +31).

## Measured

`room-approach-check FM2 300 1` (big: the size byte set to big at first control, an artificial state) and `… 300 0` (small): the TAS and 2,700 own runs each.

| size | frames of round 27's field | of them with frame `C + 40` above 152 px | frames of `low_jump` past `c_P + lowT` (a bug) | frames of `push_one` | of them more than 1 px right (a bug) |
|---|---|---|---|---|---|
| big | 0 | 0 | 0 | 86,366 | 0 |
| small | 0 | 0 | 0 | 86,275 | 0 |

No run with no wall hit had frame `C + 40` above 152 px (counter 33: 0 of 1,193 such runs, big; 0 of 1,187, small). `push_one` was counted on every run, on frames up to `t₀` before `C + 50` that start in the air after a frame stopped or moving left.

## What remains

- Nothing of `low_at`.
- `Approach.low` stays (3 measured frames of a big player: a coin above the block's left column takes the side check, and the frame is not pushed back).
- `stand_wall` (the second stand), `stand_fast` and `stand_P` are not changed in this round; `facing` is narrowed to the frames that do not follow `hstep` ([The facing in the fall](c-7-13-1-FallFacing.md)).

**Files.** `Theorems/RoomJoin.lean`: `LowS`, `SlackOK`, `lowT`, `gainCheck`, `gain_of_check`, `riseFrom`, `riseCheck`, `takeoff16`, `slack_ok`, `tight_ok`, `low_floor_atS`; `RoomCore.low_floor` and `low_jump` for every slack of `SlackOK`; new `RoomCore.push_one` (`RoomRun.push_one_of`) and `RoomCore.off_ab` (`RoomRun.off_ab_of`); new fields of `CornerFacts`: `tight`, `gain1`, `gain2`, `gain3`, `off16`, `floor16`, `rise`, `fall2`; `low_by`; `RoomFields.low_at` removed. Private: `room_corner_facts` in `Proof/RoomJoin.lean` (8 more `native_decide` lines). Program: `room-approach-check` (counters 28 to 32).

**Reproduce.**
```
.lake/build/bin/smbrta room-approach-check FM2 300 1      # big; with 0 at the end, small
```
