[← Back](README.md) | [English](c-7-6-2-FallCap.md) | [Japanese](c-7-6-2-FallCap-ja.md)

# The stored speed through the fall

Since round 33 ([The stored speed after a frame that follows the model](c-7-4-4-StoredClean.md)) the field `ab_early` of [Joining the bonus room](c-5-RoomJoin.md) was asked in two cases: after a masked side, and after a stale stored speed carried in the air with neither Left nor Right. In the second case the stored speed that frame `n` reads is the one frame `n − 1` read (`RoomRun.ab_stale`), and so on back to an earlier stop in the fall. Round 33 measured 43 such frames, with stored speeds of at most 0.375 px a frame. From round 34 this case is proved, unless an earlier frame came to its player's routine with the side it presses masked.

## What is proved

`ab(n)` is the stored speed that frame `n + 1` reads at its player's routine (`read_ab`), `A` the air threshold (1.5625 px a frame), `hs(n)` the horizontal state at the end of frame `n`, `Φ` the potential of `Potential`.

```
RoomRun.cap_fall :  d ≤ fall,  C + d ≤ t0  →  |v(C + d)| < A  ∧  (d < fall  ∧  st(C + d) = 0  →  Φ(hs(C + d)) ≤ stopPhi)
RoomRun.ab_fall  :  d ≤ fall,  C + d < t0,  no frame k ∈ (C, C + d] masked  →  ab(C + d) < A
```

A frame `k` is masked (`MaskedAt`) when it comes to its player's routine with the stored speed `|v|` but not in the state `FrameModel.AtCtrl`: the side it presses is masked by the collision bits.

`cap_fall` is an induction over the frames of the fall:

* At first control he stands still (`start_fallR`).
* A frame that follows `hstep` from the air has an air input (`air_in_of`), and `AirCap.step_cap` keeps the speed below `A`.
* A frame that ends standing in the fall does not follow `hstep` (`stand_off_of`; he is not on the floor before `C + fall`, `fall_long_of`), so it is a stop, with `Φ ≤ stopPhi`.
* One frame of `hstep` from such a stand gains at most `gFast` (`Potential.stepOk`), and `stopPhi + gFast + 255 < 256·A` (the new fact `NumFacts.stop_cap`).

`ab_fall` is an induction over the same frames:

* At first control the stored speed is 0 (`StartAt.ab`).
* After a frame that follows the model it is `|v|` (`ab_cleanW`), below `A` by `cap_fall`.
* After a stop in the state `AtCtrl` it is the size of `hstep`'s speed from the state before (`ab_fresh`), below `A` as in `cap_fall`.
* After a stale stop it is at most one adder and a fraction (`ab_stale`, `amax_air`), or in the air with neither side the one of the frame before.
* A masked frame is the only case it does not follow.

So in `RoomRun.ab_of_run`, after a stale stop in the air with neither side, the stored speed is `ab(n − 1) < A` by `ab_fall` (frame `n − 1` is at most `C + fall`: `hitF ≤ fall + 3`, the new fact `NumFacts.hit_three`), unless an earlier frame was masked.

## The field

`ab_early` (one frame), changed:

```
until round 33:  C + 34 ≤ n,  n + 1 < C + 37,  n < t0,  ¬CleanR(n),  ¬AtCtrl(T(n − 1)),  (xa = |v| at T(n − 1)  ∨  AirNoSide(n − 1))  →  ab(n) < A
from round 34:   the same with  (xa = |v| at T(n − 1)  ∨  (AirNoSide(n − 1)  ∧  ∃ k, C < k < n,  MaskedAt(T(k − 1))))
```

It is weaker than before: it asks one more premise in its second case. No field is removed; no new field. New checks: the facts `stop_cap`, `hit_three` (numbers, `native_decide`).

## Measured

`room-ab-check FM2` (the TAS and 2,800 own runs from first control):

| | |
|---|---|
| frames before `C + 37` that come to the player's routine with the side masked | 41 (all in runs of one kind of input, which holds Left with B most of the time) |
| frames of the old second case (stale, in the air with neither side) | 43 (as in round 33; stored speed at most 6, 0.375 px a frame) |
| of them after a masked frame (the field since round 34) | 0 |

## What remains (not proved)

* `ab_early` and `ab_run` after a masked side (item 1-1-c-7-4): the friction then pushes the speed the other way from the model, and the stored speed is not followed.
* `ab_run`'s second case (a stale stored speed carried in the air with neither side, from `C + 37` to `C + 40`): after the fall he may run on the floor, so `cap_fall` does not reach there. No measured frame is in it.

**Files.** `Theorems/RoomJoin.lean` (`capped_of_phi`, `RoomRun.cap_fall`, `RoomRun.ab_fall`, `MaskedAt`, `RoomRun.ab_of_run`, `NumFacts.stop_cap`, `hit_three`). `Main.lean`: `room-ab-check` counts the masked frames; the private `Proof/RoomJoin.lean` gets `stop_cap`, `hit_three`.
