[← Back](README.md) | [English](c-7-13-1-FallFacing.md) | [Japanese](c-7-13-1-FallFacing-ja.md)

# The facing in the fall, on frames that follow `hstep`

The field `facing` of [Joining the bonus room](c-5-RoomJoin.md) says that before the end of the fall (`C + 34`) a frame with an air input or a jump input keeps the facing direction. Its only user is `wall_turn`: to face anything but right after a wall hit he needs a ground frame with no jump.

This round proves the field on every frame that follows `hstep`, by a check of `hstep` on the ROM. The field is asked only on the frames that do not follow `hstep` (the frames at the left wall and right after them).

## Statements

`hs(n)` is the horizontal state at the end of frame `n`, `fd` its facing, `inp(n + 1)` the input of frame `n + 1`, with `st` (0 on the ground) and `jump` (a new press of A on the ground). `Follow(n)`: frame `n + 1` follows `hstep`.

```
faceCheck(fd) (ROM, for fd = 1, 2, 3):  ∀ s ∈ statesFd(fd), ∀ i ∈ inputsN:  (i.st = 0 ∧ ¬i.jump) ∨ hstep(s, i).fd = s.fd

face_of_check (proved):  inD(s) ∧ i ∈ inputs ∧ (i.st ≠ 0 ∨ i.jump)  →  hstep(s, i).fd = s.fd

facing (field, narrowed):
  C ≤ n < C + fall → (inp(n + 1).st ≠ 0 ∨ inp(n + 1).jump) → ¬Follow(n) → fd(hs(n + 1)) = fd(hs(n))
  (before: the same without ¬Follow(n))
```

`faceCheck` is in `WallFacts` (`face1`, `face2`, `face3`, by `native_decide` in the private `room_stand_w`). `face_of_check` reads the normalized input as `negJ_of_check` does: `norm` keeps `st` and `jump` (`norm_st`, `norm_jump`).

In `wall_turn` each frame of the chain from `C` to `b + 1` is either `Follow` (then `hs(n + 1) = hstep(hs(n), inp(n + 1))`, and `face_of_check` with `inD` of the frame, `inD_at`) or not (then the field).

Why `hstep` keeps the facing there: in `hstep` the facing is written only on the ground with Left or Right and no jump; with a jump the state becomes 1 before the routines of the move, and `X_Physics` and `ImposeFriction` do not write it. The check confirms it on every state and input of the domain.

## Measured

`room-approach-check FM2 300 1` (big, an artificial state) and `… 300 0` (small): the TAS and 2,700 own runs each, the frames from `C + 1` to `C + 34` with an air or a jump input read from the machine at the player's routine.

| size | such frames | of them not following `hstep` (the field) | of them with the facing changed (field false) | frames following `hstep` with the facing changed (a bug) |
|---|---|---|---|---|
| big | 91,834 | 7,462 | 0 | 0 |
| small | 91,823 | 7,478 | 0 | 0 |

## What remains

- `facing` on the frames that do not follow `hstep`. On those frames the collision routine stops him at the left wall; a walk of the room's frame that follows the facing byte from the player's routine to the frame's end would prove it (the climbing routine and the flagpole's routine write it, as in part e's `FaceKeep`).
- `stand_fast`, `stand_P`: not changed. Measured in the same runs: 44 stands before `C + 34` (big) and 50 (small), all with `−V ≥ standV` and `P ≤ standP` on the frame before; the least `−V` was 3952 (big) and 4256 (small) against `standV = 3584`, the largest `P` 3632 against `standP = 3712`. A proof needs the collision at the left wall with the position of the frame before.

Round 29: `facing` on the frames that do not follow `hstep` is proved too, by that walk ([The facing in the fall, on every frame](c-7-13-2-FaceWalk.md)); the field is gone.

**Files.** `Theorems/RoomJoin.lean`: `faceCheck`, `norm_jump`, `face_of_check`; `WallFacts.face1`, `face2`, `face3`; `RoomFields.facing` narrowed; `wall_turn`. Private: `room_stand_w` (3 more `native_decide` lines). Since round 29 `WallFacts.face1`–`face3` and these 3 lines are gone: the facing is proved on every frame ([The facing in the fall, on every frame](c-7-13-2-FaceWalk.md)). Program: `room-approach-check` (counters 34 to 37; 38 to 40 measure `stand_fast` and `stand_P`).
