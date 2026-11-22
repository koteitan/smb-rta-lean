[← Back](README.md) | [English](c-7-4-2-RunWalk.md) | [Japanese](c-7-4-2-RunWalk-ja.md)

# `RunningSpeed` on the frames of the room: `stop_run` proved

The field `stop_run` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-4, narrowed in round 30: [How the left wall stops him](c-7-4-1-StopRun.md)) said that after the fall a frame that does not follow `hstep` leaves `RunningSpeed` 0. This round proves it with a walk of the room's whole frame that follows `RunningSpeed` from the player's routine to the frame's end. The field `stop_run` is gone. A smaller field `ab_run` takes its place: on some ground frames from `C + 37` on, the stored speed that the frame reads is below the running threshold.

## Statements

`fm(n)` is the machine where frame `n + 1` begins, `end(n)` the machine at its end, `T_k` the machine after `k` instructions of the frame. At the player's routine (`T_k.pc = PlayerCtrlRoutine`): `rs` is `RunningSpeed`, `st` the player's state, `xa` the stored speed `Player_XSpeedAbsolute`, `a` bit 7 of the joypad byte (A now), `p` bit 7 of A of the frame before. `R = RunSpeedMin` is the running threshold (1.75 px per frame), the byte that `GetPlayerAnimSpeed` compares the stored speed with.

On the numbers: `rs(n)` is `RunningSpeed` at the end of frame `n` (0 or not), `v(n)` the speed, `st(n)` the state, `ab(n)` the stored speed that frame `n + 1` reads at the player's routine, `inp(n + 1).jump` the jump bit of its input, `Follow(n)`: frame `n + 1` follows `hstep`. The room's numbers are `fall = 34`, `hitF = 37`, `runF = 40`.

```
RunIn(T)  :=  rs = 0  ∧  (st = 1  ∨  st = 2  ∨  (st = 0 ∧ (xa < R  ∨  (a = 1 ∧ p = 0))))

run_frame (proved, RoomRunSpeed):
  the frame starts in the room's condition, every instruction meets SiteOK, the frame ends in the player's routine,
  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  RunIn(T_k)   →   rs(end(n)) = 0

InRoom.run (proved on the real machines: Route.Run.roomRun):
  C ≤ n,  n + 1 < E,  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  RunIn(T_k)   →   rs(end(n)) = 0

RoomCore.stop_run (proved: RoomRun.stop_run_of; once a field):
  C + 34 ≤ n < C + 40,  rs(n) = 0,  |v(n)| < R,  ¬Follow(n)   →   rs(n + 1) = 0

ab_run (new field):
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  ¬Follow(n),  st(n) = 0,  inp(n + 1).jump = false,  ab(n) ≠ |v(n)|   →   ab(n) < R
```

The old field was `C + 34 ≤ n < C + 40, rs(n) = 0, ¬Follow(n) → rs(n + 1) = 0`. `RoomCore.stop_run` has one premise more, `|v(n)| < R`: its only users `rs_of_safe` and `no_wall_back` know it from `safeFrom`.

How `stop_run_of` goes. At the player's routine `RunningSpeed` is that of the frame's start (`InRoom.before`), so 0, and the state is 0, 1 or 2 (`InRoom.cut`). In the air, and on the ground with a new press of A, that is `RunIn`. On the ground with no jump the stored speed is read there (`read_ab`): it is `|v(n)| < R`; or, before `C + 37`, below the air threshold (the field `ab_early`, with `AirFastSpeed ≤ RunSpeedMin`: the frame is not `CleanR`, since a `CleanR` frame follows `hstep`); or, from `C + 37` on, below `R` by the field `ab_run`. Then `InRoom.run` gives `rs(n + 1) = 0`.

`ab_run` asks fewer frames than the old `stop_run`. On a frame of `ab_run` (on the ground, no jump) the player's routine calls `GetPlayerAnimSpeed`, which stores a stored speed of `R` or more into `RunningSpeed`. So, by this reading of the code (not proved), where the old field held, `ab(n) < R` held too. `ab_run` asks nothing of the frames before `C + 37`, of the frames in the air or with a jump, and of the frames whose stored speed is `|v(n)|`. It is a condition on one byte at one instruction.

## How the walk works

The walk is `RoomVert`'s walk of one whole frame of the room (the abstract machine of `RoomMap`), with one bit, as `RoomFace`:

1. At the player's routine the walk splits the state into pieces (`piecesR`). With the bit: `rs = 0` with the state 1; with the state 2; with the state 0 and the stored speed in a block below `R` (`lowB`); with the state 0 and `a = 1`, `p = 0`. Marked `[2]`: `rs` with a bit set (8 pieces), the state 0 with the stored speed in a block from `R` on (`highB`) with `a = 0` or with `a = 1`, `p = 1`, the state 3, a state with a bit above bit 1. A block is the set of bytes whose bits above a bit `b` are those of `R`: below `R` for each bit set in `R` (3 blocks), from `R` on for each bit clear in `R` and `R` itself (6 blocks). `blocksCheck` checks on all 256 bytes that the blocks below `R` hold only bytes below `R`, the others only bytes from `R` on, and that every byte is in one of them. The pieces cover every machine (`piecesR_cover`), a piece with the bit covers only machines with `RunIn`, a piece marked `[2]` only machines without it (`piecesR_class`).
2. A piece with the bit carries its block in its list, so that the search does not join two blocks (a join of two blocks below `R` can hold a byte from `R` on).
3. The abstract machine follows the value of `RunningSpeed`. At the frame's end a state with the bit must know `RunningSpeed` 0, or have the routine byte known and not the reference's (`finRS`): the frame has left the player's routine.
4. So a frame that comes to the player's routine with `RunIn` and ends in the player's routine ends with `RunningSpeed` 0 (`after_RS`).

Why it can pass (the check decides it; this is only a reading of the code): `RunningSpeed` is written only in `GetPlayerAnimSpeed`, on the ground and while swimming. It stores the stored speed when the compare with `R` finds it at `R` or more, else 0 or nothing. On a block below `R` the abstract compare is decided (the block's largest byte is below `R`), so that store is not reached. With a new press of A on the ground the jump starts before the routine of the state, which then is the jump's and does not call `GetPlayerAnimSpeed`. In the air the routine of the state is the jump's or the fall's, and the swimming flag is 0 in the room.

The check is `room_run_speed : RoomRunSpeed.checkR sy screenNames ctx = true` and `room_run_apart` (the five bytes apart, `blocksCheck` of `RunSpeedMin`), by `native_decide` in the new private `Proof/RoomRunSpeed.lean`. As a program (`room-run-check`) the search has no failure; at the frame's end there are 210 states, 186 of them with the bit, and `finRS` refuses none. `checkR` takes about 24 s (86 s with the printed search).

## Measured

`room-approach-check FM2 300 1` (big, an artificial state) and `… 300 0` (small), the TAS and 2,701 own runs each:

| | big | small |
|---|---|---|
| frames of `RoomCore.stop_run` (from `C + 34`, not following `hstep`, `rs` 0 and `|v| < R` at the start) | 3,132 | 3,153 |
| of them `rs ≠ 0` at the end (a bug of `stop_run_of`) | 0 | 0 |
| frames of the field `ab_run` | 457 | 479 |
| of them `ab ≥ R` (`ab_run` false) | 0 | 0 |
| room frames with `RunIn` at the player's routine (`InRoom.run`) | 756,154 | 761,907 |
| of them `rs ≠ 0` at the end (a bug of `InRoom.run`) | 0 | 0 |

On the frames of `ab_run` the largest stored speed is 1.5 px per frame (the threshold `R` is 1.75 px per frame): the air's top speed, stored before a stop.

Why a frame does not follow `hstep` (for `wall` and `late`, measured only; a frame can have more than one reason):

| | `wall` big | `wall` small | `late` big | `late` small |
|---|---|---|---|---|
| frames | 8,123 | 8,154 | 3,215 | 3,226 |
| stale: the stored speed at the player's routine not the size of the speed there | 3,688 | 3,698 | 1,501 | 1,517 |
| masked: the side he presses masked by the collision bits | 3,830 | 3,854 | 1,534 | 1,549 |
| pushed: a horizontal byte at the frame's end not the one at the end of the move | 4,442 | 4,464 | 1,743 | 1,733 |
| none of the three | 0 | 0 | 0 | 0 |

On a pushed frame of `wall` the coordinate at the end of the move is 12 or 13 px (the left wall); on a pushed frame of `late` it is from 12 to 52 px (the left wall, or the block's left side).

## What remains (not proved)

- `ab_run`: from `C + 37` to `C + 40`, on the ground with no jump, a stale stored speed (not `|v(n)|`: it was stored before a stop) below `R`. A proof needs a bound on the stored speed through the frames that stop him: it is the size of the speed after `ImposeFriction` on the last frame that called it, which may be a frame before.
- `wall` and `late` (unchanged). Every measured frame of them is stale, masked or pushed, and before `C + 37` the pushes come only at the left wall (above). A proof would follow these three reasons through the frames: a push only near the wall (a walk from the end of the move that shows no push away from it), and a stale stored speed or a masked side only after a push.

**Files.** New `Theorems/RoomRunSpeed.lean` (`lowB`, `highB`, `blocksCheck`, `RunIn`, `piecesR`, `phR`, `finRS`, `apartR`, `checkR`, `piecesR_class`, `piecesR_cover`, `after_RS`, `run_frame`). `Theorems/RoomJoin.lean`: `InRoom.run` (new), `RoomFields.ab_run` (new field), `RoomFields.stop_run` removed, `RoomCore.stop_run` (new, from `RoomRun.stop_run_of` in `toCore`), `Checks.runMin`; `rs_of_safe` and `no_wall_back` pass `|v| < R`. `Theorems/Route.lean`: `Run.roomRun`; `Run.inRoom` takes the two checks. Private `Proof/RoomRunSpeed.lean`: `room_run_speed`, `room_run_apart`. Programs: `room-run-check`, `room-approach-check` (counters 59 to 72).
