[← Back](README.md) | [English](c-7-4-3-AbsKeep.md) | [Japanese](c-7-4-3-AbsKeep-ja.md)

# The stored speed after a stop: `ab_run` narrowed

The field `ab_run` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-4, made in round 31: [`RunningSpeed` on the frames of the room](c-7-4-2-RunWalk.md)) says that a stale stored speed read on a ground frame from `C + 37` to `C + 40` is below the running threshold. This round follows the stored speed from the frame that writes it to the frame that reads it. When the frame before stops him and comes to its player's routine with the stored speed `|v|` and the side he presses not masked, the stored speed that is read is the size of `hstep`'s speed from the state before. Then `safeFrom` puts it below the threshold. `ab_run` is asked only on the other frames.

## Statements

`fm(n)` is the machine where frame `n + 1` begins, `fe(n)` the machine at the end of frame `n`, `T_k` the machine after `k` instructions of frame `n + 1` (from `fm(n)`), `end(n)` the machine at its end. `xa` is the stored speed `Player_XSpeedAbsolute`. `PlayerSubs` is the end of the move. `R = RunSpeedMin` is the running threshold (1.75 px per frame).

On the numbers: `hs(n)`, `v(n)`, `rs(n)`, `st(n)` are the horizontal state, the speed, `RunningSpeed` and the state at the end of frame `n`; `inp(n)` the input of frame `n`; `ab(n)` the stored speed that frame `n + 1` reads at its player's routine; `Follow(n)`: frame `n + 1` follows `hstep`. `AtCtrl(n)`: frame `n + 1` comes to its player's routine in the state `FrameModel.AtCtrl` (with `xa = |v|` there, and the side he presses not masked by the collision bits). `CleanW(n)`, `ReadW(n)`: the two cases of the field `clean` for frame `n + 1` (it follows the model; it stops him). The room's numbers are `fall = 34`, `hitF = 37`, `runF = 40`.

```
abs_frame (proved, RoomAbsKeep):
  the frame starts in the room's condition, every instruction meets SiteOK:
  it comes to PlayerSubs at most once, and if it ends in the player's routine,
  T_k.pc = PlayerSubs,  T_k.frame = fm(n).frame   →   xa(end) = xa(T_k)

InRoom.absAfter (proved on the real machines: Route.Run.roomAbs):  the same for C ≤ n, n + 1 < E
InRoom.absBefore (proved: Route.Run.roomAbsBefore):  C ≤ n < E,  T_k.pc = PlayerCtrlRoutine   →   xa(T_k) = xa(fm(n))
InRoom.absKeep (proved: Route.Run.roomKeepA):  C ≤ n < E   →   xa(fm(n)) = xa(fe(n))

RoomRun.ab_fresh (proved):
  C ≤ n,  n + 1 < t0,  ReadW(n),  AtCtrl(n)   →   ab(n + 1) = |hstep(hs(n), inp(n + 1)).v|

RoomCore.stop_run (proved: RoomRun.stop_run_of; one premise more):
  C + 34 ≤ n < C + 40,  rs(n) = 0,  |v(n)| < R,
  (n = C + 34  ∨  ∀ i ∈ inputs, |hstep(hs(n − 1), i).v| < R),  ¬Follow(n)   →   rs(n + 1) = 0

ab_run (field, now of RoomRun; narrowed):
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  ¬Follow(n),  st(n) = 0,  inp(n + 1).jump = false,  ab(n) ≠ |v(n)|,
  (CleanW(n − 1)  ∨  ¬AtCtrl(n − 1))   →   ab(n) < R
```

The old `ab_run` (round 31) had the same premises but the last one. So the new field asks fewer frames: it is not asked when frame `n` stops him (`ReadW(n − 1)`) and comes to its player's routine in the state `AtCtrl`.

How `ab_fresh` goes. Frame `n + 1` comes to its player's routine at `k₀` in the state `AtCtrl`, and `ReadW` gives the collision bits there as one of `TopSpeed.collBits`; so the state is `FrameModel.AtFrame`. Then `FrameModel.stored_path` gives an instruction at `PlayerSubs` with `xa = |v|`, and `FrameModel.move_model` an instruction at `PlayerSubs` with the horizontal state `hstep(hs(n), inp(n + 1))`. The frame comes to `PlayerSubs` once (`InRoom.absAfter`), so the two are the same instruction. From there to the frame's end no step writes `xa` (`InRoom.absAfter`); the frames that end paused before frame `n + 2` keep it (`InRoom.absKeep`), and so does frame `n + 2` up to its player's routine (`InRoom.absBefore`), where `read_ab` reads `ab(n + 1)`.

How `stop_run_of` goes now. As in round 31, but on the ground with no jump from `C + 37` on, with a stale stored speed: the field `clean` for frame `n` says `CleanW(n − 1)` or `ReadW(n − 1)`. With `ReadW(n − 1)` and `AtCtrl(n − 1)`, `ab_fresh` gives `ab(n) = |hstep(hs(n − 1), inp(n)).v|`; the input read from a machine is one of `inputs` (`readIn_mem`), so the new premise of `stop_run` puts it below `R`. The other cases are the field `ab_run`.

The new premise of `RoomCore.stop_run` comes from `safeFrom`: `rs_of_safe3` carries, at each frame `C + 34 + d` with `1 ≤ d`, that every input of the model from the state at the end of frame `C + 34 + d − 1` keeps the speed below `R` (`safe_step` from `safeFrom` there). It is not asked at `n = C + 34`; the new number fact `NumFacts.hit_two` (`fall + 2 ≤ hitF`) says that from `C + 37` on `n` is not `C + 34`. The same premise serves the narrowed `ab_early` ([`ab_early` only from the end of the fall](c-7-6-1-EarlyFall.md)) at `n = C + 35`.

## How the walk works

The walk is `RoomVert`'s walk of one whole frame of the room (the abstract machine of `RoomMap`), with one bit, as the walk from the scroll handler of `RoomVert` (`after_QP`):

1. At `PlayerSubs` every state gets the bit (`phX`).
2. A state with the bit whose step may write `xa` (`mayWriteX`: `StepWrites.keepOK` for the one byte) drops the bit and is marked `[1]`. The erase of a coin writes in the block buffers; `apartX` says that `xa` is not there.
3. At the frame's end a state marked `[1]` must have the routine byte known and not the reference's (`RoomVert.finB`): the frame has left the player's routine.
4. So a frame that comes to `PlayerSubs` and ends in the player's routine ends with `xa` of `PlayerSubs` (`after_QX`).

Why it can pass (the check decides it; this is only a reading of the code): `xa` is written only at the end of `ImposeFriction`, which the routines of the player's state call before the end of the move.

The stored speed is also put into `RoomVert.vKeepA`, the bytes that the walk to the player's routine keeps (`RoomVert.before_R`) and that a frame that ends paused keeps (`RoomVert.paused_R`). So the old walk's check now asks one byte more.

The checks are `room_abs_keep : RoomAbsKeep.checkX sy screenNames ctx = true` and `room_abs_apart`, by `native_decide` in the new private `Proof/RoomAbsKeep.lean`, and `room_checks.stored` (`FrameModel.storedOK`). As a program (`room-abs-check`) the search has no failure; at the frame's end there are 40 states, none marked `[1]`, and `finB` refuses none; the command takes about 7 s with the printed search.

## Measured

`room-approach-check FM2 300 1` (big, an artificial state) and `… 300 0` (small), the TAS and 2,701 own runs each:

| | big | small |
|---|---|---|
| frames of the field `ab_run` of round 31 | 457 | 479 |
| of them, the frame before comes to its player's routine in the state `AtCtrl` and is pushed after its move (not `CleanW`): proved by `ab_fresh` | 457 | 479 |
| of them, the stored speed not `|hstep(hs(n − 1), inp(n)).v|` (a bug of `ab_fresh`) | 0 | 0 |
| frames of the narrowed field `ab_run` | 0 | 0 |
| frames of `RoomCore.stop_run` (from `C + 34`) | 3,132 | 3,153 |
| of them `rs ≠ 0` at the end (a bug of `stop_run_of`) | 0 | 0 |
| of them from `C + 37` (the new premise asked) | 2,504 | 2,521 |
| of them, an input of the model from the state before reaching `R` (the premise false) | 0 | 0 |

So on every measured frame of the old field the frame before stopped him and came to its player's routine with the stored speed `|v|` and the side not masked. The narrowed field asks only the frames whose frame before follows the model, or comes to its player's routine with a stale stored speed or a masked side; none was measured.

## What remains (not proved)

- `ab_run` on the frames where frame `n` follows the model (`CleanW`), or comes to its player's routine with a stale stored speed or a masked side. On a frame that follows the model `stored_path` would give `xa = |v|` at the end of the move as well, but it needs the collision bits there to be one of `TopSpeed.collBits`, which only `ReadW` gives. On a stale or masked frame `n` the speed after `ImposeFriction` is not `hstep`'s; `FrameModel.frame_readQL` bounds it by `|V(n − 1)|` and one friction adder, which `safeFrom` does not bound.
- `wall`, `late` (unchanged).

**Files.** New `Theorems/RoomAbsKeep.lean` (`mayWriteX`, `phX`, `apartX`, `checkX`, `searchX`, `keepX_step`, `after_QX`, `abs_frame`). `Theorems/RoomVert.lean`: `vKeepA` holds the stored speed. `Theorems/RoomJoin.lean`: `InRoom.absBefore`, `InRoom.absKeep`, `InRoom.absAfter` (new facts), `Checks.stored`, `NumFacts.hit_two`, `RoomFields.ab_run` removed, `RoomRun.ab_run` (the narrowed field), `RoomCore.stop_run` (one premise more), `rs_of_safe3`, `safe_v`, `RoomRun.ab_fresh`; `stop_run_of`, `rs_of_safe`, `no_wall_back`, `toCore`. `Theorems/Route.lean`: `Run.roomAbsBefore`, `Run.roomAbs`; `Run.inRoom` takes the two checks. Private `Proof/RoomAbsKeep.lean`: `room_abs_keep`, `room_abs_apart`. Programs: `room-abs-check`, `room-approach-check` (counters 73 to 81).
