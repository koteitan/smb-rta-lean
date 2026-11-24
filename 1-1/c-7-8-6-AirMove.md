[← Back](README.md) | [English](c-7-8-6-AirMove.md) | [Japanese](c-7-8-6-AirMove-ja.md)

# The air speed cap after `t0`: the frames of a slow jump

Until round 36 the field `offSlow` of [Joining the bonus room](c-5-RoomJoin.md) said: from `t0`, the first frame past the block's right end, to the entering frame `E`, a frame that starts in a slow jump from the block's top moves him at most `16·(A − 1)` sixteenths of a pixel right. `A` is the air threshold (`AirFastSpeed`, 25), so `16·(A − 1)` is 384, 1.5 px. [Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md) uses it in one case: a slow jump that would enter `aboveS = 12` frames after `t0 − 1` is too short of the mouth.

Since round 37 `offSlow` is gone. The movement routine's part of those frames is proved, and so is the speed after the end of the move. What remains is a field on the same frames about the position after the end of the move only: `offCollide`.

## What is proved

`R` is a frame's player's routine, `Q` its end of the move (`PlayerSubs`), `F` the frame's end. `v` is the speed, `s` the stored speed (`Player_XSpeedAbsolute`), `P` the position in 1/256 px. `SlowAt(M)` is `s ≤ A − 1 ∧ |v| ≤ A − 1` at the machine `M`.

**One frame, from the ROM** (`FrameModel.air_pathA`, `air_pathB`, file `Theorems/AirMove.lean`): at `R` the machine is `AtV`, he is in the air or a jump starts there (`stOf ≠ 0`), `s < A` and `|v| ≤ A − 1`. Then

```
air_pathA :  ∃ k,  Q = stepN k R at PlayerSubs  ∧  |v(Q)| ≤ A − 1  ∧  P(Q) ≡ P(R) + 16·v(Q)  (mod 2²⁴)
air_pathB :  ∃ k,  Q = stepN k R at PlayerSubs  ∧  s(Q) ≤ A − 1
```

No condition on the collision bits, and none that the stored speed is `|v|` (it is not so on 2,160 of the frames in a slow jump from `t0 − 1` on that `room-off-slow FM2 400` measured, after a hit). The checks (`FrameModel.airOK`, `native_decide` in the private `Proof/RoomJoin.lean`, about 5 s natively):

* `physAirOK`: on each case of `FrameModel` in the air with Left or Right, the walk of `X_Physics` from its cut, once for each stored speed `s < A`, known. At its return the caps are `A − 1` to the right and `−(A − 1)` to the left, and the adder is an entry of the table (`capsAir`).
* `fricAirOK`: `ImposeFriction` on the real machine next to the model's machine, with the collision bits known only on their two low bits. `ImposeFriction` reads them only in `and` with Left/Right.
* `fricCapCheck`: `ImposeFriction` with these caps, from every speed with `|v| ≤ A − 1`, every fraction, every adder, side, and value of the two low bits, ends with `|v| ≤ A − 1` and the stored speed `|v|`.
* `17 ≤ A ≤ 128`.

With neither Left nor Right the speed and the stored speed stay from `R` to the mover (the walks of `FrameModel.caseOK`). From the mover the walk `tail_spec` gives the move, and the walk `storedTailOK` keeps the stored speed.

**On the real frames of the room** (`RoomJoin.lean`):

```
air_frame :  C ≤ n < E  ∧  (st(fm n) ≠ 0 ∨ a jump at R)  ∧  SlowAt(fm n)  ∧  CollideP(Q, F)  →
               (16·(A − 1) ≤ P(fm n)  →  P(F) ≤ P(fm n) + 16·(A − 1))
             ∧ (P(fm n) + 16·(A − 1) < 2²⁴  →  P(fm n) − 16·(A − 1) − 256 ≤ P(F))
             ∧ (n + 1 < E  →  SlowAt(F))
slow_start :  T + 1 < t0, a slow takeoff at T + 1, the frames after it before t0 in the air  →  ∀ i,  T + i ≤ t0 − 1  →  SlowAt(fm(T + i))
slow_run   :  D + 1 = t0,  D + aboveS = E,  SlowAt(fm D),  every frame from D on in a slow jump  →
               ∀ i < aboveS,  P(D + i + 1) ≤ P(D + i) + 16·(A − 1)
```

`CollideP(Q, F)` (the position's part of `FrameModel.Collide`): `P(F) = P(Q) ∨ P(F) = P(Q) − 256 ∨ (P(F) = P(Q) + 256 ∧ v(Q) ≤ 0)`.

**The speed after the end of the move** (`RoomSpeedKeep`, the new fact `InRoom.speedAfter`, round 37):

```
InRoom.speedAfter :  C ≤ n  ∧  n + 1 < E  ∧  pc(k) = PlayerSubs  →  v(F) = v(trace k)  ∨  v(F) = 0
```

A walk of the room's whole frame (the abstract machine of `RoomMap`, as `RoomAbsKeep`'s walk of the stored speed) sets a bit at `PlayerSubs`. A state with the bit whose step may write the speed drops it and is marked; a marked state must end the frame out of the player's routine, or with the speed known to be 0 (`finV`). The collision routine (`ImpedePlayerMove`) and the clamp of the screen's edge store only 0. The check `checkV` (`native_decide` in the private `Proof/RoomSpeedKeep.lean`) takes about 9 s natively: 56 states at the frame's end, 20 of them marked, none refused. `Route.Run.roomSpeed` gives the fact on the real machines, as `roomAbs` gives `absAfter`.

* `air_frame`: the frame reaches its end of the move once (`InRoom.absAfter`), so the two ends of `air_pathA` and `air_pathB` are the same instruction; after it no step writes the stored speed, and the speed is kept or 0 (`speedAfter`), so `|v| ≤ A − 1` stays. `CollideP` moves him at most one pixel; a pixel forward only from `v ≤ 0`, so at most 256 ≤ `16·(A − 1)`.
* `slow_start`: the stand at `T` ends `SlowAt`. The takeoff's stored speed is that of the stand's end, and it is below `A` (the check `slowAbs`: a takeoff from the block's top with the fall force of a slow takeoff (`slowF`) read a stored speed below `A`). At the end of a frame before `t0` the stored speed is `|v|` or the speed is 0 (`absOr0`, round 33), so `|v| ≤ s ≤ A − 1`. The takeoff and the frames in the air up to `t0 − 1` keep `SlowAt` (`air_frame`, with `clean` after their end of the move).
* `slow_run`: frame `t0` is one of `clean`; the frames after it are those of the field `offCollide`. The position stays at least 8 px and far below the end of its range (`NumFacts.slow_low`, `slow_hi`), so the move `16·v` does not wrap.

`off_arc` (the slow case) uses `slow_run` in place of `offSlow`; its conclusion and that of `off_gap_of` (`t0 < E ∧ t0 + aboveF ≤ E + 1`) are unchanged. `off_arc` and `off_gap_of` now take the state at first control (`StartAt`), for `absOr0`.

## The fields

Removed:

```
offSlow :  ∀ n,  t0 ≤ n + 1  ∧  n < E  ∧  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  P(n + 1) ≤ P(n) + 16·(A − 1)
```

Added (a field of `RoomRun`, one frame):

```
offCollide :  ∀ n,  t0 ≤ n  ∧  n < E  ∧  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  ∀ j ≥ arr n,  pc(j) = PlayerSubs  →  CollideP(trace j, F)
```

`offCollide` is not weaker than `offSlow` in every way. It asks one frame less (frame `t0` is a frame of `clean`), and nothing of the movement routine or of the speed. But it asks of the position after the end of the move on its own: at most one pixel either way. So it asks also that the rest of the frame does not move him more than one pixel left, which `offSlow` did not ask. Before `t0` the field `clean` asks this and more of every frame (`ReadW.collide`, `CleanW.after`).

New ROM checks (`Checks`): `airM` (`FrameModel.airOK`) and `slowAbs` (`OffDrop.slowAbs`); the walk `RoomSpeedKeep.checkV` (`Route.Run.inRoom` takes it). New numbers (`NumFacts`): `slow_low : 2288·aboveS + 2048 ≤ goal`, `slow_hi : goal + 2032·aboveS + 4096 < 2²⁴`. New fact of `InRoom`: `speedAfter`.

## Measured

`room-air-move FM2 400` (from `PLACE/git`): the movie's room frames and 225 runs of own inputs from the room's first control (as `room-off-slow`: onto the block's top, right to `t0`, half of them with jumps from the block's top, then back and forth).

| | |
|---|---|
| runs | 226 (the movie and 225 own) |
| frames that come to the player's routine in the air or with a jump, with `s < A` and `\|v\| ≤ A − 1` | 46,800 |
| of them with `\|v(Q)\| > A − 1`, `s(Q) > A − 1`, or a move other than `16·v(Q)` (against `air_pathA`, `air_pathB`) | 0 |
| frames from `t0 + 1` on that start in a slow jump (the frames of `offCollide`) | 20,881 |
| of them with the position changed after the end of the move | 2,200 |
| of them with more than one end of the move | 0 |
| of them not `CollideP`, or with a speed at the frame's end that is neither that of the end of the move nor 0, at an end of the move | 0 |
| frames of the jumps from a slow takeoff up to the landing | 34,689 |
| of them not `SlowAt` at the player's routine | 0 |
| frames from `t0` on with neither `s = \|v\|` nor `v = 0` at their start | 0 of 43,319 |

The movie's jump from the block's top is fast, so it has no frame of `offCollide`.

## What remains (not proved)

* `offCollide`: the position after the end of the move, on the frames after `t0`. `ImpedePlayerMove` moves him one pixel; the clamp of the scroll handler (`KeepOnscr`) sets the position to the screen's edge. A walk that only follows bytes does not do: on 2,200 of the measured frames the position changes after the end of the move. A proof needs a walk of the room's frames from the end of the move that follows the position through these writes (part e has summaries of both routines, `ImpedePosition.routine_return`, `ScreenClamp.clamp_return`, for the surface's frames).
* `offTop` ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md)): not changed.

**Files.** `Theorems/AirMove.lean` (new: the checks and `air_c4`, `air_pathA`, `air_pathB`). `Theorems/RoomSpeedKeep.lean` (new: the walk `checkV`, `after_QV`, `speed_frame`). `Theorems/Route.lean` (`Run.roomSpeed`, `Run.inRoom`). `Theorems/OffDrop.lean` (`slowAbs`, `slowAbs_spec`). `Theorems/RoomJoin.lean` (`CollideP`, `SlowAt`, `offCollide`, `InRoom.speedAfter`, `air_frame`, `slow_start`, `slow_run`, `off_arc`, the checks `airM`, `slowAbs`, the numbers `slow_low`, `slow_hi`). `Main.lean`: `room-air-move`, `room-speed-keep`, the generator of the private `Proof/RoomSpeedKeep.lean`; the private `Proof/RoomJoin.lean` gets the new checks and numbers, and `Proof/Route.lean` passes the walk's check to `Run.inRoom`.

**Reproduce.**
```
.lake/build/bin/smbrta room-air-move FM2 400     # the checks airOK and slowAbs, and the facts of this page on real frames (about 2 min)
.lake/build/bin/smbrta room-speed-keep           # the walk RoomSpeedKeep.checkV (about 15 s)
```
