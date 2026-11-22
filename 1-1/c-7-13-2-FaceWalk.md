[← Back](README.md) | [English](c-7-13-2-FaceWalk.md) | [Japanese](c-7-13-2-FaceWalk-ja.md)

# The facing in the fall, on every frame

The field `facing` of [Joining the bonus room](c-5-RoomJoin.md) said that before the end of the fall (`C + 34`) a frame with an air input or a jump input keeps the facing direction. Round 28 ([The facing in the fall, on frames that follow `hstep`](c-7-13-1-FallFacing.md)) proved it on the frames that follow `hstep`. This round proves it on every frame, with a walk of the room's whole frame that follows the facing byte from the player's routine to the frame's end. The field `facing` is gone.

## Statements

`fm(n)` is the machine where frame `n + 1` begins, `end(n)` the machine at its end, `T_k` the machine after `k` instructions of the frame. At the player's routine (`T_k.pc = PlayerCtrlRoutine`): `st` the player's state, `a` bit 7 of the joypad byte that the routine reads (A now), `p` bit 7 of A of the frame before. `fd` is the facing byte.

```
FaceIn(T)  :=  st = 1  ∨  st = 2  ∨  (st = 0 ∧ a = 1 ∧ p = 0)

face_frame (proved, RoomFace):
  the frame starts in the room's condition, every instruction meets SiteOK, the frame ends in the player's routine,
  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  FaceIn(T_k)   →   fd(end(n)) = fd(T_k)

InRoom.face (proved on the real machines: Route.Run.roomFace):
  C ≤ n,  n + 1 < E,  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  FaceIn(T_k)   →   fd(end(n)) = fd(T_k)

facing_of (proved; RoomCore.facing):
  C ≤ n < C + fall,  inp(n + 1).st ≠ 0 ∨ inp(n + 1).jump   →   fd(hs(n + 1)) = fd(hs(n))
```

`inp(n + 1)` is read at the player's routine (`read_inp`): `st ≠ 0` there means the state 1 or 2 (`InRoom.cut`: the state is 0, 1 or 2), and `jump` means the state 0 with `a = 1` and `p = 0` (`faceIn_of_read`). At the player's routine the facing is that of the frame's start (`InRoom.before`). The old field asked the same as `facing_of`, with one more premise `¬Follow(n)`; `facing_of` does not need it.

## How the walk works

The walk is `RoomVert`'s walk of one whole frame of the room (the abstract machine of `RoomMap`, which knows the room's bytes, the block buffers and the target of every store), with one bit, as `RoomVert.walkB` and `RoomWall`'s walk from the collision routine:

1. At the player's routine the walk splits the state into pieces (`piecesF`): the state 1, the state 2, the state 0 with `a = 1` and `p = 0` carry the bit; the state 0 with `a = 0`, the state 0 with `a = 1` and `p = 1`, the state 3, and the states with a bit above bit 1 are marked `[2]`. The pieces cover every machine (`piecesF_cover`), and a piece with the bit covers only machines with `FaceIn`, a piece marked `[2]` only machines without it (`piecesF_class`).
2. A step of a piece with the bit that may write the facing drops the bit and marks the state `[1]` (`mayWriteF`; the erase of a coin writes only in the block buffers). The walk asks that the frame comes to the player's routine once.
3. At the frame's end a state marked `[1]` must have the routine byte known and not the reference's (`finF`): the frame has left the player's routine.
4. So a frame that comes to the player's routine with `FaceIn` and ends in the player's routine has no step from there to its end that writes the facing (`after_F`, the same proof as `RoomVert.after_Q`).

Why it can pass (the check decides it; this is only a reading of the code): in the player's routine the facing is written on the ground with Left or Right (`OnGroundStateSub`), while swimming, and in the climbing routine. With the state 1 or 2 the routine of the state is the jump's or the fall's, and the swimming flag is 0 in the room. With a new press of A on the ground the jump starts before the routine of the state, which then is the jump's. In the collision routine the facing is written at a flagpole and at a vine; the walk knows the room's map and does not reach them, or leaves the player's routine.

The check is `room_face : RoomFace.checkF sy screenNames ctx = true` and `room_face_apart` (the facing out of the block buffers, the three split bytes distinct), by `native_decide` in the private `Proof/RoomWall.lean`. As a program (`room-face-check`) it takes about 12 s and 374 MB.

## Measured

The field is gone, so nothing of it is left to measure. `room-approach-check FM2 300 1` (big, an artificial state) and `… 300 0` (small), the TAS and 2,700 own runs each, still count the frames of the old field (from `C + 1` to `C + 34`, with an air or a jump input read at the player's routine):

| size | such frames | of them not following `hstep` | of them with the facing changed |
|---|---|---|---|
| big | 91,834 | 7,462 | 0 |
| small | 91,823 | 7,478 | 0 |

`room-face-check` (the walk as a program): `apartF` and `checkF` true.

## What remains

Nothing of `facing`. `wall_turn` uses `RoomCore.facing` on every frame, with no split on `Follow`, and the ROM checks `WallFacts.face1`, `face2`, `face3` of round 28 are gone (`faceCheck` and `face_of_check` stay in RoomJoin, unused by the route).

**Files.** New `Theorems/RoomFace.lean` (`FaceIn`, `piecesF`, `phF`, `finF`, `apartF`, `checkF`, `piecesF_class`, `piecesF_cover`, `keepF_step`, `after_F`, `face_frame`). `Theorems/RoomJoin.lean`: `InRoom.face` (new), `faceIn_of_read`, `facing_of`, `RoomCore.facing` (new, from `facing_of` in `toCore`); `RoomFields.facing` removed. `Theorems/Route.lean`: `Run.roomFace`; `Run.inRoom` takes the two checks. Private `Proof/RoomWall.lean`: `room_face`, `room_face_apart`. Program: `room-face-check`.
