[← Back](README.md) | [English](c-7-8-1-OffWays.md) | [Japanese](c-7-8-1-OffWays-ja.md)

# The ways off the block: measured

The field `way` of [Joining the bonus room](c-5-RoomJoin.md) says how a run gets past the block's right end at frame `t0` (the first frame past it): over the block in one jump (`Over`, item 1-1-c-7-9), or onto the block and off it (`Approach` and `Off`, items 1-1-c-7-7 and 1-1-c-7-8). `Off` has two cases: a jump from the block's top (`Off.jump`: the takeoff frame `T + 1`, a jump from the block's height that reaches the floor at frame `F ≤ E`), or stepping off (`Off.step`: frame `t0` walks past the block's end, and he falls to the floor by `F ≤ E`). This round only measures them; no field changed.

`Over` cannot happen: `RoomJoin.no_landing` proves `False` from it with the checks (he does not pass over the whole block in one jump, from the floor or from the block's side). So on a real run the field `way` is `onto`.

## Measured

`room-off-check FM2 300` (measured only): the TAS and 1,800 own runs from the room's first control (six kinds of input that go right, with B and with jumps at random times), each up to the entry into the side pipe or 400 frames. For a run that gets past the block's right end before the entry, the last frame before `t0` that ends standing gives the way: on the block's top with frame `t0 − 1` standing there (stepping off), on the block's top earlier (a jump from it), on the floor or at another height (a jump over the block). `F` is the first frame from `t0` on that ends on the floor, `E` the entering frame.

| | runs |
|---|---|
| runs | 1,801 |
| past the block's right end before the entry | 243 |
| of them stepping off the block's top (`Off.step`) | 242 |
| of them a jump from the block's top (`Off.jump`; the TAS) | 1 |
| of them a jump over the block (`Over`) | 0 |
| runs that enter the side pipe | 124 |
| of them on the floor at some `F` with `t0 ≤ F ≤ E` | 124 |
| of them `F > E` (against `Off`) | 0 |

The least frames after first control: `t0` at `C + 99`, `F` at `C + 111`, `E` at `C + 111`. From `t0` to `F` at least 12 frames after a jump from the block's top, and at least 17 after stepping off. On the TAS he stands on the block's top last at `C + 78`, is past its right end at `C + 99`, and reaches the floor on the entering frame `C + 111`.

## What remains (not proved)

- `Off` (item 1-1-c-7-8) and the choice of the case of `way` stay fields. A proof would follow the vertical state after `t0` with the walks of the room (`InRoom.air` from a jump, `InRoom.stand` for the frames that start standing) to the floor, and tie the takeoff from the block's top to `VertJump.jumpOff` (`InRoom.jump`).
  Since round 34 this is done ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md)): `Off` is gone, and five fields on single frames are asked in its place.
- `Over` (item 1-1-c-7-9) is proved impossible (`no_landing`) once `way` is given; that a real run is one of the two cases of `way` is the field.

**Files.** `Main.lean`: the program `room-off-check` (measured only).
