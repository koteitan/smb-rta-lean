[← Back](README.md) | [English](c-7-5-16-FirstStand.md) | [Japanese](c-7-5-16-FirstStand-ja.md)

# The first stand of the fall

The field `stand_wall` of [Joining the bonus room](c-5-RoomJoin.md) said: before `C + 51`, he stands away from the floor only at the end of a frame that does not follow `hstep`. This page proves it for the first stand of the fall: a frame that ends standing away from the floor before `C + 34`, with no frame since first control that ends in the state 0. The theorems that used the field need no other frame without an earlier stand, so the field now asks only for a stand after an earlier frame that ends in the state 0. On real runs every stand away from the floor before `C + 51` is a first stand of the fall.

## Statements

`vs(n)`, `st(n)`, `hs(n)`, `P(n)` are the vertical state, the player's state, the horizontal state and the position at the end of frame `n`. `Follow(n)`: frame `n + 1` follows `hstep`. `OnFloor(s)`: `st = 0 ∧ y = 176`. `Q` is the end of the move of frame `n + 1` (its first `PlayerSubs`). At `Q`: `yhigh` the vertical page, `pg` the page, `x`, `y`, `st`, `vy`, `v` the speed byte.

```
WallQ(Q)  :=  yhigh = 1 ∧ pg = 0 ∧ x < 16 ∧ 32 ≤ y < 207 ∧ st ≤ 2 ∧ vy ≥ 0 ∧ (v = 0 ∨ v ≥ 129)

stand_wall (field, narrowed):
  C ≤ n,  n + 1 < C + 51,  (∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

stand_first (proved):
  C ≤ n,  n + 1 < C + 34,  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

stand_off_of (proved; RoomCore.stand_off):
  C ≤ n,  n + 1 < C + 51,  (n + 1 < C + 34  ∨  ∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

InRoom.wall (proved on the real machines: Route.Run.roomWall):
  C ≤ n,  n + 1 < E,  frame n + 1 starts in the air   →   ∃ Q,  vs(Q) = vstepR(vs(n), A)  ∧
    (WallQ(Q)  →  at the frame's end:  st ≠ 0  ∨  (st = 0 ∧ y = 176)  ∨  v = 0)
```

The speed byte `v ≥ 129` is a negative speed other than −128.

## How it is proved

1. Under `Follow(n)` the speed at the frame's end is that of `hstep(hs(n), inp(n + 1))`. The field `stand_fast` gives `V(hs(n)) ≤ −standV` (the speed −14 or less). A check of `hstep` (`negCheckJ`, `negJ_of_check`) on every state of the domain with `V ≤ −standV` and every input says that the speed byte after one frame is 129 or more: negative, not −128, and not 0.
2. The field `clean` makes the speed at the frame's end the speed at `Q`, or 0. It is not 0, so the speed at `Q` is that byte.
3. With no stand since first control, `vs(n)` is a state of the first fall (`fall_mem`): the state 2. So the frame starts in the air, and `InRoom.wall` gives `Q` with the vertical bytes of `vstepR`. The checks of the first fall give, at `Q`: the state 2 (`fallCheck`), `vy ≥ 0` and the vertical page 1 after the move (`highCheck`), and the height from 32 to 206 (the new check `wallYCheck`). The vertical page at the frame's start is 1 (`high_upto`: `high_fall` up to frame `n`).
4. The position at `Q`: the field `stand_P` gives `P(n) ≤ standP = 3712` (14.5 px). Under `Follow`, `P(n + 1) = P(n) + 16 · v < P(n)`. `Q` is at most 1 px right of the frame's end (`q_le_end`: the field `clean`, or `FrameModel.Collide`). So `P(Q) < 3712 + 256 < 4096`: the page 0 and `x < 16` (`page_x_of`).
5. So `Q` meets `WallQ`, and `InRoom.wall` says: at the frame's end `st ≠ 0`, or `st = 0` at the floor's height, or `v = 0`. The first is false (`st(n + 1) = 0`), the second is false (not on the floor), the third is false (step 1).
6. `Route.Run.roomWall` proves `InRoom.wall` as `Run.roomLand` proves `InRoom.land`: `RoomFall.land_frame` gives `Q` with `Good`, the stack of the player's routine and the vertical bytes of `vstepR`; `RoomBlocks.blocks_run_trace` gives `Solid` at `Q`; and `RoomWall.wall_frame` ([A stand away from the floor in the room](c-7-5-15-RoomWall.md)) goes from `Q` to the frame's end, which is in the player's routine (`roomStay`).
7. `stand_off_of` splits on an earlier frame that ends in the state 0: if there is one, the field; if not, the frame is before `C + 34`, and `stand_first`. `RoomRun.toCore` puts it into `RoomCore` as `stand_off`, which `st_ne`, `stand_gap` and `wall_turn` use. `st_ne` now asks the same condition: `fall_air`, `wall_right` and `stand_gap` use frames before `C + 34`, and `wall_turn` uses frames after its stand on the wall. `stand_late`, `land_end_of`, `floor_at_of` and `no_stand_before_land` use `stand_off_of` before `C + 34`.
8. The old field asked every frame up to `C + 50`. A frame from `C + 34` to `C + 50` with no earlier frame in the state 0 is used by no theorem, so it is not asked any more.

`stand_first` uses the fields `stand_fast`, `stand_P`, `clean`, and those that `far_inD` and `t0_far` use. It does not use `stand_wall`, `fall_long`, `fall_any`, `stand_late`, `land_at_of` or `floor_at_of`.

The ROM checks are in the private `Proof/RoomJoin.lean` (`room_stand_w`: the check of `hstep` for the three facings, `wallYCheck`, `standP + 256 < 4096`, the floor's height below 256) and `Proof/RoomWall.lean` (`room_wall`, `room_wall_after`, `room_wall_apart`, which the private route now passes to `Route.Run.inRoom`).

## Measured

`room-stand-first FM2 300`: the TAS's own frames in the room, and 2100 runs of own random inputs of 7 kinds, 60 frames each, from the TAS's first control in the room.

- 126,060 frames. 49 stand away from the floor before frame 51, all at frames 18 to 30: 14, 5, 14 and 16 runs of the kinds 1, 4, 5, 6. The TAS stands away from the floor first at frame 52, on the block.
- All 49 are first stands of the fall. Each starts in the air, meets `WallQ` at the end of its move, and ends with the speed 0.
- None of the stands before frame 51 comes after an earlier frame in the state 0, and none is from frame 34 to 50. So no frame of these runs is left to the field.
- On the same runs (`room-wall-real FM2 300 16 32 207`), the other 4 stands before frame 60 are the TAS's frames 52–54 on the block, and one run that lands on the block's left side at frame 51.

## What remains

The field `stand_wall` stays for a stand away from the floor before `C + 51` after an earlier frame that ends in the state 0 (on the floor or not). None is seen on real runs. `wall_turn` uses these frames (through `st_ne`): the frames after its stand on the wall, up to `C + 49`.

- From `C + 34` on, the fields `stand_fast` and `stand_P` do not hold, so nothing gives the speed or the position there. A stand on the block's left side comes at `C + 51` on one measured run, so the frames there are not far from a real stand.
- A second stand before `C + 34`. It is `gapF = 8` frames or more after the first (`stand_gap`), and the first is at `C + 15` or later (`stand_late`). Its frame starts in a state of `anyCheck`, but the vertical page is followed only through the first fall: after a jump, `InRoom.high` gives the vertical page at the frame's end only when he does not rise.

**Files.** `Theorems/RoomJoin.lean` (`WallQ`, `wallYCheck`, `negCheckJ`, `negJ_of_check`, `WallFacts`, `Checks.standW`, `InRoom.wall`, `high_upto`, `q_le_end`, `page_x_of`, `stand_first`, `stand_off_of`, `RoomCore.stand_off`; `RoomFields.stand_wall` narrowed), `Theorems/Route.lean` (`Run.roomWall`; `Run.inRoom` takes the checks of `RoomWall`), `Theorems/RoomWall.lean` (`speeds_of`). Private `Proof/RoomJoin.lean` (`room_stand_w`). Program `room-stand-first`.
