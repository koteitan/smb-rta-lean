[← Back](README.md) | [English](c-7-5-15-RoomWall.md) | [Japanese](c-7-5-15-RoomWall-ja.md)

# A stand away from the floor in the room

The field `stand_wall` of [Joining the bonus room](c-5-RoomJoin.md) said (before item 1-1-c-7-5-16): before `C + 51`, he stands away from the floor only at the end of a frame that does not follow `hstep`. On real frames such a stand is a landing on the room's left wall column: on the same frame the side check finds the wall, and `ImpedePlayerMove` sets the speed to 0 and pushes him 1 px right. This page proves this part of one frame on the machine, from the end of the move to the frame's end. [The first stand of the fall](c-7-5-16-FirstStand.md) joins it to the route.

## Statements

`Q` is the end of the frame's move (the first `PlayerSubs` of the frame). At `Q`: `x` the horizontal coordinate, `pg` the page, `y` the height, `st` the state, `vy` the vertical speed, `v` the speed, `yhigh` the vertical page. `G` is the instruction of `PlayerSubs` after its call of the collision routine. `yF` is the floor's height (176 px). `speeds` is the speed 0 and the negative speeds from −127 to −1.

```
At Q:  yhigh = 1,  pg = 0,  x < 16,  32 ≤ y < 207,  st ≤ 2,  vy ≥ 0,  v ∈ speeds                                  (the conditions)

wall_at    :  the conditions  →  ∃ k ≤ 3200,  stepN k Q  is at G, in the same frame, with the stack of Q, and
              st ≠ 0  ∨  (st = 0 ∧ y = yF)  ∨  v = 0
after_G    :  the frame comes to G and ends in the player's routine  →  v, x, pg, st, y at the frame's end are those at G
wall_frame :  the conditions, and the frame ends in the player's routine  →  at the frame's end
              st ≠ 0  ∨  (st = 0 ∧ y = yF)  ∨  v = 0
neg_of_check : inD(s),  V(s) ≤ −standV  (standV = 256 · 14: the speed −14 or less, 0.875 px per frame)  →  ∀ i ∈ inputs,  sbyte(hstep(s, i).v) < 0  ∧  hstep(s, i).v ∈ speeds
not_follow_of : n + 1 < C + 34,  st(vs(n + 1)) = 0,  frame n + 1 comes to some PlayerSubs j ≥ arr(n)  (hQ),
                (∀ j ≥ arr(n) at PlayerSubs:  v(trace j) ∈ speeds  →  v at the frame's end = 0)  (hq)   →   ¬Follow(n)
```

`not_follow_of` uses the fields `stand_fast` and `clean` and `neg_of_check` (with `w = standV`), not `stand_wall`. `hq` is what `wall_frame` gives on the frame when the other conditions of `wall_at` hold at its end of the move.

So a frame of the room whose end of the move meets the conditions does not end standing away from the floor with a speed other than 0.

## How it is proved

1. The first walk (`check1`) starts at a cut at `Q`. The cut copies 13 bytes from `Q`: the bytes of `RoomLand.keys` (the collision-disable flag, the vertical page, the routine, the three coordinates, the five screen bytes, the jump spring) and the state. It takes from the map the head, foot and side cells of the three adder offsets (21 cells). It does not copy the speed, the size, the crouching flag, the swimming flag or the facing: the walk follows both branches of each.
2. The first walk stops at `G`, or at `ImpedePlayerMove` when the state is known to be 0 and the height is not the floor's. At `G` it asks `endOK`: the state is not 0, or the state is 0 at the floor's height, or the speed is known to be 0. At `ImpedePlayerMove` it asks the side byte 2 (the left side), the state 0, the two return addresses on the stack, and the speed not written since `Q` or known to be 0. (At the screen's left edge `ScrollHandler` can set the speed to 0 before the collision routine.)
3. The second walk (`check2`) starts at `ImpedePlayerMove` with the speed copied, for each of the 128 speeds of `speeds`, and comes back to `G` with the speed 0.
4. `wall_end` joins the two walks. `wall_at` takes the bytes of the cut from the actual machine: the routine, the screen bytes, the jump spring and the collision-disable flag from the room's walk (`RoomLand.controls_at_subs`), the cells from `Solid` at `Q`, and the rest from the conditions. The family check covers x 0–15, y 32–206 and the states 0, 1, 2 (8,400 walks). A second check says that every cell lies in the block buffers and is not a coin.
5. `after_G` is a walk of the room's whole frame (`checkW`, as `RoomVert.after_Q`). It marks the state at `G`. A step after `G` that may write the speed, the position, the state or the height drops the mark, and such a state must end the frame out of the player's routine.
6. `wall_frame` is `wall_at` and `after_G` on the same frame.
7. `neg_of_check` is a check of `hstep` (`negCheck`) on every state of the domain with `V ≤ −standV` (39,942 states) and every normalized input (38), covered as `Potential.check_of` covers the potential's check.
8. `not_follow_of`: under `Follow`, `v(n + 1)` is the speed of `hstep(hs n, inp(n + 1))`. `stand_fast` gives `V(hs n) ≤ −standV`, and `far_inD` gives `inD(hs n)`, so `neg_of_check` makes that speed negative and one of `speeds`. The field `clean` (`CleanW.after` or `ReadW.collide`) makes the speed at the frame's end the speed at `j` or 0. It is not 0, so it is the speed at `j`, which is in `speeds`, and `hq` gives 0: a contradiction.

The ROM checks are in the private `Proof/RoomWall.lean` (`room_wall`, `room_wall_after`, `room_wall_apart`, `room_wall_neg`). The file builds in about 75 s natively. Most of it is the first walk's family: 97 million abstract steps, because the walk splits on the bytes it does not know. The check of `hstep` takes about 15 s.

## Measured

`room-wall-real FM2 100 16 32 207`: the TAS's own frames in the room, and 700 runs of own random inputs of 7 kinds, 60 frames each, from the TAS's first control in the room.

- 42,060 frames. At `Q` the conditions hold on 13,186 of them. On none of them is `endOK` false at `G`.
- 15 stands away from the floor. 12 are before frame 51. All 12 meet the conditions at `Q` (x 12, y 112, 116, 129 or 163, the state 2, the speed −17 to −20), and all 12 have the speed 0 at `G` and at the frame's end. The other 3 are the TAS's frames 52–54, standing on the room's block (x 61–64).
- On every frame, the speed and the position at the frame's end are those at `G`.
- With 300 runs of each kind (`room-wall-real FM2 300 16 32 207`): 126,060 frames, the conditions on 39,908, `endOK` false on none. 53 stands away from the floor: 49 before frame 51, all meeting the conditions at `Q` (x 12, y 112 to 163) and ending with the speed 0. Of the other 4, three are the TAS's frames 52–54 on the block, and one is a run that lands on the block's left side at frame 51 itself (x 52, y 160, the speed +20 at `Q`, pushed 1 px left, the speed 0 at the end). So a stand on the block can come at frame 51, just after the frames that `stand_wall` speaks of.

## What remains

[The first stand of the fall](c-7-5-16-FirstStand.md) uses `wall_frame` on the real machines (`InRoom.wall`, `Route.Run.roomWall`) and proves the conditions at `Q` for the first stand of the fall (`RoomRun.stand_first`). The field `stand_wall` now asks only for a stand after an earlier frame that ends in the state 0. Still not proved here:

- `stand_fast` holds only before `C + 34`. For the frames from `C + 34` to `C + 50` nothing gives the speed.
- `wall_frame` asks a speed at `Q` that is 0 or negative. With a positive speed a landing on the wall column keeps the speed (`ImpedePlayerMove` keeps a speed toward the right). Before `C + 34` under `Follow` the speed is negative (above). No real frame lands on the wall column with a positive speed: it needs a frame that ends inside the wall column.

**Files.** `Theorems/RoomWall.lean` (`retBG`, `cellsW`, `keysW`, `cutW`, `endOK`, `impCut0`, `impCut`, `stop1`, `goal1`, `check1`, `check2`, `speeds`, `family1`, `family2`, `cellsOKW`, `endOK_spec`, `wall_end`, `cutW_eq`, `at_cutW`, `cells_of_familyW`, `refCheckW`, `Checks`, `wall_at`, `hW`, `phW`, `finW`, `apartW`, `after_G`, `checkW`, `wall_frame`, `negCheck`, `neg_of_check`, `not_follow_of`). Private `Proof/RoomWall.lean` (`room_wall`, `room_wall_after`, `room_wall_apart`, `room_wall_neg`). Programs `room-wall-family`, `room-wall-real`, `room-wall-check`.
