[← Back](README.md) | [English](c-7-5-18-RoomHigh.md) | [Japanese](c-7-5-18-RoomHigh-ja.md)

# The vertical page through a jump, and the block's left side in a jump

The field `low_at` of [Joining the bonus room](c-5-RoomJoin.md) asked, with no wall hit, every frame from `C + 37` to `C + 43` that ends off the floor at or past the corner with the feet low: such a frame is not more than `S_low` past the corner. These frames are the takeoff and the first frames of a jump from the floor. The walk of the block's left side ([The block's left side, on the floor](c-7-5-17-RoomCorner.md)) needs the vertical page (`Player_Y_HighPos`) at the end of the move, and the vertical page was not followed after a rising frame. This page follows it through the takeoff and the rising frames, and proves the frames of a jump that end at the height 152 (`cornerY + 16`) or below. The field now asks only the frames that end above 152, from 136 to 151 px.

**False, measured (a big player).** `Approach.low` (inside the field `way`) is false on 2 measured runs of a big player (below). It is not narrowed: its user `landed_short` needs all of `LowAt` there. Round 25 fixed it: [A big player at the block's corner](c-7-14-1-BigApproach.md).

## Statements

`P(n)`, `vs(n)` are the position (in 1/256 px) and the vertical state at the end of frame `n`; `y`, `st` the height and the player's state. `c_P` is the corner (51 px), `S_low = 415/256` px, `y_c = 136` the corner's height, `176` the floor's height. `OnFloor(s)`: the state 0 and the height 176. `NoWall`: every frame before `C + 37` follows `hstep`. `OnArc(T, j)`: frame `j` is on the jump that takes off on frame `T + 1` (its vertical state is a state of `Jump.arcSucc` from a takeoff of `Jump.arcStart`). `Q` is the end of the move of a frame (its `PlayerSubs`), `F` its end, `hp` the vertical page.

```
low_at (field, narrowed):
  NoWall,  C + 37 ≤ n ≤ C + 43,  n ≤ t₀,  y_c ≤ y(vs(n)),  ¬OnFloor(vs(n)),  c_P ≤ P(n),  y(vs(n)) < y_c + 16   →   P(n) ≤ c_P + S_low
  (before: without the last premise)

arc_down (proved; the check arcDown):
  on a jump from the floor up to its last low frame,  T < j ≤ n   →   y(vs(n)) ≤ y(vs(j))

low_jump_of (proved; RoomCore.low_jump):
  NoWall,  C + 34 ≤ T < n ≤ C + 43,  n ≤ t₀,  (∀ j, C + 34 ≤ j ≤ T → OnFloor(vs(j))),
  (∀ j, T < j ≤ n → OnArc(T, j)),  (∀ j, T < j ≤ n → y_c + 16 ≤ y(vs(j))),  LowAt(T)   →   LowAt(n)
```

The two new fields of `InRoom`, proved on the real machines (`Route.Run.roomHighJ`, `Route.Run.roomHighA`):

```
InRoom.highJ (a takeoff):
  C ≤ n,  n + 1 < E,  frame n + 1 starts at the height 176 with hp = 1 and a jump in its input   →
    hp(F) = 1  ∧  ∃ Q, Q is the only PlayerSubs of the frame  ∧  (pg(Q) = 0,  51 ≤ x(Q) ≤ 55   →   CornerEnd(Q, F))

InRoom.highA (a frame in the air):
  C ≤ n,  n + 1 < E,  frame n + 1 starts in the air with hp = 1 on a state s of a jump's first 8 frames (VertAir.arcSet),
  vstep(s, A) is such a state and rising   →
    hp(F) = 1  ∧  ∃ Q, Q is the only PlayerSubs of the frame  ∧  (pg(Q) = 0,  51 ≤ x(Q) ≤ 55,  y_c + 16 ≤ y(vstep(s, A))   →   CornerEnd(Q, F))
```

`CornerEnd(Q, F)` is that of [The block's left side, on the floor](c-7-5-17-RoomCorner.md): above the corner's height at the end, or the page 0 and pushed back one pixel with the speed 0 (a speed from 0 to 127 at `Q`), or moving left as at `Q`.

## How the vertical page is followed

1. The takeoff frame (`RoomHigh.vert_jumpH`). The walk of two machines of `VertJump.vert_jump` (the real machine and the machine of `vstep`) follows the vertical page too, with the tag "the same on the two machines", as `OpenVert.vert_airH` does for a frame in the air. So at `Q` the page is that of the machine of `vstep` after the movement routine, from the standing state at the real height with A and the real stored speed. `RoomHigh.offCheck`: from the height 176 this page is 1 for every stored speed, and the height at `Q` is 171 or 172.
2. From `Q` to the frame's end (`RoomVert.after_QP`). The walk `walkB` of `RoomVert` from the scroll handler now keeps the vertical page with the vertical bytes (`vKeepH`): a step that may write one of them, while he is in the air and rising, must leave the player's routine. The walk passes as before (5.9 s natively); the page is out of the block buffers (`apartH`).
3. A frame in the air (`RoomHigh.air_roomH`). At `Q` the page is that of the machine of `vstep` (`RoomFall.high_room`); `RoomHigh.arcCheckH`: on the 1533 states of a jump's first 8 frames it is 1, the state is 1, and the height is at most 176. If he rises at `Q`, step 2 keeps the page and the vertical bytes to the end.
4. Between frames the page is kept (`InRoom.keepH`). So along a jump from the floor (the floor frames have the page 1: `floor_run`) every frame ends with the page 1 (`high_next`).

## How `low_jump_of` is proved

1. `low_step` is the frame step of `low_floor_of`, taken out: after a frame that is `LowAt`, a frame that ends at the corner's height or below, whose `Q` is its only `PlayerSubs`, and that ends `CornerEnd` when `Q` has the page 0 and a coordinate from 51 to 55, is `LowAt`. `low_floor_of` now uses it with `InRoom.corner`.
2. The takeoff frame `T + 1`: on the floor at `T` with the page 1 (`floor_run`), its input has a jump (else `stay_of` puts him on the floor, but `arc_facts` says he is in the air). `InRoom.highJ` gives `Q` and `CornerEnd`, and the page 1 at the end. `low_step` gives `LowAt(T + 1)`.
3. The frames in the air: `varc_at` (from `varc_of`) gives the arc's states at the frame's start and of `vstep`, rising, and that the frame ends on that `vstep`. `InRoom.highA` gives `Q` and `CornerEnd` (with the height of `vstep` at `y_c + 16` or below), and the page 1 at the end. `low_step` gives `LowAt`.
4. In `low_by` a frame of a jump at or past the corner is now split: if it ends above `y_c + 16`, the field; if not, `low_jump` from the takeoff (`v_chain2`: on the floor up to `T` and on the arc after it), with `LowAt(T)` from `low_floor_at` or, before `C + 37`, from `corner_late`. Every earlier frame of the jump ends at that height or below too: on the 1533 states of a jump's first frames `vstep` does not lower the height's byte (`arcDown`, checked natively with the other checks of `RoomJoin`), so along the jump it does not grow (`arc_down`).

The walk of the block's left side passes for the state 1 moving up only from the height 152 down ([The block's left side, on the floor](c-7-5-17-RoomCorner.md)): higher up, with the size not known, a cell holds a coin. On the states of a jump, the heights at the end of the move are 152 or more for the first 5 frames after the takeoff (`k ≤ 4`), and from `k = 5` some are higher (148 at `k = 5`, 136 at `k = 8`).

`low_jump_of` does not use `low_at`, `RoomCore.low_jump` or `toCore`; `Route.Run.roomHighJ` and `Route.Run.roomHighA` do not use `low_at` or `low_jump_of` (checked on the constants they use).

## Measured

`room-approach-check FM2 300 BIG`: the TAS's own frames in the room, and 2700 runs of own random inputs of 9 kinds from the TAS's first control in the room (kinds 8 and 9: one press of A on a frame from 28 to 47, held 1 to 24 frames, running or walking right), each up to the first frame past the block's right end (`t₀`) or 300 frames. `BIG = 1` sets the size byte to big at first control (an artificial state: no measured run enters the room big).

- The vertical page is 1 at `Q` and at the end of every one of the room frames (768,913 frames small, 764,149 big).
- The frames of the old `low_at` (no wall hit, `C + 37` to `C + 43`, feet low, off the floor, at or past the corner): small 50, big 103. Of them `low_jump` now covers 47 (small) and 48 (big), and `LowAt` holds on all of them; 3 (small) and 55 (big) are left to the field. None is more than `S_low` past the corner (largest 96/256 px small, 352/256 px big).
- **`Approach.low` is false for a big player.** In 2 runs (the kind 9) with no wall hit, no `Stop` from `C + 37` to `t₀` and a landing on the block before `t₀`, a low frame of the last takeoff is not `LowAt`: frame 45 (takeoff 35) and frame 53 (takeoff 43), 10 frames after the takeoff, at the height 138, in the state 1, moving right with the speed 23 or 24, 336/256 and 48/256 px past the corner, not stopped. `P ≤ c_P + S_low` holds on all measured low frames. For the small player `LowAt` holds on all of them. `landed_short` uses all of `LowAt` on these frames (`left_at`), so `low` is not narrowed to the position bound.

## What remains

- The field `low_at` for a frame that ends above 152 (from 136 to 151 px): the walk of the block's left side does not pass there with the size not known, and a big player is not pushed back there on measured frames. Since round 26 asked only after a frame at or past the corner ([A frame above 152 px after a frame left of the corner](c-7-5-19-BandStart.md)).
- `Approach.low`: false on measured runs of a big player; `landed_short` would need another argument for the frames of a big player at the corner (done in round 25: [A big player at the block's corner](c-7-14-1-BigApproach.md); its field `Approach.slowBig` is proved in round 26: [A big player's slow takeoff on C + 35](c-7-14-2-LandDist.md)).
- `stand_wall`: not touched.

**Files.** `Theorems/RoomHigh.lean` (new: `vTagsJH`, `goalVJH`, `caseOKJH`, `jumpHOK`, `vert_jumpH`, `jump_frameH`, `jump_roomH`, `air_roomH`, `offCheck`, `arcCheckH`, `Checks`, `off_spec`, `arc_specH`), `Theorems/RoomVert.lean` (`vKeepH`; `mayWriteV` over `vKeepH`; `apartH`, `keepVH_step`, `after_QP`), `Theorems/RoomJoin.lean` (`InRoom.highJ`, `InRoom.highA`, `RoomCore.low_jump`, `low_step`, `varc_at`, `high_next`, `low_jump_of`, `v_chain2`, `arcDown`, `Checks.down`, `arc_down`; `low_by` and the field `low_at`), `Theorems/Route.lean` (`mem_ysUp`, `Run.roomHighJ`, `Run.roomHighA`; `Run.inRoom` takes the checks of `RoomHigh`). Private `Proof/RoomHigh.lean` (`room_high`), and `down` in `room_checks` (`Proof/RoomJoin.lean`). Programs `room-high-probe`, `room-approach-check`.

**Reproduce.**
```
.lake/build/bin/smbrta room-high-probe                    # the checks of RoomHigh and RoomVert.checkB (about 6 s)
.lake/build/bin/smbrta room-approach-check FM2 300 0      # small; with 1 at the end, big
```
