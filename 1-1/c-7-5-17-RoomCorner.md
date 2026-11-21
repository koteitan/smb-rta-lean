[← Back](README.md) | [English](c-7-5-17-RoomCorner.md) | [Japanese](c-7-5-17-RoomCorner-ja.md)

# The block's left side, on the floor

The field `low_at` of [Joining the bonus room](c-5-RoomJoin.md) said: a frame from `C + 37` to `C + 43` with the feet at or below the block's top is `LowAt`. He is not far past the corner, and he is stopped, or left of the corner, or moving left. This page proves it, with no wall hit, for every frame that ends on the floor: the collision routine finds the block's left side and pushes him back. The field now asks, with no wall hit, only the frames that end off the floor at or past the corner, and only the first part of `LowAt`: he is not far past the corner. The whole `LowAt` is false on measured frames of a big player (below).

## Statements

`P(n)`, `hs(n)`, `vs(n)` are the position (in 1/256 px), the horizontal state and the vertical state at the end of frame `n`. `c_P` is the corner (the position at which his right side check is in the block's left column, 51 px), `S_low` the slack of a low frame (415/256 px), `y_c` the corner's height (136 px), `176` the floor's height. `OnFloor(s)`: the state 0 and the height 176. `NoWall`: every frame before `C + 37` follows `hstep`.

```
LowAt(n)  :=  P(n) ≤ c_P + S_low  ∧  (Stop(n) ∨ P(n) < c_P ∨ v(n) < 0)

low_at (field, narrowed):
  NoWall,  C + 37 ≤ n ≤ C + 43,  n ≤ t₀,  y_c ≤ y(vs(n)),  ¬OnFloor(vs(n)),  c_P ≤ P(n)   →   P(n) ≤ c_P + S_low

low_floor_of (proved; RoomCore.low_floor):
  NoWall,  C + 37 ≤ n + 1 ≤ C + 43,  n < t₀,  (∀ j, C + 34 ≤ j ≤ n + 1 → OnFloor(vs(j))),  LowAt(n)   →   LowAt(n + 1)

low_floor_at (proved):
  NoWall,  C + 36 ≤ n ≤ C + 43,  n ≤ t₀,  (∀ j, C + 34 ≤ j ≤ n → OnFloor(vs(j)))   →   LowAt(n)
```

At the end of the move `Q` of a frame (its `PlayerSubs`) let `x`, `pg`, `v` be the coordinate, the page and the speed byte, and `F` the frame's end.

```
CornerEnd(Q, F)  :=  y(F) < y_c  ∨  (pg(F) = 0  ∧  (v < 128  →  v(F) = 0 ∧ x(F) = x − 1)  ∧  (v ≥ 128  →  v(F) = v ∧ x(F) = x))

InRoom.corner (proved on the real machines: Route.Run.roomCorner):
  C ≤ n,  n + 1 < E,  frame n + 1 starts standing with no jump in its input, with the vertical page 1   →
    ∃ Q,  Q is the only PlayerSubs of the frame  ∧
      (it starts at the height 176 with the vertical speed not negative,  pg(Q) = 0,  51 ≤ x(Q) ≤ 55   →   CornerEnd(Q, F))
```

So at the block's left side a speed from 0 to 127 becomes 0 and he is pushed back one pixel; a negative speed is kept, and so is the coordinate.

## The walks (`Theorems/RoomCorner.lean`)

1. The first walk (`check1C`) starts at `Q` with the bytes of `RoomLand.keys`, the player's state, the sign bit of the vertical speed, and the head, foot and side cells of the three adder offsets from the reference map (`RoomWall.cellsW`). The horizontal speed is not known. It is walked for `x` from 51 to 55 and two kinds of `Q`: the state 0 at the height 176, not moving up; and the state 1, moving up, with the height from 152 to 176 (130 walks). It stops at the instruction after the call of the collision routine (`retBG`), where it asks the height above `y_c`, or at `ImpedePlayerMove`, where it asks the side byte 1 (the block on his right), the two return addresses of the side check on the stack, the coordinate and the page of `Q`, and the speed not written.
2. The second walk (`check2C`) starts at `ImpedePlayerMove` for every coordinate and every speed byte (1280 walks) and goes back to `retBG`, where it asks `CornerEnd`'s second part.
3. `corner_at` joins them; `corner_frame` adds `RoomWall`'s walk of the room's whole frame from `retBG` (`RoomWall.after_G`: no step writes the speed, the coordinate, the page, the state or the height, or the frame leaves the player's routine).

The checks take about 1.6 s natively (`room-corner-family 152`). The private proof is `room_corner` in `Proof/RoomCorner.lean`.

## How `low_floor_of` is proved

1. The frame starts on the floor with the vertical page 1 and the vertical speed 0 (`floor_run`), with no jump in its input (a takeoff ends in the air: `vjump_of`, `offCheck`, `arc_facts`). So `InRoom.corner` gives its one end of the move `Q`.
2. If the frame follows the model (`clean`: `CleanW`), nothing writes the horizontal bytes after `Q`, so `P(n + 1) = P(Q)`, and `Follow(n)` gives `P(n + 1) = P(n) + 16·v(n + 1)`. If `P(n + 1) < c_P`, `LowAt(n + 1)`. If not, `P(n + 1) ≤ P(n) + 16·v_top ≤ c_P + S_low + 640 < c_P + 1280`, so `pg(Q) = 0` and `x(Q)` is from 51 to 55 (`corner_window`). He ends on the floor, so `CornerEnd` says he was pushed back (impossible: the coordinate is kept) or he moves left: `v(n + 1) < 0` and `P(n + 1) < P(n) ≤ c_P + S_low`.
3. If not, the frame is `Stop(n + 1)` (`clean`), and `FrameModel.frame_readQ` (`frame_readR` that also gives the instruction of the end of the move) makes it a `TopSpeed.Frame` whose `P₂ = P(n) + 16·v₂` is the position at a `PlayerSubs` of the frame, which is `Q` (only one). With `P(Q) < c_P`, `Collide` gives `P(n + 1) ≤ P(Q) + 256 < c_P + S_low`. With `P(Q) ≥ c_P`, `CornerEnd` gives: pushed back, `P(n + 1) = P(n) + 16·v₂ − 256`; or moving left, `P(n + 1) = P(Q) < P(n)`. When pushed back: from `P(n) < c_P`, `v₂ ≤ v_top` gives `P(n + 1) < c_P + 16·v_top − 256 ≤ c_P + S_low`; from `P(n) ≥ c_P`, `LowAt(n)` says that he was stopped or moved left, and one frame gains less than 17 of speed (`friction_gain`, `CornerFacts.small`), so `P(n + 1) ≤ P(n)`.
4. `low_floors` starts at `C + 36`, left of the corner (`corner_late`), and goes frame by frame. `floor_low` uses it for the floor frames up to the takeoff, and `low_by` for the frames on the floor since the end of the fall. On the frames of a jump `low_by` still uses the field (`arc_facts`: off the floor), and needs only `P(n) ≤ c_P + S_low`, which holds left of the corner.

`low_floor_of` uses the fields `stand_wall`, `stand_fast`, `stand_P` (through `floor_run` and `land_end_of`), `clean`, `farNear`, `read_hs`, `read_P`, `read_vs`, `read_in`, `read_PE`, `read_stop`, and the `InRoom` fields `corner`, `floor`, `jump`, `land`, `wall`, `high`, `air`, `pair`, `keep`, `keepH`, `cut`, `arrive`, `reach`, `time`, `before`, `many`, `le`, `mouthE`, `vstart`. It does not use `low_at`, `RoomCore.low_floor` or `toCore` (checked on the constants it uses). `Route.Run.roomCorner` uses none of them either.

## Measured

`room-corner-real FM2 300 152`: the TAS's own frames in the room, and 2100 runs of own random inputs of 7 kinds, from the TAS's first control in the room.

- 14,707 frames from `C + 37` to `C + 43` at or before `t₀`; 14,626 with the feet low: 3,141 from the floor to the floor, 1,078 takeoffs, 10,407 in the air.
- 366 come to the end of the move at or past the corner. All have the page 0, a coordinate from 51 to 55 and the vertical page 1. 351 are of the walk's two kinds, and all of them end `CornerEnd`: 350 pushed back, 1 moving left. The other 15 move up with the height 149 or 151, below the walk's heights, and end off the floor. With the heights from 136 (`room-corner-real` before the bound 152) all 366 ended `CornerEnd`.
- On every one of these frames `P(Q) = P(start) + 16·v(Q)`, and every frame comes to `PlayerSubs` once.
- 68 frames end at or past the corner: 14 end on the floor (proved here), 54 end off the floor (left to the field). `LowAt` holds on all 14,626, and none is more than `S_low` past the corner.

**A big player (`room-corner-real FM2 300 152 1`: the same runs, with the size byte set to big at first control).** `LowAt` is false on 8 frames (frames 42 and 43 of 8 runs of the kind 2): he is moving up with the height 151 at the corner, moving right (speed 5 to 21), and is not pushed back on that frame; the side check runs, the head's coin code does not. None of them is more than 224/256 px past the corner, and on all 14,626 frames none is more than `S_low` past it. So the field asks only `P(n) ≤ c_P + S_low`. With the size not known, the first walk fails at the heights 136 to 151 (`room-corner-family 136`: 80 of 210 walks): a cell of these states holds a coin in the reference map, and the walk comes to an instruction that it cannot follow. `Approach.low` (inside the field `way`) asks `LowAt` on the low frames of the last takeoff; it is false on 2 measured runs of a big player ([The vertical page through a jump](c-7-5-18-RoomHigh.md)).

## What remains

- The field `low_at` for a frame that ends off the floor at or past the corner: a takeoff, or a frame of a jump. Narrowed further in [The vertical page through a jump](c-7-5-18-RoomHigh.md): the vertical page is followed through the takeoff and the rising frames, and the frames of a jump that end at 152 or below are proved.
- The first walk passes only from the height 152 up. Higher, with the size not known, a cell holds a coin and the walk fails; on measured frames a big player is not pushed back there (above).

**Files.** `Theorems/RoomCorner.lean` (`cutC`, `check1C`, `check2C`, `Checks`, `corner_at`, `corner_frame`), `Theorems/RoomJoin.lean` (`cornerX`, `xsC`, `CornerEnd`, `FrameModel.frame_readQ`, `CornerFacts`, `Checks.corner`, `InRoom.corner`, `low_floor_of`, `RoomCore.low_floor`, `low_floors`, `low_floor_at`; `RoomFields.low_at` narrowed), `Theorems/Route.lean` (`Run.roomCorner`; `Run.inRoom` takes the checks of `RoomCorner`). Private `Proof/RoomCorner.lean` (`room_corner`), `Proof/RoomJoin.lean` (`room_corner_facts`). Programs `room-corner-family`, `room-corner-real`.

**Reproduce.**
```
.lake/build/bin/smbrta room-corner-family 152             # the walks (about 1.6 s)
.lake/build/bin/smbrta room-corner-real FM2 300 152       # the frames C + 37 .. C + 43 on real runs (about 40 s)
```
