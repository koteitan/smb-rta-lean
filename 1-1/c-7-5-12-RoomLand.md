[← Back](README.md) | [English](c-7-5-12-RoomLand.md) | [Japanese](c-7-5-12-RoomLand-ja.md)

# The landing frame of the first fall

In the first fall after he enters the room, he stands on the floor at frame `C + 34`. This page proves it from the bytes at the end of the move of that frame (`PlayerSubs`, here Q). The field `land_at` is gone. The field `landQ` took its place with two bytes at Q; item 1-1-c-7-5-13 ([The collision-disable flag and the vertical page in the first fall](c-7-5-13-LandBytes.md)) proves them, and `landQ` is gone too.

## Statements

```
LandQ(q)   :=  yhigh(q) = 1  ∧  page(q) = 0  ∧  x(q) < 248
landQ_pos  :  at each PlayerSubs instruction j of frame C + 34 after the player's routine:  page(trace j) = 0  ∧  x(trace j) < 248   (theorem)
land_at_of :  NoWall  →  st(vs(C + 34)) = 0                                                                                       (theorem; the old field land_at)
```

`yhigh` is the vertical page. The player's collision routine looks at it first, and before it at the flag that turns off the collision checks; since item 1-1-c-7-5-13 that flag is a byte that the room's walk knows (`RoomLand.controlKeys`), so `LandQ` does not ask it.

## How it is proved

1. `landCheck` (a ROM check): from every state of the first fall at frame 33, `vstepR` with A or without it is at the height 180 px, and the vertical speed is not negative.
2. `RoomFall.land_frame`: a frame in the air comes to Q, and there its vertical bytes are those of `vstepR`. If some instruction of the frame after Q has the state 0, the vertical bytes at the frame's end are the landing ones. `after_QH` is `after_QC` with a history: when he does not land, every instruction of the frame from Q on has the four landing bytes of Q. `landed_of_write` uses it.
3. `RoomLand.stand_at`: if Q meets `LandQ`, has the height 180 and a speed that is not negative, then at the side check (`DoPlayerSideCheck`) the state is 0 and the height 176. A cut at Q and a walk of the instructions check it.
   - The cut copies 12 bytes from Q: the collision-disable flag, the vertical page, the routine, the three coordinates, the five screen bytes and the jump spring. It also takes from the map the head cell and both foot cells of the three adder offsets. It does not copy the size or the crouching flag; the walk follows both of their branches.
   - The routine, the screen bytes, the jump spring and (since 1-1-c-7-5-13) the collision-disable flag come from the room's walk table (`controls_at_subs`). The cells come from `Solid` at Q.
   - There are two ROM checks. The first is the walk for the 248 horizontal coordinates 0–247 of a reference machine (`family`). The reference machine is the first `PlayerSubs` of the room's map with no input, with the height set to 180. The second is that every cell lies in the buffers and is not a coin (`cellsOK`).
4. `RoomRun.landQ_pos`: at Q the page is 0 and x is below 248. The frame ends at most 34 frames of the top speed right of the start's right end (`P_upto`, `move_top`), and Q's position is that of the frame's end or 1 px from it (`CleanR.after`, `FrameModel.Collide`). The ROM check `landP` puts this left of 248 px.
5. `Route.Run.roomLand` joins 2 and 3; it is `InRoom.land`. `RoomRun.land_at_of` follows from 1, `landQ_pos`, the vertical page (`RoomRun.high_fall`, `InRoom.high`; 1-1-c-7-5-13) and `InRoom.land`. `floor_at_of` now uses it.

## Measured

- The TAS and 300 own random inputs: at Q of the landing frame the flag was always 0, the vertical page 1, the page 0, the height 180 and the speed 4. x was 13–46. Every frame ended standing at the height 176.
- At the TAS's Q, with x set to each of 256 values and the size and the crouching flag to each of 2 values, the machine always ended standing at 176.
- The cut's walk fails for x from 248 to 255; the check leaves these out.

## What remains

Nothing of the landing frame: the two bytes that `landQ` asked are proved in item 1-1-c-7-5-13.

**Files.** `Theorems/RoomLand.lean` (`keys`, `cells`, `cut`, `check`, `family`, `cellsOK`, `at_cut`, `cut_eq`, `check_of_family`, `cells_of_family`, `land`, `controlCheck`, `controls_at_subs`, `refQ`, `refCheck`, `Checks`, `stand_at`), `Theorems/RoomFall.lean` (`after_QH`, `landed_of_write`, `at_QG`, `land_frame`), `Theorems/RoomJoin.lean` (`LandQ`, `landY`, `landCheck`, `Checks.landP`, `InRoom.land`, `RoomRun.P_upto`, `RoomRun.landQ_pos`, `RoomRun.land_at_of`), `Theorems/Route.lean` (`Run.roomLand`, `Run.inRoom`). Private `Proof/RoomLand.lean` (`room_land`), `Proof/RoomJoin.lean` (`room_checks.land`).
