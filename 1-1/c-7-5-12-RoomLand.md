[← Back](README.md) | [English](c-7-5-12-RoomLand.md) | [Japanese](c-7-5-12-RoomLand-ja.md)

# The landing frame of the first fall

In the first fall after he enters the room, he stands on the floor at frame `C + 34`. This page proves it from four bytes at the end of the move of that frame (`PlayerSubs`, here Q). The field `land_at` is gone; the field `landQ`, the four conditions, takes its place.

## Statements

```
LandQ(q)   :=  disable(q) = 0  ∧  yhigh(q) = 1  ∧  page(q) = 0  ∧  x(q) < 248
landQ      :  NoWall  →  at each PlayerSubs instruction j of frame C + 34:  LandQ(trace j)        (new field)
land_at_of :  NoWall  →  st(vs(C + 34)) = 0                                                      (theorem; the old field land_at)
```

`disable` is the flag that turns off the collision checks, and `yhigh` is the vertical page. The player's collision routine looks at both first.

## How it is proved

1. `landCheck` (a ROM check): from every state of the first fall at frame 33, `vstepR` with A or without it is at the height 180 px, and the vertical speed is not negative.
2. `RoomFall.land_frame`: a frame in the air comes to Q, and there its vertical bytes are those of `vstepR`. If some instruction of the frame after Q has the state 0, the vertical bytes at the frame's end are the landing ones. `after_QH` is `after_QC` with a history: when he does not land, every instruction of the frame from Q on has the four landing bytes of Q. `landed_of_write` uses it.
3. `RoomLand.stand_at`: if Q meets `LandQ`, has the height 180 and a speed that is not negative, then at the side check (`DoPlayerSideCheck`) the state is 0 and the height 176. A cut at Q and a walk of the instructions check it.
   - The cut copies 12 bytes from Q: the collision-disable flag, the vertical page, the routine, the three coordinates, the five screen bytes and the jump spring. It also takes from the map the head cell and both foot cells of the three adder offsets. It does not copy the size or the crouching flag; the walk follows both of their branches.
   - The routine, the screen bytes and the jump spring come from the room's walk table (`controls_at_subs`). The cells come from `Solid` at Q.
   - There are two ROM checks. The first is the walk for the 248 horizontal coordinates 0–247 of a reference machine (`family`). The reference machine is the first `PlayerSubs` of the room's map with no input, with the height set to 180. The second is that every cell lies in the buffers and is not a coin (`cellsOK`).
4. `Route.Run.roomLand` joins 2 and 3; it is `InRoom.land`. `RoomRun.land_at_of` follows from 1, `landQ` and `InRoom.land`. `floor_at_of` now uses it.

## Measured

- The TAS and 300 own random inputs: at Q of the landing frame the flag was always 0, the vertical page 1, the page 0, the height 180 and the speed 4. x was 13–46. Every frame ended standing at the height 176.
- At the TAS's Q, with x set to each of 256 values and the size and the crouching flag to each of 2 values, the machine always ended standing at 176.
- The cut's walk fails for x from 248 to 255; the check leaves these out.

## What remains

The four conditions of `landQ` are assumptions: at Q the flag is 0, the vertical page is 1, the page is 0 and x is below 248. Each must be shown to stay through the frames of the room's first fall.

**Files.** `Theorems/RoomLand.lean` (`keys`, `cells`, `cut`, `check`, `family`, `cellsOK`, `at_cut`, `cut_eq`, `check_of_family`, `cells_of_family`, `land`, `controlCheck`, `controls_at_subs`, `refQ`, `refCheck`, `Checks`, `stand_at`), `Theorems/RoomFall.lean` (`after_QH`, `landed_of_write`, `at_QG`, `land_frame`), `Theorems/RoomJoin.lean` (`LandQ`, `landY`, `disableI`, `landCheck`, `InRoom.land`, `RoomRun.landQ`, `RoomRun.land_at_of`), `Theorems/Route.lean` (`Run.roomLand`, `Run.inRoom`). Private `Proof/RoomLand.lean` (`room_land`), `Proof/RoomJoin.lean` (`room_checks.land`).
