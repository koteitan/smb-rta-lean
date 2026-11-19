[← Back](README.md) | [English](c-7-5-9-RoomLanding.md) | [Japanese](c-7-5-9-RoomLanding-ja.md)

# The prelanding state and the foot-call connection

This is a partial result. Under `NoWall`, `RoomRun.no_stand_before_land` excludes standing before the landing frame. `before_land_mem` places the last state in the existing fall layer. `before_land_step` gives the two alternatives for the final step: the vertical move or its landing. They use `stand_wall` and existing fall results, but never `land_at` or `floor_at_of`. The latter explicitly uses `land_at`, so it cannot prove that missing field.

`RoomCollision.readAddress_from_coords` and `returned_map_from_coords` express the cell and returned map byte using movement-end coordinates when they agree with the actual call entry. They do not prove that agreement and add no Run field.

The landing frame was measured on 13 runs: the TAS, ten random input runs and two fixed input runs. Each made two foot calls, for 26 calls in total. Position and vertical coordinate changed zero times from the scroll-handler entry; all 26 returns matched the corresponding floor map byte. All 13 runs ended standing. The indices select the ROM's left-foot and following right-foot offsets. These samples are not a proof for every `NoWall` run.

`FrameWalk` now supports `BIT`. [RoomFootPrefix](c-7-5-10-RoomFootPrefix.md) proves coordinate and index agreement at a selected actual foot call under a local bounded-prefix check, and joins it to `Run.roomCollisionMap`. The check passed for both feet on all 13 measured runs. The earlier foot-handler cut used the wrong stack level: its stack pointer is two below the scroll-handler entry. Deriving this check for every landing frame and following the caller's landing branch remain open.

The movement-end result of `FrameModel` and uniqueness from `SubsOnce` do not establish later call reachability, coordinate preservation or index choice. Those facts must identify the floor cell before applying `Run.roomCollisionMap`; the caller's tile branch and landing-state stores must then be followed. `land_at` remains. No field was removed or added.

**File:** `Theorems/RoomLanding.lean`.
