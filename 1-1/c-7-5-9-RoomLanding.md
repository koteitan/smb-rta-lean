[← Back](README.md) | [English](c-7-5-9-RoomLanding.md) | [Japanese](c-7-5-9-RoomLanding-ja.md)

# The prelanding state and the foot-call connection

This is a partial result. Under `NoWall`, `RoomRun.no_stand_before_land` excludes standing before the landing frame. `before_land_mem` places the last state in the existing fall layer. `before_land_step` gives the two alternatives for the final step: the vertical move or its landing. They use `stand_wall` and existing fall results, but never `land_at` or `floor_at_of`. The latter explicitly uses `land_at`, so it cannot prove that missing field.

`RoomCollision.readAddress_from_coords` and `returned_map_from_coords` express the cell and returned map byte using movement-end coordinates when they agree with the actual call entry. They do not prove that agreement and add no Run field.

The landing frame was measured on 13 runs: the TAS, ten random input runs and two fixed input runs. Each made two foot calls, for 26 calls in total. Position and vertical coordinate changed zero times from the scroll-handler entry; all 26 returns matched the corresponding floor map byte. All 13 runs ended standing. The indices select the ROM's left-foot and following right-foot offsets. These samples are not a proof for every `NoWall` run.

A small 500-instruction prefix check from the scroll handler to the foot handler failed at a return with 911 known bytes. Adding collision-disable, crouching, swimming and vertical-page bytes gave 915 known bytes and reached the overlapping head/feet wrapper's `BIT`, which the FrameWalk instruction table does not support. `bit_abs_ram` proves that the real CPU instruction keeps RAM; connecting it to the instruction model and reaching the call remain. No larger search was started.

The movement-end result of `FrameModel` and uniqueness from `SubsOnce` do not establish later call reachability, coordinate preservation or index choice. Those facts must identify the floor cell before applying `Run.roomCollisionMap`; the caller's tile branch and landing-state stores must then be followed. `land_at` remains. No field was removed or added.

**File:** `Theorems/RoomLanding.lean`.
