[← Back](README.md) | [English](c-7-5-10-RoomFootPrefix.md) | [Japanese](c-7-5-10-RoomFootPrefix-ja.md)

# Coordinates at an actual foot call

This is a conditional result. `RoomFootPrefix.foot_prefix` follows a checked instruction prefix from a cut to a selected call of the block-buffer collision routine. It proves that the three address coordinates stay unchanged, A and X are zero, Y is the specified foot index, and the saved return address belongs to the selected caller. Each prefix instruction meets the model's frame-time condition.

The stop also tests the saved caller. An earlier head call to the same routine does not stop the walk. `BIT` in the overlapping wrapper is supported by `FrameWalk`.

`Route.Run.roomFootMap` composes this prefix with `Run.roomCollisionMap`. Under the existing room-map and ROM checks, enough frame time, explicit buffer bounds and a non-coin reference cell, the actual call returns the map byte computed from the cut's coordinates and specified index. The return stays in the same frame. `RoomFootPrefix.returned_map` is a lower-level version with an explicit map invariant at reads.

On 13 runs (the TAS, ten random and two fixed), the 500-instruction check passed for both actual foot entries, preserving coordinates with correct indices. All 26 real returns matched the floor map and all 13 frames ended standing. The measured sufficient start cut used 499 known-byte entries, including non-coin map cells, and left coin cells unknown. A greedy reduction on the TAS sample used 17 entries for the first call and 18 for the second, including duplicate control entries; these smaller cuts are measured only on that sample.

The start cut and prefix check are explicit local hypotheses. They have not been derived for every landing frame from current `Run` fields. The floor-cell classification, caller's tile branch, landing-state stores and preservation to frame end remain. `land_at` remains; no field is removed or added. No result uses `floor_at_of` to prove landing.

**Files:** `Theorems/RoomFootPrefix.lean`, `Theorems/FrameWalk.lean`.

Later, item 1-1-c-7-5-12 ([The landing frame of the first fall](c-7-5-12-RoomLand.md)) removed `land_at`; the field `landQ` in its place asks two bytes at the end of the landing frame's move. Item 1-1-c-7-5-13 ([The collision-disable flag and the vertical page in the first fall](c-7-5-13-LandBytes.md)) proves both bytes, and `landQ` is gone.
