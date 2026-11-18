[← Back](README.md) | [English](c-7-12-2-RoomCollisionMap.md) | [Japanese](c-7-12-2-RoomCollisionMap-ja.md)

# Map bytes at the actual collision read

`RoomBlocks.blocks_trace` exports the existing non-coin map invariant at every instruction whose machine is still in the starting frame. Its hypotheses are exactly those of `blocks_frame`: the checked walk and code, the room condition at the start, `SiteOK` on each instruction and `Solid` at the start. The old end-of-frame theorem is unchanged.

`blocks_run_trace` applies this to the room's sequence of frames. `Route.Run.roomBlocksTrace` is its Run-level companion: for each frame from first room control up to the side-entry frame, with the upper endpoint excluded, every instruction still in that frame has the reference map's value at every non-coin buffer cell. No new field of `Run` is added. The existing `Run.roomBlocks` still covers frame boundaries, including the final boundary.

## The returned tile on the real trace

`RoomCollision.frame_returned_map` combines the instruction invariant with the [complete collision call](c-7-5-8-RoomCollision.md). `Route.Run.roomCollisionMap` supplies the invariant and time bound from the existing room fields.

At an actual player call inside such a frame, assume:

- The checked collision routine, `Good`, the entry program counter and the player object index.
- The checked idle loop, already a fact in `RoomPair.VChecks.idle`.
- The index computed from the call's entry coordinates and ROM offsets is inside the block buffers, and its reference map byte is not a coin.

Then there is an actual read and return on the same frame trace. The call returns to its original caller, and A is that reference map byte. The read is reached within 93 instructions and the return within another 25. The proof derives `Solid` at the actual read; it does not assume it as a new Run field. The existing `roomSites` supplies the instruction-time bound.

## What landing still needs

`land_at` still needs the particular foot call reached on the landing frame, its selected offset index, and the position after the move at that call. The computed index must then be identified with the floor's non-coin cell, and the caller's tile classification and landing stores must be followed to the frame end. The map-at-read connection is now proved; choosing the right call, locating its cell and finishing its control flow remain. `stand_wall` and `wall` also remain. No whole-frame landing search was started.

**Files:** additions in `Theorems/RoomBlocks.lean`, `Theorems/RoomCollision.lean`; new `Theorems/RoomCollisionMap.lean`. The Run corollaries are in the new companion file, so `Route.lean` and all old signatures stay unchanged.

## Validation

`room-floor-check FM2 60` exited 0. On 59,811 frames from the TAS and own inputs it checked 82 coin erases and 410,104 player calls, reads and returns, with zero discrepancies or unfinished calls. The existing ROM predicate was true in 2,572 ms. These new lemmas add no ROM check or search.
