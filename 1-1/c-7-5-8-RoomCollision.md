[← Back](README.md) | [English](c-7-5-8-RoomCollision.md) | [Japanese](c-7-5-8-RoomCollision-ja.md)

# Coordinates, tile and return of the collision-buffer routine

`RoomCollision.routine` proves a complete `BlockBufferCollision` call for the player. Its assumptions are a checked ROM, `Good`, the entry program counter and X selecting the player object. The offset index Y, initial A, flags, stack pointer and position bytes are arbitrary. The theorem does not fix a TAS state.

Let R be the entry machine, i its offset index, T the machine at the tile read, and Q the returned machine. The offsets, row mask, screen-top subtraction and final coordinate mask come from the ROM.

```
a = selector(page(R), x(R), x_offset(i))
r = ((y(R) + y_offset(i)) & row_mask) - screen_top
address = buffer_start + (a / 16) * half_buffer_length + (a % 16) + r
```

r is the row’s byte offset, computed with byte arithmetic. `RoomAddress.encoded_eq_selector` accounts for the horizontal carry into the page. `actual_address` proves that the actual indirect read uses this address. `read_value` identifies its value with the live RAM byte at T.

The proof reaches T within 93 instructions and Q within another 25. It proves:

- A at Q and the saved tile equal the byte read at T.
- The saved row is r.
- The saved coordinate is the masked entry y when the initial A is zero, otherwise the masked entry x.
- The return program counter comes from R's original caller stack; SP advances by two.
- The coordinate bytes are kept up to T. Each instruction meets `InFrameN`, for use with the existing frame-timing lemma.

`ReadAt` and `Returned` list these conclusions. They are not new fields of `Route.Run`. The theorem is for the player object; calls for arbitrary enemy object indices are not included.

## The map and the whole frame

`returned_map` combines the result with `RoomBlocks.Solid` at T. The computed address must be in the block buffers and its reference byte must not be a coin. Then Q returns that map byte. An arbitrary entry height need not address the map, so buffer membership is explicit.

`Run.roomBlocks` supplies map agreement at frame boundaries. Its existing one-frame proof carries agreement through instructions internally; this page does not claim an exported link to every read state. That connection, the position after the move at each call, the chosen head/foot/side index and the control flow after the returned tile still need to be joined. `land_at`, `stand_wall` and `wall` remain. No field was removed or added, and no whole-frame search was enlarged.

Part d can use the same offset-index theorem for head and side reads near the pipe. Part f can use it for the address and value in `TileRead`. Both uses still need their actual call entry and subsequent control flow.

**Files:** `Theorems/RoomCollision.lean`; private `Proof/RoomCollision.lean`, `room_collision_check`. The [column-pointer lemma](c-7-5-7-RoomAddress.md) keeps its original statement.

## Checked on real frames

The ROM predicate was true in 2,617 ms natively. `room-floor-check FM2 60` checked 59,811 frames from the TAS and own inputs. There were 410,104 player calls, reads and returns. Entry `Good`, the target computed from the entry position, row, coordinate preservation, returned and saved values, and instruction bound had zero failures. There were zero unfinished calls. The command exited 0.

`room-jump-check FM2 100` checked 1,101 runs and 88,111 frames; `room-stand-check FM2 100` checked 701 runs and 56,111 frames. Both reported `bad: 0` and exited 0. These checks of runs do not prove the remaining landing and wall assumptions.
