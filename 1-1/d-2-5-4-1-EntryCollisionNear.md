[← Back](README.md) | [English](d-2-5-4-1-EntryCollisionNear.md) | [Japanese](d-2-5-4-1-EntryCollisionNear-ja.md)

# Entry reads and the gap to coin columns

This partial result connects the actual index computed by `RoomCollision` from its entry position to the existing coin-column gap. If the index is in the buffers and its column is closer to the pipe than any map coin, the reference byte is not a coin. `Solid` and the complete-call result then give the returned map byte and exclude a returned coin. Conversely, a coin actually returned by the call inherits the existing column-gap bound.

`head_reference_allowed` proves that the non-coin map byte at an actual head read belongs to `SiteOK`'s head classification. Read/saved-byte metadata, the head index, buffer membership and map agreement are explicit.

The eight ends at 192 px are not yet removed. The actual head index chosen from size/crouch and its computed cell must be identified, and that floor byte must be shown incompatible with the head classification. `buffer₂` still needs the previous frame's coin read tied to the entering position through the movement bound and the screen-update control. No near-column condition was added as a `Run` field.

`EntrySolid.cond` strengthens the FRAME-START condition; instruction-prefix `Solid` supplies map agreement at the actual read. No frame-start `RoomCond` is assumed at the read program counter.

`entry-height-check FM2 5 real` exited 0. Some groups of these few own-input runs never entered, so this does not exhaust big-player entry cases. No new ROM check, search or `Run` field was added.

**File:** `Theorems/EntryCollisionNear.lean`.
