[← Back](README.md) | [English](d-2-5-4-2-EntryHeadHeight.md) | [Japanese](d-2-5-4-2-EntryHeadHeight-ja.md)

# A head cell excludes a lower pipe entry

This is a local result. The checked address formula says: if the big, non-swimming player's first upper side cell at 192 px contains the side pipe, then the head cell at the same horizontal coordinates, within the landing-depth band above that rounded position, is in the block buffers, is not a coin and is outside the allowed head class. The head and side indices and tile value come from the ROM and symbols.

`EntryHeadHeight.excludes_head` combines this with `RoomCollision.ReadAt`, `SiteOK` and `Solid`. These conditions cannot all hold for that head read and that side cell. The finite check enumerates byte coordinates and the short landing band, not frame paths. It took about 1.2–2.0 seconds natively; private `entry_head_geometry` proves it. The existing `EntryHeight` frame walk is unchanged.

The side-index restriction matters. Extending the claim to every side offset is false: a right-side cell can contain the pipe while the head cell is empty. This is a counterexample to that broader geometric claim, not a complete frame satisfying every room hypothesis.

Measured first: the unchanged big-player walk still has eight abstract ends at 192 px and four failures. In 2,240 concrete candidate frames, 256 entered at 192 px. All 256 had the big, non-crouching head offset and the first upper side offset; the head read a non-coin pipe byte outside the head class. All had `RoomCond` and `Solid`, but every one violated `SiteOK` at the head. No complete candidate satisfied all hypotheses.

The normal real check passed for the TAS and 50 own runs per size: 20 small and 21 big entries, all at 176 px, with every entering instruction meeting `SiteOK`. The required five-run check also exited 0.

What remains: identify and join those actual head and side calls for every entering frame, prove their horizontal coordinate agreement and prelanding-height band, and exclude other call branches. The eight abstract frame ends are not removed merely by checking this local table; their lost history must be recovered. `height₂` and `buffer₂` remain unchanged. No field is added or widened.

**Files:** `Theorems/EntryHeadHeight.lean`; private `Proof/EntryHeadHeight.lean`.

**Round 21.** The link to the entering frame is now made in another way: the walk of [EntryHeightBig](d-2-5-4-3-EntryHeightBig.md) knows the head's cell on the frames that could end at 192 px and removes them with `SiteOK` and `Solid`. It does not use `excludes_head`.

**Round 22.** The field `height₂` is gone: the frame that enters the side pipe starts with a small or a big player ([the size through the room](d-2-5-4-4-SizeKeep.md)).
