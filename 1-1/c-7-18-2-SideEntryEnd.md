[← Back](README.md) | [English](c-7-18-2-SideEntryEnd.md) | [Japanese](c-7-18-2-SideEntryEnd-ja.md)

# The side pipe's entering frame: the position at its end

**Claim.** On a frame of the room that writes the side pipe's routine, the position at the end of the frame is at or right of the mouth's left end. There is no hypothesis on the position. So `P(E)` is read at the end of frame `E`, as `read_P` reads the other frames (`read_PE`), and the field `movedE` of [Joining the bonus room](c-5-RoomJoin.md) is gone (item 1-1-c-7-18-2).

Two walks prove it. The first follows the frame from its start to the first write of the side pipe's routine, on the abstract machine of [The side pipe's entry: one whole frame](c-7-16-SideFrame.md). The second follows the frame from the write to its end, on the walk of [The block map in the room](c-7-12-RoomMap.md), which knows the room's bytes and the target of every store.

`tr(j)` is the machine `j` instructions into the frame. `rt(m)` is the routine byte, `e_s` the side pipe's routine. `w` is the instruction that writes it. `x₀` is the first `x` with his right side in the mouth, `P₀ = 256·x₀` the mouth's left end. `px(m) = 256·page(m) + x(m)`, and `posP(m) = 256·px(m) + fraction(m)`.

```
splitAll   at the end of the move: the position in pieces that cover every value
             page 0 and x < x₀ (the 4 pieces of SideFrame),  page 0 and x ≥ x₀ (5 pieces),  page ≠ 0 (8 pieces: one bit of the page is 1)
splitOne   where the collision routine first reads the height on the screen: that byte is 1, or one of its bits differs from 1 (9 pieces)
posOK(A)   :=  a bit of the page is known to be 1,  or  the page is known to be 0 and the pixel's known bits are at least x₀
okA(A)     :=  rt(A) is known not to be e_s,  and  (pc(A) = w → posOK(A))
HypE(m)    :=  (AtRead(m) → TilesOK(m))  ∧  pc(m) ∉ {h, bumpAt}

write_right_of_left :  frameCheck,  FrameStart(m),  ∀ j,  Clean(tr(j)) ∧ HypE(tr(j))
                       →  ∀ j,  (∀ k ≤ j,  rt(tr(k)) ≠ e_s)  →  pc(tr(j)) = w  →  x₀ ≤ px(tr(j))

splitR     at w, while rt is known not to be e_s: page 0 and x ≥ x₀ (5 pieces),  page ≠ 0 (8 pieces)
HypW(m)    :=  pc(m) = w  →  rt(m) ≠ e_s  →  x₀ ≤ px(m)
okS(A)     :=  rt(A) is known not to be e_s,  or  rt(A) is known to be e_s and posOK(A)
okT(A, B)  :=  rt(A) known e_s  →  rt(B) known e_s

rest_end :  restCheck,  RoomCond(m),  ∀ j,  SiteOK(tr(j)),
            ∀ j,  (∀ k ≤ j,  rt(tr(k)) ≠ e_s)  →  HypW(tr(j)),
            ∃ n,  rt(tr(n)) ≠ e_s  ∧  rt(tr(n + 1)) = e_s
            →  x₀ ≤ px(frame(m, i))

mouth_of_rows :  the hypotheses of RoomMap.map_of_rows,  the checks,  b ≤ k < a,  Enters(seq(k), inp(k))
                 →  P₀ ≤ posP(frame(seq(k), inp(k)))
Run.roomMouthE :  the checks,  Run  →  P₀ ≤ posP(frame(fm(E − 1), pad(E)))          (InRoom.mouthE)
read_PE (field) :  P(E) = posP(frame(fm(E − 1), pad(E)))                              (a reading, as read_P)
RoomRun.mouth_of :  InRoom  →  P₀ ≤ P(E)
side_entry_end_check, side_rest_check (private) :  frameCheck = true,  restCheck = true   (native_decide)
```

`mouth_of_rows` puts the two walks together on a frame of the room. The first walk gives `HypW` at every state before the routine byte is the side pipe's. After it, the second walk's own `okT` keeps the routine byte the side pipe's, so `HypW` asks nothing there. `Route.Run.roomMouthE` takes the frame of `Run.roomEnter`.

Lean: `Theorems/SideEntryEnd.lean`, `Theorems/SideEntryRest.lean`; in `Theorems/RoomJoin.lean` the field `read_PE` and `InRoom.mouthE`; in `Theorems/Route.lean` `Run.roomMouthE`; private `Proof/SideEntryEnd.lean`, `Proof/SideEntryRest.lean`.

## How it works

**Up to the write** (`SideEntryEnd`). The machine and the pieces are those of [one whole frame](c-7-16-SideFrame.md), but at the end of the move the position is split with no hypothesis. On page 0 the pixel goes into a piece left or right of the mouth. On another page the walk does not know the pixel: one bit of the page is 1. Where the scroll handler asks whether he is off the screen, the pixel is split into its values if some of its bits are known, as before. With the page partly known there, the search keeps the registers apart, so that the store at the screen's edges writes known values. The height on the screen is split where the collision routine first reads it: on the screen (1), the collision routine goes on to the side check; else it leaves. A path stops where the routine byte becomes the side pipe's.

On every path the write `w` comes with the position at or right of the mouth: on page 0 the side check finds the pipe's tiles only with the pixel at or right of `x₀`, as in `SideFrame`; on another page, a bit of the page stays known to be 1.

**From the write to the frame's end** (`SideEntryRest`). The walk of the room knows the room's bytes (no enemies, no fireballs) and the target of every store. At `w` the position is split into the pieces at or right of the mouth, by `HypW`. After the write the frame finishes the player's routine and runs the other routines. No store moves the position, and the routine byte stays the side pipe's: the height on the screen is known (it was 1 at the collision routine), so the player's routine does not start the routine of a fall into a hole.

**Size.** Up to the write: 16,522,088 steps, 1,615,563 forks, 0 failures, a table of 586,648 states; in a program the search takes about 40 s and the check about 58 s (it searches again), with 4.3 GB. From the write: 454,881 steps, 0 failures, 75,908 states; the search about 4 s, the check about 7 s. Both are more than a few seconds; the first is the biggest check of part c.

**Why two walks.** One walk did not work:

* The machine of `SideFrame` to the frame's end (with the position on page 0 only): after the write, the frame stores through indexes that this machine does not know (the fireballs, the enemies, the screen's buffer), and such a store forgets the position (10,412,005 steps, 347,289 failures). With the position kept from those stores (the guard with the position among its bytes), the enemies' routines still write another routine (the injury) and move the player, since this machine does not know that the room has no enemy (3,514 failures in the first 6,000,000 steps). With the 363 bytes that the room's condition knows whole kept too, the search did not end in 15 minutes (4.7 GB).
* The walk of the room with the position split at the end of the move: the pieces multiply the states of every frame of the room, and the search passed 8 GB.

The first part of the frame needs the position but not the room's bytes. The second part needs the room's bytes, and the position only from the write.

## On real frames

The program `side-frame-check` (see [one whole frame](c-7-16-SideFrame.md)) runs 1,715 entries: the movie's, 67 from random inputs in the movie's room, 352 from every input near the entry, 1,295 from overwritten states near the mouth. In every one the position at the end of the move before the write is 195 to 216 px, and it is the position at the frame's end. So `read_PE` reads the same `P(E)` as the old `movedE`, and `P(E) ≥ P₀` holds on all of them.

## Fields of `RoomRun`

* Removed: `movedE` (`P(E)` is the position at the end of the move).
* Added: `read_PE` (`P(E)` is the position at the frame's end), a reading like `read_P`.
* `InRoom` is now `mouthE` (this page) and `bump` (no head's collision, [the block map](c-7-12-RoomMap.md)). `TilesE`, `StartE`, `CleanE`, `HeadE` and the theorems `Run.roomTiles`, `Run.roomStartE`, `Run.roomCleanE`, `Run.roomHeadE` stay as theorems; `mouth_of` no longer uses them, and `RoomJoin.Checks.sideFrame` is gone.

## Assumptions (not proved in Lean)

Nothing new. The walks use what [The block map in the room](c-7-12-RoomMap.md) proves on the frames of the room (`FrameStart`, `Clean`, `TilesOK`, no head's collision, the room's condition at each frame's start) and what it assumes: `SiteOK` on each instruction of the room's frames (`Route.Changes.roomSites`).

**Files.** `Theorems/SideEntryEnd.lean`, `Theorems/SideEntryRest.lean`, private `Proof/SideEntryEnd.lean`, `Proof/SideEntryRest.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-entry-end-search      # the searches and the checks of both walks, about 2 min
```
