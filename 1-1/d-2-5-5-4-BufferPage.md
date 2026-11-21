[← Back](README.md) | [English](d-2-5-5-4-BufferPage.md) | [Japanese](d-2-5-5-4-BufferPage-ja.md)

# A frame that erases a coin ends on page 0

**Claim.** A frame of the room that starts with the control of the screen's buffers at 0 or 6 and ends with it at 6 ends on page 0, with the position on the page from 16 to 180 px. This is proved, with one check on the ROM (the two walks of [BufferEnd](d-2-5-5-3-BufferEnd.md), now with the page; about 100 s natively). The page at the frame's start may be any value. So the field `buffer₂` is gone: the frame that enters the side pipe starts with the control at 0, and the five bytes of the first screen buffer at the entry are proved.

The names are those of [BufferEnd](d-2-5-5-3-BufferEnd.md). `c` is the control of the screen's buffers, `x(m)` the position on the page, `page(m)` the page. `Q` is the end of the move (`PlayerSubs`).

## The statement

```
finX(B)      :=  c is known not to be 6   ∨   (inside(the piece of x)  ∧  the page is known to be 0)

end_frame    :  walkE(r'),   RoomCond(r', K_B, m),   ∀ j, SiteOK(tr(j)),   c(frame m i) = 6
                →   16 ≤ x(frame m i) < 181   ∧   page(frame m i) = 0
end_of_rows  :  the conditions of RoomMap.map_of_rows on [b, a),   keepCheck,   startCheckC,   endCheck,   b ≤ n < a,   c(seq(n + 1)) = 6
                →   16 ≤ x(seq(n + 1)) < 181   ∧   page(seq(n + 1)) = 0

Run.end₂     :  c(seq(a₂ − 1)) = 6   →   16 ≤ x(seq(a₂ − 1)) < 181   ∧   page(seq(a₂ − 1)) = 0
Run.buf₂     :  EntryAt(L₅, seq a₂)                                                  (theorem; the field buffer₂ is gone)
```

`Run.buf₂`: if `c(seq(a₂ − 1)) = 6`, `Run.end₂` gives page 0 and 16 ≤ x < 181, and `Run.coin₂` (round 24) says that such a frame does not enter; but it does. So the control is not 6. By `Run.ctl₂` it is 0, the reference's value, and `EntryBuffer.buffer_of_rows` gives the five bytes.

Lean: `Theorems/BufferEnd.lean` (`MX` with `pI`, `xSbc`, `pSbc`; `pageSplit`, `cov_pageSplit`, `zoneX`, `finX`, `fin_spec`, `end_frame`, `end_step`, `end_of_rows`), `Theorems/Route.lean` (`Run.end₂`, `Run.buf₂`; the field `buffer₂` removed). The private check is still `buffer_end_check` in `Proof/BufferEnd.lean`. There is no game data in the public files.

## How it works

**The scroll handler comes before the collision routine.** In the player's routine the end of the move is followed by the scroll handler, and only then by the collision routine. In the room the scroll is locked, and the screen's edges are known in the room's condition (left edge at page 0, right edge 255 pixels further on the same page). The scroll handler asks the routine of the offscreen bits where the player is against the two edges, and if he is off the screen, it puts him at an edge (the clamp). A clamp writes the edge's page.

**Every page but 0 ends at the clamp to the left edge.** Write p for the page at the scroll handler.

* p from 1 to 128: against the right edge the difference of pages is negative; the bits say "off the screen"; the clamp to the left edge writes page 0.
* p from 129 to 254: the player is at least one page left of the right edge, and at least one page left of the left edge; the bits say "off the screen" again; the clamp writes page 0.
* p = 255: against the left edge the difference of pages is 0 or 1; with 1 the bits say "off the screen"; with 0 the pixel difference gives bits with the high bit set; the clamp writes page 0.
* p = 0 stays 0, with a clamp or without.

**A coin frame writes the page only there.** A coin found by a read for the head, a foot or a side leads to the erase and the return from the collision routine; a push of a side collision also returns from it. So a frame that erases a coin does not push, and after the scroll handler nothing writes the page.

**The walk.** The abstract machine subtracts two bytes only when all their bits are known. So, in the routine of the offscreen bits, at its subtraction of the position from the right edge (`xSbc`, the player, `X = 0`, `Y = 1`), when the position's piece is inside `[16, 181)` and the page is not known, the walk splits the page into its 256 values (`pageSplit`). For the pages 128 and 255 it also splits the position into its values: without that, the walk's unknown borrow of the first subtraction gives a path that the real machine never takes, and on that path the page stays. At the subtraction of the page (`pSbc`) with the page known and not 0 it splits the carry. Then every path ends as in the list above. At the frame's end `finX` asks the page known 0 when the control may be 6. Both walks (from the control 0 and from 6) pass, and every frame end with the control maybe 6 has the page known 0.

**The search (no part of the proof).** The key keeps the page apart, and in the routine of the offscreen bits and in the scroll handler also the registers, the flags, the position and the pixel difference. Where the bits with the high bit set are loaded in the scroll handler's call, the clamp to the left edge comes next; there a state forgets the page, the position, the pixel difference, A and four flags, so the 256 pieces join again. The pieces with the page known and not 0 are stepped without the table, up to the join. Without the join the check took 491 s natively.

**Size.** The walk from the control 0: 3,012,444 steps, 371,378 states of the search, 0 failures, 18.5 s. From the control 6: 3,620,300 steps, 439,580 states, 0 failures, 22.9 s (round 25: 1,218,211 and 1,776,901 steps). At most 2.3 GB. Frame ends with the control maybe 6: 168 and 84, all with the page known 0. The check of both walks: 83 s natively (round 25: 68 s); the private `Proof.BufferEnd` took 120 s in a full `prove.py` (round 25: 80 s). This is more than a few seconds.

**The table (no part of the proof).** The check built its table with a fold whose accumulator was a tuple read by projections; each push then copied the array, so the time grew with the square of the table's size. The fold now takes the tuple apart first. This is a change of how the table is built, not of what it holds. The same change is made in `BufferCoin` (the check of round 24: 89 s natively before, 32 s after), `EntryHeight`, `EntryHeightBig`, `RoomPause` and `ScreenPage`. The same fold is still in `RoomMap`, `RoomVert` and `SideEntryRest` (files of other parts).

## Measured, not a theorem

`buffer-ctl-check FM2 300 real` (exit 0): the movie's room and 1,200 own runs from frames of the movie in the room (kinds 0 and 1, small and big, 300 each), as in [BufferEnd](d-2-5-5-3-BufferEnd.md).

| run | frames | entries | coin frames (the control 6 at the end) | of them ending on page 0 at 16 to 180 px | entering frames that start with the control at 6 |
|---|---|---|---|---|---|
| the movie | 111 | 1 | 13 | 13 | 0 |
| kind 0, small | 125,891 | 102 | 1,019 | 1,019 | 0 |
| kind 0, big | 113,761 | 126 | 1,229 | 1,229 | 0 |
| kind 1, small | 66,202 | 218 | 1,178 | 1,178 | 0 |
| kind 1, big | 69,677 | 208 | 1,245 | 1,245 | 0 |

On these runs every frame starts on page 0. So the theorem's case of another page at the start is not reached by them. `buffer-ctl-check FM2 1000 page` (exit 0, new) tests it on own states: a room frame of the movie, small or big, with the page and the position overwritten by random bytes (half of the pages 0), then up to 40 frames of random inputs. 2,000 runs, 78,664 frames; 4,291 frames start off page 0 and 3,310 end off page 0 (all at page 255: a player put at the left edge inside the wall and pushed left). 2,355 frames end with the control at 6; all of them end on page 0 at 16 to 180 px. None of them starts off page 0: a frame that starts off page 0 is put at the left edge by the clamp, and there it reads no coin.

So the page is not 0 on every frame of every state of the room's condition; only the frames that erase a coin end on page 0. A keep of the page on every frame would need bounds on the position near the walls.

## Uses from other parts

* As [BufferEnd](d-2-5-5-3-BufferEnd.md) (part c: `RoomMap.cond_of_rows`, `MapFacts`, `startCheckT`, `chg.roomSites`, `ChangesBase.roomStay`, `Run.b₁_lt_a₂`, `RoomBlocks`; part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`; part a: `Run.entry₁`; part d: `BufferControl`, `EntryBuffer`, `EntryHeight`, `EntryHeightBig`, `BufferCoin`), and `Run.coin₂`, `Run.ctl₂` in `Run.buf₂`.
* New pieces from other files: `SideFrame.fillB`, `SideFrame.cov_fill`, `BufferCoin.bitP`, `BufferCoin.cov_bitP`, `PipeWrites.cov_then`.
* Part c's walls are not used: the page needs no bound on the position at the frame's start.
* No cycle: none of these uses `buffer₂`, `Run.buf₂` or `Run.end₂`.

## What changed in the route

* Field removed: `buffer₂` (round 25: `c(seq(a₂ − 1)) ≠ 6 ∨ page(seq(a₂ − 1)) = 0 ∨ EntryAt(L₅, seq a₂)`).
* No field added. `RoomChecks.buffer` is unchanged in type (`BufferEnd.FactsE`); its check `endCheck` now has the page in `finX`.
* `Run.end₂` also gives page 0. `Run.buf₂` has the same statement and no longer uses a field.

## Assumptions (not proved in Lean)

* `SiteOK` on each instruction in the room (`chg.roomSites`, item 1-1-d-2-4-2), as before.

**To reproduce.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 end        # the two searches
.lake/build/bin/smbrta buffer-ctl-check FM2 1 end        # and endCheck
.lake/build/bin/smbrta buffer-ctl-check FM2 1000 page    # own states with the page and the position overwritten
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # real frames
```
