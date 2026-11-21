[← Back](README.md) | [English](d-2-5-5-3-BufferEnd.md) | [Japanese](d-2-5-5-3-BufferEnd-ja.md)

# A frame that erases a coin ends at 16 to 180 px

**Claim.** A frame of the room that starts with the control of the screen's buffers at 0 or 6 and ends with it at 6 ends with the position on the page from 16 to 180 px. This is proved, with one check on the ROM (two walks of the room's frame, about 60 to 80 s natively). So the field `buffer₂` now asks only the page: if the frame before the entering frame erased a coin (the control is then 6), it ended on page 0. On real runs the page in the room is always 0. That it always is is not proved. Round 26: such a frame also ends on page 0, so `buffer₂` is gone ([BufferPage](d-2-5-5-4-BufferPage.md)); the walk of this page now also follows the page.

The names are those of [The control of the screen's buffers through the room](d-2-5-5-1-BufferControl.md) and [A frame that starts with the control at 6 left of the mouth does not enter](d-2-5-5-2-BufferCoin.md). `x(m)` and `page(m)` are the player's position on the page and the page. `Q` is the end of the move (`PlayerSubs`). `r` is the room's reference machine (control 0), `r₆` the same with the control 6. `K_B = K_T ∪ { every bit of c }`.

## The statement

```
pieces       :=  the aligned blocks of [0, 16), of [16, 181) and of [181, 256)                        (12 pieces; they cover every value)
inside(a)    :=  every value of the piece a is from 16 to 180
finX(B)      :=  c is known not to be 6   ∨   inside(the piece of x)
walkE(r')    :=  the walk from (r', K_B) passes, and every frame end of it meets finX
endCheck     :=  walkE(r)  ∧  walkE(r₆)

end_frame    :  walkE(r'),   RoomCond(r', K_B, m),   ∀ j, SiteOK(tr(j)),   c(frame m i) = 6     →   16 ≤ x(frame m i) < 181
end_step     :  keepCheck,   endCheck,   RoomCond(r, K_T, m),   ∀ j, SiteOK(tr(j)),   c(m) ∈ {0, 6},   c(frame m i) = 6
                →   16 ≤ x(frame m i) < 181
end_of_rows  :  the conditions of RoomMap.map_of_rows on [b, a),   keepCheck,   startCheckC,   endCheck,   b ≤ n < a,   c(seq(n + 1)) = 6
                →   16 ≤ x(seq(n + 1)) < 181

Run.end₂     :  c(seq(a₂ − 1)) = 6   →   16 ≤ x(seq(a₂ − 1)) < 181                                    (theorem, new)
Run.buffer₂  :  c(seq(a₂ − 1)) ≠ 6   ∨   page(seq(a₂ − 1)) = 0   ∨   EntryAt(L₅, seq a₂)                (field, narrowed)
```

`Run.end₂`: if `a₂ − 1 = b₁`, the frame starts the room and the control is the reference's 0 (`BufferControl.start_ctl`). Else the frame `a₂ − 2` is a frame of the room, and `end_of_rows` gives the position. `Run.buf₂`: with page 0 and the control at 6, `Run.end₂` gives 16 ≤ x < 181, and `Run.coin₂` (round 24) says that such a frame does not enter.

Lean: `Theorems/BufferEnd.lean` (`piecesX`, `piecesCover`, `inside`, `MX`, `zoneX`, `preX`, `finX`, `readAt`, `eraseOut`, `stepZ`, `walkX`, the search, `walkCheckX`, `piece_of_cover`, `cov_zoneX`, `cov_preX`, `s_stepZ`, `LiveX`, `cover_liveX`, `live_stepX`, `frame_of_walkX`, `WalkOKX`, `walkOKX_of_check`, `frame_endX`, `fin_spec`, `end_frame`, `findAbs`, `mxOf`, `hpX`, `walkE`, `endCheck`, `end_step`, `end_of_rows`, `FactsE`), `Theorems/Route.lean` (`RoomChecks.buffer`, `Run.buffer₂`, `Run.end₂`, `Run.buf₂`), the private `Proof/BufferEnd.lean` (`buffer_end_check`; `genBufferEnd` in `Main.lean`). There is no game data in the public files.

## How it works

**Every coin ends the collision routine.** A coin found by the read for the head, for a foot or for a side leads to the erase of the coin. The erase sets the control to 6, and the code then returns from the collision routine. A push of a side collision also returns from it. So on a frame that erases a coin the position is not written after the end of the move, except by the scroll handler, which puts the player at a screen's edge when he is off the screen.

**The position in pieces.** At `Q` the walk splits the position into 12 pieces whose known bits are a run of high bits. Seven are inside `[16, 181)`, five are outside. With a piece inside, a read of the block buffers may give any tile of `SiteOK`'s list, a coin too. The piece then stays up to the frame's end, and `finX` holds there.

**With a piece outside, the read has a known place.** The abstract machine adds bytes with all their bits known or none. So the walk splits, only for a piece outside (`zoneX`):

* at the load of the adders' offset: the offset's bits (the offset is one of three: a big player, a big one in the water, a small or crouching one);
* at the block buffer routine's add of the player's position: the position, into its values;
* at the start of the routine that makes the block buffer's address: the page's bit (the page is not known);
* at the mask of the row: the high bits of the accumulator.

Then the pointer and `Y` of the read are known. The new step `stepZ` gives, at such a read, each tile of `SiteOK`'s list that meets the known bits of the byte read (the room's condition knows the bits that are 0 in the map). In the map only the first block buffer has bytes that can be a coin: 19 cells in the columns 4 to 10. With the position outside, the column of the read is 0, 1 or 11 to 15, so the read gives no coin.

**Reads past the block buffers.** The split of the row also gives rows that the real code never reads (the height is checked before each read, but the abstract machine does not keep that). Such a read with the page's bit 1 reads RAM past the second block buffer, which the walk does not know, so it may give a coin. Then the erase would write there. `SiteOK` says that the erase writes inside the block buffers. So `stepZ` has no machine at an erase whose place is known and outside them (`eraseOut`).

**The search (no part of the proof).** The key has the control and the position's piece. With a piece outside, inside the block buffer routine and the address's routine, the key also has the registers, the pointer, the row and the sum; while the byte read may be a coin, it keeps the pointer and the row. After the add of the position, a state forgets the position's value down to its piece and the sum down to its high bits (the column). After the save of the tile it forgets the pointer, the row and `Y`, unless the tile may be a coin. At the return from the collision routine it forgets the position if the control is known not to be 6. Without these steps the search passed 26.8 GB in one try (stopped).

**Size.** The walk from the control 0: 1,218,211 steps, 311,882 states, 0 failures, 14.6 s. From the control 6: 1,776,901 steps, 373,444 states, 0 failures, 21.3 s. At most 1.9 GB. Frame ends with the control maybe 6 have only pieces inside. The check of both walks: 68 s natively. This is more than a few seconds.

## Measured, not a theorem

`buffer-ctl-check FM2 300 real` (exit 0): the movie's room and 1,200 own runs from frames of the movie in the room (kinds 0 and 1, small and big, 300 each; kind 1 starts in the last 60 frames before the entry and takes the coins next to the pipe).

| run | frames | entries | coin frames (the control 6 at the end) | of them ending at 16 to 180 px (any page) | entries where the new `buffer₂` holds |
|---|---|---|---|---|---|
| the movie | 111 | 1 | 13 (ending at 52 to 163 px) | 13 | 1 |
| kind 0, small | 125,891 | 102 | 1,019 | 1,019 | 102 |
| kind 0, big | 113,761 | 126 | 1,229 | 1,229 | 126 |
| kind 1, small | 66,202 | 218 | 1,178 | 1,178 | 218 |
| kind 1, big | 69,677 | 208 | 1,245 | 1,245 | 208 |

Coin frames end at most at 173 px; after the erase the position does not change up to the frame's end. Every frame of these runs starts on page 0. The entering frames start with the control at 0 (the first case of `buffer₂`). `entry-height-check FM2 50 real` (exit 0) counts the new `buffer₂` on its 41 entries: all hold.

`buffer-ctl-check FM2 0 end` (exit 0): the two searches, as above. `buffer-ctl-check FM2 1 end` also runs `endCheck` (true, 68 s).

## Uses from other parts

* Part c: `RoomMap.cond_of_rows`, `RoomMap.MapFacts`, `RoomMap.startCheckT`, `chg.roomSites` (`SiteOK`: the read's tile list and the erase's place), `ChangesBase.roomStay`, `Run.b₁_lt_a₂`; `RoomBlocks.readAddr_eq`, `readVal_eq`, `writeAddr_eq`, `ptrZ`, `operand`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`; part a: `Run.entry₁`.
* Part d: `BufferControl` (`keepCheck`, `keep_parts`, `cond0`, `cond6`, `ref6`, `ctl_of_rows`, `startCheckC`, `start_ctl`), `EntryBuffer` (`hpB`, `knownB`, `ctlI`), `EntryHeight` (`preY`, `stepY`, `cov_preY`, `s_stepY`), `EntryHeightBig` (`ptrLo`, `ptrHi`, `readAd`, `readI`), `BufferCoin` (`rangePieces`, `FactsB`, and `Run.coin₂` in the route).
* No cycle: none of these uses `buffer₂`, `Run.buf₂` or `Run.end₂`.

## What changed in the route

* Field narrowed: `buffer₂` lost the position. Round 24: `c ≠ 6 ∨ (page = 0 ∧ 16 ≤ x < 181) ∨ EntryAt`. Now: `c ≠ 6 ∨ page = 0 ∨ EntryAt`, all at the start of the entering frame. The old field implies the new one.
* `RoomChecks.buffer : BufferEnd.FactsE …` (was `BufferCoin.FactsB`; `FactsE` extends it with the field `ends : endCheck = true`). `buffer_facts` in the private file of `EntryHeight` builds it.
* New theorem `Run.end₂`; `Run.buf₂` uses it.

## Assumptions (not proved in Lean)

* `buffer₂`: if the frame before the entering frame erased a coin, it ended on page 0 (else the five bytes at the entry are those of a reference). To remove it one would prove that the page is 0 on every frame of the room. The move and a push carry into the page, so that needs the position on every frame of the room, near the walls too. Round 26: `buffer₂` is gone: a frame that erases a coin also ends on page 0 ([BufferPage](d-2-5-5-4-BufferPage.md), 1-1-d-2-5-5-4).
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

**Files.** `Theorems/BufferEnd.lean`, `Theorems/Route.lean`; the private check is in `Proof/BufferEnd.lean` (`genBufferEnd` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 end        # the two searches, about 40 s
.lake/build/bin/smbrta buffer-ctl-check FM2 1 end        # and endCheck, about 2 min
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # real frames, about 5 min
```
