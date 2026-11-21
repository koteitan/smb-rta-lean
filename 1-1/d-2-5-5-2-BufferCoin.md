[← Back](README.md) | [English](d-2-5-5-2-BufferCoin.md) | [Japanese](d-2-5-5-2-BufferCoin-ja.md)

# A frame that starts with the control at 6 left of the mouth does not enter

**Claim.** A frame of the room that starts with the control of the screen's buffers at 6, on page 0, with the position from 16 to 180 px, does not enter the side pipe. This is proved, with one check on the ROM (seven walks of the room's frame with one table, about 1.5 min natively since round 25) and the walk of one whole frame of [SideFrame](c-7-16-SideFrame.md) (`side_frame_check`, proved before). So the field `buffer₂` now asks less: if the frame before the entering frame erased a coin (the control is then 6), it ended on page 0 at 16 to 180 px. On real runs coin frames end at 52 to 173 px. That they always do is not proved.

The names are those of [The control of the screen's buffers through the room](d-2-5-5-1-BufferControl.md). `x(m)` and `page(m)` are the player's position on the page and the page (`Player_X_Position`, `Player_PageLoc`). `Q` is the end of the move (`PlayerSubs`), `xLo = 195 px` the mouth's left end. `r₆(a)` is the room's reference machine with `c = 6`, `page = 0` and `x` the value of the piece `a`. `K_G(a) := K_B ∪ { every bit of page } ∪ { the known bits of a }`.

## The statement

```
pieces         :=  [16, 32), [32, 64), [64, 128), [128, 160), [160, 176), [176, 180), {180}       (they cover [16, 181))
walkA(a)       :=  the walk from (r₆(a), K_G(a)) passes, and every state of its table at Q has page 0 and every x of its piece < xLo
coinCheck      :=  the pieces cover [16, 181),   K_T lists neither x, nor page, nor c,   these are three bytes,   ∀ a ∈ pieces,  walkA(a)

subs_left      :  walkA(a),   RoomCond(r₆(a), K_G(a), m),   ∀ j, SiteOK(tr(j))
                  →   ∀ j,  frame(tr(j)) ≤ frame(m),  pc(tr(j)) = Q   →   256·page(tr(j)) + x(tr(j)) < xLo
cond_piece     :  RoomCond(r, K_T, m),   c(m) = 6,   page(m) = 0,   x(m) ∈ a            →   RoomCond(r₆(a), K_G(a), m)
no_enter       :  the conditions of RoomMap.map_of_rows on [b, a),   coinCheck,   sideFrameCheck,   b ≤ k < a,
                  Enters(seq k),   c(seq k) = 6,   page(seq k) = 0,   16 ≤ x(seq k) < 181          →   False

Run.coin₂      :  c(seq(a₂ − 1)) = 6,   page(seq(a₂ − 1)) = 0,   16 ≤ x(seq(a₂ − 1)) < 181     →   False          (theorem, new)
Run.buffer₂    :  c(seq(a₂ − 1)) ≠ 6   ∨   (page(seq(a₂ − 1)) = 0  ∧  16 ≤ x(seq(a₂ − 1)) < 181)   ∨   EntryAt(L₅, seq a₂)     (field, narrowed)
```

`no_enter`: `SideFrame.entry_right_of_left` says that a frame that enters comes to `Q`, before the write of the side pipe's routine, at a position at or right of `xLo`. `subs_left` says that this frame comes to `Q` only left of `xLo`. `Run.coin₂` takes `k = a₂ − 1`: the room's entering frame (`room.enters`) is this frame, as in `Run.rt₂`. `Run.buf₂` uses `Run.coin₂` for the middle case of `buffer₂`.

Lean: `Theorems/BufferCoin.lean` (`bitP`, `MP`, `zoneM`, `preZ`, `walkG`, `posLeft`, `keyG`, `normG`, `optsG`, the search, `walkCheckG`, `rangePieces`, `rangeCover`, `mpOf`, `ref6x`, `knownG`, `startG`, `walkAll`, `searchOfG2`, `cfgOfG2`, `walkCheckG2`, `walkOKG_of_check2`, `cov_bitP`, `cov_zoneM`, `cov_preZ`, `LiveG`, `InTab`, `cover_liveG`, `live_stepG`, `subs_of_walkG`, `WalkOKG`, `walkOKG_of_check`, `left_of_posLeft`, `subs_left`, `coinCheck`, `cond_piece`, `no_enter`, `FactsB`), `Theorems/Route.lean` (`RoomChecks.buffer`, `Run.buffer₂`, `Run.coin₂`, `Run.buf₂`), the private `Proof/BufferCoin.lean` (`buffer_coin_check`; `genBufferCoin` in `Main.lean`). `FactsB` moved here from `BufferControl` and has two more fields: `coin` and `side`. There is no game data in the public files.

## How it works

**The move is short.** The move routine adds the speed's high four bits, with the sign, and a carry to the position. So for every value of the speed byte it moves the position by −8 to 8 px. The climbing routine adds one of four values of a table, −14 to 14 px. Nothing else writes the position before `Q`. From 16 to 180 px the position at `Q` is on page 0, from 2 to 194 px: left of `xLo`.

**The abstract machine adds bytes with all their bits known or none.** So the walk splits bytes into their values where the move needs them (`zoneM`):

* at the compare of the speed's high bits with 8: bit 3 of the accumulator (else the abstract compare does not tell which of the two ranges the added byte is in);
* at the compare of the added byte with 0: the accumulator (the abstract compare subtracts with all bits known or none, so without the split the sign byte did not match the added byte);
* at the add to the position: the carry, the added byte and the accumulator;
* at the add of the climbing routine: the accumulator.

So the position after the add is known. At `Q` every state must be one of the table (`walkG`), and the check asks of each of them `posLeft`. At the start of the scroll handler the search forgets the position, so that the rest of the frame is the walk of [the screen's buffer](d-2-5-5-EntryBuffer.md).

**The search (no part of the proof).** The key has the position, the page and the control. In the move routine and at the climbing routine's store the key also has the accumulator and the added byte: without them the search joins the pieces again. The room's key is put above these bytes (times 2⁴⁸), not below: with the old way of `keyY` the parts could overlap.

**Why the walk stops at `Q`.** A first design kept the position known through the whole collision routine: it passed 19 GB before the first piece ended, because the known position spreads to other bytes (the added byte, the scroll amount, the bounding box) and keeps the states apart. This design follows the known position only from the move to `Q`.

**Size.** For each piece about 1.2 to 1.33 million steps, 0 failures, 163,000 to 197,000 states, 91 to 2,170 states at `Q`, all on page 0 left of `xLo`. In a program: each search about 8 to 9 s, at most 735 MB; the check of all seven pieces 185 s natively. This is more than a few seconds.

**Round 25: one table.** The seven walks now share one search and one table (`startG`, `walkAll`, `searchOfG2`, `cfgOfG2`, `walkCheckG2`, `walkOKG_of_check2`; `walkA` is gone). The search from the 14 start states of all pieces: 2,002,560 steps, 363,068 states, 0 failures, 18.8 s; the check `coinCheck` 87 s natively (185 s with seven tables). The statement of `coinCheck` changed (one table), not that of `no_enter`.

## Measured, not a theorem

`buffer-ctl-check FM2 300 real` (exit 0): the movie's room and 1,200 own runs from frames of the movie in the room (kinds 0 and 1, small and big, 300 each; kind 1 starts in the last 60 frames before the entry and takes the coins next to the pipe).

| run | frames | entries | coin frames (the control 6 at the end) | of them ending on page 0 at 16 to 180 px | frames that start with the control 6 there | of them entering |
|---|---|---|---|---|---|---|
| the movie | 111 | 1 | 13 (ending at 52 to 163 px) | 13 | | |
| kind 0, small | 125,891 | 102 | 1,019 | 1,019 | 1,055 | 0 |
| kind 0, big | 113,761 | 126 | 1,229 | 1,229 | 1,265 | 0 |
| kind 1, small | 66,202 | 218 | 1,178 | 1,178 | 1,253 | 0 |
| kind 1, big | 69,677 | 208 | 1,245 | 1,245 | 1,320 | 0 |

No entering frame starts with the control at 6 (the first case of `buffer₂` holds on all 655 entries). Coin frames end at most at 173 px.

`buffer-ctl-check FM2 0 coin` (exit 0): the seven searches, as above. `buffer-ctl-check FM2 1 coin` also runs `coinCheck` (true).

## Uses from other parts

* Part c: `SideFrame.entry_right_of_left`, `SideFrame.frame_before` and the private `side_frame_check` (1-1-c-7-16); `RoomMap.cond_of_rows`, `RoomMap.start_of_rowsF`, `RoomMap.clean_of_rows`, `RoomMap.map_of_rows`, `RoomMap.head_of_rows`; through `Run.coin₂` `room.enters`, `Run.roomEnter`, `EntryRoutine.rt_of_rows`, `chg.roomSites`, `ChangesBase.roomStay`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`; part a: `Run.entry₁`.
* Part d: the walk of `EntryBuffer` (`hpB`, `knownB`) and of `EntryHeight` (`preY`, `stepY`, `cov_preY`, `s_stepY`), `BufferControl.Facts`.
* No cycle: none of these uses `buffer₂`, `Run.buf₂`, `Run.ctl₂` or `Run.coin₂`.

## What changed in the route

* Field narrowed: `buffer₂` has the new middle case `page = 0 ∧ 16 ≤ x < 181` at the start of the entering frame. The old field implies the new one.
* `RoomChecks.buffer : BufferCoin.FactsB …` (was `EntryBuffer.Facts`; `FactsB` is new here and extends `EntryBuffer.Facts` with the fields `ctl`, `coin` and `side`). `buffer_facts` in the private file of `EntryHeight` builds it.
* New theorem `Run.coin₂`; `Run.buf₂` uses it.

## Assumptions (not proved in Lean)

* `buffer₂`: if the frame before the entering frame erased a coin, it ended on page 0 at 16 to 180 px (else the five bytes at the entry are those of a reference). To remove it one would prove that a frame that ends with the control at 6 ends there: its coin is at least three columns left of the mouth, so it needs the position at the collision routine's read of the coin. Round 25 ([BufferEnd](d-2-5-5-3-BufferEnd.md), 1-1-d-2-5-5-3): a frame that ends with the control at 6 ends at 16 to 180 px (`Run.end₂`), so `buffer₂` now asks only page 0 there.
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

**Files.** `Theorems/BufferCoin.lean`, `Theorems/Route.lean`, `Theorems/BufferControl.lean` (`ref_of_ne6` added); the private check is in `Proof/BufferCoin.lean` (`genBufferCoin` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 coin       # the seven searches, about 1 min
.lake/build/bin/smbrta buffer-ctl-check FM2 1 coin       # and coinCheck, about 4 min
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # real frames, about 5 min
```
