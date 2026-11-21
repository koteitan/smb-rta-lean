[← Back](README.md) | [English](d-2-5-5-EntryBuffer.md) | [Japanese](d-2-5-5-EntryBuffer-ja.md)

# The screen's buffer at the side pipe's entry

**Claim.** A frame of the room that starts with the control of the screen's buffers at 0 and ends with the side pipe's routine ends with the first screen buffer of a reference of the entry: its offset and four of its bytes. This is proved, with one check on the ROM (a walk of the room's frame). So `Route.Run` no longer asks these five bytes at the side pipe's entry of a run whose entering frame starts with the control at 0. For a run whose entering frame starts with the control set it still asks them (the new field `buffer₂`). With [the height](d-2-5-4-EntryHeight.md), `chg.entry₂` asks 3 bytes, not 9 (1-1-d-2-5).

The control is not 0 at a frame's start when the frame before erased a coin. Since round 23 the control is proved to be 0 or 6 at the start of every frame of the room ([The control of the screen's buffers through the room](d-2-5-5-1-BufferControl.md), `Run.ctl₂`). That it is not 6 at the start of the entering frame is not proved.

The names are those of [The height at the side pipe's entry](d-2-5-4-EntryHeight.md). `c(m)` is the control of the screen's buffers (`VRAM_Buffer_AddrCtrl`). `L₅` is the five bytes: the offset of the first screen buffer (`VRAM_Buffer1_Offset`) and its bytes 0, 1, 2 and 7. `V` is the references of the entry, each a machine `v` and the list `X` of the bytes that it gives.

## The statement

```
EntryAt(L, m)   :=  ∃ (v, X) ∈ V,  ∀ i ∈ X,  i ∈ L  →  m[i] = v[i]
K_B             :=  K_T ∪ { every bit of c }
finB(B)         :=  B knows rt ≠ e_s   ∨   ∃ (v, X) ∈ V,  ∀ i ∈ X ∩ L₅,  B knows m[i] = v[i]

buffer_frame    :  WalkOK(finB),  RoomCond(K_B, m),  ∀ j, SiteOK(tr(j)),  rt(frame(m, i)) = e_s      →   EntryAt(L₅, frame(m, i))
buffer_of_rows  :  the hypotheses of RoomMap.map_of_rows on [b, a),  the checks,  b ≤ k < a,
                   c(seq k) = c(r),   rt(frame(seq k, inp k)) = e_s                 →   EntryAt(L₅, frame(seq k, inp k))

Run.buffer₂     :  c(seq(a₂ − 1)) = c(r)   ∨   EntryAt(L₅, seq a₂)                   (field, new)
Run.buf₂        :  EntryAt(L₅, seq a₂)                                                (theorem)
entryAt_of_buf  :  EntryAt(L₅, m)  ∧  EntryAt(R₃, m)   →   EntryAt(R₈, m)
chg.entry₂      :  EntryAt(R₃, seq a₂)                                                (3 bytes; it was R₉)
```

`R₈` is the 8 bytes of `restIdxY`, and `R₃ := R₈ \ L₅` (`restIdxB`): the area music's buffer, the event music's queue and the added note length. `c(r) = 0`. `WalkOK` and the walk are those of the height's page, with no split of the height.

**`entryAt_of_buf`.** `EntryAt` takes one reference for all its bytes. The two references agree on `R₃`: a byte of `R₃` that one gives, each gives, with the same value (`agreeCheck`). So the reference of the five bytes also gives the three.

**`Run.buf₂`** is as `Run.y₂`: frame `a₂ − 1` is a frame of the room that ends with the side pipe's routine. If `c(seq(a₂ − 1)) = c(r)`, `buffer_of_rows` gives the bytes. Else `buffer₂` gives them.

Lean: `Theorems/EntryBuffer.lean` (`finB`, `keyB`, `optsB`, `buffer_frame`, `ctlI`, `bufIdx`, `hpB`, `knownB`, `bufferCheck`, `agreeCheck`, `Facts`, `factsOf`, `buffer_of_rows`), `Theorems/EntryHeight.lean` (the walk, `WalkOK`, `frame_end`), `Theorems/Route.lean` (`restIdxB`, `RoomChecks.buffer`, `Run.buffer₂`, `Run.buf₂`, `entryAt_of_buf`, `Run.chgK`), private `Proof/EntryHeight.lean` (`entry_buffer_walk`, `entry_buffer_agree`, `buffer_facts`). There is no game data in the public files. The name `VRAM_Buffer_AddrCtrl` was added to `ScreenPage.namesOf`.

## How it works

**The frame's start.** The interrupt handler draws the screen buffer that the control names, and then empties it: it writes 0 to its offset and to its first byte, and sets the control to 0. With the control at 0 this is the first buffer. With the control set by the erase of a coin it is the second buffer, and the first one keeps its records. This is why the walk needs the control.

**The entering frame takes no coin.** A coin at the head or at the feet ends the collision routine before the side check. A coin at the side is the tile of the side check, in place of the pipe's. So no path of the walk takes a coin and then writes the side pipe's routine.

**The timer's digits.** The game timer's code does not run when the routine is below the player's control, and the side pipe's routine is.

**The colour rotation.** It is the only code that writes the first buffer on these paths. Every eighth frame it writes one record at the buffer's offset and adds the record's length to the offset. So the frame ends with the buffer empty (the offset 0 and the first byte 0), or with this one record. These are the two references: the first gives the offset and the first byte, the second all five bytes.

**The bytes after an empty buffer.** With the offset 0, bytes 1, 2 and 7 keep what an earlier record left there (the colour rotation's, or the timer's digits). The first reference does not give them, so nothing is asked of them.

**The search (no part of the proof).** The key has the control. Without it, the state in the idle loop at the frame's end is joined with the state at the frame's start (they have the same key), and the control that the start knows is lost. With the side pipe's routine the key also has the five bytes.

**Size.** 172,402 steps, 10,547 forks, 0 failures, 39,574 states. In a program: the search 2.1 s, the check 5.8 s.

## Measured, not a theorem

The walk with the control not known at the frame's start (`entry-height-check FM2 N walkbuf`):

| the control at the frame's start | steps | failures | frame ends with the side pipe's routine | the buffer at these ends |
|---|---|---|---|---|
| the reference's (0) | 172,402 | 0 | 8 | empty (offset 0, first byte 0); or one colour record (offset 7) |
| not known | 271,716 | 114 | 232 | 228 ends fail: the offset takes every value that the buffer admits |

**What would give the control.** The control is set at a frame's end only when the frame erased a coin. In the map the nearest coin is three columns left of the mouth's column. One frame moves the player by less than one column for every value of the speed byte, since the move adds only the speed's high four bits. So a frame that erases a coin is not followed by a frame that enters. To prove it one needs the position on these two frames in the abstract machine: a walk of the frame before with the position split at the read that finds the coin, and a walk of the entering frame from the positions left of the mouth. This is not done.

## Checked partial result for the previous frame

`EntryBufferNear.map_coin` proves that an actual coin read must be at a map coin under `Solid`. `entry_coin_gap` in private `Proof/EntrySolidFacts.lean` checks that all map coins lie at least three columns left of the mouth. `read_separation` and `not_short_move` prove the conditional geometry: with read offsets shorter than a column, these reads require at least 18 pixels between player positions, incompatible with a smaller one-frame displacement.

The connection from actual instructions on two frames to those read positions and displacement is not proved. A diagnostic starting at the first mouth position with full non-coin map knowledge still had 63 abstract failures (2,016,392 steps). It is not a buffer proof. `buffer₂` remains unchanged.

## Checked on real frames

A program (`entry-height-check FM2 400 real`, about 3 min): the movie's entering frame, and own inputs from frames of the movie in the room, 400 runs with a small player and 400 with a big one.

| run | entries | the control at the start of the entering frame is 0 | the five bytes are a reference's | the buffer at the entry (offset: bytes 0, 1, 2 … 7) | `R₃` is a reference's |
|---|---|---|---|---|---|
| the movie (movie frame 763) | 1 | 1 | 1 | a reference's | 1 |
| small | 142 | 142 | 142 | empty with stale bytes of the colour record 90, one colour record 35, empty with stale bytes of the timer's record 17 | 142 |
| big | 151 | 151 | 151 | one colour record 38, empty with stale bytes of the colour record 99, empty with stale bytes of the timer's record 14 | 151 |

In the 31 entries with stale bytes of the timer's record, these are bytes 1 and 2. The first reference does not give them. In every entry that comes after a frame that ends with the control set, at least 16 frames are between them.

## Round 23: the control through the room

[The control of the screen's buffers through the room](d-2-5-5-1-BufferControl.md) (1-1-d-2-5-5-1) proves that every frame of the room, from the first control to the entering frame, starts with the control at 0 or 6 (`Run.ctl₂`): the walk of this page from the control at 0 and at 6 ends with the control at 0 or 6, and the rows of the first change know it at 0 at the room's first control. So `buffer₂` excludes only the control at 6 at the start of the entering frame. Two designs of a walk that would follow the position over the coin's frame and the entering frame grew too large; the numbers are on that page. `buffer₂` is unchanged.

## Uses from other parts

* Part c: `RoomMap.cond_of_rows`, `RoomMap.stepT`, `RoomMap.s_stepT`, and through `Run.rt₂` the field `room.enters`, `Run.roomEnter`, `SideEntryEnd`, `SideEntryRest`.
* Part b: the rows of the first change at the room's first control (`ChangesK.run₁`, `inRowsT`), `ctl₁`, `ctlFirst₁`, `Run.entry₁`.
* No cycle: none of these uses `entry₂`.

## What changed in the route

* `Run.chg : ChangesK … (restIdxB sy nmS m0)`: 3 bytes at the side pipe's entry.
* `Run` has a new field `buffer₂`.
* `RoomChecks` has a new field `buffer : EntryBuffer.Facts …`, built from `buffer_facts` in the private files of the route (5 times) and of the hurry-up music (once).

Removed from the assumptions: the five bytes of the screen's buffer of `entry₂`, for a run whose entering frame starts with the control at 0. Added: `buffer₂`, which the old assumption implies.

## Assumptions (not proved in Lean)

* `buffer₂`: the entering frame starts with the control of the screen's buffers at 0, or the five bytes at the entry are those of a reference. Since round 23 the control there is proved to be 0 or 6 (`Run.ctl₂`), so this excludes only 6.
* `chg.entry₂`: 3 bytes at the entry have the values of a reference: the area music's buffer, the event music's queue, the added note length. They wait for the game timer (see [The music bytes through the room's frames](d-2-5-1-RoomMusic.md)).
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

**Files.** `Theorems/EntryBuffer.lean`, `Theorems/EntryHeight.lean`, `Theorems/Route.lean`, `Theorems/ScreenPage.lean` (one name); the private check is in `Proof/EntryHeight.lean` (`genEntryHeight` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta entry-height-check FM2 10 walkbuf    # the search and the check, with the control and without it, about 15 s
.lake/build/bin/smbrta entry-height-check FM2 400 real      # the table of real frames, about 3 min
```
