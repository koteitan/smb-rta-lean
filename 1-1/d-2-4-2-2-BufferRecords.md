[← Back](README.md) | [English](d-2-4-2-2-BufferRecords.md) | [Japanese](d-2-4-2-2-BufferRecords-ja.md)

# The screen buffers' records: the screen update's reads and the buffer's offset in the room

**Claim.** On a frame of the room, the screen update reads the screen buffer that the frame before wrote. If the frame before started with the control of the screen's buffers at 0, the walk of that frame knows the records it wrote and the first buffer's offset it left. So on the next frame:

* every read of the screen update through its pointer into the buffer reads RAM;
* if the next frame starts with the control at 6, the first buffer's offset is below 64 wherever the code uses it.

This is proved, with one check on the ROM (four walks of the room's frame). Until round 27 the route asked `Reads` through the screen update's pointer on every frame of the room, and `Off` on every frame that starts with the control at 6. Now it asks:

* `Reads` through the screen update's pointer only on the room's first frame and on the frames after a frame that starts with the control at 6;
* `Off` only on the frames that start with the control at 6 after a frame that starts with it at 6.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `c(m)` is the control of the screen's buffers. `Z₁` is the screen update's pointer (`SiteParts.ptrS`). `Rest(Z, m)` is `Late ∧ ReadsAt(Z) ∧ Read ∧ Erase ∧ Xbit` at `m` ([The parts of `SiteOK`](d-2-4-2-1-SiteParts.md)). `Rest(∅, m)` asks no read.

## The statement

```
Pat(s, m)        :=  ∀ (i, v) ∈ s,  m.ram[i] = v                      (a pattern: some bytes with given values)
InPat(v, L, m)   :=  c(m) = v  ∧  ∃ s ∈ L,  Pat(s, m)
U(n)             :=  n = b  ∨  (b < n  ∧  c(seq(n − 1)) = 6)          (the room's first frame, or a frame after a frame from the control at 6)

rec_frame1 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 0,  ∀ j, Rest(Z₁, tr(j))
              →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame2 :  the same with InPat(0, L, m) in place of c(m) = 0, and Rest(∅, tr(j)) in place of Rest(Z₁, tr(j))
rec_frame3 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(6, L₆, m),  ∀ j, Rest(∅, tr(j))                →   ∀ j, SiteOK(tr(j))
rec_frame4 :  recCheck(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 6,  ∀ j, Rest(Z₁, tr(j)) ∧ Off(tr(j))      →   ∀ j, SiteOK(tr(j))

records_sites_of_rows :
      the conditions of RoomMap.map_of_rows on [b, a),  keepCheck,  startCheckC,  RoomMusic.Facts(T),  recCheck(T, L, L₆),  Room(seq b),
      ∀ n ∈ [b, a), ∀ j, Rest(∅, tr_n(j)),
      ∀ n ∈ [b, a),  U(n)  →  ∀ j, ReadsAt(Z₁, tr_n(j)),
      ∀ n ∈ (b, a),  c(seq n) = 6  ∧  c(seq(n − 1)) = 6  →  ∀ j, Off(tr_n(j))
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))
```

The two fields of `chg` that changed (for every `j`):

```
roomReads :  b₁ ≤ n < a₂  ∧  (n = b₁  ∨  (b₁ < n  ∧  c(seq(n − 1)) = 6))   →  ReadsAt(Z₁, tr_n(j))
roomOff₆  :  b₁ < n < a₂  ∧  c(seq n) = 6  ∧  c(seq(n − 1)) = 6           →  Off(tr_n(j))

until round 27:   roomReads :  b₁ ≤ n < a₂  →  ReadsAt(Z₁, tr_n(j))        roomOff₆ :  b₁ ≤ n < a₂  ∧  c(seq n) = 6  →  Off(tr_n(j))
```

`L` and `L₆` are lists of patterns, and `T` is the music's table. A program finds them; the check does not depend on how they were found.

* `L` has 6 patterns of the first buffer: no record; the colour record; the colour record with other colours; the timer's record; and two with both.
* `L₆` has 6 patterns: the first buffer's offset and records after a frame that took a coin (the coins' and the score's records, with the colour or the timer's record or neither), and the second buffer's two records of the blank block that the erase of a coin writes.

There are no byte values on this page; the private proof lists them.

Lean: `Theorems/BufferRecords.lean`:

* patterns: `Pat`, `knowsPat`, `refPat`, `knownPat`, `patOK`, `cond_pat`, `pat_of_knows`;
* the classes at a frame's end: `ctlIs`, `anyPat`, `fin0`, `InPat`, `end0`;
* one frame with its end: `frame_of_walkPCE`;
* the walks: `preWalk`, `searchB`, `cfgB` (no part of the proof), `walkCheckB`, `BOK`, `bok_of_check`, `frameB`;
* on the ROM: `fpcOf`, `ptrBytes`, `noRegs`, `zO`, `zOC`, `walk1` to `walk4`, `recCheck`, `rec_frame1` to `rec_frame4`;
* the room's frames: `U`, `records_sites_of_rows`.

`Theorems/Route.lean`: the fields `roomReads`, `roomOff₆`, `ChangesBase.roomRest` (now `Rest(∅)`), `ChangesK.roomSites`. `Theorems/BufferEnd.lean`: `FactsE.music` (now with `recCheck` and the two lists). The private check is `buffer_records_check` in `Proof/SiteMusic.lean`; the lists `recL0`, `recL6` are in `Proof/RoomPause.lean`.

## How it works

**The classes of a frame's start.** A frame that starts with the control at 0 starts with a screen update that draws the first buffer, sets the first buffer's offset to 0 and puts an end mark at its start. Then the code of the frame writes records into the first buffer: a header of 3 bytes (the place on the screen and the length) and the data. The headers come from the ROM. The walk of `RoomMusic` from the control at 0 keeps states with different offsets apart, so the walk knows every header, the end mark and the offset at the frame's end. If the frame erases a coin, it also writes two records of a blank block into the second buffer at a fixed place, and sets the control to 6. So every frame from the control at 0 ends in one of two classes (`fin0`):

* `InPat(0, L, ·)`: the control at 0, and the first buffer's headers and end mark as a pattern of `L`;
* `InPat(6, L₆, ·)`: the control at 6, and the first buffer's offset, its headers and end mark, and the second buffer's headers and end mark as a pattern of `L₆`.

**The screen update from a pattern.** The next frame's screen update reads the buffer of its class (the first at 0, the second at 6). With the pattern known, the walk knows the length of each record, so it knows the pointer after each record, and every read through the pointer is a read of the RAM (the read's check `SiteParts.readsOK` with no pointer left out). A frame from the control at 6 does not reset the first buffer's offset. From a pattern of `L₆` the walk knows that offset, and with the offset kept apart it knows it below 64 wherever the code uses it (`SiteParts.offOK`).

**Four walks** (`recCheck`), each the walk of `RoomMusic` with a check at every state (`SiteParts.walkPC`):

| walk | start | the check at each state | at the frame's end | table | natively |
|---|---|---|---|---|---|
| (i) `walk1` | control 0, buffers not known | the offset below 64; reads, but through `Z₁` | `fin0` | 78,693 states | 18 s |
| (ii) `walk2` | the 6 patterns of `L`, control 0 | the offset below 64; every read | `fin0` | 32,154 states | 8 s |
| (iii) `walk3` | the 6 patterns of `L₆`, control 6 | the offset below 64; every read | nothing | 182,438 states | 44 s |
| (iv) `walk4` | control 6, buffers not known | reads, but through `Z₁` | nothing | 216,532 states | 38 s |

Walks (i) and (iv) are those of round 27 (`SiteParts.musicCheck`); walk (i) now also checks `fin0` at the frame's end. The search of walks (i), (ii) and (iii) keeps the first buffer's offset apart; that of (iii) also keeps the control apart.

**Two details of the walks from a pattern.** The search of walks (ii) and (iii) would join the states of the screen update's loop at its head and lose the pointer. So each start is first walked alone through the screen update (`preWalk`). The search starts after it, at the place after the call of the screen update (`fpcOf`). There the walk forgets the pointer's two bytes (`ptrBytes`), so the states join again. The aids of the search list three places in the screen update where the registers are forgotten. The walks from a pattern use no such place (`noRegs`): there the walk keeps the record's length in a register. Since their search starts after the screen update, nothing else changes.

**The frames in order.** `records_sites_of_rows` takes the room's frames one after another, as `SiteParts.music_sites_of_rows` did, and carries one more thing: the class of the frame's start. The room's first frame is in `U`. A frame from the control at 0 gives the next frame `InPat(0, L, ·)` or `InPat(6, L₆, ·)` (walks (i), (ii)). A frame from the control at 6 gives nothing (walks (iii), (iv)), and the next frame is in `U`. So every frame is in one of the three:

* `InPat(0, L, ·)`: walk (ii), from `Rest(∅)` alone;
* `InPat(6, L₆, ·)`: walk (iii), from `Rest(∅)` alone;
* `U` and the control at 0: walk (i), from `Rest(Z₁)`, that is, with the field `roomReads`;
* `U` and the control at 6: walk (iv), from `Rest(Z₁)` and `Off`. Here the frame before started with the control at 6 (the room's first frame starts at 0), so the field `roomOff₆` applies.

**Size.** The check is about 111 s natively; round 27's `musicCheck` (walks (i) and (iv) only) was about 65 s. The private proof `Proof.SiteMusic` runs this check. This is more than a few seconds.

## Why the frames after a frame from the control at 6 stay

A frame that starts with the control at 6 draws the second buffer and does not reset the first buffer's offset. Its records go after those that the coin frame left. Walk (iii) knows them, but a frame can end in many ways, and the frame after it reads all of them. With the end's patterns of walk (iii) added to `L` (29 more patterns, 35 in all), walk (ii) did not end in 20 minutes, so walk (iii) asks nothing at the frame's end. Walk (iv) starts with nothing known of the buffers: it does not know the first buffer's offset, and in the walk the records of a frame may reach past the first buffer into the second. Measured: in the walk of `BufferControl`, which does not keep the offset apart, no frame that ends with the control at 6 knows a byte of the second buffer. So for these frames a proof needs a bound on the offset over several frames: the number of coins taken in a row, from the position.

## Measured, not a theorem

`buffer-ctl-check FM2 100 recreal` (exit 0): the class of each frame's start on real frames of the room: the movie's frames, and own runs from them, small and big, 100 each (as `sites`). A frame after a frame from the control at 0 must start in a pattern; the theorem says so, and the runs agree.

| frames | in a pattern of `L` | in a pattern of `L₆` | the room's first | after a frame from 6 (`roomReads` asked) | of them at 6 too (`roomOff₆` asked) | after a frame from 0 but in no pattern |
|---|---|---|---|---|---|---|
| the movie: 111 frames of the room before the entering frame | 87 | 10 | 1 | 13 | 3 | 0 |
| own runs, small: 100 runs, 51,791 frames | 50,868 | 422 | – | 501 | 69 | 0 |
| own runs, big: 100 runs, 55,755 frames | 54,798 | 428 | – | 529 | 92 | 0 |

So on the movie the route now asks `Reads` through the screen update's pointer on 14 of the 111 frames (until round 27: all 111), and `Off` on 3 (until round 27: 13). The own runs start from frames of the movie in the room, so none of them is the room's first frame.

## Uses from other parts

* Part c: `RoomMap.cond_of_rows`, `RoomMap.room_stepT`, `MapFacts`, `startCheckT` (through `SiteParts.cond_at`); `ChangesBase.roomStay`, `ChangesK.roomAt`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`; `SideChangeEnd.ptrHiOK`, `wide_ok` (through `SiteParts.reads_of_ok`).
* Part d: `SiteParts` (`walkPC`, `live_stepPC`, `chkP_of_walk`, `chk0`, `readsOK`, `reads_of_ok`, `off_of_ok`, `siteOK_of_rest`, `knownMC`, `keepOff`, `ptrS`); `BufferControl` (`keepCheck`, `startCheckC`, `ctl_of_rows`, `start_ctl`, `cond0`, `cond6`, `ref6`); `RoomMusic` (`Facts`, `regM`, `knownM`, `start_of_invL`, `roomCond_append`); `RoomPause` (`pstep`, `searchP`, `routeP`, `aidsP`, `keyP`, `pause_step`, `InCls`, `Ph`); `StepWrites.tabOK`.
* No cycle: none of these uses `roomSites` or `Run.roomSites`; `ChangesK.roomSites` uses only the fields `roomLate`, `roomReads`, `roomRead`, `roomErase`, `roomXbit`, `roomOff₆`, `ctl₁`, `ctlFirst₁`, the rows of the first change and the checks.

## What changed in the route

* Fields narrowed: `roomReads` (only on the room's first frame and on the frames after a frame from the control at 6) and `roomOff₆` (only on the frames from the control at 6 after a frame from the control at 6).
* `RoomChecks.buffer` (`BufferEnd.FactsE.music`): `∃ T L₀ L₆, RoomMusic.Facts(T) ∧ recCheck(T, L₀, L₆)` in place of `∃ T, RoomMusic.Facts(T) ∧ musicCheck(T)`.
* One theorem's conclusion changed: `ChangesBase.roomRest` now gives `SiteParts.Rest []` (was `Rest ptrS`); its only user is `ChangesK.roomSites`. `route_1_1` still concludes `1748 + j ≤ L`.

## Assumptions (not proved in Lean)

* `Reads` through the screen update's pointer on the room's first frame and on the frames after a frame that starts with the control at 6.
* `Off` on the frames that start with the control at 6 after a frame that starts with it at 6.
* `Late`, `Read`, `Erase`, `Xbit` on each instruction of the room's frames, as before.
