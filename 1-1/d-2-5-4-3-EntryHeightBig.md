[← Back](README.md) | [English](d-2-5-4-3-EntryHeightBig.md) | [Japanese](d-2-5-4-3-EntryHeightBig-ja.md)

# The height at the side pipe's entry for a big player

**Claim.** A frame of the room that starts with a big player (the size byte 0) and ends with the side pipe's routine ends with the height of the reference entry (176 px). This is proved, with one check on the ROM (a walk of the room's frame). So the field `height₂` of `Route.Run` is narrower: it no longer asks the height of a run whose entering frame starts with a big player. It still asks it when the size byte at that frame's start is neither the reference's (small) nor 0.

The old walk of [the height](d-2-5-4-EntryHeight.md) with a big player had 8 frame ends at 192 px. Its abstract machine does not know the height when the head is read, so it does not know which cell the head reads. The new walk knows it on the frames that could end at 192 px. On those frames the head reads a cell of the pipe or of the floor, and `SiteOK` allows only 0 or a coin there. So no frame ends at 192 px.

`m[i]` is the RAM byte `i` of `m`, `frame(m, i)` one frame of `m` with the input `i`, `tr(j)` the machine `j` instructions into it, `step(m)` one instruction. `rt`, `y`, `x`, `pg`, `size` are the routine byte, the height, the horizontal position, the page and the player's size. `e_s` is the side pipe's routine, `y_e` the height of the reference entry (176 px), `d_L` the landing's depth (the ROM's `LandDepth`, 5). `r` is the room's reference machine (a small player) and `r_B` the same machine with 0 in the size byte. `K_T` is the bits of [The block map in the room](c-7-12-RoomMap.md), `K_Y := K_T ∪ { every bit of size }`. `map` is the block map of the room, `coins` its coin tile.

## The statement

```
band(y)          :=  y_e + 16 ≤ y < y_e + 16 + d_L                       (192 ≤ y < 197)
Solid(m)         :=  ∀ d in the block buffers,  map[d] ∉ coins  →  m[d] = map[d]
finY(B)          :=  B knows rt ≠ e_s   ∨   B knows y = y_e
WalkOKB          :=  the new walk from the start states of RoomCond(r_B, K_Y) passes, and every frame end meets finY

adc0_a           :  the instruction at pc(m) is ADC #0,  carry(m) = 0     →   a(step(m)) = a(m)
s_stepB          :  A covers m,  SiteOK(m),  Solid(m)     →   a successor of stepB(A) covers step(m)
height_frameB    :  WalkOKB,  RoomCond(r_B, K_Y, m),  ∀ j, SiteOK(tr(j)),  ∀ j before the frame's end, Solid(tr(j)),  rt(frame(m, i)) = e_s
                       →   y(frame(m, i)) = y_e
height_of_rowsB  :  the hypotheses of RoomMap.map_of_rows on [b, a),  the checks,  b ≤ k < a,  size(seq k) = 0,  rt(frame(seq k, inp k)) = e_s
                       →   y(frame(seq k, inp k)) = y_e

Run.height₂      :  size(seq(a₂ − 1)) = size(r)   ∨   size(seq(a₂ − 1)) = 0   ∨   y(seq a₂) = y_e        (field, narrowed)
Run.y₂           :  y(seq a₂) = y_e                                                                   (theorem)
```

**`Run.y₂`.** Frame `a₂ − 1` is a frame of the room that ends with the side pipe's routine (`Run.b₁_lt_a₂`, `Run.rt₂`). If it starts small, `EntryHeight.height_of_rows` gives the height. If it starts with the size 0, `height_of_rowsB` gives it; `Solid` on each instruction comes from `RoomBlocks.blocks_run_trace`. Else `height₂` gives it.

Lean: `Theorems/EntryHeightBig.lean` (`HB`, `meets`, `band`, `bits`, `inBand`, `zoneB`, `preB`, `refineA`, `ptrLo`, `ptrHi`, `readAd`, `readI`, `solidAt`, `stepB`, `walkB`, `keyB`, `normB`, `optsB`, `runB`, `searchB`, `searchOfB`, `cfgOfB`, `adcOK`, `walkCheckB`, `cov_band`, `bits_ok`, `cov_zoneB`, `cov_preB`, `op_69`, `adc0_a`, `AdcOK`, `adcOK_spec`, `s_stepB`, `LiveB`, `cover_liveB`, `PlB`, `live_stepB`, `frame_of_walkB`, `WalkOKB`, `walkOKB_of_check`, `frame_endB`, `height_frameB`, `hbOf`, `hbOf_H`, `hbOf_coins`, `hbOf_map`, `hpOf_P`, `refB`, `checkB`, `cond_ref`, `Facts`, `factsOf`, `height_of_rowsB`), `Theorems/Route.lean` (`RoomChecks.height`, `Run.height₂`, `Run.y₂`), private `Proof/EntryHeight.lean` (`entry_height_big`, `height_facts`). There is no game data in the public files.

## How it works

The walk is that of [the height](d-2-5-4-EntryHeight.md) (`EntryHeight.preY`, `EntryHeight.stepY`) with two more splits and two more kinds of steps. Every split covers every machine (`cov_zoneB`), with no hypothesis.

* **The band.** Where the collision routine first reads the height (before the compare of the head's check), the height is split bit by bit from the top, as long as the piece can still hold a value of `band` (`band`). There are 12 pieces. In the 5 pieces of the band the height is known; in the others it is not, and they cannot land on the row of 192 px.
* **The position.** At the head's call of the block buffer routine, when the height is known and in the band: the horizontal position (256 values) and bit 0 of the page. Then the head's cell and the side reads' cells are known on the same piece.
* **The page's `ADC #0`.** The block buffer routine adds the carry to the page with `ADC #0`. The abstract `ADC` knows nothing when a byte is not known. When the carry is known to be 0, the new step keeps the page in the accumulator (`refineA`, `adc0_a`). So the half of the block buffers is the same for the head's read and the side reads.
* **The read with the place known.** At the block buffer routine's read with the pointer and Y known, of a byte of the block buffers that is not a coin in the map, the step reads the map's byte (`Solid` on that instruction). If `SiteOK` does not allow that byte there, the piece has no machine (`stepB`, the empty list): a head read finds only 0 or a coin (`SiteOK.read`). The floor and the pipe are neither.

**The search (no part of the proof).** The key has the position and the page, so the 512 pieces are not joined again before the collision routine returns; there they are forgotten (`normB`). The key's position and page lie below bit 512, because the queue keeps only the low 512 bits of a key.

**Size.** 8,326,333 steps, 264,339 forks, 0 failures, 1,267,661 states; 272 frame ends, 64 with the side pipe's routine, all at 176 px. In a program: the search 44 s, the check 324 s.

## Measured on the way, not theorems

* A walk with the size not known (`RoomMap.knownT`, the size split at the collision routine's start) did not pass: 11,770,114 steps, 34 failures, 68 ends at 192 px. The size was joined again before the head's check reads it. With the size in the key the search ran over 11 minutes and was stopped. So `height₂` keeps the other values of the size byte.
* The splits at the head's call alone are not enough: the head's check compares the height before the call, and with the height not known the walk skips the head's read. So the band is split before that compare.
* A first measurement with 0 failures was wrong: its key put the position above bit 512, and the queue lost states. It is not used.

## Checked on real frames

See [the height](d-2-5-4-EntryHeight.md): `entry-height-check FM2 5 real` and `50 real` check `height₂` on the TAS and on own random runs, small and big; the new field is weaker than the old one, so each run that met the old field meets it. `route-check` on the TAS also passes.

## Uses from other parts

* Part c: `RoomMap.cond_of_rows`, `RoomMap.s_stepT` (through `EntryHeight.s_stepY`), `RoomBlocks.blocks_run_trace` with its checks `BChecks` and `rowsCheckR` (the map's bytes on each instruction of the room's frames), `RoomBlocks.readAddr_eq`, `RoomBlocks.readVal_eq`, `RoomBlocks.tick_a`.
* Part d: `EntryHeight` (its walk's pieces and steps, `refsCheck`).
* Part b: the rows of the first change at the room's first control (`ChangesK.run₁`, `inRowsT`), `ctl₁`, `ctlFirst₁`, `Run.entry₁`, through `Run.y₂` as before.
* No cycle: `RoomBlocks.blocks_run_trace` uses `roomSites`, `roomStay`, `ctl₁` and the rows of the first change; none of them uses `height₂` or `entry₂`.

## What changed in the route

* `Run.height₂` has a new middle disjunct, `size(seq(a₂ − 1)) = 0`. The old field implies the new one.
* `RoomChecks.height` is now `EntryHeightBig.Facts`: the facts of `EntryHeight`, the check `checkB`, and the checks of `RoomBlocks`.

Removed from the assumptions: the height at the side pipe's entry of a run whose entering frame starts with a big player. Added: nothing.

## Assumptions (not proved in Lean)

* `height₂` for the other values of the size byte (neither the reference's nor 0) at the start of the entering frame.
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

## Time

`Proof/EntryHeight.lean` now also runs `checkB` natively. It built in 355 s in the full `prove.py` of round 21 (about 45 s before, with the small player's walk only). In a program `checkB` alone takes 324 s (the search 44 s, then the walk over the table). This is much longer than a few seconds.

**Files.** `Theorems/EntryHeightBig.lean`, `Theorems/Route.lean`; the private check is in `Proof/EntryHeight.lean` (`genEntryHeight` in `Main.lean`). The program `entry-head-diag check 0` runs the search and the check.
