[← Back](README.md) | [English](d-2-4-2-6-EraseRow.md) | [Japanese](d-2-4-2-6-EraseRow-ja.md)

# The row of the coin's erase

**Claim.** On every frame of the room, the `STA (zp),Y` that erases a coin writes in the block buffers.

Round 33: the route's walks no longer use the split of this page; they keep bounds on the height and the row instead, with the same result and tables two to three times smaller: [The erase's row from bounds](d-2-4-2-7-EraseRange.md).

This is proved, with one check on the ROM (the four walks of the room's frames). The field `roomErase` is gone. Until round 31 it asked that an erase whose pointer is at or past the second block buffer's start writes below the block buffers' end (`EraseTwo`). On every measured frame every erase was through a pointer into the first block buffer (round 30: 13 on the movie, 4,802 and 5,541 on own runs), so the field was never used on a real run.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `pc(m)` is its program counter. `erase` is the place of that `STA (zp),Y`. `ptr(m)` is the 16-bit pointer that it reads from the zero page, `Y` is the row's offset, and `addr(m)` = `ptr(m) + Y` is the address it writes. `bufLo` is the block buffers' start and `bufN` their length. `y` is the player's height on the screen, `size` the size byte (0 big, 1 small), `crouch` the crouch byte. For a byte `b` of an abstract state, `max(b)` is its largest value with its known bits.

## The statement

```
eraseOK4(A)    :=  eraseOK(A)  ∧  ( pc(A) ≠ erase  ∨  256 · h + max(l) + max(Y) < bufLo + bufN )
                   (l, h: the pointer's low and high byte in A; eraseOK as in round 30: h known, at most 6, and 256 · h ≥ bufLo)
erase_of_ok4   :  Sim(A, m) ∧ eraseOK4(A)  →  Erase(m)

splitR2(A)     :=  at yAt:  y by the steps of ySteps (the pieces 0–7, 8–15, 16–31, 32–63, 64–127, 128–191, 192–207, 208–223, 224–255 px),
                            bit 0 of size, and crouch by its lowest set bit (a piece for each bit that may be the lowest set one, and one with all bits 0);
                   at adcY and at adcAt:  A and Y by their bits not known (splitK, round 31)
cov_splitR2    :  Sim(A, m)  →  ∃ B ∈ splitR2(A), Sim(B, m)          (and B keeps A's frame count and the counter's flag)

knownS         :=  the bits of knownMC, and bits 1 to 7 of size
```

`yAt` is the collision routine's first load of `y`, `adcY` the block buffer routine's add of the row's adder (`ADC abs,Y`), `adcAt` round 31's add of the pointer's low byte. All three are found from the ROM's bytes.

The four walks of `LoopTime.recCheckB` now start from states that know `knownS` and split by `splitR2` before each step (`EraseRow.walkG`, `frameG`). The frame theorems `rec_frame1B` to `rec_frame4B` take one more condition on the frame's start:

```
hz  :  size(m) & 0xFE = 0                              (bits 1 to 7 of the size are 0)
```

`loop_sites_of_rows` proves it at each frame `n` of the room from the frames before it: they meet `SiteOK` (the induction), so the room's walk that keeps the size byte (`SizeKeep.byte_all`, round 22) gives `size(seq n) = size(seq b₁)`, and that is the reference's (small) or 0 (`SizeKeep.size_of_rows`). The new conditions of `loop_sites_of_rows` are the two walks of `SizeKeep` (`RoomChecks.height.keepR`, `keep0`) and the size at the room's first control. No field is used for them.

The removed field of `chg`:

```
roomErase  :  ∀ n ∈ [b₁, a₂), ∀ j,  EraseTwo(tr_n(j))
              EraseTwo(m) := pc(m) = erase → bufLo + bufN/2 ≤ ptr(m) & 0x7FF → addr(m) & 0x7FF < bufLo + bufN
```

No field is added. `ChangesBase.roomRest` now gives `Read ∧ Xbit`. `RestU` and `RestB` lose their part `erase`.

## How it works

**The row's offset.** The block buffer routine computes the row's offset from the height: `Y = ((y + adder) & 0xF0) − 32` (8 bits), where `adder` is read from a table by the call's offset. For a pointer into the second block buffer (at most 15 past its start) the erase is below the block buffers' end exactly when `Y ≤ 192`. The collision routine tests `y` before each call:

* at its start, `y < 207`;
* before the head's call, `y ≥` the upper extent, read from a table by `size` (plus one when crouching): 32 px for a big player who does not crouch, 16 px for a small player or a crouching big one (a small crouching player, which the game does not make, would read the byte after the table);
* before the feet's calls `y < 207` again, and the feet's adder is 32;
* before the first side call `32 ≤ y < 228`, before the second `8 ≤ y < 208`, with adders of 8 or 24.

Since `y < 207` in the whole routine and every adder is at most 32, `Y > 192` only when `y + adder < 32`, and the tests exclude that. So `Y ≤ 192` at every call if the walk knows enough of `y`, of `size` and of `crouch`.

**What the walk did not know.** A branch on a flag that the walk does not know splits the flag only: the walk did not learn the tested byte. The `ADC` gives a result only when every bit of both values is known. The room's walks knew neither `y` nor `size` nor `crouch`. Also the search forgot the block buffer routine's adder offset at the feet's check, so the walk did not know `Y` there.

**The split.** At `yAt` the walk splits `y` into nine pieces whose known bits decide every test of the routine: the bounds 8, 16, 32, 207, 208 and 228 each fall at a piece's edge, or both sides of the test are harmless. It splits bit 0 of `size` and `crouch` by its lowest set bit, so that every test of `crouch` is known and the head's upper extent is known. Before the add of the row's adder it splits the accumulator (`y`) by its bits not known, so the sum is exact and `Y` is known. The splits are covers of every machine of the state (`cov_splitR2`, from `TaintRun.cov_bit`).

**Bits 1 to 7 of the size.** If `size` could be any byte, the head's upper extent would be read from bytes after the table, and a small `y` could reach the head's call. So the walks start knowing that bits 1 to 7 of `size` are 0. Each frame's start has this from the frames before it, by the walk of round 22 that keeps the size byte through the room's frames (it needs `SiteOK` on those frames: so it is taken inside the same induction over the frames, and there is no cycle).

**The search** (no part of the proof: the walk checks the table) keeps the pieces apart while `y`'s high bits are known: by `y`'s known bits from bit 3 up, the two high bits of `Y`, and the classes of `crouch` and of `size`'s bit 0 (`EraseRow.rowKey`). It keeps the adder offset through the routine's checks (`EraseRow.aidsR`). It forgets `y`, the adder offset and `Y` at the routine's return and after the erase, and `crouch` and `size` after the head's test (`EraseRow.forgetAt`). A join of offsets with the same two high bits keeps a bound on them (at most 48, 112, 176 for 00, 01, 10); the walk passes, so at every erase the state knows `256 · h + max(l) + max(Y)` below the block buffers' end.

**Measured** (`buffer-ctl-check FM2 31 rowcheck` to `34`, one walk each, natively, the four at the same time; each time is the search and the walk's check):

| walk | table (round 31) | of it in the collision routine with `y`'s high bits known | failing states | time |
|---|---|---|---|---|
| (i) | 320,474 (148,250) | 183,921 | 0 | 187 s |
| (ii) | 239,141 (66,917) | 183,921 | 0 | 162 s |
| (iii) | 1,218,249 (357,129) | 919,605 | 0 | 901 s |
| (iv) | 337,408 (265,619) | 183,921 | 0 | 200 s |

The search takes almost all the time (walk (iii): 803 s of 901 s). Two first tries cost more or failed, and are not used: with `y`'s four high bits split and the row's offset kept exactly, walk (ii)'s search had 569,234 states (round 31: 143,770) and walk (iii)'s grew past 5.6 GB; and walk (iv) first failed at 5 table states, because the search joined a frame's start (dot 0) with the idle loop after the game logic, where the size is forgotten, so the joined state allowed a second interrupt in the same frame with the size not known. The search now keeps the states whose first dot is below 10 apart.

## Assumptions (not proved in Lean)

* None new. `roomRead` and `roomXbit` are unchanged (see below).
* `roomRead` needs the block buffers' contents on every instruction (a bound over frames: `RoomBlocks` gives them from `Run.roomSites`, so it would have to be taken in the same induction) and, at the head's read, the tile above the head (the room's geometry). The new splits do not give the buffers' contents.
* `roomXbit` needs `x ≤ 207` px when the side pipe's code reads `x` (the player is not inside the pipe: a bound over frames). The walks do not know `x`.

## Lean

`Theorems/EraseRow.lean` (`splitIf`, `ySteps`, `splitY`, `zsplitL`, `splitR2`, their `cov_*` and `spent_*`, `walkG`, `LiveG`, `live_stepG`, `frame_of_walkG`, `keyR`, `normR`, `advR`, `routeR`, `runR`, `searchR`, `searchBR`, `cfgBR`, `walkCheckR`, `GOK`, `gok_of_check`, `frameG`, and on the ROM `yAt`, `adcY`, `hcAt`, `yIdx`, `sizeIdx`, `crouchIdx`, `rowIdx`, `sideIdx`, `splitRom`, `bitC`, `lowC`, `rowKey`, `aidsR`, `passAt`, `forgetAt`). `Theorems/LoopTime.lean` (round 32: `eraseOK4`, `erase_of_ok4`, `chk1R`, `chk2R`, `chk4R`, `walkChk`, `knownS`, `starts0S`, `starts6S`, `sizeCheck`, `size_parts`, `cond_size`, `walk1B_parts`; `walk1B` to `walk4B`, `RestU`, `RestB`, `rec_frame1B` to `rec_frame4B`, `loop_sites_of_rows` changed). `Theorems/Route.lean`: `roomErase` removed, `ChangesK.roomSites` passes the size's facts. The private proofs are those of round 30 (`Proof/SiteMusic1.lean` to `Proof/SiteMusic4.lean`, `Proof/SiteMusic.lean`) with the same text. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 rowcheck     # the four walks with the height's split, natively (2 also runs recCheckB)
.lake/build/bin/smbrta buffer-ctl-check FM2 11 rowcheck    # walk (i) alone (12, 13, 14: walk (ii), (iii), (iv); 31 to 34 the same)
```
