[← Back](README.md) | [English](d-2-4-2-5-EraseSplit.md) | [Japanese](d-2-4-2-5-EraseSplit-ja.md)

# The coin's erase in the first block buffer

**Claim.** On every frame of the room, the `STA (zp),Y` that erases a coin writes in the block buffers if its pointer is in the first of the two block buffers. Only an erase whose pointer is at or past the second block buffer's start is still asked to write below the block buffers' end.

This is proved, with one check on the ROM (the four walks of the room's frames). Until round 30 the field `roomErase` asked every erase to write below the block buffers' end (`EraseEnd`). Now it asks this only of an erase whose pointer is at or past the second block buffer's start (`EraseTwo`). On every measured frame every erase was through a pointer into the first block buffer (round 30: 13 on the movie, 4,802 and 5,541 on own runs).

`tr_n(j)` is the machine after `j` instructions of frame `n`. `pc(m)` is its program counter. `erase` is the place of that `STA (zp),Y`. `ptr(m)` is the 16-bit pointer that it reads from the zero page, and `addr(m)` = `ptr(m) + Y` is the address it writes. `bufLo` is the block buffers' start and `bufN` their length; the second block buffer starts at `bufLo + bufN/2`. For a byte `b` of an abstract state, `min(b)` and `max(b)` are its smallest and largest value with its known bits.

## The statement

```
EraseTwo(m)    :=  pc(m) = erase  →  bufLo + bufN/2 ≤ ptr(m) & 0x7FF  →  addr(m) & 0x7FF < bufLo + bufN
eraseOK2(A)    :=  eraseOK(A)  ∧  ( pc(A) ≠ erase
                                    ∨  256 · h + max(l) + 255 < bufLo + bufN
                                    ∨  bufLo + bufN/2 ≤ 256 · h + min(l) )
                   (l, h: the pointer's low and high byte in A; eraseOK as in round 30: h known, at most 6, and 256 · h ≥ bufLo)
erase_of_ok2   :  Sim(A, m) ∧ eraseOK2(A) ∧ EraseTwo(m)  →  Erase(m)
eraseTwo_of_end:  EraseEnd(m)  →  EraseTwo(m)

splitK(p, A)   :=  if pc(A) = p and A and Y have together at most 6 bits not known:
                     the states with each such bit of A and of Y set to 0 and to 1
                   else [A]
cov_splitK     :  Sim(A, m)  →  ∃ B ∈ splitK(p, A), Sim(B, m)          (and B keeps A's frame count and the counter's flag)
```

The changed field of `chg` (for every `n ∈ [b₁, a₂)` and every `j`):

```
roomErase  :  EraseTwo(tr_n(j))          was (round 30): EraseEnd(tr_n(j)),  pc = erase → addr & 0x7FF < bufLo + bufN
```

`EraseTwo` asks less than `EraseEnd`: it asks nothing of an erase through a pointer into the first block buffer (`eraseTwo_of_end`).

`RestU`, `RestB`, `rec_frame1B` to `rec_frame4B` and `loop_sites_of_rows` of [the loops' back jumps](d-2-4-2-4-LoopTime.md) are the same as in round 30 with `EraseTwo` in place of `EraseEnd`. `recCheckB` walks the four walks with the split.

## How it works

**The address of the erase.** The block buffer routine makes the pointer from the position: the column `c` (0 to 15) from x, and the buffer `t` (0 or 1, the first or the second block buffer) from the page's bit. The routine that makes the address loads the pointer's high byte from a table by `t` (the same in both rows: the block buffers' page) and adds `c` to the low byte of the buffer's start (`ADC abs,Y` with `Y = t`). The erase writes at the pointer plus the row's offset `Y` (0 to 255).

* In the first block buffer the pointer is at most 15 past its start, so the address is at most `bufLo + 15 + 255`, below the block buffers' end, for every `Y`.
* In the second block buffer the pointer is at most 15 past the second buffer's start, and the address is below the end only if the row's offset is at most 192. That needs the player's height, which the walks do not know.

**Why the walks did not know it.** The abstract machine's `ADC` gives a result only when every bit of both values is known. At that add the walk knows the high four bits of the accumulator (0) but not its low four bits (the column), and the high seven bits of `Y` (0) but not bit 0 (the buffer). So the low byte was not known at all: the walk allowed every low byte from 0 to 255.

**The split.** Before that add the walk splits the state by each bit of A and of Y that is not known (`splitK`): 2⁵ = 32 states, each a state of the machine's, so the split is sound (`cov_splitK`, from `PipeChangeEnd.cov_bitA`, `cov_bitY`). In each state the add is exact, and the low byte is known. The search joins states with the same key; its key (`EraseSplit.keyK`) also takes bit 7 of the pointer's low byte (and, at the store right after the add, bit 7 of the accumulator), so the two block buffers stay apart. Joined, the first buffer's states still know the low byte's high four bits, so they know that the pointer is at most 15 past that buffer's start.

**Measured** (`buffer-ctl-check FM2 1 splitcheck`, natively):

| walk | search: states | table (round 30) | failing states | time |
|---|---|---|---|---|
| (i) | 261,565 | 148,250 (141,625) | 0 | 77 s |
| (ii) | 143,770 | 66,917 (60,571) | 0 | 43 s |
| (iii) | 757,358 | 357,129 (325,399) | 0 | 349 s |
| (iv) | 422,531 | 265,619 (255,489) | 0 | 137 s |

The times are with three other jobs running. At the erase the walks (i) and (ii) meet 12 states (`buffer-ctl-check FM2 3 splitcheck`; round 30: 6, none knowing the pointer's low byte): 6 with the pointer at most 15 past the first block buffer's start, where `eraseOK2` holds for every `Y`, and 6 with it at most 15 past the second block buffer's start, where the field is asked. None knows `Y`. At the block buffer's read it is the same: 36 states, 18 and 18.

## Assumptions (not proved in Lean)

Round 32: the case left here is proved and `roomErase` is gone. The walks split the player's height in the collision routine, know bits 1 to 7 of the size at each frame's start, and so know the row's offset at every erase ([The row of the coin's erase](d-2-4-2-6-EraseRow.md)). The text below is round 31's.

* **`roomErase`** only for an erase whose pointer is at or past the second block buffer's start: that it writes below the block buffers' end. A proof needs the row's offset at most 192 (from the code's tests of the player's height before each call of the block buffer routine), so the player's height in the walk, or that the second block buffer is never used in the room (the player stays on page 0 at most 242 px from the left edge, a bound over frames). Measured (`buffer-ctl-check FM2 4 splitcheck`): the tables of walks (i) and (ii) have 5,302 states in the player's collision code (65 places), and none knows the player's height. Split into its values (up to 207 below the code's first test), that would be up to about 1.1 million more states per walk, which this round did not try.
* `roomRead` and `roomXbit` are unchanged. The split does not help them: `roomRead` needs the block buffers' contents (a bound over frames), and `roomXbit` needs x at most 207 px when the side pipe's code reads it (the player is not inside the pipe: a bound over frames).

## Lean

`Theorems/EraseSplit.lean` (`splitK`, `cov_splitK`, `SpentKeep`, `spent_splitK`, `walkK`, `LiveK`, `live_stepK`, `frame_of_walkK`, `keyK`, `bit7Key`, `bit7A`, `routeK`, `runK`, `searchK`, `searchBK`, `cfgBK`, `walkCheckK`, `KOK`, `kok_of_check`, `frameK`, `addrRoutine`, `adcAt`, `ptrKey`): the walk of `RoomLate` with the split before each step. `Theorems/LoopTime.lean` (round 31: `addr_val`, `EraseTwo`, `eraseTwo_of_end`, `eraseOK2`, `erase_of_ok2`; `chk1B`, `chk2B`, `chk4B` check `eraseOK2`; `walk1B` to `walk4B` are walks with the split). The private proofs are those of round 30 (`Proof/SiteMusic1.lean` to `Proof/SiteMusic4.lean`, `Proof/SiteMusic.lean`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 splitcheck    # the four walks with the split, natively (2 also runs recCheckB)
.lake/build/bin/smbrta buffer-ctl-check FM2 3 splitcheck    # walks (i) and (ii): what the walk knows at the erase and the read
.lake/build/bin/smbrta buffer-ctl-check FM2 4 splitcheck    # walks (i) and (ii): the table's states in the player's collision code
```
