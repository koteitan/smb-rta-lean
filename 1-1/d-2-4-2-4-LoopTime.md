[← Back](README.md) | [English](d-2-4-2-4-LoopTime.md) | [Japanese](d-2-4-2-4-LoopTime-ja.md)

# The time of the room's frames from the loops' back jumps

**Claim.** On every frame of the room, every instruction away from the idle loop runs 6000 dots or more before the frame's end, if the loops' back jumps whose counts the walk does not know run at dot 9,000 or earlier: on the room's first frame and on the frames after a frame that starts with the control of the screen's buffers at 6 (the frames `U`), those of the screen update's loop over the buffer's records and of the sound routine; on the other frames, those of the sound routine.

This is proved, with one check on the ROM. Until round 29 the route asked `Late` (the dot at most `L` = 83,342 away from the idle loop) on every instruction of the frames `U` (the field `roomLate`), and on the other frames that every instruction of the sound routine's code runs at dot 9,000 or earlier (`roomLateS`). Now:

* `roomLate` is gone. In its place `roomLateU` asks, on the frames `U`, only the back jumps of the screen update's loop (2 instructions) and of the sound routine's code (89 instructions).
* `roomLateS` asks, on the other frames, only the back jumps of the sound routine's code, not every instruction of it.

At those few instructions the bound is 9,000, not `L`. So `roomLateU` asks more than `roomLate` there (a smaller dot), and nothing anywhere else.

**Also the coin's erase.** At the `STA (zp),Y` that erases a coin the walks know the pointer's high byte: the block buffers' page. So the erase writes in the RAM, at or past the block buffers' start; this is proved. The field `roomErase` now asks only the rest: the erase writes before the block buffers' end (`EraseEnd`). It was `Erase`: in the RAM, at or past the start, and before the end.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `pc`, `dot` are its program counter and its dot in the frame. `idle` is the idle loop. `snd`, `rep`, `upd` are the addresses of `SoundEngine`, `RepeatByte`, `UpdateScreen`. `rom(p)` is the ROM's byte at `p`. `A.hi` is the last dot that an abstract state allows. `U(n)`, `InPat`, `RestS`, `timeOK` are as in [The screen buffers' records](d-2-4-2-2-BufferRecords.md) and [The time of the room's frames](d-2-4-2-3-RoomLate.md).

## The statement

```
back(p)          :=  (rom(p) & 0x1F = 0x10  ∧  rom(p + 1) ≥ 0x80)            a relative branch with a negative offset
                   ∨ (rom(p) = JMP  ∧  rom(p + 1) + 256 · rom(p + 2) ≤ p)      a JMP to an address at or before p
sndQ(p)          :=  snd ≤ p  ∧  back(p)
scrQ(p)          :=  sndQ(p)  ∨  (rep ≤ p < upd + 16  ∧  back(p))
LateS(q, m)      :=  q(pc(m))  →  dot(m) ≤ 9,000
EraseEnd(m)      :=  pc(m) = erase  →  addr(m) & 0x7FF < bufLo + bufN          (addr(m): the address that the STA (zp),Y writes)
eraseOK(A)       :=  pc(A) ≠ erase  ∨  (the pointer's high byte h is known  ∧  256 h + 510 < 2048  ∧  bufLo ≤ 256 h  ∧  0x8000 ≤ pc(A) + 1)
erase_of_ok      :  Sim(A, m) ∧ eraseOK(A) ∧ EraseEnd(m)  →  Erase(m)
RestU(m)         :=  ReadsAt(Z₁, m) ∧ Read(m) ∧ EraseEnd(m) ∧ Xbit(m) ∧ LateS(scrQ, m)
RestB(m)         :=  LateS(sndQ, m) ∧ Read(m) ∧ EraseEnd(m) ∧ Xbit(m)

rec_frame1B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 0,  ∀ j, RestU(tr(j))
                    →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame2B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(0, L, m),  ∀ j, RestB(tr(j))
                    →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame3B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(6, L₆, m),  ∀ j, RestB(tr(j))   →   ∀ j, SiteOK(tr(j))
rec_frame4B      :  recCheckB(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  c(m) = 6,  ∀ j, RestU(tr(j)) ∧ Off(tr(j))   →   ∀ j, SiteOK(tr(j))

loop_sites_of_rows :
      the conditions of late_sites_of_rows, with recCheckB(T, L, L₆) in place of recCheckT(T, L, L₆),
      ∀ n ∈ [b, a), ∀ j,  Read(tr_n(j)) ∧ EraseEnd(tr_n(j)) ∧ Xbit(tr_n(j)),
      ∀ n ∈ [b, a),  U(n)  →  ∀ j, LateS(scrQ, tr_n(j)),
      ∀ n ∈ [b, a),  ¬U(n) →  ∀ j, LateS(sndQ, tr_n(j)),
      the fields of round 28 for Reads through the screen update's pointer (on U) and Off (from 6 after 6)
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))
```

The changed fields of `chg` (for every `n ∈ [b₁, a₂)` and every `j`):

```
roomLate   :  U(n)  →  Late(tr_n(j))                       removed
roomLateU  :  U(n)  →  LateS(scrQ, tr_n(j))                new
roomLateS  :  ¬U(n) →  LateS(sndQ, tr_n(j))                was: snd ≤ pc(tr_n(j)) → dot(tr_n(j)) ≤ 9,000
roomErase  :  EraseEnd(tr_n(j))                            was: Erase(tr_n(j))
```

`recCheckB` is `recCheck` of [The screen buffers' records](d-2-4-2-2-BufferRecords.md) with all four walks walked with the time (`RoomLate.walkST`): (ii) and (iii), from the buffers' patterns, clamp the last dot to 9,000 only at `sndQ`; (i) and (iv), from buffers that the walk does not know, only at `scrQ`. Each walk checks `timeOK` and `eraseOK` at every state, so `Late` holds on every instruction, and `Erase` wherever `EraseEnd` holds. `ChangesK.roomSites` uses `loop_sites_of_rows`; `BufferEnd.FactsE.music` asks `recCheckB`.

Lean: `Theorems/LoopTime.lean` (`backJ`, `sndQ`, `scrQ`, `EraseEnd`, `eraseOK`, `ptr_val`, `addr_page`, `and7FF_of_lt`, `erase_of_ok`, `chk1B`, `chk2B`, `chk4B`, `walk1B` to `walk4B`, `recSmall`, `recCheckB`, `recCheckB_of`, `RestU`, `RestB`, `rec_frame1B` to `rec_frame4B`, `loop_sites_of_rows`), `Theorems/RoomLate.lean` (round 30: `LateS`, `sclamp`, `walkST`, `searchST`, `cfgBT`, `walkCheckST`, `STOK`, `frameST` take a predicate on the program counter in place of the address `SoundEngine`; `sndAll` is round 29's predicate), private `Proof/SiteMusic1.lean` to `Proof/SiteMusic4.lean` (`buffer_walk1` to `buffer_walk4`, one walk each) and `Proof/SiteMusic.lean` (`buffer_records_small`; `buffer_records_check` is now `recCheckB`, from `recCheckB_of`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## How it works

**Where the time grows.** The walk adds each instruction's cycles to the last dot `hi`. It knows the count of most loops: a loop over a known index, or a wait for a flag of the picture (the read of the status splits the state at the flag's dot). Round 29 found that `hi` grows for ever only in loops whose count the walk does not know: in the sound routine (it follows the music data through a pointer and offsets it does not know), and, from buffers that the walk does not know, in the screen update's loop over the records.

**The clamp at the back jumps.** Every loop goes back somewhere: one of its instructions branches or jumps to an address at or before its own. So the walk clamps `hi` to 9,000 only at the instructions that `back` picks, in the sound routine's code and in the screen update's loop (`RoomLate.sclamp` with the predicate). Every path that goes around a loop passes such an instruction, so `hi` stays bounded, and the table closes. The predicate reads the ROM's bytes at the program counter; it lists no address. A data byte of the ROM may look like a back jump; that only asks the time at a place that never runs.

**The four walks.** (i) from the control at 0 with the buffers not known, (ii) from the patterns `L`, (iii) from the patterns `L₆`, (iv) from the control at 6 with the buffers not known. Measured (`buffer-ctl-check FM2 1 loopcheck`, with three other jobs running):

| walk | clamp | search: states | table | failing states | largest `hi` away from the idle loop | time |
|---|---|---|---|---|---|---|
| (i) | `scrQ` | 254,954 | 141,625 | 0 | 56,670 | 73 s |
| (ii) | `sndQ` | 137,426 | 60,571 | 0 | 56,670 | 46 s |
| (iii) | `sndQ` | 725,638 | 325,399 | 0 | 56,886 | 232 s |
| (iv) | `scrQ` | 412,437 | 255,489 | 0 | 57,237 | 134 s |

The largest `hi` is 57,237, so every path is done 26,000 dots before `L`. The ROM has 89 back jumps in the sound routine's code and 2 in the screen update's loop (the inner loop over a record's bytes and the loop over the records).

**Cost.** Round 29's `recCheckT` walked (i) and (iv) with the clamp to `L` and took about 165 s natively, in one private file (`Proof.SiteMusic`, about 180 s). `recCheckB` walks all four with the time, which takes more: in one file it took 456 s. So the private proof checks the four walks in four files (`Proof.SiteMusic1` to `Proof.SiteMusic4`, `recCheckB_of`) that lake builds at the same time: 62 s, 37 s, 150 s and 102 s in the last full build.

**The erase.** `writeAddr(m)` is the pointer plus Y (`RoomBlocks.writeAddr_eq`). If the high byte `h` is known and `256 h + 510 < 2048`, the pointer is at most `256 h + 255` and Y at most 255, so the address is in the RAM and at least `256 h` (`addr_page`; the pointer's value from its two bytes is checked by `decide` for all 7 · 256 pointers, `ptr_val`). Measured (`loopcheck 3`, from every state of the tables of walks (i) and (ii)): at the erase the walk meets 6 states, and all know the high byte; none knows its low byte or Y. At the block buffer's read (18 states) it is the same. The walk's `ADC` gives a result only when every bit of both values is known, and the player's position is not known, so the row's offset (Y) and the column (the low byte) are not known.

## Checked on real frames

`buffer-ctl-check FM2 1100 loopreal`: the largest dot of a back jump of the sound routine's code and of the screen update's loop, on the movie's room frames and on own runs from them (random inputs, 1,100 runs small and 1,100 big, up to 600 frames each).

| Run | Frames | Sound routine's back jumps (largest dot) | Screen update's loop's back jumps (largest dot, how many ran) |
|---|---|---|---|
| the movie in the room | 111 | 6,200 | 5,420 (404) |
| own runs, small | 578,997 | 6,784 | 6,008 (884,680) |
| own runs, big | 577,374 | 7,463 | 6,539 (895,399) |

So the two fields (9,000) hold on every measured frame; the margin is 1,537 dots on the big runs.

The same runs measure the three parts of `SiteOK` that stay fields. Every erase (13 on the movie, 4,802 small, 5,541 big) wrote in the first of the two block buffers, so far from the second buffer's end. At the side pipe's read of x (1, 316, 295 times) x was 195 to 197 px; its low four bits are 0 only at 208 px. Of the block buffer's reads (728, 1,973,613, 1,972,449) none read outside the block buffers or a tile not in the list, and none for the head read a tile other than 0 or a coin.

## Assumptions (not proved in Lean)

* **`roomLateU`** on the frames `U`: the back jumps of the screen update's loop over the records and of the sound routine run at dot 9,000 or earlier. The screen update's loop runs once per record and once per byte of a record; from buffers that the walk does not know it has no count. A proof needs the records the frame before wrote (round 28 tried an end class for the frames from the control at 6: the walk did not finish).
* **`roomLateS`** on the other frames: the back jumps of the sound routine run at dot 9,000 or earlier. A proof needs the song's state at each frame's start (round 6 measured 207 song states on real runs; a summary of the sound routine for any values of its bytes is false).

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 loopcheck     # the four walks with the time at the back jumps, natively (2 also runs recCheckB), about 8 min
.lake/build/bin/smbrta buffer-ctl-check FM2 3 loopcheck     # walks (i) and (ii): what the walk knows at the tile read, the coin's erase, the side pipe's read of x
.lake/build/bin/smbrta buffer-ctl-check FM2 1100 loopreal   # the dots of the back jumps on real frames, and the read, erase and xbit parts
```
