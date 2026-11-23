[← Back](README.md) | [English](d-2-4-2-8-ReadTiles.md) | [Japanese](d-2-4-2-8-ReadTiles-ja.md)

# The block buffers' tiles at the read

**Claim.** On every instruction of every frame of the room, the block buffer routine's read reads a tile of the list. The walks of the room's frames prove
it from two facts: every byte of the two block buffers is a tile of the list, and the read's address is in the block buffers. So the field `roomRead` asks
only its half for the head: a read for the head gives the empty tile or a coin.

This is proved, with checks on the ROM in the private proofs that already exist (the four walks of `LoopTime.recCheckB` and `RoomMap.startCheckT`; no new
private file). The field `roomRead` is narrowed. No field is added.

Round 35: the field `roomRead` no longer asks the byte read for the head. It asks only that the head's cell is free in the map; the walks also carry the map's
bits, and the byte read follows ([The head's read from the head's cell in the map](d-2-4-2-10-HeadFree.md)).

`tr_n(j)` is the machine after `j` instructions of frame `n`. `B` is the set of the 416 bytes of the two block buffers, `T` the list of the tiles
(`P.tiles`: the tiles of the block buffers of the reference machine, and the empty tile; 12 tiles on this ROM). `read` is the block buffer routine's
`LDA (zp),Y`, `addr(m)` its address, `val(m)` the byte it reads, `save(m)` the byte where the routine keeps its offset, `heads` the head's offsets and
`T_head` the empty tile and the coin. `m(d)` is the RAM byte `d` of `m`.

## The statement

```
TilesIn(m)  :=  ∀ d ∈ B,  m(d) ∈ T
ReadIn(m)   :=  pc(m) = read  →  addr(m) < 0x2000  ∧  (addr(m) & 0x7FF) ∈ B
ReadH(m)    :=  pc(m) = read  →  save(m) ∈ heads  →  val(m) ∈ T_head
Read(m)     :=  pc(m) = read  →  val(m) ∈ T  ∧  (save(m) ∈ heads → val(m) ∈ T_head)          (SiteParts.Read, as before)

read_of        :  TilesIn(m) ∧ ReadIn(m) ∧ ReadH(m)  →  Read(m)
tiles_step     :  0 ∈ T,  Sim(A, m),  keepOKB(A),  SiteX(m),  TilesIn(m)   →   TilesIn(step(m))
                  (SiteX(m) is SiteOK(m) without its part for the position's bit (1-1-d-2-4-2-9))
readIn_of_ok   :  Sim(A, m),  FOK(A.log, m),  readInOK(A)   →   ReadIn(m)
tiles_of_rows  :  startCheckT,  InRowsT(m),  control(m)   →   TilesIn(m)
frameVI        :  frameV with an invariant I:  I(tr 0),  (the check of each state and I(tr j)  →  I(tr (j + 1)))   →   ∀ j, I(tr j)
```

The checks of one abstract state `A`:

```
keepOKB(A)   :=  the step of A writes no byte of B  (StepWrites.keepOK)
                 ∨  A is at the coin's erase, not at an interrupt, its operand in the ROM, and A knows the accumulator = 0
readInOK(A)  :=  pc(A) ≠ read
                 ∨  the pointer's high byte h is known,  256·h + 510 < 2048,
                    bufLo ≤ 256·h + min(l),   256·h + max(l) + max(Y) < bufLo + |B|
```

`l` is the pointer's low byte as `A` knows it, and `max(Y)` is the largest `Y` that `A`'s known bits and bounds allow (`EraseRange.rhi` of `yI`).

In `Route.ChangesBase` the field changes:

```
before   roomRead : ∀ n ∈ [b₁, a₂), ∀ j,  Read(tr_n(j))
now      roomRead : ∀ n ∈ [b₁, a₂), ∀ j,  ReadH(tr_n(j))
```

## How it works

**The tiles stay.** At the room's first control the rows of the change into the room know every byte of the block buffers (416 of 416). `RoomMap.startCheckT`
now also checks that, in every state of the rows that has control, every byte of `B` is known and is a tile of `T` (`tileRow`). The rows are computed once for
both checks. Then each step keeps `TilesIn`: a step that writes no byte of `B` keeps them all; the coin's erase `STA (zp),Y` writes the accumulator at its
address (`erase_ram`, from the CPU's code of the opcode), and the accumulator is 0 there, the empty tile, which is in `T`. The four walks check
`keepOKB` at every state they reach. So `TilesIn` holds at every instruction of the frame and at its end.

**The frame with an invariant.** `EraseRange.frame_of_walkV` goes instruction by instruction. `ReadTiles.frame_of_walkVI` does the same and carries an
invariant `I` of the machine: at instruction `j` the walk's state covers `tr(j)`, its check holds, and `I(tr(j))` with the check gives `I(tr(j + 1))`.
The check that gives `SiteOK(tr(j))` may use `I(tr(j))`. With `I = TilesIn`, `Read(tr(j))` comes from `TilesIn(tr(j))`, the check `readInOK` at the read,
and the field `ReadH`. The frames' induction (`LoopTime.loop_sites_of_rows`) carries `TilesIn` from the end of one frame to the start of the next.

**The read's address.** The routine computes the row `Y = ((y + adder) & 0xF0) − 32`, stores it, copies it to `Y` by `TAY`, and reads `LDA (zp),Y`. Round 33
(`EraseRange`) moved the height's bound to a bound on the accumulator through the row's instructions. Now the `STA zp` of the row keeps the accumulator's
bound, and `TAY` gives the bound to `Y` (`xferY`, proved from the CPU's code of the two opcodes; `Y` is a new byte of the bounds, `yI`). At the read the
walks know the pointer's page, the largest value of its low byte and a bound of `Y`, and `readInOK` holds.

## Measured

`buffer-ctl-check FM2 N tilecheck` (natively, from `PLACE/git`): the four walks with the new checks.

| walk | table (round 33) | failing table states | failing starts |
|---|---|---|---|
| (i) | 159,889 (159,849) | 0 | 0 |
| (ii) | 78,556 (78,516) | 0 | 0 |
| (iii) | 415,324 (415,124) | 0 | 0 |
| (iv) | 176,828 (176,788) | 0 | 0 |

With the checks of this page alone the tables had the size of round 33 (159,849, 78,516, 415,124, 176,788): the new bounds of `Y` and of the accumulator are
only at the `TAY` and at the read, and no table state is at the read. The numbers above are with [the side pipe's read](d-2-4-2-9-SideRead.md) too (its fifth
piece adds 40 to 200 states).
Every byte of the map's block buffers is a tile of the list (416 bytes, 0 out of the list). The private build: see [the side pipe's read](d-2-4-2-9-SideRead.md)
(the same four files, the longest 272 s). Real runs (`loopreal`, round 34, the same as round 32): 3,946,790 reads, 0 outside
the block buffers, 0 tiles not in the list, 0 reads for the head outside the head's list.

## Uses from other parts

* Part c: `RoomMap` (the rows of `startCheckT`, `InRowsT`), `RoomBlocks.readAddr_eq`, `readVal_eq`, `ptrZ`, `operand`, `zp_lt`, `tick_y`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁` (already used by `ChangesK.roomSites`).
* Part d: `EraseRange` (the walk with bounds), `LoopTime`, `StepWrites.keepOK`, `keep_step`, `ScreenPage` (`step_at`, `op_91`, `cyc_91`, `tilesOf`).
* No cycle: `TilesIn` at frame `n` comes from the rows and the frames before `n` and the instructions before `j` of frame `n`; the walks' checks are on the ROM.

## What is not proved

* `roomRead` on the head's reads: a read for the head gives the empty tile or a coin. With `TilesIn` this is a condition on the map at the head's cell: the
  cell above the head is not a brick, a block, the floor or a pipe. A proof needs where the head can be over several frames (the ceiling's height, the left
  wall), which the walks of one frame do not know.

## Lean

`Theorems/ReadTiles.lean`: `ReadH`, `ReadIn`, `read_of`, `inBuf`, `keepOKB`, `zero_mem_tilesOf`, `rd16zp_state`, `mIzy_state`, `erase_ram`, `tiles_step`,
`frame_of_walkVI`, `frameVI`, `inv_end`. `Theorems/RoomMap.lean`: `TilesIn`, `tileRow`, `startCheckT` (one more conjunct), `tiles_of_state`,
`tiles_of_invL`, `tiles_of_rows`. `Theorems/EraseRange.lean`: `yI`, `valOf_y`, `go_staZp_a`, `xferY`, `xferY_ok`; `updF` adds `xferY`; `rulesOf` moves the bounds
also through the `TAY` before the read. `Theorems/LoopTime.lean`: `readInOK`, `readIn_of_ok`, `tilesChk`, `chk1T`, `chk2T`, `chk4T` (the walks use them),
`read_of_chk`, `tiles_of_chk`, `zero_tiles`, `tilesI_of`; `RestU` and `RestB` ask `readH` in place of `read`; `rec_frame1B` to `rec_frame4B` take
`TilesIn` at the frame's start and give it at each instruction; `loop_sites_of_rows` asks `ReadH`. `Theorems/Route.lean`: the field `roomRead`.

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 2 tilecheck      # the four walks with the checks of ReadTiles, then recCheckB and startCheckT natively
.lake/build/bin/smbrta buffer-ctl-check FM2 13 tilecheck     # walk (iii) alone (11, 12, 14: walk (i), (ii), (iv))
```
