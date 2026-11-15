[← Back](README.md) | [English](c-7-12-1-RoomBlocks.md) | [Japanese](c-7-12-1-RoomBlocks-ja.md)

# The blocks of the room's map stay

**Claim.** On every frame from the first control in the bonus room to the frame of the side pipe's entry, every byte of the two block buffers that is not a coin in the map has the map's value. A brick stays a brick, the floor stays the floor, the walls and the pipes stay. This is the part "the bits that are 1" of item 1-1-c-7-12 for the bytes that are not coins; [The block map in the room](c-7-12-RoomMap.md) proves the bits that are 0. It assumes what that page assumes (`SiteOK` on each instruction), and nothing new. No theorem of the route uses it yet: it does not give `land_at`, see the end.

`B` is the set of the 416 bytes of the two block buffers, `M` the map (`RoomMap.mapRef`), `coins` the tiles that a read for the head may give but the empty one (one tile on this ROM). `z` is the byte of the zero page with the pointer of the block buffer routine, `o` the byte with the routine's offset and `t` the byte with the tile it read; the three are read from the code (`ptrOf`, `offOf`, `tileOf`). `m(d)` is the byte `d` of the RAM of `m`.

```
Solid(m)       :  ∀ d ∈ B,  M(d) ∉ coins  →  m(d) = M(d)
adr(m)         =  m(z) + 256·m(z + 1) + m(o)
Coin(m)        :  m(t) ∈ coins  ∧  (adr(m) is a byte of B  →  m(adr(m)) = m(t))

writeAddr_eq   :  the address of an STA (zp),Y  =  the pointer + Y                    readAddr_eq:  the same for an LDA (zp),Y
readVal_eq     :  the address of an LDA (zp),Y is in the RAM  →  the byte read is the RAM's byte there
step_lda_izy   :  an LDA (zp),Y puts the byte read in A and keeps the RAM
step_sta_zp    :  an STA zp writes A into its byte, and keeps A (step_sta_zp_a)
step_tay, step_ldy_zp, step_lda_imm  :  TAY: Y = A;  LDY zp: Y = the byte;  LDA #: Y stays.  Each keeps the RAM
erase_other    :  the erase writes only the byte of its address
blocks_frame   :  checkK,  codeOK,  RoomCond(m),  SiteOK on each instruction,  Solid(m)   →   Solid(frame(m, i))
solid_of_rows  :  rowsCheckB,  InRowsT(m),  control(m)   →   Solid(m)
blocks_run     :  the hypotheses of map_of_rows,  BChecks,  rowsCheckR   →   ∀ n ∈ [b, a],  Solid(seq(n))
Run.roomBlocks :  the checks,  Run   →   ∀ n ∈ [b₁, a₂],  Solid(seq(n))
room_blocks_run (private)  :  Run.roomBlocks with the checks of this ROM, for a run with every field of Run
```

## How

**Only the erase writes the block buffers.** The walk of one frame of the room asks at every state but the erase of a coin that its step may not write a byte of `B` (`RoomFall.mayWrite`). It passes with no failure. [The block map in the room](c-7-12-RoomMap.md) already has no state at the two places of the head's collision with a block.

**The erase writes a byte that holds a coin.** The erase stores the empty tile through the pointer `z` with the offset in Y, loaded from the byte `o`. The abstract machine does not know the pointer. But the block buffer routine read a tile through the same pointer with the same offset, and that tile was a coin. This is a fact about the machine that the abstract states do not hold. The walk carries it with marks (`RoomVert.frame_of_walkV`), and each step of the chain is one instruction on the machine:

| mark | the piece is at | what holds after its step |
|---|---|---|
| `[3]` | `STA o`, three bytes before the read | the byte `o` is A |
| `[6]` | `TAY` | Y is the byte `o` |
| `[4]` | the read `LDA (z),Y` | if `adr` is a byte of `B`: A is the byte at `adr` |
| `[5]` | `STA t`, after the read | if `adr` is a byte of `B`: the byte at `adr` is the byte `t` |
| `[9]` | any place, while no step may write the bytes `o`, `t` or the pointer | `Coin`: set only if the state knows the byte `t` and it is a coin |
| `[7]` | `LDY o`, four bytes before the erase | `Coin`, and Y is the byte `o` |
| `[10]` | `LDA #` | `Coin`, and Y is the byte `o` |
| `[8]` | the erase `STA (z),Y` | `Solid` |

At the erase the address is the pointer plus Y, so it is `adr`; `SiteOK` puts it in `B`; so the byte there is the byte `t`, a coin. A byte that holds a coin is a coin in the map: `Solid` says that the others hold the map's tiles, which are not coins. So the erase changes no byte of `Solid` (`erase_other`). The walk asks that a state at the erase has the mark `[8]`; a mark for one step that comes to another place is dropped, and so is `[9]` when a step may write one of its bytes. `codeOK` checks the code around the read and the erase on the ROM.

A first form had no instruction lemma for `STA o`, `TAY`, `LDY o` and `LDA #`: it split the accumulator into its 256 values at `STA o`, so that the abstract states knew Y and the byte `o` at the read and at the erase. It passed, with a table of 216,515 states and 21.7 s. The four lemmas replace the split.

**At the first control.** The rows of the change into the room know every byte of the block buffers. `rowsCheckB` is the check `rowsCheck` of [the two pairs of bytes](c-7-5-2-RoomPair.md) with one more condition on each state with control: every byte of `B` that is not a coin in the map is known with the map's value. The private proof of `rowsCheck` now comes from it (`rowsCheck_of_B`), so the rows are computed once.

| check on the ROM | size | time in a program |
|---|---|---|
| `checkK` (the walk with the marks) | search 210,206 steps (table 36,210), no failure | 4.4 s (search 2.3 s) |
| `codeOK` | 26 conditions | 0 s |
| `rowsCheckR` (in place of `rowsCheck`) | | 30.6 s (`rowsCheck` took 29 s) |

## Checked on real frames

Program `room-floor-check FM2 [N]`: the map, the checks, then from the movie's first control in the room the movie and `N` runs of each of 5 kinds of own input (up to 199 frames). Each frame is run instruction by instruction.

| run | frames | erases | the byte written does not hold a coin | the byte `t` is not the byte written | the address is not the pointer plus the byte `o` | Y is not the byte `o` | the last read at another address, or not a coin | frames where a byte of `B` changes that no erase wrote | frames that start without `Solid` |
|---|---|---|---|---|---|---|---|---|---|
| the movie | 111 | 13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| own inputs, 5 kinds × 60 | 59,700 | 69 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The map: 113 bytes are not empty and not a coin, 19 are coins. The floor's two rows hold one tile in every column of the first buffer and in half of the columns of the second; the other half of the second buffer is empty there.

## What it does not give

* **`land_at`** (with no wall he stands at `C + 34`). The frame lands if a foot reads a tile of the floor. The reads are through the pointer `z`, and which byte they read depends on the position: the buffer and the column come from the page and the pixel, and in the second buffer half of the floor's row is empty. So `land_at` needs the pointer at the feet's reads from the position (the routine that makes the address), and the foot's column from the bounds on the position. The 301 measured runs with no stand before `C + 34` all stand at `C + 34`.
* The fields about the left wall and the corner (`wall`, `stand_wall`, `low_at`, …) need the same: where a read is, from the position.
* A coin's byte: only its bits that are 0 in the map are known (the page of the map). It is the coin or empty on real frames; that is not proved.

## Assumptions (not proved in Lean)

* `SiteOK` on each instruction of the frames from the first control to the entry, and the player's routine on each of those frames: as for [the block map](c-7-12-RoomMap.md).

**Files.** `Theorems/RoomBlocks.lean` (`rd_ram`, `ptrZ`, `rd16zp_eq`, `operand`, `writeAddr_eq`, `readAddr_eq`, `readVal_eq`, `step_lda_izy`, `step_sta_zp`, `step_sta_zp_a`, `step_tay`, `step_ldy_zp`, `step_lda_imm`, `erase_other`, `bufL`, `Solid`, `zI`, `adr`, `idx`, `InB`, `oneStep`, `zoneK`, `okK`, `phK`, `codeOK`, `Coin`, `coin_keep`, `zoneK_eq`, `blocks_frame`, `coinsOf`, `ptrOf`, `offOf`, `tileOf`, `phR`, `checkK`, `rowB`, `rowsCheckB`, `rowsCheck_of_B`, `solid_of_rows`, `SolidR`, `rowsCheckR`, `BChecks`, `blocks_step`, `blocks_run`), `Theorems/Route.lean` (`Run.roomBlocks`); private `Proof/RoomBlocks.lean` (`room_blocks`, `room_blocks_rows`), `Proof/RoomBlocksRun.lean` (`room_blocks_run`), `Proof/RoomVert.lean` (`room_pair_rows`, now from `room_blocks_rows`).

**Reproduce.**
```
.lake/build/bin/smbrta room-floor-check FM2 [N]    # the map, the checks (about 40 s with the rows) and real frames: N runs of each of 5 kinds (N = 60: about 50 s)
```
