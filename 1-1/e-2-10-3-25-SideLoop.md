[← Back](README.md) | [English](e-2-10-3-25-SideLoop.md) | [Japanese](e-2-10-3-25-SideLoop-ja.md)

# The stores that may reach the side timer, in the area parser's loops

Round 34 asked the field `sideW` only at the stores that may reach the side collision's timer in two pieces of code: the area parser's code and the code of the head's collision with a block ([The stores that may reach the side timer, outside the area parser](e-2-10-3-24-SideRange.md)). That was 29 stores. Here the same walk, with a finer table and one more split, proves it at all of them but four. So the field is asked only at those four.

**Claim (round 35).** Write

```
s          = the side collision's timer, as a RAM index
SideW(m)   := a store through an index or a pointer at m does not write s
NearW(m)   := round 33 (a store to an absolute address plus X or Y from a base that some index takes to s, or STA (zp),Y)
Code(m)    := round 34's Resid(m): AreaParserCore ≤ pc(m) < GetBlockBufferAddr, or PlayerHeadCollision ≤ pc(m) < BlockObjectsCore
Resid(m)   := (Code(m) and the instruction at m is STA (zp),Y)       (a store through a pointer)
              or CRendLoop ≤ pc(m) < ChkCFloor                        (the castle's loop of rows)
```

`SideLoop.near_side`: take a frame in control with the hypotheses of `SideRange.near_side` (it starts in the idle loop, each instruction meets `CleanK` of `FrameKeep.guardE`, no instruction writes the routine, the mode or the task by its address, it comes to the player's routine at n₀). Then it comes to the scroll handler's call at a first kq > n₀, and

```
∀ j ≥ kq in the frame:  NearW(trace j) ∧ ¬Resid(trace j)  →  SideW(trace j)
```

`lCheck` is the check on the ROM. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No game data: the castle's loop is two symbols (`CRendLoop`, `ChkCFloor`, new in `tools/smb-symbols.txt`), read from the disassembly; `0x91` is the 6502's opcode of `STA (zp),Y`.

The new places are some of round 34's (`SideLoop.resid_old`, with AreaParserCore ≤ CRendLoop and ChkCFloor ≤ GetBlockBufferAddr). In the program there are 4 such stores: one store through a pointer in the area parser, two in the head's collision, and the castle loop's store to the metatile buffer. The walk asked at round 34's places fails at three of them; the fourth, the store through a pointer in the routine that checks the block's top, comes after the head collision's other store on the paths that reach it, so a path stops before it. Where a path does go on to it, it fails too: in round 34 with round 34's walk, and here with the split of X described below (54 failures there).

**The walk.** It is round 34's walk (`SideRange.walkR`: bounds on X and Y at the table's states, splits before the instructions that count an index, the zero page kept over a store that cannot reach it), with two changes, both only in the code of `Code`:

1. **The table's key** (`keyL`) also holds what the state knows of X, Y and the zero page byte 0. Before, the states of a loop at its head were joined into one table state. Then a loop counter in the zero page lost its known bits, the abstract loop did not end, and its index grew to every value. Now each pass of such a loop has its own table state. One example is the loop of the background scenery, which counts its passes in the zero page byte 0 and stores through Y.
2. **A split before `LDX abs,Y`** (`spL`, `cov_spL`): Y is split into all its values, up to 8 unknown bits. Then X is known after the load, for each value of Y. Two loads need it: the row of the staircase, read from a table at the index of the staircase's control (a byte that lives across frames), and the row of the castle's bridge and chain, read at the index of the zero page byte 0. Over all 256 values of Y the staircase's table and the bytes after it give no row that reaches the timer.

The key is no part of what the walk proves: a state is covered by a table state only when its known bits and its bounds say so (`SideRange.coverR`). `okL_spec` is the proof of `SideRange.okR_spec` with the new places.

**On the route.** The field `sideW` of `OnFrames` has the premise `SideLoop.Resid(trace n)` in place of `SideRange.Resid(trace n)`:

```
sideW : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
          ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → NearW(trace n) → Resid(trace n) → SideW(trace n)
```

`OnFrames.sideWAt` (round 33's field) takes `SideLoop.near_side` at the other stores. In `numbersCheck` the check `SideRange.rCheck` is replaced by `SideLoop.lCheck` (`Numbers.rangeC`, `AreaRun.rg`). The field asks less: the same frames, and at each frame only the 4 stores of the new `Resid` (round 34: 29).

**Measured.**

| check | what | result |
|---|---|---|
| native search (`SideLoop.lFails`) | the walk's search from the scroll handler's call | 0 failures; 64,312 states reached, 51,457 states in the table (round 34: 19,751 and 16,803) |
| native evaluation | `lCheck` for the area's type of 1-1 | true, in about 14 s (round 34's `rCheck`: about 8 s, on the same loaded machine) |
| native scratch searches | the new walk asked at round 34's places too | 42 failures at 3 places: the area parser's store through a pointer, the head collision's store through a pointer, the castle loop's store. A path stops at its first failure |
| native scratch searches | the key without the zero page byte 0 | 68 failures at 4 places (the loop of the background scenery too) |
| native scratch searches | a key with the zero page byte 6 too | the same 3 places; 279,943 states reached |
| native scratch searches | splits before `LDY abs,X` too | the loop of the foreground scenery (its row table at the index of a byte that lives across frames) split into 256 pieces of 13 passes each; the search passed 5.5 GB and I stopped it |
| `edge-real FM2 256` | `sideW`, `sideWAt (a theorem)` | 0 failures for both. 5 sets, 137,955 frames at the routine of the offscreen bits, 108,634 frames that end with the timer at most 1; it fails only on the old stored speed and `after` on frames that do not start clean, with the counts of rounds 30 to 34. The frames of the shape of `Moves.stop` are 6, all with no push and one clamp, and the field asks none of them |
| `surface-frames-check FM2 200` | `sideW` (the narrowed field), `sideWAt (a theorem)`, `SideLoop's bytes (measured only)` | 0 failures for all three. 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included. 2,239 frames come to a store of `Resid`; at each such store the block buffer's column is below 32 and `SprDataOffset_Ctrl` is 0 or 1, and at the castle loop's store, where it ran, the row was at most 10 (the count does not tell the stores apart) |

**What is not proved here.** `SideW` at the stores of `Resid`. What the walk does not know there is a byte that lives across frames:

- The area parser's store through a pointer to the block buffer. The pointer's high byte is read from a table of the program at the index `BlockBufferColumnPos ÷ 16`. For an index of 15 the byte read is a page whose mirror holds the timer, and the range of the low byte plus Y reaches the timer's place. The store misses the timer when `BlockBufferColumnPos` < 240; the program's stores to it by its address keep it below 32.
- The head collision's store through a pointer. Before it, stores to the zero page at the index `SprDataOffset_Ctrl` (`sta Block_State,x`, and the block's position and page in `InitBlock_XY_Pos`) may write the pointer, as far as the walk knows. The program's only store to `SprDataOffset_Ctrl` by its address flips its bit 0 (`eor #1`). I also tried a split of X into all its values before these stores: then the walk fails at more places (685 failures, 344,988 table states), because even in the pieces with X = 0 and X = 1 the walk knows only bits 3, 5, 6 and 7 of the pointer's high byte at the store, and in other pieces a store writes a byte that the walk does not know into the pointer.
- The castle loop's store. The loop stores rows from the row read from the area's data up to row 10, and stops when the row becomes 11. A start row of 11 or more would run the loop over the whole page and reach the timer (the disassembly notes that the game would crash).

To prove these a walk must keep a bound on such a byte from frame to frame. I measured the first step: after the scroll handler, as far as this walk knows, stores at 6 places may write `BlockBufferColumnPos` (all of them stores through a pointer to the block buffers) and stores at 19 places may write `SprDataOffset_Ctrl`. So such a bound needs more bounds first.

**Round 36.** On a frame where the block buffer's column and `SprDataOffset_Ctrl` start in their ranges and no store through an index or a pointer writes them (`SideAcross.FactsAt`, which part f's fields give), the four stores are proved too, the castle's loop with a new field on its start row (`castleRow`), and `sideW` is asked only on the other frames ([The stores that may reach the side timer, with two bytes kept across frames and the castle's start row](e-2-10-3-26-SideAcross.md)).

**File:** `Theorems/SideLoop.lean` (`residB`, `Resid`, `resid_old`, `keyL`, `spL`, `cov_spL`, `okL`, `okL_spec`, `searchL`, `lCfg`, `lCheck`, `lFails`, `near_side`). Changed: `Theorems/SurfaceFrames.lean` (the field `sideW`, `OnFrames.sideWAt`, `numbersCheck`, `Numbers.rangeC`, `AreaRun.rg`, `movesScan`), `Smbrta/Syms.lean` and `tools/smb-symbols.txt` (the symbols `CRendLoop`, `ChkCFloor`, and `BlockBufferColumnPos`, `SprDataOffset_Ctrl` for the measure only), `Main.lean` (a count in `surface-frames-check`).
