[← Back](README.md) | [English](e-2-10-3-24-SideRange.md) | [Japanese](e-2-10-3-24-SideRange-ja.md)

# The stores that may reach the side timer, outside the area parser

Round 33 asked the field `sideW` only at a store that may reach the side collision's timer ([A store that may reach the side timer](e-2-10-3-22-SideNear.md)): a store to an absolute address plus an index from whose base some index reaches the timer, or a store through a pointer (`NearW`). Here a walk proves it at each such store outside two pieces of code: the area parser's code, and the code of the head's collision with a block. So the field is asked only at the stores in those two pieces of code.

**Claim (round 34).** Write

```
s          = the side collision's timer, as a RAM index
SideW(m)   := a store through an index or a pointer at m does not write s
NearW(m)   := round 33 (a store to an absolute address plus X or Y from a base that some index takes to s, or STA (zp),Y)
Resid(m)   := AreaParserCore ≤ pc(m) < GetBlockBufferAddr        (the area parser's code)
              or PlayerHeadCollision ≤ pc(m) < BlockObjectsCore  (the head's collision with a block, and the bumped block's routines that it calls)
```

`SideRange.near_side`: take a frame in control with the hypotheses of `PushTimer.pix_end` but the fields `posW` and `sideW` (it starts in the idle loop, each instruction meets `CleanK` of `FrameKeep.guardE`, no instruction writes the routine, the mode or the task by its address, it comes to the player's routine at n₀). Then it comes to the scroll handler's call at a first kq > n₀, and

```
∀ j ≥ kq in the frame:  NearW(trace j) ∧ ¬Resid(trace j)  →  SideW(trace j)
```

`rCheck` is the check on the ROM (true natively in a few seconds). Axioms: `propext`, `Classical.choice`, `Quot.sound`. No game data: the code's places are four symbols (`AreaParserCore`, `GetBlockBufferAddr`, `PlayerHeadCollision`, `BlockObjectsCore`, new in `tools/smb-symbols.txt`), read from the disassembly.

**The walk.** `walkR` starts at the scroll handler's call, in the states of the first walk of `AfterKeep` there, and follows the frame to its end. It follows no byte. Its guard is `FrameKeep.guardE`, whose `CleanK` is the field `cleanE` of `FrameKeep.Frames`. A path stops at a store to the routine, the mode or the task by its address (the field `noStore`). At a store of `NearW` that is not of `Resid`, the walk asks that every target that its state allows misses s (`missK`): through X or Y, every value of the index; through a pointer, every value of the pointer's high byte with every sum of the low byte and Y from the smallest to the largest (`missP`). Three things let it know the index and the pointer there:

1. **Bounds at the table's states.** A table state carries bounds lo ≤ X ≤ hi and lo' ≤ Y ≤ hi' in its `log` (`bnd`), which `Sim` does not read. A walk from a table state starts from its pieces: X, then Y, split into their values inside the bounds, when there are fewer than 17 and the bounds exclude a value that the known bits allow (`pieces`, `pieces_cov`). A state is covered by a table state only when its known bits are under the table state's and its values of X and Y are inside the bounds (`coverR`, `bok_of_leB`). So a loop counter such as `INX; CPX #13; BNE` keeps the range 0..12, where known bits would grow to 0..15 and then further.
2. **Splits before some instructions.** Before `TXA`, `INX`, `DEX` and the stores through X, X is split into its values when at most 4 of its bits are not known; the same for Y before `TYA`, `INY`, `DEY` and `STA abs,Y` (`splitR`, `cov_splitR`). The pieces then go through the instruction with a known value.
3. **The zero page over a store that cannot reach it.** When a store's index is not known, TaintRun's step forgets every byte outside the guard. After a store through an index or a pointer the walk takes back each byte of the zero page that the state before knows and that the store does not write (`fixR`, `StepWrites.keep_step`). So the object offset, the temporaries and the pointers of the zero page survive a store to a table at an absolute address.

The theorem `okR_spec` turns `okR` at a state that covers m into `NearW(m) ∧ ¬Resid(m) → SideW(m)`: the target of the store is the base plus the index (`PushTimer.abx_t`, `PushTimer.aby_t`), or the pointer plus Y (`izy_t`), and that is one of the targets that `missK` checks.

**On the route.** The field `sideW` of `OnFrames` asks one more premise: `Resid(trace n)`.

```
sideW : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
          ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → NearW(trace n) → Resid(trace n) → SideW(trace n)
```

Round 33's field is the theorem `OnFrames.sideWAt` (from the field at the stores of `Resid` and `near_side` at the others). `numbersCheck` has one more check, `SideRange.rCheck`, and `AreaRun` one more field `rg` from it. The field asks less: the same frames, and at each frame only the stores of `Resid`. Of the 50 stores of `NearW` in the program (41 through an index, 9 through a pointer), 29 are in `Resid` (27 in the area parser, 2 in the head's collision).

**Measured.**

| check | what | result |
|---|---|---|
| native search (`SideRange.rFails`) | the walk's search from the scroll handler's call | 0 failures; 19,751 states reached, 16,803 states in the table |
| native evaluation | `rCheck` for the area's type of 1-1 | true |
| native scratch searches | the same walk without the bounds, or without the splits | without the bounds: 10 failures at the two stores of the misc objects' collision flag (the hammer's collision with the player), where X is the object offset that the misc objects' loop counts down from 8. Without the splits: 5 failures at those two and at the misc objects' offset routine. Interpreted scratch searches without the zero page failed at the same two stores. With known bits only (round 33's walk) the search failed at 24 places |
| native scratch search | the walk asked at the stores of `Resid` too | 140 failures at 6 places: 4 stores to the metatile buffer and the store through a pointer to the block buffer in the area parser, and the store through a pointer of the block that he bumps. A path stops at its first failure, so the stores behind them are not counted |
| `surface-frames-check FM2 200`, `edge-real FM2 256` | `sideW` (the narrowed field), `sideWAt (a theorem)` (round 33's field, `SideW` at every store of `NearW`) | 0 failures for both. `surface-frames-check`: 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included. `edge-real`: 5 sets, 137,955 frames at the routine of the offscreen bits, 108,634 frames that end with the timer at most 1; it fails only on the old stored speed and `after` on frames that do not start clean, with the counts of rounds 30 to 33 |

**What is not proved here.** `SideW` at the stores of `Resid`:

- The area parser's stores to its buffers (the metatile buffer, the area objects' lengths and offsets, the mushroom ledge's half length; 26 stores and one through a pointer). Their indices come from bytes that live across frames: for example a row read from a ROM table at an offset that is a RAM byte (the staircase's control), or the object's offset in the area data. A walk of one frame does not know them; it needs an invariant over the frames.
- The two stores through a pointer of the block that he bumps (in `PlayerHeadCollision` and in the routine that checks the block's top). The pointer's high byte is in the zero page, and a store through X to the zero page with X from a byte that lives across frames (the block's sprite offset) may overwrite it, as far as the walk knows.

Round 35 proves all of them but four with a finer table and one more split ([The stores that may reach the side timer, in the area parser's loops](e-2-10-3-25-SideLoop.md)): the field is asked only at the three stores through a pointer and at the store of the castle's loop of rows. `numbersCheck` now has `SideLoop.lCheck` in place of `rCheck`, so `near_side` of this file is no longer used by the route; `SideLoop` uses its walk.

**File:** `Theorems/SideRange.lean` (`bnd`, `pieces`, `coverR`, `splitR`, `fixR`, `missK`, `missP`, `Resid`, `okR`, `okR_spec`, `izy_t`, `walkR`, `okR_all`, `near_side`, `searchR`, `rCheck`). Changed: `Theorems/SurfaceFrames.lean` (the field `sideW`, `OnFrames.sideWAt`, `numbersCheck`, `Numbers.rangeC`, `AreaRun.rg`, `movesScan`), `Smbrta/Syms.lean` and `tools/smb-symbols.txt` (the four symbols).
