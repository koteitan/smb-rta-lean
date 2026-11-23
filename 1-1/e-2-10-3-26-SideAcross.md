[← Back](README.md) | [English](e-2-10-3-26-SideAcross.md) | [Japanese](e-2-10-3-26-SideAcross-ja.md)

# The stores that may reach the side timer, with two bytes kept across frames and the castle's start row

Round 35 asked the field `sideW` only at four stores ([The stores that may reach the side timer, in the area parser's loops](e-2-10-3-25-SideLoop.md)): the area parser's store through the block buffer's pointer, the two stores through the pointer in the head's collision with a block, and the store of the castle's loop of rows. The first three need two bytes that live across frames, and the fourth needs the castle's start row. Here the walk knows the two bytes on every frame where part f's conditions on them hold, and the start row from a condition on one instruction. So `sideW` is asked only on the other frames, and the castle's part of it is a new field `castleRow` on the start row.

**Claim (round 36).** Write

```
s, b, c     = the side collision's timer, the block buffer's column (BlockBufferColumnPos), the block objects' offset (SprDataOffset_Ctrl), as RAM indices
SideW(m)    := a store through an index or a pointer at m does not write s
NearW(m)    := round 33 (a store to an absolute address plus X or Y from a base that some index takes to s, or STA (zp),Y)
InvB(m)     := m[b] < 32 ∧ m[c] ∈ {0, 1}
MissB(m)    := a store through an index or a pointer at m writes neither b nor c
FactsAt(M)  := InvB(M) ∧ ∀ k, frame(trace M k) = frame(M) → MissB(trace M k)          (the frame of M: at its start, and at each of its instructions)
CastleRow(m):= pc(m) = CRendLoop → X(m) ≤ 10              (at the head of the castle's loop of rows the row is at most 10)
```

`SideAcross.near_sideA`: take a frame in control with the hypotheses of `SideLoop.near_side` (it starts in the idle loop, each instruction meets `CleanK` of `FrameKeep.guardE`, no instruction writes the routine, the mode or the task by its address, it comes to the player's routine at n₀), with `FactsAt(M)`, and with `CastleRow` at each instruction from the scroll handler's call on. Then it comes to the scroll handler's call at a first kq > n₀, and

```
∀ j ≥ kq in the frame:  NearW(trace j)  →  SideW(trace j)
```

The checks on the ROM are `aCheck` (the walk) and `keepCheckA` (the two bytes from the frame's start to the scroll handler's call). Axioms: `propext`, `Classical.choice`, `Quot.sound`. No game data: the two bytes and the loop's head are symbols (`BlockBufferColumnPos`, `SprDataOffset_Ctrl`, `CRendLoop`, all in `tools/smb-symbols.txt` since round 35); `0x91` is the 6502's opcode of `STA (zp),Y`.

**Why `FactsAt`.** Neither byte is kept by one frame alone, as far as any walk of one frame knows:

- the block buffer's column: the stores through the block buffer's pointer in the coin's erasing and in the block objects' update have a low byte and a row that the walk does not know (they come from additions and from bytes that live across frames), and their range reaches the column's place. Reading the code, one path could write it: if the head's collision took the row past the buffer's last row as a solid block (he would have to move up near the bottom of the screen), the block object's update would later write a metatile at the column's place. No real run measured does this;
- the block objects' offset: the screen buffer's stores through `Y` (at the screen buffer's own offset, which lives across frames) may reach it, and so may the enemies' stores through `X`.

Part f assumes that no store through an index or a pointer writes them (the fields `bKeep`, `PoleBcol.BcR`, and `keepB`, `PoleTileKeep.KeepB`, of `PoleJoin.Run`; since part f's round 36 `bKeep` is asked only where `PoleNear.near_frames` leaves it, and `PoleJoin.Run.bNoW` gives the column's part on every instruction of the frame but the parser's store, where `frames_bcol` gives it), and proves from that and the values at control that each frame starts with `InvB` (`PoleBcol.frames_bcol`: the column is the parser's column mod 32; `PoleTileKeep.frames_keepY`: bits 1 to 7 of the offset stay 0). That is `FactsAt` on every frame of the route: `SideAcross.Run.factsAll` (file `Theorems/SideAcrossRun.lean`), with two checks that the two pairs of indices (the symbols here, the operands that part f reads from the code) are the same.

**The walk.** It is round 35's walk (`SideRange.walkR` with `SideLoop`'s key and split) with four changes:

1. its guard (`guardA`) is `FrameKeep.guardE` with b and c protected: `CleanK` of it is `CleanK` of `guardE` and `MissB` (`cleanK_A`);
2. it starts at the scroll handler's call from round 35's states with b known below 32 and c known to be 0 or 1 (`setB`). The two bytes there are those of the frame's start: the walk of `CtrlKeep` that follows one byte up to the player's routine, and the walk of `PlaceKeep` from there to the scroll handler, each for b and for c (`keepCheckA`, `keep_cutA`, `keep_subsA`, as `SideTimer.keep_at` and `PlaceKeep.keep_place`);
3. after a store through a pointer whose low byte it does not know, it takes back each byte of the zero page that every target misses, from the pointer's high byte and the range of `Y` (`takeP`, `fixP`; `izy_locs`: such a store writes only its target, and `SideRange.missP` says the target misses the byte). Before, such a store made the walk forget the zero page, and with it the pointer;
4. at the head of the castle's loop it splits `X` into the rows 0 to 10 (`spC`). This split covers only the machines with `CastleRow` (`cov_spC`), so the walk's lemmas take a condition `H` on each instruction (`CovH`, `live_stepP`, `okP_all`).

With b below 32 the area parser's pointer points into the block buffers. With c at most 1 the head's collision's stores to the zero page through `X` are split into two exact pieces, and none of them writes the pointer. With the third change the pointer stays known through the parser's loop of rows and from the head's collision's first store through the pointer to its second. With the fourth the castle's loop stores rows 0 to 10 only.

**On the route.** The field `sideW` of `OnFrames` is asked only on a frame without `FactsAt`, and a new field `castleRow` takes its place at the castle's loop:

```
sideW     : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
              ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → NearW(trace n) → Resid(trace n) →
                ¬FactsAt(fm j) → SideW(trace n)
castleRow : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
              ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → CastleRow(trace n)
```

where `Resid` is round 35's `SideLoop.Resid` (the four stores). `OnFrames.sideWAt` (round 33's field) takes `near_sideA` (with `castleRow`) on a frame with `FactsAt`, and on a frame without it `SideLoop.near_side` outside `Resid` and the field at `Resid`. `numbersCheck` has one more check, `SideAcross.check` = `aCheck` and `keepCheckA` (`Numbers.acrossC`, `AreaRun.ac`).

- `sideW` asks less than round 35's field: the same frames and stores, but only on a frame without `FactsAt`, of which part f's fields leave none on the route (`Run.factsAll`). The route does not use `Run.factsAll` yet: the route's theorems that take `SurfaceFrames.AreaRun` would need the values at control as hypotheses, in files of part f.
- `castleRow` is new. It asks on the same frames and from the same instruction on as `sideW` did, but at the loop's head the row in place of the store's target. It is not weaker than the castle's part of round 35's field: on a machine where the loop starts at row 11 or more and does not reach the timer before the frame ends, round 35's field holds and `castleRow` does not. In the program the loop then runs over the whole page within the frame and does reach it.

**Measured.**

| check | what | result |
|---|---|---|
| native search (`SideAcross.aFails`) | the walk's search from the scroll handler's call | 0 failures; 53,298 states reached, 45,200 states in the table |
| native evaluation | `aCheck`, `keepCheckA` for the area's type of 1-1 | true in about 17 s and 1.5 s (round 35's `lCheck`: about 15 s, the same load) |
| native scratch search | the walk without the split at the castle's loop and with that loop left out | 0 failures but at that loop (36 failures there) |
| native scratch search | the walk with b and c known but not protected | the same 3 failing places as round 35 (the two bytes are lost at the coin's erasing and at a screen buffer's store) |
| native scratch search | the walk with b and c protected and known, without the third change | fails at the parser's store and at the head's second store through the pointer |
| native scratch search | as `aCheck`, with round 34's key and split | 125 failures at 4 places (the loops of the metatile buffer) |
| native scratch search | this walk, asked about other bytes after the scroll handler | his place byte and the scroll lock: no store may write them; the timers' control: one store, the background's loop of `RenderUnderPart`; the injury timer: 12 stores of the enemies through `X` |
| native evaluation | the two pairs of indices (`he1`, `he2` of `factsAt_frames`) | the same |
| `surface-frames-check FM2 200` | `sideW` (the narrowed field), `castleRow`, `sideWAt (a theorem)`, frames without `FactsAt` (measured) | 0 failures for all; 8 sets, 239,510 frames, 215,433 checked, the overwritten states included; 0 frames without `FactsAt` in every set; 2,239 frames come to a store of round 35's `Resid` (as in round 35) |
| `edge-real FM2 256` | `sideW`, `castleRow`, `sideWAt (a theorem)` | 0 failures; the output is that of round 35 (it fails only on the old stored speed and `after` on frames that do not start clean, with the counts of rounds 30 to 35) |

**What is not proved here.**

- `castleRow`. The start row is the low 4 bits of the castle object's second byte in the area's data. To prove it a walk must know the area's data pointer and the parser's offsets into the data, which live across frames, and the rows of 1-1's castle objects.
- `FactsAt` on the route: it follows from part f's fields `bKeep` and `keepB` (`Run.factsAll`), which are assumed, and the route does not use it yet.

**Files:** `Theorems/SideAcross.lean` (`bcpI`, `sdoI`, `InvB`, `MissB`, `FactsAt`, `CastleRow`, `spC`, `CovH`, `cov_spC`, `guardA`, `cleanK_A`, `setB`, `sim_setB`, `missP_ne`, `izy_locs`, `takeP`, `fixP`, `fixP_sim`, `sideW_of_missK`, `okA`, `okA_spec`, `walkP`, `live_stepP`, `okP_all`, `searchA`, `aCfg`, `aCheck`, `keepCheckA`, `check`, `keep_cutA`, `keep_subsA`, `near_sideA`), `Theorems/SideAcrossRun.lean` (`factsAt_frames`, `Run.factsAll`). Changed: `Theorems/SurfaceFrames.lean` (the fields `sideW` and `castleRow`, `OnFrames.sideWAt`, `numbersCheck`, `Numbers.acrossC`, `AreaRun.ac`, `movesScan`), `Main.lean` (a count in `surface-frames-check`).
