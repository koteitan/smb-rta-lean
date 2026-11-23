[← Back](README.md) | [English](d-2-4-2-11-HeadSide.md) | [Japanese](d-2-4-2-11-HeadSide-ja.md)

# The side pipe's read of the position, from the head's cell

**Claim.** On every frame of the room, the position's low bits are not 0 where the side pipe's code reads the position, if each instruction of the frame meets
the field `roomRead` (the head's cell is free in the map, [The head's read from the head's cell in the map](d-2-4-2-10-HeadFree.md)). So the field `roomXbit`
is gone: on the entering frame `Xbit` follows from `roomRead`.

This is proved, with one more check on the ROM (a walk of a frame of the room, `HeadSide.checkX`). The check is part of walk (i) of `LoopTime.recCheckB`, so
it is proved in a private proof that already exists (`Proof.SiteMusic1`; no new private file). The field `roomXbit` is removed. No field is added.

`tr(j)` is the machine after `j` instructions of the frame, `x` the position (`Player_X_Position`), `xAt` the side pipe's read of it, `M` the map. `SiteX` is
`SiteOK` without `xbit` ([The side pipe's read of the position, only on the entering frame](d-2-4-2-9-SideRead.md)), `ZeroIn`, `ReadIn`, `HeadFree` are those of
[the head's cell](d-2-4-2-10-HeadFree.md) and [the tiles at the read](d-2-4-2-8-ReadTiles.md). `K_X` is the known bits of the room's walks at a frame's start
(`RoomMusic.knownM`) and bits 1 to 7 of the player's size (`SizeKeep`).

## The statement

```
Xbit(m)        :=  pc(m) = xAt  →  x(m) & 15 ≠ 0                                       (SiteParts.Xbit)
xbitOK(A)      :=  pc(A) ≠ xAt  ∨  A knows a bit of x & 15 that is 1                    (the check of one state)

s_stepX        :  Sim(A, m),  SiteOK(m),  ZeroIn(m),  ReadIn(m),  HeadFree(m)   →   a successor of stepX(A) covers step(m)
frame_of_walkX :  the walk from A₀ passes,  A₀ covers m,  ∀ j: SiteX(tr j) ∧ ZeroIn(tr j) ∧ ReadIn(tr j) ∧ HeadFree(tr j)   →   ∀ j,  Xbit(tr j)
xbit_of_check  :  checkX,  RoomCond(r, K_X, m),  ∀ j: SiteX(tr j) ∧ ZeroIn(tr j) ∧ ReadIn(tr j) ∧ HeadFree(tr j)          →   ∀ j,  Xbit(tr j)
```

In `Route.ChangesBase`:

```
before   roomXbit : b₁ < a₂  →  ∀ j,  Xbit(tr_{a₂ − 1}(j))
now      (gone)
```

`LoopTime.loop_sites_of_rows` no longer takes `xlast`. On the frame `a₂ − 1` it applies `xbit_of_check`: the room's condition with `K_X` at the frame's start
(the induction's `RoomCond` with the size's bits, `LoopTime.cond_size`), and on each instruction `SiteX`, `ZeroIn`, `ReadIn` from the four walks
(`LoopTime.FrameOut`) and `HeadFree` from the field `roomRead`.

## How it works

The side pipe's code runs only after a side read finds the side pipe's tile, with the player standing. The collision routine reads the head's cell before the
side cells, with the same position. A position with the low bits 0 puts the head and the side in the same column. In the pipe's column the head of a player who
lands there is in a cell of the pipe or of the floor, and `HeadFree` does not allow that.

The walk follows the whole frame, as the walk of [the block map](c-7-12-RoomMap.md) does, and takes `SiteOK` on each instruction as a hypothesis: `SiteX` from
the room's walks, and `Xbit` from the walk's own check `xbitOK` at the state that covers the instruction (`xbit_of_ok`). It has more pieces and steps:

* **The position.** At the collision routine's entry, the low bits of `x` one after the other up to the first 1 (`lowBits`). With the four low bits 0, also the
  high bits and the page's low bit (`highX`): then every read's address is known. For the one position whose head and side reads lie in the side pipe's column
  (16 times the column, page 0), also the height (its four high bits, and its values in the row of the reference entry's height and the row below, `yPieces`)
  and the low bit of the player's size. Without the size the head check's bound is read through an index the walk does not know, and the walk could skip the
  head's read.
* **The state.** For that position the player's state is split at the routine's read of it, bit by bit up to the first 1. A state that is not 0 stays known not
  to be 0, so a frame that does not land does not come to the side pipe's code.
* **The page and the row.** At the page's `ADC #0` with the carry 0 the accumulator keeps the page (`EntryHeightBig.refineA`). At the row's `SBC #` with the
  carry 1 and an operand with the low bits 0, the accumulator keeps its four low bits (`refineS`; `sbc_low` from the CPU's code), so the read's `Y` has the low
  bits 0 and at most 16 values.
* **The read.** At the block buffer routine's read with the pointer known and at most 16 values of `Y` (`candRead`), the step takes each tile of the list that
  some address allows: a byte of the block buffers with no bit outside the map's byte (`ZeroIn`), and for a head read only where the map's byte is a head tile
  (`HeadFree`). A head read in a cell of the pipe has no tile: the piece has no machine.
* **The check.** Every state meets `xbitOK`, and so do the frame's ends.

The search (no part of the proof) keeps the position, the page, the height, the state and the size in its key, and forgets them where the side check ends and at
the collision routine's return. A first search that split all 256 positions grew past 6 GB and was stopped. Two later searches failed only at the side pipe's
read with the position 208: one had lost "the state is not 0" at a branch, one had joined the two values of the size.

## Measured

`buffer-ctl-check FM2 N xwalk` (natively): the search 5,933,508 steps, 433,074 forks, 0 failures, 1,165,195 table states, 316 frame ends, 44 s, 3.9 GB. With
`N = 1` also `HeadSide.checkX` natively: true, 77 s. The private build of `Proof.SiteMusic1` (walk (i) with this check) took 203 s in `prove.py` at load about 6 to 11 (round 34: 72 s); the other three walks'
files took 80, 311 and 117 s, so the private build's longest file is still `Proof.SiteMusic3`. `#print axioms route_1_1` has the same 304 names as before this
round: the check is in a `native_decide` that already exists, and the lemmas of the CPU's `SBC` and of the bits (`sbc_nat`, `refineS_mem`, `xbit_of_mem`) are
proved with `omega` and rewriting, without `bv_decide`.

Real runs: `buffer-ctl-check FM2 100 headfree` (on [the head's cell](d-2-4-2-10-HeadFree.md)) found the side pipe's read of the position at 195, 196 and 198 px
(small) and 195, 196 px (big), with the head's cell of the same frame in column 12, left of the pipe's column.

## What is not proved

* `roomRead` (`HeadFree`) itself. This page uses it on the entering frame.

## Uses from other parts

* Part c: `RoomMap.mapRef`, `RoomBlocks.readAddr_eq`, `readVal_eq`, `ptrZ`, `operand`, `tick_a`, `SideEntryRule.spots` (the side check's exits, for the
  search only).
* Part d: `EntryHeightBig` (`ptrLo`, `ptrHi`, `refineA`, `adc0_a`, `AdcOK`), `EntryHeight` (`Opts`, `routeY`, `mix64`, `heightI`), `ScreenPage` (`preS`,
  `cov_preS`, `stepS`, `s_stepS`, `readStep`, `s_readStep`, `mem_tilesFor`, `sim_of_room`, `sim_clamp`), `SizeKeep.sizeI`, `ReadTiles` (`ZeroIn`, `ReadIn`,
  `HeadFree`, `inBuf`), `SideRead` (`no_xAt` for the frames before), `LoopTime` (`FrameOut`, `cond_size`).
* No cycle: on frame `a₂ − 1` the walk uses `SiteX`, `ZeroIn`, `ReadIn` of that frame from the room's walks, which do not use `Xbit`, and the field `roomRead`.
