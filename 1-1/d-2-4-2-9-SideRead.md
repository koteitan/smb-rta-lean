[← Back](README.md) | [English](d-2-4-2-9-SideRead.md) | [Japanese](d-2-4-2-9-SideRead-ja.md)

# The side pipe's read of the position, only on the entering frame

**Claim.** On every frame of the room before the entering frame, the side pipe's code does not read the player's position. So the field `roomXbit` (the
position's low bits are not 0 at that read) is asked only on the entering frame `a₂ − 1`.

This is proved, with checks on the ROM in the private proofs that already exist (the four walks of `LoopTime.recCheckB`; no new private file). The field
`roomXbit` is narrowed. No field is added.

Round 35: the field `roomXbit` is gone. On the entering frame `Xbit` follows from the field `roomRead` by one more walk of the frame
([The side pipe's read of the position, from the head's cell](d-2-4-2-11-HeadSide.md)); on the frames before, this page's `no_xAt` still gives it.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `xAt` is the side pipe's read of the position (`LDA` of the position in `PlyrPipe`), `stAt` the
store of the routine byte after it (the first `STA zp` of the routine byte from `xAt` on), `rt(m)` the routine byte, `v` the reference's routine (the
player's routine). `a₂` is the first frame from the room's first control `b₁` on that starts with another routine than the player's.

## The statement

```
Xbit(m)      :=  pc(m) = xAt  →  x(m) & 15 ≠ 0                                       (SiteParts.Xbit, as before)
XInv(j)      :=  (∃ k ≤ j, pc(tr k) = xAt)  →  xAt ≤ pc(tr j) ≤ stAt  ∨  rt(tr j) ≠ v

xinv_step    :  rtOK(A), wsetOK(A), Sim(A, tr j), SiteX(tr j), XInv(j)   →   XInv(j + 1)
no_xAt       :  ∀ j, XInv(j),   the frame ended,   ¬(xAt ≤ pc(frame) ≤ stAt),   rt(frame) = v   →   ∀ j, pc(tr j) ≠ xAt
```

The checks of one abstract state `A`:

```
rtOK(A)    :=  (pc(A) ≠ stAt  ∧  (A's step keeps the routine byte  ∨  A is at the coin's erase))
               ∨  A is an STA zp of the routine byte, not at an interrupt, with the accumulator known and ≠ v
wsetOK(A)  :=  ¬(xAt ≤ pc(A) < stAt)  ∨  every successor B of the walk's step from A has xAt ≤ pc(B) ≤ stAt
finX(B)    :=  ¬(xAt ≤ pc(B) ≤ stAt)                 (the walks' frame ends)
```

In `Route.ChangesBase` the field changes:

```
before   roomXbit : ∀ n ∈ [b₁, a₂), ∀ j,  Xbit(tr_n(j))
now      roomXbit : b₁ < a₂  →  ∀ j,  Xbit(tr_{a₂ − 1}(j))
```

## How it works

**No hypothesis at the read.** The walk's step split the position at `xAt` into four pieces with a low bit set (`ScreenPage.preS`); that needs `Xbit`. The walks
of the room's frames now use `EraseRange.pstepX`: at `xAt` a fifth piece has the four low bits 0 (`preSX`). On that path the code does not set the area change's
timer, and goes on to the store of the routine. The step needs only `SiteX`, the five other parts of `SiteOK` (`s_pstepX`; the other functions of the step do not
look at `xAt`, so `SiteX` with `xAt` moved off the machine's place is `SiteOK`, `siteOK_movX`). The four walks prove `SiteX` on each instruction of each frame.

**From the read to the routine's store.** From `xAt` the code tests the low bits, may set the timer, loads the routine byte, compares it with two routines and
stores the side pipe's routine. The walks know the routine byte there (the player's), so no branch leaves this code. `wsetOK` checks that every successor of a
state from `xAt` to before `stAt` is from `xAt` to `stAt` (each successor of the walk's step covers the next machine: `EraseRange.succ_of`). At `stAt` the store
writes a known value that is not the player's routine. `rtOK` checks that every other step keeps the routine byte, or writes a value that is not the player's
routine (the coin's erase writes in the block buffers, which are above the routine byte). So after `xAt` the machine is from `xAt` to `stAt`, and after the store
its routine byte is not the player's (`XInv`, an invariant of the instruction's number carried by `ReadTiles.frame_of_walkVI`).

**The frames in order.** A frame of the walks ends out of `xAt` to `stAt` (`finX` in the walks' end check). A frame `n` with `n + 1 < a₂` ends with the player's
routine (the definition of `a₂`). So it never runs `xAt` (`no_xAt`), and `Xbit` holds on it with nothing to show. On the frame `a₂ − 1` the field gives it.
`LoopTime.loop_sites_of_rows` puts `SiteX` and `Xbit` together into `SiteOK`.

## Measured

`buffer-ctl-check FM2 N tilecheck` (natively, from `PLACE/git`): the four walks with the fifth piece and the checks of this page and of
[the block buffers' tiles at the read](d-2-4-2-8-ReadTiles.md).

| walk | table (before the fifth piece) | states from `xAt` to `stAt` | failing table states | failing starts |
|---|---|---|---|---|
| (i) | 159,889 (159,849) | 104 | 0 | 0 |
| (ii) | 78,556 (78,516) | 104 | 0 | 0 |
| (iii) | 415,324 (415,124) | 520 | 0 | 0 |
| (iv) | 176,828 (176,788) | 104 | 0 | 0 |

The private build with the checks of this page and of the tiles (the final `prove.py`, load about 6 to 9): `Proof.SiteMusic1` 72 s, `SiteMusic2` 51 s,
`SiteMusic3` 272 s, `SiteMusic4` 81 s (round 33: 80, 56, 236, 84 s at load about 4). Natively `LoopTime.recCheckB` is true.

Real runs (`buffer-ctl-check FM2 1100 loopreal`, round 34; the same as round 32): 612 reads of the position at `xAt` (1 on the movie, 316 and 295 on own runs), all at 195 to 197 px, none with the four low
bits 0. A first version of `rtOK` did not allow the coin's erase: it failed at the erase only (20 table states in walks (i), (ii), (iv)).

## Uses from other parts

* Part c: `RoomBlocks.erase_other`, `zI`.
* Part d: `RoomPause.pstep`'s parts (`keepP`, `inP`, `keepP_ok`, `sim_keepBits`, `sim_keep0`, `keepBits_k`, `ph_of_spent`), `EraseRange` (the walk with bounds, `step_rom`, `go_staZp`, `tick_ram`), `ScreenPage` (`preS`, `cov_preS`, `or_bit_of`, `s_stepS`, `sim_clamp`, `findOpZ`),
  `StepWrites` (`keepOK`, `keep_step`, the pieces of `s_pstep`), `ReadTiles.frame_of_walkVI`.
* `Route`: the definition of `a₂` (`ChangesBase.roomStay`: each frame of `[b₁, a₂)` starts in the player's routine), already used by `ChangesK.roomSites`.
* No cycle: `no_xAt` on frame `n` uses the walk of frame `n` (with `SiteX`, not `Xbit`) and the start of frame `n + 1` from the definition of `a₂`.

## What is not proved

* `roomXbit` on the entering frame: there the position's low bits are not 0 when the side pipe's code reads it. On the measured runs the read is at 195 to 197 px;
  the low bits are 0 only at 208 px. A proof needs a bound of the position over frames (the pipe's mouth as a wall).

## Lean

`Theorems/SideRead.lean`: `stAtOf`, `rtOK`, `wsetOK`, `finX`, `XInv`, `rt_step`, `wset_step`, `xinv_zero`, `xinv_stop`, `xinv_step`, `no_xAt`, `xChk`, `xFacts`.
`Theorems/EraseRange.lean`: `SiteX`, `siteX_of`, `siteOK_of_X`, `movX`, `ne_add_one`, `siteOK_movX`, `placesOK_movX`, `stepS_movX`, `keepP_movX`, `preSX`,
`andF0_all`, `andF0_of`, `cov_preSX`, `baseSX`, `s_baseSX`, `pstepX`, `s_pstepX`, `succ_of`; `stepV` uses `pstepX`; `live_stepV`, `frame_of_walkV`, `frameV` give
`SiteX`. `Theorems/ReadTiles.lean`: `frame_of_walkVI` and `frameVI` carry an invariant `J` of the instruction's number and give the frame's end.
`Theorems/LoopTime.lean`: `chk1X`, `chk2X`, `chk4X`, `finAnd`, `spR`, `stR`, `rtR` (the walks use them), `XInvR`, `xJ_of`, `xJs_of`, `xJ0_of`, `FrameOut`,
`pcOut_of`, `walk1B_x`; `RestU` and `RestB` lose `xbit`; `rec_frame1B` to `rec_frame4B` give `FrameOut`; `loop_sites_of_rows` asks `Xbit` only on frame `a − 1`
(`xlast`). `Theorems/Route.lean`: the field `roomXbit`.

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 2 tilecheck      # the four walks with the fifth piece and the checks, then recCheckB and startCheckT natively
.lake/build/bin/smbrta buffer-ctl-check FM2 1100 loopreal    # the reads of the position on real frames
```
