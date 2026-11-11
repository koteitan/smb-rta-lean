[← Back](README.md) | [English](f-6-1-PoleEntryRule.md) | [Japanese](f-6-1-PoleEntryRule-ja.md)

# Touching the pole, on real frames

**Claim.** This is a partial result. "He touches" is defined on real machines. If a frame touches, then when the frame's side check reads the page, Mario's position is not left of the left end of the pole's range. So the hypothesis `inRange` of `PoleJoin.Run` is gone, and it is now the theorem `Run.inRange`. The proof follows one pass of the side check with an abstract machine. It does not follow the rest of the frame. The rest stays as the hypotheses `Pass` and `pos`.

**Now replaced in the run.** `PoleJoin.Run` no longer uses this pass. [The touch of the pole: one whole frame](f-6-16-PoleFrame.md) follows the whole frame of the touch, so `Pass` and `pos` are no longer hypotheses of the run, and `Run.inRange` comes from that walk. This page stays as the proof of one pass, and its program checks the old hypotheses on real frames.

`frame(m, i)` is the real frame with the input `i`. `tr(n)` is the machine `n` instructions into that frame. `rt(m)` is `GameEngineSubroutine`. `e_f` is the number of the pole's routine. `page(m)` is `Player_PageLoc`, `x(m)` is `Player_X_Position`. `pg` is the pole's page, `col` its column. `w` is the instruction in `RunFR` that writes `rt`. `T_b`, `T_s` are the tiles of the pole's ball and shaft. `d_C` is the top of the pole's column in the block buffers. `R` is the number of rows of a block buffer.

```
WriteStep(n)    :=  rt(tr(n)) ≠ e_f  ∧  rt(tr(n + 1)) = e_f
Touches(m, i)   :=  ∃ n,  WriteStep(n)
EndsTouch(m, i) :=  rt(m) ≠ e_f  ∧  rt(frame(m, i)) = e_f
px(m)           :=  256·page(m) + x(m)
L_px            :=  256·pg + 16·col − 10

Start(m)        :=  pc(m) = DoPlayerSideCheck, the stack pointer has its value, the byte with the offset of the adders is the value of a big or a small Mario,
                    the dot is after the end of vblank and before the frame's end, no NMI, no vblank, no strobe
AtEntry(m)      :=  pc(m) = the instruction in BlockBufferCollision that reads the page  ∧  register Y is a number of the side check  ∧  register X = 0
AtRead(m)       :=  pc(m) = this routine's `LDA (zp),Y`
RowOK(m)        :=  Y mod 16 = 0  ∧  Y < 16·R
TilesOK(m)      :=  ∀ place d of the block buffers,  mem(d) ∈ {T_b, T_s}  →  (∃ r < R,  d = d_C + 16·r)  ∧  pg ≤ page(m) + 1
Pass(n)         :=  pc(tr(n)) = w  ∧  ∃ n₀ ≤ n,  Start(tr(n₀))
                    ∧  (∀ j ∈ [n₀, n],  pc(tr(j)) ∉ {ExSCH, ExCSM, ExHC, ContSChk, VineCollision})
                    ∧  (∀ j ∈ [n₀, n),  AtRead(tr(j))  →  RowOK(tr(j)) ∧ TilesOK(tr(j)))
pos(P₂)         :=  ∀ n j,  WriteStep(n)  →  j < n  →  AtEntry(tr(j))  →  ∃ f ≥ 0,  P₂ = 256·px(tr(j)) + f
```

```
no_write            :  walkCheck,  s(j + 1) = step(s(j)) (j < n),  Start(s(0)),
                       (∀ j < n,  AtEntry(s(j)) → px(s(j)) < L_px),  (∀ j < n,  AtRead(s(j)) → RowOK ∧ TilesOK),
                       no exit (j ≤ n)                                          →  pc(s(n)) ≠ w
touch_right_of_left :  ruleCheck,  Touches(m, i),  (∀ n,  WriteStep(n) → Pass(n))
                       →  ∃ n j,  WriteStep(n) ∧ j < n ∧ AtEntry(tr(j)) ∧ L_px ≤ px(tr(j))
inRange_of_pass     :  ruleCheck,  Touches(m, i),  (∀ n,  WriteStep(n) → Pass(n)),  pos(P₂)  →  P₀ ≤ P₂
Run.inRange         :  ruleCheck,  Run  →  P₀ ≤ P₂(g)          (up to this round; now from the whole frame, f-6-16)
touches_of_ends     :  EndsTouch(m, i)  →  Touches(m, i)
pole_rule_check (private) :  ruleCheck(sy, m₀) = true (native_decide)
```

**A correction.** `Touches` used to be what is now `EndsTouch`: the frame ends with the pole's routine. That is false on every direct grab, the TAS included. The flag's routine (`FlagpoleRoutine`) runs later in the same frame. It finds him at or below `FlagGrabY`, and it starts the end of the level (`GiveFPScr`). So the TAS's frame of the touch (frame 1092) goes from the control routine to the end of the level, and never ends with `e_f`. Each direct grab has its height at or below `FlagGrabY` (`IsDirect`), so no direct grab met `touches` of `Run`. The program counted touches by the instruction of the write, so it did not see this. Now `Touches` says that an instruction of the frame writes `e_f`. The theorems are the same: their proofs used only that instruction. The old form still gives the new one (`touches_of_ends`).

`P₀ = 256·L_px` is `poleP`. The theorems without the ROM use the axioms `propext`, `Classical.choice`, `Quot.sound` only.

Lean: `Theorems/PoleEntryRule.lean`, private `Proof/PoleEntryRule.lean` (`pole_rule_check`, `pole_rule_real`). `Run` in `Theorems/PoleJoin.lean` used them up to this round.

The fields of `Run` changed as follows.

* Removed: `inRange`.
* Added: `fm`, `inp` (the machine when frame `g` begins, and its input), `touches` (`Touches(fm, inp)`), `pass` (`∀ n, WriteStep(n) → Pass(n)`), `pos` (`pos(P₂(g))`).
* Then removed: `fm`, `inp`, `pass`, `pos`. `touches` is now `Touches(fm g, pad g)` on frame `g` of `keep`. Added: `tiles`, `edge`, `moved` ([The touch of the pole: one whole frame](f-6-16-PoleFrame.md)).

## How it works

**The abstract machine.** It is the machine of [The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md), used as in [Entering the vertical pipe, on real frames](a-5-1-PipeEntryRule.md). It starts from the state of `Start`. Only the stack pointer and the offset of the adders are known. The rest of the RAM, the registers, the position, the height, the speeds and the block buffers are not known. The pad is not known.

**Pieces at three places.** None of this changes the machine. The walk only divides a state into pieces (`preP`).

* Before the addition of the position: the 256 values of `x`. This needs no hypothesis. If the sum's column is not the pole's, `x` is forgotten after it.
* Before the read of the page: under `px < L_px`, one piece per page. If `x` is still known, only the `n` with `256·n + x < L_px`. This makes the pointer known.
* Before the read of the block buffer: `RowOK` gives the row, and `TilesOK` the form "the byte read differs from `T_b` at some bit". Only bits where `T_s` agrees with `T_b` are used (`tilesCover` checks this). So the byte is neither of the pole's tiles. This is done when no row is in the pole's column, or when the tiles cannot be there yet (`page + 1 < pg`) (`safe`).

**The read that is not divided.** The pointer is the pole's column and the tiles may be there. Since `px < L_px`, this is an offset of the right side, with `page = pg`. Then `x` is one of three values, where the right side reaches the column and he is still left of the left end. The value read is not known. But the low 4 bits of `x` are below `ClimbLowNybble`, so the comparison in `HandleClimbing` goes to the exit `ExHC`.

**The value read, afterwards.** Its known bit goes into a temporary byte and back into `A`. The two `CMP` in `ChkForFlagpole` see that bit and find "not equal". So no path comes to `w`. Every path goes to an exit or into a state of the table (`walkP`).

**Size.** 82,604 steps, 43,676 forks (with the pieces), 0 failures, table 5,296. About 3 s as a program, 3 to 11 s for the private proof's build (with other builds running).

## The instructions that write the pole's number into `rt`

Read from the code. This is not a proof. 12 instructions write `rt` directly.

| instruction | value |
|---|---|
| `SetPESub` | the entrance routine |
| before `GameIsOn` | the first routine |
| `PlayerRdy`, `DonePlayerTask` | the control routine |
| after the death music | the lose-life routine |
| `INC` at `NoFPObj` | one more; it runs inside the pole's routine, so it writes the number after the pole's |
| after `GiveFPScr` | the end-of-level routine |
| `SetPRout` | change of size, injury, death |
| `ChkGERtn` | the side pipe's routine |
| **`RunFR` (`w`)** | **the pole's routine** |
| `VineCollision` | the vine's routine |
| `HandlePipeEntry` | the vertical pipe's routine |

So only `w` writes the pole's number directly. `w` is reached only from `FlagpoleCollision`, and that only from `HandleClimbing`, which is only in the side check. The foot check and the head check do not go there.

**What does not count as a touch.**

* While he slides, `rt = e_f` all through the frame. `w` writes the same value again. That is no `WriteStep`, so the frame is not `Touches`.
* A frame in which an indexed write or a write through a pointer makes `rt` equal `e_f` meets `Touches`, but not `pc(tr(n)) = w` of `Pass`. So the hypotheses of `Run` leave it out. It does not occur on real frames. As [the vertical pipe's page](a-5-1-PipeEntryRule.md) says, there are 347 candidates for such a write, and their ranges are not proved.

## On real frames

A program (`pole-rule-check`).

| run | frames | side checks (control) | reads | frames that touch | heights |
|---|---|---|---|---|---|
| the movie, frames 1 to 1239 after the first control | 1,239 | 707 | 2,861 | 1 | 1 |
| the movie to frame 1089, then `02808080` | 20 | 4 | 13 | 1 | 1 |
| every input of Left, Right, A, B for 6 frames, from 2 frames of the movie | 12,912 | 8,880 | 29,872 | 48 | 1 |
| the same for 5 frames, position moved forward by 5 amounts (as `touch-search-at`) | 4,688 | 4,240 | 16,960 | 2,873 | 4 |
| random inputs towards the pole | 10,940 | 10,768 | 40,619 | 87 | 20 |
| the same, overwritten to a big Mario | 3,778 | 3,718 | 14,044 | 30 | 13 |
| jumps of 7 lengths from 22 frames of the movie | 10,192 | 9,874 | 37,824 | 14 | 9 |
| one frame from each height and position near the column, overwritten | 6,864 | 5,901 | 17,301 | 936 | 39 |

* In every row, every side check of a frame in control meets `Start`. Every read meets `RowOK` and `TilesOK`.
* Every frame that touches writes by `w`, and at the end of one pass. None is left of the left end. The position when the page is read is the position when the collision routine starts (`pos`).
* The positions are only 0 to 3 and 16 to 19 pixels from the left end of the range. These runs have frames at all those positions.
* `pole-join-check` also reads the new fields of `Run`: `f = 80` on the TAS, `f = 64` on frame 1089 then `02808080`, `f = 112` on the TAS with A held (another touch, `g = 234`).
* The routine at the end of the frame of the touch: the end of the level on the TAS and on frame 1089 then `02808080` (both direct grabs), the pole's routine on the touch with A held. Of the 676 touches of `pole-frac-check` (random inputs from control and from the movie's frames 1002 to 1091), 17 are at `FlagGrabY` or lower, and exactly these 17 end with the end of the level.

## Hypotheses (not proved in Lean)

* **The write part of `Pass`.** Only `w` makes `rt` equal `e_f`. The side check started earlier in the frame. It did not go to an exit since. Read from the code, checked on the real frames above. The rest of the frame (NMI, sound, screen, enemies) is not followed.
* **`Start`.** The stack pointer, the adders' offset, the dot, the flags. The value of a big Mario in water is left out. The stack pointer is that of the control routine, not that of the entrance routine (through `AutoControlPlayer`).
* **`RowOK`.** Read from the code: its `AND`, `SBC`, `TAY` and the `CMP` at the start of the side check. The abstract machine's addition loses the bits, so it does not check this.
* **`TilesOK`.** Narrower than the assumption of a hand-written block buffer: it is only about the pole's two tiles. The condition on the page says that the column is not in the buffer yet two pages before the pole's. The code that writes the column into the buffer is not followed.
* **`pos`.** `P₂(g)` is the position when the page is read. This is part of making a `Frame` from a real frame.
* **The right end of the range, and the height.** Only the left end comes out here, and `Run` uses only the left end. The same walk with the pieces on the right side should give the right end, but this was not tried. The height decides the row of the read, but this pass does not follow it.

**Files.** `Theorems/PoleEntryRule.lean`, private `Proof/PoleEntryRule.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta pole-rule-check FM2    # the check of one pass, and the hypotheses on real frames, about 40 s
.lake/build/bin/smbrta pole-join-check FM2 1089 02808080    # every field of Run, on the late touch
```
