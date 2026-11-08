[← Back](README.md) | [English](a-5-1-PipeEntryRule.md) | [Japanese](a-5-1-PipeEntryRule-ja.md)

# Entering the vertical pipe, on real frames

**Claim.** This is a partial result. "He enters" is defined on real machines. If a frame enters, then when the frame's foot check goes to read the right foot's block, Mario's position is not left of the left end of the pipe's window. The proof follows one pass of the foot check with an abstract machine. It does not follow the rest of the frame. The rest stays as the hypotheses `Pass` and `pos`.

`Route` does not use `Pass` of this page. It uses [the theorem on the whole frame](a-5-2-PipeWrites.md).

The names are those of [Entering the vertical pipe](a-4-PipeEntry.md). `frame(m, i)` is the real frame with the input `i`. `tr(n)` is the machine `n` instructions into that frame. `rt(m)` is `GameEngineSubroutine`. `e_v` is the number of the pipe's routine. `page(m)` is `Player_PageLoc`, `x(m)` is `Player_X_Position`. `w` is the instruction in `HandlePipeEntry` that writes `rt`. `T_R` is the pipe's right tile, `d_R` its place in the block buffer.

```
Enters(m, i)    :=  rt(m) ≠ e_v  ∧  rt(frame(m, i)) = e_v
WriteStep(n)    :=  rt(tr(n)) ≠ e_v  ∧  rt(tr(n + 1)) = e_v
px(m)           :=  256·page(m) + x(m)
L_px            :=  256·pg + x_lo

Start(m)        :=  pc(m) = DoFootCheck, the stack pointer has its value, the byte with the offset of the foot adders is the value of a big or a small Mario,
                    the dot is after the end of vblank and before the frame's end, no NMI, no vblank, no strobe
AtEntry(m)      :=  pc(m) = BlockBufferCollision  ∧  register Y is the right foot's number
AtRead(m)       :=  pc(m) = this routine's `LDA (zp),Y`  ∧  the saved Y is the right foot's number
RowOK(m)        :=  Y mod 16 = 0  ∧  Y < 16·R   (R is the number of rows of a block buffer)
TilesOK(m)      :=  page(m) ≤ pg  →  ∀ place d of the block buffers,  mem(d) = T_R  →  d = d_R  ∧  pg ≤ page(m) + 1
Pass(n)         :=  pc(tr(n)) = w  ∧  ∃ n₀ ≤ n,  Start(tr(n₀))
                    ∧  (∀ j ∈ [n₀, n],  pc(tr(j)) ∉ {DoPlayerSideCheck, AwardTouchedCoin, HandleAxeMetatile, ImpedePlayerMove})
                    ∧  (∀ j ∈ [n₀, n),  AtRead(tr(j))  →  RowOK(tr(j)) ∧ TilesOK(tr(j)))
```

```
no_write            :  ruleCheck,  s(j + 1) = step(s(j)) (j < n),  Start(s(0)),
                       (∀ j < n,  AtEntry(s(j)) → px(s(j)) < L_px),  (∀ j < n,  AtRead(s(j)) → RowOK ∧ TilesOK),
                       no exit (j ≤ n)                                          →  pc(s(n)) ≠ w
entry_right_of_left :  ruleCheck,  Enters(m, i),  (∀ n,  WriteStep(n) → Pass(n))
                       →  ∃ n j,  WriteStep(n) ∧ j < n ∧ AtEntry(tr(j)) ∧ L_px ≤ px(tr(j))
rule_on_frames      :  ruleCheck,  ∀ t,  Enters(fm t, inp t) → (∀ n, WriteStep(n) → Pass(n)),
                       (P₂(t) is the position at the right foot: P₂(t) = 256·px(tr(j)) + f,  0 ≤ f)
                       →  ∀ t,  Enters(fm t, inp t)  →  L ≤ P₂(t)
pipe_rule_check (private)    :  ruleCheck(sy, m₀) = true (native_decide)
```

`L = 256·L_px` is `windowP` of [Entering the vertical pipe](a-4-PipeEntry.md). The theorems without the ROM use the axioms `propext`, `Classical.choice`, `Quot.sound` only.

Lean: `Theorems/PipeEntryRule.lean`, private `Proof/PipeEntryRule.lean` (`pipe_rule_check`, `pipe_rule_real`). `pipe_no_entry_real`, which `Route` uses, is on [the whole frame](a-5-2-PipeWrites.md) and [The frames up to the pipe, read from the machines](a-5-5-PipeFrames.md).

## How it works

**The abstract machine.** It is the machine of [The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md). It starts from the state of `Start`. Only the stack pointer and the offset of the foot adders are known. The rest of the RAM, the registers, the position, the speeds and the block buffers are not known. The pad is not known.

**Pieces at four places.** None of this changes the machine. The walk only divides a state into pieces (`preR`).

* On entering `BlockBufferCollision` for the right foot: under `px < L_px`, one piece per position. There are at most `pg + 1` pages. This makes the pointer known.
* The left foot's read: pieces by the 8 bits of the pointer. The value read is not known.
* The right foot's read: pieces by the row, from `RowOK`, and by "the byte read differs from `T_R` at this bit", from `TilesOK`. Before that the walk checks that no row is the place `d_R`, or that `T_R` cannot be there yet (`safe`).
* States with the same pointer are then put together (the table).

**After the read.** The known bit of the byte read goes into a temporary byte. The `CMP` in `HandlePipeEntry` sees that bit and knows that they differ. So no path comes to `w`. Every path comes to an exit or into a state of the table (`walkR`).

**Size.** 46,751 steps, 17,580 forks, no failure, a table of 493. Between 1 and 2 seconds as a program, about 3 seconds in the private proof build.

## Following a whole frame (measured)

This was measured by a program. It is no theorem. The frame is the TAS frame just before the entry, with one enemy. "Not joined" is a search that does not join Mario's bytes. "Pointer split" is dividing by the pointer's 8 bits at the block buffer's read.

| not known | steps | forks | failures | first failure |
|---|---|---|---|---|
| the pad; not joined | 484,361 | 29,913 | 179 | `GetBlankPal` (time reaches the frame's end) |
| the pad | 7,009 | 210 | 4 | `BlockBufferCollision` |
| the pad; pointer split | 233,976 | 34,284 | 160 | `DBlockSte` |
| `x`, `y`, both speeds; enemy flags 0 | 198,605 | 20,729 | 144 | `BlockBufferCollision` |
| the same; pointer split | 513,200 | 75,456 | 316 | `DBlockSte` |
| 31 bytes of Mario; enemy flags 0 | 101,641 | 10,425 | 110 | `JumpEngine` |
| the same; pointer split | 376,546 | 51,237 | 272 | `JumpEngine` |
| `x`, `y`, both speeds; slots real; pointer split | 284,659 | 44,884 | 158 | `DBlockSte` |
| 31 bytes of Mario; slots real; pointer split | 198,583 | 27,583 | 186 | `JumpEngine` |
| the same; 56 enemy bytes too (flags and IDs real) | 84,843 | 16,095 | 156 | `JumpEngine` |
| 35 sound bytes | 1,857,523 | 4,656 | 650 | `HandleSquare2Music` |
| the screen buffer | 34 | 0 | 1 | `UpdateScreen` |

So with the machine of this table a whole frame does not close. The failures are at these places. With what is missing here added as a condition, it closes ([next page](a-5-2-PipeWrites.md)).

* Reads through a pointer that is not known: `BlockBufferCollision`, `DBlockSte`, `HandleSquare2Music`, `UpdateScreen`.
* A write through a pointer that is not known: `ErACM`.
* The indirect jump when `Player_State` is not known: `JumpEngine`.
* Without joining Mario's bytes, the time reaches the frame's end: `GetBlankPal`.
* With the position not known, the level parser forks: 2,632 times at one branch of `ProcessEnemyData`.

The sound bytes and the screen buffer change from frame to frame, so they cannot be fixed to one value (read from the code).

A part of a frame is small. The pass of this theorem is above. From `PlayerCtrlRoutine` to `PlayerBGCollision`, with only 4 bytes known, takes 1,804 steps (the 8 failures are `UseAdder`, a write at an index X not known at the start). So the single-frame facts of parts a, c, e and f should go by parts of the frame, from one named place to another, not by whole frames.

**The candidates for the write (counted from the code; no proof).** 12 instructions write `rt` directly, and only `w` writes `e_v`. 338 zero page indexed writes exist. 9 writes go through `(zp),Y`. So proving item 1-1-a-5-2 needs a range for the index or the pointer at those 347 places.

## Checked on real frames

This is a program (`pipe-rule-check`).

| run | frames | foot checks (in control) | frames that enter |
|---|---|---|---|
| the TAS up to the entry | 368 | 368 | 1 |
| the TAS after the entry | 1,300 | 347 | 0 |
| from states before the entry: walk, then Down | 5,480 | 5,480 | 161 |
| from states before the entry: jump, land with Down (some overwritten to a big Mario) | 25,308 | 24,161 | 14 |
| from states before the entry: random inputs | 26,855 | 26,143 | 1 |
| the same, overwritten to a big Mario | 9,000 | 8,457 | 0 |

* In every row, each foot check in control meets `Start`, and each read of the right foot meets `RowOK` and `TilesOK`.
* All 177 frames that enter write with `w`, at the end of one pass. Their positions are all 9 values of the window and none outside. The position does not change after the foot check.

## Assumed (not proved in Lean)

* **The write in `Pass` ([the whole frame](a-5-2-PipeWrites.md) has the conditions `FrameStart`, `Clean` for it).** The only instruction that makes `rt` equal to `e_v` is `w`; earlier in that frame the foot check started; from there it came to no exit. This is read from the code and checked on the real frames above. The rest of the frame (NMI, sound, screen, enemies) is not followed.
* **`Start`.** The stack pointer, the offset of the foot adders, the dot and the flags. The value of a big Mario in water is in.
* **`RowOK`.** Read from the code's `AND`, `SBC`, `TAY` and the `CMP` at the foot check's start. It is assumed on this page. [The whole frame](a-5-2-PipeWrites.md) does not assume it.
* **`TilesOK` (item 1-1-a-5-3).** This is narrower than "the same as the hand-written block buffer": it is about the right tile only. The page condition says that the pipe's column is not yet in the buffer when he is on the page two before it, which has the same parity.
* **`pos`.** `P₂` is the position on entering the routine for the right foot. It is part of making `Frame` from real frames (item 0-0-0-3-1).
* **The right end of the window and the rest of `rule`.** Only the left end is given here, and `Route` uses only the left end: `Route.Pipe` has `start`, `clean`, `tiles` and `pos` in place of `rule`. The right end, Down and the landing stay with `rule` of [Entering the vertical pipe](a-4-PipeEntry.md), on the hand-written buffer.

**Files.** `Theorems/PipeEntryRule.lean`, private `Proof/PipeEntryRule.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-rule-check FM2    # the check of one pass and the hypotheses on real frames, about 50 seconds
```
