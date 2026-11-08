[← Back](README.md) | [English](a-5-2-PipeWrites.md) | [Japanese](a-5-2-PipeWrites-ja.md)

# One whole frame: who writes the routine byte

**Claim.** An abstract machine follows a frame that starts in control, from its first instruction to its end. In a frame where the routine byte becomes the pipe's, the block buffer routine was entered for the right foot before that write, and the position there is not left of the left end of the pipe's window. `Pass` and `RowOK` of the [page before](a-5-1-PipeEntryRule.md) are no longer assumed. Three assumptions remain: the state at the frame's start `FrameStart`, a condition on each instruction `Clean`, and the tile's condition `TilesOK`. Each is a condition on one state.

The names are those of the [page before](a-5-1-PipeEntryRule.md). `tr(n)` is the machine `n` instructions into the frame. `rt` is `GameEngineSubroutine`, `e_v` is the pipe's routine. `S` is the stack pointer in the foot check.

```
Prot            :=  {rt, OperMode, OperMode_Task, the byte with the offset of the foot adders} ∪ the top of the stack [0x100 + S − 32, 0x1FF]
Plain(t)        :=  (t is in RAM ∧ its RAM place ∉ Prot)  ∨  (0x4000 ≤ t ∧ t is neither DMA nor the pad)
target(m)       :=  the address the instruction of m writes (for the instructions below)

Clean(m)        :=  store:  if the instruction of m is STA/STY zp,X, DEC/INC zp,X, STA abs,X, DEC/INC/ROR abs,X, STA abs,Y, STA (zp),Y:  Plain(target(m))
                    read:   if the instruction of m is LDA (zp),Y:  the address read is in RAM or ROM
                    jump:   if pc(m) = JumpEngine:  A(m) < the length of its table
                    time:   if pc(m) ≠ EndlessLoop:  dot(m) ≤ dotsPerFrame − 64

FrameStart(m)   :=  pc(m) = EndlessLoop  ∧  the stack pointer has its value there
                    ∧  (dot = 0 ∧ no vblank ∧ no NMI  ∨  1 ≤ dot ≤ 9 ∧ vblank ∧ NMI)
                    ∧  bit 7 of PPUCTRL is 1  ∧  no strobe  ∧  the sprite-0 flag fits the dot  ∧  not halted
                    ∧  rt = the player's routine  ∧  OperMode = game  ∧  OperMode_Task = game core

HypG(m)         :=  (AtEntry(m) → px(m) < L_px)  ∧  (AtRead(m) → TilesOK(m))
TilesAll(m)     :=  ∀ place d of the block buffers,  mem(d) = T_R  →  d = d_R  ∧  pg ≤ page(m) + 1
```

A program counts the length of a table from the ROM. It counts the words after `JSR JumpEngine` up to a word that does not point into the ROM, or up to the address an earlier word points to.

```
no_write_frame      :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)) (j ≤ n),  FrameStart(s(0)),
                       (∀ j ≤ n,  Clean(s(j)) ∧ HypG(s(j)))                         →  rt(s(n + 1)) ≠ e_v
entry_right_of_left :  ruleCheckG,  Enters(m, i),  FrameStart(m),
                       (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))))
                       →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ AtEntry(tr(j)) ∧ L_px ≤ px(tr(j))
rule_on_frames      :  ruleCheckG,  ∀ t,  Enters(fm t, inp t) → FrameStart(fm t),  Clean and TilesOK as above,
                       (P₂(t) is the position at the right foot: P₂(t) = 256·px(tr(j)) + f,  0 ≤ f,  j ≤ n)
                       →  ∀ t,  Enters(fm t, inp t)  →  L ≤ P₂(t)
tiles_of_steps      :  TilesAll(s(0)),  (∀ k < N,  TileStep(s(k), s(k + 1)))         →  ∀ k ≤ N,  TilesOK(s(k))
pipe_frame_check (private)   :  ruleCheckG(sy, m₀) = true (native_decide)
pipe_no_entry_real (private) :  start, clean, tiles, pos and the position hypotheses of `pipe_no_entry`  →  ∀ t ≤ 367,  ¬Enters(fm t, inp t)
```

The theorems with no ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/PipeWrites.lean`, private `Proof/PipeWrites.lean`.

## How it works

**The abstract machine.** It is the machine of [`TaintRun`](b-2-3-TaintRun.md). Only three bytes are known: `rt`, `OperMode`, `OperMode_Task`; and bit 7 of `PPUCTRL` and the stack pointer. Every other byte of RAM, the registers and the pad are not known.

**Steps added to the machine.** Each is proved to keep `Sim`. `TaintRun` is not changed.

* A store through an index or a pointer whose address is not known. By `Plain`, `Prot` does not change. Every other byte of RAM becomes not known (`forgetW`).
* `LDA (zp),Y` through a pointer not known. The address is no register, so the machine does not change. The value read is not known.
* `ADC abs,Y`. If the top 4 bits of `A` are known, the value added has no low 4 bits and the carry is 0, the top 4 bits of the sum are known.

**Where it divides (`preG`).** None of this changes the machine.

* The time: by `time`, the window's top is cut.
* `JumpEngine`: by `jump`, `A` is divided by the entries of the table.
* `DoFootCheck`: the vertical position is divided by its top bits. The ones too low leave the foot check at its `CMP`.
* Where the right foot loads the vertical position: it is divided by its top 4 bits. So `Y` at the read is one value, and `RowOK` is not needed.
* The entry for the right foot: under the hypothesis `px < L_px`, by the value of the position. There are at most `pg + 1` pages.
* The read of the right foot: the pointer and `Y` are known, so the place read is known. If it is in the block buffers and is not `d_R`, or the tile cannot be there yet, `TilesOK` divides it into "differs from `T_R` at some bit".

**What is checked (`walkG`).** On every path the next state's `rt` is not `e_v`. The `CMP` in `HandlePipeEntry` sees the foot's bit, so no path comes to `w`. The other direct writes write known values. The walk goes on to the frame's end, keeping one bit of `rt`.

**The search (no part of the proof).** Outside the collision routine, states with the same stack and routine byte are joined.

**Size.** 1,504,949 steps, 166,506 forks, 0 failures, table 57,015, 8,169 instructions passed. Stores with an address not known at 496 places, reads through a pointer not known at 40 places. About 4 seconds as a program.

## Checked on real frames

This is a program (`pipe-rule-check`). The conditions were checked on every instruction of every frame that starts in control, not only on the frames that enter.

| run | frames | start in control | instructions | frames that enter |
|---|---|---|---|---|
| the TAS up to the entry | 368 | 368 | 1,917,255 | 1 |
| the TAS after the entry | 1,300 | 351 | 1,635,098 | 0 |
| from states before the entry: walk, then Down | 5,480 | 5,480 | 27,774,369 | 161 |
| from states before the entry: jump, land with Down (some overwritten to a big Mario) | 25,308 | 24,161 | 145,324,806 | 14 |
| from states before the entry: random inputs | 26,855 | 26,295 | 130,905,665 | 1 |
| the same, overwritten to a big Mario | 9,000 | 8,570 | 43,271,021 | 0 |

* In every row: 0 frames fail `FrameStart`, 0 instructions fail `Clean`, 0 reads of the right foot fail `TilesOK`.
* All 177 frames that enter write with `w`. Their positions are all 9 values of the window and none outside. The position at the entry for the right foot is one value up to the write, and it does not change up to the frame's end.
* The write's dot is at most 25,622. The dot of an instruction of a frame in control is at most 69,101.
* When control comes, `T_R` is not in the block buffers. Stores of `T_R` through an index or a pointer happen 91 times in all. All go to `d_R`, with the page at least `pg − 1`. While `T_R` is there, the page does not go below `pg − 1`.
* `store` of `Clean` does not hold outside the frames in control: `InitializeMemory`, which clears RAM, writes `rt`. In frames in control too, indexed stores reach the low part of the stack's page. So `Prot` has only the top of the stack.

## Assumed (not proved in Lean)

* **`FrameStart` (item 1-1-a-5-2-1).** A frame that enters starts in the idle loop, in control.
* **`Clean` (item 1-1-a-5-2-2).** The four conditions on each instruction up to the write. The ranges of indices and pointers that were needed are now this one condition. No proof comes from indices being small. `time` is about the frame's last 64 dots.
* **`TilesOK` (item 1-1-a-5-3).** `tiles_of_steps` reduces it to a condition `TileStep` on one instruction at a time. `Route` does not use that. `T_R` comes into the block buffers from the level parser. The parser's bytes are not followed.
* **`pos` (item 1-1-a-5-9).** `P₂` is the position at the entry for the right foot. It is part of making `Frame` from real frames (item 0-0-0-3-1).
* **The right end of the window.** Only the left end is given here. `Route` uses only the left end.

**Files.** `Theorems/PipeWrites.lean`, private `Proof/PipeWrites.lean`. It uses the definitions of `Theorems/PipeEntryRule.lean`. The symbols `JumpEngine`, `EndlessLoop` were added.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-rule-check FM2    # the check of one frame and the hypotheses on real frames, about 2 minutes
```
