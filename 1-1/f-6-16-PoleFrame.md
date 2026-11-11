[← Back](README.md) | [English](f-6-16-PoleFrame.md) | [Japanese](f-6-16-PoleFrame-ja.md)

# The touch of the pole: one whole frame

**Claim.** On a real frame that touches the pole, the position at the end of the move, before the write of the pole's routine, is at or right of the left end of the pole's range. The proof follows the whole frame of the touch with an abstract machine, from the idle loop before the NMI to the frame's end, as [The side pipe's entry: one whole frame](c-7-16-SideFrame.md) does for the side pipe. The frame is frame `g` of the frames of the run (`PoleJoin.Run.keep`), so its start (`StartK`) and the condition on each instruction (`CleanK`) are what [One whole frame in control](f-6-19-FrameKeep.md) gives.

So the hypotheses `pass` and `pos` of `PoleJoin.Run` are gone, and so are `fm` and `inp`: the touch is now on frame `g` of `keep`. The new hypotheses are `moved` and `edge`, as for the two pipes, and `tiles`, a condition on the byte that a side check reads.

`tr(j)` is the machine `j` instructions into the frame of the touch: from `fm g = all(ix g − 1)` with the input `pad g`. `rt(m)` is `GameEngineSubroutine`, `e_f` the pole's routine. `px(m) = 256·page(m) + x(m)` is the position in pixels, `L = 3158` the left end of the pole's range in pixels, `pg = 12` the pole's page, `col` its column. `T_b`, `T_s` are the tiles of the pole's ball and shaft. `w_edge` is the scroll handler's store of the position at the screen's edges, `h` the routine of the head's collision with a block.

```
WriteStep(n)    :=  rt(tr(n)) ≠ e_f  ∧  rt(tr(n + 1)) = e_f
Touches         :=  ∃ n,  WriteStep(n)
SideRead(m)     :=  pc(m) = the instruction after the block buffer routine's read  ∧  the routine's offset is one of the side check
read(m)         :=  the pointer plus Y: the RAM index that the read took
TileRead(m)     :=  SideRead(m)  ∧  A(m) ∈ {T_b, T_s}   →   read(m) is in the pole's column  ∧  pg ≤ page(m) + 1
HypT(m)         :=  (pc(m) = PlayerSubs → px(m) < L)  ∧  TileRead(m)  ∧  pc(m) ∉ {w_edge, h}
```

```
no_write_frame      :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)),  FrameStart(s(0)),
                       ∀ j ≤ n,  CleanK(s(j)) ∧ HypT(s(j))                                   →   rt(s(n + 1)) ≠ e_f
touch_right_of_left :  poleFrameCheck,  Touches,  StartK(fm g),  ∀ j,  CleanK(tr(j)),
                       ∀ n,  WriteStep(n) → ∀ j ≤ n,  TileRead(tr(j)) ∧ pc(tr(j)) ∉ {w_edge, h}
                       →   ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ L ≤ px(tr(j))
inRange_of_frame    :  the same,  ∀ n j,  WriteStep(n) → j ≤ n → pc(tr(j)) = PlayerSubs → P = posP(tr(j))     →   P₀ ≤ P
Run.inRange         :  poleFrameCheck,  Run,  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0)   →   P₀ ≤ P₂(g)
pole_frame_check (private) :  poleFrameCheck(sy, m₀) = true   (native_decide)
```

`P₀ = 256·L` is `poleP`. `posP(m) = 256·px(m) + fraction`. `Run.inRange` takes the frame's start from `FrameKeep.Frames.start` and `CleanK` from `keep.clean` (`Frames.cleanAt`). The theorems without the ROM use the axioms `propext`, `Classical.choice`, `Quot.sound` only.

## How it works

**The steps.** The abstract machine is that of `FrameKeep` (`kstep`, `preK`): the steps of `PipeWrites`, with the store of the fraction in the move routine and the sum of its low bits. So the condition on one instruction is `CleanK`, which `keep.clean` asks of every frame up to the touch. The guard is that of `FrameKeep` (`guardK`) with the pole's routine.

**Pieces at four places.** None changes the machine. The walk only divides a state into pieces.

* **The end of the move (`PlayerSubs`).** Under `px < L` the position is in one of 8 pieces: the page in `{0, …, 7}`, `{8, 9}` or `{10}` (two or more pages before the pole's, the pixel not known); the page 11 (the pixel not known); the page 12 with the pixel in `[0, 63]`, `[64, 79]`, `[80, 83]` or `[84, 85]`. The walk keeps the position through the scroll handler, the bounding box and the head's and the feet's checks.
* **The addition in a side check, near the pole.** When the page may be 11 or 12, the pixel is split into its values. Then the column of the read and the block buffer are known.
* **The mask of the height in a side check, near the pole.** The high bits of the sum of the height and the adder are split. Then the row of the read is known.
* **After the read of a side check.** If the page is at most 10, or the place read is known and is not in the pole's column, `TileRead` says that the byte read is not a pole tile. The byte is split into pieces that differ from `T_b` at a bit where `T_b` and `T_s` agree (`PoleEntryRule.tilesCover`).

**The read in the pole's column.** On the page 12 the right side reaches the pole's column only with the pixel 83, 84 or 85. The byte read is not known. But the pixel's low 4 bits are 3, 4 or 5, below 6, so the climbing code (`HandleClimbing`) leaves before the comparisons with the pole's tiles. On the page 11 a side check never reads the pole's column.

**No path makes the routine byte the pole's.** The walk checks at every state that the routine byte is known not to be `e_f`, to the frame's end.

**Why `TileRead` and not `TilesOK`.** The old hypothesis `TilesOK` spoke of the bytes of the block buffers. A small Mario at a height of `0xD8` or more reads the row 13 in a side check. On an odd page that is past the end of the second block buffer, in the buffer of the column being drawn, which can hold the pole's tiles. The old `Pass` excluded this with `RowOK`. `TileRead` speaks only of the byte that a side check has read, wherever it is. On real frames no side read was outside the block buffers (below).

**Size.** 8,075,357 steps, 833,579 forks (with the pieces), 0 failures, table 326,976. The search takes 19 s, the check 42 s as a program; `Proof.PoleFrame` builds in 44 s. A first version with the pieces of `SideEntryRule` failed 791,304 times: the two pole tiles differ in one bit, so its piece for that bit holds the shaft's tile.

## On real frames

A program (`pole-frame-check FM2 1200`, exit 0, bad 0). The runs of [Touching the pole on real frames](f-6-1-PoleEntryRule.md) and random inputs from the movie's frames 1002 to 1091.

| run | frames | side reads | touches |
|---|---|---|---|
| the movie, frames 1 to 1239 after the first control | 1,239 | 2,797 | 1 |
| the movie to frame 1089, then `02808080` | 20 | 13 | 1 |
| every input of Left, Right, A, B for 6 frames, from 2 frames of the movie | 12,912 | 29,872 | 48 |
| the same for 5 frames, position moved forward by 5 amounts | 4,688 | 16,960 | 2,873 |
| random inputs towards the pole | 10,940 | 40,619 | 87 |
| the same, overwritten to a big Mario | 3,778 | 14,044 | 30 |
| jumps of 7 lengths from 22 frames of the movie | 10,192 | 37,824 | 14 |
| one frame from each height and position near the column, overwritten | 6,864 | 17,301 | 936 |
| random inputs from the movie's frames 1002 to 1091 (1,200 runs) | 137,055 | 521,670 | 675 |

* Every frame in control meets `StartK`; every instruction meets `CleanK`; every read of a side check meets `TileRead`; no read of a side check is outside the block buffers.
* Every touch (4,665): no cut place before the write, one arrival at `PlayerSubs` before it, the position there at or right of `L` (3158 to 3161 and 3174 to 3177), and the position there is the frame's start moved by the speed there (`P₂ = P + 16·v₂`, `moved`).
* 1,361 frames come to a cut place, none of them before a touch's write.

## Hypotheses (not proved in Lean)

* **`tiles`**: `TileRead` up to the write. The code that draws the pole's column into the block buffers is not followed.
* **`edge`**: no `w_edge` and no `h` up to the write, as for the two pipes.
* **`moved`**: `P₂(g)` is `posP` at `PlayerSubs` before the write: part of making the frame model from the real frame, as for the two pipes.
* `touches`, and the frames of `keep` (their own hypotheses).

Only the left end of the range is used. The height decides the row, but no bound on the height comes out.

**Files.** `Theorems/PoleFrame.lean`, `Run` in `Theorems/PoleJoin.lean`, private `Proof/PoleFrame.lean` (`pole_frame_check`).

**To reproduce.**
```
.lake/build/bin/smbrta pole-frame-search          # the search and the check of the walk (about 1 min)
.lake/build/bin/smbrta pole-frame-check FM2 1200  # the hypotheses on real frames (about 6 min)
```
