[← Back](README.md) | [English](f-6-16-PoleFrame.md) | [Japanese](f-6-16-PoleFrame-ja.md)

# The touch of the pole: one whole frame

**Claim.** On a real frame that touches the pole, the position at the end of the move, before the write of the pole's routine, is at or right of the left end of the pole's range. The proof follows the whole frame of the touch with an abstract machine, from the idle loop before the NMI to the frame's end, as [The side pipe's entry: one whole frame](c-7-16-SideFrame.md) does for the side pipe. The frame is frame `g` of the frames of the run (`PoleJoin.Run.keep`), so its start (`StartK`) and the condition on each instruction (`CleanK`) are what [One whole frame in control](f-6-19-FrameKeep.md) gives.

So the hypotheses `pass` and `pos` of `PoleJoin.Run` are gone, and so are `fm` and `inp`: the touch is now on frame `g` of `keep`. The hypotheses are `edge`, as for the two pipes, `tiles`, a condition on the byte that a side check reads, and `posKeep`, a condition on each instruction up to the write (`moved` is a theorem now: item 1-1-f-6-18-2 below).

The walk cuts no place. It follows the scroll handler's store of the position at the screen's edges and the routine of the head's collision with a block. The edge store makes the walk forget the position, so right after it the walk splits the position again, as at the end of the move. `edge` says: if he is in the pole's range right after the edge store, he was in it at the end of the move.

**This round (item 1-1-f-6-18).** The head's routine stores through indexes. Before, the walk forgot the position there and split it again after the routine, and `edge` spoke of the head's routine too. Now the walk's guard protects the position's pixel and page (`GP`), so the walk keeps the position through the head's routine. For this, each instruction up to the write meets `PosAt` (the new field `posKeep`): a store through an index or a pointer to the pixel or the page is one of the move routine's two stores of them, with the index 0. So `edge` speaks only of the edge store. `PosAt` is a condition on one state; the part of `edge` that it replaces spoke of two states.

`tr(j)` is the machine `j` instructions into the frame of the touch: from `fm g = all(ix g − 1)` with the input `pad g`. `rt(m)` is `GameEngineSubroutine`, `e_f` the pole's routine. `px(m) = 256·page(m) + x(m)` is the position in pixels, `L = 3158` the left end of the pole's range in pixels, `pg = 12` the pole's page, `col` its column. `T_b`, `T_s` are the tiles of the pole's ball and shaft. `w_edge` is the scroll handler's store of the position at the screen's edges, `h` the routine of the head's collision with a block. `a_edge` is the instruction right after the edge store's store of the page: `again = {a_edge}`. `xI`, `pI` are the RAM bytes of the pixel and the page, and `ps = {s_x, s_p}` are the move routine's two stores of them (`STA zp,X`, right after its store of the fraction). `X(m)` is the index register.

```
WriteStep(n)    :=  rt(tr(n)) ≠ e_f  ∧  rt(tr(n + 1)) = e_f
Touches         :=  ∃ n,  WriteStep(n)
SideRead(m)     :=  pc(m) = the instruction after the block buffer routine's read  ∧  the routine's offset is one of the side check
read(m)         :=  the pointer plus Y: the RAM index that the read took
TileRead(m)     :=  SideRead(m)  ∧  A(m) ∈ {T_b, T_s}   →   read(m) is in the pole's column  ∧  pg ≤ page(m) + 1
HypT(m)         :=  (pc(m) = PlayerSubs → px(m) < L)  ∧  (pc(m) ∈ again → px(m) < L)  ∧  TileRead(m)
PosAt(m)        :=  ∀ t,  m stores through an index or a pointer at t  ∧  t < 0x2000  ∧  (t mod 2048 = xI ∨ t mod 2048 = pI)   →   pc(m) ∈ ps  ∧  X(m) = 0
```

```
no_write_frame      :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)),  FrameStart(s(0)),
                       ∀ j ≤ n,  CleanK(s(j)) ∧ PosAt(s(j)) ∧ HypT(s(j))                     →   rt(s(n + 1)) ≠ e_f
touch_right_of_left :  poleFrameCheck,  Touches,  StartK(fm g),  ∀ j,  CleanK(tr(j)),
                       ∀ n,  WriteStep(n) → ∀ j ≤ n,  PosAt(tr(j)),
                       ∀ n,  WriteStep(n) → ∀ j ≤ n,  TileRead(tr(j))  ∧
                                  (pc(tr(j)) ∈ again ∧ L ≤ px(tr(j))  →  ∃ k ≤ n,  pc(tr(k)) = PlayerSubs ∧ L ≤ px(tr(k)))
                       →   ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ L ≤ px(tr(j))
inRange_of_frame    :  the same,  ∀ n j,  WriteStep(n) → j ≤ n → pc(tr(j)) = PlayerSubs → P = posP(tr(j))     →   P₀ ≤ P
Run.inRange         :  poleFrameCheck,  Run,  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0)   →   P₀ ≤ P₂(g)
pole_frame_check (private) :  poleFrameCheck(sy, m₀) = true   (native_decide)
```

`P₀ = 256·L` is `poleP`. `posP(m) = 256·px(m) + fraction`. `Run.inRange` takes the frame's start from `FrameKeep.Frames.start`, `CleanK` from `keep.clean` (`Frames.cleanAt`), and `PosAt` from `posKeep`. The theorems without the ROM use the axioms `propext`, `Classical.choice`, `Quot.sound` only.

## How it works

**The steps.** The abstract machine is that of `FrameKeep` (`kstep`, `preK`): the steps of `PipeWrites`, with the store of the fraction in the move routine and the sum of its low bits. The guard is that of `FrameKeep` (`guardK`) with the pole's routine, and with the pixel and the page protected (`GP`): a store with a target not known does not change them. At the move routine's two stores of them the walk needs the index (`kstepT`). If the index is known, the target is known and the step is the machine's. If it is known not to be 0 (another object's move), `PosAt` says that the store does not write them. Otherwise the walk fails; the index is split into 0 and not 0 at the routine's entry (`FrameKeep.splitX`), so this does not happen. So the condition on one instruction is `CleanK`, which `keep.clean` asks of every frame up to the touch, and `PosAt` (`cleanK_GP`, `clean_GP`, `s_kstepT`).

**Pieces at five places.** None changes the machine. The walk only divides a state into pieces.

* **The end of the move (`PlayerSubs`).** Under `px < L` the position is in one of 8 pieces: the page in `{0, …, 7}`, `{8, 9}` or `{10}` (two or more pages before the pole's, the pixel not known); the page 11 (the pixel not known); the page 12 with the pixel in `[0, 63]`, `[64, 79]`, `[80, 83]` or `[84, 85]`. The walk keeps the position through the scroll handler, the bounding box, the head's and the feet's checks, and the head's routine (with the pixel and the page protected).
* **Right after the edge store (`again`).** The edge store writes the screen's edge, which the walk does not know. So the position is lost. There it is split again into the same 8 pieces. The proof is by contradiction: no arrival at `PlayerSubs` before the write is in the range. So by `edge` he is left of `L` at `again` too.
* **The addition in a side check, near the pole.** When the page may be 11 or 12, the pixel is split into its values. Then the column of the read and the block buffer are known.
* **The mask of the height in a side check, near the pole.** The high bits of the sum of the height and the adder are split. Then the row of the read is known.
* **After the read of a side check.** If the page is at most 10, or the place read is known and is not in the pole's column, `TileRead` says that the byte read is not a pole tile. The byte is split into pieces that differ from `T_b` at a bit where `T_b` and `T_s` agree (`PoleEntryRule.tilesCover`).

**The read in the pole's column.** On the page 12 the right side reaches the pole's column only with the pixel 83, 84 or 85. The byte read is not known. But the pixel's low 4 bits are 3, 4 or 5, below 6, so the climbing code (`HandleClimbing`) leaves before the comparisons with the pole's tiles. On the page 11 a side check never reads the pole's column.

**No path makes the routine byte the pole's.** The walk checks at every state that the routine byte is known not to be `e_f`, to the frame's end.

**Why `TileRead` and not `TilesOK`.** The old hypothesis `TilesOK` spoke of the bytes of the block buffers. A small Mario at a height of `0xD8` or more reads the row 13 in a side check. On an odd page that is past the end of the second block buffer, in the buffer of the column being drawn, which can hold the pole's tiles. The old `Pass` excluded this with `RowOK`. `TileRead` speaks only of the byte that a side check has read, wherever it is. On real frames no side read was outside the block buffers (below).

**Size.** 8,490,979 steps, 859,283 forks (with the pieces), 0 failures, table 352,579. The search takes 22 s, the check 51 s as a program, 56 s in the private build. With the position split again after the head's routine (the last round) it was 8,150,212 steps, 840,404 forks and a table of 333,418 (17 s, 40 s, 45 s in the build): keeping the position costs 6 % more states. With the two places cut (two rounds ago) it was 8,075,357 steps, 833,579 forks and a table of 326,976. A first version with the pieces of `SideEntryRule` failed 791,304 times: the two pole tiles differ in one bit, so its piece for that bit holds the shaft's tile.

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
* Every instruction of every frame in control meets `PosAt`, not only up to the write of a touch: 382,304 stores through an index to the pixel or the page, each at one of the move routine's two stores with the index 0 (2 in each frame in control: the player's move).
* Every touch (4,665): no edge store and no head's routine before the write, one arrival at `PlayerSubs` before it, the position there at or right of `L` (3158 to 3161 and 3174 to 3177), and the position there is the frame's start moved by the speed there (`P₂ = P + 16·v₂`, `moved`). Before the write each touch has 2 stores through an index to the position, the player's move. So `edge` and `posKeep` hold on every touch.
* 1,361 frames in control come to the edge store or the head's routine: 1,095 after the edge store (all in the random runs, the largest position there 3050) and 266 after the head's routine. None is in the range there unless it was in the range at the end of the move. The head's routine never changed the position.
* Near the pole the head's routine came only in the runs with the position overwritten near the pole's column: 264 times, on the pole's page or the one before. 210 of them are in the range, each already in the range at the end of the move. In the movie it came twice, on the page 10. So near the pole the head's routine can be reached from some states. The walk now follows it with the position known, and no hypothesis needs to exclude it.
* The 1,095 edge stores are all at the screen's left edge (the index 0): the largest position after them is 3050. None is at the right edge.
* No frame in control begins with a pole tile in the block buffers outside the pole's column, or in the column with the page two or more before the pole's. But 90 side reads (all in the runs with the position overwritten near the column) read a byte that is not the byte that was at that place when the frame began: the block buffers can change inside a frame before a side read.

## `moved` is a theorem now (item 1-1-f-6-18-2)

The field `moved` said: at each instruction of the touch's frame at the end of the move (`PlayerSubs`) before the write, the position is `P₂(g)`. Part e's frames are now a definition on `keep`'s machines, and `OnFrames.touchMove` shows that `P₂(g)` is the position at one arrival at the end of the move. A frame in control comes there at one instruction at most ([A frame in control comes to the end of the move at most once](f-6-18-2-SubsOnce.md), two walks of the whole frame that do not cut the write of the pole's routine). So `moved` is the theorem `Run.moved`. Its check is now part of `poleFrameCheck`.

Why this was not done before: the touch writes the position (`FlagpoleCollision` goes on to `PutPlayerOnVine`, which stores the pole's column plus a step in the pixel and sets the speed to 0), so the frame's end does not give `P₂(g)`. On the movie's touch (frame 1092) the move ends at px 3158 = 12·256 + 86 with the fraction 80, and the frame ends at px 12·256 + 89. And part e's `AfterKeep.subs_once` asks that no instruction of the frame writes the routine, the mode or the task by its address; the touch's frame writes the routine. On real touches (`touch-move-check`, 677 touches) the end of the move is passed more than once 0 times.

## Why `tiles`, `edge` and `posKeep` stay (items 1-1-f-6-17, 1-1-f-6-18)

This round tried to prove `tiles` and `edge` from the walk, and to remove `posKeep`. None of the three worked. Nothing in the proof changed.

**`tiles`.** The walk uses `TileRead` only after a read of a side check, in two cases: the page is two or more before the pole's, or the place read is known and is not in the pole's column. Then `TileRead` says that the byte read is not a pole tile. Near the pole the walk already knows the place of each read: the pixel and the high bits of the height are split. So the address does follow from the position on each path. But `TileRead` is not about the address. It is about the byte at the address: the level as it was drawn into the block buffers. The walk does not know those bytes.

A form at the frame's start would be: when frame `g` begins, the block buffers hold a pole tile only in the pole's column, and only when the page is at most one before the pole's. It holds on every real frame in control (above). The walk cannot use it:

* The walk's RAM is not known at the start, and `Sim` ties an abstract state to one machine. "This byte is still the byte of the frame's start" is not a fact that the walk can carry. It needs a new invariant over the steps.
* The block buffers change inside a frame before a side read (90 reads above). The head's routine and the removal of a coin write them through a pointer. So the invariant needs a new condition on each instruction, as `PosAt`.
* The page condition ties the drawing of the level to Mario's page. The area parser draws at the end of each frame, after the player's routine. That is a fact over many frames.

So it would replace one condition by three. `tiles` stays.

**`edge`.** By the code (`ChkPOffscr`, `GetXOffscreenBits`), the store at the left edge puts him at the screen's left edge after the scroll. The store at the right edge puts him a little left of the screen's right edge, and only when he is already closer to that edge than that. When he is right of the right edge by a page or more, the left edge's store is taken. The walk's addition (`TaintRun.aadc`) knows its result only when every bit of both operands is known. So the walk can compare an edge with the position only when both 16-bit numbers are known exactly. Left of `L` there are 3,158 positions, and each edge has 65,536 values. Splitting the edge bytes at the frame's start does not help: the scroll adds the move's amount, which comes from the speed, and the walk does not know the speed. For the right store alone, with the position exact, the right edge's pixel must be exact (256 pieces), and its page exact where the low difference is small enough for that store (16 · 256 pieces). That is about 4,300 pieces for each of the 3,158 positions, 1.4 · 10⁷ pieces in all. The whole walk now has 8.5 · 10⁶ steps. The form on one state (`px < L` right after the store) holds on real frames, but it is a larger hypothesis than `edge`, so it is not used. On real frames every edge store was at the left edge (above). `edge` stays.

**`posKeep` without `PosAt` (a try, not kept).** A version of the walk used, at each store through an index or a pointer, what the state knows of the index and the pointer. It kept the position's bytes when no possible target is one of them, and forgot them otherwise. With no other change the search had 14,751,416 steps and 831,729 failures. The position was forgotten at one place: the head's routine stores through the index `SprDataOffset_Ctrl` (`STA Block_State,X` and others), which the walk does not know. With three more changes (that byte is 0 or 1 at the frame's start and at each load of it, the page's parity is known in the far pieces, the pointer's high byte is kept after a read of the block buffers), the search had 16,997,556 steps, twice the walk now, and still 1,256,685 failures. Two places still forget the position: the score's digits (`STA DisplayDigits,Y`, with an index from the current player and a loop), and the head's store of the blank tile (`STA (pointer),Y`, with the pointer's high byte read from a table at the page's parity). Splitting the index of such table reads took more than 12 GB of memory. So the walk would need more conditions than `PosAt` (on the block objects' offset and the current player) and would be at least twice as long. `posKeep` stays.

## Hypotheses (not proved in Lean)

* **`tiles`**: `TileRead` up to the write. The code that draws the pole's column into the block buffers is not followed.
* **`posKeep`** (new): `PosAt` on each instruction up to the write. It is what lets the walk keep the position through the head's routine. It is not proved: the walk does not follow where the stores through an index point.
* **`edge`**: up to the write, if he is in the pole's range right after the edge store, he was in it at the end of the move. That is, the edge store does not bring him into the range. Last round it spoke of the edge store and of the head's routine; two rounds ago it was: no `w_edge` and no `h` up to the write (as for the two pipes). Each older form implies the newer `edge`; `posKeep` is new. By the code, the edge store at the right edge moves him left; at the left edge it puts him at the screen's left edge, so there `edge` says that the screen's left edge is not in the pole's range. None of this is proved: the walk does not know the screen's edges.
* `touches`, and the frames of `keep` (their own hypotheses).

Only the left end of the range is used. The height decides the row, but no bound on the height comes out.

**Files.** `Theorems/PoleFrame.lean`, `Run` in `Theorems/PoleJoin.lean`, private `Proof/PoleFrame.lean` (`pole_frame_check`).

**To reproduce.**
```
.lake/build/bin/smbrta pole-frame-search          # the search and the check of the walk (about 1 min)
.lake/build/bin/smbrta pole-frame-check FM2 1200  # the hypotheses on real frames (about 6 min)
.lake/build/bin/smbrta touch-move-check FM2 300   # the touch's frame: its start state and its move (about 5 min)
```
