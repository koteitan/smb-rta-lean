[← Back](README.md) | [English](a-5-4-3-3-3-OpenMap.md) | [Japanese](a-5-4-3-3-3-OpenMap-ja.md)

# The block buffers, the jumpspring and the player's state on the first frames

**Claim.** On every frame from control to the counted frame `N` (`N = 32`), counted or not, the two block buffers are those of the machine at control `m₀`, the
jumpspring byte is 0, and the player's state is 0, 1 or 2. So the fields `st` and `spring` of [The opening on real frames](a-5-4-OpenFrames.md) are no longer assumed.
In their place one condition on each instruction of these frames is asked (`map`, `MapOK`): a store through an index or a pointer does not write the player's state, the
jumpspring byte or the block buffers, and the read of the block buffer routine is inside the first block buffer.

The block buffers are the two tables of 13 rows of 16 tiles that the collision code reads. `B` is the set of their 416 bytes. At control they hold 5 kinds of tile:
empty, ground, a brick and two kinds of block with an item. None of them is a jumpspring or a climbing tile.

`seq(n)` is the machine when frame `n` begins, `ix(t)` the frame where the counted frame `t` begins, `fm(t) = seq(ix t)`. `tr_n(k)` is the machine `k` instructions into
frame `n`. `st(m)` is the player's state, `js(m)` the jumpspring byte. `R` is the place of the `LDA (zp),Y` of the block buffer routine, `addr(m)` the address it reads,
`val(m)` the byte it reads.

```
MapAt(m)    :=  ∀ d ∈ B,  m(d) = m₀(d)   ∧   js(m) = 0   ∧   st(m) ≤ 2
MapOK(m)    :=  store:  a store through an index or a pointer of m does not write st, js or a byte of B
                read:   pc(m) = R  →  addr(m) is in the RAM and its byte is in the first block buffer (B₁ ⊂ B)
```

```
readVal_ram     :  m is not tracked,  addr(m) < 0x2000   →   val(m) = m(addr(m))
s_tstep         :  CleanK(m),  A covers m,  RdOK(m)   →   one of the steps of the walk covers the step of m
map_frame_start :  mapCheck,  FrameStart(m),  MapAt(m),  ∀ k: CleanK(tr(k)) ∧ RdOK(tr(k)),  frame(m, i) ends in control
                   →   FrameStart(frame(m, i))  ∧  MapAt(frame(m, i))
map_run         :  the same on every frame n ∈ [a, b) of a sequence   →   ∀ n ∈ [a, b],  MapAt(seq n)
Begin.map₁      :  check (TitleStart),  titleMapCheck   →   MapAt(seq 1)  ∧  st(seq 1) = 0                 (any input, Start included)
Lags.mapAt      :  lagCheck,  pauseCheck,  mapCheck,  Lags,  FrameStart(seq 1),  MapAt(seq 1),  b ≤ ix(E),
                   ∀ n ∈ [1, b), ∀ k: MapOK(tr_n(k))   →   ∀ n ∈ [1, b],  MapAt(seq n)
Real.stSpring   :  the checks,  Real (with the field map),  FrameStart(seq 1),  MapAt(seq 1)
                   →   ∀ t ∈ [1, N],  t < E  →  st(fm t) ∈ {0, 1, 2}  ∧  js(fm t) = 0                     (the old fields st and spring)
map_reads       :  the conditions of map_frame   →   at each read R of the frame with no NMI coming, ∀ d ∈ B,  m(d) = m₀(d)      (the walk's step at R asks it)
map field       :  ∀ n,  1 ≤ n ≤ ix(N),  n < ix(E),  ∀ k:  MapOK(tr_n(k))
```

`CleanK` here is `PipeWrites.Clean` of the guard of a frame in control (the field `lags.clean`) with the player's state, the jumpspring byte and `B` protected too: that is
`Clean` and the store part of `MapOK` (`cleanK_of`). `RdOK` is the read part of `MapOK` (`rdOK_of`). The theorems without the ROM use only the axioms `propext`,
`Classical.choice`, `Quot.sound`. `#print axioms route_1_1` shows no `sorryAx`.

Lean: `Theorems/OpenMap.lean` (`map_reads`, with `liveT_all`); `StSpring`, `Real.stSpring`, the field `Real.map` in `Theorems/OpenFrames.lean`; `Run.pipeOpening`, `Run.pipeOpenB` in
`Theorems/Route.lean`; private `Proof/OpenMap.lean` (`open_map_check`, `open_title_map_check`).

## How it works

**At control.** The near states of [From Start on the title to control](0-5-3-TitleStart.md) know every byte of both block buffers. `titleMapCheck` walks frame 0 again
from each near or held state, with any input, and asks at each end with control that `B` has the values of `m₀`, the jumpspring byte is 0 and the player's state is 0
(about 2.5 s natively).

**One whole frame.** The walk is that of `FrameKeep` ([part f](f-6-19-FrameKeep.md)), the same as `walk_check` of
[Every frame from control to the pipe starts in the idle loop](a-5-5-3-2-StartRun.md), with these changes:

* The bytes of `B` and the jumpspring byte are watched: known at the start with their values, and asked again at the frame's end. With the player's state they are
  protected: a store through an index or a pointer does not touch them (`MapOK.store`).
* The player's state is known at the start, as 0, 1 or 2 (six start states). At the frame's end it must be known and at most 2, or the frame ends out of control (the
  routine, the task or the mode known not to be those of control).
* At the read of the block buffer routine the walk does not know the pointer. If the read is in `B` (`MapOK.read`) and the walk knows every byte of `B`, the byte read
  is one of the 5 tiles: `val(m) = m(addr(m)) = m₀(addr(m))` (`readVal_ram`, `Sim`). So the walk follows one path for each tile (`tstep`, with `ScreenPage.readStep`).
  The routines that set the jumpspring byte (landing on a jumpspring tile) and the climbing state (touching a climbing tile) compare the tile with constants. With the
  tile known they never take that branch.

The search keeps the zero page temporaries of the collision code (where the tile is kept between the read and the comparisons) and splits its table there by `A` and these
bytes. The search is no part of the proof. Without it the walk joined paths with different tiles and failed on 89 frame ends (the climbing state, the jumpspring byte 1).

| walk | steps | forks | failures | table | time |
|---|---|---|---|---|---|
| `mapCheck` | 865,443 | 86,197 | 0 | 59,377 | search 4.9 s, with the check 6 to 7 s; the private proof 8.6 s with `titleMapCheck` |

**Frame to frame.** `map_run` is an induction over all frames, counted or not, as `StartRun.starts_dep`. A frame ends in control: a counted frame by `lags.ctl`, a frame
not counted by the check of [LagFrames](a-5-5-3-LagFrames.md) (`Lags.known_end`). So its end has state 0, 1 or 2. `Real.stSpring` takes `b = ix(t)`.

## Checked on real frames

Program `open-map-check FM2 300`. From the machine at control it runs each frame up to the counted frame 33, instruction by instruction.

| runs | frames | instructions | reads of the block buffer routine | not `MapOK` | a frame starts with `B` not that of `m₀`, `js ≠ 0` or `st > 2` |
|---|---|---|---|---|---|
| own inputs (300), the TAS (1), a pause on one of the first 4 frames for 43 to 82 frames (60) | 27,261 | 74,386,942 | 82,929 | 0 | 0 |

* On all these frames the area parser does not run and the screen does not move. The position stays at most 78 px. The high byte of the height is 1.
* On the ground, every frame starts with the same height, and with the vertical speed and its fraction 0.
* No store through an index or a pointer writes the pause byte or the bytes of `CtrlKeep.spareI`.
* At the TAS's control the block buffers are those of `m₀`.

## Assumed (not proved in Lean)

* **`map`**: `MapOK` on each instruction of the frames from frame 1 to the counted frame `N`, that one included. A condition on single instructions. It would fail when
  the screen scrolls far enough for the area parser to write the buffers, or on a read outside the first buffer (he is on page 0, so the columns he reads are those of
  the first buffer); neither happens on these frames. This round the read is asked to be in the first buffer (it was: in either buffer), and the frame of the counted
  frame `N` is included: [The flat ground of the opening](a-5-4-3-4-1-OpenFlat.md) needs both.
* **No longer assumed**: `st` and `spring` (item 1-1-a-5-4-3-3-3).
* **No longer assumed**: `flat` (item 1-1-a-5-4-3-4-1): a walk that reads the tiles by the known bits of the address sees the ground under the feet, with the new field
  `ground` ([The flat ground of the opening](a-5-4-3-4-1-OpenFlat.md)).
* **Not proved**: `jump` (item 1-1-a-5-7): the height in the air is not followed from frame to frame (`vstep` and the arcs of [The height of a jump](c-2-Jump.md) would
  give it, as part c did for the first 8 frames of a jump).

**Files.** `Theorems/OpenMap.lean`, `Theorems/OpenFrames.lean`, `Theorems/Route.lean`, private `Proof/OpenMap.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-map-walk                  # the search and the check of the walk (about 12 s)
.lake/build/bin/smbrta open-map-check FM2 300         # the title's check, the walk, and the real frames (about 25 s)
```
