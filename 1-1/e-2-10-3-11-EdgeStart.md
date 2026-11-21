[← Back](README.md) | [English](e-2-10-3-11-EdgeStart.md) | [Japanese](e-2-10-3-11-EdgeStart-ja.md)

# At control the screen's left edge is behind him

**Claim (round 25).** The field `edge₀` of the frames above ground (`SurfaceFrames.OnFrames`) is a theorem. With edge(m) = 256·left(m) + 255 (`SurfaceRead.edgeOf`; left(m) is the screen's left edge, pixel and page, read at the two operands of the clamp found in the program of m, `ScreenClamp.places`):

```
edge_zero :  Start(B, m)  ∧  StartK(m0, m)  ∧  Numbers(m0, B, J)   →   edge(m) ≤ P(m)
AreaRun.edge₀ :  0 < g  →  edge(seq 0) ≤ P(seq 0)                  (proved in OnFrames.areaRun)
```

`Start(B, m)` is the state at control that the rows of the change out of the side pipe give (`Route.Run.start`). `StartK(m0, m)` says that m starts a frame in control (`FrameKeep.StartK`). `Numbers` is what `numbersCheck`, the check on the ROM of the machine at control `B.m`, says.

**Proof.**

- `Start` has two more fields, `edgeX` and `edgeP`: at the two operands of the clamp found in the program of `B.m`, m has the bytes of `B.m`. The check of the rows (`rowStart`) asks that every state of the rows with control knows these two bytes with the values of `B.m`, and `start_of_state` proves the two fields from it. The check is a part of `rowsStart`, so of `startCheck` (the rows of [1-1-d-2-3](d-2-3-SideChangeEnd.md)) and of `SideChangeSound.startCheckK` (the rows with the sound's tables, [1-1-d-3-4-2](d-3-4-2-SideChangeSound.md), which the route uses).
- `numbersCheck` checks three more things on `B.m`: it has the program and the program's mask of `m0` (`Numbers.prgB`, `Numbers.maskB`), and edge(B.m) ≤ P(B.m) (`Numbers.edgeB`).
- A machine that starts a frame in control has the program and the mask of `m0` (the fields `prg`, `mask` of `StartK`). The clamp's operands are read from the program only (`SurfaceRead.places_congr`, with `findOp_congr`), so for m they are those of `B.m`. So edge(m) = edge(B.m) ≤ P(B.m) = P(m).
- The machine at control starts a frame in control when there is a counted frame: for 0 < g the frames of `K` up to the touch's frame start so (the argument `hst`), and the first of them is `seq 0`. `AreaRun`, which `OnFrames.areaRun` builds from `Numbers`, `Start` and `hst`, carries the result as `edge₀`. `OnFrames.readAllB`, `OnFrames.edge_behind` (new argument `Ar`) and `surface_of_frames` use it in place of the old field. `Surface.base₁` is asked when 1 ≤ g; its one use (`PoleJoin.hB_of_line`) has a frame 1 ≤ e ≤ g.

**Fields.** Removed: `OnFrames.edge₀`. Added: none. Changed, all proved: `Start` (`edgeX`, `edgeP`), `numbersCheck` and `Numbers` (`prgB`, `maskB`, `edgeB`), `AreaRun` (`edge₀`), `Surface.base₁` (asked when 1 ≤ g).

**Measured.** In round 24 a native check on the private machine showed that the rows of [1-1-d-2-3](d-2-3-SideChangeEnd.md) know the two bytes at control. Round 25 ran it again with the rows with the sound's tables too (a scratch file in the private project, removed after the run): all three lists of rows know both bytes with the values of `B.m` at every state with control, edge(B.m) ≤ P(B.m), and `B.m` has the program of `m0` (exit 0). At control (the movie's frame 852) edge − P = −14081: he is 56 px right of the edge.

## The field `edge` (one frame) stays

```
edge :  1 ≤ j < g  →  edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))        base(m) = max(P(m), edge(m))
```

**What the code does (read from the code; what the scroll handler does is proved in [1-1-e-2-10-3-12](e-2-10-3-12-ScrollRule.md), the rest is not).** The scroll handler is the first call at the end of the player's routine (at `Q`). It moves the left edge by Y px, with 0 ≤ Y ≤ X, where X is the move of this frame in whole pixels (when no jumpspring moves) plus the platforms' force on the scroll; Y is X, or X − 1, or 1 when X = 1. It moves it only when four bytes allow it: the scroll lock is 0, the byte of his place on the screen is at least 80, the side collision's timer is 0, and 1 ≤ X ≤ 128 (as a byte). The byte of his place on the screen is written in the frame before, when the player is drawn (after the player's routine and the enemies); it is pixel − left of that time, modulo 256, and it is not written on a frame where the player blinks after a hit. After the scroll the clamp at the screen's edge runs, then the collision routine.

**Why a proof of one frame does not fit in this round.**

- The byte of his place on the screen comes from the frame before. So a proof needs a relation of that byte with the position at each frame's start (a frame-to-frame invariant), or a new condition on one state that says it.
- A frame that starts 1 px left of the edge (5,440 measured frame starts, [1-1-e-2-10-3-10](e-2-10-3-10-ScreenEdge.md)) has the byte 255, which is at least 80. There only the side collision's timer stops the scroll: the push that left him there sets it. So that relation needs the timer too.
- The two bytes of the edge are not followed from the frame's start to `Q`: they are not among the bytes that the walk of `CtrlKeep` keeps up to the player's routine (`CtrlKeep.keepA`), nor among the bytes that `FrameKeep.guardE` protects. The walk of `AfterKeep` from `Q` to the frame's end follows one byte and stops at any store to it, and the scroll stores both bytes right after `Q`. So the keep before `Q` needs a new byte in `keepA` (a change to the walk of every part), and the keep after the scroll needs a walk that starts after the scroll's stores and two more protected bytes in `guardE` (the field `keep.cleanE` would ask more).
- The scroll's rule itself (Y and its conditions) is proved in this round, by pieces of the ROM's code with those bytes as known values: [The scroll's rule](e-2-10-3-12-ScrollRule.md) (`ScrollRule.scroll_rule`; the whole call of the scroll handler, up to the instruction after it, with the edge as a position: `ScrollRule.scroll_edge`). The other three things above remain; the keep after the scroll is now needed only from the instruction after the call.

**Measured (round 25, `edge-real FM2 256`).** See the table below.

## The number of pushes in a frame and `Moves.stop` stay

By the code the collision routine calls the push (`ImpedePlayerMove`) at most once; the routine of the platforms can call it again. The walks after the scroll handler do not know the objects, so they reach that routine. A bound on the number of pushes needs the objects (no platform in the enemies' slots) as a known part of the walk's state; `Moves.stop` needs that bound. Both stay. Measured below: the most calls in one frame.

`edge-real FM2 256` (exit 0, 44 min natively, 67 MB; the same runs as round 24, and no field fails on them). The edge moved on 11,289 of 137,955 frames, never back, never more than 3 px, and never more than his move in that frame (left(b) − left(a) ≤ pixel(Q) − pixel(a)). At every frame start after the first of a run, the byte of his place on the screen was pixel − left mod 256. P is in 1/256 px: the least P(b) − edge(b) on a frame where the edge moved, 20,225, is 79 px.

| runs | frames | frames where the edge moves | the most it moves in a frame | the least P(b) − edge(b) on them | the least pixel(Q) − left(Q) on them | frame starts where his place on the screen ≠ pixel − left mod 256 | the least pixel − left at a frame start where his place ≥ the threshold and the timer is 0 | the most pushes in a frame | the most clamps in a frame | frames with a clamp and a push |
|---|---|---|---|---|---|---|---|---|---|---|
| the movie from frame 852 | 239 | 208 | 3 px | 20,593 | 82 | 0 | 80 | 1 | 0 | 0 |
| `edgePipe` with its five endings | 1,060 | 90 | 3 px | 28,273 | 113 | 0 | 81 | 1 | 1 | 205 |
| `edgeJump` | 191 | 18 | 3 px | 28,273 | 113 | 0 | 81 | 1 | 1 | 26 |
| 256 random runs from the movie's frames 852 to 1091 | 63,164 | 7,384 | 3 px | 20,225 | 81 | 0 | 80 | 1 | 1 | 255 |
| 256 random runs from the movie's frames 992 to 1011, mostly Left | 73,301 | 3,589 | 3 px | 21,249 | 85 | 0 | 80 | 1 | 1 | 5,022 |

**Files:** `Theorems/SurfaceFrames.lean` (`Start`, `edgeBytes`, `rowStart`, `start_of_state`, `numbersCheck`, `Numbers`, `edge_zero`, `AreaRun.edge₀`, `OnFrames.areaRun`, `OnFrames.readAllB`, `OnFrames.edge_behind`, `Surface.base₁`, `surface_of_frames`), `Theorems/SurfaceRead.lean` (`findOp_congr`, `places_congr`), `Theorems/PoleJoin.lean` (one line in `hB_of_line`), `Main.lean` (`edge-real`: new measurements). The scroll's rule: `Theorems/ScrollRule.lean` ([1-1-e-2-10-3-12](e-2-10-3-12-ScrollRule.md)).
