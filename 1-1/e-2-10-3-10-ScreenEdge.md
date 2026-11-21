[← Back](README.md) | [English](e-2-10-3-10-ScreenEdge.md) | [Japanese](e-2-10-3-10-ScreenEdge-ja.md)

# The screen's left edge at the frame's start

This page is a measurement, and it reports a field that is false. No theorem here is new, but one field is narrowed (`clampR`, below).

**Notation.** At a machine m, left(m) is the screen's left edge and pixel(m) the player's whole pixel, both with their pages (256 per page). They are read at the two operands of the clamp at the screen's edge (`ScreenClamp.places`). M is the machine at a frame's start, Q the machine at the scroll handler, b the machine at the frame's end. P is the position in 1/256 px (`posP`), v the speed.

## The relation at the frame's start is not left(M) ≤ pixel(M)

Round 21 measured left(M) ≤ pixel(M) on every frame start, and the plans for `clampR`, `Moves.stop` and `CollideS.P` used it. It is false on real runs. On the measured frames:

```
left(M) − 1 ≤ pixel(M) ≤ left(M) + 120
pixel(M) = left(M) − 1  →  v(M) = 0  ∧  bit 0 of the collision bits is 0 (Right is blocked)
right(M) − left(M) = 255
```

**How it happens.** He stands at the screen's left edge, against a wall on his right (here the pipe before the staircase). In each frame the clamp at the screen's edge puts him at the edge (+1 px). Then the collision routine finds the wall at his right side and the push (`ImpedePlayerMove`) moves him 1 px left, sets the speed to 0 and blocks Right. So the frame ends 1 px left of the edge. The next frame does the same. Such a frame does not start clean (the collision bits block Right), so `surface-frames-check`, which looks at the clean frames, does not check `collide` on it.

## A field that is false on a real frame: `collide`

On the frame after such a frame, the push can stop (a jump takes him above the pipe's top). If he moves left on that frame and the fraction of the position goes below 0, Q is 2 px left of the edge, and the clamp puts him back at the edge with that fraction. On the run `edgeJump` of `edge-real` (inputs of my own from the movie's frame 996; its frame 190):

```
M : pixel 2850, left 2851, fraction 0, v = 0
Q : P(Q) = P(M) − 16       (v(Q) = −1: pixel 2849, fraction 240)
    the clamp, no push      (the frame calls the clamp: Calls)
b : P(b) = P(Q) + 512 = P(M) + 496,  v(b) = 0
```

`CollideS.P` asks, on a frame with a call that does not keep a speed to the right:

```
P(b) = P(Q)  ∨  P(b) = P(Q) − 256  ∨  (P(Q) ≤ P(b) ≤ P(M) + 256  ∧  v(Q) ≤ 0)
```

Here P(b) − P(M) = 496 > 256. So the field `collide` of `OnFrames` (and so of `Route.Run`) is false on this real frame, and `route_1_1` does not cover this run. The run is a whole run: with inputs of my own after it that run right and jump up the staircase, `route-check` (the movie up to frame 996, then these inputs) finds the touch on frame 1396 and the level change on frame 2063, and all the numbers of the route hold (exit 0). The frame above is frame 1187, a counted frame before the touch, and the touch is less than `farN` frames after control (544 frames after frame 852), so the route uses `collide` on it. The move of `TopSpeed.Frame` that `OnFrames.readE` builds from `collide` (`impedeP`: P' = P₂, P₂ − 256, or P' ≤ P + 256 with v₂ ≤ 0) is false there too, and with it the bound of `Frame.adv_le` for a slow frame (256).

**A second way.** Random runs found the same kind of frame in another way: on random run 188 of `edge-real 256` (from the movie's frame 904), frame 190 starts 1 px left of the edge at the top of a jump with the fraction 176 and v(Q) = −1, so Q is 1 px left of the edge; the clamp puts him at the edge, and then the push finds a wall on his left side and moves him 1 px right. Again P(b) = P(Q) + 512 = P(M) + 496. A random run that mostly holds Left (run 188 of the second group) found the first way.

**The bound that held.** After the clamp, P = 256·left + f(Q), where f is the fraction, and P(M) = 256·(left − 1) + f(M) on such a frame; a push after the clamp moves him 1 px more, either way. On the 5,440 measured frames that start below the edge, P(b) − P(M) ≤ 496, and over such a frame and the frame before it, P moved at most 496 (< 2·256): the frame before is a frame of the push, which does not move him right.

## What this means for the fields of part e

- `clampR`: on a frame that starts 1 px left of the edge, v(M) = 0 and Right is blocked by the collision bits, so pressing Right does not speed him up to the right there (this is read from the code, not proved), and `ClampR` speaks only when v > 0. `ClampR` held at every clamp with v > 0 on the runs of `pos-keep-real` and on `edgePipe` with its five endings. Round 23 asks it only where `PositionKeep.keep_frame` uses it: on a frame that moves right at the scroll handler and ends with that speed ([1-1-e-2-10-3-8](e-2-10-3-8-PositionKeep.md)).
- `Moves.stop` is asked only on clean frames; a frame that starts below the edge is not clean. It held on every measured frame.
- `CollideS.P` (`collide`) is false on the frame above. A fix needs a weaker third case for a frame that starts below the edge (for example P(b) < P(M) + 512), and then a change of `TopSpeed.Frame.impedeP` and of the bounds that use it (`Frame.adv_le`). The two frames together moved less than 2·256 on every measured case; a bound over two frames could keep the per-frame argument. This is not done.
- The plan of the brief, an induction over part e's frames for left(M) ≤ pixel(M), needs the relation above instead: left(M) − 1 ≤ pixel(M), with pixel(M) = left(M) − 1 only after a push to the left at the edge.

**Not proved.** Everything on this page is measured. The relation at the frame's start, the bounds on the frames that start below the edge, and the clamp's rule (the clamp at the left edge comes only when pixel ≤ left) are not proved.

## Measured

`edge-real FM2 N` (a program, no part of the proof) reads at each frame start pixel(M) − left(M) and right(M) − left(M), and runs `SurfaceFrames.movesScan` on every frame, clean or not; it also checks the move of `TopSpeed.Frame` on every frame. Its exit code is 1 when a field fails: on these runs it is 1, because of the frame above.

| runs | frames | pixel(M) − left(M) | start below the edge | of them other than 1 px below, v = 0, Right blocked | `collide` fails | `Frame` move fails | other fields fail (`posW`, `clampR`, `Moves.stop` on clean frames) |
|---|---|---|---|---|---|---|---|
| the movie from frame 852 (300 frames) | 239 | 56 to 113 | 0 | 0 | 0 | 0 | 0 |
| `edgePipe`, then 40 frames of Left, nothing, Right, A+Left, B+Left | 1,060 | −1 to 112 | 200 | 0 | 0 | 0 | 0 |
| `edgeJump` | 191 | −1 to 112 | 26 | 0 | 1 | 1 | 0 |
| 256 random runs of my own from the movie's frames 852 to 1091 | 63,164 | −1 to 120 | 252 | 0 | 1 | 1 | 0 |
| 256 random runs of my own from the movie's frames 992 to 1011 that mostly hold Left | 73,301 | −1 to 112 | 4,962 | 0 | 1 | 1 | 0 |

(`edge-real FM2 256`, 29 min natively. With N = 64 the two random groups had 17,390 and 18,232 frames, 0 and 1,413 frames below the edge, and no field failed.)

`edgePipe` and `edgeJump` are inputs of my own from the movie's frame 996, found with random inputs that go left and then by trying the times of a jump.

**File:** `Main.lean` (`edge-real`). Changed: `Theorems/PositionKeep.lean` (`keep_frame`), `Theorems/SurfaceFrames.lean` (`OnFrames.clampR`, `OnFrames.keepAt`, `movesScan`).
