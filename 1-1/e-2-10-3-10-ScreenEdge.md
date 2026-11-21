[← Back](README.md) | [English](e-2-10-3-10-ScreenEdge.md) | [Japanese](e-2-10-3-10-ScreenEdge-ja.md)

# The screen's left edge at the frame's start

This page reports a field that was false on a real frame (round 23), and its fix (round 24, [below](#round-24-the-fix)). Round 23 also narrowed one field (`clampR`, below).

## Round 24: the fix

The new field `collide` and the frames of part e measure the push's bound from a **base**, not from the frame's start. `left(m)` is read as before.

```
edge(m) = 256·left(m) + 255        the last position on the edge's pixel (SurfaceRead.edgeOf)
base(m) = max(P(m), edge(m))        (SurfaceRead.baseOf)

collide (CollideS.P), third case :  P(Q) ≤ P(b) ≤ base(M) + 256  ∧  v(Q) ≤ 0          (round 23: P(b) ≤ P(M) + 256)
edge   (new, each frame 1 ≤ j < g) :  edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))
edge₀  (new, at control)           :  edge(seq 0) ≤ P(seq 0)
TopSpeed.Frame with wide            :  impedeP's third case P′ ≤ B + 256 ∧ v₂ ≤ 0,  B = base(seq (j − 1))
```

**What it adds.** The new third case is weaker than the old one exactly on the frames where edge(M) > P(M): he starts on the edge's pixel (and not at its last position) or left of it. There it allows P(b) up to edge(M) + 256 instead of P(M) + 256. On every other frame it is the old case.

**Why it holds (read from the code, measured, not proved).** When he moves left or not at all at the scroll handler, the screen does not scroll, so the edge is that of M. The clamp puts him on the edge's pixel and keeps the fraction, so after it P ≤ edge(M). At most one push of 1 px follows (the clamp comes before every push: [1-1-e-2-10-3-9](e-2-10-3-9-PositionOrder.md); two pushes in a frame were never measured). So P(b) ≤ max(P(Q), edge(M)) + 256 ≤ base(M) + 256. The edge moves only when the screen scrolls, and the screen scrolls only while he is right of its middle, so it stays behind him: `edge`. At control he is 56 px right of the edge: `edge₀`.

On the false frame of round 23 (`edgeJump`, frame 190): P(b) = 730096, edge(M) = 256·2851 + 255 = 730111, so P(b) ≤ base(M) + 256 = 730367. On random run 188 (push to the right after the clamp): P(b) = 685984 ≤ 256·2678 + 255 + 256 = 686079.

**What is proved with it.** max(P, B) grows by at most the old bound in each frame (`TopSpeed.Frame.posB`, `Frame.advB`), and the bases follow each other (`TopSpeed.ChainB`, from `edge`; `Surface.links`). So the chain after the first hit moves max(P, B) by at most `reach` (`SurfaceRun.chainB_reach`, `hit_boundB`), and the first `N + E` frames move it by at most `16·top` a frame (`PoleJoin.early_leB`). The edge stays behind a position he had (`OnFrames.edge_behind`), so the first hit and the frame after it are bounded by the model's positions (`Surface.hit`, `Surface.base`). The position's range uses the base too (`OnFrames.readAllB`). The route's numbers do not change: no table, no `farN`, no count of part e changed, and the margin at frame 233 is still 16.

**`edge₀` from the rows (measured, not wired).** A native check on the private machine (a scratch file, removed after the run) shows that the rows of the change out of the side pipe ([1-1-d-2-3](d-2-3-SideChangeEnd.md)) know the two bytes of the edge at every state with control, with the values of the machine at control, and that there edge ≤ P. The route takes its state at control from the rows with the sound's tables ([1-1-d-3-4-2](d-3-4-2-SideChangeSound.md), [1-1-d-3-4-3](d-3-4-3-SidePause.md)), other parts' files and checks, so `edge₀` stays a field.

**Measured (round 24, `edge-real FM2 256`, exit 0; the checks of the new fields on every frame, clean or not).**

| runs | frames | start below the edge | clamp frames | most P(b) − P(a), clamp frames | most P(b) − P(Q), clamp frames | most P(b) − base(a), frames with a call and v(Q) ≤ 0 (the field asks ≤ 256) | most edge(b) − max(base(a), P(b)) (the field asks ≤ 0) | fields that fail |
|---|---|---|---|---|---|---|---|---|
| the movie from frame 852 | 239 | 0 | 0 | | | 256 | −14097 | 0 |
| `edgePipe` with its five endings | 1,060 | 200 | 240 | 240 | 256 | 256 | 0 | 0 |
| `edgeJump` | 191 | 26 | 34 | 496 | 512 | 256 | 0 | 0 |
| 256 random runs from the movie's frames 852 to 1091 | 63,164 | 252 | 15,204 | 496 | 768 | 256 | 0 | 0 |
| 256 random runs from the movie's frames 992 to 1011, mostly Left | 73,301 | 4,962 | 32,812 | 496 | 768 | 256 | 0 | 0 |

At control (the movie's frame 852) edge − P = −14081 (pixel 2616, left edge 2560). On the frames after one that starts below the edge, P(b) − P(a) ≤ 496. Both new bounds are reached exactly (256 and 0). `collide-real FM2 200` (exit 0) checks `CollideS` at every arrival at the scroll handler and `edge` on every frame of its runs: 0 failures. `surface-frames-check FM2 200` checks the new move of `TopSpeed.Frame` on every frame in control (`impedeP`) and `Moves` with `edge` on the clean frames.

**Not proved.** The fields `collide`, `edge` and `edge₀` are assumptions. That one push at most follows the clamp, and that the screen does not scroll when he moves left or not at all, are read from the code and measured.

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
- `CollideS.P` (`collide`) is false on the frame above. Round 24 fixed it with the base ([above](#round-24-the-fix)). A bound P(b) ≤ P(M) + 512 would not do: it adds 3,248 to `reach` over the first 17 frames after a hit, and the hit table has no room for it (a first hit from frame 8 already fails the table with 256); and with a borrow of the fraction, the clamp and a push to the right in one frame the code allows P(b) − P(M) up to 752.
- The plan of the brief, an induction over part e's frames for left(M) ≤ pixel(M), needs the relation above instead: left(M) − 1 ≤ pixel(M), with pixel(M) = left(M) − 1 only after a push to the left at the edge.

**Not proved (round 23).** Everything in the sections from here on is measured. The relation at the frame's start, the bounds on the frames that start below the edge, and the clamp's rule (the clamp at the left edge comes only when pixel ≤ left) are not proved.

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
