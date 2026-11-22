[← Back](README.md) | [English](e-2-10-3-21-StopEdge.md) | [Japanese](e-2-10-3-21-StopEdge-ja.md)

# A frame that stops him at the screen's left edge

The field `Moves.stop` (round 28) speaks of a frame that moves right at the scroll handler, ends with the speed 0 and ends at the position it had at the scroll handler. It asks that the position at the scroll handler is at most 1 px past that of the frame's start. Round 31 measured 6 such frames. On each of them one clamp at the screen's edge came and no push, and every clamp measured was the clamp at the left edge. Here the frames where he is at or left of the screen's left edge at the scroll handler are proved, when the frame starts at or right of it. The field is asked only on the other frames.

**Claim (round 32).** Write

```
a       = the end of the counted frame before (seq (j − 1)),  b = the frame's end (seq j)
Q       = the first instruction at the scroll handler's call (PlayerSubs) after the arrival at the player's routine
pix(m)  = his pixel with its page (two bytes),  left(m) = the screen's left edge with its page (two bytes)
P(m)    = 256·pix(m) + f(m),  f the fraction;  v(m) = his speed
```

`StopEdge.stop_of_edge`:

```
pix(Q) ≤ left(Q)  ∧  left(a) ≤ pix(a)  ∧  left(Q) = left(a)   →   P(Q) ≤ P(a) + 255
```

`SurfaceFrames.OnFrames.stopAt`: on each counted frame `j` with 1 ≤ j ≤ T, j < g, from a clean state `a`, the old field holds (now the definition `StopAt`):

```
0 < v(Q)  ∧  v(b) = 0  ∧  P(b) = P(Q)   →   P(Q) ≤ P(a) + 256
```

from the narrowed field `Moves.stop`:

```
0 < v(Q)  ∧  v(b) = 0  ∧  P(b) = P(Q)  ∧  (left(Q) < pix(Q)  ∨  pix(a) < left(a))   →   P(Q) ≤ P(a) + 256
```

**Proof.** If left(Q) < pix(Q) or pix(a) < left(a), this is the field. Otherwise pix(Q) ≤ left(Q) and left(a) ≤ pix(a). The frame keeps the edge's two bytes from its start to `Q` (`EdgeStep.keep_q`; `Q` is the only instruction at the scroll handler's call after the arrival, `GuardE.subs_onceE`), and the frames not counted between `a` and the frame's start keep them too (`OnFrames.edgeLag`). So left(Q) = left(a), and `stop_of_edge` gives P(Q) ≤ P(a) + 255. In `stop_of_edge` the pixel at `Q` is at most that of `a`, and the fraction is below 256.

The theorems are `StopEdge.stop_of_edge` (axioms `propext`, `Quot.sound`), `SurfaceFrames.OnFrames.stopAt` and `StopAt.stopP` (the old `Moves.stopP`, now from `StopAt`; `stopAt` also `Classical.choice`). No check on the ROM is new.

**Measured.**

| check | what | result |
|---|---|---|
| `edge-real FM2 256` | the frames of `Moves.stop` (0 < v(Q), v(b) = 0, P(b) = P(Q)), and of them those that the narrowed field asks | 6 frames (3 in the runs of my own from the movie's frames 852 to 1091, 3 in the runs from 992 to 1011 that mostly hold Left), each with one clamp and no push; P(Q) − P(a) at most 32; the narrowed field asks 0 of them. Of the 137,955 frames at the routine of the offscreen bits (5 sets), the clamp at the left edge was chosen 48,290 times, the clamp at the right edge never. `movesScan` fails only on the old stored speed and `after` on frames that do not start clean, with the counts of rounds 30 and 31 |
| `surface-frames-check FM2 200` | `stop` (the narrowed field) and `stopAt (a theorem)` (the old field), with the other conditions of `movesScan` | 0 failures: 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included |
| `route-check FM2` (and with `1089 02808080`, and with 996 and the round 23 jumprun) | the whole route | touch 1092, level change 1748 (1093 and 1748; 1396 and 2063) |
| `pos-keep-real FM2 64`, `collide-real FM2 200`, `pos-after-real FM2 200`, `keep-frames-check FM2 100`, `up-clean-u FM2` | `posW`, `clampR`, `collide`, `keep.cleanE`, `chg.upCleanU` | 0 failures |

The clamp's choice at the routine of the offscreen bits, measured on the ROM for every value of d = (right edge − pix) mod 2¹⁶ with the right edge 255 px right of the left edge (a scratch evaluation, not a part of the proof): the clamp at the left edge is chosen exactly when he is at the left edge or not within the 255 px right of it; the clamp at the right edge when he is within the last 16 px of the screen; no clamp otherwise.

**On the route.** The field `Moves.stop` is narrowed. Before (round 28):

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) → P(Q) ≤ P(a) + 256          (Q = trace k)
```

Now:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         (left16(Q) < pixel16(Q) ∨ pixel16(a) < left16(a)) → P(Q) ≤ P(a) + 256
```

No new field. `Moves.toAt` takes `StopAt` in place of `Moves`, and `OnFrames.movesAt` gives it by `OnFrames.stopAt`. The program checks the narrowed field (`stopB`, "stop") and the old one as a theorem (`stopAtB`, "stopAt (a theorem)").

**What is not proved here.** `Moves.stop` on the frames where he is right of the screen's left edge at the scroll handler: there, while he is within the 255 px right of the edge, the clamp at the left edge does not come, so the speed would have to become 0 by the clamp at the right edge or by a push. To prove it: follow the speed from the scroll handler's return to the frame's end (the walk of `PushTimer` with one more byte), and his pixel there (`PushTimer.pix_end`, which needs `sideW` on that frame; `sideW` is asked only when the place byte is at least the scroll's threshold). The frames that start left of the edge (pixel(a) < left(a)) are only measured not to be clean (round 23, [The screen's left edge at the frame's start](e-2-10-3-10-ScreenEdge.md)). `collide`, `posW`, `clampR`, `sideW`, the place-byte part of `endKeep`.

**File:** `Theorems/StopEdge.lean`. `Theorems/SurfaceFrames.lean` uses it (`Moves.stop`, `StopAt`, `StopAt.stopP`, `Moves.toAt`, `OnFrames.stopAt`, `OnFrames.movesAt`, `stopB`, `stopAtB`, `movesScan`). `Main.lean`: one count in `edge-real` (the frames of `Moves.stop` that the narrowed field asks).
