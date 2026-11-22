[← Back](README.md) | [English](e-2-10-3-23-StopClamp.md) | [Japanese](e-2-10-3-23-StopClamp-ja.md)

# A frame that the clamp stops ends at the screen's left edge

The field `Moves.stop` speaks of a frame that moves right at the scroll handler, ends with the speed 0 and ends at the position it had at the scroll handler. Round 32 asked it only where at the scroll handler he is right of the screen's left edge, or the frame starts left of it ([A frame that stops him at the screen's left edge](e-2-10-3-21-StopEdge.md)). Here a frame with no push after the scroll handler is proved to end at the left edge, and then not to be right of the edge at the scroll handler; and a counted frame with no push is proved to end at or right of the edge. So the field is asked only on a frame with a push: right of the edge at the scroll handler with a push on this frame, or starting left of the edge with a push on the frame before.

The reason in the game's code: after the scroll handler's call only three things set his speed to 0 on a frame in control: the clamp at the screen's edge (inside the scroll handler), the push (which first sets the side timer to 16), and the death (which then stores the game engine's routine, which no frame before the touch does). The side timer falls only at a frame's start, so a frame that ends with the timer not at 16 had no push after the scroll handler. On such a frame the clamp set the speed to 0. The clamp at the right edge puts him 16 px left of the right edge, and there the clamp at the right edge is not chosen; but his pixel at the end is the one where the clamp was chosen. So it was the clamp at the left edge, which puts him at the left edge.

**Claim (round 33).** Write

```
a, b    = the end of the counted frame before (seq (j − 1)), the frame's end (seq j)
Q       = the scroll handler's call after the arrival at the player's routine
C       = the start of the routine of the offscreen bits (ChkPOffscr),  R = the scroll handler's return instruction
pix(m)  = his pixel with its page,  left(m), right(m) = the screen's edges with their pages (two bytes each)
P(m)    = 256·pix(m) + f(m);  v(m) = his speed;  side(m) = the side collision's timer
t₁₆     = PushTimer.pushT, the value the push stores to the timer, read from the push's code (16)
sel(C)  = the clamp's choice at C: none, the left edge (0) or the right edge (1);  amt(t) = the clamp's amount for t
after(t, C) = pix(C) if nothing is chosen, else (edge t at C − amt(t)) mod 2¹⁶
```

`StopClamp.stop_clamp`: with right(C) ≡ left(C) + 255 (mod 2¹⁶),

```
pix(R) = after(sel(C), C)  ∧  (sel(C) = none → v(R) = v(C))
∧  pix(b) = pix(R)  ∧  v(b) = v(R)  ∧  pix(C) = pix(b)  ∧  left(b) = left(C)  ∧  v(b) ≠ v(C)     →     pix(b) = left(b)
```

On each counted frame `j` with 1 ≤ j < g:

```
SurfaceFrames.OnFrames.stopRight   : 0 < v(Q) ∧ v(b) = 0 ∧ P(b) = P(Q) ∧ side(b) ≠ t₁₆                       →  pix(b) = left(b)
SurfaceFrames.OnFrames.noStopRight : 0 < v(Q) ∧ v(b) = 0 ∧ P(b) = P(Q) ∧ side(b) ≠ t₁₆ ∧ left(Q) < pix(Q)    →  False
SurfaceFrames.OnFrames.leftEnd     : side(b) ≠ t₁₆                                                           →  left(b) ≤ pix(b)
```

`noStopRight` also needs the speed of `a` at most the top, `a` away from both ends of the position's range, and the left edge's page not 255 at the ends of the frames before; `leftEnd` needs the left edge's page not 255 at `b`. `SurfaceFrames.OnFrames.stopAt` (the old field `StopAt`, round 32) comes from these and the narrowed field.

`PushTimer.pix_end` now says: if the frame does not end with the timer at t₁₆, then his pixel, his page and his speed at the frame's end are those of the instruction after the scroll handler's call (round 32: if it ends with the timer at most 1, the pixel and the page).

The theorems are `StopClamp.stop_clamp`, `ClampSide.amt_facts` (axioms `propext`, `Quot.sound`), `PushTimer.pushT_ne`, `SurfaceFrames.OnFrames.stopRight`, `OnFrames.noStopRight`, `OnFrames.leftEnd` (also `Classical.choice`). `ClampSide.clamp_end` says more: when nothing is chosen the speed is kept. New checks on the ROM: `ClampSide.rightAmt`, the choice at the difference amt(1) is not the right edge (a part of `ClampSide.checkAll`); in `PushTimer.sCheck` a third walk, for his speed, and 2 ≤ t₁₆.

**Proof.** `stop_clamp`, by the choice at C:

* Nothing chosen: v(b) = v(R) = v(C), against v(b) ≠ v(C).
* The right edge: pix(C) = pix(b) = pix(R) = (right(C) − amt(1)) mod 2¹⁶, so the difference (right(C) − pix(C)) mod 2¹⁶ that the choice reads (`ClampSide.selM_rel`) is amt(1), and there the choice is not the right edge (`rightAmt`).
* The left edge: amt(0) = 0 (`relCheck`), so pix(b) = pix(R) = left(C) = left(b).

`stopRight`, as `OnFrames.nearStepAt`:

* Q is the frame's only scroll handler after the arrival (`GuardE.subs_onceE`), the first one (`EdgeStep.keep_r`).
* The scroll's part keeps his position and his speed up to C and gives the right edge's relation there (`RightEdge.scroll_rel`, with `OnFrames.relAll` at the frame before and `OnFrames.edgeLag`); so pix(C) = pix(Q) = pix(b), the last by P(b) = P(Q), and v(C) = v(Q) > 0 = v(b).
* The routine and the clamp give pix(R) = after(sel(C), C), the edges kept, and the speed kept when nothing is chosen (`ClampSide.clamp_end`); the return keeps the RAM (`ret_step`).
* From the instruction after the call to the frame's end his pixel, his page and his speed are kept when the frame does not end with the timer at t₁₆ (`PushTimer.pix_end`, fields `posW` and `sideW`), and the left edge is kept (`EdgeStep.keep_r`).

`noStopRight`: by `stopRight` pix(Q) = pix(b) = left(b). From `Q` to the instruction after the call the edge is kept, or the scroll is allowed and the edge moves by at most the scroll's amount, which is the byte the move stores, as the platforms' force is 0 at `Q` (`ScrollRule.scroll_edge`, `OnFrames.platQ`); from there to the frame's end it is kept (`EdgeStep.keep_r`). Without a scroll left(b) = left(Q) < pix(Q). With a scroll `EdgeStep.NearX` at `Q` (`OnFrames.nearAt`) gives left(Q) + xs(Q) + 2 ≤ pix(Q), so left(b) ≤ pix(Q) − 2. Both contradict pix(Q) = left(b).

`leftEnd`: as `OnFrames.nearStepAt`, the clamp leaves him at the left edge or at most 255 px right of it (`ClampSide.left_of`), and his pixel and the edge are kept to the frame's end (`PushTimer.pix_end`, `EdgeStep.keep_r`); with the edge's page not 255 that is left(b) ≤ pix(b).

`stopAt`: if he is at or left of the left edge at Q and the frame starts at or right of it, round 32 (`StopEdge.stop_of_edge`). If he is right of the edge at Q and the frame does not end with the timer at t₁₆, `noStopRight`. If the frame starts left of the edge and the frame before did not end with the timer at t₁₆, `leftEnd` for the frame before, or at control `AreaRun.edge₀`, says that it does not. The rest is the field. `stopAt` now takes the speed and the position of `a` (from the clean state and `far`) and the left edge's page on the frames before; `movesAt`, `one_of_frames`, `vert_of` and `quiet_upto` pass the page on, and `surface_of_frames` gives it by `OnFrames.pageAll`.

The speed's walk follows the speed byte from the instruction after the scroll handler's call to the frame's end, as the walks of the pixel and the page: it stops following it at a store by its address, and asks at the end that it is still followed or the timer is known to be t₁₆. The push stores t₁₆ to the timer before it stores 0 to the speed; the death stores the routine (a path that ends: `K.noStore`). The walks' guard protects the speed and the player's state too (`PushTimer.guardS`; `FrameKeep.guardE` protects them, so `cleanS_of` still holds).

**Measured.**

| check | what | result |
|---|---|---|
| native test (a scratch search) | the three walks of `sCheck` from the instruction after the scroll handler's call, with the end "followed, or the timer known to be t₁₆" | 0 failures for each; `sCheck` true, about 5 s natively with the evaluation of the failures; t₁₆ = 16. With the speed and the state not protected, the speed's walk failed twice |
| the ROM (round 32's scratch evaluation of the choice) | the choice for each difference d = (right − pix) mod 2¹⁶ | the right edge exactly for d from 0 to 15; nothing for d from 16 to 254; the left edge else. The clamp at the right edge puts him 16 px left of the right edge, where nothing is chosen, so `rightAmt` holds |
| `edge-real FM2 256`, `surface-frames-check FM2 200` | `stop` (the narrowed field), `stopAt (a theorem)`, `stopRight (a theorem)`, `noStopRight (a theorem)`, `leftEnd (a theorem)` | 0 failures. `edge-real`: 6 frames of `Moves.stop` (0 < v(Q), v(b) = 0, P(b) = P(Q)), each with one clamp and no push, P(Q) − P(a) at most 32; round 32's field asked 0 of them, the new field 0. Of the 137,955 frames at the routine of the offscreen bits the clamp at the left edge was chosen 48,290 times, the clamp at the right edge never. `surface-frames-check`: 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included |

**On the route.** The field `Moves.stop` is narrowed. Before (round 32):

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         (left16(Q) < pixel16(Q) ∨ pixel16(a) < left16(a)) → P(Q) ≤ P(a) + 256                       (Q = trace k)
```

Now:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         ((left16(Q) < pixel16(Q) ∧ side(b) = t₁₆) ∨ (pixel16(a) < left16(a) ∧ side(a) = t₁₆)) → P(Q) ≤ P(a) + 256
```

No new field. `stopRight` and `leftEnd` use the field `sideW` on the frames that do not end with the timer at t₁₆, whatever the lock and the place byte, and on the last counted frame before the touch: the field `sideW` is asked there now ([A store that may reach the side timer](e-2-10-3-22-SideNear.md)).

**What is not proved here.** `Moves.stop` on a frame with a push: right of the left edge at the scroll handler with a push after the scroll handler on this frame, or starting left of the edge after a frame with a push. There the pushes move him by 1 px each, and two pushes that cancel, or a push and the clamp, are not followed. To prove it: follow the pushes after the scroll handler (their number and their directions).

**File:** `Theorems/StopClamp.lean`. `Theorems/ClampSide.lean` (`rightAmt`, `checkAll`, `clamp_end`, `amt_facts`, `left_of`), `Theorems/PushTimer.lean` (`pvI`, `pushT`, `eqAt`, `finS`, `guardS`, `cleanS_of`, `sCheck`, `pushT_ne`, `pix_end`), `Theorems/SurfaceFrames.lean` (`Moves.stop`, `OnFrames.stopRight`, `OnFrames.noStopRight`, `OnFrames.leftEnd`, `OnFrames.stopAt`, `OnFrames.movesAt`, `one_of_frames`, `vert_of`, `quiet_upto`, `surface_of_frames`; `OnFrames.relStep` and `OnFrames.relAll` moved before `stopRight`, and `stopAt` to `vert_of` after `OnFrames.nearAt`; `stopB`, `stopRightB`, `noStopRightB`, `leftEndB`, `movesScan`). `Main.lean`: `edge-real` counts the frames of `Moves.stop` that the field asks now (`stopAsk33`), and its two filters know the three new names.
