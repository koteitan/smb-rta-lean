[← Back](README.md) | [English](e-2-10-3-6-PositionDispatch.md) | [Japanese](e-2-10-3-6-PositionDispatch-ja.md)

# Constructing position cuts

`PositionDispatch` advances along the actual instruction trace. At an `ImpedePlayerMove` entry it takes the complete checked call to its original return. At a decoded screen-clamp entry it does the same. Elsewhere it takes one instruction whose stores avoid the three position bytes. The calls take priority over the ordinary case. Instructions inside them are skipped.

`Ready` states the local entry conditions. An ordinary instruction must avoid the position bytes. A push needs `Good` and margins against position wrap. A clamp needs `Good`, a selector of either side and a target inside the position range. The existing ROM checks and frame-time condition remain explicit.

`next_piece` constructs a strictly later cut. A summarized call returns before the frame ends; it cannot be cut in the middle. `partition` constructs the whole chain from local `Ready` at reached dispatch states. It does not ask for `Ready` at instructions inside summarized calls. `Chain.cuts` produces the numeric cuts for `PositionPieces.trace_sum`. `Chain.sum` proves their exact total effect.

Coverage is still an obligation. It is not a new `Run` field. Rechecking the existing facing/subspeed search with `guardE` on the surface gave 20,541 states, 141,003 steps and no failed abstract transition. It retained a direct player-page store in the horizontal-platform positioning routine, outside the push and clamp routines. The current walk therefore does not establish that O/I/C covers every relevant frame. This is an abstract path, not a counterexample from a real run.

The live-edge bound also has an exact arithmetic form. Let d be the live edge's whole-pixel coordinate minus the frame-start player's whole-pixel coordinate and the ROM clamp amount. The target minus the frame-start position is 256*d plus the difference of their position fractions. Thus target ≤ P(M)+256 holds exactly when d ≤ 0, or d=1 and the clamp-entry fraction is no greater than the frame-start fraction. This relation compares two states and covers either selector algebraically. Its screen-coordinate premises still need to follow from the real frame.

The TAS, 32 new random runs and 12 edge patterns supplied 8,832 Q-frames. There were 28,963,908 ordinary dispatch steps, 69 pushes and 2,096 clamps. Ordinary-store, call-entry, return-effect and exact-sum failures were all zero. Every clamp used the left selector, and its pixel gap d was between −2 and 0; the target-bound failures were zero. This supplies no right-selector reachability proof. `CollideS.P` and `AfterP` remain. No field is added, removed or widened. Excluding other position writers, deriving the live-edge relation and relating call-entry speed to Q are still required.
