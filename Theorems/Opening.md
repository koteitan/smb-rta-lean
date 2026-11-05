[← Back](../README.md) | [English](Opening.md) | [Japanese](Opening-ja.md)

# The opening

**Statement.** From the start of 1-1 (standing still), on open flat ground, Mario cannot move
right by more than `2.5·n − 41.94` px in `n ≥ 32` frames (and not more than 38.06 px in 32 or fewer
frames). The TAS fast accel (32 frames, then Right+B) moves him exactly that far: no input
gets further than the TAS opening.

In 1/256 px, with `v_top` the running top speed:

```
state    = (horizontal state, air frames left, distance)
step     : on the ground every input (a jump start included), in the air no jump start;
           the horizontal state by hstep, the distance by 16·v'
jump     : from the start to the landing frame, a length in [L_tap(|v|), L_hold(|v|)]
           (|v| at the takeoff; measured on the emulator: a one-frame A press, A held)

opening  :  ∀ k ≤ 32,  Reach(start, k, u)  →  dist(u) ≤ 9744
            ∀ k,       Reach(start, 32 + k, u)  →  dist(u) ≤ 9744 + 16·v_top·k
            the TAS fast accel on the emulator:  P(32) − P(0) = 9744
```

`9744 + 16·v_top·k = 16·v_top·(32 + k) − 10736`, and the TAS opening followed by Right+B
moves `P` by this much (32 frames: `opening`; 52 frames: [Reach](Reach.md)).

Lean: `Theorems/Opening.lean` (`optCheck`, `opt_of_check`, `opt_after`, `reach_le`; proved
without computation), `Smbrta/Cert.lean` (`Reach`, `checkPrunedS`, `prunedS_spec`), private
`opening` (the search by `native_decide`, about 4 s).

## How

A search from the 1-1 start over the states above, frame by frame. A state is dropped when the
potential bound of [Reach](Reach.md) says that it cannot get past 9744 any more: its distance
plus `dbound(Φ, frames left)` is at most 9744 (`reach_le`, from `dist_le`). The bound is close
enough that the search ends in about 1.4 s as a program. Every kept state is checked to be at
most 9744.

What makes 9744 the limit (seen in the search and in the TAS):

* `X_Physics` allows the running top speed only on the ground with Right+B (or the running
  timer), or in the air from 1.5625 px/frame; otherwise the speed stops at the walking top speed.
* On the ground below 0.6875 px/frame, pressing against the moving direction stops a skid (speed 0),
  so the doubled adder (facing ≠ moving) is kept only in the air at low speed.
* A jump lasts at least 21 frames. Starting it at frame 2 (after one Left+Right frame), Mario
  lands at the end of frame 22; Right+B at frame 23 passes the walking top speed, Left at
  frame 24 sets the facing again, and a jump at frame 25 gives the doubled running adder up to
  the top speed at frame 32.

## Assumptions (not proved in Lean)

* Those of the open-area bound of [Reach](Reach.md): `hstep` is the horizontal part of a frame.
* Flat open ground: no blocks, holes or walls, so Mario is in the air only during a jump.
* The length of a jump depends only on `|v|` at the takeoff and lies between the lengths of a
  one-frame press and of a held A (checked for every hold length 1..60 at every speed:
  `smbrta jump-check`; pressing A again after a release does not raise the jump force again).
* A jump needs A newly pressed; the model allows it without (more inputs, so the bound still
  holds). No Start/Select.

**Files.** `Theorems/Opening.lean`, private `Proof/Opening.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-check 32 9744    # the search, as a program (true)
.lake/build/bin/smbrta open-check 32 9743    # one less is reached (false)
.lake/build/bin/smbrta jump-check            # the jump-length assumption
```
