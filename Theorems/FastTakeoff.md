[← Back](../README.md) | [English](FastTakeoff.md) | [Japanese](FastTakeoff-ja.md)

# A fast takeoff in the bonus room

**Statement.** In the bonus room Mario falls to the floor, runs, and jumps onto the brick block. Over all inputs, a jump
from the floor at 1.5625 px/frame or more cannot clear the corner of the block in time: at frame 557 he is short of the
block's right end. Moving right, a jump by frame 500 does not stay left of the corner while his feet are low. Moving
left, jumps by frame 500 exist in the model, but he is so far back that he is short whatever he does next. A jump after
frame 500 is short by the top speed alone.

In 1/256 px. A run is: `A` air frames of the fall, `g` ground frames, the jump frame `T`, `L` air frames, then any
frames up to the goal frame `n`. `v` is the speed on frame `T − 1`, `v_A` the air threshold, `c_P` the corner, `G_P`
the goal, `G` the most ground frames searched. "Low" means `P < c_P` on every frame after the fall through `T + L`.

```
no_right_takeoff   :  g ≤ G,  v ≥ v_A,  low  →  impossible
left_short         :  g ≤ G,  v ≤ −v_A,  P < c_P on the g ground frames  →  P(n) < G_P
late_short         :  g > G,  low  →  P(n) ≤ c_P − 1 + 16·v_top·(n − T − L) < G_P
fast_takeoff_short :  |v| ≥ v_A,  low  →  P(n) < G_P
```

For the room: `A = 34` (frames 460..493), `G = 6` (takeoffs 494..500), `L = 8`, `n = 557`. `P` starts at the room's start
position with any fraction of a pixel, on page 0. `c_P` is computed from the block's level object and the side
adder, `G_P` from its right end and the feet adder. `G_P` is the position that entering the side pipe at 569 needs at
557 ([The 1-1 route](../docs/route-1-1.md)).

Lean: `Theorems/FastTakeoff.lean`, private `fast_takeoff_right`, `fast_takeoff_goal` (by `native_decide`).

## How

`hstep` does not read `P`. So for each horizontal state `roomCheck` keeps the least and the greatest `P` of the runs
that reach it, and `Cov` says that these bound `P` of every run through that state. This is the merge that keeps the search
small: at most 1229 states per frame, about 122,000 frames of `hstep`.

A state is dropped when `|v|` cannot reach the threshold by the last takeoff. `Φ ≥ |V|`, and on frame `T − 1`, `|v| ≥ v_A`
gives `Φ ≥ θ = 256·v_A − 255`. `Φ` grows by at most `g_fast` per frame, and while its bound is below `θ` by at most
`g_slow` (`keep_of_run`). These come from `Facts` of [Reach](Reach.md).

On each frame `T − 1` the check does two things:

* `rightOk`: from the states moving right at the threshold or more, it runs the jump frame and `L` air frames, keeping
  what stays left of the corner. Nothing remains. In fact nothing remains after one air frame.
* `leftOk`: for the states moving left at the threshold or more, `H` is their greatest `P` and `Q` their greatest bound
  on `Φ`. It checks `H + dbound(Q, n − T + 1) < G_P`. The bound `dbound` treats `|V|` as if he were moving right, so it does
  not use the frames he needs to turn around. The margin is still more than 9 px.

## Assumptions (not proved in Lean)

* The theorems are about runs of `hstep` in the open area: `P` moves by `16·v` per frame. That real frames follow them is an
  emulator check (`hstep` agrees with the TAS on every frame from 460 to 557), not a theorem.
* The start state (stopped, facing right, moving direction 0, running speed 0) is read from the TAS at frame 459. That
  no earlier input changes it is the check of the fixed lengths in the route, not a theorem.
* `A = 34` and the floor at frame 494 come from the fall, which does not depend on the input. This is an emulator check.
* `L = 8` comes from `jump_block3` of [The height of a jump](Jump.md). It is not joined to `hstep` in Lean. Here it is only
  used in `late_short`: moving right, one air frame is already enough.
* A jump counts as fast by the speed on the frame before it. A jump just after a hit reads a stored absolute speed
  that is not the speed. That case is outside this theorem (step 5 of the route).
* A hit at the corner is outside this theorem: "low" assumes there is none. Step 5 of the route treats it.
* The left wall of the room is not in the model, so a run that touches it is not a run of this theorem. All the takeoffs moving
  left in the search have him further left than the wall let him go on the emulator (a few runs, not a proof). So these
  takeoffs probably do not occur in the game, and a run stopped by the wall is not covered. `left_short` does not need the wall.

**Files.** `Theorems/FastTakeoff.lean`, private `Proof/FastTakeoff.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta takeoff-check     # the search and the late bound, as a program
```
