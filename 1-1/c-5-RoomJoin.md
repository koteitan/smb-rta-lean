[← Back](README.md) | [English](c-5-RoomJoin.md) | [Japanese](c-5-RoomJoin-ja.md)

# Joining the bonus room

**Statement.** Let `C` be the frame of first control in the bonus room and `E` the frame Mario enters the side pipe. In every run that has the frames of the structure `RoomRun`:

```
E ≥ C + 111
```

The TAS has `C` = 459 and `E` = 570. The structure is what a real run gives: frames, positions, heights, the stored speed, the takeoff, the landing, how he leaves the block, the entry frame. Its fields are hypotheses. That real frames have them is not proved in Lean. The fields are about one frame where that could be done.

A run that lands on the left wall, jumps, and never touches the floor is covered too. On real frames it had `E` = `C` + 134 (see "Runs that stand on the left wall" below).

`P(n)` is the position at the end of frame `n`, in 1/256 px. `c_P` is the block's corner, `G_P` the position past its right end, `M_P` the left end of the pipe's mouth. `t₀` is the first frame with `P ≥ G_P`. `T` is the last takeoff from the floor before `t₀`, `s` the last low frame of that jump, `L` its landing on the block, `F` the frame the jump off the block reaches the floor. `stop(n)` means that he is slow and not far past the corner at the end of frame `n`: `Φ(n) ≤ Φ_s`, `P(n) ≤ c_P + S`.

```
no_landing   :  a jump from the floor or from the block's side still running at t₀  →  impossible
stop_short   :  stop(h),  C + 37 ≤ h ≤ t₀ ≤ C + 98  →  P(t₀) < G_P
wall_short   :  the left wall touched before C + 37,  no stop from C + 37 to t₀,  t₀ ≤ C + 98  →  P(t₀) < G_P
landed_short :  no wall touched,  no stop from C + 37 to t₀,  he landed on the block,  t₀ ≤ C + 98  →  impossible
past_late    :  t₀ > C + 98
entry_ge     :  E ≥ C + 98 + 13        (with the numbers as parameters: C + goalF + aboveF)
room_join    :  r : RoomRun  →  r.C + 111 ≤ r.E        (private, the numbers by native_decide)
```

These lemmas come from the fields about one frame. The proofs are in "What follows from the frames".

```
corner_late  :  C ≤ n < C + 37,  n ≤ t₀  →  P(n) < c_P
low_by       :  C ≤ n ≤ C + 43,  n ≤ t₀  →  P(n) ≤ c_P + S_low
floor_low    :  no wall touched,  T ≤ C + 40,  C + 37 ≤ n ≤ T  →  LowAt(n)
early_of     :  no wall touched,  T ≤ C + 40  →  the frames up to T are those of FastTakeoff
stand_gap    :  C ≤ i < j < C + 34,  standing at i and at j  →  i + 8 ≤ j
run_short    :  stop(h),  C + 37 ≤ h ≤ C + 40,  RunningSpeed(h) ≠ 0,  t₀ ≤ C + 98  →  P(t₀) < G_P
mouth_at     :  P(E) ≥ M_P
```

Lean: `Theorems/RoomJoin.lean`, private `room_nums`, `room_checks`, `room_join`, `room_floor_arcs`. `#print axioms room_join` shows no `sorryAx`; it has the `native_decide` axioms.

## How

The case split is made with `cases` and `by_cases`, so it is exhaustive in Lean. Margins are how far he is short, measured by `room-join-check`.

| case | why it is short | margin (1/256 px) |
|---|---|---|
| over the block in one jump, no landing | below the threshold at most 1.5 px per frame; at the threshold or more the top speed after the 8 low frames; the longest jump comes from `arcCheck` | 1792; 97 |
| a stop from `C + 37` on | the speed is near 0, then the potential of [Reach](../0-0/0-2-Reach.md) | 225 at frame 37; 241 at frame 41 |
| no stop, the wall touched before `C + 37` | no jump is looked at: the potential from the wall frame (`wall_short` below) | 48; 96; 128; 512 |
| no stop, a takeoff after `C + 41` | at `T + 8` he is at the corner at most, then the top speed | 97 |
| no stop, no wall touched, a slow takeoff by `C + 41` | `P(s) < c_P`, then [The air speed cap](c-1-AirCap.md) with the pairs of [The height of a jump](c-2-Jump.md): `landing_bound`, `landing_later` | 65; 193 |
| no stop, no wall touched, a fast takeoff by `C + 41` | [A fast takeoff](c-3-FastTakeoff.md): moving right impossible, moving left short | |

Then, with `t₀ > C + 98`, off the block:

| he leaves by | why |
|---|---|
| a fast jump | `t₀ − 1 + 13 ≤ F ≤ E` from `dropOk`: `E ≥ C + 111` |
| a slow jump | `t₀ − 1 + 12 ≤ F`, so `E` < `C + 111` needs `E = F = C + 110`. All frames from `C + 98` to `E` are in the air below the threshold, so `P(E) < G_P + 12·1.5 px`, 1024/256 px short of the mouth |
| stepping off | `t₀ + 16 ≤ F ≤ E` from `walkOk` |

A hit on the floor with a stale stored speed has no separate case. It is a stop, and `stop_short` does not look at the jump that follows. The same theorem covers a jump from the side of the block, which the jump tables do not describe.

Three things about the corner that the collision routine does and the route page did not say:

* **Moving left is not stopped.** At a low frame past the corner, with `v < 0`, the routine stops nothing. So `LowAt` has three cases: stopped, left of the corner, moving left. Going back frame by frame, a frame moving left past the corner comes after a stop, so with no stop `P < c_P` on every low frame (`left_of_corner`).
* **The feet stop him too.** A jump that peaks just below the block's top (feet inside the block by 5 px or more, not rising) is stopped by the foot check, 1 px back per frame, past the corner height. On the emulator he was stopped at 1136/256 px past the corner. So `S` is much larger than the slack of a low frame.
* **A jump can start from the block's side.** Falling with a foot over the block and the feet less than 5 px into a row of it, he lands on that row: state "ground", at a height inside the block. The side check stops him in the same frame, and on the next frame he can jump. So the last takeoff need not be from the floor. It always comes with a stop, so with a stop from `C + 37` on the theorem needs no takeoff at all; `Approach` is asked for only when there is no stop.

The frames after a hit do not all follow `hstep`: the blocked side is masked on the next frame, and the stored speed is stale until the next frame that updates it, which then uses a larger adder. `stop` allows for that: `Φ_s` is a fraction, one frame of the largest adder and the charge for the facing direction.

## What follows from the frames

**`corner_late`.** As long as he has touched nothing, the frames of the fall are air frames (`fall_air`): he stands only after a frame that is stopped (`stand_wall`), and he is not on the floor during the fall (`fall_long`). He keeps facing right. Define `Ψ` as follows, with `a₁` the second entry of the table of adders and `g_slow = 2·a₁`.

```
V ≥ 0                     :  Ψ = V + w
256 − g_slow ≤ V < 0      :  Ψ = V + a₁
−g_slow ≤ V < 256 − g_slow:  Ψ = V + g_slow
−g_slow − a₁ ≤ V < −g_slow:  Ψ = V + g_slow + a₁
any smaller V             :  Ψ = 0
```

Moving left the adder is doubled, so a state just below 0 gains more when it turns back. The last lines count that.

`airCheck` runs every state facing right with `|v| < v_A` and `RunningSpeed` 0 and the 4 air inputs (53248 calls of `hstep`).

```
the facing stays,   Ψ' ≤ Ψ + a₁,   V − V' ≤ g_slow
```

So `16·v ≤ 16·⌊Ψ/256⌋` and `Ψ(C + j) ≤ Φ₀ + a₁·j`. With `airDist(p, j) = Σ_{i=1..j} 16·⌊(p + a₁·i)/256⌋`, `P(C + 34) ≤ P(C) + airDist(Φ₀, 34)`. The next 2 frames are `capDist` of [The air speed cap](c-1-AirCap.md). Together he is 81/256 px left of the corner.

The wall is a field about one frame. A frame before `C + 37` that does not follow `hstep` is stopped by the left wall, with `P ≤ P_w` before and after it (`WallAt`). The wall is far from the start, so the state after the first wall frame is at `C + 15` or later (`leftDist`, the bound on moving left). After the wall, `P(n) ≤ P_w + dbound(Φ_s, n − C − 15)`. This does not reach the corner before `C + 37`: the margin is 3680/256 px.

**`low_by`.** With no wall hit he is on the floor at `C + 34` (`floor_at`). The frames after it are `VFrame`: on the floor he stays or takes off; in the air the frame is `vstep`, or he is falling. By `arcCheck` and `floorArcOk`, on the 8 frames after the takeoff frame of every jump from the floor his feet are low, he is rising and in the air state, so he does not land. So from `C + 37` to `C + 43` his feet are low, and `low_at` (the collision routine with the feet low) gives `P ≤ c_P + S_low`. With a wall hit, `P_w + dbound` and the top speed are enough up to `C + 43`: the margin is 31/256 px.

**`floor_low`.** With no wall hit and `T ≤ C + 40`, he is on the floor from `C + 34` to `T`. An earlier jump would still be in its low frames at `T`, not on the floor. Floor frames have low feet, so `low_at` applies.

**`early`.** With no wall hit, `early_of` builds the frames of `FastTakeoff`. The `hstep` frames are the absence of a wall hit. The frames of the fall come from `fall_air`, the ground frames from the floor of `floor_low`, the jump frame and the air frames from `VFrame`.

**`wall_short`.** With the wall touched before `C + 37` and no stop from `C + 37` to `t₀`, `P(t₀) < G_P` (for `t₀ ≤ C + 98`) with no look at any jump. So `Approach` is asked only of a run with no wall hit. Let `b` be the last wall frame. All frames after `b` follow `hstep`, and `P(b) ≤ P_w`, `Φ(b) ≤ Φ_s`, `b ≥ C + 15`.

```
b ≥ C + 22                   :  P(t₀) ≤ P_w + dbound(Φ_s, 76) < G_P        margin 128
b < C + 22,  facing right at b + 1 :  wall_right
b < C + 22,  another facing at b + 1 :  wall_turn
```

**`wall_right`.** Frame `b + 1` can be any frame (a jump, a ground frame, an air frame): `Φ(b + 1) ≤ Φ₁ = nxt(Φ_s)`. After it, the frames to `C + 34` are air frames: standing needs a frame that is stopped, and there is none after `b`. So `Ψ` grows by at most `a₁` per frame. Let `Q = Φ₁ + a₁·18`.

```
Φ(C + 34) ≤ Q  :  P(t₀) ≤ P_w + 16·⌊Φ₁/256⌋ + airDist(Φ₁, 18) + dbound(Q, 64) < G_P                                   margin 48
Φ(C + 34) > Q  :  V(C + 34) < 0,  −V ≥ u = Q + 1 − 2c
                  P(t₀) ≤ P_w + 16·⌊Φ₁/256⌋ + airDist(Φ₁, 9) − backD(u, 9) + capDist(64) < G_P                         margin 512
```

With `V ≥ 0`, `Φ = Ψ ≤ Q`, so on the second line he moves left. `V` falls by at most `g_slow` per frame, so on the 9 frames before he was moving left too, and he has gone back.

**`wall_turn`.** Air frames and jump frames keep the facing (`facing`). So to face anything but right he needs a ground frame with no jump by `b`. On the frame `i` before it he stands. `i` is his first stand: an earlier one gives `i ≥ C + 15 + 8` by `stand_gap`, against `i ≤ b < C + 22`. `stand_P` with `leftDist` gives `i ≥ C + 16`. Let `j = i − C`.

A stand is a frame that is stopped, so `Φ ≤ Φ_s`. To stand again he needs `−V ≥ 256·14` (`stand_fast`). Since `iterN(Φ_s, 6) < 256·14`, two stands are at least 8 frames apart. This is `stand_gap`.

There is no jump up to `b`, and after `b` he can stand only on the floor. So with no jump the height comes from `vfall`. Let `Y = 256·y + fraction`, `W = 256·vy + fraction`, and `f` the force of the fall.

```
Y(C + j) ≤ Y₀ + Σ_{l<j} (W₀ + f·l)
Y(i) ≤ that row + 255,   W(i) = 0        (stand_row)
Y(i + e) ≤ Y(i) + Σ_{l<e} f·l
```

The table `gaps` holds `(j, k)`: he does not reach the floor up to `i + k`.

```
(16, 32) (17, 32) (18, 28) (19, 28) (20, 28) (21, 25)
```

The frames up to `i + k` are air frames, so he stays below `v_A`. Let `capRamp(p, n)` be `dbound` with the speed held to `v_A − 1`.

```
P(t₀) ≤ P_w + capRamp(Φ_s, k + 1) + capDist(98 − (j + k + 1)) < G_P        margin 96 or more
```

**`run_zero`.** This field is gone. What is needed is `RunningSpeed` at a stop from `C + 37` to `C + 40`: the third condition of `J` uses it.

```
wall touched                     :  P(h) ≤ P_w + dbound: short for any RunningSpeed      margin 1280 or more
moving right at the end of the fall :  safeCheck: |v| stays below the running threshold to C + 39   RunningSpeed = 0
Φ(C + 34) at most the bound      :  the same
moving left fast at the end of the fall :  backD: P(C + 34) is small; P(h) ≤ backP, short with fastDist   margin 144
```

`safeFrom` is a small search: only the states not decided by the bound on `Φ` go on to the next inputs. A frame that does not follow `hstep` leaves `RunningSpeed` 0 (`stop_run`). A frame that follows `hstep` has `stepOk`.

**`slow_capped`, `stale`.** The takeoff reads the stored speed `ab` (`x_ab`), and `ab ≥ |v|` (`ab_ge`). A slow jump has `ab < v_A`, so `|v| < v_A`. For a fast jump with no wall hit and no stop: every frame follows `hstep` and has `ab = |v|` or changes neither (`ab_follow`), so `ab = |v|` or `ab < v_A` (`ab_or`). So `|v| ≥ v_A`.

**`mouth`.** From `entered` (the routine enters), `entry_mem` and `entry_P`, `mouth_of_enters` of [Entering the side pipe](c-4-SidePipe.md) gives `P(E) ≥ M_P`. `entry_ground` is `ground_of_enters`: the entry state is on the ground.

## Assumptions (not proved in Lean)

Each is a field of `RoomRun` or of a structure in it. "One frame" below marks a fact about a single frame.

* `fm`, `pad`, `arr`, `next`, `read_hs`, `read_P`, `read_in`, `clean` (one frame): the frames are a sequence of real machines, and the state, the position and the input are read from the machines. Every frame up to `t₀` is `FrameModel.Clean`, or it leaves him stopped (`Stop`) and is `FrameModel.ReadFrame`. That a `Clean` frame follows `hstep` (`Follow`) and that every frame moves at most the top speed (`move_top`) are proved from the theorems of [A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md). What `Clean` and `ReadFrame` assume is on that page.
* The state at first control (`start`, `startP0`, `startP1`, `v_start`, `ab_start`) is no longer assumed: he is stopped, facing right, moving direction 0, running speed 0, at the start position with any fraction, falling, at most 50 px from the top, at most 2.375 px per frame down, with the machine's first fall force and stored speed 0. `RoomRun.entry_ge` takes `StartAt(fm C)` as an argument, and [The state at the first control in the room](c-7-2-RoomStart.md) proves it from the rows of the change. What remains is that at `C` the vertical state and the stored speed are read from the machine (`vs_C`, `ab_C`).
* `wall` (one frame): a frame before `C + 37` that does not follow `hstep` is stopped by the left wall: `P ≤ P_w` before and after it, `RunningSpeed` 0. That this is the only case (he cannot reach the corner) is part of the assumption.
* `late` (one frame): a frame from `C + 37` to `C + 41` that does not follow `hstep` is at the left wall, or `P + 16·v_top ≥ c_P`.
* `stop_run` (one frame): a frame by `C + 40` that does not follow `hstep` leaves `RunningSpeed` 0.
* `air_in` (one frame): before `C + 51`, a frame that starts in an air state has an air input.
* `stand_wall` (one frame): before `C + 51`, he stands off the floor only at the end of a frame that does not follow `hstep`: the side check stops him. Standing on the top of the block comes later.
* `fall_long` (one frame): he is not on the floor before `C + 34`.
* `facing` (one frame): before `C + 34`, air frames and jump frames keep the facing.
* `stand_fast`, `stand_P` (one frame): for a stand before `C + 34`, on the frame before it `−V ≥ 256·14` and `P ≤ P_s`. `P_s` is where his foot enters the wall's column, plus one frame below the threshold. His foot enters that column only when he comes fast from outside.
* `stand_row` (one frame): from the air to standing, his height is a whole row and his downward speed is 0.
* `vfall` (one frame): before `C + 51`, a frame with no jump, not in a jump state, has `Y' ≤ Y + W` and `W' ≤ W + f`. `f` stays, and the next state is not a jump state.
* `floor_at`: with no wall hit, he is on the floor at `C + 34`.
* `vframes` (one frame): with no wall hit, the frames from `C + 34` to `C + 49` are `VFrame`.
* `low_at` (one frame): a frame from `C + 37` to `C + 43` with the feet low is `LowAt`. This is a fact of the collision routine; it is not derived from the routine.
* `ab_ge`, `ab_follow` (one frame): the stored speed is at least `|v|`. A frame that follows `hstep` stores `|v|`, or changes neither.
* `entry`, `entry_mem`, `entered`, `entry_P` (one frame): at `E` the routine enters, on a state in the domain of `sideCheck`, with the frame's `x`. The speed is replaced by one of the 4 speeds of the domain: this path of the routine does not read the speed, which is not checked in Lean. That the machine `withPipe` has the same pipe column as the real machine is also assumed.
* `Approach`: asked only with no wall hit and no stop. The takeoff is from the floor (`T1_floor`), the jump and the landing are `vstep` frames (`Cert.Reach`, `x_vs`), the air frames are air, `low` is the collision routine on the low frames, `x_ab` (one frame) is that the takeoff reads the stored speed.
* `Off`: the jump off the block is `vstep` frames up to `F`, the frame it would reach the floor if nothing stopped it. `F ≤ E` assumes that being stopped or landing on the way only delays the floor. A landing on the pipe's top really happens.
  * `slowJ`: if `F = E`, the frames of a slow jump are air frames of `hstep`, or move at most the air speed.
* `Over`: for a jump over the whole block, the same as `Approach`. Not seen in a real run. `no_landing` proves it impossible under this field.
* `way`: he passes over from the floor or the block's side (`Over`), or he lands on the block and leaves it (`Off`). A run that stands on the left wall, jumps, and passes over the block with no landing is not in `Way`. At the air speed that takes 105 frames or more, and the longest jump from up to 5 rows above the floor is 76 frames, so it should not be a real run. This is not proved in Lean.
* He does not hit his head. Jumps rise at most 45, and at the heights and columns tried the emulator shows no hit. The air frames of `VFrame` include this assumption.

These fields were compared with real frames by a program that is not in this repository. On the TAS all hold, with `E` = `C` + 111. So the fields are not contradictory. With random inputs from first control, 2800 runs (4 kinds of input, 700 each, including small changes of the TAS input) had no field failing. Of these, 740 passed the block's end and 510 touched the left wall. The earliest `E` was `C` + 111, from a small change of the TAS input; none was earlier.

Random inputs rarely stand during the fall. So 1701 runs were made from 27 inputs that reach a stand, with 7 inputs after the stand and 9 lengths of A. No field failed. In 434 of them he passed the block's end with no floor at all. With a stand on the wall the earliest `t₀` was `C` + 115, and the earliest `E` of those that touched the floor was `C` + 154. A run with no floor enters at `E` = `C` + 134 when it slows down on the block. In 1152 runs that stand, jump and try to stand again, no field failed either.

The "over the block" case has no real run, so its fields are untested. Big Mario is not included.

## Runs that stand on the left wall

The fall reaches the floor in 34 frames. A wall touch with no landing does not change that. Running left, he can land on a ledge of the left wall during the fall, when his foot enters the wall's column and is less than 5 px deep in a row. His state is ground, and the side check stops him on the same frame (`wall` before `C + 37`). On the next frame he jumps or falls.

Seen on real frames:

* In 20000 random runs, the first stand was at `C + 18`, `C + 19` (4 rows above the floor), `C + 22` (3 rows), `C + 26` (2 rows) or `C + 30` (1 row). All the others reach the floor at `C + 34`. The earliest wall frame was `C + 16`.
* Left on the frame after a stand makes a wall frame: he faces left, is pushed back 1 px and falls. Facing left, Right in the air has the doubled adder. This is the case of `wall_turn`. Left and Right together also change the facing.
* Falling from a stand, the floor comes later: from `C + 46` to `C + 50` in the 5 runs tried.
* He can stand, jump and stand again. One run stood at `C + 18`, jumped, and stood again at `C + 73` and `C + 122`. In what was tried, two stands were at least 41 frames apart.
* He can enter with no floor at all. One run stood at `C + 18`, jumped at `C + 19`, landed on the block, with `t₀` = `C` + 116 and `E` = `C` + 134.

A run that does not touch the floor must stand in the fall. With no stand he reaches the floor at `C + 34`.

**Files.** `Theorems/RoomJoin.lean`, private `Proof/RoomJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-join-check     # the longest jumps, the floor check, and the margins (1 s)
```
