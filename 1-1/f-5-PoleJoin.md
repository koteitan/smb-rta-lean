[← Back](README.md) | [English](f-5-PoleJoin.md) | [Japanese](f-5-PoleJoin-ja.md)

# Above ground: the castle is not before 366 frames after control

**Statement.** Count frames from control above ground `C`: `fr j` is the frame `C + j`. From what a real run gives (`Run`, every field a hypothesis, listed below), the castle entry comes at `C + 366` or later. The TAS has control at 852, the touch at `C + 240` (1092) and the castle at `C + 366` (1218), so the bound is exact.

In 1/256 px. `g` is the frame of the touch, `c` the frame of the castle entry. `P₂` is the position after the movement, before the collision. `P_s`, `P_f` and `P₀` are where his right side reaches the block's side, where his feet get over the block, and the left end of the pole's range. `T = 233`, `N = 126`.

```
castle_ge     :  Run  →  T + 7 + N ≤ c      (366 ≤ c)
touch_castle  :  Run  →  (T + 1 ≤ g ∧ g + N + 6 ≤ c) ∨ (T + 7 ≤ g ≤ T + 8 ∧ g + N ≤ c) ∨ (T + 9 ≤ g ∧ g + N − 1 ≤ c)
touch_ge   :  Run  →  T + 1 ≤ g             (no touch before C + 234)
```

The case split, exhaustive in Lean (`direct_castle`, `castle_ge`). `T'` is the takeoff frame of the jump, `L` the landing before it.

| the touch | what the proof gives | castle |
|---|---|---|
| not a direct grab | `g ≥ T + 1` (`touch_ge`) | `c ≥ g + N + 6` (`castle_of_other`) |
| direct, fast jump, `T' = L + 1` | `P₂(g) < P₀` at any frame (`fast_near`), so no such grab | |
| direct, fast jump, `T' > L + 1` | `P₂(g) < P₀` at any frame (`fast_late`), so no such grab | |
| direct, slow jump, `g ≤ T + 6` | `P₂(g) < P₀` (`slow_short`), so no such grab | |
| direct, slow jump, `g = T + 7`, `T + 8` | `v₂(g − 1) < 0` and `P₂(g) < P₀ + F` (`slow_tight`) | `c ≥ g + N` |
| direct, slow jump, `g ≥ T + 9` | | `c ≥ g + N − 1` |

Before the landing, every `k`. `e` is the last frame he moves over the block and his feet stay inside until `L`, and `k = L − e` (`crossed`, `landing_cases`):

| | bound on the landing's position |
|---|---|
| no such `e`, or `k ≤ 1` | `P'(L) < P_f + 16·v_top − 256` |
| `k = 2` | `P'(L) ≤ P₂(e) − 224`, and `P₂(e) < P_f + 16·v_top` |
| `k ≥ 3` | `P'(L) ≤ P₂(e) + 256·(k − 2) − 224`, and `P₂(e) + 16·v_top·(T − e) ≤ B` |
| a fast jump on the frame after `L`, `k ≥ 2` | a frame that writes the stored speed would leave it below the air threshold. So no frame writes it, and every frame pushes him back: `P(L) ≤ P₂(e) − 256` (`fast_pushes`) |

After the landing (`hop_short`), with `m = g − L − 1`: if `P'(L) − 16·m + 32 < P₀`, then `P₂(g) < P₀`. A frame may be at the side of the block or left of it.

How the parameters of [Grabbing the pole from below](f-1-PoleGrab.md) come from [Above ground](e-1-SurfaceRun.md):

```
t = T,   B = P_A + X + 16·v_top·(T − N),   P₀ = poleP
B + 32 < P₀                                   Statement.gap
P_f ≤ P₂(e),  e + d = T   →   P₂(e) + 16·v_top·d ≤ B      hB_of_line, from Statement.after and hit_bound, with hits
```

Lean: `Theorems/PoleJoin.lean`, private `pole_join_numbers`, `pole_keep`, `pole_falls`, `pole_join`, `pole_touch`. `pole_join` applies the private `surface_run`, `castle_walk`, `jump_grab`, `pole_rules`, `top_frictionCheck`, `pole_keep` and `pole_falls`, so these do not appear in its hypotheses.

## What the join changes on the route page

* **A grab by a fast jump is a different event.** On its frame 1 a fast jump is 2 px lower than a slow jump on its frame 2. On the next frame his feet are inside the block and the block stops his Right, and the end routine enters the castle at once. With the position overwritten on real frames, the castle comes at the touch + 1 or + 2. [From touching the pole to the castle](f-4-CastleWalk.md) ran only slow jumps. So the bound needs that no fast grab happens at any frame, not only before 1092. `fast_short` proves this, with no time in it. The real fast hop from the TAS at 1085 ends 912/256 px short of `P₀`.
* **The touch + 126 is not a lower bound.** A slow grab not moving left, with a fraction of 176/256 px or more, gives the touch + 125 on real frames, position overwritten. On `g = T + 7` and `T + 8` this cannot happen: `slow_tight` gives a move to the left on the frame before and a fraction below `F = 176/256` px, with a fall of at most three frames in the block's rows. `g = T + 8` is needed for the timer: the touch + 125 there would keep `E` at 1218 with one more tick, so the sum would be 1 smaller and 1-2 would start at 1727. On later grabs the touch + 125 does not lower the sum. From the TAS's state at 1085 with the position moved by 16/256 to 160/256 px, over every input of A, B, Left and Right, no touch on 1092 or 1093 gave + 125 (`touch-search-at`).
* **Another touch can take less than 160 frames.** A real run (the TAS with A held longer on the last jump) touches at 1086 near the top of the pole and enters the castle at 1239, the touch + 153. The route page's 1246 is wrong. `castle_ge` needs only `N + 6 = 132`.
* **A fast jump need not start on the frame after the landing.** Running on the ground into the block's side leaves the stored speed high, as a hit does not clear it. A jump on the next frame is fast. `fast_late` covers this.
* **Real hops leave the block's side.** `PoleGrab.no_grab_far`, `no_grab_near` and `FastHop.fast_hop_short` take every hop frame at the side of the block, and every frame from `e` to `L` with the feet inside. A real run breaks both, for example the fast hop above is 144/256 px left of the side when it takes off. `hop_short` and `crossed` have neither hypothesis.

## How

`hop_short` follows a state on each frame after the landing: pushed back from the landing's position, left of `P_s`, or pushed back from there. `crossed` follows frames from one left of `P_f`: he is left of it, or he moved over it on `e` and has been inside since.

`fast_pushes` goes back from the landing. After `e` every frame starts stopped, so `−12 ≤ v₂ ≤ 2`. A frame that writes the stored speed writes `|v₂|`, which is below the air threshold `A`. The takeoff reads at least `A`. So each frame kept the stored speed and the moving direction, which stays right.

`line` is the position bound on a real run. Before the first hit `h` it is `Statement.after`. On frame `h` it is the hit's two kinds. After it, `hit_bound` with the frames as a `Chain`. The first `N + E` frames use only `16·v_top` per frame, far short of `P_f`.

`side_of_rule`, `inBlock_of_rule`, `md_of_right` and `push_of_rule` read `Side`, `InBlock`, the moving direction and the push from `PoleGrab.ruleOk` on a case, so `poleCheck` gives them from `Collides`. `maskL_of_step` does the same with `maskCheck`. `grab_frame` reads `g = T' + 1` or `T' + 2` from `Jump.arc_spec` on the jump's path.

Four facts were hypotheses and are now theorems:

```
J ≤ h                       first_of_surface    box, off, SurfaceRun.noHitCheck
FastLink (T' = L + 1)       fastLink_of_cases   reads, stopped, air, TopSpeed.frictionCheck, keepCheck, poleCheck
A ≤ |v₂(T' − 1)|  (T' > L + 1)  approach_of_cases  reads, onGround, TopSpeed.frictionCheck
L ≤ e + 3                   rows_of_cases       fall, air, fallCheck, base_late
```

`fallCheck` is a search of every fall: every jump from the ground and from 1 to `rows` rows up, and every step off a block from 2 to `rows` rows up, for each fall force and each carried fraction. It counts the frames in a row with the feet inside the base's rows, and finds at most 3. After 120 frames every fall is over, so the search has no length hypothesis. Stepping off a block 1 row up gives 4 frames, so it is not in the search. `base_late` excludes it: with his feet over the base on frame `w − 1`, the position bound gives `w ≥ T + 1`, so he falls past frame `T + 1`.

## Assumptions (not proved in Lean)

The hypotheses are the fields of `Run` and the structures in it. `pole_join` assumes all of these.

| hypothesis | says | evidence |
|---|---|---|
| `fr`, `seq`, `frames.reads` | frames are read from the machines; on `g`, only the fields up to `P₂` are real (the touch moves him); `next` is a theorem | [Above ground: the frames from control, one by one](e-2-SurfaceFrames.md) |
| `frames.step` | one frame from a clean state is a `OneFrame`; `model`, `hit`, `stop`, `off` are theorems | real runs on that page |
| `frames.vert`, `frames.box` | frames before `J` follow `vstep`, and the collision routine does what it does on the machine at control; `box` is a theorem | real runs on that page |
| `fm`, `inp`, `touches`, `pass`, `pos` | frame `g` is a touch on real machines; the write ends one pass of the side check; `P₂(g)` is the position when the page is read; `P₀ ≤ P₂(g)` is the theorem `Run.inRange` from these | [Touching the pole on real frames](f-6-1-PoleEntryRule.md) |
| `atCastle`, `afterTouch` | the flag is set on `c`, after the touch | the code |
| `other` | not a direct grab: for 131 frames the flag is that of a checked touch at another height | measured: at least the touch + 153 |
| `path`, `atY`, `atRising` | the jump's frames are a path of `Jump.arcSucc` from the ground | `Jump.md`; the jump starts from the ground: no enemy to bounce off near the pole |
| `order`, `left`, `air` | he comes from the left, and from frame `q` he falls below the block's top. A fall cannot skip the landing window. On a frame with the feet over the block, the case has the frame's moving direction, height and fall speed | code; going over the pole and back is not covered |
| `Collides`, `lowCase`, `inBlockCase` | a frame at the block runs `PlayerBGCollision` as `PoleGrab.collide` on a case of `cases` | routine checked alone; small Mario |
| `mask` | after a push to the right, the next frame's speed is `hstep` with Left blocked. One frame's link; `maskCheck` is proved | real runs below |
| `reads` | a fast jump: the stored speed before the takeoff is at least the air threshold | the code; `Jump.vstep` reads it |
| `onGround` | a fast jump later than `L + 1`: frame `T' − 1` runs `ImposeFriction` on a state of `frictionCheck` (`Imposes`) | real runs below |
| `stopped` | a fast jump on `L + 1`: a frame from speed 0 runs `ImposeFriction`, or the movement routine on a case of `keepCases` | real runs below |
| `fall` | a slow jump: the fall began on `w ≤ q` by a start of `fallStarts`, or by stepping off the base; the frames follow `fallNext` | map facts below |
| `flagAny`, `flagTight` | slow grab: for 124 frames the flag is that of a checked direct grab; for 125 frames if the frame before moved left and the fraction is below `F` | measured below |

The state at control, `Start`, is an argument of the theorems. `Route.Run.start` gives it from the change's last row.

The map facts in `fall`, with `rows = 8` in the private proof:

* Near the pole he stands only on the ground or on a block up to 8 rows up.
* No block above him changes the fall: a bump is not a step of `fallNext`.
* The only block 1 row up that he can step off near the pole is the base. So `fall` says that his feet were over it on the frame before.
* The fall force at a step is one of `Jump.forces`: a force left by a jump.

Measured, not in Lean:

* The delay after a slow grab, on the TAS's state at the frame before, overwritten: 2592 cases with a high fraction, of speed, moving direction, stored speed, running speed and running timer, give 125 at least. 1728 cases moving left before the touch: 126 or more for a fraction below 176/256 px.
* Other touches: the touch height changed over all 161 heights on the TAS's state: 153 to 164.

`Run` holds on real runs, checked as a program (`pole-join-check`): the TAS with `h = 234`, `q = 233`, `L = 237`, `T' = 238`, `g = 240`, `c = 366`; the TAS with Left, A, A, A after 1089, with `g = 241`, `c = 367`; and the TAS with A held longer, an other touch with `g = 234`, `c = 387`. In a scratch file, `Approach` with the TAS's numbers was a Lean term, and `slow_tight` gave its conclusion on it; that was before these fields changed.

The new fields on other runs, by a scratch program. 500 runs of random inputs from control have `box` on frames 1 to 8. 1500 runs of random inputs from frames 1002 to 1089 have `off` on all, and 3384 landings, 3074 after a jump and 310 after a step. `fall` holds on all of them. `stopped` and `onGround` hold on the 1392 near the block, 14 of them before a fast jump. With the position overwritten onto the base and Left held, he steps off with 4 frames in the rows, and the step-off clause of `fall` holds.

`hstep` sets the stored speed to `|v|`, and `X_Physics` reads it. After a hit the stored speed is not `|v|`. In those random runs `hstep` gives another `v₂` than the real frame on 59 of 126510 frames. For example the TAS up to 1066, then `0082828282c102c1c1...`: on frame 1088, `v = 0` with a stored speed of 35, Left gives `v₂ = −1`, and `hstep` gives 0. `Surface.model` is only about frames before the first hit. `mask` held on all these runs. `pole-join-check` now reads `v₂` with the real stored speed.

Not proved: that every run satisfies `Run`. The bound `B` of the position is in a model with no map, so `fall` is needed: without it, `k = 4` is not excluded with `e = T` on `g = T + 7` and with `e = T + 1` on `g = T + 8`. The emulator search of [the route page](../docs/route-1-1.md) gives a smaller real bound, which would exclude it. The structures `box`, `stopped`, `onGround` and `fall` say what frames do. Nothing proves that every frame of a real run does this.

**Files.** `Theorems/PoleJoin.lean`, private `Proof/PoleJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pole-join-check FM2                  # every field of Run on the movie's frames (2 s)
.lake/build/bin/smbrta pole-join-check FM2 1036 HEX         # the same with the inputs from frame 1036 replaced
```
