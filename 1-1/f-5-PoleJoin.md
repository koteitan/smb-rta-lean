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

Lean: `Theorems/PoleJoin.lean`, private `pole_join_numbers`, `pole_keep`, `pole_falls`, `pole_frac`, `pole_join`, `pole_touch`. `pole_join` applies the private `surface_run`, `castle_walk`, `jump_grab`, `pole_rules`, `top_frictionCheck`, `pole_keep`, `pole_falls`, `pole_frame_check`, `pole_frac` and `keep_check`, so these do not appear in its hypotheses.

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

## The fraction and the castle flag

`seq j` is the machine at the end of the counted frame `j`: the frame `a + ix(j)` of the run, where `ix(j)` is the `j`-th frame from control that ends not paused. It is a definition (`Run.seq`), on every frame, before the touch and after it. `castle(m)` says that `StarFlagTaskControl` is not 0. `frac(P) = P mod 256` is the byte that `CastleWalk.atPole` writes, and `fracs` are the 16 multiples of 16 and 255.

```
keep            :  FrameKeep.Keep: the frames up to the touch on the real machine   (field)
seq j           =  S.seq(a + ix(j))                                           (definition: Run.seq)
fracCheck       :  posP(B.m) mod 16 = 0                                       (pole_frac, native_decide)
keepCheck       :  the walk of one whole frame in control                     (keep_check, native_decide)
AtCtl(seq 0)    :  seq 0 is the start of a frame in control, with the castle flag down   (an argument; Route.Run.atCtl₀)
Run.fracP       :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run  →  ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac        :  the same  →  P₂(g) mod 16 = 0
Run.frac_mem    :  the same  →  frac(P₂(g)) ∈ fracs
toCastle        :  c ≤ upTo(top)   (c frames end not paused by the end of frame top)   (field)
atCastle        :  castle(seq c) = true                                       (field)
Run.noCastle_of :  the same  →  ∀ j ≤ g,  castle(seq j) = false
Run.afterTouch  :  the same  →  g < c
```

`Run.fracP` reads `P(j) = posP(seq(j − 1))` from the machines. At control the castle flag is down (`AtCtl(seq 0)`) and `posP(seq 0) = posP(B.m)` is a multiple of 16 (`Start.P`, `fracCheck`). `AtCtl(seq 0)` comes from the rows of the change out of the side pipe ([The machine at control above ground](f-6-2-ControlStart.md)). Each frame up to the touch keeps both: the walk of one whole frame in control on the frames of `keep` ([One whole frame in control keeps the castle flag and the fraction's low bits](f-6-19-FrameKeep.md)). `Run.frac` adds `P₂ = P + 16·v₂`. So the fraction that `CastleWalk.Statement.anyFraction` checks is now the fraction of the run: `flagAny` and `flagTight` name the checked touch with `frac(P₂(g))`, and `castle_of_direct` takes `frac(P₂(g)) ∈ fracs` from `Run.frac_mem`. The flag of `flagAny`, `flagTight`, `other` is `castle(seq ·)`, not a function of its own.

The fraction of the position is the byte `SprObject_X_MoveForce` of the player. `MoveObjectHorizontally` adds the speed's low 4 bits times 16 to it. That a whole frame keeps its low 4 bits is now proved by the walk, under a condition on each instruction (`FrameKeep.CleanK`). It was the field `fracStep`, read from the code.

No castle flag up to the touch. `StarFlagTaskControl` leaves 0 only in `PlayerEndLevel`, the end of the level. The star flag's object does nothing while it is 0. The same walk proves that a whole frame in control keeps the flag down, so with `keep` and the check only the machine at control is needed (`Run.noCastle_of`). It was the field `noCastle`. `Route` no longer uses `Run.afterTouch`: `level_ge_of_parts` reads `g < c` from the bound of the join (`touch_castle`), and `Run.segsOk`, `Run.hT`, `Run.hc` take it as an argument.

The fields changed:

* Removed: `flag` (a function of its own), `afterTouch` (now the theorem `Run.afterTouch`).
* Added: `fracStep`, `noCastle`. `atCastle` now reads the machine: `castle(seq c) = true`. `flagAny`, `flagTight` take the fraction of `P₂(g)`.
* New arguments of `direct_castle`, `castle_ge`, `touch_castle`: `(hfq : fracCheck sy (above m0 n) = true)`, after `hc`.
* Then removed: `fracStep`. Added: `keep : FrameKeep.Frames sy m0 g seq`. New argument of `direct_castle`, `castle_ge`, `touch_castle`: `(hkc : FrameKeep.keepCheckOf sy m0 = true)`, after `hfq`. `Run.fracP`, `Run.frac`, `Run.frac_mem` take `(hk : FrameKeep.keepCheckOf sy m0 = true)` after `hq`.
* Then removed: `noCastle`, and in `keep` the field `start`. Added in `keep`: `ctl`, `lagStart`. New argument of `direct_castle`, `castle_ge`, `touch_castle`: `(hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))`, after `A`. `Run.fracP`, `Run.frac`, `Run.frac_mem`, `Run.noCastle_of` take `(hc0 : FrameKeep.AtCtl sy m0 (R.seq 0))` after `hk`. `Run.afterTouch` takes `st`, `hq`, `hk`, `hc0`.
* Then removed in `keep`: `fm`, `pad` (now `Frames.fm`, `Frames.pad`, read from `all` and `ix`), `ends` (now the theorem `Frames.ends`), `lag`, `lagStart` (now the theorem `Frames.all_start`). Added in `keep`: `all`, `inp`, `next`, `ix`, `ix0`, `order`, `at_ix`. `ctl` and `clean` now speak of every frame up to the touch, counted or not. No signature of `PoleJoin` changed.
* Then removed: `fm`, `inp`, `pass`, `pos`. `touches` is on frame `g` of `keep` (`Touches(keep.fm g, keep.pad g)`). Added: `tiles`, `edge`, `moved` ([The touch of the pole: one whole frame](f-6-16-PoleFrame.md)). In `keep`, `ctl` now asks two bytes, the routine and the task; that the mode is the game's is the theorem `Frames.ctlAll`. The argument `hc` of `touch_ge`, `direct_castle`, `castle_ge`, `touch_castle` is now `(hc : PoleFrame.poleFrameCheck sy m0 = true)` (it was `PoleEntryRule.ruleCheck`). `Run.inRange` takes `hc`, then `R`, `st`, `hq`, `hk`, `hc0`.
* Then (item 1-1-0-4): `Run` takes the real frames of the whole run and the frame of control, `Run sy m0 b vs B T J Nc F S a` with `S : FrameKeep.RealRun`, `a : Nat`; so does `keep : FrameKeep.Frames sy m0 S a g seq`. Removed in `keep`: `all`, `inp`, `next` (now `all n = S.seq (a + n)`, a definition, and the theorem `Frames.next`). New theorem `Run.seq0 : seq 0 = S.seq a`: the old link `Route.Run.atCtl` is now the theorem of that name. The private `pole_join`, `pole_touch`, `pole_touch_castle` take `S`, `a` as implicit arguments.
* Then removed in `keep`: `ctl` (now the theorem `Frames.ctlAll`, from the second walk of `keepCheckOf`). Added in `keep`: `noStore` (no instruction of a frame before the touch's frame writes the routine, the mode or the task by its address). `edge` changed: it no longer forbids the edge store and the head's collision routine; right after either of them, up to the write, he is left of the pole's range (`PoleFrame.again`). No signature changed.
* Then removed in `keep`: `ix`, `ix0`, `order` (the counted frames are now the frames that end not paused, a definition: `Frames.ix`, and the theorems `Frames.ix0`, `Frames.order`, `Frames.up`, `Frames.down`), `at_ix` (now the field `seqAt`), `clean` (now the field `cleanF`, `CleanK` of `FrameKeep.guardF`, and the theorem `Frames.clean`). Added in `keep`: `top`, `many` (`g` frames end not paused by the end of frame `top`). In `frames`, the fields `unpaused`, `lagPaused`, `spare` are gone ([the frames above ground](e-2-SurfaceFrames.md)). No signature changed.
* Then removed: `seq` (now the definition `Run.seq = keep.seq`: `seq j = S.seq(a + ix(j))` on every frame, so the frames after the touch are real frames of the run too), and in `keep` the field `seqAt` (`keep` is now `FrameKeep.Keep sy m0 S a g`, which has no `seq`; `keep.toFrames` is the old `FrameKeep.Frames`, with `seqAt` true by the definition). Added: `toCastle : c ≤ upTo(upAt, keep.top)`: the castle entry is the end of a counted frame of the run. `flagAny`, `flagTight` and `other` now ask the flag only on the frames up to `c` (`FollowsTouch sy flag g c E n` asks `g + k ≤ c`): weaker. `DirectFlag`, `OtherFlag`, `FollowsTouch` and `DirectWay` take `c` after `g`. `frames` is `SurfaceFrames.OnFrames sy m0 B T J g keep.seq fr keep.toFrames`. No signature of a theorem changed.

On real frames (`pole-frac-check`, after the last change, exit 0, bad 0):

| run | runs | frames | touches | frames with a push or a stop | of these at the left edge |
|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1 (fraction 80) | 5 | 0 |
| random inputs from control | 300 | 83,559 | 1 | 4,354 | 3,546 |
| random inputs from the movie's frames 1002 to 1091 | 1,200 | 137,055 | 675 | 6,896 | 732 |
| into the screen's left edge, then random | 720 | 181,894 | 0 | 15,006 | 12,940 |

* The fraction at control is 0, on the movie and on the machine of the proof.
* On every frame `P' − P` is a multiple of 16. The touches have all 16 fractions `0, 16, …, 240`, and all are in `fracs`.
* No machine has the castle flag up to the touch.
* `pole-join-check` reads the three fields on the TAS (`frac(P₂(g)) = 80`), on 1089 then `02808080` (64), and on the touch with A held (112). The flags agree with the checked touch with that fraction.

The counted frames from the touch to the castle, on real runs (`castle-count-check`, exit 0, bad 0). `g` and `c` are counted frames from control: a frame is counted when it ends not paused.

| run | runs | touches | castle entries | frames from the touch to the castle (ending paused) | `c − g` |
|---|---|---|---|---|---|
| the movie | 1 | 1 | 1 | 126 (0) | 126 |
| from 2 frames before the movie's touch, Start on frame `k` (`k` = 0 to 140) and again 45 frames later | 141 | 141 | 141 | 23,436 (5,670) | 126 |
| random inputs, Start at random, from the movie's frames 1052 to 1091 | 200 | 158 | 140 | 41,863 (17,803) | 126, 159 to 166 |

* On every run the castle flag first goes up on a frame that ends not paused. So `c` is a counted frame, `seq c` has the flag, and `toCastle` holds with `top` that frame.
* After the touch, the castle flags of the counted frames up to `c` are those of the run from the touch's end with no input and no pause, and so is `c − g`. A pause after the touch changes nothing that `FollowsTouch` reads.
* From the touch to the castle, a frame is counted exactly when the phase of the clock moves (`CastleToLevel.kindOf`): 0 frames disagree. Lean does not use this yet: `c` is not joined to the clock's castle entry `E` (part 0).

## Assumptions (not proved in Lean)

The hypotheses are the fields of `Run` and the structures in it. `pole_join` assumes all of these.

| hypothesis | says | evidence |
|---|---|---|
| `fr`, `frames.reads` | frames are read from the machines (`seq` is a definition); on `g`, only the fields up to `P₂` are real (the touch moves him); `next` is a theorem | [Above ground: the frames from control, one by one](e-2-SurfaceFrames.md) |
| `frames.step` | one frame from a clean state is a `OneFrame`; `model`, `hit`, `stop`, `off` are theorems | real runs on that page |
| `frames.vert`, `frames.box` | frames before `J` follow `vstep`, and the collision routine does what it does on the machine at control; `box` is a theorem | real runs on that page |
| `touches`, `tiles`, `edge`, `moved` | frame `g` of `keep` is a touch on real machines; up to the write, a side check that reads a pole tile reads the pole's column (`TileRead`); right after the edge store and after the head's collision routine he is left of the pole's range; `P₂(g)` is the position at the end of the move; `P₀ ≤ P₂(g)` is the theorem `Run.inRange` from these and `keep`, by the walk of the whole frame | [The touch of the pole: one whole frame](f-6-16-PoleFrame.md) |
| `keep` | the frames up to the touch on the real machine, counted or not, one after the other from control: frames of the run from frame `a` on (`all n = S.seq (a + n)`, a definition; `next` is a theorem); a frame is counted when it ends not paused, and the counted frame `j` ends at `seq j = S.seq(a + ix(j))`, a definition (`top`, `many`: `g` frames end not paused by the end of frame `top`); no instruction of a frame before the touch's frame writes the routine, the mode or the task by its address (`noStore`; that these frames end in control is the theorem `Frames.ctlAll`); each instruction meets `CleanK` of `guardF`, which also protects the pause byte, the area's type, the swimming flag and the change of size (`cleanF`). That each frame starts in control and that the `lag` frames keep the castle flag and the fraction's low 4 bits are the theorems `Frames.all_start`, `Frames.start`; `16 ∣ P₂(g)` is the theorem `Run.frac`, no castle flag up to the touch the theorem `Run.noCastle_of` | [One whole frame in control keeps the castle flag and the fraction's low bits](f-6-19-FrameKeep.md) |
| `toCastle`, `atCastle` | the castle entry `c` is a counted frame of the run (`c ≤ upTo(top)`), and the machine at its end has the castle flag; `g < c` is the theorem `Run.afterTouch`. The bound does not use `toCastle`: it makes `c` the number of frames up to a real frame, for the join with the clock | the code; `castle-count-check` below |
| `other` | not a direct grab: for 131 frames, up to `c`, the flag of the counted frames is that of a checked touch at another height | measured: at least the touch + 153 |
| `path`, `atY`, `atRising` | the jump's frames are a path of `Jump.arcSucc` from the ground | `Jump.md`; the jump starts from the ground: no enemy to bounce off near the pole |
| `order`, `left`, `air` | he comes from the left, and from frame `q` he falls below the block's top. A fall cannot skip the landing window. On a frame with the feet over the block, the case has the frame's moving direction, height and fall speed | code; going over the pole and back is not covered |
| `Collides`, `lowCase`, `inBlockCase` | a frame at the block runs `PlayerBGCollision` as `PoleGrab.collide` on a case of `cases` | routine checked alone; small Mario |
| `mask` | after a push to the right, the next frame's speed is `hstep` with Left blocked. One frame's link; `maskCheck` is proved | real runs below |
| `reads` | a fast jump: the stored speed before the takeoff is at least the air threshold | the code; `Jump.vstep` reads it |
| `onGround` | a fast jump later than `L + 1`: frame `T' − 1` runs `ImposeFriction` on a state of `frictionCheck` (`Imposes`) | real runs below |
| `stopped` | a fast jump on `L + 1`: a frame from speed 0 runs `ImposeFriction`, or the movement routine on a case of `keepCases` | real runs below |
| `fall` | a slow jump: the fall began on `w ≤ q` by a start of `fallStarts`, or by stepping off the base; the frames follow `fallNext` | map facts below |
| `flagAny`, `flagTight` | slow grab: for 124 frames, up to `c`, the flag of the counted frames is that of a checked direct grab with the fraction of `P₂(g)`; for 125 frames if the frame before moved left and the fraction is below `F` | measured below |

The state at control, `Start`, and the machine at control, `AtCtl`, are arguments of the theorems. `Route.Run.start` and `Route.Run.atCtl₀` give them from the change's last row.

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
.lake/build/bin/smbrta pole-frac-check FM2 300               # 16 ∣ P' − P, fracCheck, no castle flag on real runs (about 4 min)
.lake/build/bin/smbrta keep-frames-check FM2 100            # the conditions of keep on real runs
.lake/build/bin/smbrta castle-count-check FM2 200           # the counted frames from the touch to the castle, with pauses (about 1 min)
```
