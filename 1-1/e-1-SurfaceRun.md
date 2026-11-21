[← Back](README.md) | [English](e-1-SurfaceRun.md) | [Japanese](e-1-SurfaceRun-ja.md)

# Above ground: not at the pole by frame 1085

**Statement.** At control above ground Mario is stopped, in the same horizontal state as at the start of 1-1. In a model where every frame is
freely on the ground or in the air, he moves at most 464/256 px further than the TAS in the first 40 frames, and at most 2.5 px per frame after
that. So at frame 1085 (233 frames after control at 852) he is at most 480/256 px ahead of the TAS. The left end of the pole's range is 528/256 px ahead of
the TAS at that frame. So he has not reached it, and there is room for the 32/256 px that [Grabbing the pole from below](f-1-PoleGrab.md) needs, with 16/256 px to spare.

In 1/256 px. `A` is the machine at control above ground on a real run. `s₀` is the horizontal state of the 1-1 start. `I` is the input set of
[Reach](../0-0/0-2-Reach.md): on each frame ground, jump start or air, every set of Right, Left, Down, Up, B, the timer zero or not. `d(w)` is the sum of `16·v'` over the frames of
`w`, by `hstep` from `s₀`. `P(A)` is the position in `A`. `P₀` is the left end of the pole's range, `256·(256·page + column's x − 10)`, with the page from the level data.

```
start   :  control(A)  ∧  horizontal state(A) = s₀
within  :  ∀ w ∈ I*,  |w| ≤ 31      →  d(w) ≤ 9424
after   :  ∀ w ∈ I*,  |w| = 31 + k  →  d(w) ≤ 9424 + 16·v_top·k
reached :  ∃ w ∈ I⁴⁰,  d(w) = 9424 + 16·v_top·9 = 15184
gap     :  P(A) + 9424 + 16·v_top·(233 − 31) + 32  <  P₀
short   :  ∀ w ∈ I*,  |w| ≤ 233  →  P(A) + d(w) + 32 < P₀
far     :  2048 + 16·v_top·233 ≤ P(A)  ∧  P(A) + 16·v_top·233 + 2048 < 2²⁴
```

`far` says that 233 frames of at most `16·v_top` each, either way, keep the position away from both ends of its range. The private proof checks it on `A` (`surface_checks`). [The frames from control](e-2-SurfaceFrames.md) use it in place of the old assumption `Moves.far`.

Compared with the TAS, from its frame 852:

| frames after control | TAS frame | the TAS moves | the bound | ahead of the TAS |
|---|---|---|---|---|
| 40 | 892 | 14720 | 15184 | 464 |
| 233 | 1085 | 138224 | 138704 | 480 (the range needs 528) |

A hit is outside `hstep`. For a run whose first hit is on frame `j`:

```
hit_short :  9 ≤ j,  hit,  any frames of TopSpeed.Frame after it  →  P(233) + 32 < P₀
hit_last  :  j = 233,  hit  →  P(233) + 32 < P₀
          hit:  P(j) ≤ P(A) + d(pre ++ [i]) − 256   or   P(j) ≤ P(A) + d(pre) + 256
noHit     :  the collision routine on A, within 4 px of its x and up to 40 px above its y: no side hit
mask      :  moving right with a wall on the left: hstep with Left blocked = hstep, or a stop
```

Lean: `Theorems/SurfaceRun.lean` (`runCheck`, `maxCheck_spec`, `within_of_check`, `after_of_check`, `hit_bound`, `hit_short`, `hit_last`, `statement_of_check`), private `surface_checks`, `surface_run`, `surface_numbers`, `surface_hit` (by `native_decide`).

## How

**The start.** The machine comes from a real run: the first frames of the route of [From touching the pole to the castle](f-4-CastleWalk.md), with its own inputs, up to control above ground. The check reads its horizontal state and position there. The state equals the 1-1 start's.

**The model.** `hstep` is the horizontal part of a frame. The model chooses ground, jump start or air freely on each frame, so walking off the pipe, walking off a ledge and landing at any height are all covered. Nothing about the map is used. So it does not need the measured jump lengths of [The opening](a-3-Opening.md).

**The search.** `hstep` does not read the position. So `maxCheck` keeps one number for each horizontal state, the largest distance of the runs that reach it (`Cov`, as in [A fast takeoff](c-3-FastTakeoff.md)). A state is dropped once its distance plus `dbound` of the frames left is at most the bound (`dist_le`). `maxCheck_spec` proves this covers every input. No state is left after frame 30. The bound is exact in the model: `reached` gives inputs, and one less fails (`runCheck` is false). From frame 31 on every frame of the best run is at top speed.

The best run of the model is not a real run: it lands and takes off with no air time. The real limit is smaller. The emulator search of [the route page](../docs/route-1-1.md) gave 144/256 px at frame 892, and it was not run again for this page. The difference does not matter here, because 464/256 px is enough.

**A hit.** Four kinds of side contact exist (`TopSpeed.Frame.impedeP`, and the routine's code):

| speed on the frame | what the routine does | how it is covered |
|---|---|---|
| moving right or stopped, wall on the right | speed 0, 1 px back, Right blocked next frame | first hit: `P(j) ≤ P(A) + d(pre ++ [i]) − 256` |
| moving left or stopped, wall on the left | speed 0, 1 px forward, Left blocked next frame | first hit: `P(j) ≤ P(A) + d(pre) + 256` |
| moving left, wall on the right | nothing, Right blocked next frame | first hit, the same line |
| moving right, wall on the left | nothing, Left blocked next frame | `mask`: the next frame is the model's frame, or it stops him with `P` unmoved, and that stop is a first hit |

A stop could help, because it changes the facing and moving state. `hit_bound` covers this: up to the first hit `dbound` bounds the distance, and after it any `Frame`s, with more hits allowed, move him at most `reach(255, n)` by `TopSpeed.chain_reach`. The table `hitTable` checks this sum against the bound for every `j` from 9 to 31, and past 31 frames the search's bound is enough. For `j ≤ 8` the sum is too large. On those frames no hit happens, by `noHit`: Mario is on top of the pipe, and the collision routine on the real machine finds no side contact around him.

As a separate check (a program, not a theorem), the model with a hit of any kind allowed on every frame, including frames 1 to 8 and the blocked buttons, was searched for 40 frames. Dropping states by `TopSpeed.reach`, nothing gets past 15184. So a hit does not help in the model at all.

## Assumptions (not proved in Lean)

* Real frames follow `hstep` up to the first hit. On the TAS `hstep` agrees with the emulator on all 233 frames from 853 to 1085, which include walking off the pipe, the staircase and the ledges (program, no difference). The first difference is frame 1086, the hit at the base block.
* The frames after a hit are `TopSpeed.Frame`s: the assumptions of [Top speed bound](../0-0/0-1-TopSpeed.md) and [Reach](../0-0/0-2-Reach.md). Enemies are as on that page: a contact writes none of these bytes, except a death.
* On frames 1 to 8 Mario stays in the box of `noHit`. That he stays in the box is proved for `x` and the height (`SurfaceFrames.quiet_upto`).
* `mask` in Lean runs the fractions 0, 128 and 255. As a program over every fraction: same frame 2,288,640 times, stopped 46,080 times, anything else 0 times.
* The left screen edge is in `Frame` and `SurfaceFrames.Hit` ([Above ground: the frames from control, one by one](e-2-SurfaceFrames.md)). At the edge he can stop with `v₂ > 0` (largest measured 4), so `P` rises by 16·v₂. What holds is `v′ ≤ 0 ∧ P′ ≤ B + 256`, with the base B = max(P, edge) (round 24: `P′ ≤ P + 256` was false on a real frame that starts 1 px left of the edge, [1-1-e-2-10-3-10](e-2-10-3-10-ScreenEdge.md)).
* **Round 24: `hit_boundB`.** The frames above ground are `TopSpeed.Frame`s with `wide`. `hit_boundB` is `hit_bound` for them: the first hit ends at most 1 px past the model's position at some frame before it (`s ≤ |pre|`), and the base of the frame after it is its start or such a position. Along frames whose bases follow each other (`TopSpeed.ChainB`), max(P, B) moves by at most `reach(255, n)` (`chainB_reach`). The table and the numbers are the same; the prefixes need `dbound` to grow with the number of frames (`dbound_mono`). `hit_bound` and `hit_short` stay, for frames without `wide`.

```
hit_boundB :  9 ≤ j,  P(j) ≤ P(A) + d(pre ++ [i]) − 256  or  ∃ s ≤ |pre|, P(j) ≤ P(A) + d(pre.take s) + 256,
              B(f) ≤ P(j)  or  ∃ s ≤ |pre|, B(f) ≤ P(A) + d(pre.take s),   Chain(f :: fs) ∧ ChainB(f :: fs)
              →  P′(last) ≤ P(A) + X + 16·top·(E + k)          (the conclusion of hit_bound)
```
* The start is one real run. Other runs are not covered by a theorem. On the emulator: the TAS at 852 has the same horizontal state, position and height as `A` (17 RAM bytes differ, all timers and random numbers), and changing the fraction, speed or facing at the side pipe's entry gives the same state after the same 282 frames. If control comes later than 852 and the state is the same, `short` still applies, because it holds for every `|w| ≤ 233`.
* No Start or Select.

**Files.** `Theorems/SurfaceRun.lean`, private `Proof/SurfaceRun.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta surface-check             # the checks and the search with hits, as a program (about 3 s and 5 s)
.lake/build/bin/smbrta tas-seg FM2 852 1085      # the TAS's distances
```
