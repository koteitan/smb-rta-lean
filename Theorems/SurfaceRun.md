[← Back](../README.md) | [English](SurfaceRun.md) | [Japanese](SurfaceRun-ja.md)

# Above ground: not at the pole by frame 1085

**Statement.** At control above ground Mario is stopped, in the same horizontal state as at the start of 1-1. In a model where every frame is
freely on the ground or in the air, he moves at most 464/256 px further than the TAS in the first 40 frames, and at most 2.5 px per frame after
that. So at frame 1085 (233 frames after control at 852) he is at most 480/256 px ahead of the TAS. The left end of the pole's range is 528/256 px ahead of
the TAS at that frame. So he has not reached it, and there is room for the 32/256 px that [Grabbing the pole from below](PoleGrab.md) needs, with 16/256 px to spare.

In 1/256 px. `A` is the machine at control above ground on a real run. `s₀` is the horizontal state of the 1-1 start. `I` is the input set of
[Reach](Reach.md): on each frame ground, jump start or air, every set of Right, Left, Down, Up, B, the timer zero or not. `d(w)` is the sum of `16·v'` over the frames of
`w`, by `hstep` from `s₀`. `P(A)` is the position in `A`. `P₀` is the left end of the pole's range, `256·(256·page + column's x − 10)`, with the page from the level data.

```
start   :  control(A)  ∧  horizontal state(A) = s₀
within  :  ∀ w ∈ I*,  |w| ≤ 31      →  d(w) ≤ 9424
after   :  ∀ w ∈ I*,  |w| = 31 + k  →  d(w) ≤ 9424 + 16·v_top·k
reached :  ∃ w ∈ I⁴⁰,  d(w) = 9424 + 16·v_top·9 = 15184
gap     :  P(A) + 9424 + 16·v_top·(233 − 31) + 32  <  P₀
short   :  ∀ w ∈ I*,  |w| ≤ 233  →  P(A) + d(w) + 32 < P₀
```

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

**The start.** The machine comes from a real run: the first frames of the route of [From touching the pole to the castle](CastleWalk.md), with its own inputs, up to control above ground. The check reads its horizontal state and position there. The state equals the 1-1 start's.

**The model.** `hstep` is the horizontal part of a frame. The model chooses ground, jump start or air freely on each frame, so walking off the pipe, walking off a ledge and landing at any height are all covered. Nothing about the map is used. So it does not need the measured jump lengths of [The opening](Opening.md).

**The search.** `hstep` does not read the position. So `maxCheck` keeps one number for each horizontal state, the largest distance of the runs that reach it (`Cov`, as in [A fast takeoff](FastTakeoff.md)). A state is dropped once its distance plus `dbound` of the frames left is at most the bound (`dist_le`). `maxCheck_spec` proves this covers every input. No state is left after frame 30. The bound is exact in the model: `reached` gives inputs, and one less fails (`runCheck` is false). From frame 31 on every frame of the best run is at top speed.

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
* The frames after a hit are `TopSpeed.Frame`s: the assumptions of [Top speed bound](TopSpeed.md) and [Reach](Reach.md). Enemies are as on that page: a contact writes none of these bytes, except a death.
* On frames 1 to 8 Mario stays in the box of `noHit`. `dbound` gives less than 4 px either way, and a jump rises at most 5 px per frame. This is not joined to the check in Lean. `noHit` tries the speeds 0, ±1/16 and ±1/2 px per frame, because the routine reads a speed only by its sign.
* `mask` in Lean runs the fractions 0, 128 and 255. As a program over every fraction: same frame 2,288,640 times, stopped 46,080 times, anything else 0 times.
* The left screen edge is not in `Frame`. It stops him and leaves `P` at most where it was, so it counts as a first hit of the second kind, but that is not in Lean.
* The start is one real run. Other runs are not covered by a theorem. On the emulator: the TAS at 852 has the same horizontal state, position and height as `A` (17 RAM bytes differ, all timers and random numbers), and changing the fraction, speed or facing at the side pipe's entry gives the same state after the same 282 frames. If control comes later than 852 and the state is the same, `short` still applies, because it holds for every `|w| ≤ 233`.
* No Start or Select.

**Files.** `Theorems/SurfaceRun.lean`, private `Proof/SurfaceRun.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta surface-check             # the checks and the search with hits, as a program (about 3 s and 5 s)
.lake/build/bin/smbrta tas-seg FM2 852 1085      # the TAS's distances
```
