[← Back](README.md) | [English](f-6-9-2-StoredStep.md) | [Japanese](f-6-9-2-StoredStep-ja.md)

# The frames between the landing and a fast jump

**Claim.** A direct grab by a fast jump is excluded with one condition on the frames before the jump: the field `reads` (the stored speed at the end of frame `T' − 1` is at least the air threshold `A`). The field `ground` of `PoleJoin.ApproachCases` is gone, and no field replaces it. The frame before the takeoff need not start on the ground. The takeoff may come on any frame after the landing.

`L` is the landing's frame, `T'` the takeoff's frame, `g` the touch's frame, `q` a frame left of the base. `abs(j)` is the stored speed of `seq j`, the machine at the end of the counted frame `j`. `v₂(j)` is the speed at the end of the move of frame `j`. `P₂(g)` is the position at the end of the move of the touch's frame. `P₀` is the left end of the pole's range. `FastLink` is `A ≤ abs(L)`, with `stop_step` and the rules of the push on the frames `q < j ≤ L`.

```
stored_step        :  1 ≤ j < g   →   abs(j) = |v₂(j)|  ∨  abs(j) = abs(j − 1)
approach_of_cases  :  reads,  stored_step for L < j < T',  stop_step for q < j ≤ L   →
                        FastLink   ∨   ∃ j,  L < j < T'  ∧  13 ≤ |v₂(j)|
fast_near          :  FastLink,  L + 2 ≤ g,  the frames after L on the ground or rising   →   P₂(g) < P₀
fast_late          :  L < j < g,  13 ≤ |v₂(j)|,  the frames after L on the ground or rising   →   P₂(g) < P₀
fast_short         :  a fast jump,  g = T' + 1   →   P₂(g) < P₀
```

## How

`stored_step` is the two cases of `StopRead.stored_end`. On the ground, and in the air with Left or Right, the frame runs `ImposeFriction` and ends with the stored speed `|v₂|`. In the air with neither, it keeps the stored speed. Nothing is asked of the frame's speed, state or jump.

`approach_of_cases` goes back from the takeoff. `reads` gives `A ≤ abs(T' − 1)`. Take a frame `j` with `L < j < T'` and `A ≤ abs(j)`. If it wrote the stored speed, `|v₂(j)| = abs(j) ≥ A ≥ 13`. If it kept it, `A ≤ abs(j − 1)`, and the same question is asked one frame before. So some frame after the landing ends its move with a speed of 13 or more, or `A ≤ abs(L)`.

* `A ≤ abs(L)`: every frame after the landing kept the stored speed. This gives `FastLink`. It was used only for `T' = L + 1`. `fast_pushes` shows that every frame with the feet inside the base pushed him back, and `hop_short` bounds the touch. `fast_near` now takes any `g ≥ L + 2`: each frame after the landing moves the bound 16/256 px further back.
* `13 ≤ |v₂(j)|` on a frame `j` after the landing. At the base's side, a frame that starts pushed back has `v₂` between −12 and 2. So frame `j` starts left of the base's side, and frame `j + 1` starts left of it or pushed back from there. `hopState_iter` carries this to `g`. `fast_late` was this for `j = T' − 1` and `g = T' + 1` only.

Before, the second case took `j = T' − 1` from the field `ground`: the frame before the takeoff starts on the ground and reads no jump, so it writes `|v₂|`. Now the induction finds the frame that wrote the stored speed, wherever it is.

## Why the jump of `T'` does not give `ground`

The plan was: frame `T'` of the model is a takeoff, so the machine reads A newly pressed while he stands, so A was not pressed on frame `T' − 1`, and he stood when frame `T' − 1` began. Step by step:

1. The takeoff of the model is not tied to the machines. `direct` gives `q`, `L`, `T'`, the arc `a` and the vertical state `u` as data. The touch's height and direction (`touchY`, `touchRising`) are fields with no link to the machines. So "frame `T'` reads a jump" would be a new field.
2. With that field, "frame `T' − 1` reads no jump" is within reach of the walk of `PrevKeep`: at the frame's end, bit 7 of A of the frame before is bit 7 of the pad's bits at the player's routine. This is not written in Lean, as it is not needed.
3. "He stood when frame `T' − 1` began" does not follow. The jump of `T'` gives the state 0 at the end of frame `T' − 1`. Frame `T' − 1` can be the machine's landing. `L + 1 < T'` excludes this only if `L` is the machine's last landing, and `L` is not tied to the machines either.

So the link would add a field and would not close `ground`. The case split above needs neither.

## `reads` stays

`reads` is the only link from the class of the model's jump to the machines. The class is a field of the arc: `fast = (A ≤ v)`, for the stored speed `v` that the model's takeoff reads (`Jump.arcStart`). `reads` says that the machine's stored speed is at least `A` too. It cannot be a condition of the model only: it is a statement about a byte of a machine.

Without it one case stays open: the model's jump is fast, and the machine's stored speed is below `A`. The touch is then on `g = T' + 1`. Take `T' = L + 1` and two frames with the feet inside the base. The landing's bound is `P'(L) ≤ P₂(e) − 224 < P₀`, and `hop_short` needs `P'(L) < P₀ − 16`. The position alone is 16/256 px short.

It would follow if the arc were read from the machines: frame `T'` reads a jump (one state), and its vertical step is `vstep` with the machine's stored speed. `VertModel.vert_model` gives the step: its proof does not use the hypothesis on the stored speed, and from the state 0 its condition on the halt value is empty. This belongs to the jump's path (1-1-f-6-3).

## On real frames

`stop-read-check` (exit 0, 29 s). On every counted frame before the touch: `stored_step`. On every takeoff after a landing that reads a stored speed of `A` or more: going back from the takeoff to the landing, the first frame that ends with the stored speed `|v₂|` has `|v₂| ≥ A`; if there is none, `abs(L) ≥ A`. `L` is the machine's last landing before the takeoff.

| run | runs | frames | end with `\|v₂\|` | else kept | takeoffs with `abs ≥ A` after a landing (a frame wrote, none did) | bad |
|---|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 239 | 238 | 1 | 6 (3, 3) | 0 |
| random inputs from control | 100 | 29,055 | 28,651 | 404 | 25 (24, 1) | 0 |
| random inputs from the movie's frames | 100 | 15,777 | 15,680 | 97 | 28 (26, 2) | 0 |
| hops: A pressed and released, with or without Right | 33 | 5,750 | 5,750 | 0 | 17 (16, 1) | 0 |

Both cases come on real frames. By `fast_short`, a run that meets `Run` has no direct grab by a fast jump. So on such a run `reads` is never used with its premise.

## Not proved

* The field `reads`: the fast jump of the model reads a stored speed of at least the air threshold at `seq(T' − 1)`.
* `Run.stored_step` uses the conditions of `frames` (`state`, `collide`) and of `keep` (`cleanE`, `noStore`), and the touch not later than `farN` frames after control, as `Run.stop_step` does.

No new check on the ROM. The private proofs are unchanged.

**Files.** `stored_step` in `Theorems/StopRead.lean`; `Approach.fastWay`, `fast_near`, `fast_late`, `fast_short`, `fastLink_of_cases`, `approach_of_cases`, `Run.stored_step` in `Theorems/PoleJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta stop-read-check FM2 100     # the table above (about 30 s)
```
