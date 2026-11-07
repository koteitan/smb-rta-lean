[← Back](../README.md) | [English](SideTransition.md) | [Japanese](SideTransition-ja.md)

# The change out of the side pipe

**Statement.** From the frame Mario enters the side pipe, control above ground comes exactly 282 frames later. For one entry state
from a real run this is shown for every input on every frame, with Start and Select left out, under one hypothesis (`GMerge`). For other
entry states it is shown with no input, without a hypothesis: other pixels, fractions, speeds, a big Mario, real entries at three
pixels, and real entries on 21 consecutive frames. There is one exception: an entry frame that ends with `x` a multiple of 16 takes 378
frames. No state shown here takes fewer than 282. The exception cannot be reached by walking or falling into the mouth (see below; this reasoning is not in Lean).

`m₀` is the machine at the start of 1-1. `run(m, w)` is the machine after the real frames with the inputs `w`, `frame(m, i)` one such frame.
`ctl(m)` is `controllable`. `0^k` is `k` frames of no input. `I` is the 64 inputs: every subset of A, B, Up, Down, Left, Right, opposite
directions included. `P` is the machine on the frame before the entry in a real run, `E = frame(P, Right)` the machine at the end of the entry frame.
`x₀` is the first `x` with his right side in the mouth ([Entering the side pipe](SidePipe.md)), `z` the pixel of the mouth that is a multiple of 16. `P[x]` is `P`
with its `x` overwritten so that the entry frame ends at `x`, and `E_x = frame(P[x], Right)`. `Exact(m, n)` means `∀ k, 1 ≤ k ≤ n → ( ctl(run(m, 0^k)) ↔ k = n )`.

```
entered      :  ctl(P)  ∧  the pipe's routine is set in E  ∧  x(E) = x₀
allInputs    :  GMerge  →  ∀ w ∈ I^282 :  ctl(run(E, w))  ∧  ∀ k, 1 ≤ k < 282 → ¬ctl(run(E, w[..k]))
noInput      :  Exact(E, 282)
otherPixels  :  ∀ x ∈ {x₀, …, x₀ + 15} ∖ {z} :  the entry frame enters from P[x]  ∧  x(E_x) = x  ∧  Exact(E_x, 282)
                                                ∧  run(E_x, 0^282) = run(E, 0^282)
zeroPixel    :  the entry frame enters from P[z]  ∧  x(E_z) = z  ∧  Exact(E_z, 378)
otherMoved   :  ∀ c ∈ moved :  Exact(c(E), 282)  ∧  run(c(E), 0^282) = run(E, 0^282)
otherBig     :  a big Mario on P enters  ∧  Exact(E_big, 282)
otherRoutes  :  ∀ d ∈ {1, 2} :  a real run enters with x = x₀ + d  ∧  Exact(its end, 282)
grid         :  ∀ d < 21 :  a real run stands d more frames and walks in, it enters  ∧  Exact(its end, 282)
```

| entry state | inputs during the change | result | hypothesis |
|---|---|---|---|
| `E`: a real run, walking off the block, stopped by the pipe in the air, walking in on the floor | all of `I`, on every frame | control on frame 282, not before | `GMerge` |
| `E` | none | control on frame 282, not before | none |
| `P` overwritten, the entry frame really runs: each pixel `x₀` to `x₀ + 15` except `z` | none | control on frame 282, not before; the whole machine on that frame is the machine from `E` | none |
| `P` overwritten, the entry frame really runs: `z` | none | control on frame 378, not before | none |
| `E` overwritten (`moved`): 4 other fractions of the position; speed 0, half and full top speed both ways, with the moving direction, the facing and the stored absolute speed; the speed's fraction; the running speed; the running timer | none | control on frame 282, not before; the same whole machine | none |
| `P` overwritten: a big Mario | none | control on frame 282, not before | none |
| real runs: a jump from the block, braking in the air, Right with B again, landing at the mouth, at `x₀ + 1` and `x₀ + 2` | none | control on frame 282, not before | none |
| real runs: standing on the floor at the mouth, the entry on 21 consecutive frames, so at every place of the 21-frame grid | none | control on frame 282, not before | none |

Lean: `Theorems/SideTransition.lean` (`Statement`, `statement_of_check`, `checkOn`, `mergeTo`, `merged`, `eq_of_sameM`), and from
[The change into the bonus room](PipeTransition.md) `gchain`, `GMerge`, `first_control`, `no_input_of_chain`. Private `side_checks` (by `native_decide`) and `side_transition`.

## How

`gchain` is the check of the other change: it follows no input from the entry, on each frame runs every input of the set, and compares each result with the result of
no input. Here it runs 282 frames.

The other entry states use a shorter check. `mergeTo` runs a state with no input for 186 frames, checks it is not controllable on any of them, and compares
every field of the machine with the machine from `E` on the same frame. `eq_of_sameM` turns that into equality of machines. A frame is a function of the machine and the input,
so from then on the two runs are the same run (`merged`), and the remaining 96 frames are not run again. Nothing is assumed here. This also says more than a
comparison of the frame: the machine above ground is the same, down to the cycle count.

## Why the position does not matter

Read from the code, and checked by the runs above:

1. On the entry frame the collision routine sets the change timer and starts the pipe's routine.
2. While the pipe's routine runs, the collision routine returns at once. So the pipe is not touched again, and the timer is set only once. It does not matter that he is still in the pipe's tile.
3. The pipe's routine walks him right at 0.5 px per frame until the low nybble of `x` is 0, and the timer goes down by one on each frame. The two do not depend on each other. The
   walk ends after at most 30 frames.
4. The timer ends on frame 160. The screen goes off and most of the RAM is cleared, so `x`, its fraction and the speed are gone. From frame 161 or 162 (186 for the two pixels right of `z`) the machine is the same from
   every pixel. Then come 25 frames that build the area and 97 frames of rising out of the pipe.

**The exception.** The routine skips setting the timer if the low nybble of `x` is 0 on the entry frame. The timer is then still 0 from the last change, its first decrease wraps around, and it runs
for 256 frames instead of 160: 96 more, so 378.

Overwriting `x` at the end of the entry frame does not show this, because the timer was already set before the overwrite: with `z` written there, the run still takes 282.
That is why `otherPixels` and `zeroPixel` write on the frame before, so that the entry frame runs with that `x`.

**Why `z` is not reached.** He enters on the first ground frame at or past `x₀` while facing right. In the air the pipe stops him and pushes him back. Facing left on the ground, it stops him too. So the frame before the entry has `x < x₀`, or he
has been pushed back, and he moves at most 2.5 px per frame. So real entries have `x ≤ x₀ + 2`, and `z` is further right than that. The runs in `otherRoutes` are at `x₀ + 1` and `x₀ + 2`.

So a larger `x` gives no shorter change. The bound at frame 852 in [the 1-1 route](../docs/route-1-1.md) does not change.

## Measured, not in the theorem

* 63 real entries: `x₀`, `x₀ + 1` and `x₀ + 2`, each with 0 to 20 idle frames on the block before the same run: all 282.
* 87 other real entries (different `x`, fraction or speed) from a search over jumps and braking: 52 at `x₀`, 30 at `x₀ + 1`, 5 at `x₀ + 2`, none further, at speeds from 1/16 to 37/16 px per frame: all 282.
* The pixels `x₀ + 16` to `x₀ + 26` (his left side in the mouth), written on the frame before: they enter, all 282. `x₀ + 27` does not enter.
* Each of the 64 inputs held for all 282 frames, and 30 random sequences of the 64 inputs: control on frame 282, not before, with the key of no input on that frame.
* Select held: 282. Start is not in `I`. It pauses the game, which makes the change longer. A press on the frames tried from 161 to 185 of the change is ignored (282). A press on the other frames tried pauses, and a second press 60 frames later gives 342.
* The TAS enters at 570 at `x₀ + 1`, and has control at 852.

## Assumptions (not proved in Lean)

* `GMerge`: two states reached from `E` after the same number of frames, with equal keys, go on to equal keys under the same input. This is a hypothesis of `allInputs`, as in [The change into the bonus room](PipeTransition.md). The measurements above support it.
* All inputs ran from one entry state only. The other states ran with no input.
* Only the listed states are covered. The theorem does not say that every entry of every run takes 282 frames. That real entries have `x ≤ x₀ + 2` is the reasoning above, not a theorem here.
* The states of `otherPixels`, `zeroPixel`, `otherMoved` and `otherBig` are overwritten; they are not shown reachable as they are. A big Mario was not run from a real mushroom.
* The code sets a shorter timer if the left edge of the screen is not on the first page. The mouth is on the first page and the screen's left edge is never right of Mario, so this branch does not apply. This is read from the code, not in Lean; every run here has the screen on the first page.
* Enemies, coins and the game timer differ from run to run and only the runs above were executed. The room has no enemies.
* Start and Select are not in the input set.

## Time

The check is about 31,000 frames of the emulator. All 64 inputs on all 282 frames are kept (18,330 frames, about 6.5 s). This is above the 5 s aimed at for a check. Cutting it would need a smaller input set on some frames, and then the theorem would no longer speak of every input. The screen is off on only 25 of the 282 frames, so sparing those would save about 9%. The whole check takes about 11 s natively.

**Files.** `Theorems/SideTransition.lean`, private `Proof/SideTransition.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-change-check     # the length by pixel, the real routes, and the check (true, about 11 s)
```
