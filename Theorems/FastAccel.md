[← Back](../README.md) | [English](FastAccel.md) | [Japanese](FastAccel-ja.md)

# Fast accel

**Statement.** From the first controllable frame of 1-1, with a real controller, Mario can
reach the running top speed (2.5 px/frame) in **34** frames, and cannot in 33 or fewer.

```
upper :  ∃ w ∈ PadA^34,  v(Full(ctx, w)) ≥ v_top
lower :  ∀ σ ∈ (PadA × {land, stay})^{≤ 33},  v(Relax(ctx, σ)) < v_top
```

Lean: `fast_accel : FastAccel.Bounds sy ctx padInputsA relaxInputs 33 34`.

* `Full` is the full emulator (no model). `PadA`: the 36 button sets a real controller can
  press without Start/Select.
* `Relax` is the relaxed model: the horizontal state plus a ground/air flag; a jump starts as
  in the game, and in the air Mario may land at the end of any frame.

**The input (fast accel).**

| frames | input | what happens |
|---|---|---|
| 1 | Left | face left |
| 2 | Down | speed 0, moving direction := facing (left) |
| 3 | A+Right | jump; in the air the facing stays left, so facing ≠ moving and the acceleration doubles |
| 4–23 | Right | accelerate in the air |
| 24–25 | B+Right, Right | land; the speed is now high enough to raise the air speed cap |
| 26 | Left | face left again |
| 27 | A+Right | second backward jump |
| 28–34 | Right | top speed after frame 34 |

The no-L+R TAS (tasvideos submission 6456) uses the same opening and also reaches the top
speed after 34 frames.

**From the model to the game.** Every real run is a run of the relaxed model, because the
air code reads no vertical byte (`relax-indep`: 106,441,560 varied steps, 0 differences) and
every real landing happens at some frame. The position does not matter either
(`relax-indep … pos`: 0 differences). So no real sequence of ≤ 33 frames reaches the top
speed in the open area without Start/Select. This step is checked by programs, not by Lean.

**Files.** `Theorems/FastAccel.lean`, private `Proof/FastAccel.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta relax-layers 50          # relaxed minimum: 34
.lake/build/bin/smbrta realize 34               # finds the witness (about 40 min)
.lake/build/bin/smbrta relax-indep 33           # and: 33 pos
lake build Proof.FastAccel   # in the private project, about 16 min
```
