[← Back](../README.md) | [English](TasFastAccel.md) | [Japanese](TasFastAccel-ja.md)

# TAS fast accel

**Statement.** From the first controllable frame of 1-1, with Left+Right allowed (TAS rules),
Mario can reach the running top speed in **32** frames, and cannot in 31 or fewer.
(Otherwise as in [Fast accel](FastAccel.md).)

```
upper :  ∃ w ∈ LRA^32,  v(Full(ctx, w)) ≥ v_top          (theorem)
lower :  ∀ σ ∈ (LRA × {land, stay})^{≤ 30},  v(Relax(ctx, σ)) < v_top   (theorem)
31 frames: impossible                                     (exhaustive search, not Lean)
```

Lean: `tas_fast_accel : FastAccel.Bounds sy ctx lrInputsA relaxInputsLR 30 32`.

**The input.** The opening of the HappyLee TAS (tasvideos publication 1715M):

| frames | input |
|---|---|
| 1 | Left+Right (facing becomes "both": facing ≠ moving at once) |
| 2 | A+Right (jump) |
| 3–21 | Right |
| 22–23 | nothing, B+Right (land) |
| 24 | Left |
| 25 | A+Right (second backward jump) |
| 26–32 | Right |

Left+Right reaches the doubled acceleration in one frame instead of two (Left, then Down),
which saves the 2 frames against [Fast accel](FastAccel.md).

**Why 31 is impossible.** The relaxed model allows 31, so the relaxed bound alone stops at
31. The exact jump model (all carried bytes) was searched for 31 frames, keeping only states
whose relaxed projection can still reach the goal in time, which loses no real path. Every
branch died by frame 21. The exact model matches the full emulator on all 32 frames of the
TAS opening. Vertical independence for these inputs: 134,209,152 varied steps, 0
differences. (The position check was not run for these inputs.)

**Files.** `Theorems/TasFastAccel.lean`, private `Proof/TasFastAccel.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta relax-layers 50 lr       # relaxed minimum: 31
.lake/build/bin/smbrta realize 31 lr            # no sequence (about 50 min)
lake build Proof.TasFastAccel   # in the private project, about 20 min
```
