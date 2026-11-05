[← Back](../README.md) | [English](FastAccel.md) | [Japanese](FastAccel-ja.md)

# Fast accel

**Statement.** If small Mario stands still on the ground at the start of a level (speed 0,
facing right), in a land area (ground, underground or castle) with nothing around him, then
with a real controller he can reach the running top speed (2.5 px/frame) in **34** frames,
and cannot in 33 or fewer.

```
upper :  ∃ w ∈ PadA^34,  v(Full(ctx, w)) ≥ v_top
lower :  ∀ σ ∈ (PadA × {land, stay})^{≤ 33},  v(Relax(ctx, σ)) < v_top
```

Lean: `fast_accel : (∀ a ∈ landAreas, GainBound …) → FastAccel.BoundsAllAreas sy ctx padInputsA relaxInputs 33 34`,
i.e. `FastAccel.Bounds` for each land `AreaType` (`fast_accel_area1` … `area3`). With
`prove.py --full` also `fast_accel_full`, the same without `GainBound` (full search).

**Two proofs of the lower bound.**

* *Pruned search* (default, about 20 s per area). `V = 256·speed + subspeed`.
  `GainBound`: one frame gives `V' ≤ max(V, 0) + a_max` (`a_max` = the largest friction adder).
  So a state with `max(V, 0) + a_max·r < 256·v_top`, with `r` frames left, cannot reach the
  top speed in time, and is dropped (`Cert.lower_bound_pruned`, `lower_of_fast`). Only about
  14,000 states remain instead of about 900,000. Subspeed tricks (freezing it in the air,
  keeping it after L+R) are inside `V`, so they are covered. Under the assumption of
  [Top speed bound](TopSpeed.md) (a frame changes the speed and the subspeed only through the
  five checked routines), `GainBound` is `Frame.gain`, proved there by arithmetic. As a
  hypothesis about `stepRelax` it stays an assumption: checking it directly would cost more than
  the full search.
* *Full search* (`--full`, about 16 min per area): every relaxed state of every frame; no
  `GainBound`.

**Conditions.** The relaxed step reads, besides its state and the input, only these scene
bytes (found by `smbrta relax-reads`; the position and the vertical bytes are read too but do
not matter, see below):

| scene byte | value in the theorem |
|---|---|
| `AreaType` | each land area: ground, underground, castle |
| `PlayerSize` | small Mario |
| `SwimmingFlag`, `PlayerChangeSizeFlag`, `JumpspringAnimCtrl`, `TimerControl` | as at the 1-1 start (normal play) |
| `GameEngineSubroutine` | the player can be controlled |
| `Player_CollisionBits` | nothing touched (open area) |

The start state is the one of the 1-1 start; every level start in two TAS movies has the same
state when it starts on the ground. So the theorem covers every frame with these values.
Starting in the air (entering an underground level from above), big Mario, and water are not
covered yet.

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
