[← Back](README.md) | [English](f-6-9-1-StopRead.md) | [Japanese](f-6-9-1-StopRead-ja.md)

# The stored speed before a fast jump, read from the machines

**Claim.** Take a counted frame `j` before the touch (`1 ≤ j < g`) of the frames of `keep`, with the conditions of `frames` and the touch not later than `farN` frames after control. Then:

* a frame that starts with the speed 0 ends with the stored speed `|v₂|`, or it keeps the stored speed and the moving direction of the frame before (`Run.stop_step`);
* a frame that starts on the ground and whose player's routine reads no jump ends with the stored speed `|v₂|` (`Run.ground_step`).

So the field `stopped` of `PoleJoin.ApproachCases` is gone. The field `onGround` is replaced by a field `ground` on two single states.

`abs(j)`, `md(j)`, `st(j)` are the stored speed, the moving direction and the player's state of `seq j`, the machine at the end of the counted frame `j`. `v(j)` is the speed at its start (that of `seq(j − 1)`). `v₂(j)` is the speed at the end of the move (`PlayerSubs`). `jump(j)` is the jump that the frame's player's routine reads: on the ground, A pressed, A not pressed on the frame before. `tr(k)` is the machine `k` instructions into the frame, `n₀` the instruction where it first comes to the player's routine, `Q = PlayerSubs`. `c` is the case of the player's routine (`FrameModel.caseOf`): `st(c)` is the state of the model (1 when he jumps from the ground), `lr(c)` the Left or Right that the movement routine reads.

```
frameE_move  :  ReadE,  Same   →   ∃ k ≥ n₀,  pc(tr(k)) = Q  ∧  v₂ = v(tr(k))  ∧  f₂ = f(tr(k))  ∧  P₂ = P(tr(k))
stored_c4N   :  AtFrame(R)   →   ∃ k,  R_k at the mover  ∧  (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(R_k) = |v(R_k)|)
                                     ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(R_k) = v(R)  ∧  abs(R_k) = abs(R)  ∧  md(R_k) = md(R))
stored_subs  :  AtFrame(tr(n₀)),  Q once after n₀   →   ∀ k ≥ n₀,  pc(tr(k)) = Q   →
                   (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(tr(k)) = |v(tr(k))|)
                   ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(tr(k)) = v(tr(n₀))  ∧  abs(tr(k)) = abs(tr(n₀))  ∧  (v(tr(n₀)) = 0  →  md(tr(k)) = md(tr(n₀))))
stop_step    :  1 ≤ j < g,  v(j) = 0   →   abs(j) = |v₂(j)|  ∨  (abs(j) = abs(j − 1)  ∧  md(j) = md(j − 1))
ground_step  :  1 ≤ j < g,  st(j − 1) = 0,  jump(j) = false   →   abs(j) = |v₂(j)|
ground       :  fast,  L + 1 < T'   →   st(T' − 2) = 0  ∧  jump(T' − 1) = false                  (field of ApproachCases)
```

The track of the run (`PoleJoin.trackOf`) is now read from the machines: `abs`, `md`, `st`, `jump` as above. Only the vertical state `u` is given by the field `direct`. Before, the field `direct` gave the whole track, and nothing tied its stored speed or moving direction to the machines.

## How

`SurfaceRead.frame_readE` now also gives the instruction `k` of the end of the move, with `v₂`, `f₂`, `P₂` the bytes there. Its old conclusions are kept. So `v₂` of the frame is the speed at an arrival at `Q` (`frameE_move`).

`stored_c4N` is `FrameModel.stored_c4` without its hypothesis that the stored speed is `|v|` at the player's routine. It takes the same walks. On the ground, and in the air with Left or Right, the frame runs `ImposeFriction`, which writes `|v|` into the stored speed (`fric_abs`, from `TopSpeed.frictionCheck`). In the air with neither, the walk to the mover keeps the speed, the stored speed and the moving direction. `stored_c4` needed the hypothesis only in this branch.

`stored_subs` goes on to `Q` with two walks from the mover. The walk of `FrameModel.storedOK` keeps the speed and the stored speed. The walk of the mover (`FrameModel.tail_spec`) sets the moving direction from the speed, and keeps it when the speed is 0. The frame comes to `Q` once after the player's routine (`GuardE.subs_onceE`), so both walks end at the same instruction.

`stored_end` joins them on a counted frame. Up to the player's routine, the walk of `CtrlKeep` and the frames that end paused before it keep the speed, the stored speed, the moving direction and the player's state (`CtrlKeep.keepA`, `OnFrames.lagKeep`). From `Q` to the frame's end, `GuardE.keepHE` keeps the stored speed and the moving direction. `stop_step` is its two cases. `ground_step`: with the state 0 and no jump read, the case of the player's routine is on the ground (`stOf_ground`).

Why `ground` asks the jump too. `st(T' − 2) = 0` alone is not enough. A frame that starts on the ground and reads a jump is in the air in its case (`st(c) = 1`). With no Left or Right it keeps the stored speed, so its `|v₂|` is not the stored speed. On a real run the jump of `T'` reads A pressed and not pressed on the frame before. So A is not pressed on `T' − 1`, and `T' − 1` reads no jump.

## On real frames

`stop-read-check` (exit 0, 27 s). On every counted frame before the touch: `stop_step` when the frame starts with the speed 0, `ground_step` when it starts on the ground and reads no jump. On every takeoff `T` after a landing `L` with `L + 1 < T`: the field `ground`. `v₂` is the speed at `Q`. Every frame came to `Q` exactly once after the player's routine.

| run | runs | frames | from speed 0 (kept, not `|v₂|`) | on the ground, no jump | takeoffs after a landing, `L + 1 < T` (with `ground`) | bad |
|---|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 239 | 5 (1) | 48 | 3 (3) | 0 |
| random inputs from control | 100 | 29,055 | 9,766 (404) | 14,549 | 348 (348) | 0 |
| random inputs from the movie's frames | 100 | 15,777 | 3,385 (97) | 7,526 | 201 (201) | 0 |
| hops: A pressed and released, with or without Right | 33 | 5,750 | 2,636 (0) | 1,203 | 157 (157) | 0 |

A real direct grab never comes from a fast jump (`fast_short`), so on real runs the field `ground` is never used with its premise. The table checks what it says on every real takeoff after a landing.

## Not proved

* The field `ground`: two conditions, each on one state (the machine at the end of the counted frame `T' − 2`, and the machine at the player's routine of the frame `T' − 1`). It would follow from the jump of `T'` if the takeoff `T'` of the model were tied to the jump that the machine reads, and if a walk followed A from the player's routine to the frame's end. Neither is done.
* The field `reads`: the fast jump of the model reads a stored speed of at least the air threshold at `seq(T' − 1)`.
* `Run.stop_step` and `Run.ground_step` use the conditions of `frames` (`state`, `collide`, `spareV`) and of `keep` (`cleanE`, `noStore`), and the touch not later than `farN` frames after control, as `Run.reads` does.

No new check on the ROM: the walks are those of `SurfaceFrames.numbersCheck` (`FrameModel.modelOK`, `storedOK`, `CtrlKeep.ctrlCheck`, `AfterKeep.hCheck`). The private `pole_keep` (`keepCheck`, the movement routine on `keepCases`) is gone.

**Files.** `Theorems/StopRead.lean`; `frame_readE`, `frameE_move` in `Theorems/SurfaceRead.lean`; `trackOf`, `ApproachCases.ground`, `Run.stop_step`, `Run.ground_step` in `Theorems/PoleJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta stop-read-check FM2 100     # the table above (about 30 s)
```
