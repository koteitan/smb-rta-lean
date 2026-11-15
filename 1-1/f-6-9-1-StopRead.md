[← Back](README.md) | [English](f-6-9-1-StopRead.md) | [Japanese](f-6-9-1-StopRead-ja.md)

# The stored speed before a fast jump, read from the machines

**Claim.** Take a counted frame `j` before the touch (`1 ≤ j < g`) of the frames of `keep`, with the conditions of `frames` and the touch not later than `farN` frames after control. Then:

* a frame that starts with the speed 0 ends with the stored speed `|v₂|`, or it keeps the stored speed and the moving direction of the frame before (`Run.stop_step`);
* any frame ends with the stored speed `|v₂|`, or it keeps the stored speed of the frame before (`Run.stored_step`);
* a frame that starts on the ground and whose player's routine reads no jump ends with the stored speed `|v₂|` (`StopRead.ground_step`).

So the field `stopped` of `PoleJoin.ApproachCases` is gone. The field `onGround` was replaced by a field `ground` on two single states, and `ground` is gone too: [The frames between the landing and a fast jump](f-6-9-2-StoredStep.md). The route no longer uses `ground_step`.

`abs(j)`, `md(j)`, `st(j)` are the stored speed, the moving direction and the player's state of `seq j`, the machine at the end of the counted frame `j`. `v(j)` is the speed at its start (that of `seq(j − 1)`). `v₂(j)` is the speed at the end of the move (`PlayerSubs`). `jump(j)` is the jump that the frame's player's routine reads: on the ground, A pressed, A not pressed on the frame before. `tr(k)` is the machine `k` instructions into the frame, `n₀` the instruction where it first comes to the player's routine, `Q = PlayerSubs`. `c` is the case of the player's routine (`FrameModel.caseOf`): `st(c)` is the state of the model (1 when he jumps from the ground), `lr(c)` the Left or Right that the movement routine reads.

```
frameE_move  :  ReadE,  Same   →   ∃ k ≥ n₀,  pc(tr(k)) = Q  ∧  v₂ = v(tr(k))  ∧  f₂ = f(tr(k))  ∧  P₂ = P(tr(k))
stored_c4N   :  AtFrame(R)   →   ∃ k,  R_k at the mover  ∧  (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(R_k) = |v(R_k)|)
                                     ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(R_k) = v(R)  ∧  abs(R_k) = abs(R)  ∧  md(R_k) = md(R))
stored_subs  :  AtFrame(tr(n₀)),  Q once after n₀   →   ∀ k ≥ n₀,  pc(tr(k)) = Q   →
                   (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(tr(k)) = |v(tr(k))|)
                   ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(tr(k)) = v(tr(n₀))  ∧  abs(tr(k)) = abs(tr(n₀))  ∧  (v(tr(n₀)) = 0  →  md(tr(k)) = md(tr(n₀))))
stop_step    :  1 ≤ j < g,  v(j) = 0   →   abs(j) = |v₂(j)|  ∨  (abs(j) = abs(j − 1)  ∧  md(j) = md(j − 1))
stored_step  :  1 ≤ j < g   →   abs(j) = |v₂(j)|  ∨  abs(j) = abs(j − 1)
ground_step  :  1 ≤ j < g,  st(j − 1) = 0,  jump(j) = false   →   abs(j) = |v₂(j)|
```

The track of the run (`PoleJoin.trackOf`) is read from the machines: `abs` and `md` as above. Only the vertical state `u` is given by the field `direct`. Before, the field `direct` gave the whole track, and nothing tied its stored speed or moving direction to the machines.

## How

`SurfaceRead.frame_readE` now also gives the instruction `k` of the end of the move, with `v₂`, `f₂`, `P₂` the bytes there. Its old conclusions are kept. So `v₂` of the frame is the speed at an arrival at `Q` (`frameE_move`).

`stored_c4N` is `FrameModel.stored_c4` without its hypothesis that the stored speed is `|v|` at the player's routine. It takes the same walks. On the ground, and in the air with Left or Right, the frame runs `ImposeFriction`, which writes `|v|` into the stored speed (`fric_abs`, from `TopSpeed.frictionCheck`). In the air with neither, the walk to the mover keeps the speed, the stored speed and the moving direction. `stored_c4` needed the hypothesis only in this branch.

`stored_subs` goes on to `Q` with two walks from the mover. The walk of `FrameModel.storedOK` keeps the speed and the stored speed. The walk of the mover (`FrameModel.tail_spec`) sets the moving direction from the speed, and keeps it when the speed is 0. The frame comes to `Q` once after the player's routine (`GuardE.subs_onceE`), so both walks end at the same instruction.

`stored_end` joins them on a counted frame. Up to the player's routine, the walk of `CtrlKeep` and the frames that end paused before it keep the speed, the stored speed, the moving direction and the player's state (`CtrlKeep.keepA`, `OnFrames.lagKeep`). From `Q` to the frame's end, `GuardE.keepHE` keeps the stored speed and the moving direction. `stop_step` and `stored_step` are its two cases, with and without the moving direction. `ground_step`: with the state 0 and no jump read, the case of the player's routine is on the ground (`stOf_ground`).

A frame that starts on the ground and reads a jump is in the air in its case (`st(c) = 1`). With no Left or Right it keeps the stored speed. So "the frame starts on the ground" alone does not say that it writes `|v₂|`; `stored_step` asks neither.

## On real frames

`stop-read-check` (exit 0, 29 s). On every counted frame before the touch: `stored_step`; `stop_step` when the frame starts with the speed 0; `ground_step` when it starts on the ground and reads no jump. `v₂` is the speed at `Q`. Every frame came to `Q` exactly once after the player's routine.

| run | runs | frames | end with `\|v₂\|` | else kept | from speed 0 (kept, not `\|v₂\|`) | on the ground, no jump | bad |
|---|---|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 239 | 238 | 1 | 5 (1) | 48 | 0 |
| random inputs from control | 100 | 29,055 | 28,651 | 404 | 9,766 (404) | 14,549 | 0 |
| random inputs from the movie's frames | 100 | 15,777 | 15,680 | 97 | 3,385 (97) | 7,526 | 0 |
| hops: A pressed and released, with or without Right | 33 | 5,750 | 5,750 | 0 | 2,636 (0) | 1,203 | 0 |

On these runs every frame that keeps a stored speed other than `|v₂|` starts with the speed 0. The takeoffs are on the page of [the frames between the landing and a fast jump](f-6-9-2-StoredStep.md).

## Not proved

* The field `reads`: the fast jump of the model reads a stored speed of at least the air threshold at `seq(T' − 1)`.
* `Run.stop_step` and `Run.stored_step` use the conditions of `frames` (`state`, `collide`) and of `keep` (`cleanE`, `noStore`), and the touch not later than `farN` frames after control, as `Run.reads` does.

No new check on the ROM: the walks are those of `SurfaceFrames.numbersCheck` (`FrameModel.modelOK`, `storedOK`, `CtrlKeep.ctrlCheck`, `AfterKeep.hCheck`). The private `pole_keep` (`keepCheck`, the movement routine on `keepCases`) is gone.

**Files.** `Theorems/StopRead.lean`; `frame_readE`, `frameE_move` in `Theorems/SurfaceRead.lean`; `trackOf`, `Run.stop_step`, `Run.stored_step` in `Theorems/PoleJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta stop-read-check FM2 100     # the table above (about 30 s)
```
