[← Back](README.md) | [English](e-2-10-3-3-ImpedePosition.md) | [Japanese](e-2-10-3-3-ImpedePosition-ja.md)

# The position through ImpedePlayerMove

`ImpedePosition.routine_return` proves the whole routine on a real machine, including its return to the caller. It needs `Good`, the entry program counter, and a checked ROM. The initial stack pointer, flags, side and speed bytes are arbitrary.

Let R be the entry machine and B the returned machine. Position P counts 1/256 pixel. The checked branch defines d, which is −1, 0 or 1.

```
k ≤ 65
pc(B) = returnPc(R)
SP(B) = SP(R) + 2
P(B) ≡ P(R) + 256·d  (mod 2²⁴)
```

The speed stays unchanged or becomes zero according to the branch. The position fraction and the horizontal subspeed stay unchanged. A positive d requires a nonpositive signed input speed (`positive_only`). The signed-byte boundary case follows the actual compare instruction.

`exact_of_mod` makes the position equation exact when P(R) is at least one pixel from the lower end and P(R) + 256 is below the upper end. Without these explicit margins the result is modular.

`piece0_spec` proves a checked instruction piece with an arbitrary unchanged stack pointer. Its check watches every stack byte. The proof composes 65,536 prefix cases, 512 pixel cases, 1,024 page cases and one tail case. `routine_return` then proves the actual return instruction using the saved caller stack.

`trace_call` applies this result at a call on a frame trace, with explicit conditions on the idle loop, the current frame and the remaining instruction time. `ordinary_step` keeps the position when that instruction writes none of its three bytes. These are local pieces. They do not prove that every other instruction after the scroll handler meets this condition.

`positive_effect` proves that a positive entry speed keeps its position when the speed stays, and stops exactly one pixel left when the speed becomes zero. `SurfaceFrames.AfterP.impede_return` turns this into the existing `AfterP` relation for a single complete call under the explicit position margins. The first state of that relation is the call entry, not the scroll handler. It does not remove the whole-frame field.

## What remains

`SurfaceFrames.AfterP` and `CollideS` remain assumptions. Calls can occur more than once. The proof still needs the relation to the position at the scroll handler and at the frame's start. It must also handle the [screen clamp](e-2-10-3-4-ScreenClamp.md), climbing, platforms, and indexed stores by the movement routine. No field of `Route.Run` is removed or added by this result.

**Files:** `Theorems/ImpedePosition.lean`, private `Proof/ImpedePosition.lean`.

## Checked on real frames

`pos-after-real FM2 200` checked 128,679 frames from the TAS and own inputs: 3,053 collision-push calls and 13,551 screen-clamp calls. Entry `Good`, return, speed, fraction, modular position, margins and target range had zero failures. After the scroll handler, no instruction outside these two routines stored to a position byte. The command exited 0. The sampled frames start in control and store to none of the routine, mode or task bytes. This is a check of runs, not a proof about every frame.

The ROM predicates were true in 430 ms for the collision push and 6 ms for the screen clamp. Both private facts are generated with `native_decide`. The observed clamps selected only one edge; the ROM check and general theorem cover both.
