[← Back](../README.md) | [English](FastHop.md) | [Japanese](FastHop-ja.md)

# The fast hop beside the flagpole

**Statement.** A jump reads the stored absolute speed. A hit stops Mario but does not clear that byte, so a jump right after a hit can be
fast with no speed left. From a stopped Mario with a high stored speed:

* a frame in the air with no Left or Right keeps the stored speed, the speed and the moving direction;
* a ground frame, or Left or Right in the air, makes the stored speed `|v|`, which is below the air threshold.

So a fast hop needs no Left or Right from the hit until it starts, and it starts on the first frame on the ground. Then each frame with his
feet inside the block pushes him back, and he does not reach the pole's range.

```
absCheck        :  the movement routine follows the two points above on every state of the domain
no_update       :  frames follow them,  stored speed ≥ A after frame j + d  →  frame j updated nothing
fast_hop_short  :  x before the move over the block is left of P_f,  frames with the feet inside push back,  the hop is one
                   frame  →  P₂(g) < P₀
fast_hop_rules  :  absCheck = true        (private, by native_decide)
```

Lean: `Theorems/FastHop.lean`, private `fast_hop_rules`.

## How

`absCheck` runs the game's movement routine (`PlayerMovementSubs`) from speed 0. `no_update` goes back from the jump: if the byte is
still high after a frame, the frames since the hit did not write to it. With the moving direction kept, the collision rules of
[Grabbing the pole from below](PoleGrab.md) push him back on each of those frames, and `no_grab_near` there finishes it.

## Assumptions (not proved in Lean)

* The routine is checked alone. That real frames follow it, and that the frames between the hit and the jump have `ran` as the routine says,
  is the same kind of assumption as in [Top speed bound](TopSpeed.md). In Lean, these are the hypotheses of `no_update` and `fast_hop_short`.
* The domain: stored speed at the air threshold and at the top, every fraction, every Left and Right, every collision mask, the three states,
  facing right, moving right or left (with these the adder is doubled or not), both running speeds. Other stored speeds in between are not run.
* `no_update` itself does not name the moving direction; `fast_hop_short` takes the push back as a hypothesis, which follows from the kept moving
  direction and the collision rules. These two are not joined in one Lean statement.

**Files.** `Theorems/FastHop.lean`, private `Proof/FastHop.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta abs-check     # the routine on the domain, as a program (0 differ, 1 s)
```
