[← Back](../README.md) | [English](SidePipe.md) | [Japanese](SidePipe-ja.md)

# Entering the side pipe

**Statement.** Mario enters the side pipe exactly on a frame that lands or stands on the ground, not rising, facing right, with
his right side in the pipe's mouth. In the air the pipe stops him. So the entry frame is a frame on the ground, at the mouth's
left end or past it, and it cannot come before the fall from the block has ended.

`x₀` is the first `x` with his right side in the mouth. `P₀` is the position of the mouth's left end.

```
rule(x, y, vy, facing)  ⇔  0 ≤ vy  ∧  feet in the landing depth of the ground  ∧  facing = right  ∧  x₀ ≤ x

enters_eq_rule    :  sideCheck → on every state of the domain, enters = rule
ground_of_enters  :  sideCheck, enters → on the ground
mouth_of_enters   :  sideCheck, enters → x₀ ≤ x
no_enter_left     :  sideCheck, P < P₀ → not enters
entry_after_jump  :  P(s) < goal for s ≤ N,  goal ≤ P(t + 1),  t + d ≤ E  →  N + d ≤ E
entry_after_step  :  P(s) < goal for s ≤ N,  goal ≤ P(t),  t + w ≤ E  →  N + 1 + w ≤ E
slow_short        :  P(T + air) ≤ B + c·(air + 1),  B + c·(air + 1) < P₀  →  P(T + air) < P₀
side_rules        :  sideCheck = true        (private, by native_decide)
```

Lean: `Theorems/SidePipe.lean`, private `side_rules`.

## How

`sideCheck` runs `PlayerBGCollision` with the pipe's tiles written into the block buffer. A landing sets the state to the ground
state before the side check runs, so the check enters on that same frame. In the air the same tile stops him.

The last three theorems are the arithmetic of [the 1-1 route](../docs/route-1-1.md), section 3. `d` and `w` come from
[The height of a jump](Jump.md), `goal` is the position past the block's right end.

## Assumptions (not proved in Lean)

* The routine is checked alone, not joined to the rest of the frame. That real frames follow `rule` is the same kind of assumption
  as in [Top speed bound](TopSpeed.md).
* The block buffer is written by hand, from the tiles of the collision code and the column in the level data, on page 0.
* The domain is small Mario, from 4 px left of the mouth to the last `x` with his right side in it, heights from where his side
  reaches the part above the mouth to below the landing depth. Further right his left side reaches the mouth too, and he can enter
  there as well; a lower bound does not need that part. Rising is checked only above the ground.
* In `entry_after_jump`, `entry_after_step` and `slow_short` the positions and frames are inputs. Their source is the route page.

**Files.** `Theorems/SidePipe.lean`, private `Proof/SidePipe.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-check     # the routine against the rule, as a program
```
