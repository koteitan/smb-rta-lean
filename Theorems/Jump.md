[← Back](../README.md) | [English](Jump.md) | [Japanese](Jump-ja.md)

# The height of a jump

**Statement.** Follow one frame of the vertical bytes on the game's movement routine (`vstep`, no collisions),
from every takeoff speed, with A pressed or not on every frame. A jump is **fast** when the takeoff speed is
1.5625 px/frame or more, **slow** otherwise. Frame 0 is the takeoff frame.

1. Rising at the height of a direct grab of the flagpole happens only on frame 2 of a slow jump and on frame 1 of
   a fast one.
2. From the ground onto a block, and from a block back to the ground:

   | block, rows above the ground | onto it: (last frame at or below the height where its side stops him, first possible frame on it), slow | the same, fast | off it, slow: frames to the ground after the last frame above its top; frames in the air | off it, fast: frames to the ground after the last frame above its top | stepping off: frames to the ground |
   |---|---|---|---|---|---|
   | 1 | (1, 16) | (0, 16) | 4; 24 | 5 | 8 |
   | 2 | (5, 11) | (4, 10), (5, 9) | 8; 28 | 9 | 12 |
   | 3 | (10, 17), (11, 16) | (8, 13) | 12; 32 | 13 | 16 |
   | 4 | (18, 23) | (13, 17) | 16; 35 | 17 | 20 |

   A pair `(a, b)` means every landing has a last low frame `≥ a` and a frame `≥ b`, for one of the pairs listed.

The numbers in the table are what the search finds. The checks are in Lean:

```
arc_spec   :  arcCheck y₀ h P = true  →  P holds on every frame ≤ 80 of every jump from the height y₀
arc_k      :  the counter k is the number of frames; the takeoff class stays
jump_grab  :  arcCheck ground 1 (riseOk 1 2 1) = true
jump_block :  arcCheck ground h (windowOk h slow fast) = true,
              arcCheck (stand h) h (dropOk aboveSlow aboveFast airSlow) = true,
              walkOk h steppingOff = true
```

Lean: `Theorems/Jump.lean`, private `jump_grab`, `jump_block1` .. `jump_block4` (by `native_decide`).

## How fast he falls

The fall speed is capped, but the cap clears the fraction of the speed only when the fraction is large enough. After a
fast jump it is cleared at once, so he falls exactly 4 px per frame. After a slow jump the fraction stays on every other
frame and carries into the position: he falls about 4.2 px per frame on average, 5 px on some frames. That is why the fall
after a slow jump is one frame shorter in the table.

## Assumptions (not proved in Lean)

* The routine is run with no collisions: he is not stopped on the way up, and landing happens at the height the
  collision code gives (see [Grabbing the pole from below](PoleGrab.md)). Hitting something only ends the arc.
* The vertical bytes depend on the horizontal ones only through the absolute speed that the jump reads.
* While he is stepping off, A is not read (`walkFrames` runs with A not pressed): no jump can start in the air.

**Files.** `Theorems/Jump.lean`, private `Proof/Jump.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta jump-table     # the table and the checks, as a program (4 s)
```
