[← Back](../README.md) | [English](CastleWalk.md) | [Japanese](CastleWalk-ja.md)

# From touching the pole to the castle

**Statement.** After a direct grab of the flagpole (rising, at the height where the end routine starts at once), the castle entry comes 126 frames
after the frame of the touch if the fraction of Mario's position is 80/256 px or more, and 127 frames after otherwise. It never comes earlier. A touch at
another height takes at least 160 frames.

`E` is the machine at the frame of the touch, `I` the 64 inputs (every subset of A, B, Up, Down, Left, Right; no Start, no Select), `0^k` is `k` frames of no input.

```
entered      :  he has touched the pole in E
allInputs    :  GMerge  →  ∀ w ∈ I^126:  castle(run(E, w)) ∧ ∀ k, 1 ≤ k < 126 → ¬castle(run(E, w[..k]))
otherStates  :  each jump state before the grab, each x of a direct grab:  castle(run(E', 0^k)) ↔ k = 126,  for 1 ≤ k ≤ 126
anyFraction  :  each fraction a position can have:  ¬castle(run(E', 0^k)),  for 1 ≤ k ≤ 125
otherTouch   :  each of 8 other heights:  ¬castle(run(E', 0^k)),  for 1 ≤ k ≤ 159
```

Lean: `Theorems/CastleWalk.lean`, private `castle_checks`, `castle_walk` (by `native_decide`).

## How

The check runs real frames on the emulator. To get there it runs its own route from the 1-1 start up to the ground beside the base block: the vertical pipe of
[The change into the bonus room](PipeTransition.md), through the room and the side pipe, then Right with B and a few jumps. The last frame's position and vertical bytes
are then overwritten to give the frame before a grab.

What is measured but not all in the theorem: the fraction decides 126 or 127, with 80/256 px as the boundary. The TAS's fraction at its touch is exactly 80/256 px, the
smallest with 126. Of the 4 pixels of the pole's range, only the left 2 give a direct grab. In the right 2 his head meets the pole first, and he touches it lower down.
Touches at other heights took 162 to 165 frames.

## Assumptions (not proved in Lean)

* `GMerge`: states equal except for the bytes that echo the buttons behave the same. This is a hypothesis of `allInputs`, as in [The change into the bonus room](PipeTransition.md).
* All inputs ran from one touch state only. The other states ran with no input.
* The states at the pole are overwritten at the end of a real run; they are not shown reachable as they are. Other runs differ in enemies, scroll and timers, and these are not covered.
* `anyFraction` covers the 16 multiples of 1/16 px (a position moves by `16·v` in 1/256 px) and the largest fraction. That a position's fraction is always such a multiple is not proved.
* Start and Select are not in the input set.

**Files.** `Theorems/CastleWalk.lean`, private `Proof/CastleWalk.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta castle-check     # the frames by fraction and by height, and the check (true, about 5 s)
```
