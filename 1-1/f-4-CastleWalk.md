[← Back](README.md) | [English](f-4-CastleWalk.md) | [Japanese](f-4-CastleWalk-ja.md)

# From touching the pole to the castle

**Statement.** From the touch states listed below, after a direct grab of the flagpole (rising, at the height where the end routine starts at once), the castle entry comes 126 frames
after the frame of the touch if the fraction of Mario's position is 80/256 px or more, and 127 frames after otherwise. A touch at the 8 other heights takes at least 160 frames.
Other states give an earlier entry: this is not a lower bound over every touch state.

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
[The change into the bonus room](b-1-PipeTransition.md), through the room and the side pipe, then Right with B and a few jumps. The last frame's position and vertical bytes
are then overwritten to give the frame before a grab.

What is measured but not all in the theorem: the length depends on the fraction, the moving direction, the running speed and the stored speed. On this page's states the
boundary of the fraction is 80/256 px; on the TAS's state it is 48/256 px, and the TAS has 32/256 px to spare. A slow grab not moving left, with a fraction of 176/256 px or more,
gives the touch + 125. A grab by a fast jump gives the touch + 1 or + 2. Touches at other heights took 153 to 164 frames. That real runs do not reach these is in
[From control to the castle](f-5-PoleJoin.md). Of the 4 pixels of the pole's range, only the left 2 give a direct grab. In the right 2 his head meets the pole first, and he touches it lower down.

## Assumptions (not proved in Lean)

* `GMerge`: states equal except for the bytes that echo the buttons behave the same. This is a hypothesis of `allInputs`, as in [The change into the bonus room](b-1-PipeTransition.md).
* All inputs ran from one touch state only. The other states ran with no input.
* The states at the pole are overwritten at the end of a real run; they are not shown reachable as they are. Other runs differ in enemies, scroll and timers, and these are not covered.
* `anyFraction` covers the 16 multiples of 1/16 px (a position moves by `16·v` in 1/256 px) and the largest fraction. That the fraction of a real touch is such a multiple is the theorem `PoleJoin.Run.frac`, from the walk of one whole frame in control ([One whole frame in control keeps the castle flag and the fraction's low bits](f-6-19-FrameKeep.md)). Checking all 256 fractions here instead would take about 17 s more (measured: 18,212 ms against 1,196 ms for these 17).
* Start and Select are not in the input set.

**Files.** `Theorems/CastleWalk.lean`, private `Proof/CastleWalk.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta castle-check     # the frames by fraction and by height, and the check (true, about 5 s)
```
