[← Back](../README.md) | [English](route-1-1.md) | [Japanese](route-1-1-ja.md)

# The 1-1 route: toward a lower bound on the frame 1-2 starts

**Goal.** With frame 0 the first controllable frame of 1-1, show that 1-2 does not start (the level
number does not change) before frame 1748. 1748 is the value of HappyLee's TAS.

This page records work in progress. For each segment it says whether the result is a **Lean
theorem**, an **emulator check** (not Lean), or **open**. Numbers are frames and distances relative
to the TAS (pixels, or 1/256 px); no ROM addresses or table values.

## The TAS route

| frames | what happens |
|---|---|
| 0 → 368 | the opening (top speed at frame 32), running at top speed, entering the fourth pipe |
| 368 → 459 | going down the pipe, the area change, entering the bonus room from the ceiling |
| 459 → 570 | bonus room: falling to the floor, jumping onto the brick block, entering the side pipe on landing |
| 570 → 852 | the side pipe, the area change, rising out of the pipe above ground |
| 852 → 1092 | accelerating on the pipe, crossing the final staircase, dropping next to the flagpole's base block, a small hop, grabbing the pole while rising |
| 1092 → 1218 | waiting on the pole, walking to the castle automatically (castle entry) |
| 1218 → 1748 | timer points, raising the flag, a wait aligned to a 21-frame grid |

## Results by segment

### 1. Running into the pipe (0 → 368): earliest

- Up to frame 32 the distance is at most the TAS's, by [The opening](../Theorems/Opening.md); after
  that at most 2.5 px per frame, by [Top speed bound](../Theorems/TopSpeed.md). The TAS runs exactly
  at both bounds (exactly at the bound every frame from 32 to 362).
- The pipe can be entered only with both feet on the pipe top (a 9-pixel range), on a falling or
  landing frame, with Down held (from the code). By the bounds, at frame 367 Mario is still 0.44 px
  short of the range. So no entry before 368.
- Status: the bounds are Lean theorems; the entry condition is read from the code (an assumption);
  combining them is arithmetic, not done in Lean.

### 2, 4. Pipes and area changes: fixed lengths (emulator check)

```
control in the bonus room  = pipe entry frame + 91
control above ground       = side pipe entry frame + 282
```

They depend on no input, no position or speed on the pipe, and not on the 21-frame grid (each routine
ignores or overrides the input; the routines that wait on the 21-frame grid are skipped in these two
changes). Inserting idle frames delays them by exactly that many frames; pausing only makes them longer.

### 3. The bonus room (459 → 570): open

- The side pipe is entered on the frame Mario lands on the floor at the pipe's mouth. Hitting the upper
  part of the pipe in the air stops him.
- Entering at 569 needs Mario 2.31 px ahead of the TAS at frame 557.
- The corner of the brick block binds tightly. The TAS presses Left for 3 frames first, so that it lands
  as far right as possible while still clearing the corner (just before clearing it, it is 15/256 px left
  of the position that hits it). With 2 Left frames or fewer, Mario hits the corner and loses his speed.
- From the TAS's state just after landing on the block (frame 511), the potential bound of
  [Reach](../Theorems/Reach.md) keeps frame 557 0.38 px short. It remains to bound the position and
  speed at the block landing over all inputs, including a variant that presses Right+B once on the
  floor-landing frame to break the air speed cap before jumping.

### 5a. Accelerating above ground (852 → 892): the pole is not reached early (emulator check)

- From the TAS's state at 852, every input for 40 frames on real frames (equal states merged, states
  that cannot catch up any more dropped by the potential bound). At frame 892 Mario can be at most
  144/256 px ahead of the TAS.
- After 892, at most 2.5 px per frame by the top speed bound. The TAS is at that bound too, except for
  a 16/256 px loss at frame 980. So at frame 1085 Mario is at most 160/256 px ahead of the TAS.
- Reaching the range where the pole can be grabbed at frame 1085 needs 528/256 px. So not by 1085.
- Assumption: that the dropped states cannot catch up rests on the open-area potential bound.

### 5b. Grabbing the pole and entering the castle: not before 1218 (emulator check)

How the pole works (from the code):

- The pole is touched in a 4-pixel range where Mario's right side is 3..6 px into the pole's column,
  above the height of the base block. Running
  in at ground level, Mario is stopped by the base block before that range.
- Touching it while rising, close to the base block's height, skips the slide: the end routine starts at
  once, and the castle entry is **the touch frame + 126**. Any other touch waits for the flag to come
  down, about 39 frames later.

Necessary conditions for a castle entry by 1217 (by formulas):

1. By frame 1091, enter the range while rising and still close to the base block's height.
2. That happens only 2 or 3 frames after a jump from the ground. A jump at 1.5625 px/frame or more is
   impossible, because on the ground next to the base block the speed is set to 0. So Mario has to come
   down onto the ground next to the block from above and then hop.
3. That needs a landing by 1087. At the top fall speed Mario falls exactly 4 px per frame (the fraction
   is cleared at the cap), so at frame 1084 he must be within 12 px of the ground.

Checked: from the state at frame 1084 (not yet touching the block), with the height (13 values), the
horizontal position (from 1 px behind the TAS to 160/256 px ahead, 10 values) and the facing direction
(3 values) changed, 390 cases, every sequence of 8 inputs over 8 frames. None enters the castle by 1217.

A detail of the TAS: pressing Left+Right next to the base block counts as Left (the right side is
blocked), so the moving direction becomes left. The push from the block then goes right, and Mario stays
in the range.

Not covered: arrivals at 1084 falling slower than the top fall speed, horizontal speeds below the top
speed, inputs with Left alone.

### From the castle to 1-2: a formula (from the code)

```
L = E + T + D + 107 + ((c − T − D) mod 21)
  E: castle entry frame   T: the game timer (frozen since the touch)
  D: 33 (no fireworks)    c: the interval timer's phase at E
```

The last wait is aligned to a 21-frame grid. The TAS starts it exactly on the grid, so it waits 20 extra
frames. A castle entry at 1218 gives 1748; at 1217 it gives 1727 (21 frames earlier).

## Summary

```
1-2 starts ≥ 1748
  ⟸ castle entry ≥ 1218                         (the castle-to-1-2 formula)
  ⟸ control above ground ≥ 852, plus 5a and 5b
  ⟸ side pipe entry ≥ 570 (+282)                ← segment 3: open
  ⟸ control in the bonus room ≥ 459 (+91)
  ⟸ pipe entry ≥ 368                             (segment 1)
```

It is also assumed that arriving later at any step never helps later on.

## Reproduce

With the TAS movie (fm2), in `git/`:

```
.lake/build/bin/smbrta tas-trace FM2                    # the route, against the bound
.lake/build/bin/smbrta tas-seg FM2 A B                  # position, speed, height for frames A..B
.lake/build/bin/smbrta tas-insert FM2 AT K              # K idle frames inserted at AT
.lake/build/bin/smbrta seg-search FM2 852 40            # the 5a search (over 10 minutes)
.lake/build/bin/smbrta end-poke FM2 1084 Y DX FD 8      # one 5b case (Y height, DX shift, FD facing)
.lake/build/bin/smbrta pot-bound FM2 511 46             # bonus room: the bound from the block
```
