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
- The pipe can be entered only with both feet on the pipe's top, with Down held, on a frame that runs the landing code: falling or standing on the top ([Entering the vertical pipe](../Theorems/PipeEntry.md)). Down with Left or Right on the ground does not count: the frame code clears it. By the bounds, at frame 367 Mario is still 112/256 px (0.44 px) short of the range. So no entry before 368.
- Status: the bounds, the entry rule against the collision routine on every state near the pipe's top, and joining them are Lean theorems about frames that follow the rule. Assumed: real frames follow the rule and the bounds (the routine is checked alone). The entry at 368 itself is the TAS on the emulator.

### 2, 4. Pipes and area changes: fixed lengths (emulator check)

```
control in the bonus room  = pipe entry frame + 91
control above ground       = side pipe entry frame + 282
```

They depend on no input, no position or speed on the pipe, and not on the 21-frame grid (each routine
ignores or overrides the input; the routines that wait on the 21-frame grid are skipped in these two
changes). Inserting idle frames delays them by exactly that many frames; pausing only makes them longer.

Status of part 2: [The change into the bonus room](../Theorems/PipeTransition.md) is a Lean theorem for the entry states it lists.
From one entry of a real run, every input except Start and Select on every frame gives control exactly on frame 91, under the
hypothesis `Merge` (states equal except for the bytes echoing the buttons behave the same). With no input and no hypothesis, the
same holds for the other pixels of the window, other speeds, a big Mario, and 21 consecutive entry frames from real runs. That every
entry state of every run behaves the same is not proved. A Start press pauses the game, except on some frames of the change, where it
is ignored (read from the code and tried on the emulator). Part 4 (+282) stays an emulator check.

### 3. The bonus room (459 → 570): not before 570

What entering takes (from the code):

- The side pipe is entered on the floor at the pipe's mouth, on the frame Mario lands there at the
  earliest, facing right ([Entering the side pipe](../Theorems/SidePipe.md)). In the air the pipe stops him.
- To get to that floor he passes the right end of the brick block from above. Let `t` be the first frame he
  is past the end. How long the fall takes depends on how he left the block
  ([The height of a jump](../Theorems/Jump.md)):

  | he left the block by | the floor comes |
  |---|---|
  | a jump at 1.5625 px/frame or more | at least 12 frames after `t` |
  | a slower jump | after at least 32 frames in the air at 1.5 px/frame or less: at 569 he is 25 px short of the mouth |
  | stepping off | at least 16 frames after `t` |

  (A fast jump falls exactly 4 px per frame; a slower one falls about 4.2 px per frame, which is why it needs its own line.)
  The TAS is past the end at 558 and enters at 570. So entering at 569 needs Mario past the end at 557, which is
  592/256 px (2.31 px) ahead of the TAS.

The bound at frame 557, over all inputs:

1. The fall from the ceiling does not depend on the input, so he lands on the floor at 493. The first
   jump is at 494.
2. While his feet are below the top of the block, he has to stay left of its corner, or he hits it
   and his speed drops to about 0. Call `s` the last such frame before he lands on the block. The
   TAS has `s` = 504, 15/256 px left of hitting.
3. Takeoff below 1.5625 px/frame: [The air speed cap](../Theorems/AirCap.md) applies from `s`. Over all
   takeoff speeds and all ways of pressing A ([The height of a jump](../Theorems/Jump.md)), the earliest pairs (`s`, landing on the block) are
   (504, 511), which is the TAS, and (505, 510); the others land later. The theorem gives at most
   121.75 px from `s` to 557. So at 557 Mario is at most 527/256 px ahead of the TAS: 65/256 px
   (0.25 px) short.
4. Takeoff at 1.5625 px/frame or more: he rises faster, but `s` is still at least 8 frames after the takeoff.
   [A fast takeoff](../Theorems/FastTakeoff.md) follows the horizontal frame `hstep` from 459 with every input. Moving right, no
   takeoff by 500 stays left of the corner for the 8 frames. Moving left, takeoffs by 500 exist in the model, but he is so far back
   that at 557 he is short of the goal whatever he does next. A takeoff after 500 is too late even at top speed from the corner.
5. A hit at the corner on frame `s` leaves a speed of about 0, and Mario ends at least 8 px short. A hit
   on the floor just before a jump (the jump still counts as fast, because the stored absolute speed is
   not cleared) ends at least 3 px short.

Status: step 3's bound, step 4, the jump table and the entry rule are Lean theorems; the arithmetic of the fall is a Lean lemma
too, but joining all of these into one statement is not done in Lean. The room's left wall is not in the model of step 4. `hstep` agrees with the TAS on every frame from 460 to 557. For a big Mario the checks at
the corner are at the same heights, so the bound is the same.

### 5a. Accelerating above ground (852 → 892): the pole is not reached early (emulator check)

- From the TAS's state at 852, every input for 40 frames on real frames (equal states merged, states
  that cannot catch up any more dropped by the potential bound). At frame 892 Mario can be at most
  144/256 px ahead of the TAS.
- After 892, at most 2.5 px per frame by the top speed bound. The TAS is at that bound too, except for
  a 16/256 px loss at frame 980. So at frame 1085 Mario is at most 160/256 px ahead of the TAS.
- Reaching the range where the pole can be grabbed at frame 1085 needs 528/256 px. So not by 1085.
- Assumption: that the dropped states cannot catch up rests on the open-area potential bound.

### 5b. Grabbing the pole and entering the castle: not before 1218

How the pole works (from the code):

- The pole is touched in a 4-pixel range where Mario's right side is 3..6 px into the pole's column,
  above the height of the base block. Running in at ground level, Mario is stopped by the base block
  before that range. Call `x₀` the left end of the range.
- Touching it while rising, close to the base block's height, skips the slide: the end routine starts at
  once, and the castle entry is **the touch frame + 126**. Any other touch waits for the flag to come
  down, about 39 frames later. By 5a no touch comes before 1086, so that way enters the castle at 1251
  or later.

So a castle entry by 1217 needs this direct grab by frame `g ≤ 1091`. Why it cannot happen (from the code,
for any speed, any fall speed and any input):

1. **Only rising counts.** A falling Mario at that height either lands on top of the base block, or is
   stopped before the side check runs. Rising there comes only from a jump off the ground at frame `T`, so
   `g = T + 2` (`g = T + 1` for a jump at 1.5625 px/frame or more). With `L` the frame he lands on the ground,
   `T ≥ L + 1`, so `L ≤ 1088`.
2. **The hop gains nothing.** Beside the base block, while still below its top, moving right or stopped sets
   the speed to 0 and pushes him 1 px left; moving left does nothing. From further left he stops before
   `x₀`. So `x(g) ≤ x(L)`, and he has to land with `x(L) ≥ x₀`, already past the block's left edge. He can only
   get there from above.
3. **Getting past the edge.** Let `e` be the last frame he moves over the block (`x ≥ x₀ − 2`) before `L`, and
   `k = L − e`. The frame before, he is left of that, so before the hit `x(e) < x₀ + 0.5`.
   - Frame `e`: 1 px back, speed 0.
   - Frames between `e` and `L`: at most 1 px forward each. This takes Left, which turns the push to the
     right (the TAS's detail below).
   - Frame `L`: 1 px back, after at most 1/8 px forward (Right, as the TAS does at 1089). The push to the
     right blocks the Left button on the next frame, so he is not moving left. Only with `k ≤ 1` can he avoid
     this push.

   ```
   x(L) ≤ x(e) + k − 3 + 1/8   (k ≥ 2)
   x(L) ≤ x(e) − 1             (k ≤ 1)
   ```
4. **Too early.** `L ≤ 1088` gives `e ≤ 1088 − k`. By 5a, `x(1085) ≤ x₀ − 1.44`, and each frame before is
   2.5 px less.

   | k | e at most | x(L) at most |
   |---|---|---|
   | 0, 1 | any | `x₀ − 0.5` |
   | 2 | any | `x₀ − 0.375` |
   | 3 | 1085 | `x₀ − 1.31` |
   | 4 | 1084 | `x₀ − 2.81` |
   | more | | 1.5 px less per frame |

   All are short of `x₀`. The TAS has `e` = 1086, `k` = 3, `L` = 1089, `g` = 1092: exactly one frame later.
5. **The fast jump** ([The fast hop beside the flagpole](../Theorems/FastHop.md)). It needs the stored absolute speed still high, so no
   Left or Right from `e` to `L`, and `T = L + 1`. Then every frame pushes him back, and `x(g) < x₀ − 0.4`.

Checked on the emulator:

- From frame 1084 (not yet touching the block), the height (13 values), the horizontal position (from 1 px
  behind the TAS to 160/256 px ahead, 10 values) and the facing direction (3 values) changed, 390 cases, 8
  inputs over 8 frames: none enters the castle by 1217.
- Slower fall, slower speed, and Left alone: 135 cases at 160/256 px ahead (one family at 0), the height (15
  values), speed 2.5 or 1.5 px/frame, fall speed 4, 2 or 0 px/frame, every left/right, A and B input up to frame
  1091: no direct grab.
- The formula is close to exact. With Mario 4 px lower than the TAS at 1084 and every input, moving him forward
  by 544/256 px gives a direct grab at 1091; by 540/256 px, none. The formula says it needs at least 496/256 px (the
  Left frame and the hop cost the other 48/256 px), and 5a allows at most 160/256 px.

A detail of the TAS: pressing Left+Right next to the base block counts as Left (the right side is
blocked), so the moving direction becomes left. The push from the block then goes right, and Mario stays
in the range.

Status: the position bounds of steps 2 to 4 are Lean theorems about frames that follow the collision rules
([Grabbing the pole from below](../Theorems/PoleGrab.md)), and the rules are checked against the game's collision routine
on every state near the block. The frames of step 1 are a Lean theorem on the movement routine
([The height of a jump](../Theorems/Jump.md)). Step 5 is a Lean theorem on frames that follow the movement routine. The bound at 1085 comes from
5a (emulator). It assumes no enemy is near the pole.

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
  ⟸ side pipe entry ≥ 570 (+282)                 (segment 3)
  ⟸ control in the bonus room ≥ 459 (+91)
  ⟸ pipe entry ≥ 368                             (segment 1)
```

It is also assumed that arriving later at any step never helps later on. Each step now has a reason; what
remains is to move the parts that are not Lean theorems into Lean.

## Reproduce

With the TAS movie (fm2), in `git/`:

```
.lake/build/bin/smbrta tas-trace FM2                    # the route, against the bound
.lake/build/bin/smbrta tas-seg FM2 A B                  # position, speed, height for frames A..B
.lake/build/bin/smbrta tas-insert FM2 AT K              # K idle frames inserted at AT
.lake/build/bin/smbrta seg-search FM2 852 40            # the 5a search (over 10 minutes)
.lake/build/bin/smbrta end-poke FM2 1084 Y DX FD 8      # one 5b case (Y height, DX shift, FD facing)
.lake/build/bin/smbrta pole-check                      # the collision routine near the pole against the rules
.lake/build/bin/smbrta jump-table                      # every jump from the ground and from a block
.lake/build/bin/smbrta pipe-check                      # the routine on the pipe's top against the rule
.lake/build/bin/smbrta pipe-change-check               # the change into the bonus room
.lake/build/bin/smbrta takeoff-check                   # the fast takeoff search in the bonus room
.lake/build/bin/smbrta side-check                      # the routine at the side pipe's mouth against the rule
.lake/build/bin/smbrta abs-check                       # what updates the stored speed
.lake/build/bin/smbrta flag-poke FM2 1084 Y DX V VY FD 7 GY   # as above with speed and fall speed, all inputs (GY: grab height)
.lake/build/bin/smbrta room-bound FM2 459 493 557 CX CY WLO WHI TX
    # bonus room: the jump table and the bound at 557. CX, CY: the corner (he hits it at x ≥ CX
    # while y ≥ CY); WLO..WHI: the heights where he lands on the block when falling; TX: the x past
    # the block's right end. All are read from the room's blocks and the collision code.
```
