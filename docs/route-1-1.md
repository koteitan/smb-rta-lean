[← Back](../1-1/README.md) | [English](route-1-1.md) | [Japanese](route-1-1-ja.md)

# The 1-1 route: toward a lower bound on the frame 1-2 starts

**Goal.** With frame 0 the first controllable frame of 1-1, show that 1-2 does not start (the level
number does not change) before frame 1748. 1748 is the value of HappyLee's TAS.

This page records work in progress. For each part it says whether the result is a **Lean
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

## Results by part

### a. Running into the pipe (0 → 368): earliest

- Up to frame 32 the distance is at most the TAS's, by [The opening](../1-1/a-3-Opening.md); after
  that at most 2.5 px per frame, by [Top speed bound](../0-0/0-1-TopSpeed.md). The TAS runs exactly
  at both bounds (exactly at the bound every frame from 32 to 362).
- The pipe can be entered only with both feet on the pipe's top, with Down held, on a frame that runs the landing code: falling or standing on the top ([Entering the vertical pipe](../1-1/a-4-PipeEntry.md)). Down with Left or Right on the ground does not count: the frame code clears it. By the bounds, at frame 367 Mario is still 112/256 px (0.44 px) short of the range. So no entry before 368.
- Status: the bounds, the entry rule against the collision routine on every state near the pipe's top, and joining them are Lean theorems about frames that follow the rule. Assumed: real frames follow the rule and the bounds (the routine is checked alone). The entry at 368 itself is the TAS on the emulator.

### b, d. Pipes and area changes: lengths

```
control in the bonus room  = pipe entry frame + 91
control above ground       = side pipe entry frame + 282
```

They depend on no input, no position or speed on the pipe (for part d: at no pixel an entry can reach; see below), and not on the 21-frame grid (each routine
ignores or overrides the input; the routines that wait on the 21-frame grid are skipped in these two
changes). Inserting idle frames delays them by exactly that many frames; pausing only makes them longer.

Status of part b, last frames: [A run with unknown bytes](../1-1/b-2-3-TaintRun.md) proves the last 41 frames for every value of the bytes that differ from run to run, under conditions at frame 50. From frame 48 the same claim is false: some music states stop the game. The conditions are not proved for every run.

Status of part b: [The change into the bonus room](../1-1/b-1-PipeTransition.md) is a Lean theorem for the entry states it lists.
From one entry of a real run, every input except Start and Select on every frame gives control exactly on frame 91, under the
hypothesis `Merge` (states equal except for the bytes echoing the buttons behave the same). With no input and no hypothesis, the
same holds for the other pixels of the window, other speeds, a big Mario, and 21 consecutive entry frames from real runs.

What decides the length is on [What decides the change into the bonus room](../1-1/b-2-1-PipeTransitionAll.md). The change is 48 frames of the pipe's timer and 43
more. For the 43 frames, a Lean theorem covers every value of every byte outside a list R: enemies, objects, Mario's position and speed and the screen's position
cannot change them. The values of R are covered only for the states that were run. The 48 frames are covered only for 77 listed entry states. Every entry state is a
theorem only under the assumptions (H1) to (H4) of that page.

The +91 has exceptions, all with bytes overwritten. `HalfwayPage` or `AreaPointer` changed give 75 frames; from the code these values do not occur when Mario can enter
this pipe (not proved in Lean). Six objects close together make frames run over: 92 to 96 frames. The game timer at 000 gives no control, he dies on arrival. No
exception was found that gives an earlier control in a run.

A Start press pauses the game, except on some frames of the change, where it
is ignored (read from the code and tried on the emulator).

Status of part d: [The change out of the side pipe](../1-1/d-1-SideTransition.md) is a Lean theorem for the entry states it lists. From one entry of a real run, every
input except Start and Select on every frame gives control exactly on frame 282, under the hypothesis `GMerge`. With no input and no hypothesis, the same holds for the
other pixels of the mouth (written on the frame before the entry, so the entry frame really runs), other fractions and speeds, a big Mario, real entries at `x₀ + 1` and
`x₀ + 2`, and real entries on 21 consecutive frames. There is one exception: an entry frame ending with `x` a multiple of 16 takes 378 frames, because the timer is not
set. That pixel cannot be reached by walking or falling in (read from the code, not in Lean), and the change is never shorter there, so the bound at 852 stands. A shorter timer exists in the code for a screen not on the first page. Run on overwritten states, it gives 174 frames, a Lean theorem on [What decides the change out of the side pipe](../1-1/d-2-1-SideTransitionAll.md). In the room the screen is on the first page and the scroll lock is on, measured on all frames of a real run, so from the code a run does not reach it. This is not in Lean, and the bound at 852 depends on it.

What decides the length is on that page. The change is 160 frames of the pipe's timer and 122 more. For the 122 frames, a Lean theorem covers every value of every byte outside a list R: enemies, objects and Mario's position and speed cannot change them. The values of R are covered only for the states that were run. The 160 frames are covered only for 20 listed entry states. Every entry state is a theorem only under the assumptions (H1) to (H4) of that page. `HalfwayPage` and `WarpZoneControl` do not change this length, unlike the vertical pipe's. Six objects close together give up to 284 frames. The game timer at 000 gives no control. That every entry state of every run behaves the same is not proved.

### c. The bonus room (459 → 570): not before 570

What entering takes (from the code):

- The side pipe is entered on the floor at the pipe's mouth, on the frame Mario lands there at the
  earliest, facing right ([Entering the side pipe](../1-1/c-4-SidePipe.md)). In the air the pipe stops him.
- To get to that floor he passes the right end of the brick block from above. Let `t` be the first frame he
  is past the end. How long the fall takes depends on how he left the block
  ([The height of a jump](../1-1/c-2-Jump.md)):

  | he left the block by | the floor comes |
  |---|---|
  | a jump at 1.5625 px/frame or more | at least 12 frames after `t` |
  | a slower jump | at least 12 frames from the frame before `t`, in the air at 1.5 px/frame or less: at most 18 px from 557 to 569, and the mouth is 22 px past the end |
  | stepping off | at least 16 frames after `t` |

  (A fast jump falls exactly 4 px per frame; a slower one falls about 4.2 px per frame, which is why it needs its own line.)
  The TAS is past the end at 558 and enters at 570. So entering at 569 needs Mario past the end at 557, which is
  592/256 px (2.31 px) ahead of the TAS.

The bound at frame 557, over all inputs:

1. The fall from the ceiling does not depend on the input, so he lands on the floor at 493. The first
   jump is at 494.
2. While his feet are below the block's top and he moves right or stands, at or past the corner, a hit leaves a speed of about 0. Moving left he is not stopped. Let `s` be the last such frame before landing on the block. The TAS has `s` = 504, 15/256 px from a hit.
3. Takeoff below 1.5625 px/frame: [The air speed cap](../1-1/c-1-AirCap.md) applies from `s`. Over all
   takeoff speeds and all ways of pressing A ([The height of a jump](../1-1/c-2-Jump.md)), the earliest pairs (`s`, landing on the block) are
   (504, 511), which is the TAS, and (505, 510); the others land later. The theorem gives at most
   121.75 px from `s` to 557. So at 557 Mario is at most 527/256 px ahead of the TAS: 65/256 px
   (0.25 px) short.
4. Takeoff at 1.5625 px/frame or more: he rises faster, but `s` is still at least 8 frames after the takeoff.
   [A fast takeoff](../1-1/c-3-FastTakeoff.md) follows the horizontal frame `hstep` from 459 with every input. Moving right, no
   takeoff by 500 stays left of the corner for the 8 frames. Moving left, takeoffs by 500 exist in the model, but he is so far back
   that at 557 he is short of the goal whatever he does next. A takeoff after 500 is too late even at top speed from the corner.
5. A frame from 496 on that stops him with a speed of about 0 leaves him short of the goal at 557 whatever comes after, by at least 225/256 px by the potential bound from there. This covers a hit at the corner on the floor or in the air, a fast jump on the stale speed after a hit, the foot check (a jump that peaks just below the block's top, with a foot over the block, is stopped and pushed back 1 px per frame), and a jump from the block's side (falling with a foot over the block and the feet less than 5 px into a row, he lands on that row, the side check stops him in the same frame, and the next frame he can jump from there). Before 496 he is left of the corner.

A run that lands on the left wall, jumps, and reaches the block without touching the floor is in that theorem: after a wall hit he reaches the block's end after C + 98 with no look at the jump. A real one had E = C + 134.

Status: [Joining the bonus room](../1-1/c-5-RoomJoin.md) is a Lean theorem: from a structure `RoomRun` of a run's frames and the checks of the theorems above, `E ≥ C + 111`, relative to first control. Its fields are assumptions: real frames follow `hstep` or stop, and follow `vstep`. They hold on the TAS and on 1400 real runs with random inputs, none of them near the limit. The left wall of the room is not in the model of step 4; the theorem assumes no wall touched for a fast jump by 500. `hstep` agrees with the TAS on every frame from 460 to 558. A big Mario is not in the theorem.

### e. Above ground (852 → 1085): the pole is not reached early

- At control above ground Mario is stopped, in the same horizontal state as at the 1-1 start ([Above ground](../1-1/e-1-SurfaceRun.md)).
- In a model with ground or air chosen freely on every frame, over all inputs, at frame 892 he is at most 464/256 px ahead of the TAS. After 892, at most 2.5 px per frame by the top speed bound. The TAS is at that bound too, except for a 16/256 px loss at frame 980. So at frame 1085 he is at most 480/256 px ahead of the TAS.
- Reaching the range where the pole can be grabbed at frame 1085 needs 528/256 px. So not by 1085. The 32/256 px of [Grabbing the pole from below](../1-1/f-1-PoleGrab.md) fits, with 16/256 px to spare.
- A first hit from frame 9 on stays under the same bound (any frames of the top speed bound after it). On frames 1 to 8 the collision routine finds no side contact around him.
- Status: Lean theorems about runs of `hstep` and of the top speed bound's frames. Assumed: real frames follow them (`hstep` agrees with the TAS on every frame from 853 to 1085); he stays in the checked box on frames 1 to 8; the start state is read from one real run.
- The model has no map, so the bound is not tight for real runs. The emulator search `seg-search` (not a theorem, not run again) gave at most 144/256 px at 892 and so 160/256 px at 1085.

### f. Grabbing the pole and entering the castle: not before 1218

How the pole works (from the code):

- The pole is touched in a 4-pixel range where Mario's right side is 3..6 px into the pole's column,
  above the height of the base block. Running in at ground level, Mario is stopped by the base block
  before that range. Call `x₀` the left end of the range.
- Touching it while rising, close to the base block's height, in the left 2 px of the range, skips the slide: the end routine starts at once.
  A slow jump that moved left on the frame before enters the castle at **the touch frame + 126** or + 127 ([From touching the pole to the castle](../1-1/f-4-CastleWalk.md)). Not moving left, with a fraction of 176/256 px or more, + 125.
  With a fast jump his feet are inside the block on the next frame and the block stops Right, so the castle entry is the touch + 1 or + 2 (emulator, position overwritten). So the bound needs that a fast jump never grabs, on any frame.
  Any other touch waits for the flag to come down. The least measured is the touch + 153: a real run touches at 1086 and enters at 1239. By part e no touch comes before 1086. The theorem needs only + 132.

So to enter the castle by 1217 he needs a fast grab on some frame, or a slow grab by 1092, on 1092 exactly with the + 125 above. Why the slow case does not happen (from the code, for every speed, fall speed and input):

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
4. **Too early.** `L ≤ 1088` gives `e ≤ 1088 − k`. By part e, `x(1085) ≤ x₀ − 0.1875`, and each frame before is
   2.5 px less.

   | k | e at most | x(L) at most |
   |---|---|---|
   | 0, 1 | any | `x₀ − 0.5` |
   | 2 | any | `x₀ − 0.375` |
   | 3 | 1085 | `x₀ − 0.0625` |
   | 4 | 1084 | `x₀ − 1.5625` |
   | more | | 1.5 px less per frame |

   All are short of `x₀`. The TAS has `e` = 1086, `k` = 3, `L` = 1089, `g` = 1092: exactly one frame later.
5. **The fast jump** ([The fast hop beside the flagpole](../1-1/f-3-FastHop.md)). On the frame after the landing the stored speed must stay high, so no Left or Right from `e` to `L`, and every frame pushes him back. Later, it needs a ground frame at 1.5625 px/frame or more just before, so he was left of the block's side. Either way `x(g) < x₀` on every frame.

Checked on the emulator:

- From frame 1084 (not yet touching the block), the height (13 values), the horizontal position (from 1 px
  behind the TAS to 160/256 px ahead, 10 values) and the facing direction (3 values) changed, 390 cases, 8
  inputs over 8 frames: none enters the castle by 1217.
- Slower fall, slower speed, and Left alone: 135 cases at 160/256 px ahead (one family at 0), the height (15
  values), speed 2.5 or 1.5 px/frame, fall speed 4, 2 or 0 px/frame, every left/right, A and B input up to frame
  1091: no direct grab.
- The formula is close to exact. With Mario 4 px lower than the TAS at 1084 and every input, moving him forward
  by 544/256 px gives a direct grab at 1091; by 540/256 px, none. The formula says it needs at least 496/256 px (the
  Left frame and the hop cost the other 48/256 px), and part e allows at most 480/256 px. The two emulator checks above ran up to 160/256 px ahead, which is what the
  emulator search of part e gives; the Lean bound does not rely on them.

A detail of the TAS: pressing Left+Right next to the base block counts as Left (the right side is
blocked), so the moving direction becomes left. The push from the block then goes right, and Mario stays
in the range.

Status: joining parts e and f is a Lean theorem ([From control to the castle](../1-1/f-5-PoleJoin.md)). The link to real frames is all named assumptions (`Run`), checked as a program on the TAS and other real runs. The fall through the block's rows, the lengths after the touch and the castle flag are measured, not proved. It assumes no enemy near the pole.

A touch on 1093 needs its own case. The touch + 125 there keeps the castle at 1218 with one more tick of the timer, so 1-2 would start at 1727. The theorem shows that on 1092 and 1093 he moved left on the frame before with a fraction below 176/256 px, so + 126 or more. From the TAS's state at 1085 with the position moved by 16/256 to 160/256 px, over every input of A, B, Left and Right, no such touch gave + 125.

### g. From the castle to 1-2: not before 1748

```
L = E + T + D + 107 + ((c − T − D) mod 21)
  E: castle entry frame   T: the game timer (frozen since the touch)
  D: 33; by the last digit of T: 1 → 34, 3 → 98, 6 → 194
  c: the interval timer's phase at E
```

The last wait ends on a point of a 21-frame grid. The level changes at the first grid point not before `E + T + D + 107`. It also waits for the fanfare; with a small `T` the level changes later than the formula, off the grid, so the formula is a lower bound. On the route checked it is an equality for `T ≥ 125`.

The timer loses 1 per 24 frames of play. During an area change the sub-counter falls by 1 per frame and stops at 0, and the digits stay, so `p` frames of play in an area take `⌈p/24⌉`. What decides is not `E` alone but `E + T`. `368 + 91 + 111 + 282 + 240 + 126 = 1218` with `T = 370`, so `E + T = 1588`. One more frame above ground means one more tick, so the same sum. When a part of the run gets longer, `E + T` does not fall.

The grid is not a function of the frame number alone. Each area change has one frame on which the timers do not run. After the two changes the phase is `(3 − f) mod 21`. A later frame with no timers shifts it by one; that frame also delays the run by one, so the conclusion moves with it. A pause is 45 frames or more of this kind. The game runs with the timers stopped only for a power-up, a hit or a death; a small Mario first needs a power-up, which stops the game for 59 frames.

The TAS's sum is 1728 and the grid points are 1727 and 1748, so it waits 20 more frames. A sum 1 smaller would give 1727.

Status: [From the castle to 1-2](../1-1/g-1-CastleToLevel.md) shows `L ≥ 1748` in Lean from named assumptions on the lengths, the timer, the grid and the level change. The formula, the timer's rule and the grid are checked on real frames on listed states. That every run follows them is not proved.

## Summary

```
1-2 starts ≥ 1748                                    (the whole theorem, assuming every field of Run)
  ⟸ E + T ≥ 1588, D ≥ 33, the grid                  (from the castle to 1-2)
  ⟸ the three cases of the touch and the castle      (from control to the castle; parts e, f)
  ⟸ control above ground at the side pipe's +282     (part d; assumed)
  ⟸ side pipe at control in the room +111            (joining the bonus room; part c)
  ⟸ control in the room at the pipe's +91            (part b; assumed)
  ⟸ pipe entry ≥ 368                                 (part a)
```

This is one Lean theorem: [The whole of 1-1](../1-1/0-1-Route.md). That arriving later does not help is a theorem for the timer and the grid. What remains is to prove the theorem's assumptions on real frames.

## Reproduce

With the TAS movie (fm2), in `git/`:

```
.lake/build/bin/smbrta route-check FM2                  # the whole route's numbers: lengths, timer, grid, start of 1-2
.lake/build/bin/smbrta touch-search-at FM2 1085 DELTA 8 # the position moved by DELTA/256 px: touch to castle per frame
.lake/build/bin/smbrta tas-trace FM2                    # the route, against the bound
.lake/build/bin/smbrta tas-seg FM2 A B                  # position, speed, height for frames A..B
.lake/build/bin/smbrta tas-insert FM2 AT K              # K idle frames inserted at AT
.lake/build/bin/smbrta seg-search FM2 852 40            # the part e search (over 10 minutes)
.lake/build/bin/smbrta end-poke FM2 1084 Y DX FD 8      # one part f case (Y height, DX shift, FD facing)
.lake/build/bin/smbrta pole-check                      # the collision routine near the pole against the rules
.lake/build/bin/smbrta jump-table                      # every jump from the ground and from a block
.lake/build/bin/smbrta pipe-check                      # the routine on the pipe's top against the rule
.lake/build/bin/smbrta pipe-change-check               # the change into the bonus room
.lake/build/bin/smbrta takeoff-check                   # the fast takeoff search in the bonus room
.lake/build/bin/smbrta side-check                      # the routine at the side pipe's mouth against the rule
.lake/build/bin/smbrta abs-check                       # what updates the stored speed
.lake/build/bin/smbrta castle-check                    # from the frame of the touch to the castle
.lake/build/bin/smbrta pipe-all-check                  # what decides the change into the bonus room
.lake/build/bin/smbrta side-change-check               # the change out of the side pipe
.lake/build/bin/smbrta surface-check                   # above ground: the bound, and the search with hits
.lake/build/bin/smbrta flag-poke FM2 1084 Y DX V VY FD 7 GY   # as above with speed and fall speed, all inputs (GY: grab height)
.lake/build/bin/smbrta room-bound FM2 459 493 557 CX CY WLO WHI TX
    # bonus room: the jump table and the bound at 557. CX, CY: the corner (he hits it at x ≥ CX
    # while y ≥ CY); WLO..WHI: the heights where he lands on the block when falling; TX: the x past
    # the block's right end. All are read from the room's blocks and the collision code.
```
