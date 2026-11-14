[← Back](README.md) | [English](g-2-1-FlagRule.md) | [Japanese](g-2-1-FlagRule-ja.md)

# The star flag's rule after the castle entry

**Claim.** This is a partial result. Let the machine on the first frame after the castle entry meet one condition `Good`, with task 2 and the flag at the height it is made at. Then, with any inputs, the counters of the real machines follow the rule of one frame on every frame up to the level change, and the level changes on a frame that begins with task 5. A frame that ends paused keeps the counters: it is a `lag` frame. Any other frame follows `FlagRun`. This makes the fields `step`, `task_E`, `y_E` and `task_L` of `Flag` in [From the castle to 1-2](g-1-CastleToLevel.md) theorems. The condition `Good` stays, as a hypothesis on one state at the castle entry. How the check treats the pause is on [The pause after the castle entry](g-2-5-FlagPause.md).

`seq(n)` is the machine when frame `n` begins and `inp(n)` its input (`Changes` of [The whole of 1-1](0-1-Route.md)), so `seq(n + 1) = frame(seq(n), inp(n))`. `m[b]` is the byte `b` of `m`. `E` is the frame of the castle entry. `r` is the reference machine: the castle entry of the own route (`CastleWalk`) with no delay and the real timer. `lim` and `w₀` are those of [From the castle to 1-2](g-1-CastleToLevel.md).

## Statement

```
x(m)       = (task, t, y, w, ph)    the counters of m (flagOf); the flag is in the first enemy slot
paused(m)  = (m[GamePauseStatus] &&& 1 ≠ 0)

After(seq, inp, E, T, c, L) :
  Good(seq(E + 1))
  task(seq(E + 1)) = 2,   y(seq(E + 1)) = y(r)
  t(seq(E + 1)) = T,      ph(seq(E + 1)) = c
  E < L
  level(seq(L + 1))                         the level number or the world number is not 0
```

The theorems:

```
flagCheck(C, d) = true  →  Checked(C, d)                         checked_of_check

Checked(C, d),  Good(m),  any input i  →
  frame(m, i).frame = m.frame + 1
  ¬ level(m),  ¬ level(frame(m, i))
  paused(frame(m, i))    →  x(frame(m, i)) = x(m)  ∧  Good(frame(m, i))
  ¬ paused(frame(m, i))  →  FlagRun(lim, w₀, x(m), x(frame(m, i)))  ∧  (task(frame(m, i)) = 5  ∨  Good(frame(m, i)))
                                                                  frame_step

Checked(C, d),  ∀ n, seq(n + 1) = frame(seq(n), inp(n)),  After(seq, inp, E, T, c, L)  →
  Flag(lim, w₀, E, T, c, L)                                        flagOf_after
```

`flagCheck` is the check on the ROM. The private proof shows it with `native_decide` (`flag_check`). `C` is the context of the check (`r`, the known bytes, the names), `d` the abstract states computed from it.

In the `Flag` that `flagOf_after` builds, `x(n)` is the counters of `seq(n)` up to the first frame of task 5, and the counters of that frame after it. The `lag` frames are:

```
lag(n)  =  E < n  ∧  (task(x(n)) = 5  ∨  paused(seq(n + 1)))
```

The frames from the first frame of task 5 on keep the held counters. A frame that ends paused keeps the counters by `frame_step`. A `lag` frame only delays the level change (`Flag.hL` holds for any `lag`).

## The condition `Good`

`Good(m)` says:

* `m` is in one of 240 abstract states `B₀`. The pad is not known.
* `ph < 21` and `task ∈ {2, 3, 4}`.
* The timer's three digits are those of some `t ≤ tmax`. `tmax` is the timer's value at the start of 1-1, plus 1.
* Mario's numbers `(v, F, f, A, C, s)` are in the set `Q`: `v` is the speed, `F` and `f` the fractions of two forces, `A` the absolute speed, `C` the collision bits, `s` the timer of the side collision. `Q` has the 6714 tuples reached frame by frame from the numbers at a bump into the wall. At a bump `v = 0`, `s` has its value at a bump, `F` is a multiple of 4 and `f` a multiple of 16.
* `RunningSpeed` and `Player_MovingDir` are those of `r`.
* `task ≠ 4  →  lim − 1 ≤ y ≤ y(r)` and `task = 4  →  w ≤ w₀`.

`B₀` is computed from the ROM and `r`. Its states know:

* The frame has ended in the idle loop: the program counter, the stack, the PPU flags, a range of dots.
* Most of 345 bytes have the values of `r`: the bytes of the names in `knownNames` and the whole first block buffer. These are the modes, the level and its numbers, Mario's state, size and position, the control of the game timer, part of the sound, the sprite offsets, the control of the floating numbers, the cannon bytes, and others.
* The bytes of the pause are known only in part. `GamePauseStatus` is 0, 1, 0x80 or 0x81. `PauseModeFlag` and `PauseSoundQueue` are at most 3. `GamePauseTimer` may have any value.
* The height of the flagpole's floating number `FlagpoleFNum_Y_Pos` may have any value. The number of the flagpole's score `FlagpoleScore` is below 8. Both are set by the height of the touch. Up to the round before they had to be those of `r` ([A wider condition at the castle entry](g-2-2-1-FlagWide.md)).
* The star flag is in the first enemy slot. The other four slots are empty, or all hold fireworks.
* `EventMusicBuffer` is that of `r` or 0. Of the left and right x of the screen and of `ScrollThirtyTwo` only the high bits are known.

Any other byte may have any value: the score, the coins, the random bytes, the frame counter, `HorizontalScroll`, the places in the music (Square 1 is split by its value), the fireworks' states, the counters, the sound of the pause.

## How the check works

A frame is cut at 13 named places: `SoundEngine`, `MusicHandler`, `ReadJoypads`, `DecTimers`, `NoDecTimers`, `PlayerEndLevel`, `PlayerSubs`, `GetXOffscreenBits`, `GetPlayerOffscreenBits`, `RunStarFlagObj`, `FloateyNumbersRoutine`, `FlagpoleRoutine`, `RunGameTimer`, and then the frame's end. A stage ends when the machine first comes to one of its places (`Next`, `Arr`). Two stages have a second place, for the pause: the sound may end at `SkipSoundSubroutines`, and the stage after the pad may end at `SkipMainOper`. Two more stages follow these places (stages 14 and 15). See [The pause after the castle entry](g-2-5-FlagPause.md).

On each stage three kinds of walks of the [abstract machine](b-2-3-TaintRun.md) are checked (`Checked`):

* cover: from the states of the stage the machine comes to the next place in a state of the stage that begins there (`CoverP`, `nextIdx`);
* facts: from one value, one of some values at the next place (`FactP`). These are the phase, the interval timer, the side timer, Mario's move (4844 moves), the wall, the timer's digits, the flag's height, the fireworks counter and the last wait;
* keeps: under a condition the byte `b` does not change (`KeepP`). For values of at least 2 this is a walk with `b` as the counter (`Env.rkI`). For 0 and 1 it is a walk with the value known.

`frame_step` joins them in order: the counters change by the rule, Mario's numbers come back into `Q`, and the frame ends in `B₀`.

## Measurements

One frame from the state after the entry, with the counters not known and the other bytes known:

```
task  steps  failures
2     5173   0
3     3669   0
4     3942   0
5     2836   0
```

With the music and fireworks bytes not known as well: 84 failures within 400000 steps. The first is the loop that reads Square 1's data: with its place not known, data 0 does not end the loop. So Square 1's place is split by its value at that point (`splitAt`).

The check takes about 34 s natively (`flag-rule-check`, before the change for the pause): 6 s for the states, 16 s for the stage of the other slots, 3 s for the music stage. After the change it took 56 s and 61 s in two runs while five other workers built on the machine (load average 15 to 20 on 28 cores). In these runs the stage of the other slots, which did not change, took 1.6 and 1.9 times as long as before; divided by these factors the check takes 33 to 35 s. The two stages of the pause take a few ms. The private proof `flag_check` built in 95 s with the other workers (47 s before). Most of the time is in the walks of the keeps: 15 bytes × 3 walks × the states of the table (2562 on the stage of the other slots). The abstract machine follows only one byte as a counter in a walk.

## Real frames

`flag-rule-check`: the condition at `E + 1`, `Good` on each frame up to the first frame of task 5, and the rule on each of these frames: a frame that ends paused keeps the counters, any other frame follows `FlagRun`.

```
run                                    E     T    L      not Good  against the rule  Start  paused
TAS                                    1218  370  1748   0         0                 0      0
TAS, 96 idle frames first              1314  366  2000   0         0                 0      0
TAS, 168 idle frames first             1386  363  1958   0         0                 0      0
TAS, 216 idle frames first             1434  361  1937   0         0                 0      0
TAS, touch 1 frame late                1219  369  1748   0         0                 0      0
TAS, random inputs with no Start (2)   1218  370  1748   0         0                 0      0
TAS, every button but Start after E    1218  370  1748   0         0                 0      0
TAS, pause at E + 60 for 80 frames     1218  370  1828   0         0                 2      80
TAS, pause at E + 300 for 80 frames    1218  370  1828   0         0                 2      80
TAS, pause at E + 1 for 99 frames      1218  370  1847   0         0                 2      99
TAS, pause in task 4                   1218  370  1808   0         0                 2      60
TAS, pause on the last frames          1218  370  1803   0         0                 2      55
TAS, Start every 44 frames             1218  370  2276   0         0                 24     528
TAS, Start held from E + 1 (59)        1218  370  -      0         0                 59     3999
TAS, Start held at E + 30 (50)         1218  370  -      0         0                 50     3970
TAS, Start every 47 frames             1218  370  -      0         0                 85     1979
TAS, random inputs with Start (2)      1218  370  -      0         0                 2000   2014
reference r, no input                  E     360  E+513  0         0                 0      0
reference r, Start every 50            E     360  E+2749 0         0                 54     1350
reference r, timer set to 0 to 120     E     t    E+265  0         0                 0      0
reference r, timer set to 200          E     200  E+345  0         0                 0      0
reference r, timer set to 400          E     400  E+555  0         0                 0      0
```

In the three runs with idle frames real fireworks go up. The timer was set at the entry to 0, 1, 3, 6, 60, 100 and 120; with a small timer the level does not change before the music ends. In every run that changes the level, `L` is the first frame of task 5. A run with `-` stays paused to the end of the 4000 frames that were run: a held Start pauses the game, and the game stays paused until Start is pressed again after a release.

## What is not proved

* `Good(seq(E + 1))`, task 2 and the flag's height are hypotheses. They are not proved from the frames before the castle entry. They were checked on the runs above and on runs that touch the pole at other heights ([A wider condition at the castle entry](g-2-2-1-FlagWide.md)). The rows from the touch's end were only measured ([Rows from the touch's end to the castle](g-2-2-2-TouchRows.md)).
* Nothing outside `Good` is covered: big Mario, the flag in another slot, slots with other objects, Mario's numbers outside `Q`, a timer above `tmax`, bytes that differ from `B₀`. A run where Mario's `x` after the castle entry is 1 more than in `r` is outside too.
* `t(seq(E + 1)) = T` and `ph(seq(E + 1)) = c` stay fields that join `Frames`.
* `GMerge` (1-1-g-2-3) is not treated here.

## Files

Lean: `Theorems/FlagRule.lean` (`Checked`, `Good`, `frame_step`, `After`, `flagOf_after`), `Run.flag` in `Theorems/Route.lean`. Private: `flag_check`, `flag_checked`.

```
.lake/build/bin/smbrta flag-rule-check FM2         # the check on the ROM, then the condition and the rule on real frames
.lake/build/bin/smbrta flag-rule-check FM2 real    # real frames only
```
