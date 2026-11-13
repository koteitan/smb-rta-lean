[← Back](README.md) | [English](g-2-5-FlagPause.md) | [Japanese](g-2-5-FlagPause-ja.md)

# The pause after the castle entry

**Claim.** After the castle entry the star flag's rule holds with any inputs, Start included. A frame that ends paused keeps the counters, and the condition `Good` holds after it again. So the field `flag.noStart` of `Route.Run` (no Start from the castle entry to the level change) is gone. The proof is the check of the ROM of [The star flag's rule after the castle entry](g-2-1-FlagRule.md), under the same condition `Good` at the castle entry.

## What the game does

In each frame the handler of the frame runs the sound, reads the pad, and then the pause routine. In the game core the pause routine works so:

* After a press of Start the routine waits for a number of frames. In these frames Start does nothing.
* Then a press of Start (not held from the frame before) flips the bit 0 of `GamePauseStatus` and asks for the sound of the pause.
* When the bit 0 is 1, the frame skips the timers and the mode's routine. It goes to `SkipMainOper` and to the frame's end. The counters of the star flag are not touched.

The sound of the pause takes over the sound engine. While `PauseModeFlag` is not 0 the engine plays only the sound of the pause and skips the sound effects and the music: it goes to `SkipSoundSubroutines` without `MusicHandler`. `PauseModeFlag` stays not 0 for a while after the game goes on again.

## Statement

```
paused(m)  =  (m[GamePauseStatus] &&& 1 ≠ 0)

Good(m)  →  paused(frame(m, i))  →  x(frame(m, i)) = x(m)  ∧  Good(frame(m, i))            frame_step (any i)

lag(n)  =  E < n  ∧  (task(x(n)) = 5  ∨  paused(seq(n + 1)))                               flagOf_after
```

`x(m)` are the counters of the star flag, `Good` the condition of [The star flag's rule after the castle entry](g-2-1-FlagRule.md). A `lag` frame only delays the level change: `Flag.hL` holds for any `lag`.

## How the check treats the pause

* The pad may have any value (`AB.top`). Before, the bit of Start was known to be 0.
* `B₀` knows the bytes of the pause only in part: `GamePauseStatus` is 0, 1, 0x80 or 0x81, `PauseModeFlag` and `PauseSoundQueue` are at most 3, `GamePauseTimer` may have any value.
* `GamePauseStatus` is read in pieces by its bits 0 and 7 (`Env.splits`). A read of it splits the state into the 4 values.
* The search keeps `GamePauseStatus` apart. Without this, the search joined the paused state and the not paused state before the branch on the bit. The walk then took both branches with the bit not known, and a path went into the game core in a paused frame (34687 failures on the stage of the pad).
* Two stages have a second place to end at. The machine ends a stage at the first of its places (`Arr`, `Next` take a list of places). The stage that begins there is `nextIdx(j, pc)`.

```
0 → 1 → 2 → 3 → 4 → … → 12 → 13 → frame's end, bit 0 known 0
    1 → 14 → 3                          the sound of the pause: stage 1 ends at SkipSoundSubroutines
             3 → 15 → frame's end, bit 0 known 1    a paused frame: stage 3 ends at SkipMainOper
```

* Stage 14 goes from `SkipSoundSubroutines` to `ReadJoypads`. Stage 15 goes from `SkipMainOper` to the frame's end. On both, the 15 bytes of the rule are kept (`KeepP`, `EndKeepP`), as on the other stages.
* The end of stage 13 knows that the bit 0 is 0, the end of stage 15 that it is 1 (`EndCoverP`, `bit0_of`). So a frame is a `lag` frame exactly when it went through stage 15.

## A plan that was too slow

The plan of the round before merged the sound into one stage from `SoundEngine` to `SkipSoundSubroutines`. The check passed, but the merged stage took 55 s. Each walk of the keeps took 0.48 s: it split Square 1's place into 256 values about 21 times, once for each path of the sound effects into the music. There are 45 such walks. With the second place at `SkipSoundSubroutines` and the stage of the music kept apart, the two new stages take 3 ms and 2 ms.

## Measurements

`B₀` has 240 states, as before. Before the change the check took 34 s. After it, the check took 56 s and 61 s in two runs while five other workers built on the machine (load average 15 to 20 on 28 cores). In these runs the stage of the other slots, which did not change, took 1.6 and 1.9 times as long as before (26.6 s and 30.8 s against 16.3 s). Divided by these factors the check takes 33 to 35 s: the same as before.

## Real frames

`flag-rule-check` runs the TAS with pauses and with Start pressed often. On every frame up to the first frame of task 5 the machine is in `Good`, and every frame keeps the counters if it ends paused or follows `FlagRun` if it does not:

```
run                                    L      Start  paused  not Good  against the rule
TAS, pause at E + 60 for 80 frames     1828   2      80      0         0
TAS, pause at E + 1 for 99 frames      1847   2      99      0         0
TAS, pause in task 4                   1808   2      60      0         0
TAS, pause on the last frames          1803   2      55      0         0
TAS, Start every 44 frames             2276   24     528     0         0
TAS, Start held at E + 30 (50 frames)  -      50     3970    0         0
TAS, random inputs with Start (2)      -      2000   2014    0         0
reference r, Start every 50            E+2749 54     1350    0         0
```

The full table is on [The star flag's rule after the castle entry](g-2-1-FlagRule.md). `-`: the game stays paused to the end of the 4000 frames that were run.

## What is not proved

* `Good(seq(E + 1))`, task 2 and the flag's height at the castle entry stay hypotheses (1-1-g-2-2).
* Pauses before the castle entry are not treated here (the fields `noStart₁` and `noStart₂` of the changes, and the title).

## Files

Lean: `Theorems/FlagRule.lean` (`paused`, `bit0`, `bit0_of`, `altOf`, `cutsOf`, `nextIdx`, `toPad`, `frame_step`, `frame_next`, `flagOf_after`).

```
.lake/build/bin/smbrta flag-rule-check FM2         # the check on the ROM, then the runs with pauses
```
