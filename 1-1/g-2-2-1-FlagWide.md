[← Back](README.md) | [English](g-2-2-1-FlagWide.md) | [Japanese](g-2-2-1-FlagWide-ja.md)

# A wider condition at the castle entry

**Claim.** The condition `Good` at the castle entry asked two bytes to have the values of the reference machine `r`: the height of the flagpole's floating number (`FlagpoleFNum_Y_Pos`) and the number of the flagpole's score (`FlagpoleScore`). Both are set by the height at which Mario touches the pole. So `Good` was false at the castle entry of every measured run that touches the pole at another height. Now `Good` lets the height have any value and the number be below 8. The check on the ROM of [The star flag's rule after the castle entry](g-2-1-FlagRule.md) still passes, in about the same time. So the rule after the castle entry is proved for these runs too. `Good` at the castle entry stays a hypothesis, but a weaker one.

## Found on real runs

`touch-end-check` runs the movie from the first control above ground (`b₂`) with random inputs and pauses, as `castle-join-check` does. Of 100 random runs, 19 reach the castle. All 19 touch the pole at another height than the movie. On all 19 the old `Good` was false at `E + 1`. On 13 of them only the two bytes above differed from the nearest state of `B₀`.

```
runs                                   runs   Good at E + 1, before   Good at E + 1, now
the movie, a pause before or after      12     12                      12
the touch
random inputs from b₂, other touches    19      0                      13
```

The 6 runs that stay outside:

* 4 runs: Mario's `x` after the castle entry is 1 more than in `r`.
* 2 runs: the same, and the screen's bytes differ too (`ScreenEdge_X_Pos`, `ScreenRight_X_Pos`, `AreaParserTaskNum`, `VRAM_Buffer_AddrCtrl`, `Mirror_PPU_CTRL_REG1`).

On the 13 runs that are now in `Good`, task 2 and the flag's height also hold at `E + 1`. On every frame after `E`, up to the level change or the end of the run, the machine is in `Good` and the counters follow the rule (0 frames outside `Good`, 0 against the rule). 7 of them change the level. The other 6 stay paused at the end of the run.

## The change

`B₀` is made from seeds: states of `r` with some bytes known only in part (`FlagRule.partials`). Two entries are new:

```
FlagpoleFNum_Y_Pos   any value
FlagpoleScore        below 8         (its bits 3 to 7 are 0)
```

After the castle entry the flagpole's routine only draws the flag and the floating number. These two bytes give the sprites' height and tiles, and the sprites may have any value in `B₀`. So the walks of the check close with these bytes not known.

## Measurements

The check on the ROM (`flag-rule-check`), one run each with the machine nearly idle:

```
              data    stages
before        6.0 s   32.4 s
now           5.7 s   31.4 s
```

`B₀` has 240 states, as before.

## What is not proved

* `Good(seq(E + 1))`, task 2 and the flag's height stay hypotheses (1-1-g-2-2).
* Runs where Mario's `x` after the castle entry is 1 more than in `r` are outside `Good`. To let `x` have two values at a frame's start, the table of Mario's moves (`moveIn`, `nextMario`, `collFacts`) would have to know `x` before the move.
* Runs whose screen bytes at the castle entry differ from `r` are outside `Good`.

## Files

Lean: `Theorems/FlagRule.lean` (`partials`). The private proof `flag_check` checks the new `B₀`.

```
.lake/build/bin/smbrta flag-rule-check FM2        # the check on the ROM, then the real frames
.lake/build/bin/smbrta touch-end-check FM2 [N]    # N random runs from b₂ and runs with pauses: Good at E + 1, and the rule after it
```
