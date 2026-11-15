[← Back](README.md) | [English](g-2-2-1-FlagWide.md) | [Japanese](g-2-2-1-FlagWide-ja.md)

# A wider condition at the castle entry

**Claim.** The condition `Good` at the castle entry asked some bytes to have the values of the reference machine `r`. On real runs that touch the pole at other heights, or reach the castle a little later, some of these bytes differ, so `Good` was false at `E + 1`. Now `Good` lets these bytes have the values they have on these runs:

* the height of the flagpole's floating number (`FlagpoleFNum_Y_Pos`) any value, and the number of the flagpole's score (`FlagpoleScore`) below 8 (round 12);
* Mario's `x` at a frame's start `x0` or `x0 + 1` (`x0` is that of `r`);
* the left and right `x` of the screen (`ScreenEdge_X_Pos`, `ScreenRight_X_Pos`) from 0 to 127 (before: 0 to 63).

The check on the ROM of [The star flag's rule after the castle entry](g-2-1-FlagRule.md) still passes. So the rule after the castle entry is proved for these runs too. `Good` at the castle entry stays a hypothesis, but a weaker one. Of 193 runs with random inputs that reach the castle, 176 are now in `Good` at `E + 1`. The other 17 have the area parser at work when the frame `E + 1` begins. Round 19 brings them in through a later frame `G` and the rule on the frames before it ([The castle entry with the area parser at work](g-2-2-3-FlagParser.md)).

## Found on real runs

`castle-rule-check` runs the movie from the first control above ground (`b₂`) with random inputs and pauses, as `touch-end-check` does, for seeds 1 to 1000. 193 of the random runs reach the castle. With the movie, the runs touch the pole at 51 heights from 37 to 164.

```
runs that reach the castle                           runs   Good at E + 1
the movie and 6 runs with a pause before the touch   7      7
random inputs, seeds 1 to 1000                       193    176
```

On the 183 runs in `Good`, task 2 and the flag's height also hold at `E + 1`. On every frame after `E`, up to the level change or the end of the run, the machine is in `Good` and the counters follow the rule (0 frames outside `Good`, 0 against the rule). 109 of the random runs change the level. The others stay paused at the end of the run.

`touch-end-check` with its 100 seeds (31 runs with the pauses after the touch): `Good` at `E + 1` on 25 runs before this round, 29 now.

### Mario's `x`

On the frame `E` Mario walks 2 pixels into the castle's wall: from `x0` to `x0 + 2`. The wall pushes him back by 1, so the frame `E + 1` begins with `x0 + 1`, his speed 0 and the side timer at its value at a bump. On the frame `E + 1` the move leaves `x0 + 1` (speed 0), and the wall pushes him back to `x0`. From then on every frame begins with `x0`. Measured on the 4 such runs of the first 100 seeds: they differ from `r` in `x` only.

### The screen

On some runs the screen scrolls while he walks from the pole to the castle, and it stops further right than in `r`: the left `x` of the screen was 79 and 83 at `E + 1` on such runs. The screen scrolls only while his position on the screen is at least a bound of the scroll routine, and with `x0` this keeps the left `x` below 128.

### What stays outside

The 17 random runs outside `Good` all have the area parser at work when the frame `E + 1` begins: the screen scrolled across a multiple of 32 pixels just before `E`, and the parser draws two new columns of metatiles over the next frames. They differ from the nearest state of `B₀` in the parser's task (`AreaParserTaskNum`, 1 to 7, on 14 runs), in the buffer that the screen routine draws next (`VRAM_Buffer_AddrCtrl` 6, on 6 runs), in the bit of the PPU's control that writes columns (`Mirror_PPU_CTRL_REG1`), and in `ObjectOffset`. On all 17 the parser draws one of 5 neighbouring columns past the castle, with the area's data at its end (`AreaDataOffset` the same on all). The machine is in `Good` again from frame `E + 1 + k` on, with `k` from 1 to 9.

## The change

`B₀` is made from seeds: states of `r` with some bytes known only in part (`FlagRule.partials`). The ends of a frame from the seeds join `B₀` with `x` as in the seeds (`FlagRule.wideX`).

```
FlagpoleFNum_Y_Pos               any value
FlagpoleScore                    below 8          (bits 3 to 7 are 0)
SprObject_X_Position             x0 or x0 + 1     (bit 0 not known)
ScreenEdge_X_Pos                 0 to 127         (bit 7 is 0)
ScreenRight_X_Pos                0 to 127         (bit 7 is 0)
```

Mario's numbers carry `x` now. They were `(v, F, f, A, C, s)` and are `(v, F, f, A, C, x, s)` (`q6`). The walk of the move starts from the known `x` (`moveIn`). After the collision `x` is `x0` in both cases: he stands, or the wall pushes him back from `x0 + 1` (`collFacts`, `nextMario`). The starts at the castle entry have `x0` and `x0 + 1` (`marioStarts`). The other stages keep `x` as they keep the counters (`x` is in `Ctx.mario`), but the stage of the offscreen bits, which reads `x` and gets it from its fact (`Ctx.ruledNoX`).

## Measurements

The check on the ROM (`flag-rule-check`). The two runs were made at the same time, with a load of about 4 on 28 cores:

```
             data    stages   the offscreen bits   Mario's numbers   moves   B₀
round 12     6.1 s   33.1 s   0.8 s                6714              4844    240
now          6.9 s   34.5 s   1.7 s                8762              6892    240
```

The stage of the offscreen bits takes twice as long: it splits the two bytes of the screen by their values, and they have 128 values now. The private proof `flag_check` built in 61 s in `prove.py` (47 s with the machine idle and 95 s under load in round 12).

## What is not proved

* `Good(seq(E + 1))`, task 2 and the flag's height stay hypotheses (1-1-g-2-2).
* Runs with the area parser at work at `E + 1` are outside `Good` at `E + 1` (17 of 193 measured random runs); `After` now asks `Good` at the first frame `G` after `E` where the parser is done, and the rule on the frames before `G` as a hypothesis ([The castle entry with the area parser at work](g-2-2-3-FlagParser.md)). To prove those frames, `B₀` would need the parser's bytes known (its task, the column, the name table's address, the buffer of metatiles, the attribute buffer, the second screen buffer) in about 45 combinations, and the stages would have to keep them apart. The stage of the other slots takes 18 s with 240 states, so this was not tried.

## Files

Lean: `Theorems/FlagRule.lean` (`partials`, `wideX`, `q6`, `moveIn`, `nextMario`, `collFacts`, `marioStarts`, `Ctx.mario`, `Ctx.ruledNoX`). The private proof `flag_check` checks the new `B₀`.

```
.lake/build/bin/smbrta flag-rule-check FM2              # the check on the ROM, then the real frames
.lake/build/bin/smbrta touch-end-check FM2 [N]          # N random runs from b₂ and runs with pauses: Good at E + 1, and the rule after it
.lake/build/bin/smbrta castle-rule-check FM2 S N        # seeds S to S + N − 1: Good at E + 1 (or the bytes that differ), the rule after it
.lake/build/bin/smbrta castle-x-check FM2 S N [all]     # Mario's x and the screen's bytes on the frames around E
```
