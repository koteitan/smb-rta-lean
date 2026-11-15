[← Back](README.md) | [English](g-2-2-3-FlagParser.md) | [Japanese](g-2-2-3-FlagParser-ja.md)

# The castle entry with the area parser at work

**Claim.** This is a partial result. `After` now asks the condition `Good` on the first frame `G` after the castle entry where the area parser is done, not on frame `E + 1`. On the frames from `E + 1` to `G − 1` the counters follow the rule of one frame by a hypothesis on each of these frames (`pre`). On a run with the parser not at work at `E + 1`, `G = E + 1` and `pre` says nothing: this is the old `After`. The runs with the parser at work at `E + 1` are now in the theorem. From `G` on, the rule is proved as before ([The star flag's rule after the castle entry](g-2-1-FlagRule.md)). `pre` is not proved: the attempts and their numbers are below.

## What the game does

At the end of the game core, after the game timer, `UpdScrollVar` runs the area parser when its task (`AreaParserTaskNum`) is not 0, or when the screen has scrolled past a multiple of 32 pixels. The parser draws two new columns of metatiles in 8 tasks, one task on each frame that runs. A task that draws (`RenderAreaGraphics`, `RenderAttributeTables`) writes the second screen buffer and sets `VRAM_Buffer_AddrCtrl` to 6. On the next frame the screen routine draws the second buffer, not the first. The first buffer then waits, and the frame writes after what is in it.

When the screen scrolls just before the castle entry, the parser is still at work when frame `E + 1` begins. The machine then has bytes that the states `B₀` of `Good` do not have (the parser's task, the buffer to draw, a bit of the PPU's control, `ObjectOffset`). On the measured runs the parser is done, and the machine is in `Good` again, after at most 9 frames that end not paused.

## Statement

```
After(seq, inp, E, T, c, L) :   a number G and
  E < G,   Good(seq(G))
  pre:  ∀ n, E < n < G  →  FlagStep(lim, w₀, paused(seq(n + 1)), x(seq n), x(seq(n + 1)))
  task(seq(E + 1)) = 2,   y(x(seq(E + 1))) = y(r)
  t(seq(E + 1)) = T,      ph(seq(E + 1)) = c
  G ≤ L
  level(seq(L + 1))

Checked(C, d),  ∀ n, seq(n + 1) = frame(seq(n), inp(n)),  After(seq, inp, E, T, c, L)  →
  Flag(lim, w₀, E, T, c, L)                                        flagOf_after
```

`x(m)` are the counters of the star flag, `paused(m)` the bit 0 of the pause status. A frame before `G` that ends paused is a `lag` frame, as after `G`. `y(x(seq(E + 1)))` is the flag's height read from the flag's slot; up to round 18 it was read from the first slot, which `Good` at `E + 1` gave. The field `flag` of `Route.Run` has the new type; no field of `Run` is added or removed.

## Real runs

`castle-after-check` takes the runs of `castle-rule-check`: from control above ground (`b₂`), random inputs with and without Start, and pauses. For each run it finds `G` (the first frame from `E + 1` on in `Good`, up to `E + 40`), and checks `pre`, task 2 and the height at `E + 1`. With `rule`, it checks the frames from `G` on up to the level change.

```
seeds          runs to the castle   G = E + 1   G later (G − E − 1)   no G   against pre   task or height wrong
1 to 1000      200                  183         17 (1 to 9)            0      0             0
1001 to 3000   384                  364         20 (2 to 9; 53, 54)    0      0             0
```

On the two runs with `G − E − 1` = 53 and 54, 46 of these frames end paused: the parser does not work in a paused frame.

With `rule`, every frame from `G` on, up to the level change or the end of the run, is in `Good` and follows the rule (a frame that ends paused keeps the counters): no frame out of `Good` and no frame against the rule, on all 583 runs (the movie is in both sets).

## Why `pre` is not proved

`pre` would follow from the check of the ROM if `B₀` had the states of the parser at work. Two ways were tried, as programs.

1. **The parser's states in `B₀`, kept apart at every place** by the task, the column and the buffer to draw. The states come from 16 machines: the last round of the parser on the walk to the castle, and a round from the castle entry with the scroll pushed by 32 pixels. `B₀` has 1008 states (240 before). Each stage has 204 states (12 before), and the search of the collision stage passes its limit of 3 million steps.
2. **The parser's bytes forgotten after the screen's stage, and taken again at the parser.** The frame is cut at `UpdScrollVar` too; a new last stage runs the parser from each value of its task, column, block column and metatiles that the 16 machines have. The stages up to `UpdScrollVar` keep these 16 bytes (walks with the byte as the counter). The Lean proof of this check (`frame_step` with the new stages) compiled; it is not in this round's files. On the ROM it did not close:
   * The abstract machine splits only the reads `LDA` of a byte. The parser reads the metatiles with `LDA abs,X`, so they must be known.
   * In the states with four fireworks, the abstract frame can write 75 bytes into the first screen buffer (four explosions of 500 points in one frame), past its end and onto `VRAM_Buffer2_Offset`. The parser's values must not be applied to these states (a filter by the values the state may have).
   * With the parser's task not kept apart in the stages, the order of its tasks is lost, and the first buffer grows without bound: the second round of the closure of `B₀` gave 5040 new states.
   * With the task kept apart, the closure ends after 6 rounds with 3336 states (129 s), but each stage has 324 states (27 times as many as before), and the search of the offscreen stage passes 3 million steps.

So a proof needs the order of the parser's tasks with the first buffer's offset through the whole game core. The states then grow about 27 times. This was not done.

## What is not proved

* `pre` on the frames from `E + 1` to `G − 1` (at most 9 frames on the measured runs). It is a hypothesis on each frame.
* `Good(seq(G))`, task 2 and the flag's height at `E + 1` stay hypotheses on single states.

## Files

Lean: `Theorems/FlagRule.lean` (`After` with `G`, `hG`, `pre`; `held_inv`, `held_inv'`, `flagOf_after`). Program: `castleAfterProbe` in `Main.lean`.

```
.lake/build/bin/smbrta castle-after-check FM2 S N         # seeds S to S + N − 1: G, pre, task and height at E + 1
.lake/build/bin/smbrta castle-after-check FM2 S N rule    # and the frames from G to the level change
```
