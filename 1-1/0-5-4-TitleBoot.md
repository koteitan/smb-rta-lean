[Back to stage 1-1](README.md)

# From power-on to leaving the title

A run starts at power-on. Its RAM has no warm-boot mark, or the world-selection and continue-world bytes are zero. If it has no Start or Select before a press on frames 31 to 508, and presses Start with A or without it, the machine after that frame meets `Press`.

Start may also occur before the exit. `TitleBoot.Menu.Run` uses the first frame that leaves the title. The first input has no Start or Select. All inputs through the exit have no Select. The machine stays on the title before the exit. The exit is on frames 31 to 508. Held Start may delay that exit.

These are theorems with hypotheses. The route keeps `title.boot : TitleBoot.Start`. Its cases are `power` (the original input class), `menu` (the first-exit class), `later` (the first window after the demo), and `press` (the condition on one state for other runs).

## The condition after the exit

`Press` asks for the idle loop and stack pointer of the reference, the frame-start NMI conditions, no pause, and the reference values of the bytes `K`. It also asks that `FetchNewGameTimerFlag` is nonzero. This flag is outside `K`.

The flag makes the game load the timer when the player enters. The first menu frame leaves a different value from later menu frames. The game tests only whether the flag is zero. The former equality condition excluded the first menu frame. The nonzero condition includes it.

`TitleStart` starts its walk with this flag as the environment's byte `D`, known nonzero by `dg`. The walk follows the test and the clearing of the flag. Frame 0 and the speed at control have the same conclusions as before.

## The hypotheses

`pm n` is the machine after `n` frames from power-on. `pi n` is the input. `kp` is the exit frame. `PowerOn` fixes the reference registers and PPU state and allows RAM as described above.

The original `TitleBoot.Run` has these fields:

```
next       pm(n + 1) = frame(pm n, pi n)
power      PowerOn(pm 0)
quiet      n < kp implies no Start and no Select in pi n
start      pi kp is Start, with A or without it
lo, hi     first <= kp <= last
after      m = pm(kp + 1)
```

`TitleBoot.Menu.Run` has `next`, `power`, `lo`, `hi`, `after`, and these fields instead of `quiet` and `start`:

```
bootInput  pi 0 has no Start and no Select
quiet      n <= kp implies no Select in pi n
stays      2 <= n <= kp implies pm n is on the title
left       m is outside the title
```

`stays` and `left` refer to the game's mode byte on single states. They identify the first exit after the two startup frames. RAM before the reset has run may contain any mode byte. There is no condition that Start is absent on the preceding frame. The game may ignore a held Start.

## The proof

The first frame reads no RAM and stores no RAM. A tracked run and `StepWrites` prove that the reference covers every allowed power-on RAM. The first row has nine abstract states: the two protected bytes are zero, or one bit of the warm-boot mark differs.

The original rows use no Start and no Select before the press. `pressOK` checks the exiting frame. `Run.press` follows by induction over the rows.

The menu rows allow Start and forbid Select. Each frame ends either on the title in the next row or outside the title with `Press`. Only the former states seed the next row. `Menu.link_frame` proves this split. `Menu.Run.press` uses `stays` to discard earlier exits and `left` to discard a final frame still on the title.

The first later window is frames 1657 to 2123. It uses the original `Run`, with no Start or Select before the press. `windowAfter` finds this window while generating the private proof. `Start.later` uses it. The two startup frames and the whole first demo are included in its rows.

The ROM checks are `TitleBoot.check`, `TitleBoot.Menu.check`, and `TitleBoot.check (TitleBoot.later b)`, all in `TitleStart.check`. The route adds no hypothesis. `TitleBoot.Start.cond` and `TitleStart.Begin.press` give `Press` in all four cases.

## On real runs

The original class has 566 sampled runs, all with `Press`, including the first menu frame. The TAS exits on frame 39. The executable checks use the full new `Press`, including the nonzero flag.

The first-exit class has three groups of 200 runs: random inputs without Select, earlier Start with another button, and seeded RAM. All 600 first exits meet Press, with no counterexamples. The TAS passes. Another 100 seeded-RAM runs with random inputs without Start or Select meet Press in the later window.

Native checks take about 3.2 s for the original window, 6.4 s for the first-exit rows, and 9.4 s for the later window. These checks are longer than a few seconds. They add no run hypotheses. The existing title-to-control regression has 392 runs, 339 reaching control, with no counterexamples.

## What is not proved

Select before the exit, exits outside the two proved windows, a reset, and a title reached after a game over still use the state condition `Start.press`. A warm boot that keeps another selected world can fail `Press`. The first input of `Menu.Run` still excludes Start and Select.

Files: `Theorems/TitleBoot.lean`, `Theorems/TitleStart.lean`. Reproduce with `smbrta title-boot-check FM2`, `smbrta title-menu-check FM2`, and `smbrta title-check FM2`.

The Start-allowed menu rows fail to extend across the demo: the link to row 511 fails and that row has no title states. An unbounded sequence of later demo cycles is not proved.
