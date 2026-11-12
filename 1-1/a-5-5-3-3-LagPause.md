[← Back](README.md) | [English](a-5-5-3-3-LagPause.md) | [Japanese](a-5-5-3-3-LagPause-ja.md)

# A frame that ends paused does not call the mode's routine

**Claim.** A frame that starts in the idle loop in control and calls the routine of the mode ends with the low bit of the pause byte 0. So a frame that ends paused does not call
the routine. This holds if each instruction of the frame is `Clean` and does not write the pause byte through an index or a pointer. Up to the vertical pipe, a frame not counted
ends paused (the new field `lags.paused`). So it does not call the routine, and it keeps the speed, the subspeed and the position and ends in control by the check of
[Frames not counted, up to the pipe](a-5-5-3-LagFrames.md). The old field `lags.game` is gone.

Notation. `tr(m, i, k)` is the machine after `k` instructions of the frame of `m` with the input `i`, and `frame(m, i)` is the machine at its end. `c` is the call of the
mode's routine (the instruction before `SkipMainOper`). `g` is the RAM index of the pause byte (`GamePauseStatus`), and `bit₀(m)` is its low bit in `m`. `FrameStart(m)` and `Clean` are those of
`PipeWrites.guardOf`, as in [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md). `KeepsPause(m)` says: a store through an index or a pointer at `m` does not write the byte `g`.
`seq(n)`, `sin(n)` are the machine and the input of frame `n` of the run (every frame counted); counted frame `t` is frame `ix(t)`.

```
ends_unpaused      :  pauseCheck,  FrameStart(m),  ∀ k, Clean(tr k),  ∀ k, KeepsPause(tr k),
                      ∃ k,  frame(tr k) = frame(m)  ∧  pc(tr k) = c          →   bit₀(frame(m, i)) = 0
no_call_of_paused  :  the same,  bit₀(frame(m, i)) = 1                        →   ¬ ∃ k,  frame(tr k) = frame(m)  ∧  pc(tr k) = c

Lags   (new fields, for a frame not counted:  1 ≤ t < E,  ix t < n < ix(t + 1))
  paused  :  bit₀(seq(n + 1)) = 1
  keeps   :  ∀ k,  KeepsPause(tr(seq n, sin n, k))
Lags.no_call       :  pauseCheck,  Lags,  FrameStart(seq n)   →   frame n does not call c
```

`pauseCheck` is a check on the ROM, by `native_decide` in the private `pause_check` (`Proof/LagPause.lean`). It takes about 6 s natively.
The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/LagPause.lean`; `Lags.paused`, `Lags.keeps`, `Lags.no_call` in `Theorems/PipeFrames.lean`; private `Proof/LagPause.lean`.

## How it works

* **Why.** The NMI calls the mode's routine only when the low bit of the pause byte is 0 (read from the code: `lda GamePauseStatus; lsr; bcs SkipMainOper`). After the call no
  instruction writes the pause byte. So the bit stays 0 to the frame's end. The two walks below show this on the ROM.
* **The guard.** The walks use `guardOf` with the pause byte among the bytes that a store with a target not known does not touch (`guardP`). `Clean` and `KeepsPause` give
  `Clean` of `guardP` (`clean_with`). So the walks keep the pause byte's known bits through such stores.
* **The first walk** starts in the idle loop with the low bit of the pause byte known: 0 or 1, two starts (and early or late in the frame: four starts). It follows the frame
  up to the call `c`. The pause routine may flip the bit (Start); the walk knows the bit on each path. At `c` the walk asks that the bit is known to be 0, and that a state of the
  second walk's table covers the state. A path that ends the frame before `c` asks nothing.
* **The second walk** is the walk of [One frame in control keeps watched bits](f-6-19-FrameKeep.md) (`FrameKeep.walkK`), from the states at `c` to the frame's end, through
  the mode's routine. At the end it asks that the bit is known to be 0 (`fin`).
* **The proof** (`frame_runP`) follows the machine along the two walks, one instruction at a time. If the frame reaches `c`, the machine at `c` is covered by a state of the
  second walk, and the frame ends in a state that knows the bit is 0. If it does not, no instruction of the frame is at `c`.
* **The search's key.** The key of the search holds the pause byte's known bits, and the register `A` at a store of `A` to the pause byte. Without `A`, the two paths of the
  pause routine (the bit flipped or not) join at its store, and the bit is lost.
* **Numbers.** The first walk: 5,812 steps, 755 forks, 0 failures, a table of 566 states, 3 states at `c` (all with the bit known 0). The second walk: 1,902,459 steps,
  194,062 forks, 0 failures, a table of 127,977 states. The searches take about 3.9 s and the whole check about 6 s natively.

## Checked on real frames

A program (`lag-pause-check`). It runs the two searches and the check natively. On each frame of real runs it checks whether the frame calls `c`, whether a store through an
index or a pointer writes the pause byte, and the bit at its end. A frame on which the interval timer does not move is a frame not counted. A run stops at the entry, or at the
first counted frame that ends out of control.

| runs | counted frames | frames not counted | ending paused | storing to the pause byte | calling `c` | frames calling `c` that end paused |
|---|---|---|---|---|---|---|
| the TAS, from control to the entry | 368 | 0 | 0 | 0 | 0 | 0 of 368 |
| own inputs with Start, small and big (60) | 18,382 | 18,414 | 18,414 | 0 | 0 | 0 of 18,382 |
| a pause near the entry, then the TAS's inputs (200; 40 enter) | 1,480 | 14,140 | 14,140 | 0 | 0 | 0 of 1,480 |
| big with the super status, own inputs (60) | 18,076 | 19,157 | 19,157 | 0 | 0 | 0 of 18,076 |
| followed past a counted frame out of control (60; not part of the check) | 19,980 | 22,020 | 21,187 | 0 | 831 | 0 of 20,811 |

* Every frame not counted of the runs in the theorem ends paused: the new field `paused` holds. No instruction writes the pause byte through an index or a pointer: `keeps` holds.
* No frame that calls `c` ends paused, also after an injury or a death (last row): what `ends_unpaused` says.
* In the last row, 833 frames not counted do not end paused. They come after an injury or a death, when the master timer control stops the timers. Such a run has a counted
  frame out of control before the entry, so it is outside the theorem (`lags.ctl`; items 1-1-0-6-2, 1-1-0-6-3).

## Assumed (not proved in Lean)

* **`lags.game` is no longer assumed.** A frame not counted does not call the mode's routine; this is now a theorem from `paused` and `keeps`.
* **`lags.paused`**: each frame not counted, from control to the entry, ends paused. This is a condition on one state: the machine after the frame. Up to the pipe the frames
  not counted are those of a pause; `gap` (which frames are not counted) is not tied to the interval timer. This is the same condition as `chg.paused₁` of the first change
  (item 1-1-b-3-8).
* **`lags.keeps`**: no instruction of a frame not counted writes the pause byte through an index or a pointer. It is of the kind of `Clean`, for one more byte.
* **Not proved: that the master timer control stays 0.** It is not needed now.

**Files.** `Theorems/LagPause.lean`, `Theorems/PipeFrames.lean`, `Theorems/Route.lean`, private `Proof/LagPause.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta lag-pause-check FM2 60    # the two walks, the position at control, and the fields on real frames, about 2 minutes
```
