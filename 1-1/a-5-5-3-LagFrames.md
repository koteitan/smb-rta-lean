[← Back](README.md) | [English](a-5-5-3-LagFrames.md) | [Japanese](a-5-5-3-LagFrames-ja.md)

# Frames not counted, up to the pipe

**Claim.** A frame that starts in the idle loop either calls the routine of the mode, or it ends with the speed, the subspeed and the position it began with.
This holds if each of its instructions before that call meets `Clean`. A paused frame skips the call. So, up to the vertical pipe, the end of a counted frame is read from its
own machine. The frames not counted between two counted frames keep the three values, from conditions on single frames. What `Reads` of
[The frames up to the pipe, read from the machines](a-5-5-PipeFrames.md) assumed is now a theorem from these conditions.

Notation. `fm(t)` and `inp(t)` are the machine and the input of counted frame `t`. `seq(n)` and `sin(n)` are the machine and the input of frame `n`, every frame counted.
Counted frame `t` is frame `ix(t)`. `tr(m, i, k)` is the machine after `k` instructions of the frame of `m` with the input `i`, and `frame(m, i)` is the machine at its end.
`c` is the call of the mode's routine: the instruction before `SkipMainOper`. `V(m) = (v(m), f(m), P(m))` are the speed, the subspeed and the position.
`FrameStart₀(m)` is `PipeWrites.FrameStart` with no byte known: `m` is in the idle loop with its stack pointer, at the frame's start, with the NMI on.

```
keeps_frame   :  lagCheck,  FrameStart₀(m),
                 (∀ k,  frame(tr k) = frame(m)  ∧  (∀ j ≤ k,  pc(tr j) ≠ c)   →   Clean(tr k))
                 →   (∃ k,  frame(tr k) = frame(m)  ∧  pc(tr k) = c)   ∨   V(frame(m, i)) = V(m)

Lags          :  seq(n + 1) = frame(seq n, sin n),   seq(ix t) = fm t,   sin(ix t) = inp t,   ix t < ix(t + 1)
                 and for 1 ≤ t < E,  ix t < n < ix(t + 1):
                   start :  FrameStart₀(seq n)
                   clean :  ∀ k,  frame(tr k) = frame(seq n)  ∧  (∀ j ≤ k,  pc(tr j) ≠ c)   →   Clean(tr k)
                   game  :  (∃ k,  frame(tr k) = frame(seq n)  ∧  pc(tr k) = c)   →   V(seq(n + 1)) = V(seq n)

lags_keep     :  lagCheck,  Lags   →   ∀ t ∈ [1, E),   V(fm(t + 1)) = V(frame(fm t, inp t))
ReadsOwn      :  ∀ t ∈ [1, E],  the start of fr(t) is V(fm t);   ∀ t ∈ [1, E),  the end of fr(t) is V(frame(fm t, inp t))
reads_of_lags :  lagCheck,  ReadsOwn,  Lags   →   Reads
Pipe.reads    :  the old field reads, a theorem (Route)
```

`lagCheck` is a check on the ROM, by `native_decide` in the private `lag_check`. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/LagFrames.lean`; `ReadsOwn`, `Lags`, `lags_keep`, `reads_of_lags` in `Theorems/PipeFrames.lean`; `Pipe.own`, `Pipe.lags`, `Pipe.reads` in `Theorems/Route.lean`;
private `Proof/PipeWrites.lean`.

## How it works

* **The walk.** It is the abstract machine of `TaintRun`, as in [One whole frame](a-5-2-PipeWrites.md). It starts in the idle loop with every byte of RAM not known.
  One byte is followed as the counter of `TaintRun` (`Env.rkI`). The walk fails on any write to it. At the frame's end the byte is still followed, so it has the value it began with.
  There is one walk for each of the 5 bytes of `V`.
* **The cut.** The walk stops at the call `c`. The pause byte is not known, so the walk follows the paused path and the path that is not paused. The path that is not paused
  reaches `c`. A paused frame skips `c` and ends: the screen, the sound, the pad and the pause run, and none of them writes the 5 bytes.
* **Stores with a target not known.** `Clean.store` says such a store does not touch the bytes of `prot`. The 5 bytes are put in `prot`, so the followed byte is not touched.
  For this, `PipeWrites.aforget` now keeps the counter when its byte is in `prot` (`AS.forgetK`). The walk of `PipeWrites` has no counter, so it is not changed.
* **The counter's value.** `TaintRun` follows `DEC abs` of the counter only when the counter is at least 2. Here the byte can be 0 or 1. So the step is restated (`s_astep1L`),
  with the condition that the step is not `DEC abs` of the byte in place of the bound. The walk checks this condition at every step.
* **The frames.** `lags_keep` goes from frame `ix(t) + 1` to `ix(t + 1)`. On each frame, `keeps_frame` gives `V` kept, or the frame calls `c`, and then `game` gives it.
* **Numbers.** For each of the 5 bytes: 2,540 steps, 318 forks, 0 failures, a table of 241 states; the check takes about 10 ms natively.

## Checked on real frames

A program (`lag-check`). Each frame on which the interval timer does not move is a frame not counted. On each such frame it checks `FrameStart₀`, `Clean` on each instruction
before the call, whether the frame calls `c`, and whether `V` changes. A run stops at the entry, or at the first counted frame that ends out of control.

| runs | counted frames | frames not counted | ending paused | calling `c` | not `FrameStart₀` | not `Clean` | changing `V` |
|---|---|---|---|---|---|---|---|
| the TAS, from control to the entry | 368 | 0 | 0 | 0 | 0 | 0 | 0 |
| random inputs with Start, small and big (240) | 73,757 | 76,542 | 76,542 | 0 | 0 | 0 | 0 |
| big with the super status, random inputs (240) | 74,974 | 76,589 | 76,589 | 0 | 0 | 0 | 0 |
| a pause near the entry, then the TAS's inputs (200; 40 enter) | 1,480 | 14,140 | 14,140 | 0 | 0 | 0 | 0 |
| followed past a counted frame out of control (240; not part of the check) | 79,764 | 88,236 | 83,778 | 4,449 | 9 | 9 | 23 |

* In the runs that stop at the first counted frame out of control, every frame not counted ends paused, and none calls `c`. So `game` is never used there.
* **After an injury `game` is false.** The last row follows the runs past an injury or a death. During the injury blink (routine 10), the game runs the player's routine while the
  master timer control stops the timers. So he moves on frames not counted: 14 of the 4,449 frames that call `c`. For example `(v, f, P) = (3, 108, 78720) → (2, 156, 78752)`.
  The old `reads` was false there too. The other 9 frames do not start in the idle loop: the memory clear after a death runs past the frame's end. Each such run has a counted frame out of control before
  the entry: an injury or a death. It is outside the theorem (items 1-1-0-6-2 and 1-1-0-6-3).

## Assumed (not proved in Lean)

* **`start`, `clean`**: each frame not counted starts in the idle loop, and each of its instructions before the call is `Clean`. Conditions on one state and on single instructions.
* **`game`**: a frame not counted that calls the mode's routine keeps `V`. Before the pipe these are the frames of the master timer control: growth, injury, death.
  It is false during the injury blink (above). Read from the code: the timer control gets a value other than 0 only together with a change of the routine (`SetPRout`). So, if every counted
  frame ends in control, no frame not counted should call `c`. This is not proved.
* **Not in this item.** That the counted frames are those of `clock` (only the frame numbers join them, as before). That each counted frame is a `Frame` (item 0-0-0-3-1).

**Files.** `Theorems/LagFrames.lean`, `Theorems/PipeFrames.lean`, `Theorems/Route.lean`, `Theorems/PipeWrites.lean`, private `Proof/PipeWrites.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta lag-check FM2 240    # the check for the 5 bytes, then the fields on real frames
```
