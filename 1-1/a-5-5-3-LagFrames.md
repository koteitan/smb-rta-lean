[← Back](README.md) | [English](a-5-5-3-LagFrames.md) | [Japanese](a-5-5-3-LagFrames-ja.md)

# Frames not counted, up to the pipe

**Claim.** A frame that starts in the idle loop in control either calls the routine of the mode, or it ends with the speed, the subspeed, the position, the routine, the mode,
the task and thirteen more bytes as it began. This holds if each of its instructions before that call meets `Clean`. A paused frame skips the call. So, up to the vertical pipe, the end of a
counted frame is read from its own machine. The frames not counted between two counted frames keep the three values, from conditions on single frames. What `Reads` of
[The frames up to the pipe, read from the machines](a-5-5-PipeFrames.md) assumed is now a theorem from these conditions.

The old field `lags.store` (a store before the call does not touch the five bytes) is gone: the check proves it. A frame not counted that does not call the routine also ends
in control by the check, so `lags.ctl` is now asked only of the counted frames. The old field `lags.game` (a frame not counted that calls the routine keeps the three values) is
gone too: a frame not counted ends paused, and such a frame does not call the routine ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)).

Notation. `fm(t)` and `inp(t)` are the machine and the input of counted frame `t`. `seq(n)` and `sin(n)` are the machine and the input of frame `n`, every frame counted.
Counted frame `t` is frame `ix(t)`. `tr(m, i, k)` is the machine after `k` instructions of the frame of `m` with the input `i`, and `frame(m, i)` is the machine at its end.
`c` is the call of the mode's routine: the instruction before `SkipMainOper`. `V(m) = (v(m), f(m), P(m))` are the speed, the subspeed and the position (five bytes).
`K(m)` are the routine, the mode and the task (three bytes), and `ctl(m)` says that they are those of control. `W(m)` are thirteen more bytes: the facing and moving directions,
the running speed, the stored speed, the collision bits, the area's type, the swimming flag, the change of size, the player's state, and the height, its high byte, the
vertical speed and its fraction (the four bytes of `OpenFlat.vertA`, added in round 12). [The opening on real frames](a-5-4-OpenFrames.md) needs them.
`FrameStart(m)` is `PipeWrites.FrameStart` of `guardOf`: `m` is in the idle loop with its stack pointer, at the frame's start, with the NMI on, and `ctl(m)`.
`Clean` is the `Clean` of `PipeWrites.guardOf`: a store with a target not known does not touch the bytes of its `prot`. The five bytes of `V` are not among them.

```
keeps_frame    :  lagCheck,  FrameStart(m),
                  (∀ k,  frame(tr k) = frame(m)  ∧  (∀ j ≤ k,  pc(tr j) ≠ c)   →   Clean(tr k))
                  →   (∃ k,  frame(tr k) = frame(m)  ∧  pc(tr k) = c)   ∨   (V, K, W)(frame(m, i)) = (V, K, W)(m)
known_of_keep  :  FrameStart(m),  K(m') = K(m)   →   ctl(m')

Lags           :  seq(n + 1) = frame(seq n, sin n),   seq(ix t) = fm t,   sin(ix t) = inp t,
                  ix(0) = 0,  ix(t + 1) = the first frame after ix(t) that ends not paused (looking at dP frames),   and
                    ctl   :  ∀ t ∈ [1, E),  ctl(seq(ix t + 1))                     (each counted frame before the entry ends in control)
                    resume:  ∀ t < E,  ix(t + 1) < ix t + 1 + dP                     (no pause before the entry lasts dP frames)
                    clean :  ∀ n ∈ [1, ix E),  ∀ k,  Clean(tr(seq n, sin n, k))
                  and for a frame not counted,  t < E,  ix t < n < ix(t + 1)  (LagPause):
                    keeps  :  ∀ k,  KeepsPause(tr(seq n, sin n, k))                  (no store through an index or a pointer to the pause byte)
Lags.paused    :  t < E,  ix t < n < ix(t + 1)   →   bit₀(seq(n + 1)) = 1               (it ends paused: by the definition of ix)

Lags.no_call   :  pauseCheck,  Lags,  FrameStart(seq n)   →   a frame not counted does not call c
Lags.known_end :  lagCheck,  pauseCheck,  Lags,  1 ≤ n < ix E,  FrameStart(seq n)   →   ctl(seq(n + 1))
Lags.starts    :  lagCheck,  walkCheck,  pauseCheck,  Lags,  1 ≤ E,  FrameStart(fm 1)   →   ∀ n ∈ [ix 1, ix E],  FrameStart(seq n)      (StartRun)
lags_keepI     :  lagCheck,  walkCheck,  pauseCheck,  Lags,  FrameStart(fm 1)   →   ∀ t ∈ [1, E),   (V, K, W)(fm(t + 1)) = (V, K, W)(frame(fm t, inp t))
lags_keep      :  the same   →   ∀ t ∈ [1, E),   V(fm(t + 1)) = V(frame(fm t, inp t))
ReadsOwn       :  ∀ t ∈ [1, E],  the start of fr(t) is V(fm t);   ∀ t ∈ [1, E),  the end of fr(t) is V(frame(fm t, inp t))
reads_of_lags  :  lagCheck,  walkCheck,  pauseCheck,  ReadsOwn,  Lags,  FrameStart(fm 1)   →   Reads
Pipe.reads     :  the old field reads, a theorem (Route)
```

`lagCheck` is a check on the ROM, by `native_decide` in the private `lag_check`; `pauseCheck` is that of `pause_check` ([LagPause](a-5-5-3-3-LagPause.md)). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/LagFrames.lean`; `ReadsOwn`, `Lags`, `Lags.known_end`, `Lags.starts`, `lags_keepI`, `lags_keep`, `reads_of_lags` in `Theorems/PipeFrames.lean`; `Pipe.own`, `Pipe.lags`,
`Pipe.reads` in `Theorems/Route.lean`; private `Proof/PipeWrites.lean`.

## How it works

* **The walk.** It is the abstract machine of `TaintRun`, as in [One whole frame](a-5-2-PipeWrites.md). It starts in the idle loop with the routine, the mode and the task known,
  and every other byte of RAM not known. One byte is followed as the counter of `TaintRun` (`Env.rkI`). The walk fails on any write to it. At the frame's end the byte is still
  followed, so it has the value it began with. There is one walk for each of the 21 bytes of `V`, `K` and `W`.
* **The cut.** The walk stops at the call `c`. The pause byte is not known, so the walk follows the paused path and the path that is not paused. The path that is not paused
  reaches `c`. A paused frame skips `c` and ends: the screen, the sound, the pad and the pause run, and none of them writes the 21 bytes.
* **Stores with a target not known.** `Clean.store` says such a store does not touch the bytes of `prot`. The five bytes of `V` are not in `prot`. So at such a store the walk
  forgets the followed byte, and then it fails at the frame's end. The walk does not fail: on every path that does not reach `c`, the walk knows the target of each store.
  The stores before `c` go through an index (the screen's buffer, the timers, the random bits). The index comes from the program or from a table of the ROM. To keep it, the
  search forgets no byte of RAM and keeps both index registers in its key, as the search of `CtrlKeep` (part e) does. Before, the five bytes were put in `prot`, and so
  `store` was a field.
* **The counter's value.** `TaintRun` follows `DEC abs` of the counter only when the counter is at least 2. Here the byte can be 0 or 1. So the step is restated (`s_astep1L`),
  with the condition that the step is not `DEC abs` of the byte in place of the bound. The walk checks this condition at every step.
* **The frames.** `lags_keep` goes from frame `ix(t) + 1` to `ix(t + 1)`. On each frame, `keeps_frame` gives `V` kept, or the frame calls `c`. A frame not counted does not
  call `c` (`Lags.no_call`: it ends paused, `paused`, `keeps`).
  The induction `Lags.starts` asks `ctl` at the end of each frame from control to the entry: `ctl` gives it for a counted frame, and `keeps_frame` (with `K`) for a frame not
  counted (`Lags.known_end`).
* **Numbers.** For each of the 21 bytes: 108,633 steps, 7,157 forks, 0 failures, a table of 7,846 states; 3 paths reach `c`, 6 end the frame. The search takes about 0.2 s and the
  check about 0.3 s natively, for each byte; the whole check about 7 s.

## Checked on real frames

A program (`lag-check`). Each frame on which the interval timer does not move is a frame not counted. On each such frame it checks `FrameStart`, `Clean` on each instruction
before the call, whether the frame calls `c`, whether `V` changes, and whether it ends in control. A run stops at the entry, or at the first counted frame that ends out of control.

| runs | counted frames | frames not counted | ending paused | calling `c` | not `FrameStart` | not `Clean` | changing `V` | not calling `c`, ending out of control |
|---|---|---|---|---|---|---|---|---|
| the TAS, from control to the entry | 368 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| random inputs with Start, small and big (240) | 73,757 | 76,542 | 76,542 | 0 | 0 | 0 | 0 | 0 |
| big with the super status, random inputs (240) | 74,974 | 76,589 | 76,589 | 0 | 0 | 0 | 0 | 0 |
| a pause near the entry, then the TAS's inputs (200; 40 enter) | 1,480 | 14,140 | 14,140 | 0 | 0 | 0 | 0 | 0 |
| followed past a counted frame out of control (240; not part of the check) | 79,764 | 88,236 | 83,778 | 4,449 | 8,388 | 9 | 23 | 3,939 |

* In the runs that stop at the first counted frame out of control, every frame not counted ends paused, and none calls `c`. This is the new field `paused`.
* **Which frames not counted call `c`.** Only in the last row: 4,449 frames, after an injury or a death. Each of them starts with the master timer control not 0.
  17 of them end in control. During the injury blink (routine 10) the game runs the player's routine while the master timer control
  stops the timers, so he moves on frames not counted: 14 of the 4,449 frames. For example `(v, f, P) = (3, 108, 78720) → (2, 156, 78752)`. These frames do not end paused. Each such
  run has a counted frame out of control before the entry: an injury or a death. It is outside the theorem by `ctl` (items 1-1-0-6-2 and 1-1-0-6-3).

## Assumed (not proved in Lean)

* **`lags.store` is no longer assumed**: the check proves that no store before the call, on a frame that does not call it, touches the five bytes.
* **`lags.ctl`**, now only for the counted frames before the entry: each ends in control. A frame not counted that does not call `c` ends in control by the check.
* **`game` is no longer assumed**: a frame not counted does not call the mode's routine. It ends paused (`Lags.paused`), and a frame that ends paused does not call it
  ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)). What stays assumed there is `keeps`. Which frames are counted is read from the
  pause byte (`ixP`), so `paused` is no longer assumed; that these are the frames on which the interval timer moves is the count of `chg.ha₁`, as before.
* **Not in this item.** That the counted frames are those of `clock` (only the frame numbers join them, as before). That each counted frame is a `Frame` (item 0-0-0-3-1).

**Files.** `Theorems/LagFrames.lean`, `Theorems/PipeFrames.lean`, `Theorems/StartRun.lean`, `Theorems/Route.lean`, private `Proof/PipeWrites.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta lag-check FM2 240    # the check for the 8 bytes, then the fields on real frames, about 4 minutes
```
