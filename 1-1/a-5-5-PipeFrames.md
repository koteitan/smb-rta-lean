[← Back](README.md) | [English](a-5-5-PipeFrames.md) | [Japanese](a-5-5-PipeFrames-ja.md)

# The frames up to the pipe, read from the machines

**Claim.** From control to the frame that enters the vertical pipe, each frame's speed, subspeed and position are read from the real machines. Then the frames follow each other (`next`),
and each frame's speed is at most the running top speed (`speed`): both are theorems now. The bound of [Entering the vertical pipe](a-4-PipeEntry.md) holds as before: he does not enter
before frame 368.

`fm(t)` is the machine when frame `t` begins. Frames are numbered without the `lag` frames ([The whole of 1-1](0-1-Route.md)). Frame 0 ends in control, so `fm(1)` is the machine at control.
`v(m)` is the signed value of `Player_X_Speed`, `f(m)` is `Player_X_MoveForce`, `P(m)` is the position. `fr(t)` is the [`Frame`](../0-0/0-1-TopSpeed.md) of frame `t`, with the values at its
start `v, f, P`, at the move `v₂, P₂`, and at its end `v', f', P'`. `E` is the frame that enters, `v_top` the running top speed.

```
Reads(E, fm, fr)  :=  ∀ t ∈ [1, E],   fr(t).v = v(fm t)    ∧  fr(t).f = f(fm t)    ∧  fr(t).P = P(fm t)
                      ∀ t ∈ [1, E),   fr(t).v' = v(fm(t+1)) ∧  fr(t).f' = f(fm(t+1)) ∧  fr(t).P' = P(fm(t+1))
Next(a, b)        :=  b.v = a.v'  ∧  b.f = a.f'  ∧  b.P = a.P'

next_of_reads     :  Reads  →  ∀ t ∈ [1, E),  Next(fr t, fr(t+1))
speed_of_reads    :  16 ≤ v_top,  Reads,  v(fm 1) = 0  →  ∀ t ∈ [1, E],  |fr(t).v| ≤ v_top
speed_end         :  the same  →  ∀ t ∈ [1, E],  |fr(t).v'| ≤ v_top
end_le            :  the same,  1 ≤ N,  fr(N).P' ≤ B  →  ∀ k,  N + k < E  →  fr(N + k).P' ≤ B + 16·v_top·k
no_entry_of_reads :  16 ≤ v_top,  1 ≤ N,  (∀ t,  Enter t → L ≤ fr(t).P₂),  (∀ t ≤ N,  fr(t).P₂ ≤ B),  fr(N).P' ≤ B,
                     Reads,  v(fm 1) = 0,  B + 16·v_top·(T − N) < L,  Enter E   →   T < E

Pipe.next, Pipe.speed (Route)        :  the old fields next and speed, as theorems
Pipe.reads (Route)                   :  Reads, from the frames read from their own machines and the frames not counted (own, lags, lag_check, walk_check, the start at control)
pipe_no_entry_real (private)         :  Enters(fm E, inp E),  FrameStart(fm E),  clean, tiles, edge, moved, openP, openB,  Reads,  still   →   367 < E
```

`Reads` is no longer a field. [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md) proves it from `Pipe.own` (each counted frame ends at its own machine) and
`Pipe.lags` (the frames not counted between them).

The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/PipeFrames.lean`, `Pipe` in `Theorems/Route.lean`, private `Proof/PipeWrites.lean`.

## How it works

* **Following.** The end of `fr(t)` and the start of `fr(t+1)` are read from the same machine `fm(t+1)`. So `Next` holds by the definition.
* **Speed.** At `fm(1)` the speed is 0. `Frame.bound` says: if the speed at a frame's start is at most `v_top`, so is the speed at its end. `Next` passes this to the next frame.
  This is an induction from frame 1 to `E`.
* **The bound.** If `E ≤ N`, `openP` says `fr(E).P₂ ≤ B`. If `E > N`, the end of frame `N + k` is at most `B + 16·v_top·k` (`end_le`). With `E = N + k + 1` and
  `fr(E).P₂ ≤ fr(E).P + 16·v_top`, this gives `fr(E).P₂ ≤ B + 16·v_top·(E − N)`. If `E ≤ T`, that is left of `L`, so he cannot enter.
* The old `no_entry_by` assumed `next` on every frame after `N`, and `speed` at `N`. Here only the frames up to `E` are used.

## Checked on real frames

A program (`pipe-frames-check`). For each frame it reads the machine at the start `fm(t)`, the machine after the move (when it comes to `PlayerSubs`), and the machine at the start of
the next counted frame `fm(t+1)`. It checks two things. (a) With the values after the move as `v₂, f₂, P₂`, the 8 conditions of `Frame` hold (`v₁, f₁` are the start's values, or 0).
(b) Some `Frame` has the same two ends (`v₂` searched over a byte's range). Between frame `N` and `E`, `Reads` needs only (b). It checks that a frame that is not counted changes none of
the speed, the subspeed and the position.

| run | counted frames | `lag` frames | (a) fails | (b) fails | `lag` frames that change the values | frames that enter |
|---|---|---|---|---|---|---|
| the TAS, from control to the entry | 368 | 0 | 0 | 0 | 0 | 368 |
| random inputs from machines of the TAS (300 runs) | 343,728 | 52,400 | 3 | 0 | 0 | none |
| from machines of the TAS before the entry: Right, then Down (1,200 runs) | 90,110 | 0 | 0 | 0 | 0 | 322 times (368 to 371) |

* The speed at control: with 120 different frames for Start on the title screen, it is 0 all 120 times. The horizontal state and the position are those of the machine `m₀` of the private
  proof all 120 times. On the TAS it is 0 too.
* On the TAS, `P₂` up to frame 32 is at most `P₀ + 9744`, and the position at the start of frame 33 is exactly `P₀ + 9744` (`openP`, `openB`).
* Frames that are not counted come during a pause, and while he grows, shrinks or dies. While `TimerControl` is not 0, the game does not count down the interval timer (read from the
  code). None of the measured frames changes the speed, the subspeed or the position. Of the 300 random runs, 51 end in a death and 12 change his size.
  **Correction (this round):** a run stops at the first counted frame that ends out of control. So the frames not counted after a growth, an injury or a death were not measured
  here. During the injury blink they do change the values ([Frames not counted, up to the pipe](a-5-5-3-LagFrames.md)).
* **The 3 frames where (a) fails.** All are while he has fallen into a pit and is below the screen. The scroll stops, and `KeepOnscr` holds him at the screen's right edge.
  For example `v₂ = 24 > 0`, `P' = P₂ − 512`, `v' = 0`. `impedeP` of `Frame` has only the case of the screen's left edge. Once he has fallen below the screen, a death follows (read from the code), so such a frame never comes before an entry.
  A `Frame` with the same two ends exists (`v₂ = 0`).

## Assumed (not proved in Lean)

* **Each frame is a `Frame`.** This is the type of `fr`. It was assumed before; it is item 0-0-0-3-1 (`FrameModel.frame_read` gives it under `ReadFrame`). It is checked on the real frames above.
  New is that it is used for frames 1 to `N` as well.
* **A frame that is not counted changes none of the three values.** This is no longer assumed as a whole. It is proved for a frame that does not call the mode's routine (a paused
  frame). What stays assumed is in [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md) and [Every frame from control to the pipe starts in the idle loop](a-5-5-3-2-StartRun.md): `lags.ctl` (now only the counted frames), `lags.clean`, `lags.game`. `lags.store` is proved now.
* **`still`: the speed at control is 0.** This is now proved (`Route.Run.still`) from the press of Start on the title ([From Start on the title to control](0-5-3-TitleStart.md)).
* **The frames are those of the run (item 1-1-0-4).** `Lags` takes the real frames of the whole run (`FrameKeep.RealRun`, `Route.Run.base`) as a parameter. Where the counted frames are is
  data, `gap t` (the frames not counted after the counted frame `t`), and `ixOf gap` is a definition: the counted frame 1 is frame 1 and `ixOf gap t < ixOf gap (t + 1)`. So the
  machine of `pipe` at control is the run's frame 1 (`Lags.fm_one`, `Route.Run.pipeAt`); the old link `pipeAt`, the old fields `seq`, `sin`, `next`, `ix`, `order`, `fm_ix`, `inp_ix` of `Lags` and the fields `fm`, `inp`, `one_le` of `Route.Pipe` are gone (`Pipe.fm` is `Lags.fm`, a definition; `Pipe.one_le` is a theorem).
* **Not in this item.** `openP`, `openB` (item 1-1-a-5-4) and `edge`, `moved` (item 1-1-a-5-9) stay hypotheses.

**Files.** `Theorems/PipeFrames.lean`, `Theorems/LagFrames.lean`, `Theorems/Route.lean`, private `Proof/PipeWrites.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-frames-check FM2 300    # the speed at control, and Reads and Frame on real frames
```
