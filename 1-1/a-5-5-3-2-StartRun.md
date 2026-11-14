[← Back](README.md) | [English](a-5-5-3-2-StartRun.md) | [Japanese](a-5-5-3-2-StartRun-ja.md)

# Every frame from control to the pipe starts in the idle loop

**Claim.** From the press of Start on the title, the machine at control starts a frame in the idle loop, in control. From there, every frame up to the entry into the vertical pipe,
counted or not, starts so too, if each counted frame ends in control and each instruction is `Clean` (and does not write the pause byte through an index or a pointer, on a
frame not counted). A frame not counted ends paused by the definition of the counted frames ([LagPause](a-5-5-3-3-LagPause.md)). A frame not counted does not call the mode's routine ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)),
so it ends in control by the check of [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md). So these are no longer assumed:

* `Pipe.start` (item 1-1-a-5-2-1): the frame that enters starts in the idle loop, in control;
* `lags.start` (item 1-1-a-5-5-3-2): each frame not counted starts in the idle loop.

The old `lags.clean` (`Clean` with the five bytes of `V` protected, before the call of the mode's routine) was split last round. Its part on the five bytes (`lags.store`)
is now proved by the check of `LagFrames`. The rest is asked of every frame from control to the entry, on all its instructions (`lags.clean`).

Notation. `seq(n)` is the machine when frame `n` begins, every frame counted, `sin(n)` its input, and `seq(n + 1) = frame(seq n, sin n)`. The counted frame `t` is frame `ix(t)`, and
`fm(t) = seq(ix t)`: `ix(t + 1)` is the first frame after `ix(t)` that ends not paused, and `ix(0) = 0`. `tr_n(k)` is the machine `k` instructions into frame `n`. `c` is the call of the mode's routine. `V = (v, f, P)` are the speed, the subspeed and the position.
`vfp` is the list of their five bytes.

```
ctl(m)            :=  OperMode(m) = the game  ∧  OperMode_Task(m) = the game core  ∧  GameEngineSubroutine(m) = PlayerCtrl
FrameStart_G(m)   :=  pc(m) = EndlessLoop  ∧  the stack pointer has its value there  ∧  m is at the frame's start (two windows of the dot)
                      ∧  the NMI is on  ∧  the joypad's strobe is off  ∧  the bytes of G.known have their values
FrameStart(m)     :=  FrameStart_G(m) for G = guardOf: the routine, the mode and the task are those of control
Clean(m)          :=  PipeWrites.Clean for guardOf (store, read, jump, time)
CleanK_G(q, m)    :=  Clean_G(m), but the store at q with X = 0 is not asked (FrameKeep)
```

```
starts         :  keepCheck(S, G, W),  FrameStart_G(seq a),  W(seq a),
                  ∀ n ∈ [a, b),  ∀ j,  CleanK_G(S.store, tr_n(j)),
                  ∀ n ∈ [a, b),  the bytes of G.known have their values in seq(n + 1)
                  →   ∀ n ∈ [a, b],  FrameStart_G(seq n)  ∧  W(seq n)
starts_dep     :  the same, with the known bytes at the end of frame n asked only when FrameStart_G(seq n)
starts_clean, starts_clean_dep :  the same with no bit watched (W = []) and Clean_G in place of CleanK_G
Begin.start₁   :  check (TitleStart),  titleCheck(c, G, m₀),  Begin,  seq 1 = frame(seq 0, inp 0),  the bytes of G.known in seq 1   →   FrameStart_G(seq 1)
Begin.start₁G  :  the same for G = guardOf; ctl(seq 1) (the field Begin.ctl) gives the known bytes
Begin.pos₁     :  check,  titlePosCheck(c, m₀),  Begin,  seq 1 = frame(seq 0, inp 0)   →   P(seq 1) = P(m₀)          (this round)
Begin.hs₁      :  the same   →   startHS(seq 1) = startHS(m₀)       (the speed, the subspeed, the facing and moving directions, the running speed; this round)

Lags           :  ix t < ix(t + 1),  fm t = seq(ix t),  and
                    ctl   :  ∀ t ∈ [1, E),  ctl(seq(ix t + 1))                      (the counted frames)
                    clean :  ∀ n ∈ [1, ix E),  ∀ k,  Clean_P(tr_n(k))      (Clean with the pause byte protected too: LagPause.guardP; the old clean and keeps)
Lags.cleanG    :  Lags   →   ∀ n ∈ [1, ix E),  ∀ k,  Clean(tr_n(k))
Lags.keepsP    :  Lags   →   a frame not counted does not write the pause byte through an index or a pointer   (LagPause; it ends paused by the definition)
Lags.known_end :  lagCheck,  pauseCheck,  Lags,  n ∈ [1, ix E),  FrameStart(seq n)   →   ctl(seq(n + 1))
Lags.starts    :  lagCheck,  walkCheck,  pauseCheck,  Lags,  FrameStart(seq 1)   →   ∀ n ∈ [1, ix E],  FrameStart(seq n)
Lags.lagStart  :  the same   →   FrameStart(seq n) for a frame not counted          (the old field lags.start)
Pipe.startE    :  lagCheck,  walkCheck,  pauseCheck,  1 ≤ E,  FrameStart(seq 1)   →   FrameStart(fm E)       (the old field Pipe.start)
Run.pipeStart₁ :  title_check,  title_ctl_check   →   FrameStart(seq 1)                  (with the field title)
Run.pipeKeep₁  :  the checks,  1 ≤ E   →   the 21 bytes of LagFrames.lagI of fm 1 are those of seq 1     (the frames before the counted frame 1 end paused)
Run.pipePos    :  the checks,  title_pos_check,  1 ≤ E   →   P(pipe.fm 1) = P(m₀)
Run.pipeHS     :  the checks,  title_pos_check,  1 ≤ E   →   startHS(pipe.fm 1) = startHS(m₀)
```

`walkCheck` and `titleCheck` are checks on the ROM, by `native_decide` in the private `walk_check` and `title_ctl_check` (about 4 s together in the proof build).
`titlePosCheck` walks frame 0 as `titleCheck` does, and asks at each end with control that the bytes of the position, of the horizontal state and the ten bytes of `stI` are
known, with the values of `m₀` (the private `title_pos_check`, about 2.2 s natively).
`lagCheck` is the check of [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md), in the private `lag_check`.
The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`. `#print axioms route_1_1` shows no `sorryAx`.

Lean: `Theorems/StartRun.lean`; `Lags`, `Lags.known_end`, `Lags.starts`, `Lags.lagStart`, `Lags.startE` in `Theorems/PipeFrames.lean`; `Pipe.one_le`, `Pipe.startE`, `Pipe.reads`,
`Run.pipeStart₁` in `Theorems/Route.lean`; `rule_on_frameS` in `Theorems/PipeWrites.lean`; private `Proof/StartRun.lean`.

## How it works

* **One whole frame.** The walk is the one of `FrameKeep` ([part f](f-6-19-FrameKeep.md)): the abstract machine of `TaintRun` follows a frame from `FrameStart`, under `CleanK` on each
  instruction, and every path ends at the start of the next frame (the idle loop, its stack pointer, a window of the dot, the NMI on, the strobe off). The bytes of `G.known` at the end are
  not known to the walk. They come from `ctl` at the end of a counted frame, and from the check of `LagFrames` at the end of a frame not counted, which does not call the mode's
  routine (`Lags.no_call`, `Lags.known_end`). The last needs that the frame starts in control, so the induction asks the known bytes at the end of frame `n`
  only when frame `n` starts so (`starts_dep`). Here the walk has the guard of `PipeWrites` (`guardOf`), no bit watched and no place of the move routine (`walkCheck`), so its
  condition on one instruction is `Clean` itself. 641,723 steps, 65,610 forks, 0 failures, a table of 43,259 states; the search 1.5 s and the check 2.2 s natively.
* **The frames not counted.** The walk does not know the pause byte. So a paused frame is one of its paths. The induction goes over every frame of `seq`
  from frame 1 to `ix E`, counted or not; the frames before the counted frame 1 are frames not counted too.
* **The machine at control.** `TitleStart` proves that frame 0 begins in a near or held state of its set. `titleCheck` (`TitleStart.frame0Check`) walks frame 0 from
  these states again with any input, Start included, and asks that each end with control is the start of a frame. `Run.pipeStart₁` reads it on frame 1 of `base`; the induction carries it to `pipe.fm 1`.
* **`one_le`.** The entering frame must be frame 1 or later. This is now a theorem (`Pipe.one_le`, `Route.Run.pipeOne`): `fm 0` is the run's frame 0, frame 0 ends in control (`title`), and an entering frame ends with the pipe's routine (`Enters`). The two routines differ (`EntryKeep.KeepOK.ne`).

## Checked on real frames

A program (`start-check`). From a machine at control it runs to the entry, or to the first frame that ends out of control. On each frame it checks `FrameStart`, `Clean` on each
instruction, and on a frame not counted (the interval timer does not move) the stores before `c` (the old field `lags.store`, now proved). On the entering frame it checks `FrameStart`.
It checks that every frame ends in control, so it covers the new `lags.ctl` (the counted frames) too.

| run | frames | not counted | entries | runs stopped out of control | not `FrameStart` | not `Clean` | a store to `vfp` before `c` | entering frame not `FrameStart` |
|---|---|---|---|---|---|---|---|---|
| the TAS, from control to the entry | 367 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| own inputs with Start, small and big (240) | 150,299 | 76,542 | 0 | 51 | 0 | 0 | 0 | 0 |
| a pause near the entry, then the TAS's inputs (200) | 15,580 | 14,140 | 40 | 0 | 0 | 0 | 0 | 0 |
| from machines of the TAS before the entry: B and Right, then Down (480) | 26,903 | 0 | 93 | 0 | 0 | 0 | 0 | 0 |

* The 51 runs that stop end out of control on a death, a growth or an injury. By `lags.ctl` such a run is outside the theorem. [The whole of 1-1](0-1-Route.md) already lists
  a run with a power-up as outside it.
* No frame not counted called the mode's routine: all were pauses.
* The machine at control after the press on the title starts a frame: proved by `title_ctl_check` for every machine of the condition at the press. On the TAS it holds too.

## Assumed (not proved in Lean)

* **`lags.ctl`**: each counted frame from control to the entry ends in control. A condition on one state of each frame. It fails on a growth, an injury and a death.
  A frame not counted ends in control by the check: it ends paused (by the definition of `ix`), so it does not call the mode's routine.
* **`lags.clean`**: each instruction of these frames is `Clean`, with the pause byte protected too (no store through an index or a pointer writes it). It is the same kind
  of condition as `chg.upClean₁` (part b) on the same frames, with fewer bytes protected, and as `FrameKeep.Frames.cleanF` above ground. Checked on the same runs as
  below with the pause byte protected (`start-check FM2 240 pause`): 0 instructions fail.
* **`lags.keeps` is no longer a field** (this round): it was the pause byte's part of `Clean` on the frames not counted, and it is now in `lags.clean` (`Lags.keepsP`).
* **`lags.game` is no longer assumed**: in its place the pause byte protected in `lags.clean` and the definition of the counted frames ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)).
* `lags.store` is no longer assumed: the check of `LagFrames` proves it.
* `one_le` is no longer assumed: `Pipe.one_le` proves it.
* **`Run.pipeAt` is gone.** `pipe`'s counted frame 1 is no longer frame 1 by the definition: it is the first frame from frame 1 on that ends not paused. The values at
  control are read on frame 1 and carried to it by the frames before it (`Run.pipeKeep₁`).

`StartRun.starts` and `Begin.start₁` are general in the guard. Part b's `Run.upStart₁` does the same induction on `base.seq` inside `EntryKeep`; the two can share one lemma.

**Files.** `Theorems/StartRun.lean`, `Theorems/PipeFrames.lean`, `Theorems/Route.lean`, `Theorems/PipeWrites.lean`, private `Proof/StartRun.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta start-check FM2 240    # the two checks, then the fields on real frames, about 4 minutes
```
