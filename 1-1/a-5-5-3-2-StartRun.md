[← Back](README.md) | [English](a-5-5-3-2-StartRun.md) | [Japanese](a-5-5-3-2-StartRun-ja.md)

# Every frame from control to the pipe starts in the idle loop

**Claim.** From the press of Start on the title, the machine at control starts a frame in the idle loop, in control. From there, every frame up to the entry into the vertical pipe,
counted or not, starts so too, if each counted frame ends in control, each frame not counted that calls the mode's routine ends in control, and each instruction is `Clean`.
A frame not counted that does not call the mode's routine ends in control by the check of [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md). So these are no longer assumed:

* `Pipe.start` (item 1-1-a-5-2-1): the frame that enters starts in the idle loop, in control;
* `lags.start` (item 1-1-a-5-5-3-2): each frame not counted starts in the idle loop.

The old `lags.clean` (`Clean` with the five bytes of `V` protected, before the call of the mode's routine) was split last round. Its part on the five bytes (`lags.store`)
is now proved by the check of `LagFrames`. The rest is asked of every frame from control to the entry, on all its instructions (`lags.clean`).

Notation. `seq(n)` is the machine when frame `n` begins, every frame counted, `sin(n)` its input, and `seq(n + 1) = frame(seq n, sin n)`. The counted frame `t` is frame `ix(t)`, and
`fm(t) = seq(ix t)`. `tr_n(k)` is the machine `k` instructions into frame `n`. `c` is the call of the mode's routine. `V = (v, f, P)` are the speed, the subspeed and the position.
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

Lags           :  ix t < ix(t + 1),  fm t = seq(ix t),  and
                    ctl   :  ∀ t ∈ [1, E),  ctl(seq(ix t + 1))                      (the counted frames)
                    clean :  ∀ n ∈ [ix 1, ix E),  ∀ k,  Clean(tr_n(k))
                    game  :  for a frame not counted that calls c:  V(seq(n + 1)) = V(seq n)  ∧  ctl(seq(n + 1))
Lags.known_end :  lagCheck,  Lags,  1 ≤ E,  n ∈ [ix 1, ix E),  FrameStart(seq n)   →   ctl(seq(n + 1))
Lags.starts    :  lagCheck,  walkCheck,  Lags,  1 ≤ E,  FrameStart(fm 1)   →   ∀ n ∈ [ix 1, ix E],  FrameStart(seq n)
Lags.lagStart  :  the same   →   FrameStart(seq n) for a frame not counted          (the old field lags.start)
Pipe.startE    :  lagCheck,  walkCheck,  FrameStart(fm 1)   →   FrameStart(fm E)       (the old field Pipe.start)
Run.pipeStart₁ :  title_check,  title_ctl_check   →   FrameStart(pipe.fm 1)              (with the fields title and pipeAt of Run)
```

`walkCheck` and `titleCheck` are checks on the ROM, by `native_decide` in the private `walk_check` and `title_ctl_check` (about 4 s together in the proof build).
`lagCheck` is the check of [Frames not counted, up to the pipe](a-5-5-3-LagFrames.md), in the private `lag_check`.
The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`. `#print axioms route_1_1` shows no `sorryAx`.

Lean: `Theorems/StartRun.lean`; `Lags`, `Lags.known_end`, `Lags.starts`, `Lags.lagStart`, `Lags.startE` in `Theorems/PipeFrames.lean`; `Pipe.one_le`, `Pipe.startE`, `Pipe.reads`,
`Run.pipeStart₁` in `Theorems/Route.lean`; `rule_on_frameS` in `Theorems/PipeWrites.lean`; private `Proof/StartRun.lean`.

## How it works

* **One whole frame.** The walk is the one of `FrameKeep` ([part f](f-6-19-FrameKeep.md)): the abstract machine of `TaintRun` follows a frame from `FrameStart`, under `CleanK` on each
  instruction, and every path ends at the start of the next frame (the idle loop, its stack pointer, a window of the dot, the NMI on, the strobe off). The bytes of `G.known` at the end are
  not known to the walk. They come from `ctl` at the end of a counted frame, from `game` at the end of a frame not counted that calls the mode's routine, and from the check of
  `LagFrames` at the end of one that does not (`Lags.known_end`). The last needs that the frame starts in control, so the induction asks the known bytes at the end of frame `n`
  only when frame `n` starts so (`starts_dep`). Here the walk has the guard of `PipeWrites` (`guardOf`), no bit watched and no place of the move routine (`walkCheck`), so its
  condition on one instruction is `Clean` itself. 641,723 steps, 65,610 forks, 0 failures, a table of 43,259 states; the search 1.5 s and the check 2.2 s natively.
* **The frames not counted.** The walk does not know the pause byte. So a paused frame is one of its paths. The induction goes over every frame of `seq`
  from `ix 1` to `ix E`, counted or not.
* **The machine at control.** `TitleStart` proves that frame 0 begins in a near or held state of its set. `titleCheck` (`TitleStart.frame0Check`) walks frame 0 from
  these states again with any input, Start included, and asks that each end with control is the start of a frame. `Run.pipeStart₁` reads it on `pipe.fm 1` through `pipeAt`.
* **`one_le`.** `fm 0` is no machine of the run, so the entering frame must be frame 1 or later. This is a new field, `1 ≤ E`.

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
  A frame not counted that calls the mode's routine is asked to end in control in `lags.game`; one that does not call it ends in control by the check.
* **`lags.clean`**: each instruction of these frames is `Clean`. It is the same kind of condition as `chg.upClean₁` (part b) on the same frames, with fewer bytes protected,
  and as `FrameKeep.Frames.clean` above ground.
* **`lags.game`** ([Frames not counted, up to the pipe](a-5-5-3-LagFrames.md)), now with "it ends in control".
* `lags.store` is no longer assumed: the check of `LagFrames` proves it.
* **`one_le`**: `1 ≤ E`.
* **Not in this item.** `pipeAt` (`pipe.fm 1 = chg.seq 1`, part 0) is used by `Run.pipeStart₁`.

`StartRun.starts` and `Begin.start₁` are general in the guard. Part b's `Run.upStart₁` does the same induction on `chg.seq` inside `EntryKeep`; the two can share one lemma.

**Files.** `Theorems/StartRun.lean`, `Theorems/PipeFrames.lean`, `Theorems/Route.lean`, `Theorems/PipeWrites.lean`, private `Proof/StartRun.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta start-check FM2 240    # the two checks, then the fields on real frames, about 4 minutes
```
