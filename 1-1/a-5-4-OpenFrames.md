[← Back](README.md) | [English](a-5-4-OpenFrames.md) | [Japanese](a-5-4-OpenFrames-ja.md)

# The opening on real frames

**Claim.** The bounds of the opening on the real frames are no longer fields of `Route.Pipe`.

* `openP` (the position up to frame `N` is at most `P₀ + D`) is not needed. The position at control is `P₀`, read from the press of Start on the title (`Run.pipePos`). Up to
  frame `N` each frame moves at most `16·v_top`. An entry at a frame `E ≤ N` would be left of the pipe (`PipeFrames.no_entry_of_start`).
* `openB` (the position at the end of frame `N` is at most `P₀ + D`) is a theorem (`Run.pipeOpenB`). It comes from a condition on each of the first `N` frames: the frame is a step
  of the model of [The opening](a-3-Opening.md) (the new field `opening`).

`N = 32`, `D = 9744` (in 1/256 px), `v_top` is the running top speed (2.5 px/frame). `fm(t)` is the machine when the counted frame `t` begins, `hs(t) = startHS(fm t)` its
horizontal state (the speed, the subspeed, the facing and moving directions, the running speed), `P(t)` its position, `v(s)` the signed speed of a state `s`. `E` is the frame that
enters. `fr(t)` is the `Frame` of frame `t` ([The frames up to the pipe](a-5-5-PipeFrames.md)). `lens(|v|) = (L_tap, L_hold)`: the lengths of a jump from its start to its landing
frame, for a one-frame A and a held A, measured on the emulator for each speed at the takeoff.

```
OpenRun(air)  :  air(1) = 0,  and for each t ∈ [1, N] with t < E,  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(t + 1) = hstep(hs t, i)  ∧  P(t + 1) = P(t) + 16·v(hs(t + 1))
valid(r, i)   :=  (r = 0  ∧  i starts on the ground)  ∨  (r > 0  ∧  i starts in the air, with no jump start)
modes         :=  on the ground with a jump start: [L_tap(|v|) − 1, L_hold(|v|) − 1];  on the ground: {0};  in the air: {r − 1}

OpenRun.reach      :  OpenRun,  hs(1) = startHS(m₀)   →   ∀ k ≤ N,  1 + k ≤ E  →  Reach(start, k, ((hs(1 + k), air(1 + k)), P(1 + k) − P(1)))
OpenRun.endB       :  OpenRun,  hs(1) = startHS(m₀),  (∀ k ≤ N,  Reach(start, k, u)  →  dist(u) ≤ D),  N < E   →   P(N + 1) ≤ P(1) + D
OpenRun.openB      :  the same,  Reads,  P(1) = P(m₀),  1 ≤ N   →   N < E  →  fr(N).P' ≤ P(m₀) + D

no_entry_of_start  :  16 ≤ v_top,  1 ≤ N,  2·N ≤ T,  (∀ t, Enter t → L ≤ fr(t).P₂),  fr(1).P ≤ B,  (N < E → fr(N).P' ≤ B),
                      Reads,  v(fm 1) = 0,  B + 16·v_top·(T − N) < L,  Enter E,  1 ≤ E   →   T < E
Run.pipeP1         :  fr(1).P = P(m₀)                            (title_check, title_pos_check, and the checks of the frames)
Run.pipeHS         :  hs(1) = startHS(m₀)                        (title_check, title_pos_check)
Run.pipeOpenB      :  N < E  →  fr(N).P' ≤ P(m₀) + D             (from opening and the private opening)
```

`Reach(start, k, u)` is the model of `Opening` (`Cert.Reach` of `Opening.succ`). The bound `∀ k ≤ 32, Reach(start, k, u) → dist(u) ≤ 9744` is the private `opening`
(a search, about 4 s). `title_pos_check` is a check on the ROM in the private `Proof/LagPause.lean` (about 1.6 s natively).
The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenFrames.lean`; `no_entry_of_start`, `pos_le` in `Theorems/PipeFrames.lean`; `titlePosCheck`, `Begin.pos₁`, `Begin.hs₁` in `Theorems/StartRun.lean`;
`Pipe.opening`, `Run.pipePos`, `Run.pipeHS`, `Run.pipeP1`, `Run.pipeOpenB` in `Theorems/Route.lean`; private `Proof/LagPause.lean`, `Proof/Opening.lean`, `Proof/PipeWrites.lean`.

## How it works

* **What the frames give alone.** `Frame` and the speed 0 at control bound the end of frame 32 by `P₀ + 16·v_top·32 = P₀ + 20480`. With the bound of one frame's gain
  (`V' ≤ max(V, 0) + a_max`, `a_max = 456` in 1/256 of the speed's unit) the bound is `P₀ + 14528`. The opening needs `P₀ + 9744`. So `openB` does not follow from `Frame`: it
  needs the model of the opening (the ground's caps without B, the jump lengths).
* **`openP`.** If `E ≤ N`: `fr(E).P₂ ≤ fr(E).P + 16·v_top ≤ P(1) + 16·v_top·E` (`pos_le`), and `P(1) = P₀`. With `2·N ≤ T` this is at most
  `P₀ + D + 16·v_top·(T − N) < L`, so he cannot enter. If `E > N`, the bound at the end of frame `N` is used as before.
* **`openB`.** By induction on `k`: the state of the counted frame `1 + k` is reached by the model in `k` steps (`OpenRun.reach`). The step from frame `t` to `t + 1` is a successor of
  `Opening.succ`, by the field `step`. The start is `start(m₀)`, since `hs(1) = startHS(m₀)` and `air(1) = 0`. The model's distance is `P(t) − P(1)`. The private `opening` bounds it
  by `D` for `k = N`.
* **The state at control.** `title_pos_check` walks frame 0 from every near state of the title's set, with any input, as `title_ctl_check` does. At each end with control it asks
  that the 3 bytes of the position and the 5 bytes of the horizontal state are known, with the values of `m₀`.

## Checked on real frames

A program (`open-frames-check`). From the machine at control it runs the first 32 counted frames (the frames on which the interval timer does not move are skipped). `air(t)` is read
from `Player_State`: 0 on the ground, else the frames up to the first frame that begins on the ground. For each frame it searches an input `i` of `inputsN` with the four conditions of `step`.

| run | frames | jump starts | not a step of the model | `P(33) − P(1)` |
|---|---|---|---|---|
| the TAS | 32 | 2 | 0 | 9744 |
| own inputs from control, with Start (300) | 9,600 | 580 | 0 | at most 8448 |

* On the TAS the horizontal state at control is that of `m₀`, and the position is `P₀` (also `lag-pause-check`).

## Assumed (not proved in Lean)

* **`opening`**: each of the first 32 counted frames is a step of the model. This is a condition on single frames. It holds what [The opening](a-3-Opening.md) assumed of its
  model: open flat ground, in the air only during a jump (item 1-1-a-5-6); the length of a jump depends only on the speed at the takeoff and lies between `L_tap` and `L_hold`
  (item 1-1-a-5-7); the horizontal part of a frame is `hstep`, and the position moves by `16·v` (no wall, no screen's edge). The frames not counted between two counted frames
  (pauses) are inside the step.
* **Not proved:** that frame 368 is reached (as before).

**Files.** `Theorems/OpenFrames.lean`, `Theorems/PipeFrames.lean`, `Theorems/StartRun.lean`, `Theorems/Route.lean`, private `Proof/LagPause.lean`, `Proof/Opening.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-frames-check FM2 300    # the first 32 frames as steps of the model, on the TAS and own inputs, about 30 s
.lake/build/bin/smbrta open-check 32 9744           # the bound of the model (true)
```
