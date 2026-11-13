[← Back](README.md) | [English](a-5-4-OpenFrames.md) | [Japanese](a-5-4-OpenFrames-ja.md)

# The opening on real frames

**Claim.** The bounds of the opening on the real frames are no longer fields of `Route.Pipe`. That each of the first 32 counted frames is a step of the opening's model is a
theorem too, from conditions on single frames, on their instructions and on their starts (the field `opening`, `OpenFrames.Real`).

* `openP` (the position up to frame `N` is at most `P₀ + D`) is not needed. The position at control is `P₀`, read from the press of Start on the title (`Run.pipePos`). Up to
  frame `N` each frame moves at most `16·v_top`. An entry at a frame `E ≤ N` would be left of the pipe (`PipeFrames.no_entry_of_start`).
* `openB` (the position at the end of frame `N` is at most `P₀ + D`) is a theorem (`Run.pipeOpenB`). It comes from each of the first `N` frames being a step of the model of
  [The opening](a-3-Opening.md) (`OpenRun`).
* `OpenRun` (each frame is a step of the model) is a theorem (`OpenFrames.Real.toRun`, `Run.pipeOpening`). The horizontal part (`hstep`, the move by `16·v`) is the
  movement of a real frame (`FrameModel.move_model`, proved by walks of two machines). The state at the player's routine is the walk of `CtrlKeep`. The input of the model is
  the one the player's routine reads. The frames left in the air are read from the player's state. What stays assumed is in `Real`.
* `longer` (the frame does not end during the movement) is a theorem: the walk's frame ends after the movement, since each instruction meets `CleanK.time`
  (`FrameModel.trace_inFrame`, as part e did).
* `page` was asked at the start of every counted frame from 1 to `N + 1`. Now it is asked only at the start of the counted frame `N + 1`. At the ends of the frames before,
  the position is exact by two searches on the model: [the opening](a-3-Opening.md) bounds it on the right, [the opening to the left](a-5-4-3-3-2-OpenLeft.md) on the left.

`N = 32`, `D = 9744` (in 1/256 px), `v_top` is the running top speed (2.5 px/frame). `fm(t)` is the machine when the counted frame `t` begins and `inp(t)` its input,
`b(t) = frame(fm t, inp t)` the machine at its end, `tr(t, k)` the machine after `k` of its instructions. `n₀(t) = arrAt(fm t, inp t)` is the instruction at which the frame
first comes to the player's routine, and `in(t) = readIn(tr(t, n₀(t)))` the input that the routine reads. `hs(m) = startHS(m)` is the horizontal state (the speed, the
subspeed, the facing and moving directions, the running speed), `P(m)` the position, `v(m)` the signed speed, `st(m)` the player's state, `ab(m)` the stored speed and
`bits(m)` the collision bits. `ground(t)` is `st(fm t) = 0`. `E` is the frame that enters. `lens(|v|) = (L_tap, L_hold)` are the lengths of a jump from its start to its
landing frame, for a one-frame A and a held A, measured on the emulator for each speed at the takeoff. `Zb = 128` is above every length.

```
OpenRun(air)  :  air(1) = 0,  and for each t ∈ [1, N] with t < E,  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(fm(t + 1)) = hstep(hs(fm t), i)  ∧  P(fm(t + 1)) = P(fm t) + 16·v(hs(fm(t + 1)))
OpenRunM(air) :  OpenRun(air), with  (P(fm(t + 1)) − P(fm t) − 16·v(hs(fm(t + 1)))) mod 2²⁴ = 0  in place of the move

Real  (for each t ∈ [1, N] with t < E):
  cleanK    :  ∀ k,  CleanK(tr(t, k))                     (PipeWrites.Clean, with the castle flag and the position's fraction protected, but the move routine's own store)
  spare     :  ∀ k,  Spare(tr(t, k))                      (no store through an index or a pointer to the pause byte, the area's type, the swimming flag, the change of size)
  st        :  st(fm t) ∈ {0, 1, 2}
  spring    :  JumpspringAnimCtrl(fm t) = 0
  after     :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = PlayerSubs  →  the 8 bytes of hs and P of b(t) are those of tr(t, k),  ab(b t) = |v(b t)|,  bits(b t) = FF
  flat      :  ground(t)  ∧  ¬jump(in t)   →   ground(t + 1)
  jump      :  ground(t)  ∧  jump(in t)    →   ∃ n ≥ 1,  L_tap(|v(fm t)|) ≤ n ≤ L_hold(|v(fm t)|),  ¬ground(t + d) for 1 ≤ d < n,  ground(t + n)
and once:
  page      :  N < E  →  page(fm(N + 1)) ≠ 255

air(t)        :=  j − t,   j the first counted frame in [t, N + Zb) with ground(j),  else  N + Zb
Held(m)       :=  ab(m) = |v(m)|  ∧  bits(m) = FF  ∧  AreaType(m) = v₀  ∧  SwimmingFlag(m) = 0  ∧  PlayerChangeSizeFlag(m) = 0

hopt           :  ∀ k ≤ N,  Reach(start, k, u)  →  dist(u) ≤ D                   (Opening, private opening)
hlow           :  ∀ k < N,  Reach(start, k, u)  →  −P(m₀) ≤ dist(u)              (OpenLeft, private open_left)
htop           :  P(m₀) + D < 2²⁴                                                 (private open_left)

move_mod       :  modelOK,  AtCtrl(tr n₀),  the 8 bytes unchanged up to n₀,  frame(tr n₀) = frame(m),  CleanK.time,  idle loop,  the 8 bytes unchanged from PlayerSubs
                  →   hs(frame m i) = hstep(hs m, readIn(tr n₀))  ∧  (P(frame m i) − P(m) − 16·v(frame m i)) mod 2²⁴ = 0
Real.frame_step:  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t)
                  →   hs(b t) = hstep(hs(fm t), in t)  ∧  (P(b t) − P(fm t) − 16·v(b t)) mod 2²⁴ = 0  ∧  Held(b t)  ∧  st(tr(t, n₀)) = st(fm t)
lags_keepI     :  the frames not counted keep 17 bytes, among them hs, P, ab, bits, st, the area's three bytes      (LagFrames)
Real.toRunM    :  lagCheck, walkCheck, pauseCheck,  Checks,  FrameStart(seq 1),  Held(fm 1),  ground(1),  Real   →   OpenRunM(air)
OpenRunM.next  :  OpenRunM(air),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page,  k < N,  1 + k < E,  Reach(start, k, st(1 + k))
                  →   P(fm(k + 2)) = P(fm(k + 1)) + 16·v(fm(k + 2))  ∧  Reach(start, k + 1, st(k + 2))
OpenRunM.toRun :  OpenRunM(air),  hs(fm 1) = hs(m₀),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page   →   OpenRun(air)
Real.toRun     :  Real.toRunM, then OpenRunM.toRun
Run.pipeHeld   :  Held(fm 1)  ∧  ground(1)                     (title_check, title_pos_check, m₀ holds them: open_checks; the frames before fm 1 keep them: Run.pipeKeep₁)
Run.pipeOpening:  OpenRun(air)                                 (the field opening, and the checks)
Run.pipeOpenB  :  N < E  →  fr(N).P' ≤ P(m₀) + D              (Run.pipeOpening, and the private opening)
```

`st(t)` is the model's state when the counted frame `t` begins: `((hs(fm t), air(t)), P(fm t) − P(fm 1))`.

`Checks` are checks on the ROM: `modelOK` (the movement), `ctrlCheck` (the walk up to the player's routine), `afterCheck` (the walk of the whole frame, with the area's type
`v₀` of `m₀`), `normIdem`, every length of `lens` below `Zb`, `Held(m₀) ∧ st(m₀) = 0`, that the pause byte the NMI tests is `g`, and that the idle loop is a `JMP` to itself. The private
`open_checks` gives them: the first three and the idle loop are those of part e (`pole_numbers`), and the area's type above ground is that of `m₀`. `title_pos_check` now also asks the six bytes `ab`, `bits`, `st` and the area's three bytes at control, with
the values of `m₀` (about 2.2 s natively). `lag_check` now follows 17 bytes (about 6 s natively). The theorems without the ROM use only the axioms `propext`,
`Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenFrames.lean`, `Theorems/OpenLeft.lean`; `lags_keepI` in `Theorems/PipeFrames.lean`; `moreI`, `lagI` in `Theorems/LagFrames.lean`; `stI`, `titlePosCheck`, `Begin.bytesAll₁` in
`Theorems/StartRun.lean`; `Pipe.opening`, `Run.pipeKeep₁`, `Run.pipeHeld`, `Run.pipeOpening`, `Run.pipeOpenB` in `Theorems/Route.lean`; private `Proof/OpenFrames.lean` (`open_checks`, `open_left`), `Proof/LagPause.lean`,
`Proof/Opening.lean`, `Proof/PipeWrites.lean`.

## How it works

* **The movement.** `FrameModel.move_model`: from the player's routine to the scroll handler, the horizontal state follows `hstep` on the input read there, and `P` moves by
  `16·v` modulo `2²⁴` (`move_mod`). The frame does not end during the movement: the routine comes in the frame's own frame (`CtrlKeep.arrive_at`), every instruction
  but the idle loop runs at a dot at most `dotsPerFrame − 64` (`CleanK.time`), and the idle loop is a `JMP` to itself, so `FrameModel.trace_inFrame` follows the walk's steps
  inside the frame. This was the field `longer`.
* **The exact position.** Part e asks `2048 ≤ P` here (`far`); that is false on real frames of the opening that walk left (see below). Instead, by induction on the counted
  frames, the state when the counted frame `1 + k` begins is reached by the model in `k` steps from the start (`OpenRunM.reachAll`). The model's next state `u'` is reached
  in `k + 1` steps, and `P(fm(1 + k)) + 16·v' = P(m₀) + dist(u')`. For `k + 1 < N` the two searches put this in `[0, P(m₀) + D] ⊂ [0, 2²⁴)`, so the move is exact
  (`exact_of_mod`). For `k + 1 = N` the right bound still holds; if the sum were below 0, the position at the end would be `P + 16·v' + 2²⁴ ≥ 2²⁴ − 2048`, on page 255,
  which `page` excludes (`exact_of_page`).
* **The state at the player's routine.** The frame starts in the idle loop in control (`Lags.starts`; the guard of the walks of `CtrlKeep` has the same idle loop, stack
  pointer and known bytes). It ends not paused (`Lags.unpaused`: a counted frame is a frame that ends not paused), so it comes to the player's routine (`CtrlKeep.arrive_at`), and there the 25 bytes of `keepA` are those of its start
  (`CtrlKeep.ctrl_keep`). With `st`, `spring` and `Held` this is `FrameModel.AtCtrl`. The input's state and jump bits come from `st(fm t)`.
* **From frame to frame.** `after` gives `ab` and `bits` at the frame's end; the walk of the whole frame with `spare` gives the area's bytes (`CtrlKeep.area_end`). The frames
  not counted keep these bytes and `hs`, `P` (`lags_keepI`: the walk of `LagFrames` follows 9 more bytes). So `Held` holds at every counted frame, by induction from control.
* **The air.** `air(t) = 0` exactly when `ground(t)`. In the air, `air(t + 1) = air(t) − 1` by the definition. On the ground with no jump start, `flat` gives `air(t + 1) = 0`.
  At a jump start, `jump` gives the landing `t + n`, so `air(t + 1) = n − 1 ∈ [L_tap − 1, L_hold − 1]`. The model's input is `norm(in t)`: it has the same state and jump bits,
  and `hstep` on it is the same (`normIdem`).
* **At control.** `title_pos_check` walks frame 0 from every near state of the title's set, with any input, and asks the position, the horizontal state and the six bytes of
  `stI` known with the values of `m₀` at each end with control.

## Checked on real frames

A program (`open-real-check`). From the machine at control it runs the first 32 counted frames (a frame on which the interval timers' phase does not move is not counted). It
runs each counted frame instruction by instruction and checks each field of `Real`, what the proof derives (`Held` at the frame's start, `keepA` at the player's routine,
`hstep` and `16·v` at the frame's end and at the next counted frame), and that the frames not counted keep the 17 bytes.

| run | counted frames | frames not counted between them | jump starts | a field of `Real` fails | not a step of the model |
|---|---|---|---|---|---|
| the TAS | 32 | 0 | 2 | 0 | 0 |
| own inputs from control, with Start (300) | 9,600 | 9,600 | 528 | 0 | 0 |
| a pause on one of the first 4 frames in control for 43 to 82 frames, then the TAS's inputs (60; 58 unpause) | 1,856 | 5,814 | 116 | 0 | 0 |

* On the TAS the 6 bytes of `stI`, the position and the horizontal state at control are those of `m₀`.
* **`far` of part e is false here**: the own runs that press A with B and Left on their first frame and hold B and Left after begin the counted frame 33 at `P = 320`
  (1.25 px), with no edge of the screen. `page` holds on all of them.
* **Start on the first frame in control**: that frame ends paused and the timers' phase does not move, so the clock does not count it. Before this round `PipeFrames.Lags`
  made frame 1 of the run the counted frame 1, so on such a run `unpaused` failed at `t = 1` and the run was not covered. Now the counted frames are read from the pause byte
  (`PipeFrames.ixP`, [LagPause](a-5-5-3-3-LagPause.md)): the counted frame 1 is the first frame from frame 1 on that ends not paused, and the state at control is carried to it
  (`Run.pipeKeep₁`). The runs of the third row pause on the first frames; the frames before their counted frame 1 keep the 17 bytes. On these runs the program also runs
  every frame up to the counted frame 32 instruction by instruction (7,728 frames): each instruction is `Clean` (`lags.clean`), and no frame not counted stores to the pause
  byte through an index or a pointer (`lags.keeps`, which now also covers the frames before the counted frame 1).
* On every frame of these runs, up to the first frame that ends out of control, the timers' phase moves exactly when the frame ends not paused (81,931 frames, no exception).
  13 runs of the third row leave control later (a death: the resumed inputs no longer fit the game); after that, frames that are not counted end not paused. Such a run is
  outside the theorem (`lags.ctl`).

## Assumed (not proved in Lean)

* The fields of `Real`: `cleanK`, `spare`, `st`, `spring`, `after`, `flat`, `jump`, and `page` at the start of the counted frame `N + 1` only. They are
  conditions on single frames, on their instructions and on their starts. `after` says that from the scroll handler on nothing moves him and the collision routine finds nothing (no wall, no edge of the screen):
  the horizontal half of item 1-1-a-5-6. `flat` is its vertical half (he does not fall off the ground). `jump` is item 1-1-a-5-7.
* No longer assumed (this round): `longer`, and `page` at the starts of the counted frames 1 to `N`.
* `st` and `spring` depend on the map: the jumpspring byte is set when he lands on a jumpspring tile, the state 3 (climbing) when he touches a climbing tile. A walk of
  the frame that follows either byte cannot know the tiles that the block buffer routine reads. The search that follows the jumpspring byte through the frame (`ctrl-after-check
  spring`) did not end: it was stopped at 21.7 GB of memory after 4 minutes.
* No longer assumed: that each frame is a step of the model (`hstep`, the move by `16·v`, the input of the model, `valid`), and the sequence `air`. That each counted frame
  ends not paused is a theorem (`PipeFrames.Lags.unpaused`): the counted frames are the frames that end not paused, found within `dP` frames (`lags.resume`).
* **Not proved:** that frame 368 is reached (as before).

**Files.** `Theorems/OpenFrames.lean`, `Theorems/OpenLeft.lean`, `Theorems/PipeFrames.lean`, `Theorems/LagFrames.lean`, `Theorems/StartRun.lean`, `Theorems/Route.lean`, private `Proof/OpenFrames.lean`,
`Proof/LagPause.lean`, `Proof/Opening.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-real-check FM2 300      # the fields of Real on the TAS and own inputs, the title's check and the walks of the frames not counted, about 1 min
.lake/build/bin/smbrta open-frames-check FM2 300    # the first 32 frames as steps of the model
.lake/build/bin/smbrta open-check 32 9744           # the bound of the model (true)
.lake/build/bin/smbrta open-left-check 31 10240     # the bound of the model to the left (true)
```
