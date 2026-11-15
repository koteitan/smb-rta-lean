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
landing frame, for a one-frame A and a held A, measured on the emulator for each speed at the takeoff. `Zb = 128` is above every length. `V(m)` are the height, its high byte, the vertical speed and its fraction,
`Q` the return of the collision routine in the player's routine, and `GroundAt(m)` says that `V(m)` is that of the ground: the height of `m₀`, 1, 0, 0. `VS(m)` are the
vertical bytes of `vstep`, `hi(m)` the high byte of the height, `a(t)` A of the counted frame `t` as the player's routine reads it, `vstepO` and `ground0` the opening's
vertical model of [The jumps of the opening](a-5-7-OpenJump.md).

```
OpenRun(air)  :  air(1) = 0,  and for each t ∈ [1, N] with t < E,  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(fm(t + 1)) = hstep(hs(fm t), i)  ∧  P(fm(t + 1)) = P(fm t) + 16·v(hs(fm(t + 1)))
OpenRunM(air) :  OpenRun(air), with  (P(fm(t + 1)) − P(fm t) − 16·v(hs(fm(t + 1)))) mod 2²⁴ = 0  in place of the move

Real  (for each t ∈ [1, N] with t < E):
  cleanK    :  ∀ k,  CleanK_E(tr(t, k))                   (PipeWrites.Clean, with the castle flag, the position's fraction, the pause byte, the area's type, the
                                                          swimming flag, the change of size, A and B, A and B of the frame before, the moving direction, the
                                                          running speed and the stored speed protected, but the move routine's own store: FrameKeep.guardE)
  noStore   :  ∀ k,  no store to the routine, the mode or the task by address at tr(t, k)
  after     :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = PlayerSubs  →  the 8 bytes of hs and P of b(t) are those of tr(t, k),  ab(b t) = |v(b t)|,  bits(b t) = FF
  afterV    :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = Q  →  the 11 bytes of vsA of b(t) are those of tr(t, k)
                                                          (from the return Q of the collision routine on, the height, its high byte, the vertical speed and its
                                                          fraction, the height's fraction, the two forces, the jump's origin, the state, A and B and the halt value
                                                          do not change)
and once:
  page      :  N < E  →  page(fm(N + 1)) ≠ 255
and on each instruction of each frame n, counted or not, with 1 ≤ n ≤ ix(N), n < ix(E)  (OpenMap):
  map       :  MapOK(tr_n(k))                             (no store through an index or a pointer to the player's state, the jumpspring byte, the block buffers
                                                          or the flag that disables the collision routine; the read of the block buffer routine is in the first
                                                          buffer)

Real.stSpring :  the checks,  Real,  FrameStart(seq 1),  MapAt(seq 1)   →   st(fm t) ∈ {0, 1, 2}  ∧  JumpspringAnimCtrl(fm t) = 0     (the old fields st, spring)
Real.flat     :  the checks,  Real,  FrameStart(seq 1),  MapAt(seq 1),  Held(fm t),  ground(t),  GroundAt(fm t),  ¬jump(in t)
                 →   ground(t + 1)  ∧  GroundAt(fm(t + 1))                                                (the old field flat; OpenFlat)
Real.vertOK   :  the checks,  Real,  Held,  StSpring,  PrevOK(fm 1)   →   VertOK: each takeoff or frame in the air up to N is a step of vstepO   (the old field vert;
                                                                                                          OpenAir, a-5-7-2)
Real.jumpV    :  the checks,  VertOK,  t ∈ [1, N],  t < E,  Held(fm t),  |v(fm t)| ≤ top,  ground(t),  GroundAt(fm t),  jump(in t)
                 →   (∃ n ≥ 1,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  ¬ground(t + d) for 1 ≤ d < n,  ground(t + n),  GroundAt(fm(t + n)))
                     ∨  (¬ground(t + d) for t + d ≤ H  ∧  H − t < L_hold)                        (the old field jump; OpenJump)
Real.ground_all: the checks,  Real,  Held(fm t), StSpring, |v(fm t)| ≤ top for each t,  ground(1),  GroundAt(fm 1)   →   ground(t)  →  GroundAt(fm t)
                                                                                                          (the old field ground; OpenFlat, OpenJump)

air(t)        :=  airT(t):  0 on the ground;  after a takeoff at t − 1:  j − t  if the first counted frame j on the ground comes by H = min(N + 1, E),
                  else  max(L_tap − 1, H − t);  in the air after the air:  air(t − 1) − 1
Held(m)       :=  ab(m) = |v(m)|  ∧  bits(m) = FF  ∧  AreaType(m) = v₀  ∧  SwimmingFlag(m) = 0  ∧  PlayerChangeSizeFlag(m) = 0

hopt           :  ∀ k ≤ N,  Reach(start, k, u)  →  dist(u) ≤ D                   (Opening, private opening)
hlow           :  ∀ k < N,  Reach(start, k, u)  →  −P(m₀) ≤ dist(u)              (OpenLeft, private open_left)
htop           :  P(m₀) + D < 2²⁴                                                 (private open_left)

move_mod       :  modelOK,  AtCtrl(tr n₀),  the 8 bytes unchanged up to n₀,  frame(tr n₀) = frame(m),  CleanK.time,  idle loop,  the 8 bytes unchanged from PlayerSubs
                  →   hs(frame m i) = hstep(hs m, readIn(tr n₀))  ∧  (P(frame m i) − P(m) − 16·v(frame m i)) mod 2²⁴ = 0
Real.frame_step:  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t)
                  →   hs(b t) = hstep(hs(fm t), in t)  ∧  (P(b t) − P(fm t) − 16·v(b t)) mod 2²⁴ = 0  ∧  Held(b t)  ∧  st(tr(t, n₀)) = st(fm t)
lags_keepI     :  the frames not counted keep 28 bytes, among them hs, P, ab, bits, st, the area's three bytes, VS, the high byte, A and B of both frames,
                  the halt value                                                                                          (LagFrames)
Real.toRunM    :  lagCheck, walkCheck, pauseCheck,  Checks,  FrameStart(seq 1),  Held(fm 1),  ground(1),  GroundAt(fm 1),  |v(fm t)| ≤ top for t ≤ E,  Real,
                  PrevOK(fm 1)   →   OpenRunM(air)
OpenRunM.next  :  OpenRunM(air),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page,  k < N,  1 + k < E,  Reach(start, k, st(1 + k))
                  →   P(fm(k + 2)) = P(fm(k + 1)) + 16·v(fm(k + 2))  ∧  Reach(start, k + 1, st(k + 2))
OpenRunM.toRun :  OpenRunM(air),  hs(fm 1) = hs(m₀),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page   →   OpenRun(air)
Real.toRun     :  Real.toRunM, then OpenRunM.toRun
Run.pipeHeld   :  Held(fm 1)  ∧  ground(1)  ∧  GroundAt(fm 1)   (title_check, title_pos_check, m₀ holds them: open_checks; the frames before fm 1 keep them: Run.pipeKeep₁)
Run.pipeSpeed  :  ∀ t ∈ [1, E],  |v(fm t)| ≤ top                (PipeFrames.speed_of_reads, from Pipe.reads and Run.still)
Run.pipeOpening:  OpenRun(air)                                 (the field opening, and the checks)
Run.pipeOpenB  :  N < E  →  fr(N).P' ≤ P(m₀) + D              (Run.pipeOpening, and the private opening)
```

`st(t)` is the model's state when the counted frame `t` begins: `((hs(fm t), air(t)), P(fm t) − P(fm 1))`.

`Checks` are checks on the ROM: `modelOK` (the movement), `ctrlCheck` (the walk up to the player's routine), `afterCheck` (the walk of the whole frame, with the area's type
`v₀` of `m₀`), `normIdem`, every length of `lens` below `Zb`, `Held(m₀) ∧ st(m₀) = 0`, that the pause byte the NMI tests is `g`, that the idle loop is a `JMP` to itself,
the walks of a frame on the ground (`OpenFlat.flatCheck`, the private `open_flat_check`, about 3 s natively), `16 ≤ top`, and the search of the jumps of the
opening's vertical model (`OpenJump.arcCheck`, the private `open_jump_check`, about 2.4 s natively). The private
`open_checks` gives them: the first three and the idle loop are those of part e (`pole_numbers`), and the area's type above ground is that of `m₀`; `m₀` is on the ground at
its height (`GroundAt(m₀)`, in `start`). `title_pos_check` also asks the twelve bytes `ab`, `bits`, `st`, the area's three bytes, the four of `V`, A and B and A and B of the frame before at control, with
the values of `m₀` (about 2.2 s natively). `lag_check` now follows 28 bytes (about 7 s natively). The theorems without the ROM use only the axioms `propext`,
`Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenFrames.lean`, `Theorems/OpenLeft.lean`, `Theorems/OpenMap.lean` (`Real.stSpring` uses it), `Theorems/OpenFlat.lean` (`Real.flat` uses it), `Theorems/OpenJump.lean` (`Real.jumpV` uses it); `lags_keepI` in `Theorems/PipeFrames.lean`; `moreI`, `lagI` in `Theorems/LagFrames.lean`; `stI`, `titlePosCheck`, `Begin.bytesAll₁` in
`Theorems/StartRun.lean`; `Pipe.opening`, `Run.pipeKeep₁`, `Run.pipeHeld`, `Run.pipeOpening`, `Run.pipeOpenB` in `Theorems/Route.lean`; private `Proof/OpenFrames.lean` (`open_checks`, `open_left`), `Proof/OpenFlat.lean`,
`Proof/LagPause.lean`, `Proof/Opening.lean`, `Proof/PipeWrites.lean`.

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
  (`CtrlKeep.ctrl_keep`). With the player's state and the jumpspring byte of `Real.stSpring` and `Held` this is `FrameModel.AtCtrl`. The input's state and jump bits come from `st(fm t)`.
* **From frame to frame.** `after` gives `ab` and `bits` at the frame's end; the walk of the whole frame with `cleanK` gives the area's bytes (`SurfaceFrames.area_endF`). The frames
  not counted keep these bytes and `hs`, `P` (`lags_keepI`: the walk of `LagFrames` follows 13 more bytes). So `Held` holds at every counted frame, by induction from control.
* **The air.** `air(t) = 0` exactly when `ground(t)`. In the air, `air(t + 1) = air(t) − 1` by the definition. On the ground with no jump start, `Real.flat` ([The flat ground of the opening](a-5-4-3-4-1-OpenFlat.md)) gives `air(t + 1) = 0`.
  It needs `GroundAt(fm t)`, which holds at every counted frame on the ground (`Real.ground_all`): by induction, from `GroundAt(fm 1)`, `Real.flat` itself, and
  `Real.jumpV` after a landing.
  At a jump start, `Real.jumpV` gives the landing `t + n` by `H`, so `air(t + 1) = n − 1 ∈ [L_tap − 1, L_hold − 1]`, or no landing by `H` and `H − t < L_hold`, so
  `air(t + 1) = max(L_tap − 1, H − t − 1)` is between them too. It comes from `Real.vertOK` and the search of the model's jumps ([The jumps of the opening](a-5-7-OpenJump.md));
  the speed at the takeoff is at most the top speed (`Run.pipeSpeed`). The model's input is `norm(in t)`: it has the same state and jump bits,
  and `hstep` on it is the same (`normIdem`).
* **At control.** `title_pos_check` walks frame 0 from every near state of the title's set, with any input, and asks the position, the horizontal state and the twelve bytes of
  `stI` known with the values of `m₀` at each end with control.

## Checked on real frames

A program (`open-real-check`). From the machine at control it runs the first 32 counted frames (a frame on which the interval timers' phase does not move is not counted). It
runs each counted frame instruction by instruction and checks each field of `Real`, what the proof derives (`Held` at the frame's start, `keepA` at the player's routine,
`hstep` and `16·v` at the frame's end and at the next counted frame), and that the frames not counted keep the 28 bytes.

| run | counted frames | frames not counted between them | jump starts | a field of `Real` fails | not a step of the model |
|---|---|---|---|---|---|
| the TAS | 32 | 0 | 2 | 0 | 0 |
| own inputs from control, with Start (300) | 9,600 | 9,600 | 528 | 0 | 0 |
| a pause on one of the first 4 frames in control for 43 to 82 frames, then the TAS's inputs (60; 58 unpause) | 1,856 | 5,814 | 116 | 0 | 0 |

* On the TAS the 12 bytes of `stI`, the position and the horizontal state at control are those of `m₀`.
* The step of the vertical model (`VStep`) is checked on every counted frame in the air or with a jump up to `N`; `afterV` with its 11 bytes, `noStore` and `CleanK` of
  `guardE` on every counted frame; and the relations that the proof derives at each counted frame's start (A and B of the frame before, the halt relation, the collision
  flag 0). The numbers are on [The vertical model on real frames](a-5-7-2-OpenAir.md).
* **`far` of part e is false here**: the own runs that press A with B and Left on their first frame and hold B and Left after begin the counted frame 33 at `P = 320`
  (1.25 px), with no edge of the screen. `page` holds on all of them.
* **Start on the first frame in control**: that frame ends paused and the timers' phase does not move, so the clock does not count it. Before round 12 `PipeFrames.Lags`
  made frame 1 of the run the counted frame 1, so on such a run `unpaused` failed at `t = 1` and the run was not covered. Now the counted frames are read from the pause byte
  (`PipeFrames.ixP`, [LagPause](a-5-5-3-3-LagPause.md)): the counted frame 1 is the first frame from frame 1 on that ends not paused, and the state at control is carried to it
  (`Run.pipeKeep₁`). The runs of the third row pause on the first frames; the frames before their counted frame 1 keep the 28 bytes. On these runs the program also runs
  every frame up to the counted frame 32 instruction by instruction (7,728 frames): each instruction is `Clean` (`lags.clean`), and no frame not counted stores to the pause
  byte through an index or a pointer (`lags.keeps`, which now also covers the frames before the counted frame 1).
* On every frame of these runs, up to the first frame that ends out of control, the timers' phase moves exactly when the frame ends not paused (81,931 frames, no exception).
  13 runs of the third row leave control later (a death: the resumed inputs no longer fit the game); after that, frames that are not counted end not paused. Such a run is
  outside the theorem (`lags.ctl`).

## Assumed (not proved in Lean)

* The fields of `Real`: `cleanK`, `noStore`, `map`, `after`, `afterV`, and `page` at the start of the counted frame `N + 1` only. They are conditions on single frames,
  on their instructions and on their starts. `after` says that from the scroll handler on nothing moves him and the collision routine finds nothing (no wall, no edge of
  the screen): the horizontal half of item 1-1-a-5-6. `afterV` says that from the return of the collision routine on the 11 bytes of the vertical model do not change.
* Round 13: `vert` is no longer assumed ([The vertical model on real frames](a-5-7-2-OpenAir.md), `Real.vertOK`), nor asked after the counted frame `N`. New:
  `noStore`. Wider: `cleanK` (`guardE`: 5 more protected bytes), `afterV` (11 bytes, it asked 4), `map` (the collision flag protected too).
* No longer assumed (round 12): `ground` (`Real.ground_all`: at the counted frame 1 from the title, after a counted frame on the ground with no jump by the walks of
  [The flat ground of the opening](a-5-4-3-4-1-OpenFlat.md), after a landing by `Real.jumpV`). The walk up to the return of the collision routine checks `V` there; the
  walk after it cannot follow `V`, hence the new field `afterV`.
* No longer assumed (round 12): `jump` (item 1-1-a-5-7, a condition on many frames). It is a theorem (`Real.jumpV`) from `Real.vertOK` and the
  search of every jump of the model (`OpenJump.lands`).
* No longer assumed (round 11): `flat` (he does not fall off the ground). It is a theorem (`Real.flat`) from the walks of
  [The flat ground of the opening](a-5-4-3-4-1-OpenFlat.md) and the new field `ground`. The read of `map` is asked to be in the first block buffer, and `map` covers the
  frame of the counted frame `N` too.
* No longer assumed (earlier rounds): `longer`, and `page` at the starts of the counted frames 1 to `N`.
* No longer assumed (earlier rounds): `st` and `spring`. They are a theorem (`Real.stSpring`) from the walk of
  [The block buffers, the jumpspring and the player's state on the first frames](a-5-4-3-3-3-OpenMap.md), with the new field `map` on each instruction. `spare` is now
  part of `cleanK` (the bytes it protects are protected by the guard of `cleanK`, `FrameKeep.guardF`, as part f did).
* No longer assumed: that each frame is a step of the model (`hstep`, the move by `16·v`, the input of the model, `valid`), and the sequence `air`. That each counted frame
  ends not paused is a theorem (`PipeFrames.Lags.unpaused`): the counted frames are the frames that end not paused, found within `dP` frames (`lags.resume`).
* **Not proved:** that frame 368 is reached (as before).

**Files.** `Theorems/OpenFrames.lean`, `Theorems/OpenLeft.lean`, `Theorems/OpenMap.lean`, `Theorems/OpenFlat.lean`, `Theorems/OpenJump.lean`, `Theorems/PipeFrames.lean`, `Theorems/LagFrames.lean`, `Theorems/StartRun.lean`, `Theorems/Route.lean`, private `Proof/OpenFrames.lean`,
`Proof/OpenFlat.lean`, `Proof/LagPause.lean`, `Proof/Opening.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-real-check FM2 300      # the fields of Real on the TAS and own inputs, the title's check and the walks of the frames not counted, about 1 min
.lake/build/bin/smbrta open-frames-check FM2 300    # the first 32 frames as steps of the model
.lake/build/bin/smbrta open-check 32 9744           # the bound of the model (true)
.lake/build/bin/smbrta open-left-check 31 10240     # the bound of the model to the left (true)
```
