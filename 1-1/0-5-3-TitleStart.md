[← Back](README.md) | [English](0-5-3-TitleStart.md) | [Japanese](0-5-3-TitleStart-ja.md)

# From Start on the title to control

**Claim.** Take a run from the press of Start on the title screen, with any buttons on every frame, Start included. Assume one condition on the machine after the frame of the press. Then the frame before the first control (frame 0 of the route) begins with the timer at 401, the interval timers' phase at 2 and no hurry-up music, and at control the speed is 0.

**This is a theorem with hypotheses.** They are the fields of `TitleStart.Begin`, all listed below. The condition at the press is one state. It was checked on 339 real runs, not proved for every run. No field asks for no Start: Start is allowed on every frame, frame 0 included. The checks of other files that walk frame 0 to control (`StartRun`, `EntryKeep`, `HurryMusic`) walk it from the near and held states with any input (`frame0Check`, `Begin.frame0`).

Before this, `Route.Run` had the field `zero` (timer and phase when frame 0 begins), `Route.Pipe` had `still` (the speed at control), and `HurryMusic.Run` had `zero` and `quiet₀`. They are now theorems: `Route.Run.zero`, `Route.Run.still`, `HurryMusic.Run.zero`, `HurryMusic.Run.quiet₀`.

## What the game does

After the press the game clears RAM and draws the screen "WORLD 1-1". Then it waits until the screen's timer `ScreenTimer` runs out. That timer ticks only when the interval timers' phase goes round (every 21 frames). So the wait ends at the same phase whatever the phase was at the press. Then the level is drawn, the game core runs two frames (the timer is loaded from the level's header), and control comes. From the press to frame 0 there are 153 to 173 frames, by the phase at the press.

Start on a frame of the game core pauses the game (`PauseRoutine`, before the core's routine in the frame). A paused frame runs the sound, reads the pad and the pause routine, and skips the timers, the frame counter and the mode's routine. So the core's two frames, the phase and the timer wait. The pause sound sets `PauseModeFlag`, and then the music does not play. Start again, at least 43 frames later (`GamePauseTimer`), ends the pause; the pause sound plays again for 42 frames. So a pause only delays control: frame 0 comes later, with the same timer, phase and music bytes.

## The theorem

`tm n` is the machine `n` frames after the press, `ti n` its input. `seq`, `inp` are the machines and inputs of the route from frame 0 (`base.seq`, `base.inp`). `x` is the reference machine: from power-on, no button for 39 frames, Start on frame 39, the machine after that frame.

```
Press(m)  :  m is in the idle loop at the start of a frame (the program counter and the stack pointer of x, dot < 10, the NMI as at a frame's start),
             not paused,  and  ∀ i ∈ K,  m[i] = x[i]
K         =  the bytes that the run from x with no input reads before it writes them, up to control,  minus the free bytes,
             and PauseSoundBuffer
free      =  FrameCounter, IntervalTimerControl, PseudoRandomBitReg (7), NumberOfPlayers, TopScoreDisplay (6), the 3 bytes after the scores,
             Timers (36), JoypadBitMask (2), HorizontalScroll, VerticalScroll, SprShuffleAmtOffset, SprDataOffset (15), Mirror_PPU_CTRL_REG1
```

`K` has 53 bytes: the sound's queues and buffers, the head of the screen buffer, the world, level and area, the player's size and status, the timer's flag, the modes and tasks, the pause bytes, the scores. All other bytes are free.

`PauseSoundBuffer` (the pause sound that plays) is new in `K`. The run with no input never reads it, but a run with a pause reads it on the frame after the pause starts. If it were not known, the abstract machine could take a path on which the pause sound never sets `PauseModeFlag`, and then the music would play through a pause of any length: the search would not end. It is 0 on the title screen on every real run: the sound engine clears it at the end of each pause sound, and the power-on and a reset clear it. `GamePauseStatus` was in `K` already; the start states now keep all its bits (before, they kept only bit 0).

The fields of `TitleStart.Begin`:

```
next      tm(n + 1) = frame(tm n, ti n)
press     Press(tm 0)                                                          (one state)
atZero    tm(pre) = seq 0,  ti(pre) = inp 0
first     n ≤ pre  ⟹  ¬ctl(tm n)
ctl       ctl(seq 1)
```

The theorems (`title_check` is the check on the ROM, by `native_decide`):

```
Begin.zero     :  seq 1 = frame(seq 0, inp 0)  ⟹  timer(seq 0) = 401,  phase(seq 0) = 2,  EventMusicQueue = EventMusicBuffer = NoteLengthTblAdder = 0
Begin.timer    :  timer(seq 0) = t0  ∧  phase(seq 0) = 2
Begin.still    :  v(seq 1) = 0
Begin.anyNear  :  seq 0 is in a near or held state,  v(seq 1) = 0                   (any input)
Begin.frame0   :  frame0Check(fin)  ⟹  the end of frame 0 meets fin                  (any input; StartRun, EntryKeep and HurryMusic use it)
Route.Run.zero, Route.Run.still          from Run.title and the theorem Run.pipeAt (pipe.fm 1 = base.seq 1)
HurryMusic.Run.zero, HurryMusic.Run.quiet₀   from Run.title
```

## The proof

An abstract machine follows a set of machines at once: some bits are known, the others not, and a branch on a bit that is not known goes both ways (`TaintRun`, with the tick across the frame's end of `SideChangeEnd`, since the frame of the RAM clear ends in the middle of the routine). A search finds a set of frame-start states that is closed under one frame:

* the start states, from `Press`, are in the set;
* the far states (582): with any input, every end of their frame is a state of the set and has no control;
* the near states (8) and the held states (2): with any input, every end of their frame has control and knows the speed 0, or is a state of the set without control. They know the timer's digits 4, 0, 1, the phase 2 and the three music bytes 0.

The near states are 4 states with no pause, and 4 states just after a pause (`GamePauseStatus` = 128, `GamePauseTimer` = 43: Start does nothing on the next 43 frames). The held states are paused with the routine of the player's entrance: Start ends the pause and gives control on the same frame. With no Start, the frame of a near state ends with control, and that of a held state ends paused, without control (two more walks; no theorem needs them now).

The search is no part of the proof. `check` walks every state of the set and every state of the tables (17,591). It takes about 4 s natively (search 1.8 s, walks 2.5 s). Then by induction each `tm n` with `n ≤ pre` is in the set (`Begin.inSet`), whatever the input: a frame that ends with control before frame 0 is excluded by `first`. `tm pre` is not far, because its frame gives control (`ctl`). So it is near or held (`Begin.anyNear`), and the bytes and the speed follow.

Why the search did not end before: in the previous round, with Start allowed, the set grew past 6,852 states and did not close. The start states knew only bit 0 of `GamePauseStatus` and nothing of `PauseSoundBuffer`. Then a pause could take a path on which `PauseModeFlag` stays 0, and the music played through the pause: each frame of the song gave new states.

## On real runs

`title-check FM2`, exit code 0. The press: Start after 30 to 624 frames of the title (100 runs), A with Start (10 runs), random buttons on the title and random buttons up to control, Start included (200 runs), a pause on the first or the second frame of the game core for 43 to 200 frames, at 8 times of the press (64 runs), the title after a game over, with no input or with pauses on the first 3000 frames of the game (6 runs), a reset every 150 frames of the movie and then Start (12 runs). On frame 0, Start in the game core is taken out when control still comes without it; when Start is needed there (it ends a pause), it stays.

```
runs                                   392
no control within 3000 frames          53   (Start on frame 30, or during the demo; random Start that keeps pausing)
the press meets Press                  339 of 339
frame 0 or control not as the check    0
runs with paused frames before frame 0 117   (up to 200 paused frames)
runs with Start on frame 0             60   (the bytes and the speed are as the check says)
frames from the press to frame 0       153 to 173 with no pause, up to 373 with pauses
the movie's own press                  meets Press; frame 0 has timer 401, phase 2, no music; speed 0 at control
```

## What is not proved

* `press` is a hypothesis on one state. It holds on all 339 runs above. A run in which the title shows another world (A with Start after a game over), or a byte of `K` with another value, is outside. `PauseSoundBuffer` = 0 at the press is part of it: it holds on every real run seen, the 6 runs after a game over among them, but it is not proved from the power-on.
* There was a field `noPause` (no Start on frame 0). It is gone: `StartRun.titleCheck` and `EntryKeep.nearCheck` are now `frame0Check` (every end of frame 0 from the near and held states, with any input, meets their condition or is far), as `HurryMusic.nearCheck` is, and `Begin.frame0` replaces `Begin.near`. Both checks pass in the proof build.
* `atZero`, `first`, `ctl` say which machine is frame 0. They hold by how the sequence is made. `pipeAt` is no longer a field: `pipe` takes its machines from `base`, and its counted frame 1 is frame 1 (`Run.pipeAt`, a theorem).

**Files.** `Theorems/TitleStart.lean`, `Theorems/Route.lean` (`Run.title`, `Run.pipeAt`, `Run.zero`, `Run.still`), `Theorems/HurryMusic.lean`, the private `Proof/TitleStart.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta title-check FM2
```
