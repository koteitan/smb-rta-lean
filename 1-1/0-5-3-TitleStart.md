[← Back](README.md) | [English](0-5-3-TitleStart.md) | [Japanese](0-5-3-TitleStart-ja.md)

# From Start on the title to control

**Claim.** Take a run from the press of Start on the title screen. Assume one condition on the machine after the frame of the press, and no Start on the frames of the game core before control. Then the frame before the first control (frame 0 of the route) begins with the timer at 401, the interval timers' phase at 2 and no hurry-up music, and at control the speed is 0.

**This is a theorem with hypotheses.** They are the fields of `TitleStart.Begin`, all listed below. The condition at the press is one state. It was checked on 301 real runs, not proved for every run.

Before this, `Route.Run` had the field `zero` (timer and phase when frame 0 begins), `Route.Pipe` had `still` (the speed at control), and `HurryMusic.Run` had `zero` and `quiet₀`. They are now theorems: `Route.Run.zero`, `Route.Run.still`, `HurryMusic.Run.zero`, `HurryMusic.Run.quiet₀`.

## What the game does

After the press the game clears RAM and draws the screen "WORLD 1-1". Then it waits until the screen's timer `ScreenTimer` runs out. That timer ticks only when the interval timers' phase goes round (every 21 frames). So the wait ends at the same phase whatever the phase was at the press. Then the level is drawn, the game core runs two frames (the timer is loaded from the level's header), and control comes. From the press to frame 0 there are 153 to 173 frames, by the phase at the press.

## The theorem

`tm n` is the machine `n` frames after the press, `ti n` its input. `seq`, `inp` are the machines and inputs of the route from frame 0 (`chg.seq`, `chg.inp`). `x` is the reference machine: from power-on, no button for 39 frames, Start on frame 39, the machine after that frame.

```
Press(m)  :  m is in the idle loop at the start of a frame (the program counter and the stack pointer of x, dot < 10, the NMI as at a frame's start),
             not paused,  and  ∀ i ∈ K,  m[i] = x[i]
K         =  the bytes that the run from x with no input reads before it writes them, up to control,  minus the free bytes
free      =  FrameCounter, IntervalTimerControl, PseudoRandomBitReg (7), NumberOfPlayers, TopScoreDisplay (6), the 3 bytes after the scores,
             Timers (36), JoypadBitMask (2), HorizontalScroll, VerticalScroll, SprShuffleAmtOffset, SprDataOffset (15), Mirror_PPU_CTRL_REG1
```

`K` has 52 bytes: the sound's queues and buffers, the head of the screen buffer, the world, level and area, the player's size and status, the timer's flag, the modes and tasks, the pause bytes, the scores. All other bytes are free.

The fields of `TitleStart.Begin`:

```
next      tm(n + 1) = frame(tm n, ti n)
press     Press(tm 0)                                                          (one state)
atZero    tm(pre) = seq 0,  ti(pre) = inp 0
noPause   n ≤ pre,  OperMode_Task(tm n) = game core  ⟹  ti n has no Start          (two frames)
first     n ≤ pre  ⟹  ¬ctl(tm n)
ctl       ctl(seq 1)
```

The theorems (`title_check` is the check on the ROM, by `native_decide`):

```
Begin.zero     :  seq 1 = frame(seq 0, inp 0)  ⟹  timer(seq 0) = 401,  phase(seq 0) = 2,  EventMusicQueue = EventMusicBuffer = NoteLengthTblAdder = 0
Begin.timer    :  timer(seq 0) = t0  ∧  phase(seq 0) = 2
Begin.still    :  v(seq 1) = 0
Route.Run.zero, Route.Run.still          from Run.title and Run.pipeAt (pipe.fm 1 = chg.seq 1)
HurryMusic.Run.zero, HurryMusic.Run.quiet₀   from Run.title
```

## The proof

An abstract machine follows a set of machines at once: some bits are known, the others not, and a branch on a bit that is not known goes both ways (`TaintRun`, with the tick across the frame's end of `SideChangeEnd`, since the frame of the RAM clear ends in the middle of the routine). A search finds a set of frame-start states that is closed under one frame:

* the start states, from `Press`, are in the set;
* the far states (404): every end of their frame is a state of the set and has no control;
* the near states (4): every end of their frame has control and knows the speed 0. They know the timer's digits 4, 0, 1, the phase 2 and the three music bytes 0.

In the game core (two far states and the near states) the input has no Start, as `noPause` says.

The search is no part of the proof. `check` walks every state of the set and every state of the tables (13,221). It takes about 4 s natively. Then by induction each `tm n` with `n ≤ pre` is in the set (`Begin.inSet`): a near state would give control before frame 1 (`first`). `tm pre` is not far, because its frame gives control (`ctl`). So it is near (`Begin.near`).

## On real runs

`title-check FM2`, exit code 0. The press: Start after 30 to 624 frames of the title (100 runs), A with Start (10 runs), random buttons on the title and random buttons up to control with Start only off the game core (200 runs), a reset every 150 frames of the movie and then Start (12 runs).

```
runs                                   322
no control within 600 frames           21   (Start on frame 30, or during the demo: the press is not taken)
the press meets Press                  301 of 301
frame 0 or control not as the check    0
frames from the press to frame 0       153 to 173
the movie's own press                  meets Press; frame 0 has timer 401, phase 2, no music; speed 0 at control
```

## What is not proved

* `press` is a hypothesis on one state. It holds on all 301 runs above. A run in which the title shows another world (A with Start after a game over), or a byte of `K` with another value, is outside.
* `noPause` is a condition on the inputs of two frames. Start there pauses the game. The pause only delays control, but that is not in Lean: the search fails on the paused states in the music's code.
* `atZero`, `first`, `ctl`, `pipeAt` say which machine is frame 0, and that the two sequences agree. They hold by how the sequences are made.

**Files.** `Theorems/TitleStart.lean`, `Theorems/Route.lean` (`Run.title`, `Run.pipeAt`, `Run.zero`, `Run.still`), `Theorems/HurryMusic.lean`, the private `Proof/TitleStart.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta title-check FM2
```
