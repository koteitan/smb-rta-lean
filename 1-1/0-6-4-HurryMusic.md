[← Back](README.md) | [English](0-6-4-HurryMusic.md) | [Japanese](0-6-4-HurryMusic-ja.md)

# Runs with the hurry-up music

**Claim.** In a run with the hurry-up music, 1-2 does not start before frame 1748. With `E` the frame of the castle entry, `q · (t0 − u) ≤ E + 3q`. With the game's values `q = 24`, `t0 = 401`, `u = 100`, this is `E ≥ 7152`.

**This theorem has hypotheses.** They are the fields of `HurryMusic.Run`, all listed below.

The game queues the hurry-up music on the frame on which the timer shows 100. A run in which this music plays fails `chg.entry₂` at the side pipe (the music bytes and `NoteLengthTblAdder` differ). So it is not in the `Run` of [the whole of 1-1](0-1-Route.md). This theorem deals with it on its own.

## The theorem

`seq n` is the machine when frame `n` begins. `s(n)` are the counters of `clock` when frame `n` begins (`CastleToLevel.Frames`, the same as `Route.Run.clock`). `timer(m)` is the value of the timer's three digits in the machine `m`.

`hurryOn(m)` says that in the machine `m` the hurry-up music is queued, is playing, or makes the song after it faster. The queue and its buffer are read by the music's bit (`v`, the number of `TimeRunningOutMusic`, has one bit).

```
hurryOn(m)  =  EventMusicQueue(m) & v ≠ 0  ∨  EventMusicBuffer(m) & v ≠ 0  ∨  NoteLengthTblAdder(m) ≠ 0
```

The fields of `HurryMusic.Run`. `First(n)` says that frame `n` is the first frame that starts the music: `hurryOn(seq m) = false` for every `m ≤ n`, and `hurryOn(seq (n + 1)) = true`.

```
clock, order   Frames (each frame follows Step and plan), and the order of the segments
base           the real frames of the run (Route.Base, as in Route.Run): seq(n + 1) = frame(seq n, inp n)
title          from the press of Start on the title to frame 0 (TitleStart.Begin)
read₀          s(0).t = timer(seq 0)
k, hk, on      k ≤ E + 1,  hurryOn(seq k) = true
b              the frame from which the frames before the music are in control
start          b = 1  ∨  (b + 1 = b₁  ∧  Chg₁)  ∨  (b + 1 = b₂  ∧  Route.ChangesK)
For the first frame n that starts the music:  n < k,  First(n)  ⟹
  bLe          b ≤ n
  noStore      b ≤ j < n,  ctl(seq j)  ⟹  ∀ i,  ¬ CtlStore(tr_j(i))   (each instruction of these frames in control)
  clean        b ≤ j ≤ n  ⟹  ∀ i,  CleanM(tr_j(i))     (each instruction of these frames)
  below        s(n + 1).t ≤ timer(seq (n + 1))       (one frame)
L, after       E < L
```

`Start`, `CleanM` and `CtlStore` are those of [the frame that starts the hurry-up music](0-6-4-2-1-HurryFrame.md): `CtlStore` says that the instruction writes the routine, the mode or the task by its address. `tr_j(i)` is the machine after `i` instructions of frame `j`. `ctl(m)` says that `m` has control.
`b₁` and `b₂` are the first controls after the two changes (`Route.Base.b₁`, `Route.Base.b₂`), so `b₁ − 1` and `b₂ − 1` are the last frames of the changes. `Chg₁` is the fields of `Route.ChangesK` on the first change (`HurryStart.chg₁_of_changes`), and `Route.ChangesK` the conditions of both changes that `Route.Run` asks ([the last frame of a change](0-6-4-2-2-2-1-HurryStart.md)).

`start` asks no state now. Frame `b` is frame 1, or the last frame of a change. The start of frame 1 comes from the press of Start on the title (`Begin.start₁`). The start of the last frame of a change comes from the rows with tables of the change (`Run.startB`), under the conditions of the change, exactly as in `Route.Run`. When the music starts in the room, only the conditions of the first change are asked: such a run fails `entry₂` of the second change.

The checks on the ROM are bundled in `Checks`: `title_check`, `music_check`, `hurry_ctl_check`, `hurry_near_check`, `entry_checks`, the checks of the two changes and the room (`side_bound`, `side_sound`, `RoomChecks`: those of `route_1_1`), and `hurry_rows₁`, `hurry_rows₂`.

The theorems:

```
Frames.late             :  s(0).t = t0,  n ≤ E + 1,  s(n).t ≤ u  ⟹  q · (t0 − u) ≤ E + 3q
Run.zero                :  timer(seq 0) = t0                (from title, with the check title_check)
Run.quiet₀              :  hurryOn(seq 0) = false           (from title, with the check title_check)
first_turn              :  hurryOn(seq 0) = false,  hurryOn(seq k) = true  ⟹  ∃ n < k,  First(n)
Begin.start₁            :  Startᶜ(seq 1)  ∧  the music bits off at seq 1    (from title, with the checks title_check and hurry_near_check)
Run.startB              :  Start(seq b)                                      (Begin.start₁, or the rows of the change: HurryStart)
Run.startOrCtl          :  Startᶜ(seq b)  ∨  ctl(seq (b + 1))                (b = 1: Begin.start₁; else b + 1 is b₁ or b₂, the first control after a change)
HurryFrame.frame_ctl    :  Startᶜ(m),  off(m),  ∀ i, CleanM(tr(i)),  ∀ i, ¬ CtlStore(tr(i))  ⟹  ctl(frame(m, i))     (with the check hurry_ctl_check)
HurryFrame.frame_startC :  Start(m),  off(m),  ∀ i, CleanM(tr(i)),  ctl(frame(m, i))  ⟹
                           the music queued in frame(m, i)  ∨  (Startᶜ(frame(m, i))  ∧  off(frame(m, i)))     (with the check music_check)
Run.startAt             :  for the first frame n that starts the music,  Start(seq n)          (the old fields start and ctl)
Run.music               :  for the first frame n that starts the music,  timer(seq (n + 1)) ≤ u
Run.late                :  1 ≤ q  ⟹  q · (t0 − u) ≤ E + 3q
Run.level_ge            :  1 ≤ q,  1748 + 3q ≤ q · (t0 − u)  ⟹  1748 ≤ L
hurry_1_1 (private)     :  Checks,  q = 24,  t0 = 401,  u = 100  ⟹  1748 ≤ L
```

`q · (t0 − u) = 24 · 301 = 7224` and `1748 + 3q = 1820`. `k` can be any frame up to the castle entry. In a run that fails `chg.entry₂`, it is the frame of the side pipe's entry.

The proof:

* `hurryOn` is false on frame 0 and true on frame `k`. So there is a first frame `n < k` on which it turns from false to true (`first_turn`). `Run.startAt` gives `Start(seq n)`, `Run.music` gives `timer(seq (n + 1)) ≤ u`, and `below` gives `s(n + 1).t ≤ u`. `n + 1 ≤ k ≤ E + 1`.
* `Run.startAt`: by induction on the frames from `b` to `n`. `Startᶜ` is `Start` with the routine of control. Frame `b` begins as `Start` says (`Run.startB`): by `Begin.start₁` when `b = 1`, by `HurryStart.Chg₁.startLast` or `HurryStart.changes_startLast` when it is the last frame of a change. Frame `j < n` ends with control: frame `b` when it is the last frame of a change, since `b + 1` is the change's first control (`Run.startOrCtl`); a frame that begins with `Startᶜ` by `HurryFrame.frame_ctl`, since it has control (`HurryFrame.ctl_of_start`) and so `noStore` holds of its instructions. If frame `j < n` begins as `Start` says, with the music off, its instructions meet `CleanM` and it ends with control, then `HurryFrame.frame_startC` says it ends with the music queued, or at `Startᶜ` with the music off. The music is off when frame `j + 1 ≤ n` begins (`First`), so the second holds.
* `Frames.late`: no frame raises the timer's digits (`t_anti`), so `T = s(E + 1).t ≤ u`. `hT` gives `t0 − u ≤ ⌈p₁/q⌉ + ⌈p₂/q⌉ + ⌈p₃/q⌉`, where `p₁`, `p₂`, `p₃` are the frames of play in the three areas. Then `q · ⌈p/q⌉ ≤ p + q − 1` and `p₁ + p₂ + p₃ ≤ E`.
* `Run.level_ge`: `L > E ≥ q · (t0 − u) − 3q ≥ 1748`.

`hT` holds from any sub-counter (`playN_drop`): `p` frames of play take at most `⌈p/q⌉` off the digits. So the one frame of the music and the timer's rule are enough.

`Run.music`: the walk of `HurryFrame.frame_music` shows that the frame ends with the music off, or with the timer at `u` or less. It ends with the music, so the timer is at `u` or less. With `u = 100` the timer is 99 there on real frames.

## On real frames

`hurry-check FM2`, exit code 0:

```
the movie, when frame 0 begins           timer 401,  phase 2,  hurryOn false
the movie, 1760 frames                    frames that start the music 0, frames against Step (up to the castle) 0
runs with the timer written               on 12 frames of the movie (100 to 1100) the digits written to 100, 101, 102, 103, 105, 110, 124,
                                          then 600 frames of the movie's inputs, or of random inputs with pauses. 168 runs, 100,800 frames
  frames that start the music             108. The timer when each begins is 100. Above u = 100: 0
  frames against Step (up to the castle)  movie's inputs 0. Random inputs 11, all in the routines 0 and 7: the level restarting after a lost life
  the music at the side pipe's entry      23 runs
  (frame 571)
```

The 60 runs in which the music did not start are in a change of area (the timer does not run), after the touch, or with a value that does not fall to 100 in 600 frames.

The same check runs each of the 108 frames that start the music instruction by instruction:

```
Start                                      108 of 108   (routine of control 94, of the entrance 14)
music bits off at the start                108 of 108
instructions with CleanM                   521,286 of 521,286
timer at the end                           99 on all 108
ending in the idle loop                    108 of 108
the movie's frames in control or entrance  833: Start, off and CleanM (4,034,601 instructions) on all
```

Each of the 108 frames ends in the idle loop: its routine ends within the frame. So the counters of `clock` when the next frame begins are those of the machine, and `below` holds with equality there.

The same check follows, in each run, the frames before the first frame that starts the music. `b` is the frame after the last frame that ends without control, or the run's first frame (where the timer is written). These are the frames of `noStore` and `clean`.

```
first frames that start the music            108
frame b begins as Start                      108 of 108  (in control 50: the run's first frame; in the entrance 58: the last frame of a change)
frames from b to the music's frame           0 to 305, 7,451 in all; b is the music's frame on 16
CleanM on each instruction of these frames   35,023,871 of 35,023,871
CtlStore on the instructions of these frames
  that begin with control (not the music's)  0
```

In a run from the title, `b` is frame 1, or the last frame of a change: the frame that begins in the routine of the entrance and ends with control. The runs above begin where the timer is written, so frame 1 is not among them; its start is the theorem `Begin.start₁`. The start of the last frame of a change is the theorem `Run.startB`.

## What is not proved

* `music` is no longer a field. It is proved from the start of the music's frame and `clean` by a walk of the whole frame ([the frame that starts the hurry-up music](0-6-4-2-1-HurryFrame.md)).
* The start of the music's frame is no longer a field: it is proved from frame `b` by induction (`Run.startAt`). The start of frame `b` is no longer a field either (`Run.startB`). When `b = 1` it comes from the press of Start on the title. When the music's frame comes after a change, `b` is the last frame of the change (58 of the 108 runs above, with the routine of the entrance), and its start comes from the rows of the change ([the last frame of a change](0-6-4-2-2-2-1-HurryStart.md)). `start` now asks the conditions of the change instead: those of the first change (`Chg₁`) when the music starts in the room, those of both (`Route.ChangesK`) when it starts above ground. They are exactly the conditions of `Route.Run`, on single frames: at the side pipe's exit the pause sound is one of the kinds of `QuietK` (before, the old `Quiet`); at the vertical pipe's exit `QuietP` and the game timer not 000, `TimerOK` (before, the old `Quiet` and `TimeOK`).
* `ctl` is no longer a field: that each frame from `b` to the music's frame ends with control is proved (`Run.startAt`), from the walk with the stores of the routine, the mode and the task cut (`HurryFrame.frame_ctl`). In its place `noStore` asks that no instruction of these frames that begin with control writes one of these three bytes by its address, and `bLe` that `b` is not after the music's frame.
* `noStore` and `clean` ask, of each instruction of the frames from `b` to the music's frame, that it does not write the three bytes by their address (the frames that begin with control, the music's frame not counted) and that it meets `CleanM`. They are conditions on single instructions, checked on the 108 runs above (7,559 frames), not proved. They are asked only of the first frame that starts the music, and of the frames before it from `b` on. `bLe` is a condition on the choice of `b`: it is the last frame of the last change before the music, or frame 1.
* `below` is needed on one frame only: the frame after the first one that starts the music. Earlier it was needed on every frame up to `k`. It links the counters to the machine. In a run with no frame that runs over, the counters of `clock` are the values read from the machines, so it holds with equality. On a frame that runs over, the digits at the frame's start are not below those that the routine leaves, because the routine only lowers them. This is read from the code. On the 108 real frames above it holds with equality.
* `read₀` links the counters to the machine when frame 0 begins, as in `Route.Run`.
* `title` is the hypothesis of [From Start on the title to control](0-5-3-TitleStart.md): one condition on the machine after the press, and no Start on frame 0 in the game core. `zero` and `quiet₀` are no longer fields: they are proved from it (`Run.zero`, `Run.quiet₀`). These and `Begin.start₁` take any input before control, Start on frame 0 too: `hurry_near_check` walks frame 0 from the near and held states of `TitleStart` with any input, and an end without control is excluded by `title.ctl`.
* `step` and `plan` of `clock` are the same hypotheses as in `Route.Run` ([the whole of 1-1](0-1-Route.md)). Runs with a power-up and runs with a death do not follow `plan`, so they are not covered here either.

**Files.** `Theorems/HurryMusic.lean` (`First`, `first_turn`, `nearCheck`, `Begin.start₁`, `Run.startB`, `Run.startOrCtl`, `Run.startAt`, `Checks`), `Theorems/HurryStart.lean` (`Chg₁`, `rowsCheck₁`, `rowsCheck₂`), `Theorems/HurryFrame.lean` (`frame_startC`, `frame_ctl`, `ctlCheckOf`), `Theorems/CastleToLevel.lean` (`Frames.late`, `playN_drop`), `Theorems/TitleStart.lean`, the private `Proof/HurryMusic.lean` (`hurry_near_check`, `hurry_rows₁`, `hurry_rows₂`, `hurry_1_1`), `Proof/HurryFrame.lean` (`music_check`, `hurry_ctl_check`), `Proof/TitleStart.lean` and `Proof/Route.lean` (`side_sound`).

**Reproduce.**
```
.lake/build/bin/smbrta hurry-check FM2
.lake/build/bin/smbrta hurry-rows-check FM2
.lake/build/bin/smbrta music-check
.lake/build/bin/smbrta hurry-ctl-check
```
