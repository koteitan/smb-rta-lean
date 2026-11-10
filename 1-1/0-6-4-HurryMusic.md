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

The fields of `HurryMusic.Run`:

```
clock, order   Frames (each frame follows Step and plan), and the order of the segments
next           seq(n + 1) = frame(seq n, inp n)
title          from the press of Start on the title to frame 0 (TitleStart.Begin)
read₀          s(0).t = timer(seq 0)
k, hk, on      k ≤ E + 1,  hurryOn(seq k) = true
For a frame n that starts the music:  n < k,  hurryOn(seq n) = false,  hurryOn(seq (n + 1)) = true  ⟹
  start        Start(seq n)                          (one state: in control or in the entrance, see HurryFrame)
  clean        ∀ j,  CleanM(tr_n(j))                  (each instruction of that frame)
  below        s(n + 1).t ≤ timer(seq (n + 1))       (one frame)
L, after       E < L
```

`Start` and `CleanM` are those of [the frame that starts the hurry-up music](0-6-4-2-1-HurryFrame.md). `tr_n(j)` is the machine after `j` instructions of frame `n`.

The theorems:

```
Frames.late             :  s(0).t = t0,  n ≤ E + 1,  s(n).t ≤ u  ⟹  q · (t0 − u) ≤ E + 3q
Run.zero                :  timer(seq 0) = t0                (from title, with the check title_check)
Run.quiet₀              :  hurryOn(seq 0) = false           (from title, with the check title_check)
Run.music               :  for a frame n that starts the music,  timer(seq (n + 1)) ≤ u      (from start and clean, with the check music_check)
Run.late                :  1 ≤ q  ⟹  q · (t0 − u) ≤ E + 3q
Run.level_ge            :  1 ≤ q,  1748 + 3q ≤ q · (t0 − u)  ⟹  1748 ≤ L
hurry_1_1 (private)     :  q = 24,  t0 = 401,  u = 100  ⟹  1748 ≤ L
```

`q · (t0 − u) = 24 · 301 = 7224` and `1748 + 3q = 1820`. `k` can be any frame up to the castle entry. In a run that fails `chg.entry₂`, it is the frame of the side pipe's entry.

The proof:

* `hurryOn` is false on frame 0 and true on frame `k`. So there is a frame `n < k` on which it turns from false to true (`first_on`). `Run.music` gives `timer(seq (n + 1)) ≤ u`, and `below` gives `s(n + 1).t ≤ u`. `n + 1 ≤ k ≤ E + 1`.
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

## What is not proved

* `music` is no longer a field. It is proved from `start` and `clean` by a walk of the whole frame ([the frame that starts the hurry-up music](0-6-4-2-1-HurryFrame.md)). `start` and `clean` are conditions on that one frame and its instructions. They are checked on the 108 frames above, not proved.
* `below` is now needed on one frame only: the frame after the one that starts the music. Before, it was needed on every frame up to `k`. It links the counters to the machine. In a run with no frame that runs over, the counters of `clock` are the values read from the machines, so it holds with equality. On a frame that runs over, the digits at the frame's start are not below those that the routine leaves, because the routine only lowers them. This is read from the code. On the 108 real frames above it holds with equality.
* `read₀` links the counters to the machine when frame 0 begins, as in `Route.Run`.
* `title` is the hypothesis of [From Start on the title to control](0-5-3-TitleStart.md): one condition on the machine after the press, and no Start on the frames of the game core before control. `zero` and `quiet₀` are no longer fields: they are proved from it (`Run.zero`, `Run.quiet₀`).
* `step` and `plan` of `clock` are the same hypotheses as in `Route.Run` ([the whole of 1-1](0-1-Route.md)). Runs with a power-up and runs with a death do not follow `plan`, so they are not covered here either.

**Files.** `Theorems/HurryMusic.lean`, `Theorems/HurryFrame.lean`, `Theorems/CastleToLevel.lean` (`Frames.late`, `playN_drop`), `Theorems/TitleStart.lean`, the private `Proof/HurryMusic.lean`, `Proof/HurryFrame.lean` and `Proof/TitleStart.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta hurry-check FM2
.lake/build/bin/smbrta music-check
```
