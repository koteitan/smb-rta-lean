[← Back](README.md) | [English](0-6-4-HurryMusic.md) | [Japanese](0-6-4-HurryMusic-ja.md)

# Runs with the hurry-up music

**Claim.** In a run with the hurry-up music, 1-2 does not start before frame 1748. With `E` the frame of the castle entry, `q · (t0 − u) ≤ E + 3q`. With the game's values `q = 24`, `t0 = 401`, `u = 100`, this is `E ≥ 7152`.

**This theorem has hypotheses.** They are the fields of `HurryMusic.Run`, all listed below.

The game queues the hurry-up music on the frame on which the timer shows 100. A run in which this music plays fails `chg.entry₂` at the side pipe (the music bytes and `NoteLengthTblAdder` differ). So it is not in the `Run` of [the whole of 1-1](0-1-Route.md). This theorem deals with it on its own.

## The theorem

`seq n` is the machine when frame `n` begins. `s(n)` are the counters of `clock` when frame `n` begins (`CastleToLevel.Frames`, the same as `Route.Run.clock`). `timer(m)` is the value of the timer's three digits in the machine `m`.

`hurryOn(m)` says that in the machine `m` the hurry-up music is queued, is playing, or makes the song after it faster.

```
hurryOn(m)  =  EventMusicQueue(m) = TimeRunningOutMusic  ∨  EventMusicBuffer(m) = TimeRunningOutMusic  ∨  NoteLengthTblAdder(m) ≠ 0
```

The fields of `HurryMusic.Run`:

```
clock, order   Frames (each frame follows Step and plan), and the order of the segments
next           seq(n + 1) = frame(seq n, inp n)
zero           timer(seq 0) = t0
quiet₀         hurryOn(seq 0) = false
read₀          s(0).t = timer(seq 0)
k, hk, on      k ≤ E + 1,  hurryOn(seq k) = true
music          n < k,  hurryOn(seq n) = false,  hurryOn(frame(seq n, inp n)) = true  ⟹  timer(seq n) ≤ u        (one frame)
below          n < k  ⟹  s(n).t ≤ timer(seq n)
L, after       E < L
```

The theorems:

```
Frames.late             :  s(0).t = t0,  n ≤ E + 1,  s(n).t ≤ u  ⟹  q · (t0 − u) ≤ E + 3q
Run.late                :  1 ≤ q  ⟹  q · (t0 − u) ≤ E + 3q
Run.level_ge            :  1 ≤ q,  1748 + 3q ≤ q · (t0 − u)  ⟹  1748 ≤ L
hurry_1_1 (private)     :  q = 24,  t0 = 401,  u = 100  ⟹  1748 ≤ L
```

`q · (t0 − u) = 24 · 301 = 7224` and `1748 + 3q = 1820`. `k` can be any frame up to the castle entry. In a run that fails `chg.entry₂`, it is the frame of the side pipe's entry.

The proof:

* `hurryOn` is false on frame 0 and true on frame `k`. So there is a frame `n < k` on which it turns from false to true (`first_on`). `music` gives `timer(seq n) ≤ u`, and `below` gives `s(n).t ≤ u`.
* `Frames.late`: no frame raises the timer's digits (`t_anti`), so `T = s(E + 1).t ≤ u`. `hT` gives `t0 − u ≤ ⌈p₁/q⌉ + ⌈p₂/q⌉ + ⌈p₃/q⌉`, where `p₁`, `p₂`, `p₃` are the frames of play in the three areas. Then `q · ⌈p/q⌉ ≤ p + q − 1` and `p₁ + p₂ + p₃ ≤ E`.
* `Run.level_ge`: `L > E ≥ q · (t0 − u) − 3q ≥ 1748`.

`hT` holds from any sub-counter (`playN_drop`): `p` frames of play take at most `⌈p/q⌉` off the digits. So the one frame of the music and the timer's rule are enough.

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

## What is not proved

* `music` is a hypothesis on one frame. In the code, only `RunGameTimer` queues the hurry-up music, when the timer is at 100. `EventMusicBuffer` is copied from the queue. Only the loading of the hurry-up music from the queue sets `NoteLengthTblAdder` to a value other than 0. This is read from the code, and checked on the 108 frames above.
* `below` and `read₀` link the counters to the machines. In a run with no frame that runs over, the counters of `clock` are the values read from the machines, so they hold with equality. On a frame that runs over, the digits at the frame's start are not below those that the routine leaves, because the routine only lowers them. This is read from the code, not checked.
* `step` and `plan` of `clock` are the same hypotheses as in `Route.Run` ([the whole of 1-1](0-1-Route.md)). Runs with a power-up and runs with a death do not follow `plan`, so they are not covered here either.

**Files.** `Theorems/HurryMusic.lean`, `Theorems/CastleToLevel.lean` (`Frames.late`, `playN_drop`), the private `Proof/HurryMusic.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta hurry-check FM2
```
