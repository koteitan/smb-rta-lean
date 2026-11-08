[← Back](README.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# One whole frame in control keeps the castle flag and the fraction's low bits

**Claim.** A whole frame that starts in control keeps two things. The castle flag stays down. The fraction of the position stays a multiple of 1/16 px. This is a theorem about any machine and any input. Its conditions are one state at the frame's start and one condition on each instruction of the frame. The proof follows the whole frame with the abstract machine of `TaintRun.lean`, as [`PipeWrites`](a-5-2-PipeWrites.md) does.

So the hypothesis `fracStep` of `PoleJoin.Run` is gone. It is now the theorem `Run.fracP`, from the frames of the run (the new field `keep`) and the check on the ROM. `noCastle` also follows from its first state (`Run.noCastle_of`). It stays a field this round: `Route` uses `Run.afterTouch`, which takes no check.

`frame(m, i)` is the real frame with the input `i`. `tr(n)` is the machine `n` instructions into it. `seq j` is the machine at the end of the counted frame `j`, and `seq 0` the machine at control above ground.

```
castle(m)        :=  StarFlagTaskControl(m) ≠ 0
f(m)             :=  SprObject_X_MoveForce(m)                         the fraction of the position, in 1/256 px
Watched(m)       :=  castle(m) = false  ∧  f(m) mod 16 = 0
q                :=  the first STA abs,X of MoveObjectHorizontally    its store of the fraction
Prot_K           :=  Prot of PipeWrites  ∪  {StarFlagTaskControl, SprObject_X_MoveForce, JumpspringAnimCtrl}
FrameStart_K(m)  :=  FrameStart of PipeWrites (idle loop, stack, dot, PPU, routine = control, OperMode, OperMode_Task)  ∧  JumpspringAnimCtrl(m) = 0
CleanK(m)        :=  store:  a store through an index or a pointer, with the target t:   ¬(pc(m) = q ∧ X(m) = 0)  →  Plain(Prot_K, t)
                     read, jump, time:  as `Clean` of PipeWrites
```

`Plain(Prot_K, t)` says that the store changes no byte of `Prot_K`. The store at `q` with `X = 0` is the player's own store of the fraction, so it is not asked.

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))

Frames (keep)     :  fm j, pad j                       where the counted frame j begins, and its input
                     ends :  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
                     start:  1 ≤ j ≤ g  →  FrameStart_K(fm j)
                     clean:  1 ≤ j ≤ g  →  ∀ n,  CleanK(tr_j(n))
                     lag  :  1 ≤ j ≤ g  →  Watched(seq(j − 1))  →  Watched(fm j)
Frames.watched    :  keepCheck,  keep,  Watched(seq 0)   →   ∀ j ≤ g,  Watched(seq j)

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  the same  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  Start(seq 0),  fracCheck,  keepCheck,  castle(seq 0) = false,  Run   →   ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` is `posP(seq(j − 1))`, read from the machines (`frames.reads`). `Run.fracP` takes `castle(seq 0) = false` from the field `noCastle`, at `j = 0` only.

## The walk

It is the walk of `PipeWrites`: the stores with a target not known forget every byte outside `Prot_K`; the jump routine splits the index into the entries of its table; the time is capped. It starts from the state of `PipeWrites`, with the castle byte known to be 0 and the fraction's low 4 bits known to be 0, and it ends each path at the frame's end with `Watched` known. Two steps are its own:

* **The sum of the low bits.** `ADC zp` with the low 4 bits of `A` and of the byte and the carry known gives the low 4 bits of the sum: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16` (`s_adcL`, proved against `adc`). The move routine adds `16·v` this way: the speed shifted left four times has its low 4 bits 0.
* **The index of the move routine.** At its entry an index `X` that is not known splits into 9 pieces: `X = 0`, or the lowest bit 1 of `X` is bit `b` (`b = 0, …, 7`). With `X = 0` the walk knows the store's target. With `X ≠ 0` the store is the usual one of `PipeWrites`, and `CleanK` says that its target is `Plain`. The jumpspring's control is 0 at the start, so the player's move has `X = 0` known.

The check `keepCheck` (`keep_check` in the private proof):

| walk | steps | forks | failures | table | time |
|---|---|---|---|---|---|
| castle flag and fraction, 9 pieces | 1,044,377 | 101,574 | 0 | 79,266 | check 5.3 s in a program, `Proof.FrameKeep` 5.5 s |
| castle flag only, no pieces | 907,094 | 92,482 | 0 | 72,016 | check 4.5 s |
| castle flag and fraction, `X` split into 256 values | 9,779,840 | 767,686 | 0 | 355,602 | check 32 s |

## On real frames

`keep-frames-check FM2 100`, after the last change. Every frame from control above ground up to the touch, including the touch's frame. The inputs have no Start, so there are no `lag` frames.

| run | runs | frames | instructions | touches |
|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1,203,506 | 1 |
| random inputs from control | 100 | 29,102 | 150,058,083 | 0 |
| random inputs from the movie's frames 1002 to 1091 | 400 | 46,025 | 183,000,496 | 216 |
| into the screen's left edge, then random | 120 | 35,945 | 193,591,853 | 0 |

* Every frame meets `FrameStart_K` and starts with `Watched`. Every instruction meets `CleanK`. Every frame ends with `Watched`.
* The store at `q` with `X = 0` comes once on every frame: the player's move. No other store through an index or a pointer touches `Prot_K`.
* The latest dot of an instruction is 65,975, below the limit `dotsPerFrame − 64`.

## Hypotheses (not proved in Lean)

* **`keep.clean`: `CleanK` on each instruction of each frame up to the touch.** It is the condition of `PipeWrites`, with the three bytes added to `Prot_K` and the player's store not asked. Checked on the real frames above.
* **`keep.start`: `FrameStart_K` when each counted frame begins.** In particular the frame starts in control, and the jumpspring's control is 0.
* **`keep.ends`: the counted frame `j` ends at `seq j`.** `fm j` is `seq(j − 1)` or later by `lag` frames.
* **`keep.lag`: the `lag` frames before a counted frame keep the castle flag and the fraction's low 4 bits.**
* **`noCastle` stays a field.** With `keep` and the check, only `castle(seq 0) = false` is needed (`Run.noCastle_of`). `Route` would have to pass the check to `Run.afterTouch` to drop the rest.

What stops being a hypothesis: `fracStep` (each frame moves the position by a multiple of 1/16 px). What is new: `keep` (`ends`, `start`, `clean`, `lag`), and the check `keepCheck` on the ROM.

**Files.** `Theorems/FrameKeep.lean`, `Theorems/PoleJoin.lean`, private `Proof/FrameKeep.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta keep-check                     # the walk, as a program (about 10 s)
.lake/build/bin/smbrta keep-frames-check FM2 100      # the conditions on real frames (about 2 min)
```
