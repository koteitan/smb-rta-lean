[← Back](README.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# One whole frame in control keeps the castle flag and the fraction's low bits

**Claim.** A whole frame that starts in control keeps two things. The castle flag stays down. The fraction of the position stays a multiple of 1/16 px. The frame also ends at the start of the next frame in control, as far as the walk can see: in the idle loop, with the stack pointer, the dot and the PPU of a frame's start. This is a theorem about any machine and any input. Its conditions are one state at the frame's start and one condition on each instruction of the frame. The proof follows the whole frame with the abstract machine of `TaintRun.lean`, as [`PipeWrites`](a-5-2-PipeWrites.md) does.

So the hypothesis `fracStep` of `PoleJoin.Run` is gone. It is the theorem `Run.fracP`, from the frames of the run (the field `keep`) and the check on the ROM. The field `noCastle` is gone too: it is the theorem `Run.noCastle_of`, from the machine at control ([The machine at control above ground](f-6-2-ControlStart.md)). The field `keep.start` (each frame starts in control) is gone: it is the theorem `Frames.start`. It needs a smaller field, `keep.ctl`: each frame before the touch ends in control.

`frame(m, i)` is the real frame with the input `i`. `tr(n)` is the machine `n` instructions into it. `seq j` is the machine at the end of the counted frame `j`, and `seq 0` the machine at control above ground.

```
castle(m)        :=  StarFlagTaskControl(m) ≠ 0
f(m)             :=  SprObject_X_MoveForce(m)                         the fraction of the position, in 1/256 px
Watched(m)       :=  castle(m) = false  ∧  f(m) mod 16 = 0
q                :=  the first STA abs,X of MoveObjectHorizontally    its store of the fraction
Prot_K           :=  Prot of PipeWrites  ∪  {StarFlagTaskControl, SprObject_X_MoveForce}
Known_K(m)       :=  GameEngineSubroutine(m) = control  ∧  OperMode(m) = game  ∧  OperMode_Task(m) = core
                  =  controllable(m)                                                     (known_of_ctl)
FrameStart_K(m)  :=  FrameStart of PipeWrites (idle loop, stack, dot, PPU, strobe)  ∧  Known_K(m)          (StartK)
CleanK(m)        :=  store:  a store through an index or a pointer, with the target t:   ¬(pc(m) = q ∧ X(m) = 0)  →  Plain(Prot_K, t)
                     read, jump, time:  as `Clean` of PipeWrites
```

`Plain(Prot_K, t)` says that the store changes no byte of `Prot_K`. The store at `q` with `X = 0` is the player's own store of the fraction, so it is not asked.

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))
keep_frame_start  :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  Known_K(frame(m, i))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

Frames (keep)     :  fm j, pad j                       where the counted frame j begins, and its input
                     ends    :  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
                     ctl     :  1 ≤ j < g  →  controllable(seq j)
                     clean   :  1 ≤ j ≤ g  →  ∀ n,  CleanK(tr_j(n))
                     lag     :  1 ≤ j ≤ g  →  Watched(seq(j − 1))  →  Watched(fm j)
                     lagStart:  1 ≤ j ≤ g  →  FrameStart_K(seq(j − 1))  →  FrameStart_K(fm j)
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 the machine at control
Frames.run        :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  the same   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  the same   →   ∀ j ≤ g,  Watched(seq j)

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  the same  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  the same  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` is `posP(seq(j − 1))`, read from the machines (`frames.reads`). `AtCtl(seq 0)` is a theorem on a real run: `ControlStart.EndRun.atCtl`, from the rows of the change out of the side pipe ([The machine at control above ground](f-6-2-ControlStart.md)).

`Frames.run` is an induction on `j`. The frame `j + 1` begins at `fm(j + 1)`: `lagStart` and `lag` carry `FrameStart_K` and `Watched` from `seq j` there. The frame ends at `seq(j + 1)`. `keep_frame_start` gives `FrameStart_K(seq(j + 1))`, with `Known_K(seq(j + 1))` from `ctl`. The touch's frame `g` is not asked to end in control: there the routine changes.

## The walk

It is the walk of `PipeWrites`: the stores with a target not known forget every byte outside `Prot_K`; the jump routine splits the index into the entries of its table; the time is capped. It starts from the state of `PipeWrites`, with the castle byte known to be 0 and the fraction's low 4 bits known to be 0. It ends each path at the frame's end with `Watched` known, and with the state of a frame's start (`endOK`):

```
endOK(B)  :=  pc(B) = idle  ∧  S(B) = S₀  ∧  ((lo = hi = 0  ∧  ¬vblank  ∧  ¬nmi)  ∨  (1 ≤ lo  ∧  hi ≤ 9  ∧  vblank  ∧  nmi))
              ∧  bit 7 of ppuCtrl(B) known to be 1  ∧  ¬strobe(B)
```

`start_of_sim` turns `endOK(B)`, a machine that `B` covers, and `Known_K` on that machine into `FrameStart_K`. The walk does not know `Known_K` at the frame's end: the table joins the idle loop's states over the routine, the mode and the task. So `Known_K` stays a condition on the frame's end (`ctl`). Two steps are the walk's own:

* **The sum of the low bits.** `ADC zp` with the low 4 bits of `A` and of the byte and the carry known gives the low 4 bits of the sum: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16` (`s_adcL`, proved against `adc`). The move routine adds `16·v` this way: the speed shifted left four times has its low 4 bits 0.
* **The index of the move routine.** At its entry an index `X` that is not known splits into 9 pieces: `X = 0`, or the lowest bit 1 of `X` is bit `b` (`b = 0, …, 7`). With `X = 0` the walk knows the store's target. With `X ≠ 0` the store is the usual one of `PipeWrites`, and `CleanK` says that its target is `Plain`. The player's move takes `X` from the jumpspring's control; the pieces cover it with no condition on that byte.

The check `keepCheck` (`keep_check` in the private proof). The frame's ends: 10 kinds of state, all with `endOK`.

| walk | steps | forks | failures | table | time |
|---|---|---|---|---|---|
| castle flag and fraction, 9 pieces, `endOK` at the ends | 707,685 | 69,404 | 0 | 46,573 | check 3.8 s in a program, `Proof.FrameKeep` 5.0 s |
| the same, with the jumpspring's control known to be 0 at the start and in `Prot_K` (the last round) | 1,044,377 | 101,574 | 0 | 79,266 | check 4.9 s in a program |
| castle flag only, no pieces | 907,094 | 92,482 | 0 | 72,016 | check 4.5 s |
| castle flag and fraction, `X` split into 256 values | 9,779,840 | 767,686 | 0 | 355,602 | check 32 s |

## On real frames

`keep-frames-check FM2 100`, after the last change (exit 0, bad 0). Every frame from control above ground up to the touch, including the touch's frame. The first four kinds of run have no Start, so no `lag` frames. The last presses Start on one frame and again 10 to 49 frames later.

| run | runs | frames | instructions | touches |
|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1,203,506 | 1 |
| random inputs from control | 100 | 29,102 | 150,058,083 | 0 |
| random inputs from the movie's frames 1002 to 1091 | 400 | 46,025 | 183,000,496 | 216 |
| into the screen's left edge, then random | 120 | 35,945 | 193,591,853 | 0 |
| random inputs with a pause, from control | 100 | 37,395 (26,341 paused) | 107,816,920 | 0 |

* Every frame meets `FrameStart_K` and starts with `Watched`. Every instruction meets `CleanK`. Every frame ends with `Watched`.
* Every frame that ends with the routine of control ends with `controllable` (`ctl`).
* The store at `q` with `X = 0` comes once on every frame that is not paused: the player's move. No other store through an index or a pointer touches `Prot_K`.
* The latest dot of an instruction is 66,674, below the limit `dotsPerFrame − 64`.

## Hypotheses (not proved in Lean)

* **`keep.clean`: `CleanK` on each instruction of each frame up to the touch.** It is the condition of `PipeWrites`, with the three bytes added to `Prot_K` and the player's store not asked. Checked on the real frames above.
* **`keep.ctl`: each frame before the touch ends in control.** Three bytes of one state: the routine, the mode, the task. The walk does not know them at the frame's end.
* **`keep.ends`: the counted frame `j` ends at `seq j`.** `fm j` is `seq(j − 1)` or later by `lag` frames.
* **`keep.lag`, `keep.lagStart`: the `lag` frames before a counted frame keep the castle flag, the fraction's low 4 bits and the start of a frame in control.** On the runs with a pause above they do.

What stopped being a hypothesis: `fracStep` (each frame moves the position by a multiple of 1/16 px), then `noCastle` and `keep.start`. `CleanK` and `FrameStart_K` no longer name the jumpspring's control. What is new: `keep` (`ends`, `ctl`, `clean`, `lag`, `lagStart`), and the checks `keepCheck` and `ControlStart.ctlCheck` on the ROM.

**Files.** `Theorems/FrameKeep.lean`, `Theorems/ControlStart.lean`, `Theorems/PoleJoin.lean`, private `Proof/FrameKeep.lean`, `Proof/ControlStart.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta keep-check                     # the walk, as a program (about 10 s)
.lake/build/bin/smbrta keep-frames-check FM2 100      # the conditions on real frames (about 3 min)
```
