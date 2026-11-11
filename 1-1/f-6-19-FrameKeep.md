[← Back](README.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# One whole frame in control keeps the castle flag and the fraction's low bits

**Claim.** A whole frame that starts in control keeps two things. The castle flag stays down. The fraction of the position stays a multiple of 1/16 px. The frame also ends at the start of the next frame in control, as far as the walk can see: in the idle loop, with the stack pointer, the dot and the PPU of a frame's start. This is a theorem about any machine and any input. Its conditions are one state at the frame's start and one condition on each instruction of the frame. The proof follows the whole frame with the abstract machine of `TaintRun.lean`, as [`PipeWrites`](a-5-2-PipeWrites.md) does.

So the hypothesis `fracStep` of `PoleJoin.Run` is gone. It is the theorem `Run.fracP`, from the frames of the run (the field `keep`) and the check on the ROM. The field `noCastle` is gone too: it is the theorem `Run.noCastle_of`, from the machine at control ([The machine at control above ground](f-6-2-ControlStart.md)). The field `keep.start` (each frame starts in control) is gone: it is the theorem `Frames.start`. It needs a smaller field, `keep.ctl`: each frame before the touch ends in control.

Last round the fields `keep.ends`, `keep.lag` and `keep.lagStart` went. `keep` now lists every frame from control on, counted or not, as real frames one after the other (`all`, `inp`, `next`), and where the counted frames end (`ix`). A `lag` frame needs no rule of its own: the walk covers every frame that starts in control, paused or not. So the `lag` frames keep the castle flag, the fraction's low bits and the start of a frame in control by the same theorem as the counted frames (`Frames.all_start`), when they meet the same two conditions: `ctl` and `clean` now ask them of the `lag` frames too.

This round `ctl` asks two bytes instead of three: each frame before the touch's frame ends with the routine of control and the task of the game core. That the mode is the game's then is a theorem (`ctl_of_frame`, `Frames.ctlAll`): the walk of `keepCheckOf` keeps the mode and the task, and at every end of a frame it checks `endCtl`.

`frame(m, i)` is the real frame with the input `i`. `tr(n)` is the machine `n` instructions into it. `all n` is the machine when frame `n` begins, counted or not, and `all 0` the machine at control above ground. `seq j` is the machine at the end of the counted frame `j`, and `seq 0 = all 0`.

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

Frames (keep)     :  all n, inp n                      the machine when frame n begins, counted or not, and its input
                     next    :  all(n + 1) = frame(all n, inp n)
                     ix      :  ix 0 = 0,   j < g → ix j < ix(j + 1),   j ≤ g → seq j = all(ix j)      the counted frame j ends at all(ix j)
                     ctl     :  n + 1 < ix g  →  rt(all(n + 1)) = control  ∧  OperMode_Task(all(n + 1)) = core
                     clean   :  n < ix g  →  ∀ k,  CleanK(tr_n(k))                 tr_n:  the instructions of the frame from all n
fm j  :=  all(ix j − 1),   pad j  :=  inp(ix j − 1)                       where the counted frame j begins, and its input
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 the machine at control
Frames.ends       :  keep  →  ∀ j,  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
Frames.all_start  :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ n < ix g,  FrameStart_K(all n)  ∧  Watched(all n)
Frames.all_watched:  the same   →   ∀ n ≤ ix g,  Watched(all n)
Frames.run        :  the same   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  the same   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  the same   →   ∀ j ≤ g,  Watched(seq j)
Frames.ctlAll     :  the same   →   ∀ n,  n + 1 < ix g  →  controllable(all(n + 1))

endCtl(B)         :  rt(B) is known not to be control  ∨  the task is known not to be core  ∨  the mode is known to be game
ctl_of_frame      :  keepCheckOf,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  rt(frame(m, i)) = control,  task(frame(m, i)) = core
                       →   controllable(frame(m, i))

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  the same  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  the same  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` is `posP(seq(j − 1))`, read from the machines (`frames.reads`). `AtCtl(seq 0)` is a theorem on a real run: `ControlStart.EndRun.atCtl`, from the rows of the change out of the side pipe ([The machine at control above ground](f-6-2-ControlStart.md)).

`Frames.all_start` is an induction on `n`, over every frame, counted or not. The frame `n` begins at `all n` with `FrameStart_K` and `Watched`. It ends at `all(n + 1)` (`next`). `keep_frame_start` gives `FrameStart_K(all(n + 1))` and `Watched(all(n + 1))`, with `Known_K(all(n + 1))` from `ctl`. The touch's frame, the last one (`n = ix g − 1`), is not asked to end in control: there the routine changes. `keep_frame` gives `Watched(all(ix g))` without it (`Frames.all_watched`). The theorems on the counted frames read these at `seq j = all(ix j)` and `fm j = all(ix j − 1)`: `ix` grows, so `ix j ≤ ix g` (`Frames.ix_mono`).

## The walk

It is the walk of `PipeWrites`: the stores with a target not known forget every byte outside `Prot_K`; the jump routine splits the index into the entries of its table; the time is capped. It starts from the state of `PipeWrites`, with the castle byte known to be 0 and the fraction's low 4 bits known to be 0. It ends each path at the frame's end with `Watched` known, and with the state of a frame's start (`endOK`):

```
endOK(B)  :=  pc(B) = idle  ∧  S(B) = S₀  ∧  ((lo = hi = 0  ∧  ¬vblank  ∧  ¬nmi)  ∨  (1 ≤ lo  ∧  hi ≤ 9  ∧  vblank  ∧  nmi))
              ∧  bit 7 of ppuCtrl(B) known to be 1  ∧  ¬strobe(B)
```

`start_of_sim` turns `endOK(B)`, a machine that `B` covers, and `Known_K` on that machine into `FrameStart_K`. The walk does not know `Known_K` at the frame's end: the table's key has the routine byte but not the mode and the task, so the table joins states over them. Of the 46,573 states of the table, 45,808 do not know the mode and the task. They are lost by joins where `GameCoreRoutine` comes back from `GameRoutines` (the routine of the routine byte), and where `PlayerSubs` comes back from the collision routine. This is the walk of `keepCheck`, which part a's `StartRun` uses too.

**The walk of the run's frames (`keepCheckOf`)** has the mode and the task in the table's key (no part of the proof), and asks `endCtl` at each frame's end besides `Watched` and `endOK`. The table has 46,576 states. Last round's scratch walk with the same key (the same table) knew the three bytes at every end of a frame: 34 ends, of 17 kinds of the three bytes. 4 ends have the routine of control and the task 0: 2 with the mode of the game, 2 with the mode 2. The walk writes them at `ChgAreaMode` (an area change: the task 0) and at `HandleAxeMetatile` (the axe: the task 0 and the mode 2). Neither writes the routine byte. So the routine byte of control at the frame's end does not give control: `ctl` cannot be one byte. At every end with the routine of control and the task of the game core the mode is the game's (`endCtl`), so `ctl` asks only the routine and the task, and `ctl_of_frame` gives the mode.

Two steps are the walk's own:

* **The sum of the low bits.** `ADC zp` with the low 4 bits of `A` and of the byte and the carry known gives the low 4 bits of the sum: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16` (`s_adcL`, proved against `adc`). The move routine adds `16·v` this way: the speed shifted left four times has its low 4 bits 0.
* **The index of the move routine.** At its entry an index `X` that is not known splits into 9 pieces: `X = 0`, or the lowest bit 1 of `X` is bit `b` (`b = 0, …, 7`). With `X = 0` the walk knows the store's target. With `X ≠ 0` the store is the usual one of `PipeWrites`, and `CleanK` says that its target is `Plain`. The player's move takes `X` from the jumpspring's control; the pieces cover it with no condition on that byte.

The check `keepCheckOf` (`keep_check` in the private proof) is the first row. The frame's ends: all with `endOK` and `endCtl`.

| walk | steps | forks | failures | table | time |
|---|---|---|---|---|---|
| castle flag and fraction, 9 pieces, the mode and the task in the key, `endOK` and `endCtl` at the ends (`keepCheckOf`, this round) | 707,869 | 69,388 | 0 | 46,576 | search 2.8 s, check 3.9 s in a program |
| castle flag and fraction, 9 pieces, `endOK` at the ends (`keepCheck`, the last round) | 707,685 | 69,404 | 0 | 46,573 | check 3.8 s in a program, `Proof.FrameKeep` 5.0 s |
| the same, with the jumpspring's control known to be 0 at the start and in `Prot_K` (the last round) | 1,044,377 | 101,574 | 0 | 79,266 | check 4.9 s in a program |
| castle flag only, no pieces | 907,094 | 92,482 | 0 | 72,016 | check 4.5 s |
| castle flag and fraction, `X` split into 256 values | 9,779,840 | 767,686 | 0 | 355,602 | check 32 s |

## On real frames

`keep-frames-check FM2 100`, after the last change (exit 0, bad 0). Every frame from control above ground up to the touch, including the touch's frame, counted or not. The first four kinds of run have no Start, so no `lag` frames. The fifth presses Start on one frame and again 10 to 49 frames later; it does not reach the pole. The last starts from the movie's frames 1002 to 1091 and presses Start on one frame and again 44 to 73 frames later, after the pause timer, so that the game goes on: 241 of these runs touch, with 12,671 paused frames before their touches.

| run | runs | frames | instructions | touches |
|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1,203,506 | 1 |
| random inputs from control | 100 | 29,102 | 150,058,083 | 0 |
| random inputs from the movie's frames 1002 to 1091 | 400 | 46,025 | 183,000,496 | 216 |
| into the screen's left edge, then random | 120 | 35,945 | 193,591,853 | 0 |
| random inputs with a pause, from control | 100 | 37,395 (26,341 paused) | 107,816,920 | 0 |
| random inputs with a pause, from the movie's frames 1002 to 1091 | 400 | 76,106 (24,517 paused) | 250,174,812 | 241 |

* Every frame meets `FrameStart_K` and starts with `Watched`. Every instruction meets `CleanK`. Every frame ends with `Watched`.
* Every frame that ends with the routine of control ends with `controllable`. In a run that touches, every frame before the touch's frame ends with the routine of control, paused frames too. So `ctl` holds on these runs.
* The store at `q` with `X = 0` comes once on every frame that is not paused: the player's move. No other store through an index or a pointer touches `Prot_K`.
* The latest dot of an instruction is 66,674, below the limit `dotsPerFrame − 64`.

## Hypotheses (not proved in Lean)

* **`keep.clean`: `CleanK` on each instruction of each frame up to the touch, counted or not.** It is the condition of `PipeWrites`, with the three bytes added to `Prot_K` and the player's store not asked. Checked on the real frames above.
* **`keep.ctl`: each frame before the touch's frame ends with the routine of control and the task of the game core, counted or not.** Two bytes of one state. The mode is a theorem (`Frames.ctlAll`). The routine byte alone is not enough (above).
* **`keep.all`, `keep.inp`, `keep.next`, `keep.ix`: the frames are real frames one after the other from control on, and the counted frame `j` ends at `seq j`.** This says which machines the run is made of.

What stopped being a hypothesis: `fracStep` (each frame moves the position by a multiple of 1/16 px), then `noCastle` and `keep.start`, then `keep.ends` (`Frames.ends`), `keep.lag` and `keep.lagStart` (`Frames.all_start`). `CleanK` and `FrameStart_K` no longer name the jumpspring's control. What is new: `keep` (`all`, `inp`, `next`, `ix`, `ctl`, `clean`), and the checks `keepCheck` and `ControlStart.ctlCheck` on the ROM. This round the mode left `ctl`, and `keepCheckOf` became the walk with `endCtl`.

**What the change asks more.** `ctl` and `clean` now also ask of the `lag` frames what they ask of the counted frames. A `lag` frame that does not end in control is outside `ctl`. By the code, a frame of the master timer control after an injury of a big Mario is such a frame: the injury sets the routine of the injury and the master timer control together. The old `lag` and `lagStart` asked only that the castle flag, the fraction's low bits and the start of a frame in control come through the `lag` frames, so such a run could meet them. A paused frame ends in control.

**Files.** `Theorems/FrameKeep.lean`, `Theorems/ControlStart.lean`, `Theorems/PoleJoin.lean`, private `Proof/FrameKeep.lean`, `Proof/ControlStart.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta keep-check                     # the walk, as a program (about 10 s)
.lake/build/bin/smbrta keep-ctl-search                # the walk of keepCheckOf, with endCtl (about 12 s)
.lake/build/bin/smbrta keep-frames-check FM2 100      # the conditions on real frames (about 4 min)
```
