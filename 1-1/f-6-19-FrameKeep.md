[← Back](README.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# One whole frame in control keeps the castle flag and the fraction's low bits

**Claim.** A whole frame that starts in control keeps two things. The castle flag stays down. The fraction of the position stays a multiple of 1/16 px. The frame also ends at the start of the next frame in control, as far as the walk can see: in the idle loop, with the stack pointer, the dot and the PPU of a frame's start. If no instruction of the frame writes the routine byte, the mode byte or the task byte by its address, the frame ends in control. This is a theorem about any machine and any input. Its conditions are one state at the frame's start and one condition on each instruction of the frame. The proof follows the whole frame with the abstract machine of `TaintRun.lean`, as [`PipeWrites`](a-5-2-PipeWrites.md) does.

So the hypothesis `fracStep` of `PoleJoin.Run` is gone. It is the theorem `Run.fracP`, from the frames of the run (the field `keep`) and the check on the ROM. The field `noCastle` is gone too: it is the theorem `Run.noCastle_of`, from the machine at control ([The machine at control above ground](f-6-2-ControlStart.md)). The field `keep.start` (each frame starts in control) is gone: it is the theorem `Frames.start`. It needs a smaller field, `keep.ctl`: each frame before the touch ends in control.

Last round the fields `keep.ends`, `keep.lag` and `keep.lagStart` went. `keep` now lists every frame from control on, counted or not, as real frames one after the other (`all`, `inp`, `next`), and where the counted frames end (`ix`). A `lag` frame needs no rule of its own: the walk covers every frame that starts in control, paused or not. So the `lag` frames keep the castle flag, the fraction's low bits and the start of a frame in control by the same theorem as the counted frames (`Frames.all_start`), when they meet the same two conditions: `ctl` and `clean` now ask them of the `lag` frames too.

Last round `ctl` asked two bytes of each frame's end: the routine of control and the task of the game core. This round the field `ctl` is gone. The three bytes are in `Prot_K`, so under `CleanK` no store through an index or a pointer changes them. Only an instruction that names one of them by its address can. A second walk (`ctlKeepCheck`, now a part of `keepCheckOf`) cuts the paths at such instructions. Every other path ends with the three bytes still known with the values of control. So the new field `keep.noStore` says: no instruction of a frame before the touch's frame writes one of the three bytes by its address. That each such frame ends in control is a theorem (`Frames.ctlAll`). The walk comes to 8 such instructions, listed below. So `noStore` names the 8 ways a frame can leave control: the touch itself, a pipe, an injury or a power-up, a death, and others.

This round `keep` defines its counted frames: a frame is counted when it ends with the game not paused (the low bit of the pause byte 0). The counted frame `j` ends at `all(ix j)`, the `j`-th such end. So the field `ix` and its conditions are gone, and so are the fields `unpaused` and `lagPaused` of [the frames above ground](e-2-SurfaceFrames.md): they hold by the definition (`Frames.up`, `Frames.down`). A new field `many` says that `g` frames end not paused by the end of some frame `top`. And `clean` now asks `CleanK` of a guard with four more protected bytes (`guardF`): the pause byte, the area's type, the swimming flag, the change of size. So the field `spare` of the frames above ground is a part of `clean`. The walks still use `guardK`. Now the field is `cleanE`: `CleanK` of `guardE`, with five more bytes protected (`spareE`: A and B, A and B of the frame before, the moving direction, the running speed, the stored speed). So the field `spareE` of the frames above ground is a part of it too ([Each instruction of the frames up to the touch](f-6-21-GuardE.md)). `Frames.cleanF` is a theorem now.

Now `keep` has no `seq` either (item 1-1-f-6-22). It is `Keep sy m0 S a g`: the fields of `Frames` without the machines `seq` and the field `seqAt`. The machine at the end of the counted frame `j` is a definition, `Keep.seq j = S.seq(a + ix j)`, for every `j`, before the touch and after it. `Keep.toFrames` is the old `Frames` with `seq := Keep.seq`, and its `seqAt` holds by the definition. So `seqAt` is no longer a hypothesis, and the frames after the touch, up to the castle entry, are real frames of the run ([From control to the castle](f-5-PoleJoin.md), the field `toCastle`). [The frames above ground](e-2-SurfaceFrames.md) still take `Frames`, as `keep.toFrames`.

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
Prot_F           :=  Prot_K  ∪  {pause, AreaType, SwimmingFlag, PlayerChangeSizeFlag}        (spareK; pause is the pause byte of CtrlKeep)
CleanK_F(m)      :=  CleanK(m) with Prot_F for Prot_K                                          (CleanK of guardF)
cleanK_of_F      :  CleanK_F(m)  →  CleanK(m)
Prot_E           :=  Prot_F  ∪  {A_B_Buttons, PreviousA_B_Buttons, Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}   (spareE; and collE, speedE, vertE: 1-1-f-6-21)
CleanK_E(m)      :=  CleanK(m) with Prot_E for Prot_K                                          (CleanK of guardE)
cleanK_of_E      :  CleanK_E(m)  →  CleanK_F(m)
```

`Plain(Prot_K, t)` says that the store changes no byte of `Prot_K`. The store at `q` with `X = 0` is the player's own store of the fraction, so it is not asked.

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))
keep_frame_start  :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  Known_K(frame(m, i))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

RealRun S         :  S.seq n, S.inp n,  S.seq(n + 1) = frame(S.seq n, S.inp n)      the real frames of the whole run
up(n)             :=  pause(all n) & 1 = 0                                  the frame that ends at all n ends not paused
upTo(n)           :=  #{ k ∈ [1, n] : up(k) }
ix j              :=  min { n ≤ top : j ≤ upTo(n) }                         the j-th frame that ends not paused (definition, ixOf)
Frames (keep)     :  all n := S.seq(a + n),  inp n := S.inp(a + n)        the machine when frame n begins, counted or not, and its input (definitions)
                     next    :  all(n + 1) = frame(all n, inp n)              (the theorem Frames.next)
                     seq0    :  seq 0 = S.seq a                                (the theorem Frames.seq0)
                     top, many :  g ≤ upTo(top)                                 g frames end not paused by the end of frame top
                     seqAt   :  j ≤ g → seq j = all(ix j)                       the counted frame j ends at seq j
                     noStore :  n + 1 < ix g  →  ∀ k,  ¬CtlStore(tr_n(k))
                     cleanE  :  n < ix g  →  ∀ k,  CleanK_E(tr_n(k))               tr_n:  the instructions of the frame from all n
Keep (keep)       :  top, many, noStore, cleanE as in Frames;  no seq, no seqAt
Keep.seq j        :=  S.seq(a + ix j)                                       for every j (definition)
Keep.toFrames     :  Frames with seq := Keep.seq;  seqAt by the definition
Keep.up_at        :  1 ≤ j ≤ upTo(top)  →  pause(seq j) & 1 = 0             before the touch and after it
Keep.ends_at      :  1 ≤ j ≤ upTo(top)  →  seq j = frame(all(ix j − 1), inp(ix j − 1))
Frames.ix0        :  ix 0 = 0
Frames.order      :  j < g  →  ix j < ix(j + 1)
Frames.up         :  1 ≤ j ≤ g  →  pause(seq j) & 1 = 0                      the old field unpaused of OnFrames
Frames.down       :  1 ≤ j ≤ g,  ix(j − 1) ≤ n,  n + 1 < ix j  →  pause(all(n + 1)) & 1 = 1      the old field lagPaused of OnFrames
Frames.cleanF     :  n < ix g  →  ∀ k,  CleanK_F(tr_n(k))                    the field cleanF of before
Frames.clean      :  n < ix g  →  ∀ k,  CleanK(tr_n(k))
fm j  :=  all(ix j − 1),   pad j  :=  inp(ix j − 1)                       where the counted frame j begins, and its input
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 the machine at control
Frames.ends       :  keep  →  ∀ j,  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
Frames.all_start  :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ n < ix g,  FrameStart_K(all n)  ∧  Watched(all n)
Frames.all_watched:  the same   →   ∀ n ≤ ix g,  Watched(all n)
Frames.run        :  the same   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  the same   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  the same   →   ∀ j ≤ g,  Watched(seq j)
Frames.ctlAll     :  the same   →   ∀ n,  n + 1 < ix g  →  controllable(all(n + 1))

CtlStore(m)       :=  the instruction at pc(m) is STA, STX, STY, INC, DEC, ASL, LSR, ROL or ROR, zero page or absolute,
                      and its address (mod 2048, below 0x2000) is GameEngineSubroutine, OperMode or OperMode_Task
keep_frame_startC :  ctlKeepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  (∀ n,  ¬CtlStore(tr(n)))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

endCtl(B)         :  rt(B) is known not to be control  ∨  the task is known not to be core  ∨  the mode is known to be game
ctl_of_frame      :  keepCheckOf,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  rt(frame(m, i)) = control,  task(frame(m, i)) = core
                       →   controllable(frame(m, i))

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  the same  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  the same  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` is `posP(seq(j − 1))`, read from the machines (`frames.reads`). `AtCtl(seq 0)` is a theorem on a real run: `ControlStart.EndRun.atCtl`, from the rows of the change out of the side pipe ([The machine at control above ground](f-6-2-ControlStart.md)).

`Frames.all_start` is an induction on `n`, over every frame, counted or not. The frame `n` begins at `all n` with `FrameStart_K` and `Watched`. It ends at `all(n + 1)` (`next`). `keep_frame_startC` gives `FrameStart_K(all(n + 1))` and `Watched(all(n + 1))`, with `noStore` on the frame `n`. The touch's frame, the last one (`n = ix g − 1`), is not asked to end in control: there the routine changes. `keep_frame` gives `Watched(all(ix g))` without it (`Frames.all_watched`). The theorems on the counted frames read these at `seq j = all(ix j)` and `fm j = all(ix j − 1)`: `ix` grows, so `ix j ≤ ix g` (`Frames.ix_mono`).

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

**The walk of the frames before the touch (`ctlKeepCheck`)** is the same walk, with one more rule: a path stops at an instruction that writes the routine, the mode or the task by its address (`walkKC`). By the hypothesis `noStore` the frame does not come there. At each frame's end it asks `Watched`, `endOK`, and the three bytes known with the values of control (`knownAll`). Then `endOK` and the three bytes give `FrameStart_K` of the next frame (`start_of_sim`), and the values give `controllable` (`ctl_of_known`). The ROM has 37 instructions that write one of the three bytes by its address. The walk comes to 8 of them:

| place in the code | what it writes |
|---|---|
| `PlayerHole` | the routine of losing a life: a fall into a pit |
| `ChgAreaMode` | the task 0: an area change |
| `SetPRout` | the routine of an injury, of a death by an enemy or by the time, or of a power-up |
| the side pipe's entry (after `ChkGERtn`) | the routine of the side pipe |
| `HandleAxeMetatile` | the task 0 (and then the mode): the axe |
| `RunFR` (the pole) | the routine of the pole: the touch |
| `VineCollision` | the routine of the climb at the top of the screen |
| the vertical pipe's entry | the routine of the vertical pipe |

The check `keepCheckOf` (`keep_check` in the private proof) is the first two rows of the table: both walks. The frame's ends: all with `endOK` and `endCtl` in the first; all with `endOK` and the three bytes of control in the second.

| walk | steps | forks | failures | table | time |
|---|---|---|---|---|---|
| castle flag and fraction, 9 pieces, the mode and the task in the key, `endOK` and `endCtl` at the ends (`keepCheckOf`, its first part) | 707,869 | 69,388 | 0 | 46,576 | search 2.8 s, check 3.9 s in a program |
| the same, with the paths cut at the writes of the three bytes, `endOK` and the three bytes of control at the ends (`ctlKeepCheck`, this round) | 67,115 | 6,987 | 0 | 4,520 | search 0.1 s, check 0.2 s in a program |
| castle flag and fraction, 9 pieces, `endOK` at the ends (`keepCheck`, the last round) | 707,685 | 69,404 | 0 | 46,573 | check 3.8 s in a program, `Proof.FrameKeep` 5.0 s |
| the same, with the jumpspring's control known to be 0 at the start and in `Prot_K` (the last round) | 1,044,377 | 101,574 | 0 | 79,266 | check 4.9 s in a program |
| castle flag only, no pieces | 907,094 | 92,482 | 0 | 72,016 | check 4.5 s |
| castle flag and fraction, `X` split into 256 values | 9,779,840 | 767,686 | 0 | 355,602 | check 32 s |

## On real frames

`keep-frames-check FM2 100`, after the last change, with the guard `guardE` of `cleanE` (exit 0, bad 0). Every frame from control above ground up to the touch, including the touch's frame, counted or not. The first four kinds of run have no Start, so no `lag` frames. The fifth presses Start on one frame and again 10 to 49 frames later; it does not reach the pole. The last starts from the movie's frames 1002 to 1091 and presses Start on one frame and again 44 to 73 frames later, after the pause timer, so that the game goes on: 241 of these runs touch, with 12,671 paused frames before their touches.

| run | runs | frames | instructions | touches |
|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1,203,506 | 1 |
| random inputs from control | 100 | 29,102 | 150,058,083 | 0 |
| random inputs from the movie's frames 1002 to 1091 | 400 | 46,025 | 183,000,496 | 216 |
| into the screen's left edge, then random | 120 | 35,945 | 193,591,853 | 0 |
| random inputs with a pause, from control | 100 | 37,395 (26,341 paused) | 107,816,920 | 0 |
| random inputs with a pause, from the movie's frames 1002 to 1091 | 400 | 76,106 (24,517 paused) | 250,174,812 | 241 |

* Every frame meets `FrameStart_K` and starts with `Watched`. Every instruction meets `CleanK`. Every frame ends with `Watched`.
* Every frame that ends with the routine of control ends with `controllable`. In a run that touches, every frame before the touch's frame ends with the routine of control, paused frames too.
* In a run that touches, no frame before the touch's frame has an instruction that writes the routine, the mode or the task by its address. So `noStore` holds on these runs. Frames with such an instruction: 1 in the movie and 216 and 241 in the runs from the movie's frames, all touch's frames (`RunFR` and then the end of the level, on a direct grab); 44, 7 and 15 in the random runs from control, the runs into the left edge and the runs with a pause from control, all at `SetPRout`, in runs that do not touch.
* Every frame that meets the conditions and has no such instruction ends with `controllable` (as `keep_frame_startC` and `ctl_of_known` say).
* The store at `q` with `X = 0` comes once on every frame that is not paused: the player's move. No other store through an index or a pointer touches `Prot_E` (so none touches `Prot_F` or `Prot_K`).
* The latest dot of an instruction is 66,674, below the limit `dotsPerFrame − 64`.

**The counted frames.** `count-frames-check FM2 100` (exit 0, bad 0, about 40 s) runs the frames from control up to the touch, the touch's frame included, and compares the two ways to count a frame: it ends not paused (`up`, the definition of `keep`), or its phase moves (`CastleToLevel.kindOf` is not `lag`, the way the clock counts). It presses Start at random (about one frame in 41), and on one of the frames before the movie's touch and again 45 frames later.

| run | runs | frames | ending paused | the two ways disagree | touches | touches ending paused | stores through an index to `spareK` |
|---|---|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 0 | 0 | 1 | 0 | 0 |
| random inputs from control (a third with Start) | 100 | 30,830 | 6,905 | 0 | 0 | 0 | 0 |
| random inputs from the movie's frames 1002 to 1091 (half with Start) | 400 | 52,237 | 15,990 | 0 | 170 | 0 | 0 |
| Start on one of the 11 frames before the movie's touch | 77 | 6,542 | 2,970 | 0 | 32 | 0 | 0 |

So on these runs the counted frames of `keep` are the frames the clock counts, and with `top` the touch's frame `many` holds: the touch's frame ends not paused.

**Which writes of the three bytes the frames above ground come to (`noStore`).** `keep-reach-search` runs the search of `ctlKeepCheck` from the start of a frame in control, with what is proved of every frame before the touch's frame: the castle flag down, the fraction's low bits 0, and the area's type of control, the swimming flag 0, the change of size 0 (`OnFrames.areaAll`), with `guardF`. It still comes to all 8 places of the table above (125,034 steps, a table of 7,574 states, 0.4 s). So no fact proved so far rules out any of them. What each needs, by the code:

| place | what it needs | proved? |
|---|---|---|
| `PlayerHole` | he is below the screen (a pit) | no: the height after frame 8 is assumed (1-1-f-6-4, 1-1-f-6-5) |
| `ChgAreaMode` | from a frame in control, by the code only through `PlayerHole` on a cloud level | no, as `PlayerHole` |
| `SetPRout` | an enemy or a power-up touches him, or the time runs out | no: no enemy near the flag is assumed (1-1-f-6-14). On real runs from control it comes 44 times, in runs that do not touch |
| the side pipe's entry | a side pipe's tile at his side | no: the map is assumed (1-1-f-6-6) |
| `HandleAxeMetatile` | the axe's tile at his feet | no: the map |
| `RunFR` | the pole's tile at his side: the touch | the touch's frame. A frame before it that comes here is a touch, so it says that `g` is the first touch |
| `VineCollision` | a vine's tile, high on the screen | no: the map |
| the vertical pipe's entry | Down, and a warp pipe's top at his feet | no: the map |

On the real runs above, the frames before a touch's frame come to none of them; the touch's frames come to `RunFR`.

**Enemies at control (1-1-f-6-14).** A condition on the enemy slots at control above ground, kept by the walk, cannot rule out `SetPRout`. On the movie two enemies are loaded at control: at frame 852 two slots have the flag 1 and the kind Goomba (`tas-peek FM2 852 1092` on `Enemy_Flag` and `Enemy_ID` of the disassembly). They leave their slots by frames 951 and 1011. The area's parser loads the pole's flag into a slot by frame 1011, and the castle's flag by frame 1051. So the slots are not empty at control, and the frames fill them from the map, which the walk does not know. Whether an enemy touches him depends on his path, not on one state. On the random runs from control above, the 44 frames at `SetPRout` are all in runs that do not touch.

## Hypotheses (not proved in Lean)

* **`keep.cleanE`: `CleanK_E` on each instruction of each frame up to the touch, counted or not.** It is the condition of `PipeWrites`, with the three bytes, the four bytes of `spareK` and the five bytes of `spareE` added to the protected bytes and the player's store not asked. It holds the old fields `spare` and `spareE` of [the frames above ground](e-2-SurfaceFrames.md), and asks them of the touch's frame too. Checked on the real frames above.
* **`keep.noStore`: no instruction of a frame before the touch's frame, counted or not, writes the routine, the mode or the task by its address.** A condition on each instruction. The walk comes to 8 such places (above); each of them is a way to leave control. That the frames end in control is a theorem (`Frames.ctlAll`). `noStore` with the walk gives the old `ctl`, so it is not weaker than `ctl`; it names the places in the code instead of the bytes at the end.
* **`keep.top`, `keep.many`: `g` frames end not paused by the end of frame `top`.** The counted frame `j` ends at `seq j = S.seq(a + ix j)`, a definition (the field `seqAt` is gone). This says which machines the run is made of. Which frames are counted is a definition: the frames that end not paused. The frames themselves are no longer fields: `Frames` takes the real frames of the whole run (`RealRun`) and the frame `a` of control, and `all n = S.seq (a + n)`, `inp n = S.inp (a + n)` are definitions; `next` and `seq 0 = S.seq a` are theorems (`Frames.next`, `Frames.seq0`). So the machine at control above ground is the run's machine at the end of the second change (`Route.Run.atCtl`, item 1-1-0-4).

What stopped being a hypothesis: `fracStep` (each frame moves the position by a multiple of 1/16 px), then `noCastle` and `keep.start`, then `keep.ends` (`Frames.ends`), `keep.lag` and `keep.lagStart` (`Frames.all_start`). `CleanK` and `FrameStart_K` no longer name the jumpspring's control. What is new: `keep` (`all`, `inp`, `next`, `ix`, `ctl`, `clean`), and the checks `keepCheck` and `ControlStart.ctlCheck` on the ROM. Then the mode left `ctl`, and `keepCheckOf` became the walk with `endCtl`. Then `all`, `inp`, `next` left the fields (definitions from `RealRun`). Then `ctl` left the fields, and `noStore` came; `keepCheckOf` has the second walk `ctlKeepCheck`. This round `ix` (with `ix0` and `order`) left the fields, and `top`, `many`, `seqAt` came; the fields `unpaused`, `lagPaused`, `spare` of the frames above ground are gone; `clean` became `cleanF`. Then `seq` and `seqAt` left (`Keep`; `seq` is a definition on every frame). Then `cleanF` became `cleanE` (five more bytes), and the field `spareE` of the frames above ground left.

**What the change asks more.** `noStore` (before it `ctl`) and `clean` also ask of the `lag` frames what they ask of the counted frames. A `lag` frame that does not end in control is outside `noStore`. By the code, a frame of the master timer control after an injury of a big Mario is such a frame: the injury sets the routine of the injury and the master timer control together. The old `lag` and `lagStart` asked only that the castle flag, the fraction's low bits and the start of a frame in control come through the `lag` frames, so such a run could meet them. A paused frame ends in control.

**Files.** `Theorems/FrameKeep.lean`, `Theorems/ControlStart.lean`, `Theorems/PoleJoin.lean`, private `Proof/FrameKeep.lean`, `Proof/ControlStart.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta keep-check                     # the walk, as a program (about 10 s)
.lake/build/bin/smbrta keep-ctl-search                # the walk of keepCheckOf, with endCtl (about 12 s)
.lake/build/bin/smbrta keep-store-search              # the walk with the writes of the three bytes cut (ctlKeepCheck), and both walks of keepCheckOf (about 4 s)
.lake/build/bin/smbrta keep-frames-check FM2 100      # the conditions on real frames, with guardE (about 4 min)
.lake/build/bin/smbrta count-frames-check FM2 100     # the counted frames, the touch's frame, the stores to spareK (about 40 s)
.lake/build/bin/smbrta keep-reach-search              # the places of noStore that the walk comes to, with the facts proved at a frame's start (about 1 s)
```
