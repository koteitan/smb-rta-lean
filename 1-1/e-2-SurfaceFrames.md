[← Back](README.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# Above ground: the frames from control, one by one

**Claim.** [From control to the castle](f-5-PoleJoin.md) assumed the statements about a whole run `model`, `hit`, `stop`, `box`, `off`, `next`, `startP`, `startV`. They are theorems now. The assumptions that stay are about one frame. On frames 1 to 8 the vertical step (`vstep`) is a theorem on real machines too; what stays there is that the frame after the scroll handler keeps the vertical bytes. The part of each frame from its start to the player's routine is a theorem now: a walk of that part ([`CtrlKeep`](#the-frame-up-to-the-players-routine)) shows that it keeps 25 bytes and comes to the routine in the state the movement needs. So the fields `vBefore`, `Moves.at_ctrl`, `Moves.before`, `Moves.bits` are gone. The frame's two ends are theorems too, from conditions on one machine or one frame: a counted frame ends with the game not paused, so it comes to the player's routine (`Moves.arrive` is gone, new: `unpaused`); a frame not counted does not come to the player's routine, so it keeps the 25 bytes (`Moves.lag` is gone). A walk of the rest of the frame, from the player's routine to the frame's end ([below](#the-whole-frame-from-the-players-routine-to-its-end)), now shows that a frame that comes to the routine ends not paused, and that every frame in control keeps the area's type, the swimming flag and the change of size. So that a frame not counted does not come to the routine is a theorem (`OnFrames.lagNo`; new: `lagPaused`, a frame not counted ends paused), and so are three of the values of `state`. The new condition on each instruction is `spare`: no store through an index or a pointer writes these four bytes. The frames are those of the field `keep` of `Run` ([One whole frame in control](f-6-19-FrameKeep.md)), so the field `ends` is gone too. A frame where the side he presses is masked is a theorem too: the field `masked` is gone. Two more conditions of `moves` are theorems now ([The frame's time and the position's range](#the-frames-time-and-the-positions-range)): the frame does not end during the movement (`Moves.longer` is gone; it follows from the walks of the movement and the condition `time` of `CleanK`), and the position is far from the ends of its range (`Moves.far` is gone; it follows from the position at control and the frames before, which follow `hstep`). `startP`, `startV` are proved on real machines. They come from the last row of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). The conditions are those of that change, and that `left` is not 0 before control. Two more parts of `moves` are theorems now. `state.prevA` is gone: every frame in control keeps bit 7 of A and B of the frame before equal to that of A and B (`OnFrames.prevAll`, [below](#a-and-b-of-the-frame-before)). The fields `md` and `rs` of `After` are gone, and its `stored` is now `storedQ`, a condition on the machine at the scroll handler: the moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler (`AfterKeep.keepH`, [below](#after-the-scroll-handler-three-bytes)). The new condition on each instruction is `spareE`: no store through an index or a pointer writes these five bytes.

The unit is 1/256 px. `seq j` is the machine at the end of the counted frame `j`. `seq 0` is the machine at control. `B.m` is the machine at control that the private proof holds.

## One frame

Read a frame `a → b` on the input `i`. `hs(m)` is the horizontal state, `P(m)` the position, `v(m)` the speed, `abs(m)` the stored speed, `bits(m)` the collision bits, `vs(m)` the vertical bytes.

```
inAt(M, x, n)     : the input as the player's routine reads it, at instruction n of the frame of M with the pad x
                    (FrameModel.readIn); Select and Start read as Up
inAt_mem          : inAt(M, x, n) ∈ inputs                       from modelOK, for any machine

t = hstep(hs a, i)     v₂ = v(t)     P₂ = P(a) + 16·v₂

Clean(m)          : inD(hs m) ∧ abs(m) = |v(m)| ∧ (bits(m) = FF ∨ (bits(m) = noLeft ∧ 0 < v(m)))
Pre(i, a, b)      : hs(b) is t except for v ∧ abs(b) = |v₂|
Hit(i, a, b)      : v(b) ≤ 0 ∧ (P(b) ≤ P₂ − 256 ∨ P(b) ≤ P(a) + 256)
Coll(i, a, b)     : (P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = FF)
                  ∨ (0 < v₂ ∧ P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = noLeft)
                  ∨ Hit(i, a, b)
MaskStop(a, b)    : bits(a) = noLeft ∧ v(b) ≤ 0 ∧ P(b) ≤ P(a) + 256
OneFrame(i, a, b) : MaskStop(a, b) ∨ (Pre(i, a, b) ∧ Coll(i, a, b))
```

`Follow(i, a, b)` has the form of `RoomJoin.Follow` of [the bonus room](c-5-RoomJoin.md): `fr.hs n = hs(seq n)`, `fr.P n = P(seq n)`. The input of the counted frame `j` is `inp(j) = inAt(fm j, pad j, arr j)`, with `arr j` the first instruction of the frame at the player's routine (next section). It used to be `readIn(a, b)`, read from the two ends of the frame, and a field `input` said that the two are the same. Now the input is the one the routine reads, so that field is gone.

## One frame on the real machine

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel.md) proves the movement of a real frame: from the player's routine to the scroll handler, `hs` follows `hstep` and `P` moves by `16·v₂`. So `OneFrame` is a theorem from what the frame does outside the movement.

`fm j` is the machine when the counted frame `j` begins: `seq (j − 1)`, or later by `lag` frames. `pad j` is its input. Both come from the field `keep` of `Run` (`FrameKeep.Frames`). `arr j = arrAt(fm j, pad j)` is the first instruction at which the frame is at the player's routine (`CtrlKeep.arrAt`: the first `n ≤ fuelPerFrame` with `pc(trM(n)) = PlayerCtrlRoutine`; it was data in `OnFrames` before, now it is a definition). `R` is the machine there, and `Q` the machine when the frame comes to the scroll handler. `b = frame(M, i)` is the machine at the frame's end.

```
Masked(i, a)       : bits(a) & lr ≠ lr            lr = the Left/Right that hstep reads from i

After(a, Q, b)     : f, fd of b are those of Q ∧ abs(Q) = |v(Q)|
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)) )
AfterK(a, Q, b)    : After(a, Q, b) ∧ md, RunningSpeed, abs of b are those of Q        the three bytes are a theorem (AfterKeep.keepH)

MovesAt(a, M, x, n₀) : AtCtrl0(R)                                  the state at the player's routine, as FrameModel needs it, but the mask
                       ∧ the 8 horizontal bytes of R are those of a    nothing writes them from a to R
                       ∧ bits(R) = bits(a)                             nor the collision bits
                       ∧ frame(R) = frame(M)                           the routine comes in the frame of M (Arrive)
                       ∧ ∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64     the condition time of CleanK
                       ∧ idleAt(idle) ∧ far(a) ∧ after                 the idle loop is a JMP to itself; far, after below
                       ∧ keepH                                         md, RunningSpeed, abs at the frame's end are those at each Q (AfterKeep.keepH)

CtlState(a)        : Player_State(a) ∈ {0, 1, 2} ∧ JumpspringAnimCtrl(a) = 0
PrevOK(a)          : PrevA(a) & 80 = A_B(a) & 80                                         a theorem for every frame (OnFrames.prevAll)
AreaOK(v, a)       : AreaType(a) = v ∧ SwimmingFlag(a) = 0 ∧ PlayerChangeSizeFlag(a) = 0      a theorem for every frame (OnFrames.areaAll)
AreaRun(v)         : v = AreaType(B.m) ∈ {1, 2, 3} ∧ afterCheck(v) ∧ hCheck(v) ∧ ∀ n < ix g, AreaOK(v, all n)

Arrive(M, x, n₀)   : pc(trM(n₀)) = PlayerCtrlRoutine, in the frame of M, and no instruction before n₀ is there

Moves(a, M, x, n₀) : state    CtlState(a)
                     after    After(a, Q, b) at every Q at the scroll handler
far(a)             : 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴

Moves.toAt    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Clean(a) ∧ Arrive(M, x, n₀) ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ AreaOK(v, a) ∧ v ∈ {1, 2, 3}
                ∧ far(a) ∧ idleAt(idle) ∧ keepH ∧ Moves  →  MovesAt
at_subs       : modelOK ∧ MovesAt ∧ ¬Masked  →  ∃ Q at the scroll handler, hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_moves  : modelOK ∧ MovesAt ∧ ¬Masked  →  Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)
at_subsM      : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  ∃ Q at the scroll handler, (hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∨ v(Q) = 0)
                                                                  ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_movesM : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  OneFrame(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ Clean(seq (j − 1)) ∧ far(seq (j − 1)) ∧ idleAt(idle)  →  OneFrame(inp j, seq (j − 1), seq j)
```

`keepA` and `StartK`, `CleanK`, `ctrlCheck` are in the next section. `all n` are the frames of `keep`, counted or not, and `ix g` is the touch's frame. `StartK(all n)` is the theorem `FrameKeep.Frames.all_start`, from the machine at control; `CleanK` on each instruction is the field `keep.clean`. The other conditions of `Moves.toAt` are theorems (`OnFrames.arrive`, `OnFrames.lagKeep`, next section; `keepH` from `AfterKeep.keepH` in `OnFrames.movesAt`).

`idle` is the idle loop (`EndlessLoop`), and `idleAt(idle)` says that it is a `JMP` to itself: a check on the ROM in `numbersCheck`. `modelOK` is the check on the ROM of `FrameModel`. It is a part of `numbersCheck` now, so the private proof computes it by `native_decide` (about 3 s more). `move_model` needs that the side he presses is not masked; with `bits(R) = bits(a)` this is `¬Masked`.

**The masked frames.** On a frame where the side he presses is masked (`Masked`), the routine of the friction reads the mask and `hstep` does not. [`FrameModel.move_masked`](../0-0/0-3-2-FrameModel.md) proves that the frame still follows `hstep`, or it leaves the speed 0. A clean state with the side masked has the bits of a block of Left and moves right (`masked_clean`). With the speed 0 at the scroll handler, `After` gives `MaskStop`. `maskOK` is the check on the ROM of `move_masked` (about 0.1 s); it is a part of `numbersCheck`.

The fields that are assumed (`OnFrames`). All are in the field `frames` of `Run`. `fm`, `pad` are those of `keep`.

```
reads    : 1 ≤ j ≤ g   →  v, f, P at the start of fr j are those of seq (j − 1)
           1 ≤ j < g   →  v', f', P' at the end of fr j are those of seq j
moves    : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)
vAfter   : 1 ≤ j < J, j < g, Q at the scroll handler  →  at seq j the vertical bytes and A are those of Q
box      : 1 ≤ j < J, j < g, Q at the scroll handler  →  from Q to seq j the collision routine does what it does
           on B.m at (pix P(Q), y, w, vy, st)          (y, vy, st) is vstep's result, w stands for the speed's sign
spareE   : n < ix g  →  each instruction of the frame of all n meets SpareE (below)
```

`pause` is the pause byte (`GamePauseStatus`), read from the ROM: the operand of the load just before the NMI's call of the mode's routine (`CtrlKeep.pauseA`). Its low bit is 1 while the game is paused. The pause routine sets and clears it.

The fields `unpaused`, `lagPaused` and `spare` are gone. A frame of `keep` is counted when it ends with `pause & 1 = 0`: this is now the definition of `ix` ([One whole frame in control](f-6-19-FrameKeep.md)). So a counted frame ends not paused (`Frames.up`, the old `unpaused`) and a frame not counted ends paused (`Frames.down`, the old `lagPaused`). The old `spare` is a part of `keep.clean`: its guard `FrameKeep.guardF` protects the four bytes of `spareI` too.

The frame's end is the field `keep.ends` of `Run`: `1 ≤ j ≤ g → seq j = frame(fm j, pad j)` (`OnFrames.ends`, a theorem). The vertical bytes are `y, mf, vy, dummy, vf, vfd, origin, st, DTHJ`. `DTHJ` is `DiffToHaltJump`, `A` is bit 7 of `A_B_Buttons`, `PrevA` is `PreviousA_B_Buttons`.

**The vertical step is a theorem.** [`VertModel.vert_model`](../0-0/0-3-2-FrameModel.md) proves that from the player's routine to the scroll handler the vertical bytes follow `vstepV`: `vstep` on the machine with the stack pointer of the player's routine and `DTHJ = 1`.

```
HaltOK(m)  : st(m) = 1 → DTHJ(m) = 1
vNext(a, b) = vstepV(vs(a), A(b), abs(a))
vBefore    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Arrive ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ PrevOK(a)  →  at R the vertical bytes and A are those of a,
               and PrevA(R) & 80 = A_B(R) & 80                        (the old field vBefore)
vert_of    : vertOK ∧ ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ far(seq (j − 1)) ∧ idleAt(idle) ∧ HaltOK(seq (j − 1)) ∧ PrevOK(seq (j − 1))
               →  vs(seq j) = vNext(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

`HaltOK(seq 0)` holds because the state at control is not a jump (in `numbersCheck`), and `PrevOK(seq (j − 1))` comes from `OnFrames.prevAll`. So `quiet_upto` proves `vs(seq j) = vNext(...)` and `HaltOK(seq j)` for every `j < J` by induction, with the other facts. `vertOK` is a part of `numbersCheck` (about 0.1 s more).

| Field before | Now |
|---|---|
| `step`: every clean frame is a `OneFrame` | `moves` (the frame outside the movement), `ends` |
| `masked`: a frame with the pressed side masked is a `OneFrame` | theorem `one_of_movesM` (from `moves` and `FrameModel.move_masked`). New: `Moves.bits`; `Moves.at_ctrl` is `AtCtrl0`, with no condition on the mask |
| `reads`: `v₂(fr j) = v₂` | gone. `box` is on the real machines `Q` and `seq j`, so the frame's `v₂` is not needed |
| `box` on `fr j` | `box` on the real machines, from the scroll handler |
| `Moves.input`: the routine reads `readIn(a, b)` | gone. The model's input is the one the routine reads |
| `vert`: frames 1 to 8 follow `vstep` | theorem `vert_of`. New: `vBefore`, `vAfter` (the frame outside the movement routine keeps the vertical bytes) |
| `vBefore`: up to the player's routine the vertical bytes and A are those of the frame before, and PrevA is A | theorem `vBefore` (was `Moves.vBefore`), by the walk of `CtrlKeep`. It uses `OnFrames.lagKeep` and `PrevOK` of the frame before (`OnFrames.prevAll`) |
| `Moves.at_ctrl`: `AtCtrl0` at the player's routine | theorem `Moves.toAt`, by the walk. New: `Moves.state` (`CtlState` at the end of the frame before) |
| `Moves.before`, `Moves.bits`: nothing writes the horizontal bytes and the collision bits up to the routine | theorem `Moves.toAt`, by the walk |
| `Moves.arrive`: the frame comes to the routine at `arr j`, the first time, before its end | theorem `OnFrames.arrive`, by the walk with the pause bit, and `Frames.up` (the counted frame ends with the pause byte's low bit 0, by the definition of the counted frames) |
| `Moves.lag`: the frames not counted between `seq (j − 1)` and `fm j` keep the 25 bytes of `keepA` | theorem `OnFrames.lagKeep`, by the walk, frame by frame. New: `lagNo` (a frame not counted does not come to the player's routine) |
| `lagNo`: a frame not counted does not come to the player's routine | theorem `OnFrames.lagNo`, by the walk of the whole frame (`area_endF`), and `Frames.down` (a frame not counted ends paused, by the definition) |
| `state`: the area's type, the swimming flag, the change of size at the end of the frame before | theorem `OnFrames.areaAll`, by the walk of the whole frame and induction over the frames of `keep` from control, with `keep.clean`. `Start` has the three bytes, from the rows; `numbersCheck` asks their values on `B.m` |
| `arr`: data, the instruction of the arrival | the definition `CtrlKeep.arrAt`: the first instruction at the routine |
| `ends`, and the data `fm`, `pad` | `keep.ends`, `keep.fm`, `keep.pad` of `Run`: one set of frames for both |
| `Moves.longer`: the frame does not end within 728 instructions after the player's routine | theorem `FrameModel.trace_inFrame`, from the walks of the movement (`InFrameN`) and the condition `time` of `CleanK` (`keep.clean`). New: `idleAt(idle)`, a check on the ROM in `numbersCheck` |
| `Moves.far`: the position at the frame's start is at least 8 px from the ends of its range | theorem `far_of_follow`, from `Start` and the frames before, which follow `hstep`. New: the check `far` of `SurfaceRun.allCheck` on `B.m` |
| `CtlState.prevA`: bit 7 of A of the frame before is that of A at the end of the frame before | theorem `OnFrames.prevAll`, by the walk after the cut (`PrevKeep.prev_end`) with the stores of `noStore` cut, and induction from control. New: `spareE` (two of its bytes), `Start.ab`, `Start.prev` (from the rows), the checks `prevCheck` and `PrevOK(B.m)` in `numbersCheck` |
| `After.md`, `After.rs`, `After.stored`: the moving direction, whether the running speed is 0, the stored speed at the frame's end | theorem `AfterKeep.keepH`: the three bytes at the frame's end are those at the scroll handler. `stored` became `storedQ` (abs(Q) = abs of v(Q), on the machine at the scroll handler). New: `spareE` (three of its bytes), the check `hCheck` in `numbersCheck` |

## The frame's time and the position's range

**The time.** The walks of the movement ([`FrameModel`](../0-0/0-3-2-FrameModel.md#the-time-of-a-walked-step)) now say that each step on the way meets `InFrame`: the machine is not halted, it is not at the idle loop, and its step keeps the frame if the frame has 64 dots or more left. Each instruction of the frame of `keep` meets `CleanK`, whose condition `time` says that an instruction not at the idle loop runs at a dot at most `dotsPerFrame − 64`. So the frame does not end during the movement, and the instructions after the player's routine are the steps of the walk (`trace_inFrame`). The vertical walk (`vert_model`) and the masked frame (`move_masked`) are the same.

```
trace_inFrame : idleAt(idle) ∧ frame(R) = frame(M) ∧ InFrameN(R, k) ∧ (∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64)
                →  ∀ j ≤ k,  trM(n₀ + j) = stepN(j, R)
```

**The range.** `far(a)` is needed where `one_of_frames` is used: at the first frame `h` that does not follow `hstep` into a clean state, and on the frames before `J` (`quiet_upto`). On both, the frames before follow `hstep`, so `P(seq (j − 1)) = P(B.m) + d(w)` with `w` their inputs. Each frame of `hstep` moves at most `16·v_top` either way (`hdist_abs`), and `j − 1 ≤ T`. The check `far` of `SurfaceRun.allCheck` gives `2048 + 16·v_top·T ≤ P(B.m)` and `P(B.m) + 16·v_top·T + 2048 < 2²⁴`.

```
hdist_abs      : inD(s), w ∈ I*  →  −16·v_top·|w| ≤ d(s, w) ≤ 16·v_top·|w|
far_of_follow  : numbersCheck ∧ Start(B, seq 0) ∧ SurfaceRun.far ∧ d ≤ T ∧ frames 1..d follow hstep  →  far(seq d)
```

The private proof checks `far` on `B.m` with `T = 233` (`surface_checks`).

## The frame up to the player's routine

A frame in control runs the screen update, the sound, the pad, the pause and the timers, then the mode's routine, which calls the player's routine. `CtrlKeep` follows this part with the abstract machine of `TaintRun`, as [Frames not counted](a-5-5-3-LagFrames.md) follows a frame to the call of the mode's routine. One byte is followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on any write to it. The walk stops the first time the frame comes to the player's routine (the cut), and there it asks that the byte is still followed. There is one walk for each of the 25 bytes of `keepA`.

```
keepA      = the 8 horizontal bytes (FrameModel.hBytes), Player_CollisionBits, Player_XSpeedAbsolute, AreaType, JumpspringAnimCtrl,
             SwimmingFlag, PlayerChangeSizeFlag, the 9 vertical bytes (vKeep), A_B_Buttons, PreviousA_B_Buttons
StartK(m)  : m is in the idle loop at the start of a frame in control (FrameKeep: the stack, the dot, the PPU, the routine, the mode, the task)
CleanK(m)  : the condition of FrameKeep on one instruction
trM(n)     : the machine n instructions into the frame of M

ctrl_keep  : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pc(trM(k)) = PlayerCtrlRoutine ∧ trM(k) in the frame of M ∧ (∀ j < k, pc(trM(j)) ≠ PlayerCtrlRoutine)
             →  ∀ y ∈ keepA, y(trM(k)) = y(M)
                ∧ S(trM(k)) = the stack of the player's routine ∧ no NMI pending ∧ the NMI off ∧ GameEngineSubroutine(trM(k)) = control
```

At the cut the walk also asks the stack pointer, no NMI pending, bit 7 of the PPU's control 0, and the routine byte. With these, `ctrl_keep` gives `AtCtrl0` at `R` but the values of `AreaType`, `Player_State`, the jumpspring, swimming and the change of size, and the stored speed. Those come from `OnFrames.lagKeep` and `Moves.state`, and the stored speed from `Clean(a)` (`Moves.toAt`).

**The frame's end, if it does not come to the routine.** The walk goes on to the frame's end on the paths that do not come to the cut: these are the paused frames (the NMI skips the mode's routine). There it asks again that the byte is still followed. One more walk follows the low bit of the pause byte: it starts with that bit known (the walk is run from both values), and at the end of a frame that did not come to the cut it asks that the bit is known to be 1. The pause routine toggles the bit with `EOR` or keeps it, and the NMI branches on it, so the bit is known on every path. In that walk the search does not join states with other values of the pause byte.

```
cut_or_end    : ctrlCheck1 ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)))
                →  (∃ k ≤ fuelPerFrame, pc(trM(k)) = PlayerCtrlRoutine, in the frame of M, the first time)
                   ∨ the frame's end is covered by a state with the byte followed (and the pause bit 1)
arrive_at     : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pause(frame(M, x)) & 1 = 0  →  Arrive(M, x, arrAt(M, x))
keep_of_noCut : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ (no instruction of the frame of M is at PlayerCtrlRoutine)
                →  ∀ y ∈ keepA, y(frame(M, x)) = y(M)
OnFrames.arrive  : ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)), 1 ≤ j ≤ T, j < g  →  Arrive(fm j, pad j, arr j)        from Frames.up and keep.ends
OnFrames.lagKeep : the same  →  ∀ y ∈ keepA, y(fm j) = y(seq (j − 1))                                                       from OnFrames.lagNo (a theorem), by induction over the frames ix (j − 1) … ix j − 2
```

* **The condition on each instruction.** It is `CleanK`, the field `keep.clean`, with the move routine's store not before the cut (the walk checks the `pc`). A store with a target not known makes the walk forget the followed byte, and the walk then fails at the cut. So the walk shows that before the cut every store knows its target.
* **The search.** It is no part of the proof: the check walks every state of its table. The search of `LagFrames` forgets the bytes outside `prot` and joins the passes of a loop. Then the loops of the timers (`DEC abs,X`), the random bits (`ROR abs,X`) and the top score (`STA abs,Y`) store through an index not known, and the followed byte is lost. The search of `CtrlKeep` forgets no byte of RAM and keeps both index registers in the key. One table serves every byte.
* **Numbers.** The search for the 25 bytes: 108,736 steps, 7,157 forks, 0 failures, a table of 7,852 states, 2 arrivals at the cut, 6 frame ends (paused frames), 0.2 s. The search for the pause bit: 221,415 steps, 14,528 forks, 0 failures, a table of 16,729 states, 6 arrivals, 12 frame ends, 0.5 s. The check of the 25 bytes and the pause bit (`ctrlCheck`): 2.8 s natively (2.3 s before the pause bit). It is a part of `numbersCheck` (`Numbers.ctrl`).

`surface_of_frames` and the theorems before it take `StartK(all n)` for each frame of `keep` before the touch's frame, counted or not. In `PoleJoin` it is `FrameKeep.Frames.all_start` from the machine at control (`FrameKeep.AtCtl`), the walk's check `keepCheckOf` and `fracCheck`.

## The whole frame: from the player's routine to its end

The walk of the pause bit stops at the player's routine (the cut). Now at the cut it hands over to a walk of `FrameKeep` (`FrameKeep.walkK`), which follows the frame from there to its end. That walk forgets the bytes outside its protected bytes, as the walk of [one whole frame in control](f-6-19-FrameKeep.md) does. Its guard (`guardP`) protects four more bytes (`spareI`): the pause byte, `AreaType`, `SwimmingFlag`, `PlayerChangeSizeFlag`. At the cut it keeps of the pause byte only the low bit: it is known to be 0 there, since the NMI has just tested it. It sets the other three to their values at the frame's start (`v`, 0, 0); they still have these values at the cut (`ctrl_keep`). At the frame's end it asks the four values again (`afterCheck`).

```
Spare(m)        : a store of m through an index or a pointer, with a target t < 2000h, does not write a byte of spareI
AreaOK(v, m)    : AreaType(m) = v ∧ SwimmingFlag(m) = 0 ∧ PlayerChangeSizeFlag(m) = 0

area_end        : ctrlCheck ∧ afterCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)) ∧ Spare(trM(n))) ∧ AreaOK(v, M)
                  →  AreaOK(v, frame(M, x)) ∧ ((∃ k, pc(trM(k)) = PlayerCtrlRoutine in the frame of M) → pause(frame(M, x)) & 1 = 0)
noCut_of_paused : the same ∧ pause(frame(M, x)) & 1 = 1  →  no instruction of the frame of M is at PlayerCtrlRoutine
area_endF, noCut_of_pausedF : the same, with ∀ n, CleanK_F(trM(n)) for CleanK(trM(n)) ∧ Spare(trM(n))       CleanK_F: CleanK of FrameKeep.guardF
OnFrames.areaAll : ctrlCheck ∧ afterCheck(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaOK(v, seq 0)  →  ∀ n < ix g, AreaOK(v, all n)
OnFrames.lagNo   : ctrlCheck ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n))  →  the field lagNo of before
```

A frame that does not come to the routine is the one of the walk before: it ends paused, and it keeps `keepA`, which has the three bytes. So every frame in control keeps them, and a frame ends not paused exactly when it comes to the player's routine.

* **Why the bytes are protected.** After the player's routine the game engine stores through indices that the walk does not know (the objects). Such a store makes the walk forget every byte outside the protected ones. `CleanK` protects only the bytes of `FrameKeep.guardK`. So `keep.clean` asks `CleanK` of `FrameKeep.guardF`, which protects the four bytes too. `area_endF` is `area_end` with it: the walk after the cut asks no `Spare` at the player's own store of the fraction, so the old `Spare` on that store is not needed. On real frames no store through an index or a pointer writes these bytes (below, Measured).
* **The induction.** `seq 0` has the three bytes of `B.m` (`Start`, from the rows of the change), and `numbersCheck` asks `AreaType(B.m) ∈ {1, 2, 3}`, `SwimmingFlag(B.m) = 0`, `PlayerChangeSizeFlag(B.m) = 0`. Each frame of `keep` before the touch's frame keeps them (`area_endF`), so every `all n` has them, and so has `seq (j − 1)`.
* **The change of size.** `PlayerChangeSizeFlag` is set only in the routine of the change of size, which is not the routine of control. A power-up changes the routine byte; the flag is set on a later frame, which is not in control.
* **Numbers.** The walk of the pause bit comes to the cut in 3 states. The search after the cut: 1,633,803 steps, 154,366 forks, 0 failures, a table of 75,196 states. `afterCheck` (the walk of the pause bit up to the cut again, and the walk after it): 5.9 s in a program; it is a part of `numbersCheck` (`Numbers.after`). With only the pause bit watched the table has 46,644 states; with the pause bit, the area's type and the swimming flag 44,924. If the cut kept the whole pause byte, the 3 states at the cut would give 3 keys and a table of 139,987 states.
* **The jumpspring.** With `JumpspringAnimCtrl` protected and watched too, the search did not finish: 9 minutes, 6.8 GB, stopped. The jumpspring's object code writes it when he lands on it, so the walk could not keep it anyway.
* **`unpaused` and `lagPaused` are gone.** Which frames are counted is `ix` of `keep`. With the walk, a frame ends not paused exactly when it comes to the player's routine. So `ix` is now defined as the frames that end not paused, and the two fields hold by the definition.

## A and B of the frame before

The player's routine writes A and B (`A_B_Buttons`) from the pad's bits, and at its end the game engine copies them into A and B of the frame before (`PreviousA_B_Buttons`, the routine `SaveAB`). `PrevKeep` shows that a frame in control keeps bit 7 of the two equal.

```
PrevOK(m)        : PrevA(m) & 80 = A_B(m) & 80
SpareAB(m)       : a store of m through an index or a pointer, with a target t < 2000h, writes neither A_B nor PrevA
CtlStore(m)      : the instruction of m writes the routine, the mode or the task by its address
prev_end         : ctrlCheck ∧ prevCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareAB(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ PrevOK(M)
                   →  PrevOK(frame(M, x))
OnFrames.prevAll : ctrlCheck ∧ prevCheck(v) ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ PrevOK(seq 0)  →  ∀ n < ix g, PrevOK(all n)
```

`CleanK_F` is `CleanK` of `FrameKeep.guardF` (the field `keep.cleanF`). No frame before the touch's frame has an instruction with `CtlStore` (the field `keep.noStore`).

* **The walk.** The walk of the pause bit comes to the player's routine (the cut). There, for each value `b` of bit 7 of the pad's bits, a walk of `FrameKeep.walkKC` follows the frame to its end. It protects A_B and PrevA too, and it stops a path at a store to the routine, the mode or the task by its address. At the frame's end it asks bit 7 of A_B and of PrevA to be `b`. A frame that does not come to the routine keeps both bytes (`CtrlKeep.keep_of_noCut`).
* **Why the cut.** Round 8's search without the cut failed at 26 frame ends: there PrevA was not known. The paths that fail are those that write the task by its address: the axe (`HandleAxeMetatile`) and the change of area (`ChgAreaMode`). With the task below the game core's, the game core returns before the game engine, so `SaveAB` does not run. With the paths cut at the stores to the routine, the mode and the task (8 places: these two and six stores of the routine), the search has 0 failures and a table of 7,079 states (74,910 before).
* **The induction.** `seq 0` has the A_B and PrevA of `B.m` (`Start`, from the rows of the change: the rows know PrevA too), and `numbersCheck` asks `PrevOK(B.m)`. Each frame of `keep` before the touch's frame keeps `PrevOK`.
* **Numbers.** `prevCheck`: the walk of the pause bit to the cut and two walks after it, 3.1 s natively. It is a part of `numbersCheck` (`Numbers.prev`).

## After the scroll handler: three bytes

`AfterKeep` follows the frame from the player's routine with two walks. The first goes from the cut to the first time the frame comes to the scroll handler (`PlayerSubs`). The second goes from there to the frame's end, with one byte followed as the counter of `TaintRun` (`Env.rkI`): it fails on any write to that byte, and asks at the frame's end that the byte is still followed. It also fails if the frame comes to the scroll handler again. Both stop a path at a store to the routine, the mode or the task by its address.

```
hI          = Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute
SpareH(m)   : a store of m through an index or a pointer, with a target t < 2000h, writes no byte of hI
keepH       : ctrlCheck ∧ hCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareH(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
              →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ hI, y(frame(M, x)) = y(trM(k))
SpareE(m)   : SpareAB(m) ∧ SpareH(m)          the field spareE of OnFrames
```

* **Numbers.** The first walk: 1,769 steps, a table of 134 states, 8 states at the scroll handler. The second walk: 61,977 steps and a table of 3,986 states for each byte, 0 failures. `hCheck`: 1.9 s natively. It is a part of `numbersCheck` (`Numbers.keepH`).
* **A step with the followed byte.** `FrameKeep.s_kstep` asks the counter to be at least 2. The second walk asks instead that no instruction decrements the followed byte (`isRkDec`), as `LagFrames` does: `s_kstepL`.

**Which stores the walk meets.** The program `after-bytes` runs the second search for each horizontal byte, from the 8 states at the scroll handler.

* Under `keep.cleanF` alone, with the byte not protected, the walk loses each of these bytes at about 95 stores through an index or a pointer whose target it does not know: the enemies, the sprites, the area's parser. `SprObject_X_MoveForce`, which `guardK` protects, is not lost there.
* With the byte protected too, the three bytes of `hI` close. The others meet stores by address:

| byte | stores after the scroll handler that the walk meets |
|---|---|
| speed | `KillPlayer`, `KeepOnscr` (the screen's edge), `ImpedePlayerMove`, `PutPlayerOnVine` |
| subspeed | `PutPlayerOnVine` |
| facing | `FlagpoleCollision`, `PutPlayerOnVine` |
| x | the move routine with the index 0 (the walk splits an index it does not know), `PositionPlayerOnHPlat`, `ImpedePlayerMove`, `KeepOnscr`, `PutPlayerOnVine` |
| page | the stores of x, and `ExecGameLoopback` |
| fraction | the move routine with the index 0 |
| collision bits | `ImpedePlayerMove`, the start of `PlayerBGCollision` |

`KillPlayer` writes the speed before it writes the routine, so the cut at the routine's store comes after it. `PutPlayerOnVine` is reached also on paths that write no routine (a vine's tile below the status bar). So the subspeed and the facing stay in `After`: the walk would need to know that he touches no vine or pole, which is the map.

## The statements about the whole run are theorems

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
next_of_reads     : reads  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  frames 1..j are Follow ∧ seq 0..j are Clean ∧ bits(seq j) = FF
                                         ∧ frames 1..j are vNext ∧ seq 0..j are HaltOK
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ (∀ n < ix g, StartK(all n)) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
                    →  ∃ w h, Surface(w, h)
Run.next, Run.startP, Run.startV                                 PoleJoin
```

| Assumption before | Now | From |
|---|---|---|
| `model`: `P'(j) ≤ P_A + d(w)` for `j < h` | theorem | `one_of_frames`. `w` is the list of `inp j`, `h` the first frame that is not `Follow ∧ Clean` |
| `hit`, `stop` | theorem | `Hit` in `OneFrame` |
| `box`, `off`: no hit before `J` | theorem (`Surface.first : J ≤ h`) | `box`, `vert_of`, `moves`, the bound on the distance (`dist_abs`), the search of the height (`vCheck`) |
| `next` | theorem | `reads`. Both ends are read from the same machine |
| `startP`, `startV` | theorem | `Start`. Next section |
| `mem`, `long` | theorem | `inAt_mem`, how `w` is made |

**In the box.** `x` on frames 1 to 8 is not assumed. It is within 4 px by the bound on `|d(w)|` (`dl`; moving left the speed's byte can be 1 more, so this is a little more than `dbound`). The height is not assumed either. `vCheck` runs `vstepV` for 8 frames from `vs(B.m)`, with A or not and every stored speed from 0 to the top, and checks that every state is in the box.

## The state at control

`Start(B, m)` is about one machine.

```
Start(B, m) : hs(m) = hs(B.m) ∧ P(m) = P(B.m) ∧ abs(m) = abs(B.m) ∧ bits(m) = bits(B.m) ∧ vs(m) = vs(B.m)
              ∧ AreaType(m) = AreaType(B.m) ∧ SwimmingFlag(m) = SwimmingFlag(B.m) ∧ PlayerChangeSizeFlag(m) = PlayerChangeSizeFlag(B.m)
              ∧ A_B(m) = A_B(B.m) ∧ PrevA(m) = PrevA(B.m)
```

A state of the last row of the change that has control knows 1,763 or 1,776 of 2,048 bytes. `startCheck` checks, on every state of every row, that it says whether it has control, and if it has, that it knows the bytes of `Start` and they are those of `B.m`.

```
start_of_rows : startCheck ∧ InRows(m) ∧ ctl(m)  →  Start(B, m)
EndRun.start  : Statement ∧ EndStatement ∧ startCheck ∧ EndRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  Start(B, seq b)
Run.start     : the same conditions, on a run of Route  Start(B, pole.seq 0)
```

`left` is 0 only on the last row. It has 6 states, and 2 have control. The other 4 are the time-up states. The rows end where `left` is 0, so `left` must not be 0 before control (`EndRun.first`, proved from `chg.time₂` and `chg.ctlFirst₂`). `Route.Run.atCtl : pole.seq 0 = base.seq b₂` is a theorem: the frames of `keep` are those of `base` from frame `b₂` on. The conditions `entry₂`, `noStart₂`, `quiet₂` of `chg` are used as `Run.change₂` uses them.

The last row also gives the vertical bytes, the A button and the collision bits. The main bytes it does not know are `PlayerSize` and `EventMusicQueue`.

## The screen's left edge

When Mario is on the pixel of the screen's left edge, the scroll routine sets the speed to 0, unless Right alone is held. Left of that pixel, it puts his position back on it. The order is: the move, the scroll routine, the collision routine.

* The old `Frame.impedeP` is false on real frames. A frame that runs past the edge has `v₂ = −v_top`, `P' − P₂ = 512`. Of 53,398 frames that run to the edge, 13 do this.
* So the third case of `impedeP` is now `P' ≤ P + 256 ∧ v₂ ≤ 0` in place of `P' = P₂ + 256 ∧ v₂ ≤ 0`. `Frame.bound`, `Frame.adv_le`, `chain_reach` stay.
* In the statement on one frame this is the second kind of `Hit`. He can stop with `v₂ > 0` too (the largest measured is 4). Then `P(b) = P₂ ≤ P(a) + 256`. He does not leave the edge's pixel fast, so this is enough. That he is not fast is not proved: it is assumed in `After` (in `moves`).

## Measured

The program `surface-frames-check FM2 N`, `N = 200`, exit code 0, about 9 minutes of CPU. In every row, no frame fails `OneFrame`, `Moves`, `ends`, the `v₂` of `reads`, or `move`, `gain`, `impedeV`, `impedeF`, `impedeP` of `Frame`.

| Run | Frames | Not clean | `lag` | Routine does nothing | Left blocked | `Hit` | Put back at the edge | Frames 1 to 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| TAS from 852 | 240 | 5 | 0 | 233 | 0 | 1 | 0 | 8 |
| the late touch after 1089, A held long | 34 | 3 | 0 | 30 | 0 | 0 | 0 | 0 |
| random from control | 36,308 | 4,048 | 0 | 30,705 | 2 | 1,463 | 1 | 1,600 |
| random from the TAS's frames | 15,019 | 571 | 0 | 14,087 | 0 | 327 | 0 | 0 |
| with Select | 10,520 | 571 | 0 | 9,724 | 0 | 180 | 1 | 800 |
| with Start | 20,311 | 761 | 8,070 | 11,161 | 0 | 284 | 2 | 786 |
| running to the left edge | 53,398 | 3,804 | 0 | 47,629 | 0 | 1,835 | 13 | 0 |
| overwritten states around the stairs | 103,680 | 5,908 | 0 | 88,917 | 2,653 | 6,202 | 0 | 0 |

* On frames 1 to 8 (3,194 frames) also `vs(seq j) = vNext(seq (j − 1), seq j)`, the old `vBefore`, `vAfter`, `HaltOK` at both ends, `box`, and that `(y, vy, st)` on entering the collision routine is `vstepV`'s result. No difference.
* On every frame checked on `Moves` also `state` (with `PrevA & 80 = A_B & 80` at the end of the frame before), what `OnFrames.lagKeep` proves (the 25 bytes of `fm j` are those of `seq (j − 1)`), the arrival at the routine, and what `ctrl_keep` proves: the 25 bytes of `keepA` at the routine are those of `fm j`. No difference, also on the 8,070 `lag` frames with Start.
* The old fields `unpaused`, `lagPaused`, `spare`: no counted frame in control ends paused, no `lag` frame ends not paused, and no frame has a store through an index or a pointer to one of the four bytes of `spareI`. Also no `lag` frame comes to the player's routine (what `OnFrames.lagNo` proves), and no frame in control changes the area's type, the swimming flag or the change of size (what `OnFrames.areaAll` proves). All counts are 0 on every run, the 8,070 `lag` frames with Start included. The machine of the proof has the area's type 1, the swimming flag 0, the change of size 0.
* On every frame the input that the player's routine reads is `readIn(a, b)` of the two ends (the old field `input`): no difference.
* On 2,375 of the 3,194 frames 1 to 8 a byte of the vertical state takes another value between the scroll handler and the frame's end, and is back at the end. On the ground the collision routine sets `Player_State` to 2 and lands him again. So `vAfter` cannot come from a walk that forbids writes to these bytes.
* The pressed side is masked on 329 frames (3 from control, 326 around the stairs). All are `OneFrame` and all meet `Moves`. At the mover 182 have the model's speed and 147 the speed 0 where the model's is not 0 (`move_masked`'s second case; the kinds column counts them as `Hit`). These 147 are not `Pre ∧ Coll` and need `MaskStop`; this page said before that none needs it, which was false. `bits(R) = bits(a)` fails on no frame.
* On the 8,070 `lag` frames, no byte read here changes. So with `lag` frames after `seq j` the values read are the same. No frame overruns on these runs.
* The change: 201 runs from the TAS's entry state and `E` with random inputs with no Start. All get control after 282 frames or more, `left` is never 0 before control, and the state at control always meets `Start`.
* How it counts: a frame that ends in a machine without control (death, the touch) is outside the fields and is not counted. `Follow` and `Hit` do not hold there. Such a run is not a `Run`.
* `after-real FM2 100` (the movie from 852 and 300 own runs from control, random, with Select, with Start: 35,802 frames in control; a run stops at a frame with a store to the routine, the mode or the task): `SpareE` holds at every instruction; `PrevOK` holds at the start and the end of every frame; the three bytes of `hI` at the frame's end are those at the scroll handler, and no frame comes to the scroll handler twice after the player's routine. On the 31,949 frames from a clean state, `storedQ` and `After` hold. On 338 frames from a state that is not clean, `storedQ` fails; `moves` is not asked there.

## The first frame in the abstract machine

One frame walked from the states of the last row that have control (not in Lean).

| Known | Steps | Failures |
|---|---:|---:|
| pad not known | 27,292 | 5 (`FindEventMusicHeader+2`) |
| `EventMusicQueue = 0`, pad not known | 2,288 | 4 (`JumpEngine+18`) |
| `EventMusicQueue = 0`, each of the 128 pads with no Start | 739,183 | 1 on each of the 64 with no A (`BlockBufferCollision+43`) |
| and `PlayerSize` split | about 840,000 per case | 0, about 3 s for the 4 cases |

So frame 1 alone closes. It is one frame of 233, and the states grow on the next frames, so it is not in the proof.

## Assumptions (not proved in Lean)

* `moves`: the frame outside the movement. Up to the player's routine it is proved (`ctrl_keep`) from the frame's start in control and `CleanK`, and so are the arrival at the routine and that the frames not counted keep the 25 bytes; that the frame does not end during the movement (from `CleanK`) and that the position is far from the ends (from the frames before) are proved too, and so are bit 7 of A of the frame before (`OnFrames.prevAll`) and three bytes after the scroll handler (`AfterKeep.keepH`). What stays: the values at the end of the frame before (`state`: the player's state and the jumpspring) and `After` (`f`, `fd`, `storedQ`, `coll`). The movement is proved ([`FrameModel`](../0-0/0-3-2-FrameModel.md)), also with the pressed side masked.
* `unpaused`, `lagPaused`, `spare` are no longer assumed here: the counted frames are the frames that end not paused, and the four bytes are in the guard of `keep.clean` ([One whole frame in control](f-6-19-FrameKeep.md)).
* `state`: what stays is `Player_State` ∈ {0, 1, 2} and no jumpspring. They are written by the code of the map and the objects (the jumpspring when he lands on it, `Player_State` by the collision routine). A walk of a frame in control knows neither the map nor the objects, so it cannot keep them. `AreaType`, `SwimmingFlag`, `PlayerChangeSizeFlag` are proved (`OnFrames.areaAll`), and so is `PrevA` (`OnFrames.prevAll`).
* `After`: the subspeed and the facing (written on the vine's and the flagpole's paths, see [the table](#after-the-scroll-handler-three-bytes)), `storedQ` (the stored speed at the scroll handler is that of the speed there: the movement's walks do not follow the stored speed past `X_Physics`), and `coll` (the collision routine and the screen's edge).
* `spareE` (new, on each instruction): no store through an index or a pointer writes A_B, PrevA, the moving direction, the running speed or the stored speed. Measured: no failure (above). If `FrameKeep.spareK` had these five bytes, it would be a part of `keep.cleanF`.
* `vAfter`: on frames 1 to 8, the frame after the scroll handler keeps the vertical bytes. That the routine follows `vstep` is proved (`vert_of`), and the part before it (`Moves.vBefore`). A walk cannot give `vAfter` as it gives the part before: on 2,375 of the 3,194 frames 1 to 8 measured, a vertical byte takes another value after the scroll handler and is back at the frame's end (the collision routine sets `Player_State` to 2 and lands him again). After the collision routine the enemies' code can write the vertical speed (a stomp), and the walk knows no enemy.
* `keep.ends`, `keep.clean` and the theorem `keep.start` of [One whole frame in control](f-6-19-FrameKeep.md): the frames are the same, so `ends` is not a field here any more.
* `box`: on frames 1 to 8 the collision routine gives the same result as on the machine at control.
* `reads`: `fr` is read from the machines. That it is a `Frame` stays an assumption of [Top speed](../0-0/0-1-TopSpeed.md).
* `chg.time₂`, `chg.ctlFirst₂`, and the theorem `Run.atCtl`.

**Files.** `Theorems/SurfaceFrames.lean`, `Theorems/CtrlKeep.lean`, `Theorems/PrevKeep.lean` (`prev_end`), `Theorems/AfterKeep.lean` (`keepH`), `Theorems/VertModel.lean`, `Theorems/FrameModel.lean` (`move_masked`, `trace_inFrame`), `Theorems/FrameWalk.lean` (`InFrame`),
`Theorems/SurfaceRun.lean` (`far`), private `Proof/SurfaceFrames.lean` (`side_start`), `Proof/PoleJoin.lean` (`pole_numbers`, which now includes `ctrlCheck`, `afterCheck`, `prevCheck` and `hCheck`).

**Reproduce.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # the table above, about 9 minutes of CPU
.lake/build/bin/smbrta vert-model-check                # vertOK and each of its cases, about 0.1 s
.lake/build/bin/smbrta mask-model-check                # maskOK and its parts, about 0.1 s
.lake/build/bin/smbrta ctrl-keep-check                 # the walk up to the player's routine: each of the 25 bytes and the pause bit, about 4 s
.lake/build/bin/smbrta ctrl-after-check size           # the walk after the cut (afterCheck), about 20 s; `pause` and `area` watch fewer bytes
.lake/build/bin/smbrta ctrl-prev-check                 # round 8's search after the cut for PrevA, without the cut at the stores (not in the proof), about 10 s; exit 1 (26 failing frame ends)
.lake/build/bin/smbrta prev-why none|cut                # the same search, printing the paths to the failing frame ends; with `cut` the stores of noStore cut: 0 failures
.lake/build/bin/smbrta prev-check                       # prevCheck, about 3 s
.lake/build/bin/smbrta after-keep-check                 # the searches of AfterKeep and hCheck, about 4 s
.lake/build/bin/smbrta after-bytes guard|prot           # the second search for each horizontal byte: guard = keep.cleanF only, prot = the byte protected too
.lake/build/bin/smbrta after-real FM2 100               # SpareE, PrevOK, keepH, storedQ, After on real frames, about 80 s
```
