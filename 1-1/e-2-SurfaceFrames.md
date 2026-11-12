[← Back](README.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# Above ground: the frames from control, one by one

**Claim.** [From control to the castle](f-5-PoleJoin.md) assumed the statements about a whole run `model`, `hit`, `stop`, `box`, `off`, `next`, `startP`, `startV`. They are theorems now. The assumptions that stay are about one frame. On frames 1 to 8 the vertical step (`vstep`) is a theorem on real machines too; what stays there is that the frame after the scroll handler keeps the vertical bytes. The part of each frame from its start to the player's routine is a theorem now: a walk of that part ([`CtrlKeep`](#the-frame-up-to-the-players-routine)) shows that it keeps 25 bytes and comes to the routine in the state the movement needs. So the fields `vBefore`, `Moves.at_ctrl`, `Moves.before`, `Moves.bits` are gone. The frame's two ends are theorems too, from conditions on one machine or one frame: a counted frame ends with the game not paused, so it comes to the player's routine (`Moves.arrive` is gone, new: `unpaused`); a frame not counted does not come to the player's routine, so it keeps the 25 bytes (`Moves.lag` is gone, new: `lagNo`). The frames are those of the field `keep` of `Run` ([One whole frame in control](f-6-19-FrameKeep.md)), so the field `ends` is gone too. A frame where the side he presses is masked is a theorem too: the field `masked` is gone. `startP`, `startV` are proved on real machines. They come from the last row of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). The conditions are those of that change, and that `left` is not 0 before control.

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

After(a, Q, b)     : f, fd, md of b are those of Q ∧ (RunningSpeed(b) = 0 ⟺ RunningSpeed(Q) = 0) ∧ abs(b) = |v(Q)|
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)) )

MovesAt(a, M, x, n₀) : AtCtrl0(R)                                  the state at the player's routine, as FrameModel needs it, but the mask
                       ∧ the 8 horizontal bytes of R are those of a    nothing writes them from a to R
                       ∧ bits(R) = bits(a)                             nor the collision bits
                       ∧ longer ∧ far ∧ after                          as in Moves below

CtlState(a)        : AreaType(a) ∈ {1, 2, 3} ∧ Player_State(a) ∈ {0, 1, 2} ∧ JumpspringAnimCtrl(a) = 0 ∧ SwimmingFlag(a) = 0
                     ∧ PlayerChangeSizeFlag(a) = 0 ∧ PrevA(a) & 80 = A_B(a) & 80

Arrive(M, x, n₀)   : pc(trM(n₀)) = PlayerCtrlRoutine, in the frame of M, and no instruction before n₀ is there

Moves(a, M, x, n₀) : state    CtlState(a)
                     longer   the frame does not end within 728 instructions after R
                     far      2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴
                     after    After(a, Q, b) at every Q at the scroll handler

Moves.toAt    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Clean(a) ∧ Arrive(M, x, n₀) ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ Moves  →  MovesAt
at_subs       : modelOK ∧ MovesAt ∧ ¬Masked  →  ∃ Q at the scroll handler, hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_moves  : modelOK ∧ MovesAt ∧ ¬Masked  →  Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)
at_subsM      : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  ∃ Q at the scroll handler, (hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∨ v(Q) = 0)
                                                                  ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_movesM : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  OneFrame(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ Clean(seq (j − 1))  →  OneFrame(inp j, seq (j − 1), seq j)
```

`keepA` and `StartK`, `CleanK`, `ctrlCheck` are in the next section. `all n` are the frames of `keep`, counted or not, and `ix g` is the touch's frame. `StartK(all n)` is the theorem `FrameKeep.Frames.all_start`, from the machine at control; `CleanK` on each instruction is the field `keep.clean`. The two other conditions of `Moves.toAt` are theorems (`OnFrames.arrive`, `OnFrames.lagKeep`, next section).

`modelOK` is the check on the ROM of `FrameModel`. It is a part of `numbersCheck` now, so the private proof computes it by `native_decide` (about 3 s more). `move_model` needs that the side he presses is not masked; with `bits(R) = bits(a)` this is `¬Masked`.

**The masked frames.** On a frame where the side he presses is masked (`Masked`), the routine of the friction reads the mask and `hstep` does not. [`FrameModel.move_masked`](../0-0/0-3-2-FrameModel.md) proves that the frame still follows `hstep`, or it leaves the speed 0. A clean state with the side masked has the bits of a block of Left and moves right (`masked_clean`). With the speed 0 at the scroll handler, `After` gives `MaskStop`. `maskOK` is the check on the ROM of `move_masked` (about 0.1 s); it is a part of `numbersCheck`.

The fields that are assumed (`OnFrames`). All are in the field `frames` of `Run`. `fm`, `pad` are those of `keep`.

```
reads    : 1 ≤ j ≤ g   →  v, f, P at the start of fr j are those of seq (j − 1)
           1 ≤ j < g   →  v', f', P' at the end of fr j are those of seq j
unpaused : 1 ≤ j ≤ T, j < g  →  pause(seq j) & 1 = 0                  the counted frame ends with the game not paused
lagNo    : 1 ≤ j ≤ T, j < g, ix (j − 1) ≤ n, n + 1 < ix j  →  no instruction of the frame of all n is at PlayerCtrlRoutine
                                                                       a frame not counted does not come to the player's routine
moves    : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)
vAfter   : 1 ≤ j < J, j < g, Q at the scroll handler  →  at seq j the vertical bytes and A are those of Q
box      : 1 ≤ j < J, j < g, Q at the scroll handler  →  from Q to seq j the collision routine does what it does
           on B.m at (pix P(Q), y, w, vy, st)          (y, vy, st) is vstep's result, w stands for the speed's sign
```

`pause` is the pause byte (`GamePauseStatus`), read from the ROM: the operand of the load just before the NMI's call of the mode's routine (`CtrlKeep.pauseA`). Its low bit is 1 while the game is paused. The pause routine sets and clears it.

The frame's end is the field `keep.ends` of `Run`: `1 ≤ j ≤ g → seq j = frame(fm j, pad j)` (`OnFrames.ends`, a theorem). The vertical bytes are `y, mf, vy, dummy, vf, vfd, origin, st, DTHJ`. `DTHJ` is `DiffToHaltJump`, `A` is bit 7 of `A_B_Buttons`, `PrevA` is `PreviousA_B_Buttons`.

**The vertical step is a theorem.** [`VertModel.vert_model`](../0-0/0-3-2-FrameModel.md) proves that from the player's routine to the scroll handler the vertical bytes follow `vstepV`: `vstep` on the machine with the stack pointer of the player's routine and `DTHJ = 1`.

```
HaltOK(m)  : st(m) = 1 → DTHJ(m) = 1
vNext(a, b) = vstepV(vs(a), A(b), abs(a))
Moves.vBefore : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Arrive ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ Moves  →  at R the vertical bytes and A are those of a,
                and PrevA(R) & 80 = A_B(R) & 80                       (the old field vBefore)
vert_of    : vertOK ∧ ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ HaltOK(seq (j − 1))  →  vs(seq j) = vNext(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

`HaltOK(seq 0)` holds because the state at control is not a jump (in `numbersCheck`). So `quiet_upto` proves `vs(seq j) = vNext(...)` and `HaltOK(seq j)` for every `j < J` by induction, with the other facts. `vertOK` is a part of `numbersCheck` (about 0.1 s more).

| Field before | Now |
|---|---|
| `step`: every clean frame is a `OneFrame` | `moves` (the frame outside the movement), `ends` |
| `masked`: a frame with the pressed side masked is a `OneFrame` | theorem `one_of_movesM` (from `moves` and `FrameModel.move_masked`). New: `Moves.bits`; `Moves.at_ctrl` is `AtCtrl0`, with no condition on the mask |
| `reads`: `v₂(fr j) = v₂` | gone. `box` is on the real machines `Q` and `seq j`, so the frame's `v₂` is not needed |
| `box` on `fr j` | `box` on the real machines, from the scroll handler |
| `Moves.input`: the routine reads `readIn(a, b)` | gone. The model's input is the one the routine reads |
| `vert`: frames 1 to 8 follow `vstep` | theorem `vert_of`. New: `vBefore`, `vAfter` (the frame outside the movement routine keeps the vertical bytes) |
| `vBefore`: up to the player's routine the vertical bytes and A are those of the frame before, and PrevA is A | theorem `Moves.vBefore`, by the walk of `CtrlKeep`. It uses `OnFrames.lagKeep` and `CtlState.prevA` |
| `Moves.at_ctrl`: `AtCtrl0` at the player's routine | theorem `Moves.toAt`, by the walk. New: `Moves.state` (`CtlState` at the end of the frame before) |
| `Moves.before`, `Moves.bits`: nothing writes the horizontal bytes and the collision bits up to the routine | theorem `Moves.toAt`, by the walk |
| `Moves.arrive`: the frame comes to the routine at `arr j`, the first time, before its end | theorem `OnFrames.arrive`, by the walk with the pause bit. New: `unpaused` (the counted frame ends with the pause byte's low bit 0) |
| `Moves.lag`: the frames not counted between `seq (j − 1)` and `fm j` keep the 25 bytes of `keepA` | theorem `OnFrames.lagKeep`, by the walk, frame by frame. New: `lagNo` (a frame not counted does not come to the player's routine) |
| `arr`: data, the instruction of the arrival | the definition `CtrlKeep.arrAt`: the first instruction at the routine |
| `ends`, and the data `fm`, `pad` | `keep.ends`, `keep.fm`, `keep.pad` of `Run`: one set of frames for both |

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
OnFrames.arrive  : ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)), 1 ≤ j ≤ T, j < g  →  Arrive(fm j, pad j, arr j)        from unpaused and keep.ends
OnFrames.lagKeep : the same  →  ∀ y ∈ keepA, y(fm j) = y(seq (j − 1))                                                       from lagNo, by induction over the frames ix (j − 1) … ix j − 2
```

* **The condition on each instruction.** It is `CleanK`, the field `keep.clean`, with the move routine's store not before the cut (the walk checks the `pc`). A store with a target not known makes the walk forget the followed byte, and the walk then fails at the cut. So the walk shows that before the cut every store knows its target.
* **The search.** It is no part of the proof: the check walks every state of its table. The search of `LagFrames` forgets the bytes outside `prot` and joins the passes of a loop. Then the loops of the timers (`DEC abs,X`), the random bits (`ROR abs,X`) and the top score (`STA abs,Y`) store through an index not known, and the followed byte is lost. The search of `CtrlKeep` forgets no byte of RAM and keeps both index registers in the key. One table serves every byte.
* **Numbers.** The search for the 25 bytes: 108,736 steps, 7,157 forks, 0 failures, a table of 7,852 states, 2 arrivals at the cut, 6 frame ends (paused frames), 0.2 s. The search for the pause bit: 221,415 steps, 14,528 forks, 0 failures, a table of 16,729 states, 6 arrivals, 12 frame ends, 0.5 s. The check of the 25 bytes and the pause bit (`ctrlCheck`): 2.8 s natively (2.3 s before the pause bit). It is a part of `numbersCheck` (`Numbers.ctrl`).

`surface_of_frames` and the theorems before it take `StartK(all n)` for each frame of `keep` before the touch's frame, counted or not. In `PoleJoin` it is `FrameKeep.Frames.all_start` from the machine at control (`FrameKeep.AtCtl`), the walk's check `keepCheckOf` and `fracCheck`.

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

The program `surface-frames-check FM2 N`, `N = 200`, exit code 0, about 7 minutes of CPU. In every row, no frame fails `OneFrame`, `Moves`, `ends`, the `v₂` of `reads`, or `move`, `gain`, `impedeV`, `impedeF`, `impedeP` of `Frame`.

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
* The new fields: no `lag` frame comes to the player's routine (`lagNo`), and no counted frame in control ends paused (`unpaused`). Both counts are 0 on every run, the 8,070 `lag` frames with Start included.
* On every frame the input that the player's routine reads is `readIn(a, b)` of the two ends (the old field `input`): no difference.
* On 2,375 of the 3,194 frames 1 to 8 a byte of the vertical state takes another value between the scroll handler and the frame's end, and is back at the end. On the ground the collision routine sets `Player_State` to 2 and lands him again. So `vAfter` cannot come from a walk that forbids writes to these bytes.
* The pressed side is masked on 329 frames (3 from control, 326 around the stairs). All are `OneFrame` and all meet `Moves`. At the mover 182 have the model's speed and 147 the speed 0 where the model's is not 0 (`move_masked`'s second case; the kinds column counts them as `Hit`). These 147 are not `Pre ∧ Coll` and need `MaskStop`; this page said before that none needs it, which was false. `bits(R) = bits(a)` fails on no frame.
* On the 8,070 `lag` frames, no byte read here changes. So with `lag` frames after `seq j` the values read are the same. No frame overruns on these runs.
* The change: 201 runs from the TAS's entry state and `E` with random inputs with no Start. All get control after 282 frames or more, `left` is never 0 before control, and the state at control always meets `Start`.
* How it counts: a frame that ends in a machine without control (death, the touch) is outside the fields and is not counted. `Follow` and `Hit` do not hold there. Such a run is not a `Run`.

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

* `moves`: the frame outside the movement. Up to the player's routine it is proved (`ctrl_keep`) from the frame's start in control and `CleanK`, and so are the arrival at the routine and that the frames not counted keep the 25 bytes; what stays: the values at the end of the frame before (`state`), the frame does not end during the movement (`longer`), the position is far from the ends (`far`), and `After`. The movement is proved ([`FrameModel`](../0-0/0-3-2-FrameModel.md)), also with the pressed side masked.
* `unpaused`: a counted frame ends with the pause byte's low bit 0. `lagNo`: a frame not counted does not come to the player's routine. That a frame that comes to the routine ends not paused is not proved: after the routine a store with a target not known could write the pause byte, as far as `CleanK` says, since the pause byte is not among the bytes that `CleanK` protects. So `lagNo` cannot yet be the one-machine condition "a frame not counted ends paused".
* `state`: these bytes are written by the code of the map and the objects (the jumpspring when he lands on its tile, the change of size when he takes a power-up, `Player_State` by the collision routine, `PreviousA_B_Buttons` at the end of the game engine). A walk of a frame in control knows neither the map nor the objects, so it cannot keep them; `AreaType` and `SwimmingFlag` are written only when an area starts, but they too are not among the bytes `CleanK` protects.
* `vAfter`: on frames 1 to 8, the frame after the scroll handler keeps the vertical bytes. That the routine follows `vstep` is proved (`vert_of`), and the part before it (`Moves.vBefore`). A walk cannot give `vAfter` as it gives the part before: on 2,375 of the 3,194 frames 1 to 8 measured, a vertical byte takes another value after the scroll handler and is back at the frame's end (the collision routine sets `Player_State` to 2 and lands him again). After the collision routine the enemies' code can write the vertical speed (a stomp), and the walk knows no enemy.
* `keep.ends`, `keep.clean` and the theorem `keep.start` of [One whole frame in control](f-6-19-FrameKeep.md): the frames are the same, so `ends` is not a field here any more.
* `box`: on frames 1 to 8 the collision routine gives the same result as on the machine at control.
* `reads`: `fr` is read from the machines. That it is a `Frame` stays an assumption of [Top speed](../0-0/0-1-TopSpeed.md).
* `chg.time₂`, `chg.ctlFirst₂`, and the theorem `Run.atCtl`.

**Files.** `Theorems/SurfaceFrames.lean`, `Theorems/CtrlKeep.lean`, `Theorems/VertModel.lean`, `Theorems/FrameModel.lean` (`move_masked`), private `Proof/SurfaceFrames.lean` (`side_start`), `Proof/PoleJoin.lean` (`pole_numbers`, which now includes `ctrlCheck`).

**Reproduce.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # the table above, about 7 minutes of CPU
.lake/build/bin/smbrta vert-model-check                # vertOK and each of its cases, about 0.1 s
.lake/build/bin/smbrta mask-model-check                # maskOK and its parts, about 0.1 s
.lake/build/bin/smbrta ctrl-keep-check                 # the walk up to the player's routine: each of the 25 bytes and the pause bit, about 4 s
```
