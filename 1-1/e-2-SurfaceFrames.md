[← Back](README.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# Above ground: the frames from control, one by one

**Claim.** [From control to the castle](f-5-PoleJoin.md) assumed the statements about a whole run `model`, `hit`, `stop`, `box`, `off`, `next`, `startP`, `startV`. They are theorems now. The assumptions that stay are about one frame. On frames 1 to 8 the vertical step (`vstep`) is a theorem on real machines too; what stays there is that the rest of the frame keeps the vertical bytes. `startP`, `startV` are proved on real machines. They come from the last row of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). The conditions are those of that change, and that `left` is not 0 before control.

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

`Follow(i, a, b)` has the form of `RoomJoin.Follow` of [the bonus room](c-5-RoomJoin.md): `fr.hs n = hs(seq n)`, `fr.P n = P(seq n)`. The input of the counted frame `j` is `inp(j) = inAt(fm j, pad j, arr j)`. It used to be `readIn(a, b)`, read from the two ends of the frame, and a field `input` said that the two are the same. Now the input is the one the routine reads, so that field is gone.

## One frame on the real machine

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel.md) proves the movement of a real frame: from the player's routine to the scroll handler, `hs` follows `hstep` and `P` moves by `16·v₂`. So `OneFrame` is a theorem from what the frame does outside the movement.

`fm j` is the machine when the counted frame `j` begins: `seq (j − 1)`, or later by `lag` frames. `pad j` is its input, and `arr j` the instruction at which it comes to the player's routine. `R` is the machine there, and `Q` the machine when the frame comes to the scroll handler. `b = frame(M, i)` is the machine at the frame's end.

```
Masked(i, a)       : bits(a) & lr ≠ lr            lr = the Left/Right that hstep reads from i

After(a, Q, b)     : f, fd, md of b are those of Q ∧ (RunningSpeed(b) = 0 ⟺ RunningSpeed(Q) = 0) ∧ abs(b) = |v(Q)|
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)) )

Moves(a, M, x, n₀) : AtCtrl(R)                                   the state at the player's routine, as FrameModel needs it
                     ∧ the 8 horizontal bytes of R are those of a    nothing writes them from a to R
                     ∧ the frame does not end within 728 instructions after R
                     ∧ 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴
                     ∧ After(a, Q, b) at every Q at the scroll handler

at_subs       : modelOK ∧ Moves  →  ∃ Q at the scroll handler, hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_moves  : modelOK ∧ Moves  →  Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ Clean(seq (j − 1))  →  OneFrame(inp j, seq (j − 1), seq j)
```

`modelOK` is the check on the ROM of `FrameModel`. It is a part of `numbersCheck` now, so the private proof computes it by `native_decide` (about 3 s more). `move_model` needs that the side he presses is not masked. A frame where it is masked (`Masked`) stays a `OneFrame` by assumption: there the routine of the friction reads the mask, and `hstep` does not.

The fields that are assumed (`OnFrames`). All are in the field `frames` of `Run`. `fm`, `pad`, `arr` are data in it.

```
reads  : 1 ≤ j ≤ g   →  v, f, P at the start of fr j are those of seq (j − 1)
         1 ≤ j < g   →  v', f', P' at the end of fr j are those of seq j
ends   : 1 ≤ j ≤ T, j < g  →  seq j = frame(fm j, pad j)
moves   : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1)), ¬Masked(inp j, seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)
masked  : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1)), Masked(inp j, seq (j − 1))   →  OneFrame(inp j, seq (j − 1), seq j)
vBefore : 1 ≤ j < J, j < g  →  at R: y, mf, vy, dummy, vf, vfd, origin, st, DTHJ and A are those of seq (j − 1),
                               and PrevA & 80 = A_B & 80
vAfter  : 1 ≤ j < J, j < g, Q at the scroll handler  →  at seq j these bytes and A are those of Q
box     : 1 ≤ j < J, j < g, Q at the scroll handler  →  from Q to seq j the collision routine does what it does
          on B.m at (pix P(Q), y, w, vy, st)          (y, vy, st) is vstep's result, w stands for the speed's sign
```

`R` is the machine at the player's routine, `inAt(fm j, pad j, arr j)`'s machine. `DTHJ` is `DiffToHaltJump`, `A` is bit 7 of `A_B_Buttons`, `PrevA` is `PreviousA_B_Buttons`.

**The vertical step is a theorem.** [`VertModel.vert_model`](../0-0/0-3-2-FrameModel.md) proves that from the player's routine to the scroll handler the vertical bytes follow `vstepV`: `vstep` on the machine with the stack pointer of the player's routine and `DTHJ = 1`.

```
HaltOK(m)  : st(m) = 1 → DTHJ(m) = 1
vNext(a, b) = vstepV(vs(a), A(b), abs(a))
vert_of    : vertOK ∧ moves ∧ vBefore ∧ vAfter ∧ HaltOK(seq (j − 1))  →  vs(seq j) = vNext(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

`HaltOK(seq 0)` holds because the state at control is not a jump (in `numbersCheck`). So `quiet_upto` proves `vs(seq j) = vNext(...)` and `HaltOK(seq j)` for every `j < J` by induction, with the other facts. `vertOK` is a part of `numbersCheck` (about 0.1 s more).

| Field before | Now |
|---|---|
| `step`: every clean frame is a `OneFrame` | `moves` (the frame outside the movement), `masked` (only the frames with the pressed side masked), `ends` |
| `reads`: `v₂(fr j) = v₂` | gone. `box` is on the real machines `Q` and `seq j`, so the frame's `v₂` is not needed |
| `box` on `fr j` | `box` on the real machines, from the scroll handler |
| `Moves.input`: the routine reads `readIn(a, b)` | gone. The model's input is the one the routine reads |
| `vert`: frames 1 to 8 follow `vstep` | theorem `vert_of`. New: `vBefore`, `vAfter` (the frame outside the movement routine keeps the vertical bytes) |

## The statements about the whole run are theorems

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
next_of_reads     : reads  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  frames 1..j are Follow ∧ seq 0..j are Clean ∧ bits(seq j) = FF
                                         ∧ frames 1..j are vNext ∧ seq 0..j are HaltOK
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
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

`left` is 0 only on the last row. It has 6 states, and 2 have control. The other 4 are the time-up states. The rows end where `left` is 0, so `left` must not be 0 before control (`EndRun.first`, proved from `chg.time₂` and `chg.ctlFirst₂`). `Route` has a new field `atCtl : pole.seq 0 = chg.seq chg.b₂`. The conditions `entry₂`, `noStart₂`, `quiet₂` of `chg` are used as `Run.change₂` uses them.

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

* On frames 1 to 8 (3,194 frames) also `vs(seq j) = vNext(seq (j − 1), seq j)`, `vBefore`, `vAfter`, `HaltOK` at both ends, `box`, and that `(y, vy, st)` on entering the collision routine is `vstepV`'s result. No difference.
* On every frame the input that the player's routine reads is `readIn(a, b)` of the two ends (the old field `input`): no difference.
* The pressed side is masked on 329 frames (3 from control, 326 around the stairs). All are `OneFrame`, and on none is `MaskStop` needed: each follows `hstep`.
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

* `moves`: the frame outside the movement: `AtCtrl` at the player's routine, nothing writes the horizontal bytes before it, the frame does not end during the movement, the position is far from the ends, and `After`. The movement is proved ([`FrameModel`](../0-0/0-3-2-FrameModel.md)).
* `masked`: a frame where the pressed side is masked is a `OneFrame`.
* `ends`: `seq j` is the end of the frame of `fm j` with `pad j`.
* `vBefore`, `vAfter`: on frames 1 to 8, the frame outside the movement routine keeps the vertical bytes. That the routine follows `vstep` is proved (`vert_of`).
* `box`: on frames 1 to 8 the collision routine gives the same result as on the machine at control.
* `reads`: `fr` is read from the machines. That it is a `Frame` stays an assumption of [Top speed](../0-0/0-1-TopSpeed.md).
* `chg.time₂`, `chg.ctlFirst₂`, `atCtl`.
* `MaskStop` on a frame with Left blocked. `SurfaceRun.maskSame` covers fractions 0, 128, 255 in Lean, and this proof does not use it. All fractions were run as a program (28 s, no difference).

**Files.** `Theorems/SurfaceFrames.lean`, `Theorems/VertModel.lean`, private `Proof/SurfaceFrames.lean` (`side_start`), `Proof/PoleJoin.lean` (`pole_numbers`).

**Reproduce.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # the table above, about 7 minutes of CPU
.lake/build/bin/smbrta vert-model-check                # vertOK and each of its cases, about 0.1 s
```
