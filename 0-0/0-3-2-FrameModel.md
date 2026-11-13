[← Back](../README.md) | [English](0-3-2-FrameModel.md) | [Japanese](0-3-2-FrameModel-ja.md)

# A real frame and the horizontal and vertical models

**Statement.** `hstep` is the horizontal part of one frame, and `vstep` the vertical part. For one frame `frame(M, i)` of a real machine, Lean proves this: from the player's routine to the scroll handler, the machine's bytes change as `hstep` says, and the position moves by `16·v'`. The vertical bytes change as `vstep` says (`vert_model`). With the pressed side masked, the frame follows `hstep` or leaves the speed 0 (`move_masked`). Each of the three also says that each step on the way stays in the frame if the frame has 64 dots left (`InFrameN`, [below](#the-time-of-a-walked-step)): so the frame does not end during the movement if no instruction runs late in the frame (`trace_inFrame`). The parts before the player's routine and after the scroll handler are assumptions on one frame.

`tr(n)` is the machine `n` instructions into `frame(M, i)`. `HS(m)` is the horizontal state read from machine `m` (speed, subspeed, facing, moving direction, whether `RunningSpeed` is 0). `P(m)` is the position. `In(m)` is the input read from the machine at the player's routine. `v'` is the speed of `HS(frame(M, i))`.

```
move_model  :  modelOK,  AtCtrl(R)
               →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs  ∧  HS(stepN(k, R)) = hstep(HS(R), In(R))
                              ∧  P(stepN(k, R)) ≡ P(R) + 16·v'  (mod 2²⁴)
                              ∧  InFrameN(R, k)
clean_frame :  modelOK,  Clean(M, i, n₀)
               →  HS(frame(M, i)) = hstep(HS(M), In(tr(n₀)))  ∧  P(frame(M, i)) = P(M) + 16·v'
frame_read  :  modelOK,  frictionCheck,  ReadFrame(M, i, n₀)
               →  ∃ f : TopSpeed.Frame,  f has the speeds, subspeeds and positions of M and frame(M, i)
```

From `frame_read` and `TopSpeed`'s `Frame.bound`: with `|v| ≤ v_top`, `|v'| ≤ v_top` and `P' − P ≤ 16·v_top`. So `move_top` of `RoomJoin` is now a theorem.

Lean: `Theorems/FrameWalk.lean` (the walk over two machines: `tstep_spec`, `walkT_spec`, `piece_spec`, `leaf_spec`; with detours: `lk_detour`, `walkD_spec`, `leafD_spec`), `Theorems/FrameModel.lean` (`move_model`, `move_masked`, `clean_frame`, `frame_read`), `Theorems/VertModel.lean` (`vert_model`), private `frame_model` (`modelOK`, `native_decide`). `vertOK` and `maskOK` are parts of `SurfaceFrames.numbersCheck`. No file has game values. The checks take about 2 s, 0.1 s and 0.1 s natively.

## The walk over two machines

Instructions advance on two machines at the same place at once. For each register and byte the walk knows one of four things: nothing; the two are the same; both are zero or both are not; known bits of each. No value is enumerated, so the 256 × 256 values of speed and subspeed are not tried. An instruction goes only if the walk knows the addresses it reads and writes. Time is not looked at, because these instructions do not read the clock.

* Each instruction form is proved once (`tstep_spec`). The ROM is looked at only in the check.
* With a real machine next to the machine of `runSub`, a routine does the same in both (`leaf_spec`). Their stack pointers and times may differ.
* With one machine given twice, a piece of code is shown to leave bytes alone and to reach a place (`piece_spec`).

## The time of a walked step

The walk does not look at the time. But an instruction that it follows is not the idle loop (a `JMP` to itself: the emulator jumps there to the next PPU event), and it writes only RAM: no DMA and no register of the PPU. Its action adds at most 6 dots (the page penalty, or a branch), and then the cycles of its opcode, at most 7 (21 dots). A machine of the walk is `Good`: no NMI pending and the NMI off.

```
InFrame(m)        :  m is not halted  ∧  m.pc is not an idle loop  ∧  (fdot(m) + 64 ≤ dotsPerFrame  →  frame(step(m)) = frame(m))
inFrame_of_tstep  :  the walk takes a step from a state Q that holds of m, n  →  InFrame(m) ∧ InFrame(n)
InFrameN(R, k)    :  InFrame(stepN(j, R)) for each j < k
trace_inFrame     :  idle loop at idle,  frame(tr(n₀)) = frame(M),  InFrameN(tr(n₀), k),  ∀ n, tr(n).pc ≠ idle → fdot(tr(n)) ≤ dotsPerFrame − 64
                  →  ∀ j ≤ k,  tr(n₀ + j) = stepN(j, tr(n₀))  ∧  frame(tr(n₀ + j)) = frame(M)
```

`walkT_spec`, `walkD_spec` and `piece_specI` now say `InFrame` of every machine before the stop, and `piece_spec`, `leaf_spec`, `leafD_spec` and the pieces of `move_model` say `InFrameN`. A return that ends a routine of `leafD_spec` meets `InFrame` too (`inFrame_rts`). The cycles of the opcodes are bounded by a check (`cyc_le`, `decide`).

So the old field `longer` (the frame does not end within 728 instructions after the player's routine) follows from the time of each instruction. Above ground that is the condition `time` of `FrameKeep.CleanK`, which every instruction of a frame in control meets (the field `keep.clean`).

## Two machines that run apart for a while

At some places the code reads a byte that is not the same on the two machines, and what it writes there is of no interest. A detour (`Detour`) says: from the cut `c`, each machine alone (the walk of one machine) reaches the cut `c'` and leaves the bytes of `keep`. `walkD` follows the two machines as above, and at the start of a detour it lets each machine run its own way. Then the two are at different counts of instructions.

```
lk_detour  :  Detour.ok(d),  the walk's state at d.c holds of m, n
              →  ∃ k₁ k₂ ≤ fuel(d),  the state after d holds of stepN(k₁, m), stepN(k₂, n)
walkD_spec :  walkD(f, Q) = true,  Q holds of m, n
              →  ∃ k₁ k₂ ≤ f,  stop ∧ goal  and the end state holds of stepN(k₁, m), stepN(k₂, n)
leafD_spec :  walkD from a routine's entry, the stack pointer the same on both
              →  at the routine's return the tags relate the real machine and the result of runSub
```

`leaf_spec` needs a routine that calls no other routine. `leafD_spec` allows calls, because the stack pointer is known. `runSub2` relates the results of `runSub` of two machines in the same way.

## The vertical model

`vstepV(s, A, abs)` is `Jump.vstep` on the machine `vmach`: `m0` with the stack pointer `S` of the player's routine and `DiffToHaltJump = 1`. `A(R)` is bit 7 of `SavedJoypadBits` at `R`. `vs(m)` is the vertical state read from the machine.

```
vert_model :  vertOK,  AtCtrl0(R),  (st(R) = 1 → DTHJ(R) = 1),  PrevA(R) & 80 = A_B(R) & 80
              →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs  ∧  vs(stepN(k, R)) = vstepV(vs(R), A(R), abs(R))
                             ∧  (st = 1 → DTHJ = 1)  at stepN(k, R)  ∧  InFrameN(R, k)
```

`DTHJ` is `DiffToHaltJump`, `PrevA` is `PreviousA_B_Buttons`, `A_B` is `A_B_Buttons`. The check `vertOK`:

* from the player's routine to `PlayerMovementSubs`: one machine, 4608 cases (3 values of `Player_State`, 3 of `AreaType`, 256 of the buttons, 2 of the previous A).
* `PlayerMovementSubs`: the real machine next to the machine of `vstep`, 24 cases (3 states, 4 values of A and B, 2 of the previous A). 6 detours: the crouch's test (it reads `PlayerSize`), `X_Physics`, the jump's sound (`PlayerSize`), the ground's routine, Left and Right in the air, the first test of the vertical move (`TimerControl`).
* from the routine's return to the scroll handler: one machine.

Why the two conditions. `DiffToHaltJump` is 0 at control above ground and 1 after any jump; `m0`, at the start of the level, has 0. The routine compares with it in a jump, and the walk needs it the same on both machines. `vstep` writes A of the frame before from `s.prevA`, which reads `A_B_Buttons`; the real routine reads `PreviousA_B_Buttons`. The game copies the first into the second at the end of the game engine (`SaveAB`).

Found while the check ran as a program first: with only some bits of the buttons known, the walk of one machine cannot branch on their other bits, so the buttons are 256 cases. `MovePlayerHorizontally` indexes by a register loaded from `JumpspringAnimCtrl`, so that byte is known to be 0 at the start of two detours. The ground's routine and the air's Left and Right call routines at the routine's own stack level, so they write the two stack bytes below it.

## A frame with the pressed side masked

`ImposeFriction` first masks Left/Right with the collision bits. `hstep` runs it with the bits of `m0`, where nothing is blocked. When Left is blocked (`noLeft`) and he presses Left, the real routine can take another way.

```
move_masked :  modelOK,  maskOK,  AtCtrl0(R),  bits(R) = noLeft,  noLeft & lr ≠ lr,  0 < v(R) < 128
               →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs
                              ∧  ( HS(stepN(k, R)) = hstep(HS(R), In(R))  ∨  v(stepN(k, R)) = 0 )
                              ∧  P(stepN(k, R)) ≡ P(R) + 16·v'  (mod 2²⁴)  ∧  InFrameN(R, k)
```

`lr` is the Left/Right that `hstep` reads from `In(R)`. `AtCtrl0` is `AtCtrl` without the condition on the mask. The proof:

* `N` is the model's machine at `ImposeFriction` with the real bits. The real friction and `runSub(N)` take the same way (`fric_stage`, a walk of two machines; 1920 of the 4608 cases are masked).
* `runSub(N)` next to `runSub(C)`, `C` the model's machine (`runSub2`, a walk of two machines of `runSub`):
  * Left and Right: both take the same way.
  * Left alone at a speed `v` from 1 to 127: a detour with two starts. From `ImposeFriction` each machine alone comes to `RghtFrict` and writes nothing on the way. One walk for each `v`.
  * Left alone at the speed 0: `runSub(N)` leaves the speed 0, and the model's speed becomes negative. This is the frame that stops (`MaskStop`).
* The speed at `ImposeFriction` is `v(R)` or 0: `X_Physics` does not write it, and `GetPlayerAnimSpeed` writes only 0 to it (`gpasOK`).

`maskOK` is these checks, about 0.1 s natively. It is a part of `SurfaceFrames.numbersCheck`. A detour may now give the second machine its own start (`Detour.c₂`): at `ImposeFriction` the two machines differ in the collision bits, and the bits decide the way.

## The pieces

| piece | result |
|---|---|
| (1) from the start of the frame to the player's routine | above ground: proved from the frame's start in control (`SurfaceFrames.Moves.toAt`, the walk of `CtrlKeep`); in the room: assumption (`at_ctrl`, `before`) |
| (2) from the player's routine to the scroll handler | proved: `move_model` |
| (3) from the scroll handler to the frame's end | above ground: the moving direction, the running speed and the stored speed proved (`AfterKeep.keepH`), the rest assumption (`SurfaceFrames.After`); in the room: assumption (`after` or `collide`) |

Inside (2), for each of 4608 cases (3 values of `Player_State`, 256 of the buttons, 2 of the previous A, 3 of `AreaType`) these walks go through:

* from the player's routine to `X_Physics`: one machine with known bytes; the bytes of the buttons are known.
* `X_Physics`, `GetPlayerAnimSpeed`, `ImposeFriction`: two machines, next to the `runSub` of `hstepN`.
* between them: one machine, showing that the horizontal bytes are not written. The write of the facing is here too.
* `MoveObjectHorizontally`: the three digits from the speed (256 values), the fraction's addition (65536), the additions of `x` and of the page (131072 each), with known values. Together `P' ≡ P + 16·v` (`pos_digits`). The page has no limit.
* the moving direction: 256 values of the speed.

The input of `hstep` is read from the machine. A counts only when newly pressed with `st = 0`: a jump. Select and Start are read only as "a button", so they count as Up (`joyOf`).

## Assumptions (not proved in Lean)

The fields of `Clean(M, i, n₀)`, all on one frame:

* `at_ctrl` (`AtCtrl`): at instruction `n₀` it is at the player's routine. The stack pointer has its value, the routine number is the player's control, `AreaType` is not water, `Player_State` is 0, 1 or 2, no jumpspring, no swimming, no change of size, no NMI. The stored speed is `|v|`. The pressed side is not masked. The last two fail right after a hit.
* `before`: until then nothing writes the horizontal bytes and the position.
* `longer`: the frame does not end during the movement (728 instructions). Above ground it is a theorem (`trace_inFrame`); `Clean` of the room keeps it.
* `after`: from the scroll handler to the frame's end nothing writes them.
* `far`: the position is at least 8 px from both ends of its range. Above ground it is a theorem from the frames before (`SurfaceFrames.far_of_follow`); `Clean` of the room keeps it.

The fields of `ReadFrame(M, i, n₀)`:

* `at_frame` (`AtFrame`): `AtCtrl` without the stored speed and the mask; instead the mask is one of `TopSpeed.collBits` and `|v| ≤ v_top`.
* `before`, `longer`, `far`: as in `Clean`.
* `collide` (`Collide`): from the scroll handler to the frame's end the speed stays or becomes 0, the subspeed stays, `P` stays or moves by −256 or +256, and +256 only with `v ≤ 0`.

`modelOK` and `frictionCheck` are checks on the ROM, passed with `native_decide`.

## What was measured

With the abstract machine of `TaintRun`, each piece was walked watching each of the 8 horizontal bytes (state of TAS frame 500, `rkI`).

| piece | known bytes | steps | failures |
|---|---|---|---|
| NMI's start to the screen update | 4 | 5 | 1 (NMI's byte 10: the previous value of the PPU's control register is not known) |
| screen update to sound | 1 | 3 | 1 (`UpdateScreen+5`, a pointer) |
| sound to the pad's read | 0 | 1,780,102 | 693 (`HandleSquare2Music+9` and others, pointers) |
| the pad's read to the mode's routine | 1 | 2,188 | 0; none of the 8 is written |
| the mode's routine to the player's routine | 3 | 49 | 0; none of the 8 is written |
| the player's routine to the scroll handler | 8 | 390 | 0 (with 4 known: 8 at `UseAdder+8`) |
| the scroll handler to the collision routine | 5 | 821 | `KeepOnscr` writes the speed, `x` and the page: the screen's edge |
| the collision routine | 5 | 547 | 8 (`BlockBufferCollision+43`, a pointer) |
| after the collision routine to the game engine | 1 | 99 | 0; none of the 8 is written |
| the game engine to the frame's end | 3 | 899,031 | 4383 (enemies, sprites: indices not known) |

With the walk over two machines, all cases of (2) take few steps in the routines (`X_Physics` 2,896, `GetPlayerAnimSpeed` 14,776, `ImposeFriction` 133) with no failure.

## Checked on real frames

With `frame-model-check`:

| runs | frames | `Clean` | `Stop` and `ReadFrame` | neither | `Clean` but not as the model |
|---|---|---|---|---|---|
| the TAS in the room | 98 | 98 | 0 | 0 | 0 |
| the room, 300 runs of random inputs | 56,573 | 48,437 | 8,136 | 0 | 0 |
| the room, 3 other kinds of input, 700 runs each (a program not in this repository) | 377,372 | 333,282 | 44,090 | 0 | 0 |

On the 3442 frames of the TAS in control, 3404 are `Clean`, and 0 differ from the model. Those not `Clean`: the mask 17, a write after a hit 25, the stored speed 23 (with overlaps). 3440 are `ReadFrame`; the other 2 are frames that grab the flag. On `ReadFrame` frames, `|v'| ≤ v_top`, `P' − P ≤ 16·v_top` and `V' ≤ max(V, 0) + a_max` failed 0 times. The longest movement is 255 instructions, below the 728 allowed.

The other fields of `RoomRun` were tried again with the input read from the machine (a program not in this repository). On the TAS all hold, with `E` = `C` + 111; on 100 runs each of 4 kinds of input, 0 failed.

The writers of the horizontal bytes after the scroll handler, seen on the 3442 frames of the TAS and on random inputs: `ImpedePlayerMove` (`NXSpd`, `PlatF`), the flag and `PutPlayerOnVine`, `KillPlayer`. In the room, also with random inputs, only `ImpedePlayerMove`. `KeepOnscr` in the scroll handler can write them; it did not happen on these frames.

## What is not proved

* `before`, in the room: from the pad's read to the player's routine the walk closes, as the table shows; this is not a theorem there. Above ground it is a theorem: with the condition `FrameKeep.CleanK` on each instruction (no store through a pointer or an index touches the kept bytes, a pointer read does not read a register), the walk of `CtrlKeep` closes from the frame's start, the screen update and the sound included, to the player's routine ([Above ground: the frames from control](../1-1/e-2-SurfaceFrames.md)).
* For `vert_model`: that the vertical bytes stay after the scroll handler (`SurfaceFrames.OnFrames.vAfter`). Up to the player's routine they are those of the frame before, with the two conditions there: a theorem above ground (`SurfaceFrames.vBefore`), from the frames not counted (a theorem, `OnFrames.lagKeep`) and bit 7 of A of the frame before (a theorem, `OnFrames.prevAll`).
* `after`, `collide`: the collision routine and the game engine do not close. `after` says that there was no hit. Above ground a part is proved: the walks of `AfterKeep` follow the moving direction, the running speed and the stored speed from the scroll handler to the frame's end; what stays assumed there is `SurfaceFrames.After` (the subspeed, the facing, the stored speed at the scroll handler, the collision).
* The stack pointer, no NMI, `AreaType` and so on in `at_ctrl`: in the room not derived from the state at the frame's start. Above ground the stack pointer, no NMI and the routine come from the walk, `AreaType`, no swimming and no change of size from the walk of the whole frame, by induction from control (`SurfaceFrames.OnFrames.areaAll`), and `Player_State` and the jumpspring from their values at the end of the frame before (`SurfaceFrames.CtlState`).
* Runs with a frame that runs over. `clean` does not hold on such a frame. None was seen in the room. Even the shortest frame had 1469 instructions after the arrival.
* That the emulator is the same as the real machine.

**Files.** `Theorems/FrameWalk.lean`, `Theorems/FrameModel.lean`, `Theorems/VertModel.lean`, private `Proof/FrameModel.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta frame-model-check FM2 300
.lake/build/bin/smbrta vert-model-check          # vertOK and each case, about 0.1 s
.lake/build/bin/smbrta mask-model-check          # maskOK and its parts, about 0.1 s
```
