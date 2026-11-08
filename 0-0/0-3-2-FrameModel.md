[← Back](../README.md) | [English](0-3-2-FrameModel.md) | [Japanese](0-3-2-FrameModel-ja.md)

# A real frame and the horizontal model

**Statement.** `hstep` is the horizontal part of one frame. For one frame `frame(M, i)` of a real machine, Lean proves this: from the player's routine to the scroll handler, the machine's bytes change as `hstep` says, and the position moves by `16·v'`. The parts before the player's routine and after the scroll handler are assumptions on one frame.

`tr(n)` is the machine `n` instructions into `frame(M, i)`. `HS(m)` is the horizontal state read from machine `m` (speed, subspeed, facing, moving direction, whether `RunningSpeed` is 0). `P(m)` is the position. `In(m)` is the input read from the machine at the player's routine. `v'` is the speed of `HS(frame(M, i))`.

```
move_model  :  modelOK,  AtCtrl(R)
               →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs  ∧  HS(stepN(k, R)) = hstep(HS(R), In(R))
                              ∧  P(stepN(k, R)) ≡ P(R) + 16·v'  (mod 2²⁴)
clean_frame :  modelOK,  Clean(M, i, n₀)
               →  HS(frame(M, i)) = hstep(HS(M), In(tr(n₀)))  ∧  P(frame(M, i)) = P(M) + 16·v'
frame_read  :  modelOK,  frictionCheck,  ReadFrame(M, i, n₀)
               →  ∃ f : TopSpeed.Frame,  f has the speeds, subspeeds and positions of M and frame(M, i)
```

From `frame_read` and `TopSpeed`'s `Frame.bound`: with `|v| ≤ v_top`, `|v'| ≤ v_top` and `P' − P ≤ 16·v_top`. So `move_top` of `RoomJoin` is now a theorem.

Lean: `Theorems/FrameWalk.lean` (the walk over two machines: `tstep_spec`, `walkT_spec`, `piece_spec`, `leaf_spec`), `Theorems/FrameModel.lean` (`move_model`, `clean_frame`, `frame_read`), private `frame_model` (`modelOK`, `native_decide`). Neither file has game values. The check takes about 2 s natively.

## The walk over two machines

Instructions advance on two machines at the same place at once. For each register and byte the walk knows one of four things: nothing; the two are the same; both are zero or both are not; known bits of each. No value is enumerated, so the 256 × 256 values of speed and subspeed are not tried. An instruction goes only if the walk knows the addresses it reads and writes. Time is not looked at, because these instructions do not read the clock.

* Each instruction form is proved once (`tstep_spec`). The ROM is looked at only in the check.
* With a real machine next to the machine of `runSub`, a routine does the same in both (`leaf_spec`). Their stack pointers and times may differ.
* With one machine given twice, a piece of code is shown to leave bytes alone and to reach a place (`piece_spec`).

## The pieces

| piece | result |
|---|---|
| (1) from the start of the frame to the player's routine | assumption (`at_ctrl`, `before`) |
| (2) from the player's routine to the scroll handler | proved: `move_model` |
| (3) from the scroll handler to the frame's end | assumption (`after` or `collide`) |

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
* `longer`: the frame does not end during the movement (728 instructions).
* `after`: from the scroll handler to the frame's end nothing writes them.
* `far`: the position is at least 8 px from both ends of its range.

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

* `before`: from the pad's read to the player's routine the walk closes, as the table shows; this is not a theorem in Lean. The screen update and the sound do not close.
* `after`, `collide`: the collision routine and the game engine do not close. `after` says that there was no hit.
* The stack pointer, no NMI, `AreaType` and so on in `at_ctrl`: not derived from the state at the frame's start.
* Runs with a frame that runs over. `clean` does not hold on such a frame. None was seen in the room. Even the shortest frame had 1469 instructions after the arrival.
* That the emulator is the same as the real machine.

**Files.** `Theorems/FrameWalk.lean`, `Theorems/FrameModel.lean`, private `Proof/FrameModel.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta frame-model-check FM2 300
```
