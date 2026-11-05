[← Back](../README.md) | [English](TopSpeed.md) | [Japanese](TopSpeed-ja.md)

# Top speed bound

**Statement.** Away from platforms, vines, whirlpools, pipes, the flagpole, the axe, castle
loops, level entries and the left screen edge, Mario never moves right by more than 2.5 px
(the running top speed) in a frame, and his speed never goes over the top speed. Running at
top speed and touching nothing moves him exactly 2.5 px per frame. So once he is at top
speed, nothing he can touch (blocks from below or the side, enemies to stomp) gets him
further right than running.

Position in 1/256 px: `P = 256·(256·page + x) + fraction`; `v_top` = the running top speed.

```
Frame.bound :  |v| ≤ v_top  →  |v'| ≤ v_top  ∧  P' − P ≤ 16·v_top
chain_bound :  P(n) − P(0) ≤ 16·v_top·n
Frame.gain  :  V' ≤ max(V, 0) + a_max          (V = 256·v + subspeed; the GainBound of fast accel)
attain      :  at top speed, Right+B for 20 frames: P' − P = 16·v_top every frame
```

Lean: `Theorems/TopSpeed.lean` (`Frame.bound`, `chain_bound`, `Frame.gain`, proved without computation);
private `top_speed` (the routine checks and `attain` by `native_decide`).

## How it is split

All instructions in the ROM that write the player's speed or position were listed from the
disassembly. Apart from the situations excluded above and death, they are in five routines,
which run in this order in a frame. Each one is run alone on the emulator for every value of
the bytes it reads, in their normal ranges:

| routine | checked claim | runs |
|---|---|---|
| `GetPlayerAnimSpeed` (on the ground) | speed and subspeed unchanged, or both 0; `RunningSpeed` and the moving direction stay in range | 10 M |
| `X_Physics` | the speed caps and the friction adder are table entries; the running timer stays in range | 15 M |
| `ImposeFriction` | `|v| ≤ v_top` is kept (the caps clamp the speed); `V' ≤ max(V, 0)` + adder, with `V = 256·v + subspeed` | 24 M |
| `MoveObjectHorizontally` | `P' = P + 16·v` | 21 M |
| `ImpedePlayerMove` (side collision) | speed 0 or unchanged; `P` moves by −256, 0, or +256, and +256 only if `v ≤ 0` | 1.3 M |

Hitting a block from below and stomping an enemy write none of these bytes: they change only
the vertical speed and whether Mario is in the air.

`Frame` describes one frame by these five facts; `Frame.bound` and `chain_bound` follow by
arithmetic. The only way to be pushed right (`ImpedePlayerMove`) needs `v ≤ 0`, so that frame
moves at most 256 < 16·v_top.

## Assumptions (not proved in Lean)

* the list of writers is complete: from the disassembly, and from 390,000 frames of random play
  around the first block and Goomba of 1-1 (no other writer appeared);
* each routine depends only on the bytes it is checked on, in their normal ranges (`Player_State`
  ground or air, the collision bits with only their two low bits cleared); the page byte is
  checked at 0, 1, 30 and 31, the ends of the range of level pages: it enters the mover and the
  side collision only through one add-with-carry;
* no Start/Select.

**Files.** `Theorems/TopSpeed.lean`, private `Proof/TopSpeed*.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta top-check all     # the five routine checks and attain, as a program
```
