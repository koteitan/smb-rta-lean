[← Back](../README.md) | [English](Reach.md) | [Japanese](Reach-ja.md)

# Reach

**Statement.** From the start of 1-1 (standing still):

1. Under the conditions of [Top speed bound](TopSpeed.md) (walls and blocks allowed), Mario
   cannot move right by more than `reach(n)` in `n` frames; for `n ≥ 22` that is
   `2.5·n − 23.25` px.
2. In the open area (nothing touched), he cannot move right by more than `dbound(n)`; for
   `n ≥ 28` that is `2.5·n − 38.375` px.

The TAS fast accel (32 frames) followed by Right+B moves him `2.5·n − 41.94` px (checked at
`n = 52`), 3.56 px (1.4 frames at top speed) behind the second bound. With the jump lengths,
[The opening](Opening.md) closes this gap: nothing gets further than the TAS.

Position `P` in 1/256 px, `V = 256·v + subspeed`, `a_max` = the largest friction adder.

```
adv(w)        =  max(16·min(v_top, ⌊(w + a_max)/256⌋), 256)
reach(w, 0)   =  0
reach(w, n+1) =  adv(w) + reach(w + a_max, n)

Frame.adv_le :  max(V, 0) ≤ w  →  P' − P ≤ adv(w)
chain_reach  :  max(V(0), 0) ≤ w  →  P(n) − P(0) ≤ reach(w, n)
reach_closed :  256·v_top ≤ w + a_max·K + a_max  →  reach(w, K + m) = reach(w, K) + 16·v_top·m
reach_11     :  from the 1-1 start (w = 0): P(n) − P(0) ≤ reach(0, n),
                reach(0, 22 + m) = 16·v_top·(22 + m) − 5952,
                TAS witness: P(52) − P(0) = 16·v_top·52 − 10736
```

Lean: `Theorems/Reach.lean` (`chain_reach`, `reach_from`, `reach_closed`; proved without
computation), `Theorems/TopSpeed.lean` (`Frame.adv_le`, `Frame.gain`), private `reach_11`
(the numbers by `native_decide`). The open-area bound: below.

## How

One frame gives `V' ≤ max(V, 0) + a_max` (`Frame.gain`), so after `k` frames
`max(V, 0) ≤ w + a_max·k`. The speed a frame moves with is at most `⌊(w + a_max)/256⌋` and at
most `v_top`. The only push to the right that does not come from the speed is the push out of a
wall (`ImpedePlayerMove`, +256 = 1 px), and it only comes with a speed `≤ 0`; so a frame
moves at most `max(16·v, 256)`. Summing over the frames gives `reach`.

## Assumptions (not proved in Lean)

* Those of [Top speed bound](TopSpeed.md): the five routines are the only writers of the
  speed, the subspeed and the position, and each depends only on the bytes it was checked on.
* `X_Physics` takes the friction adder from the table (checked there), so it is at most
  `a_max`.

## The open area: a potential for the facing direction

The first bound is 18.7 px above the TAS witness: it lets every frame use the largest adder
`a_max`. In the game the adder is doubled only when the facing direction differs from the
moving direction, and setting the facing direction (Left+Right, or Left) costs a frame with a
small adder. A potential counts this:

```
Φ = |V| + w(facing, moving)
w = 0    if facing = moving            c = 2·a₀ − 2·a₁   (a₀, a₁: the first two adders)
    c    if facing ≠ moving ∈ {1, 2}
    c    if moving = 0  (not set yet: the 1-1 start)
    2·c  if moving = 3  (a stopped skid copies the facing direction Left+Right)

potCheck  :  Φ' ≤ Φ + g_fast,   and  Φ' ≤ Φ + g_slow  while slow
             (g_slow = 2·a₁, g_fast = a_max; slow: RunningSpeed = 0 and |v| < v_air)
next(p)   =  p + (p < θ ? g_slow : g_fast)          θ = 256·v_air − 255
dist_le   :  Σ_frames 16·v ≤ dbound(Φ₀, n),   dbound(p, n+1) = 16·min(v_top, ⌊next(p)/256⌋) + dbound(next(p), n)
reach_open:  from the 1-1 start, dbound(Φ₀, 28 + m) = 16·v_top·(28 + m) − 9824
```

`v_air` is the speed from which `X_Physics` uses the running adder in the air (read from the
code). While `p < θ`, every state with `Φ ≤ p` has `|v| < v_air`, and `RunningSpeed` is still
0 (it is set only from a speed of at least the running threshold, which is above `v_air`).

`hstep` is the horizontal part of a frame: `X_Physics`; on the ground `GetPlayerAnimSpeed`,
the facing direction set from Left/Right, `ImposeFriction`; in the air `ImposeFriction` when
Left or Right is held; then the moving direction from the sign of the speed. The routines run
as the game's code; the order and the two direction writes are from the disassembly.
`potCheck` runs `hstep` on every state (speed `|v| ≤ v_top`, every subspeed, facing, a moving
direction that fits the speed, `RunningSpeed` zero or not) and every input (ground, jump start,
air; every set of Right, Left, Down, Up, B; running timer zero or not). `hstep` first drops the
inputs a frame does not read (`norm`: in the air only Left/Right, and Down on a jump start; on
the ground the timer when B is held, and Up when another button is held), so 38 inputs remain:
about 4.9 M runs, three files of about 11 s. `check_of` proves that this covers the whole
domain.

Lean: `Theorems/Potential.lean` (`hstep`, `potCheck`, `step_J`, `dist_le`, `dbound_closed`,
`check_of`; proved without computation), private `reach_open` (`potCheck` and the numbers by
`native_decide`).

Assumptions (not proved in Lean): `hstep` is what a frame does to the horizontal state (the
order, the direction writes, and the inputs `norm` drops; compared with the relaxed step on
3.4 M steps of the fast-accel searches, no difference); the open area (`Player_CollisionBits` as at the start,
no side collision, so `P` moves by `16·v`); `X_Physics` reads `RunningSpeed`, `RunningTimer`
and `AreaType` only as zero or not; no Start/Select.

**Files.** `Theorems/Reach.lean`, `Theorems/Potential.lean`, private `Proof/Reach.lean`,
`Proof/ReachOpen*.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta reach-check     # the bounds against some input sequences, as a program
.lake/build/bin/smbrta pot-check       # potCheck, as a program
.lake/build/bin/smbrta hstep-validate lr 31   # hstep against the relaxed step
```
