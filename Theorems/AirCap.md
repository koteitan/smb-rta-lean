[← Back](../README.md) | [English](AirCap.md) | [Japanese](AirCap-ja.md)

# The air speed cap

**Statement.** Suppose Mario moves slower than 1.5625 px/frame (the air threshold). In the air he
stays below it, and moves at most 1.5 px per frame. He can only pass it on a ground frame. So
`K` air frames followed by any `n` frames move him at most `1.5·K` px plus a bound that depends
only on `n`. Moving a frame from the second part to the first never raises the bound.

In 1/256 px, with `A` the air threshold as a speed, `a_max` the largest friction adder, and
`dbound` from [Reach](Reach.md):

```
B             =  256·A − 1 + a_max
capDist(0)    =  0
capDist(n+1)  =  max(16·(A − 1) + capDist(n),  16·min(v_top, ⌊B/256⌋) + dbound(B, n))

step_cap      :  |v| < A  →  |v'| < A,  or the frame is on the ground and Φ' ≤ B
dist_capped   :  |v(0)| < A  →  P(n) − P(0) ≤ capDist(n)
air_run       :  |v(0)| < A, K air frames  →  |v(K)| < A and P(K) − P(0) ≤ 16·(A − 1)·K
landing_bound :  |v(0)| < A, K air frames, then n frames  →
                 P(K + n) − P(0) ≤ 16·(A − 1)·K + capDist(n)
landing_later :  16·(A − 1)·(K + k) + capDist(n) ≤ 16·(A − 1)·K + capDist(n + k)
air_cap_room  :  (K, n) = (7, 46): at most 121.75 px;  (K, n) = (5, 47): at most 121.25 px
```

Lean: `Theorems/AirCap.lean`, private `air_cap_room` (the numbers by `native_decide`).

## How

Below the threshold, a frame in the air uses a lower speed cap: the speed is cut back to it, with its
fraction kept. On the ground the higher cap applies only with the button of the moving direction
and B (or the running timer), and that frame sets the facing direction to the moving direction.
So right after the frame that reaches the threshold, `Φ = |V| ≤ 256·A − 1 + a_max`. The bound on `Φ` of
[Reach](Reach.md) does not see this: it allows the charge for the facing direction on top of a
speed at the cap, and a full gain on the next frame.

`capCheck` runs every state in the four speed steps below the threshold (every fraction, facing
direction, moving direction, running speed) through every input; about 470,000 frames, 4 s. For
lower speeds `stepOk` of the potential is enough: one frame cannot reach the threshold.

## Assumptions (not proved in Lean)

* Those of the horizontal frame `hstep`, on the page [Reach](Reach.md).
* Nothing is touched. A hit on a wall or a block sets the speed to about 0, which only lowers what
  comes after.

**Files.** `Theorems/AirCap.lean`, private `Proof/AirCap.lean`.

**Reproduce.** `python3 prove.py` builds it. [The 1-1 route](../docs/route-1-1.md) uses it for
the bonus room.
