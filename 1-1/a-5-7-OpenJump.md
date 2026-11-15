[← Back](README.md) | [English](a-5-7-OpenJump.md) | [Japanese](a-5-7-OpenJump-ja.md)

# The jumps of the opening

**Claim.** Every jump of the opening's vertical model, from the ground, with A pressed or not on every frame, lands between the two measured lengths of its takeoff speed,
at the ground's height with no vertical speed. So, on the first `N` counted frames (`N = 32`), since each counted frame in the air or with a jump is a step of this model
([The vertical model on real frames](a-5-7-2-OpenAir.md), the old field `vert`), the length of a jump (the old field `jump`) and the ground's height after a landing
(the old field `ground`) are theorems. A jump is followed only up to the counted frame `H = min(N + 1, E)`.

`fm(t)` is the machine when the counted frame `t` begins. `VS(m)` are the vertical bytes of `vstep`: the height `y`, its fraction, the vertical speed `vy`, the fraction
counter, the two forces, the jump's origin, the player's state `st` and A of the frame before. `hi(m)` is the high byte of the height, `abs(m)` the stored speed, `a(t)`
A of the counted frame `t` as the player's routine reads it, `y₀` the height of `m₀`, `S` the stack pointer of the player's routine. `vstepV` is `vstep` on the machine
`VertModel.vmach` (part c). `flat(t) := st(fm t) = 0 ∧ ¬jump(in t)`. `L(v) = (L_tap, L_hold)` are the lengths of `Opening.jumpLens` for the speed `v`.

```
land(s)        :=  if st(s) ≠ 0 ∧ vy(s) ≥ 0 ∧ y(s) ≥ y₀  then  s with y = y₀, vy = 0, fraction 0, st = 0   else  s
vstepO(s, a, b) :=  land(vstepV(s, a, b))
ground0        :=  y = y₀, every other byte 0, A of the frame before not pressed

arcOK          :  in the air:  k < L_hold,  32 ≤ y < y₀;   landed:  L_tap ≤ k ≤ L_hold,  y = y₀,  vy = 0,  fraction 0,
                  the height before land in [y₀, y₀ + LandDepth);   both:  the high byte after the step (on vstep's machine) is 1
arcCheck       :  arcOK on every state reached in at most 80 frames from the takeoff states  vstepO(ground0, A, v),  v ∈ [0, top];  L_tap ≤ L_hold ≤ 80
next_bound     :  in the air at a reached state:  the next height before land < y₀ + LandDepth  and the high byte after the step 1, for both A
lands_by       :  arcCheck,  v ≤ top,  u(1) = vstepO(ground0, A, v),  ∀ e ∈ [1, h):  u(1), …, u(e) in the air,  P(e),  the next bound  →
                     P(e + 1)  ∧  u(e + 1) = vstepO(u(e), a(e), 0)
                  →   (∃ n ≤ h,  L_tap(v) ≤ n ≤ L_hold(v),  u(1), …, u(n − 1) in the air,  st(u(n)) = 0,  y(u(n)) = y₀,  vy(u(n)) = 0,  fraction 0,  P(n))
                      ∨  (u(1), …, u(h) in the air  ∧  h < L_hold(v))

Real.jumpV     :  the checks,  VertOK,  t ∈ [1, N],  t < E,  Held(fm t),  |v(fm t)| ≤ top,  st(fm t) = 0,  GroundAt(fm t),  jump(in t)
                  →   (∃ n,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  st(fm(t + d)) ≠ 0 for 1 ≤ d < n,  st(fm(t + n)) = 0,  GroundAt(fm(t + n)))
                      ∨  (st(fm(t + d)) ≠ 0 for t + d ≤ H  ∧  H − t < L_hold)                                          (the old field jump)
Real.ground_all : the checks,  Real,  Held, StSpring and |v| ≤ top at each counted frame,  st(fm 1) = 0,  GroundAt(fm 1)
                  →   ∀ t ∈ [1, N],  t < E,  st(fm t) = 0  →  GroundAt(fm t)                                       (the old field ground)
Run.pipeSpeed  :  the checks,  1 ≤ E   →   ∀ t ∈ [1, E],  |v(fm t)| ≤ top
```

`P(e)` is carried along the jump: on real frames, the high byte of the height 1 and the halt relation. `H = min(N + 1, E)` is the horizon: the steps of the model
up to `N` need no frame after it. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`. `#print axioms route_1_1` shows no
`sorryAx`.

Lean: `Theorems/OpenJump.lean` (`land`, `vstepO`, `hiAfter`, `arcCheck`, `openJumpCheck`, `next_bound`, `start_bound`, `lands_by`); `Real.jumpV`, `Real.ground_all`,
`last_ground`, `aOf`, `airT`, `Checks.jumps`, `Checks.top16` in `Theorems/OpenFrames.lean`; `Run.pipeSpeed` in `Theorems/Route.lean`; private `Proof/OpenJump.lean`
(`open_jump_check`).

## How it works

* **The model.** At a takeoff the routine overwrites the vertical bytes from the speed's class (`InitJS`: five classes of `|v|`), so the takeoff starts from `ground0`.
  In the air `vstep` runs the movement routine with the stored speed 0: in the air the routine reads the stored speed only in its horizontal part (`VertAir`, part c).
  On the opening's flat ground the collision routine does nothing in the air but the landing: `land`.
* **The search.** The states are the vertical state, the frame count and the two lengths. From the takeoff states (3 distinct ones for the 41 speeds), each frame in the
  air branches on A. A landed state has no successor. `arcCheck` asks `arcOK` on every state of the layers up to 80 (`Cert.checkPrunedS`).
* **The landing.** `lands_by` follows the sequence `u` on the arcs: while in the air, the frame count is below `L_hold`, and `arcOK` of the next arc bounds the model's
  next height (`next_bound`), which the step of a real frame needs. The first frame on the ground comes by `L_hold`, and `arcOK` there gives `L_tap ≤ n` and the ground's
  height; if it does not come by `h`, the frames up to `h` are in the air and `h < L_hold`.
* **On real frames.** `Real.jumpV` takes `u(e) = VS(fm(t + e))` and the vertical model on each real frame (`Real.vertOK`, [The vertical model on real
  frames](a-5-7-2-OpenAir.md)), up to the horizon. The high byte of the height and the halt relation are carried as `P`. `Real.ground_all` takes the landing case
  from `Real.jumpV`: the last counted frame on the ground before a landing is a takeoff, because a frame on the ground with no jump stays on the ground (`Real.flat`). The
  speed at a takeoff is at most the top speed (`Run.pipeSpeed`). The model's count of the frames left in the air (`airT`) gives a jump that has not landed by `H` the frames
  `max(L_tap − 1, H − t − 1)`, between the two lengths.

| | numbers |
|---|---|
| takeoff states | 3 (`|v|` 0–15: lengths 21–53; 16–24: 24–58; 25–40: 21–57) |
| states of the search | 4,765; highest point `y = 93` |
| landings of the model | from `L_tap` to `L_hold` exactly, for each class |
| `openJumpCheck` | 1.2 s natively (with the high byte after each step) |

## Checked on real frames

`open-real-check FM2 300` checks the step of the model (`VStep`) on every counted frame in the air or with a jump up to `N` (see [The vertical model on real
frames](a-5-7-2-OpenAir.md) for the numbers). In the program the stricter `arcOK` holds on all 4,765 states.

## Assumed (not proved in Lean)

* **No longer assumed**: `vert` (now `Real.vertOK`), `jump`, and `ground` after a landing.

**Files.** `Theorems/OpenJump.lean`, `Theorems/OpenFrames.lean`, `Theorems/Route.lean`, private `Proof/OpenJump.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-jump-check                  # the search of the model's jumps (about 5 s)
.lake/build/bin/smbrta open-real-check FM2 300          # the fields of Real and the model's step on real frames (about 1.5 min)
```
