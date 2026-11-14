[← Back](README.md) | [English](a-5-7-OpenJump.md) | [Japanese](a-5-7-OpenJump-ja.md)

# The jumps of the opening

**Claim.** Every jump of the opening's vertical model, from the ground, with A pressed or not on every frame, lands between the two measured lengths of its takeoff speed,
at the ground's height with no vertical speed. So, on the first `N` counted frames (`N = 32`), if each counted frame in the air or with a jump is a step of this model
(the new field `vert`), the length of a jump (the old field `jump`) and the ground's height after a landing (the old field `ground`) are theorems.

`fm(t)` is the machine when the counted frame `t` begins. `VS(m)` are the vertical bytes of `vstep`: the height `y`, its fraction, the vertical speed `vy`, the fraction
counter, the two forces, the jump's origin, the player's state `st` and A of the frame before. `hi(m)` is the high byte of the height, `abs(m)` the stored speed, `a(t)`
A of the counted frame `t` as the player's routine reads it, `y₀` the height of `m₀`, `S` the stack pointer of the player's routine. `vstepV` is `vstep` on the machine
`VertModel.vmach` (part c). `flat(t) := st(fm t) = 0 ∧ ¬jump(in t)`. `L(v) = (L_tap, L_hold)` are the lengths of `Opening.jumpLens` for the speed `v`.

```
land(s)        :=  if st(s) ≠ 0 ∧ vy(s) ≥ 0 ∧ y(s) ≥ y₀  then  s with y = y₀, vy = 0, fraction 0, st = 0   else  s
vstepO(s, a, b) :=  land(vstepV(s, a, b))
ground0        :=  y = y₀, every other byte 0, A of the frame before not pressed

arcOK          :  in the air:  k < L_hold,  and  32 ≤ y < y₀  or  vy < 0
                  landed:      L_tap ≤ k ≤ L_hold,  y = y₀,  vy = 0,  fraction 0,  and the height before land in [y₀, y₀ + LandDepth)
arcCheck       :  arcOK on every state reached in at most 80 frames from the takeoff states  vstepO(ground0, A, v),  v ∈ [0, top];  every L_hold ≤ 80
lands          :  arcCheck,  v ≤ top,  u(1) = vstepO(ground0, A, v),  ∀ e ∈ [1, 80):  u(1), …, u(e) in the air  →  u(e + 1) = vstepO(u(e), a(e), 0)
                  →   ∃ n,  L_tap(v) ≤ n ≤ L_hold(v),  u(1), …, u(n − 1) in the air,  st(u(n)) = 0,  y(u(n)) = y₀,  vy(u(n)) = 0,  fraction 0

field vert     :  ∀ t,  1 ≤ t < N + 80,  st(fm s) ≠ 0 for N < s ≤ t,  ¬flat(t)   →   hi(fm(t + 1)) = 1  ∧
                  (st(fm t) = 0  →  VS(fm(t + 1)) = vstepO(ground0, A, abs(fm t)))  ∧
                  (st(fm t) ≠ 0  →  VS(fm(t + 1)) = vstepO(VS(fm t), a(t), 0))
Real.jumpV     :  the checks,  Real,  t ∈ [1, N],  Held(fm t),  |v(fm t)| ≤ top,  st(fm t) = 0,  jump(in t)
                  →   ∃ n,  L_tap ≤ n ≤ L_hold,  st(fm(t + d)) ≠ 0 for 1 ≤ d < n,  st(fm(t + n)) = 0,  GroundAt(fm(t + n))      (the old field jump)
Real.ground_all : the checks,  Real,  Held, StSpring and |v| ≤ top at each counted frame,  st(fm 1) = 0,  GroundAt(fm 1)
                  →   ∀ t ∈ [1, N],  t < E,  st(fm t) = 0  →  GroundAt(fm t)                                       (the old field ground)
Run.pipeSpeed  :  the checks,  1 ≤ E   →   ∀ t ∈ [1, E],  |v(fm t)| ≤ top
```

`vert` is asked of the counted frames up to `N`, and after `N` only while the jump that is in the air at the counted frame `N + 1` lasts: the frames after it come near the
first blocks, and the model knows no blocks. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`. `#print axioms route_1_1`
shows no `sorryAx`.

Lean: `Theorems/OpenJump.lean` (`land`, `vstepO`, `arcCheck`, `openJumpCheck`, `lands`); the field `Real.vert`, `Real.jumpV`, `Real.ground_all`, `last_ground`, `aOf`,
`Checks.jumps`, `Checks.top16` in `Theorems/OpenFrames.lean`; `Run.pipeSpeed` in `Theorems/Route.lean`; private `Proof/OpenJump.lean` (`open_jump_check`).

## How it works

* **The model.** At a takeoff the routine overwrites the vertical bytes from the speed's class (`InitJS`: five classes of `|v|`), so the takeoff starts from `ground0`.
  In the air `vstep` runs the movement routine with the stored speed 0: in the air the routine reads the stored speed only in its horizontal part (`VertAir`, part c).
  On the opening's flat ground the collision routine does nothing in the air but the landing: `land`.
* **The search.** The states are the vertical state, the frame count and the two lengths. From the takeoff states (3 distinct ones for the 41 speeds), each frame in the
  air branches on A. A landed state has no successor. `arcCheck` asks `arcOK` on every state of the layers up to 80 (`Cert.checkPrunedS`).
* **The landing.** `lands` follows the sequence `u` on the arcs (`reach_arcs`): while in the air, the frame count is below `L_hold`, so the first frame on the ground comes
  by `L_hold`, and `arcOK` there gives `L_tap ≤ n` and the ground's height.
* **On real frames.** `Real.jumpV` takes `u(e) = VS(fm(t + e))` and `vert` for each step. The high byte of the height at the landing comes from `vert` on the frame
  before it. `Real.ground_all` now takes the landing case from `Real.jumpV`: the last counted frame on the ground before a landing is a takeoff, because a frame on the
  ground with no jump stays on the ground (`Real.flat`). The speed at a takeoff is at most the top speed (`Run.pipeSpeed`, from `PipeFrames.speed_of_reads`).

| | numbers |
|---|---|
| takeoff states | 3 (`|v|` 0–15: lengths 21–53; 16–24: 24–58; 25–40: 21–57) |
| states of the search | 4,765; highest point `y = 93` |
| landings of the model | from `L_tap` to `L_hold` exactly, for each class |
| `openJumpCheck` | 2.4 s natively |

## Checked on real frames

`open-real-check FM2 300` checks `vert` on every counted frame in the air or with a jump, up to the counted frame `N` and after it up to the landing: the TAS 42 frames,
own inputs 11,839 frames, runs that pause on the first frames 2,571 frames; 0 failures. Before this round the old `jump` held on the same runs (2 + 528 + 116 jump starts).

## Assumed (not proved in Lean)

* **`vert`** (new): each counted frame in the air or with a jump is followed by a counted frame whose vertical bytes are the step of `vstepO`, with the high byte 1. A
  condition on single frames. Its parts are: the movement up to the scroll handler (`VertModel.vert_model` at the takeoff, `VertAir.vert_air` in the air: proved, with
  conditions at the player's routine), the collision routine in the air (`land`: not proved), the frame after the return of the collision routine (as `afterV`, but for
  all the bytes of `VS`), and the frames not counted (as `lags_keepI`, for the bytes of `VS` not in it). Proving these is the next step.
* **No longer assumed**: `jump`, and `ground` after a landing.

**Files.** `Theorems/OpenJump.lean`, `Theorems/OpenFrames.lean`, `Theorems/Route.lean`, private `Proof/OpenJump.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-jump-check                  # the search of the model's jumps (about 5 s)
.lake/build/bin/smbrta open-real-check FM2 300          # vert, and the other fields of Real, on real frames (about 1.5 min)
```
