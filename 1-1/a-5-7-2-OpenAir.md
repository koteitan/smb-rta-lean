[← Back](README.md) | [English](a-5-7-2-OpenAir.md) | [Japanese](a-5-7-2-OpenAir-ja.md)

# The vertical model on real frames

**Claim.** Each of the first `N` counted frames (`N = 32`, before the entry `E`) that is a takeoff or in the air is followed by a counted frame whose vertical bytes
are the step of the opening's vertical model `vstepO` ([The jumps of the opening](a-5-7-OpenJump.md)). This was the field `vert` of `OpenFrames.Real`. It is now a
theorem (`Real.vertOK`), from conditions on single frames and on their instructions. It is also no longer asked after the counted frame `N`: the model needs the frames
left in the air only up to the counted frame `H = min(N + 1, E)`.

`fm(t)` is the machine when the counted frame `t` begins, `R` the machine at the first arrival at the player's routine (`n₀ = arrAt`), `Q` the scroll handler
(`PlayerSubs`), `cE` the collision routine, `cR` its return, `end` the frame's end. `VS(m)` are the bytes of `vstep` (the height `y`, its fraction, the vertical speed
`vy`, the fraction counter, the two forces, the jump's origin, the state `st`, A), `hi(m)` the high byte of the height, `abs(m)` the stored speed, `a(t)` A of the frame
as the player's routine reads it, `y₀` the ground's height, `d = LandDepth`, `top` the top speed. `vstepV`, `vRun` are `vstep` and its machine after the movement
routine, on the machine `VertModel.vmach`.

```
Halt(m)    :=  st(m) = 1  →  DiffToHaltJump(m) = 1
PrevOK(m)  :=  bit 7 of A and B of the frame before = bit 7 of A and B
r(t)       :=  vstepV(VS(fm t), a(t), 0)
VPre(t)    :=  (st(fm t) = 0  →  jump(t) ∧ GroundAt(fm t) ∧ abs(fm t) ≤ top)
               ∧ (st(fm t) ≠ 0  →  hi(fm t) = 1 ∧ Halt(fm t) ∧ y(r(t)) < y₀ + d ∧ hi(vRun) = 1)
VStep(t)   :=  hi(fm(t + 1)) = 1  ∧  Halt(fm(t + 1))
               ∧ (st(fm t) = 0  →  VS(fm(t + 1)) = vstepO(ground0, A, abs(fm t)))
               ∧ (st(fm t) ≠ 0  →  VS(fm(t + 1)) = land(r(t)))

Real.vertOK   :  the checks,  Real,  Held and StSpring at each counted frame,  PrevOK(fm 1)
                 →   ∀ t ∈ [1, N],  t < E,  VPre(t)  →  VStep(t)
Real.prevAll  :  the checks,  Real,  Held,  PrevOK(fm 1)   →   ∀ t ∈ [1, N + 1],  t ≤ E,  PrevOK(fm t)
Real.jumpV    :  the checks,  VertOK,  a takeoff at t ≤ N,  t < E
                 →   (∃ n,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  in the air from t + 1 to t + n − 1,  GroundAt(fm(t + n)))
                     ∨  (in the air from t + 1 to H  ∧  H − t < L_hold)
air_real      :  st(m) ∈ {1, 2},  Halt(m),  the collision flag 0,  CleanK, RdOK1 on each instruction
                 →   the frame comes to Q once from R on, at k₁, then to cR at k₂, and
                     Ok1(k₁)  →  VS(k₂) = land(VS(k₁)) ∧ hi(k₂) = 1 ∧ Halt(k₂)
                     Ok1(m) := y(m) < y₀ + d ∧ hi(m) = 1 ∧ st(m) ∈ {1, 2}
take_real     :  a takeoff at y₀ with abs(m) = u ≤ top   →   at the first cR:  VS = vstepO(ground0, A, u),  hi = 1,  DiffToHaltJump = 1
vert_airH     :  vert_air (part c) with the high byte:  hi(R) = 1  →  hi(Q) = hi(vRun)
```

`land` is `OpenJump.land`. `H` is the horizon. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenAir.lean` (the phases, `piecesQ`, `zoneA`, `okA`, `startsA`, `airCheck`), `Theorems/OpenAirFrame.lean` (`PhiA`, `phi_step`, `split_cover`,
`piece_facts`, `walk_frame`, `air_real`, `take_real`, `airAll`, `AfterVS`), `Theorems/OpenWalk.lean` (`walkP`, `frame_of_walkP`), `Theorems/OpenVert.lean`
(`vert_airH`, `vertAirHOK`), `Theorems/OpenFrames.lean` (`VPre`, `VStep`, `VertOK`, `Real.vertOK`, `Real.prevAll`, `airT`); private `Proof/OpenAir.lean`
(`open_air_check`, `open_vert_check`).

## How

**A takeoff.** At the player's routine the walk knows the ground (`y₀`, the high byte 1, no vertical speed), A pressed and not on the frame before, and the stored
speed `u`, one start for each `u ≤ top`. The jump's start overwrites the other vertical bytes, so the walk knows every vertical byte up to the return of the collision
routine, and checks there that they are the model's takeoff (`vsK`).

**In the air.** The movement routine changes the vertical bytes from values the walk does not know. So up to `Q` they are related to `vstep` by the walk of two machines
(`VertAir.vert_air` of part c, with the high byte added: `OpenVert.vert_airH`). From `Q` the walk of one machine (`OpenWalk.walkP`, the walk of `OpenFlat` with phases)
follows the frame to its end. Its phases (`AS.log`):

| phase | from | asks of each step | facts outside the walk (`PhiA`) |
|---|---|---|---|
| `pre` | the player's routine | | no arrival at `Q` yet |
| `q1`, `q` | `Q` | no write to the 11 bytes of `pAll`, no second `Q` | the bytes of `pAll` are those of `Q` |
| `k1`, `k` | `cE`: an exact height below `y₀`, or near the ground and rising | the same | the same, and not landing at `Q` |
| `l1`, `l` | `cE`: near the ground, falling, the state 1 or 2 | no write to `pRest` (7 bytes) | `pRest` as at `Q`, landing at `Q` |
| `n1`, `n` | `cE`: the rest | no second `Q` | `Ok1` false at `Q` |
| `aft` | `cR`: `k` (the halt relation known), `l` (landed at `y₀` and the halt relation known), `n` | no `Q` | `Ok1(Q) → VS(cR) = land(VS(Q))`, `hi(cR) = 1`, `Halt(cR)` |
| `tk u`, `tkd` | a takeoff with the speed `u`; `cR` with `vsK` | | `VS(cR) = vstepO(ground0, A, u)` |

At `cE` a state of the phase `q` is split by the exact height (below `y₀ + d`, the high byte 1) and, near the ground, by bit 7 of the vertical speed and the state
(`piecesQ`). The first block buffer has only two tiles by rows, so with the height known every read of the collision routine is known. The "no write" of a step is
`StepWrites.keepOK` ([The one-step lemma](d-3-4-1-StepWrites.md)). The facts `PhiA` go on over each step (`phi_step`), and with `OpenWalk.frame_of_walkP` they hold at
the frame's end. The walk asks that the frame comes to `Q` only once after the player's routine; so the arrival of `vert_airH` is the walk's, and `VS(Q)` is the model's
`r(t)`. `VPre` gives `Ok1` at `Q`: the height of the model's step is below `y₀ + d`, the high byte after the step is 1 (the search of `OpenJump` asks both).

**The collision flag.** The collision routine does nothing when the flag `DisableCollisionDet` is not 0 (only the vine's entrance writes it). Its RAM index is read
from the ROM (the operand of the routine's first load). [The block buffers](a-5-4-3-3-3-OpenMap.md) now also keep it 0 on every frame, and a walk of `CtrlKeep` follows
it to the player's routine.

**After the return.** The bytes of `vsA` (11: the vertical bytes, the high byte, the state, A and B, the halt value) do not change: the field `afterV`, assumed (as
before, for more bytes). The frames not counted keep them: [LagFrames](a-5-5-3-LagFrames.md) follows 7 more bytes.

**The two relations.** The halt relation is carried along each jump: at the takeoff the walk knows the halt value 1, in the air the walk checks it at `cR`.
`PrevOK` holds at every counted frame by the walk of part e (`GuardE.prev_endE`): it asks `CleanK` of `guardE` and no store by address to the routine, the mode or the
task (the field `cleanK` with 5 more protected bytes, and the new field `noStore`), and `PrevOK` at the counted frame 1 (the title's check of the state at control now
also asks A and B and A and B of the frame before, `StartRun.stI`).

**The horizon.** A jump that has not landed by `H` is given `max(L_tap − 1, H − t − 1)` frames in the air (`airT`); `arcOK` gives `H − t < L_hold`. The model's steps up
to `N` do not need more.

| check on the ROM | numbers | time natively |
|---|---|---|
| `airCheck`: the search | 506,135 runs of the search, 0 failures, a table of 95,459 states | 40 s |
| `airCheck`: the walk of the table and of the 129 starts (3 cuts × 43) | | 4.3 s |
| `vertAirHOK` (the walks of `vert_air` with the high byte) | 4,608 first pieces, 16 cases, the last piece | 0.2 s |
| the walk of the collision flag to the player's routine | | 0.3 s |
| `openJumpCheck` with the high byte | 4,765 states | 1.2 s |

`airCheck` takes much more than a few seconds: its search is in the check (`native_decide` runs it). It is in its own private file `Proof/OpenAir.lean`.

## Checked on real frames

`open-real-check FM2 300` checks on each counted frame up to `N` the fields of `Real` (`cleanK` with `guardE`, `noStore`, `afterV` with the 11 bytes, `map`,
`after`), what the proof derives at the frame's start (`PrevOK`, the halt relation, the collision flag 0), and on the frames in the air or jumping the step `VStep`:

| runs | counted frames | in the air or jumping | jump starts | frames failing a condition |
|---|---|---|---|---|
| the movie (HappyLee), 1 run | 32 | 29 | 2 | 0 |
| own random inputs from control, 300 runs | 9,600 | 8,069 | 528 | 0 |
| own runs that pause on the first frames, 60 runs | 1,856 | 1,624 | 116 | 0 |

`open-map-check FM2 30` checks `map` (now with the collision flag): 91 runs, 9,997 frames, 24,433,366 instructions, not `MapOK` 0.

## Assumed (not proved in Lean)

* **No longer assumed**: `vert`.
* **New**: `noStore` (no instruction of a counted frame stores to the routine, the mode or the task by address).
* **Wider**: `cleanK` asks `CleanK` of `guardE` (5 more protected bytes: A and B, A and B of the frame before, the moving direction, the running speed, the stored
  speed); `afterV` asks 11 bytes (it asked 4); `map` (`MapOK`) protects the collision flag too.
* Round 19: `cleanK` is no longer a field: `Route.Run.pipeReal` proves it from `chg.upCleanU` ([One condition on each instruction up to the pipe](a-5-10-UpClean.md)).

**Files.** `Theorems/OpenAir.lean`, `Theorems/OpenAirFrame.lean`, `Theorems/OpenWalk.lean`, `Theorems/OpenVert.lean`, `Theorems/OpenFrames.lean`, private
`Proof/OpenAir.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-air-search all          # the search and the check of the walk, and the other checks (about 50 s)
.lake/build/bin/smbrta open-real-check FM2 300      # the conditions of Real on real frames
```
