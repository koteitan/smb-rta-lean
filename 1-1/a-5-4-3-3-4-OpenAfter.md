[← Back](README.md) | [English](a-5-4-3-3-4-OpenAfter.md) | [Japanese](a-5-4-3-3-4-OpenAfter-ja.md)

# The opening after the scroll handler and after the collision routine

**Claim.** Two fields of the first 32 counted frames ask less than before.

* `after` (from the scroll handler to the frame's end) asked 8 horizontal bytes, the stored speed and the collision bits. It now asks 5 bytes, that a speed that is
  not 0 is not set to 0, and the collision bits. The moving direction, the running speed, the speed and the stored speed are theorems.
* `afterV` (from the return of the collision routine to the frame's end) asked 11 vertical bytes. It now asks 7. The vertical force down, the jump's origin, the
  jump's halt value and A and B are theorems.
* The old `after` was **false on a real run** at the counted frame 32. The new one lets frame 32 end at the left end of the level.

`fm(t)` is the machine when the counted frame `t` begins, `b(t)` the machine at its end, `tr(t, k)` the machine after `k` of its instructions, `n₀(t)` the first
arrival at the player's routine. `Q` is the scroll handler (`PlayerSubs`), `cR` the return of the collision routine in the player's routine. `v` is the speed, `ab`
the stored speed, `bits` the collision bits, `hs` the horizontal state, `P` the position (1/256 px). `N = 32`, `E` is the entering frame.

```
hRest          =  {Player_X_MoveForce, PlayerFacingDir, Player_X_Position, Player_PageLoc, SprObject_X_MoveForce}
AfterR(q, b)   :=  (∀ x ∈ hRest,  b[x] = q[x])  ∧  (v(b) = 0 → v(q) = 0)  ∧  bits(b) = FF
AtEdge(b)      :=  Player_PageLoc(b) = 0  ∧  Player_X_Position(b) = 0
after  (field) :  t ∈ [1, N],  t < E,  k ≥ n₀(t),  pc(tr(t, k)) = Q   →   AfterR(tr(t, k), b(t))  ∨  (t = N ∧ AtEdge(b(t)))

vsR            =  {Player_Y_Position, Player_Y_HighPos, Player_Y_Speed, Player_Y_MoveForce, Player_YMF_Dummy, VerticalForce, Player_State}
kI             =  {VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump, A_B_Buttons}
afterV (field) :  t ∈ [1, N],  t < E,  k ≥ n₀(t),  pc(tr(t, k)) = cR   →   ∀ x ∈ vsR,  b(t)[x] = tr(t, k)[x]

Real.frame_step :  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t),  st(fm t) ∈ {0, 1, 2},  no jumpspring,  |v(fm t)| ≤ top
                   →   st(tr(t, n₀)) = st(fm t)
                       ∧ ( (hs(b t) = hstep(hs(fm t), in t)  ∧  (P(b t) − P(fm t) − 16·v(b t)) mod 2²⁴ = 0  ∧  Held(b t))
                           ∨ (t = N ∧ AtEdge(b t)) )
Real.afterVS    :  Checks,  Real,  t ∈ [1, N],  t < E,  Held(fm t)
                   →   ∀ k ≥ n₀(t),  pc(tr(t, k)) = cR  →  ∀ x ∈ vsR ∪ kI,  b(t)[x] = tr(t, k)[x]              (the old field afterV)

OpenAfter.keep_at  :  ctrlCheck,  checkAt(v, q, bs),  StartK(m),  CleanK_F on each instruction,  CleanK of the guard with x protected for each x ∈ bs,
                      no store to the routine, the mode or the task by address,  AreaOK(v, m),  n₀ the first arrival at the player's routine
                      →   ∀ k ≥ n₀,  pc(tr k) = q  →  ∀ x ∈ bs,  frame(m, i)[x] = tr(k)[x]
OpenAfter.keep_ret :  keep_at  with  q = cR,  bs = kI,  under  CleanK_E on each instruction
```

`Held(m)` is `ab(m) = |v(m)| ∧ bits(m) = FF ∧` the area's three bytes. `CleanK_E` is `CleanK` of `FrameKeep.guardE`, `CleanK_F` of `FrameKeep.guardF`. The theorems
without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenAfter.lean` (`checkAt`, `retCheck`, `keep_at`, `keep_ret`), `Theorems/OpenFrames.lean` (`hRest`, `AfterR`, `AtEdge`, `Real.frame_step`,
`Real.afterVS`, `OpenRunM.endB`), `Theorems/OpenAirFrame.lean` (`vsR`, `AfterVR`); private `Proof/OpenAfter.lean` (`open_after_check`).

## The old `after` was false on a real run

The old field said: from the scroll handler on, no horizontal byte changes, on each of the frames 1 to 32. A program (`open-left-real`) searches own inputs from
control for the smallest position (a beam search on the real machine, 10 inputs per frame).

| frames | smallest position at the frame's end | frames where the old `after` fails |
|---|---|---|
| 1 to 31 | 576 at frame 31 (2.25 px) | 0 |
| 32 | 0 (the left end) | 624 |

22,100 frames were run in all.

One of them: A with B and Left, Left, A and Left, Left, Left, A with B and Left, … for 32 frames. Frame 32 begins at `P = 576` with the speed −40. The movement
takes him to `P = −64`: the page is 255 at the scroll handler. The scroll handler finds him left of the screen's left edge, puts him at the edge and sets the speed
to 0. The frame ends at `P = 192` with the speed 0. So the position, the page and the speed at the frame's end are not those at the scroll handler.

The model says the same: in 31 frames no input gets more than 9664 to the left (so `P ≥ 576`), in 32 frames none gets more than 10304 (so `P ≥ −64`), and both
bounds are reached (`open-left-check 31 9664` true, `31 9600` false; `32 10304` true, `32 10240` false). On the frames 1 to 31 he is at least 2 px right of the
left end, so the edge does not stop him there.

So `after` now has a second case on frame `N`: the frame ends at the left end of the level (`AtEdge`: page 0, pixel 0). On the 624 frames above it holds. Then the
frame is no step of the model, and the bound of the opening is direct: he is below 1 px, and the machine at control is at least 1 px from the left end
(`Checks.left`, a check on `m₀`). `OpenRunM.step` has the same second case, `OpenRunM.reachAll` goes up to the start of frame `N`, and `OpenRunM.endB` splits frame
`N`. The field `page` is still needed in the first case.

## How: after the scroll handler

Part e proved three walks from the scroll handler to the frame's end, for a frame that starts in control, with `CleanK_E` on each instruction and no store to the
routine, the mode or the task by address. The frames of the opening meet these (`cleanK` from `chg.upCleanU`; no store: [OpenStore](a-5-4-3-3-5-OpenStore.md)).

* `GuardE.keepHE`: the moving direction, the running speed and the stored speed at the frame's end are those at `Q`.
* `CollideKeep.speed_end`: the speed at the frame's end is that at `Q`, or 0. `AfterR` says that it is not 0 unless it was 0 at `Q`. So it is that at `Q`.
* `FrameModel.stored_path`: at `Q` the stored speed is `|v|`. It needs the speed at most the top speed and the collision bits among four values when the frame
  begins (`Held`, `Run.pipeSpeed`). The frame comes to `Q` once after the player's routine (`GuardE.subs_onceE`), so the arrival of `stored_path` is that of the
  movement.

With the five bytes of `AfterR`, all 8 horizontal bytes at the frame's end are those at `Q`, and `ab = |v|` at the frame's end. This is what the old field asked.

## How: after the return of the collision routine

Part e's `VertKeep.keep_end` keeps the four bytes of `kI` from `Q` to the frame's end. `afterV` asks them at a later place, the return `cR`. The walks give the
frame's end only, not the steps between. So `OpenAfter` runs the same two walks of `AfterKeep` with `cR` in place of `Q` (`checkAt`): from the player's routine to
the first arrival at `cR`; from there to the frame's end with one byte followed (the walk fails on any write to it, and on a second arrival at `cR`).

Tried first, and why not: an "every step between" form of `keep_end`. A state without the followed byte covers the machine for every value of the byte, so the
frame's end would have two values: every state between follows the byte. But a state may say that the byte fell by one (`spent`), and nothing excludes that
without a lemma on each of the abstract instructions.

## Why the other bytes stay

`open-after-search` runs, for each byte, a search from `Q` or from `cR` to the frame's end with the byte followed and protected. A failure is a path with a store to
the byte by its address.

| byte | protected by `guardE` | failing paths from `Q` | from `cR` | stores after `cR` |
|---|---|---|---|---|
| `Player_MovingDir`, `RunningSpeed`, `Player_XSpeedAbsolute` | yes | 0 | 0 | proved (`keepHE`) |
| `Player_X_Speed` | yes | 17 | 13 | `KillPlayer` (10), `ImpedePlayerMove` (3): kept or 0, proved (`speed_end`) |
| `VerticalForceDown`, `JumpOrigin_Y_Position`, `DiffToHaltJump`, `A_B_Buttons` | yes | 0 | 0 | proved (`keep_end`, `keep_ret`) |
| `Player_CollisionBits` | yes | 4 | 3 | `ImpedePlayerMove` (a platform's side) |
| `SprObject_X_MoveForce` | yes | 25 | 25 | the move routine's store with an index that may be 0 |
| `Player_X_Position` | no | 34 | 30 | the move routine (25), `PositionPlayerOnHPlat` (2), `ImpedePlayerMove` (3) |
| `Player_PageLoc` | no | 36 | 32 | the same, and `ExecGameLoopback` (2) |
| `Player_X_MoveForce` | no | 1 | 0 | none (before `cR`: `PutPlayerOnVine`) |
| `PlayerFacingDir` | no | 2 | 0 | none (before `cR`: `FlagpoleCollision`, `PutPlayerOnVine`) |
| `Player_Y_Position` | no | 11 | 10 | `PositionPlayerOnVPlat` (8), the jumpspring (2) |
| `Player_Y_HighPos` | no | 8 | 8 | `PositionPlayerOnVPlat` |
| `Player_Y_Speed` | no | 38 | 34 | a stomp, a bounce, a platform, the jumpspring, `KillPlayer` |
| `Player_Y_MoveForce` | no | 9 | 8 | `PositionPlayerOnVPlat` |
| `Player_State` | no | 6 | 3 | `SetCollisionFlag` (a platform) |
| `Player_YMF_Dummy`, `VerticalForce` | no | 0, 1 | 0, 0 | none |

* The position, the page, the collision bits, the height, the vertical speed and the state are written after `cR` by the enemies' code (platforms, a stomp, the
  jumpspring). The walk does not know the objects, so these stay in `after` and `afterV`.
* `Player_X_MoveForce`, `PlayerFacingDir`, `Player_YMF_Dummy` and `VerticalForce` have no store after `cR`. But `guardE` does not protect them, so a store through an
  index or a pointer drops them in the walk. A new condition on each instruction would be needed (and `ImposeGravity` writes `Player_YMF_Dummy` through the index 0
  before `Q`). Not done: `guardE` and `chg.upCleanU` belong to other parts this round.

## The checks

| check | numbers | time natively |
|---|---|---|
| `OpenAfter.retCheck` (the search to `cR`: 13,324 steps, 28 states there; four searches from `cR`: 58,398 steps each, a table of 3,723) | 0 failures | 2.3 s (`Proof.OpenAfter`: 4.1 s) |
| `AfterKeep.hCheck`, `CollideKeep.vCheck`, `FrameModel.storedOK`, `TopSpeed.frictionCheck` | those of part e (`pole_numbers`, `top_frictionCheck`) | no new time |

## Checked on real frames

`open-real-check FM2 300` checks the new `after` and `afterV` on each counted frame, and what the walks and the proof say: `keepHE`, `speed_end`, `keep_ret`, the
stored speed at `Q` and at the frame's end, the 8 horizontal bytes when `AfterR` holds.

| runs | counted frames | frames failing a condition |
|---|---|---|
| the movie | 32 | 0 |
| own inputs from control (300) | 9,600 | 0 |
| own runs that pause on the first frames (60) | 1,856 | 0 |
| `open-left-real FM2 60` (the search to the left) | 22,100 | 0 (624 last frames at the left end) |

## Assumed (not proved in Lean)

* `after`: the five bytes of `hRest`, that the speed is not set to 0, the collision bits `FF`; or, on frame `N`, the left end of the level.
* `afterV`: the seven bytes of `vsR`.
* `page` (as before).

**Reproduce.**
```
.lake/build/bin/smbrta open-after-search all        # the searches from the scroll handler and from the return, byte by byte (8 s)
.lake/build/bin/smbrta open-after-search check      # OpenAfter.retCheck
.lake/build/bin/smbrta open-left-real FM2 60        # the search of own inputs to the left, with the conditions of Real (1 min)
.lake/build/bin/smbrta open-real-check FM2 300      # the conditions of Real on real frames
```
