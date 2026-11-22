[← Back](README.md) | [English](c-7-4-4-StoredClean.md) | [Japanese](c-7-4-4-StoredClean-ja.md)

# The stored speed after a frame that follows the model, and after a stale one: `ab_run`, `ab_early` narrowed

The fields `ab_run` and `ab_early` of [Joining the bonus room](c-5-RoomJoin.md) (items 1-1-c-7-4 and 1-1-c-7-6) bound the stored speed that a frame reads, on frames that do not follow the model. Round 32 ([The stored speed after a stop](c-7-4-3-AbsKeep.md)) proved the case where the frame before stops him and comes to its player's routine in the state `AtCtrl`. This round proves three more cases:

1. The frame before follows the model: then the stored speed is `|v|` at its end (`ab_cleanW`).
2. The frame before stops him and comes to its player's routine with a stale stored speed: then the speed at its start is 0, and its friction leaves at most one adder and a fraction (`ab_stale`), unless it is in the air with neither Left nor Right.
3. `RoomCore.stop_run` is used only with no wall hit, so it is asked only from `C + 37` on; then `ab_early` has one user, `RoomCore.ab_of`, and there a stop in the state `AtCtrl` at `C + 34` is already one of its cases.

So both fields are asked only when the frame before comes to its player's routine with the stored speed `|v|` and the side he presses masked, or with a stale stored speed in the air with neither Left nor Right.

## Statements

`fm(n)` is the machine where frame `n + 1` begins, `fe(n)` the machine at the end of frame `n`, `T(n)` the machine of frame `n + 1` at its player's routine. `xa` is the stored speed `Player_XSpeedAbsolute`, `v` the speed `Player_X_Speed`, `|x|` the size of a byte as a signed number. `PlayerSubs` is the end of the move. `R = RunSpeedMin` (1.75 px per frame), `A = AirFastSpeed` (1.5625 px per frame). `amax` is the largest friction adder, in 1/256 of a speed unit (about 0.11 px per frame).

On the numbers: `hs(n)`, `v(n)`, `rs(n)`, `st(n)` are the horizontal state, the speed, `RunningSpeed` and the state at the end of frame `n`; `inp(n)` the input of frame `n`; `ab(n)` the stored speed that frame `n + 1` reads at its player's routine; `Follow(n)`: frame `n + 1` follows `hstep`. `CleanW(n)`, `ReadW(n)`: the two cases of the field `clean` for frame `n + 1` (it follows the model; it stops him). `AtCtrl(n)`: `T(n)` is in the state `FrameModel.AtCtrl` (`xa = |v|`, and the side he presses not masked by the collision bits). `Stale(n)`: `xa ≠ |v|` at `T(n)`. `AirNoSide(n)`: in the model's case of `T(n)` he is in the air and presses neither Left nor Right (`FrameModel.stOf ≠ 0`, `FrameModel.lrOf = 0`). The room's numbers are `fall = 34`, `hitF = 37`, `runF = 40`.

```
FrameModel.stored_pathM (proved, StoredClean):
  AtCtrl at R,  the speed in TopSpeed's range,  storedOK,  storedM
    →   ∃ k,  (stepN k R).pc = PlayerSubs  ∧  xa = |v| there

FrameModel.stored_pathF (proved, StoredClean):
  AtFrame at R,  storedOK
    →   ∃ k,  (stepN k R).pc = PlayerSubs  ∧  (xa = |v| there  ∨  (AirNoSide  ∧  xa, v there are those of R))

RoomRun.end_cleanW (proved):   C ≤ n,  n + 1 < t0,  CleanW(n)   →   xa(fe(n + 1)) = |v(fe(n + 1))|
RoomRun.ab_cleanW (proved):    C ≤ n,  n + 1 < t0,  CleanW(n)   →   ab(n + 1) = |v(n + 1)|

RoomRun.absOr0 (proved):       C ≤ n < t0   →   xa(fe(n)) = |v(fe(n))|  ∨  v(fe(n)) = 0

RoomRun.ab_stale (proved):
  C ≤ n,  n + 1 < t0,  ReadW(n),  Stale(n)
    →   256 · ab(n + 1) ≤ 255 + amax   ∨   (AirNoSide(n)  ∧  ab(n + 1) = ab(n))

RoomCore.stop_run (proved: RoomRun.stop_run_of; now from C + 37 on):
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  |v(n)| < R,  ∀ i ∈ inputs, |hstep(hs(n − 1), i).v| < R,  ¬Follow(n)
    →   rs(n + 1) = 0
  (before: C + 34 ≤ n, and the last premise only for n ≠ C + 34)

ab_early (field of RoomRun; narrowed):
  C + 34 ≤ n,  n + 1 < C + 37,  n < t0,  ¬CleanR(n),  ¬AtCtrl(n − 1),  (¬Stale(n − 1)  ∨  AirNoSide(n − 1))   →   ab(n) < A
  (before, round 32: in place of the last two premises,  (n = C + 34  ∨  CleanW(n − 1)  ∨  ¬AtCtrl(n − 1)))

ab_run (field of RoomRun; narrowed):
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  ¬Follow(n),  st(n) = 0,  inp(n + 1).jump = false,  ab(n) ≠ |v(n)|,
  ¬AtCtrl(n − 1),  (¬Stale(n − 1)  ∨  AirNoSide(n − 1))   →   ab(n) < R
  (before, round 32: in place of the last two premises,  (CleanW(n − 1)  ∨  ¬AtCtrl(n − 1)))

NumFacts.amax_air (ROM check):   amax + 255 < 256 · A
```

With `AtV` at `T(n − 1)` (the room's walks give it), `¬AtCtrl(n − 1) ∧ ¬Stale(n − 1)` says that the side he presses is masked there. So the two fields are asked only on two kinds of frames `n`: a frame that comes to its player's routine with the stored speed `|v|` and the pressed side masked, and a frame with a stale stored speed in the air with neither Left nor Right. Each new field asks fewer frames than before: its premises imply the old ones.

## How it goes

**The stored speed of a frame that follows the model.** `FrameModel.stored_path` (round 13) needs the collision bits at the player's routine to be one of `TopSpeed.collBits`, because its stage of `ImposeFriction` is compared with `TopSpeed.frictionCheck`, which runs the routine on those values. A frame that follows the model gives only `bits &&& lr = lr` (the side he presses is not masked); the walks of the room do not know the other bits at a frame's end (round 32). `ImposeFriction` reads the bits once, in `and` with `lr`. So the new walk of `ImposeFriction` (`storedFricM`) runs the real machine, whose bits are known only on `lr` (to be 1), next to the model's machine with the bits `0xFF`: after the `and` both have `lr`, and the walk shows that they end with the same speed and stored speed. `frictionCheck` on the bits `0xFF` then gives `xa = |v|` at the mover (`fric_absM`), and `stored_c4M`, `stored_pathM` carry it to `PlayerSubs`. From there `CleanW.after` (nothing writes the speed) and `InRoom.absAfter` (nothing writes the stored speed) give `end_cleanW`; `InRoom.absKeep` and `InRoom.absBefore` carry it to the next player's routine (`ab_cleanW`).

**The invariant.** `absOr0` is an induction over the room's frames. At first control the stored speed is 0 and the speed 0 (`StartAt`). A frame that follows the model ends with `xa = |v|` (`end_cleanW`). A frame that stops him comes to `PlayerSubs` with `xa = |v|` there, or, in the air with neither Left nor Right, with the speed and the stored speed of its player's routine, which are those of the end of the frame before (`stored_pathF`: `stored_path` with no condition on the stored speed; `ImposeFriction` does not run there). After `PlayerSubs` the collision routine leaves the speed or sets it to 0 (`FrameModel.Collide`), and nothing writes the stored speed. In each case the frame ends with `xa = |v|` or `v = 0`.

**A stale stored speed.** If frame `n + 1` comes to its player's routine with `xa ≠ |v|`, then by `absOr0` the frame before ended with `v = 0`, so frame `n + 1` starts with the speed 0 and a fraction. It is a `TopSpeed.Frame` with the friction's lower bound (`FrameModel.frame_readQL`): at the end of the move `256·v₂ + f₂` is between `−amax` and `255 + amax`, so `256·|v₂| ≤ 255 + amax`. By `stored_pathF` the stored speed there is `|v₂|`, or (in the air with neither side) the stale one carried over, and the frame comes to `PlayerSubs` once (`InRoom.absAfter`). One adder and a fraction are less than 0.2 px per frame, below `A` (`NumFacts.amax_air`), so `|v₂| < A ≤ R`.

**`stop_run` from `C + 37` on.** `RoomCore.stop_run` has one user, `rs_of_safe3`, and its callers (`rs_of_safe`, `no_wall_back`) have no wall hit (`NoWall`): every frame before `C + 37` follows `hstep`. `rs_of_safe3` now takes `NoWall` and uses `stop_run` only on a frame that does not follow `hstep`, so from `C + 37` on. So `stop_run_of` no longer reads `ab_early`; the case `n = C + 34` of `ab_early` was asked only for it and for `ab_of`.

**`ab_early` in `ab_of`.** `RoomCore.ab_of` says, after a stop from `C + 34` to `C + 36`, that the stored speed is below `A` or is `|hstep(hs(n − 1), inp(n)).v|`. `ab_of_run` now splits on frame `n`: it follows the model (`ab_cleanW` gives the first case, `ab = |v|`), it stops him in the state `AtCtrl` (`ab_fresh` gives the `hstep` case, also at `C + 34`), it stops him with a stale stored speed (`ab_stale` gives `< A`, unless in the air with neither side), or the field.

## Measured

`room-ab-check FM2` (the TAS and 2,800 runs of own inputs from first control; binary of this round). The frames of the round 32 field `ab_early` (frame `n + 1` does not follow the model, `n` = `C + 34` or `C + 35`), by what frame `n` did:

| frame `n` | at `n = C + 34` | at `n = C + 35` |
|---|---|---|
| follows the model (now `ab_cleanW`) | 117 | 77 |
| stops him in the state `AtCtrl` (`ab_fresh`; at `C + 34` new in this round) | 162 | 117 |
| stops him with a stale stored speed | 37 | 6 |
| of them in the air with neither side (the field) | 37 | 6 |
| stops him with the side masked (the field) | 0 | 0 |
| other | 0 | 0 |

Round 32's field asked 316 + 83 = 399 of these frames; this round's field asks 43 of them: every stale one was in the air with neither side, so `ab_stale`'s first case took none of them. Their stored speed is at most 0.375 px per frame. None is on the TAS. On every frame of the room up to the entry (336,111 frames) the end has `xa = |v|` or `v = 0` (`absOr0`). The largest `|hstep(hs(n − 1), inp(n)).v|` after a stop in the state `AtCtrl` at `C + 34` is 0.4375 px per frame, below `A`.

`room-approach-check FM2 300 1` and `… 300 0` (the field `ab_run`): 0 frames in the round 32 field, so 0 in the new one (counters 82, 83). `room-stored-check`: `storedM` holds on every case (about 0.2 s), and `amax + 255 < 256·A`.

## Both sides of the friction in one run

`TopSpeed.frictionCheck` (the speed after `ImposeFriction` from above, and the stored speed) and `frictionLowCheck` (from below, round 30) ran `ImposeFriction` on the same machines: every speed, 256 fractions, the adders, the caps, 4 inputs and the collision bits. `FrameModel.frictionBoth` runs it once on each machine and asks both, and `friction_of_both` gives the two checks from it. The private `Proof/TopSpeedFriction.lean` now proves `fric_both` by `native_decide` and `top_frictionCheck` from it, and `Proof/RoomFricLow.lean` takes `room_fric_low` from it with no search (it took about 100 s). `frictionLowCheck` moved from `RoomJoin.lean` to `StoredClean.lean`; its statement is the same. The other way the brief names, a proof of the two bounds from the routine's paths, is not done.

## What remains (not proved)

- `ab_run` and `ab_early` on a frame after one that comes to its player's routine with the stored speed `|v|` and the side he presses masked: there `stored_path` gives the stored speed `|v₂|` of the end of the move, but `v₂` is the masked friction's, not `hstep`'s. With Left and Right both pressed and one side masked, `ImposeFriction` pushes the speed one way where the model pushes it the other, so `|v₂|` can be one adder more than any model step. None was measured.
- The same two fields after a stale stored speed carried over in the air with neither side: the stored speed is that of an earlier stop's end of the move, which in the fall the theorems do not bound. All 43 measured frames of `ab_early` that are left are of this kind.

**Files.** New `Theorems/StoredClean.lean` (`tagsFrM`, `storedFricM`, `storedM`, `fric_absM`, `stored_c4M`, `stored_pathM`, `stored_c4F`, `stored_pathF`). `Theorems/RoomJoin.lean`: `Checks.storedM`, `NumFacts.amax_air`, `RoomRun.end_cleanW`, `ab_cleanW`, `absOr0`, `stale_arith`, `ab_stale`; the fields `ab_early`, `ab_run` narrowed; `RoomCore.stop_run` from `C + 37` on; `rs_of_safe3`, `rs_of_safe` take `NoWall`; `ab_of_run`, `stop_run_of`. `StoredClean.lean` also: `frictionLowCheck` (moved), `frictionBoth`, `friction_of_both`. Programs: `room-stored-check` (new), `room-ab-check` (the split above), `room-approach-check` (counters 82, 83). Private: `Proof/TopSpeedFriction.lean` (`fric_both`) and `Proof/RoomFricLow.lean`, both written by `genRoomFricLow`.
