[← Back](README.md) | [English](c-7-13-4-StandHit.md) | [Japanese](c-7-13-4-StandHit-ja.md)

# The position before the first stand, proved

Until this round the field `stand_P` of [Joining the bonus room](c-5-RoomJoin.md) said that on the frame before the first stand of the fall (before `C + 34`) he is at or left of `standP = 3712` (14.5 px). Two theorems used it:

- `stand_first` shows that the first stand does not follow `hstep`. It used `stand_P` on a frame that follows `hstep` (it argues by contradiction).
- `wall_turn` used it on the first stand when that stand's frame is the first frame that does not follow `hstep`.

This round proves both uses, and `stand_P` is gone:

- `stand_first` takes the position from the new theorem `RoomRun.fall_left` (before the first stand he is more than one pixel left of the block's corner) and two walks from the end of the move: with x from 13 on no foot is in a solid cell (`WallF`), with x at most 12 the old argument (`WallQ`).
- `wall_turn` uses the new proved fact `RoomCore.stand_hit` (`RoomRun.stand_hit_of`): x at most 12 at the end of the move (`WallX`), and the lower bound of the friction (`FrameModel.frame_readQL`).

The field `stand_fast` is narrowed: it is asked only on a stand whose frame follows `hstep` (`stand_first`) or after an earlier stand (`stand_gap`). The proof of `stand_hit` does not use it.

## Statements

`P(n)` is the position at the end of frame `n` (in 1/256 px), `st(n)` the player's state there, `V(n) = 256·v + f` the speed with its fraction there. `Q` is the end of the move of frame `n + 1` (the machine at `PlayerSubs`), and `x(Q)`, `y(Q)`, `page(Q)`, `high(Q)`, `st(Q)`, `vy(Q)` are its bytes there. `Follow(n)`: frame `n + 1` follows `hstep`. `Φ₀ = 152` is the potential of the state at first control, `c_P = 13056` (51 px) the block's corner, `cornerX = 51`. `ysFall` is the list of the 33 heights at the end of the move of the first fall before its last frame (`vstepR` from the states of `fallLayer`).

```
WallX(Q)  :=  high(Q) = 1 ∧ page(Q) = 0 ∧ 13 ≤ x(Q) < 17 ∧ 32 ≤ y(Q) < groundY ∧ st(Q) ∈ {1, 2} ∧ vy(Q) ≥ 0
WallF(Q)  :=  high(Q) = 1 ∧ page(Q) = 0 ∧ 13 ≤ x(Q) < cornerX ∧ y(Q) ∈ ysFall ∧ st(Q) = 2 ∧ vy(Q) ≥ 0

RoomWall.wall_frameX, RoomWall.wall_frameF (walks, proved):
  a frame of the room whose end of the move Q meets WallX(Q) (or WallF(Q)), and that ends in the player's routine, ends with st ≠ 0

InRoom.wall (three new parts, proved by Route.Run.roomWall):
  the end of the move Q of a frame in the air is its only PlayerSubs  (RoomVert.after_Q)
  WallX(Q)  →  st(n + 1) ≠ 0
  WallF(Q)  →  st(n + 1) ≠ 0

FrameModel.frame_readQL (proved, with the ROM check frictionLowCheck):
  a frame that is a TopSpeed.Frame has  min(V₁, 0) − amax ≤ V₂
  (V₁ = 256·v₁ + f₁ after the animation routine, V₂ = 256·v₂ + f₂ at Q, amax = 456)

RoomRun.fall_left (proved):
  C ≤ k < C + 34,  (∀ j, C < j < k → st(j) ≠ 0)   →   P(k) + 256 < c_P

RoomCore.stand_hit (new fact, proved by RoomRun.stand_hit_of):
  C ≤ n,  n + 1 < C + 34,  n < C + 15,  (∀ j, C ≤ j < n → Follow(j)),  ¬Follow(n),
  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0     →   P(n) ≤ standP

stand_P (field): removed
  (before: C ≤ n,  n + 1 < C + 34,  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0  →  P(n) ≤ standP)

stand_fast (field, narrowed):
  C ≤ n,  n + 1 < C + 34,  (Follow(n) ∨ ∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0   →   standV ≤ −V(n)
  (before: the same without the third premise)
```

## The proofs

**`fall_left`.** It is `RoomCore.corner_late` with the frames before the first stand. `corner_late` is a theorem on `RoomCore`, whose construction uses `stand_first`, so it cannot be used there. With no frame off `hstep` before `k`, the frames are air frames (`air_in_of` and the states before the stand) and the fall's potential bounds the position (`fall_runR`): `P(k) ≤ P1 + airDist(Φ₀, 34)`. After a frame off `hstep`, the last wall frame and the potential of a stop from there (`anchor_atR`, `anchor_PR`): `P(k) ≤ wallP + dbound(stopPhi, 34 − 15)`. The check `WallFacts.fallQ` puts both more than 256 below `c_P`.

**`stand_first`.** Under `Follow(n)` the end of the frame is left of `c_P − 256` (`fall_left`) and `Q` at most 1 px right of it (`q_le_end`): the page 0 and `x(Q) < cornerX`. At `Q` the vertical bytes are those of the first fall (`fall_mem`): the state 2, `vy ≥ 0`, the vertical page 1, and a height of `ysFall`. With `x(Q) ≥ 13`, `WallF(Q)`: the frame ends with `st ≠ 0`, against `st(n + 1) = 0`. With `x(Q) ≤ 12`, `WallQ(Q)` as before (the speed at the end is `hstep`'s, negative by `stand_fast`), and the frame ends with `st ≠ 0`, on the floor, or with the speed 0: each is false.

**`stand_hit`.**

1. Frame `n + 1` does not follow `hstep`, so it is not a frame of the model (`CleanW`): it is a `TopSpeed.Frame`, and `frame_readQL` gives its end of the move `Q` with the lower bound of the friction. `Q` is the end of the move of `InRoom.wall`, since a frame in the air comes to `PlayerSubs` once.
2. Every frame before `n + 1` follows `hstep`, so `|V(n)| ≤ Φ(n) ≤ iterN(Φ₀, n − C) = 152 + 304·(n − C) ≤ 4408` (`J_runR`).
3. The field `wall`: `P(n) ≤ wallP = 3968`. So `V₂ ≤ max(V₁, 0) + amax ≤ 4408 + 456` and `P(Q) = P(n) + 16·v₂ ≤ 3968 + 304 = 4272 < 4352`: the page 0 and `x(Q) < 17` (the first part of the check `standX`).
4. At `Q` the vertical bytes are those of the first fall: the state 2, `vy ≥ 0`, the vertical page 1, and `32 ≤ y < groundY` (`wallYCheck`, the new check `wallYCheckX`). If `13 ≤ x(Q)`, then `WallX(Q)`, and the frame ends with `st ≠ 0`: against `st(n + 1) = 0`. So `x(Q) ≤ 12` and `P(Q) ≤ 3327`.
5. With `frame_readQL`, `V₂ ≥ −4408 − 456`, and `16·P(n) = 16·P(Q) − 256·v₂ ≤ 16·3327 + 4408 + 456 + 255`, so `P(n) ≤ 3646 ≤ standP` (the second part of `standX`, for each `n − C < 15`).

The proof of `stand_hit` uses the fields `wall` and `clean`; not `stand_fast` or `stand_wall`. `wall_turn` then gets, with `left_far` and `stand_far` as before, that such a stand is not before `C + 16`.

## Checks on the ROM (new)

- `RoomWall.familyX` and `cellsX` (fields of `RoomWall.Checks`, private `room_wall`): the walk `check1X` from the cut at `Q` back to the collision routine's return, for `x` from 13 to 16, the heights from 32 to one above the floor's, and the states 1 and 2 (1,152 walks). At the floor's rows (heights 176 to 180 and 192 to 196) the walk does not pass: the feet are in the floor there. So the heights stop below the floor's.
- `RoomWall.FChecks` (private `room_wall_f`): `check1X` in the state 2 for `x` from 13 to 50 and the 33 heights of `ysFall` (1,254 walks), and its cells. At `x = 51 = cornerX` the walk and the cells do not pass: his right side check is in the block's column there.
- `FrameModel.frictionLowCheck` (private `Proof/RoomFricLow.lean`, `room_fric_low`, about 60 s natively): `ImposeFriction` on the machines of `TopSpeed.frictionCheck` (every speed from −40 to 40, fraction, adder, cap, side and collision bits) ends with `V' ≥ min(V, 0) − adder`.
- `WallFacts.standX`, `yX`, `fallQ` (private `room_stand_w`).

## Measured

`room-approach-check FM2 300 1` and `… 300 0` (this round, on the final program; the TAS and 2,701 own runs each, 764,248 and 769,213 room frames; a big player and the size as it is):

- Stands before `C + 34`: 44 and 50. All are first stands (no stand after an earlier one), and none follows `hstep`. So the narrowed `stand_fast` has no measured frame in its field (the old one had all 44 and 50). On the frame before each stand `−V ≥ 3952` and `4256` (`standV = 3584`) and `P ≤ 3632` (the old `standP = 3712`).
- First stands by `C + 15` that are the first frame off `hstep` (the case of `stand_hit`): 0 and 0. Measured stands come at frames 18 to 30.
- Frames in the air before `C + 34` with `WallX` at the end of the move that end in the state 0: 0 (a bug if not).
- The fields of 1-1-c-7-4, measured only: `wall` 8,123 and 8,154 frames off `hstep` before `C + 37`, all `WallAt` (the largest `P` before 3888 and 3904, after 3824, against `wallP = 3968`); `late` 3,215 and 3,226 frames, false on none; `stop_run` 10,627 and 10,675 frames, false on none.

## What remains

- `stand_fast` (narrowed): before a stand whose frame follows `hstep`, or after an earlier stand, `−V ≥ standV`. Measured runs have no frame in the field (above). A proof needs the speed at a later stand.
- `stand_wall`, and the fields `wall`, `late`, `stop_run` of 1-1-c-7-4 (measured above, not proved; `late` and `stop_run` narrowed: [How the left wall stops him: measured, and `stop_run`, `late` narrowed](c-7-4-1-StopRun.md)).

**Files.** `Theorems/RoomWall.lean`: `endX`, `check1X`, `xsX`, `ysX`, `familyX`, `familyF`, `xsF`, `endX_spec`, `check1X_eq`, `mem_xsX`, `mem_ysX`, `mem_xsF`, `Checks.familyX`, `Checks.cellsX`, `FChecks`, `wall_atX`, `wall_atF`, `wall_frameX`, `wall_frameF`. `Theorems/RoomJoin.lean`: `FrameModel.frictionLowCheck`, `lowOK`, `fric_readL`, `frame_pathL`, `frame_readQL`; `WallX`, `WallF`, `ysFall`, `mem_ysFall`; `InRoom.wall`; `wallYCheckX`, `wallYCheckX_spec`; `WallFacts.standX`, `yX`, `fallQ`; `Checks.fricLow`; `RoomCore.stand_hit`; `RoomFields.stand_fast` (narrowed), `stand_P` (removed); `RoomRun.start_fallR`, `psiP_startR`, `fall_runR`, `anchor_PR`, `left_farR`, `wall_firstR`, `anchor_atR`, `fall_left`, `J_runR`, `hitQ_arith`, `hitP_arith`, `pos_lt_of`, `stand_hit_of`; `stand_first`, `stand_gap`, `wall_turn`, `toCore`. `Theorems/Route.lean`: `Run.roomWall`, `Run.inRoom`. Private `Proof/RoomFricLow.lean` (`room_fric_low`), `Proof/RoomWall.lean` (`room_wall`, `room_wall_f`), `Proof/RoomJoin.lean` (`room_stand_w`, `room_checks`).
