[← Back](README.md) | [English](c-7-11-1-RoomFall.md) | [Japanese](c-7-11-1-RoomFall-ja.md)

# Every frame of a jump in the room follows `vstep`, up to the landing

**Claim.** A frame of the bonus room before the entering frame that starts in the air follows `vstep` up to the landing. Let `t` be `vstep` of the vertical bytes at the frame's start, on the machine of the player's routine, with A of the frame and the stored speed 0. Then `t` is in the air (the state 1 or 2), and at the frame's end the vertical bytes are `t`, or `t` is falling and they are the landing of `t`. On the jumps from the floor this `vstep` is the one of [Joining the bonus room](c-5-RoomJoin.md). So every frame of a jump from the floor follows `vstep` up to the landing.

[The first frames of a jump](c-7-5-1-RoomVert.md) proved this for the first 8 frames of a jump from the floor, where he rises. This page adds the frames where he falls, and every state of a jump. It is item 1-1-c-7-11 (`vert_air`) on every frame of a jump from the floor: in the air the vertical motion does not depend on the horizontal one; only the takeoff reads the stored speed.

It also proves the field `stand_row` (item 1-1-c-7-5): from the air to standing, his height is a whole row and his vertical speed is 0. It is no longer assumed.

`V` is the set of bytes that `vsOf` reads: the height `y` and its fraction, the vertical speed `vy` and its fraction `mf`, the two forces, the jump's origin, the state `st`, and A and B. `V'` is `V` without `y`, `vy`, `mf`, `st`. `Q` is the scroll handler (`PlayerSubs`), `tr(j)` the machine `j` instructions into the frame, `end` the machine at the frame's end, `rt` the routine byte. "Falling" means the state is 1 or 2 and bit 7 of `vy` is 0.

```
land(s)      =  s with  y := y & F0,  vy := 0,  mf := 0,  st := 0

after_QC  :  RoomCond(M),  SiteOK on each instruction
             →  pc(tr(j)) = Q  for at most one j of the frame,
                and  pc(tr(j)) = Q,  falling(tr(j)),  rt(end) = rt_room  →
                  V(end) = V(tr(j))
                  ∨  ( V'(end) = V'(tr(j))  ∧  st(end) = 0  ∧  vy(end) = 0  ∧  mf(end) = 0  ∧  y(end) = y(tr(j)) & F0 )
jump_frame:  RoomCond(M),  SiteOK,  AtV(R),  st(M) ∈ {1, 2},  (st(M) = 1 → DTHJ(M) = 1),  PrevA(M) & 80 = A_B(M) & 80,  rt(end) = rt_room,
             each instruction away from the idle loop 64 dots or more before the frame's end
             →  t.st ∈ {1, 2}  ∧  ( vs(end) = t  ∨  (falling(t)  ∧  vs(end) = land(t)) )        t = vstepV(vs(M), A(R), 0)
bridgeAll :  every state u of every jump from the floor:  u.st ∈ {1, 2};  u not at the ground  →  ∀ a,  vstepV(u, a, 0) = vstep(u, a, 0);
             the jump reaches the ground by frame 80
vair_of   :  C ≤ n < t0,  n + 1 < E,  st(n) ≠ 0
             →  t.st ∈ {1, 2}  ∧  ( vs(n + 1) = t  ∨  (falling(t)  ∧  vs(n + 1) = land(t)) )            t = vstepR(vs(n), a(n + 1))
varc_all  :  C ≤ n < t0,  n + 1 < E,  OnArc(T, n),  ¬(falling(vs(n)) ∧ y(vs(n)) ≥ y_ground)
             →  vs(n + 1) = vstep(vs(n), a(n + 1), 0)  ∨  (falling(vstep(…))  ∧  vs(n + 1) = land(vstep(vs(n), a(n + 1), 0)))
arc_step_all: OnArc(T, n),  ¬(falling(vs(n)) ∧ y(vs(n)) ≥ y_ground),  vs(n + 1) = vstep(vs(n), a(n + 1), 0)  →  OnArc(T, n + 1)
stand_row_of: C ≤ n,  n + 1 < t0,  st(n) ≠ 0,  st(n + 1) = 0  →  y(n + 1) mod 16 = 0  ∧  W(n + 1) = 0
```

`vstepV` and `vstepR` are `vstep` on the machine `vmach` (the jump's halt value 1, the stack pointer of the player's routine). `W = 256·vy + mf`.

Lean: `Theorems/RoomFall.lean` (`phC`, `finC`, `piecesC`, `yPieces`, `after_QC`, `at_Q`, `jump_frame`, `FChecks`, `jump_room`), `Theorems/VertAir.lean` (`goalVA`, `vert_air`, `land`, `bridgeAll`, `bridgeAll_of`), `Theorems/RoomVert.lean` (`keyV`), `Theorems/RoomJoin.lean` (`vstepR`, `InRoom.air`, `RoomRun.vair_of`, `RoomRun.stand_row_of`, `RoomRun.varc_all`, `arc_step_all`, `RoomCore.stand_row`), `Theorems/RoomPair.lean` (`RoomWalks.fall`), `Theorems/Route.lean` (`Run.roomAir`, `Run.inRoom`); private `Proof/RoomFall.lean`.

## How

**The movement routine in the air.** `vert_air` now also says that the routine leaves the state 1 or 2: the walk of the routine knows the state at its return, the same on both machines, and the check asks it to be 1 or 2 (`goalVA`).

**A third walk of one whole frame (`walkC`).** It is the walk of [the block map](c-7-12-RoomMap.md), through the frame of [RoomVert](c-7-5-1-RoomVert.md) (`walkV`, `frame_of_walkV`). At `Q` a state falling in the air is split by the state (1 or 2) and gets the bit; the other states at `Q` are marked `[2]`. The bit says that no step since `Q` has written `V'`. The list says what happened to the four bytes of the landing (`y`, `vy`, `mf`, `st`):

| list | meaning |
|---|---|
| `[3]` | not written |
| `[5, h]` | not written; the high four bits of `y` are `h` |
| `[1, h, 0]` | written since |
| `[6]` | landed: `st`, `vy`, `mf` known 0, `y` known `h`; then `y` forgotten; no byte of `V` written since |
| `[4, 4, 4]` | a step that the list does not allow may have written `V` (the bit is dropped) |

A state `[3]` is split by the high bits of `y` at an `AND` with `y`: the landing takes `y & F0` so, and the walk knows the result. A state marked `[1, h, 0]` or `[4, 4, 4]` must end the frame out of the room's routine (`finC`). This is the time running out, as in `walkB`. So a frame that ends in the room's routine either keeps `V` from `Q`, or reaches `[6]`.

The first try split `y` already at `Q`, into 16 pieces each. Its search had 638,074 states and took 73 s. Splitting only at the `AND` keeps the extra pieces on the few instructions of the landing.

**The key of the search.** The search joins states with the same key. Pieces with different `h` must stay apart. `keyV` now puts the second entry of a list of two or more entries into the key. The other walks have lists of at most one entry, so their keys are the same as before. (A first try put `y` among the bytes of the key; the order of the search changed, and two states of the table before `Q` ran out of fuel.)

**The frame.** `at_Q`: the first arrival at the player's routine (`before_R`), `vert_air` there, and `FrameModel.trace_inFrame` give the arrival at `Q` with the vertical bytes `t` and `t.st ∈ {1, 2}`. Then `t` rises (`walkB`, `RoomVert.after_Q`: `V` stays) or falls (`walkC`, `after_QC`: `V` stays or he lands). `jump_frame` puts the two together.

**Every state of a jump from the floor.** `bridgeAll` checks every state of every jump from the floor (`Jump.arcCheck`): the state is 1 or 2; before the ground, `vstep` on `vmach` is `vstep` on the machine at the start of the level for both values of A; and the jump reaches the ground by frame 80, so no state is missed. `bridgeAll_of` gives it on each state reachable from a takeoff.

**In `RoomJoin`.** `InRoom.air` is `jump_frame` on the room's frames before the entry (`Route.Run.roomAir`; the player's state at the frame's start is 0, 1 or 2 by `RoomPair.quad_run`). `RoomRun.vair_of` reads it with `read_vs`, `clean` (`AtV` at the arrival) and `InRoom.pair`. A of the frame is A of the vertical state at its end in both cases, since the landing does not write A. `RoomRun.varc_all` is `vair_of` on a jump from the floor with `bridgeAll`.

**`stand_row`.** A frame from the air to standing before `t0`: by `vair_of` it is the landing of `t` (the other case keeps the state 1 or 2). So `y` is `t.y & F0`, a whole row, and `vy = mf = 0`. The field was asked before `C + 51`; it is used only on frames of the fall, before `t0`, so `RoomCore.stand_row` asks it before `t0` and `toCore` proves it (`stand_row_of`).

| check on the ROM | states | time in a program |
|---|---|---|
| `checkC` (`walkC`) | search 105,068 (table 27,492) | 9.9 s (search 5.2 s); 13 s in the build |
| `bridgeAll` from the floor | 4,765 (longest jump 57 frames) | 0.4 s |
| `vertAirOK` with `goalVA` | 16 cases | 0.1 s |

`checkC` takes more than a few seconds. It is in its own private file, `Proof/RoomFall.lean`.

## Checked on real frames

Program `room-fall-check FM2 [N]`: the checks, then each frame of the room from the first control, instruction by instruction: the movie, and `N` runs of each of 5 kinds of own input (up to 160 frames; kind 4 holds A for random lengths).

| run | frames | in the air at the start | not `vstepV` at `Q` | falling at `Q` | of them `V` kept | landings (all of the form `land`) | rising at `Q`, `V` changed | `stand_row` fails |
|---|---|---|---|---|---|---|---|---|
| the movie | 111 | 105 | 0 | 72 | 68 | 3 | 0 | 0 |
| own inputs, 5 kinds × 100 runs | 80,000 | 68,767 | 0 | 46,259 | 43,641 | 2,618 | 0 | 0 |

Of the 2,621 landings, 2,595 were on the floor. On every frame in the air, `vstepV` was `vstep` on the machine at the start of the level, and the state at `Q` was 1 or 2. The program also checks `bridgeAll` from the two heights of the block's side and from the block's top (5,537, 6,305 and 7,069 states, 0.5–0.6 s each): true. Lean uses only the floor's.

## Assumptions (not proved in Lean)

* `SiteOK` on each instruction of the room's frames, as [the block map](c-7-12-RoomMap.md).
* Nothing new. `stand_row` is gone.

## What item 1-1-c-7-11 still needs

`varc_all` gives each frame of a jump from the floor, up to the landing. The proof of [Joining the bonus room](c-5-RoomJoin.md) still states the jumps as wholes, in the field `way` (`Approach.reach`, `Over.reach`, `Off.jump.reach`):

* The takeoff frame: that a floor frame with a jump input gives a state of `arcStart` (`vfloor`, assumed), and the same from the side of the block and from the block's top (`Over` from the heights, `Off.jump`). `bridgeAll` is true from those heights in a program, but `OnArc` and Lean use only the floor.
* Which frame lands: `varc_all` says that a landing is `land` of the `vstep` state, but not on which frame he lands. The window of `Approach` (he lands on the block's top) and the frame `F` of `Off` (he reaches the floor) need the collision routine's feet check, on the block map.
* The frames that start at or below the ground falling (`varc_all` asks that he is not there).
* The inputs of the air frames (`air_in`, `Approach.air`).
* The fall from the first control (state 2, no jump) is covered by `vair_of` with `vstepR`, but `RoomJoin` uses the bounds of `vfall` there, which stay assumed: they need `vstep`'s sums for any state 2, not a finite check.

**Files.** `Theorems/RoomFall.lean`, `Theorems/VertAir.lean`, private `Proof/RoomFall.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-fall-check FM2 [N]    # the checks (about 25 s) and real frames, N runs of each of 5 kinds (N = 100: about 1 min)
```
