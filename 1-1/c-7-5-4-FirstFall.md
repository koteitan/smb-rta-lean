[← Back](README.md) | [English](c-7-5-4-FirstFall.md) | [Japanese](c-7-5-4-FirstFall-ja.md)

# The first fall in the room

**Claim.** At the first control in the room the vertical state is one known state: the rows of the change into the room know it (`InRoom.vstart`). Up to the first stand every frame starts in the air, so it is `vstepR` of the state before, or its landing ([Every frame of a jump in the room](c-7-11-1-RoomFall.md)), and a landing is a stand. So up to the first stand the state `d` frames after first control is a state of the first fall: from the start, `vstepR` with A pressed or not. A finite check on these states proves three fields of item 1-1-c-7-5 of [Joining the bonus room](c-5-RoomJoin.md) on the frames up to the first stand: `fall_long`, `vfall` and `floor_at`. What is left of them is about the frames after a stand, and one state: three smaller fields.

`vs(n)` is the vertical state at the end of the room's frame `n`, `C` the first control, `t₀` the first frame past the block's right end. `st` is the player's state (0 standing, 1 jump, 2 fall). `OnFloor(s)` is `st(s) = 0 ∧ y(s) = y_ground`. `Y = 256·y + fraction`, `W = 256·vy + fraction`, `f` the fall force. `VDrop(s, t)` is `st(t) ≠ 1 ∧ Y(t) ≤ Y(s) + W(s) ∧ W(t) ≤ W(s) + f(s) ∧ f(t) = f(s)`. `land(t)` is `t` with `y := y & F0`, `vy := 0`, the speed's fraction 0, `st := 0`. The numbers of the room: the fall `34` frames, `standF = 51`.

```
L₀ = vStart,   L_{d+1} = { vstepR(s, a) | s ∈ L_d, a ∈ {pressed, not} }

vstart     :  vs(C) ∈ vStart                                                         (RoomPair.rowsCheck, Route.Run.roomV0)
fallCheck  :  0 < 34 < 51,   P₁ + 16·v_top·51 < goalP,
              ∀ d < 51, ∀ s ∈ L_d:  st(s) = 2,  and for both a, with t = vstepR(s, a):
                 st(t) = 2,   VDrop(s, t),   falling(t) → VDrop(s, land(t)),
                 d + 1 < 34 → falling(t) → y(land(t)) ≠ y_ground,
                 d + 1 = 34 → falling(t) ∧ y(land(t)) = y_ground
t0_far     :  C + 51 < t₀
fall_mem   :  d < 51,   ∀ j ∈ (C, C + d]: st(vs(j)) ≠ 0   →   vs(C + d) ∈ L_d
fall_next  :  the same   →   vs(C + d + 1) = t  ∨  (falling(t) ∧ vs(C + d + 1) = land(t)),     t = vstepR(vs(C + d), a(C + d + 1))
vfall_first:  C ≤ n,  n + 1 < C + 51,  ∀ j ∈ (C, n]: st(vs(j)) ≠ 0   →   VDrop(vs(n), vs(n + 1))
fall_first :  C ≤ n < C + 34,  ∀ j ∈ (C, n): st(vs(j)) ≠ 0   →   ¬OnFloor(vs(n))
fall_long_of: C ≤ n < C + 34   →   ¬OnFloor(vs(n))                                           (now from the frames with no jump, and fall_any of item 1-1-c-7-5-6)
vfall_of   :  C ≤ n,  n + 1 < C + 51,  st(vs(n)) ≠ 1,  no jump on frames C + 1 … n + 1   →   VDrop(vs(n), vs(n + 1))   (now from the frames with no jump)
floor_at_of:  NoWall   →   OnFloor(vs(C + 34))                                               (with stand_wall, land_at_of)
```

`P₁` is the right end of the start position, `v_top` the top speed, `goalP` the block's right end. `t0_far` says that the frames up to `C + 51` are before `t₀`, where the room's walks speak of every frame.

## The fields

Removed from `RoomRun` (now fields of `RoomCore`, proved by `RoomRun.toCore`):

* `fall_long`: he is not on the floor before `C + 34`.
* `vfall`: before `C + 51`, a frame with no jump, not in a jump state, is `VDrop`.
* `floor_at`: with no wall hit he is on the floor at `C + 34`.

New in `RoomRun` (each is implied by the old field it replaces):

```
fall_stand :  C < i < n < C + 34,  st(vs(i)) = 0,  ¬OnFloor(vs(i))   →   ¬OnFloor(vs(n))
vfall_stand:  C < i ≤ n,  n + 1 < C + 51,  st(vs(i)) = 0,  st(vs(n)) ≠ 1,  jump(n + 1) = false   →   VDrop(vs(n), vs(n + 1))
land_at    :  NoWall   →   st(vs(C + 34)) = 0
```

* `fall_stand` is `fall_long` after a stand away from the floor, that is, after he stood on the left wall.
* `vfall_stand` is `vfall` from the first stand on.
* `land_at` is `floor_at` without the height: the first fall gives the floor's height at `C + 34`; that he stands there is the collision routine's feet check. Since item 1-1-c-7-5-12 ([The landing frame of the first fall](c-7-5-12-RoomLand.md)) `land_at` is the theorem `land_at_of`; the field `landQ` in its place asked two bytes at the end of that frame's move, and item 1-1-c-7-5-13 ([The collision-disable flag and the vertical page in the first fall](c-7-5-13-LandBytes.md)) proves them.

Since item 1-1-c-7-5-5 ([Frames that start standing in the room](c-7-5-5-RoomStand.md)) `vfall_stand` is gone and `fall_stand` is the smaller field `fall_jump`: a walk of the frames that start standing makes the states with no jump a finite set again. Since item 1-1-c-7-5-6 ([A jump from a stand during the fall in the room](c-7-5-6-RoomJump.md)) `fall_jump` is a theorem, with `stand_wall` and `wall`. `vfall` is now asked only with no jump since first control.

New in `InRoom`: `vstart` (proved, `Route.Run.roomV0`). New in `Checks`: `first` (the check `fallCheck`). New in `Nums`: `vStart`, the vertical states at first control.

## How

**The start.** The rows of the change into the room ([`RoomPair.rowsCheck`](c-7-5-2-RoomPair.md)) now also ask, on each state with control, that the 9 bytes that `vsOf` reads are known and that the state is in `vStart` (`rowV`, `v_of_rows`). The generator makes `vStart` by running the change from the vertical pipe's entry with no input up to control (`roomV0Of` in `Main.lean`). The check reads the rows that `rowsCheck` made already for the other two facts, so it costs no second pass over the rows.

**The layers.** `fallLayer d` lists the states of `L_d` (`fallNext` with `eraseDups`). The check `fallRun` walks the layers once, `d = 0, …, 50`. In state 2 the routine does not read A, and A only goes into A of the frame before; so each layer has 1 or 2 states (A pressed or not).

| frame `d` | height | speed (px per frame) | note |
|---|---|---|---|
| 0 | 48.41 px | 2.34 | first control |
| 14 | 95.44 px | 4.00 | the cap of the speed first applies; from here the speed goes 4.00, 4.16, 4.31, 4.47, then 4.00 again |
| 33 | 175.66 px | 4.47 | a landing here is on the row above the floor |
| 34 | 180.13 px | 4.00 | a landing here is on the floor |
| 50 | 247.88 px | 4.00 | the last layer |

**Up to the first stand.** `fall_mem` is an induction on `d`: the frame starts in the state 2, so `vair_of` gives `vstepR` or its landing; a landing has `st = 0`, which is a stand, so it is `vstepR` and in the next layer. `vfall_first` and `fall_first` read the check on the state and its next frame.

**After a stand.** `fall_long_of` takes the first stand `j` before `n` (`first_of`). If there is none, `fall_first`. If there is one, `fall_first` says that it is not on the floor, and `fall_stand` gives `n`. `vfall_of` is `vfall_first` or `vfall_stand`, by whether there is a stand at or before `n`. `floor_at_of`: with no wall a stand before `C + 34` would be the first stand, not on the floor (`fall_first`), so the frame before it does not follow `hstep` (`stand_wall`); with no wall that frame follows `hstep`. So frame `C + 34` is `vstepR` of the first fall or its landing; `land_at` says that he stands, so it is the landing, on the floor's height.

**`t0_far`.** Each frame moves him at most the top speed (`move_top_of`), from at most `P₁` (`start_P`). The check asks `P₁ + 16·v_top·51 < goalP`: the block's right end is 59 frames of the top speed away.

| check on the ROM | states | time in a program |
|---|---|---|
| `fallCheck` | 51 layers, 101 states | 0.06 s |
| `rowsCheck` with `rowV` | the rows of the time (14,224 states with control) | 29.5 s (the rows were already made for `rowsCheck`) |

## Checked on real frames

Program `room-first-fall-check FM2 [N]`: the two checks, then from the movie's first control in the room, the movie and `N` runs of each of 7 kinds of own input (up to 60 frames). Kinds 5 and 6 go to the left wall: some frames of any input, then Left with B, with A now and then.

| run | runs | a stand before `C + 34` (all away from the floor) | a jump from it before `C + 34` | first stand at `C + 34` | frames from the first stand on with no jump | failures |
|---|---|---|---|---|---|---|
| the movie | 1 | 0 | 0 | 1 | 0 | 0 |
| own inputs, 7 kinds × 300 | 2,100 | 46 | 13 | 2,054 | 7,493 | 0 |

"Failures" counts each of: a frame before the first stand not in its layer; a frame before the first stand not `VDrop`; `fall_stand`, `vfall_stand`, and `land_at` in a stronger form (no stand before `C + 34`, in place of no wall: then he stands on the floor at `C + 34`); and the three old fields. All were 0. The vertical state at first control of the movie is the one of `vStart`. The earliest stand was at `C + 18`.

## Assumptions (not proved in Lean)

* `landQ` (once `land_at`) is gone: its two bytes at the end of the move of `C + 34` are proved (1-1-c-7-5-13). `fall_jump` (once `fall_stand`) is a theorem since item 1-1-c-7-5-6, which uses the fields `stand_wall` and `wall`.
* `SiteOK` on each instruction of the room's frames, as for [the block map](c-7-12-RoomMap.md) (through `vair_of`).

## What is still needed

* The frames after a stand on the wall: done for the runs with no jump in [Frames that start standing in the room](c-7-5-5-RoomStand.md). The jumps from the wall are done in [A jump from a stand during the fall in the room](c-7-5-6-RoomJump.md).

**Files.** `Theorems/RoomJoin.lean` (`fallNext`, `fallLayer`, `vdropB`, `fallStep`, `fallOk`, `fallRun`, `fallCheck`, `fall_ok`, `fallStep_spec`, `first_of`, `RoomRun.vs_start`, `t0_far`, `fall_mem`, `fall_next`, `vfall_first`, `fall_first`, `fall_long_of`, `vfall_of`, `floor_at_of`), `Theorems/RoomPair.lean` (`vsBytes`, `rowV`, `rowsCheck`, `of_invL`, `v_of_state`, `v_of_rows`), `Theorems/Route.lean` (`Run.roomV0`, `Run.inRoom`); private `Proof/RoomJoin.lean` (`room_checks.first`), `Proof/RoomVert.lean` (`room_pair_rows`).

**Reproduce.**
```
.lake/build/bin/smbrta room-first-fall-check FM2 [N]    # the checks (about 30 s) and real frames, N runs of each of 7 kinds (N = 300: about 1.7 min)
```
