[← Back](README.md) | [English](c-7-5-5-RoomStand.md) | [Japanese](c-7-5-5-RoomStand-ja.md)

# Frames that start standing in the room

**Claim.** A frame of the bonus room that starts standing (the state 0) with no new press of A does not jump. The height's fraction, the two forces and the jump's origin stay. The height, the vertical speed and its fraction stay, and the state at the end is 0 or 2 (he stands, or he falls off); or he lands. So with no jump since first control the vertical states are again a finite set, from the states at first control. A check on this set proves the field `vfall_stand` and the part of `fall_stand` with no jump (item 1-1-c-7-5 of [Joining the bonus room](c-5-RoomJoin.md)). What stayed was the field `fall_jump`: after a jump from the wall he is not on the floor before `C + 34`. Item 1-1-c-7-5-6 ([A jump from a stand during the fall in the room](c-7-5-6-RoomJump.md)) now proves it, with the fields `stand_wall` and `wall`. The input of every frame is now read from the machine at the player's routine (the new field `read_stop` on the frames that do not follow the model), and with it the field `air_in` is proved too.

The notation is that of [The first fall in the room](c-7-5-4-FirstFall.md). `R` is the player's routine, `tr(j)` the machine `j` instructions into the frame, `end` the machine at the frame's end, `rt` the routine byte, `SC` the side check (`DoPlayerSideCheck`), `yhigh` the vertical page. `V_S` are the height's fraction, the two forces and the jump's origin; `V_3` are the height `y`, the vertical speed `vy` and its fraction `mf`. `A(x)` is bit 7 of the joypad's bits, `A'(x)` bit 7 of A of the frame before. `jump(n)` is the jump bit of the input of frame `n` (`Frames.inp`); `readIn` is the input that the model reads at `R`.

```
StandAt(x)    :  st(x) = 0  ∧  (A(x) = 0  ∨  A'(x) = 1)
StandNext(s, t):  V_S(t) = V_S(s)  ∧  ( (V_3(t) = V_3(s)  ∧  st(t) ∈ {0, 2})  ∨  (st(t) = 0 ∧ vy(t) = 0 ∧ mf(t) = 0 ∧ y(t) = y(s) & F0) )

after_RS      :  RoomCond(M),  SiteOK on each instruction
                 →  pc(tr(j)) = R  for at most one j of the frame,
                    and  pc(tr(j)) = R,  StandAt(tr(j)),  rt(end) = rt_room  →
                      V_S(end) = V_S(tr(j))  ∧  yhigh(end) = yhigh(tr(j))  ∧
                      ( (V_3(end) = V_3(tr(j)) ∧ st(end) ∈ {0, 2} ∧ (∀ i ≥ j,  pc(tr(i)) = SC  →  st(tr(i)) ≠ 0))
                        ∨  (st(end) = 0 ∧ vy(end) = 0 ∧ mf(end) = 0 ∧ y(end) = y(tr(j)) & F0) )
stand_frame   :  RoomCond(M),  SiteOK,  pc(tr(k)) = R,  st(M) = 0,  jump(readIn(tr(k))) = false,  rt(end) = rt_room   →   StandNext(vs(M), vs(end))
vstand_of     :  C ≤ n < t₀,  n + 1 < E,  st(vs(n)) = 0,  jump(n + 1) = false   →   StandNext(vs(n), vs(n + 1))
StandNext.vdrop:  StandNext(s, t)  →  VDrop(s, t)

next(s)       =  { s with st := c, A := a  |  c ∈ {0, 2}, a }  ∪  { land(s) with A := a  |  a }                          if st(s) = 0
              =  { vstepR(s, a)  |  a }  ∪  { land(vstepR(s, a))  |  a,  falling(vstepR(s, a)) }                         otherwise
ok(s)         =  st(s) = 0  ∨  ( st(s) = 2  ∧  ∀ a,  t = vstepR(s, a):  st(t) = 2,  VDrop(s, t),  falling(t) → VDrop(s, land(t)) )
noJumpCheck   :  from vStart, frame by frame d = 0, …, 49:  each state first seen at d meets ok, and is not on the floor if d < 34;
                 its next states not yet seen are the states first seen at d + 1
noJump_ok     :  q(0) ∈ vStart,  ∀ j < n: q(j + 1) ∈ next(q(j)),  n + 1 < 51   →   ok(q(n))  ∧  (n < 34 → ¬OnFloor(q(n)))
nj_next       :  d + 1 < 51,  jump(C + d + 1) = false   →   vs(C + d + 1) ∈ next(vs(C + d))
vfall_of      :  C ≤ n,  n + 1 < C + 51,  st(vs(n)) ≠ 1,  ∀ j ∈ [C, n]: jump(j + 1) = false   →   VDrop(vs(n), vs(n + 1))
fall_nojump   :  C ≤ n < C + 34,  ∀ j ∈ [C, n): jump(j + 1) = false   →   ¬OnFloor(vs(n))
fall_long_of  :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))                                    (fall_nojump; after a jump fall_any, item 1-1-c-7-5-6)
```

## The fields

Removed from `RoomRun`:

* `vfall_stand`: after a stand, a frame with no jump from a state not in a jump is `VDrop`. Now `vfall_of` proves `vfall` with no jump since first control.
* `fall_stand`: after a stand away from the floor he is not on the floor before `C + 34`. Now `fall_nojump` proves it with no jump since first control; with a jump the smaller field `fall_jump` stays.

New in `RoomRun`:

```
fall_jump  :  C ≤ j < n < C + 34,  jump(j + 1) = true   →   ¬OnFloor(vs(n))
read_stop  :  C ≤ n < t₀,  ¬CleanR(frame n + 1)   →   inp(n + 1) = readIn(tr(arr(n)))
```

* `fall_jump` is `fall_stand` on the runs with a jump input before `n`. A jump input comes only on a frame that starts standing (`air_in`), and the first stand is not on the floor (`fall_first`), so `fall_stand` gives it.
* `read_stop` says that the input of a frame that does not follow the model (a side stops him) is the input read from the machine at its first arrival at `R`. `read_in` reads the input so on the frames that follow the model; `read_inp` puts the two together. The input is a field of `Frames`: before, the frames that a side stops had an input that nothing tied to the machine.

Removed from `RoomFields` (now a field of `RoomCore`, proved by `RoomRun.toCore`):

* `air_in`: a frame before `C + 51` that starts in the air has an air input (the state 1, no jump). `air_in_of`: the input is read from the machine (`read_inp`); at `R` the player's state is that of the frame's start (`InRoom.stR`, from `RoomVert.st_at_R`), so not 0, and `readIn` gives no jump; every input read from a machine is one of `inputs` (`readIn_mem`).

Changed: `RoomCore.vfall` now asks no jump on the frames `C + 1, …, n + 1` (it asked no jump on frame `n + 1`). Its only use, `drop_run`, has this: it is used on the first fall and from the first stand on, and the frames before the first stand are in the air, with no jump (`air_in`).

New in `InRoom`: `stand` (proved, `Route.Run.roomStand`) and `stR` (proved, `Route.Run.roomStR`). New in `Checks`: `nojump` (the check `noJumpCheck`). New in `RoomPair.RoomWalks`: `stand` (the checks of the walk, `RoomStand.SChecks`).

## How

**A fourth walk of one whole frame (`walkS`).** It is the walk of [the block map](c-7-12-RoomMap.md), through the frame of [RoomVert](c-7-5-1-RoomVert.md) (`walkV`, `frame_of_walkV`). At `R` a state is split by the player's state and, in the state 0, by `A` and `A'`. A state standing with no new press gets the bit, and the list `[7, 1]` (`A = 0`) or `[7, 2]` (`A = A' = 1`). The other states at `R` are marked `[2]`. Then:

| list | meaning |
|---|---|
| `[7, 1]`, `[7, 2]` | standing at `R` with no new press; `V_S` and `V_3` not written; the state may be. At the scroll handler `Q` both become `[7, 7]` |
| `[5, h]` | the same, and the high four bits of `y` are `h` (split at the landing's `AND` with `y`) |
| `[1, h, 0]` | `V_3` written since |
| `[6]` | landed: the state, `vy`, `mf` known 0, `y` known `h`; then `y` forgotten; no byte of the landing written since |
| `[4, 4, 4]` | a step that the list does not allow may have written a byte (the bit is dropped) |

At the frame's end (`finS`) a state marked `[4, 4, 4]` or `[1, h, 0]` must be out of the room's routine; a state marked `[7, _]` or `[5, h]` must know the state 0 or 2, or be out of the room's routine. The collision routine stores the state 2 before the foot check; the lists `[7, _]` and `[5, h]` allow that store. `after_RS` reads the walk with one fact outside the abstract states, as `RoomFall.after_QC` does.

Item 1-1-c-7-5-14 added two things to the walk standing: it keeps the vertical page `yhigh` too (`vRestS`), and a state marked `[7, _]` or `[5, h]` must not allow the state 0 at the side check `SC` (`sideOK`). So in the first case of `after_RS` no step from `R` on comes to the side check in the state 0. [The floor frames after the fall](c-7-5-14-FloorFrames.md) uses this: a frame that does come there in the state 0 has landed.

The first try marked both pieces `[7, 7]` at `R`. The search joined them, so the abstract machine no longer knew `A` and `A'` at the jump's check, and the jump's start wrote the height's fraction (6 ends failed). Two lists up to `Q` keep them apart.

**The frame.** `stand_frame`: the walk to `R` (`RoomVert.before_R`) keeps the vertical bytes from the frame's start to `R`; there `jump(readIn) = false` and the state 0 give `StandAt` (`nopress_of`); `after_RS` from there to the end. `Route.Run.roomStand` gives it on the room's frames of `base`, as `Run.roomAir` (`InRoom.stand`).

**The frames with no jump.** With no jump on frame `n + 1`, the frame goes to a state of `next(vs(n))`: standing by `vstand_of` (with `jump_read`, from `read_inp`), in the air by `vair_of` (`nj_next`). The check `njRun` goes frame by frame: the states first seen at frame `d` meet `ok` and the floor's condition, and their next states not yet seen (a hash set) are the states first seen at `d + 1`. Each `vstepR` is computed once (`njStep`). `njRun_sound` proves by induction on the frames: every state seen by frame `d` is first seen now, or done (it meets `ok` and the floor's condition, and its next states are in the set). So every sequence from `vStart` through `next` meets `ok` at each frame (`noJump_ok`). A first form listed all states with their first frame and then checked them with lookups: 15.8 s, since each `vstepR` was computed three times.

| check on the ROM | states | time in a program |
|---|---|---|
| `checkS` (`walkS`) | search 86,809 (table 24,307) | 8.1 s (search 4.7 s) |
| `apartS` | 3 bytes apart, and `apartC` | 0 s |
| `noJumpCheck` | 14,775 states (14,087 in the state 2); first seen at frames 0, 10, 20, 30, 40, 50: 1, 70, 198, 344, 510, 682 | 2.6 s |

`checkS` takes more than a few seconds. It is in its own private file, `Proof/RoomStand.lean`.

## Checked on real frames

Program `room-stand-check FM2 [N]`: the checks, then from the movie's first control in the room, the movie and `N` runs of each of 7 kinds of own input (up to 80 frames; kinds 5 and 6 go to the left wall). The jump bit of a frame is that of `readIn` at its first arrival at `R`.

| run | frames | start standing | of them no jump, ending in the room | not `StandNext` | falls off (state 2 at the end) | frames with no jump since first control (before 51) | not in the set by their frame | not `VDrop` | on the floor before 34 with no jump | runs with a jump before 34 | of them on the floor before 34 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| the movie | 111 | 6 | 3 | 0 | 0 | 35 | 0 | 0 | 0 | 0 | 0 |
| own inputs, 7 kinds × 300 | 168,000 | 18,296 | 14,061 | 0 | 49 | 80,817 | 0 | 0 | 0 | 9 | 0 |

With the input read at `R` on every frame (`read_stop`), the other fields that speak of the input still hold:

| run | frames before 34 in the air or with a jump | of them the facing direction changed (`facing`) | frames before 51 that start in the air | of them not an air input (`air_in`) |
|---|---|---|---|---|
| the movie | 34 | 0 | 50 | 0 |
| own inputs, 7 kinds × 300 | 71,353 | 0 | 98,232 | 0 |

## Assumptions (not proved in Lean)

* `fall_jump` (above) was assumed here: only the runs with a jump input before `C + 34`. It is a theorem since item 1-1-c-7-5-6.
* `read_stop` (above): a read of the input, on the frames that do not follow the model.
* `land_at` (unchanged): with no wall he stands at `C + 34`.
* `SiteOK` on each instruction of the room's frames, as for [the block map](c-7-12-RoomMap.md).

## What is still needed

* `fall_jump`: done in item 1-1-c-7-5-6. The takeoff depends only on the height and the stored speed (3 takeoffs for a height on this ROM), and no new walk of the room was needed. But the vertical bytes alone do not give it: the set from first control reaches the floor at frame 31. It needs that the first stand is at frame `C + 15` or later, from `stand_wall` and `wall`.
* `land_at`: which frame lands needs the collision routine's feet check on the block map.

**Files.** `Theorems/RoomStand.lean` (`vRestS`, `vLand3`, `StandAt`, `standP0`, `standP1`, `newP`, `piecesS`, `phS`, `outR`, `finS`, `checkS`, `piecesS_class`, `piecesS_cover`, `apartS`, `after_RS`, `nopress_of`, `stand_frame`, `SChecks`, `stand_room`), `Theorems/RoomJoin.lean` (`StandNext`, `StandNext.vdrop`, `noJumpNext`, `noJumpOk`, `njStep`, `njAdd`, `njRun`, `noJumpCheck`, `njStep_eq`, `njAdd_spec`, `NjDone`, `njRun_sound`, `noJump_ok`, `mem_noJumpNext_air`, `mem_noJumpNext_stand`, `joyOf_mem`, `readIn_mem`, `InRoom.stand`, `InRoom.stR`, `RoomRun.read_inp`, `jump_read`, `air_in_of`, `vstand_of`, `nj_next`, `nj_ok`, `vfall_of`, `fall_nojump`, `fall_long_of`, `drop_run`), `Theorems/RoomVert.lean` (`st_at_R`), `Theorems/RoomPair.lean` (`RoomWalks.stand`), `Theorems/Route.lean` (`Run.roomStand`, `Run.roomStR`, `Run.inRoom`); private `Proof/RoomStand.lean` (`room_stand`), `Proof/RoomJoin.lean` (`room_checks.nojump`).

**Reproduce.**
```
.lake/build/bin/smbrta room-stand-check FM2 [N]    # the checks (about 15 s) and real frames, N runs of each of 7 kinds (N = 300: about 1.5 min)
```
