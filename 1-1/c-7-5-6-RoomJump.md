[← Back](README.md) | [English](c-7-5-6-RoomJump.md) | [Japanese](c-7-5-6-RoomJump-ja.md)

# A jump from a stand during the fall in the room

**Claim.** A frame of the bonus room that comes to the player's routine standing with a new press of A ends on the takeoff of its height and of the stored speed that it reads. So from the first stand on, the vertical states with any input are a finite set. With the first stand at frame `C + 15` or later, no state of this set is on the floor before `C + 34`. So the field `fall_jump` of [Joining the bonus room](c-5-RoomJoin.md) is a theorem (item 1-1-c-7-5). The proof uses the fields `stand_wall` and `wall`, which are still assumed: they put the first stand away from the floor at frame `C + 15` or later. Without them the claim is false for the vertical bytes alone (measured, below).

The notation is that of [Frames that start standing in the room](c-7-5-5-RoomStand.md). `Q` is the scroll handler, `ab(x)` the stored speed (`Player_XSpeedAbsolute`), `A(x)` bit 7 of the joypad's bits, `A'(x)` bit 7 of A of the frame before. `vstepV` is `vstep` on the machine of the player's routine. `layer(d)` is the set of the states of the first fall `d` frames after first control ([The first fall in the room](c-7-5-4-FirstFall.md)).

```
flat(y)        =  the vertical state standing at the height y: the other vertical bytes 0, A not pressed on the frame before
jumpOff(y, s)  =  vstepV(flat(y), A pressed, stored speed s)
vert_jump      :  AtV(x),  st(x) = 0,  A(x) = 1,  A'(x) = 0
                  →  ∃ k ≤ moveLen:  pc(x_k) = Q,  vs(x_k) = jumpOff(y(x), ab(x)),  st(x_k) = 1,  vy(x_k) < 0
jump_frame     :  RoomCond(M),  SiteOK,  AtV(tr(k)),  jump(readIn(tr(k))) = true,  rt(end) = rt_room   →   vs(end) = jumpOff(y(M), ab(tr(k)))
vjump_of       :  C ≤ n < t₀,  n + 1 < E,  jump(n + 1) = true   →   ∃ s,  vs(n + 1) = jumpOff(y(vs(n)), s)
stand_late     :  C ≤ n,  n + 1 < C + 34,  st(vs(n + 1)) = 0,  ¬OnFloor(vs(n + 1))   →   C + 15 ≤ n + 1          (from stand_wall, wall, wall_far)

anyNext(s)     =  next(s)  ∪  { jumpOff(y(s), v)  |  v = 0, …, 255 }      if st(s) = 0                  (next: the page of RoomStand)
               =  next(s)                                                 otherwise
anyOk(s)       =  ¬OnFloor(s)  ∧  (st(s) = 0  →  y(s) & 0F = 0)
lands(L)       =  { land(vstepR(s, a))  |  s ∈ L,  a,  falling(vstepR(s, a)) }
anyCheck       :  frame by frame d = 0, …, 33, from no state:  each state first seen at d meets anyOk;
                  its states of anyNext, and lands(layer(d)) if 15 ≤ d + 1, not yet seen, are the states first seen at d + 1
any_ok         :  15 ≤ d',  q(d') ∈ lands(layer(d' − 1)),  ∀ j ∈ [d', n): q(j + 1) ∈ anyNext(q(j)),  n < 34   →   anyOk(q(n))
any_next       :  C ≤ n,  n + 1 < C + 34,  anyOk(vs(n))   →   vs(n + 1) ∈ anyNext(vs(n))
fall_any       :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))
fall_long_of   :  C ≤ n < C + 34   →   ¬OnFloor(vs(n))          (with no jump: fall_nojump, which uses neither field;  else fall_any)
```

## The fields

Removed from `RoomRun`:

* `fall_jump`: after a jump input on a frame from `C` on, he is not on the floor before `C + 34`. Now `fall_any` proves it for every input.

Nothing is added to `RoomRun`. New in `InRoom`: `jump` (proved, `Route.Run.roomJump`). New in `Checks`: `anyin` (the check `anyCheck`). New in `RoomPair.RoomWalks`: `jump` (the check `VertJump.jumpOK`).

`fall_any` uses two fields that stay assumed:

* `stand_wall`: he stands away from the floor only at the end of a frame that does not follow `hstep`.
* `wall`: a frame before `C + 37` that does not follow `hstep` is stopped by the left wall.

`stand_late`: a stand away from the floor at the end of frame `n + 1` makes frame `n + 1` a frame that does not follow `hstep`; the first such frame is at the left wall; the wall is too far from the start for 13 frames (`wall_far`, with the bound on the distance to the left, `left_dist_le`). So `C + 15 ≤ n + 1`.

## How

**The takeoff (`VertJump`).** On a frame that starts standing with a new press of A, the movement routine starts a jump. It writes the height's fraction, the vertical speed and its fraction, the two forces, the jump's origin and the state before it reads them. So the walk of two machines of [the vertical model](../0-0/0-3-2-FrameModel.md) goes through with these six bytes not known on the real machine and 0 on the machine of `vstep` (`vTagsJ`). The height and the stored speed are the same on both. At the routine's return the walk knows that the state is 1 and the vertical speed negative (`goalVJ`). The result `jumpOff(y, s)` depends only on the height and the stored speed. On this ROM a height has 3 takeoffs for the 256 stored speeds.

**The frame (`RoomJump`).** No new walk of the room's frames: the walk to the player's routine (`RoomVert.before_R`) keeps the vertical bytes from the frame's start; `vert_jump` gives the bytes at `Q`, in a jump and rising; the walk from `Q` (`RoomVert.after_Q`) keeps them to the frame's end.

**The states with any input (`anyCheck`).** It is the check of the frames with no jump, with the takeoffs added at a stand. The takeoffs of the 16 whole rows are computed once (`offTable`: 16 × 256 calls of `vstep`); a stand of the set is on a whole row (`anyOk`). The set starts empty. At each frame from 15 on it takes the landings of the first fall's layer: the first stand is the landing of a state of the first fall (`fall_mem`, `fall_next`), and it is at frame `C + 15` or later (`stand_late`). `ajRun_sound` is the induction of `njRun_sound`, with a start at any frame.

**Why the vertical bytes alone are not enough.** The walks of the room's frames give a landing at any height when he falls: they do not know where the blocks are. From the vertical state at first control alone, with a landing allowed on any frame:

| first stand allowed from frame | states by frame 33 | first frame with a state on the floor | time in a program |
|---|---|---|---|
| 1 | 55,806 | 31 | 8.4 s |
| 2 | 51,703 | 32 | 9.4 s |
| 4 | 44,855 | 34 | 11.5 s |
| 8 | 22,165 | 34 | 4.8 s |
| 12 | 10,487 | 34 | 2.4 s |
| 15 (`wallF`) | 5,159 (heights 17 to 160) | 34 | 1.6 s |

With a stand at frame 1 the set holds a path to the floor at frame 31: a landing at frame 1 (no block is there), a jump with A held that takes the height's byte above the top of the screen and around, a landing below the floor's row, a second jump. So `fall_jump` needs that the first stand is not too early, and that is a fact about the left wall: `stand_wall` and `wall`.

| check on the ROM | size | time |
|---|---|---|
| `jumpOK` (2 cases of the walk of two machines) | | 1 ms |
| `anyCheck` | 5,159 states, 4,096 takeoffs computed | 2.4 s in a program; it is in `Proof/RoomJoin.lean` |

## Checked on real frames

Program `room-jump-check FM2 [N]`: the checks, the set, then from the movie's first control in the room the movie and `N` runs of each of 11 kinds of own input (up to 80 frames). Kinds 9 and 10 go to the left wall and press A newly on each frame that starts standing away from the floor.

| run | frames | frames with a jump at the player's routine | of them not `jumpOff(y, ab)` | jumps before 34 from a stand away from the floor | runs with a stand away from the floor before 34 | runs with the first stand before 15 | frames before 51 | of them not in the set by their frame | on the floor before 34 |
|---|---|---|---|---|---|---|---|---|---|
| the movie | 111 | 3 | 0 | 0 | 0 | 0 | 51 | 0 | 0 |
| own inputs, 11 kinds × 300 | 264,000 | 5,823 | 0 | 49 | 89 | 0 | 168,300 | 0 | 0 |

"In the set by their frame": before the first stand the state is in the first fall's layer of its frame; from the first stand on it is in the set of `anyCheck`, first seen at its frame or earlier. Of the 5,826 jumps, 790 read a stored speed that is not `|v|`.

## Assumptions (not proved in Lean)

* `stand_wall`, `wall` (above): `fall_any` uses them. They were fields before.
* `read_stop`, `land_at` (unchanged).
* `SiteOK` on each instruction of the room's frames, as for [the block map](c-7-12-RoomMap.md).

**Files.** `Theorems/VertJump.lean` (`flat`, `jumpOff`, `vTagsJ`, `goalVJ`, `caseOKJ`, `jumpOK`, `vert_jump`), `Theorems/RoomJump.lean` (`press_of`, `jump_frame`, `jump_room`), `Theorems/RoomJoin.lean` (`jumpOffR`, `jumpOffs`, `offRow`, `offTable`, `anyNext`, `anyOk`, `fallLands`, `ajRun`, `anyCheck`, `ajRun_sound`, `any_ok`, `InRoom.jump`, `RoomRun.stand_late`, `vjump_of`, `any_next`, `any_chain`, `fall_any`, `fall_long_of`), `Theorems/RoomPair.lean` (`RoomWalks.jump`), `Theorems/Route.lean` (`Run.roomJump`, `Run.inRoom`); private `Proof/RoomVert.lean` (`room_vert_jump`), `Proof/RoomJoin.lean` (`room_checks.anyin`).

**Reproduce.**
```
.lake/build/bin/smbrta room-jump-check FM2 [N [K]]    # the checks, the set with the first stand from frame K (15), real frames: N runs of each of 11 kinds (N = 300: about 2.5 min)
```
