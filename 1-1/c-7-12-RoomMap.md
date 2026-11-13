[← Back](README.md) | [English](c-7-12-RoomMap.md) | [Japanese](c-7-12-RoomMap-ja.md)

# The block map in the room

**Claim.** This is a partial result. On every frame from the first control in the room to the entry into the side pipe, every bit that is 0 in the map is 0 in the two block buffers. At every read of the block buffer routine on these frames, the side pipe's two tiles are only in the pipe's column. This is `TilesOK` of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md), now proved on the real machines of the run. The proof follows one whole frame in the room with an abstract machine, as [The screen's page in the room, and the long timer of the side pipe](d-2-4-ScreenPage.md) does, with more known bits. It assumes nothing new: `SiteOK` on each instruction and the player's routine on each frame are what that page already assumes, and the state at the first control comes from the rows of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md).

The map is a reference machine: the machine at the first control in the room after the reference entry into the pipe, with no input for 91 frames. It has control. Only the bits that are 0 in it are proved to stay 0. That the bits that are 1 stay (a brick stays a brick), and that the numbers of the other fields of [Joining the bonus room](c-5-RoomJoin.md) (the corner, the goal, the floor, the left wall) are those of the map, are not proved.

`M` is the map. `B` is the set of the 416 bytes of the two block buffers. `rt(m)` is `GameEngineSubroutine`, and `rt_r` is its value on the reference machine of `ScreenPage` (the player's routine). `seq(n)` is the machine when frame `n` begins, and `tr(j)` is the machine `j` instructions into a frame. `T₁`, `T₂`, `AtRead`, `TilesOK` are those of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md). `x & y` and `~x` are bitwise.

```
Zero(m)       :=  ∀ d ∈ B,  m(d) & ~M(d) = 0
Cond(m)       :=  ScreenPage's condition at a frame's start, with the bits of Zero added
```

`Cond(m)` holds of a machine when the frame before ended in the idle loop, the bytes of `ScreenPage` have the bits of its reference machine, the 5 screen's bytes of [one whole frame](c-7-16-SideFrame.md) (the scroll lock, the edges' positions and pages) have its values, and `Zero(m)` holds. Of the 5, only the left edge's position is new: `ScreenPage` knows the other 4.

```
s_eraseT      :  the erase of a coin writes A through a pointer the walk does not know;  A is known,
                 and every byte of B agrees with A on its known bits  →  the abstract state still covers the machine
room_stepT    :  RoomOKT,  Cond(m),  SiteOK on each instruction of frame(m, i)
                 →  (Cond(frame(m, i)) ∨ rt(frame(m, i)) ≠ rt_r)  ∧  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j))
map_run       :  RoomOKT,  seq(n + 1) = frame(seq(n), inp(n)),  Cond(seq(c)),
                 SiteOK on frames c … e − 1,  rt(seq(n)) = rt_r (c ≤ n < e)
                 →  (∀ n ∈ [c, e),  Cond(seq(n)))  ∧  (∀ n ∈ [c, e),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
start_of_rows :  startCheckT,  InRowsT(m),  control(m)  →  Cond(m)
cond_of_rows  :  the hypotheses of map_of_rows  →  ∀ n ∈ [b, a),  RoomCond(seq(n))          (used by the walks of the vertical bytes, c-7-5-1-RoomVert.md)
map_of_rows   :  MapFacts,  startCheckT,  seq(n + 1) = frame(seq(n), inp(n)),  InRowsT(seq(b)),  control(seq(b)),
                 SiteOK on frames b … a − 1,  rt(seq(n)) = rt_r (b ≤ n < a)
                 →  (∀ n ∈ [b, a),  Zero(seq(n)))  ∧  (∀ n ∈ [b, a),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
map_check, map_start (private)  :  mapCheck = true,  startCheckT = true   (native_decide)
room_map (private)              :  map_of_rows with the two checks
```

`InRowsT(m)` says that `m` is a machine of the rows of the time of the change into the room. `Route.Changes` gives it at the first control (`Changes.roomAt` uses the same), with `SiteOK` (`roomSites`) and the player's routine (`roomStay`) on the frames up to the entry `a₂`.

Lean: `Theorems/RoomMap.lean`; private `Proof/RoomMap.lean`. In `Theorems/RoomJoin.lean`: `RoomRun.TilesE`, the tiles at the reads of frame `E`, a hypothesis of `RoomRun.mouth_of` (no longer a field). In `Theorems/Route.lean`: `Run.roomEnter` and `Run.roomTiles`.

```
roomEnter       :  ∃ k,  b₁ ≤ k < a₂  ∧  fm(E − 1) = seq(k)  ∧  pad(E) = inp(k)          (the theorem Route.Run.roomEnter, k = b₁ + (E − 1 − C))
Run.roomTiles   :  the checks,  Run  →  TilesE:  ∀ n j,  WriteStep(n) → j ≤ n → AtRead(tr(j)) → TilesOK(tr(j))
```

`Run.roomTiles` is `map_of_rows` on the frames `b₁ … a₂ − 1` of `Route.Changes` (from the rows of the change into the room, `roomSites`, `roomStay`), at the frame `k` of `roomEnter`.

The same walk gives that each frame of the room starts in control, as the walk of [one whole frame](c-7-16-SideFrame.md) asks. These facts on the entering frame, with the walk of the room from the write to the frame's end, put `P(E)` at the mouth ([the position at the end of the entering frame](c-7-18-2-SideEntryEnd.md), `Run.roomMouthE`); `TilesE`, `StartE`, `CleanE`, `HeadE` stay theorems.

```
startCheckF        :  the reference machine is in the idle loop with the guard's stack pointer, Cond knows the guard's 8 bytes (3 of the game, 5 of the screen)
                      whole and with its values, the program is the same, 9 < the dot where vblank ends
frameStart_of_cond :  startCheckF,  Cond(m)  →  FrameStart(m)          (with the room's guard G_room of one whole frame)
start_of_rowsF     :  the hypotheses of map_of_rows,  startCheckF  →  ∀ n ∈ [b, a),  FrameStart(seq(n))
Run.roomStartE     :  the checks,  Run  →  FrameStart(fm(E − 1))          (StartE; the old field room.startE)
map_startF (private) :  startCheckF = true  (native_decide)
```

The walk also checks, at every state, the conditions of `Clean` ([One whole frame](a-5-2-PipeWrites.md)) that `SiteOK` does not give, with the room's guard `G_room`: its protected bytes include the 5 screen's bytes. A store through an index or a pointer has a known target outside the guard's bytes, or it is the erase of a coin, whose target `SiteOK` puts in the block buffers. At the jump routine the index is known and in its table. `SiteOK` gives the reads through a pointer and the time. So every instruction of every frame of the room is `Clean`, with no new assumption. And at no state is it at either of the two places where the head changes the vertical motion: the routine of the head's collision with a block (`h = headAt`: a brick or a block with an item) and the store of the vertical speed after the head's check (`bumpAt`: a solid block, or in the water, or while a block bounces). The walk cuts both (the guard `G_B`: `G_room` with one more place cut; its conditions of `Clean` are those of `G_room`, `clean_of_GB`). `SiteOK` lets a read for the head give only nothing or a coin, so the walk never comes to either. So no frame of the room changes the vertical motion by the head's collision with a block, and the field `vframes` of [Joining the bonus room](c-5-RoomJoin.md) no longer assumes it (item 1-1-c-7-10).

`bumpAt` is found in the ROM: the collision routine's first store of the vertical speed after its jump to the foot check.

```
cleanS(A)          :=  pc(A) ≥ 0x8000  ∧  (pc(A) = erase  ∨  the store's target is known and Plain)  ∧  (pc(A) = JumpEngine → A known, A < the length of its table)
walk, at each state :  tilesB(A)  ∧  cleanS(A)  ∧  pc(A) ∉ cuts(G_B) = {h, bumpAt}
clean_of_sim       :  CleanFacts,  A covers m,  cleanS(A),  SiteOK(m)  →  Clean(m)
clean_of_rows      :  the hypotheses of map_of_rows  →  ∀ n ∈ [b, a),  ∀ j,  Clean(tr_n(j))
cuts_run           :  the hypotheses of map_run  →  ∀ n ∈ [c, e),  ∀ j,  pc(tr_n(j)) ∉ cuts
head_of_rows       :  the hypotheses of map_of_rows  →  ∀ n ∈ [b, a),  ∀ j,  pc(tr_n(j)) ≠ h
bump_of_rows       :  the hypotheses of map_of_rows  →  ∀ n ∈ [b, a),  ∀ j,  pc(tr_n(j)) ≠ bumpAt
Run.roomCleanE     :  the checks,  Run  →  CleanE                       (the old field room.cleanE)
Run.roomHeadE      :  the checks,  Run  →  HeadE:  ∀ j,  pc(tr(j)) ≠ h    (once part of the field room.edgeE)
Run.roomBump       :  the checks,  Run  →  ∀ n,  C ≤ n < E  →  ∀ j,  pc(tr_n(j)) ≠ h  ∧  pc(tr_n(j)) ≠ bumpAt
                      (the room's frame n + 1 is frame b₁ + (n − C) of base, before a₂ by roomEnter)
Run.inRoom         :  the checks,  Run  →  InRoom:  mouthE ∧ bump          (Run.roomMouthE, Run.roomBump)
```

`CleanFacts` is part of `mapCheck`: the idle loop of the places is the guard's, their last dot is at most the guard's, and no byte of the block buffers is a byte of the guard. With these checks `mapCheck` takes about 4 s in a program (2.6 s before the screen's bytes and the cut were added).

## How it works

**At the first control.** The rows of the change know every one of the 416 bytes of the block buffers, in every state with control. On the TAS these bytes are those of the map. The check `startCheckT` asks that every state with control in the rows of the time is under a start state of `Cond`.

**The walk.** It is the walk of `ScreenPage`, with three changes.

* The erase of a coin (`ErACM`) writes through a pointer that the walk does not know. `ScreenPage` asks that no byte of `B` has a known bit there. Here it asks that `A` is known and agrees with the known bits of every byte of `B` (`bufAgree`). The erase writes 0, and the known bits of `B` are bits that are 0, so this holds.
* At each state at the read of the block buffer routine, the walk checks `tilesB`: every byte of `B` out of the pipe's column is known to be neither tile. A byte is known not to be `T₁` when `T₁` has a 1 at a bit that is known to be 0. For this map every byte out of the column has such bits for both tiles.
* At the frame's end the walk asks `tilesB`, and a start state of `Cond`, or `rt` known and not `rt_r` (the frame left the player's routine).

**Size.** The search takes 209,861 steps with 9,132 forks and no failure. The table has 9,301 states. `mapCheck` takes about 4 s in a program, and `startCheckT` about 2.6 s. The private proof builds in about 10 s.

**Why only the bits that are 0.** The erase writes into some byte of `B` that the walk does not know. A 0 written anywhere keeps every bit that is known to be 0, but not a bit that is known to be 1. To keep each byte exactly, one would need that the erase writes into a byte of a coin.

## On real frames

Program `room-map-check FM2 [N]`. Each frame of the room before it leaves the player's routine is run instruction by instruction.

| run | frames | reads | coins erased |
|---|---|---|---|
| the movie, from the first control to the entry | 111 | 728 | 13 |
| own inputs from the movie's frames in the room, biased to the right (200 runs, up to 300 frames) | 43,441 | 297,928 | 653 |
| own inputs from the first control: random, left with B, right with B, walls (4 × 200 runs, 200 frames) | 160,000 | 1,096,212 | 59 |

* On every frame: the frame starts in `Cond`, and `Zero` holds. At every read: `TilesOK`. No instruction fails `SiteOK`.
* At the movie's first control in the room (after movie frame 653) the block buffers are the map, byte by byte.
* `mapCheck` and `startCheckT` are true. With the second cut place (`bumpAt`) `mapCheck` still takes about 4.4 s; the walk is the same (209,861 steps, table 9,301).
* No frame of the movie's room and of the runs of own inputs of `side-frame-check` comes to `bumpAt` or `h` (see [one whole frame](c-7-16-SideFrame.md)).

## Assumptions (not proved in Lean)

* **`SiteOK`** on each instruction of the frames from the first control to the entry, and the player's routine on each of those frames. These are what [The screen's page in the room, and the long timer of the side pipe](d-2-4-ScreenPage.md) assumes (`Route.Changes.roomSites`; `roomStay` is a theorem).
* **`roomEnter` is a theorem.** Frame `E` of `RoomRun` (`fm(E − 1)`, `pad(E)`) is a frame of `Route.Base` in the room: the room's machines are those of `base` from frame `b₁` on, so it is frame `b₁ + (E − 1 − C)`, and that is before `a₂` (`Route.Run.roomEnter`, item 1-1-0-4). This uses the checks `RoomChecks`. The field `tiles` of `RoomRun` is gone: `Run.roomTiles` proves it from `room_map` and this link.
* **The rest of the map** (item 1-1-c-7-12). Only the bits that are 0 in the map are proved. That bricks, the floor and the wall stay as they are, and that the numbers of the other fields are those of the map, are not proved.

**Files.** `Theorems/RoomMap.lean`, private `Proof/RoomMap.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-map-check FM2 [N]    # the two checks, and real frames: N runs of each kind (N = 200: about 10 min)
```
