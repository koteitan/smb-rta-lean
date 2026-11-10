[← Back](README.md) | [English](c-7-12-RoomMap.md) | [Japanese](c-7-12-RoomMap-ja.md)

# The block map in the room

**Claim.** This is a partial result. On every frame from the first control in the room to the entry into the side pipe, every bit that is 0 in the map is 0 in the two block buffers. At every read of the block buffer routine on these frames, the side pipe's two tiles are only in the pipe's column. This is `TilesOK` of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md), now proved on the real machines of the run. The proof follows one whole frame in the room with an abstract machine, as [The screen's page in the room, and the long timer of the side pipe](d-2-4-ScreenPage.md) does, with more known bits. It assumes nothing new: `SiteOK` on each instruction and the player's routine on each frame are what that page already assumes, and the state at the first control comes from the rows of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md).

The map is a reference machine: the machine at the first control in the room after the reference entry into the pipe, with no input for 91 frames. It has control. Only the bits that are 0 in it are proved to stay 0. That the bits that are 1 stay (a brick stays a brick), and that the numbers of the other fields of [Joining the bonus room](c-5-RoomJoin.md) (the corner, the goal, the floor, the left wall) are those of the map, are not proved.

`M` is the map. `B` is the set of the 416 bytes of the two block buffers. `rt(m)` is `GameEngineSubroutine`, and `rt_r` is its value on the reference machine of `ScreenPage` (the player's routine). `seq(n)` is the machine when frame `n` begins, and `tr(j)` is the machine `j` instructions into a frame. `T₁`, `T₂`, `AtRead`, `TilesOK` are those of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md). `x & y` and `~x` are bitwise.

```
Zero(m)       :=  ∀ d ∈ B,  m(d) & ~M(d) = 0
Cond(m)       :=  ScreenPage's condition at a frame's start, with the bits of Zero added
```

`Cond(m)` holds of a machine when the frame before ended in the idle loop, the bytes of `ScreenPage` have the bits of its reference machine, and `Zero(m)` holds.

```
s_eraseT      :  the erase of a coin writes A through a pointer the walk does not know;  A is known,
                 and every byte of B agrees with A on its known bits  →  the abstract state still covers the machine
room_stepT    :  RoomOKT,  Cond(m),  SiteOK on each instruction of frame(m, i)
                 →  (Cond(frame(m, i)) ∨ rt(frame(m, i)) ≠ rt_r)  ∧  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j))
map_run       :  RoomOKT,  seq(n + 1) = frame(seq(n), inp(n)),  Cond(seq(c)),
                 SiteOK on frames c … e − 1,  rt(seq(n)) = rt_r (c ≤ n < e)
                 →  (∀ n ∈ [c, e),  Cond(seq(n)))  ∧  (∀ n ∈ [c, e),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
start_of_rows :  startCheckT,  InRowsT(m),  control(m)  →  Cond(m)
map_of_rows   :  MapFacts,  startCheckT,  seq(n + 1) = frame(seq(n), inp(n)),  InRowsT(seq(b)),  control(seq(b)),
                 SiteOK on frames b … a − 1,  rt(seq(n)) = rt_r (b ≤ n < a)
                 →  (∀ n ∈ [b, a),  Zero(seq(n)))  ∧  (∀ n ∈ [b, a),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
map_check, map_start (private)  :  mapCheck = true,  startCheckT = true   (native_decide)
room_map (private)              :  map_of_rows with the two checks
```

`InRowsT(m)` says that `m` is a machine of the rows of the time of the change into the room. `Route.Changes` gives it at the first control (`Changes.roomAt` uses the same), with `SiteOK` (`roomSites`) and the player's routine (`roomStay`) on the frames up to the entry `a₂`.

Lean: `Theorems/RoomMap.lean`; private `Proof/RoomMap.lean`. In `Theorems/SideEntryRule.lean`: `PassR` and `pass_of`. In `Theorems/RoomJoin.lean`: the field `pass` gives `PassR`, and the field `tiles` gives `TilesOK`.

## How it works

**At the first control.** The rows of the change know every one of the 416 bytes of the block buffers, in every state with control. On the TAS these bytes are those of the map. The check `startCheckT` asks that every state with control in the rows of the time is under a start state of `Cond`.

**The walk.** It is the walk of `ScreenPage`, with three changes.

* The erase of a coin (`ErACM`) writes through a pointer that the walk does not know. `ScreenPage` asks that no byte of `B` has a known bit there. Here it asks that `A` is known and agrees with the known bits of every byte of `B` (`bufAgree`). The erase writes 0, and the known bits of `B` are bits that are 0, so this holds.
* At each state at the read of the block buffer routine, the walk checks `tilesB`: every byte of `B` out of the pipe's column is known to be neither tile. A byte is known not to be `T₁` when `T₁` has a 1 at a bit that is known to be 0. For this map every byte out of the column has such bits for both tiles.
* At the frame's end the walk asks `tilesB`, and a start state of `Cond`, or `rt` known and not `rt_r` (the frame left the player's routine).

**Size.** The search takes 210,934 steps with 8,750 forks and no failure. The table has 9,378 states. `mapCheck` takes about 3.4 s in a program, and `startCheckT` about 3.5 s. The private proof builds in about 8 s.

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
* `mapCheck` and `startCheckT` are true.

## Assumptions (not proved in Lean)

* **`SiteOK`** on each instruction of the frames from the first control to the entry, and the player's routine on each of those frames. These are what [The screen's page in the room, and the long timer of the side pipe](d-2-4-ScreenPage.md) assumes (`Route.Changes.roomSites`; `roomStay` is a theorem).
* **The join to `RoomRun`.** `map_of_rows` is about the machines of `Route.Changes`. The field `tiles` of `RoomRun` is about its frame `E` (`fm(E − 1)`, `pad(E)`). That this frame is the frame `a₂ − 1` of `Route.Changes` is not stated in Lean yet. With it, `tiles` follows from `room_map`.
* **The rest of the map** (item 1-1-c-7-12). Only the bits that are 0 in the map are proved. That bricks, the floor and the wall stay as they are, and that the numbers of the other fields are those of the map, are not proved.

**Files.** `Theorems/RoomMap.lean`, private `Proof/RoomMap.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-map-check FM2 [N]    # the two checks, and real frames: N runs of each kind (N = 200: about 10 min)
```
