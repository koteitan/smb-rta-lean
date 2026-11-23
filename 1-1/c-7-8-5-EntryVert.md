[← Back](README.md) | [English](c-7-8-5-EntryVert.md) | [Japanese](c-7-8-5-EntryVert-ja.md)

# The entering frame: the frame before the entry is near the floor

Until round 35 the field `offNear` of [Joining the bonus room](c-5-RoomJoin.md) said: the frame before the entry `E` ends near the floor. Since round 36 this is proved, and the field is gone, with no new field.

`near(s)` (`OffDrop.nearB`) is: he stands at the floor's height, or he is in the air and one frame of `vstepR`, with A or not, reaches the floor's height falling. [Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md) uses it three times, to end the walk of the frames past the block's right end.

## The statement

`vE(n)` is the vertical state at the end of the room's frame `n`. `s` is `vE(E − 1)`, the state when the entering frame `E` begins. `t` is the vertical state at the end of frame `E`. `a` is bit 7 (A) of the joypad's bits at the player's routine of frame `E`. `y_floor` is the floor's height, 176 px. `y_e` is the height of the reference entry.

```
RoomRun.offNear_of :  C < E  →  near(vE(E − 1))

InRoom.airL   :  C < E  ∧  st(s) ≠ 0  →  falling(vstepR(s, a))  ∧  (t = vstepR(s, a)  ∨  t = land(vstepR(s, a)))
InRoom.standL :  C < E  ∧  st(s) = 0  ∧  no new press of A  →  StandNext(s, t)
InRoom.jumpL  :  C < E  ∧  st(s) = 0  ∧  a new press of A  →  False
InRoom.yL     :  C < E  →  y(t) = y_e
Checks.entryY :  y_e = y_floor
```

`airL` and `jumpL` also take the machine at the player's routine in the state `AtV`, and `airL` the jump's halt value and A of the frame before, as `InRoom.air` does; on frame `E` `InRoom.cut` and `InRoom.pair` give them. `standL` takes the player's routine and no jump in the input that the model reads there.

The four `InRoom` facts are proved on the real machines in `Route.lean` (`Run.roomAirL`, `Run.roomStandL`, `Run.roomJumpL`, `Run.roomLast`). `entryY` is a check on the ROM (`native_decide` in the private `Proof/RoomJoin.lean`).

**`offNear_of`.** By `yL` and `entryY`, frame `E` ends at `y_floor`.

* `st(s) ≠ 0`: by `airL`, `t = vstepR(s, a)` or `t = land(vstepR(s, a))`, and `vstepR(s, a)` falls. A landing keeps the high four bits of the height, so `y_floor ≤ y(vstepR(s, a))`. So `near(s)`.
* `st(s) = 0`: frame `E` does not take off (`jumpL`). With no new press, `StandNext(s, t)` (`standL`): `y(t) = y(s)`, or `y(t) = y(s) &&& 0xF0`. A stand is on a whole row (`stand_ok`), so `y(s) = y(t) = y_floor`. So `near(s)`.

`off_gap_of` needs `C < E`; its proof has it (`C ≤ T < t0 ≤ E`).

## How it works

**The walks of the room's frames.** Three walks follow a frame of the room to its end:

* walk B (`RoomVert`): from the scroll handler `Q`, in the air and rising;
* walk C (`RoomFall`): from `Q`, falling;
* walk S (`RoomStand`): from the player's routine `R`, standing with no new press of A.

A state on which a step may write a vertical byte where the walk does not allow it is marked. Until round 35 the frame's end condition asked of a marked state only that the routine byte is known and is not the room's. The entering frame ends in the side pipe's routine, so a marked state could end it. So the walks said nothing of frame `E`, and the `InRoom` facts held only for `n + 1 < E`.

Since round 36 the frame's end conditions ask more (`RoomVert.outE`, `RoomVert.notEng`):

* a marked state ends with the routine byte known, not the room's and not the side pipe's;
* in walk B, a state that came to `Q` rising, with no write of a vertical byte since, knows the routine byte not to be the side pipe's.

The three walks pass with these conditions, with no other change: the same searches, and no state at a frame's end is refused. The proofs from the walks (`RoomVert.after_QE`, `RoomFall.after_QHE`, `RoomStand.after_RSE`) now take a frame that ends in the room's routine or in the side pipe's. The old theorems (`after_Q`, `after_QH`, `after_RS`) are these for the room's routine; their statements did not change.

The walk of `RoomAbsKeep` (the stored speed from the end of the move) used walk B's old end condition. Its states with the bit do end in the side pipe's routine on the entering frame. So it now has its own condition `finX`, the old one.

**The entering frame** (`EntryVert`):

* `air_frame`: a frame in the air comes to `Q` with the vertical bytes of `vstepR` (`RoomFall.at_Q`). If they rise there, the frame does not end in the side pipe's routine (walk B). If they fall, the vertical bytes at the frame's end are those of `Q` or their landing (walk C).
* `stand_frame`: as `RoomStand.stand_frame`, with walk S for a frame that ends in the side pipe's routine.
* `jump_frame`: a takeoff rises at `Q` (`VertJump.vert_jump`), so the frame does not end in the side pipe's routine (walk B).

**On the real machines** (`Route.lean`). The entering frame is frame `k` of the run with `b₁ ≤ k < a₂` (`Run.roomEnter`). It ends in the side pipe's routine (`EntryRoutine.rt_of_rows`), so `a₂ = k + 1`, and part d's `Run.y₂` gives the height there (`Run.roomLast`). The frame starts in the room's condition and meets `SiteOK` on each instruction, as every frame of the room.

## The fields

Removed:

* `RoomRun.offNear`.

Not changed: `RoomRun.offTop` and `RoomRun.offSlow` (a narrowing of both to the runs that enter fewer than 12 frames after `t0` was not kept, because together they would say the conclusion of `off_gap_of`: [Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md), round 36).

Added: no field. New facts of `InRoom` (proved): `airL`, `standL`, `jumpL`, `yL`. New check on the ROM: `Checks.entryY`. The checks of walks B, C and S (`RoomVert.checkB`, `RoomFall.checkC`, `RoomStand.checkS`) have the stronger frame's end conditions; `RoomAbsKeep.checkX` has `finX`.

## Measured

`room-entry-vert FM2 300`:

| walk | steps of the search | states at a frame's end | refused by the round-36 condition | check (native) |
|---|---|---|---|---|
| B (`checkB`) | 442,838 | 50 | 0 | true, 6.5 s |
| C (`checkC`) | 615,540 | 60 | 0 | true, 11.7 s |
| S (`checkS`) | 464,647 | 52 | 0 | true, 8.2 s |
| `RoomAbsKeep.checkX` (`finX`) | | | | true, 5.9 s |

The reference entry ends at 176 px, the floor's height (`entryY`).

Real entering frames, with what `airL`, `standL`, `jumpL`, `yL` and `near` say:

| run | entering frames | state at the frame's start | against |
|---|---|---|---|
| the movie (movie frame 763) | 1 | 1 (in a jump) | 0 |
| own runs from the room's first control (300) | 48 | 0, 1 and 2 | 0 |

`room-off-back FM2 400` (round 35): 225 entries, 0 whose frame before is not near the floor.

## What remains (not proved)

* `offTop` and `offSlow` ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md)). The page says what a proof of each needs, with the measured frames of `offSlow` (`room-off-slow`).

## Uses from other parts

* Part d: `Run.y₂` (the walks `EntryHeight` and `EntryHeightBig`, with `Run.size₂` from `SizeKeep`), `EntryRoutine.rt_of_rows` (the walks `SideEntryEnd`, `SideEntryRest`).
* Part c: `Run.roomEnter`, `Run.roomIdx`, `RoomMap.cond_of_rows`, `RoomPair.quad_run`, `Run.roomSites`, `ChangesBase.roomStay`.
* No cycle: none of these uses `offNear`, `RoomRun.off_gap_of` or the new `InRoom` facts.

**Files.** `Theorems/EntryVert.lean` (`air_frame`, `stand_frame`, `jump_frame`, `air_room`, `stand_room`, `jump_room`). `Theorems/RoomVert.lean` (`outE`, `notEng`, `outE_ne`, `notEng_ne`, `not_outE`, `finB`, `finB_one`, `finB_spent`, `after_QE`). `Theorems/RoomFall.lean` (`finC`, `after_QHE`). `Theorems/RoomStand.lean` (`finS`, `after_RSE`). `Theorems/RoomAbsKeep.lean` (`finX`). `Theorems/RoomJoin.lean` (`InRoom.airL`, `standL`, `jumpL`, `yL`, `Checks.entryY`, `row_hi`, `RoomRun.offNear_of`). `Theorems/Route.lean` (`Run.roomLast`, `Run.roomAirL`, `Run.roomStandL`, `Run.roomJumpL`, `Run.inRoom`). `Main.lean`: `room-entry-vert`; the private `Proof/RoomJoin.lean` gets `entryY`. There is no game data in the public files.

**Reproduce.**
```
.lake/build/bin/smbrta room-entry-vert FM2 300    # the walks with the new conditions, entryY, and real entering frames (about 2 min)
.lake/build/bin/smbrta room-off-back FM2 400      # runs past the block's right end that enter (about 1 min)
```
