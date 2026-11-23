[← Back](README.md) | [English](c-7-8-3-OffStand.md) | [Japanese](c-7-8-3-OffStand-ja.md)

# A stand on the block's top: the bytes that a fall does not read

In round 34 the field `offStand` of [Joining the bonus room](c-5-RoomJoin.md) took the place of a part of `Off` ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md), item 1-1-c-7-8-2). It said: if frame `t0 − 1` ends standing, the jump force is the fall force, the fall force is one of a takeoff's (`forces`), and the jump's origin is the block's top or a height of `N.heights`. The proof used it only to put that stand into the list `standFam` of the check `standB`. Since round 35 `offStand` is gone. Two facts take its place, both proved:

* every frame of the room before the entry ends with a fall force of the room;
* a stand or a fall does not read the jump force or the jump's origin, so those two bytes need not be known.

## What is proved

`vstepR(s, a)` is one frame of the game's movement routine (`PlayerMovementSubs`) from the vertical state `s` with A or not, on the machine of the player's routine (`RoomJoin.vstepR`). `vE(n)` is the vertical state at the end of the room's frame `n`, read from the machine. `s[vf := v, origin := o]` is `s` with the jump force `v` and the jump's origin `o`.

```
OffStand.air_keep  :  st(s) ∈ {1, 2}  →  vfd(vstepR(s, a)) = vfd(s)  ∧  origin(vstepR(s, a)) = origin(s)  ∧  st(vstepR(s, a)) = st(s)
OffStand.fall_same :  st(s) = 2  →  vstepR(s, a) = vstepR(s[vf := v, origin := o], a)[origin := origin(s)]
RoomRun.vfd_ok     :  ∀ n ∈ [C, E),  vfd(vE(n)) ∈ forcesR
RoomRun.off_stand  :  st(vE(t0 − 1)) = 0  ∧  y(vE(t0 − 1)) = y_top  →  t0 + aboveF ≤ E + 1
```

`forcesR` (`RoomJoin.forcesR`) is the fall forces of a takeoff (`forces`) and the fall forces of the states at first control (`N.vStart`).

**The movement routine in the air** (`air_keep`, `fall_same`). In the air (the state 1 or 2) the routine writes neither the fall force, nor the jump's origin, nor the state. Only a takeoff writes them, and in the air with the swimming flag 0 the routine takes none. In a fall (the state 2) it first copies the fall force into the jump force, and it never reads the jump's origin. So two falling states that differ only in the jump force and the origin have the same next state, but the origin, which each keeps. The proof is the walk of two machines of `runSub` (`FrameModel.runSub2`), with the detours of the vertical model for the horizontal parts (`VertModel.detours`). The check `OffStand.keepOK` has eight walks: the state 1 or 2, A or not, A on the frame before or not.

**The fall force** (`vfd_ok`). At first control the fall force is one of `N.vStart` (`InRoom.vstart`). A frame that starts standing with no jump keeps it (`StandNext`). A takeoff from a whole row has one of `forces` (the check `offVfdCheck` on the takeoffs of the 16 rows; a stand is on a whole row by `stand_ok`). In the air the routine keeps it (`air_keep`), and a landing keeps it.

**Two states that differ where a stand or a fall does not read** (`SimV`). `SimV(a, b)` says that `a` and `b` have the same height, fractions, vertical speed, fall force, state and A on the frame before, and, unless the state is 0 or 2, the same jump force and origin.

```
offNext_sim :  SimV(a, b)  ∧  t ∈ offNext(a)  →  ∃ t' ∈ offNext(b),  SimV(t, t')
nearB_sim   :  SimV(a, b)  →  near(a) = near(b)
```

A stand keeps the two bytes (`StandNext`) and a takeoff writes both, so the next states of two stands of `SimV` are of `SimV` again. For two falls this is `fall_same`. So a path of the real frames past the block's right end, from a state of `SimV` to a state `w` of a list, is matched step by step by a path of `offNext` from `w` (`offB_path_sim`, `offB_gap_sim`).

**The stand at `t0 − 1`** (`off_stand`). The field `offTop` puts the stand on the block's top. `stand_ok` gives it no vertical speed, and `vfd_ok` a fall force of `forcesR`. So the state `w`, which is `vE(t0 − 1)` with the jump force put to its fall force and the origin to the block's top, is in `standFam`, and `SimV(vE(t0 − 1), w)`. From `w` the check `standB` finds no state near the floor for `aboveF − 1 = 12` frames. So the entry is more than 12 frames after `t0 − 1`, as before.

## The fields

Removed:

* `offStand` (a field of `RoomRun`).

Added: no field. New ROM checks of `RoomJoin.Checks` (`native_decide` in the private `Proof/RoomJoin.lean`): `keepA` (`OffStand.keepOK`) and `offVfd` (`offVfdCheck`). The check `standB` now starts from a smaller `standFam`: the fall forces of `forcesR`, the origin only at the block's top, any fraction, A or not, 2,048 states (was 6,144: the fall forces of `forces`, the origins of the block's top and of `N.heights`). Since round 35 it also allows a landing at any height and follows each state once ([Past the block's right end: a landing at any height](c-7-8-4-OffLand.md)).

The check `offVfdCheck` was false in its first form. It asked the fall force at first control to be one of `forces` (the three fall forces of a takeoff). It is not: it is the fall force of the machine at the room's start, a smaller force than all three, and it stays until his first takeoff. So the invariant allows the fall forces of `N.vStart` too, and `standFam` has that force as a fourth fall force. The old field `offStand` was not false on the measured runs (0 against in round 34): there he took off before he stood on the block's top.

## Measured

`room-off-stand` (the checks of this page, on the ROM):

| check | result | time (native) |
|---|---|---|
| `keepOK` (eight walks of the movement routine in the air) | true | 55 ms |
| `offVfdCheck` (the takeoffs of the 16 rows and the state at first control have a fall force of `forcesR`, four values) | true | 1.2 s |
| `standB` (from the 2,048 stands of `standFam`, no state near the floor for 12 frames of `offNext`) | true | 7.9 s (round 34: 14.5 s on 6,144 states) |

The field had no measured frame against it (round 34: `room-off-ways`, 34 stands at `t0 − 1`). `room-off-ways` still counts it.

## What remains (not proved)

* `offTop`, `offSlow` ([Off the block's top: the frames to the floor](c-7-8-2-OffDrop.md) says how each could be proved). `offNear` is proved in round 36 ([The entering frame](c-7-8-5-EntryVert.md)). `offFloor` is gone too, in round 35 (item 1-1-c-7-8-4).

**Files.** `Theorems/OffStand.lean` (`keepOK`, `run_K`, `air_keep`, `fall_same`). `Theorems/RoomJoin.lean` (`forcesR`, `standFam`, `offVfdCheck`, `jump_vfd`, `SimV`, `fall_sim`, `offNext_sim`, `nearB_sim`, `RoomRun.st_012`, `RoomRun.vfd_ok`, `RoomRun.offB_path_sim`, `RoomRun.offB_gap_sim`, `RoomRun.off_stand`; the checks `keepA`, `offVfd`). `Main.lean`: `room-off-stand`; the private `Proof/RoomJoin.lean` gets `keepA` and `offVfd`.

**Reproduce.**
```
.lake/build/bin/smbrta room-off-stand     # the checks of this page and of 1-1-c-7-8-4 (about 2 min)
```
