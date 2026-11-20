[← Back](README.md) | [English](c-7-5-1-RoomVert.md) | [Japanese](c-7-5-1-RoomVert-ja.md)

# The first frames of a jump in the room follow `vstep`

**Claim.** A frame of the bonus room on the first frames of a jump from the floor changes the vertical state as `vstep` says. This was the air part of the field `vframes` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-5). It is now a theorem on the real machines of the run. What it needs is on one frame or one machine: the frame starts in the room's condition and its instructions meet `SiteOK` (both already used by [the block map](c-7-12-RoomMap.md)), the frame comes to the player's routine in the state that `clean` already gives, and two conditions on the machine at the frame's start, `halt` and `prevA`. These two are now theorems too ([The halt value and A of the frame before](c-7-5-2-RoomPair.md), item 1-1-c-7-5-2). That the frame does not end during the movement is no longer asked (`longer`): it comes from `SiteOK` and the walk to the player's routine (item 1-1-c-7-1-1). The floor frames of `vframes` (stand or take off) stay assumed, as the field `vfloor`.

It also gives item 1-1-c-7-11 for these frames: in the air the movement routine does not read the stored speed, so the vertical motion does not depend on the horizontal one. Only the takeoff reads it. [Every frame of a jump in the room](c-7-11-1-RoomFall.md) extends this to every frame of a jump from the floor, up to the landing.

`V` is the set of bytes that `vsOf` reads: the height and its fraction, the vertical speed and its fraction, the two forces, the jump's origin, the state, and A and B. `V⁺` is `V` with A and B of the frame before, the jump's halt value, the change of size, the collision bits, the vertical page (since item 1-1-c-7-5-13) and the 8 horizontal bytes (`vKeepA`). `R` is the player's routine, `Q` the scroll handler (`PlayerSubs`). `tr(j)` is the machine `j` instructions into the frame, `end` the machine at the frame's end. `rt` is the routine byte. "Rising" means the state is 1 or 2 and bit 7 of the vertical speed is 1.

```
before_R :  RoomCond(M),  SiteOK on each instruction
            →  pc(tr(j)) = R  for at most one j of the frame,
               (∀ j' < j, pc(tr(j')) ≠ R)  →  V⁺(tr(j)) = V⁺(M),
               and  pc(tr(j)) = R  →  frame(tr(j)) = frame(M)        (the frame does not end at R)
after_Q  :  RoomCond(M),  SiteOK on each instruction
            →  pc(tr(j)) = Q  for at most one j of the frame,
               and  pc(tr(j)) = Q,  rising(tr(j)),  rt(end) = rt_room  →  V(end) = V(tr(j))
vert_air :  vertAirOK,  AtV(R),  st(R) ∈ {1, 2},  (st(R) = 1 → DTHJ(R) = 1),  PrevA(R) & 80 = A_B(R) & 80
            →  ∃ k ≤ 728,  pc(stepN(k, R)) = Q  ∧  vs(stepN(k, R)) = vstepV(vs(R), A(R), 0)  ∧  InFrameN(R, k)
bridge_of:  bridgeOK,  u ∈ arcSet(h, 8)  →  st(u) ∈ {1, 2}  ∧  ∀ a,  vstepV(u, a, 0) = vstep_m0(u, a, 0)
air_frame:  the above,  pc(tr(n)) ≠ idle → dot(tr(n)) ≤ dotsPerFrame − 64
            →  vs(end) = vstepV(vs(M), A(R), 0)          (if vstepV leaves him rising and rt(end) = rt_room)
varc_of  :  OnArc(T, n),  n + 1 − (T + 1) ≤ 8,  n < t0,  n + 1 < E
            →  vs(n + 1) = vstep(vs(n), a(n + 1), 0)
```

`a(n)` is now read from the machine: it is A of the vertical state at the end of frame `n` (`Frames.a`, which `vstep` sets to the A it was given). It was free data before.

`vstepV` is `vstep` on the machine `vmach`: the jump's halt value 1 and the stack pointer of the player's routine. `RoomJoin`'s jumps run `vstep` on the machine at the start of the level (`vstep_m0`), where the halt value is 0. The routine reads the halt value only in a jump, rising with A released: it compares it with how far he is above the jump's origin. `bridgeOK` checks that the two give the same on the 1533 states of the jumps from the floor up to 8 frames after the takeoff, for both values of A, and that the state is 1 or 2 there.

Lean: `Theorems/RoomVert.lean` (`walkV`, `frame_of_walkV`, `before_R`, `after_Q`, `piecesQ_class`, `piecesQ_cover`, `erase_keep`, `air_frame`, `air_arc`), `Theorems/VertAir.lean` (`AtV`, `vert_air`, `arcSet`, `bridgeOK`, `bridge_of`), `Theorems/RoomJoin.lean` (`RoomRun.varc_of`, `RoomCore.varc`, `arc_step`, `t0_lt_E`), `Theorems/RoomMap.lean` (`cond_of_rows`), `Theorems/Route.lean` (`Run.roomVert`, `Run.inRoom`); private `Proof/RoomVert.lean`.

## How

**Two walks of one whole frame.** Both are the walk of [the block map](c-7-12-RoomMap.md): the abstract machine knows the room's bytes and the target of every store. Each carries one bit in its states (`AS.spent`, which nothing reads while no counter is followed), and a list (`AS.log`). The walk asks that a step keeps them, and a state of the table covers a state only with the same bit and list.

* `walkA`: the bit says that the frame has come to `R`. A state at `R` with the bit set fails the walk: the frame comes there once. Before the bit is set, every step must keep `V⁺` (`StepWrites.keepOK`). With the one-step lemma of [StepWrites](d-3-4-1-StepWrites.md), no step before `R` writes `V⁺`. A state at the frame's end must not be at `R` (`finR`): so the frame comes to `R` before its end.
* `walkB`: at `Q` the state is split. The pieces in the air and rising get the bit; the others (falling, the state 0, 3, or above 3) get the list `[2]`. A state with the bit must keep `V` over its step, but the erase of a coin, which writes only in the block buffers. A step that may write `V` drops the bit and marks the state `[1]`; at the frame's end a state marked `[1]` must have the routine byte known and not the room's. This is the time running out: the routine that kills him writes the vertical speed, then the routine byte. A state at `Q` with the bit or a list fails the walk: the frame comes to `Q` once.

The proof of the two walks is one lemma (`frame_of_walkV`): a fact `Φ(j, bit, list)` about the machine after `j` instructions, kept by every step of a covering piece, holds at every instruction and at the frame's end.

| walk | steps of the search | table | check in a program |
|---|---|---|---|
| `walkA` | 468,180 | 22,016 | 6.9 s (with the search) |
| `walkB` | 443,657 | 19,547 | 5.9 s (with the search) |

The first try of `walkB` failed at the store of the vertical speed in the routine that kills him when the time runs out. That is why the bit can be dropped.

Since item 1-1-c-7-1-2, `walkA` also asks `cutOK` at `R` (the stack, the NMI, the routine byte, the area's type, the jumpspring and the swimming flag), keeps two more bytes up to `R` (the change of size and the collision bits), and splits the pause byte's low bit where the NMI loads it before the call of the mode's routine. Its search takes 468,184 steps (4 more), and the check 6.2 s in a program ([The room's frames at the player's routine](c-7-1-2-RoomCut.md)).

**The movement routine in the air.** `VertModel.vert_model` relates the real routine to `vstep` with the real stored speed, and asks `AtCtrl0`, which includes that the stored speed is `|v|`. On real frames in the room that fails after a hit: on 1,800 of 25,114 frames measured in the air and rising (below). The walk of `vert_model` does not use it. `vert_air` is `vert_model` with two changes: the condition is `AtV` (`AtCtrl0` without the stored speed), and the stored speed of `vstep`'s machine is 0 while the real one is not known (`vTagsA`). In the state 1 or 2 the routine reads the stored speed only in `X_Physics`, a detour of the walk, so the 16 cases in the air go through (`vertAirOK`, 0.4 s).

**The frame.** `before_R` with the first arrival at `R`, which is before the frame's end (the walk's states at the frame's end are not at `R`); `vert_air` there; `FrameModel.trace_inFrame` puts its machine at instruction `k + kk` of the frame, since each step of the routine keeps the frame (`InFrameN`) when it runs 64 dots or more before the frame's end, and `SiteOK` gives 6000; `after_Q` from there to the end.

**In `RoomJoin`.** The field `vframes` was used on two kinds of frames. Floor frames stayed as `vfloor`, now a theorem too (`RoomRun.vfloor_of`, item 1-1-c-7-5-14). The frames of a jump's first 8 frames (`OnArc`) are `RoomCore.varc`, which `RoomRun.varc_of` proves from `InRoom.vert` (the frame above), `read_vs`, `clean` (the state `AtV` at the arrival), `InRoom.pair` (`halt`, `prevA`), and the jump's arcs. `InRoom.vert` asks the frame to end in the player's routine, so it is stated for `n + 1 < E`. For that `low_by` and the lemmas above it now take `t0 < E` (`t0_lt_E`, from the way he leaves the block and the new numeric fact `vf`). The input `AirIn` of these frames now comes from the field `air_in`.

## Checked on real frames

Program `room-vert-check FM2 [N]`. Each frame of the room is run instruction by instruction from the first control: the movie, and `N` runs of each of 4 kinds of own input (up to 120 frames).

| run | frames | a byte of `V⁺` written before `R` | rising at `Q` (a byte of `V` changed to the end, ending in the player's routine) | in the air and rising by `vstep` (not `vstep` on the machine at control) | `halt` fails | `prevA` fails | floor frames before `C + 49` (neither stand nor take off) |
|---|---|---|---|---|---|---|---|
| the movie, first control to the entry | 111 | 0 | 36 (0) | 33 (0) | 0 | 0 | 1 (0) |
| random (200 runs) | 24,000 | 0 | 7,505 (0) | 6,718 (0) | 0 | 0 | 573 (0) |
| right with B (200 runs) | 24,000 | 0 | 6,427 (0) | 5,696 (0) | 0 | 0 | 968 (0) |
| left with B (200 runs) | 24,000 | 0 | 6,641 (0) | 5,909 (0) | 0 | 0 | 1,117 (0) |
| walls (200 runs) | 24,000 | 0 | 7,519 (0) | 6,758 (0) | 0 | 0 | 667 (0) |

On 1,800 of the 25,114 frames in the air and rising, the stored speed at the player's routine was not `|v|`: `vert_model`'s condition fails there, `vert_air`'s does not ask it. The checks on the ROM are true: `checkA` 8.0 s, `checkB` 7.5 s, `vertAirOK` 0.1 s, `bridgeOK` 0.2 s (each walk with its search).

## Assumptions (not proved in Lean)

* `vfloor` (one frame, now proved in item 1-1-c-7-5-14): a frame from `C + 34` to `C + 49` that starts on the floor stands or takes off as `VFrame` says, with the input. This is the old `vframes` on floor frames.
* `halt` and `prevA` are no longer assumed: [The halt value and A of the frame before](c-7-5-2-RoomPair.md) proves them.
* `SiteOK` on each instruction of the room's frames, as [the block map](c-7-12-RoomMap.md).
* The other fields of item 1-1-c-7-5 (`air_in`, `stand_wall`, `fall_long`, `stand_row`, `vfall`, `floor_at`, `low_at`) are not touched here.

`walkA` now also keeps the 8 horizontal bytes, and its states at the frame's end are not at `R`: this gives `Clean.before` and the arrival before the frame's end ([The room's frames: `before`, `longer` and half of `far`](c-7-1-1-FrameTime.md)).

**Files.** `Theorems/RoomVert.lean`, `Theorems/VertAir.lean`, private `Proof/RoomVert.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-vert-check FM2 [N]    # the checks (about 15 s) and real frames, N runs of each kind (N = 200: about 100 s)
```
