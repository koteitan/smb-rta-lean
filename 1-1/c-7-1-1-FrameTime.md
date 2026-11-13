[← Back](README.md) | [English](c-7-1-1-FrameTime.md) | [Japanese](c-7-1-1-FrameTime-ja.md)

# The room's frames: `before`, `longer` and half of `far` from the walks

**Claim.** The field `clean` of [Joining the bonus room](c-5-RoomJoin.md) says that each frame of the room up to `t₀` is `FrameModel.Clean`, or it leaves him stopped and is `FrameModel.ReadFrame` ([A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md)). Three parts of these are no longer assumed:
* `before`: nothing writes the horizontal bytes from the frame's start to the player's routine. The walk to the player's routine of [RoomVert](c-7-5-1-RoomVert.md) now keeps them too (`hbytes_at_R`).
* `longer`: the frame does not end in the 728 instructions after it comes to the player's routine. Now it comes from the frame's time: `SiteOK` (already assumed, `chg.roomSites`) puts every instruction away from the idle loop 6000 dots before the frame's end, and the walks of the movement show that each of their steps keeps the frame then.
* `far`, the upper half: `P + 2048 < 2²⁴`. Before `t₀` he is left of the goal (`first`), and the goal is left of the mouth (`slow_mouth`, `air_pos`), on page 0.

The lower half of `far` stayed, as a field of `RoomRun` on one machine: `2048 ≤ P` at the start of each frame up to `t₀`. It is now a theorem from a weaker field, `farNear` ([The position stays at 8 px or more](c-7-1-3-RoomFar.md), item 1-1-c-7-1-3). The state at the player's routine in `CleanR` and `ReadR` is now proved too, but the values that decide which ([The room's frames at the player's routine](c-7-1-2-RoomCut.md), item 1-1-c-7-1-2).

`R` is the player's routine, `tr(j)` the machine `j` instructions into the frame from `M`, `idle` the room's idle loop (a `JMP` to itself), `dot` the dot in the frame.

```
InTime(M, n₀)  :=  idleAt(idle)  ∧  frame(tr(n₀)) = frame(M)  ∧  ∀ n,  pc(tr(n)) ≠ idle → dot(tr(n)) ≤ dotsPerFrame − 64

hbytes_at_R  :  RoomCond(M),  SiteOK on each instruction,  pc(tr(j)) = R  →  H(tr(j)) = H(M)        (H: the 8 horizontal bytes)
clean_frameR :  modelOK,  CleanR(M, n₀),  H(tr(n₀)) = H(M),  InTime(M, n₀),  2048 ≤ P(M),  P(M) + 2048 < 2²⁴
                →  hs(end) = hstep(hs(M), in),   P(end) = P(M) + 16·v(end)
frame_readR  :  modelOK,  frictionCheck,  ReadR(M, n₀),  H(tr(n₀)) = H(M),  InTime(M, n₀),  the same range
                →  the frame is a TopSpeed.Frame
far_of       :  C ≤ n < t₀  →  2048 ≤ P(fm(n))  ∧  P(fm(n)) + 2048 < 2²⁴
t0_le_E      :  t₀ ≤ E
inTime_of    :  C ≤ n < t₀,  pc(tr(arr(n))) = R  →  InTime(fm(n), arr(n))
```

`CleanR` and `ReadR` are `Clean` and `ReadFrame` without `before`, `longer` and `far`.

Lean: `Theorems/FrameTime.lean` (`InTime`, `CleanR`, `ReadR`, `clean_frameR`, `fric_readI`, `frame_pathI`, `frame_readR`), `Theorems/RoomJoin.lean` (`RoomRun.clean`, `InRoom.le`, `InRoom.time`, `InRoom.arrive`, `InRoom.before`, `goal_mouth`, `before_of`, `goal_small`, `t0_le_E`, `far_of`, `inTime_of`, `follow_of_clean`, `move_top_of`), `Theorems/RoomVert.lean` (`vKeepA`, `finR`, `finA`, `before_R`, `hbytes_at_R`, `air_frame`, `air_arc`), `Theorems/VertAir.lean` (`vert_air`), `Theorems/Route.lean` (`late_of`, `Run.roomTime`, `Run.roomArrive`, `Run.roomBefore`, `Run.roomVert`, `Run.inRoom`); private `Proof/RoomVert.lean` (`room_vert_idle`).

## How

**The frame's time.** A step of a walk of the movement keeps the frame when it runs 64 dots or more before the frame's end: no instruction takes that long (`FrameModel.InFrame`). The walks of `move_model`, `frame_path`, `fric_read`, `tail_spec` and `vert_air` show this for each of their steps (`InFrameN`). `FrameModel.trace_inFrame` (part e) then gives: if the frame comes to `R` before its end, and every instruction not at the idle loop runs 64 dots or more before the end, the steps of the walk are the frame's steps. `FrameModel` drops `InFrameN` from `frame_path` and `fric_read`; `frame_pathI` and `fric_readI` are copies with it kept. The proofs are the same.

**The time in the room.** `SiteOK` says that an instruction not at the idle loop runs at a dot of at most `late = dotsPerFrame − 6000` (`late_of`). The idle loop is a `JMP` to itself (`room_vert_idle`, a check on the ROM).

**The arrival and `before`.** The walk to the player's routine of [RoomVert](c-7-5-1-RoomVert.md) now asks that its states at the frame's end are not at `R` (`finR`). So if `tr(j)` is at `R`, the frame has not ended there (`before_R`). The walk also keeps the 8 horizontal bytes up to `R` (they are now in `vKeepA`), and the frame comes to `R` once, so at any `j` with `tr(j)` at `R` they are those of `M` (`hbytes_at_R`). The check of the walk is true (6.4 s). `room-vert-check` saw no step before `R` write a byte of `vKeepA` on 24,111 real frames (the movie and 200 runs).

**On the room's frames.** `InRoom.time`, `InRoom.arrive` and `InRoom.before` hold for each frame before the entry `E` (`Route.Run.roomTime`, `Route.Run.roomArrive`, `Route.Run.roomBefore`: the room's frame `n` is frame `b₁ + (n − C)` of `base`, before `a₂`). `clean` speaks of frames up to `t₀`, and `t₀ ≤ E` (`t0_le_E`): on the entry frame he is at the mouth, and before `t₀` he is left of the goal, which is left of the mouth. `InRoom.le` is `C ≤ E` (`Route.Run.room_le`). `RoomVert.air_frame` uses the same time in place of its argument `hl`.

## Checked on real frames

`room-pair-check FM2 50`: the least position at the end of a frame in the room was 5920 on the movie and 3552 on 200 runs of own inputs from first control (30,000 frames). The field `far` asks 2048. `longer` was checked on real frames before; it is now a theorem.

## Assumptions (not proved in Lean)

* `far` is no longer a field: it is proved from `farNear`, a condition only on the frames that start within 3.5 px right of 8 px ([The position stays at 8 px or more](c-7-1-3-RoomFar.md)).
* `SiteOK` on each instruction of the room's frames (`chg.roomSites`, item 1-1-d-2-4-2), as before.
* The rest of `CleanR` and `ReadR`: the values at the player's routine that decide whether the frame follows the model (the stored speed, the mask, the collision bits), and what the frame does from the scroll handler on (`after`, `collide`). The rest of the state there and the arrival are proved now, from the new field `unpaused` ([The room's frames at the player's routine](c-7-1-2-RoomCut.md)).

**Files.** `Theorems/FrameTime.lean`, and the files above.

**Reproduce.**
```
.lake/build/bin/smbrta room-vert-check FM2 [N]    # the walk to the player's routine with finR
.lake/build/bin/smbrta room-pair-check FM2 [N]    # the idle loop, and the least position on real frames
```
