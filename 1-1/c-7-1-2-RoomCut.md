[← Back](README.md) | [English](c-7-1-2-RoomCut.md) | [Japanese](c-7-1-2-RoomCut-ja.md)

# The room's frames at the player's routine

**Claim.** In each frame of the bonus room before the entry, the machine at the player's routine is in the state `VertAir.AtV`: the program of the ROM, no NMI pending and the NMI off, the stack pointer of the player's routine, the routine byte of control, the area's type 1, 2 or 3, the player's state 0, 1 or 2, and the jumpspring, the swimming flag and the change of size 0. A frame that ends with the game not paused comes to the player's routine, and `arr n` is its first arrival.

These were parts of the field `clean` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-1): all of `AtCtrl` and `AtFrame` but the values that decide whether the frame follows the model. The field `arr` (the instruction of the arrival, free data) is now a definition, `CtrlKeep.arrAt`. The range of the speed at the player's routine (`AtFrame.speed`) now comes from the frames before.

What changed in `RoomRun`:

* `clean` now asks `CleanW` or `Stop ∧ ReadW`. `CleanW`: at the player's routine the stored speed is `|v|`, the side he presses is not masked, and from the scroll handler on nothing writes the horizontal bytes. `ReadW`: at the player's routine the collision bits are a value of `TopSpeed.collBits`, and `Collide` from the scroll handler on.
* `unpaused` (new, one machine): each frame up to `t₀` ends with the game not paused.
* `arr` is gone (a definition).

`R` is the player's routine, `tr(j)` the machine `j` instructions into the frame from `M`, `end` the machine at the frame's end. `st` is the player's state, `size` the change of size, `rt` the routine byte, `pz` the pause byte, `S_R` the stack pointer of the player's routine.

```
CutAt(m)     :  prg, mask of the walk's ROM,  no NMI pending,  NMI off,  s(m) = S_R,  rt(m) = rt_ctl,
                area(m) ∈ {1, 2, 3},  spring(m) = 0,  swim(m) = 0
cut_R        :  RoomCond(M),  SiteOK on each instruction,  pc(tr(j)) = R,  frame(tr(j)) = frame(M)  →  CutAt(tr(j))
arrive_R     :  RoomCond(M),  SiteOK on each instruction,  pz(end) & 1 = 0
                →  ∃ j ≤ fuelPerFrame,  pc(tr(j)) = R  ∧  frame(tr(j)) = frame(M)  ∧  ∀ j' < j,  pc(tr(j')) ≠ R
Quad(m)      :  st(m) ∈ {0, 1, 2}  ∧  size(m) = 0
quad_step    :  RoomCond(M),  SiteOK on each instruction,  Quad(M),  rt(end) = rt_room  →  Quad(end)
quad_run     :  b₁ ≤ n < a₂  →  Quad(seq(n))
Run.roomCut  :  C ≤ n < E,  pc(tr(j)) = R  →  AtV(tr(j))
Run.roomReach:  C ≤ n < E,  pz(end) & 1 = 0  →  pc(tr(arr(n))) = R
CleanW.toR   :  CleanW(M, n₀),  AtV(tr(n₀))  →  CleanR(M, n₀)
ReadW.toR    :  ReadW(M, n₀),  AtV(tr(n₀)),  |v(tr(n₀))| ≤ top  →  ReadR(M, n₀)
```

Lean: `Theorems/RoomVert.lean` (`cutOK`, `phA`, `pzLd`, `pzPieces`, `finA`, `zoneA_cover`, `CutAt`, `cut_R`, `arrive_R`, `vKeepA`), `Theorems/RoomPair.lean` (`knSt`, `knZero`, `phSt`, `phSz`, `checkSt`, `checkSz`, `Quad`, `QuadWalks`, `quad_step`, `rowQ`, `rowsCheck`, `quad_of_rows`, `quad_run`, `RoomWalks`), `Theorems/RoomJoin.lean` (`CleanW`, `ReadW`, `CleanW.toR`, `ReadW.toR`, `RoomRun.unpaused`, `RoomRun.arr`, `InRoom.reach`, `InRoom.cut`, `RoomRun.arrive`, `atV_of`, `cleanR_of`, `speed_of`, `readR_of`), `Theorems/Route.lean` (`Run.roomReach`, `Run.roomCut`, `Run.inRoom`); private `Proof/RoomVert.lean` (`room_vert_a`, `room_quad_st`, `room_quad_size`, `room_quad_apart`, `room_pair_rows`).

## How

**The walk to the player's routine** of [RoomVert](c-7-5-1-RoomVert.md) (`walkA`) now asks three more things.

* At a state at `R` that has not been there before, the walk asks `cutOK`: the stack pointer `S_R`, no NMI pending, bit 7 of the control register known 0, and the routine byte, the area's type, the jumpspring and the swimming flag known with the values of `CutAt`. The walk covers the machine at every instruction, so `cut_R` follows.
* It keeps two more bytes up to `R`: the change of size and the collision bits.
* Where the NMI loads the pause byte before the call of the mode's routine (`pzLd`), it splits the state into two pieces: the byte's low bit known 1 and known 0. The pieces carry the marks `[1]` and `[0]`, so the search keeps them apart. At `R` the mark is cleared. At the frame's end a state that has not come to `R` must know the low bit to be 1 (`finA`). So a frame that ends with the bit 0 came to `R` (`arrive_R`). With `before_R` (the frame comes to `R` at most once) this is the first arrival, and `CtrlKeep.arrAt` finds it.

**The player's state and the change of size.** The walk does not know them at a frame's start, so they come from the frames before. Each is a relation of one byte, with its own walk of the kind of [RoomPair](c-7-5-2-RoomPair.md) (`pair_frame` with `x = y`): `st ∈ {0, 1, 2}` is shown by the bits 2 to 7 known 0 and bit 0 or bit 1 known 0 (`knSt`), `size = 0` by the byte known 0 (`knZero`). At the first control the rows of the change know both (`rowQ`); the same pass over the rows checks both relations of `RoomPair` and these two (`rowsCheck`). `quad_run` is the induction over the frames, as `pair_run`. The walk to `R` keeps both bytes, so they hold at `R` too.

**The speed's range.** At the start of each frame up to `t₀` the horizontal state is in the domain `D` (`RoomRun.far_inD`, item 1-1-c-7-1-3), so `|v| ≤ top`. The walk to `R` keeps the speed (`InRoom.before`).

| check on the ROM | table | steps | time in a program |
|---|---|---|---|
| `RoomVert.checkA` (with `cutOK`, the two bytes, the split) | 69,913 | 468,184 | 6.2 s (6.9 s before) |
| `RoomPair.checkSt` | 36,165 | 209,867 | 3.4 s |
| `RoomPair.checkSz` | 36,165 | 209,867 | 3.5 s |
| `RoomPair.rowsCheck` (four relations) | the rows of the time | | 25 s, the same as the old check of two |

The split at the pause byte adds 2 states to the table.

**Tried and not done: the collision bits.** A third walk asked that the collision bits keep their bits 2 to 7 set (this is `collBits`). It fails at 6 ends. The cause is the store at the end of `ImpedePlayerMove`, which stores the bits AND the complement of X. X is loaded from a temporary byte, decremented, and on one branch incremented again; on every real path it is 1 or 2. But the abstract machine does not learn from the branch that the decremented X was 0, so X is not known at the store, and neither are the bits. A fix needs the branch to refine X in the abstract machine of `TaintRun`. So `ReadW` keeps `coll`.

## Checked on real frames

`room-ctrl-check FM2 200`: each frame of the room from the first control, run instruction by instruction: the movie, and 200 runs of each of 5 kinds of own input, up to 150 frames (kind 0: any buttons, Start and Select too; kind 4: Start on 1 frame in 8).

| | frames |
|---|---|
| frames in the room | 150,111 |
| not coming to the player's routine | 37,392 (kinds 0 and 4) |
| of them ending not paused | 0 |
| `CutAt` fails at the player's routine | 0 |
| the player's state not 0, 1, 2, or the change of size not 0 (start or routine) | 0 |
| the collision bits not in `collBits` (start or routine) | 0 |
| a byte of `vKeepA` written before the routine | 0 |
| the stored speed not `|v|`, or the side masked (not `CleanW`) | 8,606 |
| `|v| > top` at the routine | 0 |

## The pause, a false fact before this round

`clean` asked that each frame up to `t₀` comes to the player's routine (`pc` of `AtCtrl` and of `AtFrame`). A frame that ends paused does not come there. So a run that pauses in the room before `t₀` was outside the theorem, and no page said so. On the own runs above, 37,392 frames do not come to the player's routine, all paused. It is still outside the theorem, but now as its own field, `unpaused`. A pause only delays, but the room's model (`RoomCore`) counts every frame from `C`, so a paused frame is not in it.

## Assumptions (not proved in Lean)

* `unpaused` (one machine each frame, new): each frame up to `t₀` ends with the game not paused. It was hidden in `clean`.
* `CleanW` or `Stop ∧ ReadW` (one frame each): the stored speed and the mask at the player's routine (they decide whether the frame follows the model), the collision bits in `collBits`, and what the frame does from the scroll handler on (`after`, `collide`).
* `SiteOK` on each instruction of the room's frames (`chg.roomSites`), as before.

**Files.** `Theorems/RoomVert.lean`, `Theorems/RoomPair.lean`, `Theorems/RoomJoin.lean`, `Theorems/Route.lean`, private `Proof/RoomVert.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-ctrl-check FM2 [N]    # the checks (about 40 s) and real frames, N runs of each of 5 kinds
```
