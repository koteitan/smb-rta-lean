[← Back](README.md) | [English](c-7-1-4-RoomLag.md) | [Japanese](c-7-1-4-RoomLag-ja.md)

# A run that pauses in the room

**Claim.** The room's frames are now the frames of the run from the room's first control `b₁` on that end with the game not paused. A frame that ends paused does not come to the player's routine and keeps every byte that the room's model reads. So a run that pauses in the room before passing the block is in the theorem. The field `unpaused` is gone. The new field is `roomLag`: in the room, a frame that ends paused is a `lag` frame of `clock`.

Before this round `RoomRun` took the room's frame `n` to end at frame `b₁ + (n − C)` of the run, so every frame of the room was a frame of the model. The field `unpaused` asked that each frame up to `t₀` ends not paused ([The room's frames at the player's routine](c-7-1-2-RoomCut.md)). A run that pauses in the room failed it. Parts a and f already count only the frames that end not paused (`PipeFrames.Lags`, `FrameKeep.Keep`). Now the room does the same.

## The room's frames

`S` is the run (`Route.Run.base`), `seq(k)` the machine when frame `k` begins, `pz` the pause byte, `R` the player's routine. `lim = a₂ − b₁`, where `a₂` is the first machine from `b₁` on that has left the player's routine (`Route.Base.a₂`).

```
up(k)     :  pz(seq(b₁ + k)) & 1 = 0                  frame b₁ + k − 1 ends not paused
ups       :  #{ k : 1 ≤ k ≤ lim,  up(k) }
ix(j)     :  the j-th k ≥ 1 with up(k);  ix(0) = 0    (FrameKeep.ixOf, as part f)
fe(n)     :  seq(b₁ + ix(n − C))                      the end of the room's frame n
fm(n)     :  seq(b₁ + ix(n + 1 − C) − 1)              where the room's frame n + 1 begins
```

These are definitions (`RoomJoin.ixR`, `endAt`, `startAt`, `inpAt`; `RoomRun.fe`, `RoomRun.fm`). `RoomRun` takes `lim` as a new parameter. The model reads the state, the position and the vertical state at the end of each frame (`read_hs`, `read_P`, `read_vs` at `fe(n)`). The conditions on one frame (`clean`, `read_in`, `read_ab`, `ab_early`, `farNear`, `enters`, `read_PE`; once also `vfloor`) speak of the real frame from `fm(n)`.

```
RoomRun.next     :  C ≤ n,  n + 1 − C ≤ ups  →  fe(n + 1) = frame(fm(n), inAt(n))
RoomRun.up       :  C ≤ n,  n + 1 − C ≤ ups  →  pz(frame(fm(n), inAt(n))) & 1 = 0
RoomRun.between  :  ix(n − C) ≤ k,  k + 1 < ix(n + 1 − C)  →  pz(seq(b₁ + k + 1)) & 1 = 1
RoomRun.fe_C     :  fe(C) = seq(b₁)
RoomRun.arrive   :  C ≤ n < t₀  →  pc(tr_n(arr(n))) = R                    (was: from the field unpaused)
```

`tr_n(j)` is the machine `j` instructions into the frame from `fm(n)`.

## A frame that ends paused

The walk to the player's routine of [RoomVert](c-7-5-1-RoomVert.md) carries a bit that says the frame has come to `R`. At the frame's end it now asks more (`finA`): a state that has come to `R` knows the pause byte's low bit to be 0, and a state that has not come there knows it to be 1. The check `RoomVert.checkA` still holds, with the same table (69,913 states) and the same time (6.4 s in a program). With it:

```
end_R     :  RoomCond(M),  SiteOK on each instruction  →
               (∃ j,  pc(tr(j)) = R)  →  pz(end) & 1 = 0
               (∀ j,  pc(tr(j)) ≠ R)  →  pz(end) & 1 = 1  ∧  ∀ x ∈ vKeepA,  end[x] = M[x]
paused_R  :  RoomCond(M),  SiteOK,  pz(end) & 1 = 1  →  ∀ x ∈ vKeepA,  end[x] = M[x]
```

`vKeepA` holds the bytes of `readHS`, of the position and of `vsOf` (`RoomVert.model_eq_of`). So the frames between the end of the room's frame `n` and the start of its frame `n + 1` keep what the model reads (`Run.roomKeep`, the new part `InRoom.keep`):

```
Run.roomKeep  :  C ≤ n < E  →  readHS(fm(n)) = readHS(fe(n))  ∧  P(fm(n)) = P(fe(n))  ∧  vs(fm(n)) = vs(fe(n))
```

Each of these frames is a frame of `base` in the room, so it starts in the room's condition (`RoomMap.cond_of_rows`) and meets `SiteOK` (`chg.roomSites`).

## What the count needs

`room.C` and `room.E` are fixed by `clock`: `chg.hb₁` says `seen(b₁) = C + 1`, `chg.ha₂` says `seen(a₂) = E + 1`, where `seen(k)` counts the frames before `k` that are not `lag` frames. The room's frames are the frames that end not paused. The proof needs that the room's frame `E` is found by `a₂`:

```
Run.roomMany  :  E − C ≤ ups
```

It follows from one condition on each frame, the new field `roomLag`:

```
roomLag  :  b₁ ≤ n < a₂,  pz(seq(n + 1)) & 1 = 1  →  kind(n) = lag
```

Then `E − C = #{ n ∈ [b₁, a₂) : kind(n) ≠ lag } ≤ #{ n ∈ [b₁, a₂) : pz(seq(n + 1)) & 1 = 0 } = ups`. With `E − C ≤ ups`, every room frame before the entry begins at a frame of `base` in the room (`Run.roomIdx`: `b₁ ≤ b₁ + ix(n + 1 − C) − 1 < a₂`), and so do the walks' theorems (`roomBump`, `roomArrive`, `roomBefore`, `roomReach`, `roomCut`, `roomTime`, `roomVert`, `roomPair`, `roomEnter`).

Only one direction is needed. If a frame that ends not paused were a `lag` frame, `E − C < ups`; then the room's frame `E` would come before the real entry, and `enters` would be false on that run. On the real runs below there is no such frame. `roomLag` is the room's part of the rule "a `lag` frame is a frame that ends paused", as `Run.LagUp` is above ground and `chg.paused₁` in the first change.

## Removed and added

* Removed: the field `room.unpaused`.
* Added: the field `roomLag` of `Route.Run`; the parameter `lim` of `RoomRun`; the parts `many` and `keep` of `InRoom` (theorems `Run.roomMany`, `Run.roomKeep`).
* Changed: `RoomRun`'s frames (definitions above); `RoomJoin.StartAt` is asked of `fe(C)`, `Run.roomCtl` says `fe(C) = seq(b₁)`; `InRoom.vert` concludes at `frame(fm(n), inAt(n))`; `farNear` concludes at `frame(fm(n), inAt(n))`; `RoomVert.finA` asks the bit 0 after the arrival.

## Checked on real frames

`room-lag-check FM2` (about 32 s): the movie with a pause put into the room (Start at frame `f`, nothing, Start at `f + d`, then the movie's inputs `d` frames later), `f` from 461 to 569 in steps of 6 and `d` = 45, 50, 77; and 40 runs of own inputs from the room's first control, up to 300 frames, Start on 1 frame in 8. With `d` = 44 the second Start comes while the pause timer still runs, and the game stays paused.

| | |
|---|---|
| runs with a pause that reach the side pipe | 57 of 57 |
| room frames that end paused | 3,268 |
| of them with the phase moving (against `roomLag`) | 0 |
| of them coming to the player's routine | 0 |
| of them changing a byte of `vKeepA` | 0 |
| room frames with the phase still that end not paused | 0 |
| runs against `roomMany` | 0 |
| runs whose counted frame `E − C` is not the entering frame | 0 |
| counted frames whose `vKeepA` differs from the movie's frame without the pause | 0 |
| own inputs: frames, ending paused, with the phase moving, changing `vKeepA` | 12,000, 6,248, 0, 0 |

On the run with a pause at frame 500 for 60 frames, the old definition put the entering frame at frame 570 of `base`, but the real entry is frame 630: the old `enters` and `unpaused` were false there.

## Not proved

* `roomLag` (one frame each, new): in the room a frame that ends paused is a `lag` frame. It ties `clock`'s kinds to the machines in the room.
* The other fields of `RoomRun`, as before. They are now asked of the counted frames only.

**Files.** `Theorems/RoomJoin.lean`, `Theorems/RoomVert.lean`, `Theorems/Route.lean`, `Main.lean` (`room-lag-check`).

**Reproduce.**
```
.lake/build/bin/smbrta room-lag-check FM2       # pauses in the room: roomLag, the count, the frames that end paused
.lake/build/bin/smbrta room-ctrl-check FM2 [N]  # checkA with the new finA
```
