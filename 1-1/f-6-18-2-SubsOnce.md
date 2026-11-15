[← Back](README.md) | [English](f-6-18-2-SubsOnce.md) | [Japanese](f-6-18-2-SubsOnce-ja.md)

# A frame in control comes to the end of the move at most once

**Claim.** A frame in control comes to the end of the move (`PlayerSubs`, where the player's routine calls the scroll handler) at one instruction at most. The frame starts in the idle loop in control (`StartK`), and each of its instructions meets `CleanK` of `guardK`. There is no condition on the stores to the routine, the mode or the task. So it holds on the frame of the touch, which writes the pole's routine.

So the field `moved` of `PoleJoin.Run` is gone. Part e shows that `P₂(g)` of the touch's frame is the position at an arrival of the frame at the end of the move (`OnFrames.touchMove`). There is only one arrival. So `P₂(g)` is the position at every instruction of the frame at the end of the move. That is `moved` (`Run.moved`).

`tr(j)` is the machine `j` instructions into a frame. `tr_g` is the frame `g` of `keep` (from `fm g` with the input `pad g`). `Q = PlayerSubs`. `idle` is the idle loop. `CleanK_K` is `CleanK` of `guardK` with the move routine's store of the fraction excepted ([One whole frame in control](f-6-19-FrameKeep.md)).

```
subs_once   :  StartK(m)  ∧  (∀ n,  CleanK_K(tr(n)))   →   ∀ k k',  pc(tr(k)) = Q  →  pc(tr(k')) = Q  →  k = k'

touchMove   :  ∃ k,  arrAt ≤ k  ∧  pc(tr_g(k)) = Q  ∧  P₂(g) = posP(tr_g(k))                     (part e)
Run.moved   :  ∀ j,  pc(tr_g(j)) = Q   →   P₂(g) = posP(tr_g(j))                                   (it was the field moved, for j up to the write)
Run.inRange :  P₀ ≤ P₂(g)                                                                       (from the walk of the touch's frame and Run.moved)
```

## The walks

Two walks of the abstract machine of `TaintRun` follow the frame. Their steps are those of `FrameKeep` (`kstep`, the guard `guardK`). No path is cut.

* The first walk (`walkS1`) starts at the frame's start: the two start states of `FrameKeep`, with no watched bits. It goes on until each path comes to `Q`, ends the frame at the start of a frame (`endOK`), or reaches a state of its table. At `Q` it asks that the second walk succeeds from that state.
* The second walk (`walkS2`) goes on from there until each path ends the frame at the start of a frame, or reaches a state of its table. It fails if a path comes to `Q`.

`run_S1`: from a state that the first walk covers, the frame comes to `Q` at a first instruction `k₁`, where the second walk succeeds, or it never comes to `Q`. `run_S2`: from a state that the second walk covers, the frame does not come to `Q` again. After the frame's end the machine stays in the idle loop, and `Q ≠ idle`. The start of the frame is in the idle loop too. So there is one arrival or none.

`AfterKeep.subs_once` (part e) is the same fact after the player's routine. Its walks cut a path at a store to the routine, the mode or the task by its address. So it asks that no instruction of the frame has one (`noStore`). The touch's frame has one: the write of the pole's routine. A version up to the write does not help. The arrival that `frOf g` reads is chosen in `SurfaceRead.read_move`, and nothing there says that it comes before the write. The walks here do not cut the write. The walk of `FrameKeep` already follows whole frames with it.

## The check on the ROM

`subsCheck`, in a program (`subs-once-check`, exit 0):

| walk | steps of its search | table | failures | states at `Q` |
|---|---|---|---|---|
| first, from the frame's start to `Q` | 4,382 | 378 | 0 | 2 |
| second, from `Q` to the frame's end | 709,326 | 46,413 | 0 | 0 (none comes to `Q` again) |

The check takes 2.7 s natively. It is part of `PoleFrame.poleFrameCheck`, so the private `pole_frame_check` (by `native_decide`) checks it too.

On real touches (`touch-move-check`): no touch's frame comes to the end of the move more than once. This only checks the theorem; the proof does not use it.

## Not proved

Nothing new. `subs_once` asks only `StartK` and `CleanK_K`. Every frame up to the touch has them (`FrameKeep.Frames.start`, `Frames.cleanAt`). `Run.moved` uses part e's `OnFrames.touchMove`, with its conditions (`frames`, and the touch not later than `farN` frames after control). A later touch is the case `SurfaceLate`, which does not use `Run.inRange`.

**Files.** `Theorems/SubsOnce.lean`, `Run.moved` and `Run.inRange` in `Theorems/PoleJoin.lean`, `PoleFrame.poleFrameCheck` in `Theorems/PoleFrame.lean`, private `Proof/PoleFrame.lean` (`pole_frame_check`).
