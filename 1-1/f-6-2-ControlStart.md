[← Back](README.md) | [English](f-6-2-ControlStart.md) | [Japanese](f-6-2-ControlStart-ja.md)

# The machine at control above ground

**Claim.** On a real run of the change out of the side pipe, the machine at control above ground has the castle flag down, and it is the start of a frame in control as the walk of one whole frame needs it ([One whole frame in control keeps the castle flag and the fraction's low bits](f-6-19-FrameKeep.md)). The conditions are those under which the change gives the horizontal state at control (`SurfaceFrames.EndRun.start`).

So the field `noCastle` of `PoleJoin.Run` (no castle flag up to the touch) is gone, and so is the field `keep.start` (each frame up to the touch starts in control). Both are theorems now.

`seq` are the machines of the change (`SideChangeEnd.EndRun`), `a` the entry, `b` the first control. `castle(m)` says that `StarFlagTaskControl` is not 0.

```
AtCtl(m)         :=  FrameStart_K(m)  ∧  castle(m) = false
FrameStart_K(m)  :=  idle loop  ∧  S = S₀  ∧  the dot's window  ∧  NMI on  ∧  strobe off  ∧  controllable(m)

ctlCheck         :  the entry has the program of m0,  and in every state of the rows that has control:
                    castle known 0,  endOK                                    (side_ctl, native_decide)
ctl_of_rows      :  ctlCheck,  InRows(m),  controllable(m)   →   AtCtl(m)
EndRun.inRows    :  Statement,  EndStatement,  startCheck,  EndRun,  (∀ n,  a ≤ n < b  →  left(seq n) ≠ 0)   →   InRows(seq b)
EndRun.atCtl     :  the same,  ctlCheck   →   AtCtl(seq b)
Route.Run.atCtl₀ :  the checks of the change,  startCheck,  ctlCheck,  Route.Run   →   AtCtl(pole.seq 0)
```

`InRows(m)` says that a state of a row covers `m`. `EndRun.inRows` is the induction of `EndRun.start`: during the pipe or in the rows, frame by frame, up to `b`. `startCheck` says that no machine during the pipe has control, so `seq b` is in the rows. The condition on `left` comes from the time at the exit (`EndRun.first`), as for `Run.start`.

`ctl_of_rows` reads `AtCtl` from the state `S` that covers `m`. The castle flag is a known byte of `S`. `controllable(m)` gives the routine, the mode and the task. `FrameKeep.start_of_sim` gives the rest from `endOK(S)`.

## The check

| rows | rows | states | states that know the castle flag is down | states with control | of these as `rowCtl` asks |
|---|---|---|---|---|---|
| pause flag 0 | 123 | 2,152 | 2,150 | 2 | 2 |
| pause flag not 0 | 123 | 1,022 | 1,020 | 2 | 2 |

The 4 states with control know the routine (control), the mode, the task and the castle flag (0). They are in the idle loop with `S = S₀`, in one of the two windows of the dot, with bit 7 of `ppuCtrl` known to be 1 and the strobe off. The two states of each case that do not know the castle flag are in the first row, at the exit. The check takes 3.2 s in a program and 4.4 s in the private build (`Proof.ControlStart`).

## On real runs

`ctl-start-check FM2`, after the last change (exit 0, bad 0):

* The movie: control above ground after frame 1046 of the movie. The machine there is `FrameStart_K`, with the castle flag down.
* 44 real entries (the reference, the movie's, and 42 walks into the pipe), each with no input, random inputs without Start, and Start on the first 80 frames: 132 runs, all reach control, and every machine at control is `FrameStart_K` with the castle flag down.

## Hypotheses (not proved in Lean)

None of its own. `Run.atCtl₀` uses the conditions of the change that `Run.start` uses: the fields of `chg` (the entry, no Start, the sound at the exit, the time at the exit, the first control). They are listed on [the route page](0-1-Route.md).

What stops being a hypothesis: `noCastle` of `PoleJoin.Run`, and `keep.start` of `FrameKeep.Frames`. What is new: the check `ctlCheck` on the ROM, and in `keep` the fields `ctl` (each frame before the touch ends in control; later only its routine and task, and now a theorem: the hypothesis in its place is `noStore`, no frame before the touch writes the routine, the mode or the task by its address, [One whole frame in control](f-6-19-FrameKeep.md)) and `lagStart`. Later `lagStart` went again: `keep` now lists every frame, counted or not, and the walk covers the `lag` frames too ([One whole frame in control keeps the castle flag and the fraction's low bits](f-6-19-FrameKeep.md)).

**Files.** `Theorems/ControlStart.lean`, `Theorems/Route.lean` (`Run.atCtl₀`), private `Proof/ControlStart.lean` (`side_ctl`).

**To reproduce.**
```
.lake/build/bin/smbrta ctl-start-check FM2       # the check, the rows and real runs (about 20 s)
```
