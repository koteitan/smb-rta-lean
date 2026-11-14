[← Back](README.md) | [English](b-3-7-3-EntryPause.md) | [Japanese](b-3-7-3-EntryPause-ja.md)

# The pause at the vertical pipe's entry, from the title

**Claim.** Suppose that Start is pressed on the title as `TitleStart` says, and that every instruction of the frames from control to the vertical pipe's entry is `Clean` for the guard of [the state at the entry](b-3-4-EntryKeep.md). The guard's list now has the six bytes of the pause too. Then at the entry the pause is silent, or the unpause sound plays with the pause timer one more than its counter, or the unpause was pressed on that frame (`PauseV`). Start may be pressed on any of these frames. This is proved, with two checks on the ROM. So the field `chg.pause₁` is gone (item 1-1-b-3-7-3). `upClean₁` now also asks that a store through an index or a pointer does not touch the six bytes. On real frames no such store touches them.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `trace(m, i, j)` the machine `j` steps into it. `seq n` is the machine when frame `n` begins, and `a` is `a₁`, the machine after the entry frame. `FrameStart`, `Watched(kept, m)`, `Clean_G`, `Rest`, `rt(m)` and `Begin` are those of [the state at the entry](b-3-4-EntryKeep.md). The six bytes `q`, `b`, `f`, `c`, `t`, `g` (the queue, the buffer, the flag and the counter of the pause sound, the pause timer, the pause byte), the 88 classes `classesV` and `PauseV` are those of [the pause through the vertical pipe's frames](b-3-7-2-PipePause.md). `SIn(t, m)` says that the bytes of `m` are as the class `t` says.

```
InCls(m)  :=  ∃ t ∈ classesV,  SIn(t, m)
```

## The statement

```
Begin.pauseClass :  Begin(seq, inp)  →  InCls(seq 1)                                                  (check nearPauseCheck)
pause_frame      :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j))) ∧ InCls(m)
                      →  InCls(frame(m, i))  ∧  ( rt(frame(m, i)) = pipe  →  frame(m, i)[g] & 1 = 0 )     (check pauseCheck)
class_up         :  ∀ n, 1 ≤ n ≤ a  →  InCls(seq n)                                                   (induction)
pauseV_of_class  :  t ∈ classesV ∧ SIn(t, m) ∧ m[g] & 1 = 0  →  PauseV(m)                             (no ROM; L + 1 < 256)
pause_entry      :  2 ≤ a ∧ rt(seq a) = pipe  →  PauseV(seq a)
entryV_of_title  :  the hypotheses of entry_of_title  →  Entry(seq a) ∧ PauseV(seq a)                (EntryV)
```

`class_up` and `pause_entry` take, for `1 ≤ n < a`, `FrameStart(seq n)`, `Watched(kept, seq n)` and `Clean_G` on frame `n` (from `starts_of_title` and `watched_up`, as `entry_of_title`). `L` is the length of the pause sound.

In the route, `Run.entry₁` now gives `EntryV` (`Entry ∧ PauseV`) from the same hypotheses as before, and `ChangesK.run₁` takes the pause from it:

```
chg.pause₁   :  PauseV(seq a₁)                                                     (gone: Run.entry₁)
chg.upClean₁ :  1 ≤ n < a₁  →  ∀ j, Clean_G(trace(seq n, inp n, j))               (G now also protects the six bytes)
```

The theorems of `Route` that took `Entry(seq a₁)` take `EntryV(seq a₁)`. `HurryStart.Chg₁` has no field `pause₁` either.

## How it works

**Frame 0.** Frame 0 begins in a near or held state of `TitleStart`. These 10 states know the six bytes: the press condition knows the pause byte and the pause sound's buffer, and the game writes the others with known values before frame 0. `nearPauseCheck` walks frame 0 from them with any input, Start included (`TitleStart.frame0Check`), and asks at each end with control that the state knows the six bytes as one of the classes says. There are 40 such ends: 16 silent, 16 with the unpause sound, 8 with the unpause pressed.

**One frame from control.** The walk is that of [the state at the entry](b-3-4-EntryKeep.md), with the class carried beside it, as on [the pipe's frames](b-3-7-2-PipePause.md) (`vsuccs`):

* at the call of the sound routine in the frame's interrupt, the state is split into one piece for each class that agrees with it;
* in the region (the sound routine, the reading of the pads, the pause routine) every step is the step of the walk; at the call of the pause routine the state is split by bit 7 of `g`; at the return the six bytes must be in a class, and they are forgotten, but for bits 0 to 6 of `g`;
* outside the region every step must keep the six bytes: its store does not reach them (`StepWrites.keepOK`), or, for each class that agrees with the state, every step of the state with the bytes of the class still knows them as the class says (`outOK`). The second case is a store through an index or a pointer with a target not known: such a step forgets every byte but those of the guard, and the six bytes are now in the guard. So the proof needs only that the walk's step follows the machine (`FrameKeep.s_kstep`);
* the frame's end is outside the region and meets the end of `EntryKeep`'s walk; if the routine there is the pipe's, the state knows that bit 0 of `g` is 0 (`finV`).

`Ph(A, m) := inR(A) ∨ InCls(m)` holds for each state `A` of the walk that covers the machine `m` (`s_vsuccs`). At the frame's end the state is outside the region, so `InCls` holds there (`frame_of_walkV`).

**Why the frame of the entry is not paused.** The pause routine runs before the game's routine in the same frame. If it pauses, the frame skips the game's routine, so the routine byte does not change. The frame that enters the pipe ran the player's routine, which wrote the pipe's routine. The walk knows this because it keeps bit 0 of `g` after the region.

**At the entry.** The class at `seq a` has bit 0 of `g` clear. Such a class is silent, or the unpause sound with the counter from 1 to `L − 1`, or the unpause pressed. These are the three kinds of `PauseV` (`pauseV_of_class`).

**Why the classes of the vertical pipe.** `PauseV` asks that the flag is 0 when silent, and that the counter of the unpause sound is below `L`. The 90 classes of [the side pipe](d-3-4-3-SidePause.md) do not know the flag when silent, and allow the counter `L`. The 88 classes of the vertical pipe say both.

**The guard.** `EntryKeep.guardOf` lists the six bytes among the bytes that a store with a target not known does not touch (`pauseSix`). The walk of `EntryKeep` hardly changes: its table has 53,438 states (53,437 before), and `keepCheck` takes 4.8 s in a program.

**The size of the check.** 88 classes. In a program the search has 2,131,805 steps, 201,762 forks, 0 failures and a table of 95,044 states (11 to 13 s); `pauseCheck` takes 14 to 16 s with the search, `nearPauseCheck` about 1.8 s. This is more than a few seconds. The private build of `Proof/EntryKeep.lean` takes 28 to 35 s (about 7 s before). The checks are `entry_pause` and `entry_pause_near` in the private `Proof/EntryKeep.lean`, and `EntryKeep.Checks` has two new fields (`pauseNear`, `pause`).

## Measured

`entry-keep-check FM2` with the new guard (exit 0): no store through an index or a pointer touches a byte of the guard on the TAS from control to the entry (368 frames), the reference entry (440 frames), 300 runs of random inputs from control (127,841 frames, 5,390 of them paused), 300 runs of random inputs from frames of the TAS (75,241 frames, 4,746 paused), and the reference with 0 to 39 frames of standing (17,600 frames).

`title-pause-near` (exit 0): the 8 near and 2 held states of `TitleStart` know `q`, `b`, `f`, `t` and `g`; `c` in some. The 40 ends of frame 0 with control know all six bytes, but `c` in the 16 silent ends, where the class does not ask it.

## Assumptions (not proved in Lean)

* `upClean₁`: each instruction of the frames from control to the entry is `Clean`. A store through an index or a pointer now does not touch the six bytes of the pause either.
* `entryRest₁`: `Rest` at the entry, now 55 bytes: bits 1 to 6 of the pause byte left it in this round, because the frames from control keep them ([1-1-b-3-4](b-3-4-EntryKeep.md)).

**Files.** `Theorems/EntryKeep.lean` (`pauseSix`, `guardOf`, `outOK`, `vsuccs`, `coverV`, `walkV`, `keyV`, `routeV`, `runV`, `searchV`, `finV`, `cfgV`, `pauseCheck`, `nearPauseCheck`, `Checks`, `tab_of`, `keep_of_outOK`, `s_vsuccs`, `LiveV`, `cover_liveV`, `live_stepV`, `frame_of_walkV`, `PauseOK`, `pauseOK_of_check`, `pause_frame`, `low7_all`, `low7_cases`, `pauseV_of_class`, `Begin.pauseClass`, `class_up`, `pause_entry`, `entryV_of_title`), `Theorems/PipeChangeEnd.lean` (`EntryV`), `Theorems/Route.lean` (`ChangesK.run₁`, `Run.entry₁`), `Theorems/HurryStart.lean` (`Chg₁`). The private checks are `entry_pause_near` and `entry_pause` in `Proof/EntryKeep.lean`. There is no game data in the public files.

**To reproduce.**
```
.lake/build/bin/smbrta entry-pause-check     # the search, pauseCheck and nearPauseCheck, about 50 s
.lake/build/bin/smbrta title-pause-near      # what frame 0 knows of the six bytes, about 2 s
.lake/build/bin/smbrta entry-walk-check      # the walk of EntryKeep and frame 0, about 30 s
.lake/build/bin/smbrta entry-keep-check FM2  # the stores on real frames, about 4 min
```
