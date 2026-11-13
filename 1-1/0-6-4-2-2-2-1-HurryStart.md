[← Back](README.md) | [English](0-6-4-2-2-2-1-HurryStart.md) | [Japanese](0-6-4-2-2-2-1-HurryStart-ja.md)

# The last frame of a change, as the walk of the hurry-up music needs it

**Claim.** On a real run of either change of area, the last frame of the change (the frame just before the first control) begins as [the walk of the frame that starts the hurry-up music](0-6-4-2-1-HurryFrame.md) needs it (`HurryFrame.Start`): in the idle loop, in the routine of the entrance, in the game's mode and its core, with the six bytes of `DigitModifier` 0. The conditions are exactly those of the changes in [the whole of 1-1](0-1-Route.md), as `Route.Run` asks them (`Route.ChangesK`).

So in [runs with the hurry-up music](0-6-4-HurryMusic.md) the start of frame `b` is no longer a hypothesis when `b` is the last frame of a change. It comes from the rows of the change.

## Why the last frame

On the last frame of a change the routine of the entrance ends and the routine of control runs in the same frame. Then the timer routine runs. The area's setup has cleared the timer's sub-counter, so the timer ticks on this frame. If the timer shows 100, the music starts on this frame. So the frames before the music begin with this frame, not with the first frame in control.

## The theorem

`seq` are the machines of the change (`PipeChangeEnd.PipeRunK` for the first change, `SidePause.EndRunQ` for the second), `a` the entry, `b` the first control. `left(m)` is the number of frames left in the change (`left₁`, `left₂` of the route).

The rows of both changes are the rows that `route_1_1` uses. They carry the sound's bytes in tables. The rows of the first change are `PipeChangeEnd.rowsKc` ([rows with the sound's bytes in tables](b-3-7-1-SoundRows.md)): the condition at the vertical pipe's exit is `QuietP` (the pause sound silent with the song in a row, or the unpause sound playing) and the game timer not 000 (`TimerOK`). The rows of the second change are those of [`SideChangeSound`](d-3-4-2-SideChangeSound.md): the condition at the side pipe's exit is `QuietK` (the pause sound silent, the unpause sound playing, or the unpause pressed on the frame of the exit).

```
rowE(S)        :=  endOK(S)  ∧  DigitModifier known 0 in S  ∧  routine = entrance,  mode = game,  task = core  (known in S)
rowsE(rows)    :=  ∀ row,  statesOK(row)  ∧  (v(row) = 1  ⟹  ∀ S ∈ row,  rowE(S))
rowsCheck₁     :  rowsE(rowsKc)  ∧  the exit's reference not in the game core  ∧  the same program                (hurry_rows₁, native_decide)
rowsCheck₂     :  rowsE(the rows of SideChangeSound)  ∧  the same program                                       (hurry_rows₂, native_decide)

start_of_left       :  rowsE(l),  InvL(l, m),  left(m) = 1   ⟹   HurryFrame.Start(m)
PipeRunK.last       :  EndStatement,  PipeRunK,  exitOff,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n))   ⟹   a + 1 ≤ b  ∧  InvL(rowsKc, seq (b − 1))  ∧  left(seq (b − 1)) = 1
PipeRunK.startLast  :  EndStatement,  PipeRunK,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n)),  rowsCheck₁   ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
EndRunQ.startLast   :  Statement,  EndStatementK,  PipeQ,  EndRunQ,  (∀ n,  a ≤ n < b  ⟹  ¬ ctl(seq n)),  rowsCheck₂   ⟹   a + 1 ≤ b  ∧  HurryFrame.Start(seq (b − 1))
chg₁_of_changes     :  Route.ChangesK   ⟹   Chg₁
Chg₁.startLast      :  the checks,  Begin,  Chg₁            ⟹   a₁ + 1 ≤ b₁  ∧  HurryFrame.Start(base.seq (b₁ − 1))
changes_startLast   :  the checks,  Begin,  Route.ChangesK  ⟹   a₂ + 1 ≤ b₂  ∧  HurryFrame.Start(base.seq (b₂ − 1))
```

`v(row)` is the value of `left` on the states of a row. `InvL(l, m)` says that a state of a row of `l` covers `m`. `ctl(m)` says that `m` has control.

The proof of `PipeRunK.startLast` (the first three steps are `PipeRunK.last`, the last step is `start_of_left`):

* Each machine from `a` to `b` is in the pipe or in the rows with tables (`PipeChangeEnd.PipeRunK.way`), and `left ≠ 0` before `b` (`PipeChangeEnd.PipeRunK.first`). Both hold because `b` is the first control after the entry.
* The machine `seq (b − 1)` is not in the pipe. From the pipe, one frame ends in the pipe (`left ≠ 0` there, but `left(seq b) = 0` since `seq b` has control), or at the exit, whose bytes say "not in the game core" (`exitOff`), so not with control.
* So `seq (b − 1)` is in the rows, and one frame of the rows takes at most 1 off `left`: `left(seq (b − 1)) ≤ left(seq b) + 1 = 1`. With `left ≠ 0`, `left(seq (b − 1)) = 1`.
* A state that covers `seq (b − 1)` is in a row with `v = 1` (`left_of_covered`). `rowsE` says it is as `rowE` asks. So `seq (b − 1)` is in the idle loop, with the bytes of the guard of the entrance and `DigitModifier` 0 (`start_of_rowE`, `known_E`).

For the second change the first three steps are `SidePause.EndRunQ.last`: the machine `seq (b − 1)` is in the rows of `SideChangeSound` with `left` 1. `EndRunQ.startLast` then applies `start_of_left` to these rows.

On the frames of `Route.Base`: `Chg₁.startLast` builds the `PipeRunK` of the first change from `Chg₁` (`Chg₁.run₁`, as `Route.ChangesK.run₁`), with the condition at the entry from the press of Start on the title (`Chg₁.entry`, as `Route.Run.entry₁`). `b₁` is the first control after the entry by its choice (`Chg₁.ctlFirst`). `changes_startLast` uses `Route.ChangesK.run₂`, as `Route.Run.atCtl₀` does, and `b₂` is the first control after the entry by its choice (`ChangesBase.ctlFirst₂`).

`Chg₁` holds the fields of `Route.ChangesK` on the first change: `entryRest₁`, `upClean₁`, `ctlBy₁`, `paused₁`, `places₁`, `noStart₁`, `quiet₁`, `time₁`. Each has the same statement as the field of the same name of `Route.ChangesK`, so `Route.ChangesK` gives `Chg₁` (`chg₁_of_changes`). It is its own structure because a run whose music starts in the room fails `entry₂` of the second change (the music's bytes at the side pipe's entry).

## The check

The states of the rows (the rows `rowsKc` of the first change, the rows of `SideChangeSound` of the second; `hurry-rows-check FM2`):

| rows | rows | states with `left` 1 | of these as `rowE` asks |
|---|---|---|---|
| first change, `rowsKc` | 44 | 2 | 2 |
| second change, rows of `SideChangeSound` | 123 | 2 | 2 |

The states with control (`left` 0) also know `DigitModifier` 0 and `endOK` (4 in each change). Every state of the rows in the routine of the entrance does too: 34 in the first change, 192 in the second. The change clears these bytes when it sets up the area. The rows with tables forget the sound's bytes, and `rowE` reads none of them.

The check takes 26 s (`rowsCheck₁`) and 19 s (`rowsCheck₂`) in a program. Each builds the rows of its change again: 24 s of the 26 s for `rowsKc`, 15 s of the 19 s for the rows of `SideChangeSound`. `route_1_1` builds them once more in its own checks (`pipe_end`, `side_sound_checks`). Before, `rowsCheck₁` read the rows `rowsA` and `rowsB` (2.7 s), whose condition at the exit is stronger. The private `Proof/HurryMusic.lean` builds in 55 s with these two checks and `hurry_near_check` (27 to 36 s before).

## On real frames

* The movie: each of the frames 652 and 1045 of the movie (from power on) begins in the routine of the entrance and ends with control. Each begins as `HurryFrame.Start` asks, with `DigitModifier` 0 (`hurry-rows-check`).
* `hurry-check FM2`: of the 108 first frames that start the music, 58 come after a change. Frame `b` there is the frame after the last frame that ends without control, so the last frame of the change, and it begins as `HurryFrame.Start` asks in all 58.

## Hypotheses (not proved in Lean)

None of its own. It uses the conditions of the changes, as `Route.Run` does: `Chg₁` (the fields of `Route.ChangesK` on the first change) for the first change, `Route.ChangesK` for both. They are listed on [the route page](0-1-Route.md).

What stops being a hypothesis: the state at frame `b` in the field `start` of `HurryMusic.Run`, when `b` is the last frame of a change. What is new: the checks `rowsCheck₁` and `rowsCheck₂` on the ROM, and the conditions of the changes in `start`. These are now exactly those of `Route.ChangesK`, which `Route.Run` asks. At the side pipe's exit `QuietK` in place of `Quiet`, so a run with Start pressed on the frames of the side pipe is covered. At the vertical pipe's exit `QuietP ∧ SongAt(xshape)` in place of `Quiet ∧ SongAt(song) ∧ SongAt(xshape)`, and `TimerOK` (the game timer not 000) in place of `TimeOK` (the timer not 000 and the sound's pause flag 0), so a run with the unpause sound playing at the exit is covered.

**Files.** `Theorems/HurryStart.lean` (`PipeRunK.last`, `PipeRunK.startLast`, `Chg₁`, `chg₁_of_changes`), `Theorems/HurryMusic.lean` (`Run.startB`), private `Proof/HurryMusic.lean` (`hurry_rows₁`, `hurry_rows₂`).

**To reproduce.**
```
.lake/build/bin/smbrta hurry-rows-check FM2      # the rows of both changes, the checks, the movie's last frames of the changes (about 110 s)
```
