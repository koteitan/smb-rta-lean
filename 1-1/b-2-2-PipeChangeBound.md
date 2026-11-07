[← Back](README.md) | [English](b-2-2-PipeChangeBound.md) | [Japanese](b-2-2-PipeChangeBound-ja.md)

# A lower bound for the change into the room, from single frames

**Claim.** This is a partial result. Assume that a number `left` falls by at most one on each frame of a run. Then the run has no control on the first 90 frames after the entry, for any inputs. `left` is computed from a few bytes. That it falls by at most one is not proved for every state. It is a hypothesis on single frames, in place of the hypothesis on the whole change.

`m₀`, `run`, `ctl`, `0^k` and `E` are those of [What decides the length of the change](b-2-1-PipeTransitionAll.md). `w[..j]` is the first `j` inputs of `w`.

**The number `left`.** While the pipe's routine runs in the game core, `left(m) = timer(m) + 43`. Otherwise `left(m)` comes from a table with 43 rows, made by running `E` with no input from frame 48 to frame 90. Each row is a key and the frames left: frame `48 + i` has `43 - i`. The key is `OperMode_Task`, `ScreenRoutineTask`, `GameEngineSubroutine`, `DisableScreenFlag`. In the game core it also has `Player_State` and the position, fraction and speed of the vertical movement. A key that is not in the table has `left = 0`.

```
EntryCond(M)  :  routine(M) = the pipe's routine  ∧  task(M) = game core  ∧  48 ≤ timer(M)

fall(M, w)    :  ∀ j < |w| :  left(run(M, w[..j])) ≤ left(run(M, w[..j+1])) + 1

no_control_entry :  ∀ M, EntryCond(M) → ∀ w, fall(M, w) → ∀ j ≤ |w|, j < 91 → ¬ctl(run(M, w[..j]))
left_zero_of_ctl :  ctl(m) → left(m) = 0                                  (the table has no state of control: checked)
entries_ok       :  ∀ m ∈ {E, 13 real entries} :  left(m) = 91  ∧  ∀ j < 91, ¬ctl(run(m, 0^j))     (fall checked on each frame)
Change.bound     :  E ≤ C  ∧  (∀ j, E ≤ j < C → left(f j) ≤ left(f (j+1)) + 1)  ∧  91 ≤ left(f E)  ∧  left(f C) = 0  →  E + 91 ≤ C
```

All other bytes in `EntryCond` are free. Only `fall` says something about them.

Lean: `Theorems/PipeChangeBound.lean` (`low_of_fall`, `no_ctl_of_fall`, `change_ge`, `no_control`, `no_control_entry`, `left_zero_of_ctl`, `entries_ok`, `Change`, `Change.bound`), private `pipe_bound_checks` (`native_decide`), `pipe_bound_keys`, `pipe_bound_entries`, `pipe_no_control`. The theorems without ROM use only `propext` and `Quot.sound`.

## How it works

A frame that takes longer keeps `left`, so it only delays control. So do a pause and a handler that never ends. Control is possible only at `left = 0`, and `left` starts at 91. So 91 frames must pass. This is a formula, not a search. The private check takes about 3 s.

## Measured, not a theorem

A program runs real frames: the reference entry, the TAS entry, the 13 real entries and the entries of 60 random runs, 75 entries in all, each with no input, random inputs without Start, random inputs, and Start held. In all, 140,160 frames.

* `left` never falls by more than one. Control only comes at `left = 0`. `left` is 91 at each entry.
* The shortest change is 91 frames. Random inputs with Start give 181 to 199 frames. With Start held there is no control in 1,500 frames.
* The 77 listed entries of the earlier page, overwritten ones included, have no bad frame.
* Six objects close together: 92 to 96 frames, no bad frame.
* The music state that stops the game, from frame 48: no control in 400 frames, no bad frame.

Overwritten states where `fall` fails: `HalfwayPage ≠ 0` (control after 75 frames), `WarpZoneControl ≠ 0` and `GameTimerExpiredFlag ≠ 0` (228 and 229 frames, `left` drops on the way), game timer 000 (`left` drops at frame 331, no control). So `fall` does not hold for every state with `EntryCond`. It must be a statement about real runs.

## An abstract run was tried, and it did not close

An abstract machine with the pad not known, reads and writes at intervals, frames that end anywhere, the timer free and sets of values per object slot was run on one frame of the pipe's routine. It did not close: with the enemy bytes free, more than 300,000 abstract states and hundreds of failures. From frame 48 with the music state free: more than 2,000,000 states after 8,000,000 steps, growing with each frame. The causes are the level parser that runs while the screen goes on scrolling during the pipe, the status bar and VRAM buffer offsets, and the music engine. No part of this is in the theorem.

## Assumptions (not proved in Lean)

* `fall` on the frames of a run. This is the main assumption. It replaces (H1), (H2), (H3) and (H4) of the earlier page by a statement on single frames.
* Frames in `Change` must be counted as `pipe.E` and `room.C` are counted.
* Random runs did not take a power-up. Big Mario was run only as an overwritten state.

**Files.** `Theorems/PipeChangeBound.lean`, private `Proof/PipeChangeBound.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-bound-check FM2    # left on real frames, about 4 s
```
