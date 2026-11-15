[← Back](README.md) | [English](0-5-2-1-1-PhaseFrame.md) | [Japanese](0-5-2-1-1-PhaseFrame-ja.md)

# One frame in control keeps the phase exactly when it ends paused

**Claim.** Take a frame that starts in the idle loop in control (`StartK`), with the master timer control 0 and the phase at most 20, and whose instructions all meet `CleanK` of `guardPh`. Then either it ends paused with the phase it began with, or it ends not paused with the phase `(p + 20) % 21`. This is the clock's rule of the phase. A frame before the touch's frame also keeps the master timer control 0. So every frame of `pole.keep` up to the touch's frame follows this rule.

The phase is the interval timer's control (`IntervalTimerControl`). It is the `phase` of the clock (`CastleToLevel.Frames.ph`).

## Why

The NMI runs the screen, the sound, the pad and the pause routine. Then it reads the low bit of the pause byte. If the bit is 1, it skips the timers. If it is 0 and the master timer control (`TimerControl`) is 0, it runs `DecTimers`: it decrements the phase, and from 0 it sets it to the top of the cycle. Then come the timers' loop and the mode's routine. No other instruction writes the phase by its address. A store through an index or a pointer is the condition `KeepsPhase` on each instruction.

Three pieces of the abstract machine of `TaintRun` follow the frame.

* Walk `A` goes from the frame's start to the first instruction of `DecTimers` (the cut). The phase is followed as the counter of `TaintRun`: the walk fails on any write to it. The low bit of the pause byte and the master timer control (0) start known. A path that does not come to the cut is a paused frame. It goes on to the frame's end, and there the phase must still be followed and the low bit must be known to be 1.
* At the cut the phase is split into its 21 values. From each value `p`, the timer's code goes to the timers' loop (the target of the `BPL`). There the phase must be known to be `(p + 20) % 21`.
* Walk `B` goes from the timers' loop to the frame's end. The phase is followed again, from its new value. At the end the phase must still be followed and the low bit of the pause byte must be known to be 0.

The master timer control: the game writes it by its address when it frees the timers (0), when it halts them for a change of the player's state (right after a store of the routine byte), and in the NMI when it is not 0. The walk of `FrameKeep` with the stores of the three bytes of control cut (`FrameKeep.Frames.noStore`) keeps it 0, with one more watched byte (`tcCheck`).

## The theorems

`m` is a machine when a frame begins, `frame(m, i)` the machine when it ends. `trace(m, i, j)` is the machine after `j` instructions.

```
φ(m)      :=  the phase of m: the byte that the DEC of DecTimers decrements           (PhaseFrame.phaseI)
tc(m)     :=  the master timer control of m                                          (PhaseFrame.tcI)
U(m)      :=  the low bit of the pause byte of m is 0                                (FrameKeep.Unpaused)
next(p)   :=  (p + 20) % 21                                                          (the clock's rule, CastleToLevel.Step)

PhaseRule(m, m')  :=  ( ¬U(m') ∧ φ(m') = φ(m) )  ∨  ( U(m') ∧ φ(m') = next(φ(m)) )

KeepsPhase(m)     :=  every store of m through an index or a pointer to RAM writes neither φ nor tc
guardPh           :=  FrameKeep.guardE with φ and tc protected;   CleanK(guardE) ∧ KeepsPhase  ⟹  CleanK(guardPh)      (cleanPh_of)

phase_frame  :  phaseCheck,  StartK(m),  tc(m) = 0,  φ(m) ≤ 20,  ∀ j, CleanK(guardPh, trace(m, i, j))
                ⟹  PhaseRule(m, frame(m, i))
tc_frame     :  tcCheck,  StartK(m),  Watched(m),  tc(m) = 0,  ∀ j, CleanK(guardPh, trace(m, i, j)),  ∀ j, no store of control by address
                ⟹  tc(frame(m, i)) = 0
frames_phase :  keepCheckOf, phaseCheck, tcCheck,  K a FrameKeep.Frames from frame a,  StartK(seq 0),  Watched(seq 0),  tc(S.seq a) = 0,  φ(S.seq a) ≤ 20,
                ∀ n < ix(g), ∀ j,  KeepsPhase(trace(S.seq(a + n), S.inp(a + n), j))
                ⟹  ∀ n < ix(g),  tc(S.seq(a + n)) = 0  ∧  φ(S.seq(a + n)) ≤ 20  ∧  PhaseRule(S.seq(a + n), S.seq(a + n + 1))
```

`ix(g)` is the end of the touch's frame: frames `a` to `a + ix(g) − 1` are the frames of `FrameKeep.Frames`. `frames_phase` is an induction on `n`. Each frame starts in control by `Frames.all_start`. `cleanE` and `KeepsPhase` give `CleanK(guardPh)`. `tc_frame` carries `tc = 0` to the next frame (with `noStore`), and `PhaseRule` keeps `φ ≤ 20`.

All are in `Theorems/PhaseFrame.lean`. The private proof (`Proof/PhaseFrame.lean`) checks `phaseCheck` and `tcCheck` on the ROM with `native_decide`, and that `φ` is `IntervalTimerControl` of the names of the title (`Route.PhaseName`).

## The walks

| piece | starts | states of the table |
|---|---|---|
| walk `A`, to `DecTimers` | 4 (the low bit 0 or 1, early or late in the frame) | 15,554; 12 states at the cut |
| the timer's code | 12 × 21 | none |
| walk `B`, from the timers' loop | 252 | 45,392 (38,386 before `guardE` protected the collision bits) |
| the walk of `tcCheck` | 2 | a search of `FrameKeep` |

Natively `phaseCheck` takes 3.1 s with its searches, and `tcCheck` 0.3 s. `Proof.PhaseFrame` builds in about 4 s.

## On real runs

`phase-frames-check FM2` runs from the machine when frame `b₂` begins to the castle entry. On each frame up to the touch's frame (the player's routine when the frame begins) it checks `KeepsPhase` on each instruction, `tc = 0` when the frame begins, and `PhaseRule`. After the touch's frame it checks `PhaseRule` on the runs that reach the castle.

| run | runs | castle entries | frames up to the touch's frame (ending paused) | instructions | frames after it to the castle (ending paused) | fails |
|---|---|---|---|---|---|---|
| the movie | 1 | 1 | 240 (0) | 1,203,506 | 126 (0) | 0 |
| a pause of 45 or 61 frames at every second frame from `b₂` to the castle | 368 | 368 | 101,040 (12,720) | 466,482,861 | 53,046 (6,678) | 0 |
| random inputs, Start at random, from the movie's frames `b₂` to `b₂ + 199` | 100 | 19 | 58,172 (20,105) | 217,296,349 | 17,823 (6,229) | 0 |

"fails" counts the failures of `KeepsPhase`, of `tc = 0`, of `φ ≤ 20` at control, and of `PhaseRule` before and after the touch's frame. At control `φ` is at most 20 on every run.

On the 81 random runs without a castle entry, 4,650 frames after he leaves control (a death) do not follow `PhaseRule`, and on 7,989 such frames `tc` is not 0 when the frame begins. These runs are not runs of `Route.Run`, and nothing is asked of these frames.

The movie, with the kinds of the clock read from the machine (`CastleToLevel.kindOf`) from frame 0 on and the phase of `read₀`: the phase of the clock is the machine's on all 1,219 frames up to the castle entry.

## What is not proved

* `KeepsPhase` on each instruction. It is measured above.
* `tc = 0` at control above ground (`b₂`): one state, measured.
* The frames after the touch's frame up to the castle entry. The routine is not the player's there, and no walk follows those frames. `PhaseRule` on them is the hypothesis `hA` of `Run.lagUp_of` ([the castle join](0-5-2-1-CastleJoin.md)), measured above.
* The tie of the clock: its phase is the machine's on each frame above ground (`Run.PhaseUp`). See [the castle join](0-5-2-1-CastleJoin.md).

**Files.** `Theorems/PhaseFrame.lean` (`phaseCheck`, `tcCheck`, `KeepsPhase`, `PhaseRule`, `phase_frame`, `tc_frame`, `frames_phase`).

**To reproduce.**
```
.lake/build/bin/smbrta phase-frame-check            # the searches and the two checks, as a program (about 7 s)
.lake/build/bin/smbrta phase-frames-check FM2       # the conditions on real runs (about 115 s)
cd ../proof && leanman build Proof.PhaseFrame        # the checks on the ROM, natively (about 5 s)
```
