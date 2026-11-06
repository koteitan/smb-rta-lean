[← Back](../README.md) | [English](PipeTransition.md) | [Japanese](PipeTransition-ja.md)

# The change into the bonus room

**Statement.** From the frame Mario enters the vertical pipe, control in the bonus room comes exactly 91 frames
later. For one entry state from a real run this is shown for every input on every frame, with Start and Select
left out, under one hypothesis (`Merge`). For other entry states it is shown with no input, without a hypothesis.

`m₀` is the machine at the start of 1-1. `run(m, w)` is the machine after the real frames with the inputs `w`.
`ctl(m)` is `controllable`. `0^k` is `k` frames of no input. `I` is the 64 inputs: every subset of A, B, Up, Down,
Left, Right, opposite directions included. `E = run(m₀, witness)` is the machine at the end of the entry frame.
`S` is the machine of a real run in which Mario stands in the pipe's window. `D` is Down alone.

```
entered     :  ctl(run(m₀, witness without its last frame))  ∧  the pipe routine is set after the last frame
allInputs   :  Merge  →  ∀ w ∈ I^91 :  ctl(run(E, w))  ∧  ∀ k, 1 ≤ k < 91 → ¬ctl(run(E, w[..k]))
noInput     :  ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(E, 0^k)) ↔ k = 91 )
otherMoved  :  ∀ c ∈ moved :  ( ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(c(E), 0^k)) ↔ k = 91 ) )
                              ∧  key(run(c(E), 0^91)) = key(run(E, 0^91))
otherBig    :  ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(big(E), 0^k)) ↔ k = 91 )
stand       :  ∀ d < 21 :  D enters the pipe on run(S, 0^d),  and with E_d = that frame's end,
                           ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(E_d, 0^k)) ↔ k = 91 )
```

| entry state | inputs during the change | result | hypothesis |
|---|---|---|---|
| `E`: a real run, at top speed, entering on the landing frame | all of `I`, on every frame | control on frame 91, not before | `Merge` |
| `E` | none | control on frame 91, not before | none |
| `E` overwritten (`moved`): each of the 9 pixels of the window; speed 0, half and full top speed both ways, with the moving direction, the facing and the stored absolute speed; the position fraction; the speed fraction; the running speed; the running timer | none | control on frame 91, not before; the same `key` on that frame | none |
| `E` overwritten: a big Mario | none | control on frame 91, not before | none |
| real runs, standing in the window: the entry on 21 consecutive frames, so at every place of the 21-frame grid | none | control on frame 91, not before | none |

`key` is the RAM without `SavedJoypadBits` and without the bits of `JoypadBitMask` other than Start and Select, with every other
field of the machine except `pad` and the ROM. Equal `key` gives equal `ramKey`.

Lean: `Theorems/PipeTransition.lean` (`Statement`, `statement_of_check`, `first_control`, `chain_spec`), private
`pipe_checks` (by `native_decide`) and `pipe_transition`.

## How

`chain` follows no input from the entry. On each frame it runs every input of the set, and compares each result with
the result of no input by `key`. It also checks that the state after no input is controllable only on the last frame. This is
about 10,000 frames of the emulator.

`chain_spec` turns the check into statements about `run(E, 0^k)`, by induction. Nothing is assumed there, so `noInput`,
`otherMoved`, `otherBig` and `stand` need no hypothesis.

For an arbitrary `w`, `key_of_chain` gives `key(run(E, w)) = key(run(E, 0^|w|))` by induction on the length, with `Merge` in the
step. `key` contains `ctl`, so `first_control` follows.

## Assumptions (not proved in Lean)

* `Merge`: two states reached from `E` after the same number of frames, with equal `key`, go on to equal `key` under the same input.
  Such states differ only in `SavedJoypadBits`, in the bits of `JoypadBitMask` other than Start and Select, and in `pad`. What
  supports it, without proving it: the disassembly reads `JoypadBitMask` in one place, masked to those two bits; `runFrame` overwrites
  `pad`; and an emulator run with access tracking, with no input and with all buttons, found `SavedJoypadBits` not read before it is written on any
  of the 91 frames. Measured: over the 64 inputs only these two bytes of RAM ever differ, and the other fields of the machine never do.
* Only these entry states are covered. The theorem does not say that every entry state reached by any run behaves the same: positions of
  enemies, the scroll and the timers differ from run to run, and only the runs above were executed. An emulator run from the TAS's own state, which is not part of the
  proof, gives the same 91 frames.
* All inputs were run only from `E`. The other entry states ran with no input.
* The overwritten entry states are not shown reachable as they are: bytes are written directly into `E`.
* Start and Select are not in `I`. Start pauses, which only lengthens: this is read from the code. An emulator run, not part of the proof, pressed
  Start once on each frame from 41 on: on some frames of the area change the press was ignored and control still came on frame 91; on the others the game stayed paused. With a second
  press 45 frames later, control came 45 frames late.
  Select on one frame, tried on each of the 91 frames, changed nothing.
* The window's 9 pixels in `moved` are computed from a foot's offset. That Down enters exactly there is an emulator run, and belongs to the entry condition, not to this theorem.
* Frames are the emulator's frames. The emulator was checked as on [Emulator](../docs/emulator.md); it is not proved equal to a real console.

**Files.** `Theorems/PipeTransition.lean`, private `Proof/PipeTransition.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-change-check     # the whole check as a program (prints true and the time)
```
