[← Back](../README.md) | [English](PipeTransitionAll.md) | [Japanese](PipeTransitionAll-ja.md)

# What decides the change into the bonus room

**Statement.** This is a partial result. The change takes 91 = 48 + 43 frames. In the first 48 frames the pipe's timer runs out. For the last 43 frames the length is proved for every value of every byte outside a list `R`. For the first 48 frames it is proved only on 77 listed entry states. That every entry state of every run has length 91 is a theorem only under assumptions (`every_entry`). It is false for some overwritten states, and with the game timer at 000, a state the code allows for a few frames (table below).

`m₀` is the machine at the start of 1-1. `run(m, w)` is the machine after real frames with the inputs `w`. `ctl(m)` is `controllable`. `0^k` is `k` frames of no input. `E` is the machine at the end of the entry frame of [The change into the bonus room](PipeTransition.md). `T = run(E, 0^48)`, the state when the pipe's timer has run out. `m[i]` is byte `i` of RAM.

`core(m)`: the registers, the program counter, the ROM, the PPU fields, the controller's shift state, the parities of the cycle counter and of the frame counter. Not `pad`, which a frame overwrites, and not RAM. In every `core(M) = core(...)` below, `M` also has tracking off and 2048 bytes of RAM (`SameCore`).

A *place* `v` of `T` is `T` with a dot `d ≤ 9` at the frame boundary, a cycle parity, a frame parity, and a bit of the PPU control mirror (the increment bit, set after a column of the level was written). There are 80 places.

`R` (120 bytes), `RE` (282 bytes), `Rvar ⊂ R` (81 bytes) are found by running, and `Rfix = R \ Rvar` (39 bytes). `entries` is `E`, 63 overwritten states and 13 real states (below).

```
decided     :  ∀ place v of T, ∀ M :  core(M) = core(v)  ∧  (∀ i ∈ R, M[i] = v[i])
                 →  ∀ k, 1 ≤ k ≤ 43 → ( ctl(run(M, 0^k)) ↔ k = 43 )
ends        :  the same M :  ∀ i, (i ∈ R ∨ the run from v wrote i)  →  run(M, 0^43)[i] = run(v, 0^43)[i]
atEntry     :  ∀ M :  core(M) = core(E)  ∧  (∀ i ∈ RE, M[i] = E[i])
                 →  ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(M, 0^k)) ↔ k = 91 )
entryStates :  ∀ m ∈ entries, with t = run(m, 0^48) :
                 ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(m, 0^k)) ↔ k = 91 )
                 ∃ place v of T :  core(t) = core(v)  ∧  ∀ i ∈ Rfix, t[i] = v[i]
                 ∀ M :  core(M) = core(t)  ∧  (∀ i ∈ R, M[i] = t[i])  →  ∀ k, 1 ≤ k ≤ 43 → ( ctl(run(M, 0^k)) ↔ k = 43 )
otherPage   :  3 states with the screen on another page :  ∀ k, 1 ≤ k ≤ 91 → ( ctl ↔ k = 91 )
lag         :  6 states with six objects close together :  control exactly on frame L,  L > 91
other       :  3 states with one byte set :  control exactly on frame L
died        :  the game timer at 000 :  ∀ k, 1 ≤ k ≤ 100 → ¬ctl

every_entry :  ∀ M, with t = run(M, 0^48) and v = the place of T with t's dot, parities and bit :
                 (H1) ∀ k, 1 ≤ k ≤ 48 → ¬ctl(run(M, 0^k))
                 (H2) dot(t) ≤ 9  ∧  core(t) = core(v)
                 (H3) ∀ i ∈ Rfix, t[i] = v[i]
                 (H4) ∀ k, 1 ≤ k ≤ 43 → ( ctl(run(t, 0^k)) ↔ ctl(run(t with v's values on Rvar, 0^k)) )
               →  ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(M, 0^k)) ↔ k = 91 )
```

In `decided` and `atEntry`, all bytes outside `R` or `RE` are arbitrary. `R` contains no enemy byte, no position or speed of Mario, no byte of the screen's position except `HorizontalScroll`, and no byte of the block map. So those do not change frames 49 to 91.

Results with other lengths:

| state, overwritten on `E` | frames until control |
|---|---|
| `HalfwayPage` not 0 | 75 |
| `WarpZoneControl` not 0 | 228 |
| `GameTimerExpiredFlag` not 0 | 229 |
| six goombas 0, 2, 4, 8 px apart | 93, 94, 92, 92 |
| six koopas 4 px apart | 93 |
| six hammer brothers 4 px apart | 96 |
| game timer at 000 | none: on frame 91 he dies instead (Lean up to frame 100; on the emulator the life is lost on frame 325) |

Lean: `Theorems/PipeTransitionAll.lean` (`decided_of_check`, `end_of_check`, `Statement`, `statement_of_check`, `every_entry`), private `pipe_all_checks` (by `native_decide`), `pipe_all`, `pipe_all_entries`. `decided_of_check` and `every_entry` depend only on `propext`, `Classical.choice` and `Quot.sound`.

## How

**A tracked run decides.** The emulator can record the bytes a run reads before writing them. `decided_of_check` says: if a tracked run from `ref` reads only bytes of `R`, then every machine `M` with `core(M) = core(ref)` and `ref`'s values on `R` gives the same values, the same registers and the same control on every frame, whatever its other bytes are. The proof is a simulation of the tracked machine and `M`, for each of the 256 opcodes, the NMI, the PPU timing, the controller and the DMA. The two counters may differ by an even number. No ROM is involved in this proof.

**Why the cut is at frame 48.** On frame 48 the pipe routine sets the area change and the rest of the game engine is skipped. On frame 49 the area's setup clears RAM. That clear takes longer than a frame, and it ends in frame 50, a frame with no NMI. So the objects, Mario's position and speed and the screen's position are not read after frame 48, except for `HorizontalScroll` once. Tracking shows this: from `T` the run reads 111 bytes of the 2048, and 120 over all reference runs. In the last 17 frames he falls into the room under the routine's own input.

**The check** runs on the emulator, about 14,600 frames, 5 s:

* `decided`: 80 tracked runs of 43 frames from the places of `T`.
* `entries`: for each of 77 entry states, 48 frames with no control, the comparison at frame 48, 43 tracked frames. The overwritten states: no enemies; 2 to 5 goombas at 0, 8, 24 px apart; 5 koopas; goombas and koopas; 5 goombas and a power-up; big Mario, each power; the star timer; fireballs, block objects, coins; the scroll at 4 positions; Mario's page; the scroll bytes; the frame timers at 0 and at their largest value; the master timer; the interval timer; the frame counter; the digits (all 0, all 9, score, top score, coins, game timer 999 and 001); the random bytes; sound off; 4 area musics, 3 event musics, 3 sound effects, a noise effect; several at once. The real states: standing in the window 0, 25, ..., 300 more frames, then Down.

Bytes of `Rvar`: the frame counter, the music state, `HorizontalScroll`, the master timer, Mario's size and power, the interval timer, the frame timers, the random bytes, the digits on the status line. Bytes of `Rfix`: the routine, the mode and task bytes, the pause bytes, the sound effect buffers and queues, the area pointer bytes, `AltEntranceControl`, the level and world numbers, the flags of a new timer, of the time-up and of the halfway page, the screen and PPU mirrors, the joypad masks. They do not differ in any of the 77 states. (`R` also has one byte of the stack page, read by an instruction whose operand is the next instruction. Tracking counts it. Measured below: no value of it changes the length.)

**What was measured, not in the theorem.** With a program, each byte the run reads was set to each of its other 255 values, one byte at a time.

* From `T`, 111 bytes: only `OperMode`, `OperMode_Task`, `GamePauseStatus`, `VRAM_Buffer_AddrCtrl`, `GameTimerExpiredFlag`, `HalfwayPage`, `AreaPointer`, `EntrancePage`, `AltEntranceControl` change the length. Sound, digits, random bytes, timers, scroll, size and power change nothing.
* From `E`, 282 bytes: those, and `GameEngineSubroutine`, `ChangeAreaTimer`, `WarpZoneControl`, `AreaType`, and bad values of `Enemy_ID`, `EnemyFrenzyBuffer`, `EnemyFrenzyQueue`, `AreaParserTaskNum`, the music pointer, the area data pointer, the sprite offsets and a VRAM buffer length. Fewer than 91 frames, with the pipe's routine set: only `ChangeAreaTimer` itself (from 44 frames), `HalfwayPage` and `AreaPointer` (from 75 frames).

The TAS's own entry state, run by a program: control after 91 frames, (H1), (H2), (H3) hold, it reads only `R`, 21 bytes of `Rvar` differ from `T`, and with `T`'s values it still takes 43 frames. So (H4) holds for it.

Frame time, apart from frame 49 where the clear runs over: the game logic ends by dot 67,047 of 89,342 on `E` and on the TAS's state; by 80,332 with 5 goombas; 6 goombas 16 px or more apart end by 88,024 and do not run over; closer ones do.

## Assumptions (not proved in Lean)

* (H1), (H2), (H3): the first 48 frames for an arbitrary entry. Enemies, objects and sound run in these frames. Nothing proves for all their states that the timer goes down once per frame, that no frame runs over, and that `Rfix` keeps its values. Only the 77 states and the TAS's state were run. The reasons from the code, not checked in Lean: the pipe's routine runs every frame and lowers the timer once, and the collision with an enemy or a power-up is skipped unless Mario's routine is the control routine.
* (H4): the values of `Rvar`. `decided` covers only the values of `T`, and `entryStates` the values of the 77 states. Most real runs have other digits and random bytes, so without (H4) they are not covered. These bytes are read and branched on, so tracking cannot free them. The support for (H4) is the program above, which changes one byte at a time, not several.
* That `Rfix` has `T`'s values in every real run. `HalfwayPage ≠ 0` would give 75: from the code it is set only on a lost life and cleared when the next area begins, so it is 0 whenever Mario can enter. `AreaPointer` has its value from this level's data at the first controllable frame, measured on `m₀`. The sound effect buffers are 0 in the states run; a longer effect is not excluded.
* That real runs have no six objects close together. This is not proved. Overrun only makes the change longer in the 6 states run.
* The game timer at 000 with Mario alive lasts at most 24 frames in a real run, and the change then gives no control. This is an exception to the +91, on the later side.
* No input only. All inputs were run only from `E`, with the hypothesis `Merge`, on [The change into the bonus room](PipeTransition.md). Start and Select are not covered.
* Overwritten states are not shown reachable. Big Mario, for one, is overwritten here, not reached by a run.
* A frame boundary in the middle of the game logic is outside (H2). So is a screen on another page, through the name table bit. From the pipe's position and the scroll code, a real entry at this pipe has the screen on one page all through the 48 frames; this is not proved in Lean.
* Frames are the emulator's frames. See [Emulator](../docs/emulator.md).

**Files.** `Theorems/PipeTransitionAll.lean`, private `Proof/PipeTransitionAll.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-all-check                   # the sets and the check (true, about 5 s)
.lake/build/bin/smbrta pipe-all-bytes 48 43             # every value of each byte from T (about 8 min of CPU; 0 in the output: no control); pipe-all-bytes 0 91 from E (about 47 min of CPU)
.lake/build/bin/smbrta pipe-all-movie FM2               # a movie's entry against (H1) to (H4)
```
