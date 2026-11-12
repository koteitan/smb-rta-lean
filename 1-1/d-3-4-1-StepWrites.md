[← Back](README.md) | [English](d-3-4-1-StepWrites.md) | [Japanese](d-3-4-1-StepWrites-ja.md)

# Where one step of the CPU writes RAM

**Claim.** One step of the Lean CPU changes RAM only at the address that its instruction stores to, and at the bytes of the stack that it pushes. This is proved for every machine and every opcode. With it, a walk of the abstract machine can carry a fact about bytes that its states do not know: the sound's bytes are in a state of a table. This is proved as a general step and a general frame, with no game data. Used on the side change, it is measured, not proved: rows that forget the sound's bytes close for 52 kinds of the pause sound at the exit. So `chg.quiet₂` (1-1-d-3-4) and `chg.noStart₂` (1-1-d-3-3) stay; this page says what they need now.

`step(m)` is one step of the CPU. `m[i]` is the RAM byte `i` of `m`. `trace(m, inp, k)` is the machine after `k` steps of the frame of `m` with the input `inp`. `Sim(A, m)` says that the abstract state `A` of `TaintRun` covers `m`.

## The statements

```
ramIdx(a)    :=  [a & 0x7FF]  if a < 0x2000,   []  otherwise
stk(s, k)    :=  ramIdx(0x100 | s) ++ ramIdx(0x100 | (s − 1)) ++ … ,   k bytes
stepLocs(m)  :=  stk(m.s, 3)                 if an NMI is pending
                 []                          if m is halted
                 locs(w(op), m₁)             otherwise
locs(no, m₁)   := []
locs(md c, m₁) := ramIdx(c(m₁))              c(m₁) is the address of the instruction's mode
locs(st k, m₁) := stk(m₁.s, k)

step_ram   :  ∀ m i,  i ∉ stepLocs(m)  →  step(m)[i] = m[i]
trace_ram  :  (∀ k < n,  i ∉ stepLocs(trace(m, inp, k)))  →  trace(m, inp, n)[i] = m[i]
keep_step  :  Sim(A, m)  ∧  keepOK(E, P, A)  →  ∀ i ∈ P,  step(m)[i] = m[i]
keep_frame :  a frame walk with keepOK(E, P, ·) on every state  →  ∀ i ∈ P,  frame(m, inp)[i] = m[i]
```

`op` is the opcode at the program counter, and `m₁` the machine after the opcode is fetched. `w(op)` is the entry of a table of the 256 opcodes: `no` (no write), `md c` (a store or a read-modify-write through the mode `c`), `st k` (`k` pushes: 1 for `PHA` and `PHP`, 2 for `JSR`, 3 for `BRK`). `keepOK(E, P, A)` is a test on `A`: for an NMI, the three stack bytes are outside `P`; for a push, the stack bytes; for a store, the addresses that the abstract mode of `TaintRun` gives for `A`.

**The sound's bytes outside the abstract states.** `SB` is a list of RAM bytes (the sound's). A state of a table is a list of bytes, each with known bits. `SIn(t, m)` says that `m` is in the state `t`. `spent` is a bit of the abstract state that nothing reads when the counter `rk` of `TaintRun` is off. Here it says whether the routine has returned on this frame.

```
Ph(A, m)  :=  A.pc in the routine
           ∨  (A.spent = false  ∧  ∃ t ∈ T₀,  SIn(t, m))
           ∨  (A.spent = true   ∧  ∃ t ∈ T₁,  SIn(t, m))

s_tsuccs       :  Sim(A, m)  ∧  Ph(A, m)  →  ∃ B ∈ tsuccs(A),  Sim(B, step(m))  ∧  Ph(B, step(m))
tframe_of_walk :  a frame walk with tsuccs from S,  Sim(S, m)  ∧  Ph(S, m)
                  →  ∃ B,  Sim(B, frame(m, inp))  ∧  Ph(B, frame(m, inp))
```

`tsuccs` is the step of the walk:

* At the call of the routine, with `spent` false: one piece for each `t ∈ T₀` that agrees with `A`, with the bytes of `t` put into `A`. The call must keep the bytes (`keepOK`).
* In the routine: the plain step. At the return: the bytes of the state must be in a state of `T₁`; then they are forgotten and `spent` is set.
* Elsewhere: the plain step. It keeps the bytes (`keepOK`), or it writes some of them and the table stays closed (`writeOK`: every state of the table, with the written bytes as the abstract machine knows them, is in a state of the table).

Lean: `Theorems/StepWrites.lean` (`NoWr`, `WrIn`, `wRows`, `AllW`, `w_op`, `stepLocs`, `step_ram`, `trace_ram`, `keepOK`, `keep_step`, `kwalk`, `kframe_of_walk`, `keep_frame`, `Rt`, `SIn`, `aLocs`, `aLocs_ok`, `writeOK`, `tsuccs`, `Ph`, `s_tsuccs`, `twalk`, `tframe_of_walk`). The theorems use only `propext`, `Classical.choice` and `Quot.sound`. There is no game data in the file.

## How it works

**One step.** `NoWr f` says that `f` does not change RAM, `WrIn w f` that `f` changes RAM only at `w(m)`. A few routine lemmas build them: a leaf of `PipeTransitionAll` does not write; a read does not write; a write to `a` writes at `ramIdx(a)`; a push writes at the stack pointer. Each kind of instruction has a lemma (`w_opSTA`, `w_rmw`, `w_opJSR`, …), and the table `wRows` is proved row by row, as `PipeTransitionAll` proves its relation. An NMI is a push of three bytes, a halted machine does not move, and the idle loop does not write.

**The abstract side.** For an entry `md c`, the table also holds the abstract mode of `TaintRun`. The lemmas `s_mZp`, `s_mAbx`, … of `TaintRun` say that the abstract mode's interval holds the address. So the step of a covered machine writes only where the interval says. `aLocs` gives the indices when the interval is one address or outside RAM.

## Measured, not a theorem

Programs: `sound-check exits`, `sound-check keeprows`, `sound-check trows`.

**Real exits of the side pipe.** 43 entries, 20 runs each, Start at random on the pipe's frames, half of the runs also after the exit (860 runs).

| at the exit (`PauseSoundQueue`, `PauseSoundBuffer`, `PauseModeFlag`, `Squ1_SfxLenCounter`) | runs |
|---|---|
| (0, 0, 0, 0): `Quiet` holds | 275 |
| (0, 2, 2, c), c from 1 to 41: the sound of the unpause plays | 565 |
| (2, 0, 1, 0): the unpause was pressed on the frame of the exit | 20 |

The other sound bytes of `Kx` had the values of `T` at all 860 exits. The song's bytes of the second square and the triangle, and the counter of the second square's sound effect, differ between exits. They are free in `ExitCond`.

**Writes to the sound's bytes outside the sound routine.** On real frames after the exit: the RAM clear (16 sound bytes to 0) and `AreaMusicQueue` (two places); with Start, also `PauseSoundQueue` (the pause routine). On the walks of the rows `rows0` (866,701 states, 126,587 of them in the sound routine), `keepOK` fails at 7 places only: these, `EventMusicQueue` (two places) and `Square1SoundQueue` (one place). Every other state passes `keepOK`.

**The call from real sound states.** The walk of the call closes from every one of the 5,254 sound states at the calls after the exit (no Start after the exit; 380,056 steps, no failure) and of the 32,325 states with Start after the exit (1,388,838 steps, no failure). A call takes 255 to 3,291 dots.

**Rows that forget the sound's bytes.** Start states: the states of `endBase` with the 38 sound bytes forgotten. `T₀` has 52 states: the bytes of `Kx` among the sound's bytes with the values of `T`, and the four pause bytes as one of the 43 kinds above (the count c from 1 to 42), or with the pause flag 0, or with one bit of the flag 1 (8 states). For each frame the tables are made by a search (the bytes at the returns, and the writes joined in), and the frame is then searched with `tsuccs`.

| kinds at the exit | failures | steps of the search | largest table | time |
|---|---|---|---|---|
| the flag 0 and its 8 bits (what `rows0` and `rows1` cover) | 0 | 1,103,905 | 15 | 14 s |
| all 52 | 0 | 2,740,068 | 507 | 44 s |

The 122 rows close, and `left` falls by one on each. Before, `rows0` and `rows1` took 682,944 + 691,797 steps for the flag 0 and not 0. If the states at the returns are joined by kind, the music's routine that looks for the song's header runs with a byte that may be 0 and does not end (row 3). So the tables keep them apart. The time includes the searches that make the tables.

## What this gives

* `quiet₂` (1-1-d-3-4). With rows like these, the condition at the exit becomes: the pause bytes are one of 52 kinds. This is weaker than `Quiet` and holds at all 860 measured exits; `Quiet` holds at 275. Not done: the rows as a proof (the link of two rows with `twalk`, the condition `Ph` in `InvL`, the rows of the time with `dg`, `EndStatement`). The rows are also read by `SurfaceFrames.startCheck` and `ControlStart.ctlCheck`: their theorems take a run with `quiet`, so the route keeps `quiet₂` until they read the new rows. Their tests (`start_of_invL`, `ctl_of_invL`) work on any list of rows.
* The kinds are still an assumption on the exit. To prove them, the pipe's frames need the same tables: Start is allowed there, so the pause sound's state must be carried from the entry.
* `noStart₂` (1-1-d-3-3). The table makes the delay of the song harmless: the 32,325 states with Start after the exit all close. But Start pauses the game, and a paused frame does not take one off `left`. The rows have one row for each value of `left`, so paused states need rows that can stay. Not done.
* `quiet₁`, `noStart₁` (1-1-b-3-7, 1-1-b-3-6). The same holds for the change into the room: `Quiet` fails after Start on the pipe's frames, and the same tables would replace it by kinds of the pause sound. Its rows are read by `ScreenStart` and `RoomMap`. Not done.

## Assumptions (not proved in Lean)

None for the theorems on this page. The measured rows above are not a theorem.

**Files.** `Theorems/StepWrites.lean`. The programs are in `Main.lean` (`sound-check`).

**To reproduce.**
```
.lake/build/bin/smbrta sound-check exits          # real exits with Start: kinds, sound states, writes, the call from each state, about 7 min
.lake/build/bin/smbrta sound-check keeprows       # keepOK on the walks of rows0, about 4 s
.lake/build/bin/smbrta sound-check "trows;quiet"  # rows with the sound forgotten, the flag's 9 kinds, about 15 s
.lake/build/bin/smbrta sound-check "trows;nojoin" # the same for 52 kinds, about 45 s
```
