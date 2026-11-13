[← Back](README.md) | [English](d-3-4-2-SideChangeSound.md) | [Japanese](d-3-4-2-SideChangeSound-ja.md)

# The change out of the side pipe, with the sound's bytes in tables

**Claim.** The rows of the change out of the side pipe can forget the 38 bytes of the sound outside the sound routine. A table of states of these bytes is carried beside the rows. This is proved, with a check on the ROM. With these rows the condition at the exit is weaker: the pause sound may be silent, or the sound of the unpause may play, or the unpause may have been pressed on the frame of the exit (`QuietK`). Before, it had to be silent (`Quiet`). The route now asks `QuietK`: `chg.quiet₂` (1-1-d-3-4) is weaker. `QuietK` held at all 880 measured exits, `Quiet` at 257.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `Sim(S, m)` says that the abstract state `S` covers `m`. `left`, `During2`, `Entry2`, `NoStart` and `TimerOK` are those of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). `Ph`, `SIn`, `tsuccs` and `tframe_of_walk` are those of [Where one step of the CPU writes RAM](d-3-4-1-StepWrites.md).

## The condition at the exit

`q`, `b`, `f`, `c` are the bytes `PauseSoundQueue`, `PauseSoundBuffer`, `PauseModeFlag` and `Squ1_SfxLenCounter`. `x` is the reference machine at the exit. `U` is the value of the unpause sound, `P` the value of the pause sound, `L` the length of the sound. These three are read from the ROM through symbols (`UnpauseSfxValue`, `PauseSfxValue`, `PauseSfxLength`).

```
QuietK(m)  :=  ( m[q] = x[q]  ∧  m[b] = x[b] )                                   silent, any flag
            ∨  ( m[q] = x[q]  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] ≤ L )         the unpause sound plays
            ∨  ( m[q] = U  ∧  m[b] = x[b]  ∧  m[f] = P )                          the unpause was pressed on this frame
Quiet(m)   :=  m[q] = x[q]  ∧  m[b] = x[b]
```

So `Quiet(m) → QuietK(m)` (`quietK_of_quiet`).

## The rows

A row `r` holds the states `R(r)` of one frame, the number `left` of the row, and two tables of the frame: `T₀(r)` before the call of the sound routine and `T₁(r)` after its return.

```
CoveredS(r, m)  :=  ∃ S ∈ R(r),  Sim(S, m)  ∧  Ph(S, m)          Ph with T₀(r) and T₁(r)
InvS(l, m)      :=  ∃ r ∈ l,  CoveredS(r, m)

chain_stepS  :  chainS(l)  ∧  InvS(l, m)  ∧  ( coreFrame(m) → NoStart(i) )
                →  left(m) = 0  ∨  ( InvS(l, frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
ctl_of_zeroS :  chainS(l)  ∧  zeroCtl(l)  ∧  InvS(l, m)  ∧  left(m) = 0  →  ctl(m)
```

`chainS(l)` checks each frame from a row `r` to the next row `r'`: the walk with `tsuccs` from each state of `r` and of its table ends in a state of `r'`. At the frame's end the table that holds (`T₀(r)` if the routine has not returned, `T₁(r)` if it has) is in `T₀(r')`: each of its states is in a state of `T₀(r')`.

## The statement

`InRowsK(m) := InvS(rowsK, m)`. The rows `rowsK` start from the states at the exit with the sound's bytes forgotten, and `dg` (the game timer is not 000). Their first table is `T_x`: the 52 kinds of `QuietK` (silent with the flag 0 or with one bit of the flag 1, the unpause sound at each count from 1 to `L`, the unpause pressed), each with the other sound bytes of the exit. `EndStatementK` has these fields. The check `endCheckK` gives them (`endStatementK_of_check`).

```
entry         :  ∀ M,  Entry2(M) → Entry(M)
during        :  ∀ M,  Entry2(M) → During2(M)
toDuring      :  ∀ m,  During2(m) → During(m)
step          :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))
                   ∨  ( Exit(frame(m, i))  ∧  ( QuietK(frame(m, i)) ∧ TimerOK(frame(m, i)) → InRowsK(frame(m, i)) ) )
rows          :  ∀ m, InRowsK(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRowsK(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
zero          :  ∀ m,  InRowsK(m) ∧ left(m) = 0 → ctl(m)
duringLeft    :  ∀ m,  During2(m) → left(m) ≠ 0
pauseKeeps    :  ∀ m, During2(m) → ∀ i,  Paused(frame(m, i)) ∧ During2(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsNotPaused :  ∀ m,  InRowsK(m) → ¬Paused(m)
exitOff       :  ∀ m,  Exit(m) → ¬ctl(m)
```

**A run.** `EndRunK` has the fields of `SideChangeEnd.EndRun` with `QuietK` in place of `Quiet`, and one more: `TimerOK` at the exit (`time`). `b` is the first control after the entry `a` (`hc`).

```
EndRunK.bound  :  cnt(a) + 282 ≤ cnt(b)
EndRunK.first  :  hc  →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
EndRunK.inRows :  hc  →  InRowsK(seq b)
EndRunK.start  :  hc  ∧  startCheckK  →  Start(PA, seq b)
EndRunK.atCtl' :  hc  ∧  ctlCheckK    →  AtCtl(seq b)
EndRunK.last   :  hc  →  a + 1 ≤ b  ∧  seq(b − 1) is in the rows  ∧  left(seq(b − 1)) = 1
```

`Route` uses `bound`, `start` and `atCtl'`. `last` is what `HurryStart` reads from the rows; `HurryStart` does not use it yet.

Lean: `Theorems/SideChangeSound.lean` (`scan`, `SRow`, `rowsFromS`, `incl`, `finS`, `linkS`, `chainS`, `soundCtx`, `PauseIdx`, `pauseIdx`, `QuietK`, `kinds`, `tableAt`, `CoveredS`, `ph_next`, `link_frameS`, `InvS`, `chain_stepS`, `invL_of_invS`, `ctl_of_zeroS`, `inv_headS`, `bit_of_ne`, `kinds_of_quiet`, `quietK_of_quiet`, `InRowsK`, `endCheckL`, `endCheckK`, `EndStatementK`, `endStatementK_of_check`, `EndRunK`, `st_stepK`, `EndRunK.bound`, `EndRunK.way`, `EndRunK.first`, `EndRunK.inRows`, `EndRunK.last`, `startCheckK`, `ctlCheckK`, `sideCheckK`, `EndRunK.start`, `EndRunK.atCtl'`), private `side_sound_checks` (`native_decide`, in `Proof/Route.lean`), `side_sound`. There is no game data in the public file.

## How it works

**One frame.** The walk is `twalk` with `tsuccs`. Outside the sound routine the sound's bytes are not known. At the call the state is split by `T₀(r)`, and the routine is walked with the bytes known. At the return the bytes must be in `T₁(r)`, and they are forgotten. A step outside the routine that writes a sound byte must keep the table closed (`writeOK`). `tframe_of_walk` gives the frame. At its end `Ph` goes over to the next row (`ph_next`), by the check that the table that holds is in `T₀(r')`.

**The tables.** They are made by the check, frame by frame. A search with no check at the return (`scan`) gives the writes to sound bytes before the call, the bytes at the returns, and the writes after the return. The writes are joined into the tables (`joinUnder`). The states of the same search are the table of the walk, so each frame is searched once (twice when there are writes before the call). The states at the returns are kept apart: if they are joined by kind, the music's routine that looks for the song's header runs with a byte that may be 0 and does not end.

**The flag is in the table.** In `SideChangeEnd` the sound's pause flag needed two sets of rows, and nine sets of rows of the time. Here the flag is a sound byte, so its cases are states of the table, and one set of rows serves all 52 kinds.

**The exit.** The frame of the pipe that leaves the pipe ends in a state of `baseK`, which knows the exit's bytes but not the two bytes of the pause sound (the check of the pipe's frames with no bytes asked, `duringCheck` with `[]`). With the sound's bytes forgotten and `dg` it is a state of the first row. `QuietK` gives a kind (`kinds_of_quiet`), and the state's known bytes give the other sound bytes of the exit (`soundLe`). So `Ph` holds with the first table.

**The size of the check.** 123 rows, 2,280 states, 76,522 states of the tables, the largest table 507 states. The rows take about 20 s natively and their walks about 17 s; the whole check `endCheckK` about 39 s in a program. This is more than a few seconds. In the route the rows are made once for the three checks (`sideCheckK`).

## Measured, not a theorem

Program: `sound-rows-real FM2 20`. 44 entries with `Entry2` (the reference entry, the movie's entry and 42 real entries), 20 runs each, Start at random on the pipe's frames, then no Start up to control.

| at the exit | runs |
|---|---|
| all | 880 |
| `ExitCond` with the bytes of `exitKnownK` | 880 |
| `QuietK` | 880 |
| `Quiet` | 257 |
| the game timer not 000 | 880 |

After the exit, on these runs, `left` falls by exactly one on each frame, and control comes exactly where `left` is 0. From the entry to control: 375 to 598 frames.

## What changed in the route

* `Route.Changes` is split. `ChangesBase` has every field but `quiet₂`. `ChangesK` adds `quiet₂` with `QuietK`, and `Run.chg` is a `ChangesK`. `Changes` adds the old `quiet₂` with `Quiet`; `HurryStart` and `HurryMusic` still read it. `Changes.toK` turns a `Changes` into a `ChangesK`.
* `Run.change₂`, `Run.start`, `Run.atCtl₀` and `level_ge_of_parts` take `SideChangeSound.EndStatementK` (and `startCheckK`, `ctlCheckK`) in place of `SideChangeEnd.EndStatement` (and `startCheck`, `ctlCheck`).
* The bound of the change (`Run.change₂`) now also uses `chg.time₂`: the rows are rows of the time. `time₂` was already a field.

## Assumptions (not proved in Lean)

* `QuietK` at the exit (`chg.quiet₂`, 1-1-d-3-4). To prove it, the pipe's frames need tables too: Start is allowed there, so the state of the pause sound must be carried from the entry.
* `NoStart` (`chg.noStart₂`, 1-1-d-3-3): no Start on the frames of the game core after the pipe. A paused frame does not take one off `left`, and the rows have one row for each value of `left`. Not done.
* The others are as on [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md): `Entry2`, `lagPaused`, `TimerOK`.

**Files.** `Theorems/SideChangeSound.lean`; the private check is in `Proof/Route.lean` and the place of the sound routine in `Proof/SideChangeSound.lean` (`genSideSound` in `Main.lean`). The symbols `PauseSfxValue`, `UnpauseSfxValue`, `PauseSfxLength` are in `tools/smb-symbols.txt`.

**To reproduce.**
```
.lake/build/bin/smbrta sound-rows-check          # the rows, their check, and endCheckK, about 80 s
.lake/build/bin/smbrta sound-rows-real FM2 20    # the conditions on 880 real runs, about 2.5 min
```
