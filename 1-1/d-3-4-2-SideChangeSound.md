[← Back](README.md) | [English](d-3-4-2-SideChangeSound.md) | [Japanese](d-3-4-2-SideChangeSound-ja.md)

# The change out of the side pipe, with the sound's bytes in tables

**Claim.** The rows of the change out of the side pipe can forget the 38 bytes of the sound outside the sound routine. A table of states of these bytes is carried beside the rows. This is proved, with a check on the ROM. With these rows the condition at the exit is weaker: the pause sound may be silent, or the sound of the unpause may play, or the unpause may have been pressed on the frame of the exit (`QuietK`). Before, it had to be silent (`Quiet`). `QuietK` held at all 880 measured exits, `Quiet` at 257. `QuietK` at the exit is now proved from a condition at the entry ([The pause through the side pipe's frames](d-3-4-3-SidePause.md)), and the route asks that one.

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

## Start after the pipe: measured in round 11, not done

`chg.noStart₂` stays. A pause stops the song (the music routine does not run while the pause flag is set), and the game's frames go on after the unpause. So after a pause the song of a row can be the song of any earlier row: each row's table would have to hold the songs of all earlier rows. These are the numbers.

| measured | result |
|---|---|
| songs of a row of the game core (the 38 bytes without the 4 of the pause sound) | 28 per row (rows 25 to 121) |
| their union over the rows of the game core | grows by 9 a row: 55 at row 25, 920 at row 121 |
| the same without the effects' bytes | 20 per row; the union grows by 1 a row, 103 at row 120 |
| the rows with `DAC_Counter` not known in the tables | the same rows, 76,522 states of the tables; `chainS` true |
| the three effect queues not known | the first frame's search passes 1,000,000 steps |
| Square 2's three effect bytes not known | `chainS` true, but 1,092,164 states of the tables (14 times), 298 s and 268 s |
| Square 1's effect buffer not known | no result in 600 s |
| the noise effect's two bytes not known | the first frame's search passes 1,000,000 steps |
| real runs with Start at random also after the exit (`pause-rows-real FM2 20 7`: 880 runs, 1,580 pauses after the exit) | no frame lowers `left` by more than one; no frame that ends paused lowers `left`; control within 679 frames |

So the effects must stay in the tables, and the union reaches 920 states, about 33 times the 28 songs a row has now. Each row's walk splits the sound routine by its table, so the walks of the late rows would grow about that much. With the pause's six bytes in the same table, a paused row would hold each song with each of the 44 states of the pause sound. With the six bytes in a table of their own (as in [The pause through the room's frames](d-3-4-4-RoomPause.md)), the songs would have to be split only where the music runs, inside the region of the pause's table; that needs a second table with its own region, which `StepWrites` does not have. Another way would be a summary of the sound routine for a closed set of songs, used as one step of the rows' walk; that needs a walk that ends at the routine's return and a step of the frame's walk that covers the whole call. Neither is done.

Programs (temporary, in `Main.lean`): `sound-probe ROWS`, `sound-rows-p NAMES`, `pause-rows-real FM2 N R`.

## What changed in the route

* `Route.Changes` is split. `ChangesBase` has every field but `quiet₂`. `ChangesK` adds the condition of the second change on the pause, and `Run.chg` is a `ChangesK`: in round 8 `quiet₂` with `QuietK`, now `pause₂` at the entry ([The pause through the side pipe's frames](d-3-4-3-SidePause.md); `Changes.toK` is gone with it). `Changes` adds the old `quiet₂` with `Quiet`; `HurryStart` and `HurryMusic` still read it.
* `Run.change₂`, `Run.start`, `Run.atCtl₀` and `level_ge_of_parts` take `SideChangeSound.EndStatementK` (and `startCheckK`, `ctlCheckK`) in place of `SideChangeEnd.EndStatement` (and `startCheck`, `ctlCheck`).
* The bound of the change (`Run.change₂`) now also uses `chg.time₂`: the rows are rows of the time. `time₂` was already a field.

## Assumptions (not proved in Lean)

* `QuietK` at the exit is no longer assumed. [The pause through the side pipe's frames](d-3-4-3-SidePause.md) proves it from the condition `PauseE` at the entry (`chg.pause₂`, 1-1-d-3-4).
* `NoStart` (`chg.noStart₂`, 1-1-d-3-3): no Start on the frames of the game core after the pipe. A paused frame does not take one off `left`, and the rows have one row for each value of `left`. Not done; paused rows were tried and measured on [The pause through the side pipe's frames](d-3-4-3-SidePause.md).
* The others are as on [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md): `Entry2`, `lagPaused`, `TimerOK`.

**Files.** `Theorems/SideChangeSound.lean`; the private check is in `Proof/Route.lean` and the place of the sound routine in `Proof/SideChangeSound.lean` (`genSideSound` in `Main.lean`). The symbols `PauseSfxValue`, `UnpauseSfxValue`, `PauseSfxLength` are in `tools/smb-symbols.txt`.

**To reproduce.**
```
.lake/build/bin/smbrta sound-rows-check          # the rows, their check, and endCheckK, about 80 s
.lake/build/bin/smbrta sound-rows-real FM2 20    # the conditions on 880 real runs, about 2.5 min
```
