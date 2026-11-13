[← Back](README.md) | [English](b-3-7-1-SoundRows.md) | [Japanese](b-3-7-1-SoundRows-ja.md)

# The change into the room, with the sound's bytes in tables

**Claim.** The rows of the frames after the vertical pipe's exit can forget the 38 bytes of the sound outside the sound routine. Tables of states of these bytes are carried beside the rows, as on [the change out of the side pipe](d-3-4-2-SideChangeSound.md). This is proved, with a check on the ROM. With these rows the condition at the exit is weaker: the pause sound may be silent, or the sound of the unpause may play (`QuietP`). Before, it had to be silent with the sound's pause flag 0, and both squares' effects had to be as at the reference. The route now asks `QuietP` (`chg.quiet₁`, item 1-1-b-3-7) and only that the game timer is not 000 (`chg.time₁`, `TimerOK`). On 1,100 real runs with Start at random on the pipe's frames, `QuietP` held at 1,014 exits and the old condition at 557.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`. `x = run(E, 0^48)` is the reference machine at the exit. `left`, `During`, `ExitAt`, `Places` and `NoStart` are those of [the change into the room without `fall`](b-3-2-PipeChangeEnd.md). `SongAt(rows, m)` says that `m` has the bytes of one of the rows. `song` are the 1,607 rows of the song, `shape` the forms of the screen buffer at the exit.

## The condition at the exit

`q`, `b`, `f`, `c`, `s₁`, `s₂` are the bytes `PauseSoundQueue`, `PauseSoundBuffer`, `PauseModeFlag`, `Squ1_SfxLenCounter`, `Square1SoundBuffer`, `Square2SoundBuffer`. `U` is the value of the unpause sound and `L` the length of the pause sound, read from the ROM through symbols (`UnpauseSfxValue`, `PauseSfxLength`).

```
QuietP(m)  :=  ( m[q] = x[q]  ∧  m[b] = x[b]  ∧  m[f] = 0  ∧  m[s₁] = x[s₁]  ∧  m[s₂] = x[s₂]  ∧  SongAt(song, m) )     silent
            ∨  ( m[q] = x[q]  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] < L )                                          the unpause sound plays
```

The old condition was `Quiet(m) ∧ SongAt(song, m)` with `Quiet` on `q`, `b`, `s₁`, `s₂`, and `m[f] = 0` from `TimeOK`. So `Quiet(m) ∧ SongAt(song, m) ∧ m[f] = 0 → QuietP(m)` (`quietP_of_quiet`), and `Changes.toK` turns the old fields into the new ones. The count is below `L`: the sound sets the count to `L` and takes one off on the same frame.

## The rows

A row `r` holds the states `R(r)` of one frame, the number `left` of the row, and two tables of the sound's bytes: `T₀(r)` before the call of the sound routine and `T₁(r)` after its return (`SoundRows.SRow`). `Sim(S, m)` says that the abstract state `S` covers `m`, and `Ph(S, m)` that the sound's bytes of `m` are in a state of `T₀(r)`, or of `T₁(r)` after the return.

```
InRowsK(m)  :=  ∃ r ∈ rowsK, ∃ S ∈ R(r),  Sim(S, m) ∧ Ph(S, m)
InRowsT(m)  :=  ∃ r ∈ rowsK, left(r) = 0, ∃ S ∈ R(r), ∃ t ∈ T₀(r),  Sim(S + t, m)
```

`S + t` is `S` with the bytes of `t`. `InRowsT` is what the room's checks read (`ScreenStart.roomCheck`, `RoomStart.startCheck`, `RoomMap.startCheckT`). The rows start from the states at the exit with the sound's bytes forgotten and the timer not 000 (`dg`). Their first table holds the kinds of `QuietP`: one state for each row of the song, and one for each count from 1 to `L − 1`, each with the sound's bytes that the walk of the pipe's frames gives at the exit.

## The statement

`EndStatement` has five new fields. The check `endCheck` gives them, with the old ones (`endStatement_of_check`).

```
stepK :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
           During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( QuietP ∧ SongAt(shape) ∧ TimerOK at frame(m, i)  →  InRowsK(frame(m, i)) ) )
rowsK :  ∀ m, InRowsK(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRowsK(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
zeroK :  ∀ m, InRowsK(m) ∧ left(m) = 0 → ctl(m)
goK   :  ∀ m, InRowsK(m) → ¬Paused(m)
ctlK  :  ∀ m, InRowsK(m) ∧ left(m) = 0 → InRowsT(m)
```

**A run.** `PipeRunK` has the fields of `PipeRun` with `QuietP ∧ SongAt(shape)` at the exit (`quiet`) and `TimerOK` at the exit (`time`). With `b` the first control after the entry (`hc`):

```
PipeRunK.bound   :  cnt(a) + 91 ≤ cnt(b)
PipeRunK.first   :  hc  →  ∀ n, a ≤ n < b,  left(seq n) ≠ 0
PipeRunK.inRowsT :  hc  →  InRowsT(seq b)
PipeRunK.start   :  hc  ∧  startCheck  →  the room's start at seq b          (RoomStart)
```

`Route` takes the first change from `ChangesK.run₁ : PipeRunK`: `ChangesK.bound₁`, `ChangesK.first₁`, `ChangesK.roomAt`, `Run.roomStart` and the room's theorems that read `InRowsT`.

Lean: `Theorems/SoundRows.lean` (`SRow`, `scan`, `rowsFromS`, `incl`, `finS`, `linkS`, `chainS`, `CoveredS`, `link_frameS`, `InvS`, `chain_stepS`, `ctl_of_zeroS`, `inv_headS`, `refineRow`, `zeroRows`, `covered_refine`, `invL_zero`), `Theorems/PipeChangeEnd.lean` (`rtOf`, `QuietP`, `kindsP`, `baseK`, `tableP`, `startsK`, `grpP`, `rowsKc`, `InRowsK`, `timeRows`, `InRowsT`, `soundCheck`, `baseIncl`, `base_of_K`, `kinds_of_quietP`, `quietP_of_quiet`, `inRowsK_of_exit`, `PipeRunK`, `PipeRunK.bound`, `PipeRunK.way`, `PipeRunK.first`, `PipeRunK.inRowsT`), `Theorems/RoomStart.lean` (`startCheck`, `start_of_rowsT`, `PipeRunK.start`), `Theorems/Route.lean` (`ChangesK.run₁`, `ChangesK.bound₁`, `ChangesK.first₁`, `ChangesK.roomAt`, `Changes.toK`). There is no game data in these files.

## How it works

**The exit.** The walk of the pipe's frames now ends at the exit in the states `baseK`. They know the exit's bytes, the noise effect's buffer and the screen buffer's control, but not the four bytes of the old `Quiet`. The old states `baseOf` follow from them with the bytes of `Quiet` (`baseIncl`, `base_of_K`), so the old statement is still proved from the same walk.

**One frame.** The walk is `twalk` of [Where one step of the CPU writes RAM](d-3-4-1-StepWrites.md). At the call of the sound routine a state is split by `T₀(r)`, the routine is walked with the sound's bytes known, and at the return they must be in `T₁(r)` and are forgotten. The place of the call and of the return are read from the ROM: the first call to `SoundEngine` from `NonMaskableInterrupt` (`rtOf`).

**The tables.** On the first frame after the exit the second table joins the states with the same bytes of the pause sound (`grpP`): that frame and the next clear the sound's bytes of page 0, and the song's other bytes are not read until the new song sets them. The check decides whether this holds. On the other frames the tables are as the search finds them.

**The search.** It makes the tables of the walk; the check does not depend on it. Each start state in the idle loop goes alone up to the call of the sound routine, so that the forms of the screen buffer are not joined. There the states join; each piece of the first table goes on alone, with no joins, to the return. There the pieces join with the registers forgotten (`ReadJoypads` sets them next). A start state in the middle of the clear of RAM joins the others, so that the turns of the clear's loop join.

**The size of the check.** 44 rows, 1,906 states, about 10,000 states of the walks' tables, the first table 1,648 states, the largest table 3,557 states (on the last frames, where the new song and the unpause sounds of different lengths mix). In a program: the rows about 24 s, the walks of the rows about 65 s. This is more than a few seconds. The room's checks read the rows where `left` is 0 with their tables: 14,228 states, about 26 s each in a program.

## Facts that are false

* **The unpause pressed on the frame of the exit is not allowed.** On 86 of the 1,100 runs below the unpause was pressed on the frame of the exit (`m[q] = U`, `m[b] = x[b]`, `m[f]` the pause sound's value). On all 86 the room's condition `Room` (d-2-4-1) fails at control: `AreaMusicQueue` is not 0, since the new song has not started. So `QuietP` cannot have this case unless `Room` allows the song's queue.
* With the count `L` of the unpause sound in the first table, `ScreenStart.roomCheck` fails on 4 states with control (`AreaMusicQueue` 4). No real exit has the count `L`.

## Measured, not a theorem

Program: `pipe-sound-real FM2 10`. 55 entries (the reference entry, the movie's entry, 53 real entries standing in the pipe's window and pressing Down), 10 runs each with Start at random on the pipe's frames at two rates, then no Start up to control.

| kind at the exit | exits | old `quiet₁` | song | screen buffer | `s₁`, `s₂` as `x` | timer not 000 | `Room` at control |
|---|---|---|---|---|---|---|---|
| silent, flag 0 | 557 | 557 | 557 | 557 | 557 | 557 | 557 |
| unpause sound, count 1 to 41 | 457 | 0 | 457 | 457 | 457 | 457 | 457 |
| unpause pressed on the exit's frame | 86 | 0 | 86 | 86 | 86 | 86 | 0 |

From the exit to control there were always 44 frames, and `left` fell by exactly one on each frame after the exit.

## Assumptions (not proved in Lean)

* `QuietP ∧ SongAt(shape)` at the exit (`chg.quiet₁`). The song's row in the silent case and the screen buffer's form are still asked. To prove the pause sound's kind, the pipe's frames need tables too: Start is allowed there.
* `TimerOK` at the exit (`chg.time₁`).
* `NoStart` on the frames of the game core after the pipe (`chg.noStart₁`, 1-1-b-3-6). These are the last 18 frames before control. A paused frame does not take one off `left`, and the rows have one row for each value of `left`. Not done.

**Files.** `Theorems/SoundRows.lean`, `Theorems/PipeChangeEnd.lean`; the private check is `pipe_end_checks` in `Proof/PipeChangeEnd.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta pipe-sound-rows -c        # the rows, frame by frame, chainS and soundCheck
.lake/build/bin/smbrta pipe-sound-rows -r        # the room's checks on the rows where left is 0
.lake/build/bin/smbrta pipe-sound-real FM2 10    # the kinds at the exit and Room at control on 1,100 real runs, about 3 min
```
