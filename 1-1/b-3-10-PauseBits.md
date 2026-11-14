[← Back](README.md) | [English](b-3-10-PauseBits.md) | [Japanese](b-3-10-PauseBits-ja.md)

# The pause byte at the room's first control

**Claim.** At the room's first control bits 0 to 6 of the pause byte are 0. This is proved from the rows of the change into the room, with the checks on the ROM that they already had. So the field `chg.pauseBits₂` (bits 1 to 6 of the pause byte at the room's first control, item 1-1-d-3-4) is gone: `ChangesK.pauseBits₂` is a theorem with the same statement. It needs one new check on the names (`RoomChecks.pauseG`): the pause byte of the side pipe's names is the pause byte of the vertical pipe's data.

`m[i]` is the RAM byte `i` of `m`. `seq n` is the machine when frame `n` begins. `a₁` is the vertical pipe's entry, `b₁` the room's first control. `g` is the pause byte (`GamePauseStatus`) as the vertical pipe's data names it, and `g₂` as the side pipe's names name it. `Entry`, `During` and `ExitAt` are those of [the change into the room without `fall`](b-3-2-PipeChangeEnd.md), `InRowsK` and `InRowsT` those of [the change into the room, with the sound's bytes in tables](b-3-7-1-SoundRows.md), `PipeRunK` that of [the pause through the vertical pipe's frames](b-3-7-2-PipePause.md).

## The statement

```
EndStatement.bitsK  :  InRowsK(m)  →  m[g] & 0x7F = 0                                        (from the check, goOK)
PipeRunK.pauseBits  :  (∀ n, a ≤ n < b → ¬ctl(seq n))  →  seq(b)[g] & 0x7F = 0
ChangesK.pauseBits₂ :  seq(b₁)[g₂] & 0x7E = 0                                                 (theorem; it was the field pauseBits₂)
RoomChecks.pauseG   :  g₂ = g                                                                 (new; the private check pause_index)
```

`PipeRunK.pauseBits` follows from `PipeRunK.way`: the machine at `b` is in the rows with tables, because it has control. `ChangesK.pauseBits₂` takes the run of the first change from `ChangesK.run₁`, with the entry from `Run.entry₁`, as `ChangesK.pause₂` does.

## How it works

**The pause routine keeps bits 1 to 6.** The routine writes the pause byte only in two ways: with bit 0 flipped and bit 7 set (Start pressed, the pause timer 0, bit 7 clear), or with bit 7 cleared (the timer 0, Start not pressed). So bits 1 to 6 never change. The bits that the walk knows of the byte stay known through these writes.

**The entry knows them.** `Entry` asks bits 1 to 6 of the pause byte with the reference's values, which are 0 (the mask `0x7E` of `GamePauseStatus` in `entryMasks`). Since round 11 they are proved at the entry too: the near states of `TitleStart` know the pause byte, and the frames from control keep these bits ([1-1-b-3-4](b-3-4-EntryKeep.md)); before, they were part of `Rest` (`chg.entryRest₁`). The start states of the pipe's frames know them, and every frame's end that stays in the pipe must be under a start state, so the walks of the pipe's frames keep them.

**The exit's states now know them.** Before, the states at the exit of the rows with tables (`baseK`, from `SideChangeEnd.exitStarts`) knew only bit 0 of the pause byte. Now they know bits 0 to 6 with the values of the reference at the exit (`exitBitsK`). Both walks of the pipe's frames, the old one (`zcheck`) and the one with the class beside it (`pipeCheckV`), still end under them. The rows with tables start from these states, and the check `goOK` now asks every state of the rows to know that bits 0 to 6 are 0 (`low7K`).

**The names.** The rows name the pause byte by the vertical pipe's data, the room's checks by the side pipe's names. The two lists are different tables of the same names. `RoomChecks.pauseG` says that they give the same RAM index; the private file checks it (`pause_index`, in `Proof/ScreenStart.lean`).

**The checks that read the rows.** The rows of the time are built from the rows with tables, so every check that reads them runs on the new rows: `ScreenStart.roomCheck`, `RoomStart.startCheck`, `RoomMap.startCheckT`, `RoomPause.startCheck`, `RoomPair.rowsCheck`, `HurryStart.rowsCheck₁`. All pass (private builds, exit 0). The rows where `left` is 0 still have 14,224 states with the table, all with control.

**The size.** In a program: the old walk's check 6.0 s, the walk with the class beside it 11.4 s, `soundCheck` 180 s. The private build of `Proof/PipeChangeEnd.lean` took 250 s (about 232 s before; measured with other builds running).

## What changed in the route

* `chg.pauseBits₂` is gone: `ChangesK.pauseBits₂` is a theorem, and `ChangesK.pause₂` uses it.
* `RoomChecks.pauseG` is new: an equality of two RAM indices from the names. `RoomChecks` is built in the private files of the route and of the hurry-up music (`pause_index`).
* `PipeChangeEnd.EndStatement` has the new field `bitsK`.

## Assumptions (not proved in Lean)

* None new. Bits 1 to 6 of the pause byte at the vertical pipe's entry are proved from the press of Start on the title and the frames from control, under `upClean₁` ([1-1-b-3-4](b-3-4-EntryKeep.md)). Before this round they were in `chg.entryRest₁`.

**Files.** `Theorems/PipeChangeEnd.lean` (`low7K`, `low7_of`, `exitBitsK`, `baseK`, `goOK`, `EndStatement.bitsK`, `PipeRunK.pauseBits`), `Theorems/Route.lean` (`RoomChecks.pauseG`, `low6_of_low7`, `ChangesK.pauseBits₂`, `ChangesK.pause₂`). The private check is still `pipe_end_checks` in `Proof/PipeChangeEnd.lean`, and `pause_index` in `Proof/ScreenStart.lean`. There is no game data in the public files.

**To reproduce.**
```
.lake/build/bin/smbrta pipe-pause-check old   # both walks of the pipe's frames with the new exit states, about 55 s
.lake/build/bin/smbrta pipe-sound-rows -c     # the rows with tables and soundCheck, about 6 min
.lake/build/bin/smbrta pipe-sound-rows -r     # the room's checks on the rows
```
