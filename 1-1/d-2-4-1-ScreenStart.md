[← Back](README.md) | [English](d-2-4-1-ScreenStart.md) | [Japanese](d-2-4-1-ScreenStart-ja.md)

# The condition `Room` at the first control in the room

**Claim.** [The screen's page in the room, and the long timer](d-2-4-ScreenPage.md) assumed a condition `Room` on the state at the first control in the room. `Room` is the bits of 79 bytes and how the frame ended (the idle loop, the dot, the flags). This is now proved on the real machines. It comes from the rows of the time of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md). The conditions are those of that change, that the time is not up at the exit (`chg.time₁`), and that `b₁` is the first control after the entry (`chg.ctlFirst₁`). The field `chg.roomRest` (5 bytes at control) is gone.

## Statements

`r` is the reference machine of `Room` (the machine on the frame before the entry into the side pipe). `K` is the list of bits that `Room` knows. `InRowsT(m)` says that `m` is covered by a state of the rows of the time ([b-3-2](b-3-2-PipeChangeEnd.md)).

```
roomCheck     :  the mask of K is right ∧ the two environments have the same ROM ∧
                 every state S of the rows of the time knows the bytes of control,
                 and if it has control, S ≤ startR(r, K, low) for some low

room_of_rows    :  roomCheck ∧ InRowsT(m) ∧ ctl(m)  →  Room(m)
PipeRun.inRowsT :  EndStatement ∧ PipeRun ∧ time ∧ ctlFirst  →  InRowsT(seq b)       (b-3-2)
Route.Changes.roomAt :  RoomChecks ∧ Changes  →  Room(seq b₁)
```

`startR(r, K, low)` is a start state of `Room`: it knows the bits of `K` with the values of `r`, and the dot is 0 (`low`) or 1 to 9. If `S ≤ startR`, every machine that `S` covers is covered by `startR` too (`sim_le`). That gives `Room` (`ScreenPage.room_of_sim`).

`Changes.run₂` passes `Changes.roomAt` to `ScreenPage.entry_long`. `RoomChecks` has the fields `pipe` (`pipe_end`) and `start` (`screen_start`).

## Where the 5 bytes come from

Before this, the rows of the change left 5 bytes of `K` not known as in the reference at control. Now each comes from the rows of the time:

| byte | why the rows of the time know it as in the reference |
|---|---|
| `WorldNumber` | it is in the condition at the exit now. The walk of the pipe's frames gives that condition from the condition at the entry |
| `PlayerStatus` (bits 1 to 7) | the same. The condition at the entry already had these bits |
| `AreaMusicBuffer_Alt` (all bits but bit 2) | the same |
| `SecondaryHardMode` | the area's setup clears it, then sets bit 0 or not from `PrimaryHardMode` and `WorldNumber`. Both are in the condition at the exit now |
| `AreaMusicQueue` | in the rows of the time the sound's pause flag is 0, so the sound routines run and take the queue as in the reference. When the flag is not 0, the queue keeps another value; that case is in the rows `rowsB`, not in the rows of the time |

`LevelNumber` is not needed: with `WorldNumber` and `PrimaryHardMode` known, the setup does not read it.

## The check

`screen_start` (private, `native_decide`). About 4 s in a program. The rows of the time have 44 rows, 8118 states, and 2 states with control. Both are under `startR` for the whole `K`.

## Real runs

The program is `room-start-check FM2 [N]`. The entries are the reference entry, the TAS's entry, and 13 real entries. "The exit's condition" is `quiet₁`; "the time" is `TimeOK` at the exit (`time₁`).

| inputs | runs | not `Room` at control | with the exit's condition | of them without the time | of them not `Room` |
|---|---|---|---|---|---|
| TAS (control at frame 653) | 1 | 0 | 1 | 0 | 0 |
| no input | 15 | 0 | 15 | 0 | 0 |
| random, no Start | 300 | 0 | 300 | 0 | 0 |
| random, Start only on the pipe's frames | 300 | 41 | 167 | 0 | 0 |

In each of the 41 runs without `Room`, only `AreaMusicQueue` differs, and none meets the condition at the exit (`chg.quiet₁`). So these runs are outside the theorem.

## Assumptions (not proved in Lean)

* **`chg.time₁`, `chg.ctlFirst₁`.** The time is not up at the exit, and `b₁` is the first control. See [b-3-2](b-3-2-PipeChangeEnd.md).
* **The conditions of the change** (`chg.entry₁`, `places₁`, `quiet₁`, `noStart₁`). `chg.entry₁` now also asks `WorldNumber`, `PrimaryHardMode` and the bits of `AreaMusicBuffer_Alt` at the entry. A fire Mario (`PlayerStatus` 2) does not meet `chg.entry₁`.

**Files.** `Theorems/ScreenStart.lean`, `Theorems/PipeChangeEnd.lean` (`timeRows`, `PipeRun.inRowsT`), `Theorems/Route.lean` (`RoomChecks`, `Changes.roomAt`), private `Proof/ScreenStart.lean`.
