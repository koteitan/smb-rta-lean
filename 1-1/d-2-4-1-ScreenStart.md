[← Back](README.md) | [English](d-2-4-1-ScreenStart.md) | [Japanese](d-2-4-1-ScreenStart-ja.md)

# The condition `Room` at the first control in the room

**Claim.** [The screen's page in the room, and the long timer](d-2-4-ScreenPage.md) assumed a condition `Room` on the state at the first control in the room (`chg.roomStart`). `Room` is the bits of 73 bytes and how the frame ended (the idle loop, the dot, the flags). This is now proved on the real machines, except for 5 bytes (`chg.roomRest`). It comes from the rows of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md). The conditions are those of that change, that `left₁` is not 0 before control (`chg.first₁`), and the 5 bytes.

## Statements

`r` is the reference machine of `Room` (the machine on the frame before the entry into the side pipe). `K` is the list of bits that `Room` knows. `R₅` is these 5 bytes:

```
R₅ = { SecondaryHardMode, PlayerStatus, WorldNumber, AreaMusicBuffer_Alt, AreaMusicQueue }
K' = K without the bytes of R₅

RestAt(m)     :  ∀ (b, k) ∈ K,  b ∈ R₅  →  m[b] & k = r[b] & k

roomCheck     :  the mask of K' is right ∧ the two environments have the same ROM ∧
                 every state S of the rows of the two cases of the change knows the bytes of control,
                 and if it has control, S ≤ startR(r, K', low) for some low

room_of_rows  :  roomCheck ∧ InRows(m) ∧ ctl(m) ∧ RestAt(m)  →  Room(m)
Route.Changes.roomAt :  RoomChecks ∧ Changes  →  Room(seq b₁)
```

`startR(r, K', low)` is a start state of `Room`: it knows the bits of `K'` with the values of `r`, and the dot is 0 (`low`) or 1 to 9. If `S ≤ startR`, every machine that `S` covers is covered by `startR` too (`sim_le`). That gives the part of `Room` on `K'` (`ScreenPage.room_of_sim`). The bytes of `R₅` are added from `RestAt`.

`Changes.roomAt` uses `PipeRun.inRows` of [The state at the first control in the room](c-7-2-RoomStart.md). `Changes.run₂` passes `Changes.roomAt` to `ScreenPage.entry_long` in place of `chg.roomStart`. `RoomChecks` has two new fields, `pipe` (`pipe_end`) and `start` (`screen_start`).

## The check

`screen_start` (private, `native_decide`). 3.8 s in a program. The rows have 4 states with control. Each is under `startR` for `K'`, and only the 5 bytes of `R₅` are not known as in the reference (table below).

## Why 5 bytes remain

On the 4 states of the rows with control, the bytes of `R₅` are these (seen by the program):

| byte | bits the rows know | value of the known bits |
|---|---|---|
| `SecondaryHardMode` | all but bit 0 | as in the reference |
| `PlayerStatus` | none | |
| `WorldNumber` | none | |
| `AreaMusicBuffer_Alt` | none | |
| `AreaMusicQueue` | all | as in the reference in 2 states, different in 2 |

* `PlayerStatus`, `WorldNumber`, `AreaMusicBuffer_Alt` are not in the condition at the exit of the pipe (`PipeChangeEnd.exitNames`), so the rows do not know them at their start. The frames of the rows do not write a known value to them either.
* The area's setup may set bit 0 of `SecondaryHardMode` (`inc`), depending on `PrimaryHardMode`, `WorldNumber` and `LevelNumber`. The rows do not know `WorldNumber`.
* `AreaMusicQueue` is 0, as in the reference, in the rows of the case where the sound's pause flag is 0, and a value other than 0 in the rows of the other case. In the other case the sound routines do not run, so the queue keeps its value.

With `PlayerStatus`, `WorldNumber`, `AreaMusicBuffer_Alt`, `PrimaryHardMode`, `LevelNumber` added to the condition at the exit, only `AreaMusicQueue` should remain (not tried). That condition comes from the condition at the entry, so the condition at the entry would have to know them too. `PipeChangeEnd` is not changed here.

## Real runs

The program is `room-start-check FM2 [N]`.

| inputs | runs | not `Room` at control | of them with the exit's condition | not `RestAt` |
|---|---|---|---|---|
| TAS | 1 | 0 | 0 | 0 |
| no input | 15 | 0 | 0 | 0 |
| random, no Start | 300 | 0 | 0 | 0 |
| random, Start only on the pipe's frames | 300 | 41 | 0 | 41 |

In each of the 41 runs without `Room`, only `AreaMusicQueue` differs, and none meets the condition at the exit (`chg.quiet₁`). So these runs are outside the theorem. The old assumption `chg.roomStart` failed on the same 41 runs.

## Assumptions (not proved in Lean)

* **`chg.roomRest`.** At the first control in the room, the bits of the 5 bytes of `R₅` are those of the reference. It fails for a fire Mario (`PlayerStatus` 2).
* **`chg.first₁`**, **the conditions of the change.** As in [The state at the first control in the room](c-7-2-RoomStart.md).

**Files.** `Theorems/ScreenStart.lean`, `Theorems/Route.lean` (`roomRest`, `RoomChecks`, `Changes.roomAt`), private `Proof/ScreenStart.lean`.
