[← Back](README.md) | [English](c-7-2-RoomStart.md) | [Japanese](c-7-2-RoomStart-ja.md)

# The state at the first control in the room

**Claim.** [Joining the bonus room](c-5-RoomJoin.md) assumed the horizontal state, the position, the vertical state and the stored speed at first control (`start`, `startP0`, `startP1`, `v_start`, `ab_start`). This is now proved on the real machines. It comes from the rows of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md). The conditions are those of that change, and that `left₁` is not 0 before control. That is a theorem now (`Changes.first₁`), from the time at the exit (`chg.time₁`) and the first control (`chg.ctlFirst₁`), as in [b-3-2](b-3-2-PipeChangeEnd.md). That the room's machine is the change's machine (`roomCtl`) is a link field. The vertical state and the stored speed are now read from the machine on every frame (`read_vs`, `read_ab`), as the horizontal state and the position are; the proof does not use the stored speed at `C` ([Joining the bonus room](c-5-RoomJoin.md)).

## Statements

`s₀`, `P₀`, `P₁`, `Y_s`, `W_s`, `f_s` are numbers of the room (`RoomJoin.room`, `Nums`). `s₀` is the state (speed, fraction, facing, moving direction, running speed) = (0, 0, 1, 0, 0): stopped, facing right. `P₀ = 256·x_s` and `P₁ = 256·x_s + 255`, where `x_s` is the room's first `x`. `Y_s` is 50 px from the top, `W_s` is 2.375 px per frame, `f_s` is the machine's first fall force.

`hs(m)` is the machine's horizontal state (`FrameModel.readHS`), `P(m)` the position (`posP`), `pix(m) = 256·page + x`, `vs(m)` the vertical state (`SurfaceFrames.vsOf`), `ab(m)` the stored speed. `VY(s) = 256·y + fraction`, `VW(s) = 256·vy + fraction`.

```
StartAt(m)       :  hs(m) = s₀  ∧  P₀ ≤ P(m) ≤ P₁
                    ∧  vs(m).st = 2  ∧  VY(vs m) ≤ Y_s  ∧  VW(vs m) ≤ W_s  ∧  vs(m).vfd = f_s
                    ∧  ab(m) = 0

startCheck       :  every state S of the rows of the two cases of the change (rowsA, rowsB)
                    knows the bytes of control (OperMode, OperMode_Task, GameEngineSubroutine),
                    and if it has control, it knows the bytes of the horizontal state, page, x, the vertical state and the stored speed, and
                    hs(S) = s₀  ∧  P₀ ≤ 256·pix(S)  ∧  256·pix(S) + 255 ≤ P₁  ∧  the vertical state and ab as above

start_of_rows    :  startCheck ∧ InRows(m) ∧ ctl(m)  →  StartAt(m)
left_during      :  During(m)  →  left(m) ≠ 0
PipeRun.inRows   :  EndStatement ∧ PipeRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  InRows(seq b)
PipeRun.start    :  EndStatement ∧ startCheck ∧ PipeRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  StartAt(seq b)
Route.Changes.first₁ :  pipe_end ∧ Changes  →  ∀ n ∈ [a₁, b₁), left₁(seq n) ≠ 0       (from time₁ and the theorem ctlFirst₁)
Route.Run.roomStart :  pipe_end ∧ room_start ∧ Run  →  StartAt(room.fm room.C)
```

`PipeRun.inRows` shows by induction on the frames that every machine from the entry to control is a state of the pipe's frames (`During`) or in the rows (`InRows`). A frame of the pipe uses `step`, a frame in the rows uses `rows`. `rows` gives "`left` is 0 already" or "the next machine is in the rows too". `Changes.first₁` rules out the first. The last machine has control, so `left = 0` (`atControl`). A state of the pipe's frames has `left = timer + 43 > 0`, so the last machine is in the rows.

`RoomRun.toCore` and `RoomRun.entry_ge` take `StartAt(fm C)` as an argument. With `read_hs`, `read_P`, `read_vs` at `C` it gives `start`, `startP0`, `startP1`, `v_start`.

## The check

`room_start` (private, `native_decide`). It computes the rows and looks at their states. About 3 s in a program, about 4 s in the proof build. Both cases have 44 rows, with 8122 and 1924 states. Each case has 2 states with control. All of them have `s₀`, the room's first position, the falling state, the height 48 + 104/256 px from the top, the downward speed 2 + 88/256 px per frame, the machine's first fall force, and the stored speed 0.

## Real runs

The program is `room-start-check FM2 [N]`. The entries are the reference entry, the TAS's entry, and 13 real entries.

| inputs | runs | no control | `left₁ = 0` before control | not `StartAt` at control |
|---|---|---|---|---|
| TAS (control at frame 653) | 1 | 0 | 0 | 0 |
| no input | 15 | 0 | 0 | 0 |
| random, no Start | 300 | 0 | 0 | 0 |
| random, Start only on the pipe's frames | 300 | 0 | 0 | 0 |

## Assumptions (not proved in Lean)

* **`chg.time₁` (with the theorem `Changes.ctlFirst₁`).** At the exit the sound's pause flag is 0 and the game timer is not 000, and `b₁` is the first control after the entry by its definition. They give `left₁` not 0 before control (`Changes.first₁`). A run whose timer is 000 at the exit fails `time₁`: with the timer written to 000 at the entry, `left₁` is 0 at frame 91, and there the routine is the death's, with no control.
* **`roomCtl`.** `room.fm room.C = base.seq b₁`: the room's first machine is the change's last machine. It is a theorem (`Run.roomCtl`): the room's machines are those of `base` from frame `b₁` on.
* **`read_vs`.** `fr.vs n = vs(fm n)` for `C ≤ n ≤ t₀`: read from the machine, as `read_hs` and `read_P` are. It is a reading, not a fact about the run. It replaces `vs_C`, which was the same on the frame `C` only.
* The conditions of the change (the condition at the entry `Run.entry₁`: `chg.entryRest₁`, `upClean₁` with `title`; `places₁`, `quiet₁`, `noStart₁`). They are the assumptions of [The change into the room without `fall`](b-3-2-PipeChangeEnd.md).

**Files.** `Theorems/RoomStart.lean`, `Theorems/RoomJoin.lean` (`StartAt`, `read_vs`), `Theorems/Route.lean` (`Changes.first₁`, `time₁`, `ctlFirst₁`, `Run.roomCtl`, `Run.roomStart`), private `Proof/RoomStart.lean`.
