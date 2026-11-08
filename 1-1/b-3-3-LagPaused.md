[← Back](README.md) | [English](b-3-3-LagPaused.md) | [Japanese](b-3-3-LagPaused-ja.md)

# A `lag` frame of the change into the room

**Claim.** In the change into the room, a frame that ends with the game paused takes nothing off `left`. So the hypothesis `keep₁` of [the whole route](0-1-Route.md) is gone. In its place `Changes` has the field `paused₁`: each `lag` frame of the change ends with the game paused. This is a condition on one bit of one state, the machine at the end of the frame.

The notation is that of [the change into the room without `fall`](b-3-2-PipeChangeEnd.md). `Paused(m)` says that the low bit of `GamePauseStatus` is set in `m`:

```
Paused(m)  :  m[GamePauseStatus] & 1 = 1
```

**The statement.** `EndStatement` has two new parts. Both come from the check `pipe_end_checks`:

```
paused :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) → Paused(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsGo :  ∀ m, InRows(m) → ¬Paused(m)
```

The field of `PipeRun`, and of the first change in `Changes`:

```
lagPaused (chg.paused₁) :  ∀ n, a ≤ n < b,  lag(n)  →  Paused(seq (n+1))
```

It replaces

```
lagKeeps (chg.keep₁)    :  ∀ n, a ≤ n < b,  lag(n)  →  left(seq n) ≤ left(seq (n+1))
```

`PipeRun.bound` and `Changes.bound₁` keep their conclusions, `cnt(a) + 91 ≤ cnt(b)` and `e₁ + 91 ≤ c₂`. In the proof, a `lag` frame from a state in `During` keeps `left` by `paused`. A `lag` frame from a state in the rows ends paused, so by `rowsGo` it does not end in the rows. By `rows`, `left` is then already 0.

Lean: `Theorems/PipeChangeEnd.lean` (`notPausedK`, `not_paused_of`, `finRkP`, `finXP`, `z_step`, `not_paused_rows`, `Paused`, `EndStatement.paused`, `EndStatement.rowsGo`, `PipeRun.lagPaused`, `PipeRun.bound`), `Theorems/Route.lean` (`Changes.paused₁`, `Changes.run₁`). The theorems without ROM use only `propext`, `Classical.choice` and `Quot.sound`.

## How it works

**The game.** The NMI reads `GamePauseStatus` after the pause routine. If its low bit is set, the NMI skips the timers and the game's routines. So the pipe's timer does not run. Only the pause routine writes `GamePauseStatus`. The RAM clear after the exit does not reach it.

**The check.** The abstract machine already reads `GamePauseStatus` in two pieces, one for each value of the low bit (`Env.splits`). But the search for the table joined the two pieces on the next instruction. They differ only in the accumulator and the carry, and these are not in the search's key. So the states of the table did not know the bit. Now the low bit of `GamePauseStatus` is in the key (`zskey`, `kb`). The pieces stay apart.

| frames | search steps | states in the table | before |
|---|---|---|---|
| the timer ≥ 2 | 902,238 | 36,062 | 35,607 |
| the timer = 1 | 527,799 | 23,135 | 23,111 |

The check asks two more things at the end of each frame of the pipe:

* The timer ≥ 2: if the counter fell in the frame, the state knows that the low bit is 0 (`finRkP`). So a frame that ends paused leaves the timer as it was.
* The timer = 1: if the frame is the exit, the state knows that the low bit is 0 (`finXP`). So the exit frame does not end paused.

It asks one more thing of the rows after the exit: every state of every row knows that the low bit is 0. The exit has it 0 (`ExitCond`). With no Start on the frames of the game core, the pause routine keeps it 0.

The whole check takes about 23 s in a program (21 s before).

**Frames that run over.** `Frames` also lets the frame after a frame that runs over be a `lag` frame. Such a frame does not end paused. So a run with such a `lag` frame in the change is now outside the theorem. On real runs this does not happen in the change into the room:

* The frames of the pipe end in the idle loop. The check proves it under `Places`.
* After the exit one frame runs over: the frame that clears RAM. The frame after it is the `setup` frame. It is counted, and `left` falls on it.

## Measured

A `lag` frame here is a frame of the change on which the interval timer's phase stays and `left` does not fall.

* `pipe-end-check`: 15 entries (`E`, the TAS entry, 13 real entries). With no input: 0 `lag` frames. With random inputs and no Start: 0. With random inputs and Start only on the pipe's frames: 995. All 995 end paused.
* 14 entries with the same three kinds of inputs: in each run one frame ends away from the idle loop. It is the frame that clears RAM: frame 48 after the entry, or later after pauses. The frame after it is a `setup` frame each time. All 823 `lag` frames end paused.
* `changes-check` on the TAS: no `lag` frame in the change (exit 0). With a pause at frame 450 for 50 frames: 50 `lag` frames, all paused (exit 0). With a pause at frame 380 or 416 for 60 frames: 60 `lag` frames, all paused. These two runs fail `quiet₁` (the pause's sound at the exit), as before this change (exit 1).

## Assumptions (not proved in Lean)

* `paused₁`: each `lag` frame of the change ends paused. Nothing in Lean ties the kind `lag` of `Frames` to the machine. This field does it for the change into the room.
