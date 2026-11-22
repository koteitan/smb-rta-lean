[← Back](README.md) | [English](c-7-6-1-EarlyFall.md) | [Japanese](c-7-6-1-EarlyFall-ja.md)

# The stored speed before `C + 37`: `ab_early` only from the end of the fall

The field `ab_early` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-6) says that a frame before `C + 37` that does not follow the model reads a stored speed below the air threshold. The theorems use it only from the end of the fall on. This round asks it only there, and on the second frame there only when the frame before does not stop him in the state `AtCtrl` (when it does, `RoomRun.ab_fresh` of [The stored speed after a stop](c-7-4-3-AbsKeep.md) gives the stored speed).

## Statements

`ab(n)` is the stored speed that frame `n + 1` reads at its player's routine; `CleanR(n)`: frame `n + 1` follows the model (`FrameModel.CleanR`); `Stop(n)`: frame `n` leaves him stopped; `A = AirFastSpeed` is the air threshold (1.5625 px per frame); `fall = 34`, `hitF = 37`.

```
ab_early (field of RoomRun; narrowed, round 32):
  C + 34 ≤ n,  n + 1 < C + 37,  n < t0,  ¬CleanR(n),  (n = C + 34  ∨  CleanW(n − 1)  ∨  ¬AtCtrl(n − 1))   →   ab(n) < A
  (before: C ≤ n in place of C + 34 ≤ n, and no last premise)

RoomCore.ab_of (proved: RoomRun.ab_of_run; its second case changed the same way):
  C ≤ n < t0   →   ab(n) = |v(n)|  ∨
    (Stop(n + 1) ∧ (C + 34 ≤ n → n + 1 < C + 37 → ab(n) < A  ∨  (C < n ∧ ab(n) = |hstep(hs(n − 1), inp(n)).v|)))
```

`CleanW(n − 1)`, `AtCtrl(n − 1)` are as on [The stored speed after a stop](c-7-4-3-AbsKeep.md): frame `n` follows the model; frame `n` comes to its player's routine with the stored speed `|v|` and the side not masked. So `ab_early` is asked of two frames, `n = C + 34` and `n = C + 35` (frames `C + 35` and `C + 36` read the stored speed), in place of 36, and at `n = C + 35` not when frame `n` stops him (`ReadW`) in the state `AtCtrl`: then `ab_fresh` gives the last case of `ab_of`.

Why this is enough: `ab_early` has two users. `RoomRun.stop_run_of` asks it from `C + 34` on; in the case of `ab_fresh` the premise of `RoomCore.stop_run` (every input of the model from the state before keeps the speed below the running threshold, from `safeFrom`) bounds the stored speed instead. `RoomCore.ab_of` is used at a takeoff frame `T + 1` with `T ≥ C + 34` (a takeoff from the floor after the fall: `Approach.T1_ge`, `v_chain2`), with no wall hit, and at three more places that use only its first case. With no wall hit frame `T` follows `hstep` (`NoWall`), so `hstep(hs(T − 1), inp(T)) = hs(T)` and the new case says `ab(T) = |v(T)|`, which those proofs already handle. No theorem asks the stored speed of a frame in the fall.

## Measured

`room-ab-check FM2` (the TAS and 2,800 runs of own inputs from first control):

| | frames |
|---|---|
| before `C + 37`, not following the model (the old field; none on the TAS) | 10,184 |
| of them from the end of the fall on | 516 |
| of them at `n = C + 34` (the field) | 316 |
| of them at `n = C + 35`, frame `n` stopping him in the state `AtCtrl` (proved by `ab_fresh`) | 117 |
| of them, the stored speed not `|hstep(hs(n − 1), inp(n)).v|` (a bug of `ab_fresh`) | 0 |
| of them at `n = C + 35`, the other frames (the field) | 83 |

So the field asks 399 of the measured frames. Their stored speed is at most 0.5 px per frame, below the air threshold (1.5625 px per frame) on all.

## What remains (not proved)

- `ab_early` at `n = C + 34`, and at `n = C + 35` when frame `n` follows the model or comes to its player's routine with a stale stored speed or a masked side. At `n = C + 34` the case of `ab_fresh` would need a bound on `hstep` from the state at `C + 33`, in the fall, which `stop_run`'s users do not have (`safeFrom` starts at the end of the fall).
