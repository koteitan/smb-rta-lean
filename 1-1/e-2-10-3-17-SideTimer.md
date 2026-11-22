[← Back](README.md) | [English](e-2-10-3-17-SideTimer.md) | [Japanese](e-2-10-3-17-SideTimer-ja.md)

# The scroll's bytes from the frame's start to the player's routine

**Claim (round 29).** From the start of a counted frame above ground to its first arrival at the player's routine, the side collision's timer falls by one at most, and his place on the screen, the scroll lock and the screen's left edge do not change. A frame that does not come to the player's routine (a paused frame) keeps the timer and these bytes. So the field `nearA` of round 28, at the arrival, is a theorem (`OnFrames.nearAAt`) from `NearM` at the frame's start. `NearM` holds at control, the frames not counted keep it, and the new field `nearStep` asks that each counted frame keeps it from its start to its end.

```
M = K.fm j                     the start of the counted frame j
R = trace(M, pad j, arrAt)     its first arrival at the player's routine

side_at :     side(R) = side(M)  ∨  side(R) = side(M) − 1
side_le :     side(R) = 0  →  side(M) ≤ 1
keep_at :     pfs(R) = pfs(M) ∧ lock(R) = lock(M) ∧ left16(R) = left16(M)
side_noCut :  a frame in control that does not come to the player's routine ends with side = side(M)
keep_noCut :  such a frame ends with pfs, lock and the edge of M

NearM(M) :=  side(M) ≤ 1  →  lock(M) = 0  →  thr ≤ pfs(M)  →  left16(M) + 2 ≤ pixel16(M)
NearA(R) :=  side(R) = 0  →  lock(R) = 0  →  thr ≤ pfs(R)  →  left16(R) + 2 ≤ pixel16(R)      (round 28)

nearA_of_M :  NearM(M)  →  NearA(R)

near_zero :   edge(seq 0) + 257 ≤ P(seq 0)  →  NearM(seq 0)                                      (AreaRun.near₀)
nearStep :    ∀ j, 1 ≤ j → j + 1 < g → NearM(K.fm j) → NearM(seq j)                            (the new field)
nearMAll :    ∀ j, 1 ≤ j → j < g → NearM(K.fm j)

side = the side collision's timer, lock = the scroll lock, pfs = his place on the screen, thr = the scroll's first threshold (80 px),
pixel16 = 256·page + pixel, left16 = the screen's left edge with its page, edge = the edge as a position (256·left16 + 255), P = the position
```

**The timer.** The NMI's timer part decrements a block of timers by `DEC abs,X`, one timer for each value of the index, when the game is not paused and the master timer control is 0 or falls to 0 in this frame. The side collision's timer is one of them. The walks of `CtrlKeep` follow one byte as the counter of `TaintRun` (`Env.rkI`), but `TaintRun` follows only the counter's `DEC abs`: any other write to the counter stops the walk. The new step `gsuccX` also follows `DEC abs,X` of the counter when the index is known (`arkOpX`, proved for every machine in `s_rkOpX`): the counter falls by one, at most once in the frame (`AS.spent`). The flags Z and N after it are not known. The walk `walkX` is the walk of `CtrlKeep` with this step. At the player's routine it asks that the counter is followed; at the end of a frame that does not come there, that the counter is followed and has not fallen. With the bound of `Sim.rkv` this gives `side_at` and `side_noCut`.

**The table.** The walk uses a table of states, from a search that is no part of the proof (`searchX`). In a table that joins states with another value of the pause bit, two states had the pause bit not known, and from each of them a path ended the frame without coming to the player's routine and with the timer fallen; the check was false there. So the table does not join them (`pw`, as the walk of the pause bit in `CtrlKeep`): 17,260 states, and the check is true.

**The other bytes.** The place byte, the lock and the edge's two bytes are not written before the player's routine. The walks of `CtrlKeep` (one for each byte, with the table of `CtrlKeep.cutTable`) show it: `keep_at` at the arrival, `keep_noCut` on a frame that does not arrive. The position is in `CtrlKeep.keepA` (`CtrlKeep.ctrl_keep`, `OnFrames.lagKeep`).

**On the route.** `numbersCheck` has three more checks: `SideTimer.sideCheck`, `SideTimer.keepCheck`, and edge(B.m) + 257 ≤ P(B.m) on the machine of the proof at control. With the edge and the position of `Start`, that last one gives `NearM(seq 0)` whatever the timer, the lock and the place byte (`near_zero`, `SideTimer.nearM_of_edge`). The frames not counted keep the bytes of `NearM` (`OnFrames.nearLag`, `OnFrames.lagKeep`), and `nearStep` carries `NearM` over each counted frame, so every counted frame before the touch starts with `NearM` (`OnFrames.nearMAll`, an induction). Then `OnFrames.nearAAt` gives `NearA` at the arrival, and `OnFrames.nearAt` the old field `near` at the scroll handler as in round 28.

**Fields.** Removed: `OnFrames.nearA`. Added: `OnFrames.nearStep`. `nearStep` asks `NearM` at a frame's end only when it holds at the frame's start, and not of the last frame before the touch. It asks the bound at the start of the next counted frame on one kind of frame where `nearA` asked nothing: the timer is 1 at the start and the frame does not run the timers (the master timer control is at least 2 at the start), so the timer is still 1 at the arrival. This was measured (`nearMore` below).

**Measured** (`surface-frames-check` and `edge-real` check on every frame they run: `nearStep`, and as theorems `NearM` at the frame's start, `side_at` with `keep_at`, and `NearA` at the arrival):

| check | what | result |
|---|---|---|
| native test | `sideCheck`, `keepCheck` | true |
| `edge-real FM2 256` | `nearStep`, the theorems; `nearMore` | 137,955 frames (clean or not) in 5 sets, 0 failures; `nearMore` 0 in every set |
| `surface-frames-check FM2 200` | `nearStep`, the theorems; `nearMore` | 8 sets, 239,510 frames, 215,433 clean frames checked, 0 failures; `nearMore` 0 in every set. The overwritten states around the stairs run 2 frames each, so their first frame starts with his position overwritten and his place byte not: `NearM` held there too |
| `edge-real FM2 256` | for `Moves.stop` (1-1-e-2-10-3): frames with 0 < v(Q), v(b) = 0 and P(b) = P(Q) | 6 frames, each with one clamp at the screen's edge and no push; P(Q) − P(a) is at most 32 on them (1/8 px) |
| a search, no part of the proof | follow the side timer from the scroll handler to the frame's end, as here before the player's routine | the walk loses it at 95 instructions: 77 would keep it as `PlaceKeep.farRk` does, 18 are stores through an index or a pointer whose target the walk does not know and can be the timer |

**Round 30.** `nearStep` is a theorem (`OnFrames.nearStepAt`): the clamp's choice is proved ([1-1-e-2-10-3-18](e-2-10-3-18-ClampSide.md)), and the new fields `rightRel` and `endKeep` hold the rest. What follows is the state of round 29.

**What is not proved.** `nearStep`, and `Moves.stop`. `nearStep` needs the frame after the scroll handler: the drawing writes his place on the screen as (pixel − left) mod 256, the clamp at the screen's edge keeps him at or right of the edge, a push sets the side timer to 16, and no store after the drawing moves him or the edge. The drawing is skipped on every other frame while the injury timer runs, so there the place byte of the frame's start stays. A walk of the timer after the scroll handler would need a new condition on the 18 stores of the search above (as `posW` is for the position).

**File:** `Theorems/SideTimer.lean` (`decTarget`, `isRkDecX`, `decFlags`, `arkOpX`, `s_rkOpX`, `gsuccX`, `s_gsuccX`, `walkX`, `check1X`, `at_cutX`, `end_noCutX`, `searchX`, `sideTable`, `sideCheck`, `startI`, `keepCheck`, `side_at`, `side_le`, `keep_at`, `side_noCut`, `keep_noCut`, `NearM`, `nearA_of_M`, `nearM_congr`, `nearM_of_edge`). Used by `Theorems/SurfaceFrames.lean` (`near_zero`, `AreaRun.near₀`, `OnFrames.nearLag`, `OnFrames.nearMAll`, `OnFrames.nearAAt`).
