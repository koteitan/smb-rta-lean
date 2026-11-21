[← Back](README.md) | [English](e-2-10-3-8-PositionKeep.md) | [Japanese](e-2-10-3-8-PositionKeep-ja.md)

# A frame that keeps a speed to the right, or makes no call, keeps its position after the scroll handler

**Claim.** Take a frame in control, with the hypotheses of `PositionWriters.writers_end`. Let Q be the machine at the scroll handler, at instruction q, and b the machine at the frame's end. Assume two conditions on each instruction R from q to the frame's end:

- `PosW(R)`: if R stores a byte of the position (pixel, page, fraction) by its address, then R is inside the push (`ImpedePlayerMove`) or the clamp at the screen's edge (`innerP`); and if R is outside them and is not plain (it stores through an index or a pointer), then R writes no byte of the position. Round 23: the second part is not asked of a store through an absolute address and an index whose base no index can take to a byte of the position (`absFar`, below).
- `ClampR(R)`: if R is the clamp's entry and v(R) > 0, then the clamp's target is P(R).

Then (`keep_frame`):

```
0 < v(Q)  ∧  v(b) = v(Q)   →   P(b) = P(Q)
```

This is the field `AfterP.keep`. It is no longer a field: on the frames above ground it is the theorem `SurfaceFrames.OnFrames.keepAt`, and `posW` and `clampR` are new fields of `OnFrames`, one instruction at a time. The same theorem also gives `CollideS.P` on these frames, so `collide` no longer asks the position on a frame with 0 < v(Q) and v(b) = v(Q).

A second theorem needs `PosW` only (`still_frame`): if no instruction from q to the frame's end is at the push's entry or at the clamp's entry, then

```
P(b) = P(Q)
```

On the frames above ground this is `SurfaceFrames.OnFrames.stillAt`, and `collide` asks the position only of a frame that calls the push or the clamp after the scroll handler (`Calls`).

**Proof.** On such a frame every machine from q on has the speed v(Q) (`FrameW.kept`, by the speed's walk). The frame from q to b is a chain of pieces (`PositionDispatch.Edge`), and each piece keeps the position (`piece_keep`):

- At the push's entry R: a push that moves sets the speed to 0 (`ImpedePosition.routine_return`). The speed after the push is v(Q) ≠ 0, so the push does not move him: its effect is 0. The routine gives P(after) ≡ P(R) (mod 2²⁴), and both are in the position's range, so P(after) = P(R). The margins 256 ≤ P(R) and P(R) + 256 < 2²⁴ that `PositionWriters.ready_all` asked are not needed.
- At the clamp's entry R: v(R) = v(Q) > 0, so by `ClampR` the target is P(R). So the target is in the position's range, and the clamp's effect is 0. The condition Y = 0 of `ready_all` is not needed (`AtW` gives Y ∈ {0, 1}).
- At any other reached instruction R: R is not inside the two calls (`reached_in`). If R is plain, the walk's `AtW.rom` and `PosW` give that it writes no byte of the position (`PositionWriters.ordinary_plain`). If R is not plain and `absFar(R)`, `ordinary_absFar` gives it (round 23). Otherwise `PosW` says so directly.

The chain reaches b, so P(b) = P(Q) (`keep_end`). On a frame with no call, every piece is an ordinary step (`piece_ord`), so P(b) = P(Q) too (`still_end`). `keep_frame` puts this on a real frame: the scroll handler's machine is in the frame, or it is the frame's end (`PositionWriters.subs_frame`), and the frame ends within `fuelPerFrame` instructions (`FrameW.ends`). The checks on the ROM are `pCheck` (the walk of `PositionWriters` with its list of nine writers, the push, the clamp, the scroll handler not inside the two calls, the idle loop), a part of `numbersCheck`.

**Round 23: stores through an absolute address and an index (`absFar`, `ordinary_absFar`).** Let R store through the address b + X or b + Y (the opcodes whose write `StepWrites.wOf` gives as `wAbx` or `wAby`), with b the two bytes after the opcode. If for every index u from 0 to 255 the RAM byte of b + u is not a byte of the position, then R writes no byte of the position, whatever its index:

```
absFar(R)  :=  op(R) ∈ absXOps ∪ absYOps  ∧  ∀ u < 256, ramIdx(b + u) ∩ {pixel, page, fraction} = ∅
absFar(R)  →  Ordinary(R)                                   (ordinary_absFar; R's instruction and its two next bytes in the program's half)
```

The proof reads the step's written bytes (`StepWrites.stepLocs`): an interrupt pushes on the stack's page, a halted machine writes nothing, and otherwise the write goes to `ramIdx(b + X)` or `ramIdx(b + Y)`. The check is on the instruction's own bytes, so no walk and no check on the ROM changed. `posW` no longer asks its second part at these instructions. The program `pos-index-sites` counts the instructions that are not plain at the states of the walk of `PositionWriters` from the scroll handler: 729; none inside the push or the clamp; 306 of them `absFar`; 111 more through an absolute address and an index that can reach the position; 312 through the zero page and an index (`STA`, `STY`, `INC`, `DEC`) or a pointer (`STA (zp),Y`). So `posW` asks its second part at 423 of the 729 places.

**What changed in the fields.**

- Removed: `AfterP.keep` (the field `moves` asked all of `AfterP`; now it asks `AfterP.stop` only: `Moves.stop`).
- Narrowed: `collide` (`CollideS.P`) is asked only of a frame that calls the push or the clamp after the scroll handler (`Calls`, a new argument of `CollideS`), and not when 0 < v(Q) and v(b) = v(Q). On the measured frames below, 56,083 of the 66,609 frames make no call.
- Added: `OnFrames.posW` and `OnFrames.clampR`, on each instruction from the scroll handler to the frame's end of each counted frame before the touch.
- Round 23: `OnFrames.clampR` is asked only on a frame that moves right at the scroll handler and ends with that speed (0 < v(Q), v(seq j) = v(Q)), since `keep_frame` uses `ClampR` only there. Its hypothesis `hcr` changed so:

```
hcr : ∀ k n, n₀ ≤ k ≤ n,  pc(trace k) = PlayerSubs,  0 < v(trace k),  v(frame) = v(trace k),  trace n in the frame  →  ClampR(trace n)
```

`posW` is the part of round 21's conditions 1 and 2 (`ready_all`) that the walk does not prove: the walk proves that only nine instructions store the position by its address, and that a plain instruction writes no byte of the position elsewhere. Of the nine, four are inside the push and the clamp; `posW` says the other five (the platform's routine, the vine's routine, the castle's loop) do not run. Round 21's conditions 3 and 4 are not asked.

**What is not proved.**

- `posW`: the five outside instructions are kept away by the level's data (no horizontal platform, no vine, no loop command), which the walk does not know; and 423 instructions met by the walk store through an index or a pointer that could reach the position (round 23; round 20 counted 402 in another walk).
- `clampR`: the clamp at the left edge keeps the position when he moves right only if he is not left of the screen's left edge. That links the frame to the frames before. Round 23: the frame-start relation left(M) ≤ pixel(M) is false on real runs (a frame can start 1 px left of the edge, with the speed 0 and Right blocked); see [the screen's left edge at the frame's start](e-2-10-3-10-ScreenEdge.md). On a frame that keeps a speed to the right it held on every measured frame.
- `AfterP.stop`, and `CollideS.P` on the frames with a call: they need the number of the calls in a frame (the order is proved: [1-1-e-2-10-3-9](e-2-10-3-9-PositionOrder.md)), and the relation of the clamp's edge to the frame's start. Round 23: `CollideS.P` is false on a real frame ([1-1-e-2-10-3-10](e-2-10-3-10-ScreenEdge.md)).

**Measured.** `pos-keep-real` (a program, no part of the proof) checks `posW` (in the stronger form: no instruction outside the push and the clamp writes a byte of the position) and `ClampR` at every instruction from the scroll handler on, on the runs of `pos-after-real`: the TAS from frame 852, random runs from control, runs into the screen's left edge, random runs from the TAS's frames 1002 to 1091, and runs with Select.

| runs | frames with Q | instructions checked for `posW` | `posW` fails | clamps | clamps with v > 0 | `ClampR` fails | frames 0 < v(Q), v(b) = v(Q) | P(b) ≠ P(Q) on them |
|---|---|---|---|---|---|---|---|---|
| TAS from frame 852 | 239 | 699,151 | 0 | 0 | 0 | 0 | 233 | 0 |
| 64 random runs from control | 12,677 | 40,928,879 | 0 | 2,152 | 126 | 0 | 7,015 | 0 |
| 120 runs into the left edge | 35,938 | 118,047,278 | 0 | 6,359 | 721 | 0 | 16,705 | 0 |
| 128 random runs from the TAS's frames 1002 to 1091 | 14,416 | 26,981,577 | 0 | 268 | 11 | 0 | 8,023 | 0 |
| 32 runs with Select | 3,339 | 11,150,049 | 0 | 377 | 15 | 0 | 2,061 | 0 |
| all | 66,609 | 197,806,934 | 0 | 9,156 | 873 | 0 | 34,037 | 0 |

No frame had two calls: after Q each frame had no call, one clamp, or one push. On the frames with 0 < v(Q) that end with the speed 0, P(b) − P(Q) was 0 or −256 (`AfterP.stop` held).

`surface-frames-check` checks `posW` and `clampR` on every clean frame it reads (`movesScan`), and `collide` in its narrowed form: with 200 random runs, 215,433 such frames, 0 failures. `collide-real` checks `CollideS.P` without the call condition.

**File:** `Theorems/PositionKeep.lean`. Changed: `Theorems/PositionWriters.lean` (`FrameW.two`, `FrameW.ends`, `subs_frame`), `Theorems/SurfaceFrames.lean`.
