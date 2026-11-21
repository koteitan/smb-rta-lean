[← Back](README.md) | [English](e-2-10-3-14-PlatformForce.md) | [Japanese](e-2-10-3-14-PlatformForce-ja.md)

# The platforms' force on the scroll

**Claim (round 27).** At the scroll handler `Q` of each counted frame before the touch, the platforms' force on the scroll is 0 (`SurfaceFrames.OnFrames.platQ`):

```
1 ≤ j < g  →  ∃ kq ≥ arrAt(fm j, pad j),  pc(Q) = PlayerSubs  ∧  plat(Q) = 0,      Q = trace(fm j, pad j, kq)

plat(m) = the byte that the scroll handler adds to the byte the move stores (Platform_X_Scroll)
```

So at `Q` the scroll's amount is the byte the move stores, X(Q) = xs(Q). The field `near` of `OnFrames` now asks this simpler condition on the one state `Q` (`EdgeStep.NearX`):

```
NearX(Q)  :=  Allows(Q)  →  left16(Q) + xs(Q) + 2 ≤ pixel16(Q)

near_of_x :  NearX(Q) ∧ plat(Q) = 0  →  Near(Q)        Near(Q) := Allows(Q) → left16(Q) + X(Q) + 2 ≤ pixel16(Q)   (round 26)
```

`Allows`, `left16`, `pixel16` are those of the scroll's rule (1-1-e-2-10-3-12) and of the edge's step (1-1-e-2-10-3-13). No new field. `FrameKeep.guardE` protects one byte more, the platforms' force (70 bytes; the union guard of `chg.upCleanU` 147). So `keep.cleanE` and `chg.upCleanU` ask a little more: no store through an index or a pointer writes this byte.

**Proof.** The walks of the edge's step (1-1-e-2-10-3-13) follow the byte as a third byte (`EdgeStep.eI`):

1. At control it is 0: the rows of the change out of the side pipe know it, with the value of the machine at control (`SurfaceFrames.Start.plat`), and there it is 0 (`numbersCheck`). So plat(seq 0) = 0 (`AreaRun.plat₀`).
2. The frames not counted keep it (`EdgeStep.keep_noCut`, `OnFrames.edgeLag`), and so does each counted frame from its start to `Q` (`EdgeStep.keep_q`).
3. The scroll handler stores 0 to it at its end. The walk from `Q` to the instruction after the call (`R = PlayerSubs + 3`) knows it as 0 there (`EdgeStep.atR`, a part of `rCheck`).
4. From `R` to the frame's end the byte is kept (`EdgeStep.keep_r`). The only other store to it in the ROM is in the platforms' routine, right after a store to his position by its address. The field `posW` excludes that store, and the walk stops a path there (`cutPos`).

So plat(seq j) = 0 for 1 ≤ j < g (`OnFrames.platEnd`), and plat(Q) = plat(seq (j − 1)) = 0 (`OnFrames.platPrev`, `OnFrames.platQ`). The edge's step (`OnFrames.edgeAt`) now takes `Near(Q)` from `NearX(Q)` and `plat(Q) = 0` (`EdgeStep.near_of_x`). The common part of the proofs of `edgeAt` and `platEnd` is `OnFrames.scrollAt`.

**The checks on the ROM.** `EdgeStep.qCheck` and `EdgeStep.rCheck` follow three bytes now; `numbersCheck` also asks plat(B.m) = 0 and that the scroll handler's addend is this byte (`Numbers.platB`, `Numbers.platP`). Before the change, a native test of the three new parts passed (30 s with the load).

**Measured** (exit 0 on the final program):

| check | what | result |
|---|---|---|
| `edge-real FM2 256` | the platforms' force at each scroll handler and each frame start; `NearX` at the scroll handler: the movie from 852, runs against the pipe at the left edge, random runs of my own | 137,955 frames; the force not 0 at 0 scroll handlers and 0 frame starts; the scroll allowed at 11,289 scroll handlers, where the least pixel16 − left16 − xs − 2 is 78 (`NearX` asks ≥ 0) and the most X is 3; `near` fails 0 |
| `surface-frames-check FM2 200` | `near` (`NearX`) among the conditions of `movesScan`; the state at control from the rows (`Start`, with the new byte) | 8 sets, 239,510 frames, 215,433 frames checked on `Moves` and `near`: 0 failures; 201 runs of the change reach control in the state of `Start` |
| `keep-frames-check FM2 100` | `CleanK` of the new `guardE` on every instruction above ground, counted or not | 224,813 frames, no store through an index or a pointer to a protected byte |
| `up-clean-u FM2` | `CleanK` of the guard of `chg.upCleanU` on the frames up to the vertical pipe | `guardE` 70 bytes (69 before), the union guard 147 (146 before); 221,490 frames, no instruction against it |
| `route-check` (the movie; 1089 `02808080`; 996 with the jump run of round 23) | the route | touch 1092, 1093, 1396; level change 1748, 1748, 2063 |
| `collide-real FM2 200`, `pos-after-real FM2 200`, `pos-keep-real FM2 64` | the other fields of part e | exit 0 |

**What is not proved.** `NearX(Q)` is assumed. These were tried and measured this round:

* A condition at the frame's start `M` in its place. Measured (`edge-real`): where his place byte is at least the scroll's threshold and the side timer is at most 1, pixel16(M) − left16(M) ≥ 80; where the byte is at least the threshold and pixel16(M) − left16(M) is below it, the side timer is 16 (the frame right after a push: he is 1 px left of the edge, so the byte, (pixel − left) mod 256, is 255). The walks of `EdgeStep` cannot carry the side timer: the timer part of the frame decrements it by a store through an index, and `CleanK` asks every such store to miss the protected bytes.
* The same condition at the first arrival at the player's routine, after the timer part: a new walk carries the side timer, his place byte, the scroll lock and the edge from there to the scroll handler, and with a bound on the scroll's amount this gives the edge's step without `collide` (proved: [His place at the player's routine](e-2-10-3-15-PlaceKeep.md)). It is not used: the condition is false on 8,640 overwritten states of `surface-frames-check`, where `near` holds.
* The scroll's amount: the byte the move stores (`xs`) is at most 3 on real frames, but the model of the move (`FrameModel`) does not know it.

**File:** `Theorems/SurfaceFrames.lean` (`Start.plat`, `numbersCheck`, `AreaRun.plat₀`, `AreaRun.platP`, `OnFrames.scrollAt`, `platEnd`, `platPrev`, `platQ`, `edgeAt`, the field `near`). Also changed: `Theorems/EdgeStep.lean` (`platI`, `eI`, `atR`, `keep_r`, `NearX`, `near_of_x`), `Theorems/FrameKeep.lean` (`edgeE`). `Main.lean`: `edge-real` measures the byte, `NearX` and the condition at the frame's start.
