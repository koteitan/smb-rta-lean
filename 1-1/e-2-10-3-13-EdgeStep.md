[← Back](README.md) | [English](e-2-10-3-13-EdgeStep.md) | [Japanese](e-2-10-3-13-EdgeStep-ja.md)

# The edge's step of a frame

**Claim (round 26).** The old field `edge` of the frames above ground is a theorem (`SurfaceFrames.OnFrames.edgeAt`). For each counted frame `j` before the touch:

```
1 ≤ j < g  →  edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))

edge(m) = 256·left16(m) + 255        the screen's left edge as a position (SurfaceRead.edgeOf)
base(m) = max(P(m), edge(m))         (SurfaceRead.baseOf)
```

In its place there is one new field on one state, at the scroll handler `Q` of each counted frame (`OnFrames.near`, `EdgeStep.Near`):

```
Near(Q)  :=  Allows(Q)  →  left16(Q) + X(Q) + 2 ≤ pixel16(Q)

pixel16(m) = 256·his page + his pixel
left16, X, Allows: as in the scroll's rule (1-1-e-2-10-3-12)
```

and `FrameKeep.guardE` protects two more bytes: the pixel and the page of the screen's left edge (`FrameKeep.edgeE`). So `keep.cleanE` and `chg.upCleanU` ask a little more: no store through an index or a pointer writes these two bytes.

**Round 27.** The same walks follow a third byte, the platforms' force on the scroll, and `rCheck` also asks that it is 0 after the scroll handler's call. So it is 0 at each scroll handler, and the field `near` asks `NearX(Q) := Allows(Q) → left16(Q) + xs(Q) + 2 ≤ pixel16(Q)`, with the byte the move stores in place of `X` (`EdgeStep.near_of_x`): [The platforms' force on the scroll](e-2-10-3-14-PlatformForce.md). `guardE` protects that byte too.

**Proof.** One counted frame `j`, from `M = seq (j − 1)` to `b = seq j`. `Q` is the machine at the scroll handler (the first time after the player's routine) and `R` the machine at the instruction after its call (`PlayerSubs + 3`).

1. edge(start of frame j) = edge(M). The frames not counted end paused and do not come to the player's routine. A walk of `CtrlKeep` follows each byte of the edge, and on every path that does not come to the routine no instruction writes it (`EdgeStep.keep_noCut`, `OnFrames.edgeLag`).
2. edge(Q) = edge(start of frame j), and `Q` is `Good`. The same walk up to the player's routine, then a walk from there to the scroll handler with the byte followed (`EdgeStep.walkQR`, `EdgeStep.keep_q`).
3. edge(R) = edge(Q), or `Allows(Q)` and edge(R) ≤ edge(Q) + 256·Y with Y ≤ X(Q). This is the scroll's rule (`ScrollRule.scroll_edge`, round 25).
4. edge(b) = edge(R). A walk from the player's routine to the scroll handler, a walk from there to `R`, and from `R` a walk to the frame's end with the byte followed (`EdgeStep.walkKP`, `EdgeStep.keep_r`).
5. P(Q) − 256 ≤ P(b). This is a part of `collide` (`CollideE`, `EdgeStep.collideE_lower`).

If the edge does not move, edge(b) = edge(M) ≤ base(M). If it moves, `Near(Q)` gives

```
edge(b) = edge(R) ≤ 256·(left16(Q) + X(Q)) + 255 ≤ 256·pixel16(Q) − 257 ≤ P(Q) − 257 < P(b)
```

(`EdgeStep.edge_step_of`, `EdgeStep.edge_frame`).

**The walks on the ROM** (`EdgeStep.qCheck`, `EdgeStep.rCheck`; both are in `numbersCheck` with `ScrollRule.check`, about 4 s natively together):

* The walks follow each byte as the counter of `TaintRun` (`Env.rkI`): a path fails at any write to it. Their guard protects the byte (`AfterKeep.guardH`), and `CleanK` of `guardE` gives `CleanK` of that guard (`EdgeStep.cleanH_of_E`).
* `walkQR` is the first walk of `AfterKeep` that also refuses a decrement of the byte, so that it needs no condition on the byte's value (`qR_run`).
* `walkKP` is the second walk of `AfterKeep` with one more cut: a path stops at a store to a byte of his position by its address outside the push and the clamp (`cutPos`). The field `posW` says that no instruction from the scroll handler to the frame's end is such a store. Without the cut, the walk of the edge's page fails at one instruction: the loop back of a castle level moves his page and the screen's page back by 4. The walk does not know the world.
* The middle walk, from the scroll handler to `R`, makes the last walk start after the scroll handler, where `posW` holds.

**Measured** (all on the final program, exit 0):

| check | what | result |
|---|---|---|
| `edge-real FM2 256` | the movie from 852, runs against the pipe at the left edge, 256 + 256 random runs of my own; `near` and the old `edge` on every frame | 137,955 frames; the scroll allowed at 11,289 scroll handlers; there the least pixel16 − left16 − X − 2 is 78 (`near` asks ≥ 0), the most X is 3, the least pixel16 − left16 is 81; `near` and `edge` fail 0 |
| `surface-frames-check FM2 200` | `near` among the conditions of `movesScan` | 8 sets, 239,510 frames, 215,433 frames checked on `Moves` and `near`: 0 failures |
| `keep-frames-check FM2 100` | `CleanK` of the new `guardE` on every instruction above ground, the touch's frame included, counted or not | 224,813 frames, no store through an index or a pointer to a protected byte |
| `up-clean-u FM2` | `CleanK` of the guard of `chg.upCleanU` (with the new `guardE`) on the frames up to the vertical pipe | `guardE` protects 69 bytes (67 before), the union guard 146 (144 before); 221,490 frames, no instruction against it |
| `route-check` (the movie; 1089 `02808080`; 996 with the jump run of round 23) | the route | touch 1092, 1093, 1396; level change 1748, 1748, 2063 |
| `collide-real FM2 200`, `pos-after-real FM2 200`, `pos-keep-real FM2 64` | the other fields of part e | exit 0 |

The private build: `Proof.PoleJoin` (whose `numbersCheck` now has the walks of the edge and the scroll's rule) took 60 s (51 s before).

**What is not proved.** `Near(Q)` is assumed. The scroll reads his place on the screen, a byte that the player's drawing writes in the frame before as (pixel − left) mod 256 (measured, round 25). Where that byte is at least the threshold and the side timer is 0, he is at least 80 px right of the edge. This is a relation of two frames; it is not proved.

**File:** `Theorems/EdgeStep.lean`. Also changed: `Theorems/FrameKeep.lean` (`edgeE` in `guardE`), `Theorems/SurfaceFrames.lean` (the field, `numbersCheck`, `AreaRun`, `edgeLag`, `edgeAt`, `nearB` in `movesScan`). `Main.lean`: `edge-real` measures `Near`.
