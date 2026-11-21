[← Back](README.md) | [English](e-2-10-3-15-PlaceKeep.md) | [Japanese](e-2-10-3-15-PlaceKeep-ja.md)

# His place at the player's routine

**Claim (round 27).** Two theorems, proved and not used by the route yet (`Theorems/PlaceKeep.lean`).

1. `PlaceKeep.keep_place`: a frame in control keeps five bytes from its first arrival at the player's routine `n₀` to its first scroll handler `Q` after it: the side collision's timer, his place on the screen, the scroll lock, and the pixel and the page of the screen's left edge (`placeI`, the operands of the scroll handler's loads). The conditions are those of the edge's walks (1-1-e-2-10-3-13): the frame starts in control, each instruction meets `CleanK` of `guardF` and writes neither the routine, nor the mode, nor the task by its address, and the area's bytes are known. The check on the ROM is `PlaceKeep.placeCheck` (natively true, 3.4 s with the load; it is not in `numbersCheck`, so `keep_place` holds for the route's frames once a later round adds it there).

```
∀ x ∈ placeI,  ram(Q)[x] = ram(n₀)[x]
```

2. `PlaceKeep.edge_step_place`: the edge's step of a frame from two conditions on one state each, without `collide`:

```
PlaceAt(n₀)  :=  side(n₀) = 0  →  thr ≤ pfs(n₀)  →  left16(n₀) + thr ≤ pixel16(n₀)
AmountAt(Q)  :=  Allows(Q)  →  xs(Q) + 1 ≤ thr

side = the side timer, pfs = his place on the screen, thr = the scroll's first threshold (80 px), xs = the byte the move stores

scroll's rule (Q → R) ∧ edge(Q) = edge(M) ∧ edge(b) = edge(R) ∧ keep_place ∧ pixel16(n₀) = pixel16(M) ∧ PlaceAt(n₀) ∧ AmountAt(Q) ∧ plat(Q) = 0
   →  edge(b) ≤ max(base(M), P(b))
```

When the edge moves: edge(b) = edge(R) ≤ 256·(left16(n₀) + Y) + 255 ≤ 256·(pixel16(M) − 1) + 255 < P(M) ≤ base(M), with Y ≤ xs(Q) ≤ thr − 1.

**The walk.** `FrameKeep.guardE` cannot protect the side timer: the timer part of the frame decrements it by a store through an index, and `CleanK` asks every such store to miss the protected bytes. So `walkQP` follows the bytes without protecting them. A store whose target the walk does not know then stops the following (`PipeWrites.AS.forgetK`). Between `n₀` and `Q` such stores come only in the move routine: it stores the fraction, the pixel and the page through an index, with targets that cannot be any of the five bytes (an absolute base that no index takes to the byte, `PositionKeep.absFarAt`, or a zero page base, below 256). At such a store `walkQP` keeps following (`kstepP`, `s_kstepP`, with `StepWrites.step_ram`). Without that step 14 states of the walk's table lost the byte at the move routine's store; with it, none.

**False as a field.** This round also tried to put `place := PlaceAt(n₀)` and `amount := AmountAt(Q)` in place of the field `near` (then `edgeAt` needs no `collide`). It built (`prove.py` exit 0, `route_1_1` without `sorryAx`), and `edge-real FM2 256` found no failure on 137,955 frames. But `surface-frames-check FM2 200` exited 1: `place` fails on 8,640 frames of its set "overwritten states around the stairs". That set takes the movie's state at frame 200 and overwrites his position (48 px left to 46 px right of it), height, speeds and state, but not his place byte. For the 8 offsets 48 to 34 px left, he is 64 to 78 px right of the edge while the byte still says about 112: 8 × 30 × 4 × 3 × 3 = 8,640 runs. On every real frame measured the byte at a frame's start is (pixel − left) mod 256, and on the other seven sets (239,510 − 103,680 frames) `place` never fails. `near` holds on all eight sets, so the route keeps `near`.

**Measured** (the trial with the fields, binary of the trial; the walk's check natively):

| check | what | result |
|---|---|---|
| native test of `placeCheck` | the walks of the five bytes | true |
| `edge-real FM2 256` | `place` and `amount` | 137,955 frames, 0 failures; the most xs on an allowed arrival 3; the least pixel − left at an arrival with the byte at least the threshold and the side timer 0: 80 |
| `surface-frames-check FM2 200` | `place` and `amount` | `place` fails on the 8,640 overwritten frames above; `amount` 0; every other condition 0 |

**What is not proved.** `PlaceAt` and `AmountAt`. `PlaceAt` needs the frame before, from its scroll handler to its drawing (the clamp, the push), and the timer part of this frame. `AmountAt` needs the move's stored byte in the model of the move (`FrameModel`).

**File:** `Theorems/PlaceKeep.lean` (`zpIOps`, `miss_loc`, `farRk`, `kstepP`, `s_kstepP`, `walkQP`, `qP_run`, `placeI`, `pbCfg`, `placeCheck`, `keep_place`, `PlaceAt`, `AmountAt`, `edge_step_place`). No other file uses it.
