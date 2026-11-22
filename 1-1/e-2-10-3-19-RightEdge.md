[← Back](README.md) | [English](e-2-10-3-19-RightEdge.md) | [Japanese](e-2-10-3-19-RightEdge-ja.md)

# The screen's right edge in the scroll handler

The routine of the player's offscreen bits ([the side of the clamp at the screen's edge](e-2-10-3-18-ClampSide.md)) reads the screen's right edge and its left edge. Round 30 proved the clamp's choice when the right edge is 255 px right of the left edge, and asked that relation, and that the left edge's page is not 255, as the field `rightRel`. Here both halves are proved, so `rightRel` is gone and no field takes its place.

The right edge's two bytes are one byte after the left edge's. The game writes them only in one routine (GetScreenPosition: the left edge plus 255 px, with the carry into the page), which the scroll calls right after it moves the left edge and which the area's start calls, and in the castle's loop back, which also moves his page (a store that the field `posW` excludes).

**Claim (round 31).** Write

```
left16(m)  = 256·page + pixel of the screen's left edge
right16(m) = 256·page + pixel of the screen's right edge
Rel(m)     := right16(m) ≡ left16(m) + 255   (mod 2¹⁶)
PageOK(m)  := the left edge's page at m is not 255
```

1. `RightEdge.scroll_rel`: take a real machine Q at the scroll handler's call (`PlayerSubs`, with `Good`). There is k such that `stepN k Q` is in the frame at the routine of the offscreen bits, with the stack 2 below that of Q, the call's return address on the stack, his position (pixel, page, fraction) that of Q, and

```
Rel(Q) → Rel(stepN k Q)
```

2. `SurfaceFrames.OnFrames.relAll`: on the frames above ground (`OnFrames`, `AreaRun`),

```
∀ j < g,  Rel(seq j)
```

that is, at control and at the end of every counted frame before the touch.

3. `SurfaceFrames.OnFrames.pageAll`: with the touch not later than `farN` frames after control (as `OnFrames.readAll`),

```
∀ j, 1 ≤ j → j < g → PageOK(seq j)
```

With them `OnFrames.nearStepAt` (`SideTimer.NearM` at the end of each counted frame but the last before the touch) needs only the field `endKeep`: at the routine of the offscreen bits Rel holds (Rel at the end of the frame before, the frames not counted keep the four bytes, `EdgeStep.keep_q` keeps them up to the scroll handler, then `scroll_rel`), and the left edge's page there is that of the frame's end.

These are `RightEdge.scroll_rel`, `OnFrames.relStep`, `OnFrames.relAll`, `OnFrames.readAllP` and `OnFrames.pageAll` (axioms `propext`, `Classical.choice`, `Quot.sound`). The checks on the ROM are `RightEdge.check` and three more checks in `numbersCheck`; the private proof `pole_numbers` checks them by `native_decide` (`RightEdge.check` takes under 1 s natively).

**Proof of 1.** By pieces of the ROM's code, as [the scroll's rule](e-2-10-3-12-ScrollRule.md). The places come from the program: the scroll handler is the target of the call at the end of the player's routine; the call of the right edge's routine is the first `JSR` after the scroll's load of the left edge's page; its target is the routine, and the routine's `RTS` is found from it.

| piece | from | to | known values |
|---|---|---|---|
| `jsr0Check` | the scroll handler's call | the scroll handler's entry | the stack byte (256): the return address on the stack; the four bytes of the edges and his position kept |
| `w1Check` | the scroll handler's entry | the routine of the offscreen bits, or the call of the right edge's routine | nothing: one walk with the stack unknown and kept, every branch both ways. At the routine of the offscreen bits the four bytes, his position and the stack page are kept; at the call the right edge's two bytes, his position and the stack page are kept |
| `jsrCheck` | the call of the right edge's routine | the routine | the stack byte (256): its return address on the stack; the edges, his position and the two stack bytes above kept |
| `gspCheck` | the routine | its `RTS` | the left edge's pixel and page (65,536): the right edge is the left edge plus 255 px, with the carry into the page |
| `rtsOK` | | | the routine ends with an `RTS` |
| `tailCheck` | the instruction after the call | the routine of the offscreen bits | nothing: the four bytes, his position and the stack page kept |

On the paths without the call Rel(Q) is kept, as the four bytes are. On the path with the call the right edge is set from the left edge, which is kept to the routine of the offscreen bits: `ScrollRule.left_add` with 255 gives Rel there.

**Proof of 2.** By induction on the frames. At control: the rows of the change out of the side pipe know the right edge's two bytes too (`Start.rightX`, `Start.rightP`, from `edgeBytes`), and `numbersCheck` checks Rel on the machine at control (`rel_zero`). One frame (`relStep`): the frames not counted keep the four bytes (`OnFrames.edgeLag`), the counted frame keeps them up to the scroll handler (`EdgeStep.keep_q`), `scroll_rel` brings Rel to the routine of the offscreen bits, the clamp keeps both edges (`ClampSide.clamp_end`), the return keeps the RAM (`ret_step`), and from the instruction after the call to the frame's end the walks of `EdgeStep.keep_r` keep the four bytes (with `posW`). For this the walks of `EdgeStep` follow the right edge's two bytes too (`EdgeStep.eI`: 5 bytes), and `FrameKeep.guardE` protects them (`FrameKeep.edgeE`).

**Proof of 3.** `OnFrames.readAllB` bounds the base at the end of each counted frame d: base(seq d) ≤ P(control) + 16·top·d, and the edge is at most the base. `numbersCheck` checks P(control) + 16·top·farN < 65280·256, so the left edge's page is not 255 (`page_of_base`). The bound at frame d uses `OnFrames.edgeAt` at d, which uses `NearM` at the end of frame d − 1 and so `PageOK` there. So `PageOK` is a hypothesis of `nearStepAt`, `nearMAll`, `nearAAt`, `nearAt` and `edgeAt` for the earlier frames, and `readAllP` proves the bound and `PageOK` together, by induction on d.

**Measured.**

| check | what | result |
|---|---|---|
| native test | `RightEdge.check` | true; under 1 s natively (a scratch build) |
| private proofs (`prove.py`) | `pole_numbers` (`numbersCheck` with the three new checks), `side_start` (the rows of the change out of the side pipe know the right edge's two bytes) | true; `Proof.PoleJoin` builds in 89 to 106 s on a loaded machine (round 30: 63 to 72 s), `Proof.SurfaceFrames` in 9 to 11 s |
| `edge-real FM2 256` | at the routine of the offscreen bits on every frame (5 sets, 137,955 frames, clean or not) | the right edge was the left edge plus 255 px and the left edge's page not 255 on every frame (0 against); the selector: no clamp 89,665, the left edge 48,290, the right edge 0, as round 30 |
| `edge-real FM2 256`, `surface-frames-check FM2 200` | `movesScan`: `right edge (a theorem)` (Rel at the frame's start, at each routine of the offscreen bits and at the end), `leftPage (a theorem)` (at the end), and `endKeep` as narrowed | 0 failures. `edge-real` fails only on the old stored speed and `after` on frames that do not start clean, with the counts of round 30; `surface-frames-check` 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included |
| `up-clean-u FM2` | `chg.upCleanU` with the right edge's two bytes protected | 0 against |
| `keep-frames-check FM2 100` | `keep.cleanE` with them | bad 0 |
| `pos-keep-real FM2 64`, `collide-real FM2 200`, `pos-after-real FM2 200` | `posW`, `clampR` (which `endKeep`'s narrowing uses), `collide` | 0 failures |
| `route-check FM2` | the whole route | touch 1092, level change 1748; with `1089 02808080` 1093 and 1748; with 996 and the round 23 jumprun 1396 and 2063 |

**Also (round 31): `endKeep` asks less.** On a frame that moves right at the scroll handler and ends with that speed, the pixel part of `endKeep` is a theorem (in `OnFrames.nearStepAt`): the frame ends at the position of the scroll handler (`OnFrames.keepAt`), and when the routine of the offscreen bits calls the clamp, the field `clampR` at the clamp's entry says that the clamp's target is his position, so the clamp leaves him where he is. For this the routine's pieces (`ClampSide.W0`) and the pieces of `RightEdge` (`edges`) keep his speed too. So `endKeep` asks its pixel part only on frames that call the push or the clamp and do not keep a speed to the right:

```
endKeep : … → EndKeep(Calls(Q) ∧ ¬(0 < v(Q) ∧ v(seq j) = v(Q)), Rt, seq j)      (round 30: EndKeep(Calls(Q), Rt, seq j))
```

**On the route.** The field `OnFrames.rightRel` is gone. No new field. New checks in `numbersCheck`: `RightEdge.check`, Rel on the machine at control, and P(control) + 16·top·farN < 65280·256 (`Numbers.rightC`, `relB`, `pageB`; `AreaRun.rc`, `rel₀`, `pageB`). `Start` has the right edge's two bytes: the rows of the change out of the side pipe know them (the private proof `side_start` checks it). Two hypotheses ask more than before: `FrameKeep.guardE`, and so the condition on each instruction of the run (`chg.upCleanU`, `keep.cleanE`), protects the right edge's two bytes too; they are written only by address.

**What is not proved here.** `endKeep`. Its pixel part (now only on frames that call the push or the clamp and do not keep a speed to the right) needs: after the call only the pushes move him, and a frame that ends with the side collision's timer at most 1 has no push after the call. Its place-byte part (on every frame that ends with the timer at most 1, the lock 0 and the place byte at least the threshold) needs: the drawing writes his place on the screen as pixel − left edge mod 256. `Moves.stop`: it needs his place relative to the left edge at every frame's start, not only under the conditions of `NearM`.

**Round 32.** The pixel part of `endKeep` is a theorem on every frame that ends with the side timer at most 1, with a new field `sideW` on single instructions ([A push that moves him leaves the side timer at 16](e-2-10-3-20-PushTimer.md)).

**File:** `Theorems/RightEdge.lean`. `Theorems/SurfaceFrames.lean` uses it (`rel_zero`, `rel_congr`, `OnFrames.relStep`, `OnFrames.relAll`, `PageOK`, `page_of_base`, `OnFrames.readAllP`, `OnFrames.pageAll`, `OnFrames.nearStepAt`). `Theorems/EdgeStep.lean` (`eI`) and `Theorems/FrameKeep.lean` (`edgeE`) have the right edge's two bytes, and `Theorems/ClampSide.lean` (`Places.speed`, in `W0`) his speed. `Main.lean`: only the names of the checks in the filters of `edge-real`.
