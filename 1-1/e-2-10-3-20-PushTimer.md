[← Back](README.md) | [English](e-2-10-3-20-PushTimer.md) | [Japanese](e-2-10-3-20-PushTimer-ja.md)

# A push that moves him leaves the side timer at 16

Round 30 asked, in the field `endKeep`, that on a frame that ends with the side collision's timer at most 1 his pixel at the frame's end is that of the scroll handler's return instruction (when the frame calls the push or the clamp after the scroll handler; round 31 narrowed it to the frames that do not keep a speed to the right). Here that part is proved on every frame that ends with the timer at most 1. `endKeep` keeps only its place-byte part, and it is now a condition on the one state at the frame's end. One new condition on single instructions takes the place of the pixel part: `sideW`, asked on the frames where `endKeep` asks something.

The reason in the game's code: the push (ImpedePlayerMove) moves him by 1 px only on its path that first stores 16 to the side collision's timer (and 0 to his speed). The timer falls only in the timers' routine, at the start of a frame, before the player's routine. The clamp at the screen's edge is inside the scroll handler, before its return. So when a frame ends with the timer at most 1, no push after the scroll handler has moved him.

**Claim (round 32).** Write

```
side(m)    = the side collision's timer at m
pix(m)     = his pixel and his page at m (two bytes)
R          = the instruction after the scroll handler's call (PlayerSubs + 3), in the frame
SideW(m)   := a store through an index or a pointer at m does not write the side collision's timer
```

`PushTimer.pix_end`: take a counted frame above ground, in control, with the hypotheses of `EdgeStep.keep_r` (it starts in the idle loop, `CleanK` of `FrameKeep.guardE` on each instruction, no store to the routine, the mode or the task by address, the area's values). It comes to the scroll handler at `kq`, the first time after the player's routine. If from `kq` on each instruction of the frame meets `PosW` (the field `posW`) and `SideW` (the new field `sideW`), then for the instruction R after the scroll handler's call

```
side(frame's end) ≤ 1  →  pix(frame's end) = pix(R)
```

The return instruction of the scroll handler `Rt` is one step before R, and that step keeps the RAM (`SurfaceFrames.ret_step`), so pix(R) = pix(Rt). In `OnFrames.nearStepAt` this replaces the pixel part of `endKeep` on every frame that ends with the timer at most 1, the lock 0 and the place byte at least the threshold (the frames where `NearM` needs the pixel), with or without a call of the push or the clamp; there the field `sideW` gives `SideW`.

The theorems are `PushTimer.pix_end`, `endKS`, `live_stepKS`, `cutS_spec`, `posW_plain`, `cleanS_of`, `sideWL_of` (axioms `propext`, `Classical.choice`, `Quot.sound`). The check on the ROM is `PushTimer.sCheck`, a new part of `numbersCheck`; the private proof `pole_numbers` checks it by `native_decide`. Natively `sCheck` takes about 2 s.

**Proof.** A walk of TaintRun's abstract machine, as the second walks of `EdgeStep.keep_r`: the walk of `CtrlKeep` to the cut, the first walk of `AfterKeep` to the scroll handler, the middle walk of `EdgeStep` to R, and from R one more walk to the frame's end for each of the two bytes of `pix`.

* The walk follows the byte (TaintRun's counter). Just before an instruction that writes it by its address it stops following it (`CollideKeep.rkOff`).
* At the frame's end it asks: the byte is still followed, or the side timer is known to be at least 2 (`finS`).
* On the push's path that moves him, the store of 16 to the timer comes before the store to his pixel and to his page, so after them the walk knows the timer as 16.
* For this the walk's guard protects the timer, his pixel and his page (`guardS`): a store whose target the walk does not know does not forget them. `CleanK` of this guard on the real machine comes from three things (`cleanS_of`):
  * `CleanK` of `FrameKeep.guardE` (the field `keep.cleanE`);
  * for the timer, `SideW` (the field `sideW`);
  * for his pixel and his page, `PosW` (the field `posW`): outside the push and the clamp a store through an index or a pointer writes no byte of his position (`posW_plain`, with `PositionKeep.ordinary_absFar` for a store from a base that no index takes to it). The walk asks at each store through an index or a pointer that it is not inside the push or the clamp, that no interrupt is pending, and that the instruction is in the program's half of the address space (`okS`).
* A path stops at a store to his position by its address outside the push and the clamp (`EdgeStep.cutPos`), which `posW` excludes.
* The walk splits the index at the move routine's entry into 0 and not 0. On the path with 0 after the scroll handler it would come to the move's store through an index to his pixel. No real machine is there: such a store breaks `posW` (or `SideW` for the timer). So the walk stops a path at a store through an index whose target it knows and which is one of the three bytes (`cutS`, `cutS_spec`).
* At the frame's end: if the timer is known to be at least 2, then the real timer is at least 2, so a frame that ends with the timer at most 1 ends with the byte still followed, that is, with the value it had at R.

**Measured.**

| check | what | result |
|---|---|---|
| native test | the search of the walk from R, for his pixel and his page | 0 failures; `sCheck` true, about 2 s natively (a scratch build). Without `cutS` the search failed 25 times for each byte, each time at one store through an index in the move routine, with the index known 0 (for his pixel: its store of the pixel) |
| private proofs (`prove.py`) | `pole_numbers` (`numbersCheck` with `sCheck`) | true; `prove.py` EXIT 0, `Proof.PoleJoin` builds in 77 to 124 s on a loaded machine (round 31: 89 to 106 s) |
| `edge-real FM2 256`, `surface-frames-check FM2 200` | `movesScan`: `sideW` (`SideW` at every instruction from the scroll handler to the frame's end, on the frames of the field, and on every frame), `endKeep` (the place byte at the frame's end), `pix_end (a theorem)` (the frames that end with the timer at most 1 end with the pixel of the return instruction) | 0 failures. `edge-real`: 5 sets, 137,955 frames at the routine of the offscreen bits; of the 108,634 frames that end with the timer at most 1, none moved his pixel or the left edge after the return, and none had the place byte off; it fails only on the old stored speed and `after` on frames that do not start clean, with the counts of round 31. `surface-frames-check`: 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included; the change out of the side pipe: 201 runs, `Start` 0 against |
| `pos-keep-real FM2 64`, `collide-real FM2 200`, `pos-after-real FM2 200`, `keep-frames-check FM2 100`, `up-clean-u FM2` | `posW`, `clampR`, `collide`, `keep.cleanE`, `chg.upCleanU` | 0 failures (`PosW`, `ClampR`, keep 0; `CollideS` 0; bad 0; bad 0; against 0) |
| `route-check FM2` | the whole route | touch 1092, level change 1748; with `1089 02808080` 1093 and 1748; with 996 and the round 23 jumprun 1396 and 2063 |

**On the route.** The pixel part of the field `endKeep` is gone. `endKeep` is now a condition on one state, the end of each counted frame before the last one before the touch:

```
endKeep : ∀ j, 1 ≤ j → j + 1 < g → EndKeep(seq j)
EndKeep(b) := side(b) ≤ 1 → lock(b) = 0 → thr ≤ pfs(b) → pfs(b) = (pixel16(b) − left16(b)) mod 256
```

(round 31: `∀ j kq k, … → EndKeep(Calls(Q) ∧ ¬(0 < v(Q) ∧ v(seq j) = v(Q)), Rt, seq j)`, which also asked pixel16(seq j) = pixel16(Rt) on the frames that call the push or the clamp and do not keep a speed to the right). New field, on single instructions:

```
sideW : ∀ j, 1 ≤ j → j + 1 < g → side(seq j) ≤ 1 → lock(seq j) = 0 → thr ≤ pfs(seq j) →
          ∀ k n, arr(j) ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → SideW(trace n)
```

`sideW` asks something only on the frames that end as `EndKeep` asks (the timer at most 1, the lock 0, the place byte at least the threshold). On these it asks at every instruction from the scroll handler, also on the frames that call neither the push nor the clamp, or that keep a speed to the right, where the old pixel part asked nothing. It is a condition on single instructions, as `posW` is for the position. The program measured `SideW` also on every frame (`sideW on every frame (measured only)`): 0 failures. New check in `numbersCheck`: `PushTimer.sCheck` (`Numbers.pushC`, `AreaRun.pt`). `OnFrames.nearStepAt` no longer uses `OnFrames.stillAt`, `OnFrames.keepAt` or the field `clampR`; `clampR` is still used by `OnFrames.keepAt` for `AfterP.keep`. No byte more is protected by `guardE`, so `keep.cleanE` and `chg.upCleanU` ask nothing more.

**What is not proved here.** The place-byte part of `endKeep`: the drawing (RenderPlayerSub) writes his place on the screen from the relative position that RelativePlayerPosition computes as pixel − left edge. A walk of TaintRun's machine knows bits of single bytes, not a relation between two bytes, so it cannot follow this difference; and the drawing is skipped on every other frame while the injury timer runs, so the walk would also need that timer known 0 on every frame (it is an interval timer, written through an index each frame). `Moves.stop` (6 measured frames, each with one clamp at the left edge and no push; round 32 narrows it: [A frame that stops him at the screen's left edge](e-2-10-3-21-StopEdge.md)). `collide`, `posW`, `clampR`, `sideW`.

**File:** `Theorems/PushTimer.lean`. `Theorems/SurfaceFrames.lean` uses it (`EndKeep`, the fields `endKeep` and `sideW`, `nearM_of_end`, `OnFrames.nearStepAt`, `numbersCheck`, `movesScan`). `Main.lean`: only the names of the checks in the filters of `edge-real`.
