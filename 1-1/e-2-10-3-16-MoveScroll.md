[← Back](README.md) | [English](e-2-10-3-16-MoveScroll.md) | [Japanese](e-2-10-3-16-MoveScroll-ja.md)

# The byte the move stores for the scroll

**Claim (round 28).** At the scroll handler of a counted frame above ground, his pixel is that of the frame's first arrival at the player's routine plus the byte the move stores, when that byte is from 1 to 128. So the field `near` at the scroll handler (rounds 26 and 27) is a theorem, `OnFrames.nearAt`, from a new field `nearA` on the state at the arrival. `nearA` does not mention the move. It asks more than `near` did in one case: on a frame where the byte the move stores is not from 1 to 128 (he does not move right at the scroll handler), `near` asked nothing and `nearA` still asks the 2 px bound at the arrival. It held on every measured frame.

```
R = trace(fm j, pad j, arrAt)      the first arrival at the player's routine
Q = trace(fm j, pad j, k)          the first scroll handler after it
xs(Q) = the byte the move stores (the operand of the scroll handler's first load)

move_xs :    1 ≤ xs(Q) ≤ 128  →  pixel16(Q) = pixel16(R) + xs(Q)

NearA(R) :=  side(R) = 0  →  lock(R) = 0  →  thr ≤ pfs(R)  →  left16(R) + 2 ≤ pixel16(R)
NearX(Q) :=  Allows(Q)  →  left16(Q) + xs(Q) + 2 ≤ pixel16(Q)            (the old field near, round 27)

nearX_of_a :  NearA(R) ∧ (∀ x ∈ placeI, ram(Q)[x] = ram(R)[x]) ∧ plat(Q) = 0 ∧ move_xs  →  NearX(Q)

side = the side collision's timer, lock = the scroll lock, pfs = his place on the screen, thr = the scroll's first threshold (80 px),
pixel16 = 256·page + pixel, left16 = the screen's left edge with its page, plat = the platforms' force on the scroll
```

Proof of `nearX_of_a`: Allows(Q) asks side(Q) = 0, lock(Q) = 0, thr ≤ pfs(Q) and 1 ≤ xs(Q) + plat(Q) ≤ 128. The walks of `PlaceKeep.keep_place` give the same three bytes and the same edge at R. So NearA(R) gives left16(Q) = left16(R) ≤ pixel16(R) − 2 = pixel16(Q) − xs(Q) − 2.

**The mover.** The mover adds `16·v` to the position in three digits: the fraction with the low digit `l`, the pixel with the middle digit `d` and the carry `c`, the page with the high digit and the carry. It returns `d + c`, and the routine that called it stores that as the byte. The check `MoveScroll.xsTailOK` walks two pieces from each cut of the mover (`FrameModel.tailOK`):

1. from the load of the fraction, for every fraction `f` and every low digit `l`: the carry of `f + l` is pushed, and the middle digit, the speed and the bytes of the cut are not written;
2. from the load of the pixel, for every speed `v` and carry `c`: the frame comes to the scroll handler with the byte `d + c`.

`xsDigits` checks over all 256 speeds that `16·sbyte(v) = 256·sbyte(d) + l` with −8 ≤ sbyte(d) ≤ 7, and that `d + c`, when from 1 to 128, is `sbyte(d) + c`. With the position's change of `FrameModel.tail_spec` (`P(Q) ≡ P(R) + 16·v mod 2²⁴`), the fraction gives back the carry, and pixel16(Q) ≡ pixel16(R) + d + c (mod 2¹⁶) (`pix_of_xs`). The position is away from the end of its range (`Far`), so there is no wrap.

**On the route.** `OnFrames.nearAt` needs the frame to be read up to the scroll handler (`OnFrames.readH`), so it takes the speed and the position of the frame before. `OnFrames.edgeAt` and `OnFrames.edge_behind` take them too; their callers have them from `OnFrames.readAll`. The frame comes to the scroll handler once (`GuardE.subs_onceE`). `numbersCheck` has two more checks: `PlaceKeep.placeCheck` and `MoveScroll.xsCheck`.

**Measured** (`surface-frames-check` and `edge-real` check `nearA` at the arrival and `move_xs` at the scroll handler on every frame they run):

| check | what | result |
|---|---|---|
| native test of `xsCheck` | the walks of the byte, the digits | true |
| `edge-real FM2 256` | `nearA`, `move_xs` | 137,955 frames (clean or not), 0 failures; 11,289 arrivals where the scroll is allowed; the least pixel − left at an arrival with the place byte at least the threshold and the side timer 0: 80 |
| `surface-frames-check FM2 200` | `nearA`, `move_xs` | 8 sets, 239,510 frames, 215,433 clean frames checked, 0 failures; of the 103,680 overwritten states around the stairs (where round 27's `PlaceAt` failed), the 97,772 clean ones are checked, 0 failures (the other 5,908 frame starts are not clean, and the check skips them, as it did for `near`) |
| `surface-frames-check FM2 200` | for the next round: `NearM(a)` := side(a) ≤ 1 → lock(a) = 0 → thr ≤ pfs(a) → left16(a) + 2 ≤ pixel16(a) at the frame's start `a` | 0 frame starts against it on all 8 sets. The exact form "pfs(a) = pixel − left with 0 ≤ pixel − left < 256 when side(a) ≤ 1" fails on 50,760 frame starts of the overwritten set and on none of the other seven |

**What is not proved.** `nearA`. It needs the frame before: the drawing there writes his place on the screen as (pixel − left) mod 256, the clamp keeps him on the screen, and a push sets the side timer to 16. It also needs the timer part of this frame, which decrements the side timer by a store through an index. Round 29: the timer part is proved, and `nearA` is a theorem from `NearM` at the frame's start; what stays is the frame step, the field `nearStep` ([The scroll's bytes from the frame's start to the player's routine](e-2-10-3-17-SideTimer.md)).

**File:** `Theorems/MoveScroll.lean` (`lows`, `xsDigits`, `xsTailOK`, `xsCheck`, `xs_tail`, `pix_of_xs`, `move_xs`, `NearA`, `nearX_of_a`). Used by `Theorems/SurfaceFrames.lean` (`OnFrames.nearAt`).
