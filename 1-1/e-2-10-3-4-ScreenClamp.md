[← Back](README.md) | [English](e-2-10-3-4-ScreenClamp.md) | [Japanese](e-2-10-3-4-ScreenClamp-ja.md)

# The position at the screen edge

`ScreenClamp.clamp_return` proves the `KeepOnscr` clamp on a real machine, including its return to the caller. It needs `Good`, the checked ROM, its entry program counter, and one of the two edge selectors in Y. The initial stack pointer and flags are arbitrary.

Let R be the entry machine and B the returned machine. Let T be the selected live screen edge minus the amount read from the ROM, keeping the old position fraction. The table and its bytes are parameters of the ROM check.

```
k ≤ 37
pc(B) = returnPc(R)
SP(B) = SP(R) + 2
fraction(B) = fraction(R)
P(B) ≡ T  (mod 2²⁴)
```

`exact_target` gives P(B) = T when 0 ≤ T < 2²⁴. This is an explicit range condition on the entry machine. The theorem does not assume that the screen edge is close to the player.

`pieceY_spec` proves a checked piece with a known selector and an arbitrary unchanged stack pointer. Its check watches every stack byte. The check has 512 pixel cases, 1,024 page-and-borrow cases, and two tails. The subtraction and borrow are proved arithmetically; the return uses the original caller's stack bytes.

## What remains

The clamp can move the player by more than one pixel. Its local result alone does not imply `SurfaceFrames.CollideS` or `AfterP`. The proof still needs the relation of the live edge to the frame's initial position, the branch that calls the clamp, and the remaining position writers after the scroll handler. No global field was replaced by a new hypothesis.

**Files:** `Theorems/ScreenClamp.lean`, private `Proof/ImpedePosition.lean`.

## Checked on real frames

`pos-after-real FM2 200` checked 128,679 frames from the TAS and own inputs: 3,053 collision-push calls and 13,551 screen-clamp calls. Entry `Good`, return, speed, fraction, modular position, margins and target range had zero failures. After the scroll handler, no instruction outside these two routines stored to a position byte. The command exited 0. The sampled frames start in control and store to none of the routine, mode or task bytes. This is a check of runs, not a proof about every frame.

The ROM predicates were true in 430 ms for the collision push and 6 ms for the screen clamp. Both private facts are generated with `native_decide`. The observed clamps selected only one edge; the ROM check and general theorem cover both.
