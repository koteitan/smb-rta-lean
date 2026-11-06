[← Back](../README.md) | [English](PoleGrab.md) | [Japanese](PoleGrab-ja.md)

# Grabbing the pole from below

**Statement.** To grab the flagpole while rising, Mario has to be in the pole's range, past the left edge
of the base block, and get there from above. Beside the block the game pushes him back; moving left turns
the push of his feet to the right, at most 1 px per frame. So he lands no further than a bound, and the hop
adds nothing. If he is far enough behind at a given frame, he cannot grab the pole in time.

In 1/256 px. `P₂` is the position after the movement, before the collision. `P₀` is the left end of the range,
`e` the frame his feet move over the block, `L = e + k` the frame he lands on the ground, `m` the frames beside
the block after it, `g = L + m + 1` the frame he would grab.

```
landing_far   :  k ≥ 2  →  P(L) ≤ P₂(e) + 256·(k − 3) + 32
landing_one, landing_zero  :  k ≤ 1  →  P(L) ≤ P₂(e) − 256
landing_left  :  no Left or Right after e  →  P(L) ≤ P₂(e) − 256
hop_le        :  P(L + m + 1) ≤ P(L) − 16·m
grab_le       :  P₂(g) ≤ P(g) + 32
no_grab_far   :  P₂(e) + 16·v_top·(t − e) ≤ B,  B + 32 < P₀,  L ≤ t + 3,  k ≥ 2,  m ≥ 2  →  P₂(g) < P₀
no_grab_near  :  P(L) ≤ P₂(e) − 256,  m ≥ 1  →  P₂(g) < P₀
pole_rules    :  the collision routine follows the rules below on every state near the block
```

Both `no_grab` theorems also need `P_f + 16·v_top ≤ P₀ + 224`, with `P_f` where his feet get over the block.

Lean: `Theorems/PoleGrab.lean`, private `pole_rules` (by `native_decide`).

## The rules

| Mario | what the routine does |
|---|---|
| falling, feet inside the block, moving right or moving direction right | speed 0, 1 px back, blocks Right |
| falling, feet inside the block, otherwise | speed 0, 1 px forward, blocks Left |
| falling onto the top of the block | lands above the height of a direct grab |
| at the side of the block or on the ground beside it, moving right or stopped | speed 0, 1 px back, blocks Right |
| the same, moving left | nothing, blocks Right |
| rising in the pole's range, above the block's top | touches the pole |

`maskCheck`: when Left is blocked, a stopped Mario in the air does not start moving left.

## How

From speed 0 a frame reaches a speed of at most 1/8 px/frame (`a_max ≤ 512`), so a frame moves him at most 1/8 px by
itself. A frame with the feet inside then gives at most 1 px forward, and a frame at the side
at least 1/16 px back. The last frame before landing either pushes him forward, and then Left is blocked,
so the landing pushes him back; or it pushes him back itself. Summing gives `landing_far`.

For `no_grab_far`: with `k = 2` the frame before `e` is left of the block, so `P₂(e)` is less than one frame's move past
it. With `k ≥ 3` he has at most `L − e` frames at 1 px per frame, but `e` is earlier, where the bound `B` is smaller
by `16·v_top` per frame, more than he gains.

## Assumptions (not proved in Lean)

* The theorems are about frames (`Frame` of [Top speed bound](TopSpeed.md)) whose collision follows `Side`,
  `InBlock` and `MaskL`. That real frames do so is the same kind of assumption as there: the routine is checked
  alone, not joined to the rest of the frame.
* `pole_rules` is checked for a small Mario, with the pole's column written into the block buffer from the object
  code and the level data, for: positions from the first contact with the block's side to 1 px past `P₀`; heights from
  the top of the block to the ground; speeds from −0.75 px/frame up; fall speeds up to the top one; rising speeds of the first
  jump frames. In the theorems he stays inside these positions: `k ≤ 2` keeps him under 0.5 px past `P₀`, and `k ≥ 3` needs
  an earlier `e`.
* `L ≤ t + 3` and `m ≥ 2` come from the jump: rising at the height of a direct grab happens only on the third frame of a jump
  (`m = 2`), or on the second frame of a fast jump (`m = 1`); this is [The height of a jump](Jump.md). A fast jump needs no Left or
  Right after `e`, because pressing them updates the stored absolute speed: this is read from the code.
* The bound `B` is an input. [The 1-1 route](../docs/route-1-1.md) takes it from an emulator search.

**Files.** `Theorems/PoleGrab.lean`, private `Proof/PoleGrab.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pole-check     # the routine against the rules, as a program (0 differ, 4 s)
```
