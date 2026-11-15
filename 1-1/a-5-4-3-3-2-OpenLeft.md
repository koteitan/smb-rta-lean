[← Back](README.md) | [English](a-5-4-3-3-2-OpenLeft.md) | [Japanese](a-5-4-3-3-2-OpenLeft-ja.md)

# The opening to the left

**Claim.** In the model of [the opening](a-3-Opening.md), from the 1-1 start, no input gets more than `P(m₀)` to the left in 31 frames. `P(m₀)` is the position at
control (40 px). So at the end of each of the first 31 frames he is at or right of position 0, and the position does not wrap below 0 there.

Units are 1/256 px. `P(m₀) = 10240`. `dist(u)` is how far the model's state `u` has moved from the start (negative to the left). The model is that of
[the opening](a-3-Opening.md): the horizontal frame `hstep`, and jumps whose lengths lie between those of a one-frame A and of a held A.

```
leftCheck(T, n)     :  the search from the start for n frames; a state that cannot get past −T any more is dropped
low_of_check        :  leftCheck(T, n) = true   →   ∀ k ≤ n,  Reach(start, k, u)  →  −T ≤ dist(u)
open_left (private) :  ∀ k < 32,  Reach(start, k, u)  →  −P(m₀) ≤ dist(u)        and        P(m₀) + 9744 < 2²⁴
```

Lean: `Theorems/OpenLeft.lean` (`keepL`, `leftCheck`, `reach_ge`, `low_of_check`; proved without computation), private `open_left` in `Proof/OpenFrames.lean` (the search
with `native_decide`).

## How it works

It is the search of [the opening](a-3-Opening.md), turned to the left. The potential `Φ` bounds the speed either way: `|V| ≤ Φ` with `V = 256·v + f`
(`Potential.step_J`). Moving left the speed's byte can be 1 below the bound on `V`, so after one frame from `Φ ≤ p` the speed is at least `−(p'/256 + 1)` with
`p' = nxt(p)`. So `n` frames from `Φ ≤ p` move at most

```
dl(p, n)  =  Σ_{j=1..n}  16·(p_j / 256 + 1),        p_0 = p,  p_j = nxt(p_{j−1})
```

to the left (`SurfaceFrames.dl`, the same bound as part e uses; `reach_ge`). The search drops a state `x` with `r` frames left when it is in the domain and
`dist(x) − dl(pOf(x), r) ≥ −T` (`keepL`). Every state it keeps is checked: `−T ≤ dist`.

## The numbers

The program `open-left-check N T`:

| frames | `T` | result | time |
|---|---|---|---|
| 31 | 10240 | true | 1.3 s |
| 31 | 10100 | true | 1.2 s |
| 31 | 9664 | true | 1.5 s |
| 31 | 9600 | false | 1.6 s |
| 32 | 10240 | false | 1.8 s |
| 32 | 10304 | true | 1.7 s |
| 32 | 10500 | true | 1.8 s |

So in 31 frames the model gets at most 9664 to the left (`P ≥ 576`), and in 32 frames at most 10304: at the end of frame 32 the model can be up to 64 left of
position 0. On the real machine the screen's left edge stops him: the scroll handler writes the position back to the edge, and sets the speed to 0 if Left is held.
The model does not have the edge.

Round 20: a search of own inputs on the real machine (`open-left-real FM2 60`, a beam search) reaches both bounds. The smallest position at the end of frame 31 is
576, and at frame 32 the movement goes to `P = −64` and the frame ends at the left end of the level (`P = 192`, the speed 0). So frame 32 of such a run is no step
of the model. The old condition `after` was false there; see [OpenAfter](a-5-4-3-3-4-OpenAfter.md).

`dl` alone is too weak here: `dl(Φ(start), 32) = 11328 > 10240`. The search is needed.

## Use

[The opening on real frames](a-5-4-OpenFrames.md) uses it: the position at the end of each of the first 31 frames is exact (no wrap). For the end of frame 32 a
condition stays (`Real.page`: the page is not 255 when the counted frame 33 begins), and frame 32 may end at the left end of the level
(`OpenFrames.AtEdge`, `OpenRunM.endB`).

## Assumed (not proved in Lean)

Nothing new. The model is that of [the opening](a-3-Opening.md).

**Reproduce.**
```
.lake/build/bin/smbrta open-left-check 31 10240     # true
.lake/build/bin/smbrta open-left-check 32 10240     # false
.lake/build/bin/smbrta open-left-real FM2 60        # own inputs to the left on the real machine (1 min)
```
