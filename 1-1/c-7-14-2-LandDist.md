[← Back](README.md) | [English](c-7-14-2-LandDist.md) | [Japanese](c-7-14-2-LandDist-ja.md)

# A big player's slow takeoff on C + 35

[A big player at the block's corner](c-7-14-1-BigApproach.md) left one hypothesis, the field `Approach.slowBig`: a big player whose last low frame is past the corner, after a slow takeoff on `C + 35` (the first frame after the fall), gets past the block's right end only after `C + 98`. This page proves it. The field is gone.

## Why the old bound was not enough

The old bound starts from the frame before the last low frame, `P(s − 1) ≤ c_P − 1`, adds the air frames at the air speed (384/256 px each) and bounds the frames after the landing by `capDist`. For the slow pair `(10, 17)` it was 319/256 px past the goal at `C + 98`.

Two sharper bounds were measured first, and both are still short:
- an exact table of the frames after the landing (the best input on each frame, from every state): 304/256 px less than `capDist` from 10 frames on. The pair `(11, 16)` closes (113/256 px short of the goal), the pair `(10, 17)` is still 15/256 px past it;
- exact air frames before the landing, from any state below the air threshold: no gain. Eight air frames at the air speed reach the best state for the table.

So the state at `s − 1` and its position have to be bound together. Moving at the air speed at `s − 1` needs him farther back. A search from the room's first frame gives this.

## Statements

`P` is in 1/256 px. `c_P` is the corner (51 px), `G_P` the goal (the block's right end). `T1 + 1` is the takeoff frame, `s = T1 + 1 + u.low` the last low frame, `L` the frame on the block, `t₀` the first frame past the goal. A slow pair `q = (q₁, q₂)` of the jump table has `q₁ ≤ u.low` and `q₂ ≤ u.k`; here `(10, 17)` and `(11, 16)`. `hdist(x, is)` is how far the frames `is` move `P` from the state `x` (the model `hstep`).

```
dist_table:  tableOk(T, n)  →  for a state x of the domain and inputs i₁ … i_k, k ≤ n:
               hdist(x, i₁ … i_k) ≤ T[k][x]
  tableOk(T, n):  0 ≤ T[0][x],  and  16·v(hstep(x, i)) + T[k][hstep(x, i)] ≤ T[k + 1][x]
                  for every state x, every input i, every k < n

search_cov:  P(C) ∈ [P0, P1], 34 air frames of the fall, the jump frame, k more air frames,
             and P < c_P at the end of each frame from the jump frame on
             →  some entry (x, lo, hi) of search(k) has the state x and lo ≤ P ≤ hi
             (the greatest P is cut to c_P − 1 on those frames)

slow_short:  for a slow pair q, K = 98 − (34 + q₁), B = 98 − (35 + q₂):
             the state at the end of search(q₁ − 1), below the air threshold, P < c_P,
             then a air frames and b ≤ B frames, a + b ≤ K
             →  P + hdist(…) < G_P

slowCheck (new check Checks.slowLand): for each slow pair q and each b ≤ B:
  c_P − 1 + 384·(K − b) + max { T[b][x] : x below the air threshold }  <  G_P
  or, for each a ≤ K − b and each entry (x, lo, hi) of search(q₁ − 1) followed by a air frames:
  hi + T[b][x]  <  G_P
```

`landed_short`, the case `T1 = C + 34`, a slow takeoff, `¬LowAt(s)`: let `s₂ = T1 + q₁ ≤ s − 1`. The frames from `C` to `s₂` are those of the search: the fall's frames are air frames, `C + 35` is a jump frame, and every frame up to `s − 1` is left of the corner (`left_at`). At `s₂` he is below the air threshold (`capped_along`). The frames from `s₂` to `L` are air frames, and `t₀ − L ≤ B`, `t₀ − s₂ ≤ K`. So `slow_short` gives `P(t₀) < G_P`, against `G_P ≤ P(t₀)`.

## The check

`slowCheck` makes one pass of `hstep` over every state of the domain and every input: 129,024 states, 38 inputs. Each entry of that array holds its own state (`inv_trans`), and `trOk` checks that each state sits at its number, so the table's checks read the frames from the array and do not run `hstep` again. The search runs `hstep` itself; up to `C + 45` it has at most 581 states on a frame (250 after the fall).

Margins at `C + 98`, in 1/256 px short of the goal:

| pair | frames after the landing | from `c_P − 1` (first line) | from the search (second line) |
|---|---|---|---|
| (10, 17) | 45 | 241 | 401 |
| (10, 17) | 46 | −15 | 145 |
| (11, 16) | 46 | 369 | 529 |
| (11, 16) | 47 | 113 | 273 |

Only the pair `(10, 17)` with 46 frames after the landing needs the second line.

The check takes about 44 s natively (33 s of it is the pass of `hstep`). It is the private theorem `land_dist` in its own file `Proof/LandDist.lean`, which needs only the ROM, so it builds beside the other private proofs.

## What remains

- `Approach.low` itself is still a field.
- `low_at` for the frames that end at 136 to 151 px after a frame at or past the corner (the other band frames are proved: [A frame above 152 px after a frame left of the corner](c-7-5-19-BandStart.md)), and the second stand of `stand_wall`, are not done.

**Files.** `Theorems/LandDist.lean` (new): `trans`, `Inv`, `trOk`, `layer`, `layerOk`, `table`, `tableOk`, `dist_table`, `airOk`, `dist_air`, `search`, `search_cov`, `looseOk`, `exactOk`, `slowCheck`, `slow_short`. `Theorems/RoomJoin.lean`: the field `Approach.slowBig` removed, new `Checks.slowLand`, `landed_short` keeps its statement. Private: `land_dist` in `Proof/LandDist.lean`, `slowLand := land_dist` in `room_checks` (`Proof/RoomJoin.lean`).

**Reproduce.**
```
.lake/build/bin/smbrta room-big land      # the check, its time, the search's states and the margins
```
