[← Back](README.md) | [English](f-6-17-12-PoleStrict.md) | [Japanese](f-6-17-12-PoleStrict-ja.md)

# The pole's tiles: the strict rule of each frame, and `parWrap` gone

Round 30 left the field `parWrap` ([`TileSlot` on one page, and the scroll counter under the strict rule](f-6-17-11-PoleWrap.md)). It asked, on each frame before the touch's frame that comes to the player's routine, at `UpdScrollVar`: the scroll counter of 32 px of the frame's start plus the edge's move is below 256. The counter is carried over the whole run, so the field was a fact about the run. Round 30 showed that it follows from the strict rule of each frame, from `JV` at control and from a move of at most 3 px.

This round proves the strict rule on real frames, `JV` at control, and the move of at most 3 px, and the area parser's invariant on the route no longer needs `parWrap`. In its place there is one field, a condition on one state of a frame: the control byte of the screen's buffers is not 6 at `UpdScrollVar`.

## The words

`N` is the area parser's tasks left, `S` the scroll counter of 32 px, `col` the parser's column, `edge` the screen's left edge in px. `ctl` is the screen buffers' control byte. `X` is the scroll's amount: the byte that the move stores for the scroll plus the platforms' force on the scroll, mod 256 (`ScrollRule.amountOf`). For a frame from `m`, `n₀` is its first arrival at the player's routine, `kq` its call of the player's subroutines (`PlayerSubs`), where the scroll handler is called, `k₂` its `UpdScrollVar` after the scroll handler, `Y` the edge's move from the frame's start to `k₂`, and `e` the frame's end.

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32
```

## The walks with the control byte (`Theorems/PoleParserEnd.lean`)

`UpdScrollVar` first compares `ctl` with 6 and leaves when it is 6. The walks of round 28 do not know `ctl` at `UpdScrollVar` (measured: the walk's one state there knows no bit of it), so they take both ways, and they give only the weak rule (the bytes kept, or one task).

Now the state of the walk at `UpdScrollVar` is also split into 8 pieces: in piece `j` bit `j` of `ctl` is known and differs from that bit of 6 (`ctlPats`, `pats6`). Every byte but 6 is in a piece (`pats6_cover`, by `decide` over the 256 bytes). In a piece the compare is decided. From each piece a walk with no table goes to the instruction after the branch (`qN`); it may not end the frame. From there:

* for `N` = `w` in 1 ‥ 8, a walk with its own table (826 states) goes to the frame's end and asks `N = w − 1` (`finS`, `csOf`, `atSN`);
* for `N` = 0, split by the counter `s` in 32 ‥ 159, the walk must come to the task handler's call, where the walk of round 28 asks the rest (`atSZ`).

These walks are part of the check `eCheckP` (`atES = atE && atS`). So `keep_eP` and `frame_six` give two more facts:

```
ctl(k₂) ≠ 6  ∧  N ∈ {1, …, 8}                     ⇒  N(e) = N − 1
ctl(k₂) ≠ 6  ∧  N = 0  ∧  32 ≤ S(k₂) < 160          ⇒  N(e) = 7  ∧  S(e) = S(k₂) − 32
```

`frame_sixA` adds the scroll's rule at the same call of the scroll handler (`ScrollRule.scroll_call`, check `ScrollRule.check`): the call returns once (the walks of `EdgeStep`), so

```
Y = 0   ∨   (1 ≤ X(kq) ≤ 128  ∧  Y ≤ X(kq))
```

## The strict rule and `JV` (`Theorems/PoleStrict.lean`)

`step_strict`: a frame in control that comes to the player's routine follows the weak rule, keeps the column below 16, and keeps `JV`:

```
Inv(m) ∧ col(m) < 16 ∧ JV(m) ∧ (∀ UpdScrollVar k, ctl(k) ≠ 6) ∧ (∀ PlayerSubs k ≥ n₀, 1 ≤ X(k) ≤ 128 ⇒ X(k) ≤ 3)   ⇒   RuleW(m, e) ∧ col(e) < 16 ∧ JV(e)
```

Why: `Y ≤ 3` by `frame_sixA` and the bound on `X`, and `S(m) < 32`, so no wrap at `k₂` (`noWrap_of_jv`) and `S(m) ≤ S(k₂) ≤ S(m) + 3`. With `N ≥ 1`, `N(e) = N − 1` and `S(e) = S(k₂)`, so `S(e) + 3·N(e) ≤ S(m) + 3·N < 32`. With `N = 0` and `S(k₂) ≥ 32`, `S(k₂) ≤ 34 < 160`, so `N(e) = 7`, `S(e) ≤ 2` and `2 + 21 < 32`. With `N = 0` and `S(k₂) < 32`, the bytes are kept. (`strict_frame` is the same step of `JV` from `Y ≤ 3` at each `UpdScrollVar`.)

`invJ_onFrames`: on the frames of a run up to the touch's frame, the parser's invariant, the column below 16 and `JV` hold at every frame's start, by one induction (`step_strict` on a frame that comes to the player's routine; a frame that does not come there keeps the bytes).

`jv₀`: `JV` at control above ground, from the rows of the change out of the side pipe (the check `jvCheckK`, `native_decide` in the private proof `pole_parser_jv`).

On the route (`Theorems/PoleParserRun.lean`): `invJ_run` (the same on `PoleJoin.Run`) and `inv_run` (from it). `noWrapP_onFrames` gives the statement of the old field from `JV` and a move of at most 3 px at every `UpdScrollVar`; the route does not use it.

## The scroll's amount at most 3 (`PoleParserRun.amount_run`)

On each frame `n` before the touch's frame that comes to the player's routine, at each call of the player's subroutines `k` from an arrival there on:

```
1 ≤ X(trace(all n, k)) ≤ 128   ⇒   X(trace(all n, k)) ≤ 3
```

The frame is a counted frame `c` (`counted_of`). Part e reads it up to the scroll handler (`OnFrames.readH`, with the speed in range and the position far from the ends at the end of the frame before, `OnFrames.readAll`, `far_of_range`). There:

* the byte that the move stores is his pixel's move from the arrival, when it is in 1 ‥ 128 (`MoveScroll.move_xs`), and the arrival has the position of the frame's start (`ReadH.before`);
* the position (in 1/256 px) moved by `16·v₂` with `|v₂| ≤ top` (`SurfaceRead.read_move`, `Frame.move`, `Frame.anim`, `Frame.friction`);
* the platforms' force is 0 (`OnFrames.scrollAt`, `OnFrames.platPrev`), so `X` is that byte;
* the frame comes to the scroll handler once (`GuardE.subs_onceE`), so these speak of the same call.

So `256·X + f₂ − f = 16·v₂ ≤ 16·top` with the fractions `0 ≤ f, f₂ ≤ 255`, and with `top ≤ 48` (`pole_top`, `decide` on the ROM's value) `256·X ≤ 1023`, `X ≤ 3`. When he moves left `X` is above 128 as a byte (a negative move), and the scroll does not move the edge.

## The fields

Removed: `parWrap`.

Added, on each frame `n` before the touch's frame that comes to the player's routine:

```
ctlU :  at each UpdScrollVar k of it,   ctl(trace(all n, k)) ≠ 6
```

It is not weaker than the old field: it asks something the old field did not ask. But it is a condition on one state: the counter carried over the run is gone from the fields. The code sets `ctl` to 6 when he takes a coin from the block buffers.

Round 32 ([the control byte 6 on a frame where the parser is not late](f-6-17-13-PoleLate.md)): `ctlU` is asked only where the parser is late at `UpdScrollVar` (`S + 3·N ≥ 32`); on the other frames a frame with `ctl = 6` keeps `JV` too (`PoleLate.jv_weak`).

Signatures: `PoleParserRun.invJ_run`, `inv_run`, `tilesCol_run` take `(hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)` after `hs` and `(hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))` after `h0`; `tilesCol_route` takes `hsc` and `htop` after `hs` and `(hmJ : PoleStrict.jvCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)` after `hmC`. `frame_six` and `keep_eP` have the two facts above as two more conjuncts at the end; `frame_sixA` is new. `PoleWrap` imports `PoleParserEnd` (it imported `PoleParserRun`). `route_1_1` still concludes `1748 + j ≤ L`.

## Measured

`pole-keep ctl`: the walk's state at `UpdScrollVar` knows no bit of `ctl`; the new walks succeed, and the whole check `eCheckP` takes 41 s natively. `Proof.PoleParserEnd` took 85 s in the last full build of this round (137 s and 146 s in earlier ones beside other jobs; 68 s in round 30).

`pole-keep parser FM2 96` (the runs as in round 30: the TAS, own random inputs from the TAS's frames 900 to 1089, own random inputs from the first control), on the frames that start in control above ground:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frames that start in control above ground | 608 | 14,318 | 25,980 |
| of them with `JV` false at the start | 0 | 0 | 0 |
| `UpdScrollVar` above ground with the control byte 6 (`ctlU` false) | 0 | 0 | 0 |
| calls of the player's subroutines above ground | 608 | 10,086 | 18,682 |
| of them with the amount in 1 ‥ 128 and above 3 (`amount_run` asks ≤ 3) | 0 | 0 | 0 |
| the largest amount in 1 ‥ 128 | 3 | 3 | 3 |
| the largest move of the edge to `UpdScrollVar` above ground | 3 px | 3 px | 3 px |
| `UpdScrollVar` in control, any area | 719 | 10,086 | 18,682 |
| of them with the control byte 6 | 13 | 0 | 0 |

The 13 frames of the TAS with the control byte 6 are in the room below ground, where he takes coins. Above ground `ctlU` and the bound of `amount_run` held on every measured frame (about 2 min natively, beside a build). The random runs pause often, so fewer of their frames come to the player's routine.

## What is not proved

* `ctlU`: that he takes no coin from the block buffers on the frames above ground before the touch. It needs the contents of the block buffers across frames, as (slot) of `TileSlot`.
* `TileSlot` (slot, near, read on the page two before the pole's), `bufAll` (7 places), `keepB` (66 places): not changed in this round.

**Files.** `Theorems/PoleParserEnd.lean` (`kIdx`, `pats6`, `ctlPats`, `vTask`, `qN`, `finS`, `headN`, `startsN`, `csOf`, `atSN`, `atSZ`, `atS`, `atES`, `Cfgs.s`, `eCheckP`, `pats6_all`, `pats6_cover`, `cov_ctl`, `end_walkS`, `end_walkST`, `keep_eP`, `frame_six`, `frame_sixA`, `strictProbe`); `Theorems/PoleStrict.lean` (new); `Theorems/PoleParserRun.lean` (`amount_run`, `invJ_run`, `inv_run`, `tilesCol_run`, `tilesCol_route`); `Theorems/PoleJoin.lean` (`parCtlOf`, `ctlU`; `parWrap` removed); `Theorems/PoleWrap.lean` (its import); `Main.lean` (`pole_parser_jv`, `pole_top` and the import of `Proof.ScrollRule` in the private `PoleParserEnd`, the route's `tilesCol_route` line, `pole-keep ctl`, the round 31 line of `pole-keep parser`).
