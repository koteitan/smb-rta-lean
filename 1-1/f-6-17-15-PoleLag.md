[← Back](README.md) | [English](f-6-17-15-PoleLag.md) | [Japanese](f-6-17-15-PoleLag-ja.md)

# The pole's tiles: the area parser's lag may grow up to 157 px

Round 32 left the field `ctlU` ([the control byte 6 on a frame where the parser is not late](f-6-17-13-PoleLate.md)): on each frame before the touch's frame that comes to the player's routine, at each `UpdScrollVar`, the screen buffers' control byte is not 6, or `S + 3·N < 32` there. This round carries a weaker bound over the frames, so that `ctlU` asks the control byte only where `S + 3·N ≥ 157`.

## The words

`N` is the area parser's tasks left and `S` the scroll counter of 32 px. `S + 3·N` is the parser's lag: the pixels the screen has moved that the parser has not yet caught up with, counting 3 px for each task left. For a frame from `m`, `k₂` is its `UpdScrollVar` after the scroll handler and `e` its end. `Y ≤ 3` is the scroll's move to `k₂`, so `S(k₂) = S(m) + Y`.

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32        (rounds 31 and 32)
JY(v)  :=  N ≤ 7  ∧  S + 3·N < 157       (this round)
```

## Why 157 is enough

The parser's invariant and the strict walks need two things of the counter:

* no wrap at `UpdScrollVar`: `S(m) + Y < 256`;
* with `N = 0`, a new column starts only with `32 ≤ S < 160` at `UpdScrollVar`. The code compares the counter with 32 as a signed byte, so from 160 on it starts no column, and the strict walks of `PoleParserEnd` know the new column only for `S(k₂)` in 32 ‥ 159.

`JY` gives both: `S(m) < 157`, so `S(k₂) < 160 < 256`. 157 is the largest bound with this property: with `N = 0` and `S(m) = 157`, a move of 3 px gives `S(k₂) = 160`.

## The step (`Theorems/PoleLag.lean`, `Theorems/PoleStrict.lean`)

`step_strict` now takes `JY` at the frame's start and gives `JY` at its end, when at each `UpdScrollVar` `k`:

```
ctl(k) ≠ 6   ∨   S(k) + 3·N(k) < 157
```

* With `ctl(k₂) ≠ 6` (the strict forms of round 31): with `N ≥ 1`, `N(e) = N − 1` and `S(e) = S(k₂)`, so `S(e) + 3·N(e) = S(m) + Y + 3·N − 3 ≤ S(m) + 3·N < 157`. With `N = 0` and `S(k₂) ≥ 32`, `N(e) = 7` and `S(e) = S(k₂) − 32`, so `S(e) + 21 < 160 − 32 + 21 = 149`. With `N = 0` and `S(k₂) < 32`, the bytes stay.
* With `S(k₂) + 3·N < 157` (the weak forms of `PoleParser.frame_sixA`, any control byte): `N(e) ≤ N` and `S(e) = S(k₂)` (`jy_weak`), or with `N = 0` a new column, `N(e) = 7` and `S(e) = S(k₂) − 32` (`jy_col`).
* No wrap: `noWrap_of_jy` (the counter below 157 and the move at most 3 px).

`invJ_onFrames` and `ruleW_onFrames` carry `JY` over the frames with the same condition on each frame that comes to the player's routine. At control `JV` holds (`PoleStrict.jv₀`, from the rows of the change), so `JY` does (`jy_of_jv`).

## The field

Before (round 32): `ctlU :  at each UpdScrollVar k,  ctl ≠ 6  ∨  S + 3·N < 32`.

Now:

```
ctlU :  at each UpdScrollVar k of each frame n before the touch's frame that comes to the player's routine,
        ctl(trace(all n, k)) ≠ 6   ∨   S(trace(all n, k)) + 3·N(trace(all n, k)) < 157
```

The new field is weaker than the old one. It is still a condition on one state. In words: he takes no coin above ground at a moment when the parser is 157 px or more behind. By the same forms (an argument, not a theorem here): on a frame with the control byte not 6 at `UpdScrollVar` the lag ends below 32 or does not grow, and on a frame with the control byte 6 it grows by at most 3 px. So from a lag below 32 at control the field can be asked only after 42 or more frames with the control byte 6.

Signatures that changed, exactly:

* `PoleStrict.step_strict`: `hk6 : ∀ k, pc(k) = UpdScrollVar → frame(k) = frame(m) → ctl(k) ≠ 6 ∨ S(k) + 3·N(k) < 157`; `hJ : PoleLag.JY (valsOf (places sy m0) m)`; it concludes `(RuleW … ∧ ColOK …) ∧ PoleLag.JY (valsOf (places sy m0) (frame m i))`.
* `PoleStrict.invJ_onFrames`: `hJ0 : PoleLag.JY (valsOf (places sy m0) (K.all 0))`, `hk6` with 157; it concludes `PoleLag.JY` in place of `PoleWrap.JV`. The same for `PoleStrict.ruleW_onFrames` (new this round).
* `PoleParserRun.invJ_run` concludes `PoleLag.JY` in place of `PoleWrap.JV`; its hypothesis `hJ` (JV at control) is unchanged.
* `PoleJoin.Run.ctlU`: the bound 157 in place of 32.
* New: `Theorems/PoleLag.lean` (`JY`, `jy_of_jv`, `s_lt`, `jy_weak`, `jy_col`), `PoleStrict.noWrap_of_jy`. `PoleStrict` imports `PoleLag` (which imports `PoleLate`).
* `route_1_1` still concludes `1748 + j ≤ L`. No new check on the ROM.

## Measured

`pole-keep parser FM2 96` (1 min 36 s, 72 MB), at each `UpdScrollVar` of a frame that starts in control:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| visits above ground | 608 | 10,086 | 18,682 |
| of them with `S + 3·N ≥ 32` (where the round 32 field asked) | 40 | 242 | 205 |
| of them with `S + 3·N ≥ 157` (where the new field asks) | 0 | 0 | 0 |
| the largest lag `S + 3·N`, any area in control | 34 | 34 | 34 |
| visits in control with `ctl = 6` (any area) | 13 | 0 | 0 |

So the new field asks the control byte at no measured visit. The 13 visits of the TAS with `ctl = 6` are in the room below ground, where he takes coins.

## What is not proved

* `ctlU`: that he takes no coin above ground while the parser is 157 px or more behind. A proof that removes it needs the block buffers' contents at his reads on every frame (no coin's tile there) and a walk of the frame that follows the control byte, as round 32 wrote; or a bound on the number of frames above ground with the control byte 6.
* `bufAll`, `keepB` and `tilesCol` ((near) and (read)): not changed by this step.

**Files.** `Theorems/PoleLag.lean` (new); `Theorems/PoleStrict.lean` (`noWrap_of_jy`; `step_strict`, `invJ_onFrames`, `ruleW_onFrames` with `JY`); `Theorems/PoleParserRun.lean` (`invJ_run`, `colMono_run`); `Theorems/PoleJoin.lean` (`ctlU`); `Main.lean` (the round 33 (PoleLag) line of `pole-keep parser`).
