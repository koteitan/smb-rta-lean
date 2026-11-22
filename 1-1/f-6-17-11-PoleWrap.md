[← Back](README.md) | [English](f-6-17-11-PoleWrap.md) | [Japanese](f-6-17-11-PoleWrap-ja.md)

# The pole's tiles: `TileSlot` asks the column of the read on one page only, and the scroll counter under the strict rule

Round 29 left two fields of part f about the area parser: `tilesCol` (`PoleTileFar.TileSlot`) and `parWrap` (`PoleJoin.NoWrapP`). This round narrows `TileSlot` by arithmetic, asks `parWrap` only of the frames that come to the player's routine, and proves what `parWrap` follows from, without using that in the route yet.

## The words

As on [the area parser on the route's frames](f-6-17-10-PoleParserRun.md): `c₀` and `e₀` are the parser's column (16 a page) and the screen's left edge in px at the start of the touch's frame, `pg` the pole's page, `colPole = 16·pg + c` the pole's column, `page` his page and `pix = 256·page + x` his pixel right after the read. `N` is the parser's tasks left and `S` the scroll counter of 32 px.

## `TileSlot`: the column of the read only on the page two before the pole's

`TileSlot` is asked right after a read of the side check with `page + 1 < pg`, at the pole's column. It had three parts. Now the third part is asked only when `page + 2 = pg`:

```
(slot)  byte read ∈ {ball, shaft}  ⇒  colPole ≤ c₀
(near)  e₀ ≤ pix + 112
(read)  page + 2 = pg  ⇒  ∃ a < 16,  ⌊(pix + a)/16⌋ mod 32 = colPole mod 32
```

The old form asked (read) on every page `≤ pg − 2`. `tileSlot_of_R`: the old form gives the new one, so the field asks less. `tileCol_of_slot` (still pure arithmetic) gives `TileCol` from it with the parser's invariant `16·c₀ ≤ e₀ + 384`:

* `page ≤ pg − 3`: `pix ≤ 256·pg − 513`, so `16·c₀ ≤ e₀ + 384 ≤ pix + 496 ≤ 256·pg − 17 < 16·colPole`.
* `page = pg − 2`: (read) puts the read's column `r = ⌊(pix + a)/16⌋` 32 columns or more before the pole's, so `pix ≤ 16·colPole − 497` and `16·c₀ ≤ 16·colPole − 1`.

In both cases `c₀ < colPole`, so by (slot) the byte read is not one of the pole's tiles.

## `parWrap`: only on the frames that come to the player's routine

`parWrap` asked, on each frame before the touch's frame, at `UpdScrollVar`: if the edge moved by `Y` since the frame's start, then `S + Y < 256`. The parser's invariant uses it only on a frame that comes to the player's routine: a frame that does not keeps the parser's bytes and the edge (`PoleParser.step_noCut`). Now the field and `PoleParser.inv_onFrames` (its hypothesis `hw`) ask it only of such a frame:

```
parWrap :  ∀ n, n + 1 < ix(g) → ∀ n₀, pc(trace(all n, n₀)) = PlayerCtrlRoutine (in the frame) → ∀ k, pc(trace(all n, k)) = UpdScrollVar (in the frame) → NoWrapP(all n, trace(all n, k))
```

The old field gives the new one; `PoleParserRun.inv_run` passes the arrival on.

## `parWrap` under the strict rule (`Theorems/PoleWrap.lean`)

The parser's invariant is an equation and does not bound `S`. The rule that `PoleParserEnd` proves of each frame is weak (`RuleW`): when the control byte of the screen's buffers is 6 at `UpdScrollVar`, the parser skips its task, its bytes stay, and `S` grows by `Y`. The walks to the frame's end follow each byte alone, so they do not say which way the branch on the control byte went.

The strict rule `Strict(a, b)`: the scroll handler moves the counter and the edge by the same `y ≤ 3`, and the parser's part follows `Parse` with the control byte not 6. Then

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32

jv_strict :         JV(a) ∧ Strict(a, b)  ⇒  JV(b)
noWrapP_of :        JV(m) ∧ (the edge moved by Y ≤ 3 to u)  ⇒  NoWrapP(m, u)
parWrap_of_strict : JV(all 0) ∧ (∀ n + 1 < ix(g), StrictF(all n, all (n+1))) ∧ (Y ≤ 3 at each UpdScrollVar of a frame that comes to the player's routine)  ⇒  the statement of parWrap
```

`StrictF(a, b) := Strict(a, b) ∨ b = a`: a frame that does not come to `UpdScrollVar` (it ends paused) keeps the bytes. Why `JV` is kept: with `N = 0` and `S + y ≥ 32` the parser starts a new column with `S + y − 32 < 3` and `N = 7`, and `3 + 21 < 32`; with `N ≥ 1` it runs a task, `N` falls by 1 and `S` grows by at most 3. So `S < 32` at every frame's start.

These theorems are proved. The route does not use them: `parWrap` stays a field. What they leave is stated below. (Round 31: the strict rule is proved and `parWrap` is gone; the route uses `JV` and `s_lt` from here: [the strict rule of each frame](f-6-17-12-PoleStrict.md).)

## Measured

`pole-keep parser FM2 96` (1 min 18 s to 1 min 39 s natively, 73 MB). The runs as in round 29: the TAS, own random inputs from the TAS's frames 900 to 1089 (96 runs, half with Start), and own random inputs from the first control (24 runs of 1300 frames, half with Start). Every frame that starts in control is checked.

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| far reads at the pole's column (`TileSlot` asked) | 101 | 0 | 3,376 |
| of them with `page + 2 = pg` (now the only ones where (read) is asked) | 26 | 0 | 0 |
| `TileSlot` (round 30) false | 0 | 0 | 0 |
| frames that start in control above ground | 608 | 14,318 | 25,980 |
| of them with `JV` false at the start | 0 | 0 | 0 |
| the control byte 6 at `UpdScrollVar`, above ground | 0 | 0 | 0 |
| the largest move of the edge to `UpdScrollVar`, above ground | 3 px | 3 px | 3 px |
| frames above ground that follow neither `Strict` nor keep the bytes (`StrictF` false) | 0 | 0 | 0 |

The control byte is 6 at `UpdScrollVar` on 13 frames of the TAS, all in the room below ground. In the code, the routine that erases a coin from the block buffers sets it to 6. Above ground it was never 6. Each frame followed `Parse` with the control byte as read there (round 27's count, 0 false), and above ground every measured frame followed `StrictF` (counted directly).

## What is not proved

* `TileSlot` itself: (slot), (near), and (read) on the page two before the pole's. (read) needs the relation between the side check's pointer and his pixel; the walk of the touch's frame does not know his pixel far from the pole (round 25: splitting the sum's high 4 bits there passed 5.8 GB). (near) needs the clamp's decision on the touch's frame (`GetXOffscreenBits`); part e assumes the same kind of fact for the frames before the touch (`collide`). (slot) needs the contents of the block buffers across frames.
* `parWrap`: `JV` at control, that each frame before the touch follows `StrictF`, and that the edge moves at most 3 px a frame. For `Strict` the end walks of `PoleParserEnd` would have to follow the branch on the control byte together with the parser's bytes. The control byte is 6 when he takes a coin from the block buffers, so `Strict` also needs that no frame above ground takes one.
* `bufAll` (7 places) and `keepB` (66 places): not attempted in this round.

**Files.** `TileSlot`, `TileSlotR`, `tileSlot_of_R`, `tileCol_of_slot` in `Theorems/PoleTileFar.lean`; the field `parWrap` in `Theorems/PoleJoin.lean`, `hw` of `inv_onFrames` in `Theorems/PoleParserEnd.lean` and its use in `Theorems/PoleParserRun.lean`; `Theorems/PoleWrap.lean` (`JV`, `Strict`, `StrictF`, `rule_of_strict`, `jv_strict`, `jv_strictF`, `jv_frames`, `s_lt`, `parS_eq`, `noWrapP_of`, `parWrap_of_strict`); the round 30 line of `pole-keep parser` in `Main.lean`.
