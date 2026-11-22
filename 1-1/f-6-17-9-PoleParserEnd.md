[← Back](README.md) | [English](f-6-17-9-PoleParserEnd.md) | [Japanese](f-6-17-9-PoleParserEnd-ja.md)

# The pole's tiles: the area parser, the second half of a frame

[The area parser against the screen's left edge](f-6-17-8-PoleParser.md) proved the parser's invariant at control, that the rule of one frame keeps it, and the first half of that rule on a real frame (from the frame's start to `UpdScrollVar`, `frame_toU`). The second half (`ParseU`, from `UpdScrollVar` to the frame's end) was left. This page proves it, for every value of the tasks left `N` from 0 to 8, in a weak form of the rule that keeps the invariant as well. The field `tilesCol` is unchanged: nothing in the route uses this yet.

## The weak rule

The words of [the page before](f-6-17-8-PoleParser.md): `N` the tasks left, `S` the scroll counter, `col` the parser's column with its page (16 columns a page), `edge` the screen's left edge in px.

```
Step(a, b)    :=  if a.n = 0 then 32 ≤ a.s < 160 ∧ b.n = 7 ∧ b.s = a.s − 32 ∧ b.col = a.col
                  else b.n = a.n − 1 ∧ b.s = a.s ∧ b.col = a.col + [a.n ∈ {1, 5}]
ParseW(a, b)  :=  b.edge = a.edge ∧ ((b.n, b.s, b.col) = (a.n, a.s, a.col) ∨ Step(a, b))
RuleW(a, b)   :=  ∃ c, Scroll(a, c) ∧ ParseW(c, b)
```

`ParseW` does not say which case happens (the control byte 6 of the screen buffers keeps the bytes). Each case of it is a case of `Parse`, so:

* `parseW_of : Parse(ctl6, a, b) ⇒ ParseW(a, b)`, `ruleW_of : Rule(a, b) ⇒ RuleW(a, b)`;
* `inv_ruleW : Inv(L, a) ∧ RuleW(a, b) ⇒ Inv(L, b)`, and `inv_runW` for the frames of a run.

## A frame, as a whole

`rule_frame`: a frame in control that comes to the player's routine follows the weak rule,

```
RuleW(vals(m), vals(frame(m, i))),
```

when at its start `N ≤ 8`, the parser's column (in its page) is below 16 and its page is not 255, and with the conditions of `frame_toU` (below). It is the three cases `rule_zero` (`N = 0`), `rule_col` (`N ∈ {1, 5}`: the column's step) and `rule_six` (`N ∈ {2, 3, 4, 6, 7, 8}`). A frame that does not come to the player's routine keeps the bytes (`rule_of_noCut` of the page before), so it follows `Rule` and `RuleW`.

## How: walks from `UpdScrollVar` to the frame's end

The walks of `PoleParser.uCheckP` to `UpdScrollVar`, one for each byte with the byte followed, go on from there (`atE`). The followed bytes are the parser's four and the edge's two (`pE`). At `UpdScrollVar` each state is split by the value of `N` (`SideFrame.fillB`), and for each value a walk of `EdgeStep` (`walkKP`) goes to the frame's end:

* `N ∈ {2, 3, 4, 6, 7, 8}` (`atRkE`): the walk follows the byte, so it is kept; for `N` itself it knows the value and asks at the end `v` or `v − 1` (`finE`).
* `N ∈ {1, 5}` (`atRkV`): the column's step writes the column and maybe the page, so a walk cannot follow them. The page's walk is split again by the column `c` (below 16): for `c < 15` it follows the page and asks at the end `N` and the column kept, or `N − 1` and `c + 1` (`finC`); for `c = 15` it is split by the page `p` (not 255) and asks `N`, the column and the page kept, or `N − 1`, the column 0 and the page `p + 1` (`finP`). The other bytes are followed as above.
* `N = 0` (`atRkZ`): `UpdScrollVar` compares `S` with 32 and stores `S − 32`. The counter's walk is split by its value `s` and goes, with no table, to the frame's end (asks `N = 0` and `S = s`, `fin0`) or to the call of the task handler (`qR`, `RunParser`). There it asks `32 ≤ s < 160` and `S = s − 32`, and a walk with `S` followed goes on to the frame's end and asks `N = 7` (`finT`). `walkEQ` and `endEQ` are this walk to the frame's end or to a place. The other bytes are followed as above.

`keep_eP` (the chain of `keep_uP` with these walks) and `frame_six` (the frame as `frame_toU`) give the facts at the frame's end; `parseW_six`, `parseW_col`, `parseW_zero` turn them into `ParseW`, and `scroll_of` gives `Scroll` from `frame_toU`'s conclusion and no wrap.

The check on the ROM is `eCheckP`; the private proof `pole_parser_e` gives it above ground (area type 1). The private file `Proof/PoleParserEnd.lean` (with `pole_parser_col`, below) builds natively in 32 to 85 s (85 s in the last full run, with other jobs on the machine).

**The loop that round 27 did not find.** Round 27's walks of this kind ran out of fuel. A probe that returns the path of the first failing walk showed it: `DrawMTLoop` (`RenderAreaGraphics`) and then `AttribLoop` (`RenderAttributeTables`), again and again. The walk's guard did not protect `N`. A store through an index with an unknown target in `DrawMTLoop` made the walk forget `N` and the loop's counter in the zero page, so `DEC N` gave an unknown `N` and the path went into `RenderAttributeTables`, and no state of the loop was covered by the table, whose search did protect `N`. Here the guard of each walk to the end protects the byte, `N`, the column and the page (`guardN`), and the table's key holds their values (`keyN`), so that a state at the idle loop with `N = v` and one with `N = v − 1` are not joined.

## The column in its page, and the invariant on a run

The column's step needs the parser's column in its page below 16 at the frame's start. It holds at control (`col₀`, from the rows of the change out of the side pipe, as `inv₀`; check `colCheckK`, private proof `pole_parser_col`), and each frame keeps it (`col_frame`; a frame that does not come to the player's routine keeps the bytes, `step_noCut`). The page is not 255 when the invariant holds and `edge + L < 65280` (`page_of_inv`; with `L = 384`, the edge below 64896 px). So, by induction (`inv_runC`, `step_frame`, `step_noCut`):

```
Inv(L, ms 0) ∧ ColOK(ms 0)  ∧  ∀ n, (the conditions of the frame n, and edge(ms n) + L < 65280)
  ⇒  ∀ n, Inv(L, ms n) ∧ ColOK(ms n)
```

`N ≤ 8` and the column below 16 are then no hypotheses of the frames: they come from the induction. In `step_frame` the protection of the bytes is one condition on each instruction, `CleanK` of `guardPar` (the guard of the frames with the parser's four bytes, the edge's two and the platforms' force protected); it gives the conditions of the walks (`cleanH_of_par`, `cleanN_of_par`) and `CleanK` of `FrameKeep.guardF`. With the field `cleanE` of the frames of a run (`CleanK` of `FrameKeep.guardE`, which protects the edge's bytes), what is new is `CleanK` of `guardPI`: no store through an index or a pointer writes the parser's four bytes (`cleanPar_of`).

`inv_onFrames` is this induction on the frames of a run up to the touch's frame (`FrameKeep.Frames`, from the machine at control): the frames give the start in the idle loop in control (`Frames.all_start`), `cleanE`, `noStore` and the time, and each frame comes to the player's routine a first time or not at all (`arrival_cases`). What it asks of each frame before the touch's frame: the area's type `v`, the field `posW` from the scroll handler on, no wrap, the edge below `65280 − L` px, and `CleanK` of `guardPI`. With `L = 384` it gives, at every frame's start up to the touch's frame, `16·col + 16·p(N) + S = edge + 384`, `N ≤ 8` and the column below 16.

## The conditions

The conditions of `frame_toU`, and:

* (`hN`) each instruction of the frame meets `CleanK` of `guardN` for each byte of `pE`: no store through an index or a pointer writes the byte, `N`, the column or the page;
* (`hw`, `NoWrap`) at `UpdScrollVar` the scroll does not wrap: `S + Y < 256`, `edge + Y < 2¹⁶`;
* at the frame's start, `N ≤ 8` (a part of `Inv`), the column below 16 and the page not 255 (for the column's step). On a run the first two come from the induction above, and the third from the edge below 64896 px.

All are conditions on single instructions or single states. None is a field: nothing in the route uses this yet.

## Measured

`pole-keep parser FM2 400` (5 min natively, 71 MB; the TAS, own random inputs from the TAS's frames 900 to 1089 (400 runs, half with Start), and own random inputs from the first control (100 runs of 1300 frames, half with Start)): the strong rule `Parse` from `UpdScrollVar` to the frame's end is false on no frame, and so is the weak rule. `N = 96` gave the same. At the starts of the frames in control that come to `UpdScrollVar`:

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frames | 719 | 40,877 | 76,151 |
| largest column in its page (the rule asks < 16) | 15 | 15 | 15 |
| largest page (asks ≠ 255) | 13 | 13 | 4 |
| frames with `N` = 0; 1; 5 | 444; 39; 39 | 32,719; 1,244; 1,141 | 69,324; 967; 977 |
| stores through an index or a pointer on a parser's byte | 0 | 0 | 0 |
| largest `S`; largest `Y` (no wrap) | 31; 3 | 31; 3 | 31; 3 |
| largest edge (asks < 64896 px) | 3,046 px | 3,065 px | 806 px |

## What is not proved

* The protection of the parser's bytes (`hH`, `hN`) on the frames of the run: measured, no store through an index or a pointer writes them; they are not in `FrameKeep.guardE`.
* No wrap of the scroll on each frame, and the edge below 64896 px (measured: the parser's page 13 at most).
* `hslot` across frames (the parser draws the pole's tiles only at the pole's column), and `hnear`, `hread` at the touch's frame.

So `tilesCol` stays.

Round 29: the route supplies these conditions, and `tilesCol` asks only `TileSlot` ([The area parser on the route's frames](f-6-17-10-PoleParserRun.md)). The walks ask `posW` only from the first arrival at the player's routine on.

Round 31: the walks at `UpdScrollVar` are also split by the screen buffers' control byte into 8 pieces where it is not 6 (`ctlPats`), and from each piece a strict walk asks `N − 1` at the frame's end (for `N` = 0 with the counter in 32 ‥ 159: the task handler's call); `keep_eP` and `frame_six` have these two facts at their end ([the strict rule of each frame](f-6-17-12-PoleStrict.md)).

**Files.** `Theorems/PoleParserEnd.lean`; `genPoleParserEnd` and `pole-keep parser` (the round 28 line) in `Main.lean`.
