[← Back](README.md) | [English](f-6-17-8-PoleParser.md) | [Japanese](f-6-17-8-PoleParser-ja.md)

# The pole's tiles: the area parser against the screen's left edge

The field `tilesCol` of `PoleJoin.Run` says: at a read of the side check two or more pages before the pole's page, in the pole's column of the block buffers, the byte read is not one of the pole's tiles (`PoleTileFar.TileCol`, [The reads far from the pole are in the block buffers](f-6-17-5-PoleTileFar.md)).

Why it should hold. The block buffers hold 32 columns of 16 px, so the pole's column there is also the column 512 px before the pole. The area parser draws the columns ahead of the screen, a fixed distance ahead of the screen's left edge. Until it draws the pole's column, that place holds the column 512 px before it, which has no pole's tile. When it draws the pole's column, the edge is near the pole, and he cannot be two pages before it.

This page proves a part of that argument: the invariant at control, that its rule keeps it, the first half of the rule on a real frame, and the arithmetic from which `tilesCol` would follow. The field `tilesCol` is unchanged.

## The parser's bytes, from the code

`PoleParser.places` finds the bytes from the program: in `UpdScrollVar`, the operands of its first load (the screen buffers' control byte), of its load of the tasks left `N` and of its load of the scroll counter `S`; its call of the task handler; in the task handler its call of the task routine; that routine's first entry is the column's step, whose two `INC` give the parser's column and its page. The screen's left edge is that of the clamp (`ScreenClamp.places`). There is no address in the files.

## The invariant on one state

Write `col` for the parser's column with its page (16 columns a page), `p(N) = [N ≥ 1] + [N ≥ 5]` for the column steps still to come in the tasks left, and `edge` for the screen's left edge in px.

```
Inv(L, m)  :=  N ≤ 8  ∧  16·col + 16·p(N) + S = edge + L
```

The rule of one frame (`Rule`), from the code:

* the scroll handler adds the scroll's amount `Y` to `S` and to `edge` (`Scroll`);
* then (`Parse`): if the screen buffers' control byte is 6, nothing more. If `N = 0` and `32 ≤ S < 160` (the code's `CMP` and `BMI`), `S − 32` and `N` becomes 8; if `N = 0` otherwise, nothing more. Then the task `N − 1` runs and `N` falls by 1; the tasks 0 and 4 step the column by one.

Proved, pure arithmetic:

* `inv_rule : Inv(L, a) ∧ Rule(a, b) ⇒ Inv(L, b)`, and `inv_frames` for a sequence of frames;
* `col_rule`, `edge_rule`: the column and the edge do not fall;
* `col_le : Inv(L, m) ⇒ 16·col ≤ edge + L`, and `edge_of_col : Inv(L, m) ∧ c ≤ col ⇒ 16·c ≤ edge + L`.

## At control

`inv₀`, from the rows of the change out of the side pipe (as `PoleTileCtl.watch₀`): the machine at control has `Inv(L, m)` and no pole's tile in the block buffers (`NoTiles`). The check on the ROM is `invCheckK`; the private proof `pole_parser_rows` gives it with `L = 384`.

## A frame up to `UpdScrollVar`

Three pieces, joined in `frame_toU`. The first two are the walks of `EdgeStep` (the edge's two bytes, part e) with the parser's bytes in place of the edge's; the third is
the pieces of `ScrollRule` (part e) with the scroll counter added.

* `keep_qP`, `keep_noCutP`: from a frame's start to the scroll handler, the four bytes `N`, `S`, the column and the page are kept; a frame that does not come to the
  player's routine keeps them (check `qCheckP`).
* `scroll_callS`: from the scroll handler's call to the instruction after it, the edge and `S` are both kept, or both move by the same `Y` (check `checkS`: the
  pieces of `ScrollRule` with `S` in place of the fraction, so that each piece that keeps the position keeps `S`; the scroll itself is cut in two, its first five
  instructions move `S` by `Y`, the next ones move the edge's pixel by `Y` with the carry; the clamp's part keeps the edge and `S`).
* `keep_uP`: the scroll handler keeps `N`, the column and the page (a middle walk with each followed); from the instruction after its call to the first
  `UpdScrollVar`, the four parser's bytes and the edge's two are kept (a walk to `UpdScrollVar` with a cut at a store to his position by its address outside the push
  and the clamp, which the field `posW` excludes; the cut stops the loop back of a castle, which moves the parser's page back); and the frame comes to the instruction
  after the call only once (the walk of `EdgeStep` to the frame's end). Check `uCheckP`. `walkQP`, `live_stepQP`, `qP_run` are the walk with the cut to a given place.

`frame_toU`: a frame in control comes to `UpdScrollVar` at some `k₂` in the frame, and there

```
N, col, page  =  those of the frame's start,
(edge, S) = those of the start   or   ∃ Y,  edge = (edge₀ + Y) mod 2¹⁶  ∧  S = (S₀ + Y) mod 256.
```

This is the part `Scroll` of `Rule` on a real frame. The private proofs `pole_parser_q`, `pole_parser_u` and `pole_parser_s` give the three checks (above ground, area
type 1). The private file `Proof/PoleParser.lean` with its four checks builds natively in 25 to 44 s. Probes on the same checks with a wrong byte or a wrong value are false: the frame counter before the
player's routine, the edge's pixel and `S` in the scroll handler, the buttons' byte right before `UpdScrollVar`, a counter's piece with one more, the counter's piece
on the fraction's place.

What `frame_toU` needs besides the checks: each instruction meets `CleanK` of the walk's guard for each byte of the parser and of the edge (`hH`: no store through an
index or a pointer writes it; for the edge's two bytes this is a part of `FrameKeep.guardE`, for the parser's four it is not), the field `posW` from the scroll
handler on (`hp`), and the time of the frame (`ht`, as `CleanK` gives it). These are hypotheses of the theorem, not fields: nothing in the route uses it yet.

## The run: what is left for the invariant

`inv_run`: with the frames of a run `ms (n + 1) = frame(ms n, ins n)`, the invariant holds at every frame's start if it holds at the first (`inv₀` at control) and
every frame follows `Rule`.

* `rule_of_noCut`: a frame that does not come to the player's routine keeps the six bytes (`keep_noCutP`, `EdgeStep.keep_noCut`), so it follows `Rule`.
* `rule_of_toU`: a frame with the conclusion of `frame_toU` follows `Rule` if the scroll does not wrap (`S + Y < 256`, `edge + Y < 2¹⁶`) and from `UpdScrollVar` to
  its end it follows `Parse` (`ParseU`).

So the invariant at every frame's start of the run is left to three things of each frame that comes to the player's routine: the protection of the parser's four bytes
(`hH`), no wrap (measured: `S ≤ 31` at frame starts, `Y ≤ 3`), and `ParseU`.

## What `tilesCol` would follow from

`tileCol_of` (pure arithmetic): at a state where the premises of `TileCol` hold, the byte read is not a pole's tile if

* (`hslot`) a pole's tile read in the pole's column means that the parser's column has come to the pole's column;
* (`hcol`) `16·col ≤ edge + L` (from `Inv`);
* (`hnear`) `edge ≤ his pixel + δ`;
* (`hread`) the read is, in the 32 columns of the block buffers (the column's number mod 32), at the column of his pixel plus an adder `a < A`;

with `A ≤ 16` and `L + δ ≤ 496`. The numbers: his page is at most the pole's page minus 2 and the adder is below 16, so his pixel plus the adder is in a column before the pole's page; the read is at the pole's column counted mod 32, so that column is 32 columns or more before the pole's column `colPole`, and `pixel < 16·colPole − 496`. With a pole's tile, `16·colPole ≤ 16·col ≤ edge + L ≤ pixel + δ + L < 16·colPole − 496 + δ + L`, which is false when `L + δ ≤ 496`.

## Measured

`pole-keep parser FM2 400`: the TAS (719 frames that start in control), own random inputs from the TAS's frames 900 to 1089 (400 runs, half with Start: 58,587 frames in control), and own random inputs from the first control (100 runs of 1300 frames, half with Start: 103,703 frames in control). 163,009 frames in control in all, 8 min natively. `N = 96` gave the same (no false case).

| | TAS | random 900–1089 | random from the first control |
|---|---|---|---|
| frames in control that come to `UpdScrollVar` | 719 | 40,877 | 76,151 |
| start to `UpdScrollVar`: column, page, `N` kept, `S` and edge moved by the same `Y`: false | 0 | 0 | 0 |
| `UpdScrollVar` to the end by `Parse`: false | 0 | 0 | 0 |
| frames that do not come there and change a byte | 0 | 0 | 0 |
| the value of `16·col + 16·p(N) + S − edge` at frame starts and at side reads | 384 | 384 | 384 |
| largest `S`, `N` at frame starts; largest `Y` | 31, 7; 3 | 31, 7; 3 | 31, 7; 3 |
| stores through an index or a pointer on a parser's byte | 0 | 0 | 0 |
| side reads; least (his pixel − edge) | 2,797; 23 px | 157,953; 0 px | 303,748; 0 px |
| side reads in the pole's column counted mod 32; not at his pixel plus an adder < 16 | 108; 0 | 2,266; 0 | 11,220; 0 |
| a pole's tile read there with the parser's column before the pole's | 0 | 0 | 0 |
| frame starts with a pole's tile in the pole's column and the parser's column before the pole's | 0 | 0 | 0 |

So on real frames `L = 384`, `δ = 0` and `A = 16` hold, and `L + δ = 384 ≤ 496`. The stores of the parser's bytes by their address are at 11 places only.

**Tried and not done.** The second half of a frame for six values of `N` (2, 3, 4, 6, 7, 8: the column's step does not run): at `UpdScrollVar` each state of the walks
to it split by the value of `N`, and for each value a walk of `EdgeStep` to the frame's end that follows `S`, the column or the page, or knows `N`. Its check was false
natively (10 s). Probes of its parts (`N` = 3 and 7): the walk that knows `N` succeeds from its starts, and the walks that follow `S`, the column or the page
run out of fuel there (also with 16 times the fuel): they go round a loop that they do not leave, and that path passes no covered cut of their table. It is not in the files.

## What is not proved

* The rest of one frame for the rule: from `UpdScrollVar` to the frame's end, `Parse` (the parser's own code, and that the task routines keep the bytes and return).
* The protection of the parser's four bytes (`hH`) on the frames of the run: measured, no store through an index or a pointer writes them; it is not in
  `FrameKeep.guardE`.
* `hslot` across frames: the area parser draws the pole's tiles only at the pole's column (a part of `bufAll`), and the column of the block buffers is the parser's
  column mod 32.
* No wrap of the scroll (`S + Y < 256`, `edge + Y < 2¹⁶`) on each frame.
* `hnear` and `hread` at the touch's frame.

So `tilesCol` stays.

Round 28: the second half of a frame is proved, for every `N` from 0 to 8, in a weak form of the rule that keeps the invariant: [The area parser, the second half of a frame](f-6-17-9-PoleParserEnd.md).

**Files.** `Theorems/PoleParser.lean`; `genPoleParser` and `pole-keep parser` in `Main.lean`.
