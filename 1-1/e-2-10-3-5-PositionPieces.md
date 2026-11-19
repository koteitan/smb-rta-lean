[← Back](README.md) | [English](e-2-10-3-5-PositionPieces.md) | [Japanese](e-2-10-3-5-PositionPieces-ja.md)

# Exact sums of position effects

This is a conditional partial result. `PositionPieces.ordinary_interval` proves that any interval of ordinary CPU steps keeps position when every step's actual write locations avoid the pixel, page and fraction. Stores of unchanged bytes are included in this condition.

`impede_piece` and `clamp_piece` supply complete, exact call effects, through the original caller's return. A push takes at most 65 instructions and changes position by its signed pixel delta, with explicit margins against wrap. A clamp takes at most 37 instructions and sets the exact live-edge target, with an explicit target range. Both keep the good-machine and frame-time conclusions of the routine results.

`position_sum` adds any finite list of explicit local position effects. `trace_sum` states the identity on selected cuts of the actual frame trace. Ordinary intervals contribute zero, pushes contribute a signed pixel, and a clamp contributes its target minus its entry position. `pushes_after_clamp` gives the last clamp target plus all later signed pixel effects. No bound on the number or signs of calls is assumed implicitly.

Measured first: on 239 TAS frames, 1,633 frames from eight random runs, 3,256 edge-test frames and 729 frames from eight near-pole runs, the sum matched the actual suffix displacement with zero errors. These 5,857 frames made 104 push calls and 902 clamp calls. No position store occurred outside the summarized calls. This smaller sample had at most one push and one clamp per frame and no mixed sequence; that is a measurement, not a universal call-count bound.

The stronger bound “the clamp target is at or before the frame-start position” is false: 109 of these clamp calls exceeded it. All 902 targets were within one pixel past frame start; the largest excess was 240 position units, less than one pixel. Every measured selector chose the left edge. The live-edge relation still needs a proof, including the other selector.

The existing larger position suite again contains four suffix displacements of two pixels with negative movement-end speed. A dedicated search identified a valid control frame with exactly one left-edge clamp and no `ImpedePlayerMove` call: movement put Q two and a half pixels left of frame start, and the clamp moved it back by two pixels. The result is still half a pixel left of frame start. These two pixels do not come from pushes. A one-pixel bound on the complete suffix remains false.

What remains: construct the ordinary/call cuts for every relevant frame from current guards and code; derive the live-edge bound; and control later call signs, speed changes and counts to obtain `CollideS.P` and `AfterP`. The local equalities in the sum theorem are explicit hypotheses, not a new frame-summary field. Neither old field was removed, widened or replaced.

**File:** `Theorems/PositionPieces.lean`.
