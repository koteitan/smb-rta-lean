[← Back](README.md) | [English](c-7-5-7-RoomAddress.md) | [Japanese](c-7-5-7-RoomAddress-ja.md)

# The room's block-buffer column pointer

**Partial result.** The small `GetBlockBufferAddr` routine turns each of the 32 column/buffer selectors into the corresponding map pointer, for every stack byte. `RoomAddress.pointer_of_check` proves this from an actual machine at the routine's entry, with the selector in A. It reaches the return cut within 40 instructions with the pointer known. The private ROM check `room_address_check` checks 8,192 cases in about 0.74 s natively.

For selector `a`, the pointer is

```
buffer_start + (a / 16) * half_buffer_length + (a % 16)
```

The routine's entry and pointer bytes are read from the code by the existing `EntryHeight.hpOf`. The public file contains no ROM bytes or addresses. The check factors those shared parameters out of its loop; computing them separately for every case was too slow and was stopped at 90 s. The theorem's assumptions and result did not change.

## The horizontal arithmetic

`encoded_eq_selector` proves that adding the horizontal offset to the pixel, carrying into the page, and combining the page's parity with the pixel's high nibble gives the selector of the full horizontal coordinate modulo the two buffers. `selector_lt` proves that this selector is below 32. `bytes16_eq` proves the low/high byte reconstruction used by the pointer lemma. These are general bit-vector identities, proved with Lean's standard `bv_decide`, without Mathlib or ROM assumptions.

The pointer lemma itself starts with A already known. The new [RoomCollision](c-7-5-8-RoomCollision.md) proves the preceding coordinate calculation, the row, the actual tile read and the complete return for a player call with any offset index. The whole-frame position and landing links remain separate.

## What the landing still needs

`Solid` supplies the floor tile once its buffer index is known. This result identifies the column pointer at the end of its small routine. `RoomCollision` now proves the coordinate/row calculation and pointer preservation through the actual read inside the call. To remove `land_at`, one still needs the position after the frame's move at each foot call, the relevant map cells, and the rest of the landing control flow. The same whole-frame gap affects `stand_wall` and `wall`. All three fields remain unchanged; no new Run field was added.

The whole-frame trial started from a first-fall state one frame before the expected landing, full non-coin map knowledge and one horizontal nibble. The first bounded search had 1,062,638 steps, 169,175 states and 2,433 pending. Admitting paused ends and using a 300,000-state cap gave 2,236,722 steps, 300,001 states and 2,638 pending, with 77 diagnostic failures. This is neither a proof nor a real counterexample. Horizontal arithmetic still loses the column correlation in that abstraction, so a larger search was not retained.

## Real frames

The augmented `room-floor-check` compares the selector at the column routine with the coordinate formula, and each tile read's pointer and address with that selected column plus Y. Existing coin-erase, solid-map and landing checks remain. `room-jump-check` and `room-stand-check` check the existing room fields on movie and independent random inputs.

Lean: `Theorems/RoomAddress.lean` (`target`, `encoded`, `selector`, `encoded_eq_selector`, `selector_lt`, `start`, `finish`, `coreCheck`, `caseCheck`, `check`, `case_of_check`, `pointer_of_check`). Private: `Proof/RoomAddress.lean` (`room_address_check`). No Route signature changed.

Final validation passed: full `prove.py`, the new private check, `room-jump-check FM2 100`, `room-stand-check FM2 100`, and `room-floor-check FM2 60` all exited 0. On 59,811 floor-test frames, all 410,104 selectors, pointers and read addresses matched; all discrepancy counters were zero. These real checks support the formula but do not remove the remaining proof obligations. The final route and new-theorem axiom checks exited 0 without `sorryAx`.
