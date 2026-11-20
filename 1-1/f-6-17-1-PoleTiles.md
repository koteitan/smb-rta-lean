[← Back](README.md) | [English](f-6-17-1-PoleTiles.md) | [Japanese](f-6-17-1-PoleTiles-ja.md)

# A tile condition at the frame's start

This is a conditional partial result. `PoleTiles.ColumnMap` classifies pole bytes in a specified RAM interval at one machine: each is in the pole's column and the player's page is close enough. It does not fix the other bytes or require that they stay unchanged.

`WriteOK` checks only actual write locations. A resulting pole byte must have the right column and page. A page-byte write must preserve the page condition for existing pole bytes. `step_column` and `prefix_column` carry `ColumnMap` from frame start to every instruction before the touch's write. Coin erasures and blank block writes are permitted. The proof uses `StepWrites` and does not assume `TileRead`.

`load_result` proves the byte identity for an actual indirect-indexed `LDA` from RAM: RAM and Y stay unchanged, and A is the byte at the post-read address. The opcode and pointer metadata are checked by `readCheck`. `tile_after_load` and `prefix_tile_after_load` then derive `TileRead` for reads in the classified interval.

Measured before proving: the block-buffer condition and write test passed on 1,091 TAS frames, 3,169 frames from 32 random runs, and 6,864 frames with overwritten heights and positions. They made 2,857, 11,486 and 17,301 side reads respectively. No read was outside the block buffers and no `TileRead` failed. Ninety reads in the overwritten cases saw a blank written by the head collision during the frame, rather than the frame-start value. Their writes satisfy the value-aware test.

The interval cannot simply be extended to the column buffer. That stronger start condition failed on four TAS frames and 48 random frames, because the column being drawn temporarily holds pole tiles. Its write test also failed. This false condition is not installed.

The original field `tiles` remains unchanged. Deriving the write tests from existing ROM/control assumptions, proving all relevant reads lie in the classified interval, and connecting every post-read program counter to its preceding actual load remain open. The actual-load theorem also explicitly requires a RAM address and a good machine. No new field replaces these gaps.

**Files:** `Theorems/PoleTiles.lean`; private `Proof/PoleTiles.lean` checks only load metadata.

**Round 21:** the field `tiles` is gone. `TileRead` is proved along the walk of the touch's frame from a map at the frame's start and conditions on single stores and reads: [The pole's tiles at the touch](f-6-17-2-PoleTileWalk.md).
