[← Back](README.md) | [English](e-2-10-3-22-SideNear.md) | [Japanese](e-2-10-3-22-SideNear-ja.md)

# A store that may reach the side timer

Round 32 made the field `sideW` ([A push that moves him leaves the side timer at 16](e-2-10-3-20-PushTimer.md)): on a counted frame that ends with the side collision's timer at most 1 (with the lock 0 and the place byte at least the threshold), at each instruction from the scroll handler to the frame's end, a store through an index or a pointer does not write the timer. Here it is proved at every instruction but a few kinds of stores, and the field is asked only at those.

The reason: the timer is a byte of RAM outside the zero page and the stack's page. A store through `X` to the zero page has its target in the zero page. A store to an absolute address plus an index reaches at most 255 bytes past its base, so from most bases no index reaches the timer.

**Claim (round 33).** Write

```
s          = the side collision's timer, as a RAM index (from the scroll handler's load of it)
SideW(m)   := a store through an index or a pointer at m does not write s
NearW(m)   := at m a store to an absolute address plus X or Y whose base some index 0..255 takes to s (modulo the RAM's mirrors),
              or a store through a pointer (STA (zp),Y)
```

`PushTimer.sideW_far`: if 256 ≤ s, the two bytes after the opcode at m are in the program's half of the address space, and ¬NearW(m), then SideW(m).

`PushTimer.sideW_of_near`: at a state of PushTimer's walk that covers m (the walk asks `okS` there: no interrupt pending, the instruction and its two next bytes in the program's half), (NearW(m) → SideW(m)) → SideW(m).

`PushTimer.pix_end` now asks, from the scroll handler on, PosW(m) ∧ (NearW(m) → SideW(m)) at each instruction m in place of PosW(m) ∧ SideW(m). `sCheck` has one more part: 256 ≤ s.

The theorems are `PushTimer.sideW_far`, `PushTimer.sideW_of_near` (axioms `propext`, `Quot.sound`). No game data: the opcodes are those of the 6502, the bases are read from the program.

**Proof.** By the opcode at m (the stores of `PipeWrites.wTarget`):

* `STA`, `STY`, `DEC`, `INC` zero page with `X`: the target is (operand + X) mod 256, below 256 ≤ s.
* `STA`, `DEC`, `INC`, `ROR` absolute with `X`, `STA` absolute with `Y`: the target is the base plus the index; ¬NearW(m) says that for no index 0..255 is that the timer (`PositionKeep.farB_spec`).
* `STA (zp),Y`: NearW(m).

**Measured.**

| check | what | result |
|---|---|---|
| the ROM (a scratch listing of the disassembly) | the stores of `NearW` | 41 stores to an absolute address plus an index from a base 0 to 255 bytes below the timer, and 9 stores through a pointer, in the whole program. Most are in the area parser (the metatile buffer, the area objects' lengths and offsets) |
| native test (a scratch search) | PushTimer's walk with `SideW` asked of what the walk knows (the index, the pointer's bytes), not of the field | fails at 21 to 24 places, all of them stores of `NearW`: the metatile buffer, the area objects' lengths and offsets, the block buffer through the pointer (the coin and the axe, the enemy's ground, the block that he hits, the vine), the hammer's enemy offset, the misc objects' collision flag. There the walk does not know the index (TaintRun knows bits; `INX`, `DEX` on an index with some bits unknown forget it). With the index and `Y` in the table's key and the index split before `INX`, `DEX`, `INY`, `DEY` the search did not end in 300,000 runs (167,395 states, 194 failures at 13 places, some with the index known as the one value that reaches the timer: paths that no real machine takes) |
| `surface-frames-check FM2 200`, `edge-real FM2 256` | `sideW` (the narrowed field, on the frames of the field), `sideW on every frame (measured only)` (`SideW` at every instruction of every frame from the scroll handler on) | 0 failures for both. `surface-frames-check`: 8 sets, 239,510 frames, 215,433 frames checked, the overwritten states included. `edge-real`: 5 sets, 137,955 frames at the routine of the offscreen bits, 108,634 frames that end with the timer at most 1; it fails only on the old stored speed and `after` on frames that do not start clean, with the counts of rounds 30 to 32 |

**On the route.** The field `sideW` is asked at fewer instructions and on more frames. Before (round 32):

```
sideW : ∀ j, 1 ≤ j → j + 1 < g → side(seq j) ≤ 1 → lock(seq j) = 0 → thr ≤ pfs(seq j) →
          ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → SideW(trace n)
```

Now:

```
sideW : ∀ j, 1 ≤ j → j < g → side(seq j) ≠ t₁₆ →
          ∀ k n, arrAt ≤ k → k ≤ n → pc(trace k) = PlayerSubs → frame(trace n) = frame(fm j) → NearW(trace n) → SideW(trace n)
```

where t₁₆ = `PushTimer.pushT`, the value the push stores to the timer (16), read from the push's code. It no longer asks the lock 0 and the place byte at least the threshold, it asks every frame that does not end with the timer at the push's value (in place of the frames that end with it at most 1), and it asks the last counted frame before the touch too: [A frame that the clamp stops ends at the screen's left edge](e-2-10-3-23-StopClamp.md) uses it on those frames. So the new field is not weaker than the old one: it asks less at each frame and more frames.

**What is not proved here.** `SideW` at the stores of `NearW`. To prove it a walk must bound the index at those stores (the rows of the metatile buffer are 0 to 12, the area objects 0 to 2, the misc objects 0 to 8) and know that the block buffer's pointer is a block buffer. TaintRun's walk knows bits only and forgets an index that it counts in a loop; a walk with ranges, or with the index in the table's key and the loop counters followed, is needed. Round 34: such a walk proves it at every store of `NearW` outside the area parser's code and the head's collision with a block ([The stores that may reach the side timer, outside the area parser](e-2-10-3-24-SideRange.md)), and the field is asked only at the others.

**File:** `Theorems/PushTimer.lean` (`absWOps`, `nearWB`, `NearW`, `sideW_far`, `sideW_of_near`, `sCheck`, `pix_end`). `Theorems/SurfaceFrames.lean`: the field `sideW`, `movesScan` ("sideW" only at the stores of `NearW`).
