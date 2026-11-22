[← Back](README.md) | [English](d-2-4-2-7-EraseRange.md) | [Japanese](d-2-4-2-7-EraseRange-ja.md)

# The erase's row from bounds

**Claim.** The four walks of the room's frames prove what they proved in round 32 (on every frame of the room the coin's erase writes in the block buffers,
and the other parts of `SiteOK` from the remaining fields), with tables two to three times smaller: the private build is about three times shorter.

This is proved. No field is removed or added. The statements of the frame theorems (`LoopTime.rec_frame1B` to `rec_frame4B`, `loop_sites_of_rows`) and of
`route_1_1` are the same as in round 32. What changed is the walk inside the checks, and so the private proofs' tables.

## Why round 32 was slow

Round 32 (`EraseRow`) split the player's height `y` into nine pieces in the collision routine and kept them apart up to the routine's return. The walk's byte
knows only bits, so a bound such as `y ≤ 207` lives only in pieces whose known high bits imply it. Measured in round 33 on walk (ii): 183,921 of its 239,141
table states were in that region, but they had only 32,654 keys without the pieces (5.6 states per key). Walk (iii): 919,605 of 1,218,249, with 163,270 keys.

## The statement

`tr_n(j)` is the machine after `j` instructions of frame `n`. A **bound** is three numbers `(i, lo, hi)`: the byte `i` (a RAM byte, or `aI` for the
accumulator) is at least `lo` and at most `hi`. The walk's abstract state carries a list of bounds in its field `log`, which `Sim` (the relation between an
abstract state and a machine) does not read.

```
FOK(l, m)       :=  ∀ (i, lo, hi) ∈ l,  lo ≤ val(m, i) ≤ hi          (val(m, aI) = m.a, else the RAM byte)
rlo(A, i), rhi(A, i) :=  the smallest and largest value of byte i that A's known bits and A's bounds allow
range_ok        :  Sim(A, m) ∧ FOK(A.log, m)  →  rlo(A, i) ≤ val(m, i) ≤ rhi(A, i)

keepF_ok        :  Sim(A, m) ∧ FOK(l, m)  →  FOK(keepF(A, l), step(m))       (the bounds on RAM bytes that the step does not write: StepWrites.keepOK)
xferA_ok        :  Sim(A, m) ∧ FOK(A.log, m)  →  FOK(xferA(A), step(m))      (the accumulator's bound through seven kinds of instruction, below)
mkL_ok          :  Sim(B, m) ∧ FOK(B.log, m)  →  FOK(mkL(is, B), m)          (new bounds from B's known bits)
fok_of_leF      :  Sim(W, m) ∧ FOK(W.log, m) ∧ leF(W, D)  →  FOK(D.log, m)    (the cover of a table state D asks its bounds too)
covF_splitVal   :  Sim(A, m) ∧ FOK(A.log, m)  →  ∃ B ∈ splitVal(i, A), Sim(B, m)   (the values of byte i inside its bound)
```

`xferA` gives, for one step from `A` at the places `xq` (the row's seven instructions), with `[lo, hi]` the accumulator's range in `A`:

```
LDA zp,X  (X known)                    a' ∈ [rlo(A, z + X), rhi(A, z + X)]
CLC, SEC                               a' ∈ [lo, hi]
ADC abs,Y (Y, carry c known, ROM)      a' ∈ [lo + v + c, hi + v + c]          if hi + v + c ≤ 255   (v: the operand)
AND #0xF0                              a' ∈ [16 · ⌊lo/16⌋, 16 · ⌊hi/16⌋]
SBC #k    (carry c known)              a' ∈ [lo − (k + 1 − c), hi − (k + 1 − c)]   if k + 1 − c ≤ lo
STA zp                                 ram'(z) ∈ [lo, hi]
```

Each case is proved from the CPU's code of that opcode (`step_rom`, `go_ldaZpx`, `go_adcAby`, `go_andImm`, `go_sbcImm`, `go_staZp`, `tick_a`, `tick_ram`).

The walk with bounds (`walkV`) splits a state (`piecesF`: the pieces of a split that the bounds do not exclude), takes the step of round 32's walk
(`RoomPause.pstep`), and gives each successor its bounds (`updF`: those kept, those of `xferA`, and new ones from the known bits at the places of `Rules.mkAt`; none at
the collision routine's return and after the erase). `frameV` has the conclusions of `EraseRow.frameG` (round 32):

```
frameV  :  VOK(…) → RoomCond E r K m → InCls G m → (∀ j, R(tr j))  →  (∀ j, SiteOK P (tr j)) ∧ ∃ B, fin B ∧ Sim E (m.frame, 2) B (frame m i)
```

## How it works

**The height's tests.** The collision routine tests `y` in six places: at its start (`y < 207`), before the head's call (`y ≥` the head's upper extent), before
the feet's calls (`y < 207`), where the player lands (`y := y & 0xF0`), and before each side call (`32 ≤ y < 228`, `8 ≤ y < 208`). The walk finds the six
places from the ROM's bytes (`windows`: each `LDA zp` of `y` followed by a compare, and the `AND zp` of `y` followed by its store). At each one it splits `y` into
round 32's nine pieces (pruned by `y`'s bound), the compares and branches decide in each piece, and at the places after the window the walk makes a bound on `y`
from the piece's known bits and forgets the bits. So the pieces meet again at once: the region has about one state per key.

**The row.** The block buffer routine computes the row's offset `Y = ((y + adder) & 0xF0) − 32` by `LDA zp,X`, `CLC`, `ADC abs,Y`, `AND #0xF0`, `SEC`,
`SBC #32`, `STA zp`. `xferA` moves `y`'s bound through these seven instructions to a bound on the stored row byte, with no split. At the erase's `LDY zp` of the
row byte the walk splits the byte into its values inside its bound, so `Y` is known at the erase and round 32's check `eraseOK4` holds. This split is only on the paths to the erase.

**The search** (no part of the proof: the walk checks the table) keeps the pieces of a window apart only inside the window (`keyL`), runs them through it to the
places after it (`advAt`), joins two states by widening each bound of the first to hold on the second (`joinV`), and forgets the accumulator and `Y` after
the erase (`aidsV`: the code after it loads both before it reads them). The lists of places are made once (`Rules`, `KeyD`, `SplitD`): a first version that
found them again at each step took twice as long.

**Measured** (`buffer-ctl-check FM2 11 rangecheck` to `14`, natively, the four at the same time with three other workers running; the search alone):

| walk | table (round 32, round 31) | search | failing states |
|---|---|---|---|
| (i) | 159,849 (320,474, 148,250) | 64 s | 0 |
| (ii) | 78,516 (239,141, 66,917) | 44 s | 0 |
| (iii) | 415,124 (1,218,249, 357,129) | 194 s | 0 |
| (iv) | 176,788 (337,408, 265,619) | 73 s | 0 |

The private build (the final `prove.py`, step 5, with other workers' builds at the same time, load about 4): `Proof.SiteMusic1` 80 s (round 32: 223 s),
`SiteMusic2` 56 s (196 s), `SiteMusic3` 236 s (1,186 s; about 820 s on a quiet machine), `SiteMusic4` 84 s (231 s). In one session, natively, the four walks of
`LoopTime.recCheckB` took 412 s together; round 32's four walks took 1,366 s (`buffer-ctl-check FM2 1 rowcheck`).

Tried and not used: a split of `y` into its values at the row's load (about 200 pieces at each call; the tables were as small, but each piece was copied and
covered); rounding the dots of joined states to multiples of 64 to 2048 in the search (the rounding of the last dot adds up along a path and breaks the
time's check: 346 failing states for 64; rounding only the first dot made the search longer).

## Assumptions (not proved in Lean)

* None new. `roomRead` and `roomXbit` are unchanged.
* `roomXbit` (the position's low bits not 0 when the side pipe's code reads the position) needs `x ≤ 207` px at that read: a bound over frames (the pipe's
  mouth as a wall). The walks do not know `x`. Narrowing it to the entering frame would need the walks of `EntryRoutine.rt_of_rows` (through `SideEntryEnd`,
  `SideEntryRest`, `RoomMap.clean_of_rows`) restated without it; with `x & 15 = 0` the code does not set the area change's timer.
* `roomRead` needs the block buffers' contents in the walks' states; the erase's step asks that the walk knows no byte of the block buffers (`bufFree`).

## Lean

`Theorems/EraseRange.lean`: bounds (`mkF`, `fI`, `fLo`, `fHi`, `aI`, `valOf`, `abK`, `FOK`, `loOf`, `hiOf`, `rlo`, `rhi`, `okI`, `range_ok`, `mkL`, `keepF`,
`leF`, `consF`), the CPU's seven steps (`tick_*`, `step_rom`, `go_mZpx`, `go_ldaZpx`, `go_fetch16`, `go_penalty`, `go_adcAby`, `go_andImm`, `go_sbcImm`,
`go_staZp`, `add3_toNat`, `and_f0`, `not_toNat`), `xferA`, `xferA_ok`, `Rules`, `updF`, `updF_ok`, splits (`CovF`, `piecesF`, `cov_pieces`, `splitVal`,
`covF_splitVal`, `splitV`, `covF_splitV`), the walk (`stepV`, `coverV`, `weakenV`, `walkV`, `LiveV`, `live_stepV`, `frame_of_walkV`), the search (`joinV`,
`routeV`, `advV`, `runV`, `searchV`, `searchBV`, `cfgBV`), the check (`walkCheckV`, `VOK`, `vok_of_check`, `frameV`), and on the ROM `windows`, `merges`,
`rowPcs`, `eraY`, `zPtr`, `SplitD`, `splitData`, `aidsV`, `rulesOf`, `forgetV`, `advAt`, `KeyD`, `keyL`, `keyData`. `Theorems/LoopTime.lean`: `walkChk` uses
`EraseRange.walkCheckV`; `rec_frame1B` to `rec_frame4B` use `EraseRange.frameV` (same statements). The private proofs have the same text as in round 32. The
theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 rangecheck     # the four walks with bounds, natively (2 also runs recCheckB)
.lake/build/bin/smbrta buffer-ctl-check FM2 13 rangecheck    # walk (iii) alone (11, 12, 14: walk (i), (ii), (iv))
```
