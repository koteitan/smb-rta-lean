[← Back](README.md) | [English](c-7-16-SideFrame.md) | [Japanese](c-7-16-SideFrame-ja.md)

# The side pipe's entry: one whole frame

**Claim.** An abstract machine follows a frame from the idle loop to the frame's end. If an instruction of the frame makes the routine byte the side pipe's, then at the end of the move (`PlayerSubs`) before that write, the position is at or right of the mouth's left end. So three hypotheses of `RoomRun` are gone: `pass` (the write ends one pass of the side check), `pos` (`P(E)` is the position when the side check reads the page) and `edgeE` (no store at the screen's edges and no head's collision up to the write).

The walk needs conditions on single states, as for the vertical pipe ([One whole frame](a-5-2-PipeWrites.md), [The position at the end of the move](a-5-9-MoveEnd.md)). Four of them are proved on the real machines of the run, from the walk of [The block map in the room](c-7-12-RoomMap.md): frame `E` starts in control with the screen's bytes of the room (`StartE`), each of its instructions up to the write is `Clean` (`CleanE`), its reads find the side pipe's tiles only in the pipe's column (`TilesE`), and it does not come to the routine of the head's collision with a block (`HeadE`). One stays assumed: `movedE`.

The walk follows the scroll handler's store of the position at the screen's edges (`w_edge`). It knows the screen's bytes of the room (the scroll lock, the edges' positions and pages), and where the scroll handler asks whether he is off the screen it splits the position into its values. Left of the mouth, the store comes only at the left edge (`x = 0`), and it writes the position that is already there. So `edgeE` is gone.

The names are those of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md) and of the two pages of the vertical pipe. `tr(j)` is the machine `j` instructions into frame `E`, from `fm(E − 1)` with the input `pad(E)`. `x₀` is the first `x` with his right side in the mouth, and `P₀ = 256·x₀` is the mouth's left end. `posP(m) = 256·(256·page(m) + x(m)) + fraction(m)`.

```
G_room                 the guard of One whole frame, with the 5 screen's bytes (the scroll lock, the left and right edges' x and page) known at the start
                       with the room's values and protected from stores with a target not known, and the place h cut (roomG)
FrameStart, Clean      as in One whole frame, with G_room (neither depends on the routine's number)
h                      as in The position at the end of the move: the routine of the head's collision with a block
HypF(m)        :=  (pc(m) = PlayerSubs  →  px(m) < x₀)  ∧  (AtRead(m) → TilesOK(m))  ∧  pc(m) ≠ h

no_write_frame       :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)) (j ≤ n),  FrameStart(s(0)),
                        (∀ j ≤ n,  Clean(s(j)) ∧ HypF(s(j)))                                 →  rt(s(n + 1)) ≠ e_s
entry_right_of_left  :  sideFrameCheck,  Enters(m, i),  FrameStart(m),
                        (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))) ∧ pc(tr(j)) ≠ h)
                        →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ x₀ ≤ px(tr(j))
mouth_of_frame       :  the same,  (∀ n j,  WriteStep(n) → j ≤ n → pc(tr(j)) = PlayerSubs → P = posP(tr(j)))   →  P₀ ≤ P

StartE     :=  FrameStart(fm(E − 1))                         (with G_room: the screen's bytes too)
CleanE     :=  ∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j))     (with G_room)
TilesE     :=  ∀ n j,  WriteStep(n) → j ≤ n → AtRead(tr(j)) → TilesOK(tr(j))
HeadE      :=  ∀ j,  pc(tr(j)) ≠ h
InRoom     :=  TilesE ∧ StartE ∧ CleanE ∧ HeadE
RoomRun.mouth_of     :  Checks,  RoomRun,  InRoom                                                    →  P₀ ≤ P(E)
Route.Run.inRoom     :  the checks of the room,  Run                                                 →  InRoom
side_frame_check (private) :  sideFrameCheck(sy, m₀) = true  (native_decide)
```

`sideFrameCheck` is `PlayerSubs ≠ 0` and the check of the walk. `Route.Run.inRoom` is on [The block map in the room](c-7-12-RoomMap.md).

The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/SideFrame.lean`, `RoomRun` in `Theorems/RoomJoin.lean`, private `Proof/SideFrame.lean` (`side_frame_check`).

## How it works

**The machine.** It is the machine of [One whole frame](a-5-2-PipeWrites.md), with its steps for a store or a read whose target it does not know (`Clean`). At the start it knows the routine byte, the game mode bytes, the 5 screen's bytes, bit 7 of `PPUCTRL` and the stack pointer. The screen's bytes are found in the ROM (the loads of the scroll handler and of the routine of the offscreen bits); their values are those of the reference machine of the room. In the room the scroll lock is on, so the scroll handler does not move the screen.

**Where it splits.** None of this changes the machine.

* At the end of the move, under `px < x₀`: the page is 0, and `x` is in one of a few pieces of `[0, x₀)`. For each bit of `x₀` that is 1 there is one piece: the bits above it as in `x₀`, that bit 0, the bits below it not known. `x₀` has four bits that are 1, so there are 4 pieces. `posCover` checks all 256 bytes.
* At the addition of `x` in the block buffer routine, for a side check: `x` by each of its values that meet its known bits. This needs no hypothesis.
* At the mask of the sum of the height and the adder, for a side check: the 4 high bits of `A` (16 pieces, no hypothesis). Then the row of the read is known. So `RowOK` is not needed.
* At the read, for a side check: the place is known. If it is in the block buffers and not in the pipe's column, `TilesOK` gives the 8 pieces of [The side pipe's entry on real frames](c-7-3-SideEntryRule.md): the byte is neither tile.
* A side check is known by the offset that the routine saves. There are three values of the adders' offset: a big Mario, a big one in the water, a small or crouching one. With only the two of `Start` the walk fails 94,639 times, at reads with the offset of the water.
* Where the scroll handler calls the routine of the offscreen bits: `x` by each of its values (no hypothesis). The abstract addition knows a sum only when it knows both numbers, so the position must be whole here. Then the routine and the edge store are followed exactly. With the screen at its first page, left of the mouth only `x = 0` is off the screen (at the left), and the store writes the left edge, 0, on page 0: the same position. No `x < x₀` is off the screen at the right.
* `h` is cut. The walk of [The block map in the room](c-7-12-RoomMap.md) shows that no frame of the room comes there: `SiteOK` lets a read for the head give only nothing or a coin.

**What is checked.** On every path the routine byte is not the side pipe's. The compares in `ChkPBtm` see a byte that is neither tile, so no path comes to the write `w`.

**The search (no part of the proof).** It keeps the position's piece from the end of the move to the side check. At the return from the scroll handler, and after the column of a read is known, it puts the position back into its piece, so states with other values of `x` are joined. While the position is whole in the routine of the offscreen bits, the registers are in the key: that routine is a loop, and joining its two passes would forget the result. At the start of the side check it forgets every byte but the position and the bytes of `Clean`.

**Size.** 7,523,911 steps, 805,523 forks, 0 failures, table 249,435. In a program: the search about 17 s, the check about 26 s. With `w_edge` cut as before: 7,109,418 steps, table 233,700. Without the screen's bytes, or with the position in pieces at the offscreen question, the walk comes to the write: 199,006 failures. A first walk that split the position into each of its 195 values took 43,422,222 steps and a table of 2,810,791 states (17 GB): too large.

## Checked on real frames

A program (`side-frame-check`). The runs are those of `side-rule-check` on [The side pipe's entry on real frames](c-7-3-SideEntryRule.md).

| run | frames | in control | instructions | reads | entries |
|---|---|---|---|---|---|
| the movie's room (from first control to 3 frames after the entry) | 113 | 111 | 431,592 | 728 | 1 |
| random inputs to the right, from frames of the movie in the room (200 runs) | 45,123 | 45,123 | 174,974,667 | 309,608 | 67 |
| every input of Left, Right, A, B for 5 frames, from 12, 8, 5, 3 frames before the entry | 11,072 | 11,072 | 43,110,571 | 76,496 | 352 |
| one frame per height, position, state and facing near the mouth, overwritten | 38,400 | 38,400 | 144,438,759 | 191,144 | 1,295 |

* In every row, every frame in control meets `FrameStart` with `G_room` (its 5 screen's bytes have the room's values), every instruction of it meets `Clean` with `G_room`, and every read of the block buffer routine meets `TilesOK`. No frame in control comes to `w_edge` or `h`: the walk now follows `w_edge`, and `h` is proved (`HeadE`).
* The program takes about 2 minutes.
* All 1,715 entries write with `w`. Each comes to the end of the move once before the write. There the position is 195 to 216 px, never left of `x₀` (195). It is the frame's end position (`movedE` agrees with `read_P`), and it is the position at every read of the page in the side check.

## The fields of `RoomRun`

* Removed: `pass`, `pos` (and `tiles`, see [The block map in the room](c-7-12-RoomMap.md)). `Checks.sideRule` became `Checks.sideFrame`. Then `edgeE` (no `w_edge`, no `h` up to the write): `w_edge` is followed by the walk, and `h` is `HeadE`.
* Left: `movedE` (`P(E)` is `posP` at the end of the move before the write), a fact about frame `E` alone.
* Not fields: `StartE`, `CleanE`, `TilesE`, `HeadE`. `Route.Run.inRoom` proves them from the walk of the room's frames and the link `roomEnter` of `Route.Run`.

## Assumptions (not proved in Lean)

* **`movedE`.** `P(E)` is the position at the end of the move. The frames up to `t0` read `P(n)` at the frame's end (`read_P`); frame `E` is later than `t0`, and nothing reads it from the machine yet. On real frames the two are the same (above).
* **The link `roomEnter`** (item 1-1-0-4): frame `E` of `RoomRun` is a frame of `Route.Changes` in the room. `StartE`, `CleanE`, `TilesE`, `HeadE` rest on it, and on `SiteOK` of the room's frames (`chg.roomSites`).
* **The right end of the mouth.** Only the left end comes out. `RoomJoin` uses only the left end.

**Files.** `Theorems/SideFrame.lean`, `Theorems/RoomJoin.lean`, private `Proof/SideFrame.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-frame-search          # the search and the check of the walk, about 45 s
.lake/build/bin/smbrta side-frame-check FM2 [N]   # the conditions on real frames; N runs of own inputs (N = 200: about 2 min)
```
