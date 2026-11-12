[← Back](README.md) | [English](c-7-3-SideEntryRule.md) | [Japanese](c-7-3-SideEntryRule-ja.md)

# The side pipe's entry on real frames

**Claim.** This is a partial result. An entry into the side pipe is defined on the real machines. If a frame enters, then when the side check of that frame reads the page, Mario is at or right of the left end of the pipe's mouth. So the hypotheses `entry`, `entry_mem`, `entered`, `entry_P` of `RoomJoin` are gone. These four said that the collision routine, run alone on a hand-written block buffer (`SidePipe.withPipe`), enters. The proof follows one pass of the side check with an abstract machine. It does not follow the rest of the frame. What is left is the hypotheses `Pass` and `pos`.

**Now.** `RoomRun` no longer uses this page's theorem. [The side pipe's entry: one whole frame](c-7-16-SideFrame.md) follows the whole frame, and `Pass` and `pos` are no longer fields. The theorems here stay, and the pieces of a byte read (`pieces`) are used there.

The method is that of [Touching the pole on real frames](f-6-1-PoleEntryRule.md). The side check is the same. The write, the tiles, the exits and the page are other ones.

`frame(m, i)` is a real frame with input `i`. `tr(n)` is the machine `n` instructions into that frame. `rt(m)` is `GameEngineSubroutine`. `e_s` is the number of the side pipe's routine. `page(m)` is `Player_PageLoc`, `x(m)` is `Player_X_Position`. `w` is the instruction in `ChkGERtn` that writes `rt`. `T₁` is the side pipe's tile, `T₂` the value of the first compare after `ContSChk`. The routine enters by either of the two. `col` is the pipe's column, and `d_C` the top of that column in the block buffers. `R` is the number of rows of a block buffer. `x₀` is the first `x` with his right side in the mouth, and `P₀ = 256·x₀` is the position of the mouth's left end ([Entering the side pipe](c-4-SidePipe.md)).

```
WriteStep(n)    :=  rt(tr(n)) ≠ e_s  ∧  rt(tr(n + 1)) = e_s
Enters(m, i)    :=  ∃ n,  WriteStep(n)
EndsEntry(m, i) :=  rt(m) ≠ e_s  ∧  rt(frame(m, i)) = e_s
px(m)           :=  256·page(m) + x(m)

Start(m)        :=  pc(m) = DoPlayerSideCheck, the stack pointer is its value, the byte of the adders' offset is a big or a small Mario's,
                    the dot is after vblank and before the frame's end, no NMI, no vblank, no strobe
AtEntry(m)      :=  pc(m) = the read of the page in BlockBufferCollision  ∧  register Y is an offset of the side check  ∧  register X = 0
AtRead(m)       :=  pc(m) = the routine's `LDA (zp),Y`
RowOK(m)        :=  Y mod 16 = 0  ∧  Y < 16·R
TilesOK(m)      :=  ∀ place d of the block buffers,  mem(d) ∈ {T₁, T₂}  →  ∃ r < R,  d = d_C + 16·r
Pass(n)         :=  pc(tr(n)) = w  ∧  ∃ n₀ ≤ n,  Start(tr(n₀))
                    ∧  (∀ j ∈ [n₀, n],  pc(tr(j)) ∉ exits)
                    ∧  (∀ j ∈ [n₀, n),  AtRead(tr(j))  →  RowOK(tr(j)) ∧ TilesOK(tr(j)))
exits           :=  ExSCH, ExCSM, the instruction before `ContSChk` (the jump to the climbing routine), ErACM (a coin), ImpedePlayerMove (a stop)
pos(P)          :=  ∀ n j,  WriteStep(n)  →  j < n  →  AtEntry(tr(j))  →  ∃ f ≥ 0,  P = 256·px(tr(j)) + f
```

`TilesOK` is the formula of the pole. The pole's condition on the page always holds here, because the page is 0.

```
no_write             :  walkCheck,  s(j + 1) = step(s(j)) (j < n),  Start(s(0)),
                        (∀ j < n,  AtEntry(s(j)) → px(s(j)) < x₀),  (∀ j < n,  AtRead(s(j)) → RowOK ∧ TilesOK),
                        no exit (j ≤ n)                                          →  pc(s(n)) ≠ w
entry_right_of_left  :  ruleCheck,  Enters(m, i),  (∀ n,  WriteStep(n) → Pass(n))
                        →  ∃ n j,  WriteStep(n) ∧ j < n ∧ AtEntry(tr(j)) ∧ x₀ ≤ px(tr(j))
mouth_of_pass        :  ruleCheck,  Enters(m, i),  (∀ n,  WriteStep(n) → Pass(n)),  pos(P)  →  P₀ ≤ P
enters_of_ends       :  EndsEntry(m, i)  →  Enters(m, i)
PassR(n)             :=  Pass(n) with RowOK alone at the reads (no TilesOK)
pass_of              :  PassR(n),  (∀ j < n,  AtRead(tr(j)) → TilesOK(tr(j)))  →  Pass(n)
RoomRun.mouth_of     :  Checks,  RoomRun  →  P₀ ≤ P(E)
side_rule_check (private) :  ruleCheck(sy, m₀) = true (native_decide)
```

The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/SideEntryRule.lean`, `RoomRun` in `Theorems/RoomJoin.lean`, private `Proof/SideEntryRule.lean` (`side_rule_check`).

The fields of `RoomJoin` changed as follows.

* Removed: `entry`, `entry_mem`, `entered`, `entry_P` (in `RoomFields`). `Checks.side` became `Checks.sideRule`.
* Added: `enters` (`Enters(fm(E − 1), pad(E))`, the machine and the input when frame `E` begins), `pass` (`∀ n, WriteStep(n) → Pass(n)`), `pos` (`pos(P(E))`). All are fields of `RoomRun`, and facts about frame `E` alone. `RoomRun.mouth_of` makes `RoomCore.mouth` (`P₀ ≤ P(E)`) from them. Now `pass` gives `PassR(n)`, and the tiles are a field of their own, `tiles` (`∀ n j, WriteStep(n) → j < n → AtRead(tr(j)) → TilesOK(tr(j))`); `pass_of` puts them together.

The old `entry_ground` (the entry state is on the ground) is gone. The proof did not use it.

## How it works

**The abstract machine.** The machine and the start state of [Touching the pole on real frames](f-6-1-PoleEntryRule.md). Only the stack pointer and the adders' offset are known.

**Three places to split.** Before the addition of the position and before the read of the page, as for the pole. Before the read of the page the split is under the hypothesis `px < x₀`. The mouth is on page 0, so the page is 0 and `x < x₀`. Then the pointer is known, and the right side's read is left of the pipe's column.

**The pieces of a byte read.** Here it differs from the pole. The pole's two tiles differ in one bit. `T₁` and `T₂` differ in 5 bits. So a piece "differs from `T₁` at a bit" does not rule out `T₂`. There are 8 pieces:

* at a bit where the two tiles agree (3 of them): differs from that value;
* name the bits where they differ `d₀ … d₄`. For each `k`: `d_k` as in `T₂`, and `d_{k+1}` (`d₅ = d₀`) as in `T₁`. 5 of them.

A byte that is neither tile is in a piece. On the bits where they differ, `T₁` and `T₂` are exact opposites. A byte that is neither differs from both at a bit where they agree, or has in the cycle a place where a bit as in `T₂` is followed by a bit as in `T₁`. `piecesCover` checks all 256 bytes. Each piece is known to differ from both tiles.

**What happens to the byte read.** It stays in `A` and comes to the two `CMP` of `ChkPBtm`. From its known bits they are known not equal, and the path goes to the routine that stops him (an exit). So no path comes to `w`.

**Size.** 38,814 steps, 21,028 forks, 0 failures, table 1,412. About 2 s in a program, about 3 s in the build of the private proof.

## The instructions that write the side pipe's number to `rt`

Read from the code, not proved. Of the 12 instructions that write `rt` directly, only `w` in `ChkGERtn` writes the side pipe's number. `w` is reached only when a compare in `ChkPBtm` finds one of the two tiles, and that only from `CheckSideMTiles` of the side check.

A frame where an indexed write or a write through a pointer makes `rt` equal `e_s` meets `Enters`. It does not meet `pc(tr(n)) = w` of `Pass`, so the hypotheses of `RoomRun` exclude it. It does not occur on real frames.

## Checked on real frames

A program (`side-rule-check`).

| run | frames | side checks (control) | reads | entries |
|---|---|---|---|---|
| the movie's room (from first control to 3 frames after the entry) | 113 | 103 | 406 | 1 |
| random inputs to the right, from frames of the movie in the room (200 runs) | 45,123 | 44,638 | 174,758 | 67 |
| every input of Left, Right, A, B for 5 frames, from 12, 8, 5, 3 frames before the entry | 11,072 | 11,072 | 43,280 | 352 |
| one frame per height, position, state and facing near the mouth, overwritten | 38,400 | 22,110 | 75,944 | 1,295 |

* In every row, every side check of a frame in control meets `Start`. Every read meets `RowOK` and `TilesOK`.
* Every entry writes with `w`, and every one ends a pass. None is left of the mouth. The position at the read of the page is the frame's end position without its fraction (`pos`). An entry frame ends with the side pipe's routine (`EndsEntry`).
* The movie: the first control in the room is after movie frame 653, and the entry 111 frames later. Then the block buffer has, in the pipe's column and the next, `T₁` and the tile after it in the third row from the bottom, and above them the pipe's top tile and the one after it. This is the same as `SidePipe.withPipe`.
* The positions are 0 to 21 px from the mouth's left end. The heights are only on the ground.

## Assumptions (not proved in Lean)

* **The write in `Pass`.** Only `w` makes `rt` equal `e_s`. Earlier in that frame the side check started, and from there it did not go to an exit. Read from the code, and checked on the real frames above. The rest of the frame (NMI, sound, screen, enemies) is not followed.
* **`Start`.** The stack pointer, the adders' offset, the dot, the flags. As for the pole.
* **`RowOK`.** Read from the code, as for the pole.
* **`TilesOK`.** The two tiles are only in the pipe's column of the block buffers. [The block map in the room](c-7-12-RoomMap.md) proves it at every read of every frame of the room, on the machines of the change into the room and out of it (`Route.Changes`), from what the room's frames already assume there (`SiteOK`). `Route.Run.roomTiles` joins frame `E` of `RoomRun` to those machines by the theorem `Route.Run.roomEnter`; the field `tiles` is gone.
* **`pos`.** `P(E)` is the position at the read of the page. This is part of making a `Frame` from a real frame. No longer a field of `RoomRun`: [one whole frame](c-7-16-SideFrame.md) needs `P(E)` only at the end of the move (`movedE`).
* **The right end, the height, the ground.** Only the left end comes out here. `RoomJoin` uses only the left end.

**Files.** `Theorems/SideEntryRule.lean`, private `Proof/SideEntryRule.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-rule-check FM2 [N]    # the check of one pass, and the hypotheses on real frames; N runs of random inputs
```
