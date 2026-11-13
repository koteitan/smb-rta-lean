[← Back](README.md) | [English](c-7-5-2-RoomPair.md) | [Japanese](c-7-5-2-RoomPair-ja.md)

# The halt value and A of the frame before, in the room's frames

**Claim.** At the end of each frame of the bonus room before the entry, two relations hold on the machine: in a jump the jump's halt value is 1, and bit 7 of A of the frame before is bit 7 of A. [The first frames of a jump](c-7-5-1-RoomVert.md) needs both at the start of a frame. They were the fields `halt` and `prevA` of [Joining the bonus room](c-5-RoomJoin.md) (item 1-1-c-7-5). Now they are a theorem on the real machines of the run. Nothing new is assumed: the proof uses what [the block map](c-7-12-RoomMap.md) already uses.

`st` is the player's state, `d` the jump's halt value (`DiffToHaltJump`), `p` A of the frame before (`PreviousA_B_Buttons`), `a` A and B (`A_B_Buttons`). `fm(n)` is the machine at the end of the room's frame `n`, `C` the first control, `E` the entry frame. `M` is the machine at a frame's start, `end` the machine at its end, `rt` the routine byte.

```
Pair(m)   :  (st(m) = 1 → d(m) = 1)  ∧  p(m) & 80 = a(m) & 80

pair_frame:  RoomCond(M),  SiteOK on each instruction,  R(x(M), y(M)),  rt(end) = rt_room
             →  R(x(end), y(end))                                 (one walk for each relation R)
pair_of_rows: m in the rows of the time of the change,  m has control  →  Pair(m)
pair_run  :  ∀ n,  b₁ ≤ n < a₂  →  Pair(seq(n))
Run.roomPair: ∀ n,  C ≤ n < E  →  Pair(fm(n))
```

Lean: `Theorems/RoomPair.lean` (`keepXY`, `nextOK`, `markP`, `phP`, `finP`, `pair_frame`, `knHalt`, `knPrev`, `splitLda`, `pair_step`, `rowsCheck`, `pair_of_rows`, `pair_run`, `RoomWalks`), `Theorems/RoomJoin.lean` (`InRoom.pair`, `RoomRun.varc_of`), `Theorems/Route.lean` (`Run.roomPair`, `Run.inRoom`); private `Proof/RoomVert.lean`.

## How

**A walk with a mark.** The walk is the walk of one whole frame of [the block map](c-7-12-RoomMap.md), through the frame of [RoomVert](c-7-5-1-RoomVert.md) (`walkV`, `frame_of_walkV`). Each state has a mark: `[]` says that the relation holds on the machine, `[1]` that it may not. Before each step the mark is set (`markP`):

* if every state that the step gives knows enough bits of the two bytes to show the relation (`nextOK`), the mark is `[]`;
* else, if the mark is `[]` and the step may store to one of the two bytes (`keepXY` fails), the mark is `[1]`;
* else the mark stays. A step that keeps `[]` writes neither byte: by [the one-step lemma](d-3-4-1-StepWrites.md), or it is the erase of a coin, which writes only in the block buffers.

At the frame's end the mark is `[]`, or the routine byte is known and is not the room's (`finP`). `Φ(j) = (mark [] → R(x(tr(j)), y(tr(j))))` holds at every instruction. So a frame that starts with the relation and ends in the player's routine ends with it (`pair_frame`).

**The two relations.**

* `halt`: `x = st`, `y = d`. The jump stores the state 1, and a few instructions later the halt value 1. The walk knows both values: after the first store the mark is `[1]`, after the second `[]`. A store of another known state (0, 2, 3) gives `[]` too (`knHalt`).
* `prevA`: `x = p`, `y = a`. The player's routine stores the new A and B: the mark is `[1]`. At its end the game engine copies them with a load of `a` and a store to `p`. Before such a load the walk splits a state marked `[1]` into the two values of bit 7 of `a` (`splitLda`). The store then leaves bit 7 known and the same in both bytes: the mark is `[]` (`knPrev`). The bit `spent` holds bit 7 in the two pieces, so the search keeps them apart up to the store.

A frame that ends paused does not run the game engine. It writes neither byte, so the mark stays `[]`.

**At the first control.** The rows of the time of the change into the room know `st = 2` and bit 7 of `p` and of `a` at the machine with control (`rowsCheck`, `pair_of_rows`).

**Every frame.** `RoomMap.cond_of_rows` gives the room's condition at the start of each frame from `b₁` to `a₂`. With `SiteOK` (`roomSites`) and the routine byte at each frame's end (`roomStay`), induction on the frames gives `pair_run`. `Run.roomPair` puts the room's frame `n` at frame `b₁ + (n − C)` of `base`, before `a₂`.

| check on the ROM | table | time in a program |
|---|---|---|
| `checkH` (halt) | 36,165 | 3.7 s |
| `checkA` (A) | 36,175 | 3.5 s |
| `rowsCheck` | the rows of the time | 2.5 s |

The first try of `checkA` split at every load of `a`, and did not keep the pieces apart: the search joined them, and bit 7 was lost before the store (6 ends marked `[1]`). With the bit `spent` it went through, but slowly (11 s, 98,441 states), since the pieces stayed apart through the whole player's routine. Now the split is only at a load of `a` followed by a store to `p`, and the mark `[]` clears the bit.

## Checked on real frames

Program `room-pair-check FM2 [N]`: the checks, then each frame of the room from the first control, on the movie and on `N` runs of each of 4 kinds of own input (up to 150 frames; kind 0 presses any button, Start and Select too). At each frame's end in the room both relations are checked.

| run | frames in the room | a relation fails at a frame's end |
|---|---|---|
| the movie, first control to the entry | 110 (and the machine at first control) | 0 |
| any buttons, Start and Select too (50 runs) | 7,500 | 0 |
| right with B (50 runs) | 7,500 | 0 |
| left with B (50 runs) | 7,500 | 0 |
| walls (50 runs) | 7,500 | 0 |

The checks on the ROM are true: `checkH` 3.9 s, `checkA` 3.9 s, `rowsCheck` 3.2 s, `apartP`. `room-vert-check` also counts both relations on its frames: 0 failures there too.

## Assumptions (not proved in Lean)

None new. The proof uses `SiteOK` on each instruction of the room's frames (`chg.roomSites`, item 1-1-d-2-4-2), and the conditions of the change into the room that give its rows, as [the block map](c-7-12-RoomMap.md) does.

**Files.** `Theorems/RoomPair.lean`, private `Proof/RoomVert.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-pair-check FM2 [N]    # the checks (about 10 s) and real frames
```
