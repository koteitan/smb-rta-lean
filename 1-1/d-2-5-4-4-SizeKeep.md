[← Back](README.md) | [English](d-2-5-4-4-SizeKeep.md) | [Japanese](d-2-5-4-4-SizeKeep-ja.md)

# The player's size through the room

**Claim.** The frame that enters the side pipe starts with a small player (the reference's size) or a big one (the size byte 0). This is proved. The room's frames keep the size (two walks of the room's frames, about 3 s each natively), and at the room's first control the rows of the first change know bits 1 to 7 of the size byte (one check of the rows, about 33 s natively). So the field `height₂` of `Route.Run` is gone, with no new field. It asked that the entering frame starts with one of the two sizes, or that the height at the entry is the reference entry's.

For this the vertical pipe's entry knows bits 1 to 7 of the size byte, as it knows those of the player's status (`PipeChangeEnd.entryMasks`), and the exit's list has them too (`exitMasks`). The press of Start on the title and the frames from control give them at the entry (`EntryKeep`, `Run.entry₁`): the change of size flips only bit 0. With it the guard of `chg.upCleanU` protects the size byte too (144 bytes, was 143).

`m[i]` is the RAM byte `i` of `m`, `frame(m, i)` one frame of `m` with the input `i`, `trₙ(j)` the machine `j` instructions into frame `n`. `seq(n)` is the machine when frame `n` of the run begins. `a₁`, `b₁`, `a₂` are the vertical pipe's entry, the room's first control and the side pipe's entry (`Route.Base`). `size(m)` is the player's size byte, `rt(m)` the routine byte, `r` the room's reference machine (a small player), `e` the vertical pipe's reference entry. `Room` and `SiteOK` are those of [The screen's page in the room](d-2-4-ScreenPage.md). `Keep(v)` is the check that the walk of [the level's number](d-2-5-3-AreaKeep.md) passes with the size byte in a table of one state with the value `v` (`roomCheckS`). `timeRows` are the rows of the first change where `left` is 0, and `InRowsT(m)` says that `m` is in them ([The change into the room](b-3-2-PipeChangeEnd.md)).

## The statement

```
entryMasks, exitMasks  ∋  (size, bits 1 to 7)                                   (round 22)
Entry(m)       ⟹  size(m) &&& 0xFE = size(e) &&& 0xFE                           (PipeChangeEnd.Entry; Run.entry₁ gives it at a₁)

rowsCheckS     :  ∀ row ∈ timeRows, ∀ S ∈ row:  S knows bits 1 to 7 of size to be 0,   size(r) &&& 0xFE = 0,   size(r) ≠ 0
size_of_rows   :  rowsCheckS,  InRowsT(m),  m has control      →   size(m) = size(r)  ∨  size(m) = 0
byte_all       :  Keep(v),  Room(seq c),  size(seq c) = v,
                  ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j)))  ∧  rt(seq n) = rt(r)
                  →  ∀ n ∈ [c, e]:  size(seq n) = v
size_run       :  Keep(size(r)),  Keep(0),  the same conditions,  size(seq c) ∈ {size(r), 0}
                  →  ∀ n ∈ [c, e]:  size(seq n) ∈ {size(r), 0}

Run.size₁      :  size(seq b₁) = size(r)  ∨  size(seq b₁) = 0                       (theorem)
Run.size₂      :  size(seq(a₂ − 1)) = size(r)  ∨  size(seq(a₂ − 1)) = 0              (theorem)
Run.y₂         :  y(seq a₂) = y_e                                                    (theorem, now with no field)
```

`Run.size₁`: the machine at the room's first control is in the rows of the first change (`ChangesK.run₁`, `inRowsT`) and has control (`ChangesBase.ctl₁`). `Run.size₂` takes `c = b₁` and `e = a₂ − 1`: `b₁ < a₂` (`Run.b₁_lt_a₂`), the room's first control is in the room's condition (`ChangesK.roomAt`), and each frame from `b₁` before `a₂` meets `SiteOK` (`chg.roomSites`) and starts in the player's routine (`ChangesBase.roomStay`). `Run.y₂` has two cases: with the reference's size the walk of [the height](d-2-5-4-EntryHeight.md) gives the height, with the size 0 the walk of [EntryHeightBig](d-2-5-4-3-EntryHeightBig.md).

Lean: `Theorems/SizeKeep.lean` (`sizeI`, `refSize`, `roomCheckS`, `KeepOK`, `byte_all`, `rowS`, `rowsCheckS`, `low_one`, `zero_or_one`, `size_of_state`, `size_of_rows`, `Facts`, `factsOf`, `size_run`), `Theorems/PipeChangeEnd.lean` (`entryMasks`, `exitMasks`), `Theorems/Route.lean` (`RoomChecks.height : SizeKeep.Facts …`, `Run.size₁`, `Run.size₂`, `Run.y₂`), the private `Proof/SizeKeep.lean` (`size_keep_ref`, `size_keep_zero`, `size_rows`) and `Proof/EntryHeight.lean` (`height_facts`). There is no game data in the public files.

## How it works

Only three places of the game store to the size byte by its address (read from the disassembly): the setup of a new game and the continue store the small value, and the change of size stores the old value with its low bit flipped. So bits 1 to 7 of the size byte stay 0 from the start of the game, if no store through an index or a pointer reaches the byte.

* **From the title to the vertical pipe** (part a). The size's bits are one of the kept watches of `EntryKeep` (the bytes and masks of the entry that `restNames` does not list). The condition at the press of Start on the title knows the byte, so frame 0 ends with the bits (`nearCheck`). Each frame from control keeps them (`keepCheck`): the change of size is `EOR #1`, which keeps bits 1 to 7, and the guard of `upCleanU` protects the byte from the stores through an index or a pointer.
* **Through the vertical pipe** (part b). The start states of the pipe's walk know the bits (`startsP`, the masks of the entry). No frame of the pipe stores to the size, so the walk's frames keep them, and the exit's states know them by the exit's masks. So every state of the rows after the exit knows them, and the machine at the room's first control has them (`rowsCheckS`, `size_of_rows`).
* **Through the room** (part d). The walk of `AreaKeep` (the walk of `RoomPause`) with the byte in a table of one state: inside the sound routine, the pads and the pause routine the walk knows the byte; everywhere else every step must keep it, or write a value of the table (`RoomPause.pstep`). The walk passes with the reference's value and with 0. So a frame that starts in the room's condition with the byte at the value ends with it (`RoomPause.pause_step`). The induction is that of `RoomPause.pause_run`, at every frame and not only at the last.

`SizeKeep.Facts` extends `EntryHeightBig.Facts` with the two walks and the check of the rows, so that `RoomChecks.height` holds them and the constructions of `RoomChecks` in the private files stay as they were.

## Measured

* `size-keep-check FM2 50 walk` (exit 0): the two walks of the room natively 3.0 s and 5.0 s on a busy machine (3.1 s and 2.6 s on a quieter one); the rows of the time: 1 row of 14,224 states, every state knows bits 1 to 7 of the size to be 0, `rowsCheckS` 32.5 s natively.
* `entry-walk-check` (exit 0), with the size among the watches: one frame from control 1,176,671 steps, no failure; `keepCheck` 7.2 s, `nearCheck` 3.1 s.
* `entry-keep-check FM2` (exit 0): `Entry` has 110 bytes and masks (was 109), 75 proved at the entry, 72 kept from control, 35 in `Rest`; on the real runs of that check every frame keeps the kept bytes and every entry meets `Entry`.
* `pipe-end-check FM2` (exit 0): the check of the pipe's frames and rows with the new masks, 309 s natively on a busy machine; 15 real entries meet the condition at the entry.
* `up-clean-u FM2` (exit 0): `CleanK` of the guard with the size byte holds on every instruction of the movie (368 frames), the reference entry (440), 300 own runs from control (127,841 frames), 300 own runs from the movie's frames (75,241) and 40 late entries (17,600).
* `size-keep-check FM2 30 mushroom` (exit 0): own runs from the movie's frames at 200 to 400 px with a walk, a held jump and then right; 1,200 tries, 10 take the mushroom (the size changes from the reference's to 0). On these 10 runs from control (3,328 frames) `CleanK` of the guard with the size byte holds on every instruction, and bits 1 to 7 of the size stay 0.
* The movie: from the first control on the size is the reference's; so it is at the vertical pipe's entry, at the room's first control (after movie frame 653), at the start of the room's 111 frames before the entry, and at the start of the entering frame.
* The movie's inputs with a big player put in 30 frames before the vertical pipe's entry: the run enters the pipe, the room's first control has the size 0, and the room's 111 frames all start with 0.
* 50 own runs of 400 frames from the movie's frames from control to the vertical pipe: the size never changes (no run takes the mushroom).
* Own runs in the room: small, 50 runs, 19,938 frames, 19 entries; big, 50 runs, 20,612 frames, 18 entries. No frame ends with another size than its run's start; every entering frame starts with the run's size.

## Uses from other parts

* Part a: `Run.entry₁` (`EntryKeep.entryV_of_title`, with `title`, `Run.upStart₁`, `Run.upClean₁` from `chg.upCleanU`, `chg.entryRest₁`).
* Part b: the masks of `PipeChangeEnd`, `ChangesK.run₁`, `PipeRunK.inRowsT` with `RoomChecks.pipe`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`.
* Part c: `ChangesK.roomAt` (the room's condition at the first control), `chg.roomSites`, `ChangesBase.roomStay`, `Run.b₁_lt_a₂`.
* Part d: the walk of `AreaKeep` (`roomCheckA`, `roomOK_of_check`) and `RoomPause.pause_step`.
* No cycle: none of these uses `height₂`, `Run.size₁`, `Run.size₂` or `Run.y₂`.

## What changed in the route

* Removed: the field `height₂`.
* Added: no field.
* `PipeChangeEnd.Entry` (at the vertical pipe's entry) asks bits 1 to 7 of the size too; `Run.entry₁` proves it, `chg.entryRest₁` does not ask it.
* The guard of `chg.upCleanU` protects the size byte too: no store through an index or a pointer on the frames from control to the vertical pipe writes it.
* `RoomChecks.height : SizeKeep.Facts …` (it was `EntryHeightBig.Facts …`).

## Assumptions (not proved in Lean)

* The fields that were there before: `SiteOK` on each instruction in the room (`chg.roomSites`), and `chg.upCleanU` with one more protected byte.

**Files.** `Theorems/SizeKeep.lean`, `Theorems/PipeChangeEnd.lean`, `Theorems/Route.lean`; the private checks are in `Proof/SizeKeep.lean` (`genSizeKeep` in `Main.lean`), used in `Proof/EntryHeight.lean` (`genEntryHeight`).

**To reproduce.**
```
.lake/build/bin/smbrta size-keep-check FM2 50 walk     # the two walks, the rows, the movie and own runs, about 2 min
.lake/build/bin/smbrta entry-walk-check                # the walks of EntryKeep
.lake/build/bin/smbrta pipe-end-check FM2              # the pipe's frames and rows, about 5 min
.lake/build/bin/smbrta up-clean-u FM2                  # the guard on real frames
.lake/build/bin/smbrta size-keep-check FM2 30 mushroom   # own runs that take the mushroom, with the guard, about 3 min
```
