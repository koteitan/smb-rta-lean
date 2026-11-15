[← Back](README.md) | [English](d-2-5-4-EntryHeight.md) | [Japanese](d-2-5-4-EntryHeight-ja.md)

# The height at the side pipe's entry

**Claim.** A frame of the room that starts with a small player and ends with the side pipe's routine ends with the height of the reference entry. This is proved, with one check on the ROM (a walk of the room's frame). So `Route.Run` no longer asks the height (`Player_Y_Position`) at the side pipe's entry of a run whose entering frame starts with a small player. For a run whose entering frame starts with another size it still asks it (the new field `height₂`). `chg.entry₂` asks 8 bytes, not 9 (1-1-d-2-5); with [the screen's buffer](d-2-5-5-EntryBuffer.md) it asks 3.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `tr(j)` the machine `j` instructions into it. `seq(n)` and `inp(n)` are the machine when frame `n` of the run begins and its input. `rt(m)`, `y(m)`, `size(m)` are the routine byte, the height and the player's size. `e_s` is the side pipe's routine, `r` the reference machine of the room (a small player), `y_e` the height of the reference entry. `b₁` is the room's first control and `a₂` the side pipe's entry. `RoomCond`, `SiteOK` are those of [The screen's page in the room](d-2-4-ScreenPage.md), `K_T` the bits of [The block map in the room](c-7-12-RoomMap.md): the room's bytes, in each byte of the block buffers the bits that are 0 in the map, and the screen's bytes.

## The statement

```
K_Y             :=  K_T ∪ { every bit of size }
finY(B)         :=  B knows rt ≠ e_s   ∨   B knows y = y_e
WalkOK(fin)     :=  the walk from the start states of RoomCond(K) passes, and every frame end meets fin

frame_end       :  WalkOK(fin),  RoomCond(K, m),  ∀ j, SiteOK(tr(j))        →   ∃ B,  fin(B) ∧ B covers frame(m, i)
height_frame    :  WalkOK(finY),  RoomCond(K_Y, m),  ∀ j, SiteOK(tr(j)),  rt(frame(m, i)) = e_s      →   y(frame(m, i)) = y_e
height_of_rows  :  the hypotheses of RoomMap.map_of_rows on [b, a),  the checks,  b ≤ k < a,
                   size(seq k) = size(r),   rt(frame(seq k, inp k)) = e_s           →   y(frame(seq k, inp k)) = y_e

Run.height₂     :  size(seq(a₂ − 1)) = size(r)   ∨   y(seq a₂) = y_e                 (field, new)
Run.y₂          :  y(seq a₂) = y_e                                                    (theorem)
entryAt_of_y    :  m[y] = y_e  ∧  EntryAt(R₈, m)   →   EntryAt(R₉, m)
```

`R₉` is the 9 bytes of `restIdxA`, `R₈ := R₉ \ {y}` (`restIdxY`). `EntryAt` is that of [The routine at the side pipe's entry](d-2-5-2-EntryRoutine.md).

**`Run.y₂`.** `b₁ < a₂` (`Run.b₁_lt_a₂`), so frame `a₂ − 1` is a frame of the room, and it ends with the side pipe's routine (`Run.rt₂`). If `size(seq(a₂ − 1)) = size(r)`, `height_of_rows` gives the height. Else `height₂` gives it.

Lean: `Theorems/EntryHeight.lean` (`HP`, `bitSet`, `top2`, `top1`, `topY`, `lowA`, `zoneY`, `preY`, `stepY`, `finY`, `walkY`, `mix64`, `keyY`, `normY`, `Opts`, `optsY`, `putY`, `routeY`, `runY`, `searchY`, `searchOf`, `cfgOf`, `walkCheckY`, `cov_top2`, `cov_top1`, `cov_topY`, `cov_lowA`, `cov_zoneY`, `cov_preY`, `s_stepY`, `LiveY`, `cover_liveY`, `live_stepY`, `frame_of_walkY`, `WalkOK`, `walkOK_of_check`, `frame_end`, `height_frame`, `sizeI`, `heightI`, `hpOf`, `aidsY`, `knownY`, `heightCheck`, `refsCheck`, `Facts`, `factsOf`, `height_of_rows`), `Theorems/Route.lean` (`restIdxY`, `RoomChecks.height`, `Run.height₂`, `Run.y₂`, `entryAt_of_y`, `Run.chgK`), private `Proof/EntryHeight.lean` (`entry_height_walk`, `entry_height_refs`, `height_facts`). There is no game data in the public files. `height_frame` and `height_of_rows` use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## How it works

**Why the height is a row's.** The side pipe's code (`ChkPBtm`) asks the player's state to be standing. The collision routine (`PlayerBGCollision`) first makes a standing state falling. It makes the state standing again at one place only (`InitSteP`). The code comes there after the landing (`LandPlyr`), which first rounds the height down to a row, or when the jumpspring moves, and the room's condition knows that it does not. So on a frame that enters, the height at the side check is a row's.

**The walk.** It is the walk of the room's frame of [The block map in the room](c-7-12-RoomMap.md) (`RoomMap.stepT`), with four more splits. None needs a hypothesis: each covers every machine.

* Where the foot check reads the height: its high bits, in 6 pieces (`0xxxxxxx`, `10xxxxxx`, `1100xxxx`, `1101xxxx`, `1110xxxx`, `1111xxxx`). The foot check compares the height with a value near the screen's bottom, and only for one piece the abstract machine does not know the result. So the pieces at or below that value do not come to the landing.
* After the landing's store of the height: each of its values (13 rows).
* Where the block buffer's address is made, when the height is known: the 5 low bits of the accumulator (the column and the buffer). Then the pointer of the read is known.
* After the block buffer routine saves the tile: each value of the tile.

**The read.** When the pointer and the row are known, the walk takes the machine's own step at the block buffer routine's read (`stepY`): it reads the byte of the block buffers. The room's condition knows the bits of this byte that are 0 in the map. Elsewhere the read gives a tile of the list, as before (`SiteOK`).

**Why only one height.** Only one place of the map has the bits of a side pipe's tile: the mouth's lower tile. The small player's two side reads are at the same row, so only one height reads that place. The walk checks this: every frame end has the routine known not to be the side pipe's, or the height known and equal to `y_e`.

**The search (no part of the proof).** Its key has the height, the player's state and the pointer of the read. Without the state in the key, the states "jumping" and "falling" are joined, and the join also admits "standing". The offset of the collision routine's adders is not forgotten (`aidsY`). After the collision routine the height is forgotten, unless the routine is the side pipe's.

Two things about the search were found on the way. A hash table reads only the low 64 bits of a key, and the low 64 bits of the room's key take few values (the stack and two bytes). A search of 1.8 million steps with such a key took 110 to 206 s. With 64 mixed bits below the key (`mix64`) the search of 1.2 million steps takes 7 s. The other walks of the room have the same key (`ScreenPage.Aids.key`). And the queue of the room's search takes the key modulo 2²⁰⁰ (`SearchS.put`): a longer key makes two states take the same place, and one is lost. This walk has its own queue (`putY`).

**Size.** 1,230,581 steps, 49,455 forks, 0 failures, 199,714 states. In a program: the search 6.8 s, the check about 20 s. `Proof/EntryHeight.lean` built in 34 s with this check alone, and in 69 s with the check of [the screen's buffer](d-2-5-5-EntryBuffer.md) while other builds ran. This is more than a few seconds.

## Measured, not a theorem

The walk with another size at the frame's start (`entry-height-check FM2 N walkall`):

| the size at the frame's start | steps | failures | frame ends with the side pipe's routine | their heights |
|---|---|---|---|---|
| the reference's (small) | 1,230,581 | 0 | 8 | 176 px |
| big | 2,300,695 | 4 | 24 | 176 px and 192 px (8 ends) |
| not known | 2,432,097 | 4 | 24 | 176 px and 192 px (8 ends) |

**Why a big player's height stays.** A big player's upper side read is one row above his lower one. The walk knows the bits that are 0 in the map, not the floor's tiles (1-1-c-7-12). Without the floor, a big player who stands one row lower reads the mouth's lower tile with his upper side read, and enters one row lower (192 px in the table). On the real machine the floor is there: the left side's lower read finds it first, and the frame does not enter (the table below). To prove it one needs the floor's tiles on every frame of the room.

## Checked on real frames

A program (`entry-height-check FM2 400 real`, about 3 min).

| run | frames | entries | the frame starts in `RoomCond(K_T)` | with the reference's size | every instruction `SiteOK` | heights at the entry | `height₂`, `buffer₂` and `entry₂` hold |
|---|---|---|---|---|---|---|---|
| the movie's entering frame (movie frame 763) | 1 | 1 | 1 | 1 | 1 | 176 px | 1 |
| one frame from the movie's entering frame, small; the height (112 to 207 px), the vertical state and the vertical speed overwritten | 1,440 | 55 | | | | 176 px | |
| the same, big | 1,440 | 55 | | | | 176 px | |
| own inputs from frames of the movie in the room, small (400 runs) | 164,375 | 142 | 142 | 142 | 142 | 176 px | 142 |
| the same, big | 161,042 | 151 | 151 | 0 | 151 | 176 px | 151 |

For a big player the left disjunct of `height₂` is false and the right one holds.

## Uses from other parts

* Part c: `RoomMap.cond_of_rows` (the room's condition with the map's bits at each frame's start; its checks `map_facts`, `map_start`), the step `RoomMap.stepT` with `RoomMap.s_stepT`, and through `Run.rt₂` the field `room.enters`, the theorem `Run.roomEnter` and the walks `SideEntryEnd`, `SideEntryRest`.
* Part b: the rows of the first change at the room's first control (`ChangesK.run₁`, `inRowsT`), `ctl₁`, `ctlFirst₁`, `Run.entry₁`.
* No cycle: none of these uses `entry₂`.

## What changed in the route

* `Run.chg : ChangesK … (restIdxB sy nmS m0)` (3 bytes; `restIdxY` is the 8 bytes without the height). `Run.chgK` gives the changes with the 11 bytes from `Run.buf₂`, `Run.y₂`, `Run.area₂`, `Run.rt₂`.
* `Run` has a new field `height₂`.
* `RoomChecks` has a new field `height : EntryHeight.Facts …`, built from `height_facts` in the private files of the route (5 times) and of the hurry-up music (once).

Removed from the assumptions: the height of `entry₂`, for a run whose entering frame starts with a small player. Added: `height₂`, which the old assumption implies.

## Assumptions (not proved in Lean)

* `height₂`: the entering frame starts with a small player, or the height at the entry is the reference entry's.
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

**Files.** `Theorems/EntryHeight.lean`, `Theorems/Route.lean`; the private check is in `Proof/EntryHeight.lean` (`genEntryHeight` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta entry-height-check FM2 10 walk       # the search and the check of both walks, about 40 s
.lake/build/bin/smbrta entry-height-check FM2 10 walkall    # also with a big player and with the size not known, about 2 min
.lake/build/bin/smbrta entry-height-check FM2 400 real      # the table of real frames, about 3 min
```
