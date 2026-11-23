[← Back](README.md) | [English](d-2-4-2-1-SiteParts.md) | [Japanese](d-2-4-2-1-SiteParts-ja.md)

# The parts of `SiteOK`: the buffer's offset and the reads through a pointer in the room

**Claim.** `SiteOK`, the condition that the route asked on every instruction of every frame of the room (`chg.roomSites`), is split into its six parts. Two of them are now proved on most instructions:

* `Off` (the first screen buffer's offset is below 64 where the code uses it as an index) on every frame that starts with the control of the screen's buffers at 0.
* `Reads` (an `LDA (zp),Y` reads RAM or ROM) at every such read whose pointer is not the screen update's pointer into the buffer.

This is proved, with one check on the ROM (two walks of the room's frame; about 65 s natively). The route now asks `Off` only on the frames that start with the control at 6, and `Reads` only through that one pointer. The other four parts are asked as before, as fields of their own.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `c(m)` is the control of the screen's buffers, `off(m)` the first buffer's offset. `L` is the room's last dot (`late`). `InCls(T, m)` says that the music bytes of `m` are in a state of the table `T` of [the music bytes through the room's frames](d-2-5-1-RoomMusic.md).

## The statement

```
Late(m)       :=  pc(m) ≠ idle  →  dot(m) ≤ L
Reads(m)      :=  pc(m) ≥ 0x8000  ∧  op(m) = LDA (zp),Y  →  addr(m) < 0x2000  ∨  addr(m) ≥ 0x8000
ReadsAt(Z, m) :=  the same, only when the zero page operand of the instruction is in Z
Read(m)       :=  pc(m) = read  →  val(m) ∈ T_tiles  ∧  (save(m) ∈ heads → val(m) ∈ T_head)
Erase(m)      :=  pc(m) = erase  →  the address is in the block buffers
Off(m)        :=  pc(m) ∈ offAt  →  off(m) < 64
Xbit(m)       :=  pc(m) = xAt  →  x(m) & 15 ≠ 0

SiteOK(m)  ⟺  Late(m) ∧ Reads(m) ∧ Read(m) ∧ Erase(m) ∧ Off(m) ∧ Xbit(m)                  (siteOK_of)
Rest(Z, m) :=  Late(m) ∧ ReadsAt(Z, m) ∧ Read(m) ∧ Erase(m) ∧ Xbit(m)
Z₁         :=  ptrS = { the pointer of the screen update's first read }

music_frame0  :  musicCheck(T),   RoomCond(r, K_M, m),   InCls(T, m),   c(m) = 0,   ∀ j, Rest(Z₁, tr(j))                →   ∀ j, SiteOK(tr(j))
music_frame6  :  musicCheck(T),   RoomCond(r, K_M, m),   InCls(T, m),   c(m) = 6,   ∀ j, Rest(Z₁, tr(j)) ∧ Off(tr(j))     →   ∀ j, SiteOK(tr(j))
music_sites_of_rows :
      the conditions of RoomMap.map_of_rows on [b, a),   keepCheck,   startCheckC,   RoomMusic.Facts(T),   musicCheck(T),   Room(seq b),
      ∀ n ∈ [b, a), ∀ j, Rest(Z₁, tr_n(j)),     ∀ n ∈ [b, a),  c(seq n) = 6  →  ∀ j, Off(tr_n(j))
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))

Run.roomSites :  ∀ n ∈ [b₁, a₂),  ∀ j,  SiteOK(tr_n(j))                       (theorem; it was the field chg.roomSites)
```

`K_M` is the room's condition of `RoomMusic` (`knownM`). The new fields of `chg` (each for every `n ∈ [b₁, a₂)` and every `j`):

```
roomLate  : Late(tr_n(j))          roomReads : ReadsAt(Z₁, tr_n(j))          roomRead : Read(tr_n(j))
roomErase : Erase(tr_n(j))         roomXbit  : Xbit(tr_n(j))                 roomOff₆ : c(seq n) = 6  →  Off(tr_n(j))
```

(Round 27's forms. Round 28 narrowed `roomReads` to the room's first frame and the frames after a frame from the control at 6, and `roomOff₆` to a frame from 6 after a frame from 6: [The screen buffers' records](d-2-4-2-2-BufferRecords.md). Round 34 narrowed `roomRead` to the head's half of `Read`: [The block buffers' tiles at the read](d-2-4-2-8-ReadTiles.md), and `roomXbit` to the entering frame: [The side pipe's read of the position, only on the entering frame](d-2-4-2-9-SideRead.md).)

Lean: `Theorems/SiteParts.lean`:

* the parts, `Rest`, `ReadsAt`, `ptrS`;
* the checks at a state: `offOK`, `off_of_ok`, `hiOK`, `readsOK`, `reads_of_ok`;
* the walk of `RoomMusic` with a check at every state: `walkPC`, `frame_of_walkPC`, `cfgPC`, `walkCheckPC`, `music_frame`;
* on the ROM: `musicCheck`, `music_frame0`, `music_frame6`, `cond_at`, `music_sites_of_rows`;
* a first version on the walk of `BufferControl` (`walkC`, `frame_of_walkC`, `siteCheck`, `sites_of_rows`): it proves the same but the reads through the music's pointer; the route does not use it.

`Theorems/Route.lean`: the six fields, `ChangesBase.roomRest`, `ChangesK.roomSites`, `Run.roomSites`, `lateL_of`. `Theorems/BufferEnd.lean`: `FactsE.music`. The private check was `buffer_music_check` in `Proof/SiteMusic.lean` (round 27); since round 28 that file holds `buffer_records_check` of [The screen buffers' records](d-2-4-2-2-BufferRecords.md) in its place. There is no game data in the public files: the pointer is read from the ROM at a symbol.

## How it works

**A walk that checks a condition at every state.** The walk is that of [the music bytes through the room's frames](d-2-5-1-RoomMusic.md) (`RoomPause.pstep`): the room's frame by the abstract machine; at the call of the sound routine the state is split by the states of the music's table, so the sound routine runs with the music bytes known. Here its condition also knows the control of the screen's buffers (0 or 6), and its search keeps states with different offsets of the first buffer apart. `walkPC` is this walk with one more check `chk` at every state it reaches, and at the frame's end. If a state `A` covers a machine `m`, and `chk(A)` holds, and `m` meets the rest, then `m` meets `SiteOK`. The frame theorem (`frame_of_walkPC`) goes instruction by instruction: the state at instruction `j` comes from `SiteOK` at the instructions before `j` only; the check at that state gives the missing parts at `j`. So the frame needs only the rest on each instruction, and it gives all six. The walk asks nothing more at the frame's end (`cfgPC`): the frame theorem gives only `SiteOK`, and the condition at the next frame's start comes from the walks that the route already has.

**The offset.** The screen update at the start of a frame that starts with the control at 0 writes 0 to the first buffer's offset. Then the code of the frame (the palette of the player, the colour rotation, the digits of the score, the coins and the timer) adds known lengths to it. The walk from the control at 0 knows the offset below 64 at every state where the code uses it as an index (`offOK`: its largest value with the known bits is below 64).

**The reads.** At every `LDA (zp),Y` the check asks that the state knows the pointer's high byte at most `0x1E` or at least `0x80` (`SideChangeEnd.ptrHiOK`). Then every address `pointer + Y` is in the RAM or the ROM (`SideChangeEnd.wide_ok`, `RoomBlocks.readAddr_eq`). The music's pointer is one of the music bytes, so the walk knows it at each of its reads. The walk does not know the screen update's pointer at 7 states (from the control at 0) and 11 (from 6): it moves through the buffer by the lengths of its records, which the walk does not know. So the check does not ask the reads through this pointer (`readsOK`), and the route asks `Reads` there (`ReadsAt(Z₁, ·)`).

**The frames in order.** `music_sites_of_rows` takes the room's frames one after another. At frame `n` these need `SiteOK` only on the frames before `n`: the room's condition with the bits of the map (`RoomMap.cond_of_rows` up to frame `n − 1` and one step of `RoomMap.room_stepT`), the control at 0 or 6 (`BufferControl.ctl_of_rows`), and the condition of `RoomMusic` with the music bytes in a state of the table (carried from frame to frame by `RoomPause.pause_step`; at the room's first control from the rows of the first change, `RoomMusic.start_of_invL`). A frame that starts at 0 gets all six parts from `music_frame0`, one that starts at 6 from `music_frame6` with the field `roomOff₆`.

**Size.** The walk from the control at 0: a table of 78,693 states; from 6: 216,532. The check of both walks: about 65 s natively, more than a few seconds. The private `Proof.SiteMusic`: 67 s in a full `prove.py` with other jobs running.

**The first version.** On the walk of [BufferControl](d-2-5-5-1-BufferControl.md) (the room's walk with the control known, without the music bytes) the same checks pass (`siteCheck`, 9.6 s natively) but for the reads through the music's pointer: that walk does not know the pointer's high byte at 187 states (from 0) and 197 (from 6), at 4 places of the screen update and 5 of the music routine.

## Why `Off` stays on the frames that start with the control at 6

A frame that erases a coin sets the control to 6. The next frame's screen update draws the second buffer, and does not reset the first buffer's offset. So the offset at the start of that frame is the one that the coin frame left. A coin frame adds 14 bytes to the first buffer (the coins' two digits and the score's six digits, each with a header of 3 bytes), and the timer's digits and the colours add more. Coin frames can follow each other (a frame erases one coin, and the player can touch several coins at once). So a bound needs the number of coins in a row, which this walk does not know. Measured: from the control at 6, with the offset not known at the start, the walk does not know the offset below 64 at 92 states.

## Measured, not a theorem

`buffer-ctl-check FM2 100 sites` (exit 0): own runs in the room from frames of the movie, small and big, 100 each.

| player | runs | frames | frames that start with the control at 6 | the first buffer's offset at their start, at most | at its uses on them, at most | reads through the screen update's or the music's pointer | instructions that fail a part of `SiteOK` |
|---|---|---|---|---|---|---|---|
| small | 100 | 42,438 | 316 | 42 | 41 | 105,632 | 0 |
| big | 100 | 42,452 | 403 | 55 | 46 | 107,760 | 0 |

Every read through these two pointers reads the RAM (the screen's buffer) or the ROM (the music's data). On these runs the offset at the start of a frame from the control at 6 reaches 55. A coin on such a frame would add 14 bytes and pass 64. So a bound on the offset at the start of such a frame, with this walk, cannot give `Off`: the walk would also need to know that no coin is taken on that frame, that is, the position.

## Uses from other parts

* Part c: `RoomMap.cond_of_rows`, `RoomMap.start_of_rows`, `RoomMap.room_stepT`, `MapFacts`, `startCheckT`; `RoomBlocks.readAddr_eq`, `ptrZ`, `operand`; `ChangesBase.roomStay`, `ChangesK.roomAt`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`; `SideChangeEnd.ptrHiOK`, `ptrWide`, `wide_ok`.
* Part a: `Run.entry₁`.
* Part d: `BufferControl` (`keepCheck`, `startCheckC`, `ctl_of_rows`, `cond0`, `cond6`, `ref6`), `RoomMusic` (`Facts`, `regM`, `knownM`, `start_of_invL`, `roomCond_append`), `RoomPause` (`pstep`, `s_pstep`, `pause_step`, `cfgOfP`, `InCls`, `Ph`), `StepWrites` (`tabOK`, `le_pc_spent`), `EntryBuffer`, `EntryHeight` (the first version).
* No cycle: none of these uses `roomSites` or `Run.roomSites`; `ChangesK.roomSites` uses only the fields `roomLate`, `roomReads`, `roomRead`, `roomErase`, `roomXbit`, `roomOff₆`, `ctl₁`, `ctlFirst₁`, the rows of the first change and the checks.

## What changed in the route

* Field removed: `chg.roomSites` (`∀ n ∈ [b₁, a₂), ∀ j, SiteOK(tr_n(j))`).
* Fields added: `roomLate`, `roomReads` (only through the screen update's pointer), `roomRead`, `roomErase`, `roomXbit`, `roomOff₆` (only on the frames that start with the control at 6).
* `Run.roomSites hR hB hK R` gives the old field's statement. The theorems of the room that used `chg.roomSites` take the room's checks `hR` now (`Run.roomBump`, `roomArrive`, `roomBefore`, `roomStR`, `roomReach`, `roomCut`, `roomVert`, `roomAir`, `roomHigh`, `roomLand`, `roomWall`, `roomHighJ`, `roomHighA`, `roomCorner`, `roomStand`, `roomFloor`, `roomJump`, `roomBlocks`, `roomPair`, `roomV0`, `roomKeepA`, `roomKeep`, `roomBlocksTrace`, `roomCollisionMap`, `roomFootMap`). `Run.roomTime` uses `roomLate`.
* `RoomChecks.buffer` (`BufferEnd.FactsE`) has the new field `music`: the facts of `RoomMusic` with a table and `musicCheck` with the same table.

## Assumptions (not proved in Lean)

* `Late`, `Read`, `Erase`, `Xbit` on each instruction of the room's frames, as before (item 1-1-d-2-4-2). Round 26 measured what the walks know of them ([The screen's page in the room](d-2-4-ScreenPage.md)): they need the dot's bound on each path, and the position and the height over several frames.
* `Reads` through the screen update's pointer into the buffer.
* `Off` on the frames that start with the control at 6.
