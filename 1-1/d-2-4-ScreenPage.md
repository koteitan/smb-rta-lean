[← Back](README.md) | [English](d-2-4-ScreenPage.md) | [Japanese](d-2-4-ScreenPage-ja.md)

# The screen's page in the room, and the long timer of the side pipe

**Claim.** This is a partial result. Suppose the state at the first control in the room meets one condition `Room`, each instruction of each frame from there to the entry meets a condition `SiteOK`, and each frame before the entry starts in the player's routine. Then on every frame up to the entry the screen is on the first page and the scroll lock is on, and at the end of the entry frame the timer has the long value, at least 160. If also 16 bytes at the end of the entry frame have the values of a reference (`EntryRest`), the state there meets the whole condition `Entry2` at the entry of the side pipe ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)). `Entry2` asks for 90 bytes (93 with a record in the screen's buffer), the program counter, the stack pointer and the frame's end in the idle loop. The proof follows one whole frame in the room with the abstract machine. It does not cut the frame into parts. `Room`, `SiteOK`, the condition on the routine and `EntryRest` are assumptions. They were checked on real frames.

`m₀` is the machine at the start of 1-1. `r` is the reference machine, a real run on the frame before the entry (`P` of [The change out of the side pipe](d-1-SideTransition.md)). `frame(m, i)` is one real frame with input `i`. `tr(n)` is the machine `n` instructions into that frame. `page(m)` is `ScreenLeft_PageLoc`, `lock(m)` is `ScrollLock`, `rt(m)` is `GameEngineSubroutine`, `timer(m)` is `ChangeAreaTimer`, `x(m)` is `Player_X_Position`. `e_s` is the number of the side pipe's routine, `long` is the first value of `AreaChangeTimerData`. `L` is 6000 dots before the frame's end.

```
Room(m)     :=  m ended its frame in the idle loop: pc and S as in r, dot ≤ 9,
                vblank and NMI flags fit the dot, sprite-0 flag set, NMI on in the PPU control, no strobe
                ∧  ∀ (b, k) ∈ K,  m[b] & k = r[b] & k

SiteOK(m)   :=  ( pc(m) ≠ idle loop                    →  dot(m) ≤ L )
              ∧ ( the instruction of m is LDA (zp),Y   →  the address read is RAM or ROM )
              ∧ ( pc(m) = the block buffer read        →  the byte read ∈ T )
              ∧ ( same place, adder offset of the head →  the byte read ∈ {0, coin} )
              ∧ ( pc(m) = the write that erases a coin →  the address written is in the block buffers )
              ∧ ( pc(m) ∈ 3 places of the screen buffer →  VRAM_Buffer1_Offset < 64 )
              ∧ ( pc(m) = the pipe code's read of x    →  x(m) & 15 ≠ 0 )

Leaves(m')  :=  page(m') = page(r) ∧ lock(m') = lock(r) ∧ rt(m') ≠ rt(r)
              ∧ ( rt(m') = e_s → timer(m') = long ∧ ∀ (v, X) ∈ V,  RoomCond(v, X ∖ R)(m') )

EntryRest(m) :=  ∃ (v, X) ∈ V,  ∀ b ∈ X ∩ R,  m[b] = v[b]
```

`K` is known bits of 83 bytes, listed below. `T` is the tiles in the block buffers of `r`, and 0. `V` are the two reference machines of `Entry2` with their lists `X` of bytes (`SideChangeEnd.refs2`). `RoomCond(v, Y)` is `Room` with `v` in place of `r` and all the bits of the bytes `Y`. `R` is the list of 16 bytes below (`restIdx`).

```
room_step    :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  Room(frame(m, i)) ∨ Leaves(frame(m, i))
room_run     :  seq(n + 1) = frame(seq(n), inp(n)),  c ≤ e,  Room(seq(c)),
                ∀ n ∈ [c, e),  (∀ j, SiteOK(tr_n(j))) ∧ rt(seq(n)) = rt(r),   rt(seq(e)) = e_s
                →  (∀ n ∈ [c, e), Room(seq(n)))  ∧  timer(seq(e)) = long  ∧  page(seq(e)) = page(r)  ∧  lock(seq(e)) = lock(r)
room_keeps   :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  page(frame(m, i)) = page(m)  ∧  lock(frame(m, i)) = lock(m)
RoomRun.screen :  the same  →  ∀ n ∈ [c, e],  page(seq(n)) = 0  ∧  lock(seq(n)) ≠ 0
RoomRun.timer  :  the same  →  160 ≤ timer(seq(e))
room_leaves  :  the same as room_run  →  (∀ n ∈ [c, e), Room(seq(n)))  ∧  Leaves(seq(e))
entry_rest   :  the same (in place of rt(seq(e)) = e_s, EntryRest(seq(e)))  →  Entry2(seq(e)) with timer ≥ 160
entry_long   :  the same (in place of rt(seq(e)) = e_s, the entry condition with no timer)  →  the entry condition with the timer at least 160
screen_check (private): roomCheck(sy, nm, m₀, 160, V) = true (native_decide)
```

`entry_rest` takes `rt(seq(e)) = e_s` from `EntryRest`, since `GameEngineSubroutine` is in `R`.

Lean: `Theorems/ScreenPage.lean` (`readStep`, `writeStep`, `s_readStep`, `s_writeStep`, `SiteOK`, `preS`, `cov_preS`, `walkS`, `frame_of_walkS`, `RoomCond`, `Leaves`, `room_step`, `room_keeps`, `room_leaves`, `room_run`, `RoomRun`, `RoomRun.screen`, `RoomRun.timer`, `entry_long`, `EntryRest`, `entry_rest`), private `Proof/ScreenPage.lean` (`screen_check`, `screen_first_page`, `screen_long_timer`, `screen_entry`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## The parts of the item

**(1) The entry frame.** It is inside the check of a whole frame. If the abstract state at the frame's end has `rt = e_s`, the check fails unless `timer` is known to be `long` in it. In the pipe's code `page` is known to be 0, so there is one branch that writes the timer.

**(2) One frame keeps it.** The list `K` has all the bits of the page and the lock. In both cases of `room_step` their values do not change (`room_keeps`). With a reference that has the lock off, or the page at 1, the check does not pass (see below).

**(3) The start.** It stays a condition on one state, `Room(seq(c))`. In the route it comes from the rows of the change into the room, but for 5 bytes ([The condition `Room` at the first control in the room](d-2-4-1-ScreenStart.md)).

**(4) The condition at the entry.** If the abstract state at the frame's end has `rt = e_s`, the check also asks that it lies under a start state of each reference `(v, X ∖ R)`. That is, it knows the program counter, the stack pointer, the dot and the flags, and every byte of `X ∖ R` with the value of `v`. Then `Entry2` needs only the bytes of `R` (`entry_rest`).

The walk ends the entry frame in 2 abstract states (dot 0, and dots 1 to 9). In both, the walk knows 78 of the 90 bytes of `Entry2` as the reference does, and 78 of 93 with the record (measured by `screen-check`). The 12 (15) that it does not know, and `GameEngineSubroutine`, are `R`. Before this round it knew 76: the two bytes of the player below were not known. With the 79 bytes of `K` of an earlier round, 17 (20) were not known; with the 73 bytes of the round before, 23.

| Bytes of `R` | Why the walk does not know them |
|---|---|
| `GameEngineSubroutine` | the walk knows it; it is in `R` because it says that the entry happened at `seq(e)` |
| `Player_Y_Position` | the player's height. It changes in the room. The tile read does not depend on the place in the walk, so the walk cannot tell the row of the pipe |
| `VRAM_Buffer1_Offset`, `VRAM_Buffer1` (+0, +1, +2, +7) | the screen's buffer. The walk only splits the offset below 64 |
| `AreaMusicBuffer`, `EventMusicBuffer`, `MusicData` (2), `MusicOffset_Square1`, `NoiseSoundBuffer`, `EventMusicQueue`, `NoteLengthTblAdder` | the sound. `K` does not follow the sound engine. The hurry-up music changes these bytes |
| `AreaNumber` | the level's number. The rows of the change into the room do not know it at control: the condition at the vertical pipe's entry does not have it |

With one of these bytes added to `K` (measured in an earlier round, when `Player_State` and `Player_Y_HighPos` were still in `R`), the walk fails: `Player_Y_HighPos` 1 failure, `VRAM_Buffer1_Offset` 3, `EventMusicBuffer` 1, `MusicOffset_Square1` 1, `NoiseSoundBuffer` 1, `VRAM_Buffer1` 2. For the last group and `MusicData`, `EventMusicQueue`, `Player_Y_Position`, `Player_State`, `AreaMusicBuffer`, the rows of the change into the room do not know the reference's value at control (of 4 states with control: 0, 2 or none). Six bytes passed both tests and are now in `K`: `ScreenRoutineTask`, `DisableScreenFlag`, `Fireball_State` (2), `JoypadOverride`, `GameTimerExpiredFlag`. The rows know them at control, and the check of [The condition `Room`](d-2-4-1-ScreenStart.md) still passes with them.

Last round three more bytes went into `K`: `AreaPointer`, `EntrancePage`, `PrimaryHardMode`, the next area and the hard mode. The rows of the time of the change into the room know them at control with the reference's values (both states with control). With them in `K` the walk has 0 failures and the same table, and the check of [The condition `Room`](d-2-4-1-ScreenStart.md) passes. So `EntryRest` no longer asks them. `AreaNumber` too passes the walk, but the rows do not know it. No other part of the route follows `AreaNumber` either: the condition at the vertical pipe's entry, the whole-frame keep of part a, and the rows of the change into the room do not have it. It is 0 from the start of the game, and no code of these frames writes it; this is not proved. On real runs in the room (113 runs, 36 entries; measured with a temporary program, not kept), these four bytes and `Player_Y_HighPos` and the sound bytes of `R` never change; with the sound bytes in `K` the walk passes, but at the end of the entry frame it does not know them, because the search joins states where they differ.

Item 1-1-c-7-5-13 put one more byte into `K`: `DisableCollisionDet`, the flag that turns off the player's collision checks. The change into the room clears it, and no step of the room writes it. The rows of the change know it at control with the reference's value, the walk keeps it, and the checks pass as before. The landing of the first fall takes it from the walk ([The collision-disable flag and the vertical page in the first fall](c-7-5-13-LandBytes.md)).

**This round: the player's state and his height on the screen.** `K` knows only the high bits of `Player_State` and nothing of `Player_Y_HighPos`, because both change in the room. But on the path into the pipe the code tests them.

* The side pipe's code tests the state with `LDY`, `CPY #0`, `BNE`. The machine of `TaintRun` reads a byte in pieces only for `LDA`, so a branch on `Y` did not tell the walk the byte. Now the walk splits the two low bits of the state at this `LDY` (`preS`, `Places.stAt`). On the path into the pipe the state is 0.
* The collision routine tests the high byte with `LDA`, `CMP #1`, `BNE`, and leaves if it is not 1. The pipe's code is inside the collision routine. Now the walk splits all the bits of the high byte at this `LDA` (`Places.hpAt`). Only the piece with the value 1 goes on into the collision code. The search keeps the pieces apart at the `CMP` by the accumulator (`Aids.aAt`); else it joins them again at once.

A split is safe: each machine lies under one of the pieces (`cov_preS`, from `TaintRun.cov_bit` and `PipeEntryRule.cov_all`). Nothing new is assumed. At the end of the entry frame the walk now knows the state 0 and the high byte 1, as the references have them. So `EntryRest` no longer asks for these two bytes: `R` has 16 bytes, before 18. The search has 208,238 steps (before 210,934) and the table 9,276 states (before 9,378). The walk of [the block map in the room](c-7-12-RoomMap.md) (part c) uses the same pieces; its check still passes (`room-map-check`: `mapCheck` true, the same table).

## How it works

**The abstract machine.** The machine of [A run with unknown bytes](b-2-3-TaintRun.md), with no change. Three ways of walking are added on top of it. Each is proved for one instruction against the real `step`.

* `LDA (zp),Y` with a pointer not known (`readStep`, `s_readStep`). If the address read is RAM or ROM, nothing else in the machine changes. The value read is taken as not known. At the block buffer read, the value is split into each value of `T`.
* `STA (zp),Y` that erases a coin (`writeStep`, `s_writeStep`). The block buffers have no known bit, so the abstract state does not change wherever it writes.
* Splitting (`preS`). `dot ≤ L` cuts the time window. The index of the screen buffer is split into the values below 64. `x` is split into the four cases of a set low bit. The player's state is split by its two low bits where the side pipe's code reads it, and his high byte by all its bits where the collision routine reads it. The last two need no condition.

**The table.** A search makes a table of abstract states. The check walks from each state of the table and checks that each path ends in a state of the table, or at the frame's end in `Room` or `Leaves` (`walkS`, `finR`). What the search forgets, the check confirms with `AS.le`. So the search is no part of the proof.

**Size.** The search has 208,238 steps, 8,862 forks, 0 failures, a table of 9,276. The whole check takes about 5 s in a program.

**Why one frame closes.** An earlier measure ([Entering the pipe on real frames](a-5-1-PipeEntryRule.md)) had 179 failures with only the pad not known. The sites were reads through pointers, the jump table and time. Here four things close it.

* The rule that allows a read through a pointer not known. Its condition is only that it does not read a register.
* Splitting the value of a tile. The paths to the flagpole, a vine, the axe and a spring go away.
* The head reads only 0 or a coin. The path that hits a brick goes away.
* The list `K`, which has the objects' bytes.

**The instructions that write the page and the lock** (counted from the disassembly). The 338 zero page indexed writes do not reach them.

| Kind | Page | Lock | Instructions the walk goes through |
|---|---|---|---|
| direct | 3 | 5 | page: none. Lock: one, in `PlayerHole`. It writes 1, so the value does not change |
| indexed absolute (of 439, those that can reach) | 31 | 31 | 6 (sprite offsets 4, joypad 2). Their indexes are known and do not reach |
| through a pointer | 9 | 9 | 1 (erasing a coin), in the block buffers |

The walk goes through 2,668 instructions. It does not go through `ScrollScreen`, `StartPage`, `ExecGameLoopback`, `ScrollLockObject`, `PlayerEndLevel`, `WarpZoneObject`, `FlagpoleCollision`.

## What happens without each condition (measured)

Programs, not theorems. These were measured before this round, with the 73 bytes of `K` and the old end of the frame.

| Condition taken away | Steps | Failures | First failure, result |
|---|---|---|---|
| none | 211,005 | 0 | |
| `dot ≤ L` | 12,248 | 296 | `OutputToVRAM`: time reaches the frame's end |
| the head reads 0 or a coin | 214,032 | 4 | `DBlockSte`: the path that hits a brick |
| the tile read (any byte) | stopped at 400,000 | 116 or more | `DBlockSte` |
| `VRAM_Buffer1_Offset < 64` | 114,966 | 18 | `SetupNums`: a write with an index not known |
| `x & 15 ≠ 0` | 210,820 | 0 | at the frame's end `timer` is not known |

With the reference machine overwritten. Lock off: 1,204,601 steps, 4552 failures, and the frames' ends are not accepted. Page 1: 211,021 steps, 0 failures, but the timer at the end of the entry frame is not `long`, so the ends are not accepted. So the check does not pass on an empty case.

## Checked on real frames

A program (`screen-check`). On runs not overwritten, no part of `SiteOK` fails. On the run written right of the pipe, the head's read reads a tile of the pipe, so some instructions do not meet the head's condition. The theorem does not apply to those frames; the page and the lock still do not change. `Room` holds on all first states. "Other histories" are runs with random inputs on the pipe and then Down, and runs with the lives, coins, score, game timer and random bytes overwritten at the start of 1-1.

| Run | Frames | Paused | Entries | Short timer | Entries with `EntryRest` | Of them with `Entry2` | First states in `Room` | Frames with `SiteOK` that end in neither `Room` nor `Leaves` | Instructions not `SiteOK` |
|---|---|---|---|---|---|---|---|---|---|
| the TAS in the room | 111 | 0 | 1 | 0 | 1 | 1 | 1 / 1 | 0 | 0 |
| 13 real entries, 17 other histories, the TAS's first state, with random inputs and runs to the right | 130,030 | 28,315 | 20 | 0 | 20 | 20 | 31 / 31 | 0 | 0 |
| the same, written big at the first state | 15,975 | 3,757 | 5 | 0 | 5 | 5 | 4 / 4 | 0 | 0 |
| the game timer written near 100 at the first state, no input | 900 | 0 | 0 | 0 | | | 3 / 3 | 0 | 0 |
| written right of the pipe, Right and B, pauses | 4,800 | 2,328 | 0 | 0 | | | 12 / 12 | 0 | 192 |

`Room` here has the 83 bytes of `K`. `Entry2` is with the timer at least 160.

* Every entry frame ends with the timer at `long`.
* Every real entry meets `EntryRest`, and `Entry2` as `entry_rest` says.
* On every run, the first frame that leaves the player's routine enters the side pipe: no frame ends with another routine (injury, death). So `a₂` of the route is the entry on these runs.
* Every frame ends in `Room` or `Leaves`.
* The last instruction of the slowest handler is at dot 43,009; `L` is 83,342.
* He does not run right past the screen. While the scroll lock is on, `ChkPOffscr` puts him back on the screen. Written right of the pipe, holding Right and B, he reaches at most pixel 240, and his page stays 0.

## Round 26: what the room's walk knows of each part of `SiteOK` (measured)

Item 1-1-d-2-4-2. The question: which parts of `SiteOK` could a walk of the room's frames prove from the rows at the room's first control, as the walks of the control and of the coin frames do. The most precise walk of the room is that of [BufferEnd](d-2-5-5-3-BufferEnd.md) (the room's condition, the control of the screen's buffers at 0 or 6, the position's pieces, and since round 26 the page, [BufferPage](d-2-5-5-4-BufferPage.md)). `buffer-ctl-check FM2 4000 sites26` takes every state of its table and follows the walk's steps up to a covered state or the frame's end, and at each state asks whether the state alone already gives the part (no part of the proof).

| part | what it asks | from the control 0: known / not known | from the control 6: known / not known | places where not known |
|---|---|---|---|---|
| `reads` | an `LDA (zp),Y` reads RAM or ROM (pointer's high byte at most 0x1E or at least 0x80) | 15,007 / 294 | 15,009 / 308 | the screen update's reads of the buffer (4 places), the music routine (5 places) |
| `off` | the screen buffer's offset below 64 where it is an index | 119 / 0 | 1,703 / 242 | the three places that write into the buffer |
| `xbit` | the position's low bits not 0 at the side pipe's read | 12 / 64 | 12 / 64 | the side pipe's read |
| `read` | the block buffer routine reads a tile of the list (place in the block buffers) | 13,202 / 1,204 | 13,202 / 1,204 | the routine's read |
| `erase` | the coin is erased in the block buffers | 0 / 310 | 0 / 310 | the erase |
| `late` | the handler is done before dot `L` | 50,543 / 1,603,443 | 73,948 / 2,003,652 | almost everywhere |

What this says:

* `off` is known on every frame that starts with the control at 0. A frame that starts with 6 draws the second buffer, and the first buffer's offset is not reset; the room's condition does not know it. So `off` would need the offset in the room's condition, kept from frame to frame (as `BufferControl` keeps the control), and a version of the walk's theorems that proves `off` instruction by instruction instead of assuming it.
* `reads` is known at all but about 2% of the reads. The rest go through pointers that the walk does not know: the screen update's pointer into the buffer after its loop, and the music data's pointer.
* `xbit`, `read`, `erase` need the position (and the height) at the instruction, which a walk from the room's condition does not know: they need bounds over several frames (the walls, the floor).
* `late`: the walk's own bound on the dot is above `L` at most states; it is the clamp by `SiteOK.late` that keeps it. A proof needs the time of each path of the handler.

So no part can be split off by the walks as they are. Every theorem that uses the room's walks takes `SiteOK` on every instruction as one hypothesis, and so does `RoomMap.cond_of_rows`, which gives the room's condition; a proved part needs the walks' theorems in a form with the parts apart. `chg.roomSites` stays as it is.

**Round 27.** The parts are now conditions of their own, and two of them are proved on most instructions by a walk that checks them at every state ([The parts of `SiteOK`](d-2-4-2-1-SiteParts.md), item 1-1-d-2-4-2-1): `off` on every frame that starts with the control at 0, and `reads` through every pointer but the screen update's. The field `chg.roomSites` is gone; the route asks the other parts as six fields.

**Round 28.** `reads` through the screen update's pointer is proved on every frame of the room but the first one and those after a frame that starts with the control at 6 ([The screen buffers' records](d-2-4-2-2-BufferRecords.md), item 1-1-d-2-4-2-2): a frame from the control at 0 leaves records in the buffer that the walk knows, and the next frame's screen update reads them. `off` is proved also on the frames that start with the control at 6 after a frame at 0: the walk knows the offset that the frame before left.

**Round 29.** `late` is proved on every frame of the room but the first one and those after a frame that starts with the control at 6, if each instruction of the sound routine's code runs at dot 9,000 or earlier ([The time of the room's frames](d-2-4-2-3-RoomLate.md), item 1-1-d-2-4-2-3): the walks from the buffers' patterns check the time at every state and clamp it only in the sound routine's code. Without a clamp the walk's time grows for ever only in the sound routine (it does not know the music's offsets), and in the wait for the sprite-0 flag, where the search forgot A after the read of the picture's status (`ScreenPage.jsrRets` takes the byte `0x20` of the status's address as a call; `RoomLate.fixCuts`).

**Round 30.** `late` is proved on every frame of the room, if the loops' back jumps whose counts the walk does not know run at dot 9,000 or earlier: those of the screen update's loop over the records and of the sound routine on the room's first frame and the frames after a frame from the control at 6, those of the sound routine on the other frames ([The time from the loops' back jumps](d-2-4-2-4-LoopTime.md), item 1-1-d-2-4-2-4). Every loop has an instruction that jumps back, so the walks clamp the time only there. `erase` is narrowed: the walks know the pointer's page at the erase, so it writes in the RAM at or past the block buffers' start; the field asks only that it writes before their end. `read`, `xbit` and that end stay fields: at those places the walk knows neither the player's position nor the row's offset (its `ADC` gives a result only when every bit of both values is known), and not the block buffers.

**Round 31.** `erase` is narrowed again: the walks split the state before the add of the pointer's low byte, so they know which of the two block buffers the pointer is in, and an erase through a pointer into the first block buffer is below the block buffers' end for every row's offset. The field asks the end only of an erase whose pointer is at or past the second block buffer's start ([The coin's erase in the first block buffer](d-2-4-2-5-EraseSplit.md), item 1-1-d-2-4-2-5). `read`, `xbit` and that case stay fields.

**Round 32.** `erase` is proved on every instruction of the room's frames: the walks split the player's height in the collision routine, the size's bit 0 and the crouch byte, and start each frame knowing bits 1 to 7 of the size, so they know the row's offset at every erase ([The row of the coin's erase](d-2-4-2-6-EraseRow.md), item 1-1-d-2-4-2-6). `read` and `xbit` stay fields.

## Assumptions (not proved in Lean)

* **`EntryRest(seq(e))`.** The 16 bytes of `R` at the end of the entry frame have the values of a reference of `Entry2` (see (4)). The hurry-up music breaks it ([The runs with the hurry-up music](0-6-4-HurryMusic.md)). Item 1-1-d-2-5. The route now asks 11 of them: five music bytes follow from the room's frames ([The music bytes through the room's frames](d-2-5-1-RoomMusic.md)).
* **`Room(seq(c))`.** 83 bytes at the first control in the room. In the route it is proved from the rows of the time of the first change ([The condition `Room` at the first control in the room](d-2-4-1-ScreenStart.md)). The rest of this item is as written for this page, with 73 bytes. `K` keeps only bytes that do not differ between runs. It fails for a fire Mario (`PlayerStatus` 2); before this pipe in 1-1 there is one power-up. It should come from walking the rows of the change into the room, since the state after that change is nearly all known. If the last row of item 1-1-b-3-2 knows the values of `K`, one check with `AS.le` is enough. The bytes of `K` that the area's setup does not clear are `AreaType`, `CurrentPlayer`, `PlayerStatus`, `WorldNumber`, `OperMode`, `OperMode_Task`, `AreaMusicBuffer_Alt`. The exit condition of those rows has to know them. This page does not depend on those rows, and they were not run here.
* **The time in `SiteOK`.** The frames in the room do not overrun.
* **The address of a read.** `LDA (zp),Y` does not read a register. Measured (temporary program, not kept): with the rule of [the last frames of the change](d-2-3-SideChangeEnd.md) (the high byte of the pointer known to be at most `0x1E` or at least `0x80`) in place of this condition, the room's walk fails at the screen update's first read, `LDA ($00),Y`: the NMI loads the pointer from a table at the index `VRAM_Buffer_AddrCtrl`, which `Room` does not know (taking a coin changes it). So the walk would need that byte's bits in `Room` and a split of its read. Also [the block map in the room](c-7-12-RoomMap.md) uses this part of `SiteOK` for every `LDA (zp),Y`, also through a known pointer, so this part cannot be taken out of `chg.roomSites` without changing what that page's theorems are given. Item 1-1-d-2-4-2.
* **Tiles.** A block buffer read gives a value of `T`. This comes from the address being in the block buffers, and the block buffers of the room being as at the start or with coins erased. Not proved.
* **The head.** A read for the head gives 0 or a coin. This comes from the head not reaching a brick in the room. On real frames the jump is too low (measured: the least `y` of a big Mario is 45, and his head is below the top row).
* **The address that erases a coin, the buffer's index.** Both hold on real frames. The index was at most 55.
* **`x & 15 ≠ 0`.** This is that `z` of [The change out of the side pipe](d-1-SideTransition.md) is not reached. Without it the change takes 378 frames, which is the long side, but `Entry2` asks for `timer ≥ 160`.
* **Starting in the player's routine up to the entry.** Time-up can leave this routine (the check has ends with the routines of injury, death and losing a life). Such a run uses far more than 1748 frames. In the route this is no longer an assumption: `a₂` is defined as the first machine from `b₁` on that has left the player's routine, and the routine byte of `EntryRest` says that this routine is the side pipe's.
* Frames are the emulator's frames.

## Use in the [route](0-1-Route.md)

`chg.entry₂` asks 11 of the 16 bytes of `EntryRest` (`RoomMusic.EntryRestM`); five music bytes come from the room's frames ([The music bytes through the room's frames](d-2-5-1-RoomMusic.md), `ChangesK.entryRest₂`). The room gives the rest of `Entry2` and the timer (`entry_rest`, private `screen_entry`). `Changes.run₂` uses `entry_rest`. The checks on the ROM are `Route.RoomChecks` (`facts` is `RoomFacts` with `V`; `rt` is `entryEnvOK`: the references know the routine and it is `e_s`, the routine is in `R`, and `Entry2` has the room's ROM).

```
a₂         := first(n ≥ b₁, n ≤ b₁ + dR : rt(seq n) ≠ rt(r))     (Changes.a₂; b₁ + dR if none)
entry₂     : EntryRestM(seq a₂)                      (11 bytes; EntryRest(seq a₂) is ChangesK.entryRest₂)
Room(seq b₁)                                           (Changes.roomAt: the rows of the time of the first change, chg.time₁, Changes.ctlFirst₁)
roomSites  : ∀ n ∈ [b₁, a₂),  ∀ j,  SiteOK(tr_n(j))          (Run.roomSites; from round 27 a theorem from six fields: SiteParts)
roomOrder  : b₁ ≤ a₂                                   (theorem, from the definition of a₂)
roomStay   : ∀ n ∈ [b₁, a₂),  rt(seq n) = rt(r)        (theorem, from the definition of a₂)
```

**The list `K`** (names):

`GameEngineSubroutine`, `Enemy_Flag` (6), `Enemy_ID+5`, `Player_State` (bits 0xfc), `Block_State` (2), `Misc_State` (9), `EnemyData`, `EnemyDataHigh`, `AreaMusicBuffer` (bits 0xfb), `AreaMusicQueue`, `FloateyNum_Timer` (6), `VineFlagOffset`, `Block_RepFlag` (2), `Cannon_PageLoc` (6), `Cannon_X_Position` (6), `Cannon_Y_Position` (4), `EnemyFrenzyBuffer`, `SecondaryHardMode`, `EnemyFrenzyQueue`, `SprDataOffset`, `SwimmingFlag`, `JumpspringAnimCtrl`, `FireballThrowingTimer`, `ScreenLeft_PageLoc`, `ScreenRight_PageLoc`, `ScreenRight_X_Pos`, `AreaParserTaskNum`, `ScrollLock`, `EnemyDataOffset`, `EnemyObjectPageLoc`, `ScrollThirtyTwo`, `CloudTypeOverride`, `AreaType`, `CurrentPlayer`, `PlayerStatus` (bits 0xfe), `WorldNumber`, `OperMode`, `OperMode_Task`, `StarInvincibleTimer`, `AreaMusicBuffer_Alt` (bits 0xfb), `ScreenRoutineTask`, `DisableScreenFlag`, `Fireball_State` (2), `JoypadOverride`, `GameTimerExpiredFlag`, `AreaPointer`, `EntrancePage`, `PrimaryHardMode`, `DisableCollisionDet`

**The list `R`** (names): `GameEngineSubroutine`, `Player_Y_Position`, `VRAM_Buffer1_Offset`, `VRAM_Buffer1` (+0, +1, +2, +7), `AreaMusicBuffer`, `EventMusicBuffer`, `MusicData` (2), `MusicOffset_Square1`, `NoiseSoundBuffer`, `EventMusicQueue`, `NoteLengthTblAdder`, `AreaNumber`

**Files.** `Theorems/ScreenPage.lean`, private `Proof/ScreenPage.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta screen-check FM2    # the check, the bytes the walk does not know at the entry, the conditions on real frames, about 2 min
```
