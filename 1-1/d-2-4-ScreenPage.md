[← Back](README.md) | [English](d-2-4-ScreenPage.md) | [Japanese](d-2-4-ScreenPage-ja.md)

# The screen's page in the room, and the long timer of the side pipe

**Claim.** This is a partial result. Suppose the state at the first control in the room meets one condition `Room`, each instruction of each frame from there to the entry meets a condition `SiteOK`, and each frame before the entry starts in the player's routine. Then on every frame up to the entry the screen is on the first page and the scroll lock is on, and at the end of the entry frame the timer has the long value, at least 160. The proof follows one whole frame in the room with the abstract machine. It does not cut the frame into parts. `Room`, `SiteOK` and the condition on the routine are assumptions. They were checked on real frames.

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

Leaves(m')  :=  page(m') = page(r) ∧ lock(m') = lock(r) ∧ rt(m') ≠ rt(r) ∧ ( rt(m') = e_s → timer(m') = long )
```

`K` is known bits of 73 bytes, listed below. `T` is the tiles in the block buffers of `r`, and 0.

```
room_step    :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  Room(frame(m, i)) ∨ Leaves(frame(m, i))
room_run     :  seq(n + 1) = frame(seq(n), inp(n)),  c ≤ e,  Room(seq(c)),
                ∀ n ∈ [c, e),  (∀ j, SiteOK(tr_n(j))) ∧ rt(seq(n)) = rt(r),   rt(seq(e)) = e_s
                →  (∀ n ∈ [c, e), Room(seq(n)))  ∧  timer(seq(e)) = long  ∧  page(seq(e)) = page(r)  ∧  lock(seq(e)) = lock(r)
room_keeps   :  Room(m) ∧ (∀ j, SiteOK(tr(j)))  →  page(frame(m, i)) = page(m)  ∧  lock(frame(m, i)) = lock(m)
RoomRun.screen :  the same  →  ∀ n ∈ [c, e],  page(seq(n)) = 0  ∧  lock(seq(n)) ≠ 0
RoomRun.timer  :  the same  →  160 ≤ timer(seq(e))
entry_long   :  the same (in place of rt(seq(e)) = e_s, the entry condition with no timer)  →  the entry condition with the timer at least 160
screen_check (private): roomCheck(sy, nm, m₀, 160) = true (native_decide)
```

Lean: `Theorems/ScreenPage.lean` (`readStep`, `writeStep`, `s_readStep`, `s_writeStep`, `SiteOK`, `walkS`, `frame_of_walkS`, `RoomCond`, `Leaves`, `room_step`, `room_keeps`, `room_run`, `RoomRun`, `RoomRun.screen`, `RoomRun.timer`, `entry_long`), private `Proof/ScreenPage.lean` (`screen_check`, `screen_first_page`, `screen_long_timer`, `screen_entry`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## The three parts of the item

**(1) The entry frame.** It is inside the check of a whole frame. If the abstract state at the frame's end has `rt = e_s`, the check fails unless `timer` is known to be `long` in it. In the pipe's code `page` is known to be 0, so there is one branch that writes the timer.

**(2) One frame keeps it.** The list `K` has all the bits of the page and the lock. In both cases of `room_step` their values do not change (`room_keeps`). With a reference that has the lock off, or the page at 1, the check does not pass (see below).

**(3) The start.** It stays a condition on one state, `Room(seq(c))`. It does not come from the rows of the change into the room (see the assumptions below).

## How it works

**The abstract machine.** The machine of [A run with unknown bytes](b-2-3-TaintRun.md), with no change. Three ways of walking are added on top of it. Each is proved for one instruction against the real `step`.

* `LDA (zp),Y` with a pointer not known (`readStep`, `s_readStep`). If the address read is RAM or ROM, nothing else in the machine changes. The value read is taken as not known. At the block buffer read, the value is split into each value of `T`.
* `STA (zp),Y` that erases a coin (`writeStep`, `s_writeStep`). The block buffers have no known bit, so the abstract state does not change wherever it writes.
* Splitting (`preS`). `dot ≤ L` cuts the time window. The index of the screen buffer is split into the values below 64. `x` is split into the four cases of a set low bit.

**The table.** A search makes a table of abstract states. The check walks from each state of the table and checks that each path ends in a state of the table, or at the frame's end in `Room` or `Leaves` (`walkS`, `finR`). What the search forgets, the check confirms with `AS.le`. So the search is no part of the proof.

**Size.** The search has 211,005 steps, 8,767 forks, 0 failures, a table of 9,383. The whole check takes about 4 s in a program and about 9 s in the private build.

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

Programs, not theorems.

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

| Run | Frames | Paused | Entries | Short timer | First states in `Room` | Frames with `SiteOK` that end in neither `Room` nor `Leaves` | Instructions not `SiteOK` |
|---|---|---|---|---|---|---|---|
| the TAS in the room | 111 | 0 | 1 | 0 | 1 / 1 | 0 | 0 |
| 13 real entries, 17 other histories, the TAS's first state, with random inputs and runs to the right | 130,030 | 28,315 | 20 | 0 | 31 / 31 | 0 | 0 |
| the same, written big at the first state | 15,975 | 3,757 | 5 | 0 | 4 / 4 | 0 | 0 |
| the game timer written near 100 at the first state, no input | 900 | 0 | 0 | 0 | 3 / 3 | 0 | 0 |
| written right of the pipe, Right and B, pauses | 4,800 | 2,328 | 0 | 0 | 12 / 12 | 0 | 192 |

* Every entry frame ends with the timer at `long`.
* Every frame ends in `Room` or `Leaves`.
* The last instruction of the slowest handler is at dot 43,009; `L` is 83,342.
* He does not run right past the screen. While the scroll lock is on, `ChkPOffscr` puts him back on the screen. Written right of the pipe, holding Right and B, he reaches at most pixel 240, and his page stays 0.

## Assumptions (not proved in Lean)

* **`Room(seq(c))`.** 73 bytes at the first control in the room. `K` keeps only bytes that do not differ between runs. It fails for a fire Mario (`PlayerStatus` 2); before this pipe in 1-1 there is one power-up. It should come from walking the rows of the change into the room, since the state after that change is nearly all known. If the last row of item 1-1-b-3-2 knows the values of `K`, one check with `AS.le` is enough. The bytes of `K` that the area's setup does not clear are `AreaType`, `CurrentPlayer`, `PlayerStatus`, `WorldNumber`, `OperMode`, `OperMode_Task`, `AreaMusicBuffer_Alt`. The exit condition of those rows has to know them. This page does not depend on those rows, and they were not run here.
* **The time in `SiteOK`.** The frames in the room do not overrun.
* **The address of a read.** `LDA (zp),Y` does not read a register.
* **Tiles.** A block buffer read gives a value of `T`. This comes from the address being in the block buffers, and the block buffers of the room being as at the start or with coins erased. Not proved.
* **The head.** A read for the head gives 0 or a coin. This comes from the head not reaching a brick in the room. On real frames the jump is too low (measured: the least `y` of a big Mario is 45, and his head is below the top row).
* **The address that erases a coin, the buffer's index.** Both hold on real frames. The index was at most 55.
* **`x & 15 ≠ 0`.** This is that `z` of [The change out of the side pipe](d-1-SideTransition.md) is not reached. Without it the change takes 378 frames, which is the long side, but `Entry2` asks for `timer ≥ 160`.
* **Starting in the player's routine up to the entry.** Time-up can leave this routine (the check has ends with the routines of injury, death and losing a life). Such a run uses far more than 1748 frames.
* Frames are the emulator's frames.

## Use in the [route](0-1-Route.md)

The timer in `chg.entry₂` can be replaced by these (`entry_long`, private `screen_entry`). `Route.Changes` has this form, and `Changes.run₂` uses `entry_long`. The checks on the ROM are `Route.RoomChecks`.

```
entry₂     : Entry2 nm₂ nx₂ E 0 (seq a₂)            (no condition on the timer)
roomOrder  : b₁ ≤ a₂
roomStart  : Room(seq b₁)
roomSites  : ∀ n ∈ [b₁, a₂),  ∀ j,  SiteOK(tr_n(j))
roomStay   : ∀ n ∈ [b₁, a₂),  rt(seq n) = rt(r)
```

**The list `K`** (names):

`GameEngineSubroutine`, `Enemy_Flag` (6), `Enemy_ID+5`, `Player_State` (bits 0xfc), `Block_State` (2), `Misc_State` (9), `EnemyData`, `EnemyDataHigh`, `AreaMusicBuffer` (bits 0xfb), `AreaMusicQueue`, `FloateyNum_Timer` (6), `VineFlagOffset`, `Block_RepFlag` (2), `Cannon_PageLoc` (6), `Cannon_X_Position` (6), `Cannon_Y_Position` (4), `EnemyFrenzyBuffer`, `SecondaryHardMode`, `EnemyFrenzyQueue`, `SprDataOffset`, `SwimmingFlag`, `JumpspringAnimCtrl`, `FireballThrowingTimer`, `ScreenLeft_PageLoc`, `ScreenRight_PageLoc`, `ScreenRight_X_Pos`, `AreaParserTaskNum`, `ScrollLock`, `EnemyDataOffset`, `EnemyObjectPageLoc`, `ScrollThirtyTwo`, `CloudTypeOverride`, `AreaType`, `CurrentPlayer`, `PlayerStatus` (bits 0xfe), `WorldNumber`, `OperMode`, `OperMode_Task`, `StarInvincibleTimer`, `AreaMusicBuffer_Alt` (bits 0xfb)

**Files.** `Theorems/ScreenPage.lean`, private `Proof/ScreenPage.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta screen-check FM2    # the check, the conditions on real frames, about 104 s
```
