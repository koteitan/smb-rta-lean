[← Back](README.md) | [English](d-2-5-1-RoomMusic.md) | [Japanese](d-2-5-1-RoomMusic-ja.md)

# The music bytes through the room's frames

**Claim.** At the side pipe's entry, five bytes of the music follow from the room's frames: the song's pointer (two bytes), square 1's offset, the event music's buffer and the noise effect's buffer have the values of the reference, if the area music's buffer has the reference's value. This is proved, with checks on the ROM. So the route asks 11 bytes at the entry, not 16 (`entry₂`, 1-1-d-2-5). Nothing new is assumed.

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `trₙ(j)` the machine `j` instructions into frame `n`. `seq(n)` is the machine when frame `n` begins. `rt(m)` is the routine byte, `r` the reference machine of the room. `Room`, `SiteOK`, `EntryRest` and `R` (its 16 bytes) are those of [The screen's page in the room](d-2-4-ScreenPage.md). `InRowsT` is the rows of the time of [the change into the room](b-3-7-1-SoundRows.md). `SIn(t, m)`: the bytes of `m` are as the state `t` of a table says ([Where one step of the CPU writes RAM](d-3-4-1-StepWrites.md)).

## The statement

The table `T` holds 9 bytes: the event music's buffer, the song's pointer (2), square 1's offset, the noise effect's buffer, the added note length, the area music's buffer and its copy, and the event music's queue. `a` is the area music's buffer. `D` is the five bytes that follow. `R'` is `R` without `D` (11 bytes). `V` is the references of the entry.

```
music_run     :  Room(seq c) ∧ InRowsT(seq c) ∧ ctl(seq c),
                 ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),     rt(seq e) ≠ rt(r)
                   →  ∃ t ∈ T,  SIn(t, seq e)
derive_spec   :  t ∈ T ∧ SIn(t, m) ∧ m[a] = r[a]  →  ∀ i ∈ D,  m[i] = r[i]
EntryRestM(m) :=  ∃ (v, X) ∈ V,  ∀ i ∈ X ∩ R',  m[i] = v[i]
entryRest_of  :  (∃ t ∈ T, SIn(t, m)) ∧ EntryRestM(m)  →  EntryRest(m)
```

`music_run` follows from the check `roomCheckM` (the walk) and `startCheckM` (the first control), `derive_spec` from `deriveCheck`, `entryRest_of` from `refsCheck` (each reference lists `a` and has the values of `r` on `a` and on `D`). `Facts` holds these checks; `factsOf` makes it.

In the route:

```
entry₂ : EntryRestM(seq a₂)                         (11 bytes; it was EntryRest, 16 bytes)
RoomChecks.music : ∃ T, Facts(T)                     (new; the checks on the ROM)
ChangesK.entryRest₂ : EntryRest(seq a₂)              (theorem; from c = b₁, e = a₂)
```

Lean: `Theorems/RoomMusic.lean` (`ix`, `amb`, `emq`, `hurryBit`, `tabIdx`, `derivedIdx`, `extraOf`, `knownM`, `regM`, `cfgM`, `roomCheckM`, `knowsMasked`, `rowM`, `startCheckM`, `startBoth`, `startBoth_parts`, `deriveCheck`, `restIdxM`, `EntryRestM`, `refsCheck`, `masked_of`, `masked_of_knows`, `roomCond_append`, `start_of_invL`, `derive_spec`, `refs_spec`, `Facts`, `factsOf`, `music_run`, `entryRest_of`, `rt_mem`), `Theorems/Route.lean` (`ChangesBase.entry₂`, `RoomChecks.music`, `ChangesK.entryRest₂`), private `musicTab`, `room_starts`, `room_music_walk`, `room_music_derive`, `room_music_refs`, `room_music_rt`, `room_music_bit`, `room_music` (in `Proof/RoomPause.lean`). There is no game data in the public files.

## How it works

**The walk.** It is the walk of [The pause through the room's frames](d-3-4-4-RoomPause.md) with another table. At the call of the sound routine the state is split by the table, the sound routine, the pads and the pause routine are walked with the 9 bytes known, and after the pause routine the bytes must be in a state of the table. Then they are forgotten, but for the bits of the area music's buffer and its copy that the room's condition knows (`RoomPause.Reg.keepB`). A frame that leaves the room need not end with bit 0 of the pause byte known (`RoomPause.Reg.needG`). Outside the region a step keeps the 9 bytes, or writes some of them and every state of the table, so written, is in a state of the table (`StepWrites.writeOK`). The room's condition is taken with one more byte, the noise effect's queue, known to be 0 (`knownM`).

**Why a step outside the region writes.** When the player falls into a hole, the code stores the death music in the event music's queue. The walk does not know the player's height well enough to rule this out, nor the value stored. So the table also has states with the queue not known. These frames stay in the player's routine, so the queue cannot be a byte of the room's condition.

**The first control.** The rows of the time of the change into the room know at control: the event music's buffer 0, the song's pointer, square 1's offset 0, the noise effect's buffer 0, the area music's buffer, its copy but for one bit, and the noise effect's queue 0. They do not know the added note length. The event music's queue is 0, or holds the hurry-up music, or only its bit of the hurry-up music is not known. The check splits each state by that bit (`TaintRun.splitBit`); each piece is under a state of the table. The bit is read from the disassembly (`TimeRunningOutMusic`).

**The table.** It is found by a program; the check does not depend on it. 62 states: the room's music with the queue 0, with the hurry-up music queued, or with the queue not known; the hurry-up music; and other songs. The other songs come from the queue not known: the code that looks for the song's header then reads the queue bit by bit, and the walk follows each bit. All of these have the area music's buffer 0, so they do not admit the reference's value, and `deriveCheck` asks nothing of them. In these states square 1's offset is not followed (the walk does not know the note counters, so the offset of the hurry-up music would take every value).

**What stays in `entry₂`.** The area music's buffer (it picks the room's music), the event music's queue (the hurry-up music may be queued on the entry frame), the added note length (not known at the first control), and the 8 bytes that are not music: the routine, the player's vertical position, the screen's buffer (5 bytes), the level's number. Since round 13 the routine is a theorem in `Route.Run` ([The routine at the side pipe's entry](d-2-5-2-EntryRoutine.md)), so `Run` asks 10 bytes.

**The size of the check.** The table takes about 25 s to find (in `gen-proofs`). `roomCheckM` takes about 15 s in a program. `startBoth` makes the rows of the time once for `RoomPause.startCheck` and `startCheckM`, about 26 s. These are more than a few seconds.

## Measured, not a theorem

The search for the table, as a program (`room-music-check`):

| choice | result |
|---|---|
| the queue in the room's condition with its bit of the hurry-up music free, not in the table | the queue is read bit by bit: 7 other songs' headers; 25 new states each round, no end after 131 rounds |
| the queue in the table; square 1's offset followed in every state | 231 states after 230 rounds, still growing |
| square 1's offset followed only where the area music's buffer admits the reference's value | 62 states; the room's search 635,696 steps, 0 failures; `roomCheckM` true |
| the queue also in the room's condition (all but the hurry-up bit) | 6 frame ends refused: the hole death stores the queue with a value not known |

Real runs (`room-music-real FM2 5 R`): the runs of [The pause through the room's frames](d-3-4-4-RoomPause.md). The first controls in the room from 13 real entries into the vertical pipe, 5 runs each (Start at random on the pipe's frames, once in `R` frames), then 600 frames of random inputs with Start at random; walks into the side pipe from 42 states near it; and the movie.

| `R` | first controls | in the table | room frame starts | in the table | side pipe entries | in the table | `EntryRestM` | `EntryRest` | the five bytes as the reference |
|---|---|---|---|---|---|---|---|---|---|
| 20 | 65 | 65 | 68,135 | 68,135 | 210 | 210 | 210 | 210 | 210 |
| 7 | 65 | 62 | 69,597 | 69,594 | 210 | 210 | 210 | 210 | 210 |

With `R` = 7, three first controls have no music at all (every byte of the table 0). In each of these runs `quiet₁` of the first change fails at the vertical pipe's exit, so the run is outside the rows of the first change, and the theorem does not speak of it. On the movie every frame in the room is in the table, and at the entry (movie frame 764) `EntryRestM` and `EntryRest` hold.

## Round 12: why the other 11 bytes stay (measured)

A program, not a theorem (`entry-bytes-check`, about 51 s). It reads what the rows of the time of the change into the room know at control (14,224 states with control), and what the room's walk of [The screen's page in the room](d-2-4-ScreenPage.md) knows at its frame ends.

The room's walk has 14 frame ends: 2 with the side pipe's routine, 6 with the player's control, 2 with the routine of losing a life (`PlayerLoseLife`, after a fall into a hole), and 4 with the routines of the injury or of death and `GameTimerExpiredFlag` set (the time-up, `TimeUpOn`). At the 2 ends with the side pipe's routine the walk knows the player's high byte, `VRAM_Buffer_AddrCtrl`, `GameTimerExpiredFlag` and all bits but one of the area music's buffer. It knows none of the 11 bytes.

| byte | at the room's first control | why it stays | what would give it |
|---|---|---|---|
| `GameEngineSubroutine` | known | it says that the first frame that leaves the player's routine enters the side pipe. The walk also leaves by a fall into a hole and by the time-up | the player's height in the room, and the timer |
| `Player_Y_Position` | known (the height where he drops in) | the walk does not follow the height. Part c's walk of the entering frame (`SideFrame`) knows the row of the side read, not the height at the frame's end | a walk of the entering frame that keeps the height (part c) |
| `VRAM_Buffer1_Offset`, `VRAM_Buffer1` (+0, +1, +2, +7) | known | erasing a coin (`RemoveCoin_Axe`) sets `VRAM_Buffer_AddrCtrl` so that the next frame's screen update clears the second buffer, not the first: the first keeps the coin's records. A coin on the entering frame adds records too | no coin on the entering frame and the frame before: the position on two frames (part c) |
| `AreaMusicBuffer` | known | the table has states where it is 0: the hurry-up music, and songs read from the queue that the hole's code stores | no hurry-up music in the room (the timer), no fall into a hole (the height) |
| `EventMusicQueue` | the hurry-up music queued in 7,112 states; in the other 7,112 all bits but the hurry-up bit known 0 | in the table it is 0, the hurry-up music, or not known. The sound routine keeps the music queues while the pause sound plays (`SkipSoundSubroutines`), so the hurry-up music queued on a frame of the unpause sound is still queued at the entry. The hole's code stores the death music with `DeathMusicLoaded + 1`, which the room's condition does not know | the timer, and the height |
| `NoteLengthTblAdder` | not known | the rows of the change into the room do not know it: the condition at the vertical pipe's entry does not have it. Also, after the hurry-up music the area music starts again (`MusicLoopBack`) with this byte still set: with the table built from it known to be 0 at control (`entry-bytes-check nlta`, about 96 s), 64 states, and 2 of the 6 with the reference's area music buffer have it 8 | part b's rows, and the timer |
| `AreaNumber` | not known | the rows do not know it (part b). It cannot leave `Entry2`: after the exit the area parser reads it (`VerticalPipe`, whether a pipe gets a piranha plant) | part b's rows |

So 8 of the 11 bytes wait on two facts that no walk of the room knows: the game timer (the hurry-up music and the time-up, [The runs with the hurry-up music](0-6-4-HurryMusic.md)) and the player's height (no fall below the screen in the room). The screen's buffer waits on the position on two frames; `NoteLengthTblAdder` and `AreaNumber` on the rows of part b.

The game timer at the room's first control: no state with control knows a bit of the three digits, and none has `dg` (see [The game timer at the side pipe](d-3-5-1-SideTime.md)).

## What changed in the route

* `entry₂` asks 11 bytes (`RoomMusic.EntryRestM`). The theorem `ChangesK.entryRest₂` gives the 16 bytes of `EntryRest`, and `ChangesK.run₂` uses it.
* `RoomChecks` has a new field `music : ∃ T, RoomMusic.Facts … T`. `RoomChecks` is built in the private files of the route and of the hurry-up music.
* `RoomPause.Reg` has two new fields with defaults (`keepB := []`, `needG := true`), and a step outside the region may write by `writeOK`. The pause's check is the same with the defaults.

## Assumptions (not proved in Lean)

* `entry₂`: 11 bytes at the entry have the values of a reference (1-1-d-2-5). Before, 16.
* `SiteOK` on each instruction in the room (`chg.roomSites`) and the conditions of the first change's rows, as before.

**Files.** `Theorems/RoomMusic.lean`, `Theorems/RoomPause.lean`; the private checks are in `Proof/RoomPause.lean` (`genRoomMusic` in `Main.lean`, which also writes the checks of [the pause](d-3-4-4-RoomPause.md)). The names `NoiseSoundQueue` and `TimeRunningOutMusic` were added to `ScreenPage.namesOf`.

**To reproduce.**
```
.lake/build/bin/smbrta room-music-check           # the table, roomCheckM, startCheckM, deriveCheck, refsCheck, about 90 s
.lake/build/bin/smbrta room-music-real FM2 5 20    # the table on real runs, about 2 min (also with 7)
```
