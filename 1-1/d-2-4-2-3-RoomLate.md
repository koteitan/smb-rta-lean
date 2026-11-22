[← Back](README.md) | [English](d-2-4-2-3-RoomLate.md) | [Japanese](d-2-4-2-3-RoomLate-ja.md)

# The time of the room's frames from the walk

**Claim.** On a frame of the room that starts in a class of the screen buffers' records ([The screen buffers' records](d-2-4-2-2-BufferRecords.md)), every instruction away from the idle loop runs 6000 dots or more before the frame's end, if every instruction of the sound routine's code runs at dot 9,000 or earlier.

This is proved, with one check on the ROM. Until round 28 the route asked `Late` (the dot at most `L` = 83,342 away from the idle loop) on every instruction of every frame of the room. Now it asks:

* `Late` only on the room's first frame and on the frames after a frame that starts with the control of the screen's buffers at 6 (the frames `U`);
* on the other frames, only `LateS`: an instruction of the sound routine's code (from `SoundEngine` on in the ROM) runs at dot 9,000 or earlier.

The time of the rest of the handler on those frames is proved: the screen update, the pads, the pause, the timers, the waits for the sprite-0 flag, the game's routine and the sprites.

`tr_n(j)` is the machine after `j` instructions of frame `n`. `pc`, `dot` are its program counter and its dot in the frame. `idle` is the idle loop. `snd` is the address of `SoundEngine`. `A.hi` is the last dot that an abstract state allows. `Rest(Z, m)`, `U(n)`, `InPat` are as in [The screen buffers' records](d-2-4-2-2-BufferRecords.md).

## The statement

```
Late(m)          :=  pc(m) ≠ idle  →  dot(m) ≤ L                       (L = 83,342: 6000 dots before the frame's end)
LateS(m)         :=  snd ≤ pc(m)   →  dot(m) ≤ 9,000
timeOK(A)        :=  pc(A) = idle  ∨  A.hi ≤ L
RestS(m)         :=  LateS(m) ∧ Read(m) ∧ Erase(m) ∧ Xbit(m)

late_of_time     :  Sim(A, m) ∧ timeOK(A)  →  Late(m)
frame_of_walkST  :  the walk walkST succeeds from the frame's start, and chk(A) ∧ R(m) → SiteOK(m) at every state, and R → LateS,
                    and ∀ j, R(tr(j))   →   (∀ j, SiteOK(tr(j)))  ∧  the frame ends in a state that fin accepts
rec_frame2T      :  recCheckT(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(0, L, m),  ∀ j, RestS(tr(j))
                    →  (∀ j, SiteOK(tr(j)))  ∧  (InPat(0, L, frame(m, i)) ∨ InPat(6, L₆, frame(m, i)))
rec_frame3T      :  recCheckT(T, L, L₆),  RoomCond(r, K_M, m),  InCls(T, m),  InPat(6, L₆, m),  ∀ j, RestS(tr(j))   →   ∀ j, SiteOK(tr(j))

late_sites_of_rows :
      the conditions of records_sites_of_rows, with recCheckT(T, L, L₆) in place of recCheck(T, L, L₆),
      ∀ n ∈ [b, a), ∀ j,  Read(tr_n(j)) ∧ Erase(tr_n(j)) ∧ Xbit(tr_n(j)),
      ∀ n ∈ [b, a),  U(n)  →  ∀ j, Late(tr_n(j)),
      ∀ n ∈ [b, a),  ¬U(n) →  ∀ j, LateS(tr_n(j)),
      the fields of round 28 for Reads through the screen update's pointer (on U) and Off (from 6 after 6)
      →   ∀ n ∈ [b, a), ∀ j, SiteOK(tr_n(j))
```

The changed fields of `chg` (for every `n ∈ [b₁, a₂)` and every `j`):

```
roomLate   :  U(n)   →  Late(tr_n(j))          (was: on every frame)
roomLateS  :  ¬U(n)  →  LateS(tr_n(j))          (new)
```

`recCheckT` is `recCheck` of [The screen buffers' records](d-2-4-2-2-BufferRecords.md) with the walks (ii) (from the patterns `L`) and (iii) (from the patterns `L₆`) replaced by the walk with the time. Walks (i) and (iv), from buffers that the walk does not know, are as before. `Run.roomTime` (the frames do not end during the movement, used by part c) now comes from `Run.roomSites`; it takes the checks `hR`, `hB`, `hK`.

Lean: `Theorems/RoomLate.lean` (`timeOK`, `late_of_time`, `LateS`, `sclamp`, `sim_sclamp`, `walkST`, `live_stepST`, `frame_of_walkST`, `searchST`, `cfgBT`, `walkCheckST`, `STOK`, `frameST`, `fixCuts`, `chkT`, `walk2T`, `walk3T`, `recCheckT`, `rec_frame1T` to `rec_frame4T`, `late_sites_of_rows`), private `Proof/SiteMusic.lean` (`buffer_records_check` is now `recCheckT`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## How it works

**The time in the walk.** An abstract state has a first and a last dot (`lo`, `hi`), and `Sim` says that the machine's dot is between them. Each step adds the instruction's cycles. A read of the picture's status splits the state at the dot where a flag changes (vblank's end, the sprite-0 flag), so a wait for a flag ends in the walk too.

**The old clamp.** The room's walks clamp `hi` to `L` before each step (`ScreenPage.clampS`), and that needs `Late` of the machine. The searches also set `hi` to `L` when a state is joined the third time. So the walk's own bound was `L` almost everywhere (round 26: above `L` at 1.6 M of 1.65 M steps).

**The new walk** (`walkST`). It checks `timeOK` at every state, and covers a state by a state of the table with no clamp to `L`. Only in the sound routine's code it clamps `hi` to 9,000 (`sclamp`), and that needs `LateS` of the machine. The table comes from a search (`searchST`) that joins states with the same key and keeps the larger `hi`; it widens `hi` to 9,000 at the third join only in the sound routine's code. So `Late` on every instruction follows from the check and `LateS` (`late_of_time`); the clamp to `L` inside `RoomPause.pstep` changes nothing.

**Why the sound routine stays assumed** (measured, `buffer-ctl-check FM2 N lateW`). Without any clamp, the search of walk (ii) has 93,415 states with `hi` at most 20,000 and 44,042 states whose `hi` grows to the cap; the first of them are in the sound routine, and every later state inherits them. The walk follows the music data through a pointer and offsets it does not know (the music table of [RoomMusic](d-2-5-1-RoomMusic.md) knows 9 of the sound's bytes):

* `FindEventMusicHeader` shifts the music's queue until a set bit. The walk knows the event music's buffer only up to its victory bit; after the shifts it has a piece where the queue is known to be 0, and that piece shifts for ever.
* The fetch of square 1's data and of the noise's data loop on a zero byte, read at an offset the walk does not know.

On a real run the song's data end these loops. In the walk they do not end, so a bound needs the song's state.

**The sprite-0 wait** (found this round). `ScreenPage.jsrRets` takes every byte `0x20` of the handler as a call, and the address of the picture's status has the high byte `0x20`. So the search forgot A and Y right after each read of the status, also in the wait for the sprite-0 flag; the walk then did not know the flag, and with no clamp the wait went on for ever. It is no fault of the proof (the walk checks that it only forgets), but it cost precision. `fixCuts` keeps a place only if the call's target is in the ROM.

**Size.** Walk (ii) with the time: search 137,425 states, table 48,455, every state passes, the largest `hi` away from the idle loop 54,912 (about 25 s natively). Walk (iii): search 725,637 states, table 264,079, the largest `hi` 55,128 (about 140 s). Before, walks (ii) and (iii) took 8 s and 44 s. `recCheckT` takes about 165 s natively (`recCheck` about 107 s), and the private `Proof.SiteMusic` about 180 s (round 28: 135 s).

**The choice of 9,000.** After the sound routine come the pads, the pause, the timers and the wait for the end of vblank (the sprite-0 flag clears). A path that reaches this wait after the sprite-0 flag is set again (dot 17,732) waits until the next frame, in the walk and on the real machine. With the clamp at 10,000 (measured before the fix of the cuts above), the walk reached the wait at dot 17,679 at the latest, 53 dots before. With 9,000 the check passes; the real sound routine ends by dot 7,159 on every measured frame.

## Checked on real frames

`buffer-ctl-check FM2 1100 latereal`: the largest dot of an instruction of the sound routine's code, and of any instruction away from the idle loop, on the movie's room frames and on own runs from them (random inputs, 1,100 runs small and 1,100 big, up to 600 frames each).

| Run | Frames | Sound routine's last dot (largest) | Any instruction (largest) |
|---|---|---|---|
| the movie in the room | 111 | 6,491 | 41,402 |
| own runs, small | 51,791 | 6,497 | 42,151 |
| own runs, big | 55,755 | 7,159 | 42,437 |

So `LateS` (9,000) holds on every measured frame; the margin is 1,841 dots on the big runs. The frames `U`, where `Late` is still asked, are 14 of the movie's 111 frames (round 28's count: the first frame and 13 after a frame from the control at 6).

## Assumptions (not proved in Lean)

* **`roomLate`** on the frames `U`: walks (i) and (iv) start from buffers that the walk does not know, and the screen update's loop over the records then has no count the walk knows. Measured with the time (`timecheck 3`): walk (i) has 11 failing states of 91,263, walk (iv) 26 of 222,570, all in the screen update.
* **`roomLateS`** on the other frames: the sound routine's instructions run at dot 9,000 or earlier. A proof needs the song's state at each frame's start (round 6 measured 207 song states on real runs; a summary of the sound routine for any values of its bytes is false).

## Reproduce

```
.lake/build/bin/smbrta buffer-ctl-check FM2 1 timecheck     # the two walks with the time, natively (2 also runs recCheckT), about 8 min
.lake/build/bin/smbrta buffer-ctl-check FM2 3 timecheck     # walks (i) and (iv) with the time: they fail at the screen update (measured only)
.lake/build/bin/smbrta buffer-ctl-check FM2 1100 latereal   # the dots on real frames
.lake/build/bin/smbrta buffer-ctl-check FM2 0 late2         # the search of walk (ii) with no clamp at all, with the old cuts (measured only)
```
