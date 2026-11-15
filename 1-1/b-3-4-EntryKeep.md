[← Back](README.md) | [English](b-3-4-EntryKeep.md) | [Japanese](b-3-4-EntryKeep-ja.md)

# The state at the vertical pipe's entry, from the title

**Claim.** This is a partial result. `Entry` is the condition on the state at the end of the frame that enters the vertical pipe ([the change into the room without `fall`](b-3-2-PipeChangeEnd.md)). The frame has ended in the idle loop, the pipe's timer is at least 48, and 97 bytes and 12 bytes under a mask have the values of the reference entry (115 and 13 before round 12). Here the idle loop, the pipe's timer and 73 of these 109 bytes come from the press of Start on the title and from the frames from control to the entry. The field `entry₁` of [the whole route](0-1-Route.md) is gone. In its place `Changes` has two fields:

* `entryRest₁`: the condition `Entry` on the other 36 bytes only (`Rest`). This is a condition on one state.
* `upClean₁`: each instruction of the frames from control to the entry meets `Clean` with the 71 bytes of `held`, the pipe's timer and the six bytes of the pause among the bytes that a store through an index or a pointer does not touch. Since round 14 it is the theorem `Run.upClean₁` from the one field `chg.upCleanU` ([One condition on each instruction up to the pipe](a-5-10-UpClean.md)).

In round 10, item 1-1-b-3-4-2 shrank from 61 bytes and the timer to 56 bytes: the frames keep 4 more bytes (the kind of enemy slot 4, the place of cannon 0: 3 bytes), and the walk of the entry frame gives one more byte (the buttons left and right) and the timer. Each byte that stays has a measured reason below.

**Round 11.** Two changes. (1) The bits 1 to 6 of the pause byte (`GamePauseStatus`, under the mask `0x7E`) are no longer in `restNames`: the near states of `TitleStart` now know the pause byte (the press condition knows it since round 5), and the walk of a frame from control keeps these bits, because the pause routine writes the byte only with bit 0 flipped and bit 7 set, or with bit 7 cleared. So `Rest` has 55 bytes, `atEntry` 73, `held` 71, `kept` 70. (2) The guard also lists the six bytes of the pause (`pauseSix`), and `Checks` has two more checks, for [the pause at the entry](b-3-7-3-EntryPause.md). The walk of a frame hardly changes: 1,176,671 steps and a table of 53,438 states (53,437 before).

**Round 12.** `Entry` no longer asks 19 bytes, and these left `Rest`: the walks of the pipe's frames do not need them (`PipeChangeEnd.entryDropped`). So `Rest` has 36 bytes, and `Entry` 97 bytes and 12 under a mask. `atEntry`, `held`, `kept`, the guard and the walk of this page do not change, because the 19 bytes were all in `Rest`. They are the buttons up and down, the enemies' page, the screen's timer, the demo's timer, three bytes after the world's number in the menu, the byte after the mode, the height of misc object 8, Mario's state, the state of enemy slot 5, the second square's effect queue, the flagpole's number, the vine's height, the first cannon's offset, the duplicate, the colours, the loop, and the flag of a new game timer. How they were found: for each byte of `Rest` alone, the start states of the walks of [the change into the room without `fall`](b-3-2-PipeChangeEnd.md) were made without it, and the old walk (`zcheck`), the walk with the pause's class beside it (`pcheck`, [b-3-7-2](b-3-7-2-PipePause.md)) and `leftCheck` ran again (`entry-need`). 20 bytes pass alone. 19 of them pass together too; the tables are then 38,253 and 23,238 states for the old walk (36,062 and 23,135 before), and 58,850 and 43,229 for `pcheck` (56,816 and 43,120 before). The 20th is the first square's effect queue: the walks pass without it, but the tables of `pcheck` grow to 156,721 and 143,033 states (with the 19 too: 158,808 and 143,194, about 63 s in a program instead of 27 s), so it stays. The private build of `Proof/PipeChangeEnd.lean` is the check that the walks pass with the new `Entry`.

That each of these frames starts in the idle loop in control (`FrameStart`) is proved too (item 1-1-b-3-4-3): by induction from the press of Start, under `upClean₁`. The field `upStart₁` is gone. For this, the entry `a₁` is now the first frame from control on whose machine has no control (as `a₂` and `b₂` are first frames), and `Changes` has the bound `dA` in place of the number `a₁`.

The notation: `seq n` is the machine when frame `n` begins, and `seq (n+1) = frame(seq n, inp n)`. Frame 0 is the frame before control, so `seq 1` has control. `ctl(m)` says that `m` has control: the mode is the game's, the task is the game core, the routine is the player's. `a` is `a₁`, the machine after the entry frame:

```
a₁ = upEnd(seq, dA) = the least n with 1 ≤ n ≤ 1 + dA and (¬ctl(seq n) or n = 1 + dA)
```
 `e` is the reference entry. A watched byte is `(i, k, v)`: its index, the bits it asks, and the value of `e`.

```
Watched(W, m)  :  ∀ (i, k, v) ∈ W,  m[i] & k = v & k
atEntry        :  the 109 bytes of Entry but those of restNames          (73)
held           :  atEntry but OperMode and OperMode_Task                  (71)
kept           :  held but those of endNames (the buttons left and right) (70)
rt(m)          :  m[GameEngineSubroutine]
IdleAt(m)      :  m has ended a frame in the idle loop, with the pc and the stack of e
Rest(m)        :  Entry's bytes of restNames have the values of e      (36)
T(m)           :  48 ≤ m[ChangeAreaTimer]                                (the pipe's timer)
```

**The statements.** `starts_of_title` and `entry_of_title`, with the checks `hB` (`TitleStart.check`) and `hK` (`EntryKeep.Checks`):

```
Begin(seq, inp)
∧ ∀ n, seq (n+1) = frame(seq n, inp n)
∧ ∀ n, 1 ≤ n < a → ctl(seq n)
∧ ∀ n, 1 ≤ n < a → ∀ j, Clean_G(trace(seq n, inp n, j))
→ ∀ n, 1 ≤ n < a → FrameStart(seq n)
```


```
Begin(seq, inp)                                             (Start on the title, as TitleStart says)
∧ ∀ n, seq (n+1) = frame(seq n, inp n)
∧ 1 ≤ a
∧ ∀ n, 1 ≤ n < a → FrameStart(seq n)
∧ ∀ n, 1 ≤ n < a → ∀ j, Clean_G(trace(seq n, inp n, j))
∧ Rest(seq a)
→ Entry(seq a)
```

They come from these steps:

```
Begin.start    :  Begin(seq, inp) → FrameStart(seq 1) ∧ Watched(kept, seq 1)
keep_frame     :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j)))
                    → (rt(frame(m, i)) = player → Watched(kept, frame(m, i)))
                    ∧ (rt(frame(m, i)) = pipe   → Watched(atEntry, frame(m, i)) ∧ IdleAt(frame(m, i)))
keep_start     :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j))) ∧ ctl(frame(m, i))
                    → FrameStart(frame(m, i)) ∧ Watched(kept, frame(m, i))
pipe_end       :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j))) ∧ rt(frame(m, i)) = pipe
                    → Watched(atEntry, frame(m, i)) ∧ IdleAt(frame(m, i)) ∧ T(frame(m, i))
start_up       :  the induction of keep_start from frame 1:  ∀ n, 1 ≤ n < a → FrameStart(seq n) ∧ Watched(kept, seq n)
entry_of_rest  :  IdleAt(m) ∧ Watched(atEntry, m) ∧ T(m) ∧ Rest(m) → Entry(m)
```

`start_up` is an induction on `n`. `Begin.start` gives frame 1. If frame `n` starts as `FrameStart` with the kept bytes, the walk ends it in the idle loop with the kept bytes when its routine at the end is the player's (`keep_start`). Control at `seq (n+1)` gives the routine, the mode and the task. Then `Watched(atEntry, seq a)`, `IdleAt(seq a)` and `T(seq a)` (`pipe_end`, `watched_entryT`): the routine at `seq a` is the pipe's, by `Rest`. If `a = 1`, `seq 1` has control and the routine is the player's, which contradicts `Rest`.

In `Route`, `Changes.upStay` gives `ctl(seq n)` for `1 ≤ n < a₁` from the choice of `a₁`. `Run.upStart₁` gives `FrameStart(seq n)` for `1 ≤ n < a₁` from `title` and `upClean₁`. `Run.entry₁` gives `Entry(base.seq a₁)` from `title`, `Run.upStart₁`, `upClean₁` and `entryRest₁`. `Changes.run₁` takes it as an argument. `Run.change₁`, `Run.change₂`, `Run.start`, `Run.roomStart` and `level_ge_of_parts` take the two checks. `route_1_1` still concludes `1748 + j ≤ L`.

Lean: `Theorems/PipeChangeEnd.lean` (`entryDropped`, `entryKnown`), `Theorems/EntryKeep.lean` (`restNames`, `endNames`, `atEntry`, `held`, `kept`, `Rest`, `timerI`, `timerOK`, `IdleAt`, `guardOf`, `finE`, `walkE`, `keepCheck`, `nearCheck`, `listCheck`, `Checks`, `fin_frame`, `keep_frame`, `keep_start`, `start_to`, `Begin.start`, `Begin.watched`, `watched_up`, `watched_entry`, `timer_of`, `pipe_end`, `watched_entryT`, `start_up`, `starts_of_title`, `entry_of_rest`, `entry_of_title`), `Theorems/Route.lean` (`upEnd`, `Base.dA`, `Base.a₁`, `Changes.upStay`, `Changes.entryRest₁`, `Changes.upClean₁`, `Changes.one_le`, `Changes.run₁`, `Run.upStart₁`, `Run.entry₁`). The private proof: `entry_near`, `entry_keep`, `entry_lists` by `native_decide`, and `entry_checks`.

## How it works

**Frame 0.** `TitleStart` makes a set of frame-start states that covers every machine from the press to frame 0. Frame 0 begins in a near or held state. `nearCheck` (`TitleStart.frame0Check`) walks frame 0 from these states again with any input, Start included, and asks at each end with control, besides the speed 0, that the 69 kept bytes are known with the values of `e`, and that the state is in the idle loop as a frame in control starts (`FrameKeep.endOK`: the program counter and the stack, the dot and its flags, NMI on, no strobe). It also asks that the title's program is the program of the frames from control. The near states know these bytes, because the game writes them with known values between the press and control.

**One frame from control.** The walk is that of [FrameKeep](f-6-19-FrameKeep.md). The frame starts in the idle loop with the player's routine, the mode and the task known, and the kept bytes known. Every other byte is not known. A store through an index or a pointer forgets every byte but those of the guard's list (`held` and the list of `PipeWrites`). `Clean` says that it does not touch them. The end of a frame is good if the routine is known and:

* if it is the player's routine, the kept bytes are known with their values, and the state is in the idle loop as a frame in control starts (`FrameKeep.endOK`);
* if it is the pipe's routine, the bytes of `atEntry` are known with their values, and the state is in the idle loop as `IdleAt` asks (the dots, the flags, the program counter and the stack of `e`). The buttons left and right are not known when the frame starts, but every path to such an end writes them with 0;
* any other routine (a death, a power-up, the flagpole, a side pipe, ...) is good with no more.

The search for the table keeps the accumulator apart where it is about to be stored as the routine. Without this, the routine of a death and that of a power-up were joined, and the routine was not known at 110 ends.

**Why `a₁` is the first frame without control.** The walk does not ask the mode and the task at the end. If it asks them with the values at control, it fails at one end: the routine is the player's, but the mode is 2 and the task 0. This is the axe at the end of a castle (`HandleAxeMetatile` writes the mode and the task and keeps the routine). The walk knows no map, so it cannot exclude it. So the induction takes control at `seq (n+1)` from the choice of `a₁`, and the walk asks only the idle loop.

**Why 36 bytes stay** (round 12). Two facts hold for each of the 36 bytes.

(1) The walks of the pipe's frames need it. With the byte not known at the entry, `zcheck` and `pcheck` fail (`entry-need`). For the area music's queue and the event music's queue the search did not end in 10 minutes (the two walks take about 40 s with them known). The first square's effect queue is the exception above: it is not needed, but the walk without it is about three times as large.

(2) The press of Start and the frames from control do not give it. Each byte was measured alone (`entry-widen`, `entry-writers`, `entry-stores`, exit 0, run again in round 12): on real frames from control to the entry (the TAS 368 frames, the reference 440, 60 runs of random inputs from control, 25,238 frames), by a search of the walk with the byte kept too, and by a search with the byte asked only at the pipe's end. Every byte below fails at least one of these. A byte that the frames keep must have the value of `e` at the start of every frame, must stay in the walk of a frame, must be known at frame 0, and must not be stored through an index on real frames (else `upClean₁` would fail on them).

| group | bytes | why |
|---|---|---|
| other values on real frames | 16 | some frame from control to the entry starts with another value: the routine (every frame; it also says that the first frame without control enters the vertical pipe: that frame may also end with the routine of a death or a power-up, and `Rest` says which run this is), the enemies' page select (TAS 66 of 368 frames), the states and flags of blocks 0 and 1 (4), the state of misc object 8, the scores 0 to 2 (3), the states of enemy slots 0 to 2 (3), the flag and the kind of enemy slot 5 (the power-up's, 2), the first square's effect queue |
| written by the walk of a frame | 15 | the walk knows nothing of the objects, the area's data or the sound, and finds a frame that ends with the player's routine after it writes the byte (at 1 to 8 ends): the flag of enemy slot 4 (`EraseEnemyObject`, `KillELoop`, `FinishFlame`), the music and the noise (6: the queues by `StoreMusic`, `HandlePowerUpCollision`, `RunGameTimer`, `HoleDie`, `BrickShatter`, the warp pipe; the buffers by the sound engine), the vine's flag offset, the frenzy (2), the warp zone (the area parser), the next area (2: the enemy data's command, `ParseRow0e`), the star (`HandlePowerUpCollision`), the world (`GetWNum`, a warp pipe) |
| not known at frame 0 | 1 | the saved song: no near state of `TitleStart` knows it, and the walk also writes it (`NoStopSfx`) |
| stored through an index on real frames | 4 | the walk keeps them and frame 0 knows them, but real frames store to them through an index, which `Clean` forbids for a kept byte: the kinds of enemy slots 0 to 2 (the enemy loader: on the TAS 4, 2 and 1 times), score 5 (5 times on random runs) |

The group of the warp pipe does not help: if the warp zone were kept, the walk would not write the world, but the area parser writes the warp zone, and the enemy data's command writes the next area. The bytes of round 10 that left in round 12 were in the first group (7), the second (7) and the third (5).

**The pipe's timer.** The entry frame writes the timer: the vertical pipe's code writes 48. On some ends the side pipe's code runs after it in the same frame and writes the timer again, read from a table at one of two places that a branch chooses; the timer is then 160 or 52. Before this round the search joined the two branches, and the walk knew only some bits: the value was one of 32, 36, 48, 52, 160, 164, 176, 180. Now the search keeps the index apart where the table is read for the timer, keeps the timer among the guard's bytes, and keys the states whose routine is the pipe's by what they know of the timer. Then every end with the pipe's routine knows bits of the timer that make at least 48 (`timerOK`: the known bits, the others 0, give at least 48; then every value with these bits is at least 48).

**The checks.** Natively (`entry-walk-check`, exit 0): `nearCheck` 1.3 s, `keepCheck` 4.4 s (a search of 1,176,662 steps and a table of 53,437 states, then the walks), `listCheck` at once. The search finds no end that fails. In the proof build the three checks take about 7 s.

## Measured

`entry-keep-check FM2` (exit 0):

* The lists: `Entry` has 109 bytes and masks; 73 proved at the entry, 70 kept from control, 36 assumed (`Rest`) (round 12; 128 and 55 in round 11, 72, 69 and 56 before). The runs below were done again in round 12 with these lists, with the same counts and no failure.
* Start on the title on 100 frames, no other input: 79 runs reach control, all with the kept bytes.
* The TAS from control to the entry: 368 frames, all `FrameStart`, every instruction `Clean` (1,917,255), the kept bytes on every frame. At the entry `Rest`, `atEntry`, `IdleAt` and `Entry` hold. So on the TAS the first frame without control after control is the entry, and `a₁` is the frame of the entry as before.
* The reference entry: 440 frames, the same.
* Random inputs from control (300 runs, 127,841 frames, 5,390 of them paused) and from frames of the TAS (300 runs, 75,241 frames): no frame against `FrameStart` or `Clean`, no frame that loses a kept byte. The largest dot of an instruction is 70,697 (the limit is 89,278).
* The reference's inputs with 0 to 39 frames of standing before the last jump: 38 entries, all with `Rest`, `atEntry`, `IdleAt` and `Entry`.

Each byte of `restNames` alone (all exit 0; round 12, with the 36 bytes):

* `entry-need`: for each of the 55 bytes of round 11, the walks of the pipe's frames with the byte not known at the entry (about 65 s each; 8 at once). 20 pass, 33 fail, and for the two music queues the search did not end in 10 minutes. `entry-need group ...`: the 19 bytes together pass.
* `entry-widen FM2 real`: the value at control, and the frames from control to the entry that start with another value (the TAS, the reference, 60 random runs from control with 25,238 frames). 16 bytes have another value on some frame; 20 keep the value of `e`.
* `entry-widen FM2`: for each of the 20, the search of the final walk with the byte kept too (about 6 s each), and the check of frame 0. No failing end for 4 of them (the kinds of enemy slots 0 to 2, score 5), and frame 0 knows them; the other 16 fail at 1 to 8 ends, all at the frame's end in the idle loop. Frame 0 does not know the saved song.
* `entry-stores FM2`: the stores through an index or a pointer to each byte on real frames (the runs of `entry-keep-check`). Real frames store to the other 4: the kinds of enemy slots 0 to 2 (TAS 4, 2, 1; reference 3, 2, 2; random 653, 180, 134), score 5 (random 5).
* `entry-widen FM2 end`: the search with the byte asked only at the pipe's end. Only the routine has no failing end; every other byte fails at 1 to 6 ends.
* `entry-writers NAME ...`: the places where the walk with the byte kept changes it. The routines in the table come from here.
* Run with the lists before this round's change, the same tests passed for the 5 bytes that are now proved: the kind of enemy slot 4 and the place of cannon 0 (no failing end, known at frame 0, no store through an index on real frames), and the buttons left and right (no failing end when asked only at the pipe's end).

## Measured in round 13: one condition for these frames and part a's

`upClean₁` and two conditions of part a speak of the same frames from control to the entry: `pipe.lags.clean` (`Clean` with the pause byte protected, on the frames before the entering frame, counted or not) and `pipe.opening.cleanK` (`CleanK` of `FrameKeep.guardF`, on the counted frames 1 to 32). `pipe.clean` (`Clean` on the entering frame up to the routine's write) is a fourth. All four guards are the guard of `PipeWrites` with more protected bytes, and they have the same idle loop, the same `late` and the same jump tables. So one condition could take their place:

```
GU        :=  the guard of PipeWrites, protecting the bytes of EntryKeep.guardOf, LagPause.guardP and FrameKeep.guardF      (128 bytes)
q         :=  the move routine's store of the fraction  (FrameKeep.spotOf.store)
upCleanU  :   ∀ n, 1 ≤ n < a₁ → ∀ j,  CleanK(GU, q, trace(seq n, inp n, j))
```

It would give each of the four, if two small facts are proved (not done):

* `FrameKeep.cleanK_sub` gives `CleanK` of `guardF` from `CleanK` of `GU`: this is `opening.cleanK`.
* `Clean` of a guard asks every store to be `Plain`, and `CleanK` leaves out the store at `q` with the index 0. That store writes the player's fraction. The guard of `EntryKeep`, `guardP` and the guard of `PipeWrites` do not protect it (read from the ROM: the target of `STA abs,X` at `q` with `X = 0`). A lemma on this one instruction would give `upClean₁`, `lags.clean` and `pipe.clean` from `upCleanU`.
* The frames must be the same: the entering frame is frame `a₁ − 1`, so `pipe.lags.ix pipe.E + 1 = a₁`. This would be an induction: the frames up to `ix E` end in control (`Lags.ctl` for the counted frames, `LagFrames.keeps_frame` for the others, which needs `Clean` on the frame, so `n < a₁` first), the entering frame ends with the pipe's routine (`pipe.enter`), and `Rest` says that `seq a₁` has the pipe's routine.

`up-clean-union FM2` (exit 0, about 8 min; `quick` prints only the guards): on the runs of `entry-keep-check` (the TAS 368 frames, the reference 440, 300 random runs from control, 300 from frames of the TAS, the reference with 0 to 39 frames of standing): 221,490 frames, 978,397,731 instructions. No instruction is against `upCleanU`, and none against any of the old conditions, `CleanK` of `guardF` on every frame included. The store at `q` with the index 0 ran 211,323 times, and was `Plain` for the guard of `EntryKeep` and for `guardP` every time. `GU` protects 4 bytes that only `guardF` protects: the swimming flag, the change of size, the castle flag and the player's fraction. So `upCleanU` asks more than the four conditions only this: no store through an index or a pointer writes these 4 bytes on the frames after the 32nd counted frame and on the frames not counted (the fraction: but at `q` with the index 0).

What would change in part a's files (not done here):

* `Theorems/PipeFrames.lean`: the field `Lags.clean` goes; `Lags.cleanG`, `Lags.keepsP` and the theorems that use them (`Lags.no_call`, `Lags.known_end`, `Lags.starts`, `lags_keepI`, and those after them) take it as a hypothesis on the frames `1 ≤ n < ix E`.
* `Theorems/OpenFrames.lean`: the field `Real.cleanK` goes; the two theorems that read `O.cleanK` (`Real.frame_step`, `Real.flat`) take it as a hypothesis on the counted frames `1 ≤ t ≤ N`, `t < E`.
* `Theorems/Route.lean`: the field `Pipe.clean` goes; `ChangesBase.upClean₁` becomes `upCleanU`; new theorems give the four conditions from it, and the theorems of `Run` that use `pipe` pass them on. The private `route_1_1` (`genProofs` in `Main.lean`) passes the new theorem in place of `R.pipe.clean`.
* `Theorems/HurryStart.lean`: `Chg₁.upClean₁` the same.

Fields removed: `chg.upClean₁`, `pipe.lags.clean`, `pipe.clean`, `pipe.opening.cleanK`. Field added: `chg.upCleanU`.

## Assumptions (not proved in Lean)

* `entryRest₁`: `Rest` at the entry: 36 bytes (55 in round 11; 56 before, with the pause's bits). Before this round it also asked the pipe's timer and 5 more bytes; before that, `entry₁` asked the idle loop, the timer and 128 bytes.
* `upClean₁`: each instruction of these frames is `Clean`; a store through an index or a pointer does not touch the 71 bytes of `held`, the pipe's timer and the six bytes of the pause (round 11). A run that fills one of these slots before the entry is outside the theorem: the enemy slots 3 and 6 and the kind and the state of slot 4, the fireballs, the blocks 2 and 3, the misc objects 0 to 7, the cannons 0 to 5, the scores 3, 4 and 6. No real run here does. This round added the kind of slot 4, the place of cannon 0, the buttons left and right and the pipe's timer to these bytes. On real frames no store through an index touches them (`entry-keep-check`).

`upClean₁` is not reduced here. `entry-clean-use` (exit 0) counts the places where the walk leaves an instruction to `Clean`, because its state does not decide it. The bound on the dot (`late`) is used at all 9,068 places that the walk passes. A store through an index or a pointer with a target not known: 710 places, in 324 routines of objects, drawings, the vine, the fireworks, the bridge, the scores and others. `LDA (zp),Y` with a pointer not known: 47 places (the area parser, the enemy data, the music). The jump with an index not known: 1 place. Of the 724 places with such a store, the walk knows the target on every visit at 14 places only. So asking `Clean` only where the walk does not know it would take 14 places off.
