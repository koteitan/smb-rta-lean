[← Back](README.md) | [English](b-3-4-EntryKeep.md) | [Japanese](b-3-4-EntryKeep-ja.md)

# The state at the vertical pipe's entry, from the title

**Claim.** This is a partial result. `Entry` is the condition on the state at the end of the frame that enters the vertical pipe ([the change into the room without `fall`](b-3-2-PipeChangeEnd.md)). The frame has ended in the idle loop, the pipe's timer is at least 48, and 115 bytes and 13 bytes under a mask have the values of the reference entry. Here the idle loop, the pipe's timer and 72 of these 128 bytes come from the press of Start on the title and from the frames from control to the entry. The field `entry₁` of [the whole route](0-1-Route.md) is gone. In its place `Changes` has two fields:

* `entryRest₁`: the condition `Entry` on the other 56 bytes only (`Rest`). This is a condition on one state.
* `upClean₁`: each instruction of the frames from control to the entry meets `Clean` with the 70 bytes of `held` and the pipe's timer among the bytes that a store through an index or a pointer does not touch.

Item 1-1-b-3-4-2 shrank this round from 61 bytes and the timer to 56 bytes: the frames keep 4 more bytes (the kind of enemy slot 4, the place of cannon 0: 3 bytes), and the walk of the entry frame gives one more byte (the buttons left and right) and the timer. Each of the 56 bytes has a measured reason below.

That each of these frames starts in the idle loop in control (`FrameStart`) is proved too (item 1-1-b-3-4-3): by induction from the press of Start, under `upClean₁`. The field `upStart₁` is gone. For this, the entry `a₁` is now the first frame from control on whose machine has no control (as `a₂` and `b₂` are first frames), and `Changes` has the bound `dA` in place of the number `a₁`.

The notation: `seq n` is the machine when frame `n` begins, and `seq (n+1) = frame(seq n, inp n)`. Frame 0 is the frame before control, so `seq 1` has control. `ctl(m)` says that `m` has control: the mode is the game's, the task is the game core, the routine is the player's. `a` is `a₁`, the machine after the entry frame:

```
a₁ = upEnd(seq, dA) = the least n with 1 ≤ n ≤ 1 + dA and (¬ctl(seq n) or n = 1 + dA)
```
 `e` is the reference entry. A watched byte is `(i, k, v)`: its index, the bits it asks, and the value of `e`.

```
Watched(W, m)  :  ∀ (i, k, v) ∈ W,  m[i] & k = v & k
atEntry        :  the 128 bytes of Entry but those of restNames          (72)
held           :  atEntry but OperMode and OperMode_Task                  (70)
kept           :  held but those of endNames (the buttons left and right) (69)
rt(m)          :  m[GameEngineSubroutine]
IdleAt(m)      :  m has ended a frame in the idle loop, with the pc and the stack of e
Rest(m)        :  Entry's bytes of restNames have the values of e      (56)
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

Lean: `Theorems/EntryKeep.lean` (`restNames`, `endNames`, `atEntry`, `held`, `kept`, `Rest`, `timerI`, `timerOK`, `IdleAt`, `guardOf`, `finE`, `walkE`, `keepCheck`, `nearCheck`, `listCheck`, `Checks`, `fin_frame`, `keep_frame`, `keep_start`, `start_to`, `Begin.start`, `Begin.watched`, `watched_up`, `watched_entry`, `timer_of`, `pipe_end`, `watched_entryT`, `start_up`, `starts_of_title`, `entry_of_rest`, `entry_of_title`), `Theorems/Route.lean` (`upEnd`, `Base.dA`, `Base.a₁`, `Changes.upStay`, `Changes.entryRest₁`, `Changes.upClean₁`, `Changes.one_le`, `Changes.run₁`, `Run.upStart₁`, `Run.entry₁`). The private proof: `entry_near`, `entry_keep`, `entry_lists` by `native_decide`, and `entry_checks`.

## How it works

**Frame 0.** `TitleStart` makes a set of frame-start states that covers every machine from the press to frame 0. Frame 0 begins in a near or held state. `nearCheck` (`TitleStart.frame0Check`) walks frame 0 from these states again with any input, Start included, and asks at each end with control, besides the speed 0, that the 69 kept bytes are known with the values of `e`, and that the state is in the idle loop as a frame in control starts (`FrameKeep.endOK`: the program counter and the stack, the dot and its flags, NMI on, no strobe). It also asks that the title's program is the program of the frames from control. The near states know these bytes, because the game writes them with known values between the press and control.

**One frame from control.** The walk is that of [FrameKeep](f-6-19-FrameKeep.md). The frame starts in the idle loop with the player's routine, the mode and the task known, and the kept bytes known. Every other byte is not known. A store through an index or a pointer forgets every byte but those of the guard's list (`held` and the list of `PipeWrites`). `Clean` says that it does not touch them. The end of a frame is good if the routine is known and:

* if it is the player's routine, the kept bytes are known with their values, and the state is in the idle loop as a frame in control starts (`FrameKeep.endOK`);
* if it is the pipe's routine, the bytes of `atEntry` are known with their values, and the state is in the idle loop as `IdleAt` asks (the dots, the flags, the program counter and the stack of `e`). The buttons left and right are not known when the frame starts, but every path to such an end writes them with 0;
* any other routine (a death, a power-up, the flagpole, a side pipe, ...) is good with no more.

The search for the table keeps the accumulator apart where it is about to be stored as the routine. Without this, the routine of a death and that of a power-up were joined, and the routine was not known at 110 ends.

**Why `a₁` is the first frame without control.** The walk does not ask the mode and the task at the end. If it asks them with the values at control, it fails at one end: the routine is the player's, but the mode is 2 and the task 0. This is the axe at the end of a castle (`HandleAxeMetatile` writes the mode and the task and keeps the routine). The walk knows no map, so it cannot exclude it. So the induction takes control at `seq (n+1)` from the choice of `a₁`, and the walk asks only the idle loop.

**Why 56 bytes stay.** Each byte was measured alone (`entry-widen`, `entry-writers`, `entry-stores`, exit 0): on real frames from control to the entry (the TAS 368 frames, the reference 440, 60 runs of random inputs from control, 25,238 frames), by a search of the walk with the byte kept too, and by a search with the byte asked only at the pipe's end. Every byte below fails at least one of these. A byte that the frames keep must have the value of `e` at the start of every frame, must stay in the walk of a frame, must be known at frame 0, and must not be stored through an index on real frames (else `upClean₁` would fail on them).

| group | bytes | why |
|---|---|---|
| other values on real frames | 23 | some frame from control to the entry starts with another value: the buttons up and down, the routine, the enemies' page (2), the screen's timer, the states and flags of blocks 0 and 1 (4), misc object 8 (2), the scores 0 to 2 (3), Mario's state, the states of enemy slots 0 to 2 (3), the state, the flag and the kind of enemy slot 5, the power-up's (3), the two sound effects (2) |
| written by the walk of a frame | 22 | the walk knows nothing of the objects, the area's data or the sound, and finds a frame that ends with the player's routine after it writes the byte: the flag of enemy slot 4 (`EraseEnemyObject`, `KillELoop`, `FinishFlame`), the music and the noise (6: `StoreMusic`, `HandlePowerUpCollision`, `RunGameTimer`, `HoleDie`, `BrickShatter`, the sound engine), the flagpole's number (`FlagpoleObject`), the vine (2), the first cannon's offset (`StrCOffset`), the frenzy (2), the duplicate, the warp zone, the colours (`Alter2`), the loop (`ChkRow13`), the next area (2: `ParseRow0e`), the star (`HandlePowerUpCollision`), the world and the flag of a new game timer (2: `GetWNum`, a warp pipe) |
| not known at frame 0 | 7 | the walk of frame 0 begins in a near state of `TitleStart`, and none of the 4 near states knows them: the demo's timer (a timer, free at the press), three bytes after the world's number in the menu and the byte after the mode (not read from the press to control, so the condition at the press does not ask them), the pause's bits (asked at the press, lost before frame 0), the saved song (also written by the walk: `NoStopSfx`). The walk of a frame from control keeps the first 6 |
| stored through an index on real frames | 4 | the walk keeps them and frame 0 knows them, but real frames store to them through an index, which `Clean` forbids for a kept byte: the kinds of enemy slots 0 to 2 (the enemy loader: on the TAS 4, 2 and 1 times), score 5 (5 times on random runs) |

**The pipe's timer.** The entry frame writes the timer: the vertical pipe's code writes 48. On some ends the side pipe's code runs after it in the same frame and writes the timer again, read from a table at one of two places that a branch chooses; the timer is then 160 or 52. Before this round the search joined the two branches, and the walk knew only some bits: the value was one of 32, 36, 48, 52, 160, 164, 176, 180. Now the search keeps the index apart where the table is read for the timer, keeps the timer among the guard's bytes, and keys the states whose routine is the pipe's by what they know of the timer. Then every end with the pipe's routine knows bits of the timer that make at least 48 (`timerOK`: the known bits, the others 0, give at least 48; then every value with these bits is at least 48).

**The checks.** Natively (`entry-walk-check`, exit 0): `nearCheck` 1.3 s, `keepCheck` 4.4 s (a search of 1,176,662 steps and a table of 53,437 states, then the walks), `listCheck` at once. The search finds no end that fails. In the proof build the three checks take about 7 s.

## Measured

`entry-keep-check FM2` (exit 0):

* The lists: `Entry` has 128 bytes and masks; 72 proved at the entry, 69 kept from control, 56 assumed (`Rest`).
* Start on the title on 100 frames, no other input: 79 runs reach control, all with the kept bytes.
* The TAS from control to the entry: 368 frames, all `FrameStart`, every instruction `Clean` (1,917,255), the kept bytes on every frame. At the entry `Rest`, `atEntry`, `IdleAt` and `Entry` hold. So on the TAS the first frame without control after control is the entry, and `a₁` is the frame of the entry as before.
* The reference entry: 440 frames, the same.
* Random inputs from control (300 runs, 127,841 frames, 5,390 of them paused) and from frames of the TAS (300 runs, 75,241 frames): no frame against `FrameStart` or `Clean`, no frame that loses a kept byte. The largest dot of an instruction is 70,697 (the limit is 89,278).
* The reference's inputs with 0 to 39 frames of standing before the last jump: 38 entries, all with `Rest`, `atEntry`, `IdleAt` and `Entry`.

Each byte of `restNames` alone (all exit 0):

* `entry-widen FM2 real`: the value at control, and the frames from control to the entry that start with another value (the TAS, the reference, 60 random runs from control with 25,238 frames). 23 bytes have another value on some frame; 33 keep the value of `e`.
* `entry-widen FM2`: for each of the 33, the search of the final walk with the byte kept too (about 4 s each), and the check of frame 0. No failing end for 10 of them; the other 23 fail at 1 to 8 ends. Frame 0 does not know 6 of the 10.
* `entry-stores FM2`: the stores through an index or a pointer to each byte on real frames (the runs of `entry-keep-check`). Real frames store to the other 4: the kinds of enemy slots 0 to 2 (TAS 4, 2, 1; reference 3, 2, 2; random 653, 180, 134), score 5 (random 5).
* `entry-widen FM2 end`: the search with the byte asked only at the pipe's end. Only the routine has no failing end; every other byte fails at 1 to 6 ends.
* `entry-writers NAME ...`: the places where the walk with the byte kept changes it. The routines in the table come from here.
* Run with the lists before this round's change, the same tests passed for the 5 bytes that are now proved: the kind of enemy slot 4 and the place of cannon 0 (no failing end, known at frame 0, no store through an index on real frames), and the buttons left and right (no failing end when asked only at the pipe's end).

## Assumptions (not proved in Lean)

* `entryRest₁`: `Rest` at the entry: 56 bytes. Before this round it also asked the pipe's timer and 5 more bytes; before that, `entry₁` asked the idle loop, the timer and 128 bytes.
* `upClean₁`: each instruction of these frames is `Clean`; a store through an index or a pointer does not touch the 70 bytes of `held` and the pipe's timer. A run that fills one of these slots before the entry is outside the theorem: the enemy slots 3 and 6 and the kind and the state of slot 4, the fireballs, the blocks 2 and 3, the misc objects 0 to 7, the cannons 0 to 5, the scores 3, 4 and 6. No real run here does. This round added the kind of slot 4, the place of cannon 0, the buttons left and right and the pipe's timer to these bytes. On real frames no store through an index touches them (`entry-keep-check`).

`upClean₁` is not reduced here. `entry-clean-use` (exit 0) counts the places where the walk leaves an instruction to `Clean`, because its state does not decide it. The bound on the dot (`late`) is used at all 9,068 places that the walk passes. A store through an index or a pointer with a target not known: 710 places, in 324 routines of objects, drawings, the vine, the fireworks, the bridge, the scores and others. `LDA (zp),Y` with a pointer not known: 47 places (the area parser, the enemy data, the music). The jump with an index not known: 1 place. Of the 724 places with such a store, the walk knows the target on every visit at 14 places only. So asking `Clean` only where the walk does not know it would take 14 places off.
