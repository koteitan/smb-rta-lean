[← Back](README.md) | [English](b-3-4-EntryKeep.md) | [Japanese](b-3-4-EntryKeep-ja.md)

# The state at the vertical pipe's entry, from the title

**Claim.** This is a partial result. `Entry` is the condition on the state at the end of the frame that enters the vertical pipe ([the change into the room without `fall`](b-3-2-PipeChangeEnd.md)). The frame has ended in the idle loop, the pipe's timer is at least 48, and 115 bytes and 13 bytes under a mask have the values of the reference entry. Here the idle loop and 67 of these 128 bytes come from the press of Start on the title and from the frames from control to the entry. The field `entry₁` of [the whole route](0-1-Route.md) is gone. In its place `Changes` has three fields:

* `entryRest₁`: the condition `Entry` on the other 61 bytes only, and the pipe's timer (`Rest`). This is a condition on one state.
* `upStart₁`: each frame from control to the entry starts in the idle loop, in control (`FrameStart`).
* `upClean₁`: each instruction of these frames meets `Clean` with the 65 kept bytes among the bytes that a store through an index or a pointer does not touch.

The notation: `seq n` is the machine when frame `n` begins, and `seq (n+1) = frame(seq n, inp n)`. Frame 0 is the frame before control, so `seq 1` has control. `a` is `a₁`, the machine after the entry frame. `e` is the reference entry. A watched byte is `(i, k, v)`: its index, the bits it asks, and the value of `e`.

```
Watched(W, m)  :  ∀ (i, k, v) ∈ W,  m[i] & k = v & k
atEntry        :  the 128 bytes of Entry but those of restNames          (67)
kept           :  atEntry but OperMode and OperMode_Task                  (65)
rt(m)          :  m[GameEngineSubroutine]
IdleAt(m)      :  m has ended a frame in the idle loop, with the pc and the stack of e
Rest(m)        :  48 ≤ m[ChangeAreaTimer]  ∧  Entry's bytes of restNames have the values of e      (61)
```

**The statement.** `entry_of_title`, with the checks `hB` (`TitleStart.check`) and `hK` (`EntryKeep.Checks`):

```
Begin(seq, inp)                                             (Start on the title, as TitleStart says)
∧ ∀ n, seq (n+1) = frame(seq n, inp n)
∧ 1 ≤ a
∧ ∀ n, 1 ≤ n < a → FrameStart(seq n)
∧ ∀ n, 1 ≤ n < a → ∀ j, Clean_G(trace(seq n, inp n, j))
∧ Rest(seq a)
→ Entry(seq a)
```

It comes from three steps:

```
Begin.watched  :  Begin(seq, inp) → Watched(kept, seq 1)
keep_frame     :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j)))
                    → (rt(frame(m, i)) = player → Watched(kept, frame(m, i)))
                    ∧ (rt(frame(m, i)) = pipe   → Watched(atEntry, frame(m, i)) ∧ IdleAt(frame(m, i)))
entry_of_rest  :  IdleAt(m) ∧ Watched(atEntry, m) ∧ Rest(m) → Entry(m)
```

By induction, `Watched(kept, seq n)` for `1 ≤ n < a`: the routine at `seq (n+1)` is the player's, by `FrameStart(seq (n+1))`. At `seq a` the routine is the pipe's, by `Rest`. So `Watched(atEntry, seq a)` and `IdleAt(seq a)`. If `a = 1`, `seq 1` has control and the routine is the player's, which contradicts `Rest`.

In `Route`, `Run.entry₁` gives `Entry(chg.seq chg.a₁)` from `title`, `upStart₁`, `upClean₁` and `entryRest₁`. `Changes.run₁` takes it as an argument. `Run.change₁`, `Run.change₂`, `Run.start`, `Run.roomStart` and `level_ge_of_parts` take the two checks. `route_1_1` still concludes `1748 + j ≤ L`.

Lean: `Theorems/EntryKeep.lean` (`restNames`, `atEntry`, `kept`, `Rest`, `IdleAt`, `guardOf`, `walkE`, `keepCheck`, `nearCheck`, `listCheck`, `Checks`, `keep_frame`, `Begin.watched`, `watched_up`, `watched_entry`, `entry_of_rest`, `entry_of_title`), `Theorems/Route.lean` (`Changes.entryRest₁`, `Changes.upStart₁`, `Changes.upClean₁`, `Changes.one_le`, `Changes.run₁`, `Run.entry₁`). The private proof: `entry_near`, `entry_keep`, `entry_lists` by `native_decide`, and `entry_checks`.

## How it works

**Frame 0.** `TitleStart` makes a set of frame-start states that covers every machine from the press to frame 0. Frame 0 begins in a state of its near group. `nearCheck` walks the near group's frames again and asks at each end, besides control and the speed 0, that the 65 kept bytes are known with the values of `e`. The near states know these bytes, because the game writes them with known values between the press and control.

**One frame from control.** The walk is that of [FrameKeep](f-6-19-FrameKeep.md). The frame starts in the idle loop with the player's routine, the mode and the task known, and the kept bytes known. Every other byte is not known. A store through an index or a pointer forgets every byte but those of the guard's list. `Clean` says that it does not touch them. The end of a frame is good if the routine is known and:

* if it is the player's routine, the kept bytes are known with their values;
* if it is the pipe's routine, the bytes of `atEntry` are known with their values, and the state is in the idle loop as `IdleAt` asks (the dots, the flags, the program counter and the stack of `e`);
* any other routine (a death, a power-up, the flagpole, a side pipe, ...) is good with no more.

The search for the table keeps the accumulator apart where it is about to be stored as the routine. Without this, the routine of a death and that of a power-up were joined, and the routine was not known at 110 ends.

**Why 61 bytes stay.** The walk knows nothing of the objects on the screen. So it finds frames where a new object comes, an event's music starts, or a new area is set.

| group | bytes | why |
|---|---|---|
| at control | 12 | the walk of frame 0 does not know them, or they have other values at control: the buttons up and down, the routine, the enemies' page (2), the screen's timer, the demo's timer, three bytes after the world in the menu, the byte after the mode, the pause's bits, the saved song |
| on the way | 11 | other values on real runs before the entry, back at the entry: the first block's state and flag, the last misc object (2), the first scores (2), Mario's state, the first two enemies' states, the two sound effects |
| unknown objects | 30 | a frame may write them with the player's routine kept: the buttons left and right, the enemy slots 4 and 5 (5), the first enemy's kind and the third's, the music and the noise (6), the flagpole's number, the vine (2), the first cannon (4), the frenzy (2), the duplicate, the warp zone, the colours, the loop, the next area (2), the star |
| written through an index | 6 | real frames store to them through an index: the second block's state and flag, the second enemy's kind, the third enemy's state, two scores |
| warp pipe | 2 | the entry frame of a warp pipe writes the world and the flag of a new timer |

The pipe's timer is not proved either. At two of the four ends with the pipe's routine, the side pipe's code has also run in the frame and has read its timer from a table with an index not known. There the walk knows only some bits of the timer: the value is one of 32, 36, 48, 52, 160, 164, 176, 180. The real values are 48, 52 and 160, but the walk cannot tell.

**The checks.** Natively: `nearCheck` 1.2 s, `keepCheck` 4.1 s (a search of 1,104,799 steps and a table of 49,733 states, then the walks), `listCheck` at once.

## Measured

`entry-keep-check FM2` (exit 0):

* Start on the title on 100 frames, no other input: 79 runs reach control, all with the kept bytes.
* The TAS from control to the entry: 368 frames, all `FrameStart`, every instruction `Clean` (1,917,255), the kept bytes on every frame. At the entry `Rest`, `atEntry`, `IdleAt` and `Entry` hold.
* The reference entry: 440 frames, the same.
* Random inputs from control (300 runs, 127,841 frames, 5,390 of them paused) and from frames of the TAS (300 runs, 75,241 frames): no frame against `FrameStart` or `Clean`, no frame that loses a kept byte. The largest dot of an instruction is 70,697 (the limit is 89,278).
* The reference's inputs with 0 to 39 frames of standing before the last jump: 38 entries, all with `Rest`, `atEntry`, `IdleAt` and `Entry`.

The six bytes written through an index were found this way. With them among the kept bytes, real frames stored to them through an index: on the TAS once per frame to the second block's state, and twice to the second enemy's kind; on the reference six times; on random runs more.

## Assumptions (not proved in Lean)

* `entryRest₁`: `Rest` at the entry: the pipe's timer and 61 bytes. Before, `entry₁` asked the idle loop, the timer and 128 bytes.
* `upStart₁`: each frame from control to the entry starts in the idle loop in control. New.
* `upClean₁`: each instruction of these frames is `Clean`; a store through an index or a pointer does not touch the 65 kept bytes. New. A run that fills one of these slots before the entry is outside the theorem: the enemy slots 3 and 6 and the state of slot 4, the fireballs, the blocks 2 and 3, the misc objects 0 to 7, the cannons 1 to 5, the scores 3, 4 and 6. No real run here does.
