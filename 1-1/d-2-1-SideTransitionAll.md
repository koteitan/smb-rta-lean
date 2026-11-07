[← Back](README.md) | [English](d-2-1-SideTransitionAll.md) | [Japanese](d-2-1-SideTransitionAll-ja.md)

# What decides the change out of the side pipe

**Statement.** This is a partial result. The change takes 282 = 160 + 122 frames. In the first 160 frames the pipe's timer runs out. For the last 122 frames the length is proved for every value of every byte outside a list `R`. For the first 160 frames it is proved only on 20 listed entry states. That every entry state of every run has length 282 is a theorem only under assumptions (`every_entry`). It is false for some overwritten states.

**A shorter change.** The code's second timer was run. With the screen not on the first page on the frame before the entry, Mario enters and the change takes 174 frames, 108 fewer (Lean, 2 overwritten states). No run reached such a state. From the code a real run cannot reach it (below; this reasoning is not in Lean). So the bound at frame 852 in [the 1-1 route](../docs/route-1-1.md) does not change, but it depends on this reasoning.

`m₀` is the machine at the start of 1-1. `run(m, w)` is the machine after real frames with the inputs `w`. `ctl(m)` is `controllable`. `0^k` is `k` frames of no input. `P` and `E` are the machines before and at the end of the entry frame of [The change out of the side pipe](d-1-SideTransition.md). `T = run(E, 0^160)`, the state when the pipe's timer has run out. `m[i]` is byte `i` of RAM.

`core(m)`: the registers, the program counter, the ROM, the PPU fields, the controller's shift state, the parities of the cycle counter and of the frame counter. Not `pad`, which a frame overwrites, and not RAM. In every `core(M) = core(...)` below, `M` also has tracking off and 2048 bytes of RAM (`SameCore`).

A *place* `v` of `T` is `T` with a dot `d ≤ 9` at the frame boundary, a cycle parity and a frame parity. There are 40 places. The increment bit of the PPU control mirror is off in all of them: unlike above ground, the room writes no column of the level.

`R` (116 bytes), `RE` (218 bytes), `Rvar ⊂ R` (73 bytes) are found by running, and `Rfix = R \ Rvar` (43 bytes). `entries` is `E`, 13 overwritten states and 6 real states (below).

```
decided     :  ∀ place v of T, ∀ M :  core(M) = core(v)  ∧  (∀ i ∈ R, M[i] = v[i])
                 →  ∀ k, 1 ≤ k ≤ 122 → ( ctl(run(M, 0^k)) ↔ k = 122 )
ends        :  the same M :  ∀ i, (i ∈ R ∨ the run from v wrote i)  →  run(M, 0^122)[i] = run(v, 0^122)[i]
atEntry     :  ∀ M :  core(M) = core(E)  ∧  (∀ i ∈ RE, M[i] = E[i])
                 →  ∀ k, 1 ≤ k ≤ 282 → ( ctl(run(M, 0^k)) ↔ k = 282 )
entered     :  P enters  ∧  the screen is on the first page in P
entryStates :  ∀ m ∈ entries, with t = run(m, 0^160) :
                 ∀ k, 1 ≤ k ≤ 282 → ( ctl(run(m, 0^k)) ↔ k = 282 )
                 core(t) = core(T at t's dot, parities and bit)  ∧  ∀ i ∈ Rfix, t[i] = T[i]
                 ∀ M :  core(M) = core(t)  ∧  (∀ i ∈ R, M[i] = t[i])  →  ∀ k, 1 ≤ k ≤ 122 → ( ctl(run(M, 0^k)) ↔ k = 122 )
real        :  each of the 6 real states enters, with the screen on the first page
shorter     :  2 states of P with the screen not on the first page :  they enter  ∧  ∀ k, 1 ≤ k ≤ 174 → ( ctl ↔ k = 174 )
timer       :  E with the timer overwritten by v, 2 values :  ∀ k, 1 ≤ k ≤ 122 + v → ( ctl ↔ k = 122 + v )
lag         :  2 states with six objects close together :  control exactly on frame L,  L > 282
flag        :  the time-up flag set :  control exactly on frame 427
died        :  the game timer at 000 :  ∀ k, 1 ≤ k ≤ 300 → ¬ctl

every_entry :  ∀ M, with t = run(M, 0^160) and v = the place of T with t's dot and parities :
                 (H1) ∀ k, 1 ≤ k ≤ 160 → ¬ctl(run(M, 0^k))
                 (H2) dot(t) ≤ 9  ∧  the increment bit of t is off  ∧  core(t) = core(v)
                 (H3) ∀ i ∈ Rfix, t[i] = v[i]
                 (H4) ∀ k, 1 ≤ k ≤ 122 → ( ctl(run(t, 0^k)) ↔ ctl(run(t with v's values on Rvar, 0^k)) )
               →  ∀ k, 1 ≤ k ≤ 282 → ( ctl(run(M, 0^k)) ↔ k = 282 )
```

In `decided` and `atEntry`, all bytes outside `R` or `RE` are arbitrary. `R` contains no enemy byte, no position or speed of Mario, no byte of the screen's position except `HorizontalScroll` and `VerticalScroll`, and no byte of the block map. So those do not change frames 161 to 282. `every_entry` is about any machine `M`, whether or not it is an entry.

Results with other lengths. The first three are shorter than 282.

| state | where it is written | frames until control |
|---|---|---|
| the screen on pages 2 and 3, Mario on page 2 | `P` | **174** (Lean) |
| the screen's page byte alone, 255 | `P` | **174** (Lean; measured: all values from 129) |
| the change's timer at `v` | `E` | **122 + v** (Lean for 2 values; measured: every `v` from 1, and 0 gives 378) |
| the time-up flag | `E` | 427 (Lean) |
| six goombas 0 px apart, six hammer brothers 4 px apart | `E` | 283, 284 (Lean) |
| six goombas 2, 4, 8 px apart, six koopas 4 px apart | `E` | 283, 283, 282, 283 (measured) |
| game timer at 000 | `E` | no control for 300 frames (Lean): he dies on arrival. On the emulator a life is lost and control comes back in 1-1 on frame 800 |

`HalfwayPage` and `WarpZoneControl`, which change the length of [the vertical pipe's change](b-2-1-PipeTransitionAll.md), do not change this one: 282 with both set (Lean, one state). `WarpZoneControl` is not in `RE`, so `atEntry` covers all its values.

Lean: `Theorems/SideTransitionAll.lean` (`Statement`, `statement_of_check`, `every_entry`, `no_control_before`), and from [What decides the change into the bonus room](b-2-1-PipeTransitionAll.md) `decided_of_check`, `end_of_check`, `entryFacts_of_check`. That page's `Statement` and `every_entry` are about the vertical pipe's entry, so this file has its own, with the same proof. Private `side_all_checks` (by `native_decide`), `side_all`, `side_all_entries`. `every_entry` depends only on `propext`, `Classical.choice` and `Quot.sound`.

## How

**A tracked run decides.** This is the same theorem as on [the vertical pipe's page](b-2-1-PipeTransitionAll.md). If a tracked run from `ref` reads only bytes of `R`, then every machine with `core(M) = core(ref)` and `ref`'s values on `R` gives the same values and the same control on every frame.

**Why the cut is at frame 160.** On frame 160 the pipe's routine sets the area change and the rest of the game engine is skipped. On frame 161 the area's setup clears RAM, and the clear is still running at the end of that frame. So the objects and Mario's position and speed are not read after frame 160. Tracking shows this: from `T` the run reads 107 bytes of the 2048, and 116 over all reference runs. Then come 25 frames that build the area and 97 frames of rising out of the pipe.

**The check** runs on the emulator, about 13,700 frames, about 5 s:

* `decided`: 40 tracked runs of 122 frames from the places of `T`.
* `entries`: for each of 20 entry states, 160 frames with no control, the comparison at frame 160, 122 tracked frames. The overwritten states: 5 goombas; 5 goombas and a power-up; a big fiery Mario with the star timer; fireballs, block objects and coins; the scroll bytes; the frame timers, the master timer, the interval timer and the frame counter, all at their largest value; the same at 0, without the master timer; the digits at 9 with 99 coins; the digits at 0 with the game timer at 001; the random bytes at 0; the random bytes at 255; sound; `HalfwayPage` and `WarpZoneControl`. The real states: entries at `x₀ + 1` and `x₀ + 2` from [The change out of the side pipe](d-1-SideTransition.md), and standing on the floor 0, 5, 10, 15 more frames, then walking in.

**What was left out to stay near 5 s.** The vertical pipe's check has 77 entry states, and here each one takes 3 times as many frames. So the 63 overwritten states of that check are not in this one. They were run on this entry by a program, and all take 282. Places with the increment bit on are also left out, which is why (H2) asks for the bit off.

Bytes of `Rvar`: the frame counter, the music state, `HorizontalScroll`, the master timer, Mario's size and power, `HalfwayPage`, the interval timer, the frame timers, the random bytes, the digits on the status line. Bytes of `Rfix`: the routine, the mode and task bytes, the pause bytes, the sound effect buffers and queues, the area pointer bytes, `AltEntranceControl`, `JoypadOverride`, the level and world numbers, the flags of a new timer and of the time-up, the screen and PPU mirrors, the joypad masks, the demo timer, the bytes of the player count, `PrimaryHardMode`, a few bytes of the sound routine, one frame timer. They do not differ in any of the 20 states.

**What was measured, not in the theorem.**

* From `T`, 107 bytes, every other value, one byte at a time: only `OperMode`, `OperMode_Task`, `GamePauseStatus`, `VRAM_Buffer_AddrCtrl`, `GameTimerExpiredFlag`, `AreaPointer`, `EntrancePage`, `AltEntranceControl`, `JoypadOverride` change the length. All are in `Rfix`. Fewer than 122 frames: only `AltEntranceControl`, which the routine itself writes on frame 160.
* From `E`, 218 bytes, one byte at a time: ten values of each (0, 1, 2, 16, 64, 127, 128, 255, the value ± 1), and every value of a byte where one of them changes the length. So a byte that changes the length only at another value is missed. 15 bytes change it. Fewer than 282 frames:

| byte, overwritten on `E` | values with a shorter change | frames |
|---|---|---|
| `ChangeAreaTimer` | 159 | 123 to 281 |
| `GameEngineSubroutine` (not the pipe's routine) | 8 | 1, 18, 163, 187 |
| `Player_Y_HighPos` | 124 | 163 |
| `OperMode_Task` | 1 | 163 |
| `Player_State` | 2 | 60 |
| `EnemyFrenzyQueue` | 3 | 3, 5 |
| `AreaParserTaskNum` | 10 | 1 |

  The other 8 give a longer change or none: `EnemyFrenzyBuffer`, `AreaPointer`, `EntrancePage`, `JoypadOverride`, `GameTimerExpiredFlag`, `OperMode`, `VRAM_Buffer_AddrCtrl`, `GamePauseStatus`.
* On `P`, every other value of each of the 184 bytes the entry frame reads, one byte at a time: he enters with a timer other than the real one only in two ways. The screen's page byte from 129 gives the shorter timer. A frame that ends on the pixel `z` of [The change out of the side pipe](d-1-SideTransition.md) leaves the timer as it was: writing `x`, or writing the screen's left edge, which pushes him there. With the page byte from 1 to 128 he does not enter. On `z` with 5 written in the timer on `P`, the change takes 127 = 122 + 5.
* The screen on an even page with Mario on the same page: he enters, 174. On an odd page he does not enter, because the mouth is in the block buffer of the even pages.
* 42 real entries, 0 to 20 more frames on the block or on the floor, all at `x₀`: all take 282 and satisfy (H1) to (H4).
* The TAS's own entry state: control after 282 frames, (H1) to (H4) hold, it reads only `R`, and 23 bytes of `Rvar` differ from `T`.

## Why the shorter states are not reached

Read from the code and measured on real runs. None of this is in Lean.

* **The screen's page.** When the room starts, the screen's page comes from `EntrancePage`, which is 0 for this room. The scroll lock is on before control comes in the room, and the screen does not scroll while it is on. Measured on a real run, on all 168 frames from the first control in the room to the frame before the entry: page 0, lock on. `entered` and `real` show page 0 at the 7 real entries of the check.
* **The timer.** The entry frame writes it, except on the pixel `z`. It is 0 on those 168 frames. So a value other than the two of the code needs an overwrite.
* **The routine and the task.** The entry frame sets the routine. `OperMode_Task` is the game's task during play: it has one value on those 168 frames.
* **Mario's state and height.** He has to be on the ground to enter. `Player_Y_HighPos` is the height's page, 1 on the floor.
* **The parser's bytes.** `AreaParserTaskNum` starts when the screen has moved 32 px. `EnemyFrenzyQueue` is set by a level object while the parser runs. Both are 0 on those 168 frames.

## Assumptions (not proved in Lean)

* (H1), (H2), (H3): the first 160 frames for an arbitrary entry. Nothing proves for all states that the timer goes down once per frame, that no frame runs over, and that `Rfix` keeps its values. Only the 20 states, 42 real entries and the TAS's state were run. The reasons from the code, not checked in Lean: the pipe's routine runs every frame and lowers the timer once, and the collision routines return at once while the pipe's routine runs.
* (H4): the values of `Rvar`. `decided` covers only the values of `T`, and `entryStates` the values of the 20 states. Real runs have other digits and random bytes, so without (H4) they are not covered. These bytes are read and branched on, so tracking cannot free them. The support for (H4) is the measurement above, which changes one byte at a time, and the real entries above.
* That `Rfix` has `T`'s values in every real run. `AreaPointer` and `EntrancePage` come from the room's level data, measured at the first control in the room. Sound effect bytes are not excluded by a proof; the measurement above shows that no single value changes the length.
* That the screen is on the first page at every real entry, and that a real entry's `x` is not a multiple of 16 ([The change out of the side pipe](d-1-SideTransition.md)). The first is the reasoning above. `every_entry` needs neither by name: the 2 states with the shorter timer satisfy (H1) but not (H2) and (H3) at frame 160 (measured), as they must.
* That real runs have no six objects close together. The room has no enemies. In the 6 states run, overrun gives 282 or more.
* The game timer at 000 with Mario alive: the change then gives no control. This is an exception to the +282, on the later side.
* No input only. All inputs were run only from `E`, with the hypothesis `GMerge`, on [The change out of the side pipe](d-1-SideTransition.md). Start and Select are not covered.
* Overwritten states are not shown reachable.
* [The whole route](0-1-Route.md) does not use this theorem: its `change₂` comes from [the first frames](d-2-2-SideChangeBound.md) and [the last frames](d-2-3-SideChangeEnd.md) of the change. `every_entry` and `no_control_before` give the exact length for a run that satisfies (H1) to (H4), and nothing here shows that every run does.
* Frames are the emulator's frames. See [Emulator](../docs/emulator.md).

**Files.** `Theorems/SideTransitionAll.lean`, private `Proof/SideTransitionAll.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta side-all-check                   # the sets and the check (true, about 5 s; about 16 s in all)
.lake/build/bin/smbrta side-all-bytes 160 122           # every value of each byte from T (0 in the output: no control)
.lake/build/bin/smbrta side-all-few 0 282               # from E: ten values of each byte, then every value of a byte that changes the length
.lake/build/bin/smbrta side-all-before                  # the frame before the entry: the values that enter with another timer (about 40 s)
.lake/build/bin/smbrta side-all-real                    # 42 real entries against (H1) to (H4), the vertical pipe's states, six objects (about 27 s)
.lake/build/bin/smbrta side-all-movie FM2               # a movie's entry against (H1) to (H4)
```
