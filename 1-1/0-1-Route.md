[← Back](README.md) | [English](0-1-Route.md) | [Japanese](0-1-Route-ja.md)

# The whole of 1-1: 1-2 does not start before frame 1748

**Statement.** If a run satisfies every assumption of `Run`, the frame `L` on which 1-2 starts has `L ≥ 1748 + j`. `j` counts the frames on which no timer runs, other than one in each change of area. The TAS has `j = 0` and `L = 1748`.

**This is a theorem with assumptions.** The assumptions of `Run` are not proved for every run. This page is the list of them.

Frames are numbered from the first controllable frame of 1-1. `E` counts all frames. `E_a`, `C_r`, `E_b`, `C_s`, `g`, `c` count frames without the `lag` frames (the frames counted by `j`).

```
P₁ = E_a                 the frame he enters the vertical pipe
X₁ = C_r − E_a           the change into the room
P₂ = E_b − C_r           control in the room to the side pipe
X₂ = C_s − E_b           the change above ground
P₃ = g                   control above ground to the touch of the pole
W  = c − g               the touch to the castle
E  = C_s + c + j         the frame he enters the castle
T                        the timer at E
c_E                      the interval timer's phase at E
```

How the theorems join:

```
P₁ ≥ 368                                                       pipe_no_entry (part a)
X₁ ≥ 91                                                        Run.change₁ (part b, from single frames)
P₂ ≥ 111                                                       room_join (part c)
X₂ ≥ 282                                                       Run.change₂ (part d, from single frames)
(g ≥ 234 ∧ W ≥ 132) ∨ (240 ≤ g ≤ 241 ∧ W ≥ 126) ∨ (g ≥ 242 ∧ W ≥ 125)    pole_touch_castle (parts e, f)
E = P₁ + X₁ + P₂ + X₂ + P₃ + W + j                             Run.hE (from the rule of clock)
401 ≤ T + ⌈P₁/24⌉ + ⌈P₂/24⌉ + ⌈P₃/24⌉                          Run.hT (from the rule of clock)
─────────────────────────────────────────
E + T ≥ 1588 + j                                               sum_ge
(c_E + E) mod 21 = (3 + j) mod 21                              Run.hc (from the rule of clock)
E + T + D + 107 + ((c_E − T − D) mod 21) ≤ L,  D ≥ 33          Run.hD, Run.hL (from the rule of flag)
─────────────────────────────────────────
L ≥ 1748 + j                                                   level_ge_of_parts
```

Lean: `Run`, `Changes`, `Run.change₁`, `Run.change₂`, `Run.hE`, `Run.hT`, `Run.hc`, `Run.hD`, `Run.hL`, `Run.start`, `RoomChecks` and `level_ge_of_parts` in `Theorems/Route.lean`, and the private `route_1_1`. `#print axioms route_1_1` shows no `sorryAx`; it shows the axioms of `native_decide`.

## The assumptions

All are fields of `Run`, so none is hidden. The page of each part explains its fields.

| part | field | what it says | checked on |
|---|---|---|---|
| a | `pipe.fm`, `inp`, `start`, `clean`, `tiles`, `pos` | an entering frame is on real machines and starts in control; each instruction up to the write is `Clean`, each read of the right foot `TilesOK`; `P₂` is the position at the right foot's entry | 68,311 real frames, 177 entries ([One whole frame: who writes the routine byte](a-5-2-PipeWrites.md)) |
| a | `pipe.openP`, `openB`, `speed`, `next` | the bound of the opening and the frames after it | [Entering the vertical pipe](a-4-PipeEntry.md) |
| b | `chg.a₁`, `b₁`, `order₁`, `ha₁`, `hb₁`, `ctl₁` | which machines of `chg.seq` are the entry and control | `route-check` on the two runs below |
| b | `chg.entry₁` | the condition on the state at the entry: 113 bytes, 12 bytes under a mask, the timer at least 48, the frame ended in the idle loop | 437 entries ([The change into the room without `fall`](b-3-2-PipeChangeEnd.md)) |
| b | `chg.places₁` | on the pipe's frames, at each place of the table, the dot is under the bound and the machine has a row of the place | every frame of the pipe of 437 runs, three kinds of inputs. Not proved |
| b | `chg.quiet₁` | at the exit no pause sound, and the song and the screen buffer are rows of the tables | fails after Start on the pipe's frames (129 of 437); true on the runs with no Start there |
| b | `chg.noStart₁` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| b | `chg.keep₁` | a `lag` frame takes nothing off `left₁` | the runs in the section below. Not proved |
| c | `room` | the frames in the room: each frame is `Clean`, or stops him and is `ReadFrame`; the frames are read from machines | the TAS and real runs ([Joining the bonus room](c-5-RoomJoin.md), [A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md)) |
| d | `chg.a₂`, `b₂`, `order₂`, `ha₂`, `hb₂`, `ctl₂` | which machines of `chg.seq` are the entry and control | `route-check` on the two runs below |
| d | `chg.entry₂` | the condition on the state at the entry: 90 bytes, the screen buffer, the frame ended in the idle loop; the timer comes from the room (`ScreenPage.entry_long`) | 76 of 80 sampled entries ([The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md)), and the 8 bytes more on 44 entries ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)). The ones that fail are listed below |
| d | `chg.roomOrder`, `roomStart`, `roomSites`, `roomStay` | the condition `Room` at the first control in the room, `SiteOK` on each instruction in the room, the player's routine on each frame before the entry | 130,030 real frames and overwritten runs ([The screen's page in the room, and the long timer](d-2-4-ScreenPage.md)) |
| d | `chg.noStart₂` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| d | `chg.quiet₂` | no pause sound running at the exit | fails after Start on the pipe's frames ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)); true on the runs with no Start there |
| d | `chg.keep₂` | a `lag` frame takes nothing off `left₂` | the runs in the section below. Not proved |
| d, e | `chg.first₂` | `left₂` is not 0 before control | 201 real runs ([Above ground: the frames from control, one by one](e-2-SurfaceFrames.md)) |
| e, f | `pole` | the one-frame form above ground (`frames`), the collisions near the base, the frame that touches the pole (`touches`, `pass`, `pos`), the castle flag | real runs ([Above ground: the frames from control, one by one](e-2-SurfaceFrames.md), [Touching the pole on real frames](f-6-1-PoleEntryRule.md), [From control to the castle](f-5-PoleJoin.md)) |
| e | `atCtl` | `pole`'s first machine is `chg`'s machine at control | how the sequence is made |
| all | `clock`, `z₁`, `z₂` | the kind and the counters of every frame: the rule on one frame, and which frame is in which part | every frame of 7 runs, one with pauses, and of the TAS ([From the castle to 1-2](g-1-CastleToLevel.md)) |
| all | `chg.seq`, `inp`, `next` | one sequence of real machines for both changes, numbered as `clock` numbers the frames | holds for any run by how the sequence is made |
| all | `flag`, `L` | the condition `Good` on the real machine just after the castle entry (task 2, the flag's height, `T`, `c`), no Start up to `L`, the level number changed after frame `L` | the rule on every frame and task 5 are proved ([The star flag's rule after the castle entry](g-2-1-FlagRule.md)); the condition was checked on the TAS, the late touch, real fireworks, random inputs with no Start, and set timers |

`E = C_s + c + j`, the timer's formula and the grid's formula are no longer fields of `Run`. They are proved from `clock` (`Run.hE`, `Run.hT`, `Run.hc`). `D ≥ 33` and the formula of the level change are proved from `flag` (`Run.hD`, `Run.hL`). `change₁` and `change₂` are no longer fields either. They are proved from `chg` (`Run.change₁`, `Run.change₂`). `level_ge_of_parts` also uses `2 ≤ q ≤ 90`, computed from the game's value, and the checks on the ROM `pipe_end`, `side_bound`, `side_end`, `side_start`, `RoomChecks` (`screen_facts`, `screen_timer_same`, `screen_rt`) and `flag_checked`, and that the star flag's delay is at least 6, which are private theorems and not assumptions.

`route_1_1` does not use `Merge`, `GMerge`, `Cond` or H3: they are neither fields of `Run` nor arguments of the theorem. It does not use that six objects stay apart either: a frame that runs over is a `lag` frame, which `keep₁` and `keep₂` cover. These belong to the theorems on the exact length.

By the form of `Run`, these runs are not in the theorem:

* A run that does not take the two pipes. That walking is slower is outside this theorem.
* A big Mario, or a run with a power-up. A power-up stops the game for 59 frames, and the arithmetic is in `level_ge_of_late`; it is not joined yet.
* A run with an enemy near the pole, or one that goes over the pole and comes back.
* A run with Start on the frames of the game core after the vertical pipe (`chg.noStart₁`), with a pause sound, or a song or screen buffer not in the tables, at its exit (`chg.quiet₁`), with an enemy loaded or a parser column not in the rows during the pipe's frames (`chg.places₁`), or with fire Mario at the entry (`chg.entry₁`, `chg.roomStart`).
* A run with Start after the castle entry (`flag`). A pause only delays (80 frames for a pause of 80 frames), but that is not in Lean.
* A run with Start on the frames of the game core after the side pipe (`chg.noStart₂`), or with a pause sound running at its exit (`chg.quiet₂`). A pause there only delays control on the runs measured, but that is not in Lean.
* A run that does not meet `chg.entry₂` at the side pipe: the hurry-up music plays, a fireball is alive, a block object is alive, or the entry frame runs over. By the timer, the music means far more than 1748 frames, and 1-1 has only one power-up before this pipe, but neither is in Lean.

## The two changes (`chg`)

`chg` has one sequence of real machines. `seq n` is the machine when frame `n` begins, so `seq (n + 1)` is what frame `n` leaves, as in `clock`. `r(n)` counts the frames before `n` that are not `lag` frames (`seen`).

```
seq(n + 1) = frame(seq n, inp n)
r(a₁) = E_a + 1,   r(b₁) = C_r + 1,   r(a₂) = E_b + 1,   r(b₂) = C_s + 1
entry₁ : Entry(seq a₁)                     ctl₁ : ctl(seq b₁)
entry₂ : Entry2(0, seq a₂)                 ctl₂ : ctl(seq b₂)
room : Room(seq b₁),  b₁ ≤ n < a₂ → (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r)
keep₁ : a₁ ≤ n < b₁ ∧ kind(n) = lag  →  left₁(seq n) ≤ left₁(seq(n + 1))
places₁ : a₁ ≤ n < b₁ ∧ inPipe(seq n)  →  ∀ j, Places(trₙ(j))
noStart₁ : a₁ ≤ n < b₁ ∧ coreFrame(seq n)  →  inp n has no Start
quiet₁ : a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  Quiet ∧ Song ∧ Shape (seq n)
keep₂ : a₂ ≤ n < b₂ ∧ kind(n) = lag  →  left₂(seq n) ≤ left₂(seq(n + 1))
noStart₂ : a₂ ≤ n < b₂ ∧ coreFrame(seq n)  →  inp n has no Start
quiet₂ : a₂ ≤ n ≤ b₂ ∧ ExitAt(seq n)  →  Quiet(seq n)
first₂ : a₂ ≤ n < b₂  →  left₂(seq n) ≠ 0
```

From these:

```
E_a + 91 ≤ C_r                                               Run.change₁, by PipeRun.bound with pipe_end
timer(seq a₂) ≥ 160                                          ScreenPage.entry_long, from room and RoomChecks
─────────────────────────────────────────
E_b + 282 ≤ C_s                                              Run.change₂, by EndRun.bound with side_bound and side_end
```

`left` is read at the frame boundary. A frame whose routine runs over ends in the middle of the routine, and the next frame is the `lag` frame.

**What a `lag` frame does to `left`: nothing.** In each change, among the frames where the interval timer's phase stays, `left` falls on one frame only, and that frame is `setup`. It is counted, and `z₁`, `z₂` are its number. On every other such frame `left` stays. `change-scenes` shows this from real entries, for no input, random inputs, Start pressed twice, and six objects written at a frame so that frames run over:

| change | runs | frames | runs that ran over | `lag` frames | `lag` frames where `left` falls | frames where `left` falls by 2 or more | least frames to control, without `lag` |
|---|---|---|---|---|---|---|---|
| into the room | 237 | 24,767 | 67 | 3,200 | 0 | 0 | 91 |
| out of the side pipe | 356 | 125,628 | 54 | 26,176 | 0 | 0 | 282 |

Not covered:

* Frames ran over only on states with objects written in. On the runs without written states, the only such frame in a change is `setup`, apart from pauses.
* Six objects written during the last 122 frames of the change out of the side pipe did not make a frame run over. There the `lag` rule was seen only with pauses.

These fields are hypotheses on single frames, and they are not proved. `seq` is tied to `pipe`, `room` and `pole` by frame numbers only.

## The assumptions are not empty

`route-check` reads the numbers of `Run` from real frames.

| run | control changes | touch | castle | T | E + T | 1-2 |
|---|---|---|---|---|---|---|
| the TAS | 368, 459, 570, 852 | 1092 | 1218 | 370 | 1588 | 1748 |
| the TAS to 1089, then Left, A, A, A | 368, 459, 570, 852 | 1093 | 1219 | 369 | 1588 | 1748 |

Both satisfy every numeric assumption, and `L` equals the formula. `route-check` also reads `chg`: `a₁, b₁, a₂, b₂` = 369, 460, 571, 853; without `lag`, less one, they are 368, 459, 570, 852; `left` at the entries is 91 and 282, and both conditions hold; `z₁, z₂` = 418, 732; no other frame has the phase still; no frame takes 2 or more off `left`. `changes-check FM2 pause F D` gives the same counts for pauses at 380, 416, 450, 575, 730 and 845, with 50 or 60 `lag` frames. Start is ignored on some frames of a change; there the movie goes out of step, and the check ends with exit 1 before the second change is done. The rule of `clock` holds on every frame of both (a working program). The structure above ground was checked on these runs by `pole-join-check`. The room's structure was checked on the TAS by a working program that is not in the repository. No Lean term of every field was built from the TAS.

## The closest case

The sum `E + T` has no slack: 1 less gives 1-2 at 1727. Exactly one case lowers it by 1.

```
g = 241,  W = 125   →   E = 1218,  T = 369,  sum 1587
```

`W = 125` does occur: a slow jump not moving left, with a fraction of 176/256 px or more (real frames, position overwritten). `slow_tight` excludes it: for `g ≤ 241` he moved left on the frame before, with a fraction below 176/256 px. That `W ≥ 126` then holds is the assumption `flagTight`, which is measured.

That a fall through the base's rows takes at most 3 frames (`fall`, `fallCheck`) is used here too.

From the TAS's state at 1085 with the position moved by 16/256 to 160/256 px in 10 steps, over every input of A, B, Left and Right up to 1093: every touch on 1092 and 1093 had `W ≥ 126`.

## Reproduce

```
python3 prove.py                                      # checks every theorem
.lake/build/bin/smbrta route-check FM2                # the whole route's numbers
.lake/build/bin/smbrta route-check FM2 1089 02808080  # a touch one frame later
.lake/build/bin/smbrta changes-check FM2 pause 380 60 # the fields of chg with a pause
.lake/build/bin/smbrta change-scenes FM2              # left with random inputs, pauses and frames that run over
.lake/build/bin/smbrta frames-check FM2                # the rules of clock and flag on every frame
.lake/build/bin/smbrta pipe-rule-check FM2             # the fields of pipe on real frames
.lake/build/bin/smbrta side-end-check FM2              # the condition at the exit and left after it, on real frames
.lake/build/bin/smbrta pole-join-check FM2 1089 02808080
.lake/build/bin/smbrta touch-search-at FM2 1085 80 8  # the position moved: touch to castle per frame
```
