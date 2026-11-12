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

Lean: `Run`, `Base`, `Changes`, `Run.pipeAt`, `Run.pipeOne`, `Run.roomCtl`, `Run.roomEnter`, `Run.atCtl`, `Changes.b₁_lt_a₂`, `Run.change₁`, `Run.change₂`, `Run.hE`, `Run.hT`, `Run.hc`, `Run.zero`, `Run.still`, `Run.s_zero`, `Run.ph_zero`, `Run.hD`, `Run.hL`, `Run.start`, `Run.atCtl₀`, `Run.entry₁`, `Run.upStart₁`, `Run.pipeStart₁`, `Run.roomStart`, `Run.inRoom`, `Changes.roomAt`, `RoomChecks` and `level_ge_of_parts` in `Theorems/Route.lean`, and the private `route_1_1`. `#print axioms route_1_1` shows no `sorryAx`; it shows the axioms of `native_decide`.

## The assumptions

All are fields of `Run`, so none is hidden. The page of each part explains its fields.

| part | field | what it says | checked on |
|---|---|---|---|
| a | `pipe.enter`, `clean`, `tiles`, `edge`, `moved` | an entering frame is on real machines, those of `base` (`pipe.fm t = base.seq (ixOf gap t)` is a definition; that it starts in control is proved: `Pipe.startE`, `Run.pipeStart₁`); each instruction up to the write is `Clean`, each read of the right foot `TilesOK`; up to the write it neither stores the position at the screen's edge nor bumps a block with the head; `P₂` is the position at the end of the move (`PlayerSubs`) | 68,311 real frames, 177 entries ([One whole frame: who writes the routine byte](a-5-2-PipeWrites.md), [The position at the end of the move](a-5-9-MoveEnd.md)) |
| a | `pipe.opening` | each of the first 32 counted frames is a step of the opening's model (`hstep`, the move by 16·v, the air counter with the measured jump lengths); the bound at the end of frame 32 is proved from it (`Run.pipeOpenB`), and no bound before it is needed | 32 TAS frames, 9,600 frames of 300 own runs ([The opening on real frames](a-5-4-OpenFrames.md)) |
| a | `pipe.own` | the frames 1 to `E` are read from their own machines; the speed at control is 0 is proved (`Run.still`) | 434,206 real frames ([The frames up to the pipe, read from the machines](a-5-5-PipeFrames.md)) |
| a | `pipe.lags` | the counted frames are frames of `base`: the counted frame `t` is frame `ixOf gap t`, the counted frame 1 is frame 1 (a definition; `Run.pipeAt`); each instruction of every frame from control to the entry, counted or not, is `Clean`; each counted frame ends in control; a frame not counted ends paused (`lags.paused`), and its instructions do not write the pause byte through an index or a pointer (`lags.keeps`). Proved: each frame starts in the idle loop (`Lags.starts`), and a frame not counted does not call the mode's routine, keeps the three values and ends in control (`lag_check`, `pause_check`) | 193,149 real frames, 134 entries ([Every frame from control to the pipe starts in the idle loop](a-5-5-3-2-StartRun.md)), 167,271 real frames not counted in scope ([Frames not counted, up to the pipe](a-5-5-3-LagFrames.md)), 51,711 frames not counted ([A frame that ends paused does not call the mode's routine](a-5-5-3-3-LagPause.md)) |
| b | `base.dA`, `dB`, `chg.ha₁`, `hb₁`, `ctlBy₁` | which machines of `base.seq` are the entry and control; `a₁` is the first machine from frame 1 on without control (a definition, `Base.a₁`; `dA` bounds it); `b₁` is the first machine from `a₁` on with control (a definition, `Base.b₁`; `dB` bounds it; `ctlBy₁`: control at `a₁ + dB`); `ha₁`, `hb₁`: the counts without `lag` at `a₁`, `b₁` | `route-check` on the two runs below |
| b | `chg.entryRest₁` | at the entry: the 56 bytes of `EntryKeep.restNames` (the idle loop, the pipe's timer and the other 72 bytes come from `title`, `upClean₁`: `Run.entry₁`; that each frame starts in control is proved by `Run.upStart₁`) | 437 entries ([The change into the room without `fall`](b-3-2-PipeChangeEnd.md), [The state at the vertical pipe's entry, from the title](b-3-4-EntryKeep.md)) |
| b | `chg.upClean₁` | each instruction of those frames is `Clean`, with the 70 bytes of `EntryKeep.held` and the pipe's timer protected | the same runs; a run that fills some object slots through an index before the entry is outside the theorem |
| b | `chg.places₁` | on the pipe's frames, at each place of the table, the dot is under the bound and the machine has a row of the place | every frame of the pipe of 437 runs, three kinds of inputs. Not proved |
| b | `chg.quiet₁` | at the exit no pause sound, and the song and the screen buffer are rows of the tables | fails after Start on the pipe's frames (129 of 437); true on the runs with no Start there |
| b | `chg.noStart₁` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| b | `chg.paused₁` | a `lag` frame of the change ends paused (the low bit of `GamePauseStatus` is set) | 995 + 823 `lag` frames with Start, pauses on the TAS ([A `lag` frame of the change into the room](b-3-3-LagPaused.md)). Not proved |
| b | `chg.time₁` | at the exit of the first change the sound's pause flag is 0 and the game timer is not 000; `b₁` is the first control by its definition; that `left₁` is not 0 before control is proved | 15 entries × 3 kinds, 615 runs, the TAS ([The change into the room without `fall`](b-3-2-PipeChangeEnd.md)); it fails with a pause in the pipe, where `quiet₁` fails too |
| c | `room` | the frames in the room: each frame is `Clean`, or stops him and is `ReadFrame`; the frames, the vertical state and the stored speed are read from machines (`read_vs`, `read_ab`); the entry frame enters on the real machines (`enters`); `P(E)` is read at the frame's end (`read_PE`); the position there comes from the walks `SideEntryEnd`, `SideEntryRest`; its start (with the screen's bytes), `Clean`, tiles and no head's collision come from `RoomMap` through `Run.roomEnter`. The room's machines are those of `base` from frame `b₁` on (a definition: frame `n` ends at `seq(b₁ + (n − C))`), so its first machine is the machine at control in the room (`Run.roomCtl`), and its entering frame is the frame `b₁ + (E − 1 − C)` of the room (`Run.roomEnter`) | the TAS and real runs ([Joining the bonus room](c-5-RoomJoin.md), [A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md)) ([The block map in the room](c-7-12-RoomMap.md), [The side pipe's entry: one whole frame](c-7-16-SideFrame.md)) |
| d | `base.dR`, `d₂`, `chg.ha₂`, `hb₂`, `ctlBy₂` | `a₂` is the first machine after `b₁` that has left the player's routine, `b₂` the first with control after it (definitions, `Base.a₂`, `Base.b₂`); bounds on the frames to them; the counts without `lag` at `a₂`, `b₂` | `route-check` on the two runs below |
| d | `chg.entry₂` | 16 bytes at the entry are as in a reference (the routine, the player's vertical position, the screen's buffer, the sound, the level's number); the room gives the rest (`ScreenPage.entry_rest`) | the walk of every frame in the room knows 78 of the 90 bytes of `Entry2` at the end of the entry frame ([The screen's page in the room, and the long timer](d-2-4-ScreenPage.md)) |
| d | `chg.roomSites` | `SiteOK` on each instruction in the room; `Room` comes from the rows of the time of the first change (`Changes.roomAt`), and that he stays in the player's routine up to the entry from the definition of `a₂` | 130,030 real frames and overwritten runs ([The screen's page in the room, and the long timer](d-2-4-ScreenPage.md)) |
| d | `chg.noStart₂` | no Start on the frames of the game core after the pipe | a condition on the inputs; true on the TAS |
| d | `chg.quiet₂` | no pause sound running at the exit | fails after Start on the pipe's frames ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)); true on the runs with no Start there |
| d | `chg.paused₂` | a `lag` frame of the change ends paused | 46,829 frames of 264 runs with Start on the pipe's frames ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)). Not proved |
| d | `chg.time₂` | the game timer is not 000 at the exit (the sound's pause flag is not needed) | 132 real runs and 75 with Start ([The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md)); that `left₂` is not 0 before control is proved |
| e, f | `pole` | the one-frame form above ground (`frames`), the collisions near the base, the frame that touches the pole (`touches`, `tiles`, `edge`, `moved`; `keep.noStore`: the frames before the touch write no routine, mode or task byte by its address; the last frame of `keep`, the walk of the whole frame `PoleFrame`), the castle flag. Its frames up to the touch are those of `base` from frame `b₂` on (a definition in `keep`: `all n = seq(b₂ + n)`), so its first machine is the machine at control (`Run.atCtl`) | real runs ([Above ground: the frames from control, one by one](e-2-SurfaceFrames.md), [Touching the pole on real frames](f-6-1-PoleEntryRule.md), [From control to the castle](f-5-PoleJoin.md)) |
| all | `clock`, `z₁`, `z₂` | the kind and the counters of every frame: the rule on one frame, and which frame is in which part | every frame of 7 runs, one with pauses, and of the TAS ([From the castle to 1-2](g-1-CastleToLevel.md)) |
| all | `title` | the machine after the frame on which Start is pressed on the title: the idle loop, and 52 bytes that the run reads before it writes them and the pause sound's buffer, those of a reference machine. No Start on frame 0 in the game core (Start before it may pause the game). Frame 0 is the frame before the first control. From these, frame 0 begins with the timer at `t0` and the phase 2, and the speed at control is 0 (`Run.zero`, `Run.still`; these two do not use the condition on frame 0) | the TAS and 339 real runs: Start after any frames of the title, any buttons on the title, A with Start, pauses in the game core, the title after a game over, a reset during a game (`title-check`) ([From Start on the title to control](0-5-3-TitleStart.md)) |
| all | `read₀` | the counters of `clock` before frame 0 are those of the machine when frame 0 begins | how the sequences are made |
| all | `base` (`seq`, `inp`, `next`) | one sequence of real machines for the whole run, numbered as `clock` numbers the frames; `pipe`, `room`, `pole` and `chg` take their machines from it | holds for any run by how the sequence is made |
| all | `flag`, `L` | the condition `Good` on the real machine just after the castle entry (task 2, the flag's height, `T`, `c`), no Start up to `L`, the level number changed after frame `L` | the rule on every frame and task 5 are proved ([The star flag's rule after the castle entry](g-2-1-FlagRule.md)); the condition was checked on the TAS, the late touch, real fireworks, random inputs with no Start, and set timers |

`E = C_s + c + j`, the timer's formula and the grid's formula are no longer fields of `Run`. They are proved from `clock` (`Run.hE`, `Run.hT`, `Run.hc`), with the timer and the phase before frame 0 from `title` and `read₀` (`Run.zero`, `Run.s_zero`, `Run.ph_zero`). `D ≥ 33` and the formula of the level change are proved from `flag` (`Run.hD`, `Run.hL`). `change₁` and `change₂` are no longer fields either. They are proved from `chg` (`Run.change₁`, `Run.change₂`). `level_ge_of_parts` also uses `2 ≤ q`, computed from the game's value, and the checks on the ROM `pipe_end`, `side_bound`, `side_end`, `side_start`, `side_ctl`, `room_start`, `RoomChecks` (`screen_facts`, `screen_timer_same`, `screen_rt`, `pipe_end`, `screen_start`), `flag_checked` and `title_check`, and that the star flag's delay is at least 6, which are private theorems and not assumptions.

`route_1_1` does not use `Merge`, `GMerge`, `Cond` or H3: they are neither fields of `Run` nor arguments of the theorem. It does not use that six objects stay apart either. These belong to the theorems on the exact length. But a `lag` frame is assumed to end paused (`paused₁`, `paused₂`), so a run with a `lag` frame in a change that is not a pause (such as the frame after one that runs over) is outside the theorem. On real runs the only frame of a change that runs over is the RAM clear, and the frame after it is the counted `setup` frame.

By the form of `Run`, these runs are not in the theorem:

* A run that does not take the two pipes. That walking is slower is outside this theorem.
* A big Mario, or a run with a power-up. A power-up stops the game for 59 frames, and the arithmetic is in `level_ge_of_late`; it is not joined yet.
* A run with an enemy near the pole, or one that goes over the pole and comes back.
* A run whose entering frame, up to the write, stores the position at the screen's edge or bumps a block with the head (`pipe.edge`).
* A run where a frame above ground before the touch writes the routine, the mode or the task: a power-up, an injury, a death, a pipe, the vine, the axe, an area change, or an earlier touch (`pole.keep.noStore`).
* A run whose touching frame, before the write, comes into the pole's range by the edge store or by a head bump (`pole.edge`).
* A run with a counted frame between control and the vertical pipe that ends out of control: a growth, an injury, a death (`pipe.lags.ctl`).
* A run that, before the vertical pipe, fills some object slots through an index (enemy slots 3 and 6, the fireballs, blocks 2 and 3, and others; `chg.upClean₁`).
* A run with Start on the frames of the game core after the vertical pipe (`chg.noStart₁`), with a pause sound, or a song or screen buffer not in the tables, at its exit (`chg.quiet₁`), with an enemy loaded or a parser column not in the rows during the pipe's frames (`chg.places₁`), or with fire Mario at the entry (`chg.entry₁`, `chg.roomStart`).
* A run with Start after the castle entry (`flag`). A pause only delays (80 frames for a pause of 80 frames), but that is not in Lean.
* A run with Start on the frames of the game core after the side pipe (`chg.noStart₂`), or with a pause sound running at its exit (`chg.quiet₂`). A pause there only delays control on the runs measured, but that is not in Lean.
* A run with a `lag` frame in a change that does not end paused (`chg.paused₁`, `chg.paused₂`).
* A run whose machine after the press does not meet the condition (`title.press`). Start and pauses before control are in.
* A run that does not meet `chg.entry₂` at the side pipe: the hurry-up music plays, a fireball is alive, a block object is alive, or the entry frame runs over. For the music, a theorem of its own shows that 1-2 does not start before frame 1748 ([Runs with the hurry-up music](0-6-4-HurryMusic.md), under the hypotheses `start`, `ctl`, `clean` and `below` on the first frame that starts the music and the frames in control before it). 1-1 has only one power-up before this pipe, but that is not in Lean.

## The two changes (`chg`)

`base` has one sequence of real machines. `seq n` is the machine when frame `n` begins, so `seq (n + 1)` is what frame `n` leaves, as in `clock`. `r(n)` counts the frames before `n` that are not `lag` frames (`seen`).

```
seq(n + 1) = frame(seq n, inp n)
r(a₁) = E_a + 1,   r(b₁) = C_r + 1,   r(a₂) = E_b + 1,   r(b₂) = C_s + 1
entryRest₁ : Rest(seq a₁)                 b₁ = firstCtl(seq, a₁, dB)   ctlBy₁ : ctl(seq (a₁ + dB))
a₁ = the first n with 1 ≤ n ≤ 1 + dA and ¬ctl(seq n)      upClean₁ : 1 ≤ n < a₁ → ∀ j, Clean(trₙ(j))
a₂ = the first n ≥ b₁ with rt(seq n) ≠ rt(r)      b₂ = the first n ≥ a₂ with ctl(seq n)      ctlBy₂ : ctl(seq(a₂ + d₂))
entry₂ : EntryRest(seq a₂)
roomSites : b₁ ≤ n < a₂ → ∀ j, SiteOK(trₙ(j))
paused₁ : a₁ ≤ n < b₁ ∧ kind(n) = lag  →  Paused(seq(n + 1))
time₁ : a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  Time(seq n)
places₁ : a₁ ≤ n < b₁ ∧ inPipe(seq n)  →  ∀ j, Places(trₙ(j))
noStart₁ : a₁ ≤ n < b₁ ∧ coreFrame(seq n)  →  inp n has no Start
quiet₁ : a₁ ≤ n ≤ b₁ ∧ ExitAt(seq n)  →  Quiet ∧ Song ∧ Shape (seq n)
paused₂ : a₂ ≤ n < b₂ ∧ kind(n) = lag  →  Paused(seq(n + 1))
noStart₂ : a₂ ≤ n < b₂ ∧ coreFrame(seq n)  →  inp n has no Start
quiet₂ : a₂ ≤ n ≤ b₂ ∧ ExitAt(seq n)  →  Quiet(seq n)
time₂ : a₂ ≤ n ≤ b₂ ∧ ExitAt(seq n)  →  Timer(seq n)
```

The parts take their machines from `base`, so the old links of `Run` are theorems:

```
pipe.fm 1 = seq 1                                            Run.pipeAt      (ixOf gap 1 = 1, a definition)
room.fm C_r = seq b₁                                         Run.roomCtl     (room.fm n = seq(b₁ + (n − C_r)), a definition)
b₁ < a₂                                                      Changes.b₁_lt_a₂ (Room(seq b₁), entry₂, RoomChecks)
k = b₁ + (E_b − 1 − C_r),  b₁ ≤ k < a₂,  room.fm(E_b − 1) = seq k     Run.roomEnter   (r(a₂) − r(b₁) ≤ a₂ − b₁: seen_le_add)
pole.seq 0 = seq b₂                                          Run.atCtl       (keep.all n = seq(b₂ + n), a definition)
1 ≤ E_a                                                      Run.pipeOne     (pipe.fm 0 = seq 0; frame 0 ends in control, an entry ends with the pipe's routine)
```

From these:

```
E_a + 91 ≤ C_r                                               Run.change₁, by PipeRun.bound with pipe_end
a₁ ≤ n < b₁ → left₁(seq n) ≠ 0                              Changes.first₁, from time₁ and the theorem Changes.ctlFirst₁
Room(seq b₁)                                                 Changes.roomAt, from the rows of the time and screen_start
Entry2(seq a₂)                                               ScreenPage.entry_rest, from Room, SiteOK and entry₂
timer(seq a₂) ≥ 160                                          ScreenPage.entry_long, from Room and RoomChecks
StartAt(room.fm room.C)                                      Run.roomStart, from pipe_end and room_start
─────────────────────────────────────────
a₂ ≤ n < b₂ → left₂(seq n) ≠ 0                              EndRun.firstF, from time₂ and the definition of b₂
E_b + 282 ≤ C_s                                              Run.change₂, by EndRun.bound with side_bound and side_end
```

`left` is read at the frame boundary. A frame whose routine runs over ends in the middle of the routine, and the next frame is the `lag` frame.

**What a `lag` frame does to `left`: nothing.** `keep₁` and `keep₂` are no longer assumed: from a `lag` frame ending paused (`paused₁`, `paused₂`) the check on the ROM proves that `left` does not fall. The measurements below are the earlier ones. In each change, among the frames where the interval timer's phase stays, `left` falls on one frame only, and that frame is `setup`. It is counted, and `z₁`, `z₂` are its number. On every other such frame `left` stays. `change-scenes` shows this from real entries, for no input, random inputs, Start pressed twice, and six objects written at a frame so that frames run over:

| change | runs | frames | runs that ran over | `lag` frames | `lag` frames where `left` falls | frames where `left` falls by 2 or more | least frames to control, without `lag` |
|---|---|---|---|---|---|---|---|
| into the room | 237 | 24,767 | 67 | 3,200 | 0 | 0 | 91 |
| out of the side pipe | 356 | 125,628 | 54 | 26,176 | 0 | 0 | 282 |

Not covered:

* Frames ran over only on states with objects written in. On the runs without written states, the only such frame in a change is `setup`, apart from pauses.
* Six objects written during the last 122 frames of the change out of the side pipe did not make a frame run over. There the `lag` rule was seen only with pauses.

These fields are hypotheses on single frames, and they are not proved. `pipe`, `room`, `pole` and `chg` take their machines from `base`, so they are tied by definition. Not tied: the kinds of `clock` meet the machines only at frame 0 (`read₀`), after the castle entry (`flag`), in `paused₁`, `paused₂`, and through the counts `ha₁`, `hb₁`, `ha₂`, `hb₂`; and `pole.seq` after the touch (`atCastle`, the castle flag of `direct`, `other`) is not read from `base`.

## The assumptions are not empty

`route-check` reads the numbers of `Run` from real frames.

| run | control changes | touch | castle | T | E + T | 1-2 |
|---|---|---|---|---|---|---|
| the TAS | 368, 459, 570, 852 | 1092 | 1218 | 370 | 1588 | 1748 |
| the TAS to 1089, then Left, A, A, A | 368, 459, 570, 852 | 1093 | 1219 | 369 | 1588 | 1748 |

Both satisfy every numeric assumption, and `L` equals the formula. `route-check` also reads `chg`: `a₁, b₁, a₂, b₂` = 369, 460, 571, 853; without `lag`, less one, they are 368, 459, 570, 852; `left` at the entries is 91 and 282, and both conditions hold; `z₁, z₂` = 418, 732; no other frame has the phase still; no frame takes 2 or more off `left`. It also checks the links: frame 1 is counted, and the room's entering frame `b₁ + (E_b − 1 − C_r)` is 570 = `a₂ − 1` on both runs. With pauses at 100 (before the vertical pipe), 380, 416, 450, 575, 730 and 845 it is `a₂ − 1` too. `changes-check FM2 pause F D` gives the same counts for pauses at 380, 416, 450, 575, 730 and 845, with 50 or 60 `lag` frames. Start is ignored on some frames of a change; there the movie goes out of step, and the check ends with exit 1 before the second change is done. The rule of `clock` holds on every frame of both (a working program). The structure above ground was checked on these runs by `pole-join-check`. The room's structure was checked on the TAS by a working program that is not in the repository. No Lean term of every field was built from the TAS.

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
