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
X₁ ≥ 91                                                        assumed (part b)
P₂ ≥ 111                                                       room_join (part c)
X₂ ≥ 282                                                       assumed (part d)
(g ≥ 234 ∧ W ≥ 132) ∨ (240 ≤ g ≤ 241 ∧ W ≥ 126) ∨ (g ≥ 242 ∧ W ≥ 125)    pole_touch_castle (parts e, f)
E = P₁ + X₁ + P₂ + X₂ + P₃ + W + j                             Run.hE (from the rule of clock)
401 ≤ T + ⌈P₁/24⌉ + ⌈P₂/24⌉ + ⌈P₃/24⌉                          Run.hT (from the rule of clock)
─────────────────────────────────────────
E + T ≥ 1588 + j                                               sum_ge
(c_E + E) mod 21 = (3 + j) mod 21                              Run.hc (from the rule of clock)
E + T + D + 107 + ((c_E − T − D) mod 21) ≤ L,  D ≥ 33          assumed
─────────────────────────────────────────
L ≥ 1748 + j                                                   level_ge_of_parts
```

Lean: `Run`, `Run.hE`, `Run.hT`, `Run.hc` and `level_ge_of_parts` in `Theorems/Route.lean`, and the private `route_1_1`. `#print axioms route_1_1` shows no `sorryAx`; it shows the axioms of `native_decide`.

## The assumptions

All are fields of `Run`, so none is hidden. The page of each part explains its fields.

| part | field | what it says | checked on |
|---|---|---|---|
| a | `pipe.rule` | an entry follows the collision routine | the routine on every state near the pipe; the link to frames is assumed |
| a | `pipe.openP`, `openB`, `speed`, `next` | the bound of the opening and the frames after it | [Entering the vertical pipe](a-4-PipeEntry.md) |
| b | `change₁` | the change takes at least 91 frames | 77 entry states; every entry state only under four assumptions ([What decides the change into the bonus room](b-2-1-PipeTransitionAll.md)) |
| b | | every entry state, the last 41 frames | for every value of the bytes that differ, under conditions at frame 50 ([A run with unknown bytes](b-2-3-TaintRun.md)). Not joined to `change₁` |
| c | `room` | the frames in the room | the TAS and 4501 real runs ([Joining the bonus room](c-5-RoomJoin.md)) |
| d | `change₂` | the change takes at least 282 frames | first 160 frames for any inputs under a condition on the entry ([The first frames of the change out of the side pipe](d-2-2-SideChangeBound.md)); the last 122 on single-frame hypotheses. Not yet joined to `Run` |
| e, f | `pole` | the frames above ground, the collisions near the base, the castle flag | the TAS and 4 real runs ([From control to the castle](f-5-PoleJoin.md)) |
| all | `clock`, `z₁`, `z₂` | the kind and the counters of every frame: the rule on one frame, and which frame is in which part | every frame of 7 runs, one with pauses, and of the TAS ([From the castle to 1-2](g-1-CastleToLevel.md)) |
| all | `hD`, `hL` | the fireworks, the frame of the level change. These still state results about the whole run | real frames of the listed states |

`E = C_s + c + j`, the timer's formula and the grid's formula are no longer fields of `Run`. They are proved from `clock` (`Run.hE`, `Run.hT`, `Run.hc`). `level_ge_of_parts` also uses `2 ≤ q ≤ 90`, computed from the game's value.

By the form of `Run`, these runs are not in the theorem:

* A run that does not take the two pipes. That walking is slower is outside this theorem.
* A big Mario, or a run with a power-up. A power-up stops the game for 59 frames, and the arithmetic is in `level_ge_of_late`; it is not joined yet.
* A run with an enemy near the pole, or one that goes over the pole and comes back.

## The assumptions are not empty

`route-check` reads the numbers of `Run` from real frames.

| run | control changes | touch | castle | T | E + T | 1-2 |
|---|---|---|---|---|---|---|
| the TAS | 368, 459, 570, 852 | 1092 | 1218 | 370 | 1588 | 1748 |
| the TAS to 1089, then Left, A, A, A | 368, 459, 570, 852 | 1093 | 1219 | 369 | 1588 | 1748 |

Both satisfy every numeric assumption, and `L` equals the formula. The rule of `clock` holds on every frame of both (a working program). The structure above ground was checked on these runs by `pole-join-check`. The room's structure was checked on the TAS by a working program that is not in the repository. No Lean term of every field was built from the TAS.

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
.lake/build/bin/smbrta pole-join-check FM2 1089 02808080
.lake/build/bin/smbrta touch-search-at FM2 1085 80 8  # the position moved: touch to castle per frame
```
