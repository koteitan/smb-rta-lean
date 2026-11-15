[← Back](README.md) | [English](0-5-2-1-CastleJoin.md) | [Japanese](0-5-2-1-CastleJoin-ja.md)

# Above ground: the clock's `lag` frames and the frames that end paused

**Claim.** Above ground, suppose that each frame from control (`b₂`) to the castle entry `E` is a `lag` frame of `clock` exactly when it ends paused (`LagUp`, a condition on single frames). Then `clock` and `pole` count the same frames:

* the counted frame `j` of `pole` is the frame of `clock` with the count `Cs + j`; it is a frame of play for `j < g` and an `auto` frame for `g ≤ j ≤ c`;
* the castle entry `E` of `clock` is the counted frame `c` of `pole`: the machine after frame `E` is `pole.seq c`;
* the `lag` frames above ground are the frames that end paused: `E + 1 − b₂ − c` of them;
* the castle flag of `pole.atCastle` follows from `flag`.

`LagUp` is not a field of `Route.Run`. The theorems take it. `route_1_1` does not change.

`LagUp` follows from the phase of `clock` being the machine's on each frame above ground (`PhaseUp`) and from the machine's rule of the phase on each frame (`Run.lagUp_of`). That rule is proved for the frames up to the touch's frame ([one frame in control](0-5-2-1-1-PhaseFrame.md)).

## Why

`pole` counts a frame when it ends not paused (`FrameKeep.Keep`): its counted frame `j` ends at `pole.seq j = seq (b₂ + ix j)`, where `ix j` is the `j`-th frame from `b₂` that ends not paused. `clock` counts a frame when it is not a `lag` frame (`seen`). Above ground the two meet only in one number: `clock` counts `Cs + c` frames before `E` (`Segs.last`), and `c` is the number of `pole`. Which frames are `lag` frames is free. So up to now nothing said that the castle entry `E` of `clock` (where `flag` reads the machine) is the castle entry of `pole` (where `atCastle` reads the castle flag). `LagUp` ties the two ways of counting frame by frame.

## The theorems

`seq` is `base.seq`. `kind` is `clock.kind`. `r(n)` counts the frames before `n` that are not `lag` frames (`seen`).

```
LagUp        :=  ∀ n,  b₂ ≤ n ≤ E   ⟹   ( kind(n) = lag   ⟺   seq(n + 1) ends paused )

up(k)        :=  seq(b₂ + k) ends not paused                      (FrameKeep.upAt)
U(d)         :=  #{ k ∈ [1, d] : up(k) }                          (FrameKeep.upTo)
ix(j)        :=  the least k ≤ top with j ≤ U(k)                  (FrameKeep.ixOf;  pole.seq j = seq(b₂ + ix(j)))

seen_up          :  LagUp   ⟹   ∀ d,  b₂ + d ≤ E + 1   ⟹   r(b₂ + d) = r(b₂) + U(d)
up_E             :  LagUp,  g < c   ⟹   b₂ ≤ E  ∧  U(E + 1 − b₂) = c  ∧  up(E + 1 − b₂)
castle_join      :  LagUp,  g < c   ⟹   seq(E + 1) = pole.seq(c)  ∧  ix(c) = E + 1 − b₂
count_up         :  LagUp,  g < c   ⟹   ∀ j ∈ [1, c],  ∃ n ∈ [b₂, E],  seq(n + 1) = pole.seq(j)  ∧  kind(n) ≠ lag  ∧  r(n) = Cs + j
kind_up          :  LagUp,  g < c   ⟹   ∀ j ∈ [1, c],  ∃ n ∈ [b₂, E],  seq(n + 1) = pole.seq(j)  ∧  kind(n) = (play if j < g;  auto if g ≤ j)
j_up             :  LagUp,  g < c   ⟹   j = #{ i < b₂ : kind(i) = lag } + (E + 1 − b₂ − c)
atCastle_of_flag :  LagUp,  g < c,  fc.sy = sy   ⟹   castle(pole.seq(c))
```

All are `Route.Run.*` in `Theorems/Route.lean`. `g < c` is the same hypothesis as in `Run.hT` and `Run.hc`.

The proof:

* `r(b₂) = Cs + 1` (`chg.hb₂`), `r(E) = Cs + c` (`clock.seen_E`), and `E` is not a `lag` frame (`clock.runs_E`). So `r(E + 1) = Cs + c + 1`.
* `seen_up`, by induction on `d`: frame `b₂ + d` adds 1 to `r` exactly when it is not a `lag` frame, and 1 to `U` exactly when it ends not paused. `LagUp` says these are the same.
* `b₂ ≤ E`: otherwise `r(E + 1) ≤ r(b₂)`, so `c ≤ 0`; but `c > g ≥ 1`. So `U(E + 1 − b₂) = c`, and frame `E` ends not paused (`LagUp` at `E`). So `U(k) ≤ c − 1` for `k < E + 1 − b₂`.
* `ix(c)` is the least `k ≤ top` with `c ≤ U(k)`, and `c ≤ U(top)` (`pole.toCastle`). By the last line, `ix(c) = E + 1 − b₂` (`FrameKeep.nthUp_spec`).
* `count_up`: `ix(j) ≤ ix(c)`, `U(ix(j)) = j` and `up(ix(j))` (`FrameKeep.nthUp_at`). Take `n = b₂ + ix(j) − 1`.
* `kind_up`: `clock.plan` gives `kind(n) = Segs.kind(Cs + j)`: play for `Cs ≤ Cs + j < Cs + g`, `auto` for `Cs + g ≤ Cs + j` (`Segs.kind_play₃`, `Segs.kind_after`).
* `j_up`: `r(n) + #lag(n) = n` at `n = E` and `n = b₂` (`seen_add_lag`), and `c ≤ E + 1 − b₂` (`seen_le_add`).
* `atCastle_of_flag`: `flag.task_E` says the star flag's task byte is 2 after frame `E`. `castle(m)` says this byte is not 0.

## `LagUp` from the phase

[One frame in control](0-5-2-1-1-PhaseFrame.md) proves the machine's rule of the phase (`PhaseRule`: a frame keeps the phase `φ` exactly when it ends paused, and else moves it to `next(φ) = (φ + 20) % 21`) on the frames up to the touch's frame. Here it meets the clock.

```
PhaseAt(n)   :=  clock.ph(n) = phaseOf(seq n)                         (read₀ says it at n = 0)
PhaseUp      :=  ∀ n,  b₂ ≤ n ≤ E + 1  ⟹  PhaseAt(n)
PhaseName    :=  IntervalTimerControl of the names of the title is the byte φ of PhaseFrame        (a check on the ROM)

not_setup         :  ∀ n,  b₂ ≤ n ≤ E  ⟹  kind(n) ≠ setup
lag_of_phase      :  PhaseName,  b₂ ≤ n ≤ E,  PhaseAt(n),  PhaseAt(n + 1),  PhaseRule(seq n, seq(n + 1))
                     ⟹  ( kind(n) = lag  ⟺  seq(n + 1) ends paused )
phase_succ_iff    :  PhaseName,  b₂ ≤ n ≤ E,  PhaseAt(n),  PhaseRule(seq n, seq(n + 1))
                     ⟹  ( PhaseAt(n + 1)  ⟺  ( kind(n) = lag  ⟺  seq(n + 1) ends paused ) )
lagUp_of_phase    :  PhaseName,  PhaseUp,  ∀ n ∈ [b₂, E],  PhaseRule(seq n, seq(n + 1))   ⟹   LagUp
rule_up           :  the checks,  StartK(seq b₂),  Watched(seq b₂),  tc(seq b₂) = 0,  φ(seq b₂) ≤ 20,  KeepsPhase on the frames up to the touch's frame
                     ⟹  ∀ n < ix(g),  PhaseRule(seq(b₂ + n), seq(b₂ + n + 1))
lagUp_of          :  the checks,  StartK(seq b₂),  Watched(seq b₂),  tc(seq b₂) = 0,  PhaseUp,  KeepsPhase on the frames up to the touch's frame,
                     hA : ∀ n ∈ [b₂ + ix(g), E],  PhaseRule(seq n, seq(n + 1))   ⟹   LagUp
atCastle_of_phase :  the hypotheses of lagUp_of,  g < c,  fc.sy = sy   ⟹   castle(pole.seq(c))
```

The checks are `FrameKeep.keepCheckOf`, `PhaseFrame.phaseCheck`, `PhaseFrame.tcCheck` and `TitleStart.check`. `ix(g)` is the end of the touch's frame, counted from `b₂`. `StartK` and `Watched` at `b₂` come from `Run.atCtl₀` and `PoleJoin.Run.watched₀`.

The proof:

* `not_setup`: a `setup` frame has the count `z₁` or `z₂` (`Segs.kind`), and both are below `Cs`; above ground the count is at least `Cs + 1` (`chg.hb₂`).
* `lag_of_phase`: by `clock.step`, a `lag` frame keeps the phase of the clock, and a frame of play or an `auto` frame moves it to `next`. `next(p) ≠ p` for every `p`. With `PhaseAt` at both ends, the clock keeps its phase exactly when the machine keeps it, and `PhaseRule` says that the machine keeps it exactly when the frame ends paused.
* `phase_succ_iff`: the same, the other way.
* `lagUp_of`: `PhaseAt(b₂)` and the clock's phase below 21 (`CastleToLevel.Frames.ph_lt`, from `ph(0) = 2`) give `φ(seq b₂) ≤ 20`. Then `rule_up` gives `PhaseRule` up to the touch's frame, `hA` after it, and `lagUp_of_phase` gives `LagUp`.

So `phase_succ_iff` says how far the clock's rule carries the phase. If the phase of the clock is the machine's when frame `n` begins, it is the machine's when the frame ends exactly when frame `n` meets `LagUp`. From `read₀` at frame 0 the rule gives no later frame without a tie of the kinds of the clock to the machine.

## Which frame is the castle entry

`flag` reads the machine after frame `E`. `flag.task_E` says that the castle flag is up there (`castle_E`). Up to now nothing said that it is down before, so `E` could be a later frame of task 2 than the first one. `FirstCastle` says so, one state at a time:

```
FirstCastle  :=  ∀ n,  b₂ ≤ n ≤ E   ⟹   ¬castle(seq n)

castle_E        :  fc.sy = sy   ⟹   castle(seq(E + 1))
noCastle_up     :  keepCheckOf,  StartK(pole.seq 0),  Watched(pole.seq 0)   ⟹   ∀ n ≤ ix(g),  ¬castle(seq(b₂ + n))
firstCastle_of  :  the same,  hA : ∀ n,  b₂ + ix(g) < n ≤ E  ⟹  ¬castle(seq n)   ⟹   FirstCastle
E_first         :  FirstCastle   ⟹   ∀ n ≥ b₂,  castle(seq(n + 1))  ⟹  E ≤ n
c_first         :  LagUp,  g < c,  FirstCastle   ⟹   ∀ j < c,  ¬castle(pole.seq j)
```

So with `FirstCastle`, `E` is the first frame from `b₂` on that ends with the castle flag, and with `LagUp` as well, `c` is the first counted frame of `pole` with it (`pole.atCastle` says it is up at `c`).

The proof:

* `noCastle_up`: the walk of `FrameKeep` keeps the watched bits on every frame up to the end of the touch's frame, counted or not (`FrameKeep.Frames.all_watched`). The castle flag down is one of them (`FrameKeep.castle_of_watched`).
* `firstCastle_of`: `noCastle_up` up to `b₂ + ix(g)`, `hA` after it.
* `E_first`: if `n < E`, then `n + 1 ≤ E`, and `FirstCastle` says the flag is down when frame `n + 1` begins.
* `c_first`: `pole.seq 0 = seq(b₂)` (`Run.atCtl`). For `1 ≤ j < c`, `count_up` gives a frame `n ∈ [b₂, E]` with `seq(n + 1) = pole.seq(j)` and `r(n) = Cs + j`. Since `r(E) = Cs + c` (`clock.seen_E`), `n ≠ E`, so `n + 1 ≤ E`.

`FirstCastle` is not a field: the theorems take it, as they take `LagUp`. `route_1_1` does not change. On real runs the programs take `E` as the first frame that ends with the castle flag (`touchRunOf`), so `FirstCastle` holds there by this choice. On the 183 runs of [A wider condition at the castle entry](g-2-2-1-FlagWide.md) that are in `Good` at `E + 1`, this `E` meets `flag` (task 2, the flag's height, `Good`). [The rows from the touch's end to the castle](g-2-2-2-TouchRows.md) show that the first frame after the touch's end with the castle flag ends with task 2; with `FirstCastle` that frame is `E`.

## On real runs

`castle-join-check FM2` reads the kinds of `clock` from the machine as the checks of [the timer and the grid](g-1-CastleToLevel.md) do (`CastleToLevel.kindOf`: a frame whose phase stays is a `lag` frame). It runs from the machine when frame `b₂` begins and stops at the castle entry.

| run | runs | castle entries | frames from `b₂` to the castle entry | of these ending paused | `LagUp` fails | `castle_join` fails | `kind_up` fails | `j_up` fails |
|---|---|---|---|---|---|---|---|---|
| the movie | 1 | 1 | 366 | 0 | 0 | 0 | 0 | 0 |
| a pause of 45, 50 or 61 frames at every second frame from `b₂` to the castle | 552 | 552 | 230,580 | 28,548 | 0 | 0 | 0 | 0 |
| two pauses, 70 frames apart | 74 | 74 | 33,308 | 6,224 | 0 | 0 | 0 | 0 |
| random inputs, Start at random, from the movie's frames `b₂` to `b₂ + 199` | 100 | 19 | 12,290 | 2,622 | 0 | 0 | 0 | 0 |

The movie: frame 0 is the movie's frame 193 from power on. `b₂ = 853`, `Cs = 852` (no `lag` frame before `b₂`; the `setup` frames are 418 and 732), `E = 1218`, `c = 366`, `g = 240`, `j = 0`. So `E + 1 − b₂ = 366 = c` and `Cs + c = 1218 = E`. On the random runs that reach the castle `c − g` is 159 to 165 (other touches), and up to 322 frames end paused.

On the 81 random runs without a castle entry, the phase and the pause agree on every frame while the player is in control. They disagree on 4,650 frames after he has left it (a death). On 4,643 of them the game's master timer control (`TimerControl`) is not 0 when the frame begins: it stops the timers without a pause. The game sets it on a death, an injury and a change of size. None of these is on a run of `Route.Run`.

## What is not proved

* `LagUp` itself. It follows from `PhaseUp`, from `tc = 0` and the start in control at `b₂`, from `KeepsPhase` on each instruction up to the touch's frame, and from `hA` (`Run.lagUp_of`). The machine's part up to the touch's frame is proved ([one frame in control](0-5-2-1-1-PhaseFrame.md)).
* `PhaseUp`: the phase of `clock` is the machine's on each frame above ground, as `read₀` says at frame 0 and `flag` after `E`. It does not follow from the fields: above ground the kinds of `clock` are chosen with the run, and `lag_of_phase` and `phase_succ_iff` show that, frame by frame, `PhaseUp` and `LagUp` say the same thing. On the movie, with the kinds read from the machine, `PhaseUp` holds on all 1,219 frames.
* `hA`: the frames after the touch's frame up to `E` follow `PhaseRule`. No walk follows those frames. Measured on 388 runs to the castle (70,995 frames).
* `pole.atCastle` stays a field. It would be a theorem (`atCastle_of_phase`) if `PhaseUp` and `hA` were fields, but they are conditions on every frame above ground in place of one on one machine.
* `hA` of `firstCastle_of`: the castle flag is down when each frame after the touch's frame, up to `E`, begins. No walk follows those frames.
* Below ground and before the first pipe the kinds are tied only as before: `paused₁`, `paused₂` (a `lag` frame of a change ends paused), the counts `ha₁`, `hb₁`, `ha₂`, `hb₂`, and `read₀` at frame 0.

**Files.** `Theorems/Route.lean` (`Run.LagUp`, `Run.seen_up`, `Run.up_E`, `Run.castle_join`, `Run.count_up`, `Run.kind_up`, `Run.j_up`, `Run.atCastle_of_flag`; `Run.PhaseAt`, `Run.PhaseUp`, `PhaseName`, `Run.not_setup`, `Run.lag_of_phase`, `Run.phase_succ_iff`, `Run.lagUp_of_phase`, `Run.rule_up`, `Run.lagUp_of`, `Run.atCastle_of_phase`; `Run.FirstCastle`, `Run.castle_E`, `Run.noCastle_up`, `Run.firstCastle_of`, `Run.E_first`, `Run.c_first`), `Theorems/CastleToLevel.lean` (`Frames.ph_lt`).

**To reproduce.**
```
.lake/build/bin/smbrta castle-join-check FM2      # the runs above (about 140 s)
.lake/build/bin/smbrta phase-frames-check FM2     # the conditions of lagUp_of on real runs (about 115 s)
```
