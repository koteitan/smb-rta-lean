[← Back](README.md) | [English](0-5-2-1-CastleJoin.md) | [Japanese](0-5-2-1-CastleJoin-ja.md)

# Above ground: the clock's `lag` frames and the frames that end paused

**Claim.** Above ground, suppose that each frame from control (`b₂`) to the castle entry `E` is a `lag` frame of `clock` exactly when it ends paused (`LagUp`, a condition on single frames). Then `clock` and `pole` count the same frames:

* the counted frame `j` of `pole` is the frame of `clock` with the count `Cs + j`; it is a frame of play for `j < g` and an `auto` frame for `g ≤ j ≤ c`;
* the castle entry `E` of `clock` is the counted frame `c` of `pole`: the machine after frame `E` is `pole.seq c`;
* the `lag` frames above ground are the frames that end paused: `E + 1 − b₂ − c` of them;
* the castle flag of `pole.atCastle` follows from `flag`.

`LagUp` is not a field of `Route.Run`. The theorems take it. `route_1_1` does not change.

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

* `LagUp` itself. It is a condition on single frames, measured above and not proved. `kind` is chosen with the run; `LagUp` says how to choose it above ground. It would follow from two facts: the phase of `clock` is the phase of the machine (`clock.ph n = phaseOf(seq n)`; now only at frame 0 and after `E`), and on a frame above ground the phase stays exactly when the frame ends paused (the code: the timers are skipped when the pause bit is set after the pause routine, or when `TimerControl` is not 0).
* `LagUp` is not a field of `Route.Run`, so nothing stops being a hypothesis. Made a field, it would make `pole.atCastle` a theorem (`atCastle_of_flag`), and it would join the castle entry of `flag` to that of `pole`. It is a condition on every frame above ground in place of one on one machine, so it is not made a field here.
* Below ground and before the first pipe the kinds are tied only as before: `paused₁`, `paused₂` (a `lag` frame of a change ends paused), the counts `ha₁`, `hb₁`, `ha₂`, `hb₂`, and `read₀` at frame 0.

**Files.** `Theorems/Route.lean` (`Run.LagUp`, `Run.seen_up`, `Run.up_E`, `Run.castle_join`, `Run.count_up`, `Run.kind_up`, `Run.j_up`, `Run.atCastle_of_flag`).

**To reproduce.**
```
.lake/build/bin/smbrta castle-join-check FM2      # the runs above (about 140 s)
```
