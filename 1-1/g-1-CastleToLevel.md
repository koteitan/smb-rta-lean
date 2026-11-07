[← Back](README.md) | [English](g-1-CastleToLevel.md) | [Japanese](g-1-CastleToLevel-ja.md)

# From the castle entry to the start of 1-2

**Statement.** The level changes on the first point of a 21-frame grid at or after `E + T + D + 107`. If each part of a run takes at least as long as the TAS's part, the game timer follows its rule and the grid lies where the run's frames put it, then the level does not change before frame 1748.

The quantities, all counted in frames:

```
E            the castle entry (StarFlagTaskControl set), frame 0 = the first control of 1-1
T            the game timer at E
D            33; by the last digit of T: 1 → 34, 3 → 98, 6 → 194
c            the interval timer's phase at E
wait         (c − T − D) mod 21
L            the frame the level changes
P1, P2, P3   frames of play: in 1-1, in the bonus room, above ground up to the touch
X1, X2       the two changes of area
W            from the touch to E
j            frames on which no timer runs, other than one in each change
q, t0        the timer's period, and its value before the first tick
```

The theorem:

```
level_ge:
  hq   :  2 ≤ q
  ht0  :  t0 = 370 + ⌈368/q⌉ + ⌈111/q⌉ + ⌈240/q⌉
  hP1  :  368 ≤ P1            hX1 :  91 ≤ X1
  hP2  :  111 ≤ P2            hX2 :  282 ≤ X2
  hP3  :  (234 ≤ P3 ∧ 132 ≤ W) ∨ (240 ≤ P3 ≤ 241 ∧ 126 ≤ W) ∨ (242 ≤ P3 ∧ 125 ≤ W)
  hE   :  E = P1 + X1 + P2 + X2 + P3 + W + j
  hT   :  t0 ≤ T + ⌈P1/q⌉ + ⌈P2/q⌉ + ⌈P3/q⌉
  hD   :  33 ≤ D
  hc   :  (c + E) mod 21 = (3 + j) mod 21
  hL   :  E + T + D + 107 + wait ≤ L
  ⟹  1748 + j ≤ L
```

With the timer's numbers of the game, `hq` and `ht0` are decided, so only the other lines remain as hypotheses (private `level_ge_rom`).

The numbers of the TAS, from a run of the movie: `P1 = 368`, `X1 = 91`, `P2 = 111`, `X2 = 282`, `P3 = 240`, `W = 126`, `j = 0`, `E = 1218`, `T = 370`, `D = 33`, `c = 3`, `wait = 20`, `L = 1748`. So `E + T + D + 107 = 1728`, and the grid has the points 1727 and 1748. Lean checks that these numbers satisfy the hypotheses (private `level_ge_tas_numbers`), and so do the numbers of this page's own route (private `level_ge_own_numbers`). So the hypotheses are not contradictory.

The other theorems of the arithmetic part:

```
level_next    :  S ≤ S + wait < S + 21,  (S + wait) mod 21 = (c + E + 107) mod 21,   S = E + T + D + 107
level_mono    :  (c + E) ≡ (c' + E') mod 21  ∧  E + S ≤ E' + S'  ⟹  E + S + wait(c, S) ≤ E' + S' + wait(c', S')
sum_mono      :  Pi ≤ Pi'  ⟹  P1 + P2 + P3 + T(P) ≤ P1' + P2' + P3' + T(P'),    T(P) = t0 − Σ⌈Pi/q⌉
playN_t       :  p frames of play from sub-counter 0:  timer falls by ⌈p/q⌉
level_ge_of_late :  E = P1 + X1 + P2 + X2 + P3 + W + F,  20 ≤ F,  and hq ... hP3, hT, hD, hL  ⟹  1748 ≤ L    (no grid needed)
```

`hE`, `hT`, `hc`, `hD` and `hL` are proved from rules on one frame: see the next two sections.

What the checks prove on real frames, for the listed states only (private `castle_to_level`, by `native_decide`). `0^k` is `k` frames of no input, `I` the 64 inputs of [the castle walk](f-4-CastleWalk.md):

```
phases    :  T = 125, 21 delays d beside the block:  level(run(E_d, 0^k)) ↔ k = T + 33 + 107 + wait,  for 1 ≤ k ≤ that;  (c + E) mod 21 = 3
real      :  the route's own timer, the same;  the walk does not change T
values    :  T = 200, the same
fireworks :  T = 131, 133, 136:  the same with D = 34, 98, 194
slide     :  a touch at another height, the same
allInputs :  GMerge  →  ∀ w ∈ I^148:  level(run(E*, w)) ∧ ∀ k, 1 ≤ k < 148 → ¬level(run(E*, w[..k]))
runs      :  6 real runs with idle frames in the three areas:  every frame follows Step and plan,
             T + Σ⌈Pi/q⌉ = t0,  2 frames without timers,  (c + f) mod 21 = 3 at the end
pauses    :  a real run with a pause in each of the 5 segments:  the same, with j = 252 and 2 + j frames without timers
starts    :  Start pressed on 5 different frames of the title:  the same phase, timer and sub-counter at frame 0;
             before frame 0, s(0) = (t0, 0) and ph(0) = 2
flags     :  the castle entries of phases, real, values, fireworks:  every frame up to the level change follows FlagStep,
             task(E + 1) = 2,  lim + 30 ≤ y(E + 1),  task(L) = 5,  early(L) = T + D
flagPauses:  T = 125, a pause in task 2, in task 3, in task 4, and on the frame of the level change:  the same,  L not before the formula
```

`E*` is a real castle entry, with the timer overwritten to 8 and the music stopped, so that the chain is short.

Lean: `Theorems/CastleToLevel.lean` (`level_ge`, `Frames`, `Flag`), private `level_ge_rom`, `castle_to_level`, `castle_level_formula`, `castle_level_inputs`, `castle_level_timer`, `castle_level_flag`.

## The rule on one frame

The frames of a run are one sequence (`Frames`). `n` counts all frames. Frame `n` has a kind `k(n)`, and `s(n) = (t, sub)` and `ph(n)` are the counters when frame `n` begins.

```
k(n)     (t, sub) → (t', sub')                                       ph → ph'
play     sub − 1 = 0: (t − 1, q);  otherwise (t, sub − 1)            (ph − 1) mod 21
auto     t' = t,  sub' ≤ sub − 1                                     (ph − 1) mod 21
setup    t' = t,  sub' ≤ sub                                         ph' = ph
lag      t' = t,  sub' = sub                                         ph' = ph

start    s(0) = (t0, 0),  ph(0) = 2
```

`play` is a frame of play. `auto` is a frame on which the timers run and the play routine does not: a frame of a change, or a frame from the touch to the castle. `setup` is the one frame of each change on which the timers do not run. `lag` is any other frame on which the timers do not run: a pause, or a frame that runs over.

Which frame is in which segment is decided by the count without `lag` frames, `r(n) = #{i < n : k(i) ≠ lag}`.

```
n ≤ E  →  k(n) = lag  ∨  k(n) = plan(r(n))

plan(r) = play    r < e₁
          auto    e₁ ≤ r < c₂,  r ≠ z₁      (setup at r = z₁)
          play    c₂ ≤ r < e₂
          auto    e₂ ≤ r < c₃,  r ≠ z₂      (setup at r = z₂)
          play    c₃ ≤ r < g
          auto    g ≤ r

k(E) ≠ lag,  r(E) = last
```

The theorems. They use the order `e₁ ≤ z₁ < c₂ ≤ e₂ ≤ z₂ < c₃ ≤ g ≤ last` and `e₁ + q < c₂`, `e₂ + q < c₃` (`Segs.Ok`).

```
j = #{i < E : k(i) = lag},   T = t(E + 1),   c = ph(E + 1)

Frames.hE :  E = last + j
Frames.hT :  t0 ≤ T + ⌈e₁/q⌉ + ⌈(e₂ − c₂)/q⌉ + ⌈(g − c₃)/q⌉
Frames.hc :  (c + E) mod 21 = (3 + j) mod 21
```

The proofs:

* `hE`: every frame is a `lag` frame or not, so `n = r(n) + #{i < n : k(i) = lag}`.
* `hT`: a stretch of play has only `play` and `lag` frames, so it is `playN` (`play_stretch`). In a change the digits do not move. Each `auto` frame takes 1 off the sub-counter, and a change is longer than `q`, so the sub-counter is 0 at its end (`change_stretch`). The rest is `playN_t`.
* `hc`: `(ph(n) + n) mod 21 = (2 + #lag + #setup) mod 21` (`phase`), and there are 2 `setup` frames up to `E` (`setups`).

On real frames the kind is read from the phase and from control (`kindOf`). A phase that stays is `lag` or `setup`; a phase that moves is `play` with control and `auto` without. The Lean checks `runs` and `pauses` test this very rule (`Step`, `Segs.kind`) on every frame.

The fields hold together: for any segments there is a sequence with no `lag` frames (`Frames.noLag`).

The TAS, the run that touches one frame later, and the TAS with a pause of 45 to 66 frames put in at 36 places also follow the rule on every frame, and the three formulas hold on them (`frames-check`). A run with a death does not follow `plan`.

**Frames that run over.** With five Hammer Brothers overwritten close by, the routine can run into the next frame. Read at the frame boundary, a tick of the timer is split over two frames: `(t, 1) → (t, 0) → (t − 1, q)` or `(t, 1) → (t, q) → (t − 1, q)`. The phase does not move on the second. A frame that moves together with the frames that do not move after it follows the rule. In 3 tests of 1500 frames, 28 frames read at the boundary break the rule, and 0 taken together do. So `s(n)` is the value when the routine of the frame before has ended. On a run with nothing overwritten this equals the value read at the boundary.

## The frames after the castle entry

The sequence of frames goes on past `E`, up to the level change `L` (`Flag`). `Frames` does not change. `x(n) = (task, t, y, w, ph)` are the counters when frame `n` begins: the star flag's task, the game timer, the flag's height on the screen, its interval timer, the phase. `y` falls as the flag rises. `lim` is the height the flag rises to and `w₀` the value its task sets; both are read from the code of the ROM.

A frame that does not run leaves all the counters. A frame that runs has `ph' = (ph − 1) mod 21`. The interval timer falls when the phase wraps: `tick = w − 1` if `ph = 0` (it stops at 0), and `tick = w` otherwise.

```
task 2,  t ≠ 0      task' = 2,  t' = t − 1,  y' = y,      w' = tick
task 2,  t = 0      task' = 3,  t' = 0,      y' = y,      w' = tick
task 3,  lim ≤ y    task' = 3,  t' = t,      y' = y − 1,  w' = tick
task 3,  y < lim    t' = t,  y' = y,  (task' = 3 ∧ w' = tick) ∨ (task' = 4 ∧ w' = w₀)
task 4              t' = t,  y' = y,  w' = tick,  task' = 4 ∨ (task' = 5 ∧ w' = 0)
```

A frame with task 3 and `y < lim` can stay in task 3: the fireworks. A frame with task 4 can stay in task 4: the music. So these two only delay. A frame that runs with task 5 changes the level. It is frame `L`, which the rule does not cover.

Every frame `n` with `E < n < L` follows this rule (`FlagStep`). The other fields:

```
t(E + 1) = T,  ph(E + 1) = c       the T and c of Frames
task(E + 1) = 2
lim + 30 ≤ y(E + 1)                the flag's height at E
E < L,  task(L) = 5
```

The theorems:

```
early(n) = #{i : E < i < n, frame i runs, task(i) ≤ 3}
D        = early(L) − T

Flag.hD :  33 ≤ D
Flag.hL :  6 ≤ w₀  →  E + T + D + 107 + wait(c, T + D) ≤ L
```

The proofs (`Flag.Inv`, `inv_step`):

* `hD`: let `r = t + (y + 1 − lim) + 2` in task 2 and `r = (y + 1 − lim) + 1` in task 3. A frame that runs takes at most 1 off `r`. At `E + 1`, `r ≥ T + 33`. In task 4 it is used up, so `early ≥ T + 33`.
* `hL`: up to task 3 every frame that runs is counted, so `(ph + early) mod 21 = c mod 21`, and the frame that sets `w` leaves `ph = wait(c, T + D)`. That frame is at least `E + T + D`. In task 4, `21 w + ph` falls by at most 1 per frame. It starts at `21 w₀ + wait`, and task 5 needs `w = 0`, so it is then at most 20. With `w₀ ≥ 6` that is `106 + wait` frames, and frame `L` is one more.

`D` does not count the frames that do not run, so a pause does not change it. A pause moves `L` and leaves `D` and `wait`.

`6 ≤ w₀` is not a field: `route_1_1` computes it from the ROM (`by decide`).

On real frames the counters are read from memory (`flagOf`). The star flag's enemy slot is found by its name. A frame whose phase stays does not run (`flagLag`).

Real runs with nothing overwritten, by `frames-check`. All their frames follow the rule, and `hD` and `hL` are true. `lag` is the frames after `E` that do not run.

```
run                                       E     T    c   D    lag  L     L − (E + T + D + 107 + wait)
TAS                                       1218  370  3   33   0    1748  0
TAS, inputs 02 80 80 80 after frame 1089  1219  369  2   33   0    1748  0
TAS, 96 idle frames first                 1314  366  12  194  0    2000  0
TAS, 168 idle frames first                1386  363  3   98   0    1958  0
TAS, 216 idle frames first                1434  361  18  34   0    1937  0
```

The last three have real fireworks. A pause of `d` frames after `E` gives `lag = d` and moves `L` by `d`, with the same `D`. This was run at frames 1219, 1300, 1450, 1590, 1600, 1625, 1700, 1747, 1748, with `d` from 45 to 66, so in tasks 2, 3, 4 and on the frame of the level change. A pause before `E`, at frames 100 and 1100, gives `j = 45`, `lag = 0`, `L = 1793`. Random inputs after `E`, with Start in them, also follow the rule: 6 runs, 751 to 788 frames that do not run on the 5 that reach the level change. The sixth is still paused when the inputs end. The 6 with no Start have `L = 1748`.

With the timer overwritten at the entry, `T` = 0, 60, 100, 120, the music holds the level change back to `E + 265`. The rule and `hL` hold there too (`castle-level-check`).

The fields hold together: for any numbers with `1 ≤ lim` there is a sequence with no `lag` frames (`Flag.noLag`). With `lim = 0`, `y − 1` stops at 0 and task 3 does not end.

## How

**The frames after the entry** (from the code; `FlagStep` is its rule on one frame). On frame `E` the star flag's task reads the timer's last digit: 1, 3 or 6 sets fireworks. The next `T` frames take 1 off the timer each. One frame ends that task, and 31 frames raise the flag. The frame after that sets a timer that falls only when the interval timer runs out, so `D = 33`. Fireworks hold that frame back: one firework costs 1 frame, and each further one 32. Then 6 steps of the interval timer take 106 frames plus the delay to the next step, and on the following frame the level number changes. Together this is `L = E + T + D + 107 + wait`.

**The music.** That last task also waits for the victory music to end. On this route, at all 21 phases, the music has ended by then when `T ≥ 125`. With a small `T` it has not, and the level changes off the grid, later than the formula, at `E + 265`. The formula is a lower bound in all the cases measured, so `hL` is an inequality.

**Inputs.** The frames ignore A, B, Up, Down, Left and Right: the routine that walks into the castle overrides the buttons. All 64 inputs on every frame give the same state in `allInputs`. Run as a program from the real entry, with `T = 360` and all 513 frames, the result is the same.

**The timer's rule.** On a frame of play the sub-counter falls by 1. When it reaches 0 the timer falls by 1 and the sub-counter is set to `q`, so the timer falls by 1 every 24 frames of play. During a change of area the sub-counter falls by 1 per frame and stops at 0, and the digits do not change. A change is longer than `q`, so the sub-counter is 0 at its end. So each area ticks on its first frame of play, and `p` frames of play take `⌈p/q⌉` off the timer. That is why the sub-counter cannot differ between runs with the same `P1`, `P2`, `P3`: whatever it was when he entered a pipe falls to 0. The TAS has `⌈368/24⌉ + ⌈111/24⌉ + ⌈240/24⌉ = 31` ticks, the first on frame 0: the timer shows 400 on frame 0 and 370 at the touch. On the frame of the TAS's touch the sub-counter is 0, but the touch has already changed the routine, so no tick comes.

**Arriving later.** `p − ⌈p/q⌉` does not fall when `p` grows, so `E + T` does not fall when a part of the run gets longer (`sum_mono`). It can stay equal: `P3 = 241` has one more frame and one more tick, so the same sum 1728. Over all parts, the smallest sum is at `(368, 111, 240)` and `(368, 111, 241)`. The three cases of `hP3` are `touch_castle` of [From control to the castle](f-5-PoleJoin.md). Another touch with `P3 = 234` and `W = 132` has the sum 1728, as the TAS does (the least measured is `W = 153`). Only `P3 = 241` with `W = 125` gives the sum 1727, so `hP3` asks for `W ≥ 126` up to `P3 = 241`. From `P3 = 242` on, `W = 125` does not lower the sum; this uses `2 ≤ q`.

**The grid.** The phase falls by 1 modulo 21 on each frame on which the timers run. It is not an absolute function of the frame. Each change of area has one frame on which the timers do not run (the area's setup runs over a frame): frames 418 and 732 in the TAS, 490 and 862 on this page's route. So the phase is `(1 − f) mod 21` in 1-1, and `(3 − f) mod 21` after both changes. The phase at the first control of 1-1 does not depend on when Start was pressed on the title: it was the same for 35 presses (5 of them in Lean), and from the code the screen before 1-1 ends on a step of the interval timer. A frame on which no timer runs delays everything by 1: the frames of play and the grid move together, which is what `j` says in `hE` and `hc`. The conclusion moves by the same `j`.

**Fireworks and later frames.** `L` is the first grid point at or after the sum (`level_next`), and more frames never give an earlier one (`level_mono`). With fireworks `D` is larger, so `L` is not earlier. Measured: `T = 360` and `T = 361` give the same `L`.

**Pausing.** Measured from the real entry, with `T = 360`: Start on one frame and Start again `k` frames later moves `L` by exactly `k`, and `c` stays still during the pause. The second press works from `k = 45` on. So a pause is `j ≥ 45`. On a play frame before the touch, `(c + E) mod 21 = (3 + j) mod 21` was measured for `j` = 45, 46, 47, 50, 66. With a small `T` a pause costs more, because the music comes back later than the game: 25 more frames at `T = 140`.

**A frame that runs the game but not the timers** would move the grid without moving the sum, and one such frame would give `L = 1728`. Only a power-up, a hit or a death stops the timers while the game runs. A small Mario must first take a power-up. That freezes the game for 59 frames (measured with the routine and the timer control overwritten, not on a real power-up), so the sum is more than 20 frames later and `L ≥ 1748` holds without the grid (`level_ge_of_late`).

Frames that run over are the other case. With five Hammer Brothers close together, overwritten at the entry (the star flag kept), 60 frames ran without timers, and the level changed exactly 60 frames later than without them.

No way was found to make `E + T + D + 107` smaller than the TAS's, or to move the grid without moving the sum.

## Assumptions (not proved in Lean)

`level_ge` is proved for numbers. That a real run gives numbers with these properties is assumed:

* `hP1`, `hP2`, `hP3`: the parts of the route. They come from the other theorems of [the route](../docs/route-1-1.md), and they are joined in [The whole of 1-1](0-1-Route.md). A run that does not take these two pipes is not covered.
* `hX1`, `hX2`: [the two changes](b-1-PipeTransition.md), proved for the entry states they list. A frame that runs over counts in `j`.
* `hE`, `hT`, `hc`: in [The whole of 1-1](0-1-Route.md) these are proved from `Frames`. The assumptions are the fields of `Frames`: each frame follows `Step` and `plan`, `s(0)`, `ph(0)`, and the number of `E`. That a real run satisfies them is not proved. They are checked on every frame of 7 real runs of this page and on the TAS. Frames with a power-up, a hit or a death are not in this form; for a power-up use `level_ge_of_late`. A run restarted after a death is not covered.
* `hD`, `hL`: in [The whole of 1-1](0-1-Route.md) these are proved from `Flag`. The assumptions are the fields of `Flag`: each frame follows `FlagStep`, `task(E + 1) = 2`, the flag's height at `E`, `task(L) = 5`. That a real run satisfies them is not proved. They are checked on every frame of the listed runs. That the flag starts at the same height in every run is still read from the code; only these runs check it.
* `T` and `c` link `Flag` to `Frames` by number. `L` is a frame that begins with task 5. That the level number changes on no other frame is read from the code and seen on the listed runs. It is not a field.
* Frames that run over after `E`: measured only with five Hammer Brothers overwritten at the entry, with the flag in the first slot and in the last slot (26 and 66 such frames; a working program, not in the repository). No frame read at the boundary broke `FlagStep`. That is no proof for other frames that run over.
* The counters before frame 0 are checked for 5 Start presses.
* The formula as an equality: checked on the listed states, with no input, from one route. Every input ran from one state only, with `GMerge` as a hypothesis and with the timer and the music overwritten. From the real entry that is a program's result, not a theorem. The bound does not use it.
* The states at the pole are overwritten at the end of a real run, as in [the castle walk](f-4-CastleWalk.md). Enemies, score and other bytes of other runs are not covered.
* Start and Select are not in the input set of the theorem. Pausing is measured, not proved. Select held was measured to change nothing.

**Files.** `Theorems/CastleToLevel.lean`, private `Proof/CastleToLevel.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta castle-level-check     # the four checks (true, about 20 s), then small timers, fireworks, a pause, and every input on the real state (about 13 s more)
.lake/build/bin/smbrta frames-check FM2       # the rules of Frames and Flag on a movie's frames. Also: A HEX, pause F D, insert A K
```
