[← Back](README.md) | [English](c-5-RoomJoin.md) | [Japanese](c-5-RoomJoin-ja.md)

# Joining the bonus room

**Statement.** Let `C` be the frame of first control in the bonus room and `E` the frame Mario enters the side pipe. In every run that has the frames of the structure `RoomRun`:

```
E ≥ C + 111
```

The TAS has `C` = 459 and `E` = 570. The structure is what a real run gives: frames, positions, heights, the stored speed, the takeoff, the landing, how he leaves the block, the entry frame. Its fields are hypotheses. That real frames have them is not proved in Lean. The fields are about one frame where that could be done.

A run that lands on the left wall, jumps, and never touches the floor is covered too. On real frames it had `E` = `C` + 134 (see "Runs that stand on the left wall" below).

`P(n)` is the position at the end of frame `n`, in 1/256 px. `c_P` is the block's corner, `G_P` the position past its right end, `M_P` the left end of the pipe's mouth. `t₀` is the first frame with `P ≥ G_P`. `T` is the last takeoff from the floor before `t₀`, `s` the last low frame of that jump, `L` its landing on the block, `F` the frame the jump off the block reaches the floor. `stop(n)` means that he is slow and not far past the corner at the end of frame `n`: `Φ(n) ≤ Φ_s`, `P(n) ≤ c_P + S`.

```
no_landing   :  a jump from the floor or from the block's side still running at t₀  →  impossible
stop_short   :  stop(h),  C + 37 ≤ h ≤ t₀ ≤ C + 98  →  P(t₀) < G_P
wall_short   :  the left wall touched before C + 37,  no stop from C + 37 to t₀,  t₀ ≤ C + 98  →  P(t₀) < G_P
landed_short :  no wall touched,  no stop from C + 37 to t₀,  he landed on the block,  t₀ ≤ C + 98  →  impossible
past_late    :  t₀ > C + 98
entry_ge     :  E ≥ C + 98 + 13        (with the numbers as parameters: C + goalF + aboveF)
room_join    :  r : RoomRun  →  r.C + 111 ≤ r.E        (private, the numbers by native_decide)
```

These lemmas come from the fields about one frame. The proofs are in "What follows from the frames".

```
corner_late  :  C ≤ n < C + 37,  n ≤ t₀  →  P(n) < c_P
low_by       :  C ≤ n ≤ C + 43,  n ≤ t₀  →  P(n) ≤ c_P + S_low
floor_low    :  no wall touched,  T ≤ C + 40,  C + 37 ≤ n ≤ T  →  LowAt(n)
early_of     :  no wall touched,  T ≤ C + 40  →  the frames up to T are those of FastTakeoff
stand_gap    :  C ≤ i < j < C + 34,  standing at i and at j  →  i + 8 ≤ j
run_short    :  stop(h),  C + 37 ≤ h ≤ C + 40,  RunningSpeed(h) ≠ 0,  t₀ ≤ C + 98  →  P(t₀) < G_P
mouth_of     :  P(E) ≥ M_P
ab_clean     :  frame n + 1 follows the model  →  ab(n) = |v(n)|
```

Lean: `Theorems/RoomJoin.lean`, private `room_nums`, `room_checks`, `room_join`, `room_floor_arcs`. `#print axioms room_join` shows no `sorryAx`; it has the `native_decide` axioms.

## How

The case split is made with `cases` and `by_cases`, so it is exhaustive in Lean. Margins are how far he is short, measured by `room-join-check`.

| case | why it is short | margin (1/256 px) |
|---|---|---|
| over the block in one jump, no landing | below the threshold at most 1.5 px per frame; at the threshold or more the top speed after the 8 low frames; the longest jump comes from `arcCheck` | 1792; 97 |
| a stop from `C + 37` on | the speed is near 0, then the potential of [Reach](../0-0/0-2-Reach.md) | 225 at frame 37; 241 at frame 41 |
| no stop, the wall touched before `C + 37` | no jump is looked at: the potential from the wall frame (`wall_short` below) | 48; 96; 128; 512 |
| no stop, a takeoff after `C + 41` | at `T + 8` he is at the corner at most, then the top speed | 97 |
| no stop, no wall touched, a slow takeoff by `C + 41` | `P(s) < c_P`, then [The air speed cap](c-1-AirCap.md) with the pairs of [The height of a jump](c-2-Jump.md): `landing_bound`, `landing_later` | 65; 193 |
| no stop, no wall touched, a fast takeoff by `C + 41` | [A fast takeoff](c-3-FastTakeoff.md): moving right impossible, moving left short | |

Then, with `t₀ > C + 98`, off the block:

| he leaves by | why |
|---|---|
| a fast jump | `t₀ − 1 + 13 ≤ F ≤ E` from `dropOk`: `E ≥ C + 111` |
| a slow jump | `t₀ − 1 + 12 ≤ F`, so `E` < `C + 111` needs `E = F = C + 110`. All frames from `C + 98` to `E` are in the air below the threshold, so `P(E) < G_P + 12·1.5 px`, 1024/256 px short of the mouth |
| stepping off | `t₀ + 16 ≤ F ≤ E` from `walkOk` |

A hit on the floor with a stale stored speed has no separate case. It is a stop, and `stop_short` does not look at the jump that follows. The same theorem covers a jump from the side of the block, which the jump tables do not describe.

Three things about the corner that the collision routine does and the route page did not say:

* **Moving left is not stopped.** At a low frame past the corner, with `v < 0`, the routine stops nothing. So `LowAt` has three cases: stopped, left of the corner, moving left. Going back frame by frame, a frame moving left past the corner comes after a stop, so with no stop `P < c_P` on every low frame (`left_of_corner`).
* **The feet stop him too.** A jump that peaks just below the block's top (feet inside the block by 5 px or more, not rising) is stopped by the foot check, 1 px back per frame, past the corner height. On the emulator he was stopped at 1136/256 px past the corner. So `S` is much larger than the slack of a low frame.
* **A jump can start from the block's side.** Falling with a foot over the block and the feet less than 5 px into a row of it, he lands on that row: state "ground", at a height inside the block. The side check stops him in the same frame, and on the next frame he can jump. So the last takeoff need not be from the floor. It always comes with a stop, so with a stop from `C + 37` on the theorem needs no takeoff at all; `Approach` is asked for only when there is no stop.

The frames after a hit do not all follow `hstep`: the blocked side is masked on the next frame, and the stored speed is stale until the next frame that updates it, which then uses a larger adder. `stop` allows for that: `Φ_s` is a fraction, one frame of the largest adder and the charge for the facing direction.

## What follows from the frames

**`corner_late`.** As long as he has touched nothing, the frames of the fall are air frames (`fall_air`): he stands only after a frame that is stopped (`stand_wall`), and he is not on the floor during the fall (`fall_long`). He keeps facing right. Define `Ψ` as follows, with `a₁` the second entry of the table of adders and `g_slow = 2·a₁`.

```
V ≥ 0                     :  Ψ = V + w
256 − g_slow ≤ V < 0      :  Ψ = V + a₁
−g_slow ≤ V < 256 − g_slow:  Ψ = V + g_slow
−g_slow − a₁ ≤ V < −g_slow:  Ψ = V + g_slow + a₁
any smaller V             :  Ψ = 0
```

Moving left the adder is doubled, so a state just below 0 gains more when it turns back. The last lines count that.

`airCheck` runs every state facing right with `|v| < v_A` and `RunningSpeed` 0 and the 4 air inputs (53248 calls of `hstep`).

```
the facing stays,   Ψ' ≤ Ψ + a₁,   V − V' ≤ g_slow
```

So `16·v ≤ 16·⌊Ψ/256⌋` and `Ψ(C + j) ≤ Φ₀ + a₁·j`. With `airDist(p, j) = Σ_{i=1..j} 16·⌊(p + a₁·i)/256⌋`, `P(C + 34) ≤ P(C) + airDist(Φ₀, 34)`. The next 2 frames are `capDist` of [The air speed cap](c-1-AirCap.md). Together he is 81/256 px left of the corner.

The wall is a field about one frame. A frame before `C + 37` that does not follow `hstep` is stopped by the left wall, with `P ≤ P_w` before and after it (`WallAt`). The wall is far from the start, so the state after the first wall frame is at `C + 15` or later (`leftDist`, the bound on moving left). After the wall, `P(n) ≤ P_w + dbound(Φ_s, n − C − 15)`. This does not reach the corner before `C + 37`: the margin is 3680/256 px.

**`low_by`.** With no wall hit he is on the floor at `C + 34` (`floor_at`). The frames after it are `VFrame`: on the floor he stays or takes off; in the air the frame is `vstep`, or he is falling. By `arcCheck` and `floorArcOk`, on the 8 frames after the takeoff frame of every jump from the floor his feet are low, he is rising and in the air state, so he does not land. So from `C + 37` to `C + 43` his feet are low, and `low_at` (the collision routine with the feet low) gives `P ≤ c_P + S_low`. With a wall hit, `P_w + dbound` and the top speed are enough up to `C + 43`: the margin is 31/256 px. The frames up to `t₀` end before the entry: `t₀ < E` (`t0_lt_E`), so `vfloor` and `varc` speak of them.

**`floor_low`.** With no wall hit and `T ≤ C + 40`, he is on the floor from `C + 34` to `T`. An earlier jump would still be in its low frames at `T`, not on the floor. Floor frames have low feet, so `low_at` applies.

**`early`.** With no wall hit, `early_of` builds the frames of `FastTakeoff`. The `hstep` frames are the absence of a wall hit. The frames of the fall come from `fall_air`, the ground frames from the floor of `floor_low`, the jump frame and the air frames from `VFrame`. The air frames are the 8 low frames of the jump, before the landing on the block (`land_late`), so before the entry.

**`wall_short`.** With the wall touched before `C + 37` and no stop from `C + 37` to `t₀`, `P(t₀) < G_P` (for `t₀ ≤ C + 98`) with no look at any jump. So `Approach` is asked only of a run with no wall hit. Let `b` be the last wall frame. All frames after `b` follow `hstep`, and `P(b) ≤ P_w`, `Φ(b) ≤ Φ_s`, `b ≥ C + 15`.

```
b ≥ C + 22                   :  P(t₀) ≤ P_w + dbound(Φ_s, 76) < G_P        margin 128
b < C + 22,  facing right at b + 1 :  wall_right
b < C + 22,  another facing at b + 1 :  wall_turn
```

**`wall_right`.** Frame `b + 1` can be any frame (a jump, a ground frame, an air frame): `Φ(b + 1) ≤ Φ₁ = nxt(Φ_s)`. After it, the frames to `C + 34` are air frames: standing needs a frame that is stopped, and there is none after `b`. So `Ψ` grows by at most `a₁` per frame. Let `Q = Φ₁ + a₁·18`.

```
Φ(C + 34) ≤ Q  :  P(t₀) ≤ P_w + 16·⌊Φ₁/256⌋ + airDist(Φ₁, 18) + dbound(Q, 64) < G_P                                   margin 48
Φ(C + 34) > Q  :  V(C + 34) < 0,  −V ≥ u = Q + 1 − 2c
                  P(t₀) ≤ P_w + 16·⌊Φ₁/256⌋ + airDist(Φ₁, 9) − backD(u, 9) + capDist(64) < G_P                         margin 512
```

With `V ≥ 0`, `Φ = Ψ ≤ Q`, so on the second line he moves left. `V` falls by at most `g_slow` per frame, so on the 9 frames before he was moving left too, and he has gone back.

**`wall_turn`.** Air frames and jump frames keep the facing (`facing`). So to face anything but right he needs a ground frame with no jump by `b`. On the frame `i` before it he stands. `i` is his first stand: an earlier one gives `i ≥ C + 15 + 8` by `stand_gap`, against `i ≤ b < C + 22`. `stand_P` with `leftDist` gives `i ≥ C + 16`. Let `j = i − C`.

A stand is a frame that is stopped, so `Φ ≤ Φ_s`. To stand again he needs `−V ≥ 256·14` (`stand_fast`). Since `iterN(Φ_s, 6) < 256·14`, two stands are at least 8 frames apart. This is `stand_gap`.

There is no jump up to `b`, and after `b` he can stand only on the floor. So with no jump the height comes from `vfall`. Let `Y = 256·y + fraction`, `W = 256·vy + fraction`, and `f` the force of the fall.

```
Y(C + j) ≤ Y₀ + Σ_{l<j} (W₀ + f·l)
Y(i) ≤ that row + 255,   W(i) = 0        (stand_row)
Y(i + e) ≤ Y(i) + Σ_{l<e} f·l
```

The table `gaps` holds `(j, k)`: he does not reach the floor up to `i + k`.

```
(16, 32) (17, 32) (18, 28) (19, 28) (20, 28) (21, 25)
```

The frames up to `i + k` are air frames, so he stays below `v_A`. Let `capRamp(p, n)` be `dbound` with the speed held to `v_A − 1`.

```
P(t₀) ≤ P_w + capRamp(Φ_s, k + 1) + capDist(98 − (j + k + 1)) < G_P        margin 96 or more
```

**`run_zero`.** This field is gone. What is needed is `RunningSpeed` at a stop from `C + 37` to `C + 40`: the third condition of `J` uses it.

```
wall touched                     :  P(h) ≤ P_w + dbound: short for any RunningSpeed      margin 1280 or more
moving right at the end of the fall :  safeCheck: |v| stays below the running threshold to C + 39   RunningSpeed = 0
Φ(C + 34) at most the bound      :  the same
moving left fast at the end of the fall :  backD: P(C + 34) is small; P(h) ≤ backP, short with fastDist   margin 144
```

`safeFrom` is a small search: only the states not decided by the bound on `Φ` go on to the next inputs. A frame that does not follow `hstep` leaves `RunningSpeed` 0 (`stop_run`). A frame that follows `hstep` has `stepOk`.

**`slow_capped`, `stale`.** `ab(n)` is the stored speed that frame `n + 1` reads when it comes to the player's routine (`read_ab`). The takeoff reads it (`x_ab`). On a frame that follows the model, `ab(n) = |v(n)|` (`ab_clean`): `AtCtrl` asks it, and nothing wrote the speed before the player's routine. Every other frame leaves him stopped (`clean`). So at the takeoff `T`:

```
frame T + 1 follows the model          :  ab(T) = |v(T)|
otherwise                              :  stop(T + 1)
```

A slow jump has `ab < v_A`. In the first case `|v(T)| < v_A`. In the second, `stop(T + 1)` gives `|v(T + 1)| < v_A`, and the air speed cap starts one frame later. For a fast jump with no stop from `C + 37` on, the second case has `T + 1 < C + 37`, and then `ab < v_A` (`ab_early`). So only the first case is left, and `|v(T)| ≥ v_A`.

The air speed cap does not do the fast case: a fast jump lands on the block 13 frames after the takeoff frame, and the air speed and then `capDist` give a bound 1727/256 px past the goal.

**`mouth`.** Frame `E` is an entry on the real machines: one instruction writes the side pipe's routine (`enters`). `P(E)` is read at the frame's end (`read_PE`), as `read_P` reads the other frames. [The side pipe's entering frame: the position at its end](c-7-18-2-SideEntryEnd.md) proves that the position there is at or right of `M_P` (`InRoom.mouthE`, proved by `Route.Run.roomMouthE`), with no hypothesis on the position: one walk up to the write, and the walk of the room from there to the frame's end.

## Assumptions (not proved in Lean)

Each is a field of `RoomRun` or of a structure in it. "One frame" below marks a fact about a single frame.

* The machines are no longer fields (item 1-1-0-4): `RoomRun` takes the real frames of the whole run (`FrameKeep.RealRun`, `Route.Run.base`) and the frame `b` of first control, and the room's frame `n` ends at `seq(b + (n − C))` (`RoomRun.fm`), with the input `pad n`. So `next` is a theorem (`RoomRun.next`), the machine at first control is `seq b` (`RoomRun.fm_C`, `Route.Run.roomCtl`), and frame `E` is the run's frame `b + (E − 1 − C)` (`Route.Run.roomEnter`). Now the room's frame `n` ends at `seq(b + ix(n − C))`, the end of the `(n − C)`-th frame from `b` on that ends not paused (`RoomRun.fe`), and the room's frame `n + 1` is the real frame from `seq(b + ix(n + 1 − C) − 1)` (`RoomRun.fm`). The frames that end paused in between are not counted; they keep what the model reads (`InRoom.keep`). The machine at first control is `seq b` (`RoomRun.fe_C`). See [A run that pauses in the room](c-7-1-4-RoomLag.md).
* `read_hs`, `read_P`, `read_vs`, `read_in`, `read_ab`, `clean` (one frame): the frames are a sequence of real machines, and the state, the position, the vertical state, the input and the stored speed are read from the machines. With the vertical state read so, `fall_long`, `stand_row` and `vfall` (the frames that start no jump) hold on the TAS and on 2800 runs of own inputs from first control (`room-vs-check`: 170,912 frames, 2,820 landings before `C + 51`). The stored speed is read when the next frame first comes to the player's routine, at `arr n`; `arr` is no longer free data but `CtrlKeep.arrAt`, the first arrival. Every frame up to `t₀` is `CleanW` (at the player's routine the stored speed is `|v|` and the side he presses is not masked; from the scroll handler on nothing writes the horizontal bytes), or it leaves him stopped (`Stop`) and is `ReadW` (the collision bits are a value of `collBits`; `Collide`). With the state at the player's routine that the room's walks give (`InRoom.cut`) and the speed's range from the frames before, these are `FrameModel.CleanR` and `FrameModel.ReadR` (`CleanW.toR`, `ReadW.toR`; [The room's frames at the player's routine](c-7-1-2-RoomCut.md), item 1-1-c-7-1-2). `CleanR` and `ReadR` are `Clean` and `ReadFrame` of [A real frame and the horizontal model](../0-0/0-3-2-FrameModel.md) without `before`, `longer` and `far`: `before` comes from the walk to the player's routine, that the frame does not end during the movement from the frame's time, and the position's range from `far_of` ([The room's frames: the frame's time](c-7-1-1-FrameTime.md), item 1-1-c-7-1-1). That a `CleanR` frame follows `hstep` (`Follow`) and that every frame moves at most the top speed (`move_top`) are proved from `clean_frameR` and `frame_readR`.
* `unpaused` (one machine, new): each frame up to `t₀` ends with the game not paused. Then it comes to the player's routine (`InRoom.reach`). This was hidden in `clean` (the `pc` of `AtCtrl` and `AtFrame`): a run that pauses in the room before `t₀` was outside the theorem. Now `unpaused` is gone: a frame of the room ends not paused by the definition of the room's frames (`RoomRun.up`), and a run that pauses in the room is in the theorem. The new field is `Route.Run.roomLag`: in the room a frame that ends paused is a `lag` frame ([A run that pauses in the room](c-7-1-4-RoomLag.md)).
* `farNear` (one frame, new): a frame up to `t₀` that starts between 8 px and 11.5 px ends at 8 px or more. It replaces `far` (every frame starts at 8 px or more), which is now a theorem (`far_inD`, `far_of`): a frame that starts further right moves left by at most 3.5 px ([The position stays at 8 px or more](c-7-1-3-RoomFar.md), item 1-1-c-7-1-3). On real runs no frame starts below 11.5 px; the least position in the room was 3552 (`room-pair-check`).
* The state at first control (`start`, `startP0`, `startP1`, `v_start`) is no longer assumed: he is stopped, facing right, moving direction 0, running speed 0, at the start position with any fraction, falling, at most 50 px from the top, at most 2.375 px per frame down, with the machine's first fall force and stored speed 0 (the proof no longer uses the stored speed at `C`). `RoomRun.entry_ge` takes `StartAt(fm C)` as an argument, and [The state at the first control in the room](c-7-2-RoomStart.md) proves it from the rows of the change. The vertical state at `C` is that of the machine by `read_vs`, which reads it on every frame (it replaces `vs_C`, which read it at `C` only).
* `wall` (one frame): a frame before `C + 37` that does not follow `hstep` is stopped by the left wall: `P ≤ P_w` before and after it, `RunningSpeed` 0. That this is the only case (he cannot reach the corner) is part of the assumption.
* `late` (one frame): a frame from `C + 37` to `C + 41` that does not follow `hstep` is at the left wall, or `P + 16·v_top ≥ c_P`.
* `stop_run` (one frame): a frame by `C + 40` that does not follow `hstep` leaves `RunningSpeed` 0.
* `air_in` is no longer assumed (item 1-1-c-7-5-5): before `C + 51`, a frame that starts in an air state has an air input. The input of every frame is read from the machine at the player's routine (`read_in`, and the new field `read_stop` on the frames that do not follow the model), and there the player's state is that of the frame's start (`InRoom.stR`): [Frames that start standing in the room](c-7-5-5-RoomStand.md) (`RoomRun.air_in_of`).
* `stand_wall` (one frame): before `C + 51`, after an earlier frame that ends in the state 0, he stands off the floor only at the end of a frame that does not follow `hstep`: the side check stops him. Standing on the top of the block comes later. The first stand of the fall is proved ([The first stand of the fall](c-7-5-16-FirstStand.md), `RoomRun.stand_first`).
* `fall_long` is no longer assumed (item 1-1-c-7-5-4): he is not on the floor before `C + 34`. [The first fall in the room](c-7-5-4-FirstFall.md) proves it up to the first stand (`RoomRun.fall_first`). With no jump since first control [Frames that start standing in the room](c-7-5-5-RoomStand.md) proves it after the stands too (`RoomRun.fall_nojump`). After a jump from the wall, [A jump from a stand during the fall in the room](c-7-5-6-RoomJump.md) proves it (`RoomRun.fall_any`, item 1-1-c-7-5-6): it uses `stand_wall` and `wall`, which put the first stand at `C + 15` or later. The field `fall_jump` is gone.
* `facing` (one frame): before `C + 34`, air frames and jump frames keep the facing.
* `stand_fast`, `stand_P` (one frame): for a stand before `C + 34`, on the frame before it `−V ≥ 256·14` and `P ≤ P_s`. `P_s` is where his foot enters the wall's column, plus one frame below the threshold. His foot enters that column only when he comes fast from outside.
* `stand_row` is no longer assumed (item 1-1-c-7-5-3): from the air to standing, his height is a whole row and his downward speed is 0. [Every frame of a jump in the room](c-7-11-1-RoomFall.md) proves it on the frames before `t₀` (`RoomRun.stand_row_of`), and the proof uses it only there (`RoomCore.stand_row`, on the frames of the fall).
* `vfall` is no longer assumed (item 1-1-c-7-5-4): before `C + 51`, a frame with no jump, not in a jump state, has `Y' ≤ Y + W` and `W' ≤ W + f`; `f` stays, and the next state is not a jump state. [The first fall in the room](c-7-5-4-FirstFall.md) proves it before the first stand (`RoomRun.vfall_first`). It is now asked only with no jump since first control, and [Frames that start standing in the room](c-7-5-5-RoomStand.md) proves it on every such frame (`RoomRun.vfall_of`); `vfall_stand` is gone.
* `floor_at` is no longer assumed (item 1-1-c-7-5-4): with no wall hit he is on the floor at `C + 34`. The first fall gives the floor's height there (`RoomRun.floor_at_of`). What stays is `land_at` (one state): with no wall hit he stands at `C + 34`.
* `vfloor` is no longer assumed (item 1-1-c-7-5-14): with no wall hit, the frames from `C + 34` to `C + 49` that start on the floor, when he has stood on the floor since the end of the fall, are `VFrame` (he stands or takes off). [The floor frames after the fall](c-7-5-14-FloorFrames.md) proves it (`RoomRun.vfloor_of`): with a jump in the input the frame takes off (`InRoom.jump`, `offCheck`); with none the foot check at the end of the move finds the floor, and the frame lands there (`InRoom.floor`). This was the old field `vframes` on floor frames; its air part is a theorem too (item 1-1-c-7-5-1, below).
* `halt`, `prevA` are no longer assumed (item 1-1-c-7-5-2): at the end of each frame before the entry, in a jump the jump's halt value is 1, and A of the frame before is A. [The halt value and A of the frame before](c-7-5-2-RoomPair.md) proves both (`InRoom.pair`, `Route.Run.roomPair`). [The first frames of a jump in the room](c-7-5-1-RoomVert.md) uses them.
* `low_at` (one frame): a frame from `C + 37` to `C + 43` with the feet low is `LowAt`. This is a fact of the collision routine; it is not derived from the routine.
* `ab_early` (one frame): a frame before `C + 37` that does not follow the model reads a stored speed below `v_A`. Such a frame is a wall hit, or comes right after one and reads the stored speed of before the hit. On real frames the stored speed before `C + 37` was at most 21, and `v_A` is 25 (`room-ab-check`: the TAS and 2800 runs of own inputs from first control, with 10,184 such frames; on every frame that follows the model the stored speed read is `|v|`, and it is the one the frame before left).
* `enters`, `read_PE` (one frame): frame `E` enters the side pipe on the real machines, and `P(E)` is the position at the frame's end. `read_PE` is a reading, as `read_P`. The field `movedE` (`P(E)` is the position at the end of the move) is gone (item 1-1-c-7-18-2): [the position at the end of the entering frame](c-7-18-2-SideEntryEnd.md) is proved on the machines of the change (`Route.Changes`), and the theorem `Route.Run.roomEnter` says that frame `E` is one of those frames. `InRoom` is now `mouthE`, `bump`, `vert`, `air`, `stand`, `pair`, `le`, `time`, `arrive`, `reach`, `cut`, `before`, `vstart` and `stR` (`RoomRun.InRoom`, `Route.Run.inRoom`).
* `Approach`: asked only with no wall hit and no stop. The takeoff is from the floor (`T1_floor`), the jump and the landing are `vstep` frames (`Cert.Reach`, `x_vs`), the air frames are air, `low` is the collision routine on the low frames, `x_ab` (one frame) is that the takeoff reads the stored speed.
* `Off`: the jump off the block is `vstep` frames up to `F`, the frame it would reach the floor if nothing stopped it. `F ≤ E` assumes that being stopped or landing on the way only delays the floor. A landing on the pipe's top really happens.
  * `slowJ`: if `F = E`, the frames of a slow jump are air frames of `hstep`, or move at most the air speed.
* `Over`: for a jump over the whole block, the same as `Approach`. Not seen in a real run. `no_landing` proves it impossible under this field.
* `way`: he passes over from the floor or the block's side (`Over`), or he lands on the block and leaves it (`Off`). A run that stands on the left wall, jumps, and passes over the block with no landing is not in `Way`. At the air speed that takes 105 frames or more, and the longest jump from up to 5 rows above the floor is 76 frames, so it should not be a real run. This is not proved in Lean.
* He does not hit his head (item 1-1-c-7-10). This is no longer an assumption; it rests on `SiteOK`, as the rest of the block map does. The collision routine changes the vertical motion by the head at two places: the routine of the head's collision with a block (`h = headAt`: a brick or a block with an item) and the store of the vertical speed after the head's check (`bumpAt`: a solid block, or in the water, or while a block bounces). [The block map in the room](c-7-12-RoomMap.md) proves that no frame of the room comes to either place (`head_of_rows`, `bump_of_rows`): `SiteOK` lets a read for the head give only nothing or a coin. `Route.Run.roomBump` puts this on the frames of `RoomRun` before the entry (`InRoom.bump`). `toCore` once removed the premise of `vframes` (later `vfloor`) with it. That field is now gone (item 1-1-c-7-5-14): the heights of the floor frames come from the walks, which follow the whole frame and need no premise about the head. Frames at or after `E` are not asked at all: the proof uses `VFrame` only on frames before the entry. Two small lemmas give this: the entry is not before `t0` (`t0_le_E`: on the entry frame he is at the mouth, past the goal, and before `t0` he is not past the goal), and a landing on the block comes after the low frames of the jump (`land_late`: on them he is rising, by `arc_facts`). The air frames of `VFrame` are now a theorem: on the first 8 frames of a jump from the floor the frame's height is that of `vstep` (`varc`, item 1-1-c-7-5-1). [The first frames of a jump in the room](c-7-5-1-RoomVert.md) proves it from two walks of the room's frames and the movement routine in the air; `InRoom.vert` (`Route.Run.roomVert`) puts it on the frames of `RoomRun`, and `RoomRun.varc_of` reads it with `read_vs`, `clean` and `InRoom.pair`. A on frame `n` is no longer free data: it is A of the vertical state at the frame's end (`Frames.a`).

```
NoBump(n)       :=  ∀ j,  pc(tr_n(j)) ≠ headAt  ∧  pc(tr_n(j)) ≠ bumpAt           (tr_n(j): j instructions into frame n + 1, from fm(n) with pad(n + 1))
InRoom.bump     :  ∀ n,  C ≤ n < E  →  NoBump(n)                                (Route.Run.roomBump)
RoomCore.vfloor :  NoWall  →  C + 34 ≤ n < C + 49  →  n < E  →  (∀ j ∈ [C + 34, n],  OnFloor(vs(j)))  →  VFrame(n)       (RoomRun.vfloor_of)
RoomCore.varc   :  C ≤ n < t0,  n + 1 < E,  OnArc(T, n),  n + 1 − (T + 1) ≤ 8  →  vs(n + 1) = vstep(vs(n), a(n + 1), 0)    (RoomRun.varc_of)
RoomRun.varc_all:  C ≤ n < t0,  n + 1 < E,  OnArc(T, n),  not at the ground  →  vs(n + 1) = vstep(…)  ∨  (falling  ∧  vs(n + 1) = land(vstep(…)))    (InRoom.air)
RoomCore.stand_row:  C ≤ n,  n + 1 < t0,  st(n) ≠ 0,  st(n + 1) = 0  →  y(n + 1) mod 16 = 0  ∧  W(n + 1) = 0    (RoomRun.stand_row_of)
t0_le_E         :  Off  →  t0 ≤ E
t0_lt_E         :  Off,  vf  →  t0 < E        (vf: 2 ≤ aboveS, 2 ≤ aboveF, 1 ≤ walk, fall + lastG + 1 + rise ≤ standF; numbers checked)
land_late       :  Approach  →  T + 1 + 8 < L
```

These fields were compared with real frames by a program that is not in this repository. On the TAS all hold, with `E` = `C` + 111. So the fields are not contradictory. With random inputs from first control, 2800 runs (4 kinds of input, 700 each, including small changes of the TAS input) had no field failing. Of these, 740 passed the block's end and 510 touched the left wall. The earliest `E` was `C` + 111, from a small change of the TAS input; none was earlier.

Random inputs rarely stand during the fall. So 1701 runs were made from 27 inputs that reach a stand, with 7 inputs after the stand and 9 lengths of A. No field failed. In 434 of them he passed the block's end with no floor at all. With a stand on the wall the earliest `t₀` was `C` + 115, and the earliest `E` of those that touched the floor was `C` + 154. A run with no floor enters at `E` = `C` + 134 when it slows down on the block. In 1152 runs that stand, jump and try to stand again, no field failed either.

The "over the block" case has no real run, so its fields are untested. Big Mario is not included.

## Runs that stand on the left wall

The fall reaches the floor in 34 frames. A wall touch with no landing does not change that. Running left, he can land on a ledge of the left wall during the fall, when his foot enters the wall's column and is less than 5 px deep in a row. His state is ground, and the side check stops him on the same frame (`wall` before `C + 37`). On the next frame he jumps or falls.

Seen on real frames:

* In 20000 random runs, the first stand was at `C + 18`, `C + 19` (4 rows above the floor), `C + 22` (3 rows), `C + 26` (2 rows) or `C + 30` (1 row). All the others reach the floor at `C + 34`. The earliest wall frame was `C + 16`.
* Left on the frame after a stand makes a wall frame: he faces left, is pushed back 1 px and falls. Facing left, Right in the air has the doubled adder. This is the case of `wall_turn`. Left and Right together also change the facing.
* Falling from a stand, the floor comes later: from `C + 46` to `C + 50` in the 5 runs tried.
* He can stand, jump and stand again. One run stood at `C + 18`, jumped, and stood again at `C + 73` and `C + 122`. In what was tried, two stands were at least 41 frames apart.
* He can enter with no floor at all. One run stood at `C + 18`, jumped at `C + 19`, landed on the block, with `t₀` = `C` + 116 and `E` = `C` + 134.

A run that does not touch the floor must stand in the fall. With no stand he reaches the floor at `C + 34`.

**Files.** `Theorems/RoomJoin.lean`, private `Proof/RoomJoin.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta room-join-check     # the longest jumps, the floor check, and the margins (1 s)
.lake/build/bin/smbrta room-ab-check FM2 [N]    # the stored speed read on real frames in the room, N runs of each of 4 kinds of input (N = 700: about 6 min)
.lake/build/bin/smbrta room-vs-check FM2 [N]    # the vertical state read from the machine: fall_long, stand_row, vfall on real frames (N = 700: about 1.5 min)
```
