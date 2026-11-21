[← Back](README.md) | [English](c-7-14-1-BigApproach.md) | [Japanese](c-7-14-1-BigApproach-ja.md)

# A big player at the block's corner

The field `way` of [Joining the bonus room](c-5-RoomJoin.md) gives, with no wall hit and no stop from `C + 37` to `t₀`, the last takeoff from the floor before a landing on the block (`Approach`). Its part `low` said that every low frame of that jump (the feet at the corner's height or lower) is `LowAt`: the collision routine keeps him left of the corner, or stops him, or he moves left. This is false for a big player on measured runs. This page replaces `low` by a statement that holds for a big player too, proves the fast takeoff of a big player and the slow takeoff after the first frame after the fall, and left one hypothesis for the slow takeoff of a big player on that first frame (`Approach.slowBig`). Round 26 proves it too: [A big player's slow takeoff on C + 35](c-7-14-2-LandDist.md).

**False, measured (round 24).** `Approach.low` is false for a big player: on 2 measured runs with no wall hit, no stop and a landing on the block, the last low frame (10 frames after the takeoff, at the height 138, moving right) ends 336/256 px and 48/256 px past the corner, not stopped. The cause: a big player's side check has two points, 8 px and 24 px below his top. At the heights 136 to 151 the upper point is in the row above the block, where a coin is above the block's left column. The routine takes the coin and leaves the side check, so on that frame the lower point does not push him back. The coin is then gone, so this happens on one frame only.

## Statements

`P(n)`, `vs(n)` are the position (in 1/256 px) and the vertical state at the end of frame `n`. `c_P` is the corner (51 px), `S_low = 415/256` px, `G_P` the goal (the block's right end). `T1 + 1` is the takeoff frame, `s = T1 + 1 + u.low` the last low frame of the jump, `L` the frame on the block. `sz` is the player's size byte at first control: 0 is big. `LowAt(n) := P(n) ≤ c_P + S_low ∧ (Stop(n) ∨ P(n) < c_P ∨ v(n) < 0)`. `fast` says that the takeoff read a stored speed of 25 or more.

```
Approach.low (field, was  ∀ n ∈ [T1 + 1, s],  LowAt(n)):
  ∀ n ∈ [T1 + 1, s],   LowAt(n)  ∨  (sz = 0  ∧  n = s  ∧  P(n) ≤ c_P + S_low)

Approach.slowBig (field of round 25; gone in round 26, proved by LandDist.slow_short):
  sz = 0  →  fast = false  →  ¬LowAt(s)  →  T1 = C + 34  →  C + 98 < t₀

slowBigOk (new check, in Checks.roomBig): for each slow pair (q₁, q₂) ∈ {(10, 17), (11, 16)},
  c_P − 1 + 384·(q₂ + 1 − q₁) + capDist(98 − (34 + 2 + q₂))  <  G_P

fast_short (proved):  with the search of FastTakeoff for L' low air frames after the jump frame (L' ≤ 8),
  no wall hit, no stop from C + 37 to t₀, t₀ ≤ C + 98, a fast takeoff by C + 40, and P(n) < c_P for every n ≤ T1 + 1 + L'   →   False

landed_short (proved, same statement): with no wall hit and no stop, a landing on the block gives C + 98 < t₀
```

`landed_short` splits on `LowAt(s)`:
- `LowAt(s)` (always for a player who is not big): as before. Every low frame is `LowAt`, so every frame up to `s` is left of the corner (`left_at`); a slow takeoff is short by the air speed cap (the pairs `(10, 17)`, `(11, 16)`, 65/256 and 193/256 px to spare), a fast one by the search of `FastTakeoff` with 8 low air frames (`roomOk`).
- not `LowAt(s)`: then `sz = 0` and only the last low frame may be past the corner. Every frame up to `s − 1` is left of it (`left_at` with `w = s − 1`). A fast jump has at least 8 low air frames (`s ≥ T1 + 9`), so the 7 air frames after the jump frame are left of the corner, and the search of `FastTakeoff` with 7 low air frames (`roomB`, the new check `Checks.roomBig`) gives the contradiction. A slow takeoff after `C + 35` (`T1 ≥ C + 35`) has the bound from `s − 1`: one more frame in the air, but the landing is one frame later too, and `capDist(n + 1) ≥ 384 + capDist(n)`; `pair_bound` with the pair `(q₁, q₂ + 1)` and `slowBigOk` give the contradiction. A slow takeoff on `C + 35` was `slowBig`; since round 26 it is the search of `LandDist` (`Checks.slowLand`).

**Why `slowBig` was not proved here** (round 26 does it with a table of the frames after the landing and a search from the room's first frame: [A big player's slow takeoff on C + 35](c-7-14-2-LandDist.md)). On `C + 35` the landing is not later. From `P(s − 1) < c_P` the slow takeoff's bound has one more frame at the air speed: `c_P − 1 + 384·8 + capDist(46)` is 319/256 px past the goal at `C + 98` (it was 65/256 px short from `P(s) < c_P`). No condition at or before the landing helps: a measured big run has `P(L) − c_P = 2880/256` px on its landing frame, while the bound would need at most about 2752. The looseness is after the landing: `capDist(46)` is 28480, and the TAS covers 27984 in those 46 frames. A tighter bound needs a new search after the landing (round 26: the exact table alone is still 15/256 px past the goal; the search from the room's first frame closes it).

## Measured

- The TAS (small): takeoff on frame `C + 35`, last low frame `C + 45` at 16/256 px left of the corner, landing on the block on `C + 52`, `t₀ = C + 99`; at `C + 98` it is 592/256 px short of the goal. On frame `C + 46` the small player's side check takes the same coin.
- A big player (the size byte set to big at first control, an artificial state), a hill climb over own inputs from the TAS's: the coin is taken on the last low frame `C + 45` at 208/256 px past the corner, not pushed back; the best run is 320/256 px short of the goal at `C + 98`, `t₀ = C + 99`. A beam search (300 states per frame, 16 inputs with Left+Right) from that frame gives the same −320; from the TAS's state at `C + 45` it gives −544 (the TAS −592).
- `FastTakeoff.roomCheck` with 7 low air frames is true (about 1.4 s natively), as with 8.
- `room-approach-check FM2 300 1` (big; the TAS, 2,700 own runs and the climb's run, up to `t₀` or 300 frames): 38 runs with no wall hit, no stop and a landing on the block, 437 low frames. The old `low` is false on 3 of them (the 2 frames above and the climb's frame `C + 45`); the new `low` holds on all. `slowBig`'s premises hold on 2 runs (`t₀ = C + 108` and `C + 99`), and it holds on both. No run goes against `fast_short` or `slowBigOk`. `… 300 0` (small): 37 such runs, all 428 low frames `LowAt`.
- Not measured, an estimate: from the TAS's state at first control `P` moves in steps of 16/256 px, so a big player's `P(C + 44) ≤ c_P − 16`, and with the speed at most 24 `P(C + 45) ≤ c_P + 368`, 160/256 px more than the climb's run. With the measured play after the landing this is about 160/256 px short of the goal at `C + 98`. A search for the farthest such frame `C + 45` did not get past the climb's run.

## What remains

- `slowBig`: proved in round 26 ([A big player's slow takeoff on C + 35](c-7-14-2-LandDist.md)); the field is gone.
- `Approach.low` itself is still a field: that the collision routine keeps a low frame `LowAt` (or a big player's last one not far past the corner) is not derived.

**Files.** `Theorems/RoomJoin.lean`: `Approach` takes `sz` (`low` changed, new `slowBig`), `Way` and `RoomFields`, `RoomCore` take `sz`, `RoomRun` sets it to the size byte of `S.seq b` (the machine at first control), new `roomB`, `slowBigOk`, `Checks.roomBig`, `fast_short`; `landed_short` keeps its statement. Private: `roomBig` in `room_checks` (`Proof/RoomJoin.lean`). Programs `room-approach-check`, `room-big` (probe, beam, fast).

**Reproduce.**
```
.lake/build/bin/smbrta room-approach-check FM2 300 1      # big; with 0 at the end, small
.lake/build/bin/smbrta room-big fast 7                    # the search of FastTakeoff with 7 and 8 low air frames
.lake/build/bin/smbrta room-big probe FM2 3000            # the TAS's room frames for both sizes, and a hill climb
.lake/build/bin/smbrta room-big beam FM2 300 45 INPUTS    # a beam search from frame C + 45
```
