[← Back](README.md) | [English](d-2-5-2-EntryRoutine.md) | [Japanese](d-2-5-2-EntryRoutine-ja.md)

# The routine at the side pipe's entry

**Claim.** At the side pipe's entry (frame `a₂`), the routine byte is the side pipe's. This is proved from the room's entering frame. So `Route.Run` asks 10 bytes at the entry, not 11 (`chg.entry₂`, 1-1-d-2-5). One small field is new: the search for `a₂` looks at least one frame past the room's first control (`dR_pos : 1 ≤ dR`).

`m[i]` is the RAM byte `i` of `m`. `frame(m, i)` is one frame of `m` with the input `i`, and `tr(j)` the machine `j` instructions into it. `seq(n)` and `inp(n)` are the machine when frame `n` of the run begins and its input. `rt(m)` is the routine byte, `e_s` the side pipe's routine, `r` the reference machine of the room. `b₁` is the room's first control. `a₂ = firstWith(p, b₁, dR)` is the first frame from `b₁` on, within `dR` frames, with `p(n) := rt(seq n) ≠ rt(r)`. `R₁₁` is the 11 bytes of `RoomMusic.restIdxM`, `R₁₀ := R₁₁ \ {rt}`. `V` is the references of the entry.

## The statement

```
EntryAt(L, m)   :=  ∃ (v, X) ∈ V,  ∀ i ∈ X,  i ∈ L  →  m[i] = v[i]

rest_rt        :  RestOK,  RoomCond(m),  ∀ j, SiteOK(tr(j)),
                  ∀ j, (∀ k ≤ j, rt(tr(k)) ≠ e_s) → HypW(tr(j)),
                  ∃ n, rt(tr(n)) ≠ e_s ∧ rt(tr(n + 1)) = e_s
                  →  rt(frame(m, i)) = e_s
rt_of_rows     :  the hypotheses of RoomMap.map_of_rows on [b, a),  the checks,  b ≤ k < a,  Enters(seq k, inp k)
                  →  rt(frame(seq k, inp k)) = e_s

Run.b₁_lt_a₂   :  1 ≤ dR  →  b₁ < a₂
Run.rt₂        :  rt(seq a₂) = e_s
entryAt_of_rt  :  rt(m) = e_s  ∧  EntryAt(R₁₀, m)  →  EntryAt(R₁₁, m)
Run.chgK       :  the changes with EntryAt(R₁₁, seq a₂), from chg and Run.rt₂
```

**`rest_rt`** is the induction of `SideEntryRest.rest_end` with another conclusion. The walk of `SideEntryRest` asks at every step that once the routine byte is `e_s` it stays `e_s` (`okT`). `rest_end` shows this inside its proof and concludes the position; `rest_rt` concludes the routine byte at the frame's end. **`rt_of_rows`** joins the two walks of the entering frame as `SideEntryRest.mouth_of_rows` does: the walk of `SideEntryEnd` gives `HypW` up to the first write, and `rest_rt` carries the routine to the frame's end.

**`Run.b₁_lt_a₂`.** `rt(seq b₁) = rt(r)` (the room's condition at the first control, `ChangesK.roomAt`), so `p(b₁)` is false. With `dR = d + 1`: `firstWith(p, b₁, d + 1) = firstWith(p, b₁ + 1, d) ≥ b₁ + 1`.

**`Run.rt₂`.** `Run.roomEnter` (part c) gives the room's entering frame as a frame `k` of the run with `b₁ ≤ k < a₂`. It writes `e_s` (`room.enters`). By `rt_of_rows`, `rt(seq(k + 1)) = e_s`. Every frame `n` with `b₁ ≤ n < a₂` has `rt(seq n) = rt(r) ≠ e_s` (`ChangesBase.roomStay`, `RoomFacts.ne`). So `k + 1 < a₂` is false, and `a₂ = k + 1`.

**`entryAt_of_rt`.** Every reference lists the routine byte with the value `e_s` (`RoomChecks.rt`). For `i = rt` the value comes from `rt(m) = e_s`; every other byte of `R₁₁` is in `R₁₀`.

Lean: `Theorems/EntryRoutine.lean` (`rest_rt`, `rt_of_rows`), `Theorems/Route.lean` (`EntryAt`, `restIdxR`, the parameter `L` of `ChangesBase` and `ChangesK`, `entryAt_of_rt`, `Run.dR_pos`, `Run.b₁_lt_a₂`, `Run.rt₂`, `Run.chgK`, the new fields of `RoomChecks`). There is no new check on the ROM: the walks are those of part c, with their private checks `map_facts`, `map_start`, `map_startF`, `side_entry_end_check`, `side_rest_check`.

## Uses from other parts

* Part c: the field `room.enters` (the room's frame `E` writes the side pipe's routine), the theorem `Run.roomEnter`, the walks `SideEntryEnd.write_right_of_left` and `SideEntryRest` (`RestOK`, `live_stepP`, `okS`, `HypW`, `clean_E`, `start_E`, `restCheck`), and `RoomMap` (`map_of_rows`, `map_run`, `start_of_rows`, `start_of_rowsF`, `clean_of_rows`, `head_of_rows`, `bump_of_rows`).
* Part b: the rows of the first change at the room's first control (`ChangesK.run₁`, `inRowsT`) and `ctl₁`, `ctlFirst₁`.
* No cycle: `Run.roomEnter` asked `b₁ < a₂` of `ChangesK.b₁_lt_a₂`, which read the routine byte of `entry₂`. It now asks it of `Run.b₁_lt_a₂`, which uses `dR_pos` and the room's first control. None of the theorems above uses `entry₂`.

## What changed in the route

* `ChangesBase` and `ChangesK` have a parameter `L : List Nat`, by default `RoomMusic.restIdxM` (11 bytes). `entry₂ : EntryAt L V (seq a₂)`. `HurryMusic` and `HurryStart` take `ChangesK` with the default, so they do not change. The theorems that do not read the routine byte (`upStay`, `ctl₁`, `roomStay`, `run₁`, `bound₁`, `roomAt`, `pauseBits₂`, …) are for any `L`; `rt₂`, `pause₂`, `entryRest₂`, `run₂`, `bound₂`, `b₁_lt_a₂` are for the default.
* `Run.chg : ChangesK … (restIdxR sy nmS m0)`: 10 bytes. `Run.chgK` gives the changes with the 11 bytes; `Run.change₂`, `Run.start`, `Run.atCtl₀` use it (these three moved below `Run.roomEnter`).
* `Run` has a new field `dR_pos : 1 ≤ base.dR`.
* `RoomChecks` has five new fields: `map`, `mapStart`, `mapStartF`, `sideEnd`, `sideRest`. `RoomChecks` is built in the private files of the route (5 times) and of the hurry-up music (once).

Removed from the assumptions: the routine byte of `entry₂`. Added: `dR_pos`.

## Why the height and the screen's buffer stay (measured)

Round 15: both are now proved on the entering frame, each under a condition at the frame's start (a small player; the control of the screen's buffers at 0): see [The height at the side pipe's entry](d-2-5-4-EntryHeight.md) and [The screen's buffer at the side pipe's entry](d-2-5-5-EntryBuffer.md). What follows is the measurement of round 13.

A program, not a theorem: `entry-y-check FM2 400` (about 1 min). It runs the movie to the room, then 400 runs of random inputs from frames of the movie in the room, then one frame from the start of the movie's entering frame with the height, the state and the vertical speed overwritten.

| what | result |
|---|---|
| the movie | first control after movie frame 653; `t0 = C + 99`, `E = C + 111`. The 12 frames from `t0` to `E` are all in the air (state 1); the entering frame lands: height `AD → B0` |
| random entries | 157; the height at the end of the entering frame is `B0` in all; at its start `AD`, `AE`, `AF` or `B0` |
| frames from `t0` to `E` | 12 to 244 (122 runs); 43,492 frames in the air in between |
| overwritten starts | 960 frames (heights `90` to `CF`, 5 vertical states, 3 inputs): 55 enter, all with the height `B0` at the end |
| the screen's buffer at the entry | offset `00` or `07` (the two references); the buffer control at the start of the entering frame is `00` in every entry |
| coins | 1,348 taken; the largest position of a frame that takes one is 44,528, the mouth's left end 49,920 (21 px further); at least 16 frames from the last coin to the entry |

**The height.** Part c reads the vertical state from the machines only up to `t0` (`read_vs : n ≤ t0`, `vair_of : n < t0`). From `t0` to `E` its model has the jump off the block as numbers (`Off`), not as machines. On the movie all 12 frames of that stretch are in the air, and the entering frame is the landing. The walks of the entering frame (`SideFrame`, `SideEntryEnd`, `SideEntryRest`) do not follow the height, and the room's walk knows only the bits that are 0 in the block map, not the floor's 1 bits. So no walk knows the row on which the entering frame lands. On real frames the overwritten starts show that only the frames that end at `B0` enter. What would give it: the vertical bytes on the machines from `t0` to the entry (part c), or a walk of the entering frame with the height in pieces and the floor's tiles known.

**The screen's buffer.** On the entering frame only the colour rotation writes the first buffer: the game timer does not run, because the player's routine is no longer running when the timer's code comes. But a coin taken on the frame before sets the buffer control so that the next screen update clears the second buffer, not the first. Then the coin's records stay in the first buffer at the entry. To exclude it one needs the position on the two frames before the entry. Part c has the position on the machines up to `t0` and at the end of frame `E`, not on the frames between. Measured: no coin within 16 frames of an entry.

## Assumptions (not proved in Lean)

* `chg.entry₂`: 10 bytes at the entry have the values of a reference: the player's height, the screen's buffer (5 bytes), the area music's buffer, the event music's queue, the added note length, the level's number (1-1-d-2-5). Since round 14, 9: the level's number comes from the vertical pipe's entry ([1-1-d-2-5-3](d-2-5-3-AreaKeep.md)). Since round 15 the height and the five bytes of the screen's buffer come from the entering frame, when it starts with a small player and with the control of the screen's buffers at 0 ([1-1-d-2-5-4](d-2-5-4-EntryHeight.md), [1-1-d-2-5-5](d-2-5-5-EntryBuffer.md)): `chg.entry₂` asks 3 bytes, and `Run` has the two fields `height₂`, `buffer₂` for the other runs.
* `dR_pos`: the search for the entry looks at least one frame past the room's first control.

**Files.** `Theorems/EntryRoutine.lean`, `Theorems/Route.lean`; in `Main.lean` the `RoomChecks` in the generated route and hurry-up proofs, and the program `entry-y-check`.

**To reproduce.**
```
.lake/build/bin/smbrta entry-y-check FM2 400     # the table above, about 1 min
```
