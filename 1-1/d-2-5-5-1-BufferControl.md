[← Back](README.md) | [English](d-2-5-5-1-BufferControl.md) | [Japanese](d-2-5-5-1-BufferControl-ja.md)

# The control of the screen's buffers through the room

**Claim.** Every frame of the room, from the room's first control to the frame that enters the side pipe, starts with the control of the screen's buffers at 0 or at 6. This is proved, with two checks on the ROM: two walks of the room's frame (about 8 s together natively) and one check of the rows of the first change (about 30 s natively). The field `buffer₂` stays. With this page it excludes only one value: the control at 6 at the start of the entering frame, which is the value after a frame that erased a coin. Round 24 narrowed it further: a frame that starts with the control at 6 on page 0 at 16 to 180 px does not enter ([BufferCoin](d-2-5-5-2-BufferCoin.md)), so `buffer₂` asks only that a coin frame just before the entry ends there.

The names are those of [The screen's buffer at the side pipe's entry](d-2-5-5-EntryBuffer.md). `c(m)` is the control of the screen's buffers (`VRAM_Buffer_AddrCtrl`) in the machine `m`. `r` is the room's reference machine, and `c(r) = 0`. `r₆` is `r` with `c = 6`. `K_T` is the list of the bits that the room's condition knows (the map's bits), and `K_B := K_T ∪ { every bit of c }`. `seq(n)` is the machine when frame `n` of the run begins, `trₙ(j)` the machine `j` instructions into frame `n`. `b₁` is the room's first control and `a₂` the side pipe's entry.

## The statement

```
finK(B)        :=  B knows c,  and its value is 0 or 6
keepCheck      :=  K_T does not list c,   c(r) = 0,
                   the room's walk with K_B from r ends in states with finK,   and from r₆ too

keep_frame     :  the walk from (r', K) ends with finK,   RoomCond(r', K, m),   ∀ j, SiteOK(tr(j))     →   c(frame(m, i)) ∈ {0, 6}
cond0          :  RoomCond(r, K, m),   c(m) = c(r)                                    →   RoomCond(r, K ∪ {c}, m)
cond6          :  RoomCond(r, K, m),   K does not list c,   c(m) = 6                  →   RoomCond(r₆, K ∪ {c}, m)
ctl_step       :  keepCheck,   RoomCond(r, K_T, m),   ∀ j, SiteOK(tr(j)),   c(m) ∈ {0, 6}     →   c(frame(m, i)) ∈ {0, 6}
ctl_run        :  the conditions of RoomMap.map_of_rows on [b, a),   c(seq b) ∈ {0, 6}      →   ∀ n ∈ [b, a],  c(seq n) ∈ {0, 6}

startCheckC    :=  every state of the rows of the time of the first change knows the bits of K_B with the values of r
start_ctl      :  startCheckC,   InRowsT(m),   m has control                          →   c(m) = c(r)
ctl_of_rows    :  the conditions of RoomMap.map_of_rows on [b, a),   keepCheck,   startCheckC     →   ∀ n ∈ [b, a],  c(seq n) ∈ {0, 6}

Run.ctl₂       :  c(seq(a₂ − 1)) = 0   ∨   c(seq(a₂ − 1)) = 6                          (theorem, new)
Run.buffer₂    :  c(seq(a₂ − 1)) = c(r)   ∨   EntryAt(L₅, seq a₂)                        (field in round 23)
Run.buffer₂    :  c(seq(a₂ − 1)) ≠ 6   ∨   (page = 0  ∧  16 ≤ x < 181 at seq(a₂ − 1))   ∨   EntryAt(L₅, seq a₂)     (field, narrowed in round 24)
```

`Run.ctl₂` takes `b = b₁` and `a = a₂`. The machine at `b₁` is in the rows of the first change (`ChangesK.run₁`, `inRowsT`) and has control (`ChangesBase.ctl₁`); each frame from `b₁` before `a₂` meets `SiteOK` (`chg.roomSites`) and starts in the player's routine (`ChangesBase.roomStay`); `b₁ < a₂` (`Run.b₁_lt_a₂`), so `b₁ ≤ a₂ − 1 ≤ a₂`. Since round 24 the checks `keepCheck` and `startCheckC` are in `RoomChecks.buffer` (its field `ctl`, `BufferCoin.FactsB`), and `Run.ctl₂` has no argument for them; `Run.buf₂` uses `Run.ctl₂` (`ref_of_ne6`: a control of 0 or 6 that is not 6 is the reference's).

Lean: `Theorems/BufferControl.lean` (`finK`, `ref6`, `walkK`, `keepCheck`, `keep_frame`, `cond0`, `cond6`, `keep_parts`, `ctl_step`, `ctl_run`, `startCheckC`, `and_ff`, `start_ctl`, `Facts`, `ctl_of_rows`, `ref_of_ne6`), `Theorems/Route.lean` (`Run.ctl₂`), the private `Proof/BufferControl.lean` (`buffer_control_keep`, `buffer_control_start`, `buffer_control_facts`; `genBufferControl` in `Main.lean`). There is no game data in the public files.

## How it works

**Who writes the control.** The interrupt handler draws the buffer that the control names and then sets the control to 0. In the game's code the control is set to 6 by the erase of a coin (so that the next frame draws the second buffer, where the erase wrote the blank tiles). The area parser's column output and its rendering of the attributes also set it to 6; only the tasks that write messages and palettes set it to other values. On real frames of the room only two instructions write it: the handler's reset and the erase of a coin.

**The walk.** It is the walk of `EntryBuffer`: the room's walk with the control known at the frame's start, and the control in the key of the search. From the control at 0, and from the control at 6, every path ends with the control known to be 0 or 6. With the control at 6 the handler draws the second buffer, whose bytes the walk does not know; the walk follows this draw without them, and no path fails.

**The room's first control.** The rows of the first change know the control there, with the reference's value 0. So the induction over the room's frames starts with 0.

**What `buffer₂` still asks.** At the start of the entering frame the control is 0 or 6. With 0 the five bytes of the first buffer are proved (`Run.buf₂`). With 6 the frame before erased a coin; the handler then draws the second buffer and keeps the records of the first one (the coin's digits), and the five bytes are not those of a reference. So `buffer₂` is still needed to exclude 6.

## Measured, not a theorem

`buffer-ctl-check FM2 300 real` (exit 0): the movie's room and own runs from frames of the movie in the room, 300 runs of each kind with a small player and 300 with a big one. Kind 0 are random inputs from any frame of the room; kind 1 start in the last 60 frames before the movie's entry, with more jumps (so they take the coins near the block's right end).

| run | frames | entries | frames that end with the control set | the control at the frames' ends | the largest position at an erase of a coin | the least position at the start of an entering frame | frames from the last frame with the control set to the entry |
|---|---|---|---|---|---|---|---|
| the movie | 111 | 1 | 13 | 0, 6 | 163 px | 194 px | 16 |
| kind 0, small | 125,891 | 102 | 1,019 | 0, 6 | 173 px | 193 px | at least 16 |
| kind 0, big | 113,761 | 126 | 1,229 | 0, 6 | 172 px | 194 px | at least 16 |
| kind 1, small | 66,202 | 218 | 1,178 | 0, 6 | 173 px | 194 px | at least 16 |
| kind 1, big | 69,677 | 208 | 1,245 | 0, 6 | 172 px | 194 px | at least 16 |

On every run: the only instructions that change the control are the handler's reset and the erase of a coin; the page is 0; the erased coins are in the map's coin columns, the nearest three columns left of the mouth's; a frame that erases a coin ends at the position of the erase; one frame moves the position by −1 to 3 px from its start to the end of the move, and by −1 to 1 px after it; no entering frame starts with the control at 6. At the room's first control the control is 0 (the movie), and every state of the rows of the first change knows it at 0 (14,224 states).

Walks (`buffer-ctl-check FM2 0 walk`): from the control at 0, 172,182 steps, 0 failures; from the control at 6, 323,827 steps, 0 failures; both end with the control 0 or 6. The checks (`buffer-ctl-check FM2 0 keep`): `keepCheck` 8.1 s, `startCheckC` 30.4 s natively on a busy machine.

## Measured: the parts of `SiteOK` in the room

`chg.roomSites` (1-1-d-2-4-2) asks `SiteOK` on each instruction of the room. `buffer-ctl-check FM2 100 sites` (exit 0) steps every instruction of own runs from the movie's frames in the room: 100 runs with a small player (42,438 frames) and 100 with a big one (42,452 frames). No instruction fails a part. The margins:

| part | what real frames do | what a proof would need |
|---|---|---|
| `late` | the handler is done by dot 42,656; the bound is 83,342 | a bound on the time of every path of the walk (the walks clamp the clock by this part) |
| `reads` | 1.76 million reads through a pointer at 15 places, all in RAM or ROM | the pointer's high byte known at each such read |
| `read` | the tiles read are in the list; reads for the head give only nothing or a coin; no read outside the block buffers | the map's bytes on each instruction (part c's `RoomBlocks` proves them, but from `roomSites`), and for the head the position: no brick above a reachable head |
| `erase` | 695 erases, all in the block buffers | the erase's place is the read's |
| `off` | the screen buffer's offset at most 46 at its uses; the bound is 64 | a bound on the records that one frame writes |
| `xbit` | the position's low bits at the side pipe's read are 3 or 4 | the position at the entry |

## Round 24

[BufferCoin](d-2-5-5-2-BufferCoin.md) (1-1-d-2-5-5-2) proves the half of the plan below for the entering frame: a frame that starts with the control at 6, on page 0, at 16 to 180 px, comes to the end of the move only left of the mouth, so it does not enter. Its walk splits the position, the added byte and the carry only at the move's add, and forgets the position at the scroll handler. `buffer₂` now asks only the other half on one state: a coin frame just before the entry ends on page 0 at 16 to 180 px.

## What would remove `buffer₂` (round 23's plan)

One would prove `Cls(m) := c(m) = 0 ∨ (c(m) = 6 ∧ x(m) < 176)` on every frame of the room, where `x` is the position on the page and 176 px is the left end of the column right of the nearest coins: a frame that ends with `c = 6` ends left of 176 px, and a frame that starts left of 176 px does not enter (the mouth's left end is 195 px). The measured margins are wide (173 px against 193 px). But the abstract machine adds bytes with all their bits known or none, so the walk must split the position into its values where the collision routine adds it to an offset, and where the move adds the speed. Two designs were tried in programs (no part of the proof):

* the position split at every read of the block buffers (256 values × the page's bit × the row): 12.5 million steps, 2.3 million states, 146 s, 1,004 failures;
* the position in pieces at the end of the move (left and right of 174 px), split only at reads right of it, at side reads and at the push, with the read of `EntryHeightBig` (the map's byte at a known place) and no machine at an erase outside the block buffers: from the control at 0, 3.0 million steps, 707,000 states, 31 s, 2.5 GB, 24 failures, and 48 frame ends with the control at 6 and the position in a piece right of 176 px (from paths that do not come to the erase of a coin); from the control at 6, two of the three classes passed 5.5 GB and were stopped, the third had 136 ends that enter (the page wraps in the abstract move).

## Uses from other parts

* Part c: `RoomMap.cond_of_rows` (the room's condition at each frame), `RoomMap.MapFacts`, `RoomMap.startCheckT`, `ScreenStart.room_of_invL`; through `Run.ctl₂` `chg.roomSites`, `ChangesBase.roomStay`, `Run.b₁_lt_a₂`.
* Part b: `ChangesK.run₁`, `PipeRunK.inRowsT` with `RoomChecks.pipe`, `ChangesBase.ctlFirst₁`, `ChangesBase.ctl₁`, the rows of the time of the first change.
* Part a: `Run.entry₁`.
* Part d: the walk of `EntryBuffer` (`hpB`, `knownB`, `optsB`) and of `EntryHeight` (`walkCheckY`, `frame_end`).
* No cycle: none of these uses `buffer₂`, `Run.buf₂` or `Run.ctl₂`.

## What changed in the route

* Fields: none removed, none added in round 23.
* New theorem `Run.ctl₂`. Since round 24 `Run.buf₂` uses it, its checks are in `RoomChecks.buffer`, and `buffer₂` excludes only the control at 6 outside page 0 at 16 to 180 px.

## Assumptions (not proved in Lean)

* `buffer₂`: by `Run.ctl₂` and `Run.coin₂` it excludes only the control at 6 at the start of the entering frame, with the start not on page 0 at 16 to 180 px.
* `SiteOK` on each instruction in the room (`chg.roomSites`), as before.

**Files.** `Theorems/BufferControl.lean`, `Theorems/Route.lean`; the private checks are in `Proof/BufferControl.lean` (`genBufferControl` in `Main.lean`).

**To reproduce.**
```
.lake/build/bin/smbrta buffer-ctl-check FM2 0 keep       # the two checks, about 40 s
.lake/build/bin/smbrta buffer-ctl-check FM2 0 walk       # the walks from the control at 0 and at 6, about 5 s
.lake/build/bin/smbrta buffer-ctl-check FM2 0 rows       # what the rows of the first change know, about 30 s
.lake/build/bin/smbrta buffer-ctl-check FM2 300 real     # the table of real frames, about 4 min
.lake/build/bin/smbrta buffer-ctl-check FM2 100 sites    # the parts of SiteOK on real frames, about 1 min
```
