[← Back](README.md) | [English](c-7-1-3-RoomFar.md) | [Japanese](c-7-1-3-RoomFar-ja.md)

# The room's frames: the position stays at 8 px or more

**Claim.** At the start of each frame of the bonus room up to `t₀` the position is at least 2048 (8 px). This was the field `far` of [Joining the bonus room](c-5-RoomJoin.md) (the lower half of the old `Clean.far`, item 1-1-c-7-1-1). Now it is a theorem from a weaker field, `farNear`: only a frame that starts within `16·top + 256` (3.5 px) right of 8 px is asked to end at 8 px or more. A frame that starts further right ends there anyway: one frame moves him left by at most the top speed (2.5 px), and the collision routine pushes him by at most 1 px more.

`P(n)` is the position at the end of the room's frame `n` (the start of frame `n + 1`), `hs(n)` the horizontal state, `D` the domain of the model (`inD`), `top` the top speed. `C` is the first control, `t₀` the first frame past the block.

```
farNear          :  C ≤ n,  n + 1 < t₀,  2048 ≤ P(n) < 2048 + 16·top + 256  →  2048 ≤ P(n + 1)        (field, one frame)
start_far        :  2048 ≤ 256·x_start                                                               (numbers, checked)
frame_readR_low  :  ReadR(M, n₀),  the conditions of frame_readR  →  P(M) − 16·top − 256 ≤ P(end)
step_far         :  C ≤ n < t₀,  2048 ≤ P(n),  hs(n) ∈ D
                    →  (Follow(n) ∨ Stop(n + 1))  ∧  P(n) − 16·top − 256 ≤ P(n + 1)  ∧  hs(n + 1) ∈ D
far_inD          :  C + d < t₀  →  2048 ≤ P(C + d)  ∧  hs(C + d) ∈ D
far_of           :  C ≤ n < t₀  →  2048 ≤ P(n)  ∧  P(n) + 2048 < 2²⁴
```

Lean: `Theorems/FrameTime.lean` (`frame_readR_low`), `Theorems/RoomJoin.lean` (`RoomRun.farNear`, `NumFacts.start_far`, `far_up`, `follow_of_far`, `step_far`, `far_inD`, `far_of`, `inD_of`, `follow_of_clean`, `frames_of`, `move_top_of`); private `Proof/RoomJoin.lean` (`room_nums`).

## How

**One frame's move.** A frame that follows the model ends at `P + 16·v'` (`clean_frameR`), and `v'` is in the domain, so `|v'| ≤ top` (`FastTakeoff.step_facts`). A frame that stops him is a `TopSpeed.Frame`: it moves `16·v₂` with `|v₂| ≤ top`, and after the scroll handler the position stays, or moves 256 left or right (`Collide`). `frame_readR` keeps only an upper bound in its third case; `frame_readR_low` is its copy with the lower bound. So each frame moves him left by at most `16·top + 256`.

**The induction.** At first control the position is at least `256·x_start` (`StartAt.P0`, the start's pixel), which is at least 2048 (`start_far`, a number fact of the room, checked by `native_decide`), and the state is the room's start, in `D`. If a frame starts at 8 px or more with the state in `D`, `step_far` gives its move and the state at its end in `D`. If it started at `2048 + 16·top + 256` or more, it ends at 2048 or more; otherwise `farNear` says so. Both `clean_frameR` and `frame_readR` need `2048 ≤ P` at the frame's start, so the position and the domain go together in one induction (`far_inD`).

The domain also gives the speed's range at the player's routine (`speed_of`), which `ReadR` needs ([The room's frames at the player's routine](c-7-1-2-RoomCut.md)). `inD_of`, `follow_of_clean`, `frames_of` and `move_top_of` now take the state at first control (`StartAt`), as `toCore` gives it.

## Checked on real frames

`room-ctrl-check FM2 200` (150,111 frames of the movie and own runs, item 1-1-c-7-1-2): no frame starts below `2048 + 16·top + 256`, so the premise of `farNear` never holds on them, and no frame ends below 2048. The least position in the room was 3552 (`room-pair-check`, earlier).

## Assumptions (not proved in Lean)

* `farNear` (one frame, new): a frame up to `t₀` that starts between 8 px and 11.5 px ends at 8 px or more. The left wall keeps him there. The proof would need the collision routine with the wall's blocks, the 1 bits of the map, which [the block map](c-7-12-RoomMap.md) does not prove.

The field `far` is gone.

**Files.** `Theorems/FrameTime.lean`, `Theorems/RoomJoin.lean`, private `Proof/RoomJoin.lean`.
