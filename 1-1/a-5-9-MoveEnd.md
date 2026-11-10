[← Back](README.md) | [English](a-5-9-MoveEnd.md) | [Japanese](a-5-9-MoveEnd-ja.md)

# The position at the end of the move

**Claim.** The walk of [one whole frame](a-5-2-PipeWrites.md) now splits the position where the move ends (`PlayerSubs`), not at the entry for the right foot. From there it follows the position through the scroll handler, the screen bits, the bounding box, the head's check and the left foot, to the right foot. So in a frame that enters, the position at the end of the move, before the write, is not left of the left end of the pipe's window. This is the frame model's `P₂`.

The old assumption `pos` ("`P₂` is the position at the entry for the right foot") is gone. Two assumptions take its place:

* `moved`: `P₂` is the position at the end of the move. This is how the frame model builds `P₂` (`FrameModel.frame_read`).
* `edge`: up to the write, the frame does not come to two places: the scroll handler's store of the position, and the routine of the head's collision with a block.

The names are those of [one whole frame](a-5-2-PipeWrites.md). `tr_t(j)` is the machine `j` instructions into frame `t`. `posP(m) = 256·(256·page(m) + x(m)) + subpixel(m)`, and `L = 256·L_px` is the window's left end.

```
w_edge          :=  the scroll handler's STA of Player_X_Position  (its part KeepOnscr puts him back at the screen's edge)
h               :=  the routine of the head's collision with a block  (PlayerHeadCollision)
G_S             :=  guardOf  with  subs := PlayerSubs,  cuts := [w_edge, h]

HypG(m)         :=  (subs = 0  →  AtEntry(m) → px(m) < L_px)  ∧  (AtRead(m) → TilesOK(m))
                    ∧  (subs ≠ 0  →  pc(m) = subs → px(m) < L_px)  ∧  pc(m) ∉ cuts
```

The two places are found in the ROM: `w_edge` is the first `STA` of `Player_X_Position` in the routine that `PlayerSubs` calls first; `h` is the routine called just before the collision routine's `JMP DoFootCheck`. No symbol was added.

```
entry_right_of_leftS :  ruleCheckS,  Enters(m, i),  FrameStart(m),
                        (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))) ∧ pc(tr(j)) ≠ w_edge ∧ pc(tr(j)) ≠ h)
                        →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ L_px ≤ px(tr(j))
rule_on_framesS      :  ruleCheckS,  start, clean, tiles as in rule_on_frames,
                        edge:   ∀ t,  Enters(fm t, inp t) → ∀ n, WriteStep(n) → ∀ j ≤ n,  pc(tr_t(j)) ≠ w_edge ∧ pc(tr_t(j)) ≠ h
                        moved:  ∀ t,  Enters(fm t, inp t) → ∀ n j,  WriteStep(n) → j ≤ n → pc(tr_t(j)) = PlayerSubs → P₂(t) = posP(tr_t(j))
                        →  ∀ t,  Enters(fm t, inp t)  →  L ≤ P₂(t)
pipe_frame_check (private)   :  ruleCheckS(sy, m₀) = true (native_decide)
pipe_no_entry_real (private) :  Enters(fm E, inp E),  FrameStart(fm E),  clean, tiles, edge, moved,  openP, openB,  the frames read from the machines  →  367 < E
```

`ruleCheckS` is `PlayerSubs ≠ 0` and the check of the walk with `G_S`. The old `entry_right_of_left` and `rule_on_frames` (the split at the right foot) are kept; `Route` no longer uses them.

The theorems with no ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/PipeWrites.lean` (the fields `subs`, `cuts` of `Guard`; `splitPos`, `cov_split`, `guardS`, `ruleCheckS`, `entry_right_of_leftS`, `rule_on_framesS`), `Theorems/Route.lean` (`Pipe.edge`, `Pipe.moved`), private `Proof/PipeWrites.lean`.

## How it works

* **The split.** At `PlayerSubs`, under `px < L_px`, the walk makes one piece for each value of the position: 916 pieces. The proof is the one of the split at the right foot (`cov_split`).
* **The cuts.** At `w_edge` and `h` the walk has no piece: `HypG` says that the frame does not come there.
* **The search (no part of the proof).** From `PlayerSubs` to the collision routine's return, the search keeps the position and keeps states apart by it. It forgets the position at the return, at the exits of the foot check, and at the read of the right foot.
* **Why the head's collision is cut.** It stores through an index whose target the walk does not know (`Block_State,X` with `X = SprDataOffset_Ctrl`, the screen's buffer). After such a store the walk forgets every byte outside `Prot`, the position too. The position cannot go into `Prot`: the move itself stores it through an index (`STA SprObject_X_Position,X`), so `Clean` would fail on the frames in control. Its routine can also set the vertical speed to 0 (a block that does not break), so the walk cannot exclude a landing in the same frame.
* **Without the cut at `h`**: 223,149 failures, at paths that come to the write with the position not known. With both cuts: 0.

**Size.** 3,209,542 steps, 300,327 forks, 0 failures, table 150,681. As a program: the search about 8-11 s, the check about 22-30 s. The old walk was 1,504,949 steps, its check about 6 s.

## Checked on real frames

This is a program (`pipe-subs-check`). The runs are those of `pipe-rule-check` on [one whole frame](a-5-2-PipeWrites.md).

| run | frames | start in control | frames that enter | frames in control at a cut place |
|---|---|---|---|---|
| the TAS up to the entry | 368 | 368 | 1 | 1 |
| the TAS after the entry | 1,300 | 351 | 0 | 1 |
| from states before the entry: walk, then Down | 5,480 | 5,480 | 161 | 0 |
| from states before the entry: jump, land with Down | 25,308 | 24,161 | 14 | 0 |
| from states before the entry: random inputs | 26,855 | 26,295 | 1 | 7 |
| the same, overwritten to a big Mario | 9,000 | 8,570 | 0 | 21 |

In all 177 frames that enter:
* no instruction before the write is at `w_edge` or `h` (`edge`);
* the frame comes to `PlayerSubs` once before the write;
* there `posP = posP(at the frame's start) + 16·v`, with `v` the speed there: the move of the frame model (`P₂ = P + 16·v₂`);
* there `px ≥ L_px`, and `px` is the position at the entry for the right foot.

`FrameStart`, `Clean` and `TilesOK` fail on no frame, as before.

## What changed

* **No longer assumed:** that nothing between the end of the move and the foot check moves him. The walk proves it for the scroll handler except its store at the edge, the screen bits, the relative position, the bounding box, the head's check and the left foot.
* **New:** `edge`, a condition on the instructions of the frame that enters, up to the write.
* **`moved`** says what `P₂` is. It is the definition the frame model uses when it builds a `Frame` from a real frame.

## Assumed (not proved in Lean)

* **`moved`.** It is part of making `Frame` from real frames (item 0-0-0-3-1).
* **`edge`.** The frame that enters is not at the screen's edge and does not bump a block with its head, up to the write.
* The other assumptions of [one whole frame](a-5-2-PipeWrites.md): `FrameStart`, `Clean`, `TilesOK`.

**Files.** `Theorems/PipeWrites.lean`, `Theorems/Route.lean`, private `Proof/PipeWrites.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta pipe-subs-search       # the walk with the split at the end of the move: the search and the check, about 1 minute
.lake/build/bin/smbrta pipe-subs-check FM2    # the check and the conditions on real frames, about 3 minutes
```
