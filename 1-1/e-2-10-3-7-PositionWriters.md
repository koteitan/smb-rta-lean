[← Back](README.md) | [English](e-2-10-3-7-PositionWriters.md) | [Japanese](e-2-10-3-7-PositionWriters-ja.md)

# The instructions that write the position after the scroll handler

**Claim.** Take a frame in control, with the hypotheses of the speed's walk (`CollideKeep.speed_end`). Let Q be the machine at the scroll handler, at instruction q. From q to the frame's end the frame meets `FrameW` (`writers_end`):

- Each machine R of the frame from q on meets `AtW`:
  - R writes the position's pixel, page or fraction by its address only at an instruction of the list `writersIn`.
  - At the entry of the push (`ImpedePlayerMove`) and at the entry of the clamp at the screen's edge, R is `Good`, its speed is v(Q) or 0, and the call returns to an instruction outside the two calls.
  - At the clamp's entry, Y(R) ∈ {0, 1}.
  - R's instruction is in the program's half of the address space.
- A step into the inside of the two calls (`innerP`: after the push's entry up to its return, and the clamp's pixel and page stores) comes from the inside or from one of the two entries.
- If the frame ends with the speed v(Q) and v(Q) ≠ 0, every machine of the frame from q on has the speed v(Q) (`FrameW.kept`, by `speedKW`: a step of the walk never starts to follow the speed again).

The walk is the speed's walk from Q to the frame's end, on the same table. It asks these things at each of its states and at each of its steps (`okW`, `walkKW`). The private check proves them on the ROM (`position_writers_check`; the private file builds in about 10 s). It also proves that `writersIn` has nine instructions (`position_writers_count`), that five of them are outside the push and the clamp (`position_writers_outside`), and the small check `wCover` (`position_writers_cover`).

The nine instructions are these. Two are in the clamp (pixel, page). Two are in the push (pixel, page). Two are in the routine that moves the player with a horizontal platform (pixel, page). Two are in the routine that puts the player on a vine (pixel, page). One is in the loop of a castle level, which sends the player back by some pages.

**`Ready` at every reached cut.** `PositionDispatch.partition` needed `Ready` at every reached cut as a hypothesis. Here it follows from `FrameW` and four conditions on single instructions from q to the frame's end (`ready_all`):

1. none of the five outside instructions runs;
2. an instruction that is not plain does not write the position (`Ordinary`); a plain one writes nothing, or only the stack, or one byte by its address (`plainOp`);
3. at the push's entry, 256 ≤ P(R) and P(R) + 256 < 2²⁴;
4. at the clamp's entry, Y = 0.

The proof has three parts. A reached cut is never inside the two calls (`reached_outside`): Q is outside, an ordinary step does not step into the inside, and a call returns outside. At a plain instruction that is not one of the nine and not an entry, `Ready` holds (`ordinary_plain`, `ready_ordinary`). At the entries, `ready_impede` and `ready_clamp` give `Ready`: at the left edge the clamp puts the player exactly at the edge (the check reads this from the ROM), so its target is in the position's range. So the frame from q to its end is a chain of ordinary steps, pushes and clamps whose effects add up to P(end) − P(Q) (`chain_of`). On the frames of the run above ground, every counted frame before the touch meets `FrameW` from its scroll handler on (`writersAt`, from the same hypotheses as `SurfaceFrames.OnFrames.collideAt`, the check `wCheck`, and the scroll handler's machine in the frame).

**`AfterP.keep` from conditions.** Take a frame with v(Q) > 0 that ends with v(end) = v(Q). Add to the four conditions one more: at each clamp's entry R, the target is P(R). Then P(end) = P(Q) (`keep_of`). A push that moves sets the speed to 0, so with `FrameW.kept` no push moves him (`chain_zero`), and each clamp adds 0. This is the field `AfterP.keep`; the field stays, because the five conditions are not yet proved.

**A correction.** Round 20 reported one store outside the push and the clamp: the page store of the platform routine. That search looked only at the states at the start of a branch. The straight runs of up to 64 instructions between them were not looked at. The walk here asks at every state. It finds five stores outside the push and the clamp.

**What is not proved.**

- The four conditions of `ready_all`. They are on single instructions and they held on every measured frame (below), but they are hypotheses. To prove 1, the walk needs facts of the level: no horizontal platform in an enemy slot, no vine tile, no loop command. The walk does not know these bytes. They come from the level's data through the area parser and the enemy parser. For 2: in the search of round 20 (the walk of the subspeed, with every byte of `FrameKeep.guardE` protected), 402 instructions that store through an index may write the position, because the index is not known there, and `FrameKeep.guardE` does not protect the position; keeping the object offset known in that search leaves 394 of them. Seven more store through a pointer.
- How many calls a frame makes, and in which order. `CollideS.P` and `AfterP.stop` need it: after a push that stops him, a second push could move him back. A frame with one clamp and then a push to the right could break `CollideS.P`. Such frames were not seen. Condition 1 does not exclude the platforms' own calls of the push.
- The clamp's condition of `keep_of`: at the clamp of a frame with v(Q) > 0, the target is the position.
- The relation of the clamp's edge to the frame's start (d ≤ 0). On real frames the left edge never moved before a clamp (the screen does not scroll on a frame with a clamp), so d = left edge(M) − pixel(M). Then d ≤ 0 needs left edge(M) ≤ pixel(M) at the frame's start M. That condition links a frame to the one before; two cuts of one frame do not give it.
- `CollideS.P` and `AfterP` stay fields. No field is added, removed or widened.

**Measured.** The TAS from frame 852, 64 random runs of 300 frames and 48 runs that hold Left at the screen's left edge give 26,638 frames that come to Q.

| after Q | frames |
|---|---|
| no call | 19,682 |
| one clamp at the left edge | 6,738 |
| one push of 1 px left | 201 |
| one push that does not move | 12 |
| one push of 1 px right | 5 |

The four conditions of `ready_all` held at every instruction from Q to the frame's end: the five outside instructions never ran; 3,253,671 steps of instructions that are not plain wrote no position byte; the margins held at all 218 entries of the push; Y was 0 at all 6,738 entries of the clamp. No frame has two calls. No frame has a clamp at the right edge. On real frames the position is written after Q only by the stores of the clamp and of the push. Every clamp moved the position right by 0 to 1 px from P(Q); on the 469 clamps of frames with v(Q) > 0 the target was P(Q) itself. The clamp's pixel gap d was in [−2, 0]. At every frame start M: 0 ≤ pixel(M) − left edge(M) ≤ 113, and right edge(M) − pixel(M) ≥ 142. Here pixel is the whole-pixel coordinate (256 per page). The screen scrolled on 3,726 of the frames, never on a frame with a clamp, and the left edge at every clamp's entry was the left edge at the frame's start. The player's screen position that the scroll handler reads was pixel(M) − left edge(M) (mod 256) on every frame. The enemy slots in use held goombas and the flagpole's flag only. The loop command was 0 at every frame start.

**File:** `Theorems/PositionWriters.lean`. Private: `Proof/PositionWriters.lean` (generated by `genPositionWriters` in `Main.lean`).
