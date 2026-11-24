[← Back](README.md) | [English](e-2-10-3-27-SideFacts.md) | [Japanese](e-2-10-3-27-SideFacts-ja.md)

# Part f's facts of the two bytes on the route

Round 36 asked the field `sideW` only on a frame without `SideAcross.FactsAt` ([The stores that may reach the side timer, with two bytes kept across frames and the castle's start row](e-2-10-3-26-SideAcross.md)), and proved from part f's fields that no frame of the route lacks it (`SideAcross.Run.factsAll`), but the route did not use that proof. Here the route passes it to part e, and the field `sideW` is gone.

**Claim (round 37).** Write

```
b, c        = the block buffer's column (BlockBufferColumnPos), the block objects' offset (SprDataOffset_Ctrl), as RAM indices
InvB(m)     := m[b] < 32 ∧ m[c] ∈ {0, 1}
MissB(m)    := a store through an index or a pointer at m writes neither b nor c
FactsAt(M)  := InvB(M) ∧ ∀ k, frame(trace M k) = frame(M) → MissB(trace M k)
K           = the frames of part f's run up to the touch's frame (PoleJoin.Run.keep): all n, inp n for n < ix g
```

1. `SideAcross.Run.factsK`: for a run `R` of `PoleJoin.Run`, with part f's checks on the ROM (`poleCheckZ`, `keepCheckOf`, `bcolCheck`, `PoleNear.nCheck`), the machine at control (`Start`, `fracCheck`, `AtCtl`), the two bytes and the map at control (`PoleBcol.BInv`, `PoleTileKeep.watchB`, `PoleTileWalk.ColMap`), and the two checks that the two pairs of RAM indices are the same (`he1`, `he2`):

```
∀ n < ix g,  FactsAt(all n)          (every frame up to the touch's frame, counted or not)
```

   It is `SideAcross.factsAt_frames` on part f's fields `bKeep` (through `Run.bNoW`), `keepB` and `bufAll`. `Run.factsAll` (the counted frames) now follows from it.
2. `SurfaceFrames.AreaRun` has a new part `facts : ∀ n < ix g, FactsAt(all n)`, and `OnFrames.areaRun` takes it as a hypothesis `hF`.
3. `OnFrames.sideWAt` (round 33's form of the field: at every store that may reach the side timer) is now one walk on every frame: `SideAcross.near_sideA` with `AreaRun.facts` and the field `castleRow`. The field `sideW` is gone.

Axioms of the changed theorems: `propext`, `Classical.choice`, `Quot.sound`. No game data: `b` and `c` are symbols.

**Fields.** Removed: `OnFrames.sideW`. Added: none. The route gains no field: `hF` is proved in the private proof of the route from `R.pole` (`SideAcross.Run.factsKM`: `Run.factsK` with the box written `⟨M, dx, dy, rows⟩`, as `PoleJoin.touch_castle` writes it, so that the private proof's facts on its machine match without unfolding it), with the facts at control that it already had (`PoleTileCtl.colMap₀`, `PoleTileCtl.watch₀`) and one more (`PoleParserRun.bInv₀`, with the check `pole_bcol_rows` that the route already had), and the two checks `he1`, `he2` (`native_decide` on the ROM).

**No cycle.** `factsAt_frames` takes only part f's frames `FrameKeep.Frames` and part f's fields; none of them is proved from `OnFrames`, so none uses `sideW` or `sideWAt`. `PoleBcol.frames_bcol`, `PoleTileKeep.frames_keepY`, `PoleNear.near_frames` take no `OnFrames` either.

**The theorems that take `hF`.** Each theorem that makes an `AreaRun`, and each theorem that uses one of those, takes `hF` and passes it on:

- part e: `OnFrames.areaRun`, `quiet_upto`, `surface_of_frames`;
- part f, `PoleJoin`: `Run.reads`, `Run.next`, `Run.moved`, `Run.stop_step`, `Run.stored_step`, `Run.inRange`, `hB_run`, `base_late`, `touch_ge`, `direct_castle`, `castle_ge`, `touch_castle`;
- part f, `PoleParserRun`: `edgeLow_run`, `amount_run`, `invJ_run`, `inv_run`, `colMono_run`, `tilesCol_run`, `colEdge_run`, `tilesCol_route`.

In part f's theorems `hF` comes right after `hc0` (the machine at control in control), in part e's right after `hst` (each frame starts in control). The private proof's `pole_join`, `pole_touch` and `pole_touch_castle` take it too.

**One check less.** `numbersCheck` had `SideLoop.lCheck` (round 35's walk, about 15 s natively), which `sideWAt` used only on frames without `FactsAt`. It is gone, with `Numbers.rangeC` and `AreaRun.rg`.

**Measured.**

| check | what | result |
|---|---|---|
| `surface-frames-check FM2 200` | frames without `FactsAt`; `castleRow`; `sideWAt (a theorem)`; frames that start with the scroll lock not 0, with the timers' control not 0 (new measures) | exit 0 (1:10:35, 564 MB): 8 sets, 239,510 frames; 0 failures (`castleRow`, `sideWAt (a theorem)`, and round 36's `sideW` measured); 0 frames without `FactsAt`; 0 frames that start with the scroll lock not 0, 0 with the timers' control not 0; the rest of the output is round 36's |
| `edge-real FM2 256` | as round 36 | exit 0 (48:27): the output is round 36's but the times |
| `route-check` (TAS, 1089 `02808080`, 996 with round 23's jump run), `up-clean-u`, `keep-frames-check 100`, `pos-keep-real 64`, `collide-real 200`, `pos-after-real 200` | as round 36 | all exit 0; the outputs are round 36's but the times |

**The castle's start row (not proved).** The field `castleRow` stays. Measured on the TAS and on the ROM:

- the area data's pointer has one value on all frames above ground; the area's data above ground is a list of objects of 2 bytes after the header, with an end mark; one of them is a castle, whose start row is within the bound of `castleRow`;
- the parser's offsets into the data (`AreaDataOffset`, the three of `AreaObjOffsetBuffer`) are even on every frame of the TAS; the castle is loaded into an object's slot before the touch;
- on the ROM, an object at an even offset of the data (up to 254) that the parser takes for a castle has start row at most 10; at an odd offset one does not.

So a walk that knows the pointer and that the offsets are even, and that splits each offset into its values where the parser loads it, would know which object the parser decodes, and the castle's row. Two searches of such a walk (no part of the proof):

| search | result |
|---|---|
| the walk of `near_sideA` without the split at the castle's loop, the pointer known and the offsets' bit 0 known at the scroll handler's call, the offsets split into their values at the parser's two loads and forgotten (but bit 0) at the objects' routines | 39 failures in the first 3,000 table states: the pointer is lost at 4 stores of the enemies' code through `X` to the zero page, where the walk does not know `X` (the table's states there have `X` from 0 to 255) |
| the same, with the pointer protected (as if no store through an index or a pointer wrote it) | no failure in the first 3,000 table states, but the whole search did not end in 21 minutes and passed 5.8 GB (round 36's walk: 17 s) |

To prove `castleRow` this way, a walk needs (1) the pointer kept: no store through an index or a pointer writes it, which the walk shows only with `X` bounded in the enemies' code; (2) the offsets even at every frame's start, kept from frame to frame (the walk's state at the frame's end); (3) a search far smaller than the split into values gives.

**The scroll lock, the timers' control, the injury timer (not proved).** `clampR` needs the scroll lock 0, case B of `Moves.stop` the timers' control 0, and the place byte of `endKeep` the injury timer 0, at frames that the route reaches. Round 36's walk has, after the scroll handler, no store through an index or a pointer that may write the scroll lock, one (the background's loop of `RenderUnderPart`) for the timers' control, and 12 of the enemies through `X` for the injury timer. The program writes each of them by its address too: the scroll lock in the scroll lock's area object (which only the area's data selects), when he falls below the screen, and at the flagpole; the timers' control when he is hurt or dies (on the same frame as a store of the routine, which `FrameKeep.Frames.noStore` excludes before the touch's frame), and it counts down only from a value that is not 0. A proof needs each byte at control, a walk that knows its value from the frame's start to its end, and, for the scroll lock, the area's data as above. On the 239,510 frames of `surface-frames-check FM2 200` no frame starts with the scroll lock or the timers' control not 0.

**What is not proved here.**

- `castleRow` (above).
- `FactsAt` rests on part f's fields `bKeep`, `keepB`, `bufAll`, which are assumed.

**Files:** changed `Theorems/SideAcrossRun.lean` (`Run.factsK`, `Run.factsKM`; `Run.factsAll` from `Run.factsK`), `Theorems/SurfaceFrames.lean` (`AreaRun.facts`, `OnFrames.areaRun`, `OnFrames.sideWAt`, the field `sideW` removed, `numbersCheck` without `SideLoop.lCheck`, `quiet_upto`, `surface_of_frames`, `movesScan`'s two measures), `Theorems/SideAcross.lean` (a sentence), `Theorems/PoleJoin.lean` and `Theorems/PoleParserRun.lean` (`hF` in the theorems above), `Main.lean` (the private proofs: `hF` in `pole_join`, `pole_touch`, `pole_touch_castle`, the route's `have hFa`, and the import of `Theorems.SideAcrossRun`; two counts in `surface-frames-check`).
