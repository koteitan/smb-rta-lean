[← Back](README.md) | [English](f-6-21-GuardE.md) | [Japanese](f-6-21-GuardE-ja.md)

# Each instruction of the frames up to the touch

**Claim.** The run assumes one condition on each instruction of each frame from control above ground up to the touch, counted or not: `keep.cleanE`. It is `CleanK` of a guard `guardE`. Under it, no store through an index or a pointer writes a protected byte. The player's own store of the fraction is not asked. This round `guardE` protects five more bytes than `guardF` did: A and B, A and B of the frame before, the moving direction, the running speed and the stored speed. So the field `spareE` of [the frames above ground](e-2-SurfaceFrames.md) is gone. It was the same five bytes, asked of each instruction.

The two theorems that used `spareE` are the walk of A and B of the frame before (`PrevKeep.prev_end`) and the walk of the three horizontal bytes from the scroll handler to the frame's end (`AfterKeep.keepH`). They ask `CleanK` of `guardF` and, of every instruction, `SpareAB` or `SpareH`. They use both only to get `CleanK` of the guard of their walks. That guard does not ask the player's own store of the fraction either. So `CleanK` of `guardE` gives it directly. `GuardE.prev_endE` and `GuardE.keepHE` are the same two theorems with the one condition `CleanK_E`: the same walks, the same checks on the ROM, the same proofs.

`tr(n)` is the machine `n` instructions into a frame. `Prot_K`, `Prot_F`, `CleanK`, `q` are those of [One whole frame in control](f-6-19-FrameKeep.md). `t(m)` is the target of a store through an index or a pointer at `m`. `idx(t) = t mod 2048`.

```
spareE           :=  {A_B_Buttons, PreviousA_B_Buttons, Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}
Prot_E           :=  edgeE  ∪  stateE  ∪  faceE  ∪  spareE  ∪  collE  ∪  speedE  ∪  vertE  ∪  Prot_F    (guardE, 70 bytes; round 26: edgeE = the pixel and the page of the screen's left edge, 1-1-e-2-10-3-13; round 27: and the platforms' force on the scroll, 1-1-e-2-10-3-14; round 15: stateE = {Player_State, VerticalForce}, faceE = {PlayerFacingDir, Player_X_MoveForce}; round 13: collE = {Player_CollisionBits}; round 14: speedE = {Player_X_Speed}, vertE = {VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump}; so `spareC`, `spareV` and four bytes of `vAfter` of part e come from `keep.cleanE`)
CleanK_E(m)      :=  CleanK(m) with Prot_E for Prot_K
keep.cleanE      :  n < ix g  →  ∀ k,  CleanK_E(tr_n(k))                               (the field; it was cleanF, with Prot_F)

cleanK_of_E      :  CleanK_E(m)  →  CleanK_F(m)
Frames.cleanF    :  keep  →  n < ix g  →  ∀ k,  CleanK_F(tr_n(k))                       (a theorem now)
cleanK_sub       :  CleanK_G(m),  Prot_G' ⊆ Prot_G,  the other parts of G' those of G   →   CleanK_G'(m)
cleanAB_of_E     :  CleanK_E(m)  →  CleanK of PrevKeep.guardAB (m)                       Prot = {A_B_Buttons, PreviousA_B_Buttons} ∪ Prot_F
cleanH_of_E      :  x ∈ hI,  CleanK_E(m)  →  CleanK of AfterKeep.guardH x (m)            Prot = {x} ∪ Prot_F,  hI = {Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute}

SpareE(m)        :=  ∀ t,  t(m) = t  →  t < 0x2000  →  idx(t) ∉ spareE                  (AfterKeep.SpareE: the old field spareE)
spareE_of        :  CleanK_E(m),  ¬(pc(m) = q ∧ X(m) = 0)   →   SpareE(m)

prev_endE        :  ctrlCheck,  prevCheck v,  FrameStart_K(m),  (∀ n, CleanK_E(tr(n))),  (∀ n, ¬CtlStore(tr(n))),  AreaOK_v(m),  PrevOK(m)
                       →   PrevOK(frame(m, i))
keepHE           :  ctrlCheck,  hCheck v,  FrameStart_K(m),  (∀ n, CleanK_E(tr(n))),  (∀ n, ¬CtlStore(tr(n))),  AreaOK_v(m),
                    pc(tr(n₀)) = PlayerCtrlRoutine (the first time, in the frame)
                       →   ∀ k ≥ n₀,  pc(tr(k)) = PlayerSubs  →  ∀ x ∈ hI,  x(frame(m, i)) = x(tr(k))
```

`PrevOK(m)` says that bit 7 of A and B of the frame before equals bit 7 of A and B. `OnFrames.prevAll` and `OnFrames.movesAt` now use `prev_endE` and `keepHE` with `keep.cleanE`, in place of `prev_end` and `keepH` with `keep.cleanF` and `spareE`. No other signature changed.

## Why `CleanK_E` does not give `SpareE` everywhere

`CleanK` does not ask the store at `q` with `X = 0`: that is the player's own store of the fraction, and the walks know its target. `SpareE` asks every instruction. So `CleanK_E` gives `SpareE` on every instruction but that one (`spareE_of`). At that one the target is the fraction's byte, so `SpareE` holds on real frames. A proof of it needs the instruction at `q` from the ROM and that the program bytes of the machine do not change along a frame. There is no lemma for the second yet. It is not needed: the walks of `prev_end` and `keepH` do not ask anything of that store.

## Why a new guard

`guardF` is also the guard of walks of part e: `PrevKeep.guardAB` is `guardF` with A and B protected, `AfterKeep.guardH x` is `guardF` with `x` protected, and the first walk of `AfterKeep` uses `guardF`. Their tables come from searches that protect the bytes of `CtrlKeep.spareI`. Adding the five bytes to `spareK` would change these walks and their checks `prevCheck` and `hCheck`. So the five bytes are protected only in the condition on each instruction (`guardE`), not in a walk. No walk changed, no check on the ROM changed, and no private proof got longer.

## On real frames

`keep-frames-check FM2 100` checks `CleanK` on every instruction of real frames above ground, from control up to the touch, the touch's frame included, counted or not. This round it uses the guard `guardE` (exit 0, bad 0, 4 min 39 s). No store through an index or a pointer touches `Prot_E`, but the player's store of the fraction.

| run | runs | frames | instructions | touches | store not `Plain` |
|---|---|---|---|---|---|
| the movie from control to the touch | 1 | 240 | 1,203,506 | 1 | 0 |
| random inputs from control | 100 | 29,102 | 150,058,083 | 0 | 0 |
| random inputs from the movie's frames 1002 to 1091 | 400 | 46,025 | 183,000,496 | 216 | 0 |
| into the screen's left edge, then random | 120 | 35,945 | 193,591,853 | 0 | 0 |
| random inputs with a pause, from control | 100 | 37,395 | 107,816,920 | 0 | 0 |
| random inputs with a pause, from the movie's frames 1002 to 1091 | 400 | 76,106 | 250,174,812 | 241 | 0 |

`after-real FM2 100` of [the frames above ground](e-2-SurfaceFrames.md) checks `SpareE` on every instruction of real frames in control above ground, the player's store included (exit 0, 1 min 21 s). No frame has a store through an index or a pointer to a byte of `spareE`: 0 of 240 frames of the movie from control, 19,870 frames of random runs from control, 5,316 with Select and 10,376 with Start.

## Hypotheses (not proved in Lean)

* **`keep.cleanE`: `CleanK_E` on each instruction of each frame up to the touch, counted or not.** A condition on one machine. It holds the old fields `spare` and `spareE` of the frames above ground, and asks them of the touch's frame and of the `lag` frames too.

What stopped being a hypothesis: the field `spareE` of `OnFrames` (`PoleJoin.Run.frames.spareE`). What changed: the field `keep.cleanF` (`CleanK` of `guardF`) became `keep.cleanE` (`CleanK` of `guardE`, five more bytes); `Frames.cleanF` is a theorem.

**Files.** `Theorems/GuardE.lean` (new), `Theorems/FrameKeep.lean` (`spareE`, `guardE`, `cleanK_of_E`, `cleanK_sub`, the field `cleanE`), `Theorems/SurfaceFrames.lean` (the field `spareE` removed; `prevAll`, `movesAt`).

**To reproduce.**
```
.lake/build/bin/smbrta keep-frames-check FM2 100      # CleanK of guardE on real frames above ground (about 5 min)
.lake/build/bin/smbrta after-real FM2 100             # SpareE on real frames (part e)
```
