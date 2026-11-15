[← Back](README.md) | [English](a-5-10-UpClean.md) | [Japanese](a-5-10-UpClean-ja.md)

# One condition on each instruction up to the pipe

**Claim.** Four conditions on the instructions of the frames from control to the vertical pipe's entry were fields of `Route.Run`. They follow from one field,
`chg.upCleanU`: each instruction of each frame `n` with `1 ≤ n < a₁` meets `CleanK` of one guard `GU`, the union of the four guards.

`a₁` is the entry of the first change: the first frame from frame 1 on that begins without control (`Route.Base.a₁`). `q` is the move routine's store of the fraction
(`FrameKeep.spotOf`). `tr(n, j)` is the machine after `j` instructions of frame `n` of the run.

```
GU        :=  the guard of PipeWrites, with  prot(GU) = prot(EntryKeep.guardOf) ++ prot(LagPause.guardP p) ++ prot(FrameKeep.guardE)
              p = the pause byte that the NMI tests (CtrlKeep.pauseI)
CleanU(m) :=  CleanK(GU, q, m)     if qCheck
              Clean(GU, m)         if not qCheck
upCleanU  :   ∀ n,  1 ≤ n < a₁  →  ∀ j,  CleanU(tr(n, j))
```

`CleanK(G, q, m)` is `Clean(G, m)`, but a store at `q` with the index `X = 0` is not asked. `qCheck` is a check on the ROM: the instruction at `q` is `STA abs,X`,
its target with `X = 0` is a byte of RAM, the guard of `EntryKeep` does not protect it, and it is not `p`. On this ROM `qCheck` holds (private `up_q_check`), so
`CleanU = CleanK(GU, q)` (private `up_clean_iff`).

From it (`Route.lean`, `UpClean.lean`):

```
Run.upClean₁   :  ∀ n, 1 ≤ n < a₁ → ∀ j,  Clean(EntryKeep.guardOf, tr(n, j))                       the old field chg.upClean₁
Run.entryIx    :  ix(E) < a₁                                                                   the entering frame is before a₁
Run.lagsClean  :  ∀ n, 1 ≤ n < ix(E) → ∀ k,  Clean(LagPause.guardP g, tr(n, k))                  the old field pipe.lags.clean
Run.pipeClean  :  ∀ j,  Clean(PipeWrites.guardOf, tr(ix(E), j))                                  the old field pipe.clean
Run.pipeReal   :  ∀ t, 1 ≤ t ≤ N, t < E → ∀ k,  CleanK(guardE, q, tr(ix(t), k))                 the old field pipe.opening.cleanK
```

`E` is `pipe.E`, the counted entering frame, and `ix(t)` the frame of the run where the counted frame `t` begins. `g` is the pause byte of `pipe`; `hg : p = g` is a
field of the checks of the opening (`OpenFrames.Checks.pause`).

Lean: `Theorems/UpClean.lean` (`guardU`, `qCheck`, `CleanU`, `at_q`, `clean_of_U`, `cleanE_of_U`, `upClean₁_of`), `Theorems/StepPrg.lean` (`step_prg`, `trace_prg`,
`run_prg`), `Theorems/Route.lean` (`Run.prg₁`, `Run.upClean₁`, `Run.entryIx`, `Run.lagsClean`, `Run.pipeClean`, `Run.pipeReal`), private `Proof/UpClean.lean`
(`up_q_check`, `up_clean_iff`, `native_decide`, under 1 s).

## How it works

* **The same guard but the protected bytes.** The four guards are the guard of `PipeWrites` with more protected bytes. They have the same idle loop, the same `late`
  and the same jump tables (`UpClean.SameW`). So `CleanK` of `GU` gives `CleanK` of each of them (`UpClean.cleanK_sub`, from `FrameKeep.cleanK_sub`). This is already
  the old `opening.cleanK` (`cleanE_of_U`).
* **The store of the move routine.** Three of the guards ask `Clean`. `CleanK` is `Clean` but at `q` with `X = 0` (`FrameKeep.clean_of`). At `q` with `X = 0` the
  machine runs the ROM's program, so its instruction is `STA abs,X` and its target is `tq`, the word after `q` in the ROM (`at_q`). `qCheck` says that `tq` is a byte
  of RAM that none of the three guards protects. So the store is `Plain` for each of them (`clean_of_U`). This store writes the player's fraction, which `guardE`
  protects and the three do not.
* **The machine runs the ROM's program.** No step of the CPU changes the program or its mask (`StepPrg.step_prg`). This is proved for each part of the CPU and for each
  of the 256 entries of `opTable`, as `StepWrites` does for RAM. So along a frame (`trace_prg`) and along a run (`run_prg`) the program is that of frame 1, and frame 1
  begins in the idle loop with the ROM's program, from the press of Start on the title (`Run.prg₁`).
* **The frames are the same** (`Run.entryIx`). The four conditions speak of frames up to `pipe`'s entering frame `ix(E)`. If `a₁ ≤ ix(E)`, look at frame `a₁ − 1`.
  It is frame 0, or a counted frame of `pipe` before `E`, or a frame not counted between them. Frame 0 ends in control (`title`). A counted frame ends in control
  (`lags.ctl`). A frame not counted ends paused, so it does not call the mode's routine, and it keeps the routine (`Lags.known_end`); for this it starts in control
  (`Run.upStart₁`) and its instructions are `Clean` with the pause byte, by `upCleanU`, since `a₁ − 1 < a₁`. So frame `a₁` begins with the routine of control. But it
  begins with the pipe's routine: the routine byte is a byte of `entryRest₁`, and the reference entry has the pipe's routine there (the list check of `EntryKeep`).
  The two routines differ. So `ix(E) < a₁`. With the definition of `a₁` this is `ix(E) + 1 = a₁`; only the bound is used.
* **Why the `if`.** `Run.upStart₁` and `Run.entry₁` take only the checks `hB` and `hK`, and about 20 theorems of other parts use them. `qCheck` is not among those
  checks. With the `if`, they need no new argument: if `qCheck` fails, `CleanU` sets nothing apart. On this ROM it holds, and the field asks `CleanK(GU, q)`.

## Measured on real frames

`up-clean-u FM2` (exit 0) runs the runs of `up-clean-union` (part b, round 13) with the guard `GU` of the Lean statement, and again with part e's new byte of this round
(the speed, `speedE` in `FrameKeep.guardE`) added: the merged guard.

| runs | frames (paused) | instructions | against `CleanU` | against the merged guard | the store at `q` with `X = 0` (`Plain` for `EntryKeep` and `guardP`) |
|---|---|---|---|---|---|
| the TAS, 368 frames to the entry | 368 (0) | 1,917,255 | 0 | 0 | 368 (368) |
| the reference entry | 440 (0) | 2,256,005 | 0 | 0 | 440 (440) |
| 300 random runs from control | 127,841 (5,390) | 530,759,258 | 0 | 0 | 122,439 (122,439) |
| 300 random runs from frames of the TAS | 75,241 (4,746) | 353,240,139 | 0 | 0 | 70,476 (70,476) |
| the reference with 0 to 39 frames of standing | 17,600 (0) | 90,225,074 | 0 | 0 | 17,600 (17,600) |
| total | 221,490 (10,136) | 978,397,731 | 0 | 0 | 211,323 (211,323) |

`qCheck` is true. None of the four old conditions fails either; `CleanK` of `guardE` holds on every frame, not only on the counted frames 1 to 32. 40 runs enter
the pipe. The run takes about 14 minutes.

## What the union asks beyond the four

The four old conditions asked:

| field | guard | frames |
|---|---|---|
| `chg.upClean₁` | `EntryKeep.guardOf` (124 bytes) | `1 ≤ n < a₁` |
| `pipe.lags.clean` | `LagPause.guardP` (48 bytes) | `1 ≤ n < ix(E)` |
| `pipe.clean` | `PipeWrites.guardOf` | the entering frame `ix(E)`, up to the write |
| `pipe.opening.cleanK` | `FrameKeep.guardE` (59 bytes), `CleanK` | the counted frames 1 to 32 |

`GU` protects 134 bytes (135 with part e's speed byte). The guard of `EntryKeep` already protects the pause byte of `guardP` (the same byte), so on the entering frame
nothing is new for it. What is new: **no store through an index or a pointer writes the 10 bytes of `guardE` that neither the guard of `EntryKeep` nor `guardP` protects**
(A and B, A and B of the frame before, the moving direction, the running speed, the stored speed `|v|`, the collision bits, the swimming flag, the change of size, the
castle flag, the player's fraction but at `q` with `X = 0`; 11 with part e's speed), **on the frames that are not among the counted frames 1 to 32**: the frames not
counted before the counted frame 32, and every frame after it up to the entry. At `q` with `X = 0` the union asks less than `upClean₁` did: nothing. On this ROM that store
is `Plain` for the guard of `EntryKeep` (`qCheck`), so it is the same.

## Assumed (not proved in Lean)

* **`chg.upCleanU`**: the condition above on each instruction of the frames from control to the entry. It replaces `chg.upClean₁`, `pipe.lags.clean`, `pipe.clean` and
  `pipe.opening.cleanK`. A run that fills a slot whose bytes the guards protect (enemy slots 3 and 6, fireballs, blocks 2 and 3, misc objects, cannons, some scores:
  part b's list) is outside the theorem, as before.
* Proved now: that the store of the move routine is `Plain` for the three guards of `Clean` (`qCheck`, by the ROM), and that the four conditions speak of the frames
  before `a₁` (`Run.entryIx`).
* Not proved: anything about the indices of the stores. `upCleanU` is a condition on each instruction, as the four were.

**Files.** `Theorems/UpClean.lean`, `Theorems/StepPrg.lean`, `Theorems/Route.lean`, `Theorems/PipeFrames.lean` (`Lags.CleanP`), `Theorems/OpenFrames.lean`
(`RealB`, `Real`), `Theorems/HurryStart.lean` (`Chg₁.upCleanU`), private `Proof/UpClean.lean`.

**Reproduce.**
```
cd git
.lake/build/bin/smbrta up-clean-u FM2 quick    # the guards and qCheck
.lake/build/bin/smbrta up-clean-u FM2          # the runs (minutes)
```
