[← Back](README.md) | [English](a-5-4-3-3-5-OpenStore.md) | [Japanese](a-5-4-3-3-5-OpenStore-ja.md)

# A frame that ends in control does not store the routine, the mode or the task

**Claim.** A frame that starts in the idle loop in control and ends in control has no instruction that writes the routine, the mode or the task byte by its
address. So the field `noStore` of the first 32 counted frames is a theorem: each of them ends in control (`lags.ctl`).

`tr(k)` is the machine after `k` instructions of the frame of `m` with the input `i`. `CtlStore(x)` says that the instruction at the `pc` of `x` is a store, an
increment, a decrement or a shift of one of the three bytes by its zero page or absolute address (`FrameKeep.storesTo`). `ctl(x)` is `controllable`: the mode is
the game's, the task is the game core's and the routine is the player's control.

```
OpenStore.noStore_of_ctl :  storeCheck,  StartK(m),  (∀ k, CleanK_F(tr k)),  ctl(frame(m, i))   →   ∀ k,  ¬CtlStore(tr k)
OpenStore.keep_of_cleanK :  CleanK(G, q, x),  ¬(pc(x) = q ∧ X(x) = 0),  i ∈ prot(G),  no NMI pending,  pc(x) ≥ 0x8000,  the opcode at pc(x) is in wtOps
                            →   step(x)[i] = x[i]
Real.noStore             :  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t)   →   ∀ k,  ¬CtlStore(tr(t, k))            (the old field noStore)
```

`wtOps` are the ten opcodes of a store through an index or a pointer that the walks know (`PipeWrites.wTarget`). `CleanK_F` is `CleanK` of `FrameKeep.guardF`, which
`cleanK` gives. The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

Lean: `Theorems/OpenStore.lean` (`walkH`, `walkS`, `okW`, `storeCheck`, `keep_of_cleanK`, `runH`, `endS`, `noStore_of_ctl`), `Theorems/OpenFrames.lean`
(`Real.noStore`); private `Proof/OpenStore.lean` (`open_store_check`).

## How

Two walks cover the frame.

* **Up to the first store** (`walkH`): the walk of `FrameKeep` with the stores cut (`FrameKeep.walkKC`), from the frame's start. At an instruction that stores to one
  of the three bytes it asks that the second walk succeeds from there. If the frame has no such instruction, the walk comes to the frame's end, and there is nothing
  to show (`runH`).
* **From a store to the frame's end** (`walkS`). After a store to one of the three bytes it asks that the routine, the task or the mode is known not to be that of
  control (`OpenFlat.finX`). Every such store writes a value that the walk knows: death and injuries, the pipes, the flagpole, the vine, the axe, the hole. Then
  it forgets the three bytes, so the states after different stores are the same states. At every other instruction it asks that the step does not write the three
  bytes (`okW`).

So from the first store on, the machine is out of control: a fact about the machine, outside the abstract states (`endS`). At the frame's end it is out of control,
and the frame was said to end in control.

**A step that does not write the three bytes** (`okW`), two ways:

* the abstract state says so (`StepWrites.keepOK`: the instruction does not write, or pushes elsewhere, or its addresses are away from the three bytes);
* or the instruction is a store through an index or a pointer of `wtOps`. Its address may not be known to the walk. But `CleanK` says that its target is outside
  the bytes that the guard protects, and the three bytes are protected. One step changes RAM only where its instruction stores (`StepWrites.step_ram`), so the
  step keeps them (`keep_of_cleanK`). The move routine's own store with the index 0 is not asked by `CleanK`; there the walk knows the index, and the first way
  applies.

**The search's key.** Two routines load the value in `A` and then come to the same store (the two power-ups). A table that joins their states does not know `A`
(the join of 9 and 12 leaves 8 possible, the value of control). So near a store the key keeps the states of different `A` apart (`nearStore`). The key is no part
of the proof.

## First try, too large

One walk of the whole frame with a mark after the first store, the stored values kept to the frame's end (the walk of `OpenWalk` with two phases): 792,839 steps, a
table of 53,610 states, 261 s for the search. Each stored value makes its own copy of the rest of the frame. The two walks above forget the values and carry the
fact outside the states.

## The numbers

| | steps | failures | table | time natively |
|---|---|---|---|---|
| the search up to a store | 67,582 | 0 | 4,519 (39 states at a store, at 8 places) | 0.2 s |
| the search from a store | 124,935 | 0 | 6,030 | 0.4 s |
| `OpenStore.storeCheck` (both searches and both walks) | | | | 0.8 s |

## Checked on real frames

`open-store-real FM2 200` runs the movie from control to its end and 200 runs of own inputs of 700 frames from control. On each frame that starts in control it
looks for an instruction that stores to one of the three bytes.

| runs | frames that start in control | with a store | of them ending in control |
|---|---|---|---|
| the movie | 11,740 | 15 | 0 |
| own inputs (200 runs) | 125,196 | 48 | 0 |

The 68 stores of these 63 frames: deaths, injuries and power-ups (48), the vertical pipe (7), the flagpole (5) and its score (4, on frames of the flagpole), the
side pipe (2), the axe (2, on one frame).

## Uses

* `lags.ctl` (each counted frame before the entry ends in control), a field of part a.
* `cleanK` (`Run.pipeReal`, from `chg.upCleanU`).
* No cycle: `noStore` was used only by the walks after the player's routine (`Real.prevAll`, `Real.frame_step`, `Real.afterVS`).

## Assumed (not proved in Lean)

Nothing new. `noStore` is no longer assumed.

**Reproduce.**
```
.lake/build/bin/smbrta open-store-search check      # the two searches and OpenStore.storeCheck (2 s)
.lake/build/bin/smbrta open-store-real FM2 200      # the stores on real frames (1.5 min)
```
