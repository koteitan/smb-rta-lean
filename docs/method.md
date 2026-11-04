[← Back](../README.md) | [English](method.md) | [Japanese](method-ja.md)

# Method

**Models that run the game code.** A model step writes the model state into a real RAM
snapshot (the first controllable frame of 1-1), runs a range of the game's code on the
emulator, and reads the state back. Nothing is re-implemented by hand.

**Which bytes are the state.** With RAM access tracking, the bytes that a frame reads before
writing and that are written (by the frame or by the parts emulated around it, such as the
frame timers) are the bytes carried between frames. The model state is exactly those, minus
bytes that are shown not to matter.

**Reachability certificates** (`Smbrta/Cert.lean`, proved without `native_decide`).

```
L_0 = [s0],   L_{k+1} = next(L_k) = { step(s, i) | s ∈ L_k, i ∈ I }   (duplicates removed)
run_mem :      ∀ w ∈ I^k,  run(s0, w) ∈ L_k
lower_bound :  checkUpTo(P, n, [s0]) = true  →  ∀ w ∈ I^{≤ n},  P(run(s0, w))
```

Only `checkUpTo` (P on every layer) is computed by `native_decide`. Many input sequences
lead to the same state, so the layers stay small (at most a few hundred thousand states)
although there are about 36^33 sequences.

**Pruned search.** A state that cannot reach the goal in the frames left, by a proved bound
on what one frame can do, is dropped (`Cert.lower_bound_pruned`): the kept states must satisfy
the property, and the dropped ones are safe by the bound. Fast accel uses
`V' ≤ max(V, 0) + a_max` for the speed with subspeed `V`.

**Relaxed model.** For jumps, the vertical state is replaced by a ground/air flag, and
landing may happen at the end of any frame. Every real run is a run of the relaxed model,
so a relaxed lower bound is a real lower bound.

**Pruned exact search.** To decide whether a relaxed bound is reached by a real sequence,
the exact model is searched for `n` frames, keeping only states whose relaxed projection
can still reach the goal in the remaining frames. A real sequence of `n` frames passes only
through such states, so nothing is lost.

**Checks of the assumptions** (programs, not Lean): the model against the full emulator on
random walks; the dropped bytes (position, vertical bytes) varied on every search step:
0 differences. See each theorem page for the numbers.
