[← Back](README.md) | [English](b-2-3-TaintRun.md) | [Japanese](b-2-3-TaintRun-ja.md)

# A run in which some bytes are not known

**Claim.** The last 41 frames of the change into the bonus room have the same length for every value of the bytes that differ from run to run. The conditions are three: Mario's size is 0 or 1, the game timer is not 000, and a list of 220 bytes has the reference's values at frame 50. This removes assumption (H4) of [what decides the change](b-2-1-PipeTransitionAll.md). The cut moves from frame 48 to frame 50. So frames 49 and 50 are now under the assumptions (H1), (H2), (H3).

**"Every value" is false at frame 48.** The emulator shows two cases at `T = run(E, 0^48)`.

* Nine bytes of the music state, changed together, give no control in 400 frames. The music pointer points at zeros, and the square 1 fetch never ends. Each of these bytes alone changes nothing.
* A game timer at 000 gives no control.

So no theorem can hold for all values of `Rvar` at frame 48. At frame 50 the RAM clear of frame 49 has set the music pointer and offsets to 0, and this loop does not run.

`m₀`, `run`, `ctl`, `0^k`, `E`, `core`, `entries` are as on the page [what decides the change](b-2-1-PipeTransitionAll.md). `T = run(E, 0^50)`. A *place* `v` of `T` is `T` with a dot `d ≤ 9`, the two parities and one bit of the PPU control mirror. `K` is a list of 220 RAM bytes, found by running. `sz` is `PlayerSize`. `g` is `GameTimerDisplay`.

```
Cond(t)     :  ∃ place v :  dot(t) = dot(v) ≤ 9  ∧  core(t) = core(v)  ∧  (∀ i ∈ K, t[i] = v[i])
               ∧  t[sz] ∈ {0, 1}  ∧  (t[g], t[g+1], t[g+2]) ≠ (0, 0, 0)

decided     :  ∀ t,  Cond(t)  →  ∀ k, 1 ≤ k ≤ 41 → ( ctl(run(t, 0^k)) ↔ k = 41 )
entryStates :  ∀ m ∈ entries :  (∀ k, 1 ≤ k ≤ 50 → ¬ctl(run(m, 0^k)))  ∧  Cond(run(m, 0^50))
every_entry :  ∀ M,  (∀ k, 1 ≤ k ≤ 50 → ¬ctl(run(M, 0^k)))  ∧  Cond(run(M, 0^50))
               →  ∀ k, 1 ≤ k ≤ 91 → ( ctl(run(M, 0^k)) ↔ k = 91 )
```

All bytes outside `K ∪ {sz, g, g+1, g+2}` are arbitrary in `decided`: frame timers, random bytes, digits, `PlayerStatus`, what is left of the music state, and all others. Only the three digits together have a condition.

Lean: `Theorems/TaintRun.lean` (`ctl_of_check`, `decided_of_run`, `Statement`, `statement_of_check`, `every_entry`), private `taint_checks` (`native_decide`), `taint_run`, `taint_entries`. `ctl_of_check` and `every_entry` use only the axioms `propext`, `Classical.choice`, `Quot.sound`.

## How it works

**The abstract machine.** It follows a set of machines. Each byte has known bits and unknown bits. The dot in the frame is an interval. A branch on a flag that is not known goes both ways. Two paths that reach the same place are joined: a bit that differs becomes unknown.

**Soundness.** `Sim A m` says that the abstract state `A` covers the machine `m`. For each of the 256 opcodes, NMI, the PPU time, the bus, DMA and the controller there is a lemma: one abstract step follows one step of `m`. A *table* of abstract states is closed under steps (`walk`). `ctl_of_check` says: if the table is closed, every machine of a start state gets control on the same frame. There is no ROM in this proof.

**Time.** Paths take different numbers of cycles. The sprite-0 flag is a function of the dot, so a read of the PPU status splits the state at the event. Then the flag is known in each part. So a wait for the flag ends with a small interval, whatever came before. Cycle parity and frame parity are not tracked. A frame may only end in the idle loop. The new dot is then in `0..9`, as in the places of `T`. Any other instruction near the end of a frame makes the check fail. Frames 51 to 91 have none.

**The pieces.** A state may be cut into parts that cover it. The digits of the timer are cut in the last frame: one known bit is 1 in one digit. Mario's size is cut at the start, because big and small Mario have different collisions.

**The check** follows 412,456 abstract steps and 3,350 forks, with 16,302 states in the table. It takes about 4 s as a program (with the 77 entries), and about 45 s in the proof build, because `Theorems` is not precompiled.

**Measured, not a theorem.** 300 random states with `Cond` give control after exactly 41 frames. The TAS entry state meets `Cond` and has no control for 50 frames. 22 of its bytes outside `K` differ from `T`.

## Assumptions (not proved in Lean)

* (H1), (H2), (H3) at frame 50: no control for 50 frames, and `Cond`. This now includes frames 49 and 50, with the RAM clear. It holds on the 77 entries (`entryStates`). For all runs it is not proved.
* The music state before frame 50. Some values stop the game, as above. A proof for all real runs needs a fact about the music state, for example that the music pointer is 0 or a value from the music header table.
* `t[sz] ∈ {0, 1}` and the timer not 000 at frame 50. They are read from the state. That a real run has these values is not proved.
* Frames that end outside the idle loop are not covered by this tool.
* No input only.

**Files.** `Theorems/TaintRun.lean`, private `Proof/TaintRun.lean`.

**To reproduce.**
```
.lake/build/bin/smbrta taint-check      # the known bytes, the check, about 20 s
```
