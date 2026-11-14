[← Back](README.md) | [English](a-5-4-3-4-1-OpenFlat.md) | [Japanese](a-5-4-3-4-1-OpenFlat-ja.md)

# The flat ground of the opening

**Claim.** On the first `N` counted frames (`N = 32`), a frame that begins on the ground at the ground's height and whose player's routine reads no jump is
followed by a counted frame that begins on the ground at the ground's height. So the field `flat` of [The opening on real frames](a-5-4-OpenFrames.md) is not assumed
(`Real.flat`), and neither is the field `ground`: by induction on the counted frames, every counted frame that begins on the ground begins at the ground's height
(`Real.ground_all`). After a landing this comes from [The jumps of the opening](a-5-7-OpenJump.md) (`Real.jumpV`). For this the walk up to the return of the collision routine checks the vertical bytes there, and one new condition on single frames is
asked (`afterV`): from that return to the frame's end the height, its high byte, the vertical speed and its fraction do not change. The read of the block buffer routine
is asked to be in the first block buffer (`map`, `MapOK.read`), on the frames up to the counted frame `N` included.

`fm(t)` is the machine when the counted frame `t` begins, `b(t)` its end, `tr(t, k)` the machine after `k` of its instructions, `n₀(t)` the first arrival at the player's
routine and `in(t) = readIn(tr(t, n₀(t)))` the input that the routine reads. `st(m)` is the player's state, `y(m)` the height, `hi(m)` its high byte, `vy(m)` the vertical
speed, `mf(m)` its fraction, `js(m)` the jumpspring byte, `V(m) = (y, hi, vy, mf)`. `R` is the read of the block buffer routine (`LDA (zp),Y`), `addr(m)` the address it
reads. `Q` is the return from the collision routine in the player's routine. `flat(t) := st(fm t) = 0 ∧ ¬jump(in t)`.

```
GroundAt(m)  :=  y(m) = y(m₀)  ∧  hi(m) = 1  ∧  vy(m) = 0  ∧  mf(m) = 0
RdOK1(m)     :=  pc(m) = R  ∧  no NMI comes   →   addr(m) is in the first block buffer  ∧  m(addr(m)) = m₀(addr(m))
AfterV(t)    :=  ∀ k ≥ n₀(t),  pc(tr(t, k)) = Q   →   V(b t) = V(tr(t, k))
fin(B)       :=  st(B) = 0   ∨   out(B)            out(B) := the routine, the task or the mode is known not to be that of control

flat_end      :  ctrlCheck,  flatCheck,  StartK(m),  ∀ k: CleanK_K(tr k) ∧ CleanK_Q(tr k),  ∀ k in the frame: RdOK1(tr k),
                 frame(m, i) ends not paused,  AreaOK(m),  st(m) = 0,  GroundAt(m),  js(m) = 0,  ¬jump(readIn(tr n₀)),  AfterV
                 →   ∃ B,  fin(B)  ∧  B covers frame(m, i)  ∧  (out(B)  ∨  GroundAt(frame(m, i)))
map_reads     :  the conditions of map_frame (OpenMap)   →   at each read R in the frame with no NMI coming, the block buffers are those of m₀
Real.flat     :  the checks,  Real,  t ∈ [1, N],  t < E,  Held(fm t),  js(fm t) = 0,  flat(t),  GroundAt(fm t)   →   st(fm(t + 1)) = 0  ∧  GroundAt(fm(t + 1))
Real.ground_all : the checks,  Real,  Held, js = 0 and |v| ≤ top at each counted frame,  st(fm 1) = 0,  GroundAt(fm 1)
                 →   ∀ t ∈ [1, N],  t < E,   st(fm t) = 0  →  GroundAt(fm t)                                     (the old field ground)

field afterV :  ∀ t ∈ [1, N],  t < E,   AfterV(t)                                                            (new)
field map    :  ∀ n,  1 ≤ n ≤ ix(N),  n < ix(E),  ∀ k:  MapOK(tr_n(k))
```

`CleanK_K` is `CleanK` of `FrameKeep.guardK`, `CleanK_Q` that of the guard with the player's state, the jumpspring byte and the bytes of `CtrlKeep.spareI` protected.
Both come from the field `cleanK` and the stores of `MapOK` (`cleanQ_of`). `RdOK1` comes from the read of `MapOK` and the walk of [OpenMap](a-5-4-3-3-3-OpenMap.md)
(`rdOK1_of`, `map_reads`). `GroundAt(fm 1)` comes from the press of Start on the title: `title_pos_check` now also asks the four bytes of `V` at control with the values of
`m₀`, `m₀` is on the ground at its height (`Checks.start`), and the frames before the counted frame 1 keep `V` (`LagFrames.lagI` has the four bytes now: 21 walks).
The frames not counted between counted frames keep `V` too (`lags_keepI`). The theorems without the ROM use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
`#print axioms route_1_1` shows no `sorryAx`.

Lean: `Theorems/OpenFlat.lean` (`AfterV`, `vertA`, `groundOK`, `finX`, `flat_end`); `Real.flat`, `Real.ground_all`, the fields `Real.afterV`, `Real.map`
and `Checks.flat` in `Theorems/OpenFrames.lean`; `LagFrames.moreI`, `StartRun.stI`; `Run.pipeHeld` in `Theorems/Route.lean`; `OpenMap.map_reads`, `OpenMap.liveT_all`,
`OpenMap.bufI1` in `Theorems/OpenMap.lean`; private `Proof/OpenFlat.lean` (`open_flat_check`).

## How it works

Three walks cover the frame, one after the other.

* **Up to the player's routine.** The walk of the pause bit of `CtrlKeep` stops at the first arrival at the player's routine (`CtrlKeep.cut_or_end2`). There the bytes of
  `CtrlKeep.keepA` are those of the frame's start (`CtrlKeep.ctrl_keep`): the state, the height, the vertical speed and its fraction, the jumpspring byte, the area's
  bytes. One more walk of `CtrlKeep` follows the high byte of the height (`high_at_cut`). With `GroundAt` of the frame's start (`Real.ground_all`), the walk after the cut starts with these bytes known. The jump
  that the routine reads, `jump = (st = 0 ∧ A pressed ∧ A not held)`, is false, so one of two cases holds: bit 7 of the joypad's bits is 0, or it is 1 and bit 7 of A of the
  frame before is 1. Each case is set at the cut.
* **Up to the return of the collision routine.** The walk is that of `FrameKeep`, but at the read of the block buffer routine (`fstep`). There the walk follows one path
  for each tile that the known bits of the address allow: the pointer's two bytes and `Y` give the addresses, and the tiles are those of the first block buffer of `m₀`
  there (`tilesAt`, with `RdOK1`). At the routine that makes the pointer, `Y` (the buffer's number) is split into its two values (`yPieces`), so the pointer's high bits
  are known. With the height known, the row of each read is known. On the ground the feet read the ground row and the head and the sides read empty rows, so he lands
  again: at `Q`, on every path, the state is 0 and the four bytes of `V` are known with the values of `GroundAt` (`groundOK`; `walkQ`, `to_stop`). A path that ends the
  frame before `Q` ends out of control (`finX`).
* **From `Q` to the frame's end.** A walk of `FrameKeep` with the state and the jumpspring byte protected (`after_endK`). After `Q` the code sets the state only to 0
  (a platform) or leaves control (an injury).

So the frame ends with the state 0 or out of control. It ends in control (`Lags.known_end`), so the state is 0. From `Q` on `V` does not change (`afterV`), so the frame
ends at the ground's height. The frames not counted keep the state and `V` (`lags_keepI`).

**Why `afterV` is assumed.** A search after `Q` that keeps the four bytes of `V` (no part of the proof, `open-ground-exp`) ends 100 times; on 76 ends the state is known
0, and on 74 of these the height is not known. The four bytes are lost at 26 instructions, each a store through an index that the walk does not know (`STA abs,X`,
`DEC zp,X`, `STA abs,Y`, ...): such a store forgets every byte outside the guard's protected list. Also the enemies' code writes the vertical speed by its address and
keeps the state 0 (a stomp: `ChkForPlayerInjury`, `EnemyStomped`); the walk does not know the enemies and cannot exclude it. On the opening's real frames no enemy is near
and `afterV` holds. It is the vertical half of the field `after`.

The search up to `Q` keeps every byte of the RAM. Its key has the index registers in the bounding box routine, and `A`, `Y` and the temporaries in the routine that makes
the pointer. The search is no part of the proof. Without these, the search joined paths of a big and of a small Mario, and 8 of the 18 states at `Q` were not on the
ground. A single walk from the player's routine to the frame's end does not work: it joined paths through code that the opening does not run (a fireball of a fire
flower, enemies), forgot the height, and grew to 731,297 states with failures.

| walk | steps | table | time |
|---|---|---|---|
| up to `Q` | 4,345 | 132 | search 0.6 s; 6 states at `Q`, all with the state 0 |
| from `Q` to the frame's end | 443,885 | 30,659 | search 1.0 s, check 0.5 s |
| `flatCheck` (with the walk of the pause bit and of the high byte) | | | 3.0 s natively; private proof 3.3 s |

## Checked on real frames

* `open-real-check FM2 300`: on the TAS (32 counted frames), own inputs (9,600) and runs that pause on the first frames (1,856), every counted frame meets `afterV`
  (0 failures; each comes to `Q`), every counted frame that begins on the ground has `GroundAt` (0 failures; 1 + 294 + 58 = 353 of them after a landing), and the old
  field `flat` holds (0 failures). At control the four bytes of `V` are those of `m₀` on the TAS.
* `lag-check FM2`: the 21 walks of a frame not counted (the four new bytes of `V` among them) succeed, about 0.3 s each natively.
* `open-map-check FM2 300`: 27,261 frames, 74,386,942 instructions, 82,929 reads of the block buffer routine: every instruction meets `MapOK` with the read in the first
  buffer (0 failures), and every frame that begins on the ground has `GroundAt`.

## Assumed (not proved in Lean)

* **`afterV`** (new): from the return of the collision routine to the frame's end, the four bytes of `V` do not change. A condition on single frames, the vertical half
  of `after`.
* **`map`**: the read of the block buffer routine in the first buffer (he is on page 0), and `map` on the frame of the counted frame `N` too.
* **No longer assumed**: `flat`; `ground` (after a landing it comes from the field `vert` of [The jumps of the opening](a-5-7-OpenJump.md)).

**Files.** `Theorems/OpenFlat.lean`, `Theorems/OpenFrames.lean`, `Theorems/OpenMap.lean`, `Theorems/LagFrames.lean`, `Theorems/StartRun.lean`, `Theorems/Route.lean`,
private `Proof/OpenFlat.lean`.

**Reproduce.**
```
.lake/build/bin/smbrta open-flat-check                  # the searches and the check of the walks (about 6 s)
.lake/build/bin/smbrta open-real-check FM2 300          # afterV, ground and flat on real frames (about 1 min)
.lake/build/bin/smbrta open-map-check FM2 300           # MapOK with the read in the first buffer, and GroundAt, on real frames (about 30 s)
.lake/build/bin/smbrta open-ground-exp                  # the title's check, and with EXP_ALL=1 the search after Q that keeps V (about 2 min)
```
