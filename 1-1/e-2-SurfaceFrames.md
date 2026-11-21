[← Back](README.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# Above ground: the frames from control, one by one

**Claim.** [From control to the castle](f-5-PoleJoin.md) assumed the statements about a whole run `model`, `hit`, `stop`, `box`, `off`, `next`, `startP`, `startV`. They are theorems now. The assumptions that stay are about one frame. On frames 1 to 8 the vertical step (`vstep`) is a theorem on real machines too; what stays there is that the frame after the scroll handler keeps five of the vertical bytes. The part of each frame from its start to the player's routine is a theorem now: a walk of that part ([`CtrlKeep`](#the-frame-up-to-the-players-routine)) shows that it keeps 25 bytes and comes to the routine in the state the movement needs. So the fields `vBefore`, `Moves.at_ctrl`, `Moves.before`, `Moves.bits` are gone. The frame's two ends are theorems too, from conditions on one machine or one frame: a counted frame ends with the game not paused, so it comes to the player's routine (`Moves.arrive` is gone, new: `unpaused`); a frame not counted does not come to the player's routine, so it keeps the 25 bytes (`Moves.lag` is gone). A walk of the rest of the frame, from the player's routine to the frame's end ([below](#the-whole-frame-from-the-players-routine-to-its-end)), now shows that a frame that comes to the routine ends not paused, and that every frame in control keeps the area's type, the swimming flag and the change of size. So that a frame not counted does not come to the routine is a theorem (`OnFrames.lagNo`; new: `lagPaused`, a frame not counted ends paused), and so are three of the values of `state`. The new condition on each instruction is `spare`: no store through an index or a pointer writes these four bytes. The frames are those of the field `keep` of `Run` ([One whole frame in control](f-6-19-FrameKeep.md)), so the field `ends` is gone too. A frame where the side he presses is masked is a theorem too: the field `masked` is gone. Two more conditions of `moves` are theorems now ([The frame's time and the position's range](#the-frames-time-and-the-positions-range)): the frame does not end during the movement (`Moves.longer` is gone; it follows from the walks of the movement and the condition `time` of `CleanK`), and the position is far from the ends of its range (`Moves.far` is gone; it follows from the position at control and the frames before, which follow `hstep`). `startP`, `startV` are proved on real machines. They come from the last row of [The last frames of the change out of the side pipe](d-2-3-SideChangeEnd.md). The conditions are those of that change, and that `left` is not 0 before control. Two more parts of `moves` are theorems now. `state.prevA` is gone: every frame in control keeps bit 7 of A and B of the frame before equal to that of A and B (`OnFrames.prevAll`, [below](#a-and-b-of-the-frame-before)). The fields `md` and `rs` of `After` are gone, and its `stored` is now `storedQ`, a condition on the machine at the scroll handler: the moving direction, the running speed and the stored speed at the frame's end are those at the scroll handler (`AfterKeep.keepH`, [below](#after-the-scroll-handler-three-bytes)). The new condition on each instruction is `spareE`: no store through an index or a pointer writes these five bytes. The field `storedQ` of `After` is gone too: the stored speed at the scroll handler is `|v|` there (`MovesAt.stored`, [below](#the-stored-speed-at-the-scroll-handler)). `ImposeFriction` stores it, the walks of `FrameModel.stored_path` follow it to the scroll handler, and the frame comes there once after the player's routine (`AfterKeep.subs_once`). New: the check `storedOK` in `numbersCheck`, and `TopSpeed.frictionCheck` (the field `fric` of `SurfaceRun.Statement`). The frames `fr` are no longer data of `Run`: they are a definition on the machines of `keep` (`SurfaceFrames.frOf`, [below](#the-frames-read-from-the-machines)), so the field `reads` is gone. Each frame before the touch is proved to be a `TopSpeed.Frame` that starts and ends at the machines, from conditions on one frame or one machine. New: `state` on every frame (it was `Moves.state`, on the clean frames up to `T`), `coll`, `collide` and `farLate`. `collide` speaks of the same part of the frame as `After`, so `After` is smaller now (`AfterR`): its subspeed and the frames that move left or not at all at the scroll handler come from `collide`. Two of these four are gone now. `coll` is a theorem: a walk of the frame from the player's routine, with `X` split at `ImpedePlayerMove`, keeps the collision bits one of the four values (`OnFrames.collAll`, [below](#the-collision-bits)). New: `spareC`, a condition on each instruction: no store through an index or a pointer writes the collision bits. `farLate` is gone: a touch later than `farN` frames after control is a case of its own, and its bound comes from the count of frames alone (`SurfaceLate`, [below](#a-late-touch)). Nothing new for it but a check on `B.m`. `spareC` is gone too: the guard `guardE` of `keep.cleanE` protects the collision bits as well ([below](#the-collision-bits)). The speed's part of `collide` is a theorem now: a walk that follows the speed from the scroll handler to the frame's end shows that the speed at the end is that of the scroll handler, or 0 (`OnFrames.collideAt`, [below](#after-the-scroll-handler-the-speed)). `collide` is now `CollideR`: the subspeed and the position only. New: `spareV`, a condition on each instruction: no store through an index or a pointer writes the speed. `spareV` is gone too: `guardE` protects the speed as well (`FrameKeep.speedE`). Four of the ten bytes of `vAfter` are a theorem now: the vertical force down, the jump's origin, the jump's halt value and A are kept from the scroll handler to the frame's end (`OnFrames.kAt`, [below](#after-the-scroll-handler-four-vertical-bytes)). `vAfter` asks the other six. New: `guardE` protects three more bytes (`FrameKeep.vertE`). The facing, the subspeed and the collision bits after the scroll handler are theorems now, up to two small conditions ([below](#after-the-scroll-handler-the-facing-the-subspeed-and-the-collision-bits)). A walk shows that a frame keeps the facing and the subspeed from the scroll handler to its end, or ends with the speed 0 and the subspeed 0 (`FaceKeep.keepZ_end`). With the rest of `After`, a frame that ends with the speed 0 is a hit, and a hit needs no facing: `OneFrame` has `Hit` as a case of its own now. So the facing of `After` is no field any more, but on the frames before `J`, which must follow `hstep`: there the new field `faceJ` asks it, on a frame that ends with the speed 0 and the subspeed 0. `collide` asks the subspeed only on a frame that ends so (`CollideS`). Another walk shows that a frame that moves right at the scroll handler ends with the collision bits `FF` or those of a block of Left, or with the speed 0 (`FaceKeep.bits_end`). So `AfterR` is now `AfterP`: the position on a frame that moves right there. New: `guardE` protects two more bytes (`FrameKeep.faceE`: the facing and the subspeed), and the checks `zCheck` and `bCheck` in `numbersCheck`. The vertical force is out of `vAfter` too ([below](#after-the-scroll-handler-the-vertical-force)): a walk shows that a frame keeps it from the scroll handler to its end, or ends on the ground with the value that the landing on a jumpspring stores (`FaceKeep.vf_end`), and the vertical model allows that value on the ground (`VStep`). `vAfter` asks five bytes. New: `guardE` protects two more bytes (`FrameKeep.stateE`: the player's state and the vertical force), and the check `vfCheck` in `numbersCheck`.

**Round 24.** The field `collide` was false on a real frame that starts 1 px left of the screen's left edge ([The screen's left edge at the frame's start](e-2-10-3-10-ScreenEdge.md)). Its third case now asks P(b) ≤ base(M) + 256, where base(M) = max(P(M), edge(M)) and edge(M) = 256·left(M) + 255 is the last position on the edge's pixel. `Hit`, `MaskStop` and `After` say the same. The frames from control are `TopSpeed.Frame`s with `wide`, and their base B is base(seq (j − 1)) (`frOf_B`). Two fields are new: `edge` on each frame and `edge₀` at control. With them max(P, B) grows by at most the old bound in each frame (`TopSpeed.Frame.posB`, `Frame.advB`, `SurfaceRun.chainB_reach`, `SurfaceRun.hit_boundB`), so the numbers of the route do not change. `Surface` has three new parts, all proved: `base`, `links` and `base₁`. Its `hit` now uses the model's position at some frame before the hit (`OnFrames.edge_behind`).

**Round 25.** The field `edge₀` is a theorem (`edge_zero`, [At control the screen's left edge is behind him](e-2-10-3-11-EdgeStart.md)): `Start` has the two bytes of the screen's left edge, from the rows of the change out of the side pipe, and `numbersCheck` checks edge ≤ P on the machine at control `B.m` and that `B.m` has the program of `m0`. `AreaRun` carries it as `edge₀ : 0 < g → edge(seq 0) ≤ P(seq 0)`, and `Surface.base₁` is asked when 1 ≤ g.

The unit is 1/256 px. `seq j` is the machine at the end of the counted frame `j`. `seq 0` is the machine at control. `B.m` is the machine at control that the private proof holds.

## One frame

Read a frame `a → b` on the input `i`. `hs(m)` is the horizontal state, `P(m)` the position, `v(m)` the speed, `abs(m)` the stored speed, `bits(m)` the collision bits, `vs(m)` the vertical bytes.

```
inAt(M, x, n)     : the input as the player's routine reads it, at instruction n of the frame of M with the pad x
                    (FrameModel.readIn); Select and Start read as Up
inAt_mem          : inAt(M, x, n) ∈ inputs                       from modelOK, for any machine

t = hstep(hs a, i)     v₂ = v(t)     P₂ = P(a) + 16·v₂

Clean(m)          : inD(hs m) ∧ abs(m) = |v(m)| ∧ (bits(m) = FF ∨ (bits(m) = noLeft ∧ 0 < v(m)))
Pre(i, a, b)      : hs(b) is t except for v ∧ abs(b) = |v₂|
edge(m)           : 256·left(m) + 255     left(m): the screen's left edge, pixel and page (SurfaceRead.edgeOf)
base(m)           : max(P(m), edge(m))                                                (SurfaceRead.baseOf)
Hit(i, a, b)      : v(b) ≤ 0 ∧ (P(b) ≤ P₂ − 256 ∨ P(b) ≤ base(a) + 256)
Coll(i, a, b)     : (P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = FF)
                  ∨ (0 < v₂ ∧ P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = noLeft)
                  ∨ Hit(i, a, b)
MaskStop(a, b)    : bits(a) = noLeft ∧ v(b) ≤ 0 ∧ P(b) ≤ base(a) + 256
OneFrame(i, a, b) : MaskStop(a, b) ∨ (Pre(i, a, b) ∧ Coll(i, a, b)) ∨ Hit(i, a, b)
```

A hit needs no `Pre`. A frame that ends with the speed 0 can have another facing than `hstep` gives: a climbing tile near the screen's left edge turns him. The run leaves the model at a hit anyway (`step_of_one : Clean(a) ∧ OneFrame(i, a, b) → (Follow(i, a, b) ∧ Clean(b)) ∨ Hit(i, a, b)`, the same statement as before).

`Follow(i, a, b)` has the form of `RoomJoin.Follow` of [the bonus room](c-5-RoomJoin.md): `fr.hs n = hs(seq n)`, `fr.P n = P(seq n)`. The input of the counted frame `j` is `inp(j) = inAt(fm j, pad j, arr j)`, with `arr j` the first instruction of the frame at the player's routine (next section). It used to be `readIn(a, b)`, read from the two ends of the frame, and a field `input` said that the two are the same. Now the input is the one the routine reads, so that field is gone.

## One frame on the real machine

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel.md) proves the movement of a real frame: from the player's routine to the scroll handler, `hs` follows `hstep` and `P` moves by `16·v₂`. So `OneFrame` is a theorem from what the frame does outside the movement.

`fm j` is the machine when the counted frame `j` begins: `seq (j − 1)`, or later by `lag` frames. `pad j` is its input. Both come from the field `keep` of `Run` (`FrameKeep.Frames`). `arr j = arrAt(fm j, pad j)` is the first instruction at which the frame is at the player's routine (`CtrlKeep.arrAt`: the first `n ≤ fuelPerFrame` with `pc(trM(n)) = PlayerCtrlRoutine`; it was data in `OnFrames` before, now it is a definition). `R` is the machine there, and `Q` the machine when the frame comes to the scroll handler. `b = frame(M, i)` is the machine at the frame's end.

```
Masked(i, a)       : bits(a) & lr ≠ lr            lr = the Left/Right that hstep reads from i

After(a, Q, b)     : f of b is that of Q ∧ (fd of b is that of Q ∨ (v(b) = 0 ∧ f(b) = 0))
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ base(a) + 256)) )
AfterP(a, Q, b)    : 0 < v(Q)  →  (v(b) = v(Q) → P(b) = P(Q))                          what After still asks: the position; keep is the theorem OnFrames.keepAt, stop is Moves.stop
                                  ∧ (v(b) = 0 → P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)
After.of           : AfterP(a, Q, b) ∧ CollideE(a, Q, b) ∧ (fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0)) ∧ (0 < v(Q) → bits(b) ∈ {FF, noLeft} ∨ v(b) = 0)
                     ∧ P(Q) = P(a) + 16·v(Q)  →  After(a, Q, b)
hit_of_stop        : After(a, Q, b) ∧ v(b) = 0 ∧ v₂ = v(Q) ∧ P(Q) = P(a) + 16·v(Q)  →  Hit(i, a, b)
AfterK(a, Q, b)    : After(a, Q, b) ∧ md, RunningSpeed, abs of b are those of Q        the three bytes are a theorem (AfterKeep.keepH)
                     ∧ abs(Q) = |v(Q)|                                                a theorem (MovesAt.stored)

MovesAt(a, M, x, n₀) : AtCtrl0(R)                                  the state at the player's routine, as FrameModel needs it, but the mask
                       ∧ the 8 horizontal bytes of R are those of a    nothing writes them from a to R
                       ∧ bits(R) = bits(a)                             nor the collision bits
                       ∧ frame(R) = frame(M)                           the routine comes in the frame of M (Arrive)
                       ∧ ∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64     the condition time of CleanK
                       ∧ idleAt(idle) ∧ far(a) ∧ after ∧ collide       the idle loop is a JMP to itself; far below; AfterP and CollideE at each Q
                       ∧ face                                          fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0) at each Q (FaceKeep.keepZ_end)
                       ∧ bitsR                                         0 < v(Q) → bits(b) ∈ {FF, noLeft} ∨ v(b) = 0 at each Q (FaceKeep.bits_end)
                       ∧ keepH                                         md, RunningSpeed, abs at the frame's end are those at each Q (AfterKeep.keepH)
                       ∧ stored                                        abs(Q) = |v(Q)| at each Q (storedQ_of)

CtlState(a)        : Player_State(a) ∈ {0, 1, 2} ∧ JumpspringAnimCtrl(a) = 0
PrevOK(a)          : PrevA(a) & 80 = A_B(a) & 80                                         a theorem for every frame (OnFrames.prevAll)
AreaOK(v, a)       : AreaType(a) = v ∧ SwimmingFlag(a) = 0 ∧ PlayerChangeSizeFlag(a) = 0      a theorem for every frame (OnFrames.areaAll)
AreaRun(v)         : v = AreaType(B.m) ∈ {1, 2, 3} ∧ afterCheck(v) ∧ hCheck(v) ∧ ∀ n < ix g, AreaOK(v, all n)

Arrive(M, x, n₀)   : pc(trM(n₀)) = PlayerCtrlRoutine, in the frame of M, and no instruction before n₀ is there

Moves(a, M, x, n₀) : stop     at every Q at the scroll handler, 0 < v(Q) ∧ v(b) = 0 → P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256    (AfterP.stop; state is the field state of OnFrames now)
far(a)             : 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴

Moves.toAt    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Clean(a) ∧ Arrive(M, x, n₀) ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ AreaOK(v, a) ∧ v ∈ {1, 2, 3}
                ∧ far(a) ∧ idleAt(idle) ∧ keepH ∧ once ∧ modelOK ∧ frictionCheck ∧ storedOK ∧ CtlState(a) ∧ keep ∧ Moves  →  MovesAt      keep is AfterP.keep at every Q (OnFrames.keepAt)
at_subs       : modelOK ∧ MovesAt ∧ ¬Masked  →  ∃ Q at the scroll handler, hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_moves  : modelOK ∧ MovesAt ∧ ¬Masked  →  (Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)) ∨ Hit(inAt(M, x, n₀), a, b)
at_subsM      : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  ∃ Q at the scroll handler, (hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∨ v(Q) = 0)
                                                                  ∧ P(Q) = P(a) + 16·v(Q) ∧ AfterK(a, Q, b)
one_of_movesM : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  OneFrame(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ Clean(seq (j − 1)) ∧ far(seq (j − 1)) ∧ idleAt(idle)  →  OneFrame(inp j, seq (j − 1), seq j)
```

`one_of_moves` gives `Pre` when the facing at the frame's end is that of the scroll handler (`pre_of_after`), and a hit when the frame ends with the speed 0 (`hit_of_stop`). `face` and `bitsR` come from the walks of `FaceKeep` in `OnFrames.movesAt`; `bitsR` uses that a clean state has the collision bits `FF` or those of a block of Left.

`keepA` and `StartK`, `CleanK`, `ctrlCheck` are in the next section. `all n` are the frames of `keep`, counted or not, and `ix g` is the touch's frame. `StartK(all n)` is the theorem `FrameKeep.Frames.all_start`, from the machine at control; `CleanK` on each instruction is the field `keep.clean`. The other conditions of `Moves.toAt` are theorems (`OnFrames.arrive`, `OnFrames.lagKeep`, next section; `keepH` from `AfterKeep.keepH` and `once` from `AfterKeep.subs_once` in `OnFrames.movesAt`).

`idle` is the idle loop (`EndlessLoop`), and `idleAt(idle)` says that it is a `JMP` to itself: a check on the ROM in `numbersCheck`. `modelOK` is the check on the ROM of `FrameModel`. It is a part of `numbersCheck` now, so the private proof computes it by `native_decide` (about 3 s more). `move_model` needs that the side he presses is not masked; with `bits(R) = bits(a)` this is `¬Masked`.

**The masked frames.** On a frame where the side he presses is masked (`Masked`), the routine of the friction reads the mask and `hstep` does not. [`FrameModel.move_masked`](../0-0/0-3-2-FrameModel.md) proves that the frame still follows `hstep`, or it leaves the speed 0. A clean state with the side masked has the bits of a block of Left and moves right (`masked_clean`). With the speed 0 at the scroll handler, `After` gives `MaskStop`. `maskOK` is the check on the ROM of `move_masked` (about 0.1 s); it is a part of `numbersCheck`.

The fields that are assumed (`OnFrames`). All are in the field `frames` of `Run`. `fm`, `pad` are those of `keep`.

```
state    : 1 ≤ j ≤ g   →  CtlState(seq (j − 1))                       (it was Moves.state, on the clean frames up to T)
collide  : 1 ≤ j < g, Q at the scroll handler  →  CollideS(seq (j − 1), Q, seq j, Calls)  Calls: from Q, in the frame, an instruction at the push's or the clamp's entry
           CollideS(M, Q, b, c) : (v(b) = 0 ∧ f(b) = 0 → f(Q) = 0) ∧ (c → ¬(0 < v(Q) ∧ v(b) = v(Q)) → P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ base(M) + 256 ∧ v(Q) ≤ 0))
                                                  the speed and, on most frames, the subspeed are theorems (OnFrames.collideAt); so is the position on a frame that keeps a speed to the right or makes no call (OnFrames.keepAt, OnFrames.stillAt)
edge     : 1 ≤ j < g  →  edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))        (round 24: the screen scrolls only while he is right of its middle)
moves    : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)     Moves is now AfterP.stop only
posW     : 1 ≤ j < g, Q at the scroll handler, R an instruction from Q to the frame's end  →  PosW(R)       the position is stored by its address only inside the push and the clamp; outside them a store through an index or a pointer writes no byte of it
           (round 23: not asked of a store through an absolute address and an index whose base no index takes to the position: PositionKeep.absFar)
clampR   : 1 ≤ j < g, Q at the scroll handler, 0 < v(Q), v(seq j) = v(Q), R an instruction from Q to the frame's end  →  ClampR(R)     if R is the clamp's entry and 0 < v(R), the clamp's target is P(R)
           (round 23: asked only on a frame that keeps a speed to the right, where keep_frame uses it)
vAfter   : 1 ≤ j < J, j < g, Q at the scroll handler  →  at seq j the five bytes of vHard are those of Q
           vHard = y, mf, vy, dummy, st              (vfd, origin, DTHJ and A: the theorem OnFrames.kAt; vf: the theorem OnFrames.vfAt)
faceJ    : 1 ≤ j < J, j < g, Q at the scroll handler, v(seq j) = 0, f(seq j) = 0  →  fd(seq j) = fd(Q)
box      : 1 ≤ j < J, j < g, Q at the scroll handler  →  from Q to seq j the collision routine does what it does
           on B.m at (pix P(Q), y, w, vy, st)          (y, vy, st) is vstep's result, w stands for the speed's sign
```

`pause` is the pause byte (`GamePauseStatus`), read from the ROM: the operand of the load just before the NMI's call of the mode's routine (`CtrlKeep.pauseA`). Its low bit is 1 while the game is paused. The pause routine sets and clears it.

The fields `unpaused`, `lagPaused` and `spare` are gone. A frame of `keep` is counted when it ends with `pause & 1 = 0`: this is now the definition of `ix` ([One whole frame in control](f-6-19-FrameKeep.md)). So a counted frame ends not paused (`Frames.up`, the old `unpaused`) and a frame not counted ends paused (`Frames.down`, the old `lagPaused`). The old `spare` is a part of `keep.clean`: its guard `FrameKeep.guardF` protects the four bytes of `spareI` too.

The frame's end is the field `keep.ends` of `Run`: `1 ≤ j ≤ g → seq j = frame(fm j, pad j)` (`OnFrames.ends`, a theorem). The vertical bytes are `y, mf, vy, dummy, vf, vfd, origin, st, DTHJ`. `DTHJ` is `DiffToHaltJump`, `A` is bit 7 of `A_B_Buttons`, `PrevA` is `PreviousA_B_Buttons`.

**The vertical step is a theorem.** [`VertModel.vert_model`](../0-0/0-3-2-FrameModel.md) proves that from the player's routine to the scroll handler the vertical bytes follow `vstepV`: `vstep` on the machine with the stack pointer of the player's routine and `DTHJ = 1`.

```
HaltOK(m)  : st(m) = 1 → DTHJ(m) = 1
vNext(a, b) = vstepV(vs(a), A(b), abs(a))
vBefore    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Arrive ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ PrevOK(a)  →  at R the vertical bytes and A are those of a,
               and PrevA(R) & 80 = A_B(R) & 80                        (the old field vBefore)
VStep(a, b) : vs(b) = vNext(a, b) ∨ (st(vNext(a, b)) = 0 ∧ vs(b) = vNext(a, b) with vf := cv)          cv = FaceKeep.vfC, the value a jumpspring's landing stores
vert_of    : vertOK ∧ ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ far(seq (j − 1)) ∧ idleAt(idle) ∧ HaltOK(seq (j − 1)) ∧ PrevOK(seq (j − 1))
               →  VStep(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

`HaltOK(seq 0)` holds because the state at control is not a jump (in `numbersCheck`), and `PrevOK(seq (j − 1))` comes from `OnFrames.prevAll`. So `quiet_upto` proves `VStep(seq (j − 1), seq j)` and `HaltOK(seq j)` for every `j < J` by induction, with the other facts. `vertOK` is a part of `numbersCheck` (about 0.1 s more).

| Field before | Now |
|---|---|
| `step`: every clean frame is a `OneFrame` | `moves` (the frame outside the movement), `ends` |
| `masked`: a frame with the pressed side masked is a `OneFrame` | theorem `one_of_movesM` (from `moves` and `FrameModel.move_masked`). New: `Moves.bits`; `Moves.at_ctrl` is `AtCtrl0`, with no condition on the mask |
| `reads`: `v₂(fr j) = v₂` | gone. `box` is on the real machines `Q` and `seq j`, so the frame's `v₂` is not needed |
| `reads`: the frames `fr` (data of `Run`) start and end with the bytes of `seq` | gone: `fr` is the definition `frOf` on the machines, and `OnFrames.reads` proves it. New: `state` on every frame, `coll`, `collide`, `farLate` ([below](#the-frames-read-from-the-machines)) |
| `coll`: at the end of each frame before the touch the collision bits are one of the four values of `collBits` | theorem `OnFrames.collAll`, by the walk of `CollKeep` with `X` split at `ImpedePlayerMove`, and induction over the frames of `keep` from control. New: `spareC`, the checks `collCheck` and `collBitsOK` in `numbersCheck` ([below](#the-collision-bits)) |
| `farLate`: from frame 746 after control on, the position is at least 8 px from both ends of its range | gone. The theorems that read the frames ask `g ≤ farN(B.m)`; a later touch has the bound by the count of frames (`SurfaceLate.level_ge_of_late`), and `route_1_1` splits the two cases. New: the check `pole_far_count` (`492 ≤ farN(B.m)`) ([below](#a-late-touch)) |
| `Moves.state`: `CtlState` at the end of the frame before, on the clean frames up to `T` | the field `state` of `OnFrames`, on every frame up to the touch: `frOf` needs it on every frame |
| `After.f`, and `After.coll` when `v(Q) ≤ 0` | theorem `After.of`, from `collide` and the move. `Moves.after` became `AfterR`: the facing, and `coll` when `v(Q) > 0` (it is `AfterP` now, see the rows below) |
| `box` on `fr j` | `box` on the real machines, from the scroll handler |
| `Moves.input`: the routine reads `readIn(a, b)` | gone. The model's input is the one the routine reads |
| `vert`: frames 1 to 8 follow `vstep` | theorem `vert_of`. New: `vBefore`, `vAfter` (the frame outside the movement routine keeps the vertical bytes) |
| `vBefore`: up to the player's routine the vertical bytes and A are those of the frame before, and PrevA is A | theorem `vBefore` (was `Moves.vBefore`), by the walk of `CtrlKeep`. It uses `OnFrames.lagKeep` and `PrevOK` of the frame before (`OnFrames.prevAll`) |
| `Moves.at_ctrl`: `AtCtrl0` at the player's routine | theorem `Moves.toAt`, by the walk. New: `Moves.state` (`CtlState` at the end of the frame before) |
| `Moves.before`, `Moves.bits`: nothing writes the horizontal bytes and the collision bits up to the routine | theorem `Moves.toAt`, by the walk |
| `Moves.arrive`: the frame comes to the routine at `arr j`, the first time, before its end | theorem `OnFrames.arrive`, by the walk with the pause bit, and `Frames.up` (the counted frame ends with the pause byte's low bit 0, by the definition of the counted frames) |
| `Moves.lag`: the frames not counted between `seq (j − 1)` and `fm j` keep the 25 bytes of `keepA` | theorem `OnFrames.lagKeep`, by the walk, frame by frame. New: `lagNo` (a frame not counted does not come to the player's routine) |
| `lagNo`: a frame not counted does not come to the player's routine | theorem `OnFrames.lagNo`, by the walk of the whole frame (`area_endF`), and `Frames.down` (a frame not counted ends paused, by the definition) |
| `state`: the area's type, the swimming flag, the change of size at the end of the frame before | theorem `OnFrames.areaAll`, by the walk of the whole frame and induction over the frames of `keep` from control, with `keep.clean`. `Start` has the three bytes, from the rows; `numbersCheck` asks their values on `B.m` |
| `arr`: data, the instruction of the arrival | the definition `CtrlKeep.arrAt`: the first instruction at the routine |
| `ends`, and the data `fm`, `pad` | `keep.ends`, `keep.fm`, `keep.pad` of `Run`: one set of frames for both |
| `Moves.longer`: the frame does not end within 728 instructions after the player's routine | theorem `FrameModel.trace_inFrame`, from the walks of the movement (`InFrameN`) and the condition `time` of `CleanK` (`keep.clean`). New: `idleAt(idle)`, a check on the ROM in `numbersCheck` |
| `Moves.far`: the position at the frame's start is at least 8 px from the ends of its range | theorem `far_of_follow`, from `Start` and the frames before, which follow `hstep`. New: the check `far` of `SurfaceRun.allCheck` on `B.m` |
| `CtlState.prevA`: bit 7 of A of the frame before is that of A at the end of the frame before | theorem `OnFrames.prevAll`, by the walk after the cut (`PrevKeep.prev_end`) with the stores of `noStore` cut, and induction from control. New: `spareE` (two of its bytes), `Start.ab`, `Start.prev` (from the rows), the checks `prevCheck` and `PrevOK(B.m)` in `numbersCheck` |
| `After.md`, `After.rs`, `After.stored`: the moving direction, whether the running speed is 0, the stored speed at the frame's end | theorem `AfterKeep.keepH`: the three bytes at the frame's end are those at the scroll handler. `stored` became `storedQ` (abs(Q) = abs of v(Q), on the machine at the scroll handler). New: `spareE` (three of its bytes), the check `hCheck` in `numbersCheck` |
| `spareC`: no instruction of a frame before the touch writes the collision bits through an index or a pointer | a part of `keep.cleanE`: `FrameKeep.guardE` protects the collision bits too (`FrameKeep.collE`). `coll_end` asks `cleanE` only ([below](#the-collision-bits)) |
| the speed's part of `collide` (`CollideE.v`): the speed is that of the scroll handler, or 0 | theorem `OnFrames.collideAt` (`CollideKeep.speed_end`). `collide` became `CollideR` (the subspeed and the position; it is `CollideS` now, see the rows below). New: `spareV`, the check `vCheck` in `numbersCheck` ([below](#after-the-scroll-handler-the-speed)) |
| `spareV`: no instruction of a frame before the touch writes the speed through an index or a pointer | a part of `keep.cleanE`: `FrameKeep.guardE` protects the speed too (`FrameKeep.speedE`). `speed_end` asks `cleanE` only ([below](#after-the-scroll-handler-the-speed)) |
| `vAfter`: after the scroll handler the ten vertical bytes (`vKeep` and A) are kept | four are the theorem `OnFrames.kAt` (`VertKeep.keep_end`): the vertical force down, the jump's origin, the jump's halt value, A. `vAfter` asks the six of `vHard`. New: `FrameKeep.vertE` in `guardE` (three bytes), the check `kCheck` in `numbersCheck` ([below](#after-the-scroll-handler-four-vertical-bytes)) |
| the vertical force's part of `vAfter` | theorem `OnFrames.vfAt` (`FaceKeep.vf_end`): the vertical force stays, or the frame ends on the ground with the value of a jumpspring's landing; `vert_of` gives `VStep`, and `vCheck` follows both values on the ground. `vAfter` asks five bytes. New: `FrameKeep.stateE` in `guardE` (two bytes), the check `vfCheck` in `numbersCheck` ([below](#after-the-scroll-handler-the-vertical-force)) |
| `AfterR.fd`: the facing at the end of a frame from a clean state up to `T` is that of the scroll handler | theorem `FaceKeep.keepZ_end` (the facing stays, or the frame ends with the speed 0 and the subspeed 0), and `OneFrame` with `Hit` as a case of its own (`hit_of_stop`). New: `faceJ` (the frames before `J` that end with the speed 0 and the subspeed 0), `FrameKeep.faceE` in `guardE` (two bytes), the check `zCheck` in `numbersCheck` ([below](#after-the-scroll-handler-the-facing-the-subspeed-and-the-collision-bits)) |
| `AfterR.coll`: a frame that moves right at the scroll handler leaves nothing, the block of Left, or a hit | the collision bits are the theorem `FaceKeep.bits_end`, the speed is `CollideKeep.speed_end`. `Moves.after` is now `AfterP`: the position. New: the check `bCheck` in `numbersCheck` |
| `AfterP.keep`: a frame that moves right at the scroll handler and ends with that speed keeps the position; and `collide`'s position on that frame and on a frame that makes no call | the theorems `OnFrames.keepAt` (`PositionKeep.keep_frame`) and `OnFrames.stillAt` (`PositionKeep.still_frame`). `Moves` asks `stop` only; `collide` does not ask the position on these frames (new argument `Calls`). New: the fields `posW`, `clampR` on single instructions, the check `pCheck` in `numbersCheck` ([A frame that keeps a speed to the right](e-2-10-3-8-PositionKeep.md)) |
| `clampR` on every frame (round 23) | asked only on a frame that moves right at the scroll handler and ends with that speed: `PositionKeep.keep_frame` uses it only there. The field `collide` is false on a real frame (a frame that starts 1 px left of the screen's left edge): [The screen's left edge at the frame's start](e-2-10-3-10-ScreenEdge.md) |
| `collide`'s third case P(b) ≤ P(M) + 256 (false on a real frame, round 23) | round 24: P(b) ≤ base(M) + 256 with the screen's left edge. New: the fields `edge` (one frame) and `edge₀` (the state at control) |
| `edge₀`: at control edge(seq 0) ≤ P(seq 0) (round 24) | round 25: theorem `edge_zero` from the rows of the change out of the side pipe (`Start.edgeX`, `Start.edgeP`) and `numbersCheck` (`Numbers.edgeB`), inside `AreaRun.edge₀` ([At control the screen's left edge is behind him](e-2-10-3-11-EdgeStart.md)). `Surface.base₁` is asked when 1 ≤ g. No new field |
| the subspeed's part of `collide` (`CollideR.f`): the subspeed stays | theorem `FaceKeep.keepZ_end` on every frame that does not end with the speed 0 and the subspeed 0. `collide` is now `CollideS`: the position, and the subspeed on the frames that end so |
| `After.storedQ`: the stored speed at the scroll handler is `\|v\|` there | theorem `storedQ_of`: the walks of `FrameModel.stored_path` and `AfterKeep.subs_once`. New: the check `storedOK` in `numbersCheck`, and `TopSpeed.frictionCheck` (the field `fric` of `SurfaceRun.Statement`) |

## The frame's time and the position's range

**The time.** The walks of the movement ([`FrameModel`](../0-0/0-3-2-FrameModel.md#the-time-of-a-walked-step)) now say that each step on the way meets `InFrame`: the machine is not halted, it is not at the idle loop, and its step keeps the frame if the frame has 64 dots or more left. Each instruction of the frame of `keep` meets `CleanK`, whose condition `time` says that an instruction not at the idle loop runs at a dot at most `dotsPerFrame − 64`. So the frame does not end during the movement, and the instructions after the player's routine are the steps of the walk (`trace_inFrame`). The vertical walk (`vert_model`) and the masked frame (`move_masked`) are the same.

```
trace_inFrame : idleAt(idle) ∧ frame(R) = frame(M) ∧ InFrameN(R, k) ∧ (∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64)
                →  ∀ j ≤ k,  trM(n₀ + j) = stepN(j, R)
```

**The range.** `far(a)` is needed where `one_of_frames` is used: at the first frame `h` that does not follow `hstep` into a clean state, and on the frames before `J` (`quiet_upto`). On both, the frames before follow `hstep`, so `P(seq (j − 1)) = P(B.m) + d(w)` with `w` their inputs. Each frame of `hstep` moves at most `16·v_top` either way (`hdist_abs`), and `j − 1 ≤ T`. The check `far` of `SurfaceRun.allCheck` gives `2048 + 16·v_top·T ≤ P(B.m)` and `P(B.m) + 16·v_top·T + 2048 < 2²⁴`.

```
hdist_abs      : inD(s), w ∈ I*  →  −16·v_top·|w| ≤ d(s, w) ≤ 16·v_top·|w|
far_of_follow  : numbersCheck ∧ Start(B, seq 0) ∧ SurfaceRun.far ∧ d ≤ T ∧ frames 1..d follow hstep  →  far(seq d)
```

The private proof checks `far` on `B.m` with `T = 233` (`surface_checks`).

## The frame up to the player's routine

A frame in control runs the screen update, the sound, the pad, the pause and the timers, then the mode's routine, which calls the player's routine. `CtrlKeep` follows this part with the abstract machine of `TaintRun`, as [Frames not counted](a-5-5-3-LagFrames.md) follows a frame to the call of the mode's routine. One byte is followed as the counter of `TaintRun` (`Env.rkI`): the walk fails on any write to it. The walk stops the first time the frame comes to the player's routine (the cut), and there it asks that the byte is still followed. There is one walk for each of the 25 bytes of `keepA`.

```
keepA      = the 8 horizontal bytes (FrameModel.hBytes), Player_CollisionBits, Player_XSpeedAbsolute, AreaType, JumpspringAnimCtrl,
             SwimmingFlag, PlayerChangeSizeFlag, the 9 vertical bytes (vKeep), A_B_Buttons, PreviousA_B_Buttons
StartK(m)  : m is in the idle loop at the start of a frame in control (FrameKeep: the stack, the dot, the PPU, the routine, the mode, the task)
CleanK(m)  : the condition of FrameKeep on one instruction
trM(n)     : the machine n instructions into the frame of M

ctrl_keep  : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pc(trM(k)) = PlayerCtrlRoutine ∧ trM(k) in the frame of M ∧ (∀ j < k, pc(trM(j)) ≠ PlayerCtrlRoutine)
             →  ∀ y ∈ keepA, y(trM(k)) = y(M)
                ∧ S(trM(k)) = the stack of the player's routine ∧ no NMI pending ∧ the NMI off ∧ GameEngineSubroutine(trM(k)) = control
```

At the cut the walk also asks the stack pointer, no NMI pending, bit 7 of the PPU's control 0, and the routine byte. With these, `ctrl_keep` gives `AtCtrl0` at `R` but the values of `AreaType`, `Player_State`, the jumpspring, swimming and the change of size, and the stored speed. Those come from `OnFrames.lagKeep` and `Moves.state`, and the stored speed from `Clean(a)` (`Moves.toAt`).

**The frame's end, if it does not come to the routine.** The walk goes on to the frame's end on the paths that do not come to the cut: these are the paused frames (the NMI skips the mode's routine). There it asks again that the byte is still followed. One more walk follows the low bit of the pause byte: it starts with that bit known (the walk is run from both values), and at the end of a frame that did not come to the cut it asks that the bit is known to be 1. The pause routine toggles the bit with `EOR` or keeps it, and the NMI branches on it, so the bit is known on every path. In that walk the search does not join states with other values of the pause byte.

```
cut_or_end    : ctrlCheck1 ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)))
                →  (∃ k ≤ fuelPerFrame, pc(trM(k)) = PlayerCtrlRoutine, in the frame of M, the first time)
                   ∨ the frame's end is covered by a state with the byte followed (and the pause bit 1)
arrive_at     : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pause(frame(M, x)) & 1 = 0  →  Arrive(M, x, arrAt(M, x))
keep_of_noCut : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ (no instruction of the frame of M is at PlayerCtrlRoutine)
                →  ∀ y ∈ keepA, y(frame(M, x)) = y(M)
OnFrames.arrive  : ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)), 1 ≤ j ≤ T, j < g  →  Arrive(fm j, pad j, arr j)        from Frames.up and keep.ends
OnFrames.lagKeep : the same  →  ∀ y ∈ keepA, y(fm j) = y(seq (j − 1))                                                       from OnFrames.lagNo (a theorem), by induction over the frames ix (j − 1) … ix j − 2
```

* **The condition on each instruction.** It is `CleanK`, the field `keep.clean`, with the move routine's store not before the cut (the walk checks the `pc`). A store with a target not known makes the walk forget the followed byte, and the walk then fails at the cut. So the walk shows that before the cut every store knows its target.
* **The search.** It is no part of the proof: the check walks every state of its table. The search of `LagFrames` forgets the bytes outside `prot` and joins the passes of a loop. Then the loops of the timers (`DEC abs,X`), the random bits (`ROR abs,X`) and the top score (`STA abs,Y`) store through an index not known, and the followed byte is lost. The search of `CtrlKeep` forgets no byte of RAM and keeps both index registers in the key. One table serves every byte.
* **Numbers.** The search for the 25 bytes: 108,736 steps, 7,157 forks, 0 failures, a table of 7,852 states, 2 arrivals at the cut, 6 frame ends (paused frames), 0.2 s. The search for the pause bit: 221,415 steps, 14,528 forks, 0 failures, a table of 16,729 states, 6 arrivals, 12 frame ends, 0.5 s. The check of the 25 bytes and the pause bit (`ctrlCheck`): 2.8 s natively (2.3 s before the pause bit). It is a part of `numbersCheck` (`Numbers.ctrl`).

`surface_of_frames` and the theorems before it take `StartK(all n)` for each frame of `keep` before the touch's frame, counted or not. In `PoleJoin` it is `FrameKeep.Frames.all_start` from the machine at control (`FrameKeep.AtCtl`), the walk's check `keepCheckOf` and `fracCheck`.

## The whole frame: from the player's routine to its end

The walk of the pause bit stops at the player's routine (the cut). Now at the cut it hands over to a walk of `FrameKeep` (`FrameKeep.walkK`), which follows the frame from there to its end. That walk forgets the bytes outside its protected bytes, as the walk of [one whole frame in control](f-6-19-FrameKeep.md) does. Its guard (`guardP`) protects four more bytes (`spareI`): the pause byte, `AreaType`, `SwimmingFlag`, `PlayerChangeSizeFlag`. At the cut it keeps of the pause byte only the low bit: it is known to be 0 there, since the NMI has just tested it. It sets the other three to their values at the frame's start (`v`, 0, 0); they still have these values at the cut (`ctrl_keep`). At the frame's end it asks the four values again (`afterCheck`).

```
Spare(m)        : a store of m through an index or a pointer, with a target t < 2000h, does not write a byte of spareI
AreaOK(v, m)    : AreaType(m) = v ∧ SwimmingFlag(m) = 0 ∧ PlayerChangeSizeFlag(m) = 0

area_end        : ctrlCheck ∧ afterCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)) ∧ Spare(trM(n))) ∧ AreaOK(v, M)
                  →  AreaOK(v, frame(M, x)) ∧ ((∃ k, pc(trM(k)) = PlayerCtrlRoutine in the frame of M) → pause(frame(M, x)) & 1 = 0)
noCut_of_paused : the same ∧ pause(frame(M, x)) & 1 = 1  →  no instruction of the frame of M is at PlayerCtrlRoutine
area_endF, noCut_of_pausedF : the same, with ∀ n, CleanK_F(trM(n)) for CleanK(trM(n)) ∧ Spare(trM(n))       CleanK_F: CleanK of FrameKeep.guardF
OnFrames.areaAll : ctrlCheck ∧ afterCheck(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaOK(v, seq 0)  →  ∀ n < ix g, AreaOK(v, all n)
OnFrames.lagNo   : ctrlCheck ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n))  →  the field lagNo of before
```

A frame that does not come to the routine is the one of the walk before: it ends paused, and it keeps `keepA`, which has the three bytes. So every frame in control keeps them, and a frame ends not paused exactly when it comes to the player's routine.

* **Why the bytes are protected.** After the player's routine the game engine stores through indices that the walk does not know (the objects). Such a store makes the walk forget every byte outside the protected ones. `CleanK` protects only the bytes of `FrameKeep.guardK`. So `keep.clean` asks `CleanK` of `FrameKeep.guardF`, which protects the four bytes too. `area_endF` is `area_end` with it: the walk after the cut asks no `Spare` at the player's own store of the fraction, so the old `Spare` on that store is not needed. On real frames no store through an index or a pointer writes these bytes (below, Measured).
* **The induction.** `seq 0` has the three bytes of `B.m` (`Start`, from the rows of the change), and `numbersCheck` asks `AreaType(B.m) ∈ {1, 2, 3}`, `SwimmingFlag(B.m) = 0`, `PlayerChangeSizeFlag(B.m) = 0`. Each frame of `keep` before the touch's frame keeps them (`area_endF`), so every `all n` has them, and so has `seq (j − 1)`.
* **The change of size.** `PlayerChangeSizeFlag` is set only in the routine of the change of size, which is not the routine of control. A power-up changes the routine byte; the flag is set on a later frame, which is not in control.
* **Numbers.** The walk of the pause bit comes to the cut in 3 states. The search after the cut: 1,633,803 steps, 154,366 forks, 0 failures, a table of 75,196 states. `afterCheck` (the walk of the pause bit up to the cut again, and the walk after it): 5.9 s in a program; it is a part of `numbersCheck` (`Numbers.after`). With only the pause bit watched the table has 46,644 states; with the pause bit, the area's type and the swimming flag 44,924. If the cut kept the whole pause byte, the 3 states at the cut would give 3 keys and a table of 139,987 states.
* **The jumpspring.** With `JumpspringAnimCtrl` protected and watched too, the search did not finish: 9 minutes, 6.8 GB, stopped. The jumpspring's object code writes it when he lands on it, so the walk could not keep it anyway.
* **`unpaused` and `lagPaused` are gone.** Which frames are counted is `ix` of `keep`. With the walk, a frame ends not paused exactly when it comes to the player's routine. So `ix` is now defined as the frames that end not paused, and the two fields hold by the definition.

## A and B of the frame before

The player's routine writes A and B (`A_B_Buttons`) from the pad's bits, and at its end the game engine copies them into A and B of the frame before (`PreviousA_B_Buttons`, the routine `SaveAB`). `PrevKeep` shows that a frame in control keeps bit 7 of the two equal.

```
PrevOK(m)        : PrevA(m) & 80 = A_B(m) & 80
SpareAB(m)       : a store of m through an index or a pointer, with a target t < 2000h, writes neither A_B nor PrevA
CtlStore(m)      : the instruction of m writes the routine, the mode or the task by its address
prev_end         : ctrlCheck ∧ prevCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareAB(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ PrevOK(M)
                   →  PrevOK(frame(M, x))
OnFrames.prevAll : ctrlCheck ∧ prevCheck(v) ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ PrevOK(seq 0)  →  ∀ n < ix g, PrevOK(all n)
```

`CleanK_F` is `CleanK` of `FrameKeep.guardF` (the field `keep.cleanF`). No frame before the touch's frame has an instruction with `CtlStore` (the field `keep.noStore`).

* **The walk.** The walk of the pause bit comes to the player's routine (the cut). There, for each value `b` of bit 7 of the pad's bits, a walk of `FrameKeep.walkKC` follows the frame to its end. It protects A_B and PrevA too, and it stops a path at a store to the routine, the mode or the task by its address. At the frame's end it asks bit 7 of A_B and of PrevA to be `b`. A frame that does not come to the routine keeps both bytes (`CtrlKeep.keep_of_noCut`).
* **Why the cut.** Round 8's search without the cut failed at 26 frame ends: there PrevA was not known. The paths that fail are those that write the task by its address: the axe (`HandleAxeMetatile`) and the change of area (`ChgAreaMode`). With the task below the game core's, the game core returns before the game engine, so `SaveAB` does not run. With the paths cut at the stores to the routine, the mode and the task (8 places: these two and six stores of the routine), the search has 0 failures and a table of 7,079 states (74,910 before).
* **The induction.** `seq 0` has the A_B and PrevA of `B.m` (`Start`, from the rows of the change: the rows know PrevA too), and `numbersCheck` asks `PrevOK(B.m)`. Each frame of `keep` before the touch's frame keeps `PrevOK`.
* **Numbers.** `prevCheck`: the walk of the pause bit to the cut and two walks after it, 3.1 s natively. It is a part of `numbersCheck` (`Numbers.prev`).

## After the scroll handler: three bytes

`AfterKeep` follows the frame from the player's routine with two walks. The first goes from the cut to the first time the frame comes to the scroll handler (`PlayerSubs`). The second goes from there to the frame's end, with one byte followed as the counter of `TaintRun` (`Env.rkI`): it fails on any write to that byte, and asks at the frame's end that the byte is still followed. It also fails if the frame comes to the scroll handler again. Both stop a path at a store to the routine, the mode or the task by its address.

```
hI          = Player_MovingDir, RunningSpeed, Player_XSpeedAbsolute
SpareH(m)   : a store of m through an index or a pointer, with a target t < 2000h, writes no byte of hI
keepH       : ctrlCheck ∧ hCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_F(trM(n)) ∧ SpareH(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
              →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ hI, y(frame(M, x)) = y(trM(k))
SpareE(m)   : SpareAB(m) ∧ SpareH(m)          the old field spareE; now a part of keep.cleanE (GuardE)
```

* **Numbers.** The first walk: 1,769 steps, a table of 134 states, 8 states at the scroll handler. The second walk: 61,977 steps and a table of 3,986 states for each byte, 0 failures. `hCheck`: 1.9 s natively. It is a part of `numbersCheck` (`Numbers.keepH`).
* **A step with the followed byte.** `FrameKeep.s_kstep` asks the counter to be at least 2. The second walk asks instead that no instruction decrements the followed byte (`isRkDec`), as `LagFrames` does: `s_kstepL`.

**Which stores the walk meets.** The program `after-bytes` runs the second search for each horizontal byte, from the 8 states at the scroll handler.

* Under `keep.cleanF` alone, with the byte not protected, the walk loses each of these bytes at about 95 stores through an index or a pointer whose target it does not know: the enemies, the sprites, the area's parser. `SprObject_X_MoveForce`, which `guardK` protects, is not lost there.
* With the byte protected too, the three bytes of `hI` close. The others meet stores by address:

| byte | stores after the scroll handler that the walk meets |
|---|---|
| speed | `KillPlayer`, `KeepOnscr` (the screen's edge), `ImpedePlayerMove`, `PutPlayerOnVine` |
| subspeed | `PutPlayerOnVine` |
| facing | `FlagpoleCollision`, `PutPlayerOnVine` |
| x | the move routine with the index 0 (the walk splits an index it does not know), `PositionPlayerOnHPlat`, `ImpedePlayerMove`, `KeepOnscr`, `PutPlayerOnVine` |
| page | the stores of x, and `ExecGameLoopback` |
| fraction | the move routine with the index 0 |
| collision bits | `ImpedePlayerMove`, the start of `PlayerBGCollision` |

`KillPlayer` writes the speed before it writes the routine, so the cut at the routine's store comes after it. `PutPlayerOnVine` is reached also on paths that write no routine (a vine's tile below the status bar). So the subspeed and the facing stay in `After`: the walk would need to know that he touches no vine or pole, which is the map.

## After the scroll handler: the speed

The speed's part of `collide`, `CollideE.v` (the speed at the end is that of the scroll handler, or 0), is now a theorem from walks (`Theorems/CollideKeep.lean`). The first walk is that of `AfterKeep`, from the cut to the scroll handler. The second goes from there to the frame's end and follows the speed as the counter of `TaintRun` (`Env.rkI`). It differs from the second walk of `AfterKeep` in two things. Before an instruction that writes the speed by its address, the walk stops following it (`rkOff`). At the frame's end it asks that the speed is still followed, or known to be 0 (`finV`).

```
SpareV(m)          : a store of m through an index or a pointer, with a target t < 2000h, does not write the speed      (a part of CleanK_E: spareV_of)
rkOff(A)           : A no longer following the speed, if A follows it and the instruction at A.pc writes the speed by its address; else A
finV(B)            : B still follows the speed ∨ the speed is known to be 0 in B
speed_end          : ctrlCheck ∧ vCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                     →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  v(frame(M, x)) = v(trM(k)) ∨ v(frame(M, x)) = 0
CollideR(M, Q, b)  : f(b) = f(Q) ∧ (P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ base(M) + 256 ∧ v(Q) ≤ 0))        the old field collide; now from CollideS and the walk of the subspeed (CollideS.toR)
CollideR.toE       : CollideR(B₀, Q, b) ∧ (v(b) = v(Q) ∨ v(b) = 0)  →  CollideE(B₀, Q, b)
OnFrames.collideAt : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  CollideE(base(seq (j − 1)), trM(k), frame(fm j, pad j))       M = fm j, x = pad j
```

* **The pieces.** A state that no longer follows the speed covers every machine that the state covered (`cov_rkOff`): `rkv` of `Sim` is asked only while the byte is followed. The walk `walkKV` is `AfterKeep.walkKR` with the pieces of `rkOff` after those of `FrameKeep.preK` (the form of `CollKeep.walkKX`). `endKV` has the proof of `AfterKeep.endKR`.
* **Numbers.** The second walk: from the 8 states at the scroll handler, 123,279 steps, a table of 7,888 states, 0 failures. It stops following the speed at 4 places: the stores of 0 at the screen's edge (`KeepOnscr`), in the collision routine (`ImpedePlayerMove`) and in the climbing routine (`PutPlayerOnVine`), and the death (`KillPlayer`). The death's path writes the routine after it, so `noStore` cuts it. `vCheck` takes 1.5 s as a program. It is a part of `numbersCheck` (`Numbers.vkeep`, `AreaRun.vkeep`), so `pole_numbers` takes about 1.5 s more.
* **The protected byte.** Without the speed protected, the walk loses it at about 95 stores through an index or a pointer whose target it does not know (`after-bytes guard`). So the speed must be protected. `FrameKeep.guardE` protects it (`FrameKeep.speedE`), so `CleanK_E` gives `CleanK` of the walk's guard (`cleanV_of`), and the old one-instruction condition `spareV` is a part of `CleanK_E` (`spareV_of`, on every instruction but the player's own store of the fraction, which `CleanK` does not ask). Protecting the player's state, or a condition on the state at the frame's end, is not needed.
* **Measured with the speed in `guardE`.** `keep-frames-check FM2 100` (224,813 frames above ground, the touch's frames and frames with a pause included): no store through an index or a pointer to a protected byte. `open-real-check FM2 300` (the opening's frames: part a's `Real.cleanK` asks `CleanK_E` too): 0 frames failing a condition. `phase-frame-check` (the walk of `PhaseFrame` uses `guardE` with two more bytes): the check is true. `open-air-search all`: 0 failures, the table of 95,459 states as before. The first three again with the three bytes of `vertE` protected too (below): the same counts, 0 failures.

**The subspeed.** It is in the next section: the walk closes with the end "still followed, or the speed and the subspeed are known to be 0". With the end "still followed, or the player's state is known and not 0, 1 or 2" it does not: 141,003 steps, a table of 10,650 states, 1 failure (`collide-keep-check`). The failing path: the side check comes to the climbing routine (`PutPlayerOnVine`), which sets the subspeed to 0 and the state to 3. Later in the same frame a platform's collision (`SetCollisionFlag`) sets the state to 0. So the condition on the state at the frame's end (`state`) does not exclude the path. The walk knows neither the map nor the objects.

**The position (measured, not proved).** `CollideS` and `AfterP` ask it. After the scroll handler the three bytes of the position are written at these places (`after-bytes prot`: the walk with the byte protected):

| place | what it writes | why a walk does not close it |
|---|---|---|
| the scroll handler's clamp (`KeepOnscr`) | the pixel and the page: the screen's edge. It sets the speed to 0 unless he holds the button away from the edge | whether `P(b) ≤ P(a) + 256` holds depends on where the edge is and where he was at the frame's start: a relation of two values that the walk does not know |
| the collision routine's push (`ImpedePlayerMove`) | 1 px left or right, with the carry into the page, and the speed 0 | the walk knows bytes, not sums: `P(b) = P(Q) − 256` is a relation of three bytes before and after. It needs a lemma of that routine on real machines, and the walk cut there |
| the climbing routine (`PutPlayerOnVine`) | the pixel from the tile's column, the page | the map |
| a platform that moves sideways (`PositionPlayerOnHPlat`) | the pixel and the page from the platform's | the objects |
| the move routine with an index (`MoveObjectHorizontally`) | the fraction, the pixel, the page of the object with that index | after the scroll handler the index is an enemy's, 1 or more, but the walk does not know the object's number (`ObjectOffset`): its table forgets it. The pixel and the page cannot be in `guardE`: the player's own move writes them with the index 0 before the scroll handler, and `CleanK` leaves out only his store of the fraction |
| the loop of the castles (`ExecGameLoopback`) | the page | a path of other levels |

So the position stays assumed. On real frames (`pos-after-real`, [below](#after-the-scroll-handler-the-facing-the-subspeed-and-the-collision-bits)) only the first two places write it.

**Measured on real frames.** `collide-real FM2 200` (each run stops before a frame that writes the routine, the mode or the task, so these are frames before the touch):

| run | frames in control | arrivals at the scroll handler | the speed set to 0 after it | not `SpareV` | the speed neither that there nor 0 | the subspeed not that there |
|---|---:|---:|---:|---:|---:|---:|
| the movie from 852 | 239 | 239 | 3 | 0 | 0 | 0 |
| random from control (200 runs) | 36,218 | 36,218 | 3,687 | 0 | 0 | 0 |
| into the screen's left edge (120 runs) | 35,938 | 35,938 | 4,145 | 0 | 0 | 0 |
| random from the movie's frames 1002 to 1091 (400 runs) | 45,809 | 45,809 | 1,633 | 0 | 0 | 0 |
| with Select (100 runs) | 10,475 | 10,475 | 523 | 0 | 0 | 0 |
| with Start (100 runs) | 20,276 | 12,206 | 625 | 0 | 0 | 0 |

Many arrivals have the speed set to 0, so the "or 0" of `finV` is needed.

## After the scroll handler: four vertical bytes

Of the ten bytes that `vAfter` asked, four are kept by the second walk of `AfterKeep` (`Theorems/VertKeep.lean`): the vertical force down, the jump's origin, the jump's halt value, A and B. The walk follows each of them, one at a time, from the scroll handler to the frame's end, fails on any write to it, and asks at the frame's end that it is still followed. Its guard protects the byte.

```
kI               = VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump, A_B_Buttons
vertE            = VerticalForceDown, JumpOrigin_Y_Position, DiffToHaltJump          (FrameKeep.vertE: guardE protects them; A_B_Buttons is in spareE)
Prot_E           = stateE ∪ faceE ∪ spareE ∪ collE ∪ speedE ∪ vertE ∪ Prot_F          (faceE, stateE: the next sections)
keep_end         : ctrlCheck ∧ kCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                     →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ kI, y(frame(M, x)) = y(trM(k))
OnFrames.kAt     : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  ∀ y ∈ kI, y(seq j) = y(trM(k))          M = fm j, x = pad j
vAfter           : 1 ≤ j < J, j < g, k ≥ arr j, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ vHard, y(seq j) = y(trM(k))
vHard            = Player_Y_Position, Player_Y_MoveForce, Player_Y_Speed, Player_YMF_Dummy, Player_State          (VerticalForce: the next section but one)
```

`vert_of` takes the nine bytes of `vKeep` and A from `vAfter` and `kAt`. `kCheck` is `AfterKeep.hCheck` with the bytes of `kI`: 1.9 s natively. It is a part of `numbersCheck` (`Numbers.vk`, `AreaRun.kv`).

**Which stores the walk meets after the scroll handler** (`vert-after-bytes prot`: one search for each of the ten bytes, followed and protected besides the bytes of `keep.cleanE`, from the 8 states at the scroll handler, with the stores to the routine, the mode and the task by address cut):

| byte | failures | stores by address that the walk meets |
|---|---:|---|
| `VerticalForceDown`, `JumpOrigin_Y_Position`, `DiffToHaltJump`, `A_B_Buttons`, `Player_YMF_Dummy` | 0 | none |
| `VerticalForce` | 1 | the jumpspring (`ChkForLandJumpSpring`) |
| `Player_State` | 6 | the collision routine (`SetPSte`: 2, `InitSteP`: 0), the vine (`PutPlayerOnVine`), a platform (`SetCollisionFlag`) |
| `Player_Y_Position` | 11 | the landing (`LandPlyr`: the low four bits 0), the vertical platforms (`PositionPlayerOnVPlat`), the jumpspring (`JumpspringHandler`, `DownJSpr`) |
| `Player_Y_MoveForce` | 9 | the landing (`LandPlyr`), the vertical platforms |
| `Player_Y_Speed` | 38 | the landing, the head's bump (`NYSpd`), the blocks (`BumpBlock`, `BrickShatter`), the stomps (`EnemyStompedPts`, `SBnce`), the platforms (`PositionPlayerOnVPlat`, `ProcLPlatCollisions`), the jumpspring (`BounceJS`), the death (`KillPlayer`) |

Each search: about 62,000 steps, a table of about 3,980 states, 0.2 s. With the byte not protected (`vert-after-bytes guard`) every byte but A and B is lost at about 95 stores through an index or a pointer whose target the walk does not know.

**Why five of the other six stay assumed.**

* `Player_YMF_Dummy`, the height, its fraction and the vertical speed are written through an index (index 0) by the player's own vertical move before the scroll handler (`ImposeGravity`). So `guardE`, a condition on every instruction of the frame, cannot protect them. A condition only on the instructions after the scroll handler would be a new field.
* `VerticalForce` is no longer assumed: [below](#after-the-scroll-handler-the-vertical-force).
* The height, its fraction, the vertical speed and the state: the collision routine writes them on every frame that starts on the ground, and lands him again with the same values. Part c's `RoomFall` proves such a landing by splitting the height at the landing, but its walk knows the room's map and that there is no enemy. Above ground the walk knows neither: the foot check may find no ground (the state stays 2), the head check may bump (the speed 1 or 0), an enemy may be stomped, a platform or the jumpspring may move him. Each needs a condition on the map or on the objects.

**Measured on real frames** (`vert-after-real FM2 400`: the frames 1 to 8 of the movie from 852 and of own runs from control, random, with taps, with Select; a run stops before a frame that writes the routine, the mode or the task):

| run | frames | `vAfter` false | at `Q` on the ground | at `Q` rising | a byte changes after `Q` |
|---|---:|---:|---:|---:|---:|
| the movie from 852 | 8 | 0 | 1 | 7 | 1 |
| random from control (400 runs) | 3,200 | 0 | 2,411 | 789 | 2,411 |
| random taps from control (400 runs) | 3,200 | 0 | 2,321 | 879 | 2,321 |
| with Select (200 runs) | 1,600 | 0 | 1,180 | 420 | 1,180 |

On the ground at `Q` the state is 0, the vertical speed and its fraction 0, the height's low four bits 0. On every such frame the only change after `Q` is the state: 2 at `SetPSte`, then 0 at `InitSteP`; the landing writes the height, the speed and its fraction with the values they have. Rising at `Q` (the state 1, the speed negative) no byte changes. No other class occurs at `Q`.

## After the scroll handler: the facing, the subspeed and the collision bits

`Theorems/FaceKeep.lean`. Two results about the frame from the scroll handler to its end. Both walks start, as those of `AfterKeep`, at the cut, and go through a first walk to the scroll handler.

**The facing and the subspeed.** After the scroll handler the facing is written by its address at two places. The flagpole's collision (`FlagpoleCollision`) sets it; that path then writes the routine, so `noStore` cuts it. The climbing routine (`PutPlayerOnVine`) turns him left when he is near the screen's left edge. The subspeed is written only in the climbing routine. That routine first sets the speed and the subspeed to 0. The walk follows the byte as the counter of `TaintRun` (`Env.rkI`), stops following it before a store to it by its address (`CollideKeep.rkOff`), and asks at the frame's end that it is still followed, or that the speed and the subspeed are known to be 0.

```
zI               = PlayerFacingDir, Player_X_MoveForce
faceE            = PlayerFacingDir, Player_X_MoveForce          (FrameKeep.faceE: guardE protects them)
finZ(B)          : B still follows the byte ∨ (the speed and the subspeed are known to be 0 in B)
keepZ_end        : ctrlCheck ∧ zCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  ∀ y ∈ zI,  y(frame(M, x)) = y(trM(k)) ∨ (v(frame(M, x)) = 0 ∧ f(frame(M, x)) = 0)
CollideS.toR     : CollideS(M, Q, b, c) ∧ (f(b) = f(Q) ∨ (v(b) = 0 ∧ f(b) = 0)) ∧ (0 < v(Q) ∧ v(b) = v(Q) → P(b) = P(Q)) ∧ (¬c → P(b) = P(Q))  →  CollideR(M, Q, b)
```

* **The facing.** `After.fd` is now `fd(b) = fd(Q) ∨ (v(b) = 0 ∧ f(b) = 0)`: the theorem above (`MovesAt.face`). When the facing is that of the scroll handler, the frame is `Pre` as before. When the frame ends with the speed 0, `After.coll` makes it a `Hit` (`hit_of_stop`): the first case of `coll` gives `v(Q) = 0`, so `P(b) = P(Q) = P(a)`; the second cannot be; the third is a hit. `OneFrame` allows a `Hit` with no `Pre`, and `step_of_one` gives a hit for it. So on a frame from a clean state up to `T` the facing is no assumption any more.
* **The frames before `J`.** No hit may come before `J`: `quiet_upto` shows that each of these frames follows `hstep`. So it needs `Pre`, and the facing. The walk gives the facing but on a frame that ends with the speed 0 and the subspeed 0. There the field `faceJ` asks it. On such a frame he stands still.
* **The subspeed.** `collide` is `CollideS`: it asks the position as before, and of the subspeed only that a frame that ends with the speed 0 and the subspeed 0 has the subspeed 0 at the scroll handler. With the theorem this is `CollideR` (`CollideS.toR`), and with the speed `CollideE` (`OnFrames.collideAt`). `TopSpeed.Frame.impedeF` asks `f' = f₂` on every frame, so the subspeed cannot be dropped on a hit as the facing is.
* **Why a walk gives no more.** The climbing routine is reached when a side point is on a climbing tile. A walk knows neither the map nor the objects. With the player's state protected and the end "still followed, or the state is known and not 0, 1 or 2" (the field `state` excludes that), the walk fails on one path: the climbing routine sets the state to climbing, and a platform's collision sets it back in the same frame (`collide-keep-check`).

**The collision bits of a frame that moves right at the scroll handler.** The collision routine sets the bits to `FF`. `ImpedePlayerMove` clears the bit of a side. On the side of a block of Right it also sets the speed to 0, unless he moves left; on the side of a block of Left, unless he moves right. So a frame that does not move left at the scroll handler ends with `FF` or the bits of a block of Left, or with the speed 0.

```
nl               = noLeft                                       (the bits of a block of Left)
noLeftOK         : ∀ x,  x & nl = nl  →  x = FF ∨ x = nl           (a check on the 256 bytes)
finB(B)          : the bits are known under the mask nl in B (every bit but that of Left is 1) ∨ the speed is known to be 0 in B
bits_end         : ctrlCheck ∧ bCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ bits(M) & nl = nl ∧ Arrive(M, x, n₀) ∧ once
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs ∧ v(trM(k)) & 80 = 0  →  bits(frame(M, x)) ∈ {FF, nl} ∨ v(frame(M, x)) = 0
```

`once` is the conclusion of `subs_once`. With it `AfterR`, which asked the collision bits, is `AfterP` (`After.of`).

* **The pieces.** The first walk goes from the cut to the scroll handler with the collision bits protected and watched under the mask `nl` (`b1Cfg`: the first walk of `AfterKeep` with the guard of `CollKeep`). So a frame that leaves the collision routine early (he is not on the screen's rows) still has its bits under `nl` at the end. At the scroll handler the speed's sign bit is set to 0 in the state (`toSign`). The second walk (`CollideKeep.walkKV`) splits `X` at the `DEX` of `ImpedePlayerMove`, as `CollKeep` does, and `Y`, which holds the speed there, at its two `CPY #` (`splitYAt`): one piece for each value that the known bits of `Y` allow. The compare of the abstract machine knows the sign of its result only when both bytes are known, so without the split the walk follows both branches. Each piece covers the machine of its own `Y` (`cov_splitYAt`), and pieces after pieces cover (`cov_comp`).
* **The table's key.** It has the known bits of the speed, so that a state with the speed known to be 0 is not joined with one where only the sign is known; and `X` and `Y` inside `ImpedePlayerMove`. With the collision bits in the key too the table is four times as large (36,521 states, 964,629 steps, 8 s) and nothing more is proved.
* **Numbers.** The facing: 119,906 steps, a table of 7,659 states, 0 failures; it stops following at the flagpole's store and at the climbing routine's. The subspeed: 119,889 steps, 7,659 states, 0 failures. `zCheck`: 1.6 s natively. The collision bits: the first walk 1,769 steps, 8 states at the scroll handler, all with the bits known under `nl`; the second walk 314,246 steps, a table of 9,349 states, 0 failures. `bCheck`: 2.5 s. Both are parts of `numbersCheck` (`Numbers.zk`, `Numbers.bk`, `AreaRun.zk`, `AreaRun.bk`), so `pole_numbers` takes about 4 s more.

**Measured on real frames.** `collide-real FM2 200` (each run stops before a frame that writes the routine, the mode or the task). An arrival is a frame's arrival at the scroll handler.

| run | arrivals | the frame ends with the speed 0 and the subspeed 0 | the facing changes after it | starts with `FF` or a block of Left, sign bit 0 there | from a clean state | `CollideS.f` false | `CollideS` false | `keepZ_end` false | `bits_end` false | `AfterP` false |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| the movie from 852 | 239 | 0 | 0 | 236 | 234 | 0 | 0 | 0 | 0 | 0 |
| random from control (200 runs) | 36,218 | 3,064 | 0 | 26,911 | 32,170 | 0 | 0 | 0 | 0 | 0 |
| into the screen's left edge (120 runs) | 35,938 | 3,794 | 0 | 23,939 | 31,512 | 0 | 0 | 0 | 0 | 0 |
| random from the movie's frames 1002 to 1091 (400 runs) | 45,809 | 5,532 | 0 | 36,135 | 42,908 | 0 | 0 | 0 | 0 | 0 |
| with Select (100 runs) | 10,475 | 767 | 0 | 8,041 | 9,904 | 0 | 0 | 0 | 0 | 0 |
| with Start (100 runs) | 12,206 | 1,215 | 0 | 9,389 | 11,445 | 0 | 0 | 0 | 0 | 0 |

`CollideS.f` is asked on 10.2 % of the arrivals: the frames that end with the speed 0 and the subspeed 0. The old `CollideR.f` was asked on all. The facing does not change after the scroll handler on any of these frames.

`pos-after-real FM2 200`: which instructions change the three bytes of the position after the scroll handler, on the first five kinds of runs (128,679 frames). Only two places do: the scroll handler's clamp (`KeepOnscr`: the pixel on 465 frames, the page on 450) and the collision routine's push (`ImpedePlayerMove`: the pixel on 2,592 frames). The fraction changes on no frame. The position at the frame's end is that at the scroll handler, or 1 px less (the push left), or 1 px more (the push right, or the clamp), or 2 px more (the clamp, on 4 frames, all moving left).

## After the scroll handler: the vertical force

`vAfter` used to ask the vertical force too. After the scroll handler one place stores it by its address: the landing on a jumpspring (`ChkForLandJumpSpring`). The landing then sets the player's state to 0. The only later stores to the state by its address that a walk meets are a platform's collision (0) and the climbing routine (3). So a frame keeps the vertical force, or it ends with the stored value and the state 0 or 3; the field `state` excludes 3.

```
stateE           = Player_State, VerticalForce                    (FrameKeep.stateE: guardE protects them)
Prot_E           = stateE ∪ faceE ∪ spareE ∪ collE ∪ speedE ∪ vertE ∪ Prot_F
cv               = vfC                                            the value that the store writes, read from the search: a parameter of the check and of the theorem
finVF(B)         : B still follows the vertical force ∨ (it is known to be cv in B ∧ the state is known to be 0 or 3 in B)
vf_end           : ctrlCheck ∧ vfCheck(v, c) ∧ StartK(M) ∧ (∀ n, CleanK_E(trM(n)) ∧ ¬CtlStore(trM(n))) ∧ AreaOK(v, M) ∧ Arrive(M, x, n₀)
                   →  ∀ k ≥ n₀, pc(trM(k)) = PlayerSubs  →  vf(frame(M, x)) = vf(trM(k)) ∨ (vf(frame(M, x)) = c ∧ st(frame(M, x)) ∈ {0, 3})
OnFrames.vfAt    : 1 ≤ j < g ∧ k ≥ arr j ∧ pc(trM(k)) = PlayerSubs  →  vf(seq j) = vf(trM(k)) ∨ (vf(seq j) = cv ∧ st(seq j) = 0)          M = fm j, x = pad j
VStep(a, b)      : vs(b) = vNext(a, b) ∨ (st(vNext(a, b)) = 0 ∧ vs(b) = vNext(a, b) with vf := cv)
vVar(w)          = [w, w with vf := cv]  if st(w) = 0,    [w]  else
vNextAll(l)      = the states of vVar(vstepV(s, A, abs)) for s ∈ l, A pressed or not, abs ≤ v_top
vCheck_spec      : vCheck(n, l) ∧ u 0 ∈ l ∧ (∀ i < k, u (i + 1) ∈ vVar(vstepV(u i, A i, abs i)))  →  u k is in the box          (1 ≤ k ≤ n)
```

* **The walk.** It is the walk of the speed (`CollideKeep.walkKV`) with the vertical force followed and the player's state protected. Its table's key has the known bits of the state once the vertical force is no longer followed, so that the states 0 and 3 are not joined. `vfC` is the vertical force in the first state of the search that no longer follows it. No value is written in the Lean file.
* **Why the state, and not the jumpspring's byte.** Round 14 asked at the frame's end "still followed, or the jumpspring's byte known not 0" (`state` asks that byte 0). That walk fails on 2 paths (200,638 steps, a table of 13,449 states), which are one thing. The landing sets the jumpspring's byte and the jumpspring's timer, both to values that are not 0. The jumpspring's own code runs for each enemy slot that holds one, and the walk does not know the slots. Each run adds 1 to the byte when the timer is 0, and after a few such runs one sets the byte back to 0. On a real machine the timer is not 0 after the landing, so no run adds. The walk forgets the timer: its table keeps only the protected bytes. With the timer protected too that walk closes (120,856 steps, a table of 7,781 states, 0 failures; `face-keep-check ADDR` with the timer's RAM address). But the timer cannot be in `guardE`: the NMI's timer loop decrements it through an index whenever it is not 0, so that condition on each instruction would say that the timer is 0 on every frame. The player's state needs no such thing.
* **The model.** On the ground no vertical step reads the vertical force, and a jump's start stores it anew. So a frame before `J` that ends on the ground need not have the model's vertical force. `VStep` allows the stored value there, `vNextAll` follows both states (`vVar`), and `vCheck` checks the box on both. `box` reads only the height, the vertical speed and the state of `vNext`, which are the same in both cases.
* **Numbers.** The walk: 178,839 steps, a table of 11,507 states, 0 failures. `vfCheck`: 1.7 s natively. It is a part of `numbersCheck` (`Numbers.vfk`, `AreaRun.vfk`), and `vCheck` takes `vfC`, so `pole_numbers` takes about 4 s more for the two.
* **Measured.** On the frames 1 to 8 of real runs the vertical force does not change after the scroll handler (`vert-after-real FM2 400`: 8,008 frames, [above](#after-the-scroll-handler-four-vertical-bytes)). The four new bytes of `guardE` (`faceE`, `stateE`) were measured together: `keep-frames-check FM2 100` (224,813 frames above ground, touch frames and frames with a pause included): no store through an index or a pointer to a protected byte on any run (exit code 0). `open-real-check FM2 300` (part a's frames): 0 frames failing a condition. `up-clean-u FM2 quick`: exit code 0 (`guardE` protects 67 bytes, the union guard 143 with part b's byte of this round). `open-air-search all`: 0 failures, a table of 95,459 states as before, `airCheck` true. `phase-frame-check`: the check is true; the table of its second walk has 45,022 states (it had 45,260).

## The stored speed at the scroll handler

`ImposeFriction` ends by storing `|v|` in the stored speed (`Player_XSpeedAbsolute`). On the ground it runs on every frame. In the air it runs only with Left or Right; without them neither the speed nor the stored speed changes before the scroll handler. So the stored speed at the scroll handler is `|v|` there if it is `|v|` at the player's routine, and `Clean(a)` gives that.

```
storedOK    : for each of the 4608 cases, ImposeFriction next to the machine of frictionCheck, with the speed and the stored speed out;
              and from each cut at the mover, a walk of one machine to the scroll handler that writes neither byte
stored_path : modelOK ∧ frictionCheck ∧ storedOK ∧ AtFrame(R) ∧ abs(R) = |v(R)|
              →  ∃ k,  pc(stepN(k, R)) = PlayerSubs ∧ abs(stepN(k, R)) = |v(stepN(k, R))| ∧ InFrameN(R, k)
subs_once   : the conditions of keepH  →  ∀ k k' ≥ n₀,  pc(trM(k)) = PlayerSubs ∧ pc(trM(k')) = PlayerSubs  →  k = k'
storedQ_of  : modelOK ∧ frictionCheck ∧ storedOK ∧ AtCtrl0(R) ∧ Clean(a) ∧ v(R) = v(a) ∧ bits(R) = bits(a) ∧ time ∧ idleAt(idle) ∧ once
              →  ∀ k ≥ n₀,  pc(trM(k)) = PlayerSubs  →  abs(trM(k)) = |v(trM(k))|
```

`R = trM(n₀)` is the machine at the player's routine, and `once` is the conclusion of `subs_once`.

* **The walks.** Up to `ImposeFriction` they are those of `frame_path` (`caseOK`, `frameCaseOK`). At `ImposeFriction` the real machine runs next to the machine of `TopSpeed.frictionCheck`: `m0` with the speed, the subspeed, the adder, the two caps and the collision bits of the real machine. That check says that the stored speed after the routine is `|v'|`. From its return to the mover the piece of `fricOK` now watches the stored speed too (`watchM`). From the mover to the scroll handler a new walk of one machine (`storedTailOK`) watches the speed and the stored speed. There are 2 cuts at the mover (`tailsOf`); from both the walk comes to the scroll handler at the stack of the player's routine.
* **Which arrival.** `stored_path` comes to the scroll handler at some step, and the movement (`move_model`) at its own step. `After` speaks of every arrival after the player's routine. The walks of `AfterKeep` show that there is only one: the first walk stops at the first arrival, and the second walk fails at another (`subs_once`; `keepH` is now proved from the same theorem `keepH_once`). So all are the same instruction.
* **Conditions.** `AtFrame(R)` needs `|v(R)| ≤ v_top` and the collision bits in `TopSpeed.collBits`. Both come from `Clean(a)`: `inD`, and the bits `FF` or `noLeft`. `frictionCheck` is the check of [Top speed](../0-0/0-1-TopSpeed.md). It takes about 55 s natively, and the private proof has it already (`top_frictionCheck`). So it is passed in, as the field `fric` of `SurfaceRun.Statement`, and not computed again.
* **Numbers.** `storedOK`: 4608 cases, 0 failures, 357 ms in a program. It is a part of `numbersCheck` (`Numbers.storedW`).

## The frames read from the machines

`fr j` used to be data of `Run`, and the field `reads` said that it starts with the bytes of `seq (j − 1)` and ends with those of `seq j`. So `reads` held a claim that was not written: each real frame is a `TopSpeed.Frame`. Now `fr` is a definition (`SurfaceFrames.frOf`, `Run.fr`), and that claim is proved from conditions on one frame or one machine.

```
CollideE(B₀, Q, b) : (v(b) = v(Q) ∨ v(b) = 0) ∧ f(b) = f(Q)
                    ∧ (P(b) = P(Q) ∨ P(b) = P(Q) − 256 ∨ (P(Q) ≤ P(b) ≤ B₀ + 256 ∧ v(Q) ≤ 0))
ReadH(M, x, n₀)   : modelOK ∧ frictionCheck ∧ AtFrame(R) ∧ the 8 horizontal bytes of R are those of M ∧ InTime ∧ far(M)
ReadE(M, x, n₀, B₀) : ReadH(M, x, n₀) ∧ CollideE(B₀, Q, b) at every Q at the scroll handler      (B₀ is the base base(seq (j − 1)) at the end of the counted frame before)
frameE(a, M, x, n₀) = the Frame of frame_readE with the start of a,   if ReadE and M has the horizontal bytes of a
                      a frame that stops at the start of a,             else
frameH(a, M, x, n₀) = the Frame of read_move with the start of a,     if ReadH and M has the horizontal bytes of a
                      (it ends at the scroll handler: v' = v₂, f' = f₂, P' = P₂)
                      a frame that stops at the start of a,             else
frOf j = frameE(seq (j − 1), fm j, pad j, arr j)    for j < g
         frameH(seq (j − 1), fm j, pad j, arr j)    for j ≥ g
farN(m) = min(⌊(P(m) − 2048) / (16·v_top + 256)⌋, ⌊(2²⁴ − 2049 − P(m)) / (16·v_top)⌋)          745 for B.m
```

`AtFrame(R)` is the state at the player's routine as `FrameModel.frame_read` needs it: `AtCtrl0` without the stored speed, with the collision bits in `collBits` and `|v| ≤ v_top`. `InTime` is the frame's time ([`FrameTime`](c-7-1-1-FrameTime.md)), which the condition `time` of `CleanK` gives.

```
read_move         : ReadH(M, x, n₀)  →  a Frame with v, f, P of M, and some k ≥ n₀ at the scroll handler with v₂, f₂, P₂ those of trM(k)
frame_readE       : ReadE(M, x, n₀)  →  a Frame with v, f, P of M, v', f', P' of the frame's end, and P₂ − 256 ≤ P'
frameE_move       : ReadE(M, x, n₀)  →  some k ≥ n₀ at the scroll handler with v₂, f₂, P₂ of frameE those of trM(k)      (round 14, for part f's StopRead)
OnFrames.readH    : 1 ≤ j ≤ g ∧ |v(seq (j − 1))| ≤ v_top ∧ far(seq (j − 1))  →  ReadH(fm j, pad j, arr j) ∧ fm j has the horizontal bytes of seq (j − 1)
OnFrames.readAll  : g ≤ farN(B.m)  →  ∀ d < g,  |v(seq d)| ≤ v_top  ∧  (d < farN(B.m)  →  P(B.m) − (16·v_top + 256)·d ≤ P(seq d) ≤ P(B.m) + 16·v_top·d)
OnFrames.reads    : g ≤ farN(B.m)  →  Reads(g, seq, frOf)                (the old field reads)
OnFrames.touchMove: P₂(frOf g) and v₂(frOf g) are P and v at some arrival k ≥ arr g at the scroll handler
```

* `frame_readE` is `FrameModel.frame_readR` with `CollideE` in place of `Collide`. `Collide` asks `P(b) = P(Q) + 256` in its third case. At the screen's left edge the scroll handler puts him on the edge, and `P(b) − P(Q)` can be 512 ([The screen's left edge](#the-screens-left-edge)). `CollideE` allows this, as `TopSpeed.Frame.impedeP` does, and asks `P(Q) ≤ P(b)`: the edge pushes him right, not left.
* `readH`: the walk of `CtrlKeep` (`ctrl_keep`) keeps the 25 bytes of `keepA` up to the routine, and the `lag` frames keep them too (`OnFrames.lagKeep`, now on every frame up to the touch). The area's values and the collision bits come from `AreaRun` (`OnFrames.areaRun`: `areaAll` and `collAll`). `state` gives the rest of `AtFrame`.
* `readAll`: induction over the frames. At control `v = 0`. Each frame before the touch is `frameE` with `ReadE`. So `Frame.bound` keeps `|v'| ≤ v_top`. The frame moves him at most `16·v_top` right, and at most `16·v_top + 256` left (`P' ≥ P₂ − 256 = P + 16·v₂ − 256`). So on the first `farN` frames the position stays away from both ends of its range. `readAll`, `readE_at`, `reads` and `touchMove` ask `g ≤ farN(B.m)`, so every frame before the touch is one of these. A later touch: [below](#a-late-touch).
* `reads`: the start is that of `seq (j − 1)` by the definition. The end of a frame before the touch is that of `frame(fm j, pad j)`, which is `seq j` (`keep.ends`), by `frame_readE`.
* The touch's frame `g` does not end as a `Frame` ends: the touch moves him. `frOf g` is the frame up to the scroll handler. `touchMove` says that `P₂(g)` is the position at an arrival at the scroll handler. The field `moved` of `Run` (part f) says that every arrival before the routine's write has this position.

**Measured.** `surface-read-check FM2 200` (a program, exit code 0, about 2 minutes 15 seconds of CPU). On each counted frame, from the end of the counted frame before: `state`, `coll`, `|v| ≤ v_top`, `far`, that the `lag` frames keep the 25 bytes, `AtFrame` at the routine, the horizontal bytes up to the routine, the frame's time, an arrival at the scroll handler, and on the frames before the touch `CollideE` at every arrival at the scroll handler. The last frame of a run, which ends out of control (the touch or a death), is checked as the touch's frame: all but `CollideE`.

| Run | counted frames | `lag` | last frames | fails | `CollideE` but not `Collide` | largest move right, left |
|---|---:|---:|---:|---:|---:|---|
| TAS from 852 | 240 | 0 | 1 | 0 | 0 | 640, −224 |
| random from control (200 runs) | 53,724 | 0 | 94 | 0 | 2 | 640, −592 |
| random from the TAS's frames | 32,715 | 0 | 65 | 0 | 0 | 640, −640 |
| with Select, with Start | 28,689 | 8,070 | 91 | 0 | 3 | 640, −592 |
| running to the left edge | 53,398 | 0 | 130 | 0 | 13 | 640, −640 |
| the late touch, the long jump | 34 | 0 | 1 | 0 | 0 | 640, −16 |

The position at control is 669696 (`B.m` and the TAS), and `v_top = 40`. So `farN(B.m) = ⌊667648 / 896⌋ = 745`. The TAS touches the pole on frame 240. A touch on frame 746 or later is the late touch ([below](#a-late-touch)).

## The collision bits

`bits(m)` are the collision bits. The old field `coll` said: at the end of each frame before the touch, `bits ∈ collBits = {FC, FD, FE, FF}`. Now it is a theorem.

The collision routine sets the bits to `FF`. `ImpedePlayerMove` clears the bit given by `X` at its end. On every path `X` is 1 or 2 there: the routine loads the side check's counter (a byte of the zero page), takes 1 from it, and sets `X = 1` when that is 0, `X = 2` else. When he is not on the screen's rows the routine keeps the bits.

A walk does not know the counter when it comes there from a state of its table: the table forgets the byte. Then `dex` gives an `X` that is not known. The branch on the zero flag is followed both ways, and on the way with the zero flag set the walk does not learn `X = 0`. So the bit to clear is not known, and the walk failed at 4 frame ends (round 11).

Now the walk splits `X` into its 256 values at that `dex` (`splitXAt`). Each value is one piece, and the piece of the machine's own `X` covers it (`cov_splitXAt`). The table's key has `X` from the split to the routine's end, so the pieces are not joined again.

```
CollOK(m)        : bits(m) & FC = FC
collBitsOK       : ∀ x,  x & FC = FC  →  x ∈ collBits                    (a check on the 256 bytes)
SpareC(m)        : a store of m through an index or a pointer does not write the collision bits         a part of CleanK_E (spareC_of)
coll_end         : ctrlCheck ∧ collCheck(v) ∧ StartK(m) ∧ (∀ n, CleanK_E(trm(n))) ∧ (∀ n, ¬CtlStore(trm(n)))
                   ∧ AreaOK(v, m) ∧ CollOK(m)  →  CollOK(frame(m, i))
OnFrames.collAll : CollOK(seq 0)  →  ∀ n < ix g,  CollOK(all n)
```

`CleanK_E` is `CleanK` of `guardE`, the field `keep.cleanE`. From this round `guardE` protects the collision bits too (`FrameKeep.collE`). The walk's guard is `guardF` with the bits protected; each byte it protects, `guardE` protects, so `CleanK_E` alone gives it (`cleanC_of`). `SpareC` of the old field `spareC` is a part of `CleanK_E` (`spareC_of`; but at the player's store of the fraction, where `CleanK` asks nothing). A frame that comes to the player's routine is the walk (`walkKX`: `FrameKeep.walkKC` with the split before each step). A frame that does not come there keeps the bits (`CtrlKeep.keep_of_noCut`). At control `bits = FF` (`numbersCheck` on `B.m`, and `Start.bits`). `collAll` is the induction over the frames of `keep`, counted or not, with `noStore` and `cleanE` on the frames before the touch's frame. `readH` takes `bits(seq (j − 1)) ∈ collBits` from it and `collBitsOK`.

**Measured.** The searches after the player's routine, with the bits watched under `FC`, as programs:

| Search | Steps | Table | Failures | Time |
|---|---:|---:|---:|---:|
| round 11 (`coll-cut-check`) | 404,240 | 22,446 | 4 | 1.4 s |
| the zero page byte 0 protected and in the key (`coll-key-check 0`) | 106,190,191 | 3,719,813 | 267 | 527 s |
| `X` split, `X` not in the key | 411,125 | 22,457 | 4 | 3.4 s |
| `X` split, `X` in the key (`coll-split-check`) | 615,303 | 38,413 | 0 | 3.9 s |

The byte 0 is a temp of the whole game, so in the key it splits the table into many states, and its protection fails at 267 places. So the split of `X` is the way. `collCheck` takes about 5 s as a program. It is in `numbersCheck` (`collCheckAll`), so `pole_numbers` takes about 5 s more.

`coll-real FM2 200` (the movie from 852 and own runs from control; a run stops at a frame with a store to the routine, the mode or the task):

| Run | Frames | Not `SpareC` | Starts with `CollOK`, ends without | Ends without `CollOK` | Values at the ends |
|---|---:|---:|---:|---:|---|
| TAS from 852 | 239 | 0 | 0 | 0 | FD, FE, FF |
| random from control | 36,218 | 0 | 0 | 0 | FD, FE, FF |
| with Select | 10,475 | 0 | 0 | 0 | FE, FF |
| with Start | 20,276 | 0 | 0 | 0 | FD, FE, FF |

`cleanE` is asked on the touch's frame too, so `guardE` with the collision bits was checked there too. `keep-frames-check FM2 100` (the check of [One whole frame in control](f-6-19-FrameKeep.md), with the new `guardE`): the movie, 100 random runs from control, 400 from the movie's frames 1002 to 1091, 120 into the screen's left edge, 500 with pauses. About 225,000 frames, 457 touch frames. No store that is not `Plain`, no failure (exit code 0, about 4 minutes).

The walk that uses `guardE` is that of [`PhaseFrame`](0-5-2-1-1-PhaseFrame.md) (`guardPh` is `guardE` with two more bytes). With one more protected byte, the table of its second walk grows from 38,386 to 45,392 states, and `phaseCheck` from 2.8 s to 3.1 s as a program. The private `Proof.PhaseFrame` builds (exit code 0). The other walks use `guardF` or `guardK`, so they do not change.

## A late touch

The frames are read from the machines on the first `farN(B.m) = 745` frames (`readAll`). So the theorems that read them ask `g ≤ farN(B.m)`: `readAll`, `readE_at`, `reads`, `touchMove`, `surface_of_frames`, and in [`PoleJoin`](f-5-PoleJoin.md) `Run.reads`, `Run.next`, `hB_run`, `base_late`, `touch_ge`, `direct_castle`, `castle_ge`, `touch_castle` (the new argument `hg`). The old field `farLate` gave the position's range on the later frames.

A later touch needs no frames: the count of frames gives the bound. The timer ticks at most once in 2 frames, so 2 more frames of play add at least 1 to the sum `E + T` of `CastleToLevel.sum_ge`.

```
ticks_add_twice  : 2 ≤ q  →  ticks(q, p + 2k) ≤ ticks(q, p) + k
sum_ge_late      : the bounds of sum_ge on P1, X1, P2, X2, E, T, and 492 ≤ P3  →  1588 + j ≤ E + T          (any W)
level_ge_late    : the same, with the bounds of level_ge on D, c, L  →  1748 + j ≤ L
level_ge_of_late : Route.Run ∧ 368 ≤ pipe.E ∧ room.C + 111 ≤ room.E ∧ 492 ≤ pole.g ∧ pole.g < pole.c  →  1748 + j ≤ L
pole_far_count   : 492 ≤ farN(B.m)                                        (native_decide in the private proof; farN(B.m) = 745)
```

Why 492: `sum_ge` needs `W + P3 − ticks(P3) + ticks(240) ≥ 366` from the third stretch. `ticks_add_twice(240, 126)` gives `ticks(492) ≤ ticks(240) + 126`, so from `P3 = 492` on `P3 − ticks(P3) + ticks(240) ≥ 366` with `W = 0`.

`route_1_1` splits the two cases. If `g ≤ farN(B.m)`, it is the old way (`pole_touch_castle` with `hg`). Else `492 ≤ g` by `pole_far_count`, and `g < c` is `PoleJoin.Run.afterTouch`. So `farLate` is gone, and nothing is assumed in its place.

## The statements about the whole run are theorems

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
OnFrames.reads    : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ v(seq 0) = 0 ∧ P(seq 0) = P(B.m)  →  Reads(g, seq, frOf)
next_of_reads     : Reads(g, seq, fr)  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  frames 1..j are Follow ∧ seq 0..j are Clean ∧ bits(seq j) = FF
                                         ∧ frames 1..j are VStep ∧ seq 0..j are HaltOK
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ (∀ n < ix g, StartK(all n)) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
                    →  ∃ w h, Surface(w, h)
Run.next, Run.startP, Run.startV                                 PoleJoin
```

| Assumption before | Now | From |
|---|---|---|
| `model`: `P'(j) ≤ P_A + d(w)` for `j < h` | theorem | `one_of_frames`. `w` is the list of `inp j`, `h` the first frame that is not `Follow ∧ Clean` |
| `hit`, `stop` | theorem | `Hit` in `OneFrame` |
| `box`, `off`: no hit before `J` | theorem (`Surface.first : J ≤ h`) | `box`, `vert_of`, `moves`, the bound on the distance (`dist_abs`), the search of the height (`vCheck`) |
| `next` | theorem | `OnFrames.reads`. Both ends are read from the same machine |
| `startP`, `startV` | theorem | `Start`. Next section |
| `mem`, `long` | theorem | `inAt_mem`, how `w` is made |

**In the box.** `x` on frames 1 to 8 is not assumed. It is within 4 px by the bound on `|d(w)|` (`dl`; moving left the speed's byte can be 1 more, so this is a little more than `dbound`). The height is not assumed either. `vCheck` runs `vstepV` for 8 frames from `vs(B.m)`, with A or not and every stored speed from 0 to the top, and checks that every state is in the box.

## The state at control

`Start(B, m)` is about one machine.

```
Start(B, m) : hs(m) = hs(B.m) ∧ P(m) = P(B.m) ∧ abs(m) = abs(B.m) ∧ bits(m) = bits(B.m) ∧ vs(m) = vs(B.m)
              ∧ AreaType(m) = AreaType(B.m) ∧ SwimmingFlag(m) = SwimmingFlag(B.m) ∧ PlayerChangeSizeFlag(m) = PlayerChangeSizeFlag(B.m)
              ∧ A_B(m) = A_B(B.m) ∧ PrevA(m) = PrevA(B.m)
```

A state of the last row of the change that has control knows 1,763 or 1,776 of 2,048 bytes. `startCheck` checks, on every state of every row, that it says whether it has control, and if it has, that it knows the bytes of `Start` and they are those of `B.m`.

```
start_of_rows : startCheck ∧ InRows(m) ∧ ctl(m)  →  Start(B, m)
EndRun.start  : Statement ∧ EndStatement ∧ startCheck ∧ EndRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  Start(B, seq b)
Run.start     : the same conditions, on a run of Route  Start(B, pole.seq 0)
```

`left` is 0 only on the last row. It has 6 states, and 2 have control. The other 4 are the time-up states. The rows end where `left` is 0, so `left` must not be 0 before control (`EndRun.first`, proved from `chg.time₂` and `chg.ctlFirst₂`). `Route.Run.atCtl : pole.seq 0 = base.seq b₂` is a theorem: the frames of `keep` are those of `base` from frame `b₂` on. The conditions `entry₂`, `noStart₂`, `quiet₂` of `chg` are used as `Run.change₂` uses them.

The last row also gives the vertical bytes, the A button and the collision bits. The main bytes it does not know are `PlayerSize` and `EventMusicQueue`.

## The screen's left edge

When Mario is on the pixel of the screen's left edge, the scroll routine sets the speed to 0, unless Right alone is held. Left of that pixel, it puts his position back on it. The order is: the move, the scroll routine, the collision routine.

* The old `Frame.impedeP` is false on real frames. A frame that runs past the edge has `v₂ = −v_top`, `P' − P₂ = 512`. Of 53,398 frames that run to the edge, 13 do this.
* So the third case of `impedeP` is now `P' ≤ P + 256 ∧ v₂ ≤ 0` in place of `P' = P₂ + 256 ∧ v₂ ≤ 0`. `Frame.bound`, `Frame.adv_le`, `chain_reach` stay.
* In the statement on one frame this is the second kind of `Hit`. He can stop with `v₂ > 0` too (the largest measured is 4). Then `P(b) = P₂ ≤ P(a) + 256`. He does not leave the edge's pixel fast, so this is enough. That he is not fast is not proved: it is assumed in `After` (in `moves`).

## Measured

The program `surface-frames-check FM2 N`, `N = 200`, exit code 0, about 9 minutes of CPU. In every row, no frame fails `OneFrame`, `Moves`, `ends`, the `v₂` of `reads`, or `move`, `gain`, `impedeV`, `impedeF`, `impedeP` of `Frame`.

| Run | Frames | Not clean | `lag` | Routine does nothing | Left blocked | `Hit` | Put back at the edge | Frames 1 to 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| TAS from 852 | 240 | 5 | 0 | 233 | 0 | 1 | 0 | 8 |
| the late touch after 1089, A held long | 34 | 3 | 0 | 30 | 0 | 0 | 0 | 0 |
| random from control | 36,308 | 4,048 | 0 | 30,705 | 2 | 1,463 | 1 | 1,600 |
| random from the TAS's frames | 15,019 | 571 | 0 | 14,087 | 0 | 327 | 0 | 0 |
| with Select | 10,520 | 571 | 0 | 9,724 | 0 | 180 | 1 | 800 |
| with Start | 20,311 | 761 | 8,070 | 11,161 | 0 | 284 | 2 | 786 |
| running to the left edge | 53,398 | 3,804 | 0 | 47,629 | 0 | 1,835 | 13 | 0 |
| overwritten states around the stairs | 103,680 | 5,908 | 0 | 88,917 | 2,653 | 6,202 | 0 | 0 |

* On frames 1 to 8 (3,194 frames) also `vs(seq j) = vNext(seq (j − 1), seq j)`, the old `vBefore`, `vAfter`, `HaltOK` at both ends, `box`, and that `(y, vy, st)` on entering the collision routine is `vstepV`'s result. No difference.
* On every frame checked on `Moves` also `state` (with `PrevA & 80 = A_B & 80` at the end of the frame before), what `OnFrames.lagKeep` proves (the 25 bytes of `fm j` are those of `seq (j − 1)`), the arrival at the routine, and what `ctrl_keep` proves: the 25 bytes of `keepA` at the routine are those of `fm j`. No difference, also on the 8,070 `lag` frames with Start.
* On every frame checked on `Moves` also the new fields and what the new walks prove: `AfterP`, `CollideS`, the facing and the subspeed (`keepZ_end`), the collision bits when the speed's sign bit is 0 at the scroll handler (`bits_end`); on frames 1 to 8 also `faceJ` and `vAfter` on its five bytes. No difference. The old `After`, with the facing equal on every frame, holds on these frames too.
* The old fields `unpaused`, `lagPaused`, `spare`: no counted frame in control ends paused, no `lag` frame ends not paused, and no frame has a store through an index or a pointer to one of the four bytes of `spareI`. Also no `lag` frame comes to the player's routine (what `OnFrames.lagNo` proves), and no frame in control changes the area's type, the swimming flag or the change of size (what `OnFrames.areaAll` proves). All counts are 0 on every run, the 8,070 `lag` frames with Start included. The machine of the proof has the area's type 1, the swimming flag 0, the change of size 0.
* On every frame the input that the player's routine reads is `readIn(a, b)` of the two ends (the old field `input`): no difference.
* On 2,375 of the 3,194 frames 1 to 8 a byte of the vertical state takes another value between the scroll handler and the frame's end, and is back at the end. On the ground the collision routine sets `Player_State` to 2 and lands him again. So `vAfter` cannot come from a walk that forbids writes to these bytes. For four bytes it can: they are not written after the scroll handler (`OnFrames.kAt`, [above](#after-the-scroll-handler-four-vertical-bytes)). The vertical force is written there only by a jumpspring's landing (`OnFrames.vfAt`, [above](#after-the-scroll-handler-the-vertical-force)).
* The pressed side is masked on 329 frames (3 from control, 326 around the stairs). All are `OneFrame` and all meet `Moves`. At the mover 182 have the model's speed and 147 the speed 0 where the model's is not 0 (`move_masked`'s second case; the kinds column counts them as `Hit`). These 147 are not `Pre ∧ Coll` and need `MaskStop`; this page said before that none needs it, which was false. `bits(R) = bits(a)` fails on no frame.
* On the 8,070 `lag` frames, no byte read here changes. So with `lag` frames after `seq j` the values read are the same. No frame overruns on these runs.
* The change: 201 runs from the TAS's entry state and `E` with random inputs with no Start. All get control after 282 frames or more, `left` is never 0 before control, and the state at control always meets `Start`.
* How it counts: a frame that ends in a machine without control (death, the touch) is outside the fields and is not counted. `Follow` and `Hit` do not hold there. Such a run is not a `Run`.
* `after-real FM2 100` (the movie from 852 and 300 own runs from control, random, with Select, with Start: 35,802 frames in control; a run stops at a frame with a store to the routine, the mode or the task): `SpareE` holds at every instruction; `PrevOK` holds at the start and the end of every frame; the three bytes of `hI` at the frame's end are those at the scroll handler, and no frame comes to the scroll handler twice after the player's routine. On the 31,949 frames from a clean state, `storedQ` and `After` hold. On 338 frames from a state that is not clean, `storedQ` fails; `moves` is not asked there.

## The first frame in the abstract machine

One frame walked from the states of the last row that have control (not in Lean).

| Known | Steps | Failures |
|---|---:|---:|
| pad not known | 27,292 | 5 (`FindEventMusicHeader+2`) |
| `EventMusicQueue = 0`, pad not known | 2,288 | 4 (`JumpEngine+18`) |
| `EventMusicQueue = 0`, each of the 128 pads with no Start | 739,183 | 1 on each of the 64 with no A (`BlockBufferCollision+43`) |
| and `PlayerSize` split | about 840,000 per case | 0, about 3 s for the 4 cases |

So frame 1 alone closes. It is one frame of 233, and the states grow on the next frames, so it is not in the proof.

## The player's state and the jumpspring (not proved)

`state` (it was `Moves.state`) asks two values at the end of the frame before: `Player_State` ∈ {0, 1, 2} and `JumpspringAnimCtrl` = 0. These are the stores that write them in a frame in control before the touch (with `noStore`: no store to the routine, the mode or the task by its address).

* The jumpspring byte: only `ChkForLandJumpSpring` makes it not 0. The foot check calls it on the path that lands him (`LandPlyr`), and it stores when the tile there is one of the two jumpspring tiles. The jumpspring object's code writes the byte only when it is not 0.
* The state 3 (climbing): only `PutPlayerOnVine`. The side check of the collision routine comes to it (`HandleClimbing`) when a side point in the middle part of a tile is a climbing tile that is not the flagpole's. The flagpole's tile stores the routine as well, so that frame is the touch. The climbing tests of the foot check and of the head check store no state. The other stores of 3 are in the routines of the area's start, of the vine's entrance and of the climb up the vine, not in the player's control. The other stores of the state in such a frame write 0, 1 or 2 (a jump 1; the collision routine 0, 1, 2; a platform 0). The stores of a power-up and of a hit write the routine too, so `noStore` cuts them.

So these conditions on one frame, on the tiles the collision routine reads, would give the two values: the landing tile of the foot check is not a jumpspring tile, and no side point in the middle part of a tile is a climbing tile other than the flagpole's. With them a proof would need these steps:

* The jumpspring: the walk after the player's routine closes with the byte watched as 0, protected, and each path stopped at a store to it by its address: 84,594 steps, 0 failures, a table of 7,217 states, 0.4 s (program `spring-cut-check`). The only store to the byte where it stops is the one in `ChkForLandJumpSpring` (2 times; the other 8 stops are the stores of `noStore`). The searches before stopped no path, neither at these stores nor at those of `noStore`, and did not end (9 minutes and 6.8 GB on this page; 4 minutes and 21.7 GB in part a).
* The state: the walks watch a byte with one value under a mask. {0, 1, 2} is no such set, so the walk needs a new kind of watch, or a split by the value with a check of the set at the frame's end. Not tried.
* Each byte needs a place in the condition on stores through an index or a pointer (as `spareE`).

Is this smaller than `state`? No. `state` is two bytes of one machine, for each counted frame. The conditions above are on every frame before the touch, counted or not, on up to 6 tile reads each (2 of the feet, 4 of the side points), and add 2 bytes to the condition on stores through an index or a pointer. With the walks they give `state`, and `state` does not give them. What they add: they are about the map, so a model of the block buffer above ground could prove them; `state` does not follow from the map without these walks. So `state` stays as it is.

Measured on real frames (`spring-real FM2 100`: the movie from 852 and own runs from control, random, with Select, with Start; 35,731 frames in control; a run stops at a frame with a store to the routine, the mode or the task): no instruction writes the jumpspring byte, none stores 3 to the state, no store through an index or a pointer writes the state, and no frame ends with the state 3 or the jumpspring byte not 0.

## Assumptions (not proved in Lean)

* `moves`: the frame outside the movement. Up to the player's routine it is proved (`ctrl_keep`) from the frame's start in control and `CleanK`, and so are the arrival at the routine and that the frames not counted keep the 25 bytes; that the frame does not end during the movement (from `CleanK`) and that the position is far from the ends (from the frames before) are proved too, and so are bit 7 of A of the frame before (`OnFrames.prevAll`) and three bytes after the scroll handler (`AfterKeep.keepH`). The stored speed at the scroll handler is proved too (`MovesAt.stored`). What stays: the position on a frame that moves right at the scroll handler (`AfterP`). The values at the end of the frame before are the field `state` now. The movement is proved ([`FrameModel`](../0-0/0-3-2-FrameModel.md)), also with the pressed side masked.
* `unpaused`, `lagPaused`, `spare` are no longer assumed here: the counted frames are the frames that end not paused, and the four bytes are in the guard of `keep.clean` ([One whole frame in control](f-6-19-FrameKeep.md)).
* `state` (now a field of `OnFrames`, on every frame up to the touch; it was `Moves.state`, on the clean frames up to `T`): what stays is `Player_State` ∈ {0, 1, 2} and no jumpspring. They are written by the code of the map and the objects (the jumpspring when he lands on it, `Player_State` by the collision routine). A walk of a frame in control knows neither the map nor the objects, so it cannot keep them. Which conditions on the tiles would give them, and why they are not smaller: [above](#the-players-state-and-the-jumpspring-not-proved). `AreaType`, `SwimmingFlag`, `PlayerChangeSizeFlag` are proved (`OnFrames.areaAll`), and so is `PrevA` (`OnFrames.prevAll`).
* `After`, now `AfterP`: the position on a frame that moves right at the scroll handler. If the speed stays, the position stays; if the speed ends 0, the position ends 1 px behind the move or at most 1 px past the frame's start. The facing and the collision bits are no longer asked here: they are theorems ([above](#after-the-scroll-handler-the-facing-the-subspeed-and-the-collision-bits)). The subspeed (`After.f`) and `coll` on a frame that moves left or not at all there follow from `collide` (`After.of`). `storedQ` is no longer assumed ([above](#the-stored-speed-at-the-scroll-handler)).
* `faceJ`: on frames 1 to 8, a frame that ends with the speed 0 and the subspeed 0 has the facing of the scroll handler at its end. These frames must follow `hstep` (no hit before `J`), so here a hit is not enough. He stands still on such a frame; a walk does not know whether a climbing tile turned him.
* `spareE`, `spareC` and `spareV` are not assumed here any more: all are in the guard `guardE` of `keep.cleanE` (`spareE` from round 10, `spareC` from round 13, `spareV` from round 14). From this round `guardE` protects the facing and the subspeed (`FrameKeep.faceE`) and the player's state and the vertical force (`FrameKeep.stateE`) too.
* `vAfter`: on frames 1 to 8, the frame after the scroll handler keeps five of the vertical bytes (`vHard`: the height, its fraction, the vertical speed, the fraction counter, the state). That the routine follows `vstep` is proved (`vert_of`), and the part before it (`Moves.vBefore`), and five bytes after it (`OnFrames.kAt`: the vertical force down, the jump's origin, the jump's halt value, A; `OnFrames.vfAt`: the vertical force). For the five a walk is not enough ([above](#after-the-scroll-handler-four-vertical-bytes)): four of them are written through an index before the scroll handler, so `guardE` cannot protect them; on the ground the collision routine sets `Player_State` to 2 and lands him again; and the walk knows neither the map nor the objects (stomps, platforms, the jumpspring, the blocks).
* `keep.ends`, `keep.clean` and the theorem `keep.start` of [One whole frame in control](f-6-19-FrameKeep.md): the frames are the same, so `ends` is not a field here any more.
* `box`: on frames 1 to 8 the collision routine gives the same result as on the machine at control.
* `reads` is gone: `fr` is a definition on the machines (`frOf`), and that each frame before the touch is a `TopSpeed.Frame` is proved ([above](#the-frames-read-from-the-machines)). What stays of it is on one frame or one machine:
  * `collide`: on each frame before the touch, what the collision routine and the rest of the frame do to the position, and to the subspeed on a frame that ends with the speed 0 and the subspeed 0 (`CollideS`). It speaks of the same part of the frame as `After`, on every frame, not only the clean ones. The enemies' code runs there too. The speed's part is proved (`OnFrames.collideAt`), and so is the subspeed on every other frame (`FaceKeep.keepZ_end`). On a frame that ends with the speed 0 and the subspeed 0 the walk cannot tell whether the climbing routine set a subspeed that was not 0 to 0; `TopSpeed.Frame` asks `f' = f₂` on every frame, so this stays. For the position the walk fails at the enemies' move, the platforms that move sideways, the collision routine's push and the screen's edge ([above](#after-the-scroll-handler-the-speed)).
  * `state` on every frame (above).
* `chg.time₂`, `chg.ctlFirst₂`, and the theorem `Run.atCtl`.

**Files.** `Theorems/SurfaceFrames.lean` (`frOf`, `OnFrames.reads`, `OnFrames.collAll`), `Theorems/SurfaceRead.lean` (`CollideE`, `read_move`, `frame_readE`, `frameE`, `frameH`), `Theorems/CtrlKeep.lean`, `Theorems/PrevKeep.lean` (`prev_end`), `Theorems/AfterKeep.lean` (`keepH`, `subs_once`), `Theorems/CollKeep.lean` (`splitXAt`, `walkKX`, `collCheck`, `coll_end`, `cleanC_of`, `spareC_of`), `Theorems/CollideKeep.lean` (`rkOff`, `walkKV`, `vCheck`, `endKV`, `speed_end`, `cleanV_of`, `spareV_of`), `Theorems/VertKeep.lean` (`kI`, `kCheck`, `keep_end`), `Theorems/FaceKeep.lean` (`zI`, `zCheck`, `keepZ_end`, `splitYAt`, `bCheck`, `bits_end`, `vfC`, `vfCheck`, `vf_end`, `cleanZ_of`, `cleanB_of`, `cleanVF_of`), `Theorems/SurfaceLate.lean` (`sum_ge_late`, `level_ge_of_late`), `Theorems/VertModel.lean`, `Theorems/FrameModel.lean` (`move_masked`, `trace_inFrame`, `stored_path`), `Theorems/FrameWalk.lean` (`InFrame`),
`Theorems/SurfaceRun.lean` (`far`, `Statement.fric`), private `Proof/SurfaceFrames.lean` (`side_start`), `Proof/PoleJoin.lean` (`pole_numbers`, which now includes `ctrlCheck`, `afterCheck`, `prevCheck`, `hCheck`, `storedOK`, `collCheckAll`, `vCheck`, `kCheck`, `zCheck`, `bCheck` and `vfCheck`; `pole_far_count`), `Proof/SurfaceRun.lean` (`surface_run`, with `top_frictionCheck`).

**Reproduce.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # the table above, about 9 minutes of CPU
.lake/build/bin/smbrta surface-read-check FM2 200      # the frames read from the machines, about 2 minutes of CPU
.lake/build/bin/smbrta vert-model-check                # vertOK and each of its cases, about 0.1 s
.lake/build/bin/smbrta mask-model-check                # maskOK and its parts, about 0.1 s
.lake/build/bin/smbrta ctrl-keep-check                 # the walk up to the player's routine: each of the 25 bytes and the pause bit, about 4 s
.lake/build/bin/smbrta ctrl-after-check size           # the walk after the cut (afterCheck), about 20 s; `pause` and `area` watch fewer bytes
.lake/build/bin/smbrta ctrl-prev-check                 # round 8's search after the cut for PrevA, without the cut at the stores (not in the proof), about 10 s; exit 1 (26 failing frame ends)
.lake/build/bin/smbrta prev-why none|cut                # the same search, printing the paths to the failing frame ends; with `cut` the stores of noStore cut: 0 failures
.lake/build/bin/smbrta prev-check                       # prevCheck, about 3 s
.lake/build/bin/smbrta after-keep-check                 # the searches of AfterKeep and hCheck, about 4 s
.lake/build/bin/smbrta after-bytes guard|prot           # the second search for each horizontal byte: guard = keep.cleanF only, prot = the byte protected too
.lake/build/bin/smbrta after-real FM2 100               # SpareE, PrevOK, keepH, storedQ, After on real frames, about 80 s
.lake/build/bin/smbrta stored-check                     # storedOK and its parts, about 0.4 s
.lake/build/bin/smbrta spring-cut-check                 # the walk after the cut with the jumpspring byte watched and its stores stopped (no part of the proof), about 1 s
.lake/build/bin/smbrta spring-real FM2 100              # the writes of the jumpspring byte and of the state on real frames, about 80 s
.lake/build/bin/smbrta coll-cut-check                   # round 11's walk with the collision bits watched (no part of the proof), about 1.4 s; exit 1 (4 failures)
.lake/build/bin/smbrta coll-key-check 0                 # the same with the byte 0 protected and in the key (no part of the proof), about 9 minutes; exit 1
.lake/build/bin/smbrta coll-split-check                 # the search with X split and collCheck, about 9 s
.lake/build/bin/smbrta coll-real FM2 200                # SpareC and the collision bits on real frames, about 2 minutes
.lake/build/bin/smbrta keep-frames-check FM2 100        # CleanK of guardE (the collision bits, the speed and vertE too) on real frames, touch frames too, about 4 minutes
.lake/build/bin/smbrta collide-keep-check               # the search of the walk of the speed and vCheck, the tries for the subspeed, about 5 s. exit 0
.lake/build/bin/smbrta collide-real FM2 200             # SpareV, the speed, the subspeed, the facing, the collision bits, CollideS and AfterP after the scroll handler on real frames, about 7 minutes
.lake/build/bin/smbrta face-keep-check                  # the searches of the walks of FaceKeep, zCheck, bCheck and vfCheck, about 12 s; also the facing with the end "followed" and the vertical force by the jumpspring's byte (no part of the proof)
.lake/build/bin/smbrta face-keep-check ADDR             # the same, the vertical force by the jumpspring's byte also with the RAM byte ADDR protected (the jumpspring's timer: 0 failures)
.lake/build/bin/smbrta pos-after-real FM2 200           # which instructions change the position after the scroll handler on real frames, and by how much, about 7 minutes
.lake/build/bin/smbrta vert-after-bytes prot            # one search for each vertical byte after the scroll handler, the vertical force with the jumpspring, kCheck; about 6 s. exit 1 (the bytes of vHard, and the vertical force with the end "followed")
.lake/build/bin/smbrta vert-after-bytes guard           # the same with the byte not protected: lost at about 95 stores; exit 1
.lake/build/bin/smbrta vert-after-real FM2 400          # vAfter on real frames 1 to 8: the classes at the scroll handler, the changes after it, their order; about 30 s. exit 0
```
