[← Back](README.md) | [English](e-2-10-3-9-PositionOrder.md) | [Japanese](e-2-10-3-9-PositionOrder-ja.md)

# The order of the calls after the scroll handler

**Claim.** Take a frame in control, with the hypotheses of `PositionWriters.writers_end`, and let q be the instruction at the scroll handler Q. Call the scroll handler's call *open* at a machine R (`Ph0(R)`) when the stack is at least two bytes below the stack sQ at Q, and four bytes of the stack's page still hold the return addresses of that call and of the routine it is in (`phQ`). Then:

```
ph_down          : q < j ≤ n,  Ph0(T n)  →  Ph0(T j)
clamp_before_push: q ≤ a, q ≤ a',  pc(T a) = clamp's entry,  pc(T a') = push's entry  →  a < a'
clamp_once       : q ≤ a < b' ≤ a₂,  pc(T a) = clamp's entry,  s(T b') = s(T a) + 2  →  pc(T a₂) ≠ clamp's entry
chain_order      : in a chain of pieces from a ≥ q to the frame's end, a piece at the clamp's entry is the only one, and it comes before every piece at the push's entry
```

All indices are in the frame. In words: every clamp at the screen's edge comes before every push (`ImpedePlayerMove`), and once the clamp has returned (the stack is two bytes up again) no clamp comes. In the chain of `PositionDispatch` there is at most one clamp, and the pushes come after it. The number of pushes is not bounded here.

**Proof.** The walk of `PositionWriters` now asks three more things at its states and steps (`okW`, `walkKW`), with what it knows of `Ph0` (`phK`: known open; `phN`: known not open):

- at the clamp's entry the call is known open, and the stack is two bytes below sQ (`AtW.phC`);
- at the push's entry it is known not open (`AtW.phI`);
- a step into a state that may be open comes from a state known open, or from Q (`FrameW.ph`).

The private check proves this on the ROM (`position_writers_check`, about 11 s). So the machines where the call is open come right after q, one after another (`ph_down`). A push's entry is not open, and every machine between q and a clamp's entry is open, so the push comes later. The clamp returns with the stack at sQ, where the call is not open, so no later machine is open, and no later clamp comes.

**A first try that failed.** With only the two bytes of the call's own return address, the check on the ROM was false. A native diagnostic found two steps where it failed: in routines that the game engine calls at the same depth as the player's routine, two pushes of bytes the walk does not know bring the stack to sQ − 2. So `Ph0` also asks the two bytes above them: the return address of the routine that the player's routine is in (`callerRet`). At those steps the walk knows these two bytes and one of them differs, so it knows that the call is not open, and the check is true.

**What is not proved.** The number of pushes in a frame (by its code the collision routine calls the push at most once, but the platforms' routine can call it again; neither is proved), and the relation of the clamp's target to the frame's start (d ≤ 0). `CollideS.P` and `AfterP.stop` still need them; no field changes here. On real frames no frame had two calls ([1-1-e-2-10-3-8](e-2-10-3-8-PositionKeep.md)).

**File:** `Theorems/PositionOrder.lean`. Changed: `Theorems/PositionWriters.lean` (`phL`, `phK`, `phN`, `Ph0`, `callerRet`, `phQ`, `AtW.phC`, `AtW.phI`, `FrameW.ph`).
