[← Back](README.md) | [English](f-6-3-PoleJump.md) | [Japanese](f-6-3-PoleJump-ja.md)

# Read the pole jump from the machines

**Partial result.** A counted frame that starts standing and reads a new press of A reaches the scroll handler with `VertJump.jumpOff` of the preceding counted machine's height and stored speed. It is jumping, rising, and has the jump's halt value. `take_subs` proves this with the existing frame conditions. `take_end` gives the same at the frame's end with the five-byte condition `VEnd` stated explicitly. No field of `PoleJoin.Run` was removed or added: its `direct` still supplies an arbitrary arc, and its `reads`, `path`, `atY`, `atRising` remain assumptions.

## From one machine to the next

The new file is `Theorems/PoleJump.lean`.

- `vert_jumpH`, `vert_airH` export the halt value already required by the goals of the existing movement walks. They use the same ROM checks as `VertJump.vert_jump` and `VertAir.vert_air`.
- `atV_of_atFrame` lists the required subset of `FrameModel.AtFrame`: good machine, routine address and stack, control routine, area type, player state, no jumpspring animation, no swimming, no size change.
- `take_read` follows the real timed frame from the player's routine to the scroll handler, within `FrameModel.moveLen` instructions. A new press means A is read in `SavedJoypadBits` and was off in `PreviousA_B_Buttons`, both at that routine. It does not equate the input pad with that read.
- `take_subs` uses `OnFrames.readE_at` and `StopRead.keep_at`. Its height, standing state and stored speed come from `seq(j-1)`. It applies also to the touch frame (`j ≤ g`).
- `air_subs` uses the same frame conditions, an air state, `HaltOK`, and `PrevOK`. The vertical step uses stored speed zero, as proved by `VertAir`; the actual air routine's stored speed need not be zero.

The frame conditions are named arguments: the control/model/friction/idle checks, `OnFrames`, start conditions for each frame, `AreaRun`, initial zero speed and position, the range bound `g ≤ farN`, and the counted-frame bounds. They come from the existing `frames` and `keep` arguments of the pole route. `PrevOK` can be propagated from control by `OnFrames.prevAll` with the existing previous-button check. Halt is exported by the takeoff and air lemmas. No new run condition is hidden here.

## What is left after the scroll handler

`VEnd` states exactly that the height, height fraction, vertical speed, fraction counter and player state (`SurfaceFrames.vHard`) are preserved from a scroll-handler visit to the counted frame's end. It is **an explicit hypothesis**, not a theorem for all frames above ground. Existing `vAfter` covers only its earlier range, not all frames of the final jump.

Given `VEnd` and an air state at the handler, `end_vertical` proves equality of all nine vertical-state components. The force-down, origin, halt and A bytes follow from `OnFrames.kAt`. The vertical force follows from `vfAt`: its exceptional case would end standing, excluded by the preserved air state. `take_end` and `air_end` then give the actual end states. Only frames before the touch use this end preservation; the touch's own vertical state must be read at the handler before the grab changes it.

## The arc and `reads`

`arcM` takes a sequence of supplied vertical states and keeps the model's counters (`k`, `low`, `above`). `arcOf` uses the actual stored speed of `seq(T-1)` for its takeoff class. `reads_of_machine_arc` proves:

```
(arcOf sy seq v T n).fast = true
    -> AirFastSpeed <= stored_speed(seq(T-1))
```

This is the implication formerly asked by `ApproachCases.reads`, for this defined arc. It does not prove that the arbitrary arc currently supplied by `Run.direct` is that arc.

`arcM_start` gives membership in the jump model's initial states when the actual takeoff has the ground height and its stored speed is at most `TopSpeed.top`. `arcM_step` gives a successor from one actual vertical step, as long as the model has not stopped. `path_of_frames` assembles `JumpPath` on `VertModel.vmach`, with the ground takeoff, stored-speed range, each air step, no stop before the touch, and the duration bound explicitly stated. It does not discharge those hypotheses for the route.

`arcM_atY` and `arcM_atRising` follow directly for the supplied touch state. For the route one must still identify that state with the touch machine and its currently free `touchY` and `touchRising`. These endpoint equalities do not require all intervening air steps; `path` does.

Private `Proof/PoleJump.lean` checks the grab-height property of the jump model on `vmach`, whose stack and halt match the movement lemmas. This is a separate ROM check; the original route and its model were not changed.

## Checks and remaining work

The augmented `stop-read-check FM2 100` compares actual takeoff and air states at the handler with the proved model steps. Where the five hard bytes are preserved, it also compares the frame's end. It counts frames where those bytes change separately: such frames are not assumed to meet `VEnd`. `pole-join-check FM2` remains the route regression check.

Still needed to remove route assumptions: a suitable machine takeoff from the ground, the five-byte preservation through its air frames, the remaining model path bounds, and the link to the actual touch. Replacing the current fields with these stronger or unrelated fields would not be a removal, so this partial result leaves the route fields unchanged.

The final full build and both commands exited 0. Across 50,821 counted frames, 873 takeoffs and 26,622 air steps matched at the handler; 873 takeoffs and 25,543 air steps also matched at the end under measured `VEnd`. There were 1,185 frames with changed hard bytes, counted separately, and no tested takeoff stored speed exceeded `TopSpeed.top`. The new `vmach` grab-height check passed. The route and new theorem axiom checks exited 0 with no `sorryAx`.
