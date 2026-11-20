[← Back](README.md) | [English](c-7-5-14-FloorFrames.md) | [Japanese](c-7-5-14-FloorFrames-ja.md)

# The floor frames after the fall

The field `vfloor` of [Joining the bonus room](c-5-RoomJoin.md) said: with no wall hit, a frame from `C + 34` to `C + 49` that starts on the floor before the entry is `VFrame`. He stays on the floor with a ground input, or he takes off with a jump input to a first state of a jump from the floor (`arcStart`). This page proves both cases. The field `vfloor` is gone.

## Statements

`yF` is the floor's height (176), `yhigh` the vertical page, `vy` the vertical speed, `fm(n)` the machine where frame `n + 1` begins, `Q` the end of the frame's move (the first `PlayerSubs`).

```
jump(n + 1),  OnFloor(vs n)   →   vs(n + 1) = jumpOffR(yF, ab) = x.s  for some  x ∈ arcStart(yF)                    (takeoff_of)
no jump,  OnFloor(vs n),  yhigh(fm n) = 1,  vy(vs n) ≥ 0
          →   OnFloor(vs(n + 1))  ∧  vy(vs(n + 1)) = 0  ∧  yhigh(fm(n + 1)) = 1                                    (stay_of)
∀ e ≤ d,  OnFloor(vs(C + 34 + e))   →   yhigh(fm(C + 34 + d)) = 1  ∧  vy(vs(C + 34 + d)) = 0                         (floor_run)
NoWall,  C + 34 ≤ n < C + 49,  ∀ j ∈ [C + 34, n],  OnFloor(vs j)   →   VFrame(n)                                     (vfloor_of)
```

## How it is proved

1. **The takeoff.** A frame that starts standing with a new press of A ends on `jumpOff` of its height and of the stored speed (`InRoom.jump`, `RoomRun.vjump_of`). The new check `offCheck` says: for each of the 256 stored speeds, the takeoff from `yF` is the first state of one of `arcStart`, which has the stored speeds up to the top speed. The input is a jump input: it is read at the player's routine, where the state is that of the frame's start, 0 (`gnd_in_of`).
2. **Standing to the end of the move.** `VertStand.vert_stand` follows the movement routine on two machines, as `OpenVert.vert_airH` does in the air, in the 6 cases standing with no new press of A (`vCasesS`). In each case no step writes the height, `vy`, its fraction, the state or the vertical page (`goalVS`), and the frame comes to `Q` with the stack of the player's routine. So at `Q` these five bytes are those of the frame's start (`RoomFloor.floor_frame`).
3. **The foot check at `Q`.** `RoomLand.stand_at` at the height `yF` (the new checks `room_floor`: the walk from `Q` for each of 248 values of x, the cells, the reference machine) says that he is at the side check in the state 0. At `Q` the page is 0 and x is below 248: `q_pos`, the general form of `landQ_pos`, with the new number fact `floorP`: `P₁ + 640 · 49 + 256 < 256 · 248`.
4. **The walk standing knows the side check.** The walk from the player's routine standing (`walkS`) now also asks that a state which came there standing and has not landed (`[7, _]`, `[5, h]`) is not in the state 0 at the side check (`sideOK`); and it keeps the vertical page (`vRestS`). So in `RoomStand.after_RS` the case "the height kept and the state 0 or 2" also says that no step comes to the side check in the state 0. Step 3 rules that case out: the frame lands. At its end the state, `vy` and its fraction are 0, and the height is `yF & F0 = yF` (the new fact `floorRow`).
5. **The vertical page and `vy` at the frame starts**, by induction from the end of the fall: the landing frame ends with `vy = 0` and the vertical page 1 (`land_end_of`), and the frames between keep the page (`InRoom.keepH`). A floor frame followed by a floor frame has no jump: a takeoff ends in the air (`arc_facts`). So it is a frame of step 4, and the next frame starts with the page 1 and `vy = 0` (`floor_run`).
6. **In `RoomCore`** the field `vfloor` now asks that he has stood on the floor since the end of the fall. Its three uses have this: `v_chain` now says it of the floor case, and `floor_all` gives it to `early_of`.
7. **The head.** The field asked that the frame does not come to the head's collision with a block (`InRoom.bump`). The new proof does not need this: the walks follow the whole frame.

## Measured

- The walk standing with `sideOK` and the vertical page: table 20,937 states, none fails; the search has no end it does not accept (`room-stand-check`). On the TAS and 140 own random runs, 920 frames start standing with no jump and end in the room; all are `StandNext`.
- The checks of step 3 at the height 176 for x below 248, run on a scratch file: all true (133 s in the interpreter).

**Files.** `Theorems/VertStand.lean` (new: `vCasesS`, `standKeep`, `goalVS`, `caseOKS`, `standOK`, `vert_stand`), `Theorems/RoomFloor.lean` (new: `floor_frame`), `Theorems/RoomStand.lean` (`vRestS`, `sideOK`, `phS`, `after_RS`, `stand_frame`), `Theorems/RoomJoin.lean` (`offCheck`, `offCheck_spec`, `Checks.off`, `Checks.floorP`, `Checks.floorRow`, `InRoom.floor`, `RoomCore.vfloor`, `v_chain`, `RoomRun.gnd_in_of`, `takeoff_of`, `q_pos`, `landQ_pos`, `land_end_of`, `stay_of`, `floor_run`, `vfloor_of`; the field `RoomRun.vfloor` is gone), `Theorems/Route.lean` (`Run.roomFloor`, `Run.inRoom`). Private `Proof/RoomJoin.lean` (`room_checks.off`, `floorP`, `floorRow`), `Proof/RoomLand.lean` (`room_floor`), `Proof/RoomStand.lean` (`stand_vert_check`).
