[← Back](README.md) | [English](c-7-5-13-LandBytes.md) | [Japanese](c-7-5-13-LandBytes-ja.md)

# The collision-disable flag and the vertical page in the first fall

The landing of the first fall (1-1-c-7-5-12) asked two bytes at the end of the move of frame `C + 34` (`PlayerSubs`, here Q): the collision-disable flag 0 and the vertical page 1. This page proves both. The field `landQ` is gone.

## Statements

```
flag(q) = ref's flag (= 0)                       at every PlayerSubs q of a frame of the room         (RoomLand.controls_at_subs)
yhigh(fe C) = 1                                  at first control                                      (StartAt.high)
yhigh(M) = 1  →  yhigh(Q) = yhigh(vRunR(vs M, a))                                                       (RoomFall.high_frame, InRoom.high)
          and  vy(vstepR(vs M, a)) ≥ 0  →  yhigh(frame end) = yhigh(vRunR(vs M, a))
∀ d < 34,  yhigh(fm (C + d)) = 1                                                                        (RoomRun.high_fall)
```

`vRunR(s, a)` is the machine of `vstepR` after the movement routine: the reference machine of `vstep` with the vertical bytes `s` and A pressed or not (`VertModel.vRun`).

## How it is proved

1. **The flag.** The change into the room clears it, and no step of the room writes it. So it is now one of the bytes that the room's condition knows (`ScreenPage.roomNames`). The rows of the change at first control know it with the reference's value, and the room's walk keeps it (the checks `screen_start` and `map_check` pass as before). At `PlayerSubs` the walk knows it, so `RoomLand.controls_at_subs` gives it, as it gives the routine, the screen bytes and the jump spring (`controlKeys`). `RoomLand.stand_at` no longer asks it.
2. **The vertical page at first control.** The rows of the change know it, and it is 1 there (`RoomStart.vBytes`, `vOK`; the check `room_start`).
3. **Before the player's routine** no step of the frame writes it: it is now in `RoomVert.vKeepA`, the bytes that the walk to the player's routine keeps. So the frames that end paused keep it too (`InRoom.keepH`).
4. **The movement routine** adds the carry of the height into it. `OpenVert.vert_airH` (the opening's check `open_vert_check`, at the same stack) says that at Q it is that of `vRunR`. `RoomFall.high_frame` puts this on the room's frames; the frame comes to Q once (`after_QH`), so every `PlayerSubs` after the player's routine is that Q.
5. **After Q**, falling, the walk from the scroll handler (`walkC`) keeps it: it is now in `vRestW`, the bytes the walk keeps besides the landing's (`after_QH`). The bytes apart (`apartC`) now say that it is out of the block buffers.
6. **The check `highCheck`**: on every state of the first 34 layers of the first fall, with A or not, `vstepR` does not rise and `vRunR` has the vertical page 1.
7. `RoomRun.high_fall` puts 2–6 together frame by frame. `RoomRun.land_at_of` takes the vertical page at the landing frame's Q from it, and the flag comes from the walk.

## Measured

- The TAS and 300 own random inputs: at Q of the landing frame the flag was always 0 and the vertical page 1 (1-1-c-7-5-12).

**Files.** `Theorems/ScreenPage.lean` (`roomNames`), `Theorems/RoomLand.lean` (`controlKeys`, `refCheck`, `stand_at`), `Theorems/RoomStart.lean` (`vBytes`, `vOK`), `Theorems/RoomVert.lean` (`vKeepA`), `Theorems/RoomFall.lean` (`vRestW`, `apartC`, `phC`, `after_QH`, `high_frame`, `high_room`), `Theorems/RoomJoin.lean` (`vRunR`, `StartAt.high`, `highCheck`, `highCheck_spec`, `Checks.high`, `InRoom.keepH`, `InRoom.high`, `RoomRun.high_fall`, `RoomRun.land_at_of`; `LandB` and the field `landQ` are gone), `Theorems/Route.lean` (`Run.roomKeepA`, `Run.roomHigh`, `Run.inRoom`). Private `Proof/RoomJoin.lean` (`room_checks.high`).
