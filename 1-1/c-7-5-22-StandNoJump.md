[← Back](README.md) | [English](c-7-5-22-StandNoJump.md) | [Japanese](c-7-5-22-StandNoJump-ja.md)

# A later stand with no jump since

The field `stand_wall` of [Joining the bonus room](c-5-RoomJoin.md) says that before `C + 51` he stands away from the floor only at the end of a frame that does not follow `hstep`. Since round 22 ([The first stand of the fall](c-7-5-16-FirstStand.md)) it is asked only after an earlier frame that ends in the state 0. This round asks it from the end of the fall (`C + 34`) on only when no frame since that earlier frame has a jump in its input. The only theorem that uses those frames, `wall_turn`, has no jump there.

## Statements

`vs(n)`, `st(n)` are the vertical state and the player's state at the end of frame `n`. `inp(n + 1).jump`: frame `n + 1` has a new press of A on the ground. `Follow(n)`: frame `n + 1` follows `hstep`. `OnFloor(s)`: `st = 0 ∧ y = 176`.

```
stand_wall (field, narrowed):
  C ≤ n,  n + 1 < C + 51,  (∃ j, C < j ≤ n ∧ st(j) = 0),
  (n + 1 < C + 34  ∨  ∃ j, C < j ≤ n ∧ st(j) = 0 ∧ ∀ l, j ≤ l ≤ n → ¬inp(l + 1).jump),
  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)
  (before: the same without the second line)

RoomCore.stand_off (proved, narrowed in the same way):
  C ≤ n,  n + 1 < C + 51,
  (n + 1 < C + 34  ∨  ∃ j, C < j ≤ n ∧ st(j) = 0 ∧ ∀ l, j ≤ l ≤ n → ¬inp(l + 1).jump),
  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)
```

## How it is proved

1. `stand_off_of` splits on an earlier frame that ends in the state 0, as before. With one, the field; the field's new premise is `stand_off`'s premise. With none, the frame is before `C + 34` (the second case of the premise has such a frame), and `stand_first`.
2. `st_ne` takes the same premise. `fall_air`, `stand_gap`, `wall_turn`'s first stand and the frames before `C + 34` use its first case.
3. `wall_turn` uses its second case on the frames after its stand `i` on the wall, up to `i + k`. It shows on these frames that he does not stand again: with no jump since `i` he falls with the first force, so he is not on the floor for `k` frames (`hnoj`). The no-jump fact is what `hnoj` gives on the frames before (`ih`, and `hnoj` itself on the air frames).

## Why this matters

Before this round the field also asked a stand after a jump from the floor, for example a landing on top of the block before `C + 51`. Such a landing follows `hstep` when no side stops him on that frame, and then the field is false on it. Measured runs stand there from frame 51 on (the TAS on the block at frames 52 to 54, one own run at the block's left side at frame 51: [The first stand of the fall](c-7-5-16-FirstStand.md)), one frame past the field's range. With no jump since a frame in the state 0 he cannot get onto the block: its left side is a wall of `h` rows above the floor.

## Measured

`room-stand-first FM2 300` (this round, the TAS and 2,100 own runs, 126,060 frames): 49 stands away from the floor before frame 51, all first stands of the fall at frames 18 to 30; none comes after an earlier frame that ends in the state 0. So the old field and the narrowed one have no measured frame.

## What remains

The field for a stand from `C + 34` to `C + 50` after a frame in the state 0 with no jump since, and before `C + 34` after an earlier stand. A proof needs, at the end of the move of such a stand, the conditions of `WallQ` (the vertical page after a frame that starts standing away from the floor is not followed), and a link between the speed at the end of the move and `hstep` (the push of 1 px with the speed 0 at the wall: under `Follow` the end is `P(n)`, so the speed at the end of the move would be −16; the model of a frame that stops, `TopSpeed.Frame`, bounds the speed there only from above).

**Files.** `Theorems/RoomJoin.lean`: `RoomFields.stand_wall`, `RoomCore.stand_off`, `stand_off_of`, `st_ne`, `wall_turn`.
