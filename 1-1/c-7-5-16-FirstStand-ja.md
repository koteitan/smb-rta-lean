[← Back](README-ja.md) | [English](c-7-5-16-FirstStand.md) | [Japanese](c-7-5-16-FirstStand-ja.md)

# 落下の最初の立ち

[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `stand_wall` は次のことを言っていました。`C + 51` より前で、床のほかに立つのは `hstep` に従わないフレームの終わりだけです。このページは、落下の最初の立ちについてこれを証明します。`C + 34` より前に床のほかに立って終わるフレームで、最初の操作からそれまでに状態 0 で終わるフレームがないものです。フィールドを使っていた定理は、それより前の立ちがないほかのフレームを使いません。なのでフィールドは、それより前に状態 0 で終わるフレームがあるときの立ちだけを求めるようになりました。本物の走りでは、`C + 51` より前に床のほかに立つのはどれも、落下の最初の立ちです。

## 主張

`vs(n)`、`st(n)`、`hs(n)`、`P(n)` は、フレーム `n` の終わりの縦の状態、プレイヤーの状態、横の状態、位置です。`Follow(n)` は、フレーム `n + 1` が `hstep` に従うことです。`OnFloor(s)` は `st = 0 ∧ y = 176` です。`Q` はフレーム `n + 1` の移動の終わり（その最初の `PlayerSubs`）です。`Q` で、`yhigh` は縦のページ、`pg` はページ、`x`、`y`、`st`、`vy`、`v` は速さのバイトです。

```
WallQ(Q)  :=  yhigh = 1 ∧ pg = 0 ∧ x < 16 ∧ 32 ≤ y < 207 ∧ st ≤ 2 ∧ vy ≥ 0 ∧ (v = 0 ∨ v ≥ 129)

stand_wall（フィールド、狭めた）:
  C ≤ n,  n + 1 < C + 51,  (∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

stand_first（証明）:
  C ≤ n,  n + 1 < C + 34,  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

stand_off_of（証明。RoomCore.stand_off）:
  C ≤ n,  n + 1 < C + 51,  (n + 1 < C + 34  ∨  ∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0,  ¬OnFloor(vs(n + 1))   →   ¬Follow(n)

InRoom.wall（本物の機械の上で証明: Route.Run.roomWall）:
  C ≤ n,  n + 1 < E,  フレーム n + 1 は空中で始まる   →   ∃ Q,  vs(Q) = vstepR(vs(n), A)  ∧
    (WallQ(Q)  →  フレームの終わりで  st ≠ 0  ∨  (st = 0 ∧ y = 176)  ∨  v = 0)
```

速さのバイト `v ≥ 129` は、−128 でない負の速さです。

## 証明の流れ

1. `Follow(n)` のもとでは、フレームの終わりの速さは `hstep(hs(n), inp(n + 1))` の速さです。フィールド `stand_fast` から `V(hs(n)) ≤ −standV`（速さ −14 以下）です。`hstep` の確認（`negCheckJ`、`negJ_of_check`）は、`V ≤ −standV` の定義域のすべての状態とすべての入力で、1 フレームあとの速さのバイトが 129 以上であることを確かめます。負で、−128 でなく、0 でもありません。
2. フィールド `clean` から、フレームの終わりの速さは `Q` での速さか 0 です。0 ではないので、`Q` での速さはそのバイトです。
3. 最初の操作から立っていないので、`vs(n)` は最初の落下の状態です（`fall_mem`）。状態は 2 です。なのでフレームは空中で始まり、`InRoom.wall` は `vstepR` の縦のバイトをもつ `Q` を与えます。最初の落下の確認から、`Q` で次が分かります。状態は 2（`fallCheck`）、`vy ≥ 0` で移動のあとの縦のページは 1（`highCheck`）、高さは 32〜206（新しい確認 `wallYCheck`）です。フレームの始めの縦のページは 1 です（`high_upto`: フレーム `n` までの `high_fall`）。
4. `Q` での位置: フィールド `stand_P` から `P(n) ≤ standP = 3712`（14.5 ピクセル）です。`Follow` のもとでは `P(n + 1) = P(n) + 16 · v < P(n)` です。`Q` はフレームの終わりから右に 1 ピクセル以内です（`q_le_end`: フィールド `clean`、または `FrameModel.Collide`）。なので `P(Q) < 3712 + 256 < 4096` で、ページは 0、`x < 16` です（`page_x_of`）。
5. なので `Q` は `WallQ` を満たし、`InRoom.wall` から、フレームの終わりで `st ≠ 0` か、床の高さで `st = 0` か、`v = 0` です。1 つ目は偽（`st(n + 1) = 0`）、2 つ目も偽（床の上ではない）、3 つ目も偽（1 の手順）です。
6. `Route.Run.roomWall` は、`Run.roomLand` が `InRoom.land` を証明するのと同じように `InRoom.wall` を証明します。`RoomFall.land_frame` が、`Good` で、プレイヤーのルーチンのスタックで、`vstepR` の縦のバイトをもつ `Q` を与えます。`RoomBlocks.blocks_run_trace` が `Q` での `Solid` を与えます。`RoomWall.wall_frame`（[部屋で床のほかに立つフレーム](c-7-5-15-RoomWall-ja.md)）が `Q` からフレームの終わりまで進みます。フレームはプレイヤーのルーチンの中で終わります（`roomStay`）。
7. `stand_off_of` は、それより前に状態 0 で終わるフレームがあるかで場合分けします。あればフィールドです。なければフレームは `C + 34` より前で、`stand_first` です。`RoomRun.toCore` はこれを `stand_off` として `RoomCore` に入れ、`st_ne`、`stand_gap`、`wall_turn` が使います。`st_ne` もいまは同じ条件を求めます。`fall_air`、`wall_right`、`stand_gap` が使うのは `C + 34` より前のフレームで、`wall_turn` が使うのは壁の上の立ちのあとのフレームです。`stand_late`、`land_end_of`、`floor_at_of`、`no_stand_before_land` は `C + 34` より前で `stand_off_of` を使います。
8. 前のフィールドは `C + 50` までのすべてのフレームを求めていました。`C + 34` から `C + 50` までで、それより前に状態 0 のフレームがないものは、どの定理も使わないので、もう求めません。

`stand_first` が使うのは、フィールド `stand_fast`、`stand_P`、`clean` と、`far_inD` と `t0_far` が使うフィールドです。`stand_wall`、`fall_long`、`fall_any`、`stand_late`、`land_at_of`、`floor_at_of` は使いません。

ROM の確認は非公開の `Proof/RoomJoin.lean`（`room_stand_w`: 3 つの向きでの `hstep` の確認、`wallYCheck`、`standP + 256 < 4096`、床の高さが 256 より小さいこと）と `Proof/RoomWall.lean`（`room_wall`、`room_wall_after`、`room_wall_apart`。非公開の道筋がいまはこれを `Route.Run.inRoom` に渡します）にあります。

## 測ったこと

`room-stand-first FM2 300`: 部屋での TAS 自身のフレームと、7 種類の自前の乱数入力の 2100 回の走り（それぞれ 60 フレーム、部屋での TAS の最初の操作から）。

- 126,060 フレーム。フレーム 51 より前に床のほかに立つのは 49 で、どれもフレーム 18〜30 です。種類 1、4、5、6 の 14、5、14、16 回の走りです。TAS が最初に床のほかに立つのはフレーム 52 で、ブロックの上です。
- 49 はどれも落下の最初の立ちです。どれも空中で始まり、移動の終わりで `WallQ` を満たし、速さ 0 で終わります。
- フレーム 51 より前の立ちで、それより前に状態 0 のフレームがあるものはなく、フレーム 34〜50 のものもありません。なので、これらの走りのフレームでフィールドに残るものはありません。
- 同じ走りで（`room-wall-real FM2 300 16 32 207`）、フレーム 60 より前のほかの 4 つの立ちは、ブロックの上の TAS のフレーム 52〜54 と、フレーム 51 でブロックの左の横に着地する 1 回の走りです。

## 残ること

フィールド `stand_wall` は、`C + 51` より前で、それより前に状態 0 で終わるフレーム（床の上でもほかでも）があるときに床のほかに立つことについて残ります。本物の走りでは 1 つも見えません。`wall_turn` がこのフレームを使います（`st_ne` を通して）。壁の上の立ちのあと、`C + 49` までのフレームです。

- `C + 34` からは、フィールド `stand_fast` と `stand_P` が成り立たないので、そこでは速さも位置も分かりません。測った走りの 1 つでは、ブロックの左の横に `C + 51` で立ちます。なので、そこでのフレームは本物の立ちから遠くありません。
- `C + 34` より前の 2 回目の立ち。最初の立ちから `gapF = 8` フレーム以上あと（`stand_gap`）で、最初の立ちは `C + 15` 以降です（`stand_late`）。そのフレームは `anyCheck` の状態で始まりますが、縦のページは最初の落下でしかたどっていません。ジャンプのあとでは、`InRoom.high` がフレームの終わりの縦のページを与えるのは上がっていないときだけです。

**ファイル.** `Theorems/RoomJoin.lean`（`WallQ`、`wallYCheck`、`negCheckJ`、`negJ_of_check`、`WallFacts`、`Checks.standW`、`InRoom.wall`、`high_upto`、`q_le_end`、`page_x_of`、`stand_first`、`stand_off_of`、`RoomCore.stand_off`。`RoomFields.stand_wall` を狭めた）、`Theorems/Route.lean`（`Run.roomWall`。`Run.inRoom` は `RoomWall` の確認をとる）、`Theorems/RoomWall.lean`（`speeds_of`）。非公開の `Proof/RoomJoin.lean`（`room_stand_w`）。プログラム `room-stand-first`。
