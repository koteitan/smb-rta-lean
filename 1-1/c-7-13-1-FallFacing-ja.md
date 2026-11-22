[← Back](README-ja.md) | [English](c-7-13-1-FallFacing.md) | [Japanese](c-7-13-1-FallFacing-ja.md)

# 落下の間の向き（`hstep` に従うフレーム）

[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `facing` は、落下の終わり（`C + 34`）より前で、空中の入力かジャンプの入力のフレームは向きを変えない、と言います。これを使うのは `wall_turn` だけです。壁に触ったあとに右のほかを向くには、ジャンプのない地上のフレームが要ります。

このラウンドでは、`hstep` に従うすべてのフレームでこのフィールドを証明します。ROM での `hstep` の確認を使います。フィールドが求めるのは、`hstep` に従わないフレーム（左の壁でのフレームと、そのすぐあとのフレーム）だけになります。

## 命題

`hs(n)` はフレーム `n` の終わりの横の状態で、`fd` はその向きです。`inp(n + 1)` はフレーム `n + 1` の入力で、`st`（地上なら 0）と `jump`（地上での A の新しい押し）をもちます。`Follow(n)` はフレーム `n + 1` が `hstep` に従うことです。

```
faceCheck(fd)（ROM、fd = 1, 2, 3）:  ∀ s ∈ statesFd(fd), ∀ i ∈ inputsN:  (i.st = 0 ∧ ¬i.jump) ∨ hstep(s, i).fd = s.fd

face_of_check（証明）:  inD(s) ∧ i ∈ inputs ∧ (i.st ≠ 0 ∨ i.jump)  →  hstep(s, i).fd = s.fd

facing（フィールド、狭めた）:
  C ≤ n < C + fall → (inp(n + 1).st ≠ 0 ∨ inp(n + 1).jump) → ¬Follow(n) → fd(hs(n + 1)) = fd(hs(n))
  （前は ¬Follow(n) なしで同じもの）
```

`faceCheck` は `WallFacts` にあります（`face1`、`face2`、`face3`。非公開の `room_stand_w` で `native_decide`）。`face_of_check` は `negJ_of_check` と同じように、正規化した入力を読みます。`norm` は `st` と `jump` を変えません（`norm_st`、`norm_jump`）。

`wall_turn` では、`C` から `b + 1` までの鎖の各フレームは `Follow` か（このとき `hs(n + 1) = hstep(hs(n), inp(n + 1))` で、そのフレームの `inD`（`inD_at`）と `face_of_check` を使います）、そうでないか（このときフィールド）です。

そこで `hstep` が向きを変えない理由: `hstep` で向きを書くのは、地上で左か右があってジャンプがないときだけです。ジャンプがあると、移動のルーチンの前に状態が 1 になります。`X_Physics` と `ImposeFriction` は向きを書きません。確認は、定義域のすべての状態と入力でこれを確かめます。

## 測ったこと

`room-approach-check FM2 300 1`（大きいプレイヤー、人工の状態）と `… 300 0`（小さいプレイヤー）。どちらも TAS と自分の入力 2,700 本です。`C + 1` から `C + 34` までのフレームで、プレイヤーのルーチンで機械から読んだ入力が空中かジャンプのものです。

| 大きさ | そのフレーム | そのうち `hstep` に従わないもの（フィールド） | そのうち向きが変わるもの（フィールドが偽） | `hstep` に従って向きが変わるフレーム（バグ） |
|---|---|---|---|---|
| 大きい | 91,834 | 7,462 | 0 | 0 |
| 小さい | 91,823 | 7,478 | 0 | 0 |

## 残ること

- `hstep` に従わないフレームでの `facing`。そのフレームでは、当たり判定のルーチンが左の壁で止めます。プレイヤーのルーチンからフレームの終わりまで向きのバイトを追う部屋のフレームの歩きで証明できます（つるを登るルーチンと旗ざおのルーチンが向きを書きます。パート e の `FaceKeep` と同じです）。
- `stand_fast`、`stand_P`: 変えていません。同じ走りで測りました。`C + 34` より前の立ちは 44 個（大きい）と 50 個（小さい）で、すべて 1 つ前のフレームで `−V ≥ standV` と `P ≤ standP` でした。いちばん小さい `−V` は 3952（大きい）と 4256（小さい）で、`standV = 3584` です。いちばん大きい `P` は 3632 で、`standP = 3712` です。証明には、1 つ前のフレームの位置を使う左の壁での当たり判定が要ります。

ラウンド 29: `hstep` に従わないフレームでの `facing` も、その歩きで証明しました（[落下の間の向き（すべてのフレーム）](c-7-13-2-FaceWalk-ja.md)）。フィールドはなくなりました。

**ファイル。** `Theorems/RoomJoin.lean`: `faceCheck`、`norm_jump`、`face_of_check`。`WallFacts.face1`、`face2`、`face3`。`RoomFields.facing` を狭めた。`wall_turn`。非公開: `room_stand_w`（`native_decide` の行が 3 つ増えた）。ラウンド 29 から `WallFacts.face1`〜`face3` とこの 3 行はなくなった。向きはすべてのフレームで証明した（[落下の間の向き（すべてのフレーム）](c-7-13-2-FaceWalk-ja.md)）。プログラム: `room-approach-check`（カウンタ 34 から 37。38 から 40 は `stand_fast` と `stand_P` を測る）。
