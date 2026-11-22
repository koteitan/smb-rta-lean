[← Back](README-ja.md) | [English](c-7-13-2-FaceWalk.md) | [Japanese](c-7-13-2-FaceWalk-ja.md)

# 落下の間の向き（すべてのフレーム）

[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `facing` は、落下の終わり（`C + 34`）より前で、空中の入力かジャンプの入力のフレームは向きを変えない、と言っていました。ラウンド 28（[落下の間の向き（`hstep` に従うフレーム）](c-7-13-1-FallFacing-ja.md)）は、`hstep` に従うフレームでこれを証明しました。このラウンドでは、すべてのフレームで証明します。部屋のフレーム全体の歩きで、プレイヤーのルーチンからフレームの終わりまで向きのバイトを追います。フィールド `facing` はなくなりました。

## 命題

`fm(n)` はフレーム `n + 1` が始まる機械、`end(n)` はその終わりの機械、`T_k` はフレームの `k` 命令あとの機械です。プレイヤーのルーチンで（`T_k.pc = PlayerCtrlRoutine`）: `st` はプレイヤーの状態、`a` はルーチンが読むジョイパッドのバイトのビット 7（いまの A）、`p` は 1 つ前のフレームの A のビット 7 です。`fd` は向きのバイトです。

```
FaceIn(T)  :=  st = 1  ∨  st = 2  ∨  (st = 0 ∧ a = 1 ∧ p = 0)

face_frame（証明、RoomFace）:
  フレームは部屋の条件で始まり、すべての命令は SiteOK、フレームはプレイヤーのルーチンで終わる、
  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  FaceIn(T_k)   →   fd(end(n)) = fd(T_k)

InRoom.face（本物の機械で証明: Route.Run.roomFace）:
  C ≤ n,  n + 1 < E,  T_k.pc = PlayerCtrlRoutine,  T_k.frame = fm(n).frame,  FaceIn(T_k)   →   fd(end(n)) = fd(T_k)

facing_of（証明。RoomCore.facing）:
  C ≤ n < C + fall,  inp(n + 1).st ≠ 0 ∨ inp(n + 1).jump   →   fd(hs(n + 1)) = fd(hs(n))
```

`inp(n + 1)` はプレイヤーのルーチンで読みます（`read_inp`）。そこで `st ≠ 0` なら状態は 1 か 2 です（`InRoom.cut`: 状態は 0、1、2 のどれか）。`jump` なら状態は 0 で `a = 1`、`p = 0` です（`faceIn_of_read`）。プレイヤーのルーチンでの向きはフレームの始まりの向きです（`InRoom.before`）。前のフィールドは `facing_of` と同じものを、前提 `¬Follow(n)` を 1 つ多くして求めていました。`facing_of` はその前提を使いません。

## 歩きのしくみ

歩きは `RoomVert` の部屋の 1 フレーム全体の歩きです（`RoomMap` の抽象機械で、部屋のバイト、ブロックのバッファ、すべての書きこみの行き先を知っています）。`RoomVert.walkB` や、当たり判定のルーチンからの `RoomWall` の歩きと同じく、ビットを 1 つもちます。

1. プレイヤーのルーチンで、歩きは状態を切り分けます（`piecesF`）。状態 1、状態 2、`a = 1` で `p = 0` の状態 0 はビットをもちます。`a = 0` の状態 0、`a = 1` で `p = 1` の状態 0、状態 3、ビット 1 より上のビットがある状態には `[2]` の印をつけます。切り分けはすべての機械をおおいます（`piecesF_cover`）。ビットをもつ切れはしは `FaceIn` の機械だけをおおい、`[2]` の切れはしは `FaceIn` でない機械だけをおおいます（`piecesF_class`）。
2. ビットをもつ状態の 1 歩が向きを書くかもしれないときは、ビットを落として `[1]` の印をつけます（`mayWriteF`。コインを消す書きこみはブロックのバッファにだけ書きます）。歩きは、フレームがプレイヤーのルーチンに 1 回だけ来ることを求めます。
3. フレームの終わりで `[1]` の状態は、ルーチンのバイトがわかっていて、参照の値と違わなければいけません（`finF`）。つまりフレームはプレイヤーのルーチンを出ています。
4. なので、`FaceIn` でプレイヤーのルーチンに来て、プレイヤーのルーチンで終わるフレームでは、そこから終わりまでのどの歩みも向きを書きません（`after_F`。証明は `RoomVert.after_Q` と同じです）。

確認が通る理由（決めるのは確認で、これはコードを読んだだけのものです）: プレイヤーのルーチンで向きを書くのは、地上で左か右があるとき（`OnGroundStateSub`）、泳いでいるとき、つるを登るルーチンです。状態 1 か 2 なら、状態のルーチンはジャンプか落下のものです。部屋では泳ぐ旗は 0 です。地上で A を新しく押すと、状態のルーチンの前にジャンプが始まり、状態のルーチンはジャンプのものになります。当たり判定のルーチンでは、旗ざおとつるで向きを書きます。歩きは部屋の地図を知っていて、そこに来ないか、プレイヤーのルーチンを出ます。

確認は `room_face : RoomFace.checkF sy screenNames ctx = true` と `room_face_apart`（向きのバイトはブロックのバッファの外、切り分けの 3 つのバイトは別々）で、非公開の `Proof/RoomWall.lean` で `native_decide` です。プログラム（`room-face-check`）では約 12 秒、374 MB です。

## 測ったこと

フィールドがなくなったので、測るものは残りません。`room-approach-check FM2 300 1`（大きいプレイヤー、人工の状態）と `… 300 0`（小さいプレイヤー）は、どちらも TAS と自分の走り 2,700 本で、前のフィールドのフレーム（`C + 1` から `C + 34` まで、プレイヤーのルーチンで読んだ入力が空中かジャンプのもの）を今も数えます:

| 大きさ | そのフレーム | そのうち `hstep` に従わないもの | そのうち向きが変わるもの |
|---|---|---|---|
| 大きい | 91,834 | 7,462 | 0 |
| 小さい | 91,823 | 7,478 | 0 |

`room-face-check`（プログラムとしての歩き）: `apartF` と `checkF` は true。

## 残ること

`facing` には何も残りません。`wall_turn` は `Follow` で場合を分けずに、すべてのフレームで `RoomCore.facing` を使います。ラウンド 28 の ROM の確認 `WallFacts.face1`、`face2`、`face3` はなくなりました（`faceCheck` と `face_of_check` は RoomJoin に残りますが、ルートは使いません）。

**ファイル。** 新しい `Theorems/RoomFace.lean`（`FaceIn`、`piecesF`、`phF`、`finF`、`apartF`、`checkF`、`piecesF_class`、`piecesF_cover`、`keepF_step`、`after_F`、`face_frame`）。`Theorems/RoomJoin.lean`: `InRoom.face`（新しい）、`faceIn_of_read`、`facing_of`、`RoomCore.facing`（新しい。`toCore` で `facing_of` から）。`RoomFields.facing` を消した。`Theorems/Route.lean`: `Run.roomFace`。`Run.inRoom` は 2 つの確認を受けとる。非公開の `Proof/RoomWall.lean`: `room_face`、`room_face_apart`。プログラム: `room-face-check`。
