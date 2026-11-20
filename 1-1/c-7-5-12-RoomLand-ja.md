[← Back](README-ja.md) | [English](c-7-5-12-RoomLand.md) | [Japanese](c-7-5-12-RoomLand-ja.md)

# 最初の落下の着地のフレーム

部屋に入ったあとの最初の落下で、フレーム `C + 34` に床に立つことを証明します。使う条件は、そのフレームの移動の終わり（`PlayerSubs`、以下 Q）での 2 つのバイトだけです。フィールド `land_at` はなくなり、かわりにこの 2 つの条件のフィールド `landQ` を置きました。

## 主張

```
LandB(q)   :=  disable(q) = 0  ∧  yhigh(q) = 1
LandQ(q)   :=  LandB(q)  ∧  page(q) = 0  ∧  x(q) < 248
landQ      :  NoWall  →  フレーム C + 34 のプレイヤーのルーチンより後の PlayerSubs の各命令 j で  LandB(trace j)   （新しいフィールド）
landQ_pos  :  そのような j で  page(trace j) = 0  ∧  x(trace j) < 248                                          （定理）
land_at_of :  NoWall  →  st(vs(C + 34)) = 0                                                                  （定理。もとのフィールド land_at）
```

`disable` は当たり判定を止める旗、`yhigh` は縦のページです。どちらも、プレイヤーの当たり判定のルーチンが最初に見るバイトです。

## 証明の流れ

1. `landCheck`（ROM の確認）：最初の落下の 33 フレーム目のどの状態からも、`vstepR` は A を押しても押さなくても高さ 180 ピクセルで、縦の速さは負でありません。
2. `RoomFall.land_frame`：空中のフレームは Q に来て、そこでの縦のバイトは `vstepR` の値です。Q のあと同じフレームの中で状態が 0 になる命令があれば、フレームの終わりの縦のバイトは着地の値です。`after_QH` は `after_QC` に履歴を足したものです。着地しない場合には、Q からフレームの各命令で、着地の 4 バイトが Q の値のままです。`landed_of_write` はこれを使います。
3. `RoomLand.stand_at`：Q で `LandQ` が成り立ち、高さが 180 で、速さが負でなければ、横の判定の入口（`DoPlayerSideCheck`）で状態は 0、高さは 176 です。Q で切れ目をとり、命令の歩きで確かめます。
   - 切れ目は Q から 12 バイトを写します。当たり判定を止める旗、縦のページ、ルーチン、座標 3 つ、画面の 5 バイト、ジャンプ台です。さらに、3 つの足し算の位置について、頭と両足のマスの値を地図からとります。大きさとしゃがみの旗は写しません。歩きが両方の分岐をたどります。
   - ルーチン、画面、ジャンプ台の値は、部屋の歩きの表から出ます（`controls_at_subs`）。マスの値は、Q での `Solid` から出ます。
   - ROM の確認は 2 つです。1 つ目は、参照の機械の x を 0〜247 の 248 通りに変えた歩き（`family`）です。参照の機械は、地図の部屋で入力なしの最初の `PlayerSubs` で、高さを 180 にしたものです。2 つ目は、マスがバッファの中にありコインでないこと（`cellsOK`）です。
4. `RoomRun.landQ_pos`：Q のページは 0 で、x は 248 より小さい。フレームの終わりの位置は、最初の位置の右端から 34 フレームの最高速の距離までにあります（`P_upto`、`move_top`）。Q の位置はフレームの終わりと同じか、1 ピクセル違うだけです（`CleanR.after`、`FrameModel.Collide`）。ROM の確認 `landP` で、この範囲は 248 ピクセルより左です。
5. `Route.Run.roomLand` は 2 と 3 をつなぎます。これが `InRoom.land` です。`RoomRun.land_at_of` は、1、`landQ`、`landQ_pos`、`InRoom.land` から出ます。`floor_at_of` は今これを使います。

## 測ったこと

- TAS と自分の乱数の入力 300 本：着地のフレームの Q はいつも、旗 0、縦のページ 1、ページ 0、高さ 180、速さ 4 でした。x は 13〜46 でした。フレームの終わりでは、全部が高さ 176 に立っていました。
- TAS の Q で、x を 256 通り、大きさとしゃがみを 2 通りずつ変えて実機で走らせました。全部が高さ 176 に立ちました。
- 切れ目の歩きは、x が 248〜255 のときは通りません。この範囲は確認に入れていません。

## 残るもの

`landQ` の 2 つは仮定です。Q で、当たり判定を止める旗が 0 で、縦のページが 1 であることです。どちらも、部屋の最初の落下の各フレームで保たれることを示す必要があります。

**ファイル.** `Theorems/RoomLand.lean`（`keys`、`cells`、`cut`、`check`、`family`、`cellsOK`、`at_cut`、`cut_eq`、`check_of_family`、`cells_of_family`、`land`、`controlCheck`、`controls_at_subs`、`refQ`、`refCheck`、`Checks`、`stand_at`）、`Theorems/RoomFall.lean`（`after_QH`、`landed_of_write`、`at_QG`、`land_frame`）、`Theorems/RoomJoin.lean`（`LandQ`、`LandB`、`landY`、`disableI`、`landCheck`、`Checks.landP`、`InRoom.land`、`RoomRun.landQ`、`RoomRun.P_upto`、`RoomRun.landQ_pos`、`RoomRun.land_at_of`）、`Theorems/Route.lean`（`Run.roomLand`、`Run.inRoom`）。非公開の `Proof/RoomLand.lean`（`room_land`）、`Proof/RoomJoin.lean`（`room_checks.land`）。
