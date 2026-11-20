[← Back](README-ja.md) | [English](c-7-5-13-LandBytes.md) | [Japanese](c-7-5-13-LandBytes-ja.md)

# 最初の落下での当たり判定を止める旗と縦のページ

最初の落下の着地（1-1-c-7-5-12）は、フレーム `C + 34` の移動の終わり（`PlayerSubs`、以下 Q）で 2 つのバイトを仮定していました。当たり判定を止める旗が 0 で、縦のページが 1 であることです。このページでは両方を証明します。フィールド `landQ` はなくなりました。

## 主張

```
flag(q) = 参照の旗 (= 0)                         部屋のフレームの各 PlayerSubs の q で                 （RoomLand.controls_at_subs）
yhigh(fe C) = 1                                  最初の操作で                                          （StartAt.high）
yhigh(M) = 1  →  yhigh(Q) = yhigh(vRunR(vs M, a))                                                       （RoomFall.high_frame、InRoom.high）
          かつ  vy(vstepR(vs M, a)) ≥ 0  →  yhigh(フレームの終わり) = yhigh(vRunR(vs M, a))
∀ d < 34,  yhigh(fm (C + d)) = 1                                                                        （RoomRun.high_fall）
```

`vRunR(s, a)` は、移動のルーチンのあとの `vstepR` の機械です。`vstep` の参照の機械に縦のバイト `s` を入れ、A を押すか押さないかで走らせたものです（`VertModel.vRun`）。

## 証明の流れ

1. **旗。** 部屋に入るときの切り替えがこの旗を 0 にし、部屋のどの命令も書きません。そこで、部屋の条件が知るバイトにこの旗を入れました（`ScreenPage.roomNames`）。最初の操作での切り替えの段はこの旗を参照の値で知っていて、部屋の歩きもこの値を保ちます（確認 `screen_start` と `map_check` は前と同じく通ります）。歩きは `PlayerSubs` でこの旗を知っているので、`RoomLand.controls_at_subs` がこの値を出します。ルーチン、画面のバイト、ジャンプ台と同じ扱いです（`controlKeys`）。`RoomLand.stand_at` はもうこの旗を仮定しません。
2. **最初の操作での縦のページ。** 切り替えの段は縦のページを知っていて、そこでは 1 です（`RoomStart.vBytes`、`vOK`。確認 `room_start`）。
3. **プレイヤーのルーチンより前**では、フレームのどの命令も縦のページを書きません。縦のページを `RoomVert.vKeepA`（プレイヤーのルーチンまでの歩きが保つバイト）に入れました。そのため、一時停止で終わるフレームも縦のページを保ちます（`InRoom.keepH`）。
4. **移動のルーチン**は、高さの繰り上がりを縦のページに足します。`OpenVert.vert_airH`（オープニングの確認 `open_vert_check`、同じスタック）によると、Q での縦のページは `vRunR` のものです。`RoomFall.high_frame` はこれを部屋のフレームに当てはめます。フレームが Q に来るのは 1 回だけなので（`after_QH`）、プレイヤーのルーチンより後の `PlayerSubs` はどれもその Q です。
5. **Q のあと**、落ちているときは、スクロールの処理からの歩き（`walkC`）が縦のページを保ちます。縦のページを `vRestW`（着地のバイトのほかに歩きが保つバイト）に入れました（`after_QH`）。離れたバイトの確認（`apartC`）に、縦のページがブロックバッファの外にあることを足しました。
6. **確認 `highCheck`**：最初の落下の 34 層のどの状態からも、A を押しても押さなくても、`vstepR` は上がらず、`vRunR` の縦のページは 1 です。
7. `RoomRun.high_fall` は 2〜6 をフレームごとにつなぎます。`RoomRun.land_at_of` は、着地のフレームの Q での縦のページをここから取り、旗は歩きから取ります。

## 測ったこと

- TAS と自分の乱数の入力 300 本：着地のフレームの Q では、いつも旗は 0、縦のページは 1 でした（1-1-c-7-5-12）。

**ファイル.** `Theorems/ScreenPage.lean`（`roomNames`）、`Theorems/RoomLand.lean`（`controlKeys`、`refCheck`、`stand_at`）、`Theorems/RoomStart.lean`（`vBytes`、`vOK`）、`Theorems/RoomVert.lean`（`vKeepA`）、`Theorems/RoomFall.lean`（`vRestW`、`apartC`、`phC`、`after_QH`、`high_frame`、`high_room`）、`Theorems/RoomJoin.lean`（`vRunR`、`StartAt.high`、`highCheck`、`highCheck_spec`、`Checks.high`、`InRoom.keepH`、`InRoom.high`、`RoomRun.high_fall`、`RoomRun.land_at_of`。`LandB` とフィールド `landQ` はなくなった）、`Theorems/Route.lean`（`Run.roomKeepA`、`Run.roomHigh`、`Run.inRoom`）。非公開の `Proof/RoomJoin.lean`（`room_checks.high`）。
