[← Back](README-ja.md) | [English](c-7-5-14-FloorFrames.md) | [Japanese](c-7-5-14-FloorFrames-ja.md)

# 落下のあとの床のフレーム

[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `vfloor` は次のことを言っていました。壁に触らないとき、`C + 34` から `C + 49` までの、入る前に床で始まるフレームは `VFrame` です。地面の入力で床にとどまるか、ジャンプの入力で床からのジャンプの最初の状態（`arcStart`）に跳びます。このページは両方を証明します。フィールド `vfloor` はなくなりました。

## 主張

`yF` は床の高さ（176）、`yhigh` は縦のページ、`vy` は縦の速さです。`fm(n)` はフレーム `n + 1` が始まる機械、`Q` はフレームの移動の終わり（最初の `PlayerSubs`）です。

```
jump(n + 1),  OnFloor(vs n)   →   vs(n + 1) = jumpOffR(yF, ab) = x.s  （ある x ∈ arcStart(yF)）                     (takeoff_of)
ジャンプなし,  OnFloor(vs n),  yhigh(fm n) = 1,  vy(vs n) ≥ 0
          →   OnFloor(vs(n + 1))  ∧  vy(vs(n + 1)) = 0  ∧  yhigh(fm(n + 1)) = 1                                    (stay_of)
∀ e ≤ d,  OnFloor(vs(C + 34 + e))   →   yhigh(fm(C + 34 + d)) = 1  ∧  vy(vs(C + 34 + d)) = 0                         (floor_run)
NoWall,  C + 34 ≤ n < C + 49,  ∀ j ∈ [C + 34, n],  OnFloor(vs j)   →   VFrame(n)                                     (vfloor_of)
```

## 証明のしかた

1. **跳ぶフレーム。** 立って始まり A を新しく押したフレームは、その高さと覚えている速さの `jumpOff` で終わります（`InRoom.jump`、`RoomRun.vjump_of`）。新しい検査 `offCheck` は次を言います。256 通りの覚えている速さのどれでも、`yF` からの跳びは `arcStart` のどれかの最初の状態です。`arcStart` は最高速までの覚えている速さを持ちます。入力はジャンプの入力です。プレイヤーのルーチンで読み、そこでの状態はフレームの始まりのもの、つまり 0 だからです（`gnd_in_of`）。
2. **立ったまま移動の終わりまで。** `VertStand.vert_stand` は移動のルーチンを 2 つの機械で追います。空中の `OpenVert.vert_airH` と同じやり方です。場合は、立っていて A を新しく押していない 6 通りです（`vCasesS`）。どの場合も、高さ、`vy`、その端数、状態、縦のページを書く命令はありません（`goalVS`）。フレームはプレイヤーのルーチンのスタックで `Q` に来ます。なので `Q` でのこの 5 バイトはフレームの始まりのものです（`RoomFloor.floor_frame`）。
3. **`Q` からの足の判定。** 高さ `yF` での `RoomLand.stand_at` は、横の判定のときに状態が 0 だと言います。新しい検査 `room_floor` を使います。x の 248 通りの値それぞれについての `Q` からの歩き、マス、参照の機械です。`Q` でページは 0、x は 248 未満です。これは `q_pos`（`landQ_pos` の一般の形）と、新しい数の事実 `floorP` からです: `P₁ + 640 · 49 + 256 < 256 · 248`。
4. **立つ歩きは横の判定を知る。** プレイヤーのルーチンからの立つ歩き（`walkS`）に、条件を足しました。立ってそこに来て、まだ着地していない状態（`[7, _]`、`[5, h]`）は、横の判定で状態 0 ではありません（`sideOK`）。また縦のページも保ちます（`vRestS`）。なので `RoomStand.after_RS` の「高さは同じで状態は 0 か 2」の場合は、状態 0 で横の判定に来る命令がないことも言います。3 がこの場合を除くので、フレームは着地します。終わりで状態、`vy`、その端数は 0、高さは `yF & F0 = yF` です（新しい事実 `floorRow`）。
5. **フレームの始まりの縦のページと `vy`** は、落下の終わりからの帰納法で示します。着地のフレームは `vy = 0` と縦のページ 1 で終わります（`land_end_of`）。あいだのフレームはページを保ちます（`InRoom.keepH`）。床のフレームの次も床なら、そのフレームはジャンプしません。跳ぶと空中で終わるからです（`arc_facts`）。なので 4 のフレームで、次のフレームはページ 1、`vy = 0` で始まります（`floor_run`）。
6. **`RoomCore` では** フィールド `vfloor` は、落下の終わりからずっと床にいることを前提にしました。3 つの使い場所はこれを持っています。`v_chain` は床の場合にそれを言うようにし、`floor_all` が `early_of` に渡します。
7. **頭。** フィールドは、フレームが頭がブロックに当たる処理に来ないことを前提にしていました（`InRoom.bump`）。新しい証明はこれを使いません。歩きがフレーム全体を追うからです。

## 測ったこと

- `sideOK` と縦のページを足した立つ歩き: 表は 20,937 状態で、失敗はありません。探索の終わりで受け入れないものもありません（`room-stand-check`）。TAS と自分のランダム入力 140 本で、ジャンプなしに立って始まり部屋で終わるフレームは 920 で、すべて `StandNext` でした。
- 3 の検査を高さ 176、x が 248 未満で下書きのファイルで走らせ、すべて真でした（インタプリタで 133 秒）。

**ファイル。** `Theorems/VertStand.lean`（新しい: `vCasesS`、`standKeep`、`goalVS`、`caseOKS`、`standOK`、`vert_stand`）、`Theorems/RoomFloor.lean`（新しい: `floor_frame`）、`Theorems/RoomStand.lean`（`vRestS`、`sideOK`、`phS`、`after_RS`、`stand_frame`）、`Theorems/RoomJoin.lean`（`offCheck`、`offCheck_spec`、`Checks.off`、`Checks.floorP`、`Checks.floorRow`、`InRoom.floor`、`RoomCore.vfloor`、`v_chain`、`RoomRun.gnd_in_of`、`takeoff_of`、`q_pos`、`landQ_pos`、`land_end_of`、`stay_of`、`floor_run`、`vfloor_of`。フィールド `RoomRun.vfloor` はなくなった）、`Theorems/Route.lean`（`Run.roomFloor`、`Run.inRoom`）。私的な `Proof/RoomJoin.lean`（`room_checks.off`、`floorP`、`floorRow`）、`Proof/RoomLand.lean`（`room_floor`）、`Proof/RoomStand.lean`（`stand_vert_check`）。
