[← Back](README-ja.md) | [English](c-7-5-17-RoomCorner.md) | [Japanese](c-7-5-17-RoomCorner-ja.md)

# 床の上でのブロックの左側

[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `low_at` は次のことを言っていました。`C + 37` から `C + 43` までで、足がブロックの上面かそれより下にあるフレームは `LowAt` です。角からあまり先に出ておらず、止まっているか、角より左か、左に動いています。このページは、壁に触らないとき、床の上で終わるすべてのフレームについてこれを証明します。当たり判定のルーチンがブロックの左側を見つけ、押し戻します。フィールドは、壁に触らないときに、角かその先で床のほかで終わるフレームだけを、`LowAt` の 1 つ目の部分（角からあまり先に出ていない）だけ求めるようになりました。`LowAt` 全体は、大きなプレイヤーの測ったフレームで偽です（下）。

## 主張

`P(n)`、`hs(n)`、`vs(n)` は、フレーム `n` の終わりの位置（1/256 ピクセル単位）、横の状態、縦の状態です。`c_P` は角（右側の判定がブロックの左の列に入る位置、51 ピクセル）、`S_low` は低いフレームの余裕（415/256 ピクセル）、`y_c` は角の高さ（136 ピクセル）、`176` は床の高さです。`OnFloor(s)` は状態 0 で高さ 176 です。`NoWall` は、`C + 37` より前のフレームがどれも `hstep` に従うことです。

```
LowAt(n)  :=  P(n) ≤ c_P + S_low  ∧  (Stop(n) ∨ P(n) < c_P ∨ v(n) < 0)

low_at（フィールド、狭めた）:
  NoWall,  C + 37 ≤ n ≤ C + 43,  n ≤ t₀,  y_c ≤ y(vs(n)),  ¬OnFloor(vs(n)),  c_P ≤ P(n)   →   P(n) ≤ c_P + S_low

low_floor_of（証明。RoomCore.low_floor）:
  NoWall,  C + 37 ≤ n + 1 ≤ C + 43,  n < t₀,  (∀ j, C + 34 ≤ j ≤ n + 1 → OnFloor(vs(j))),  LowAt(n)   →   LowAt(n + 1)

low_floor_at（証明）:
  NoWall,  C + 36 ≤ n ≤ C + 43,  n ≤ t₀,  (∀ j, C + 34 ≤ j ≤ n → OnFloor(vs(j)))   →   LowAt(n)
```

フレームの移動の終わり `Q`（その `PlayerSubs`）で、`x`、`pg`、`v` を横の座標、ページ、速さのバイトとし、`F` をフレームの終わりとします。

```
CornerEnd(Q, F)  :=  y(F) < y_c  ∨  (pg(F) = 0  ∧  (v < 128  →  v(F) = 0 ∧ x(F) = x − 1)  ∧  (v ≥ 128  →  v(F) = v ∧ x(F) = x))

InRoom.corner（本物の機械の上で証明: Route.Run.roomCorner）:
  C ≤ n,  n + 1 < E,  フレーム n + 1 は入力にジャンプがなく、縦のページ 1 で立って始まる   →
    ∃ Q,  Q はフレームのただ 1 つの PlayerSubs  ∧
      (高さ 176 で縦の速さが負でなく始まり、pg(Q) = 0、51 ≤ x(Q) ≤ 55   →   CornerEnd(Q, F))
```

つまりブロックの左側では、0〜127 の速さは 0 になり、1 ピクセル押し戻されます。負の速さはそのままで、座標もそのままです。

## 歩き（`Theorems/RoomCorner.lean`）

1. 1 つ目の歩き（`check1C`）は `Q` から始まります。`RoomLand.keys` のバイト、プレイヤーの状態、縦の速さの符号のビット、それに 3 つの加算のずれの頭・足・横のセルを参照の地図から知っています（`RoomWall.cellsW`）。横の速さは知りません。`x` が 51〜55 で、2 種類の `Q` について歩きます。高さ 176 で状態 0、上に動いていないもの。状態 1 で上に動いていて、高さが 152〜176 のもの（130 の歩き）。止まるのは、当たり判定のルーチンを呼んだ次の命令（`retBG`）か、`ImpedePlayerMove` です。`retBG` では高さが `y_c` より上であることを求めます。`ImpedePlayerMove` では、横のバイト 1（ブロックは右）、横の判定の 2 つの戻り先がスタックにあること、`Q` の座標とページ、速さが書かれていないことを求めます。
2. 2 つ目の歩き（`check2C`）は `ImpedePlayerMove` から、すべての座標とすべての速さのバイト（1280 の歩き）で始まり、`retBG` に戻ります。そこで `CornerEnd` の 2 つ目の部分を求めます。
3. `corner_at` は 2 つをつなぎます。`corner_frame` は、`retBG` からの `RoomWall` の部屋のフレーム全体の歩きを足します（`RoomWall.after_G`: どのステップも速さ、座標、ページ、状態、高さを書かないか、フレームはプレイヤーのルーチンから出ます）。

確認はネイティブで約 1.6 秒です（`room-corner-family 152`）。非公開の証明は `Proof/RoomCorner.lean` の `room_corner` です。

## `low_floor_of` の証明の流れ

1. フレームは床の上で、縦のページ 1、縦の速さ 0 で始まります（`floor_run`）。入力にジャンプはありません（跳ぶフレームは空中で終わる: `vjump_of`、`offCheck`、`arc_facts`）。なので `InRoom.corner` が、ただ 1 つの移動の終わり `Q` を与えます。
2. フレームがモデルに従うなら（`clean`: `CleanW`）、`Q` のあとに横のバイトを書くものはないので `P(n + 1) = P(Q)` です。`Follow(n)` から `P(n + 1) = P(n) + 16·v(n + 1)` です。`P(n + 1) < c_P` なら `LowAt(n + 1)` です。そうでなければ `P(n + 1) ≤ P(n) + 16·v_top ≤ c_P + S_low + 640 < c_P + 1280` なので、`pg(Q) = 0` で、`x(Q)` は 51〜55 です（`corner_window`）。床の上で終わるので、`CornerEnd` から、押し戻された（座標はそのままなので起きない）か、左に動いています。`v(n + 1) < 0` で `P(n + 1) < P(n) ≤ c_P + S_low` です。
3. そうでなければフレームは `Stop(n + 1)` です（`clean`）。`FrameModel.frame_readQ`（移動の終わりの命令も与える `frame_readR`）で、フレームは `TopSpeed.Frame` になり、`P₂ = P(n) + 16·v₂` はフレームの `PlayerSubs` での位置で、それは `Q` です（ただ 1 つ）。`P(Q) < c_P` なら、`Collide` から `P(n + 1) ≤ P(Q) + 256 < c_P + S_low` です。`P(Q) ≥ c_P` なら、`CornerEnd` から、押し戻されて `P(n + 1) = P(n) + 16·v₂ − 256` か、左に動いて `P(n + 1) = P(Q) < P(n)` です。押し戻されたとき: `P(n) < c_P` なら、`v₂ ≤ v_top` から `P(n + 1) < c_P + 16·v_top − 256 ≤ c_P + S_low` です。`P(n) ≥ c_P` なら、`LowAt(n)` から止まっていたか左に動いていて、1 フレームで速さは 17 未満しか増えないので（`friction_gain`、`CornerFacts.small`）、`P(n + 1) ≤ P(n)` です。
4. `low_floors` は角より左の `C + 36`（`corner_late`）から始め、1 フレームずつ進みます。`floor_low` は跳ぶまでの床のフレームにこれを使い、`low_by` は落下の終わりから床にいるフレームに使います。ジャンプのフレームでは `low_by` はまだフィールドを使います（`arc_facts`: 床の外）。要るのは `P(n) ≤ c_P + S_low` だけで、角より左ではそれは成り立ちます。

`low_floor_of` が使うのは、フィールド `stand_wall`、`stand_fast`、`stand_P`（`floor_run` と `land_end_of` を通して）、`clean`、`farNear`、`read_hs`、`read_P`、`read_vs`、`read_in`、`read_PE`、`read_stop`、それに `InRoom` のフィールド `corner`、`floor`、`jump`、`land`、`wall`、`high`、`air`、`pair`、`keep`、`keepH`、`cut`、`arrive`、`reach`、`time`、`before`、`many`、`le`、`mouthE`、`vstart` です。`low_at`、`RoomCore.low_floor`、`toCore` は使いません（使う定数で確かめた）。`Route.Run.roomCorner` もどれも使いません。

## 測ったこと

`room-corner-real FM2 300 152`: 部屋の中の TAS のフレームと、TAS の部屋での最初の操作から始めた 7 種類の自分のランダム入力 2100 本です。

- `t₀` 以前の `C + 37` から `C + 43` のフレームは 14,707。足が低いものは 14,626 で、床から床が 3,141、跳ぶフレームが 1,078、空中が 10,407。
- 366 は移動の終わりが角かその先です。どれもページ 0、座標 51〜55、縦のページ 1 です。351 は歩きの 2 種類のどちらかで、どれもフレームの終わりで `CornerEnd` です。350 は押し戻され、1 は左に動いています。残りの 15 は、歩きの高さより上の高さ 149 か 151 で上に動いていて、床のほかで終わります。高さ 136 からにしたとき（境 152 を入れる前の `room-corner-real`）は、366 のどれも `CornerEnd` でした。
- これらのフレームのどれでも `P(Q) = P(始め) + 16·v(Q)` で、どのフレームも `PlayerSubs` に 1 回だけ来ます。
- 68 のフレームが角かその先で終わります。14 は床の上で終わり（ここで証明）、54 は床のほかで終わります（フィールドに残る）。14,626 のどれでも `LowAt` が成り立ち、角から `S_low` より先のものはありません。

**大きなプレイヤー（`room-corner-real FM2 300 152 1`: 同じ走りで、最初の操作で大きさのバイトを大きいにしたもの）。** `LowAt` は 8 のフレームで偽です（種類 2 の 8 本の走りのフレーム 42 と 43）。高さ 151 で角で上に動き、右に動いていて（速さ 5〜21）、そのフレームでは押し戻されません。横の判定は通り、頭のコインのコードは通りません。どれも角から 224/256 ピクセル以内で、14,626 のどのフレームも角から `S_low` より先ではありません。なのでフィールドは `P(n) ≤ c_P + S_low` だけを求めます。大きさが分からないと、1 つ目の歩きは高さ 136〜151 で失敗します（`room-corner-family 136`: 210 のうち 80 の歩き）。これらの状態のセルの 1 つは参照の地図でコインで、歩きはたどれない命令に来ます。`Approach.low`（フィールド `way` の中）は、最後に跳んだジャンプの低いフレームで `LowAt` を求めます。大きなプレイヤーでは同じように偽かもしれません。測っていません。

## 残っていること

- 角かその先で床のほかで終わるフレーム（跳ぶフレーム、ジャンプのフレーム）のフィールド `low_at`。これらのフレームの歩きには、移動の終わりでの縦のページが要ります。上に動くフレームのあとではそれを追っていません（`InRoom.high` は上に動かないときだけ終わりでの縦のページを与えます）。跳ぶフレームには、まだ移動の終わりまでの歩きがありません。
- 1 つ目の歩きが通るのは高さ 152 からだけです。それより上では、大きさが分からないとセルの 1 つがコインで、歩きは失敗します。測ったフレームでは、大きなプレイヤーはそこで押し戻されません（上）。

**ファイル。** `Theorems/RoomCorner.lean`（`cutC`、`check1C`、`check2C`、`Checks`、`corner_at`、`corner_frame`）、`Theorems/RoomJoin.lean`（`cornerX`、`xsC`、`CornerEnd`、`FrameModel.frame_readQ`、`CornerFacts`、`Checks.corner`、`InRoom.corner`、`low_floor_of`、`RoomCore.low_floor`、`low_floors`、`low_floor_at`。`RoomFields.low_at` を狭めた）、`Theorems/Route.lean`（`Run.roomCorner`。`Run.inRoom` は `RoomCorner` の確認をとる）。非公開の `Proof/RoomCorner.lean`（`room_corner`）、`Proof/RoomJoin.lean`（`room_corner_facts`）。プログラム `room-corner-family`、`room-corner-real`。

**再現。**
```
.lake/build/bin/smbrta room-corner-family 152             # 歩き（約 1.6 秒）
.lake/build/bin/smbrta room-corner-real FM2 300 152       # 本物の走りの C + 37 .. C + 43 のフレーム（約 40 秒）
```
