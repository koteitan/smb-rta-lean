[← Back](README-ja.md) | [English](c-7-5-18-RoomHigh.md) | [Japanese](c-7-5-18-RoomHigh-ja.md)

# ジャンプを通した縦のページと、ジャンプ中のブロックの左側

[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `low_at` は、壁に触らないとき、`C + 37` から `C + 43` までで足が低く、角かその先で床のほかで終わるフレームをすべて求めていました。そのフレームは角から `S_low` より先に出ません。これらのフレームは、床から跳ぶフレームと、そのジャンプの最初のフレームです。ブロックの左側の歩き（[床の上でのブロックの左側](c-7-5-17-RoomCorner-ja.md)）は、移動の終わりで縦のページ（`Player_Y_HighPos`）を必要とします。上昇するフレームのあとでは、縦のページを追っていませんでした。このページは、跳ぶフレームと上昇するフレームを通して縦のページを追い、高さ 152（`cornerY + 16`）かそれより下で終わるジャンプのフレームを証明します。フィールドは、152 より上（136 から 151 ピクセル）で終わるフレームだけを求めるようになりました。

**偽（測定、大きなプレイヤー）。** `Approach.low`（フィールド `way` の中）は、大きなプレイヤーの測った 2 つの走りで偽です（下）。狭めていません。それを使う `landed_short` が、そこで `LowAt` 全体を必要とするからです。

## 主張

`P(n)`、`vs(n)` は、フレーム `n` の終わりの位置（1/256 ピクセル単位）と縦の状態です。`y`、`st` は高さとプレイヤーの状態です。`c_P` は角（51 ピクセル）、`S_low = 415/256` ピクセル、`y_c = 136` は角の高さ、`176` は床の高さです。`OnFloor(s)` は状態 0 で高さ 176 です。`NoWall` は、`C + 37` より前のフレームがどれも `hstep` に従うことです。`OnArc(T, j)` は、フレーム `j` がフレーム `T + 1` で跳ぶジャンプの上にあることです（縦の状態が `Jump.arcStart` の跳びから `Jump.arcSucc` で来る状態）。`Q` はフレームの移動の終わり（`PlayerSubs`）、`F` はフレームの終わり、`hp` は縦のページです。

```
low_at（フィールド、狭めた）:
  NoWall,  C + 37 ≤ n ≤ C + 43,  n ≤ t₀,  y_c ≤ y(vs(n)),  ¬OnFloor(vs(n)),  c_P ≤ P(n),  y(vs(n)) < y_c + 16   →   P(n) ≤ c_P + S_low
  （前は最後の前提なし）

arc_down（証明。確認 arcDown）:
  床からのジャンプの最後の低いフレームまでで,  T < j ≤ n   →   y(vs(n)) ≤ y(vs(j))

low_jump_of（証明。RoomCore.low_jump）:
  NoWall,  C + 34 ≤ T < n ≤ C + 43,  n ≤ t₀,  (∀ j, C + 34 ≤ j ≤ T → OnFloor(vs(j))),
  (∀ j, T < j ≤ n → OnArc(T, j)),  (∀ j, T < j ≤ n → y_c + 16 ≤ y(vs(j))),  LowAt(T)   →   LowAt(n)
```

`InRoom` の新しい 2 つのフィールドは、本物の機械の上で証明しました（`Route.Run.roomHighJ`、`Route.Run.roomHighA`）。

```
InRoom.highJ（跳ぶフレーム）:
  C ≤ n,  n + 1 < E,  フレーム n + 1 は高さ 176、hp = 1 で始まり、入力にジャンプがある   →
    hp(F) = 1  ∧  ∃ Q, Q はそのフレームのただ 1 つの PlayerSubs  ∧  (pg(Q) = 0,  51 ≤ x(Q) ≤ 55   →   CornerEnd(Q, F))

InRoom.highA（空中のフレーム）:
  C ≤ n,  n + 1 < E,  フレーム n + 1 は空中で hp = 1、ジャンプの最初の 8 フレームの状態 s（VertAir.arcSet）で始まり、
  vstep(s, A) もそのような状態で上昇中   →
    hp(F) = 1  ∧  ∃ Q, Q はそのフレームのただ 1 つの PlayerSubs  ∧  (pg(Q) = 0,  51 ≤ x(Q) ≤ 55,  y_c + 16 ≤ y(vstep(s, A))   →   CornerEnd(Q, F))
```

`CornerEnd(Q, F)` は [床の上でのブロックの左側](c-7-5-17-RoomCorner-ja.md) のものです。終わりで角の高さより上か、ページ 0 で、速さ 0 で 1 ピクセル押し戻される（`Q` で速さが 0 から 127）か、`Q` のまま左に動いています。

## 縦のページの追い方

1. 跳ぶフレーム（`RoomHigh.vert_jumpH`）。`VertJump.vert_jump` の 2 つの機械（本物の機械と `vstep` の機械）の歩きが、縦のページも「2 つの機械で同じ」という印で追います。空中のフレームで `OpenVert.vert_airH` がするのと同じです。なので `Q` でのページは、本物の高さに立った状態から A と本物の覚えている速さで移動のルーチンを走らせたあとの `vstep` の機械のページです。`RoomHigh.offCheck`: 高さ 176 からでは、どの覚えている速さでもこのページは 1 で、`Q` での高さは 171 か 172 です。
2. `Q` からフレームの終わりまで（`RoomVert.after_QP`）。スクロールの処理からの `RoomVert` の歩き `walkB` が、縦のバイトといっしょに縦のページも保つようになりました（`vKeepH`）。空中で上昇中に、そのどれかを書くかもしれない歩みは、プレイヤーのルーチンを離れなければなりません。歩きは前と同じく通ります（ネイティブで 5.9 秒）。ページはブロックバッファの外です（`apartH`）。
3. 空中のフレーム（`RoomHigh.air_roomH`）。`Q` でのページは `vstep` の機械のページです（`RoomFall.high_room`）。`RoomHigh.arcCheckH`: ジャンプの最初の 8 フレームの 1533 の状態で、それは 1、状態は 1、高さは 176 以下です。`Q` で上昇中なら、2 がページと縦のバイトを終わりまで保ちます。
4. フレームの間でページは保たれます（`InRoom.keepH`）。なので床からのジャンプでは（床のフレームはページ 1: `floor_run`）、どのフレームもページ 1 で終わります（`high_next`）。

## `low_jump_of` の証明

1. `low_step` は `low_floor_of` の 1 フレームの段を取り出したものです。`LowAt` のフレームのあと、角の高さかそれより下で終わり、`Q` がただ 1 つの `PlayerSubs` で、`Q` がページ 0 で座標が 51 から 55 のとき `CornerEnd` で終わるフレームは `LowAt` です。`low_floor_of` は今これを `InRoom.corner` で使います。
2. 跳ぶフレーム `T + 1`: `T` で床にいてページは 1 です（`floor_run`）。その入力にはジャンプがあります（なければ `stay_of` で床にいますが、`arc_facts` は空中と言います）。`InRoom.highJ` が `Q` と `CornerEnd`、終わりでのページ 1 を与えます。`low_step` で `LowAt(T + 1)` です。
3. 空中のフレーム: `varc_at`（`varc_of` から）が、フレームの始まりと `vstep` のジャンプの状態、上昇中であること、フレームがその `vstep` で終わることを与えます。`InRoom.highA` が `Q` と `CornerEnd`（`vstep` の高さが `y_c + 16` かそれより下のとき）、終わりでのページ 1 を与えます。`low_step` で `LowAt` です。
4. `low_by` では、角かその先のジャンプのフレームを分けます。`y_c + 16` より上で終わればフィールド、そうでなければ跳ぶところから `low_jump` です（`v_chain2`: `T` まで床、そのあとジャンプの上）。`LowAt(T)` は `low_floor_at` から、`C + 37` より前なら `corner_late` からです。そのジャンプの前のフレームもその高さかそれより下で終わります。ジャンプの最初のフレームの 1533 の状態で `vstep` は高さのバイトを下げません（`arcDown`。`RoomJoin` のほかの確認といっしょにネイティブで確かめる）。なのでジャンプに沿って高さは増えません（`arc_down`）。

ブロックの左側の歩きは、上昇中の状態 1 では高さ 152 から下だけで通ります（[床の上でのブロックの左側](c-7-5-17-RoomCorner-ja.md)）。それより上では、大きさがわからないと、ある升にコインがあります。ジャンプの状態で、移動の終わりの高さは、跳んだあと最初の 5 フレーム（`k ≤ 4`）では 152 以上で、`k = 5` からはそれより上のものがあります（`k = 5` で 148、`k = 8` で 136）。

`low_jump_of` は `low_at`、`RoomCore.low_jump`、`toCore` を使いません。`Route.Run.roomHighJ` と `Route.Run.roomHighA` は `low_at` と `low_jump_of` を使いません（使う定数で確かめた）。

## 測ったこと

`room-approach-check FM2 300 BIG`: 部屋での TAS 自身のフレームと、部屋での TAS の最初の操作から自分の乱数入力の 9 種類 2700 の走り（種類 8 と 9: 28 から 47 のフレームで A を 1 回押し、1 から 24 フレーム押し続ける。右へ走るか歩く）。どれもブロックの右端を越える最初のフレーム（`t₀`）か 300 フレームまで。`BIG = 1` は最初の操作で大きさのバイトを大きいにします（作った状態です。測ったどの走りも大きいまま部屋に入りません）。

- 部屋のどのフレームでも、`Q` とフレームの終わりで縦のページは 1 です（小さいとき 768,913 フレーム、大きいとき 764,149 フレーム）。
- 前の `low_at` のフレーム（壁に触らない、`C + 37` から `C + 43`、足が低い、床のほか、角かその先）: 小さいとき 50、大きいとき 103。そのうち 47（小さい）と 48（大きい）を今は `low_jump` が受け持ち、どれでも `LowAt` が成り立ちます。3（小さい）と 55（大きい）がフィールドに残ります。どれも角から `S_low` より先に出ません（一番遠くて小さいとき 96/256 ピクセル、大きいとき 352/256 ピクセル）。
- **`Approach.low` は大きなプレイヤーで偽です。** 壁に触らず、`C + 37` から `t₀` まで `Stop` がなく、`t₀` より前にかたまりに着地する 2 つの走り（種類 9）で、最後に跳んだジャンプの低いフレームが `LowAt` ではありません。フレーム 45（跳んだのは 35）とフレーム 53（跳んだのは 43）で、跳んで 10 フレーム後、高さ 138、状態 1、速さ 23 か 24 で右に動き、角から 336/256 と 48/256 ピクセル先、止まっていません。測ったどの低いフレームでも `P ≤ c_P + S_low` は成り立ちます。小さいプレイヤーでは、どれでも `LowAt` が成り立ちます。`landed_short` はこれらのフレームで `LowAt` 全体を使う（`left_at`）ので、`low` を位置の上限だけに狭めていません。

## 残ること

- 152 より上（136 から 151 ピクセル）で終わるフレームについてのフィールド `low_at`。大きさがわからないとブロックの左側の歩きはそこを通らず、測ったフレームでは大きなプレイヤーはそこで押し戻されません。
- `Approach.low`: 大きなプレイヤーの測った走りで偽です。角での大きなプレイヤーのフレームについて、`landed_short` には別の議論が要ります。
- `stand_wall`: 手をつけていません。

**ファイル。** `Theorems/RoomHigh.lean`（新しい: `vTagsJH`、`goalVJH`、`caseOKJH`、`jumpHOK`、`vert_jumpH`、`jump_frameH`、`jump_roomH`、`air_roomH`、`offCheck`、`arcCheckH`、`Checks`、`off_spec`、`arc_specH`）、`Theorems/RoomVert.lean`（`vKeepH`。`mayWriteV` は `vKeepH` について。`apartH`、`keepVH_step`、`after_QP`）、`Theorems/RoomJoin.lean`（`InRoom.highJ`、`InRoom.highA`、`RoomCore.low_jump`、`low_step`、`varc_at`、`high_next`、`low_jump_of`、`v_chain2`、`arcDown`、`Checks.down`、`arc_down`。`low_by` とフィールド `low_at`）、`Theorems/Route.lean`（`mem_ysUp`、`Run.roomHighJ`、`Run.roomHighA`。`Run.inRoom` は `RoomHigh` の確認を取る）。非公開の `Proof/RoomHigh.lean`（`room_high`）と、`room_checks` の `down`（`Proof/RoomJoin.lean`）。プログラム `room-high-probe`、`room-approach-check`。

**再現。**
```
.lake/build/bin/smbrta room-high-probe                    # RoomHigh の確認と RoomVert.checkB（約 6 秒）
.lake/build/bin/smbrta room-approach-check FM2 300 0      # 小さい。最後を 1 にすると大きい
```
