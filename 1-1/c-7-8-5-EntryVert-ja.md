[← Back](README-ja.md) | [English](c-7-8-5-EntryVert.md) | [Japanese](c-7-8-5-EntryVert-ja.md)

# 入るフレーム: 入る 1 つ前のフレームは床の近く

ラウンド 35 まで、[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `offNear` は次を言っていました。入る `E` の 1 つ前のフレームは床の近くで終わる。ラウンド 36 でこれを証明し、このフィールドはなくなりました。新しいフィールドはありません。

`near(s)`（`OffDrop.nearB`）は次のことです。床の高さに立っている。または空中にいて、A ありかなしの `vstepR` の 1 フレームで、落ちながら床の高さに届く。[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md) はこれを 3 か所で使い、かたまりの右端を越えたあとのフレームの歩きを終わらせます。

## 主張

`vE(n)` は部屋のフレーム `n` の終わりの縦の状態です。`s` は `vE(E − 1)`、入るフレーム `E` が始まるときの状態です。`t` はフレーム `E` の終わりの縦の状態です。`a` はフレーム `E` のプレイヤーのルーチンでのジョイパッドのビットのビット 7（A）です。`y_floor` は床の高さ 176 px、`y_e` は基準の入りの高さです。

```
RoomRun.offNear_of :  C < E  →  near(vE(E − 1))

InRoom.airL   :  C < E  ∧  st(s) ≠ 0  →  falling(vstepR(s, a))  ∧  (t = vstepR(s, a)  ∨  t = land(vstepR(s, a)))
InRoom.standL :  C < E  ∧  st(s) = 0  ∧  A の新しい押しなし  →  StandNext(s, t)
InRoom.jumpL  :  C < E  ∧  st(s) = 0  ∧  A の新しい押し  →  False
InRoom.yL     :  C < E  →  y(t) = y_e
Checks.entryY :  y_e = y_floor
```

`airL` と `jumpL` は、プレイヤーのルーチンの機械が状態 `AtV` にあることも受け取ります。`airL` は `InRoom.air` と同じく、ジャンプの止めの値と前のフレームの A も受け取ります。フレーム `E` では `InRoom.cut` と `InRoom.pair` がそれらを与えます。`standL` は、プレイヤーのルーチンと、そこでモデルが読む入力にジャンプがないことを受け取ります。

`InRoom` の 4 つの事実は `Route.lean` で本物の機械の上で証明します（`Run.roomAirL`、`Run.roomStandL`、`Run.roomJumpL`、`Run.roomLast`）。`entryY` は ROM のチェックです（非公開の `Proof/RoomJoin.lean` で `native_decide`）。

**`offNear_of`。** `yL` と `entryY` から、フレーム `E` は `y_floor` で終わります。

* `st(s) ≠ 0`: `airL` から `t = vstepR(s, a)` か `t = land(vstepR(s, a))` で、`vstepR(s, a)` は落ちています。着地は高さの上の 4 ビットを保つので、`y_floor ≤ y(vstepR(s, a))` です。だから `near(s)` です。
* `st(s) = 0`: フレーム `E` は飛び上がりません（`jumpL`）。新しい押しがなければ `StandNext(s, t)` です（`standL`）。つまり `y(t) = y(s)` か `y(t) = y(s) &&& 0xF0` です。立ちはちょうどの段にある（`stand_ok`）ので、`y(s) = y(t) = y_floor` です。だから `near(s)` です。

`off_gap_of` は `C < E` を要ります。その証明にはこれがあります（`C ≤ T < t0 ≤ E`）。

## しくみ

**部屋のフレームの歩き。** 3 つの歩きが部屋のフレームを終わりまで追います。

* 歩き B（`RoomVert`）: スクロール処理 `Q` から、空中で上がっているとき。
* 歩き C（`RoomFall`）: `Q` から、落ちているとき。
* 歩き S（`RoomStand`）: プレイヤーのルーチン `R` から、A の新しい押しなしで立っているとき。

歩きが許さないところで縦のバイトを書くかもしれない一歩をした状態には、しるしをつけます。ラウンド 35 まで、フレームの終わりの条件は、しるしのついた状態にルーチンのバイトがわかっていて部屋のものでないことだけを求めていました。入るフレームは横の土管のルーチンで終わるので、しるしのついた状態がそれを終わらせることができました。だから歩きはフレーム `E` について何も言わず、`InRoom` の事実は `n + 1 < E` でだけ成り立っていました。

ラウンド 36 から、フレームの終わりの条件はもっと求めます（`RoomVert.outE`、`RoomVert.notEng`）。

* しるしのついた状態は、ルーチンのバイトがわかっていて、部屋のものでも横の土管のものでもない状態で終わる。
* 歩き B では、上がりながら `Q` に来て、そのあと縦のバイトを書いていない状態は、ルーチンのバイトが横の土管のものでないと知っている。

3 つの歩きは、ほかに何も変えずにこの条件で通ります。探索は同じで、フレームの終わりで断られる状態はありません。歩きからの証明（`RoomVert.after_QE`、`RoomFall.after_QHE`、`RoomStand.after_RSE`）は、部屋のルーチンか横の土管のルーチンで終わるフレームを受け取ります。前の定理（`after_Q`、`after_QH`、`after_RS`）は部屋のルーチンの場合のこれで、主張は変わっていません。

`RoomAbsKeep` の歩き（移動の終わりからの覚えている速さ）は歩き B の前の終わりの条件を使っていました。そのビットのある状態は、入るフレームでは横の土管のルーチンで終わります。そこで前の条件をそれ自身の条件 `finX` として持たせました。

**入るフレーム**（`EntryVert`）:

* `air_frame`: 空中のフレームは `vstepR` の縦のバイトで `Q` に来ます（`RoomFall.at_Q`）。そこで上がっていれば、フレームは横の土管のルーチンで終わりません（歩き B）。落ちていれば、フレームの終わりの縦のバイトは `Q` のものかその着地です（歩き C）。
* `stand_frame`: `RoomStand.stand_frame` と同じで、横の土管のルーチンで終わるフレームに歩き S を使います。
* `jump_frame`: 飛び上がりは `Q` で上がっている（`VertJump.vert_jump`）ので、フレームは横の土管のルーチンで終わりません（歩き B）。

**本物の機械の上で**（`Route.lean`）。入るフレームは走りのフレーム `k` で、`b₁ ≤ k < a₂` です（`Run.roomEnter`）。それは横の土管のルーチンで終わる（`EntryRoutine.rt_of_rows`）ので `a₂ = k + 1` で、そこの高さはパート d の `Run.y₂` が与えます（`Run.roomLast`）。このフレームは部屋のどのフレームとも同じく部屋の条件で始まり、各命令で `SiteOK` を満たします。

## フィールド

なくなったもの:

* `RoomRun.offNear`

変えなかったもの: `RoomRun.offTop` と `RoomRun.offSlow`（どちらも `t0` から 12 フレームより早く入る走りにだけ求める狭めは残さなかった。合わせると `off_gap_of` の結論を言うことになるから: [かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md)、ラウンド 36）。

足したもの: フィールドはありません。`InRoom` の新しい事実（証明済み）: `airL`、`standL`、`jumpL`、`yL`。ROM の新しいチェック: `Checks.entryY`。歩き B、C、S のチェック（`RoomVert.checkB`、`RoomFall.checkC`、`RoomStand.checkS`）は強いフレームの終わりの条件を持ちます。`RoomAbsKeep.checkX` は `finX` を持ちます。

## 測ったこと

`room-entry-vert FM2 300`:

| 歩き | 探索の歩数 | フレームの終わりの状態 | ラウンド 36 の条件が断るもの | チェック（ネイティブ） |
|---|---|---|---|---|
| B（`checkB`） | 442,838 | 50 | 0 | true、6.5 秒 |
| C（`checkC`） | 615,540 | 60 | 0 | true、11.7 秒 |
| S（`checkS`） | 464,647 | 52 | 0 | true、8.2 秒 |
| `RoomAbsKeep.checkX`（`finX`） | | | | true、5.9 秒 |

基準の入りは床の高さ 176 px で終わります（`entryY`）。

本物の入るフレームで、`airL`、`standL`、`jumpL`、`yL`、`near` が言うこと:

| 走り | 入るフレーム | フレームの始まりの状態 | 反するもの |
|---|---|---|---|
| ムービー（ムービーのフレーム 763） | 1 | 1（ジャンプ中） | 0 |
| 部屋の最初の操作からの自分の入力（300） | 48 | 0、1、2 | 0 |

`room-off-back FM2 400`（ラウンド 35）: 入りは 225、そのうち 1 つ前のフレームが床の近くにないものは 0。

## 残っていること（証明していない）

* `offTop` と `offSlow`（[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md)）。そのページに、それぞれの証明に要るものと、`offSlow` のフレームの測定（`room-off-slow`）があります。

## ほかのパートから使うもの

* パート d: `Run.y₂`（歩き `EntryHeight` と `EntryHeightBig`、`SizeKeep` の `Run.size₂`）、`EntryRoutine.rt_of_rows`（歩き `SideEntryEnd`、`SideEntryRest`）。
* パート c: `Run.roomEnter`、`Run.roomIdx`、`RoomMap.cond_of_rows`、`RoomPair.quad_run`、`Run.roomSites`、`ChangesBase.roomStay`。
* 循環はありません。これらのどれも `offNear`、`RoomRun.off_gap_of`、新しい `InRoom` の事実を使いません。

**ファイル。** `Theorems/EntryVert.lean`（`air_frame`、`stand_frame`、`jump_frame`、`air_room`、`stand_room`、`jump_room`）。`Theorems/RoomVert.lean`（`outE`、`notEng`、`outE_ne`、`notEng_ne`、`not_outE`、`finB`、`finB_one`、`finB_spent`、`after_QE`）。`Theorems/RoomFall.lean`（`finC`、`after_QHE`）。`Theorems/RoomStand.lean`（`finS`、`after_RSE`）。`Theorems/RoomAbsKeep.lean`（`finX`）。`Theorems/RoomJoin.lean`（`InRoom.airL`、`standL`、`jumpL`、`yL`、`Checks.entryY`、`row_hi`、`RoomRun.offNear_of`）。`Theorems/Route.lean`（`Run.roomLast`、`Run.roomAirL`、`Run.roomStandL`、`Run.roomJumpL`、`Run.inRoom`）。`Main.lean`: `room-entry-vert`。非公開の `Proof/RoomJoin.lean` に `entryY` を足します。公開のファイルにゲームのデータはありません。

**再現。**
```
.lake/build/bin/smbrta room-entry-vert FM2 300    # 新しい条件での歩き、entryY、本物の入るフレーム（約 2 分）
.lake/build/bin/smbrta room-off-back FM2 400      # かたまりの右端を越えて入る走り（約 1 分）
```
