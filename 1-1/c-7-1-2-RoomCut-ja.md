[← Back](README-ja.md) | [English](c-7-1-2-RoomCut.md) | [Japanese](c-7-1-2-RoomCut-ja.md)

# 部屋のフレーム: プレイヤーのルーチンでの状態

**主張.** ボーナス部屋の入る前の各フレームで、プレイヤーのルーチンでの機械は `VertAir.AtV` の状態です。ROM のプログラム、待っている NMI なし、NMI はオフ、プレイヤーのルーチンのスタックポインタ、操作のルーチンのバイト、エリアの種類は 1、2、3 のどれか、プレイヤーの状態は 0、1、2 のどれか、ジャンプ台と泳ぎのフラグと大きさの変化は 0 です。ゲームが止まっていない状態で終わるフレームはプレイヤーのルーチンに来ます。`arr n` は最初に来たところです。

これらは [部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `clean` の一部でした（項目 1-1-c-7-1）。`AtCtrl` と `AtFrame` のうち、フレームがモデルに従うかを決める値のほかの全部です。フィールド `arr`（来た命令の番号、自由なデータ）は今は定義です（`CtrlKeep.arrAt`）。プレイヤーのルーチンでの速さの範囲（`AtFrame.speed`）は、前のフレームから出ます。

`RoomRun` で変わったこと:

* `clean` は今は `CleanW` か `Stop ∧ ReadW` を求めます。`CleanW`: プレイヤーのルーチンで覚えている速さは `|v|`、押している側は塞がれていない、スクロールの処理から後は横のバイトに何も書かない。`ReadW`: プレイヤーのルーチンで当たりのビットは `TopSpeed.collBits` の値、スクロールの処理から後は `Collide`。
* `unpaused`（新しい、1 つの機械）: `t₀` までの各フレームは、ゲームが止まっていない状態で終わる。これはまたなくなりました。部屋のフレームはいまは止まっていない状態で終わるフレームです（[部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md)）。
* `arr` はなくなりました（定義）。

`R` はプレイヤーのルーチン、`tr(j)` は `M` からフレームの `j` 命令目の機械、`end` はフレームの終わりの機械です。`st` はプレイヤーの状態、`size` は大きさの変化、`rt` はルーチンのバイト、`pz` は一時停止のバイト、`S_R` はプレイヤーのルーチンのスタックポインタです。

```
CutAt(m)     :  歩きの ROM の prg と mask,  待っている NMI なし,  NMI オフ,  s(m) = S_R,  rt(m) = rt_ctl,
                area(m) ∈ {1, 2, 3},  spring(m) = 0,  swim(m) = 0
cut_R        :  RoomCond(M),  各命令が SiteOK,  pc(tr(j)) = R,  frame(tr(j)) = frame(M)  →  CutAt(tr(j))
arrive_R     :  RoomCond(M),  各命令が SiteOK,  pz(end) & 1 = 0
                →  ∃ j ≤ fuelPerFrame,  pc(tr(j)) = R  ∧  frame(tr(j)) = frame(M)  ∧  ∀ j' < j,  pc(tr(j')) ≠ R
Quad(m)      :  st(m) ∈ {0, 1, 2}  ∧  size(m) = 0
quad_step    :  RoomCond(M),  各命令が SiteOK,  Quad(M),  rt(end) = rt_room  →  Quad(end)
quad_run     :  b₁ ≤ n < a₂  →  Quad(seq(n))
Run.roomCut  :  C ≤ n < E,  pc(tr(j)) = R  →  AtV(tr(j))
Run.roomReach:  C ≤ n < E,  pz(end) & 1 = 0  →  pc(tr(arr(n))) = R
CleanW.toR   :  CleanW(M, n₀),  AtV(tr(n₀))  →  CleanR(M, n₀)
ReadW.toR    :  ReadW(M, n₀),  AtV(tr(n₀)),  |v(tr(n₀))| ≤ top  →  ReadR(M, n₀)
```

Lean: `Theorems/RoomVert.lean`（`cutOK`、`phA`、`pzLd`、`pzPieces`、`finA`、`zoneA_cover`、`CutAt`、`cut_R`、`arrive_R`、`vKeepA`）、`Theorems/RoomPair.lean`（`knSt`、`knZero`、`phSt`、`phSz`、`checkSt`、`checkSz`、`Quad`、`QuadWalks`、`quad_step`、`rowQ`、`rowsCheck`、`quad_of_rows`、`quad_run`、`RoomWalks`）、`Theorems/RoomJoin.lean`（`CleanW`、`ReadW`、`CleanW.toR`、`ReadW.toR`、`RoomRun.arr`、`InRoom.reach`、`InRoom.cut`、`RoomRun.arrive`、`atV_of`、`cleanR_of`、`speed_of`、`readR_of`）、`Theorems/Route.lean`（`Run.roomReach`、`Run.roomCut`、`Run.inRoom`）。非公開の `Proof/RoomVert.lean`（`room_vert_a`、`room_quad_st`、`room_quad_size`、`room_quad_apart`、`room_pair_rows`）。

## 方法

**プレイヤーのルーチンへの歩き.** [RoomVert](c-7-5-1-RoomVert-ja.md) の歩き（`walkA`）は、今は 3 つのことを足して求めます。

* 前に来ていない状態が `R` にいるとき、歩きは `cutOK` を求めます。スタックポインタは `S_R`、待っている NMI なし、制御レジスタのビット 7 は 0 と分かっている、ルーチンのバイト、エリアの種類、ジャンプ台、泳ぎのフラグは `CutAt` の値で分かっている。歩きはどの命令でも機械を覆うので、`cut_R` が出ます。
* `R` まで、さらに 2 つのバイトを保ちます。大きさの変化と当たりのビットです。
* NMI がモードのルーチンを呼ぶ前に一時停止のバイトを読むところ（`pzLd`）で、状態を 2 つに分けます。バイトの下のビットが 1 と分かっているものと、0 と分かっているものです。2 つには印 `[1]` と `[0]` が付くので、探索は 2 つを分けたままにします。`R` で印は消えます。フレームの終わりで、`R` に来ていない状態は下のビットが 1 と分かっていなければなりません。そして（[部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md) から）`R` に来た状態は 0 と分かっていなければなりません（`finA`）。なので、そのビットが 0 で終わるフレームは `R` に来ています（`arrive_R`）。`before_R`（フレームが `R` に来るのは多くて 1 回）と合わせると、これが最初に来たところで、`CtrlKeep.arrAt` がそれを見つけます。

**プレイヤーの状態と大きさの変化.** 歩きはフレームの始まりでこれらを知らないので、前のフレームから出します。それぞれ 1 つのバイトの関係で、[RoomPair](c-7-5-2-RoomPair-ja.md) の種類の歩きを 1 つずつ使います（`pair_frame` で `x = y`）。`st ∈ {0, 1, 2}` は、ビット 2 から 7 が 0 と分かっていて、ビット 0 かビット 1 が 0 と分かっていることで示します（`knSt`）。`size = 0` はバイトが 0 と分かっていることで示します（`knZero`）。最初の操作では切り替えの段が両方を知っています（`rowQ`）。段を 1 回たどる中で、`RoomPair` の 2 つの関係とこの 2 つをまとめて調べます（`rowsCheck`）。`quad_run` は `pair_run` と同じくフレームについての帰納法です。`R` への歩きは両方のバイトを保つので、`R` でも成り立ちます。

**速さの範囲.** `t₀` までの各フレームの始まりで、横の状態は範囲 `D` の中にあります（`RoomRun.far_inD`、項目 1-1-c-7-1-3）。なので `|v| ≤ top` です。`R` への歩きは速さを保ちます（`InRoom.before`）。

| ROM の検査 | 表 | ステップ | プログラムでの時間 |
|---|---|---|---|
| `RoomVert.checkA`（`cutOK`、2 つのバイト、分割つき） | 69,913 | 468,184 | 6.2 秒（前は 6.9 秒） |
| `RoomPair.checkSt` | 36,165 | 209,867 | 3.4 秒 |
| `RoomPair.checkSz` | 36,165 | 209,867 | 3.5 秒 |
| `RoomPair.rowsCheck`（4 つの関係） | 時間の段 | | 25 秒。前の 2 つの関係の検査と同じ |

一時停止のバイトでの分割で、表は 2 状態増えます。

**試してできなかったこと: 当たりのビット.** 3 つ目の歩きで、当たりのビットのビット 2 から 7 が 1 のままであること（これが `collBits`）を求めました。終わりの 6 つで失敗します。原因は `ImpedePlayerMove` の終わりの書き込みで、当たりのビットと X の補数の AND を書きます。X は一時的なバイトから読み、1 減らし、片方の分岐でまた 1 増やします。本物のどの道でも 1 か 2 です。でも抽象機械は、分岐から 1 減らした X が 0 だったことを学びません。なので書き込みで X が分からず、ビットも分かりません。直すには、`TaintRun` の抽象機械で分岐が X を絞る必要があります。なので `ReadW` に `coll` が残ります。

## 本物のフレームでの確認

`room-ctrl-check FM2 200`: 部屋の最初の操作からの各フレームを、命令ごとに走らせます。映像と、自分の入力 5 種類それぞれ 200 回の走り、最大 150 フレームです（種類 0: どのボタンも、Start と Select も。種類 4: 8 フレームに 1 回 Start）。

| | フレーム |
|---|---|
| 部屋のフレーム | 150,111 |
| プレイヤーのルーチンに来ない | 37,392（種類 0 と 4） |
| そのうち止まっていない状態で終わる | 0 |
| プレイヤーのルーチンで `CutAt` が成り立たない | 0 |
| プレイヤーの状態が 0、1、2 でない、または大きさの変化が 0 でない（始まりかルーチン） | 0 |
| 当たりのビットが `collBits` にない（始まりかルーチン） | 0 |
| ルーチンの前に `vKeepA` のバイトに書く | 0 |
| 覚えている速さが `|v|` でない、または押す側が塞がれている（`CleanW` でない） | 8,606 |
| ルーチンで `|v| > top` | 0 |

## 一時停止: このラウンドの前の間違い

`clean` は、`t₀` までの各フレームがプレイヤーのルーチンに来ることを求めていました（`AtCtrl` と `AtFrame` の `pc`）。止まった状態で終わるフレームはそこに来ません。なので、`t₀` より前に部屋で一時停止する走りは定理の外でした。そう書いたページはありませんでした。上の自分の走りでは 37,392 フレームがプレイヤーのルーチンに来ず、すべて止まった状態でした。そのときは定理の外で、それ自身のフィールド `unpaused` になりました。いまは定理に入っています。部屋は止まっていない状態で終わるフレームだけを数えます（[部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md)）。

## 仮定（Lean で証明していない）

* `unpaused` はなくなりました（[部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md)）。かわりに `roomLag`: 部屋で止まった状態で終わるフレームは `lag` のフレーム。
* `CleanW` か `Stop ∧ ReadW`（各 1 フレーム）: プレイヤーのルーチンでの覚えている速さと塞ぎ（フレームがモデルに従うかを決めます）、当たりのビットが `collBits` にあること、スクロールの処理から後にフレームがすること（`after`、`collide`）。
* 部屋のフレームの各命令の `SiteOK`（`chg.roomSites`）。前と同じ。

**ファイル.** `Theorems/RoomVert.lean`、`Theorems/RoomPair.lean`、`Theorems/RoomJoin.lean`、`Theorems/Route.lean`、非公開の `Proof/RoomVert.lean`。

**再現.**
```
.lake/build/bin/smbrta room-ctrl-check FM2 [N]    # 検査（約 40 秒）と本物のフレーム。5 種類それぞれ N 回の走り
```
