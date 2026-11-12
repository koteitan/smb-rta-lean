[← Back](README-ja.md) | [English](c-7-18-2-SideEntryEnd.md) | [Japanese](c-7-18-2-SideEntryEnd-ja.md)

# 横の土管に入るフレーム: 終わりの位置

**主張.** 部屋のフレームで横の土管のルーチンを書くものでは、フレームの終わりの位置は口の左端より左ではありません。位置についての仮定はありません。なので `P(E)` は、ほかのフレームを `read_P` が読むのと同じく、フレーム `E` の終わりで読みます（`read_PE`）。[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) の欄 `movedE` はなくなりました（項目 1-1-c-7-18-2）。

2 つの抽象機械で証明します。1 つめは、[横の土管に入るフレーム: 1 フレーム全部](c-7-16-SideFrame-ja.md) の抽象機械で、フレームの始めから横の土管のルーチンを最初に書くところまで追います。2 つめは、[部屋のブロックの地図](c-7-12-RoomMap-ja.md) の歩きで、書き込みからフレームの終わりまで追います。この歩きは部屋のバイトと、どの書き込みの行き先も知っています。

`tr(j)` はフレームの `j` 命令あとの機械です。`rt(m)` はルーチンのバイト、`e_s` は横の土管のルーチン、`w` はそれを書く命令です。`x₀` は右側が口に入る最初の `x`、`P₀ = 256·x₀` は口の左端です。`px(m) = 256·page(m) + x(m)`、`posP(m) = 256·px(m) + fraction(m)` です。

```
splitAll   移動の終わりで、位置をすべての値を覆う切れに分ける
             ページ 0 で x < x₀（SideFrame の 4 切れ）,  ページ 0 で x ≥ x₀（5 切れ）,  ページ ≠ 0（8 切れ: ページのどれかのビットが 1）
splitOne   当たり判定のルーチンが画面での高さを最初に読むところ: そのバイトは 1、または 1 とどこかのビットが違う（9 切れ）
posOK(A)   :=  ページのビットが 1 とわかっている,  または  ページが 0 とわかっていて、x のわかっているビットが x₀ 以上
okA(A)     :=  rt(A) が e_s でないとわかっている,  かつ  (pc(A) = w → posOK(A))
HypE(m)    :=  (AtRead(m) → TilesOK(m))  ∧  pc(m) ∉ {h, bumpAt}

write_right_of_left :  frameCheck,  FrameStart(m),  ∀ j,  Clean(tr(j)) ∧ HypE(tr(j))
                       →  ∀ j,  (∀ k ≤ j,  rt(tr(k)) ≠ e_s)  →  pc(tr(j)) = w  →  x₀ ≤ px(tr(j))

splitR     w で、rt が e_s でないとわかっている間: ページ 0 で x ≥ x₀（5 切れ）,  ページ ≠ 0（8 切れ）
HypW(m)    :=  pc(m) = w  →  rt(m) ≠ e_s  →  x₀ ≤ px(m)
okS(A)     :=  rt(A) が e_s でないとわかっている,  または  rt(A) が e_s とわかっていて posOK(A)
okT(A, B)  :=  rt(A) が e_s とわかっている  →  rt(B) が e_s とわかっている

rest_end :  restCheck,  RoomCond(m),  ∀ j,  SiteOK(tr(j)),
            ∀ j,  (∀ k ≤ j,  rt(tr(k)) ≠ e_s)  →  HypW(tr(j)),
            ∃ n,  rt(tr(n)) ≠ e_s  ∧  rt(tr(n + 1)) = e_s
            →  x₀ ≤ px(frame(m, i))

mouth_of_rows :  RoomMap.map_of_rows の仮定,  確認,  b ≤ k < a,  Enters(seq(k), inp(k))
                 →  P₀ ≤ posP(frame(seq(k), inp(k)))
Run.roomMouthE :  確認,  Run  →  P₀ ≤ posP(frame(fm(E − 1), pad(E)))          （InRoom.mouthE）
read_PE（欄）   :  P(E) = posP(frame(fm(E − 1), pad(E)))                        （read_P と同じ読み）
RoomRun.mouth_of :  InRoom  →  P₀ ≤ P(E)
side_entry_end_check, side_rest_check（非公開） :  frameCheck = true,  restCheck = true   （native_decide）
```

`mouth_of_rows` が、部屋のフレームで 2 つの歩きをつなぎます。1 つめの歩きは、ルーチンのバイトが横の土管のものになる前のどの状態でも `HypW` を出します。そのあとは、2 つめの歩きの `okT` がルーチンのバイトを横の土管のもののままにするので、`HypW` は何も求めません。`Route.Run.roomMouthE` は `Run.roomEnter` のフレームで使います。

Lean: `Theorems/SideEntryEnd.lean`、`Theorems/SideEntryRest.lean`。`Theorems/RoomJoin.lean` に欄 `read_PE` と `InRoom.mouthE`。`Theorems/Route.lean` に `Run.roomMouthE`。非公開の `Proof/SideEntryEnd.lean`、`Proof/SideEntryRest.lean`。

## しくみ

**書き込みまで**（`SideEntryEnd`）. 抽象機械と切れは [1 フレーム全部](c-7-16-SideFrame-ja.md) のものですが、移動の終わりでは仮定なしに位置を分けます。ページ 0 なら x を口の左か右の切れに入れます。ほかのページなら x はわかりません。ページのどれかのビットが 1 です。画面の外かを調べるところでは、前と同じく、x のビットが少しでもわかっていれば値に分けます。そこでページが一部わかっているときは、探索はレジスタを別々に保ちます。すると画面の端での書き込みは、わかっている値を書きます。画面での高さは、当たり判定のルーチンが最初に読むところで分けます。画面の中（1）なら当たり判定は横の判定まで進み、そうでなければ出ます。ルーチンのバイトが横の土管のものになったところで、その道は止めます。

どの道でも、`w` が来るときの位置は口の左端より左ではありません。ページ 0 なら、`SideFrame` と同じく、横の判定が土管のタイルを見つけるのは x が `x₀` 以上のときだけです。ほかのページなら、ページのビットが 1 とわかったままです。

**書き込みからフレームの終わりまで**（`SideEntryRest`）. 部屋の歩きは、部屋のバイト（敵もファイアボールもいない）と、どの書き込みの行き先も知っています。`w` で、`HypW` により位置を口の左端より右の切れに分けます。書き込みのあと、フレームは操作のルーチンの残りと、ほかのルーチンを動かします。位置を動かす書き込みはなく、ルーチンのバイトは横の土管のもののままです。画面での高さはわかっている（当たり判定で 1 だった）ので、操作のルーチンは穴に落ちたときのルーチンを始めません。

**大きさ.** 書き込みまで: 16,522,088 歩、1,615,563 回の分かれ、失敗 0、表は 586,648 状態。プログラムで探索は約 40 秒、確認は約 58 秒（もう一度探索する）、4.3 GB。書き込みから: 454,881 歩、失敗 0、75,908 状態。探索は約 4 秒、確認は約 7 秒。どちらも数秒より長く、1 つめはパート c でいちばん大きい確認です。

**なぜ 2 つの歩きか.** 1 つの歩きではできませんでした。

* `SideFrame` の抽象機械でフレームの終わりまで（位置はページ 0 だけ）: 書き込みのあと、フレームはこの機械が知らない添字で書きます（ファイアボール、敵、画面のバッファ）。そういう書き込みは位置を忘れます（10,412,005 歩、失敗 347,289）。その書き込みから位置を守っても（ガードの守るバイトに位置を入れる）、敵のルーチンはほかのルーチン（けが）を書き、Mario を動かします。この機械は部屋に敵がいないことを知らないからです（最初の 6,000,000 歩で失敗 3,514）。部屋の条件が全部知っている 363 バイトも保つと、探索は 15 分で終わりませんでした（4.7 GB）。
* 部屋の歩きで、移動の終わりで位置を分ける: 切れが部屋のどのフレームの状態も増やし、探索は 8 GB を超えました。

フレームの前の部分には位置がいりますが、部屋のバイトはいりません。後の部分には部屋のバイトがいり、位置は書き込みからだけでいいのです。

## 本物のフレームで

プログラム `side-frame-check`（[1 フレーム全部](c-7-16-SideFrame-ja.md) を見てください）は 1,715 回の入るフレームを動かします。動画の 1 回、動画の部屋から乱数の入力で 67 回、入る近くのすべての入力で 352 回、口の近くの書きかえた状態で 1,295 回です。どれでも、書き込みの前の移動の終わりの位置は 195〜216 px で、それはフレームの終わりの位置です。なので `read_PE` は前の `movedE` と同じ `P(E)` を読み、どれでも `P(E) ≥ P₀` です。

## `RoomRun` の欄

* なくなった: `movedE`（`P(E)` は移動の終わりの位置）。
* 増えた: `read_PE`（`P(E)` はフレームの終わりの位置）。`read_P` と同じ読みです。
* `InRoom` は `mouthE`（このページ）と `bump`（頭が当たらない、[ブロックの地図](c-7-12-RoomMap-ja.md)）になりました。`TilesE`、`StartE`、`CleanE`、`HeadE` と定理 `Run.roomTiles`、`Run.roomStartE`、`Run.roomCleanE`、`Run.roomHeadE` は定理として残ります。`mouth_of` はもう使いません。`RoomJoin.Checks.sideFrame` はなくなりました。

## 前提（Lean では証明していない）

新しいものはありません。2 つの歩きは、[部屋のブロックの地図](c-7-12-RoomMap-ja.md) が部屋のフレームで証明するもの（`FrameStart`、`Clean`、`TilesOK`、頭が当たらないこと、各フレームの始めの部屋の条件）と、それが仮定するもの（部屋のフレームの各命令の `SiteOK`、`Route.Changes.roomSites`）を使います。

**ファイル.** `Theorems/SideEntryEnd.lean`、`Theorems/SideEntryRest.lean`、非公開の `Proof/SideEntryEnd.lean`、`Proof/SideEntryRest.lean`。

**再現.**
```
.lake/build/bin/smbrta side-entry-end-search      # 2 つの歩きの探索と確認、約 2 分
```
