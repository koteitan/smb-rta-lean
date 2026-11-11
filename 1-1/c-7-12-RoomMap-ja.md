[← Back](README-ja.md) | [English](c-7-12-RoomMap.md) | [Japanese](c-7-12-RoomMap-ja.md)

# 部屋のブロックの地図

**主張.** これは部分的な結果です。部屋で最初に操作できてから横の土管に入るまでのどのフレームでも、2 つのブロックバッファでは、地図で 0 のビットは 0 です。これらのフレームでブロックバッファのルーチンが読むたびに、横の土管の 2 つのタイルは土管の列にしかありません。これは [横の土管に入るフレームを本物のフレームで](c-7-3-SideEntryRule-ja.md) の `TilesOK` で、走りの本物の機械の上で証明しました。証明は、[部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md) と同じように部屋の 1 フレーム全部を抽象機械で追い、わかっているビットを増やします。新しい仮定はありません。各命令の `SiteOK` と各フレームの操作のルーチンは、そのページがすでに仮定しているものです。最初の操作の状態は [`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md) の段から出ます。

地図は参照の機械です。参照の縦の土管に入ったあと、入力なしで 91 フレーム進めた、部屋で最初に操作できる機械です。操作できます。証明したのは、地図で 0 のビットが 0 のままであることだけです。1 のビットが残ること（レンガがレンガのままであること）と、[地下の部屋をつなぐ](c-5-RoomJoin-ja.md) のほかのフィールドの数（角、ゴール、床、左の壁）が地図のものであることは、証明していません。

`M` は地図です。`B` は 2 つのブロックバッファの 416 バイトの集合です。`rt(m)` は `GameEngineSubroutine`、`rt_r` は `ScreenPage` の参照の機械での値（操作のルーチン）です。`seq(n)` はフレーム `n` の始めの機械、`tr(j)` はフレームの `j` 命令あとの機械です。`T₁`、`T₂`、`AtRead`、`TilesOK` は [横の土管に入るフレームを本物のフレームで](c-7-3-SideEntryRule-ja.md) のものです。`x & y` と `~x` はビットごとの演算です。

```
Zero(m)       :=  ∀ d ∈ B,  m(d) & ~M(d) = 0
Cond(m)       :=  ScreenPage のフレームの始めの条件に Zero のビットを足したもの
```

`Cond(m)` は、前のフレームが待ちのループで終わり、`ScreenPage` のバイトがその参照の機械のビットを持ち、[1 フレーム全部](c-7-16-SideFrame-ja.md) の画面の 5 バイト（スクロールの固定、両端の位置とページ）がその値を持ち、`Zero(m)` が成り立つことです。5 バイトのうち新しいのは左端の位置だけです。ほかの 4 つは `ScreenPage` が知っています。

```
s_eraseT      :  コインを消す命令は、抽象機械が知らないポインタを通して A を書く。A がわかっていて、
                 B のどのバイトも、わかっているビットで A と同じ  →  抽象状態は機械をまだ覆う
room_stepT    :  RoomOKT,  Cond(m),  frame(m, i) の各命令で SiteOK
                 →  (Cond(frame(m, i)) ∨ rt(frame(m, i)) ≠ rt_r)  ∧  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j))
map_run       :  RoomOKT,  seq(n + 1) = frame(seq(n), inp(n)),  Cond(seq(c)),
                 フレーム c … e − 1 で SiteOK,  rt(seq(n)) = rt_r (c ≤ n < e)
                 →  (∀ n ∈ [c, e),  Cond(seq(n)))  ∧  (∀ n ∈ [c, e),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
start_of_rows :  startCheckT,  InRowsT(m),  control(m)  →  Cond(m)
map_of_rows   :  MapFacts,  startCheckT,  seq(n + 1) = frame(seq(n), inp(n)),  InRowsT(seq(b)),  control(seq(b)),
                 フレーム b … a − 1 で SiteOK,  rt(seq(n)) = rt_r (b ≤ n < a)
                 →  (∀ n ∈ [b, a),  Zero(seq(n)))  ∧  (∀ n ∈ [b, a),  ∀ j,  AtRead(tr(j)) → TilesOK(tr(j)))
map_check, map_start（非公開）  :  mapCheck = true,  startCheckT = true   （native_decide）
room_map（非公開）              :  2 つの確認をつけた map_of_rows
```

`InRowsT(m)` は、`m` が部屋への切り替えの時間の段の機械であることです。`Route.Changes` は最初の操作でこれを与えます（`Changes.roomAt` も同じものを使います）。入るフレーム `a₂` までのフレームでの `SiteOK`（`roomSites`）と操作のルーチン（`roomStay`）も与えます。

Lean: `Theorems/RoomMap.lean`、非公開の `Proof/RoomMap.lean`。`Theorems/RoomJoin.lean` に `RoomRun.TilesE`（フレーム `E` の読みでのタイル。`RoomRun.mouth_of` の仮定で、もう欄ではない）。`Theorems/Route.lean` につなぎ `roomEnter` と `Run.roomTiles`。

```
roomEnter       :  ∃ k,  b₁ ≤ k < a₂  ∧  fm(E − 1) = seq(k)  ∧  pad(E) = inp(k)          （Route.Run の欄）
Run.roomTiles   :  確認,  Run  →  TilesE:  ∀ n j,  WriteStep(n) → j ≤ n → AtRead(tr(j)) → TilesOK(tr(j))
```

`Run.roomTiles` は、`Route.Changes` のフレーム `b₁ … a₂ − 1` での `map_of_rows`（部屋に入る切り替えの段、`roomSites`、`roomStay` から）を、`roomEnter` のフレーム `k` で使います。

同じ抽象機械から、部屋のどのフレームも操作できる状態で始まることが出ます。[1 フレーム全部](c-7-16-SideFrame-ja.md) の抽象機械が求める形です。

```
startCheckF        :  基準の機械は待ちのループにいてスタックポインタはガードの値、Cond はガードの 8 つのバイト（ゲームの 3 つ、画面の 5 つ）を
                      全部その値で知っている、プログラムは同じ、9 < vblank が終わるドット
frameStart_of_cond :  startCheckF,  Cond(m)  →  FrameStart(m)          （1 フレーム全部 の部屋のガード G_room で）
start_of_rowsF     :  map_of_rows の仮定,  startCheckF  →  ∀ n ∈ [b, a),  FrameStart(seq(n))
Run.roomStartE     :  確認,  Run  →  FrameStart(fm(E − 1))          （StartE。前の欄 room.startE）
map_startF（非公開） :  startCheckF = true（native_decide）
```

抽象機械はまた、どの状態でも、`SiteOK` が与えない `Clean`（[1 フレーム全部](a-5-2-PipeWrites-ja.md)）の条件を、部屋のガード `G_room` で確かめます。守るバイトには画面の 5 バイトも入ります。添字やポインタを通す書き込みは、行き先がわかっていてガードのバイトの外にあるか、コインを消す書き込みです。コインを消す書き込みの行き先は、`SiteOK` がブロックバッファの中に置きます。ジャンプのルーチンでは、番号がわかっていて表の中にあります。ポインタを通す読みと時間は `SiteOK` が与えます。だから部屋のどのフレームのどの命令も、新しい仮定なしに `Clean` です。そしてどの状態も、頭がブロックに当たったときのルーチン（`h`、`G_room` が切るただ 1 つの場所）にいません。`SiteOK` では頭の読みは何もないかコインしか出さないので、抽象機械はそこに来ないのです。

```
cleanS(A)          :=  pc(A) ≥ 0x8000  ∧  (pc(A) = erase  ∨  書き込みの行き先がわかっていて Plain)  ∧  (pc(A) = JumpEngine → A がわかっていて表の長さより小さい)
歩きの各状態       :  tilesB(A)  ∧  cleanS(A)  ∧  pc(A) ∉ cuts(G_room) = {h}
clean_of_sim       :  CleanFacts,  A が m を覆う,  cleanS(A),  SiteOK(m)  →  Clean(m)
clean_of_rows      :  map_of_rows の仮定  →  ∀ n ∈ [b, a),  ∀ j,  Clean(tr_n(j))
cuts_run           :  map_run の仮定  →  ∀ n ∈ [c, e),  ∀ j,  pc(tr_n(j)) ∉ cuts
head_of_rows       :  map_of_rows の仮定  →  ∀ n ∈ [b, a),  ∀ j,  pc(tr_n(j)) ≠ h
Run.roomCleanE     :  確認,  Run  →  CleanE                       （前の欄 room.cleanE）
Run.roomHeadE      :  確認,  Run  →  HeadE:  ∀ j,  pc(tr(j)) ≠ h    （前の欄 room.edgeE の一部）
Run.inRoom         :  確認,  Run  →  TilesE ∧ StartE ∧ CleanE ∧ HeadE     （RoomRun.InRoom）
```

`CleanFacts` は `mapCheck` の一部です。場所の待ちのループはガードのもので、最後のドットはガードのもの以下で、ブロックバッファのどのバイトもガードのバイトではありません。この確認を足して、`mapCheck` はプログラムで約 4 秒です（画面のバイトと切る場所を足す前は 2.6 秒）。

## しくみ

**最初の操作.** 切り替えの段は、操作できるどの状態でも、ブロックバッファの 416 バイトを全部知っています。TAS ではこれらのバイトは地図と同じです。確認 `startCheckT` は、時間の段の操作できるどの状態も、`Cond` の始めの状態の下にあることを求めます。

**歩き.** `ScreenPage` の歩きに、3 つの違いがあります。

* コインを消す命令（`ErACM`）は、歩きが知らないポインタを通して書きます。`ScreenPage` は、そこで `B` のどのバイトもわかっているビットを持たないことを求めます。ここでは、`A` がわかっていて、`B` のどのバイトのわかっているビットとも同じであることを求めます（`bufAgree`）。消す命令は 0 を書き、`B` のわかっているビットは 0 のビットなので、これは成り立ちます。
* ブロックバッファのルーチンが読む場所の各状態で、歩きは `tilesB` を確かめます。土管の列にない `B` のどのバイトも、どちらのタイルでもないとわかっていることです。`T₁` が 1 で、0 とわかっているビットがあれば、そのバイトは `T₁` ではないとわかります。この地図では、列にないどのバイトも、両方のタイルについてそういうビットを持ちます。
* フレームの終わりで、歩きは `tilesB` と、`Cond` の始めの状態か、`rt` がわかっていて `rt_r` でないこと（フレームが操作のルーチンを出た）を求めます。

**大きさ.** 探索は 209,861 ステップ、9,132 の枝分かれ、失敗 0 です。表は 9,301 状態です。`mapCheck` はプログラムで約 4 秒、`startCheckT` は約 2.6 秒です。非公開の証明のビルドは約 10 秒です。

**0 のビットだけの理由.** 消す命令は、歩きが知らない `B` のどれかのバイトに書きます。どこに 0 を書いても、0 とわかっているビットは残ります。1 とわかっているビットは残りません。どのバイトもそのまま残すには、消す命令がコインのバイトに書くことが要ります。

## 本物のフレームで確かめたこと

プログラム `room-map-check FM2 [N]` です。部屋のフレームを、操作のルーチンを出るまで、1 命令ずつ動かします。

| 走り | フレーム | 読み | 消したコイン |
|---|---|---|---|
| 動画、最初の操作から入るまで | 111 | 728 | 13 |
| 部屋の動画のフレームから、右へ向かう乱数の入力（200 回、300 フレームまで） | 43,441 | 297,928 | 653 |
| 最初の操作から、乱数、B つきの左、B つきの右、壁（4 × 200 回、200 フレーム） | 160,000 | 1,096,212 | 59 |

* どのフレームも `Cond` で始まり、`Zero` が成り立ちます。どの読みでも `TilesOK` です。`SiteOK` を満たさない命令はありません。
* 動画の部屋の最初の操作（動画のフレーム 653 のあと）では、ブロックバッファは 1 バイトずつ地図と同じです。
* `mapCheck` と `startCheckT` は真です。

## 前提（Lean では証明していない）

* **`SiteOK`.** 最初の操作から入るまでのフレームの各命令で。それらの各フレームは操作のルーチンで始まる。これは [部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md) が仮定しているものです（`Route.Changes.roomSites`。`roomStay` は定理）。
* **つなぎ `roomEnter`.** `RoomRun` のフレーム `E`（`fm(E − 1)`、`pad(E)`）は、部屋の中の `Route.Changes` のフレームの 1 つです。同じフレームの 2 つの番号づけのつなぎで、`roomCtl` と同じ種類です（項目 1-1-0-4）。`RoomRun` の欄 `tiles` はなくなりました。`Run.roomTiles` が `room_map` とこのつなぎから証明します。
* **地図の残り**（項目 1-1-c-7-12）. 証明したのは、地図で 0 のビットだけです。レンガ、床、壁がそのまま残ることと、ほかのフィールドの数が地図のものであることは、証明していません。

**ファイル.** `Theorems/RoomMap.lean`、非公開の `Proof/RoomMap.lean`。

**再現.**
```
.lake/build/bin/smbrta room-map-check FM2 [N]    # 2 つの確認と本物のフレーム。それぞれの種類で N 回走る（N = 200 で約 10 分）
```
