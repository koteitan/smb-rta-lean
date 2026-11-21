[← Back](README-ja.md) | [English](d-2-5-4-4-SizeKeep.md) | [Japanese](d-2-5-4-4-SizeKeep-ja.md)

# 部屋を通るプレイヤーの大きさ

**主張.** 横の土管に入るフレームは、小さいプレイヤー（基準の大きさ）か大きいプレイヤー（大きさのバイト 0）で始まります。証明しました。部屋のフレームは大きさを保ちます（部屋のフレームの歩き 2 つ、ネイティブでそれぞれ約 3 秒）。部屋の最初の操作では、最初の切り替えの段が大きさのバイトのビット 1 から 7 を知ります（段の確認 1 つ、ネイティブで約 33 秒）。そこで `Route.Run` のフィールド `height₂` はなくなりました。新しいフィールドはありません。`height₂` は、入るフレームが 2 つの大きさのどちらかで始まること、または入口の高さが基準の入口のものであることを求めていました。

そのために、縦の土管の入口は大きさのバイトのビット 1 から 7 を知ります。プレイヤーの状態のビットと同じです（`PipeChangeEnd.entryMasks`）。出口の一覧もそのビットを持ちます（`exitMasks`）。タイトルでの Start と操作からのフレームが、入口でそのビットを与えます（`EntryKeep`、`Run.entry₁`）: 大きさの変化はビット 0 だけを反転します。これで `chg.upCleanU` のガードは大きさのバイトも守ります（144 バイト、前は 143）。

`m[i]` は `m` の RAM のバイト `i`、`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`trₙ(j)` はフレーム `n` の `j` 命令目の機械です。`seq(n)` は走りのフレーム `n` が始まるときの機械です。`a₁`、`b₁`、`a₂` は縦の土管の入口、部屋の最初の操作、横の土管の入口です（`Route.Base`）。`size(m)` はプレイヤーの大きさのバイト、`rt(m)` はルーチンのバイト、`r` は部屋の基準の機械（小さいプレイヤー）、`e` は縦の土管の基準の入口です。`Room` と `SiteOK` は [部屋での画面のページ](d-2-4-ScreenPage-ja.md) のものです。`Keep(v)` は、[レベルの番号](d-2-5-3-AreaKeep-ja.md) の歩きが、大きさのバイトを値 `v` の 1 状態の表に入れて通るという確認です（`roomCheckS`）。`timeRows` は最初の切り替えの段のうち `left` が 0 のもの、`InRowsT(m)` は `m` がそこにあることです（[部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)）。

## 定理

```
entryMasks, exitMasks  ∋  (size, ビット 1 から 7)                                 （ラウンド 22）
Entry(m)       ⟹  size(m) &&& 0xFE = size(e) &&& 0xFE                           （PipeChangeEnd.Entry。a₁ では Run.entry₁ が与える）

rowsCheckS     :  ∀ row ∈ timeRows, ∀ S ∈ row:  S は size のビット 1 から 7 を 0 と知る,   size(r) &&& 0xFE = 0,   size(r) ≠ 0
size_of_rows   :  rowsCheckS,  InRowsT(m),  m は操作できる      →   size(m) = size(r)  ∨  size(m) = 0
byte_all       :  Keep(v),  Room(seq c),  size(seq c) = v,
                  ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j)))  ∧  rt(seq n) = rt(r)
                  →  ∀ n ∈ [c, e]:  size(seq n) = v
size_run       :  Keep(size(r)),  Keep(0),  同じ条件,  size(seq c) ∈ {size(r), 0}
                  →  ∀ n ∈ [c, e]:  size(seq n) ∈ {size(r), 0}

Run.size₁      :  size(seq b₁) = size(r)  ∨  size(seq b₁) = 0                       （定理）
Run.size₂      :  size(seq(a₂ − 1)) = size(r)  ∨  size(seq(a₂ − 1)) = 0              （定理）
Run.y₂         :  y(seq a₂) = y_e                                                    （定理。もうフィールドを使わない）
```

`Run.size₁`: 部屋の最初の操作の機械は最初の切り替えの段にあり（`ChangesK.run₁`、`inRowsT`）、操作できます（`ChangesBase.ctl₁`）。`Run.size₂` は `c = b₁`、`e = a₂ − 1` とします: `b₁ < a₂` です（`Run.b₁_lt_a₂`）。部屋の最初の操作は部屋の条件にあります（`ChangesK.roomAt`）。`b₁` から `a₂` の前までの各フレームは `SiteOK` を満たし（`chg.roomSites`）、プレイヤーのルーチンで始まります（`ChangesBase.roomStay`）。`Run.y₂` の場合は 2 つです: 基準の大きさなら [高さ](d-2-5-4-EntryHeight-ja.md) の歩きが、大きさ 0 なら [EntryHeightBig](d-2-5-4-3-EntryHeightBig-ja.md) の歩きが高さを出します。

Lean: `Theorems/SizeKeep.lean`（`sizeI`、`refSize`、`roomCheckS`、`KeepOK`、`byte_all`、`rowS`、`rowsCheckS`、`low_one`、`zero_or_one`、`size_of_state`、`size_of_rows`、`Facts`、`factsOf`、`size_run`）、`Theorems/PipeChangeEnd.lean`（`entryMasks`、`exitMasks`）、`Theorems/Route.lean`（`RoomChecks.height : SizeKeep.Facts …`、`Run.size₁`、`Run.size₂`、`Run.y₂`）、非公開の `Proof/SizeKeep.lean`（`size_keep_ref`、`size_keep_zero`、`size_rows`）と `Proof/EntryHeight.lean`（`height_facts`）。公開のファイルにゲームのデータはありません。

## しくみ

大きさのバイトに番地で書くのは、ゲームの 3 か所だけです（逆アセンブルで読みました）: 新しいゲームの準備とコンティニューは小さい値を書きます。大きさの変化は、前の値の一番下のビットを反転して書きます。だから添字やポインタを通した書き込みがこのバイトに届かなければ、ゲームの始まりから大きさのバイトのビット 1 から 7 は 0 のままです。

* **タイトルから縦の土管まで**（パート a）。大きさのビットは `EntryKeep` の保つ見張りの 1 つです（入口のバイトとマスクのうち `restNames` にないもの）。タイトルでの Start の条件はこのバイトを知るので、フレーム 0 はそのビットで終わります（`nearCheck`）。操作からの各フレームはそれを保ちます（`keepCheck`）: 大きさの変化は `EOR #1` でビット 1 から 7 を保ちます。`upCleanU` のガードは、添字やポインタを通した書き込みからこのバイトを守ります。
* **縦の土管を通って**（パート b）。土管の歩きの始まりの状態はこのビットを知ります（`startsP`、入口のマスク）。土管のフレームは大きさに書かないので、歩きのフレームはそれを保ちます。出口の状態は出口のマスクでそれを知ります。だから出口のあとの段のどの状態もそれを知り、部屋の最初の操作の機械はそのビットを持ちます（`rowsCheckS`、`size_of_rows`）。
* **部屋を通って**（パート d）。`AreaKeep` の歩き（`RoomPause` の歩き）で、バイトを 1 状態の表に入れます: 音のルーチン、パッド、ポーズのルーチンの中では歩きはバイトを知ります。ほかではどのステップもバイトを保つか、表の値を書かなければなりません（`RoomPause.pstep`）。歩きは基準の値でも 0 でも通ります。だから部屋の条件でバイトがその値で始まるフレームは、その値で終わります（`RoomPause.pause_step`）。帰納法は `RoomPause.pause_run` のものです。ただし最後だけでなく各フレームで言います。

`SizeKeep.Facts` は `EntryHeightBig.Facts` に 2 つの歩きと段の確認を足したものです。だから `RoomChecks.height` がそれらを持ち、非公開のファイルでの `RoomChecks` の作り方は変わりません。

## 測ったこと

* `size-keep-check FM2 50 walk`（終了コード 0）: 部屋の 2 つの歩きはネイティブで 3.0 秒と 5.0 秒（混んだ機械。すいた機械で 3.1 秒と 2.6 秒）。時間の段は 1 段 14,224 状態で、どの状態も大きさのビット 1 から 7 を 0 と知ります。`rowsCheckS` はネイティブで 32.5 秒。
* `entry-walk-check`（終了コード 0）、大きさを見張りに入れて: 操作からの 1 フレームは 1,176,671 ステップ、失敗なし。`keepCheck` 7.2 秒、`nearCheck` 3.1 秒。
* `entry-keep-check FM2`（終了コード 0）: `Entry` はバイトとマスクで 110（前は 109）、入口で証明 75、操作から保つ 72、`Rest` 35。この確認の本物の走りでは、どのフレームも保つバイトを保ち、どの入口も `Entry` を満たします。
* `pipe-end-check FM2`（終了コード 0）: 新しいマスクでの土管のフレームと段の確認、混んだ機械でネイティブ 309 秒。本物の入口 15 回が入口の条件を満たします。
* `up-clean-u FM2`（終了コード 0）: 大きさのバイトを含むガードの `CleanK` は、TAS（368 フレーム）、基準の入口（440）、操作からの自分の走り 300 回（127,841 フレーム）、TAS のフレームからの自分の走り 300 回（75,241）、遅い入口 40 回（17,600）のどの命令でも成り立ちます。
* `size-keep-check FM2 30 mushroom`（終了コード 0）: 200 から 400 px の TAS のフレームから、歩き、長押しのジャンプ、そのあと右、という自分の走り。1,200 回のうち 10 回がキノコを取ります（大きさが基準のものから 0 になる）。この 10 回の操作からのフレーム（3,328）で、大きさのバイトを含むガードの `CleanK` はどの命令でも成り立ち、大きさのビット 1 から 7 は 0 のままです。
* TAS: 最初の操作から大きさは基準のものです。縦の土管の入口、部屋の最初の操作（ムービーのフレーム 653 のあと）、入口の前の部屋の 111 フレームの始まり、入るフレームの始まりでもそうです。
* 縦の土管の入口の 30 フレーム前に大きいプレイヤーを入れた TAS の入力: 走りは土管に入り、部屋の最初の操作で大きさは 0、部屋の 111 フレームはどれも 0 で始まります。
* 最初の操作から縦の土管までの TAS のフレームから、自分の 400 フレームの走り 50 回: 大きさは一度も変わりません（キノコを取る走りはありません）。
* 部屋での自分の走り: 小さい、50 回、19,938 フレーム、入口 19 回。大きい、50 回、20,612 フレーム、入口 18 回。走りの始まりと違う大きさで終わるフレームはありません。入るフレームはどれも走りの大きさで始まります。

## ほかのパートから使うもの

* パート a: `Run.entry₁`（`EntryKeep.entryV_of_title`。`title`、`Run.upStart₁`、`chg.upCleanU` からの `Run.upClean₁`、`chg.entryRest₁` を使う）。
* パート b: `PipeChangeEnd` のマスク、`ChangesK.run₁`、`RoomChecks.pipe` での `PipeRunK.inRowsT`、`ChangesBase.ctlFirst₁`、`ChangesBase.ctl₁`。
* パート c: `ChangesK.roomAt`（最初の操作での部屋の条件）、`chg.roomSites`、`ChangesBase.roomStay`、`Run.b₁_lt_a₂`。
* パート d: `AreaKeep` の歩き（`roomCheckA`、`roomOK_of_check`）と `RoomPause.pause_step`。
* 循環はありません。どれも `height₂`、`Run.size₁`、`Run.size₂`、`Run.y₂` を使いません。

## 道筋で変わったこと

* なくなった: フィールド `height₂`。
* 加わった: フィールドはなし。
* `PipeChangeEnd.Entry`（縦の土管の入口）は大きさのビット 1 から 7 も求めます。`Run.entry₁` がそれを証明し、`chg.entryRest₁` は求めません。
* `chg.upCleanU` のガードは大きさのバイトも守ります: 操作から縦の土管までのフレームで、添字やポインタを通した書き込みはこのバイトに書きません。
* `RoomChecks.height : SizeKeep.Facts …`（前は `EntryHeightBig.Facts …`）。

## 仮定（Lean で証明していない）

* 前からあるフィールド: 部屋の各命令の `SiteOK`（`chg.roomSites`）と、守るバイトが 1 つ増えた `chg.upCleanU`。

**ファイル.** `Theorems/SizeKeep.lean`、`Theorems/PipeChangeEnd.lean`、`Theorems/Route.lean`。非公開の確認は `Proof/SizeKeep.lean`（`Main.lean` の `genSizeKeep`）で、`Proof/EntryHeight.lean`（`genEntryHeight`）が使います。

**再現.**
```
.lake/build/bin/smbrta size-keep-check FM2 50 walk     # 2 つの歩き、段、TAS、自分の走り、約 2 分
.lake/build/bin/smbrta entry-walk-check                # EntryKeep の歩き
.lake/build/bin/smbrta pipe-end-check FM2              # 土管のフレームと段、約 5 分
.lake/build/bin/smbrta up-clean-u FM2                  # 本物のフレームでのガード
.lake/build/bin/smbrta size-keep-check FM2 30 mushroom   # キノコを取る自分の走りとガード、約 3 分
```
