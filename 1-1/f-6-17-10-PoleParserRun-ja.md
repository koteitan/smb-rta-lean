[← Back](README-ja.md) | [English](f-6-17-10-PoleParserRun.md) | [Japanese](f-6-17-10-PoleParserRun-ja.md)

# 旗のタイル: ルートのフレームの上のエリアの解析

[エリアの解析と画面の左の端](f-6-17-8-PoleParser-ja.md) と [フレームの後半](f-6-17-9-PoleParserEnd-ja.md) は、操作の始まりの解析の不変式と、どのフレームもそれを保つことを、フレームごとの条件のもとで証明しました。ルートはそれを使っていませんでした。このページは不変式を、旗に触るまでのルートのフレームに持っていき、触るフレームで使います。前のフィールド `tilesCol` は、新しいフィールド `TileSlot` と解析の不変式からの定理になりました。これは前のものより弱くはありません: 旗の列でのどの遠い読みでも (near) と (read) の部分も求めます。前のフィールドは、旗のタイルを読まなければ何も求めませんでした。測った 3,477 回の遠い読みで 3 つの部分はすべて成り立ちました。

## 言葉

`col` はページ込みの解析の列（1 ページ 16 列）、`N` は残りのタスクの数、`p(N) = [N ≥ 1] + [N ≥ 5]`、`S` は 32 px のスクロールのカウンタ、`edge` は画面の左の端（px）。不変式:

```
Inv(L, m)  :=  N ≤ 8  ∧  16·col + 16·p(N) + S = edge + L
```

`colPole = 16·pg + c` は旗の列（ページ `pg`、ページの中の列 `c`）。`pix = 256·page + x` はマリオの画素。

## 各フレームの条件をルートから

`PoleParser.inv_onFrames` は、触るフレームより前の各フレームに次を求めます。

* **添字かポインタを通した書き込みは、解析の 4 つのバイトを書かない。** いま `FrameKeep.guardE` がこれを守ります（`FrameKeep.parE`。解析の場所と同じく `UpdScrollVar` のコードから見つける。`pI_eq`）。なのでフィールド `keep.cleanE` がこれを与えます（`cleanPI_of_E`）。`keep.cleanE` と `chg.upCleanU` は少しだけ多くを求めます: 守るバイトが 4 つ増えた。
* **エリアの種類、泳ぎのフラグ、大きさの変化**: `SurfaceFrames.AreaRun`（`frames.areaRun`）。
* **スクロールの処理からあとの `posW`。** フィールド `frames.posW` は数えるフレームでだけ成り立ちます。触るフレームより前で、プレイヤーのルーチンに来るフレームは数えるフレームです（`counted_of`）。数えないフレームはポーズで終わり、そこに来ません（`OnFrames.lagNo`）。そこに最初に来るのは `CtrlKeep.arrAt` より前ではありません（`arrAt_le`）。なので `posW` が歩きの求めるものを与えます（`cut_of_posW`）。`PoleParser` の歩きは、いまは最初に来たところからだけそれを求めます（`frame_toU`、`rule_frame`、`inv_onFrames`）。
* `UpdScrollVar` での**スクロールの折り返しがないこと**: 新しいフィールド `parWrap`（下）。
* フレームの始まりで**左の端が 64,896 px より下**: 定理です（`edgeLow_run`）。パート e は、触るのが操作から `farN` フレーム以内なら、触る前の各数えるフレーム `d` の終わりで、マリオの位置と左の端の大きい方を `posP(B.m) + 16·top·d`（1/256 px）で押さえます（`OnFrames.readAllB`。もっと遅い触りは `SurfaceLate`）。数えないフレームは左の端のバイトを保ちます（`lag_edge`）。ROM の上の 1 つの数で閉じます: `posP(B.m) + 16·top·farN < 64896·256`（ルートの非公開の証明でネイティブに確かめる）。

`noWrap_of` は `parWrap` と左の端の評価から `PoleParser.NoWrap` を作ります。

操作の始まりでは、`L = 384` の不変式と 16 より下の列が、横の土管から出る切り替えの行から来ます（`PoleParser.inv₀`、`PoleParser.col₀`）。なので:

```
inv_run :  ∀ n < ix(g),  Inv(384, all n) ∧ col_in_page(all n) < 16
```

触るフレームまでのどのフレームの始まりでも、数えるかどうかにかかわらず成り立ちます。`col_le` で、触るフレームの始まりで:

```
16·col ≤ edge + 384
```

## 触るフレーム: `TileSlot` から `TileCol`

前のフィールド `tilesCol` は、ルーチンを書くまで `TileCol` を求めていました: マリオのページが旗のページより 2 つ以上前の横の当たり判定の読み込みのすぐあと、旗の列では、読んだバイトは旗のタイルではない。いまこれは定理です（`tilesCol_run`、ルートでは `tilesCol_route`）。不変式と、新しい 1 つの状態の条件 `TileSlot`（`PoleTileFar.TileSlot`）から出ます。`c₀` と `e₀` を触るフレームの始まりの解析の列と左の端として、そういう読み込みのすぐあとで:

```
(slot)  読んだバイト ∈ {ball, shaft}  ⇒  colPole ≤ c₀
(near)  e₀ ≤ pix + 112
(read)  ∃ a < 16,  ⌊(pix + a)/16⌋ mod 32 = colPole mod 32
```

`tileCol_of_slot` は算術です。旗のタイルを読んだとすると `16·colPole ≤ 16·c₀ ≤ e₀ + 384 ≤ pix + 496`。マリオのページは `pg − 2` 以下なので、読み込みの列 `r = ⌊(pix + a)/16⌋` は `16·pg − 16` 以下で、`colPole` より下です。それは mod 32 で `colPole` なので `r ≤ colPole − 32`、そして `pix < 16·(r + 1) ≤ 16·colPole − 496`。2 つの評価は両立しません。

つまり解析は左の端より高々 24 列先にあり、マリオが旗より 32 列以上前を読むあいだ、旗の列には来ていません。

30 回目のラウンド: (`read`) は、マリオのページが旗のページのちょうど 2 つ前のときだけ求めます。3 つ以上前なら (`near`) だけで足ります（[`TileSlot` を 1 つのページだけで、厳しい規則のもとのスクロールのカウンタ](f-6-17-11-PoleWrap-ja.md)）。

## フィールド

| フィールド | 前 | いま |
|---|---|---|
| `tilesCol` | 書くまでの各状態で `TileCol` | フレームの始まりの解析の列と左の端での `TileSlot` |
| `parWrap`（新しい） | — | 触るフレームより前の各フレーム、`UpdScrollVar` で: 左の端が `Y` 動いたら `S + Y < 256`（`PoleJoin.NoWrapP`） |
| `keep.cleanE` | `guardE` の `CleanK` | 同じ。`guardE` は解析の 4 つのバイトも守る |

`Run.inRange`、`touch_ge`、`direct_castle`、`castle_ge`、`touch_castle` は `hgN` のあとに `(hT : R.TileColAll)`（前のフィールドの主張）を取ります。ルートの非公開の証明が、触るのが操作から `farN` フレーム以内の場合に、`tilesCol_route` でそれを与えます。`tilesCol_route` は解析の確かめ（`pole_parser_rows`、`pole_parser_col`、`pole_parser_q`、`pole_parser_e`、`pole_parser_s`）、操作の始まりのエリアの種類 1、左の端の評価の数を求めます（後の 2 つはルートの非公開の証明でネイティブに）。

## 測ったこと

`pole-keep parser FM2 96`（ネイティブで 1 分 53 秒、71 MB）。ランは TAS、TAS のフレーム 900 から 1089 からの自分の乱数入力（96 ラン、半分はスタートあり）、最初の操作からの自分の乱数入力（1300 フレームを 24 ラン、半分はスタートあり）。触るフレームだけでなく、操作できる状態で始まるどのフレームも調べます:

| | TAS | 乱数 900〜1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 旗の列での遠い読み込み（`TileSlot` を求める） | 101 | 0 | 3,376 |
| `TileSlot` が偽 | 0 | 0 | 0 |
| 横の読み込みでの `pix − e₀` の最小（−112 以上を求める） | 23 px | 0 px | 0 px |
| `UpdScrollVar` に来た回数（`parWrap` を求める） | 719 | 10,086 | 18,682 |
| `NoWrapP` が偽 | 0 | 0 | 0 |
| フレームの始まりの左の端の最大（いまは定理: 64,896 px より下） | 3,046 px | 3,055 px | 616 px |

28 回目の `N = 400` の測りでも、解析のバイトへの添字かポインタを通した書き込みはありませんでした。大きくなった `guardE` が求めるのはこれです。解析のバイトを入れた `guardE`（74 バイト、前は 70。`chg.upCleanU` の合わせたガードは 151 バイト）で:

* `keep-frames-check FM2 100`（`keep.cleanE` と地上のフレームのほかの条件）: TAS と自分のラン（ポーズあり、なし）の 224,813 フレームで bad 0。
* `up-clean-u FM2`（`chg.upCleanU`、フレーム 1 から縦の土管に入るまで）: 221,490 フレームで、合わせたガードに反するものは 0。

## 証明していないこと

* `TileSlot` そのもの: (`slot`) 解析は旗の列に来てから旗のタイルを書く。(`near`) マリオは左の端よりずっと左にはいない。(`read`) 読み込みの列はマリオの画素に足す数を足した列。本物のランでは、旗の列での遠い読み込みが旗のタイルを読むことはないので、(`slot`) はそこでは使われません。33 回目のラウンド: (`slot`) は触るフレームの歩きの定理になり、代わりに `bufAll` が多く求めます。(`near`) と (`read`) は、もっと弱い `PoleSlot.TileSlotC`（解析の列が旗の列まで来ていない）に置きかえました（[エリアの解析の場所は定理になった](f-6-17-14-PoleSlot-ja.md)）。
* `parWrap`（上で測った）。解析はフレームによってはタスクをとばすので（制御バイト 6）、弱い決まりは `S` を押さえません。30 回目のラウンド: プレイヤーのルーチンに来るフレームにだけ求めます。各フレームの厳しい規則から出ます（[f-6-17-11](f-6-17-11-PoleWrap-ja.md)）。31 回目のラウンド: `parWrap` はなくなりました。厳しい規則を証明し、`invJ_run` が、新しいフィールド `ctlU`（`UpdScrollVar` で制御バイトが 6 でない）、スクロールの量が高々 3 であること（定理 `amount_run`）、操作の始まりでの `JV` から、不変式を `JV` といっしょに運びます（[f-6-17-12](f-6-17-12-PoleStrict-ja.md)）。
* `bufAll`（7 か所）と `keepB`（66 か所）: このラウンドでは手をつけていません。

**ファイル.** `Theorems/PoleParserRun.lean`（`edgeLow_run`、`lag_edge`、`surf_edge` も）。`Theorems/FrameKeep.lean` の `FrameKeep.parRt`、`FrameKeep.parE`、`guardE`。`Theorems/PoleTileFar.lean` の `TileSlot`、`tileCol_of_slot`。`Theorems/PoleJoin.lean` のフィールドと `parColOf`、`parSOf`、`NoWrapP`、`Run.TileColAll`。`PoleParser.lean` と `PoleParserEnd.lean` の最初に来たところからの `hp`。`Main.lean` の非公開の Route の部分と `pole-keep parser` の 29 回目の行。
