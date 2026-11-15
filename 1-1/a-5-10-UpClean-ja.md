[← Back](README-ja.md) | [English](a-5-10-UpClean.md) | [Japanese](a-5-10-UpClean-ja.md)

# 土管までの各命令に 1 つの条件

**主張.** 操作から縦の土管に入るまでのフレームの命令についての 4 つの条件は、`Route.Run` のフィールドでした。これらは 1 つのフィールド `chg.upCleanU` から出ます。
`1 ≤ n < a₁` の各フレーム `n` の各命令が、4 つのガードを合わせた 1 つのガード `GU` の `CleanK` を満たす、という条件です。

`a₁` は 1 回目の切り替えの入口です。フレーム 1 から先で、操作できない状態で始まる最初のフレームです（`Route.Base.a₁`）。`q` は移動のルーチンが端数を書く場所です
（`FrameKeep.spotOf`）。`tr(n, j)` は走りのフレーム `n` の `j` 命令あとの機械です。

```
GU        :=  PipeWrites のガードで  prot(GU) = prot(EntryKeep.guardOf) ++ prot(LagPause.guardP p) ++ prot(FrameKeep.guardE)
              p = NMI が調べるポーズのバイト（CtrlKeep.pauseI）
upCleanU  :   ∀ n,  1 ≤ n < a₁  →  ∀ j,  CleanK(GU, q, tr(n, j))
```

`CleanK(G, q, m)` は `Clean(G, m)` ですが、`q` で添字 `X = 0` の書き込みは求めません。`qCheck` は ROM の確認です。`q` の命令は `STA abs,X` で、`X = 0` での
行き先は RAM のバイトで、`EntryKeep` のガードはそれを守らず、それは `p` ではありません。`qCheck` は `EntryKeep.Checks` の確認の 1 つです
（フィールド `q`。非公開の `up_q_check`）。なので `hK` を受け取る定理はどれもこれを持っています。

これから（`Route.lean`、`UpClean.lean`）:

```
Run.upClean₁   :  ∀ n, 1 ≤ n < a₁ → ∀ j,  Clean(EntryKeep.guardOf, tr(n, j))                       前のフィールド chg.upClean₁
Run.entryIx    :  ix(E) < a₁                                                                   入るフレームは a₁ より前
Run.lagsClean  :  ∀ n, 1 ≤ n < ix(E) → ∀ k,  Clean(LagPause.guardP g, tr(n, k))                  前のフィールド pipe.lags.clean
Run.pipeClean  :  ∀ j,  Clean(PipeWrites.guardOf, tr(ix(E), j))                                  前のフィールド pipe.clean
Run.pipeReal   :  ∀ t, 1 ≤ t ≤ N, t < E → ∀ k,  CleanK(guardE, q, tr(ix(t), k))                 前のフィールド pipe.opening.cleanK
```

`E` は `pipe.E`（数えたときの入るフレーム）、`ix(t)` は数えるフレーム `t` が始まる走りのフレームです。`g` は `pipe` のポーズのバイトで、`hg : p = g` は出だしの
確認のフィールドです（`OpenFrames.Checks.pause`）。

Lean: `Theorems/UpClean.lean`（`guardU`、`at_q`、`clean_of_U`、`cleanE_of_U`、`upClean₁_of`。`qCheck` は `Theorems/EntryKeep.lean` にある）、`Theorems/StepPrg.lean`（`step_prg`、`trace_prg`、
`run_prg`）、`Theorems/Route.lean`（`Run.prg₁`、`Run.upClean₁`、`Run.entryIx`、`Run.lagsClean`、`Run.pipeClean`、`Run.pipeReal`）、非公開の `Proof/UpClean.lean`
（`up_q_check`。`native_decide`、1 秒かからない）。

## しくみ

* **守るバイトのほかは同じガード.** 4 つのガードは、`PipeWrites` のガードに守るバイトを足したものです。アイドルループ、`late`、ジャンプの表は同じです
  （`UpClean.SameW`）。なので `GU` の `CleanK` からそれぞれの `CleanK` が出ます（`UpClean.cleanK_sub`。`FrameKeep.cleanK_sub` から）。これでもう前の
  `opening.cleanK` です（`cleanE_of_U`）。
* **移動のルーチンの書き込み.** 3 つのガードは `Clean` を求めます。`CleanK` は、`q` で `X = 0` のところのほかは `Clean` です（`FrameKeep.clean_of`）。`q` で
  `X = 0` のとき、機械は ROM のプログラムを動かしているので、命令は `STA abs,X` で、行き先は `tq`（ROM で `q` のあとの 2 バイト）です（`at_q`）。`qCheck` は、
  `tq` が 3 つのガードのどれも守らない RAM のバイトだと言います。なのでこの書き込みはどのガードにも `Plain` です（`clean_of_U`）。この書き込みはプレイヤーの
  端数を書きます。`guardE` はそれを守り、ほかの 3 つは守りません。
* **機械は ROM のプログラムを動かす.** CPU のどの 1 歩もプログラムとそのマスクを変えません（`StepPrg.step_prg`）。CPU の各部分と、`opTable` の 256 の各項目に
  ついて証明しました。`StepWrites` が RAM についてしたのと同じやり方です。なのでフレームのあいだ（`trace_prg`）も走りのあいだ（`run_prg`）も、プログラムは
  フレーム 1 のものです。フレーム 1 は、タイトルで Start を押したところから、ROM のプログラムでアイドルループで始まります（`Run.prg₁`）。
* **フレームは同じ**（`Run.entryIx`）. 4 つの条件は `pipe` の入るフレーム `ix(E)` までのフレームについてです。`a₁ ≤ ix(E)` なら、フレーム `a₁ − 1` を見ます。
  それはフレーム 0 か、`E` より前の `pipe` の数えるフレームか、そのあいだの数えないフレームです。フレーム 0 は操作できる状態で終わります（`title`）。数える
  フレームも操作できる状態で終わります（`lags.ctl`）。数えないフレームはポーズで終わるので、モードのルーチンを呼ばず、ルーチンを変えません（`Lags.known_end`）。
  そのためにそれは操作できる状態で始まり（`Run.upStart₁`）、その命令はポーズのバイトも守る `Clean` です（`a₁ − 1 < a₁` なので `upCleanU` から）。なので
  フレーム `a₁` は操作のルーチンで始まります。でもそれは土管のルーチンで始まります: ルーチンのバイトは `entryRest₁` のバイトで、入口の手本はそこに土管の
  ルーチンを持ちます（`EntryKeep` のリストの確認）。2 つのルーチンは違います。なので `ix(E) < a₁` です。`a₁` の定義とあわせると `ix(E) + 1 = a₁` です。
  使うのは上限だけです。
* **`if` はなくなりました（15 回目）.** 14 回目のフィールドは、`qCheck` が成り立てば `CleanK(GU, q)`、成り立たなければ `Clean(GU)` でした。`Run.upStart₁` と
  `Run.entry₁` が確認 `hB` と `hK` だけを受け取り、ほかのパートの 20 ほどの定理がそれを使うからです。今は `qCheck` が `EntryKeep.Checks` のフィールドなので、
  `hK` がそれを運び、フィールドはただの `CleanK` です。

## 本物のフレームで測ったこと

`up-clean-u FM2`（exit 0）は、`up-clean-union`（パート b、13 回目）の走りを、Lean の文の `GU` で動かします。もう一度、この回のパート e の新しいバイト
（速さ、`FrameKeep.guardE` の `speedE`）を足したガード（合わせたガード）でも動かします。

| 走り | フレーム（ポーズ） | 命令 | `upCleanU` に反する | 合わせたガードに反する | `q` で `X = 0` の書き込み（`EntryKeep` と `guardP` に `Plain`） |
|---|---|---|---|---|---|
| TAS、入るまでの 368 フレーム | 368 (0) | 1,917,255 | 0 | 0 | 368 (368) |
| 入口の手本 | 440 (0) | 2,256,005 | 0 | 0 | 440 (440) |
| 操作からの 300 のでたらめな走り | 127,841 (5,390) | 530,759,258 | 0 | 0 | 122,439 (122,439) |
| TAS のフレームからの 300 のでたらめな走り | 75,241 (4,746) | 353,240,139 | 0 | 0 | 70,476 (70,476) |
| 手本に 0 から 39 フレームの立ち止まりを入れたもの | 17,600 (0) | 90,225,074 | 0 | 0 | 17,600 (17,600) |
| 合計 | 221,490 (10,136) | 978,397,731 | 0 | 0 | 211,323 (211,323) |

`qCheck` は true です。前の 4 つの条件もどれも成り立ちます。`guardE` の `CleanK` は、数えるフレーム 1 から 32 だけでなく、どのフレームでも成り立ちます。
40 の走りが土管に入ります。走らせるのに 14 分ほどかかります。

## 合わせた条件が 4 つより多く求めること

前の 4 つの条件が求めたこと:

| フィールド | ガード | フレーム |
|---|---|---|
| `chg.upClean₁` | `EntryKeep.guardOf`（124 バイト） | `1 ≤ n < a₁` |
| `pipe.lags.clean` | `LagPause.guardP`（48 バイト） | `1 ≤ n < ix(E)` |
| `pipe.clean` | `PipeWrites.guardOf` | 入るフレーム `ix(E)` の書き込みまで |
| `pipe.opening.cleanK` | `FrameKeep.guardE`（67 バイト）、`CleanK` | 数えるフレーム 1 から 32 |

`GU` は 143 バイトを守ります。`EntryKeep` のガードの 125 バイト（15 回目からレベルの番号を含む）と、ほかの 2 つが守らない `guardE` の 18 バイトです。`EntryKeep` のガードは `guardP` のポーズのバイト（同じバイト）をもう守るので、入るフレームでも
新しいことはありません。新しいのは次のことです: **`EntryKeep` のガードも `guardP` も守らない `guardE` の 18 バイトを、添字やポインタを通った書き込みが書かない**
（A と B、前のフレームの A と B、動く向き、走る速さ、覚えている速さ `|v|`、当たりのビット、泳ぎのフラグ、大きさの変化、城の旗、プレイヤーの端数（`q` で `X = 0`
のところを除く）。14 回目と 15 回目から、速さ、ジャンプの 3 バイト、プレイヤーの状態、縦の力、向き、サブ速さ）。**それを、数えるフレーム 1 から 32 でないフレームで求めます**: 数えるフレーム 32 より前の数えないフレームと、
そのあと入るまでのすべてのフレームです。`q` で `X = 0` のところでは、合わせた条件は `upClean₁` より求めることが少ないです（何も求めません）。この ROM では
その書き込みは `EntryKeep` のガードに `Plain` なので（`qCheck`）、同じです。

## 前提（Lean では証明していない）

* **`chg.upCleanU`**: 操作から入るまでのフレームの各命令についての上の条件。`chg.upClean₁`、`pipe.lags.clean`、`pipe.clean`、`pipe.opening.cleanK` のかわりです。
  ガードが守るバイトの場所を埋める走り（敵の場所 3 と 6、火の玉、ブロック 2 と 3、そのほかの物、大砲、いくつかの点数: パート b の一覧）は、前と同じく定理の外です。
* いま証明したこと: 移動のルーチンの書き込みは `Clean` の 3 つのガードに `Plain`（`qCheck`、ROM から）。4 つの条件は `a₁` より前のフレームについてのもの
  （`Run.entryIx`）。
* 証明していないこと: 書き込みの添字について何も。`upCleanU` は、前の 4 つと同じく各命令についての条件です。

**ファイル.** `Theorems/UpClean.lean`、`Theorems/StepPrg.lean`、`Theorems/Route.lean`、`Theorems/PipeFrames.lean`（`Lags.CleanP`）、`Theorems/OpenFrames.lean`
（`RealB`、`Real`）、`Theorems/HurryStart.lean`（`Chg₁.upCleanU`）、非公開の `Proof/UpClean.lean`。

**再現.**
```
cd git
.lake/build/bin/smbrta up-clean-u FM2 quick    # ガードと qCheck
.lake/build/bin/smbrta up-clean-u FM2          # 走り（数分）
```
