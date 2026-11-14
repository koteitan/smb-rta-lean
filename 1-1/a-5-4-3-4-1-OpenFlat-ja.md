[← Back](README-ja.md) | [English](a-5-4-3-4-1-OpenFlat.md) | [Japanese](a-5-4-3-4-1-OpenFlat-ja.md)

# 出だしの平らな地面

**主張.** 最初の `N` 個の数えるフレーム（`N = 32`）で、地面の上の地面の高さで始まり、プレイヤーのルーチンがジャンプを読まないフレームのあとの数えるフレームは、
地面の上の地面の高さで始まります。なので [本物のフレームでの出だし](a-5-4-OpenFrames-ja.md) のフィールド `flat` は仮定ではありません（`Real.flat`）。フィールド
`ground` も仮定ではありません: 数えるフレームについての帰納法で、地面の上で始まるどの数えるフレームも地面の高さで始まります（`Real.ground_all`）。着地のあとは
[出だしのジャンプ](a-5-7-OpenJump-ja.md) から出ます（`Real.jumpV`）。
このために、当たり判定のルーチンから戻るところまでの歩きはそこで縦のバイトを確かめます。そして 1 フレームごとの新しい条件を 1 つ求めます（`afterV`）: そこから
フレームの終わりまで、高さ、その上位バイト、縦の速さ、その端数は変わらない。ブロックバッファのルーチンの読み出しは最初のブロックバッファの中にある、とも
求めます（`map`、`MapOK.read`）。`map` は数えるフレーム `N` のフレームまで含みます。

`fm(t)` は数えるフレーム `t` が始まるときの機械、`b(t)` はその終わり、`tr(t, k)` はその `k` 命令あとの機械、`n₀(t)` はプレイヤーのルーチンに最初に着くところ、
`in(t) = readIn(tr(t, n₀(t)))` はそのルーチンが読む入力です。`st(m)` はプレイヤーの状態、`y(m)` は高さ、`hi(m)` はその上位バイト、`vy(m)` は縦の速さ、
`mf(m)` はその端数、`js(m)` はジャンプ台のバイト、`V(m) = (y, hi, vy, mf)` です。`R` はブロックバッファのルーチンの読み出し（`LDA (zp),Y`）、`addr(m)` は
それが読む番地です。`Q` はプレイヤーのルーチンの中で当たり判定のルーチンから戻るところです。`flat(t) := st(fm t) = 0 ∧ ¬jump(in t)` です。

```
GroundAt(m)  :=  y(m) = y(m₀)  ∧  hi(m) = 1  ∧  vy(m) = 0  ∧  mf(m) = 0
RdOK1(m)     :=  pc(m) = R  ∧  NMI が来ない   →   addr(m) は最初のブロックバッファの中  ∧  m(addr(m)) = m₀(addr(m))
AfterV(t)    :=  ∀ k ≥ n₀(t),  pc(tr(t, k)) = Q   →   V(b t) = V(tr(t, k))
fin(B)       :=  st(B) = 0   ∨   out(B)            out(B) := ルーチン、タスク、モードのどれかが操作のときのものでないと分かる

flat_end      :  ctrlCheck,  flatCheck,  StartK(m),  ∀ k: CleanK_K(tr k) ∧ CleanK_Q(tr k),  フレームの中の ∀ k: RdOK1(tr k),
                 frame(m, i) はポーズでなく終わる,  AreaOK(m),  st(m) = 0,  GroundAt(m),  js(m) = 0,  ¬jump(readIn(tr n₀)),  AfterV
                 →   ∃ B,  fin(B)  ∧  B が frame(m, i) を覆う  ∧  (out(B)  ∨  GroundAt(frame(m, i)))
map_reads     :  map_frame（OpenMap）の条件   →   フレームの中で NMI が来ない各読み出し R で、ブロックバッファは m₀ のもの
Real.flat     :  確認,  Real,  t ∈ [1, N],  t < E,  Held(fm t),  js(fm t) = 0,  flat(t),  GroundAt(fm t)   →   st(fm(t + 1)) = 0  ∧  GroundAt(fm(t + 1))
Real.ground_all : 確認,  Real,  各数えるフレームで Held、js = 0、|v| ≤ top,  st(fm 1) = 0,  GroundAt(fm 1)
                 →   ∀ t ∈ [1, N],  t < E,   st(fm t) = 0  →  GroundAt(fm t)                                     （前のフィールド ground）

フィールド afterV :  ∀ t ∈ [1, N],  t < E,   AfterV(t)                                                            （新しい）
フィールド map    :  ∀ n,  1 ≤ n ≤ ix(N),  n < ix(E),  ∀ k:  MapOK(tr_n(k))
```

`CleanK_K` は `FrameKeep.guardK` の `CleanK`、`CleanK_Q` はプレイヤーの状態、ジャンプ台のバイト、`CtrlKeep.spareI` のバイトを保護したガードの `CleanK` です。
どちらもフィールド `cleanK` と `MapOK` の書き込みから出ます（`cleanQ_of`）。`RdOK1` は `MapOK` の読み出しと [OpenMap](a-5-4-3-3-3-OpenMap-ja.md) の歩きから出ます
（`rdOK1_of`、`map_reads`）。`GroundAt(fm 1)` はタイトルで Start を押したところから出ます: `title_pos_check` は操作のときの `V` の 4 バイトも `m₀` の値かを確かめ、
`m₀` は地面の高さにいて（`Checks.start`）、数えるフレーム 1 の前のフレームは `V` を変えません（`LagFrames.lagI` にこの 4 バイトが入りました。歩きは 21 個）。
数えるフレームのあいだの数えないフレームも `V` を変えません（`lags_keepI`）。ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。
`#print axioms route_1_1` に `sorryAx` はありません。

Lean: `Theorems/OpenFlat.lean`（`AfterV`、`vertA`、`groundOK`、`finX`、`flat_end`）。`Theorems/OpenFrames.lean` の `Real.flat`、`Real.ground_all`、フィールド
`Real.afterV`、`Real.map`、`Checks.flat`。`LagFrames.moreI`、`StartRun.stI`。`Theorems/Route.lean` の `Run.pipeHeld`。`Theorems/OpenMap.lean` の
`OpenMap.map_reads`、`OpenMap.liveT_all`、`OpenMap.bufI1`。非公開の `Proof/OpenFlat.lean`（`open_flat_check`）。

## しくみ

3 つの歩きが、順にフレームを覆います。

* **プレイヤーのルーチンまで.** `CtrlKeep` のポーズのビットの歩きは、プレイヤーのルーチンに最初に着いたところで止まります（`CtrlKeep.cut_or_end2`）。そこで
  `CtrlKeep.keepA` のバイトはフレームの始めのものと同じです（`CtrlKeep.ctrl_keep`）: 状態、高さ、縦の速さとその端数、ジャンプ台のバイト、エリアのバイトです。
  `CtrlKeep` の歩きをもう 1 つ使って、高さの上位バイトも追います（`high_at_cut`）。フレームの始まりの `GroundAt`（`Real.ground_all`）とあわせて、切ったあとの歩きはこれらのバイトを知って始まります。
  ルーチンが読むジャンプ `jump = (st = 0 ∧ A を押した ∧ 前のフレームで A を押していない)` は偽なので、2 つの場合のどちらかです: ジョイパッドのビットのビット 7 が 0、
  またはそれが 1 で前のフレームの A のビット 7 が 1。それぞれの場合を切ったところで決めます。
* **当たり判定のルーチンから戻るところまで.** 歩きは `FrameKeep` のものですが、ブロックバッファのルーチンの読み出しだけ違います（`fstep`）。そこで歩きは、
  番地の分かっているビットが許すタイルごとに 1 本の道をたどります。ポインタの 2 バイトと `Y` が番地を決め、タイルはそこの `m₀` の最初のブロックバッファのものです
  （`tilesAt`、`RdOK1` を使う）。ポインタを作るルーチンでは `Y`（バッファの番号）を 2 つの値に分けるので（`yPieces`）、ポインタの上位ビットが分かります。高さが
  分かるので、各読み出しの行が分かります。地面の上では足は地面の行を読み、頭と横は空の行を読むので、もう一度着地します: どの道でも `Q` で状態は 0 で、
  `V` の 4 バイトは `GroundAt` の値で分かっています（`groundOK`。`walkQ`、`to_stop`）。`Q` の前にフレームを終える道は、操作できない状態で終わります（`finX`）。
* **`Q` からフレームの終わりまで.** 状態とジャンプ台のバイトを保護した `FrameKeep` の歩きです（`after_endK`）。`Q` のあとのコードが状態を変えるのは、0 にするとき
  （乗れる台）か、操作できない状態にするとき（けが）だけです。

なのでフレームは状態 0 か、操作できない状態で終わります。フレームは操作できる状態で終わるので（`Lags.known_end`）、状態は 0 です。`Q` からあと `V` は
変わらないので（`afterV`）、フレームは地面の高さで終わります。数えないフレームは状態と `V` を変えません（`lags_keepI`）。

**`afterV` を仮定する理由.** `V` の 4 バイトを忘れない `Q` のあとの探索（証明の一部ではない。`open-ground-exp`）は 100 回フレームを終えます。そのうち 76 回で
状態は 0 と分かり、その 74 回で高さは分かりません。4 バイトは 26 の命令で失われます。どれも、歩きが添字を知らない添字つきの書き込みです（`STA abs,X`、
`DEC zp,X`、`STA abs,Y` など）。このような書き込みは、ガードが保護するバイトのほかをすべて忘れます。また敵のコードは、状態を 0 のまま、縦の速さを番地で書きます
（踏みつけ: `ChkForPlayerInjury`、`EnemyStomped`）。歩きは敵を知らないので、これを除けません。出だしの本物のフレームでは近くに敵はなく、`afterV` は成り立ちます。
これはフィールド `after` の縦の半分です。

`Q` までの探索は RAM のどのバイトも忘れません。その鍵は、境界の箱のルーチンでは添字のレジスタを、ポインタを作るルーチンでは `A`、`Y`、一時バイトを含みます。
探索は証明の一部ではありません。これがないと探索は大きいマリオと小さいマリオの道を合わせてしまい、`Q` の 18 の状態のうち 8 が地面の上にありませんでした。
プレイヤーのルーチンからフレームの終わりまでを 1 つの歩きにすると、うまくいきません: 出だしでは走らないコード（ファイアフラワーの火の玉、敵）を通る道を合わせて
高さを忘れ、731,297 の状態まで増えて失敗しました。

| 歩き | 段 | 表 | 時間 |
|---|---|---|---|
| `Q` まで | 4,345 | 132 | 探索 0.6 秒。`Q` の 6 つの状態はどれも状態 0 |
| `Q` からフレームの終わりまで | 443,885 | 30,659 | 探索 1.0 秒、確認 0.5 秒 |
| `flatCheck`（ポーズのビットの歩きと上位バイトの歩きを含む） | | | ネイティブで 3.0 秒。非公開の証明は 3.3 秒 |

## 本物のフレームでの確認

* `open-real-check FM2 300`: TAS（数えるフレーム 32）、自分の入力（9,600）、最初のフレームでポーズする走り（1,856）で、どの数えるフレームも `afterV` を
  満たします（失敗 0。どれも `Q` に来ます）。地面の上で始まるどの数えるフレームも `GroundAt` を満たします（失敗 0。そのうち着地のあとは
  1 + 294 + 58 = 353 フレーム）。前のフィールド `flat` も成り立ちます（失敗 0）。TAS では操作のときの `V` の 4 バイトは `m₀` のものです。
* `lag-check FM2`: 数えないフレームの 21 の歩き（`V` の新しい 4 バイトを含む）はどれも成功します。ネイティブで 1 つ約 0.3 秒です。
* `open-map-check FM2 300`: 27,261 フレーム、74,386,942 命令、ブロックバッファのルーチンの読み出し 82,929 回で、どの命令も読み出しを最初のバッファにした
  `MapOK` を満たします（失敗 0）。地面の上で始まるどのフレームも `GroundAt` を満たします。

## 仮定（Lean で証明していないもの）

* **`afterV`**（新しい）: 当たり判定のルーチンから戻るところからフレームの終わりまで、`V` の 4 バイトは変わらない。1 フレームごとの条件で、`after` の縦の半分です。
* **`map`**: ブロックバッファのルーチンの読み出しは最初のバッファの中にある（ページ 0 にいる）。`map` は数えるフレーム `N` のフレームも含む。
* **もう仮定でないもの**: `flat`、`ground`（着地のあとは [出だしのジャンプ](a-5-7-OpenJump-ja.md) のフィールド `vert` から出ます）。

**ファイル.** `Theorems/OpenFlat.lean`、`Theorems/OpenFrames.lean`、`Theorems/OpenMap.lean`、`Theorems/LagFrames.lean`、`Theorems/StartRun.lean`、
`Theorems/Route.lean`、非公開の `Proof/OpenFlat.lean`。

**再現.**
```
.lake/build/bin/smbrta open-flat-check                  # 歩きの探索と確認（約 6 秒）
.lake/build/bin/smbrta open-real-check FM2 300          # 本物のフレームでの afterV、ground、flat（約 1 分）
.lake/build/bin/smbrta open-map-check FM2 300           # 本物のフレームでの、読み出しを最初のバッファにした MapOK と GroundAt（約 30 秒）
.lake/build/bin/smbrta open-ground-exp                  # タイトルの確認。EXP_ALL=1 で V を忘れない Q のあとの探索も（約 2 分）
```
