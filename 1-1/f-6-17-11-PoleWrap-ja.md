[← Back](README-ja.md) | [English](f-6-17-11-PoleWrap.md) | [Japanese](f-6-17-11-PoleWrap-ja.md)

# 旗のタイル: `TileSlot` は読みの列を 1 つのページでだけ求める、厳しい規則のもとのスクロールのカウンタ

29 回目のラウンドは、パート f にエリアの解析についての 2 つのフィールドを残しました: `tilesCol`（`PoleTileFar.TileSlot`）と `parWrap`（`PoleJoin.NoWrapP`）。このラウンドは `TileSlot` を算術で狭め、`parWrap` をプレイヤーのルーチンに来るフレームだけに求め、`parWrap` が何から出るかを証明します。その最後のものはまだルートでは使いません。

## 言葉

[ルートのフレームの上のエリアの解析](f-6-17-10-PoleParserRun-ja.md) と同じです: `c₀` と `e₀` は触るフレームの始まりの解析の列（1 ページ 16 列）と画面の左の端（px）、`pg` は旗のページ、`colPole = 16·pg + c` は旗の列、`page` は読み込みのすぐあとのマリオのページ、`pix = 256·page + x` はマリオの画素。`N` は解析の残りのタスクの数、`S` は 32 px のスクロールのカウンタ。

## `TileSlot`: 読みの列は旗のページの 2 つ前のページでだけ

`TileSlot` は、`page + 1 < pg` の横の当たり判定の読み込みのすぐあと、旗の列で求めます。3 つの部分がありました。いま 3 つ目は `page + 2 = pg` のときだけ求めます:

```
(slot)  読んだバイト ∈ {ball, shaft}  ⇒  colPole ≤ c₀
(near)  e₀ ≤ pix + 112
(read)  page + 2 = pg  ⇒  ∃ a < 16,  ⌊(pix + a)/16⌋ mod 32 = colPole mod 32
```

前の形は `pg − 2` 以下のどのページでも (read) を求めていました。`tileSlot_of_R`: 前の形から新しい形が出ます。なのでフィールドが求めるものは減りました。`tileCol_of_slot`（いまも算術だけ）は、解析の不変式 `16·c₀ ≤ e₀ + 384` とこれから `TileCol` を出します:

* `page ≤ pg − 3`: `pix ≤ 256·pg − 513` なので、`16·c₀ ≤ e₀ + 384 ≤ pix + 496 ≤ 256·pg − 17 < 16·colPole`。
* `page = pg − 2`: (read) で読みの列 `r = ⌊(pix + a)/16⌋` は旗の列より 32 列以上前なので、`pix ≤ 16·colPole − 497`、`16·c₀ ≤ 16·colPole − 1`。

どちらでも `c₀ < colPole`。なので (slot) で、読んだバイトは旗のタイルではありません。

## `parWrap`: プレイヤーのルーチンに来るフレームだけで

`parWrap` は、触るフレームより前の各フレームの `UpdScrollVar` で、フレームの始まりから左の端が `Y` 動いたら `S + Y < 256` を求めていました。解析の不変式がこれを使うのは、プレイヤーのルーチンに来るフレームだけです: 来ないフレームは解析のバイトと左の端を保ちます（`PoleParser.step_noCut`）。いまフィールドと `PoleParser.inv_onFrames`（その仮定 `hw`）は、そういうフレームにだけこれを求めます:

```
parWrap :  ∀ n, n + 1 < ix(g) → ∀ n₀, pc(trace(all n, n₀)) = PlayerCtrlRoutine（そのフレームで） → ∀ k, pc(trace(all n, k)) = UpdScrollVar（そのフレームで） → NoWrapP(all n, trace(all n, k))
```

前のフィールドから新しいものが出ます。`PoleParserRun.inv_run` は着いたことを渡します。

## 厳しい規則のもとの `parWrap`（`Theorems/PoleWrap.lean`）

`parWrap` は、フレームの始まりから左の端が `Y` 動いたら `S + Y < 256` を求めます。解析の不変式は等式なので `S` を押さえません。`PoleParserEnd` が各フレームについて証明する規則は弱い形です（`RuleW`）: `UpdScrollVar` で画面のバッファの制御バイトが 6 なら、解析はタスクをとばし、そのバイトはそのままで、`S` は `Y` だけ増えます。フレームの終わりまでの歩きはバイトを 1 つずつ追うので、制御バイトでの分かれ道をどちらに行ったかを言いません。

厳しい規則 `Strict(a, b)`: スクロールの処理がカウンタと左の端を同じ `y ≤ 3` だけ動かし、解析の部分は制御バイトが 6 でないとして `Parse` に従う。すると

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32

jv_strict :         JV(a) ∧ Strict(a, b)  ⇒  JV(b)
noWrapP_of :        JV(m) ∧ （u までに左の端が Y ≤ 3 動いた）  ⇒  NoWrapP(m, u)
parWrap_of_strict : JV(all 0) ∧ (∀ n + 1 < ix(g), StrictF(all n, all (n+1))) ∧ （プレイヤーのルーチンに来るフレームの各 UpdScrollVar で Y ≤ 3）  ⇒  parWrap の主張
```

`StrictF(a, b) := Strict(a, b) ∨ b = a`: `UpdScrollVar` に来ないフレーム（ポーズで終わる）はバイトを保ちます。`JV` が保たれるわけ: `N = 0` で `S + y ≥ 32` なら、解析は新しい列を始め、`S + y − 32 < 3`、`N = 7`、そして `3 + 21 < 32`。`N ≥ 1` ならタスクを 1 つ走らせ、`N` は 1 減り、`S` は高々 3 増えます。なのでどのフレームの始まりでも `S < 32`。

これらの定理は証明済みです。ルートはまだ使いません: `parWrap` はフィールドのままです。残るものは下に書きます。（31 回目のラウンド: 厳しい規則を証明し、`parWrap` はなくなりました。ルートはここの `JV` と `s_lt` を使います: [各フレームの厳しい規則](f-6-17-12-PoleStrict-ja.md)。）

## 測ったこと

`pole-keep parser FM2 96`（ネイティブで 1 分 18 秒から 1 分 39 秒、73 MB）。ランは 29 回目と同じ: TAS、TAS のフレーム 900 から 1089 からの自分の乱数入力（96 ラン、半分はスタートあり）、最初の操作からの自分の乱数入力（1300 フレームを 24 ラン、半分はスタートあり）。操作できる状態で始まるどのフレームも調べます。

| | TAS | 乱数 900〜1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 旗の列での遠い読み込み（`TileSlot` を求める） | 101 | 0 | 3,376 |
| そのうち `page + 2 = pg`（いま (read) を求めるのはここだけ） | 26 | 0 | 0 |
| `TileSlot`（30 回目）が偽 | 0 | 0 | 0 |
| 地上で操作できる状態で始まるフレーム | 608 | 14,318 | 25,980 |
| そのうち始まりで `JV` が偽 | 0 | 0 | 0 |
| 地上で `UpdScrollVar` の制御バイトが 6 | 0 | 0 | 0 |
| 地上で `UpdScrollVar` までの左の端の動きの最大 | 3 px | 3 px | 3 px |
| 地上で `Strict` にも従わず、バイトも保たないフレーム（`StrictF` が偽） | 0 | 0 | 0 |

TAS では `UpdScrollVar` で制御バイトが 6 のフレームが 13 あり、すべて地下の部屋のフレームです。コードでは、ブロックのバッファからコインを消すルーチンが制御バイトを 6 にします。地上では一度も 6 になりませんでした。どのフレームも、そこで読んだ制御バイトでの `Parse` に従いました（27 回目の数え、偽 0）。地上では測ったどのフレームも `StrictF` に従いました（じかに数えた）。

## 証明していないこと

* `TileSlot` そのもの: (slot)、(near)、そして旗のページの 2 つ前のページでの (read)。(read) には横の当たり判定のポインタとマリオの画素の関係が要ります。触るフレームの歩きは、旗から遠いところでマリオの画素を知りません（25 回目: そこで和の上の 4 ビットを分けると 5.8 GB を超えた）。(near) には触るフレームでの画面の端の押し戻しの判断（`GetXOffscreenBits`）が要ります。パート e は触る前のフレームで同じ種類のことを仮定しています（`collide`）。(slot) にはフレームをまたいだブロックのバッファの中身が要ります。
* `parWrap`: 操作の始まりでの `JV`、触る前の各フレームが `StrictF` に従うこと、左の端が 1 フレームに高々 3 px 動くこと。`Strict` には、`PoleParserEnd` のフレームの終わりまでの歩きが、制御バイトでの分かれ道と解析のバイトをいっしょに追う必要があります。ブロックのバッファからコインを取ると制御バイトは 6 になるので、`Strict` には地上のどのフレームもコインを取らないことも要ります。
* `bufAll`（7 か所）と `keepB`（66 か所）: このラウンドでは手をつけていません。

**ファイル.** `Theorems/PoleTileFar.lean` の `TileSlot`、`TileSlotR`、`tileSlot_of_R`、`tileCol_of_slot`。`Theorems/PoleJoin.lean` のフィールド `parWrap`、`Theorems/PoleParserEnd.lean` の `inv_onFrames` の `hw` と `Theorems/PoleParserRun.lean` でのその使い方。`Theorems/PoleWrap.lean`（`JV`、`Strict`、`StrictF`、`rule_of_strict`、`jv_strict`、`jv_strictF`、`jv_frames`、`s_lt`、`parS_eq`、`noWrapP_of`、`parWrap_of_strict`）。`Main.lean` の `pole-keep parser` の 30 回目の行。
