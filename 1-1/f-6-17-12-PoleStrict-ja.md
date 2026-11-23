[← Back](README-ja.md) | [English](f-6-17-12-PoleStrict.md) | [Japanese](f-6-17-12-PoleStrict-ja.md)

# 旗のタイル: 各フレームの厳しい規則、`parWrap` はなくなった

30 回目のラウンドはフィールド `parWrap` を残しました（[`TileSlot` を 1 つのページで、厳しい規則のもとのスクロールのカウンタ](f-6-17-11-PoleWrap-ja.md)）。これは、触るフレームより前の、プレイヤーのルーチンに来る各フレームの `UpdScrollVar` で、フレームの始まりの 32 px のスクロールのカウンタと左の端の動きの和が 256 より小さいことを求めていました。カウンタはラン全体を通して持ち越される値なので、このフィールドはランについての事実でした。30 回目のラウンドは、これが各フレームの厳しい規則、操作の始まりでの `JV`、高々 3 px の動きから出ることを示しました。

このラウンドは、実際のフレームで厳しい規則を証明し、操作の始まりでの `JV` と高々 3 px の動きも証明します。ルートの上のエリアの解析の不変式は、もう `parWrap` を使いません。代わりに、フレームの 1 つの状態についての条件であるフィールドが 1 つあります: `UpdScrollVar` で画面のバッファの制御バイトが 6 でないこと。

## 言葉

`N` はエリアの解析の残りのタスクの数、`S` は 32 px のスクロールのカウンタ、`col` は解析の列、`edge` は画面の左の端（px）。`ctl` は画面のバッファの制御バイト。`X` はスクロールの量: 移動がスクロールのために書くバイトと、台がスクロールに加える力の和（mod 256、`ScrollRule.amountOf`）。`m` からのフレームについて、`n₀` はプレイヤーのルーチンに最初に着いたところ、`kq` はプレイヤーのサブルーチンの呼び出し（`PlayerSubs`、ここでスクロールの処理を呼ぶ）、`k₂` はスクロールの処理のあとの `UpdScrollVar`、`Y` はフレームの始まりから `k₂` までの左の端の動き、`e` はフレームの終わり。

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32
```

## 制御バイトを使う歩き（`Theorems/PoleParserEnd.lean`）

`UpdScrollVar` は、まず `ctl` を 6 と比べ、6 なら抜けます。28 回目のラウンドの歩きは `UpdScrollVar` で `ctl` を知りません（測った: そこでの歩きの 1 つの状態は、そのどのビットも知らない）。なので両方の道を行き、弱い規則（バイトを保つか、タスクを 1 つ）しか出しません。

いま、`UpdScrollVar` での歩きの状態を 8 つの切れにも分けます: 切れ `j` では `ctl` のビット `j` を知っていて、6 のそのビットと違います（`ctlPats`、`pats6`）。6 でないどのバイトもどれかの切れに入ります（`pats6_cover`、256 のバイトについての `decide`）。切れの中では比べた結果が決まります。各切れから、表のない歩きが分かれ道のあとの命令（`qN`）まで行きます。その歩きはフレームを終えてはいけません。そこから:

* `N` = `w` が 1 ‥ 8 なら、自分の表（826 の状態）を持つ歩きがフレームの終わりまで行き、`N = w − 1` を求めます（`finS`、`csOf`、`atSN`）;
* `N` = 0 なら、カウンタ `s` で分け、`s` が 32 ‥ 159 のとき、歩きはタスクの処理の呼び出しに来なければならず、そこで 28 回目の歩きが残りを求めます（`atSZ`）。

これらの歩きはチェック `eCheckP` の一部です（`atES = atE && atS`）。なので `keep_eP` と `frame_six` は事実を 2 つ多く出します:

```
ctl(k₂) ≠ 6  ∧  N ∈ {1, …, 8}                     ⇒  N(e) = N − 1
ctl(k₂) ≠ 6  ∧  N = 0  ∧  32 ≤ S(k₂) < 160          ⇒  N(e) = 7  ∧  S(e) = S(k₂) − 32
```

`frame_sixA` は、同じスクロールの処理の呼び出しで、スクロールの規則を加えます（`ScrollRule.scroll_call`、チェック `ScrollRule.check`）: 呼び出しは 1 度だけ戻る（`EdgeStep` の歩き）ので

```
Y = 0   ∨   (1 ≤ X(kq) ≤ 128  ∧  Y ≤ X(kq))
```

## 厳しい規則と `JV`（`Theorems/PoleStrict.lean`）

`step_strict`: 操作できる状態でプレイヤーのルーチンに来るフレームは、弱い規則に従い、列を 16 より小さく保ち、`JV` を保ちます:

```
Inv(m) ∧ col(m) < 16 ∧ JV(m) ∧ (∀ UpdScrollVar k, ctl(k) ≠ 6) ∧ (∀ PlayerSubs k ≥ n₀, 1 ≤ X(k) ≤ 128 ⇒ X(k) ≤ 3)   ⇒   RuleW(m, e) ∧ col(e) < 16 ∧ JV(e)
```

わけ: `frame_sixA` と `X` の評価で `Y ≤ 3`、そして `S(m) < 32` なので、`k₂` で回り込まず（`noWrap_of_jv`）、`S(m) ≤ S(k₂) ≤ S(m) + 3`。`N ≥ 1` なら `N(e) = N − 1`、`S(e) = S(k₂)` で、`S(e) + 3·N(e) ≤ S(m) + 3·N < 32`。`N = 0` で `S(k₂) ≥ 32` なら `S(k₂) ≤ 34 < 160` なので `N(e) = 7`、`S(e) ≤ 2`、`2 + 21 < 32`。`N = 0` で `S(k₂) < 32` ならバイトは保たれます。（`strict_frame` は、各 `UpdScrollVar` での `Y ≤ 3` からの、同じ `JV` の一歩です。）

`invJ_onFrames`: 触るフレームまでのランのフレームで、解析の不変式、16 より小さい列、`JV` がどのフレームの始まりでも成り立ちます。帰納法は 1 つです（プレイヤーのルーチンに来るフレームでは `step_strict`。来ないフレームはバイトを保つ）。

`jv₀`: 地上の操作の始まりでの `JV`。横の土管から出る切り替えの行から出ます（チェック `jvCheckK`、非公開の証明 `pole_parser_jv` の `native_decide`）。

ルートの上で（`Theorems/PoleParserRun.lean`）: `invJ_run`（`PoleJoin.Run` の上の同じもの）と `inv_run`（そこから）。`noWrapP_onFrames` は、`JV` とどの `UpdScrollVar` でも高々 3 px の動きから、前のフィールドの主張を出します。ルートはこれを使いません。

## スクロールの量は高々 3（`PoleParserRun.amount_run`）

触るフレームより前の、プレイヤーのルーチンに来る各フレーム `n` で、そこに着いたところから先のプレイヤーのサブルーチンの各呼び出し `k` で:

```
1 ≤ X(trace(all n, k)) ≤ 128   ⇒   X(trace(all n, k)) ≤ 3
```

そのフレームは数えるフレーム `c` です（`counted_of`）。パート e はそれをスクロールの処理まで読みます（`OnFrames.readH`。ひとつ前のフレームの終わりで速さが範囲の中、位置が端から遠い: `OnFrames.readAll`、`far_of_range`）。そこで:

* 移動が書くバイトは、1 ‥ 128 なら、着いたところからのマリオの画素の動き（`MoveScroll.move_xs`）。着いたところはフレームの始まりの位置を持つ（`ReadH.before`）;
* 位置（1/256 px）は `16·v₂` だけ動き、`|v₂| ≤ top`（`SurfaceRead.read_move`、`Frame.move`、`Frame.anim`、`Frame.friction`）;
* 台の力は 0（`OnFrames.scrollAt`、`OnFrames.platPrev`）なので、`X` はそのバイト;
* フレームはスクロールの処理に 1 度だけ来る（`GuardE.subs_onceE`）ので、これらは同じ呼び出しのこと。

なので、端数 `0 ≤ f, f₂ ≤ 255` で `256·X + f₂ − f = 16·v₂ ≤ 16·top`、そして `top ≤ 48`（`pole_top`、ROM の値についての `decide`）で `256·X ≤ 1023`、`X ≤ 3`。左に動くとき `X` はバイトとして 128 より大きく（負の動き）、スクロールは左の端を動かしません。

## フィールド

なくなったもの: `parWrap`。

増えたもの。触るフレームより前の、プレイヤーのルーチンに来る各フレーム `n` で:

```
ctlU :  その各 UpdScrollVar k で、  ctl(trace(all n, k)) ≠ 6
```

これは前のフィールドより弱くはありません: 前のフィールドが求めなかったことを求めます。ただし、1 つの状態についての条件です: ランを通して持ち越すカウンタはフィールドから消えました。コードは、マリオがブロックのバッファからコインを取ると `ctl` を 6 にします。

32 回目のラウンド（[解析が遅れていないフレームの制御バイト 6](f-6-17-13-PoleLate-ja.md)）: `ctlU` は、`UpdScrollVar` で解析が遅れているとき（`S + 3·N ≥ 32`）だけ求めます。ほかのフレームでは、`ctl = 6` のフレームも `JV` を保ちます（`PoleLate.jv_weak`）。33 回目のラウンド（[エリアの解析の遅れは 157 px まで増えてよい](f-6-17-15-PoleLag-ja.md)）: `step_strict` と `invJ_onFrames` はもっと弱い `PoleLag.JY`（`S + 3·N < 157`）を運び、`ctlU` は `S + 3·N ≥ 157` のところだけで求めます。

シグネチャ: `PoleParserRun.invJ_run`、`inv_run`、`tilesCol_run` は `hs` のあとに `(hsc : ScrollRule.check sy m0 = true) (htop : TopSpeed.top sy ≤ 48)` を、`h0` のあとに `(hJ : PoleWrap.JV (valsOf (places sy m0) (R.seq 0)))` を取ります。`tilesCol_route` は `hs` のあとに `hsc` と `htop` を、`hmC` のあとに `(hmJ : PoleStrict.jvCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)` を取ります。`frame_six` と `keep_eP` は、上の 2 つの事実を最後の 2 つの連言として持ちます。`frame_sixA` は新しい。`PoleWrap` は `PoleParserEnd` を import します（前は `PoleParserRun`）。`route_1_1` はいまも `1748 + j ≤ L` を結論にします。

## 測ったこと

`pole-keep ctl`: `UpdScrollVar` での歩きの状態は `ctl` のどのビットも知りません。新しい歩きは成功し、チェック `eCheckP` 全体はネイティブで 41 秒です。このラウンドの最後の全体のビルドで `Proof.PoleParserEnd` は 85 秒でした（ほかの仕事と並んだ前のビルドでは 137 秒と 146 秒。30 回目は 68 秒）。

`pole-keep parser FM2 96`（ランは 30 回目と同じ: TAS、TAS のフレーム 900 から 1089 からの自分の乱数入力、最初の操作からの自分の乱数入力）。地上で操作できる状態で始まるフレームで:

| | TAS | 乱数 900〜1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 地上で操作できる状態で始まるフレーム | 608 | 14,318 | 25,980 |
| そのうち始まりで `JV` が偽 | 0 | 0 | 0 |
| 地上で、制御バイトが 6 の `UpdScrollVar`（`ctlU` が偽） | 0 | 0 | 0 |
| 地上でのプレイヤーのサブルーチンの呼び出し | 608 | 10,086 | 18,682 |
| そのうち量が 1 ‥ 128 で 3 より大きい（`amount_run` は 3 以下を言う） | 0 | 0 | 0 |
| 1 ‥ 128 の量の最大 | 3 | 3 | 3 |
| 地上で `UpdScrollVar` までの左の端の動きの最大 | 3 px | 3 px | 3 px |
| 操作できる状態の `UpdScrollVar`、どのエリアでも | 719 | 10,086 | 18,682 |
| そのうち制御バイトが 6 | 13 | 0 | 0 |

TAS で制御バイトが 6 の 13 のフレームは地下の部屋のフレームで、そこでマリオはコインを取ります。地上では、`ctlU` と `amount_run` の評価は測ったどのフレームでも成り立ちました（ネイティブで約 2 分、ビルドと並べて）。乱数のランはよくポーズするので、プレイヤーのルーチンに来るフレームは少なくなります。

## 証明していないこと

* `ctlU`: 触る前の地上のフレームで、マリオがブロックのバッファからコインを取らないこと。`TileSlot` の (slot) と同じく、フレームをまたいだブロックのバッファの中身が要ります。
  35 回目のラウンド: `ctlU` はなくなりました。各フレームの歩きが、コインのタイルのないブロックのバッファの地図から、コインのコードを切って制御バイトを追います。新しいフィールドは `coinBuf`、`readC`、`ctlKeep` です（[ブロックのバッファにコインがないので、制御バイトは 6 でない](f-6-17-17-PoleCoin-ja.md)）。
* `TileSlot`（slot、near、旗のページの 2 つ前のページでの read）、`bufAll`（7 か所）、`keepB`（66 か所）: このラウンドでは変えていません。

**ファイル.** `Theorems/PoleParserEnd.lean`（`kIdx`、`pats6`、`ctlPats`、`vTask`、`qN`、`finS`、`headN`、`startsN`、`csOf`、`atSN`、`atSZ`、`atS`、`atES`、`Cfgs.s`、`eCheckP`、`pats6_all`、`pats6_cover`、`cov_ctl`、`end_walkS`、`end_walkST`、`keep_eP`、`frame_six`、`frame_sixA`、`strictProbe`）。`Theorems/PoleStrict.lean`（新しい）。`Theorems/PoleParserRun.lean`（`amount_run`、`invJ_run`、`inv_run`、`tilesCol_run`、`tilesCol_route`）。`Theorems/PoleJoin.lean`（`parCtlOf`、`ctlU`。`parWrap` を消した）。`Theorems/PoleWrap.lean`（import）。`Main.lean`（非公開の `PoleParserEnd` の `pole_parser_jv`、`pole_top` と `Proof.ScrollRule` の import、ルートの `tilesCol_route` の行、`pole-keep ctl`、`pole-keep parser` の 31 回目の行）。
