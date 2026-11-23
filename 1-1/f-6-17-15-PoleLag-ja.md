[← Back](README-ja.md) | [English](f-6-17-15-PoleLag.md) | [Japanese](f-6-17-15-PoleLag-ja.md)

# 旗のタイル: エリアの解析の遅れは 157 px まで増えてよい

32 回目のラウンドはフィールド `ctlU` を残しました（[解析が遅れていないフレームの制御バイト 6](f-6-17-13-PoleLate-ja.md)）: 触るフレームより前の、プレイヤーのルーチンに来る各フレームの各 `UpdScrollVar` で、画面のバッファの制御バイトが 6 でないか、そこで `S + 3·N < 32`。このラウンドは、フレームの上でもっと弱い上限を運び、`ctlU` が制御バイトを求めるのを `S + 3·N ≥ 157` のところだけにします。

## 言葉

`N` はエリアの解析の残りのタスクの数、`S` は 32 px のスクロールのカウンタ。`S + 3·N` は解析の遅れです: 画面が動いたのに解析がまだ追いついていないピクセルで、残りのタスク 1 つを 3 px と数えます。`m` からのフレームについて、`k₂` はスクロールの処理のあとの `UpdScrollVar`、`e` はフレームの終わり。`Y ≤ 3` は `k₂` までのスクロールの動きで、`S(k₂) = S(m) + Y`。

```
JV(v)  :=  N ≤ 7  ∧  S + 3·N < 32        （31 回目と 32 回目のラウンド）
JY(v)  :=  N ≤ 7  ∧  S + 3·N < 157       （このラウンド）
```

## 157 で足りるわけ

解析の不変式と厳しい歩きは、カウンタに 2 つのことを求めます:

* `UpdScrollVar` で回り込まない: `S(m) + Y < 256`。
* `N = 0` のとき、新しい列が始まるのは `UpdScrollVar` で `32 ≤ S < 160` のときだけ。コードはカウンタを符号つきのバイトとして 32 と比べるので、160 からはどの列も始めません。`PoleParserEnd` の厳しい歩きも、新しい列を知っているのは `S(k₂)` が 32 ‥ 159 のときだけです。

`JY` は両方を出します: `S(m) < 157` なので `S(k₂) < 160 < 256`。この性質を持つ上限で 157 がいちばん大きいです: `N = 0`、`S(m) = 157` で 3 px 動けば `S(k₂) = 160`。

## 1 フレーム（`Theorems/PoleLag.lean`、`Theorems/PoleStrict.lean`）

`step_strict` は、いま、フレームの始まりの `JY` を受け取り、終わりの `JY` を出します。各 `UpdScrollVar` `k` で次が成り立つとき:

```
ctl(k) ≠ 6   ∨   S(k) + 3·N(k) < 157
```

* `ctl(k₂) ≠ 6` なら（31 回目のラウンドの厳しい形）: `N ≥ 1` なら `N(e) = N − 1`、`S(e) = S(k₂)` なので `S(e) + 3·N(e) = S(m) + Y + 3·N − 3 ≤ S(m) + 3·N < 157`。`N = 0` で `S(k₂) ≥ 32` なら `N(e) = 7`、`S(e) = S(k₂) − 32` なので `S(e) + 21 < 160 − 32 + 21 = 149`。`N = 0` で `S(k₂) < 32` なら、バイトはそのまま。
* `S(k₂) + 3·N < 157` なら（`PoleParser.frame_sixA` の弱い形。制御バイトはなんでもよい）: `N(e) ≤ N` で `S(e) = S(k₂)`（`jy_weak`）、または `N = 0` で新しい列、`N(e) = 7`、`S(e) = S(k₂) − 32`（`jy_col`）。
* 回り込まない: `noWrap_of_jy`（カウンタが 157 より小さく、動きが高々 3 px）。

`invJ_onFrames` と `ruleW_onFrames` は、プレイヤーのルーチンに来る各フレームで同じ条件を受け取り、フレームの上で `JY` を運びます。操作の始まりでは `JV` が成り立つので（`PoleStrict.jv₀`、切り替えの行から）、`JY` も成り立ちます（`jy_of_jv`）。

## フィールド

前（32 回目）: `ctlU :  各 UpdScrollVar k で、  ctl ≠ 6  ∨  S + 3·N < 32`。

いま:

```
ctlU :  触るフレームより前の、プレイヤーのルーチンに来る各フレーム n の各 UpdScrollVar k で、
        ctl(trace(all n, k)) ≠ 6   ∨   S(trace(all n, k)) + 3·N(trace(all n, k)) < 157
```

新しいフィールドは前のものより弱いです。1 つの状態の条件のままです。言葉では: 解析が 157 px 以上遅れているときに、マリオは地上でコインを取らない。同じ形から（ここでは定理ではなく、理由づけ）: `UpdScrollVar` で制御バイトが 6 でないフレームでは、遅れは 32 より小さくなるか、増えません。制御バイトが 6 のフレームでは、高々 3 px 増えます。なので、操作の始まりの遅れが 32 より小さければ、このフィールドが求められるのは、制御バイトが 6 のフレームが 42 回以上あったあとだけです。

変わった型（そのまま）:

* `PoleStrict.step_strict`: `hk6 : ∀ k, pc(k) = UpdScrollVar → frame(k) = frame(m) → ctl(k) ≠ 6 ∨ S(k) + 3·N(k) < 157`、`hJ : PoleLag.JY (valsOf (places sy m0) m)`、結論は `(RuleW … ∧ ColOK …) ∧ PoleLag.JY (valsOf (places sy m0) (frame m i))`。
* `PoleStrict.invJ_onFrames`: `hJ0 : PoleLag.JY (valsOf (places sy m0) (K.all 0))`、`hk6` は 157 で、結論は `PoleWrap.JV` のかわりに `PoleLag.JY`。`PoleStrict.ruleW_onFrames`（このラウンドで新しい）も同じ。
* `PoleParserRun.invJ_run` の結論は `PoleWrap.JV` のかわりに `PoleLag.JY`。仮定 `hJ`（操作の始まりの JV）は同じ。
* `PoleJoin.Run.ctlU`: 32 のかわりに上限 157。
* 新しいもの: `Theorems/PoleLag.lean`（`JY`、`jy_of_jv`、`s_lt`、`jy_weak`、`jy_col`）、`PoleStrict.noWrap_of_jy`。`PoleStrict` は `PoleLag` を読み込みます（`PoleLag` は `PoleLate` を読み込む）。
* `route_1_1` の結論は `1748 + j ≤ L` のままです。ROM の新しい検査はありません。

## 測ったこと

`pole-keep parser FM2 96`（1 分 36 秒、72 MB）。操作で始まるフレームの各 `UpdScrollVar` で:

| | TAS | 乱数 900–1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 地上で来た回数 | 608 | 10,086 | 18,682 |
| そのうち `S + 3·N ≥ 32`（32 回目のフィールドが求めたところ） | 40 | 242 | 205 |
| そのうち `S + 3·N ≥ 157`（新しいフィールドが求めるところ） | 0 | 0 | 0 |
| 遅れ `S + 3·N` のいちばん大きい値（操作中のどのエリアでも） | 34 | 34 | 34 |
| 操作中で `ctl = 6` の回数（どのエリアでも） | 13 | 0 | 0 |

なので新しいフィールドは、測ったどの回でも制御バイトを求めません。TAS で `ctl = 6` の 13 回は地下の部屋で、そこでマリオはコインを取ります。

## 証明していないこと

* `ctlU`: 解析が 157 px 以上遅れているあいだ、マリオは地上でコインを取らない。これをなくす証明には、32 回目のラウンドが書いたとおり、どのフレームでもマリオが読むところのブロックのバッファの中身（そこにコインのタイルがない）と、フレームの中で制御バイトを追う歩きが要ります。あるいは、地上で制御バイトが 6 のフレームの数の上限が要ります。
  35 回目のラウンド: `ctlU` はなくなりました。各フレームの歩きが、コインのタイルのないブロックのバッファの地図から、コインのコードを切って制御バイトを追います。新しいフィールドは `coinBuf`、`readC`、`ctlKeep` です（[ブロックのバッファにコインがないので、制御バイトは 6 でない](f-6-17-17-PoleCoin-ja.md)）。
* `bufAll`、`keepB`、`tilesCol`（(near) と (read)）: この段では変えていません。

**ファイル.** `Theorems/PoleLag.lean`（新しい）。`Theorems/PoleStrict.lean`（`noWrap_of_jy`。`JY` での `step_strict`、`invJ_onFrames`、`ruleW_onFrames`）。`Theorems/PoleParserRun.lean`（`invJ_run`、`colMono_run`）。`Theorems/PoleJoin.lean`（`ctlU`）。`Main.lean`（`pole-keep parser` の 33 回目のラウンドの PoleLag の行）。
