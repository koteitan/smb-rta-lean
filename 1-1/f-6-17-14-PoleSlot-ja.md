[← Back](README-ja.md) | [English](f-6-17-14-PoleSlot.md) | [Japanese](f-6-17-14-PoleSlot-ja.md)

# 旗のタイル: エリアの解析の場所（slot）は定理になった

29 回目のラウンドは、フィールド `tilesCol` に 3 つの部分を与えました（[ルートのフレームの上のエリアの解析](f-6-17-10-PoleParserRun-ja.md)、[`TileSlot` を 1 つのページで](f-6-17-11-PoleWrap-ja.md)）。これらは、旗から遠い横のチェックの読み（マリオのページが旗のページの 2 つ以上前）で、旗の列で、触るフレームのルーチンの書き込みまでのことを言います:

* (slot) 読んだバイトが旗のタイルなら、触るフレームの始まりのエリアの解析の列は旗の列まで来ていた。
* (near) マリオは、フレームの始まりの画面の左の端より、高々 112 px 左にいる。
* (read) マリオのページが旗のページの 2 つ前なら、読みは、マリオのピクセルに 16 px より少なく足した列にある（mod 32）。

このラウンドは (slot) をなくします: 触るフレームの歩きがこれを証明します。使うのは、操作の始まりからどのフレームも保つ地図です。代わりに、フィールド `bufAll` が、もう話している書き込みで、1 つ多く求めます。そのあと (near) と (read) が要るのは、そのような読みで解析の列が旗の列まで来ていないことを示すためだけです。なので `tilesCol` は、いま、それだけを求めます。ルートが証明する解析の不変式があれば (near) と (read) からこれが出るので、新しい `tilesCol` は前の (near) と (read) より少なく求めます。

## 言葉

* 旗のタイルは、玉のタイルか、ポールのタイルです。
* `colP = 16·pg + c` は旗の列です。解析の列と同じに数えます（1 ページに 16 列）。
* `c(n)` は、操作の始まりからのフレーム `n` の始まりでの解析の列です（`PoleJoin.parColOf`）。`c₀` と `e₀` は、触るフレームの始まりでの解析の列と、画面の左の端（px）です。
* `pix = 256·page + x` は、読みのすぐあとのマリオのピクセルです。
* 旗の列での遠い読み: 横のチェックの読みのすぐあとで、`page + 1 < pg`、旗の列（状態の `pc` は読みの次の命令で、オフセットは横のチェックのもの）。

```
SlotMap(c, m)  :=  colP ≤ c   ∨   m のブロックのバッファのどのバイトも旗のタイルでない
```

## `bufAll` の新しい条件（`PoleSlot.BufVS`）

26 回目のラウンドから、`bufAll` は、触るフレームまでの各フレームの各命令に `PoleKeepFar.BufV` を求めていました: 添え字かポインタを通した書き込みで、`farBuf` が決めないもの（ROM からの `STA` では A が旗のタイルのときだけ）は、旗のタイルをブロックのバッファに書くなら旗の列にだけ書く。いま、フレーム `n` で `BufVS(c(n))` を求めます:

```
BufVS(c, m)  :=  farBuf(m) = false  →  （NMI が待っていない ROM からの STA なら A は旗のタイル）  →  （添え字かポインタを通した書き込み）  →
                 ステップが旗のタイルに変えるブロックのバッファの各バイト i について:   i は旗の列にある   ∧   colP ≤ c
```

`colP ≤ c` の部分が新しいです。新しいフィールドは前のものより多くを求めます: 旗のタイルの書き込みで、フレームの始まりの解析の列が旗の列まで来ていることも求めます。これから `BufAt` が出て（`bufAt_of_VS`）、どの命令でも `BufC(c)` が出ます: ブロックのバッファのバイトを旗のタイルに変えるステップでは `colP ≤ c`（`bufC_of_VS`: `farBuf` が決める書き込みはブロックのバッファのどのバイトも書かない。ほかのバイトの `STA` は旗のタイルを書かない）。

解析は、タスク `AreaParserCore` で、自分の列に、ブロックのバッファの 1 列を書きます。1 フレームに走るタスクは多くて 1 つです。なので旗のタイルを書くフレームでは、フレームの始まりの解析の列は旗の列です。本物のフレームでは、旗のタイルのどの書き込みでも、その差は 0 でした（下）。

## 操作の始まりからのフレーム（`PoleSlot.frames_slot`）

* 操作の始まりでは、ブロックのバッファのどのバイトも旗のタイルではありません。これは横の土管から出る切り替えの行からの定理です（`PoleParser.inv₀`。証明がもう持っている検査 `pole_parser_rows` で）。なので `SlotMap(c(0), all 0)` が成り立ちます。
* 1 フレーム（`frame_slot`）。`colP ≤ c(n)` なら、地図はそのあとのどの列でも成り立ちます。そうでなければ、`BufC(c(n))` で、フレームのどのステップも旗のタイルをブロックのバッファに書かず、フレームの歩きが「旗のタイルがない」を保ちます。歩きは `PoleTileKeep` のフレームの歩き（`keepCheckOfY`）で、場所は `noCol Q` です。これは旗の列を RAM の外に動かした `Q` なので、ブロックのバッファのどのバイトも旗のタイルでなければ `ColMap (noCol Q)` が成り立ちます。歩きのテスト `okSK` は場所をブロックのバッファのバイトでしか見ないので、`noCol Q` の検査は `Q` の検査と同じです（`keepCheckS_noCol`）。なので `SlotMap(c(n), all(n+1))`。
* 列は戻りません: `c(n) ≤ c(n+1)`（`PoleParserRun.colMono_run`）。どのフレームも解析の弱い規則 `RuleW` に従い（`PoleStrict.ruleW_onFrames`: プレイヤーのルーチンに来るフレームでは `step_strict`、ほかでは `PoleParser.step_noCut`。`invJ_onFrames` の条件で）、弱い規則は列を保つか 1 足します（`PoleStrict.col_of_ruleW`）。なので `SlotMap(c(n+1), all(n+1))`。

なので触るフレームの始まりで `SlotMap(c₀, …)` が成り立ちます。

## 触るフレーム（`PoleSlot.no_write_frameZS`）

これは 25 回目のラウンドの歩き（`PoleTileKeep.no_write_frameZ`）で、場所の地図を、地図 `ColMap` と同じにステップからステップへ運びます（触るフレームの各命令の `BufC(c₀)` で）。歩きが知っている旗の列での遠い読み（テスト `pairOK` と `readPF`）のすぐあとで、フィールドが `c₀ < colP` を出します。なので場所の地図で、ブロックのバッファのどのバイトも旗のタイルでなく、読んだバイトはブロックのバッファのバイトです（`noTile_after`: 場所 `noCol Q` での `PoleTileFar.tileRead_afterF`）。なので旗のタイルではありません: そこで `TileCol` が成り立ちます。歩きが `tilesCol` を使っていたのはここだけです。歩きのほかの部分は変わりません。

## フィールド

旗の列での遠い読みで、`tilesCol` の前（30 回目）といま:

```
前:    TileSlot(c₀, e₀, m)  :=  (slot) 読んだバイトが旗のタイル ⇒ colP ≤ c₀   ∧   (near) e₀ ≤ pix + 112   ∧   (read) page + 2 = pg ⇒ ∃ a < 16, ⌊(pix + a)/16⌋ mod 32 = colP mod 32
いま:  TileSlotC(c₀, m)     :=  c₀ < colP
```

`tileSlotC_of_N`: (near) ∧ (read) ∧ `16·c₀ ≤ e₀ + 384` ⇒ `TileSlotC`（30 回目のラウンドの算数、`PoleTileFar.tileCol_of_slot`）。`16·c₀ ≤ e₀ + 384` は触るフレームでの解析の不変式で、ルートの上の定理です（`PoleParserRun.colEdge_run`）。なのでルートの上では前のフィールドから新しいものが出ます: `tilesCol` は少なく求めます。`bufAll` は多く求めます（上）。部分 (slot) はマリオの読みから解析の書き込みへ移り、場所は `bufAll` がもう話している場所です。部分 (near) と (read) は、それが使われていた 1 つの事実になりました。

`PoleJoin.Run.TileColAll` は名前を保ちます（非公開のファイルが使う）が、いまは触るフレームが解析に求めることを言います: `n + 1 < ix(g)` で `c(n) ≤ c(n+1)`、`SlotMap(c(0), all 0)`。これは定理です（`PoleParserRun.tilesCol_run`、`tilesCol_route`）。

変わった型（そのまま）:

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleSlot.BufVS (spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (trace (S.seq (a + n)) (S.inp (a + n)) k)`（前は `PoleKeepFar.BufV (spotsF sy m0) (…)`）。
* `PoleJoin.Run.tilesCol : ∀ n, WriteStep … n → ∀ j ≤ n, PoleSlot.TileSlotC (spotsF sy m0) (parColOf sy m0 (keep.fm g)) (trace (keep.fm g) (keep.pad g) j)`（前は `PoleTileFar.TileSlot (spotsF sy m0) (parColOf sy m0 (keep.fm g)) (left16 (keep.fm g)) (…)`）。
* `PoleJoin.Run.TileColAll R := (∀ n, n + 1 < ix g → parColOf(all n) ≤ parColOf(all (n+1))) ∧ PoleSlot.SlotMap (spotsF sy m0) (parColOf(all 0)) (all 0)`（前は書き込みまでの各状態での `TileCol`）。
* `PoleParserRun.tilesCol_run` は `hJ` のあとに `(hNT : PoleParser.NoTiles (spotsF sy m0) (R.seq 0))` を受け取ります。`tilesCol_route` の型は同じです（`(PoleParser.inv₀ …).2` を渡す）。
* 新しいもの: `PoleJoin.Run.bufC₁`、`PoleJoin.Run.slotStart`、`PoleStrict.col_of_ruleW`、`PoleStrict.ruleW_onFrames`、`PoleParserRun.colMono_run`、`PoleParserRun.colEdge_run`（ルートは使わない）、ファイル `Theorems/PoleSlot.lean`。
* `Run.inRange` の型は同じです。いまは `PoleSlot.inRange_of_frameZS` を使います。`route_1_1` の結論は `1748 + j ≤ L` のままです。

ROM の新しい検査はありません: 歩きは 25 回目と 31 回目のラウンドのもので、操作の始まりの地図は `pole_parser_rows` から出ます。

## 測ったこと

`pole-keep parser FM2 96` と `pole-keep check FM2 96`。ランは TAS、TAS のフレーム 900 から 1089 からの自分の乱数の入力（半分は Start あり）、最初の操作からの自分の乱数の入力です:

| | TAS | 乱数 900–1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 操作で始まるフレーム | 719 | 14,318 | 25,980 |
| 旗のタイルをブロックのバッファに書く書き込み | 10 | 150 | 0 |
| そこでの、フレームの始まりの解析の列 − `colP` | 0 | 0 | – |
| そのうち `BufVS` が偽 | 0 | 0 | 0 |
| `SlotMap(c(n), all n)` が偽の、操作で始まるフレームの始まり | 0 | 0 | 0 |
| 旗の列での遠い読み（`tilesCol` が求めるところ） | 101 | 0 | 3,376 |
| そのうち `TileSlotC` が偽（フレームの始まりで `c ≥ colP`） | 0 | 0 | 0 |
| そのうち 30 回目の (near) か (read) が偽 | 0 | 0 | 0 |

遠い読みは操作中のどのフレームでも数えます。これはフィールドが求める触るフレームより広いです。

`pole-keep check FM2 96`（3 分 44 秒、73 MB）は、操作で始まる 41,021 フレームのすべての命令を走らせます（167,758,026 命令。TAS、そのフレーム 1089 から `02808080`、フレーム 900 から 1089 からの自分の乱数の入力（Start あり、なし）、最初の操作からの自分の乱数の入力）。ブロックのバッファのバイトを旗のタイルに変える書き込みは 160 回（TAS で 10、フレーム 900 から 1089 からの乱数で 150）で、どれもフレームの始まりの解析の列が `colP` と等しいところでした。なので `BufVS` が偽は 0 回、`SlotMap` が偽のフレームの始まりは 0 です。終了コードは、いま、地上でのこの 2 つの数が 0 であることも求めます（終了コード 0）。

## 証明していないこと

* 7 か所の `bufAll`: 旗のタイルを書くのは旗の列にだけで、いまは、フレームの始まりの解析の列が旗の列まで来ているときだけでもあること。証明には、解析のタスク `AreaParserCore` を、その書き込みまで列を追って歩く歩きが要ります。
* `tilesCol`（`TileSlotC`）: 触るフレームの旗の列での遠い読みで、解析はまだ旗の列まで来ていないこと。証明した不変式があれば (near) と (read) からこれが出ます。(near) の証明には、触るフレームのスクロールの処理の押し戻しのあとのマリオのピクセルが要ります: パート e はその結果を触るフレームより前のフレームでだけ証明します。その歩きは、フレームのどの命令もアドレスでルーチンを書かないことを求めますが、触るフレームは書くからです（旗の書き込み）。(read) には、マリオのピクセルからの読みのアドレスが要ります。25 回目のラウンドは、そこで和の上のビットを分けると 5.8 GB を超えることを見ました。
* `ctlU` は次の段で狭めました（[エリアの解析の遅れは 157 px まで増えてよい](f-6-17-15-PoleLag-ja.md)）。`keepB`: このラウンドでは変えていません。

**ファイル.** `Theorems/PoleSlot.lean`（新しい）。`Theorems/PoleJoin.lean`（`bufAll`、`tilesCol`、`Run.TileColAll`、`Run.bufC₁`、`Run.slotStart`、`Run.inRange`）。`Theorems/PoleStrict.lean`（`col_of_ruleW`、`ruleW_onFrames`）。`Theorems/PoleParserRun.lean`（`colMono_run`、`colEdge_run`、`tilesCol_run`、`tilesCol_route`）。`Main.lean`（`pole-keep check` と `pole-keep parser` の 33 回目のラウンドの数）。
