[← Back](README-ja.md) | [English](f-6-17-16-PoleRing.md) | [Japanese](f-6-17-16-PoleRing-ja.md)

# 旗のタイル: 解析は列を輪の中の自分の場所に書く

33 回目のラウンド（[エリアの解析の場所](f-6-17-14-PoleSlot-ja.md)）は、フィールド `bufAll` に、旗のタイルをブロックのバッファに書く各書き込みで 1 つ多く求めさせました（`PoleSlot.NoTileC`）: フレームの始まりのエリアの解析の列が、旗の列まで来ている。このラウンドは、そこで求めることを減らします。書き込みは、ブロックのバッファの中の解析自身の列にあるか、解析が旗まで来ている。残りは証明します。

## 言葉

* 旗のタイルは、玉のタイルか、ポールのタイルです。
* `colP = 16·pg + c` は旗の列です。解析の列と同じに数えます（1 ページに 16 列）。
* `c(n)` は、地上の操作の始まりからのフレーム `n` の始まりでの解析の列です（`PoleJoin.parColOf`）。
* ブロックのバッファは 32 列を持ちます: 16 列のバッファが 2 つで、1 行は 16 バイトです。これは輪です: 面の列 `x` は、輪の列 `x mod 32` に入ります。
* `ringCol(i)` は、ブロックのバッファの RAM のバイト `i` の、輪の列です: 前にあるバッファ 1 つごとに 16 と、行の中の場所です（`PoleRing.ringCol`）。

## `bufAll` の新しい条件（`PoleRing.BufVM`）

```
前（33 回目）:  NoTileC(c, m)  :=  ステップが旗のタイルに変えるブロックのバッファの各バイト i で:   colP ≤ c
いま:           NoTileM(c, m)  :=  ステップが旗のタイルに変えるブロックのバッファの各バイト i で:   colP ≤ c   ∨   ringCol(i) = c mod 32
```

`BufVM(c, m)` は、`PoleKeepFar.BufV(m)` と、同じ書き込みでの `NoTileM(c, m)` です。フレーム `n` では `c = c(n)` です。`NoTileC ⇒ NoTileM` なので、新しいフィールドは少なく求めます（`bufVM_of_VS`）。

言葉で: 旗のタイルをブロックのバッファに書く書き込みは、輪の中の解析自身の列にあるか、解析の列が旗の列まで来ている。解析は、タスク `AreaParserCore` でブロックのバッファの列を書きます。各フレームは高々 1 つのタスクを走らせ、そのタスクは列を動かしません。なので、解析の書き込みでの解析の列は、フレームの始まりの列です。

## これで足りるわけ（`PoleRing.noTileC_of_M`）

* `BufV`（26 回目から求めている）は、旗のタイルを旗の列にだけ置きます。旗の列のどのバイトも、輪の列 `colP mod 32` にあります（`RingOK`。場所のチェック `ringCheck` から）。
* なので、`ringCol(i) = c mod 32` で旗のタイルを書く書き込みでは `c ≡ colP (mod 32)` です。
* さらに `colP < c + 32` なら `colP ≤ c` です。これが `NoTileC(c)` で、33 回目の歩きが使ったのはこれだけです（`PoleSlot.frames_slot`、`no_write_frameZS`）。

```
NoTile(m) ∧ NoTileM(c, m) ∧ RingOK ∧ colP < c + 32   ⇒   NoTileC(c, m)
```

## 上界 `colP < c(n) + 32`（`PoleParserRun.low₀`、`PoleJoin.Run.low`）

* 地上の操作の始まりで `colP < c(0) + 32` です。これは、横の土管から出る変化の行のチェックです（`PoleParserRun.lowCheckK`、非公開の `pole_parser_low`）。28 回目がそこで列が 16 より小さいことをチェックしたのと同じです（`PoleParser.col₀`）。
* 解析の列はフレームからフレームへ戻りません（`PoleParserRun.colMono_run`、33 回目）。なので、触るフレームまでのどのフレームの始まりでも `colP < c(n) + 32` です（`PoleRing.low_mono`）。

`PoleJoin.Run.TileColAll`（触るフレームが解析に求めること）は 2 つの部分が増えます: `colP < c(0) + 32` と `RingOK`。どちらもルートの上の定理です（`PoleParserRun.tilesCol_run`、`tilesCol_route`）。

## 変わったシグネチャ（正確に）

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleRing.BufVM (spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (trace (S.seq (a + n)) (S.inp (a + n)) k)`（前は `PoleSlot.BufVS`）。
* `PoleJoin.Run.TileColAll R := (∀ n, n + 1 < ix g → parColOf(all n) ≤ parColOf(all (n+1))) ∧ SlotMap (spotsF sy m0) (parColOf(all 0)) (all 0) ∧ colP (spotsF sy m0) < parColOf(all 0) + 32 ∧ RingOK (spotsF sy m0)`。
* `PoleJoin.Run.bufC₁` は `j` の前に `(hT : R.TileColAll)` を取ります。新しい定理: `PoleJoin.Run.low`。
* `PoleParserRun.tilesCol_run` は `hNT` のあとに `(hL : colP (spotsF sy m0) < parColOf sy m0 (R.seq 0) + 32) (hRg : PoleRing.RingOK (spotsF sy m0))` を取ります。
* `PoleParserRun.tilesCol_route` は `hmJ` のあとに `(hmL : lowCheckK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true)` を取ります。
* `PoleParserRun` に新しく: `rowLow`、`lowCheckK`、`low_of_state`、`low_of_invL`、`EndRunQ.low`、`ring_of_low`、`low₀`。新しいファイル `Theorems/PoleRing.lean`: `ringCol`、`RingOK`、`ringCheck`、`ringOK_of_check`、`NoTileM`、`BufVM`、`noTileM_of_C`、`bufVM_of_VS`、`bufV_of_VM`、`bufAt_of_VM`、`noTileC_of_M`、`bufVS_of_VM`、`bufC_of_VM`、`low_mono`。
* `route_1_1` は今も `1748 + j ≤ L` を結論します。ROM の新しいチェックは 1 つ: `pole_parser_low`（`native_decide`、新しい非公開ファイル `Proof/PoleRing.lean`）。

## 測ったこと

`pole-keep check FM2 96`（4 分 32 秒。ほかのチェックと並べてピーク 3.6 GB）は、操作の中で始まる 41,021 フレームのすべての命令を走らせます（167,758,026 命令。TAS、そのフレーム 1089 のあと `02808080`、フレーム 900 から 1089 からの自分の乱数の入力（Start ありとなし）、最初の操作からの自分の乱数の入力）:

| | TAS | フレーム 1089 のあと `02808080` | 乱数 900–1089、Start なし | 乱数 900–1089、Start あり | 最初の操作からの乱数 |
|---|---|---|---|---|---|
| ブロックのバッファのバイトを旗のタイルに変える書き込み | 10 | 0 | 90 | 60 | 0 |
| そのうち `NoTileM` が偽のもの | 0 | 0 | 0 | 0 | 0 |
| そこでの、バイトの輪の列から解析の列 mod 32 を引いたもの | 0 | – | 0 | 0 | – |
| 部屋のあとの地上のフレームの始まりでの `c + 32 − colP` の最小 | 18 | 47 | 19 | 18 | –（そのフレームはない） |

旗のタイルの 160 の書き込みは、すべて 1 つの命令、解析の列の書き込みです。`pole-keep parser FM2 96`: 操作の中で始まるどのフレームでも（TAS で 719、乱数で 14,318 と 25,980）、ブロックのバッファの列は解析の列 mod 32 に等しい。`pole-keep check` の終了コードは、いま、地上で `NoTileM` が偽にならないことと、部屋のあとの最小の上界が 0 より大きいことも求めます（終了コード 0）。

## 証明していないこと

* 7 か所の `bufAll`: 旗のタイルを旗の列にだけ書く（`BufV`、26 回目）こと、そして、輪の中の解析の列に書くか解析が旗まで来ている（`NoTileM`）こと。
* 2 つ目の部分は解析自身の書き込みでは正しいのですが、証明にはもう 1 つのバイトが要ります。`AreaParserCore` は、書き込みのアドレスを解析の列から計算しません。3 つ目のバイト、ブロックのバッファの列を読んで、輪のその列に書きます。列のステップ（`IncrementColumnPos`）は、列と一緒にそのバイトに 1 を足します（mod 32）。なので実際のフレームでは `B ≡ c (mod 32)` が成り立ちます（27 回目に測った: `B ≠ c mod 32` のフレームは 0）が、解析の歩きは `B` を追いません。証明には、列を追うのと同じように `B` を追う各フレームの歩き（列のステップのフレームでは値で分ける）と、`B` から書き込みのポインタを知る `AreaParserCore` の終わりの歩きが要ります。
  35 回目のラウンド: 解析自身の書き込みでは証明しました（[解析は自分の列をブロックのバッファの列に書く](f-6-17-18-PoleBcol-ja.md)）。`bufAll` は `NoTileM` をほかの書き込みにだけ求めます。
* `tilesCol`（`TileSlotC`）と `ctlU`: このラウンドでは変えていません。`keepB`: 変えていません。

**ファイル.** `Theorems/PoleRing.lean`（新しい）、`Theorems/PoleJoin.lean`（`bufAll`、`TileColAll`、`Run.low`、`Run.bufC₁`、`Run.slotStart`、`Run.inRange`、`Run.tilesStart`、`Run.bufAt₁`）、`Theorems/PoleParserRun.lean`（行のチェック、`low₀`、`tilesCol_run`、`tilesCol_route`）、`Main.lean`（`genPoleRing`、Route のブロック、`pole-keep check` の 34 回目の数）。
