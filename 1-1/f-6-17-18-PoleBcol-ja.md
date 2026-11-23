[← Back](README-ja.md) | [English](f-6-17-18-PoleBcol.md) | [Japanese](f-6-17-18-PoleBcol-ja.md)

# 旗のタイル: 解析は自分の列をブロックのバッファの列に書く

34 回目のラウンド（[解析は列を輪の中の自分の場所に書く](f-6-17-16-PoleRing-ja.md)）は、フィールド `bufAll` に、旗のタイルをブロックのバッファに書く各書き込みで、書き込みがフレームの始まりのエリアの解析の列の輪の列にあるか、解析の列が旗の列まで来ていることを求めさせました（`PoleRing.NoTileM`）。本物のフレームでは、そのような書き込みはどれも 1 つの命令、解析の列の書き込みがします。このラウンドは、その命令でその部分を証明します。なので `bufAll` はそれをほかの書き込みにだけ求めます。そこでは、測った旗のタイルの書き込みは 1 つもありません。

## コードがすること

* 解析の列の書き込み（`AreaParserCore` の中）は、書く場所を解析の列から計算しません。3 つ目のバイト、ブロックのバッファの列 `B` を読み、ブロックのバッファのその列のアドレスをとり（`GetBlockBufferAddr`）、13 行をポインタを通して書きます。
* 列の進み（`IncrementColumnPos`）は、解析の列（とそのページ）に 1 を足し、`B` に 1 を足します（mod 32）。
* ループのコマンドの戻り（`ExecGameLoopback`）は、解析のページから 4 ページ引きます。4 は偶数なので、列の mod 32 は変わりません。

## 言葉

* `c = 16·page + col` は解析の列（`PoleJoin.parColOf`）で、`col` はページの中の列です。
* `BInv(m)`: `B = c mod 32` かつ `col < 16`（`PoleBcol.BInv`）。
* `StoreRing(b, m)`: `m` のステップが変えるブロックのバッファのどのバイトも、輪の列 `b` にある（`PoleRing.ringCol`）。

## 歩き（`Theorems/PoleBcol.lean`）

`walkB` は、`FrameKeep` の操作中の 1 フレーム全体の歩きを、32 の片 `b` のどれかで行うものです:

* フレームは `B = b`、`col = b mod 16`、ページの一番下のビット `b / 16` が知られて始まります（`startB`）。これは `BInv` の `B = b` の場合です。
* ガードは `B`、列、ページを守ります（`guardB`）。フィールド `keep.cleanE` はもう列とページを守っています（`FrameKeep.parE` のバイトです）。新しいフィールド `bKeep` は、添え字やポインタを通す書き込みが `B` を書かないことを言います。
* 列の進みのページの `INC` と、ループのコマンドの戻りの入口で、知られていないページを、知られているビットに合う値に分けます（`prePage`）。なので、そこを通ってもページの一番下のビットは知られたままです。
* NMI の待ちのない解析の書き込みで、書き込みの行き先は知られていて、ブロックのバッファの中なら輪の列 `b` にあります（`storeOK`）。
* フレームの終わりで、`B`、列、ページの一番下のビットは知られていて、`BInv` を満たします（`endB`）。

表は 32 の探索から来ます（証明の一部ではない）。ROM では、片ごとに約 47,000 状態です。32 の片すべてのチェックはネイティブで 119 秒かかります（`pole-keep bcol`、最大 0.5 GB）。このラウンドでいちばん長いチェックです。

## 証明すること

`frame_bcol`: `BInv` で始まり、その命令が歩きのガードの `CleanK` を満たす操作中のフレームは、`BInv` で終わり、その解析の各書き込みで:

```
StoreRing(フレームの始まりの B, trace(m, k))
```

`frames_bcol`: 操作の始まりで `BInv` なら（横の土管から出る変化の行のチェック、`PoleParserRun.bInv₀`）、触るフレームまでのどのフレーム `n`（`n < ix g`）でも:

```
BInv(all n)   ∧   ∀ k,  pc(trace(all n, k)) = 解析の書き込み  →  StoreRing(c(n) mod 32, trace(all n, k))
```

`StoreRing(c mod 32, m)` は `NoTileM(c, m)` を与えます（`noTileM_of_ring`）。なので、解析の書き込みでは `NoTileM` は定理です。触る前のフレームでも、触るフレームでも。

## フィールド

変えたもの:

```
bufAll :  PoleRing.BufVR(spotsF, c(n), 解析の書き込み, trace(all n, k))
          （34 回目の BufVM で、NoTileM は解析の書き込みでない命令でだけ求める。BufVM ⇒ BufVR: bufVR_of_VM）
```

足したもの。触るフレームまでの各フレーム（`n < ix g`）の各命令で:

```
bKeep :  farStore([B]) = false  →  添え字やポインタを通す書き込みは B を書かない
```

`bufAll` は前より少なく求めます。`bKeep` は新しく、`keepB` の種類です。

変わったシグネチャ（正確に）:

* `PoleJoin.Run.bufAll : ∀ n, n < ixOf … g → ∀ k, PoleRing.BufVR (PoleFrame.spotsF sy m0) (parColOf sy m0 (S.seq (a + n))) (PoleBcol.bcOf sy m0).store (trace (S.seq (a + n)) (S.inp (a + n)) k)`。
* 新しいフィールド `PoleJoin.Run.bKeep : ∀ n, n < ixOf … g → ∀ k, PoleBcol.BcR (PoleBcol.bcOf sy m0) (trace (S.seq (a + n)) (S.inp (a + n)) k)`。
* `PoleJoin.Run.TileColAll` は最後に 1 つの部分を持ちます: `∀ n, n < ix g → ∀ k, pc(trace(all n, k)) = (bcOf sy m0).store → PoleRing.NoTileM (spotsF sy m0) (parColOf sy m0 (all n)) (trace (all n) (inp n) k)`。
* `PoleParserRun.tilesCol_run` は、`hRg` のあとに `(hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0))` をとる。
* `PoleParserRun.tilesCol_route` は、`hcC` のあとに `(hmB : bInvK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcB : PoleBcol.bcolCheck sy m0 = true)` をとる。
* `PoleRing` に新しい: `BufVR`、`bufVR_of_VM`、`bufVM_of_R`、`bufAt_of_VR`。`PoleParserRun` に新しい: `rowB`、`bInvK`、`bInv_of_state`、`bInv_of_invL`、`EndRunQ.bInv`、`bInv₀`。
* 新しい記号 1 つ: `ExecGameLoopback`。
* `route_1_1` の結論は今も `1748 + j ≤ L` です。ROM の新しいチェックは 2 つ: `pole_bcol_walk` と `pole_bcol_rows`（`native_decide`、新しい非公開のファイル `Proof/PoleBcol.lean`）。

## 測ったもの

`pole-keep parser FM2 96` で、操作の中で始まるフレーム（TAS で 719、乱数の走りで 14,318 と 25,980）:

| | TAS | 乱数 900–1089 | 最初の操作からの乱数 |
|---|---|---|---|
| `BInv` が偽の、操作の中のフレームの始まり（どのエリアでも） | 0 | 0 | 0 |
| `bKeep` が偽の命令（どのエリアでも） | 0 | 0 | 0 |
| ブロックのバッファへの旗のタイルの書き込み | 10 | 150 | 0 |
| そのうち解析の書き込みでないもの（`bufAll` がまだ `NoTileM` を求めるところ） | 0 | 0 | 0 |
| 解析の書き込みで、`B` の輪の列の外で変わったバイト | 0 | 0 | 0 |

## 証明していないこと

* `bufAll`: `BufV`（旗のタイルは旗の列にだけ入る、26 回目）と、解析の列の書き込みでないところでの `NoTileM`（測った旗のタイルの書き込みはそこにはない）。
* `bKeep`: 添え字やポインタを通す書き込みが `B` を書かないこと（測って 0）。36 回目: 解析の列の書き込み以外のポインタを通す書き込みと、触るフレームでルーチン、モード、タスクの最初の書き込みのあとでだけ求めます。ほかは `PoleNear` の歩きが証明し、解析の書き込みではこの歩きが証明します（`missS`）（[制御バイトとブロックのバッファの列に届きうる書き込み](f-6-17-19-PoleNear-ja.md)）。
* 解析の書き込みでの `BufV` はまだ求めています: その行が旗のタイルを旗の列にだけ持つこと。証明には、解析が描くメタタイルが要ります。

**ファイル.** `Theorems/PoleBcol.lean`（新しい）。`Theorems/PoleRing.lean`（`BufVR`）。`Theorems/PoleJoin.lean`（`bufAll`、`bKeep`、`TileColAll`、`Run.bufC₁`、`Run.slotStart`、`Run.tilesStart`、`Run.bufAt₁`）。`Theorems/PoleParserRun.lean`（行のチェック、`bInv₀`、`tilesCol_run`、`tilesCol_route`）。`Smbrta/Syms.lean`、`tools/smb-symbols.txt`（`ExecGameLoopback`）。`Main.lean`（`genPoleBcol`、Route のブロック、`pole-keep bcol`、`pole-keep parser` の数）。
