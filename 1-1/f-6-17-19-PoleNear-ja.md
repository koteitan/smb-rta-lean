[← Back](README-ja.md) | [English](f-6-17-19-PoleNear.md) | [Japanese](f-6-17-19-PoleNear-ja.md)

# 制御バイトとブロックのバッファの列に届きうる書き込み

35 回目のラウンドは、操作からのフレームの各命令に 2 つのフィールドを足しました（[ブロックのバッファにコインがない](f-6-17-17-PoleCoin-ja.md)、[解析の書き込みはブロックのバッファの列に](f-6-17-18-PoleBcol-ja.md)）:

* `ctlKeep`: 添え字やポインタを通す書き込みは、画面のバッファの制御バイト `ctl` を書かない（触るフレームより前のフレーム）。
* `bKeep`: 添え字やポインタを通す書き込みは、ブロックのバッファの列 `B` を書かない（触るフレームまでのフレーム）。

このラウンドは、添え字やポインタを通す各書き込みがどこへ行きうるかを知る、各フレーム全体の 1 つの歩きで、ほとんどすべての命令で両方を証明します。2 つのフィールドは、いくつかの場所でだけ求めます。

## 言葉

* `NoW(s, m)`: `m` の命令は、行き先が RAM のバイト `s` である添え字やポインタを通す書き込みではない（`PoleBcol.NoW`）。そのような書き込みでない命令では、すぐに成り立ちます。
* `CtlStore(m)`: `m` の命令は、ルーチン、モード、タスクのバイトを番地で書く（`FrameKeep.CtlStore`）。触るフレームより前のフレームにはありません（`keep.noStore`）。
* `store`: エリアの解析の列の書き込み（`STA (zp),Y`。`AreaParserCore` からの最初のもの）。
* `ResidC(m)`（`PoleNear.ResidC`）、`ctlKeep` が残る場所:
  * 頭がブロックに当たるときのコード（`PlayerHeadCollision` から `BlockObjectsCore` まで）の中の、ポインタを通す書き込み。
  * 城の行のループ（`CRendLoop` から `ChkCFloor` まで）。
  * `RenderUnderPart` の書き込み（最初の `STA abs,X`）。
* `ResidB(m)`（`PoleNear.ResidB`）、`bKeep` が残る場所: `store` 以外の、ポインタを通すすべての書き込み（`STA (zp),Y`）。

## 歩き（`Theorems/PoleNear.lean`）

歩きは、パート e の `SideRange` の歩き（`SideRange.walkR`）です。表の状態は `X` と `Y` の範囲を持ち、表の状態からの歩きは、範囲の中の `X` と `Y` の値から始まります。いくつかの命令の前で `X` や `Y` を分けもします。ここでは、スクロールの処理ではなくフレームの始まりから始まるので、フレーム全体を覆います:

* ガードは `FrameKeep.guardE` です。その `CleanK` はフィールド `keep.cleanE` です。
* 道は、ルーチン、モード、タスクを番地で書く命令で止まります。なので触るフレームでは、最初のそのような書き込みまでの命令を覆います。
* `store` 以外の、添え字やポインタを通す各書き込み（`PushTimer.wOps` の命令）で、2 つのバイトのそれぞれについて、次のどれかを求めます（`PoleNear.okN`）: その書き込みは `PoleKeepFar.farStore` が決める（元のアドレスからどの添え字もそのバイトに届かない）。状態が許すどの行き先もそのバイトを外す（`SideRange.missK`）。その書き込みは `ResidC`（`ctl` について）か `ResidB`（`B` について）の場所である。
* `store` では何も求めません。

表のキーは、`SideRange.residB` のコードの中と、スプライトの並べ替え（`SpriteShuffler`）の中では、`X`、`Y`、ゼロページのバイト 0 も持ちます。なので、数を数えるループの状態はまとめられません。キーは証明の一部ではありません: 状態が表の状態に覆われるのは、知られているビットと範囲がそう言うときだけです。

`store` では、`PoleBcol` の歩きが `B` を知っているので、行き先を知っています。新しいテスト `missS`: `store` で行き先は知られていて、`B` でも `ctl` でもない。

ROM では、表は 66,996 状態です。探索は 19 秒、チェック `PoleNear.nCheck` はネイティブで 23 秒かかります（`pole-keep near-check`、0.5 GB）。新しいテストのある `PoleBcol` のチェックは 131 秒です（119 秒でした）。

## 証明すること

`near_frame`: 操作中のフレーム `m` で、その命令が `guardE` の `CleanK` を満たすもの。各 `k` で:

```
(∀ j < k, ¬CtlStore(trace(m, j)))  ∧  frame(trace(m, k)) = frame(m)  ∧  pc(trace(m, k)) ≠ store  →
    (¬ResidC(trace(m, k)) → NoW(ctl, trace(m, k)))  ∧  (¬ResidB(trace(m, k)) → NoW(B, trace(m, k)))
```

`near_frames`: 同じことを、どのフレーム `n < ix g` でも（どれも操作中で始まる: `FrameKeep.Frames.all_start`）。

`PoleBcol.frames_bcol`（変えた）: `NoW(B)` を、フレームの `store` 以外の命令でだけ求めます（35 回目は各命令で `BcR` を求めました）。そして、どのフレーム `n < ix g` でも、`store` で次を与えます:

```
StoreRing(c(n) mod 32, trace(all n, k))  ∧  NoW(B, trace(all n, k))  ∧  NoW(ctl, trace(all n, k))
```

`PoleBcol` の歩きは、各ステップで `NoW(B)` を必要とします。`store` では、そのステップの自分の状態からそれをとります（`live_stepB`）。なので循環はありません。

`PoleJoin.Run.bNoW`: どのフレーム `n < ix g` でも、フレームの `store` 以外のどの命令でも `NoW(B)`。最初の `CtlStore` までで `ResidB` でないところは `near_frames` から、残りは `bKeep` から。

`PoleJoin.Run.ctlR`: `n + 1 < ix g` のどのフレーム `n` でも、フレームのどの命令でも `CtlR`（35 回目の形）。`store` では `frames_bcol` から、`ResidC` では `ctlKeep` から、ほかでは `near_frames` から（触るフレームより前に `CtlStore` はない）。`Run.ctl6` がこれを使います。

## フィールド

狭めたもの（どちらも前より求めることが少ない）:

```
ctlKeep :  ∀ n, n + 1 < ix g → ∀ k,  ResidC(trace(all n, k)) → CtlR(trace(all n, k))
bKeep   :  ∀ n, n < ix g → ∀ k,  (ResidB(trace(all n, k)) ∨ ∃ j < k, CtlStore(trace(all n, j))) → BcR(trace(all n, k))
```

`CtlR` と `BcR` は 35 回目のものです: `farStore` が決めない、添え字やポインタを通す書き込みは `ctl`（`B`）を書かない。触るフレームより前には `CtlStore` がないので、そこでは `bKeep` は `ResidB` でだけ求めます。触るフレームでは、ルーチン、モード、タスクの最初の書き込みのあとでも求めます（歩きはそこで止まる）。

足したフィールドはありません。

変わったシグネチャ（正確に）:

* `PoleJoin.Run.ctlKeep : ∀ n, n + 1 < ixOf … g → ∀ k, PoleNear.ResidC sy m0 (trace (S.seq (a + n)) (S.inp (a + n)) k) → PoleCoin.CtlR (PoleCoin.coinOf sy m0) (trace (S.seq (a + n)) (S.inp (a + n)) k)`。
* `PoleJoin.Run.bKeep : ∀ n, n < ixOf … g → ∀ k, (PoleNear.ResidB sy m0 (trace … k) ∨ ∃ j, j < k ∧ FrameKeep.CtlStore sy (trace … j) = true) → PoleBcol.BcR (PoleBcol.bcOf sy m0) (trace … k)`。
* `PoleJoin.Run.ctl6` は `hm0` のあとに `(hcN : PoleNear.nCheck sy m0 = true) (hcB : PoleBcol.bcolCheck sy m0 = true) (hIB : PoleBcol.BInv (PoleBcol.bcOf sy m0) (R.seq 0))` をとる。
* `PoleParserRun.invJ_run`、`inv_run`、`colMono_run`、`colEdge_run` は `hmK` のあとに `(hcN) (hcB) (hIB)`（同じ型）をとる。`tilesCol_run` は `hmK` のあとに `(hcN : PoleNear.nCheck sy m0 = true)` をとる。`tilesCol_route` は `hcB` のあとに `(hcN : PoleNear.nCheck sy m0 = true)` をとる。
* `PoleBcol.frames_bcol`: `hct` は `∀ n, n < Fr.ix g → ∀ k, frame(trace k) = frame(all n) → pc(trace k) ≠ store → NoW B (trace k)`。`store` での結論に `∧ NoW B ∧ NoW ctl` がつく。`frame_bcol`、`frame_of_walkB`、`live_stepB` は、フレームの命令で、守るバイトのないガードの `CleanK`、`NoW B → CleanK`、`store` 以外での `NoW B` をとる。`cleanK_B` は `BcR` のかわりに `NoW` をとる。`Bc` に新しいフィールド `ctlI`。
* `PoleCoin.frames_coin`: `hct` はフレームの命令でだけ求める。`frame_coin` と `frame_of_walkC` は `CleanK` をそこでだけ求める。
* 新しい記号 2 つ: `SpriteShuffler`、`RenderUnderPart`。
* `route_1_1` は変わらず `1748 + j ≤ L` を結論します。ROM の新しいチェックが 1 つ: `pole_near_walk`（`native_decide`、新しい非公開ファイル `Proof/PoleNear.lean`）。

## 歩きが知らないこと

`ResidC` と `ResidB` の場所で、探索は失敗しました:

* 頭がブロックに当たるときのポインタを通す書き込み: ポインタは彼の位置から来ます。
* 城の行のループと `RenderUnderPart`: エリアのデータから読んだ行から行を描きます。ループの終わりの判定を、歩きは `X` の範囲に使いません（`MetatileBuffer + X = ctl` になる `X` に届きました）。
* `B` については、`store` 以外の、ブロックのバッファへのポインタを通すすべての書き込み: ブロックのバッファの最後のバイトは `B` のすぐ前にあり、歩きはそこで行がバッファの中だと知りません。

## 測ったこと

`pole-keep parser FM2 96`（TAS、900 から 1089 からのランダムな走り、最初の操作からのランダムな走り）。次の数は 3 つすべてで 0 でした:

* 35 回目の `ctlKeep` や `bKeep`（各命令）が偽である命令（どのエリアでも）。
* `ResidC` や `ResidB` の場所で、狭めたフィールドが偽である命令。
* `ctl` や `B` を書く解析の書き込み。

フレーム: TAS で 719、ランダムな走りで 14,318 と 25,980（操作中で始まるフレーム）。フィールドが残る場所の命令:

| | TAS | ランダム 900–1089 | 最初の操作からのランダム |
|---|---|---|---|
| `ResidC` の場所の命令（どのエリアでも） | 354 | 3,742 | 181 |
| `ResidB` の場所の命令（どのエリアでも） | 17 | 16 | 22 |

## `coinBuf` と `readC`: 試したが証明していない

* `coinBuf`。同じ歩きに 3 つ目のテスト（`PoleNear.missB`: その書き込みは `farBuf` が決めるか、割り込みの待ちのない、コインのタイルでないバイトの `STA` か、どの行き先もブロックのバッファを外す）を足すと、書き込みでコインの場所の `BufAt` が出ます（`bufAt_of_missB`、証明した）。しかし探索は 30 より多くの書き込みで失敗します（24 の場所で 993 の失敗、そのあと同じルーチンの 9 の場所で 662）。それらは、ブロックのバッファの前の 256 バイトにある物の配列への、絶対アドレスと添え字を通す書き込みで、歩きは、まとめたあとの添え字も書くバイトも知りません。また、書くバイトが RAM から来るポインタを通す書き込みです。その 1 つは物の箱の書き込み（`BoundingBoxCore`、物のオフセットの 4 倍のところ）です: 歩きの範囲はそこでオフセット 9 から 24 を許すので、歩きの知る限り書き込みはバッファに届きえます。コードでは一番大きいオフセットは 17（雑多な物、オフセット高々 8 に 9 を足す）なので、箱の最後のバイトはバッファの 13 バイト前です。測った書き込みで、バッファにコインのタイルを残すものはありません。`coinBuf` は残ります。
* `readC`。2 つの読みにテスト（状態が許すどのアドレスもブロックのバッファの中）を置くと、探索は当たり判定のルーチンのプレイヤーの読みで失敗します（105 の失敗、`X` は 0 と知られている）。そこで歩きはポインタの上のバイトを知っていますが、下のバイトも `Y` も知りません。なので歩きの知る限り、読みはバッファの終わりの先へ行きえます。読みの前の高さの確認は、歩きが使わない分岐です。`readC` は残ります。

## 証明していないこと

* `ResidC` の場所での `ctlKeep`、`ResidB` の場所と、触るフレームでルーチン、モード、タスクの最初の書き込みのあとでの `bKeep`（偽になるところは測って 0）。
* `coinBuf`、`readC`、`bufAll`、`keepB`、`tilesCol`: 変わらない。

**ファイル。** `Theorems/PoleNear.lean`（新しい）。`Theorems/PoleBcol.lean`（`NoW`、`Bc.ctlI`、`missS`、`store_target`、`store_miss`、`cov_preB0`、歩きとその定理）。`Theorems/PoleCoin.lean`（フレームの命令での `CleanK` と `CtlR`）。`Theorems/PoleJoin.lean`（`ctlKeep`、`bKeep`、`Run.bNoW`、`Run.ctlR`、`Run.ctl6`）。`Theorems/PoleParserRun.lean`（シグネチャ）。`Smbrta/Syms.lean`、`tools/smb-symbols.txt`（`SpriteShuffler`、`RenderUnderPart`）。`Main.lean`（`genPoleNear`、Route のブロック、`pole-keep near-check`、`near-search`、`near`、`pole-keep parser` の数）。
