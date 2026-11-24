[← Back](README-ja.md) | [English](f-6-17-20-PoleOffset.md) | [Japanese](f-6-17-20-PoleOffset-ja.md)

# ブロックのオブジェクトのオフセットを知って、頭が当たるとき

36 回目のラウンド（[制御バイトとブロックのバッファの列に届きうる書き込み](f-6-17-19-PoleNear-ja.md)）は、フィールド `ctlKeep`（添え字やポインタを通す書き込みは画面のバッファの制御バイト `ctl` を書かない。触るフレームより前のフレーム）を、3 種類の場所（`PoleNear.ResidC`）でだけ求めました:

* 頭がブロックに当たるときのコードの中の、ポインタを通す 2 つの書き込み。
* 城の行のループ。
* `RenderUnderPart` の書き込み。

このラウンドは、ブロックのオブジェクトのオフセットが 0 か 1 で始まる各フレームで、1 種類目の場所でもこのフィールドを証明します。

## 36 回目の歩きが頭が当たるときに失敗したわけ

頭が当たるときのコードは、ブロックのオブジェクトのオフセット（`SprDataOffset_Ctrl`）を添え字にして、ゼロページを通して書きます。36 回目の歩きはオフセットを知りません。なので、歩きの知る限り、そのような書き込みがブロックのバッファのポインタを書くかもしれず、歩きはポインタの上のバイトを失います。するとそのポインタを通す書き込みはどこへでも、`ctl` へも行けます。

## 言葉

* `InvS(m)`（`PoleOffset.InvS`）: 状態 `m` で、ブロックのオブジェクトのオフセットのビット 1 から 7 が 0。1 つの状態の条件です。
* `ResidC(m)`（`PoleOffset.ResidC`）、`ctlKeep` が残る場所: 城の行のループ（`CRendLoop` から `ChkCFloor` まで）と `RenderUnderPart` の書き込み。`PoleNear.ResidC` の 3 種類のうちの 2 つです。
* `NoW(s, m)`、`CtlStore(m)`、`store` は 36 回目のものです。

## 歩き（`Theorems/PoleOffset.lean`）

36 回目の歩きに 3 つの変更をしたものです:

* ガード `guardO` は、オフセットも守る `FrameKeep.guardE` です。その `CleanK` は、フィールド `keep.cleanE` とフィールド `keepB`（`PoleTileKeep.KeepB`: 添え字やポインタを通す書き込みはオフセットを書かない）から来ます（`cleanK_O`、`noW_of_keepB`）。
* フレームの始まりの状態 `startO` は、オフセットのビット 1 から 7 が 0 だと知っています。`InvS` を満たす機械を覆います（`sim_startO`）。
* 各ステップのあと、`SideAcross.fixP` が、ポインタを通す書き込みが届かないゼロページの各バイトを取り戻します（パート e の歩き `SideAcross.walkP`）。

`store` 以外の、添え字やポインタを通す各書き込みで、歩きは、その書き込みが `ctl` を外すこと（`PoleNear.missT`）か、`ResidC` の場所であることを求めます（`okO`）。道は `CtlStore` で止まります。

ROM では、表は 67,672 状態です。探索は 14 秒、チェック `PoleOffset.oCheck` はネイティブで 16 秒かかります（0.5 GB、`pole-keep offset-check`）。このラウンドから `PoleNear.nCheck` は、36 回目のチェック（`PoleNear.nCheckN`）とこのチェックです。両方で 33 秒です。

## 証明すること

`off_frame`: 操作中のフレーム `m` で、`InvS(m)` で始まり、その命令が `guardE` の `CleanK` と `KeepB` を満たすもの。各 `k` で:

```
(∀ j < k, ¬CtlStore(trace(m, j)))  ∧  frame(trace(m, k)) = frame(m)  ∧  pc(trace(m, k)) ≠ store  ∧  ¬ResidC(trace(m, k))
    →  NoW(ctl, trace(m, k))
```

`off_frames`: `InvS` で始まる各フレーム `n < ix g` で同じこと。`invS_frames`: 操作のときの事実（`PoleTileCtl.watch₀`、`PoleTileCtl.colMap₀`）があれば、各フレーム `n < ix g` は `InvS` で始まる（`PoleTileKeep.frames_keepY`）。

`PoleJoin.Run.ctlR`（シグネチャは同じ）: `n + 1 < ix g` の各フレーム `n` で、フレームの各命令で `CtlR`:

* `store` では `PoleBcol.frames_bcol` から。
* `ResidC` では `ctlKeep` から。
* `InvS` で始まるフレームでは、ほかは `off_frames` から。
* `InvS` で始まらないフレームでは、`PoleNear.ResidC` では `ctlKeep` から、ほかは 36 回目の `PoleNear.near_frames` から。

## フィールド

狭めました（前より求めることが少ない）:

```
ctlKeep :  ∀ n, n + 1 < ix g → ∀ k,
    (ResidC(trace(all n, k))  ∨  (¬InvS(all n) ∧ PoleNear.ResidC(trace(all n, k))))  →  CtlR(trace(all n, k))
```

36 回目は `PoleNear.ResidC(trace(all n, k)) → CtlR(trace(all n, k))` を求めました。新しいフィールドは、城のループと `RenderUnderPart` では同じことを求め、頭が当たるときのコードでは `InvS` で始まらないフレームでだけ求めます。ルートの各フレームは `InvS` で始まります（`invS_frames`）。でも `ctlKeep` を使う定理（`Run.ctlR`、`Run.ctl6`、`PoleParserRun` の定理）は `PoleNear.nCheck` だけを取り、操作のときの事実を取らないので、フィールドにはその場合が残ります。フィールドは足していません。ほかのフィールドは変わりません。

シグネチャ: 定理のシグネチャは変わっていません。`PoleNear.nCheck` は `PoleOffset` で `PoleNear.nCheckN && PoleOffset.oCheck` と定義します。前のチェックは `PoleNear.nCheckN` で、`PoleNear.near_frame`、`near_frames` はそれを取ります。プライベートな証明 `pole_near_walk : PoleNear.nCheck sy ctx = true` は `Theorems.PoleOffset` を読み込みます。`route_1_1` の結論は今も `1748 + j ≤ L` です。

## 残る場所で歩きが知らないこと

* 城のループは、城のオブジェクトのデータがくれる行から始まります。始めの行が 11 以上だと、ループはページ全体を回ります。
* `RenderUnderPart` は、呼ぶ側がくれる行から描きます。探索は、階段から `MetatileBuffer + X = ctl` の `X` に届きました: 階段は、フレームをまたいで残るバイト `StaircaseControl` を添え字にして表から行を読み、歩きはそのバイトを知りません。

## 測ったこと

`pole-keep parser FM2 96`（TAS、900 から 1089 からのランダムな走り、最初の操作からのランダムな走り。操作中に始まるフレーム）:

| | TAS | ランダム 900–1089 | 最初の操作からのランダム |
|---|---|---|---|
| 操作中に始まるフレーム | 719 | 14,318 | 25,980 |
| そのうち `InvS` でないもの | 0 | 0 | 0 |
| 36 回目の `ctlKeep` を求めた命令（`PoleNear.ResidC`、どのエリアでも） | 354 | 3,742 | 181 |
| 狭めた `ctlKeep` を求める命令 | 352 | 3,738 | 170 |
| そのうちそれが偽のもの | 0 | 0 | 0 |

なのでこれらの走りでは、フィールドは城のループと `RenderUnderPart` でだけ求めます。頭が当たるときのコードの命令（2、4、11）は証明しました。

## 試して、残さなかったこと: 歩きの中の彼の高さ

もっと細かい歩きが、彼の当たり判定のルーチンを通して彼の高さを追いました: ルーチンの中で高さを読み込むたびに、ルーチンが比べる高さのあいだの、知られているビットのかたまりに高さを分けました。ブロックのバッファのルーチンでは、2 つの足し算で `A` と `Y` をその値に分けました。キーには、ルーチンとそれが呼ぶルーチンの中で、高さ、ゼロページのバイト 2、ポインタの下のバイトを入れました。探索で測りました（証明の一部ではありません）:

* 頭が当たるときの書き込み（当たったブロック）で `bKeep` を証明します。表は 143,692 状態、42 秒で、このラウンドの表の 2 倍より大きいです。
* 当たったブロックの上の書き込み（`CheckTopOfBlock`）で失敗します: そこでは、歩きは彼の大きさが 0 か 1 であることを要ります（頭の上の限りの表を大きさで読む）。それを証明するものはまだありません。
* `ErACM` の書き込みで失敗します: 当たり判定のルーチンが呼ぶルーチンの中で、歩きは高さを失います（歩きが知らない添え字を足してゼロページを通す書き込みは、ゼロページを忘れます）。足の判定は、画面の下の判定なしに、高さをまた分けます。
* `readC`（彼の当たり判定の読み込み）には、同じ大きさのことと、1 つの道で 2 回読む、しゃがみの旗と泳ぎの旗が合うことと、敵の読み込みの添え字が 0 でないことが要ります。

なので `bKeep`、`readC`、`coinBuf` は前のままです。キーに旗を入れると、細かい歩きの表は 717,085 状態になりました。

## 証明していないこと

* 城のループと `RenderUnderPart` での `ctlKeep`。`InvS` で始まらないフレームでの、頭が当たるときのコードでの `ctlKeep`（ルートにはそういうフレームはない）。
* `bKeep`、`coinBuf`、`readC`、`bufAll`、`keepB`、`tilesCol`: 変わらない。

**ファイル。** `Theorems/PoleOffset.lean`（新しい）。`Theorems/PoleNear.lean`（前のチェックを `nCheckN` に名前を変えた）。`Theorems/PoleJoin.lean`（`ctlKeep`、`Run.ctlR`、`Run.bNoW` のチェックの使い方）。`Main.lean`（`genPoleNear` は `Theorems.PoleOffset` を読み込む、`pole-keep offset-check`、`offset-search`、`pole-keep parser` の数）。
