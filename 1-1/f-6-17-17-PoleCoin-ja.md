[← Back](README-ja.md) | [English](f-6-17-17-PoleCoin.md) | [Japanese](f-6-17-17-PoleCoin-ja.md)

# 旗のタイル: ブロックのバッファにコインがないので、制御バイトは 6 でない

33 回目のラウンドはフィールド `ctlU` を残しました（[エリアの解析の遅れは 157 px まで増えてよい](f-6-17-15-PoleLag-ja.md)）: 触るフレームより前の、プレイヤーのルーチンに来る各フレームの各 `UpdScrollVar` で、画面のバッファの制御バイトが 6 でないか、そこで解析の遅れ `S + 3·N` が 157 より小さい。このラウンドは `ctlU` をなくします。1 フレーム全体の歩きが制御バイトを追い、これらのフレームのどの `UpdScrollVar` でも 6 でないことを証明します。かわりに、`bufAll` や `keepB` と同じ種類の 3 つの条件が入ります: ブロックのバッファへの書き込み、その読み、制御バイトへの書き込みについての条件です。

## コードが制御バイトにすること

* 各フレームの始まりの画面の更新が、制御バイトを 0 にします。
* ゲームの中心で `UpdScrollVar` より前に制御バイトを書くのは `RemoveCoin_Axe` だけで、6 を書きます。これが走るのは、プレイヤーの当たり判定のルーチンがコインのタイルを見つけたとき（頭、足、横で）、斧に触ったとき、たたいたブロックの上の確かめ（`CheckTopOfBlock`）がコインのタイルを見つけたときです。
* 斧のコードは、モードもアドレスで書きます。触るフレームより前のフレームは、モードをアドレスで書きません（`FrameKeep.Frames.noStore`）。

なので、`UpdScrollVar` で制御バイトが 6 になるのは、マリオがコインを取るフレームだけです。1-1 の地上では、ブロックのバッファにコインのタイルはありません。

## 言葉

* コインのタイルは、コインの確かめが比べる 2 つのタイルのどちらかです（`sy.CoinTile`、`sy.CoinTile2`: `CheckForCoinMTiles` の 2 つの比べの値）。
* `ctl` は画面のバッファの制御バイトです（`UpdScrollVar` の最初の読み込みの値の場所）。
* 機械 `m` のコインの地図: ブロックのバッファのどのバイトもコインのタイルを持たない。これは、場所 `PoleCoin.Coin.Q` の `PoleTileWalk.ColMap` です: 旗の地図の場所で、旗のタイルのかわりに 2 つのコインのタイルを持ち、列を持たないものです。
* 2 つの読み: 当たり判定のルーチンのブロックのバッファの読み（その `LDA (zp),Y`、`Spots.read`）と、たたいたブロックの上の確かめの読み（`CheckTopOfBlock` の `LDA (zp),Y`）です。

## 歩き（`Theorems/PoleCoin.lean`）

`walkC` は、`FrameKeep` の操作中の 1 フレーム全体の歩きに、途中のテストと分け方を足したものです:

* ガードは `FrameKeep.guardK` に `ctl` も守らせたものです（`guardC`）。なので、歩きが行き先を知らない書き込みも `ctl` を保ちます。画面の更新の 0 の書き込みで `ctl` は知られます。
* プレイヤーの読み（添え字 `X` が 0 と知られている）のすぐあとと、たたいたブロックの上の読みのすぐあとで、読んだバイトを、2 つのコインのタイルが等しいビットごとに 1 つの片に分けます: 各片ではそのビットが知られ、1 つ目のコインのタイルと違います（`pieceC`）。ROM の値のチェックが、これらの片がコインのタイルでないどのバイトも含むことを示します（`PoleEntryRule.tilesCover`）。これで、コインの確かめはコインのコードへ分かれません。
* 道は、ルーチン、モード、タスクをアドレスで書く命令で止まります（`FrameKeep.walkKC` と同じ）。
* 途中のどの状態でも: `UpdScrollVar` で `ctl` が知られていて 6 でない（`ctlOK`）。ステップはブロックのバッファのバイトを書かないか、添え字やポインタを通す書き込みである（`PoleTileWalk.okSK`）。2 つの読みのすぐあとの状態は、NMI の待ちなしにその読みから来る（`pairC`）。

歩きの表は探索から来ます（証明の一部ではない）。ROM では 5,854 状態で、チェックはネイティブで 0.4 秒です（`pole-keep coin`）。

## 片が正しいわけ（`coinRead_after`、`frame_of_walkC`）

歩きはコインの地図をステップからステップへ運びます: `okSK` が許すステップはブロックのバッファのバイトを書かないか、添え字やポインタを通す書き込みで、それはそこにコインのタイルを書きません（`BufAt`）。2 つの読みで、読んだバイトがコインのタイルなら、読みはブロックのバッファの中です（`ReadC`）。地図は、そこにコインのタイルのバイトはないと言います。なので、読んだバイトはコインのタイルではありません:

```
ColMap(m) ∧ ReadC(m) ∧ m が NMI の待ちなしに 2 つの読みのどちらかにある   ⇒   ¬ coin(ステップのあとの A)
```

## 1 フレームと、触るフレームより前のフレーム

`frame_coin`: `FrameStart` からのフレームで、その命令が歩きのガードの `CleanK` を満たし、ルーチン、モード、タスクをアドレスで書かず、`BufAt` と `ReadC` を満たすなら、コインの地図を保ち、フレームの各 `UpdScrollVar` で `ctl ≠ 6` です。

`frames_coin`: 操作の始まりでコインの地図があれば、触るフレームより前の各フレーム `n`（`n + 1 < ix g`）で:

```
ColMap(all n)   ∧   ∀ k,  pc(trace(all n, k)) = UpdScrollVar  →  frame(trace(all n, k)) = frame(all n)  →  ctl(trace(all n, k)) ≠ 6
```

`PoleJoin.Run.ctl6` がこれをルートのフレームで読みます。これは、`ctlU` が `PoleStrict.invJ_onFrames` に渡していた条件（その 1 つ目の場合、`ctl ≠ 6`）を与えます。なので、解析の不変式、`JY`、列の進みは、制御バイトについてのフィールドを要りません（`PoleParserRun.invJ_run`、`colMono_run`）。

## 操作の始まりの地図（`PoleParserRun.coinMap₀`）

横の土管から出る変化の行の、操作できるどの状態でも、ブロックのバッファのどのバイトも知られていて、どれもコインのタイルではありません（`coinMapK`、非公開の `pole_coin_rows`）。旗の地図（`PoleTileCtl.colMap₀`）と同じく、操作の始まりの機械はこれらの行にあります。

## フィールド

なくなったもの: `ctlU`。

足したもの。それぞれ、触るフレームより前の各フレーム `n`（`n + 1 < ix g`）の各命令で:

```
coinBuf :  PoleKeepFar.BufV(Coin.Q, trace(all n, k))
           （添え字やポインタを通す書き込みは、ブロックのバッファにコインのタイルを残さない。farBuf が片づけない書き込みにだけ求め、
            STA abs,X、STA abs,Y、STA (zp),Y には A がコインのタイルを持つときだけ求める）
readC   :  (pc = read ∧ X = 0)  ∨  pc = top   →   coin(読んだバイト)  →  読みは RAM の、ブロックのバッファの中
ctlKeep :  farStore([ctl]) = false  →  添え字やポインタを通す書き込みは ctl を書かない
```

`coinBuf` は、`bufAll` が旗のタイルに求めることをコインに求めます。`ctlKeep` は `keepB` の種類です。`readC` は、コインのタイルを見つけるプレイヤーの読み（またはたたいたブロックの上の読み）がブロックのバッファの中にあることを求めます。ほかの物の読みには求めません（`LDA (zp),Y` は `X` を保つ: `PoleCoin.step_lda_izy_x`。なので読みのすぐあとの状態は、それがプレイヤーの読みだったことを知ります）。

新しいフィールドは `ctlU` より弱くはありません: `ctlU` は遅れが 157 px 以上のところでだけ何かを求めました（測ったところでは 0 回）。新しいフィールドはどのフレームでも求めます。けれども、どれも 1 命令の条件で、解析の遅れには触れません。

変わったシグネチャ（正確に）:

* `PoleJoin.Run`: フィールド `ctlU` はない。新しいフィールド `coinBuf`、`readC`、`ctlKeep`（上のとおり）。
* 新しい: `PoleJoin.Run.ctl6 (R) (hk : FrameKeep.keepCheckOf sy m0 = true) (hcC : PoleCoin.coinCheck sy m0 = true) (hs0 : FrameKeep.StartK sy m0 (R.seq 0)) (hw0 : FrameKeep.Watched (FrameKeep.watchOf sy) (R.seq 0)) (hm0 : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))`。
* `PoleParserRun.invJ_run`、`inv_run`、`colMono_run`、`colEdge_run`、`tilesCol_run` は、`hJ` のあとに `(hcC : PoleCoin.coinCheck sy m0 = true) (hmK : PoleTileWalk.ColMap (PoleCoin.coinOf sy m0).Q (R.seq 0))` をとる。
* `PoleParserRun.tilesCol_route` は、`hmL` のあとに `(hmK : coinMapK sy m0 nm₂ nx₂ (SideTransition.entry m0) 160 122 rt = true) (hcC : PoleCoin.coinCheck sy m0 = true)` をとる。
* `PoleParserRun` に新しい: `coinMapK`、`EndRunQ.coinMap`、`coinMap₀`。
* 新しい記号 2 つ: `CheckTopOfBlock` と `CoinTile2`（2 つ目のコインのタイル、`byte:CheckForCoinMTiles+5`）。`tools/smb-symbols.txt` と `Smbrta/Syms.lean` に。
* `route_1_1` の結論は今も `1748 + j ≤ L` です。ROM の新しいチェックは 2 つ: `pole_coin_walk` と `pole_coin_rows`（`native_decide`、新しい非公開のファイル `Proof/PoleCoin.lean`）。

## 測ったもの

`pole-keep parser FM2 96` で、操作の中で始まるフレームのすべての命令（TAS、900 から 1089 のフレームからの Start ありとなしの自分の乱数の入力、最初の操作からの自分の乱数の入力。719、14,318、25,980 フレーム）:

| | TAS | 乱数 900–1089 | 最初の操作からの乱数 |
|---|---|---|---|
| 地上の `UpdScrollVar` での `ctl` | いつも 0 | いつも 0 | いつも 0 |
| `ctl` への、添え字やポインタを通す書き込み（どのエリアでも） | 0 | 0 | 0 |
| プレイヤーの当たり判定のルーチンの読み | 4,943 | 69,356 | 130,621 |
| たたいたブロックの上の読み | 2 | 4 | 11 |
| これらの読みのうち、ブロックのバッファの外（どのエリアでも） | 0 | 0 | 0 |
| 地上でコインのタイルを読んだ | 0 | 0 | 0 |
| ブロックのバッファにコインのタイルがある地上のフレームの始まり | 0 | 0 | 0 |
| 地上で、ブロックのバッファにコインのタイルを残す、添え字やポインタを通す書き込み | 0 | 0 | 0 |
| `readC` が偽の命令（どのエリアでも） | 0 | 0 | 0 |
| `ctlKeep` が偽の命令（どのエリアでも） | 0 | 0 | 0 |

`pole-keep parser` の終了コードは、いま地上でこれらを求めます（終了コード 0）。TAS がコインを取るのは地下の部屋だけです。

## 証明していないこと

* `coinBuf`: 地上で、添え字やポインタを通す書き込みがブロックのバッファにコインのタイルを残さないこと。エリアの解析は面のデータから列を描きます。1-1 の地上ではそこにコインはありません。証明には、解析の歩きが書くメタタイルを追う必要があります。
* `readC`: コインのタイルを見つける読みがブロックのバッファの中にあること。当たり判定のルーチンの高さの確かめは、マリオのどの読みも 13 行の中に保ちます（測った: ブロックのバッファの外の読みはない）。けれども、歩きはそこで高さを知りません。
* `ctlKeep`: 添え字やポインタを通す書き込みが制御バイトを書かないこと（測って 0）。
* `tilesCol`（`TileSlotC`）、`bufAll`、`keepB`: この一歩では変えていません。

**ファイル.** `Theorems/PoleCoin.lean`（新しい）。`Theorems/PoleJoin.lean`（フィールド、`Run.ctl6`）。`Theorems/PoleParserRun.lean`（`coinMapK`、`EndRunQ.coinMap`、`coinMap₀`、新しい仮定）。`Smbrta/Syms.lean`、`tools/smb-symbols.txt`（記号 2 つ）。`Main.lean`（`genPoleCoin`、Route のブロック、`pole-keep coin`、`pole-keep parser` の 35 回目の数）。
