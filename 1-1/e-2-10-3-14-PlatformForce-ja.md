[← Back](README-ja.md) | [English](e-2-10-3-14-PlatformForce.md) | [Japanese](e-2-10-3-14-PlatformForce-ja.md)

# スクロールへの足場の力

**主張（第 27 回）.** 触る前の数えるフレームのそれぞれで、スクロールの処理 `Q` では、スクロールへの足場の力は 0 です（`SurfaceFrames.OnFrames.platQ`）:

```
1 ≤ j < g  →  ∃ kq ≥ arrAt(fm j, pad j),  pc(Q) = PlayerSubs  ∧  plat(Q) = 0、      Q = trace(fm j, pad j, kq)

plat(m) = スクロールの処理が、動きの書くバイトに足すバイト（Platform_X_Scroll）
```

だから `Q` でのスクロールの量は、動きの書くバイトです。X(Q) = xs(Q)。`OnFrames` のフィールド `near` は、1 つの状態 `Q` の、この簡単な条件を求めるようになりました（`EdgeStep.NearX`）:

```
NearX(Q)  :=  Allows(Q)  →  left16(Q) + xs(Q) + 2 ≤ pixel16(Q)

near_of_x :  NearX(Q) ∧ plat(Q) = 0  →  Near(Q)        Near(Q) := Allows(Q) → left16(Q) + X(Q) + 2 ≤ pixel16(Q)   （第 26 回）
```

`Allows`、`left16`、`pixel16` はスクロールの規則（1-1-e-2-10-3-12）とフレームの端の進み（1-1-e-2-10-3-13）と同じです。新しいフィールドはありません。`FrameKeep.guardE` はバイトを 1 つ多く守ります。足場の力です（70 バイト。`chg.upCleanU` の合わせたガードは 147）。だから `keep.cleanE` と `chg.upCleanU` は少し多くを求めます: 添字かポインタでの書き込みは、このバイトを書きません。

**証明.** フレームの端の進み（1-1-e-2-10-3-13）の歩きが、このバイトを 3 つ目のバイトとして追います（`EdgeStep.eI`）:

1. 操作の始めでは 0 です。横の土管から出る切り替えの行がこのバイトを知っていて、その値は操作の始めの機械の値です（`SurfaceFrames.Start.plat`）。そこでは 0 です（`numbersCheck`）。だから plat(seq 0) = 0（`AreaRun.plat₀`）。
2. 数えないフレームはこれを保ちます（`EdgeStep.keep_noCut`、`OnFrames.edgeLag`）。数えるフレームも、始めから `Q` までこれを保ちます（`EdgeStep.keep_q`）。
3. スクロールの処理は、終わりにこれに 0 を書きます。`Q` から呼び出しの次の命令（`R = PlayerSubs + 3`）までの歩きは、そこでこれを 0 と知っています（`EdgeStep.atR`、`rCheck` の一部）。
4. `R` からフレームの終わりまで、このバイトは保たれます（`EdgeStep.keep_r`）。ROM でこれへのほかの書き込みは、足場のルーチンの中の 1 つだけです。それは彼の位置へのアドレスでの書き込みのすぐあとにあります。フィールド `posW` はその書き込みを除き、歩きはそこで道を止めます（`cutPos`）。

だから 1 ≤ j < g で plat(seq j) = 0（`OnFrames.platEnd`）、そして plat(Q) = plat(seq (j − 1)) = 0 です（`OnFrames.platPrev`、`OnFrames.platQ`）。フレームの端の進み（`OnFrames.edgeAt`）は、`Near(Q)` を `NearX(Q)` と `plat(Q) = 0` から取るようになりました（`EdgeStep.near_of_x`）。`edgeAt` と `platEnd` の証明の共通の部分は `OnFrames.scrollAt` です。

**ROM での確認.** `EdgeStep.qCheck` と `EdgeStep.rCheck` は 3 つのバイトを追うようになりました。`numbersCheck` は plat(B.m) = 0 と、スクロールの処理の足すバイトがこのバイトであることも確かめます（`Numbers.platB`、`Numbers.platP`）。変更の前に、新しい 3 つの部分のネイティブの試しが通りました（読み込みを入れて 30 秒）。

**測ったこと**（最後のプログラムで、終了コード 0）:

| 確認 | 何を | 結果 |
|---|---|---|
| `edge-real FM2 256` | スクロールの処理とフレームの始めでの足場の力。スクロールの処理での `NearX`: 852 からの動画、左端で土管に向かう走り、自分の乱数の走り | 137,955 フレーム。力が 0 でないスクロールの処理は 0、フレームの始めも 0。スクロールが許されるスクロールの処理は 11,289 で、そこでの pixel16 − left16 − xs − 2 の最小は 78（`NearX` は ≥ 0 を求める）、X の最大は 3。`near` の失敗は 0 |
| `surface-frames-check FM2 200` | `movesScan` の条件のうちの `near`（`NearX`）。行からの操作の始めの状態（`Start`、新しいバイトも） | 8 つの集まり、239,510 フレーム、`Moves` と `near` を確かめたフレーム 215,433: 失敗 0。切り替えの 201 の走りが `Start` の状態で操作の始めに来る |
| `keep-frames-check FM2 100` | 地上のすべての命令（数えるフレームも数えないフレームも）での、新しい `guardE` の `CleanK` | 224,813 フレーム。守るバイトへの添字かポインタでの書き込みはない |
| `up-clean-u FM2` | 縦の土管までのフレームでの、`chg.upCleanU` のガードの `CleanK` | `guardE` は 70 バイト（前は 69）、合わせたガードは 147（前は 146）。221,490 フレーム、それに反する命令はない |
| `route-check`（動画。1089 `02808080`。996 と第 23 回のジャンプの走り） | ルート | 触るのは 1092、1093、1396。レベルの切り替えは 1748、1748、2063 |
| `collide-real FM2 200`、`pos-after-real FM2 200`、`pos-keep-real FM2 64` | パート e のほかのフィールド | 終了コード 0 |

**証明していないこと.** `NearX(Q)` は仮定です。この回に試して測ったこと:

* そのかわりに、フレームの始め `M` での条件。測ったこと（`edge-real`）: 彼の場所のバイトがスクロールのしきい値以上で、横の当たりのタイマーが 1 以下のところでは、pixel16(M) − left16(M) ≥ 80 です。バイトがしきい値以上で、pixel16(M) − left16(M) がしきい値より小さいところでは、タイマーは 16 です（押し戻しのすぐ次のフレーム: 彼は端より 1 px 左にいるので、バイト (pixel − left) mod 256 は 255）。`EdgeStep` の歩きはタイマーを運べません: フレームのタイマーの部分は、添字での書き込みでタイマーを減らします。`CleanK` は、そういう書き込みがどれも守るバイトを外れることを求めます。
* 同じ条件を、タイマーの部分のあと、プレイヤーのルーチンに最初に来たところで。新しい歩きが、横のタイマー、場所のバイト、スクロールのロック、端をそこからスクロールの処理まで運びます。スクロールの量の上限と合わせると、`collide` なしでフレームの端の進みが出ます（証明した: [プレイヤーのルーチンでの彼の場所](e-2-10-3-15-PlaceKeep-ja.md)）。使っていません: この条件は `surface-frames-check` の書き換えた 8,640 の状態で偽で、そこでも `near` は成り立ちます。
* スクロールの量: 動きの書くバイト（`xs`）は、本当のフレームでは 3 以下です。でも動きのモデル（`FrameModel`）はそれを知りません。

**ファイル:** `Theorems/SurfaceFrames.lean`（`Start.plat`、`numbersCheck`、`AreaRun.plat₀`、`AreaRun.platP`、`OnFrames.scrollAt`、`platEnd`、`platPrev`、`platQ`、`edgeAt`、フィールド `near`）。ほかに変えたもの: `Theorems/EdgeStep.lean`（`platI`、`eI`、`atR`、`keep_r`、`NearX`、`near_of_x`）、`Theorems/FrameKeep.lean`（`edgeE`）。`Main.lean`: `edge-real` がこのバイト、`NearX`、フレームの始めの条件を測ります。
