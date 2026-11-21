[← Back](README-ja.md) | [English](e-2-10-3-15-PlaceKeep.md) | [Japanese](e-2-10-3-15-PlaceKeep-ja.md)

# プレイヤーのルーチンでの彼の場所

**主張（第 27 回）.** 2 つの定理です。証明しましたが、ルートではまだ使いません（`Theorems/PlaceKeep.lean`）。

1. `PlaceKeep.keep_place`: 操作中のフレームは、プレイヤーのルーチンに最初に来たところ `n₀` から、そのあとの最初のスクロールの処理 `Q` まで、5 つのバイトを保ちます: 横の当たりのタイマー、画面での彼の場所、スクロールのロック、画面の左端のピクセルとページ（`placeI`、スクロールの処理の読み込みのオペランド）。条件は端の歩き（1-1-e-2-10-3-13）と同じです: フレームは操作中に始まり、どの命令も `guardF` の `CleanK` を満たし、ルーチン、モード、タスクを番地で書かず、エリアのバイトが分かっています。ROM での確認は `PlaceKeep.placeCheck` です（ネイティブで true、読み込みを入れて 3.4 秒。`numbersCheck` には入れていません。あとの回がそこに入れれば、`keep_place` はルートのフレームで成り立ちます）。

```
∀ x ∈ placeI,  ram(Q)[x] = ram(n₀)[x]
```

2. `PlaceKeep.edge_step_place`: フレームの端の進みを、それぞれ 1 つの状態の 2 つの条件から出します。`collide` は使いません:

```
PlaceAt(n₀)  :=  side(n₀) = 0  →  thr ≤ pfs(n₀)  →  left16(n₀) + thr ≤ pixel16(n₀)
AmountAt(Q)  :=  Allows(Q)  →  xs(Q) + 1 ≤ thr

side = 横のタイマー、pfs = 画面での彼の場所、thr = スクロールの 1 つ目のしきい値（80 px）、xs = 動きの書くバイト

スクロールの規則（Q → R） ∧ edge(Q) = edge(M) ∧ edge(b) = edge(R) ∧ keep_place ∧ pixel16(n₀) = pixel16(M) ∧ PlaceAt(n₀) ∧ AmountAt(Q) ∧ plat(Q) = 0
   →  edge(b) ≤ max(base(M), P(b))
```

端が動くとき: edge(b) = edge(R) ≤ 256·(left16(n₀) + Y) + 255 ≤ 256·(pixel16(M) − 1) + 255 < P(M) ≤ base(M)。ここで Y ≤ xs(Q) ≤ thr − 1。

**歩き.** `FrameKeep.guardE` は横のタイマーを守れません: フレームのタイマーの部分は、添字での書き込みでタイマーを減らします。`CleanK` は、そういう書き込みがどれも守るバイトを外れることを求めます。だから `walkQP` はバイトを守らずに追います。このとき、歩きが行き先を知らない書き込みがあると、追うのが止まります（`PipeWrites.AS.forgetK`）。`n₀` と `Q` のあいだで、そういう書き込みは動きのルーチンの中だけにあります: それは端数、ピクセル、ページを添字で書きます。その行き先は 5 つのバイトのどれでもありえません（どの添字でもそのバイトに届かない絶対番地 `PositionKeep.absFarAt` か、256 より下のゼロページ）。そういう書き込みでは `walkQP` は追うのを続けます（`kstepP`、`s_kstepP`。`StepWrites.step_ram` を使う）。この歩みなしでは、歩きの表の 14 の状態が、動きのルーチンの書き込みでバイトを失いました。この歩みありでは、0 です。

**フィールドとしては偽.** この回は、フィールド `near` のかわりに `place := PlaceAt(n₀)` と `amount := AmountAt(Q)` を置くことも試しました（そうすると `edgeAt` は `collide` を使いません）。ビルドは通り（`prove.py` 終了コード 0、`route_1_1` に `sorryAx` なし）、`edge-real FM2 256` は 137,955 フレームで失敗を見つけませんでした。でも `surface-frames-check FM2 200` は終了コード 1 でした: `place` は、その集まり「階段のあたりの書き換えた状態」の 8,640 フレームで偽です。この集まりは、動画の 200 フレーム目の状態をとり、彼の位置（そこから左 48 px から右 46 px まで）、高さ、速さ、状態を書き換えますが、場所のバイトは書き換えません。左 48 px から 34 px までの 8 つのずれでは、彼は端から 64 から 78 px 右にいるのに、バイトは 112 くらいのままです: 8 × 30 × 4 × 3 × 3 = 8,640 の走り。測った本当のフレームではどれも、フレームの始めのバイトは (pixel − left) mod 256 で、ほかの 7 つの集まり（239,510 − 103,680 フレーム）では `place` は一度も偽になりません。`near` は 8 つの集まりのすべてで成り立つので、ルートは `near` のままです。

**測ったこと**（フィールドで試したときのプログラムで。歩きの確認はネイティブで）:

| 確認 | 何を | 結果 |
|---|---|---|
| `placeCheck` のネイティブの試し | 5 つのバイトの歩き | true |
| `edge-real FM2 256` | `place` と `amount` | 137,955 フレーム、失敗 0。許されるスクロールの処理での xs の最大は 3。バイトがしきい値以上で横のタイマーが 0 の、ルーチンに来たところでの pixel − left の最小は 80 |
| `surface-frames-check FM2 200` | `place` と `amount` | `place` は上の書き換えた 8,640 フレームで偽。`amount` は 0。ほかの条件はすべて 0 |

**証明していないこと.** `PlaceAt` と `AmountAt`。`PlaceAt` には、前のフレームのスクロールの処理から描画まで（補正、押し戻し）と、このフレームのタイマーの部分が要ります。`AmountAt` には、動きのモデル（`FrameModel`）が動きの書くバイトを知ることが要ります。

**ファイル:** `Theorems/PlaceKeep.lean`（`zpIOps`、`miss_loc`、`farRk`、`kstepP`、`s_kstepP`、`walkQP`、`qP_run`、`placeI`、`pbCfg`、`placeCheck`、`keep_place`、`PlaceAt`、`AmountAt`、`edge_step_place`）。ほかのファイルはこれを使いません。
