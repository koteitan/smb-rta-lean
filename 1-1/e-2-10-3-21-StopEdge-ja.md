[← Back](README-ja.md) | [English](e-2-10-3-21-StopEdge.md) | [Japanese](e-2-10-3-21-StopEdge-ja.md)

# 画面の左端で彼を止めるフレーム

フィールド `Moves.stop`（第 28 回）は、次のフレームについてのものです: スクロールの処理で右に動いていて、速さ 0 で終わり、スクロールの処理での位置で終わる。そのようなフレームでは、スクロールの処理での位置はフレームの始めの位置より高々 1 px 先、と求めます。第 31 回はそのようなフレームを 6 つ測りました。どれも画面の端での補正が 1 回あり、押し戻しはありませんでした。測ったどの補正も左端での補正でした。ここでは、スクロールの処理で彼が画面の左端かその左にいるフレームを証明します（フレームが左端かその右で始まるとき）。フィールドはそれ以外のフレームでだけ求めます。

**主張（第 32 回）.** 次のように書きます。

```
a       = 1 つ前の数えるフレームの終わり（seq (j − 1)）、 b = フレームの終わり（seq j）
Q       = プレイヤーのルーチンに来たあと、スクロールの処理の呼び出し（PlayerSubs）に来る最初の命令
pix(m)  = 彼のピクセルとそのページ（2 バイト）、 left(m) = 画面の左端とそのページ（2 バイト）
P(m)    = 256·pix(m) + f(m)、 f は端数。 v(m) = 彼の速さ
```

`StopEdge.stop_of_edge`:

```
pix(Q) ≤ left(Q)  ∧  left(a) ≤ pix(a)  ∧  left(Q) = left(a)   →   P(Q) ≤ P(a) + 255
```

`SurfaceFrames.OnFrames.stopAt`: 1 ≤ j ≤ T、j < g で、きれいな状態 `a` からの数えるフレーム `j` のどれでも、古いフィールド（いまは定義 `StopAt`）が成り立つ:

```
0 < v(Q)  ∧  v(b) = 0  ∧  P(b) = P(Q)   →   P(Q) ≤ P(a) + 256
```

これを狭めたフィールド `Moves.stop` から示します:

```
0 < v(Q)  ∧  v(b) = 0  ∧  P(b) = P(Q)  ∧  (left(Q) < pix(Q)  ∨  pix(a) < left(a))   →   P(Q) ≤ P(a) + 256
```

**証明.** left(Q) < pix(Q) か pix(a) < left(a) なら、フィールドです。そうでなければ pix(Q) ≤ left(Q) かつ left(a) ≤ pix(a) です。フレームは始めから `Q` まで左端の 2 つのバイトを保ちます（`EdgeStep.keep_q`。`Q` はプレイヤーのルーチンに来たあとスクロールの処理の呼び出しに来るただ 1 つの命令: `GuardE.subs_onceE`）。`a` とフレームの始めのあいだの数えないフレームも保ちます（`OnFrames.edgeLag`）。だから left(Q) = left(a) で、`stop_of_edge` から P(Q) ≤ P(a) + 255 です。`stop_of_edge` では、`Q` でのピクセルは `a` でのもの以下で、端数は 256 より小さい。

定理は `StopEdge.stop_of_edge`（公理 `propext`、`Quot.sound`）、`SurfaceFrames.OnFrames.stopAt`、`StopAt.stopP`（前の `Moves.stopP`。いまは `StopAt` から。`stopAt` は `Classical.choice` も）です。ROM の新しい確認はありません。

**測ったこと.**

| 確かめ | 何を | 結果 |
|---|---|---|
| `edge-real FM2 256` | `Moves.stop` のフレーム（0 < v(Q)、v(b) = 0、P(b) = P(Q)）と、そのうち狭めたフィールドが求めるもの | 6 フレーム（動画のフレーム 852 から 1091 からの自分の入力で 3、992 から 1011 からの主に左を押す入力で 3）。どれも補正が 1 回、押し戻しはなし。P(Q) − P(a) は高々 32。狭めたフィールドが求めるのは 0。画面外のビットのルーチンに来る 137,955 フレーム（5 組）では、左端での補正が 48,290 回選ばれ、右端での補正は 1 回もない。`movesScan` が外れるのは、きれいに始まらないフレームでの古い保存された速さと `after` だけで、数は第 30 回、第 31 回と同じ |
| `surface-frames-check FM2 200` | `stop`（狭めたフィールド）と `stopAt (a theorem)`（古いフィールド）、ほかの `movesScan` の条件 | 外れ 0: 8 組、239,510 フレーム、確かめたのは 215,433 フレーム。書きかえた状態も含む |
| `route-check FM2`（`1089 02808080` つき、996 と第 23 回の jumprun つき） | ルート全体 | 旗に触るのは 1092、レベルの切り替わりは 1748（1093 と 1748。1396 と 2063） |
| `pos-keep-real FM2 64`、`collide-real FM2 200`、`pos-after-real FM2 200`、`keep-frames-check FM2 100`、`up-clean-u FM2` | `posW`、`clampR`、`collide`、`keep.cleanE`、`chg.upCleanU` | 外れ 0 |

画面外のビットのルーチンでの補正の選び方を、ROM で d = (右端 − pix) mod 2¹⁶ のすべての値について測りました（右端は左端の 255 px 右。試しの評価で、証明の一部ではありません）: 左端での補正が選ばれるのは、ちょうど彼が左端にいるか、左端の右 255 px の中にいないとき。右端での補正は画面の右の 16 px の中にいるとき。それ以外は補正なし。

**ルートでは.** フィールド `Moves.stop` を狭めました。前（第 28 回）:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) → P(Q) ≤ P(a) + 256          （Q = trace k）
```

いま:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         (left16(Q) < pixel16(Q) ∨ pixel16(a) < left16(a)) → P(Q) ≤ P(a) + 256
```

新しいフィールドはありません。`Moves.toAt` は `Moves` のかわりに `StopAt` を受け取り、`OnFrames.movesAt` はそれを `OnFrames.stopAt` で与えます。プログラムは狭めたフィールド（`stopB`、"stop"）と、定理になった古いもの（`stopAtB`、"stopAt (a theorem)"）を確かめます。

**ここで証明していないこと.** スクロールの処理で彼が画面の左端より右にいるフレームでの `Moves.stop`。そこでは、彼が左端の右 255 px の中にいるあいだ左端での補正は来ないので、速さは右端での補正か押し戻しで 0 にならなければなりません。証明するには: スクロールの処理の戻りからフレームの終わりまで速さを追うこと（`PushTimer` の歩きにバイトを 1 つ足す）、そこでの彼のピクセル（`PushTimer.pix_end`。そのフレームで `sideW` が要るが、`sideW` は場所のバイトがスクロールのしきい値以上のときだけ求める）。左端より左で始まるフレーム（pixel(a) < left(a)）は、きれいでないことを測っただけです（第 23 回、[フレームの始めの画面の左端](e-2-10-3-10-ScreenEdge-ja.md)）。`collide`、`posW`、`clampR`、`sideW`、`endKeep` の場所のバイトの部分。

第 33 回（[補正が止めるフレームは画面の左端で終わる](e-2-10-3-23-StopClamp-ja.md)）: スクロールの処理で端より右にいて横のタイマーが押し戻しの値で終わらないフレームはない（`OnFrames.noStopRight`。速さを追い、彼のピクセルは `PushTimer.pix_end`）。タイマーがその値で終わらなかったフレームのあと、フレームは端より左で始まらない（`OnFrames.leftEnd`）。フィールドは押し戻しのあるフレームでだけ求める。`sideW` はいまはそれらのフレームでも求める。

**ファイル:** `Theorems/StopEdge.lean`。`Theorems/SurfaceFrames.lean` がこれを使います（`Moves.stop`、`StopAt`、`StopAt.stopP`、`Moves.toAt`、`OnFrames.stopAt`、`OnFrames.movesAt`、`stopB`、`stopAtB`、`movesScan`）。`Main.lean`: `edge-real` の数え 1 つ（狭めたフィールドが求める `Moves.stop` のフレーム）。
