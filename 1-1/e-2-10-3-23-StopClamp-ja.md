[← Back](README-ja.md) | [English](e-2-10-3-23-StopClamp.md) | [Japanese](e-2-10-3-23-StopClamp-ja.md)

# 補正が止めるフレームは画面の左端で終わる

フィールド `Moves.stop` は、次のフレームについてのものです: スクロールの処理で右に動いていて、速さ 0 で終わり、スクロールの処理での位置で終わる。第 32 回は、スクロールの処理で彼が画面の左端より右にいるか、フレームが左端より左で始まるところでだけこれを求めました（[画面の左端で彼を止めるフレーム](e-2-10-3-21-StopEdge-ja.md)）。ここでは、スクロールの処理のあとに押し戻しのないフレームは左端で終わり、そのときスクロールの処理で端より右にいないことを証明します。押し戻しのない数えるフレームは端かその右で終わることも証明します。だからフィールドは押し戻しのあるフレームでだけ求めます: スクロールの処理で端より右にいて、このフレームに押し戻しがあるもの、または 1 つ前のフレームに押し戻しがあって端より左で始まるもの。

ゲームのコードでの理由: 操作中のフレームで、スクロールの処理の呼び出しのあと彼の速さを 0 にするのは 3 つだけです: 画面の端での補正（スクロールの処理の中）、押し戻し（まず横のタイマーを 16 にする）、死ぬこと（そのあとゲームのエンジンのルーチンを書く。旗に触る前のフレームはどれもそれをしない）。横のタイマーはフレームの始めでだけ減るので、タイマーが 16 でなく終わるフレームでは、スクロールの処理のあとに押し戻しはありません。そのようなフレームでは補正が速さを 0 にしました。右端での補正は彼を右端の 16 px 左に置き、そこでは右端での補正は選ばれません。一方、終わりでの彼のピクセルは補正を選んだときのものです。だからそれは左端での補正で、彼を左端に置きます。

**主張（第 33 回）.** 次のように書きます。

```
a, b    = 1 つ前の数えるフレームの終わり（seq (j − 1)）、フレームの終わり（seq j）
Q       = プレイヤーのルーチンに来たあとのスクロールの処理の呼び出し
C       = 画面外のビットのルーチン（ChkPOffscr）の始め、 R = スクロールの処理の戻りの命令
pix(m)  = 彼のピクセルとそのページ、 left(m)、right(m) = 画面の端とそのページ（どれも 2 バイト）
P(m)    = 256·pix(m) + f(m)、 v(m) = 彼の速さ、 side(m) = 横の当たりのタイマー
t₁₆     = PushTimer.pushT、押し戻しがタイマーに書く値。押し戻しのコードから読む（16）
sel(C)  = C での補正の選び: なし、左端（0）、右端（1）、 amt(t) = t の補正の量
after(t, C) = 何も選ばないなら pix(C)、それ以外は (C での端 t − amt(t)) mod 2¹⁶
```

`StopClamp.stop_clamp`: right(C) ≡ left(C) + 255 (mod 2¹⁶) のとき、

```
pix(R) = after(sel(C), C)  ∧  (sel(C) = なし → v(R) = v(C))
∧  pix(b) = pix(R)  ∧  v(b) = v(R)  ∧  pix(C) = pix(b)  ∧  left(b) = left(C)  ∧  v(b) ≠ v(C)     →     pix(b) = left(b)
```

1 ≤ j < g の数えるフレーム `j` のどれでも:

```
SurfaceFrames.OnFrames.stopRight   : 0 < v(Q) ∧ v(b) = 0 ∧ P(b) = P(Q) ∧ side(b) ≠ t₁₆                       →  pix(b) = left(b)
SurfaceFrames.OnFrames.noStopRight : 0 < v(Q) ∧ v(b) = 0 ∧ P(b) = P(Q) ∧ side(b) ≠ t₁₆ ∧ left(Q) < pix(Q)    →  偽
SurfaceFrames.OnFrames.leftEnd     : side(b) ≠ t₁₆                                                           →  left(b) ≤ pix(b)
```

`noStopRight` はほかに、`a` の速さが高々最大、`a` が位置の範囲の両端から離れ、それまでのフレームの終わりで左端のページが 255 でないことを要します。`leftEnd` は `b` で左端のページが 255 でないことを要します。`SurfaceFrames.OnFrames.stopAt`（古いフィールド `StopAt`、第 32 回）は、これらと狭めたフィールドから出ます。

`PushTimer.pix_end` はいまこう言います: フレームがタイマー t₁₆ で終わらないなら、フレームの終わりでの彼のピクセル、ページ、速さは、スクロールの処理の呼び出しの次の命令でのもの（第 32 回: タイマー高々 1 で終わるなら、ピクセルとページ）。

定理は `StopClamp.stop_clamp`、`ClampSide.amt_facts`（公理 `propext`、`Quot.sound`）、`PushTimer.pushT_ne`、`SurfaceFrames.OnFrames.stopRight`、`OnFrames.noStopRight`、`OnFrames.leftEnd`（`Classical.choice` も）です。`ClampSide.clamp_end` はより多くを言います: 何も選ばないとき速さは保たれる。ROM の新しい確認: `ClampSide.rightAmt`、差 amt(1) での選びは右端でない（`ClampSide.checkAll` の一部）。`PushTimer.sCheck` には、彼の速さの 3 つめの歩きと 2 ≤ t₁₆ が加わりました。

**証明.** `stop_clamp`、C での選びで分けます:

* 何も選ばない: v(b) = v(R) = v(C) で、v(b) ≠ v(C) に反する。
* 右端: pix(C) = pix(b) = pix(R) = (right(C) − amt(1)) mod 2¹⁶。だから選びが読む差 (right(C) − pix(C)) mod 2¹⁶（`ClampSide.selM_rel`）は amt(1) で、そこでは選びは右端でない（`rightAmt`）。
* 左端: amt(0) = 0（`relCheck`）なので、pix(b) = pix(R) = left(C) = left(b)。

`stopRight` は `OnFrames.nearStepAt` のように示します:

* Q はプレイヤーのルーチンに来たあとのただ 1 つのスクロールの処理（`GuardE.subs_onceE`）、その最初のもの（`EdgeStep.keep_r`）。
* スクロールの部分は C まで彼の位置と速さを保ち、そこで右端の関係を与える（`RightEdge.scroll_rel`、1 つ前のフレームの `OnFrames.relAll` と `OnFrames.edgeLag`）。だから pix(C) = pix(Q) = pix(b)（最後は P(b) = P(Q) から）、v(C) = v(Q) > 0 = v(b)。
* ルーチンと補正は pix(R) = after(sel(C), C) とし、端を保ち、何も選ばないとき速さを保つ（`ClampSide.clamp_end`）。戻りは RAM を保つ（`ret_step`）。
* 呼び出しの次の命令からフレームの終わりまで、フレームがタイマー t₁₆ で終わらないなら、彼のピクセル、ページ、速さは保たれ（`PushTimer.pix_end`、フィールド `posW` と `sideW`）、左端も保たれる（`EdgeStep.keep_r`）。

`noStopRight`: `stopRight` から pix(Q) = pix(b) = left(b)。`Q` から呼び出しの次の命令まで、端は保たれるか、スクロールが許されて端はスクロールの量まで動く。それは動きが書くバイトです（`Q` で足場の力は 0: `ScrollRule.scroll_edge`、`OnFrames.platQ`）。そこからフレームの終わりまで端は保たれる（`EdgeStep.keep_r`）。スクロールがなければ left(b) = left(Q) < pix(Q)。スクロールがあれば、`Q` での `EdgeStep.NearX`（`OnFrames.nearAt`）から left(Q) + xs(Q) + 2 ≤ pix(Q)、だから left(b) ≤ pix(Q) − 2。どちらも pix(Q) = left(b) に反する。

`leftEnd`: `OnFrames.nearStepAt` のように、補正は彼を左端か、その右 255 px 以内に置き（`ClampSide.left_of`）、彼のピクセルと端はフレームの終わりまで保たれる（`PushTimer.pix_end`、`EdgeStep.keep_r`）。端のページが 255 でなければ、それは left(b) ≤ pix(b)。

`stopAt`: Q で彼が左端かその左にいて、フレームが左端かその右で始まるなら、第 32 回（`StopEdge.stop_of_edge`）。Q で端より右にいて、フレームがタイマー t₁₆ で終わらないなら、`noStopRight`。フレームが端より左で始まり、1 つ前のフレームがタイマー t₁₆ で終わらなかったなら、1 つ前のフレームの `leftEnd`（操作の始めなら `AreaRun.edge₀`）がそうでないと言う。残りはフィールド。`stopAt` は、`a` の速さと位置（きれいな状態と `far` から）と、それまでのフレームの左端のページを受け取るようになりました。`movesAt`、`one_of_frames`、`vert_of`、`quiet_upto` はページを渡し、`surface_of_frames` は `OnFrames.pageAll` でそれを与えます。

速さの歩きは、ピクセルとページの歩きと同じように、スクロールの処理の呼び出しの次の命令からフレームの終わりまで速さのバイトを追います: そのアドレスへの書き込みで追うのをやめ、終わりで、まだ追っているか、タイマーが t₁₆ と知られていることを求めます。押し戻しは速さに 0 を書く前にタイマーに t₁₆ を書きます。死ぬことはルーチンを書きます（そこで終わる道: `K.noStore`）。歩きの守りは速さとプレイヤーの状態も守ります（`PushTimer.guardS`。`FrameKeep.guardE` がそれらを守るので、`cleanS_of` はなお成り立つ）。

**測ったこと.**

| 確かめ | 何を | 結果 |
|---|---|---|
| 自前の試し（試しの探索） | 終わりを「まだ追っている、またはタイマーが t₁₆ と知られている」とした、スクロールの処理の呼び出しの次の命令からの `sCheck` の 3 つの歩き | どれも外れ 0。`sCheck` は true、外れの評価とあわせて自前で約 5 秒。t₁₆ = 16。速さと状態を守らないと、速さの歩きは 2 回外れた |
| ROM（第 32 回の、選びの試しの評価） | 差 d = (right − pix) mod 2¹⁶ のそれぞれでの選び | 右端はちょうど d が 0 から 15。d が 16 から 254 では何も選ばない。それ以外は左端。右端での補正は彼を右端の 16 px 左に置き、そこでは何も選ばれないので、`rightAmt` が成り立つ |
| `edge-real FM2 256`、`surface-frames-check FM2 200` | `stop`（狭めたフィールド）、`stopAt (a theorem)`、`stopRight (a theorem)`、`noStopRight (a theorem)`、`leftEnd (a theorem)` | 外れ 0。`edge-real`: `Moves.stop` のフレーム（0 < v(Q)、v(b) = 0、P(b) = P(Q)）は 6 つ、どれも補正が 1 回で押し戻しはなし、P(Q) − P(a) は高々 32。第 32 回のフィールドが求めるのは 0、新しいフィールドも 0。画面外のビットのルーチンに来る 137,955 フレームで、左端での補正が 48,290 回選ばれ、右端での補正は 1 回もない。`surface-frames-check`: 8 組、239,510 フレーム、確かめたのは 215,433 フレーム、書きかえた状態も含む |

**ルートでは.** フィールド `Moves.stop` を狭めました。前（第 32 回）:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         (left16(Q) < pixel16(Q) ∨ pixel16(a) < left16(a)) → P(Q) ≤ P(a) + 256                       （Q = trace k）
```

いま:

```
stop : ∀ k, n₀ ≤ k → pc(trace k) = PlayerSubs → 0 < v(Q) → v(b) = 0 → P(b) = P(Q) →
         ((left16(Q) < pixel16(Q) ∧ side(b) = t₁₆) ∨ (pixel16(a) < left16(a) ∧ side(a) = t₁₆)) → P(Q) ≤ P(a) + 256
```

新しいフィールドはありません。`stopRight` と `leftEnd` は、ロックと場所のバイトによらずタイマー t₁₆ で終わらないフレームと、旗に触る前の最後の数えるフレームで、フィールド `sideW` を使います: いまフィールド `sideW` はそこでも求めます（[横のタイマーに届きうる書き込み](e-2-10-3-22-SideNear-ja.md)）。

**ここで証明していないこと.** 押し戻しのあるフレームでの `Moves.stop`: スクロールの処理で左端より右にいて、このフレームのスクロールの処理のあとに押し戻しがあるもの、または押し戻しのあったフレームのあと端より左で始まるもの。そこでは押し戻しが彼を 1 px ずつ動かし、打ち消しあう 2 つの押し戻しや、押し戻しと補正は追っていません。証明するには: スクロールの処理のあとの押し戻しを追う（その数と向き）。

**ファイル:** `Theorems/StopClamp.lean`。`Theorems/ClampSide.lean`（`rightAmt`、`checkAll`、`clamp_end`、`amt_facts`、`left_of`）、`Theorems/PushTimer.lean`（`pvI`、`pushT`、`eqAt`、`finS`、`guardS`、`cleanS_of`、`sCheck`、`pushT_ne`、`pix_end`）、`Theorems/SurfaceFrames.lean`（`Moves.stop`、`OnFrames.stopRight`、`OnFrames.noStopRight`、`OnFrames.leftEnd`、`OnFrames.stopAt`、`OnFrames.movesAt`、`one_of_frames`、`vert_of`、`quiet_upto`、`surface_of_frames`。`OnFrames.relStep` と `OnFrames.relAll` は `stopRight` の前に、`stopAt` から `vert_of` までは `OnFrames.nearAt` のあとに移した。`stopB`、`stopRightB`、`noStopRightB`、`leftEndB`、`movesScan`）。`Main.lean`: `edge-real` はいまフィールドが求める `Moves.stop` のフレームを数え（`stopAsk33`）、その 2 つのふるいは新しい 3 つの名前を知る。
