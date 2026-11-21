[← Back](README-ja.md) | [English](e-2-10-3-13-EdgeStep.md) | [Japanese](e-2-10-3-13-EdgeStep-ja.md)

# フレームの端の進み

**主張（第 26 回）.** 地上のフレームの前のフィールド `edge` は定理になりました（`SurfaceFrames.OnFrames.edgeAt`）。触る前の数えるフレーム `j` のそれぞれで:

```
1 ≤ j < g  →  edge(seq j) ≤ max(base(seq (j − 1)), P(seq j))

edge(m) = 256·left16(m) + 255        画面の左端を位置として（SurfaceRead.edgeOf）
base(m) = max(P(m), edge(m))         （SurfaceRead.baseOf）
```

その代わりに、新しいフィールドが 1 つあります。数えるフレームのスクロールの処理 `Q` の、1 つの状態の条件です（`OnFrames.near`、`EdgeStep.Near`）:

```
Near(Q)  :=  Allows(Q)  →  left16(Q) + X(Q) + 2 ≤ pixel16(Q)

pixel16(m) = 256·彼のページ + 彼のピクセル
left16, X, Allows: スクロールの規則（1-1-e-2-10-3-12）と同じ
```

また `FrameKeep.guardE` は 2 つのバイトを多く守ります。画面の左端のピクセルとページです（`FrameKeep.edgeE`）。だから `keep.cleanE` と `chg.upCleanU` は少し多くを求めます: 添字かポインタでの書き込みは、この 2 つのバイトを書きません。

**証明.** 数えるフレーム `j` を 1 つ、`M = seq (j − 1)` から `b = seq j` まで考えます。`Q` はスクロールの処理にある機械（プレイヤーのルーチンのあとの最初）、`R` はその呼び出しの次の命令（`PlayerSubs + 3`）にある機械です。

1. edge(フレーム j の始まり) = edge(M)。数えないフレームはポーズで終わり、プレイヤーのルーチンに来ません。`CtrlKeep` の歩きが端のバイトを 1 つずつ追い、ルーチンに来ない道ではどの命令もそれを書きません（`EdgeStep.keep_noCut`、`OnFrames.edgeLag`）。
2. edge(Q) = edge(フレーム j の始まり)、そして `Q` は `Good`。同じ歩きでプレイヤーのルーチンまで行き、そこからバイトを追う歩きでスクロールの処理まで行きます（`EdgeStep.walkQR`、`EdgeStep.keep_q`）。
3. edge(R) = edge(Q)、または `Allows(Q)` で edge(R) ≤ edge(Q) + 256·Y、Y ≤ X(Q)。これはスクロールの規則です（`ScrollRule.scroll_edge`、第 25 回）。
4. edge(b) = edge(R)。プレイヤーのルーチンからスクロールの処理までの歩き、そこから `R` までの歩き、`R` からフレームの終わりまでバイトを追う歩きです（`EdgeStep.walkKP`、`EdgeStep.keep_r`）。
5. P(Q) − 256 ≤ P(b)。これは `collide` の一部です（`CollideE`、`EdgeStep.collideE_lower`）。

端が動かなければ edge(b) = edge(M) ≤ base(M) です。動けば `Near(Q)` から

```
edge(b) = edge(R) ≤ 256·(left16(Q) + X(Q)) + 255 ≤ 256·pixel16(Q) − 257 ≤ P(Q) − 257 < P(b)
```

です（`EdgeStep.edge_step_of`、`EdgeStep.edge_frame`）。

**ROM の上の歩き**（`EdgeStep.qCheck`、`EdgeStep.rCheck`。どちらも `ScrollRule.check` とともに `numbersCheck` に入っています。合わせて native で約 4 秒）:

* 歩きは `TaintRun` のカウンタ（`Env.rkI`）として各バイトを追います。道はそれへのどの書き込みでも失敗します。歩きのガードはそのバイトを守り（`AfterKeep.guardH`）、`guardE` の `CleanK` からそのガードの `CleanK` が出ます（`EdgeStep.cleanH_of_E`）。
* `walkQR` は `AfterKeep` の 1 つ目の歩きで、バイトを減らす命令も拒みます。だからバイトの値に条件がいりません（`qR_run`）。
* `walkKP` は `AfterKeep` の 2 つ目の歩きに、切るところを 1 つ足したものです: 押し戻しと端の補正の外で、彼の位置のバイトへアドレスで書く命令で道を止めます（`cutPos`）。フィールド `posW` は、スクロールの処理からフレームの終わりまでにそのような命令がないと言います。切らないと、端のページの歩きが 1 つの命令で失敗します: 城の面のループで、彼のページと画面のページを 4 戻すところです。歩きはワールドを知りません。
* 真ん中の歩き（スクロールの処理から `R` まで）は、最後の歩きをスクロールの処理のあとから始めるためのものです。そこからは `posW` が成り立ちます。

**測ったもの**（すべて最後のプログラムで。終了コード 0）:

| 確認 | 何を | 結果 |
|---|---|---|
| `edge-real FM2 256` | 852 からのムービー、左端で土管に向かう走り、自分の乱数の走り 256 + 256 回。すべてのフレームで `near` と前の `edge` | 137,955 フレーム。スクロールが許されるスクロールの処理は 11,289。そこで pixel16 − left16 − X − 2 の最小は 78（`near` は 0 以上を求める）、X の最大は 3、pixel16 − left16 の最小は 81。`near` と `edge` が成り立たないもの 0 |
| `surface-frames-check FM2 200` | `movesScan` の条件の中の `near` | 8 組、239,510 フレーム。`Moves` と `near` を確かめたフレーム 215,433。成り立たないもの 0 |
| `keep-frames-check FM2 100` | 地上のすべての命令で新しい `guardE` の `CleanK`。触るフレームも、数えるかどうかによらず | 224,813 フレーム。添字かポインタで守るバイトへ書く命令はない |
| `up-clean-u FM2` | 縦の土管までのフレームで、`chg.upCleanU` のガード（新しい `guardE` を含む）の `CleanK` | `guardE` が守るのは 69 バイト（前は 67）、合わせたガードは 146（前は 144）。221,490 フレーム。条件に反する命令はない |
| `route-check`（ムービー。1089 `02808080`。996 と第 23 回のジャンプの走り） | ルート | 触るのは 1092、1093、1396。面の切り替えは 1748、1748、2063 |
| `collide-real FM2 200`、`pos-after-real FM2 200`、`pos-keep-real FM2 64` | パート e のほかのフィールド | 終了コード 0 |

非公開のビルド: `Proof.PoleJoin`（その `numbersCheck` が端の歩きとスクロールの規則を持つ）は 60 秒（前は 51 秒）でした。

**証明していないもの.** `Near(Q)` は仮定です。スクロールは画面の上の彼の場所を読みます。これは前のフレームで彼の絵の処理が (pixel − left) mod 256 として書くバイトです（第 25 回に測りました）。そのバイトがしきい値以上で横のタイマーが 0 のところでは、彼は端より 80 px 以上右にいます。これは 2 つのフレームの関係で、証明していません。

**ファイル:** `Theorems/EdgeStep.lean`。ほかに変えたもの: `Theorems/FrameKeep.lean`（`guardE` に `edgeE`）、`Theorems/SurfaceFrames.lean`（フィールド、`numbersCheck`、`AreaRun`、`edgeLag`、`edgeAt`、`movesScan` の `nearB`）。`Main.lean`: `edge-real` が `Near` を測ります。
