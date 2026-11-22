[← Back](README-ja.md) | [English](e-2-10-3-19-RightEdge.md) | [Japanese](e-2-10-3-19-RightEdge-ja.md)

# スクロールの処理での画面の右端

プレイヤーの画面の外のビットのルーチン（[画面の端での補正の向き](e-2-10-3-18-ClampSide-ja.md)）は、画面の右端と左端を読みます。第 30 回は、右端が左端の 255 px 右にあるときの補正の選び方を証明し、その関係と、左端のページが 255 でないことを、フィールド `rightRel` として仮定しました。ここでは両方を証明します。`rightRel` はなくなり、かわりのフィールドはありません。

右端の 2 バイトは、左端の 2 バイトの 1 バイトあとにあります。ゲームがそれを書くのは 1 つのルーチン（GetScreenPosition: 左端 + 255 px、ページへの繰り上がりつき）だけで、スクロールは左端を動かした直後にそれを呼び、エリアの始まりもそれを呼びます。ほかには城のループの戻りが書きますが、そこは彼のページも動かします（フィールド `posW` が除く書き込み）。

**主張（第 31 回）.** 次のように書きます。

```
left16(m)  = 画面の左端の 256·ページ + ピクセル
right16(m) = 画面の右端の 256·ページ + ピクセル
Rel(m)     := right16(m) ≡ left16(m) + 255   (mod 2¹⁶)
PageOK(m)  := m での左端のページが 255 でない
```

1. `RightEdge.scroll_rel`: スクロールの処理の呼び出し（`PlayerSubs`、`Good`）にある本物の機械 Q をとります。ある k があって、`stepN k Q` は同じフレームの中で画面の外のビットのルーチンにあり、スタックは Q の 2 つ下、呼び出しの戻り先がスタックにあり、彼の位置（ピクセル、ページ、端数）は Q のものと同じで、

```
Rel(Q) → Rel(stepN k Q)
```

2. `SurfaceFrames.OnFrames.relAll`: 地上のフレーム（`OnFrames`、`AreaRun`）で、

```
∀ j < g,  Rel(seq j)
```

つまり、操作できるようになったときと、触れる前の数えるフレームのそれぞれの終わりで成り立ちます。

3. `SurfaceFrames.OnFrames.pageAll`: 触れるのが操作できるようになってから `farN` フレーム以内のとき（`OnFrames.readAll` と同じ）、

```
∀ j, 1 ≤ j → j < g → PageOK(seq j)
```

これで `OnFrames.nearStepAt`（触れる前の最後のフレームを除く、数えるフレームのそれぞれの終わりでの `SideTimer.NearM`）は、フィールド `endKeep` だけを使います: 画面の外のビットのルーチンで Rel が成り立ち（前のフレームの終わりでの Rel、数えないフレームは 4 バイトを保つ、`EdgeStep.keep_q` がスクロールの処理まで保つ、そして `scroll_rel`）、そこでの左端のページはフレームの終わりでのものと同じです。

これらは `RightEdge.scroll_rel`、`OnFrames.relStep`、`OnFrames.relAll`、`OnFrames.readAllP`、`OnFrames.pageAll` です（公理 `propext`、`Classical.choice`、`Quot.sound`）。ROM の確認は `RightEdge.check` と、`numbersCheck` の 3 つの確認です。非公開の証明 `pole_numbers` がそれを `native_decide` で確かめます（`RightEdge.check` はネイティブで 1 秒かかりません）。

**1 の証明.** [スクロールの規則](e-2-10-3-12-ScrollRule-ja.md) と同じく、ROM のコードの区間で確かめます。場所はプログラムから読みます: スクロールの処理はプレイヤーのルーチンの終わりの呼び出しの行き先、右端のルーチンの呼び出しは、スクロールが左端のページを読んだあとの最初の `JSR`、その行き先がルーチンで、ルーチンの `RTS` はそこから探します。

| 区間 | から | まで | 知っている値 |
|---|---|---|---|
| `jsr0Check` | スクロールの処理の呼び出し | スクロールの処理の入口 | スタックのバイト（256）: 戻り先がスタックにある。端の 4 バイトと彼の位置は変わらない |
| `w1Check` | スクロールの処理の入口 | 画面の外のビットのルーチン、または右端のルーチンの呼び出し | なし: スタックを知らずに保つ 1 回の歩きで、分かれ道はすべて両方へ進む。画面の外のビットのルーチンでは 4 バイト、彼の位置、スタックのページが変わらない。呼び出しでは右端の 2 バイト、彼の位置、スタックのページが変わらない |
| `jsrCheck` | 右端のルーチンの呼び出し | ルーチン | スタックのバイト（256）: その戻り先がスタックにある。端、彼の位置、スタックの上の 2 バイトは変わらない |
| `gspCheck` | ルーチン | その `RTS` | 左端のピクセルとページ（65,536）: 右端は左端 + 255 px、ページへの繰り上がりつき |
| `rtsOK` | | | ルーチンは `RTS` で終わる |
| `tailCheck` | 呼び出しの次の命令 | 画面の外のビットのルーチン | なし: 4 バイト、彼の位置、スタックのページは変わらない |

呼び出しのない道では、4 バイトが変わらないので Rel(Q) が保たれます。呼び出しのある道では、右端が左端から決まり、左端は画面の外のビットのルーチンまで変わりません。そこで `ScrollRule.left_add`（255 で）が Rel を与えます。

**2 の証明.** フレームについての帰納法です。操作できるようになったとき: 横の土管から出る変化の行は右端の 2 バイトも知っています（`Start.rightX`、`Start.rightP`、`edgeBytes` から）。`numbersCheck` は操作できるようになったときの機械で Rel を確かめます（`rel_zero`）。1 つのフレーム（`relStep`）: 数えないフレームは 4 バイトを保ち（`OnFrames.edgeLag`）、数えるフレームはスクロールの処理まで保ち（`EdgeStep.keep_q`）、`scroll_rel` が Rel を画面の外のビットのルーチンまで運び、補正は両方の端を保ち（`ClampSide.clamp_end`）、戻りは RAM を保ち（`ret_step`）、呼び出しの次の命令からフレームの終わりまで `EdgeStep.keep_r` の歩きが 4 バイトを保ちます（`posW` とともに）。そのために `EdgeStep` の歩きは右端の 2 バイトも追います（`EdgeStep.eI`: 5 バイト）。`FrameKeep.guardE` はそれを守ります（`FrameKeep.edgeE`）。

**3 の証明.** `OnFrames.readAllB` は、数えるフレーム d の終わりでの基準を限ります: base(seq d) ≤ P(操作できるようになったとき) + 16·top·d。端は基準以下です。`numbersCheck` は P(操作できるようになったとき) + 16·top·farN < 65280·256 を確かめるので、左端のページは 255 ではありません（`page_of_base`）。フレーム d での限りは d での `OnFrames.edgeAt` を使い、それはフレーム d − 1 の終わりでの `NearM`、つまりそこでの `PageOK` を使います。そこで `PageOK` を、`nearStepAt`、`nearMAll`、`nearAAt`、`nearAt`、`edgeAt` の前のフレームについての仮定にしました。`readAllP` は限りと `PageOK` を一緒に、d についての帰納法で証明します。

**測った結果.**

| 確認 | 何を | 結果 |
|---|---|---|
| ネイティブの試し | `RightEdge.check` | 真。ネイティブで 1 秒かからない（試しのビルド） |
| 非公開の証明（`prove.py`） | `pole_numbers`（3 つの新しい確認を含む `numbersCheck`）、`side_start`（横の土管から出る変化の行が右端の 2 バイトを知っている） | 真。`Proof.PoleJoin` は混んだ機械で 89 〜 106 秒（第 30 回: 63 〜 72 秒）、`Proof.SurfaceFrames` は 9 〜 11 秒 |
| `edge-real FM2 256` | すべてのフレームの画面の外のビットのルーチンで（5 組、137,955 フレーム、clean かどうかによらず） | どのフレームでも右端は左端 + 255 px で、左端のページは 255 でなかった（反例 0）。選び方: 補正なし 89,665、左端 48,290、右端 0（第 30 回と同じ） |
| `edge-real FM2 256`、`surface-frames-check FM2 200` | `movesScan`: `right edge (a theorem)`（フレームの始め、画面の外のビットのルーチンのそれぞれ、終わりでの Rel）、`leftPage (a theorem)`（終わりで）、狭めた `endKeep` | 失敗 0。`edge-real` の失敗は、clean で始まらないフレームでの前からの stored speed と `after` だけで、数は第 30 回と同じ。`surface-frames-check` は 8 組、239,510 フレーム、確かめたフレーム 215,433（書き換えた状態を含む） |
| `up-clean-u FM2` | 右端の 2 バイトも守る `chg.upCleanU` | 反例 0 |
| `keep-frames-check FM2 100` | それを守る `keep.cleanE` | bad 0 |
| `pos-keep-real FM2 64`、`collide-real FM2 200`、`pos-after-real FM2 200` | `posW`、`clampR`（`endKeep` を狭めるのに使う）、`collide` | 失敗 0 |
| `route-check FM2` | ルート全体 | 触れるのは 1092、レベルの変化は 1748。`1089 02808080` では 1093 と 1748。996 と第 23 回のジャンプの入力では 1396 と 2063 |

**ほかに（第 31 回）: `endKeep` は前より少なくを求めます.** スクロールの処理で右へ動き、その速さで終わるフレームでは、`endKeep` のピクセルの部分は定理です（`OnFrames.nearStepAt` の中）: フレームはスクロールの処理での位置で終わり（`OnFrames.keepAt`）、画面の外のビットのルーチンが補正を呼ぶときは、補正の入口でのフィールド `clampR` が補正の行き先は彼の位置だと言うので、補正は彼を動かしません。そのためにルーチンの区間（`ClampSide.W0`）と `RightEdge` の区間（`edges`）は彼の速さも保ちます。だから `endKeep` がピクセルの部分を求めるのは、押し戻しか補正を呼び、右への速さを保たないフレームだけです:

```
endKeep : … → EndKeep(Calls(Q) ∧ ¬(0 < v(Q) ∧ v(seq j) = v(Q)), Rt, seq j)      （第 30 回: EndKeep(Calls(Q), Rt, seq j)）
```

**ルートでは.** フィールド `OnFrames.rightRel` はなくなりました。新しいフィールドはありません。`numbersCheck` の新しい確認: `RightEdge.check`、操作できるようになったときの機械での Rel、P(操作できるようになったとき) + 16·top·farN < 65280·256（`Numbers.rightC`、`relB`、`pageB`。`AreaRun.rc`、`rel₀`、`pageB`）。`Start` は右端の 2 バイトを持ちます: 横の土管から出る変化の行がそれを知っています（非公開の証明 `side_start` が確かめます）。前より多くを求める仮定が 2 つあります: `FrameKeep.guardE`、つまり走りの各命令の条件（`chg.upCleanU`、`keep.cleanE`）は右端の 2 バイトも守ります。それはアドレスでしか書かれません。

**ここで証明していないこと.** `endKeep`。そのピクセルの部分（いまは押し戻しか補正を呼び、右への速さを保たないフレームだけ）には、呼び出しのあとで彼を動かすのは押し戻しだけであること、横の当たりのタイマーが 1 以下で終わるフレームには呼び出しのあとの押し戻しがないことが要ります。場所のバイトの部分（タイマー 1 以下、ロック 0、場所のバイトがしきい値以上で終わるすべてのフレームで）には、描画が画面での彼の場所を pixel − 左端 mod 256 として書くことが要ります。`Moves.stop`: `NearM` の条件のもとだけでなく、すべてのフレームの始めでの、左端に対する彼の場所が要ります。

**ファイル:** `Theorems/RightEdge.lean`。`Theorems/SurfaceFrames.lean` がそれを使います（`rel_zero`、`rel_congr`、`OnFrames.relStep`、`OnFrames.relAll`、`PageOK`、`page_of_base`、`OnFrames.readAllP`、`OnFrames.pageAll`、`OnFrames.nearStepAt`）。`Theorems/EdgeStep.lean`（`eI`）と `Theorems/FrameKeep.lean`（`edgeE`）は右端の 2 バイトを、`Theorems/ClampSide.lean`（`Places.speed`、`W0` の中）は彼の速さを持ちます。`Main.lean`: `edge-real` のフィルターの確認の名前だけ。
