[← Back](README-ja.md) | [English](e-2-10-3-17-SideTimer.md) | [Japanese](e-2-10-3-17-SideTimer-ja.md)

# フレームの始めからプレイヤーのルーチンまでのスクロールのバイト

**主張（第 29 回）.** 地上の数えるフレームの始めから、プレイヤーのルーチンに最初に来るところまでに、横の当たりのタイマーは高々 1 減ります。画面での彼の場所、スクロールのロック、画面の左端は変わりません。プレイヤーのルーチンに来ないフレーム（ポーズのフレーム）は、タイマーとこれらのバイトを保ちます。だから、第 28 回のフィールド `nearA`（ルーチンに来たところ）は、フレームの始めでの `NearM` からの定理（`OnFrames.nearAAt`）になります。`NearM` はコントロールの始めで成り立ち、数えないフレームはそれを保ちます。新しいフィールド `nearStep` は、数えるフレームのそれぞれが、始めから終わりまで `NearM` を保つことを求めます。

```
M = K.fm j                     数えるフレーム j の始め
R = trace(M, pad j, arrAt)     そのフレームがプレイヤーのルーチンに最初に来たところ

side_at :     side(R) = side(M)  ∨  side(R) = side(M) − 1
side_le :     side(R) = 0  →  side(M) ≤ 1
keep_at :     pfs(R) = pfs(M) ∧ lock(R) = lock(M) ∧ left16(R) = left16(M)
side_noCut :  プレイヤーのルーチンに来ないコントロール中のフレームは side = side(M) で終わる
keep_noCut :  そのようなフレームは M の pfs、lock、端で終わる

NearM(M) :=  side(M) ≤ 1  →  lock(M) = 0  →  thr ≤ pfs(M)  →  left16(M) + 2 ≤ pixel16(M)
NearA(R) :=  side(R) = 0  →  lock(R) = 0  →  thr ≤ pfs(R)  →  left16(R) + 2 ≤ pixel16(R)      （第 28 回）

nearA_of_M :  NearM(M)  →  NearA(R)

near_zero :   edge(seq 0) + 257 ≤ P(seq 0)  →  NearM(seq 0)                                      （AreaRun.near₀）
nearStep :    ∀ j, 1 ≤ j → j + 1 < g → NearM(K.fm j) → NearM(seq j)                            （新しいフィールド）
nearMAll :    ∀ j, 1 ≤ j → j < g → NearM(K.fm j)

side = 横の当たりのタイマー、lock = スクロールのロック、pfs = 画面での彼の場所、thr = スクロールの 1 つ目のしきい値（80 px）、
pixel16 = 256·ページ + ピクセル、left16 = 画面の左端（ページつき）、edge = 位置としての端（256·left16 + 255）、P = 位置
```

**タイマー.** NMI のタイマーの部分は、ゲームがポーズでなく、全体のタイマーの制御が 0 か、このフレームで 0 になるとき、タイマーの並びを `DEC abs,X` で減らします。添字の値ごとに 1 つのタイマーです。横の当たりのタイマーはその 1 つです。`CtrlKeep` の歩きは 1 つのバイトを `TaintRun` のカウンター（`Env.rkI`）として追いますが、`TaintRun` が追うのはカウンターの `DEC abs` だけです。カウンターへのほかの書き込みがあると歩きは止まります。新しいステップ `gsuccX` は、添字が分かっているとき、カウンターの `DEC abs,X` も追います（`arkOpX`。すべての機械について `s_rkOpX` で証明）: カウンターは 1 減り、それはフレームで高々 1 回です（`AS.spent`）。そのあとのフラグ Z と N は分かりません。歩き `walkX` は、このステップを使う `CtrlKeep` の歩きです。プレイヤーのルーチンでは、カウンターが追えていることを求めます。そこに来ないフレームの終わりでは、カウンターが追えていて、減っていないことを求めます。`Sim.rkv` の値と合わせて、これが `side_at` と `side_noCut` になります。

**表.** 歩きは状態の表を使います。表は証明の一部でない探索（`searchX`）から作ります。ポーズのビットの値が違う状態を合わせる表では、2 つの状態でポーズのビットが分からなくなりました。それぞれから、プレイヤーのルーチンに来ずに、タイマーが減ったままフレームを終える道ができ、そこで確認が偽になりました。だから表はそれらを合わせません（`pw`、`CtrlKeep` のポーズのビットの歩きと同じ）: 17,260 の状態で、確認は true です。

**ほかのバイト.** 場所のバイト、ロック、端の 2 つのバイトは、プレイヤーのルーチンより前には書かれません。`CtrlKeep` の歩き（バイトごとに 1 つ、`CtrlKeep.cutTable` の表で）がそれを示します: 到着では `keep_at`、到着しないフレームでは `keep_noCut`。位置は `CtrlKeep.keepA` にあります（`CtrlKeep.ctrl_keep`、`OnFrames.lagKeep`）。

**ルートの上で.** `numbersCheck` には確認が 3 つ増えました: `SideTimer.sideCheck`、`SideTimer.keepCheck`、そしてコントロールの始めでの証明の機械で edge(B.m) + 257 ≤ P(B.m)。最後のものは、`Start` の端と位置と合わせて、タイマー、ロック、場所のバイトが何であっても `NearM(seq 0)` を与えます（`near_zero`、`SideTimer.nearM_of_edge`）。数えないフレームは `NearM` のバイトを保ち（`OnFrames.nearLag`、`OnFrames.lagKeep`）、`nearStep` が数えるフレームのそれぞれで `NearM` を運ぶので、タッチより前の数えるフレームはすべて `NearM` で始まります（`OnFrames.nearMAll`、帰納法）。そして `OnFrames.nearAAt` がルーチンに来たところでの `NearA` を与え、`OnFrames.nearAt` が第 28 回と同じく、スクロールの処理での前のフィールド `near` を与えます。

**フィールド.** なくなったもの: `OnFrames.nearA`。増えたもの: `OnFrames.nearStep`。`nearStep` は、フレームの始めで `NearM` が成り立つときだけ、フレームの終わりで `NearM` を求めます。タッチの前の最後のフレームには求めません。1 つの種類のフレームでは、`nearA` が何も求めなかったのに、次の数えるフレームの始めで上限を求めます: 始めでタイマーが 1 で、フレームがタイマーを動かさない（始めで全体のタイマーの制御が 2 以上）ので、到着でもタイマーが 1 のフレームです。これは測りました（下の `nearMore`）。

**測ったこと**（`surface-frames-check` と `edge-real` は、走るすべてのフレームで、`nearStep` と、定理としてフレームの始めでの `NearM`、`side_at` と `keep_at`、ルーチンに来たところでの `NearA` を確かめます）:

| 確認 | 何を | 結果 |
|---|---|---|
| ネイティブの試し | `sideCheck`、`keepCheck` | true |
| `edge-real FM2 256` | `nearStep`、定理、`nearMore` | 5 つの集まりで 137,955 フレーム（clean でもそうでなくても）、失敗 0。`nearMore` はどの集まりでも 0 |
| `surface-frames-check FM2 200` | `nearStep`、定理、`nearMore` | 8 つの集まり、239,510 フレーム、clean で確かめた 215,433 フレーム、失敗 0。`nearMore` はどの集まりでも 0。階段のあたりの書き換えた状態はそれぞれ 2 フレーム走るので、1 つ目のフレームは位置を書き換えて場所のバイトを書き換えない状態から始まります: そこでも `NearM` は成り立ちました |
| `edge-real FM2 256` | `Moves.stop`（1-1-e-2-10-3）のために: 0 < v(Q)、v(b) = 0、P(b) = P(Q) のフレーム | 6 フレーム。どれも画面の端での補正が 1 回で、押し戻しはない。そこでの P(Q) − P(a) は高々 32（1/8 px） |
| 探索（証明の一部でない） | ここでのプレイヤーのルーチンより前と同じように、スクロールの処理からフレームの終わりまで横のタイマーを追う | 歩きは 95 の命令でタイマーを見失う: 77 は `PlaceKeep.farRk` のように追い続けられ、18 は、歩きが行き先を知らず、行き先がタイマーでありうる、添字かポインタでの書き込み |

**証明していないこと.** `nearStep` と `Moves.stop`。`nearStep` にはスクロールの処理のあとのフレームが要ります: 描画が画面での彼の場所を (pixel − left) mod 256 として書き、画面の端での補正が彼を端かその右に保ち、押し戻しが横のタイマーを 16 にし、描画のあとの書き込みが彼も端も動かさないこと。けがのタイマーが動いている間は、1 つおきのフレームで描画が飛ばされるので、そこではフレームの始めの場所のバイトが残ります。スクロールの処理のあとのタイマーの歩きには、上の探索の 18 の書き込みについての新しい条件が要ります（位置についての `posW` のように）。

**ファイル:** `Theorems/SideTimer.lean`（`decTarget`、`isRkDecX`、`decFlags`、`arkOpX`、`s_rkOpX`、`gsuccX`、`s_gsuccX`、`walkX`、`check1X`、`at_cutX`、`end_noCutX`、`searchX`、`sideTable`、`sideCheck`、`startI`、`keepCheck`、`side_at`、`side_le`、`keep_at`、`side_noCut`、`keep_noCut`、`NearM`、`nearA_of_M`、`nearM_congr`、`nearM_of_edge`）。`Theorems/SurfaceFrames.lean`（`near_zero`、`AreaRun.near₀`、`OnFrames.nearLag`、`OnFrames.nearMAll`、`OnFrames.nearAAt`）が使います。
