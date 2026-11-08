[← Back](README-ja.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# 地上: 操作できてからのフレームを 1 つずつ

**主張.** [操作から城まで](f-5-PoleJoin-ja.md) は走り全体についての文 `model`、`hit`、`stop`、`box`、`off`、`next`、`startP`、`startV` を仮定していました。これらは定理になりました。残る仮定は 1 フレームについての文です。`startP`、`startV` は本物の機械で証明しました。[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) の最後の段から出ます。条件はその切り替えの条件と、`left` が操作の前に 0 にならないことだけです。

単位は 1/256 ピクセルです。`seq j` は数えるフレーム `j` の終わりの機械です。`seq 0` は操作できるときの機械です。`B.m` は非公開の証明が持つ、操作できるときの機械です。

## 1 フレームの形

フレーム `a → b` について読みます。`hs(m)` は横方向の状態、`P(m)` は位置、`v(m)` は速さ、`abs(m)` は覚えている速さ、`bits(m)` は当たり判定のビット、`vs(m)` は縦のバイトです。

```
readIn(a, b)   : st は a から、ジャンプは a と b の状態から、ボタンは b から、タイマーは a から
                 Select と Start は上ボタンと同じに読む
readIn_mem     : readIn(a, b) ∈ inputs                          どの 2 つの機械でも

t = hstep(hs a, readIn(a, b))     v₂ = v(t)     P₂ = P(a) + 16·v₂

Clean(m)       : inD(hs m) ∧ abs(m) = |v(m)| ∧ (bits(m) = FF ∨ (bits(m) = noLeft ∧ 0 < v(m)))
Pre(a, b)      : hs(b) は v を除いて t と同じ ∧ abs(b) = |v₂|
Hit(a, b)      : v(b) ≤ 0 ∧ (P(b) ≤ P₂ − 256 ∨ P(b) ≤ P(a) + 256)
Coll(a, b)     : (P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = FF)
               ∨ (0 < v₂ ∧ P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = noLeft)
               ∨ Hit(a, b)
MaskStop(a, b) : bits(a) = noLeft ∧ v(b) ≤ 0 ∧ P(b) ≤ P(a) + 256
OneFrame(a, b) : MaskStop(a, b) ∨ (Pre(a, b) ∧ Coll(a, b))
```

`Follow(a, b)` は [地下の部屋](c-5-RoomJoin-ja.md) の `RoomJoin.Follow` と同じ形です。`fr.hs n = hs(seq n)`、`fr.P n = P(seq n)`、入力は `readIn` です。

## 本物の機械の 1 フレーム

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel-ja.md) は本物のフレームの移動を証明しています。プレイヤーのルーチンからスクロールの処理まで、`hs` は `hstep` のとおりで、`P` は `16·v₂` 動きます。なので `OneFrame` は、フレームの移動の外の部分から出る定理です。

`fm j` は数えるフレーム `j` が始まるときの機械です。`seq (j − 1)` か、そのあとの `lag` のフレームのあとです。`pad j` はその入力、`arr j` はプレイヤーのルーチンに来る命令の番号です。`R` はそこでの機械、`Q` はスクロールの処理に来たときの機械です。`b = frame(M, i)` はフレームの終わりの機械です。

```
Masked(a, b)       : bits(a) & lr ≠ lr            lr は hstep が readIn(a, b) から読む左右

After(a, Q, b)     : b の f, fd, md は Q のもの ∧ (RunningSpeed(b) = 0 ⟺ RunningSpeed(Q) = 0) ∧ abs(b) = |v(Q)|
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)) )

Moves(a, M, i, n₀) : AtCtrl(R)                                   プレイヤーのルーチンでの状態。FrameModel が要るもの
                     ∧ R の横の 8 バイトは a のもの                  a から R まで書かれない
                     ∧ R から 728 命令のうちにフレームが終わらない
                     ∧ FrameModel.readIn(R) = readIn(a, b)           ルーチンが読む入力
                     ∧ 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴
                     ∧ スクロールの処理に来るどの Q でも After(a, Q, b)

at_subs       : modelOK ∧ Moves  →  スクロールの処理に来る Q があって hs(Q) = t ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_moves  : modelOK ∧ Moves  →  Pre(a, b) ∧ Coll(a, b)
one_of_frames : OnFrames ∧ Clean(seq (j − 1))  →  OneFrame(seq (j − 1), seq j)
```

`modelOK` は `FrameModel` の ROM の確認です。これは `numbersCheck` の一部になったので、非公開の証明が `native_decide` で計算します（約 3 秒増えます）。`move_model` は押している側がふさがれていないことを要ります。ふさがれているフレーム（`Masked`）は仮定で `OneFrame` のままです。そこでは摩擦の処理がふさぎを読み、`hstep` は読みません。

仮定のフィールドです（`OnFrames`）。全部 `Run` の `frames` に入ります。`fm`、`pad`、`arr` はその中のデータです。

```
reads  : 1 ≤ j ≤ g   →  fr j の始まりの v, f, P は seq (j − 1) のもの
         1 ≤ j < g   →  fr j の終わりの v', f', P' は seq j のもの
ends   : 1 ≤ j ≤ T, j < g  →  seq j = frame(fm j, pad j)
moves  : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1)), ¬Masked(seq (j − 1), seq j)  →  Moves(seq (j − 1), fm j, pad j, arr j)
masked : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1)), Masked(seq (j − 1), seq j)   →  OneFrame(seq (j − 1), seq j)
vert   : 1 ≤ j < J, j < g  →  vs(seq j) = vstep(vs(seq (j − 1)), A, abs(seq (j − 1)))
box    : 1 ≤ j < J, j < g, Q はスクロールの処理  →  Q から seq j まで、当たり判定のルーチンは B.m で
         (pix P(Q), y, w, vy, st) を動かしたときと同じ        (y, vy, st) は vstep の結果、w は速さの符号の代表
```

| 前のフィールド | 今 |
|---|---|
| `step`: Clean なフレームは全部 `OneFrame` | `moves`（移動の外の部分）、`masked`（押している側がふさがれたフレームだけ）、`ends` |
| `reads`: `v₂(fr j) = v₂` | なくなった。`box` が本物の機械 `Q` と `seq j` の文なので、フレームの `v₂` は要らない |
| `fr j` についての `box` | 本物の機械についての `box`、スクロールの処理から |

## 走り全体の文は定理

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
next_of_reads     : reads  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  フレーム 1..j は Follow ∧ seq 0..j は Clean ∧ bits(seq j) = FF
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
                    →  ∃ w h, Surface(w, h)
Run.next, Run.startP, Run.startV                                 PoleJoin
```

| 前の仮定 | 今 | どこから |
|---|---|---|
| `model`: `j < h` で `P'(j) ≤ P_A + d(w)` | 定理 | `one_of_frames`。`w` は `readIn` の列、`h` は `Follow ∧ Clean` でない最初のフレーム |
| `hit`、`stop` | 定理 | `OneFrame` の `Hit` |
| `box`、`off`: `J` の前にぶつからない | 定理（`Surface.first : J ≤ h`） | `box`、`vert`、`moves`、距離の上限（`dist_abs`）、高さの探索（`vCheck`） |
| `next` | 定理 | `reads`。両方の端を同じ機械から読む |
| `startP`、`startV` | 定理 | `Start`。下の節 |
| `mem`、`long` | 定理 | `readIn_mem`、`w` の作り方 |

**箱の中.** 1〜8 フレーム目の `x` は仮定ではありません。`|d(w)|` の上限から 4 ピクセル以内です（`dl`、左へは速さのバイトが 1 大きくなるので `dbound` より少し大きい）。高さも仮定ではありません。`vCheck` は `vs(B.m)` から A の有無と 0 から最高速までの覚えている速さの全部で 8 フレーム `vstep` を動かし、全部が箱の中であることを確かめます。

## 操作できるときの状態

`Start(B, m)` は 1 つの機械についての文です。

```
Start(B, m) : hs(m) = hs(B.m) ∧ P(m) = P(B.m) ∧ abs(m) = abs(B.m) ∧ bits(m) = bits(B.m) ∧ vs(m) = vs(B.m)
```

切り替えの最後の段の操作できる状態は、2,048 バイトのうち 1,763 か 1,776 を知っています。`startCheck` は、全部の段の全部の状態について、操作できるかどうかが読めて、操作できるなら `Start` のバイトを知っていて `B.m` と同じであることを確かめます。

```
start_of_rows : startCheck ∧ InRows(m) ∧ ctl(m)  →  Start(B, m)
EndRun.start  : Statement ∧ EndStatement ∧ startCheck ∧ EndRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  Start(B, seq b)
Run.start     : 同じ条件で、Route の走りについて  Start(B, pole.seq 0)
```

段の中で `left` が 0 なのは最後の段だけです。最後の段には 6 つの状態があり、操作できるのは 2 つです。ほかの 4 つは時間切れです。段は `left` が 0 のところで終わるので、`left` が操作の前に 0 にならないことが要ります（`EndRun.first`。`chg.time₂` と `chg.ctlFirst₂` から証明）。`Route` の新しいフィールドは `atCtl : pole.seq 0 = chg.seq chg.b₂` です。`chg` の条件 `entry₂`、`noStart₂`、`quiet₂` は `Run.change₂` と同じものを使います。

最後の段からは縦のバイトと、A のボタン、当たり判定のビットも出ます。知らない主なものは `PlayerSize` と `EventMusicQueue` です。

## 画面の左端

マリオが画面の左端のピクセルにいるとき、右ボタンだけを押していなければ、スクロールの処理が速さを 0 にします。左端より左に出ると、位置をそのピクセルに戻します。順番は、移動、スクロールの処理、当たり判定です。

* 前の `Frame.impedeP` は本物のフレームで成り立ちません。左へ走って左端を越えるフレームは `v₂ = −v_top`、`P' − P₂ = 512` です。左端へ走る 53,398 フレームのうち 13 フレームがこれです。
* なので `impedeP` の 3 番目を `P' = P₂ + 256 ∧ v₂ ≤ 0` から `P' ≤ P + 256 ∧ v₂ ≤ 0` にしました。`Frame.bound`、`Frame.adv_le`、`chain_reach` はそのままです。
* 1 フレームの文では、これは `Hit` の 2 番目です。`v₂ > 0` でも止まることがあります（測った最大は 4）。そのとき `P(b) = P₂ ≤ P(a) + 256` です。左端のピクセルを速く離れることはないので、これで足ります。この「速くない」は証明していません。`After` の中（`moves` の中）の仮定です。

## 測ったもの

プログラム `surface-frames-check FM2 N`、`N = 200`、終了コード 0、約 3 分です。全部の行で、`OneFrame`、`reads` の `v₂`、`Frame` の `move`、`gain`、`impedeV`、`impedeF`、`impedeP` が成り立たないフレームは 0 です。

| 走り | フレーム | Clean でない | `lag` | 何もしない | 左をふさぐ | `Hit` | 左端で戻す | 1〜8 フレーム目 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| TAS の 852 から | 240 | 5 | 0 | 233 | 0 | 1 | 0 | 8 |
| 1089 のあとの遅い触り、A を長く押す | 34 | 3 | 0 | 30 | 0 | 0 | 0 | 0 |
| 操作からランダム | 36,308 | 4,048 | 0 | 30,705 | 2 | 1,463 | 1 | 1,600 |
| TAS のフレームからランダム | 15,019 | 571 | 0 | 14,087 | 0 | 327 | 0 | 0 |
| Select あり | 10,520 | 571 | 0 | 9,724 | 0 | 180 | 1 | 800 |
| Start あり | 20,311 | 761 | 8,070 | 11,161 | 0 | 284 | 2 | 786 |
| 左端へ走る | 53,398 | 3,804 | 0 | 47,629 | 0 | 1,835 | 13 | 0 |
| 階段のまわりを書き換えた状態 | 103,680 | 5,908 | 0 | 88,917 | 2,653 | 6,202 | 0 | 0 |

* 1〜8 フレーム目では `vert`、`box`、当たり判定に入るときの `(y, vy, st)` が `vstep` の結果であることも確かめました。違いは 0 です。
* `lag` のフレーム 8,070 では、ここで読むバイトは変わりません。なので `seq j` のあとに `lag` のフレームがあっても読む値は同じです。はみ出すフレームはこれらの走りにありません。
* 切り替え: TAS の入る状態と `E` から、Start なしのランダムな入力で 201 回。全部 282 フレーム以上で操作でき、操作の前に `left` が 0 になることはなく、操作のときの状態は全部 `Start` を満たします。
* 測り方: 操作できない機械で終わるフレーム（死ぬ、旗に触る）はフィールドの外なので数えません。そこで `Follow` と `Hit` は成り立ちません。そういう走りは `Run` ではありません。

## 最初のフレームを抽象機械で

最後の段の操作できる状態から 1 フレームを歩いてみました（Lean には入れていません）。

| 知っていること | 歩数 | 失敗 |
|---|---:|---:|
| パッドが不明 | 27,292 | 5（`FindEventMusicHeader+2`） |
| `EventMusicQueue = 0`、パッドが不明 | 2,288 | 4（`JumpEngine+18`） |
| `EventMusicQueue = 0`、パッドは Start なしの 128 通りのそれぞれ | 739,183 | A なしの 64 通りで 1 回（`BlockBufferCollision+43`） |
| さらに `PlayerSize` を場合分け | 1 つの場合に約 840,000 | 0、4 つの場合で約 3 秒 |

なのでフレーム 1 だけなら閉じます。これは 233 フレームのうちの 1 つで、次のフレームの状態の数は増えるので、入れていません。

## 前提（Lean では証明していない）

* `step`: 本物のフレームが `OneFrame` であること。[`FrameModel`](../0-0/0-3-2-FrameModel-ja.md) の仕事です。
* `vert`、`box`: 1〜8 フレーム目のフレームが `vstep` のとおりで、当たり判定が操作のときの機械と同じ結果になること。
* `reads`: `fr` を機械から読むこと。`Frame` であること自体は [最高速の上限](../0-0/0-1-TopSpeed-ja.md) の前提のままです。
* `chg.time₂`、`chg.ctlFirst₂`、`atCtl`。
* 左をふさいだフレームの `MaskStop`。`SurfaceRun.maskSame` は Lean では端数 0、128、255 だけで、この証明には使っていません。全部の端数はプログラムで確かめました（28 秒、違いなし）。

**ファイル.** `Theorems/SurfaceFrames.lean`、非公開の `Proof/SurfaceFrames.lean`（`side_start`）、`Proof/PoleJoin.lean`（`pole_numbers`）。

**再現.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # 上の表、約 3 分
```
