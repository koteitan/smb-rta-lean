[← Back](README-ja.md) | [English](a-5-5-PipeFrames.md) | [Japanese](a-5-5-PipeFrames-ja.md)

# 土管までのフレームを機械から読む

**主張.** 操作できるときから縦の土管に入るフレームまで、各フレームの速さ、速さの端数、位置を本物の機械から読みます。すると、フレームが次々につながること（`next`）と、
各フレームの速さが走りの最高速以下であること（`speed`）は定理になります。[縦の土管に入る](a-4-PipeEntry-ja.md) の上限はそのまま成り立ち、フレーム 368 より前には入りません。

`fm(t)` はフレーム `t` が始まるときの機械です。フレームは `lag` のフレームを数えずに番号をつけます（[1-1 全体](0-1-Route-ja.md)）。フレーム 0 は操作できる状態で終わるので、
`fm(1)` が操作できるときの機械です。`v(m)` は `Player_X_Speed` の符号つきの値、`f(m)` は `Player_X_MoveForce`、`P(m)` は位置です。`fr(t)` はフレーム `t` の
[`Frame`](../0-0/0-1-TopSpeed-ja.md) で、始まりの値 `v, f, P`、移動のときの `v₂, P₂`、終わりの値 `v', f', P'` を持ちます。`E` は入るフレーム、`v_top` は走りの最高速です。

```
Reads(E, fm, fr)  :=  ∀ t ∈ [1, E],   fr(t).v = v(fm t)    ∧  fr(t).f = f(fm t)    ∧  fr(t).P = P(fm t)
                      ∀ t ∈ [1, E),   fr(t).v' = v(fm(t+1)) ∧  fr(t).f' = f(fm(t+1)) ∧  fr(t).P' = P(fm(t+1))
Next(a, b)        :=  b.v = a.v'  ∧  b.f = a.f'  ∧  b.P = a.P'

next_of_reads     :  Reads  →  ∀ t ∈ [1, E),  Next(fr t, fr(t+1))
speed_of_reads    :  16 ≤ v_top,  Reads,  v(fm 1) = 0  →  ∀ t ∈ [1, E],  |fr(t).v| ≤ v_top
speed_end         :  同じ仮定  →  ∀ t ∈ [1, E],  |fr(t).v'| ≤ v_top
end_le            :  同じ仮定,  1 ≤ N,  fr(N).P' ≤ B  →  ∀ k,  N + k < E  →  fr(N + k).P' ≤ B + 16·v_top·k
no_entry_of_reads :  16 ≤ v_top,  1 ≤ N,  (∀ t,  Enter t → L ≤ fr(t).P₂),  (∀ t ≤ N,  fr(t).P₂ ≤ B),  fr(N).P' ≤ B,
                     Reads,  v(fm 1) = 0,  B + 16·v_top·(T − N) < L,  Enter E   →   T < E
pos_le            :  16 ≤ v_top,  Reads,  v(fm 1) = 0   →   ∀ k,  1 + k ≤ E  →  fr(1 + k).P ≤ fr(1).P + 16·v_top·k
no_entry_of_start :  16 ≤ v_top,  1 ≤ N,  2·N ≤ T,  (∀ t,  Enter t → L ≤ fr(t).P₂),  fr(1).P ≤ B,  (N < E → fr(N).P' ≤ B),
                     Reads,  v(fm 1) = 0,  B + 16·v_top·(T − N) < L,  Enter E,  1 ≤ E   →   T < E          （N までの各フレームの上限は要らない）

Pipe.next, Pipe.speed（Route）       :  前のフィールド next と speed を定理として
Pipe.reads（Route）                   :  Reads を、自分の機械から読むフレームと数えないフレームから（own、lags、lag_check、walk_check、pause_check、操作できるときの始まり）
pipe_no_entry_real（非公開）          :  Enters(fm E, inp E),  FrameStart(fm E),  clean, tiles, edge, moved,  fr(1).P = P₀,  (32 < E → fr(32).P' ≤ P₀ + 9744),  Reads,  still,  1 ≤ E   →   367 < E
```

`Reads` はもうフィールドではありません。[土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md) が、`Pipe.own`（数えるフレームはそのフレーム自身の機械で終わる）と
`Pipe.lags`（そのあいだの数えないフレーム）から証明します。

ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/PipeFrames.lean`、`Theorems/Route.lean` の `Pipe`、非公開の `Proof/PipeWrites.lean`。

## しくみ

* **つながり.** `fr(t)` の終わりと `fr(t+1)` の始まりは、同じ機械 `fm(t+1)` から読みます。なので `Next` は定義から出ます。
* **速さ.** `fm(1)` で速さは 0 です。`Frame.bound` は、始まりの速さが `v_top` 以下なら終わりの速さも `v_top` 以下だと言います。`Next` でこれを次のフレームに渡します。
  フレーム 1 から `E` まで、帰納法です。
* **上限.** `E ≤ N` なら: フレーム `E` は操作のときから `16·v_top·(E − 1)` 以下しか右で始まらないので（`pos_le`）、`fr(E).P₂ ≤ fr(1).P + 16·v_top·E ≤ B + 16·v_top·N` です。
  `2·N ≤ T` なので、これは `L` より左です（`no_entry_of_start`。前はフィールド `openP` が `fr(E).P₂ ≤ B` を言いました）。`E > N` なら、フレーム `N + k` の終わりは `B + 16·v_top·k` 以下です（`end_le`）。`E = N + k + 1` で
  `fr(E).P₂ ≤ fr(E).P + 16·v_top` なので、`fr(E).P₂ ≤ B + 16·v_top·(E − N)` です。`E ≤ T` だと `L` より左なので、入れません。フレーム `N` の上限は `N < E` のときだけ求めます。
* 前の `no_entry_by` は `N` のあとの全部のフレームの `next` と、`N` での `speed` を仮定しました。ここでは `E` までのフレームだけを使います。

## 本物のフレームで確かめたこと

プログラムです（`pipe-frames-check`）。各フレームについて、始まりの機械 `fm(t)`、移動のあとの機械（`PlayerSubs` に来たとき）、次に数えるフレームの始まりの機械 `fm(t+1)` を読みます。
2 つを確かめます。(a) 移動のあとの値を `v₂, f₂, P₂` として、`Frame` の 8 つの条件が成り立つか（`v₁, f₁` は始まりの値か 0）。(b) 同じ両端を持つ `Frame` があるか（`v₂` を 1 バイトの範囲で探す）。
フレーム `N` と `E` のあいだで `Reads` が求めるのは (b) だけです。数えないフレームは、速さ、端数、位置を変えないことを確かめます。

| 走り | 数えるフレーム | `lag` のフレーム | (a) が成り立たない | (b) が成り立たない | `lag` で値が変わる | 入ったフレーム |
|---|---|---|---|---|---|---|
| TAS の操作から入るまで | 368 | 0 | 0 | 0 | 0 | 368 |
| TAS の機械から乱数の入力（300 回） | 343,728 | 52,400 | 3 | 0 | 0 | なし |
| TAS の入る前の機械から右、そのあと下（1,200 回） | 90,110 | 0 | 0 | 0 | 0 | 322 回（368 から 371） |

* 操作できるときの速さ: タイトル画面で Start を押すフレームを 120 通りに変えて、120 回とも 0 です。横の状態と位置も、120 回とも非公開の証明の機械 `m₀` と同じです。TAS も 0 です。
* TAS では、フレーム 32 までの `P₂` は `P₀ + 9744` 以下で、フレーム 33 の始まりの位置はちょうど `P₀ + 9744` です（前のフィールド `openP`、`openB`。いまは [本物のフレームでの出だし](a-5-4-OpenFrames-ja.md)）。
* 数えないフレームは、ポーズのあいだと、大きくなる、小さくなる、死ぬときに出ます。`TimerControl` が 0 でないあいだ、ゲームはインターバルタイマーを減らさないからです（コードから読みました）。
  測ったどの数えないフレームも、速さ、端数、位置を変えません。乱数の 300 回のうち、51 回は死んで終わり、12 回は大きさが変わりました。
  **訂正（この回）:** 走りは、操作できない状態で終わる最初の数えるフレームで止めています。なので、大きくなる、けが、死のあとの数えないフレームはここでは測っていません。
  けがのあとの点滅のあいだは、値が変わります（[土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md)）。
* **(a) が成り立たない 3 フレーム.** どれも、穴に落ちて画面より下にいるときです。スクロールが止まり、`KeepOnscr` が画面の右端でマリオを止めます。
  たとえば `v₂ = 24 > 0`、`P' = P₂ − 512`、`v' = 0` です。`Frame` の `impedeP` は画面の左端の場合しか含みません。画面より下に落ちると、そのあと死にます（コードから読みました）。なので入るフレームより前には来ません。
  同じ両端の `Frame` はあります（`v₂ = 0`）。

## 前提（Lean では証明していない）

* **各フレームは `Frame` である.** `fr` の型です。前からの前提で、項目 0-0-0-3-1 です（`FrameModel.frame_read` は `ReadFrame` のもとでこれを出します）。上の本物のフレームで確かめました。
  新しいのは、フレーム 1 から `N` までにもこれを使うことです。
* **数えないフレームは 3 つの値を変えない.** まとめての仮定ではなくなりました。モードのルーチンを呼ばないフレーム（ポーズ）では証明しました。
  残る仮定は [土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md) と [操作から土管までの各フレームはアイドルループで始まる](a-5-5-3-2-StartRun-ja.md) の `lags.ctl`（いまは数えるフレームだけ）と、各命令の `Clean`（`Lags.CleanP`。前のフィールド `lags.clean` で、いまは `chg.upCleanU` から: [土管までの各命令に 1 つの条件](a-5-10-UpClean-ja.md)）です。これが `lags.keeps` のしていたことも出します（[ポーズで終わるフレームはモードのルーチンを呼ばない](a-5-5-3-3-LagPause-ja.md)）。`lags.store` はいまは証明しています。`lags.paused` はなくなりました。数えないフレームは、数えるフレームの定義からポーズで終わります。
* **`still`: 操作できるときの速さは 0.** いまはタイトルで Start を押したところから証明しています（`Route.Run.still`、[タイトルの Start から操作できるまで](0-5-3-TitleStart-ja.md)）。
* **フレームは走りのフレーム（項目 1-1-0-4）.** `Lags` は走り全体の本物のフレーム（`FrameKeep.RealRun`、`Route.Run.base`）を引数にとります。数えるフレームの場所は機械から読みます。`ixP` は定義で、数えるフレーム `t + 1` は数えるフレーム `t` のあとでポーズでなく終わる最初のフレーム（`dP` フレームまで見る）、数えるフレーム 1 はフレーム 1 から先の最初のそういうフレームです。
  なので `pipe` の操作できるときの機械は走りのフレーム 1 の値を持ちます（`Route.Run.pipeKeep₁`）。前のつなぎ `pipeAt`（数えるフレーム 1 はフレーム 1）、フィールド `gap`、`Lags` の前のフィールド `seq`、`sin`、`next`、`ix`、`order`、`fm_ix`、`inp_ix`、`Route.Pipe` のフィールド `fm`、`inp`、`one_le` はなくなりました（`Pipe.fm` は定義 `Lags.fm`、`Pipe.one_le` は定理）。
* **この項目でないもの.** `openP` はなくなり、`openB` はフィールド `opening` からの定理です（項目 1-1-a-5-4、[本物のフレームでの出だし](a-5-4-OpenFrames-ja.md)）。`edge`、`moved`（項目 1-1-a-5-9）は、仮定のままです。

**ファイル.** `Theorems/PipeFrames.lean`、`Theorems/LagFrames.lean`、`Theorems/Route.lean`、非公開の `Proof/PipeWrites.lean`。

**再現.**
```
.lake/build/bin/smbrta pipe-frames-check FM2 300    # 操作できるときの速さと、本物のフレームでの Reads と Frame
```
