[← Back](README-ja.md) | [English](a-5-4-OpenFrames.md) | [Japanese](a-5-4-OpenFrames-ja.md)

# 本物のフレームでの出だし

**主張.** 本物のフレームでの出だしの上限は、もう `Route.Pipe` のフィールドではありません。最初の 32 の数えるフレームがどれも出だしのモデルの 1 歩であることも定理です。
1 フレームごと、その命令ごと、その始まりの状態ごとの条件から出ます（フィールド `opening`、`OpenFrames.Real`）。

* `openP`（フレーム `N` までの位置は `P₀ + D` 以下）は要りません。操作のときの位置は `P₀` で、タイトルで Start を押したことから読みます（`Run.pipePos`）。フレーム `N` までは
  各フレームが動くのは `16·v_top` 以下です。フレーム `E ≤ N` で入ることは、土管の左なのでできません（`PipeFrames.no_entry_of_start`）。
* `openB`（フレーム `N` の終わりの位置は `P₀ + D` 以下）は定理です（`Run.pipeOpenB`）。最初の `N` フレームのどれもが [出だし](a-3-Opening-ja.md) のモデルの 1 歩であること
  （`OpenRun`）から出ます。
* `OpenRun`（どのフレームもモデルの 1 歩）は定理です（`OpenFrames.Real.toRun`、`Run.pipeOpening`）。横の部分（`hstep`、`16·v` の移動）は本物のフレームの移動です
  （`FrameModel.move_model`、2 つの機械の歩きで証明）。プレイヤーのルーチンでの状態は `CtrlKeep` の歩きから出ます。モデルの入力は、プレイヤーのルーチンが読む入力です。
  空中に残るフレーム数はプレイヤーの状態から読みます。仮定に残るものは `Real` にあります。

`N = 32`、`D = 9744`（1/256 px）、`v_top` は走りの最高速（2.5 px/フレーム）です。`fm(t)` は数えるフレーム `t` が始まるときの機械、`inp(t)` はその入力、
`b(t) = frame(fm t, inp t)` はその終わりの機械、`tr(t, k)` はその `k` 命令あとの機械です。`n₀(t) = arrAt(fm t, inp t)` は、そのフレームが初めてプレイヤーのルーチンに来る命令、
`in(t) = readIn(tr(t, n₀(t)))` はそのルーチンが読む入力です。`hs(m) = startHS(m)` は横の状態（速さ、端数、向き、動く向き、走りの速さ）、`P(m)` は位置、`v(m)` は符号つきの速さ、
`st(m)` はプレイヤーの状態、`ab(m)` は覚えている速さ、`bits(m)` は当たりのビットです。`ground(t)` は `st(fm t) = 0` です。`E` は入るフレームです。
`lens(|v|) = (L_tap, L_hold)` は、ジャンプの始まりから着地のフレームまでの長さで、A を 1 フレームだけ押したときと押し続けたときのものです。跳ぶときの速さごとに
エミュレータで測りました。`Zb = 128` はどの長さよりも大きい数です。

```
OpenRun(air)  :  air(1) = 0,  そして t ∈ [1, N],  t < E  の各 t で  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(fm(t + 1)) = hstep(hs(fm t), i)  ∧  P(fm(t + 1)) = P(fm t) + 16·v(hs(fm(t + 1)))

Real  （t ∈ [1, N],  t < E  の各 t で）:
  cleanK    :  ∀ k,  CleanK(tr(t, k))                     （PipeWrites.Clean に城の旗と位置の端数の保護を足したもの。ただし移動のルーチン自身の書き込みは除く）
  spare     :  ∀ k,  Spare(tr(t, k))                      （添字やポインタでの書き込みが、ポーズのバイト、エリアの種類、泳ぎのフラグ、大きさの変化を書かない）
  st        :  st(fm t) ∈ {0, 1, 2}
  spring    :  JumpspringAnimCtrl(fm t) = 0
  page      :  P(fm t) < 2²³   （t ∈ [1, N + 1],  t ≤ E。ページが 128 より小さい）
  longer    :  フレームは命令 n₀(t) + moveLen より前に終わらない
  after     :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = PlayerSubs  →  b(t) の hs と P の 8 バイトは tr(t, k) のもの,  ab(b t) = |v(b t)|,  bits(b t) = FF
  flat      :  ground(t)  ∧  ¬jump(in t)   →   ground(t + 1)
  jump      :  ground(t)  ∧  jump(in t)    →   ∃ n ≥ 1,  L_tap(|v(fm t)|) ≤ n ≤ L_hold(|v(fm t)|),  1 ≤ d < n で ¬ground(t + d),  ground(t + n)

air(t)        :=  j − t   （j は [t, N + Zb) で ground(j) となる最初の数えるフレーム。なければ N + Zb）
Held(m)       :=  ab(m) = |v(m)|  ∧  bits(m) = FF  ∧  AreaType(m) = v₀  ∧  SwimmingFlag(m) = 0  ∧  PlayerChangeSizeFlag(m) = 0

move_page      :  modelOK,  AtCtrl(tr n₀),  n₀ まで 8 バイトは変わらない,  longer,  PlayerSubs から 8 バイトは変わらない,  P(m) < 2²³,  P(frame m i) < 2²³
                  →   hs(frame m i) = hstep(hs m, readIn(tr n₀))  ∧  P(frame m i) = P(m) + 16·v(frame m i)
Real.frame_step:  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t),  P(b t) < 2²³
                  →   hs(b t) = hstep(hs(fm t), in t)  ∧  P(b t) = P(fm t) + 16·v(b t)  ∧  Held(b t)  ∧  st(tr(t, n₀)) = st(fm t)
lags_keepI     :  数えないフレームは 17 バイトを変えない。その中に hs、P、ab、bits、st、エリアの 3 バイトがある      （LagFrames）
Real.toRun     :  lagCheck, walkCheck, pauseCheck,  Checks,  FrameStart(seq 1),  Held(fm 1),  ground(1),  Real   →   OpenRun(air)
Run.pipeHeld   :  Held(fm 1)  ∧  ground(1)                     （title_check、title_pos_check、m₀ がそれを満たす: open_checks。fm 1 の前のフレームが変えない: Run.pipeKeep₁）
Run.pipeOpening:  OpenRun(air)                                 （フィールド opening と確認から）
Run.pipeOpenB  :  N < E  →  fr(N).P' ≤ P(m₀) + D              （Run.pipeOpening と非公開の opening から）
```

`Checks` は ROM での確認です。`modelOK`（移動）、`ctrlCheck`（プレイヤーのルーチンまでの歩き）、`afterCheck`（1 フレーム全体の歩き。エリアの種類は `m₀` の `v₀`）、
`normIdem`、`lens` のどの長さも `Zb` より小さいこと、`Held(m₀) ∧ st(m₀) = 0`、NMI が見るポーズのバイトが `g` であることです。非公開の `open_checks` がこれを出します。はじめの 3 つはパート e の確認
（`pole_numbers`）で、地上のエリアの種類は `m₀` のものと同じです。`title_pos_check` は、操作のときの `ab`、`bits`、`st` とエリアの 3 バイトの 6 バイトも `m₀` の値かを
確かめるようになりました（ネイティブで約 2.2 秒）。`lag_check` は 17 バイトを追うようになりました（ネイティブで約 6 秒）。ROM のない定理が使う公理は `propext`、
`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/OpenFrames.lean`、`Theorems/PipeFrames.lean` の `lags_keepI`、`Theorems/LagFrames.lean` の `moreI`、`lagI`、`Theorems/StartRun.lean` の `stI`、
`titlePosCheck`、`Begin.bytesAll₁`、`Theorems/Route.lean` の `Pipe.opening`、`Run.pipeKeep₁`、`Run.pipeHeld`、`Run.pipeOpening`、`Run.pipeOpenB`、非公開の `Proof/OpenFrames.lean`、
`Proof/LagPause.lean`、`Proof/Opening.lean`、`Proof/PipeWrites.lean`。

## しくみ

* **移動.** `FrameModel.move_model`: プレイヤーのルーチンからスクロールの処理まで、横の状態はそこで読んだ入力での `hstep` のとおりで、`P` は `2²⁴` を法として `16·v` だけ
  動きます。フレームの始まりと終わりで `P < 2²³` なら `|P' − P − 16·v| < 2²³ + 2048 < 2²⁴` なので、移動はちょうどです（`move_page`）。パート e はここで `2048 ≤ P`
  （`far`）を求めます。これは左へ歩く出だしの本物のフレームで成り立ちません（下を見てください）。ページの条件で足ります。
* **プレイヤーのルーチンでの状態.** フレームはアイドルループで操作できる状態で始まります（`Lags.starts`。`CtrlKeep` の歩きのガードは、アイドルループ、スタックポインタ、
  わかっているバイトが同じです）。ポーズでなく終わる（`Lags.unpaused`: 数えるフレームはポーズでなく終わるフレーム）ので、プレイヤーのルーチンに来ます（`CtrlKeep.arrive_at`）。そこで `keepA` の 25 バイトは始まりの値です
  （`CtrlKeep.ctrl_keep`）。`st`、`spring`、`Held` と合わせて `FrameModel.AtCtrl` になります。入力の状態とジャンプのビットは `st(fm t)` から出ます。
* **フレームからフレームへ.** `after` がフレームの終わりの `ab` と `bits` を出します。1 フレーム全体の歩きと `spare` がエリアのバイトを出します（`CtrlKeep.area_end`）。
  数えないフレームはこれらのバイトと `hs`、`P` を変えません（`lags_keepI`: `LagFrames` の歩きが 9 バイト多く追います）。なので、操作のときからの帰納法で、どの数えるフレームでも
  `Held` が成り立ちます。
* **空中.** `air(t) = 0` は `ground(t)` のときだけです。空中では定義から `air(t + 1) = air(t) − 1` です。地面で跳び始めなければ、`flat` から `air(t + 1) = 0` です。
  跳び始めでは、`jump` が着地 `t + n` を出すので `air(t + 1) = n − 1 ∈ [L_tap − 1, L_hold − 1]` です。モデルの入力は `norm(in t)` です。状態とジャンプのビットは同じで、
  それでの `hstep` も同じです（`normIdem`）。
* **操作のとき.** `title_pos_check` は、タイトルの集合の近い状態のどれからもどの入力でもフレーム 0 を追います。操作できる終わりのそれぞれで、位置、横の状態、`stI` の
  6 バイトが `m₀` の値でわかっていることを確かめます。

## 本物のフレームで確かめたこと

プログラムです（`open-real-check`）。操作のときの機械から最初の 32 の数えるフレームを動かします（インターバルタイマーの段が動かないフレームは数えません）。各フレームを
1 命令ずつ動かし、`Real` の各フィールド、証明が出すこと（フレームの始まりの `Held`、プレイヤーのルーチンでの `keepA`、フレームの終わりと次の数えるフレームでの `hstep` と
`16·v`）、数えないフレームが 17 バイトを変えないことを確かめます。

| 走り | 数えるフレーム | そのあいだの数えないフレーム | 跳び始め | `Real` のフィールドが成り立たない | モデルの 1 歩でない |
|---|---|---|---|---|---|
| TAS | 32 | 0 | 2 | 0 | 0 |
| 操作のときからの自分の入力、Start あり（300 回） | 9,600 | 10,229 | 566 | 0 | 0 |
| 操作できる最初の 4 フレームのどれかで 43〜82 フレームのポーズ、そのあと TAS の入力（60 回、ポーズが終わるのは 58 回） | 1,856 | 5,814 | 116 | 0 | 0 |

* TAS では、操作のときの `stI` の 6 バイト、位置、横の状態は `m₀` のものです。
* **パート e の `far` はここでは成り立ちません**: 自分の走りの 50 フレームで、フレーム 32 より前に `P = 2048`（8 px）より左へ歩きます。ページの条件はどれでも成り立ちます。
* **操作できる最初のフレームで Start**: そのフレームはポーズで終わり、タイマーの段は動かないので、時計はそれを数えません。この回の前は `PipeFrames.Lags` が走りの
  フレーム 1 を数えるフレーム 1 にしていたので、そういう走りでは `t = 1` で `unpaused` が成り立たず、扱えていませんでした。いまは数えるフレームをポーズのバイトから読みます
  （`PipeFrames.ixP`、[LagPause](a-5-5-3-3-LagPause-ja.md)）。数えるフレーム 1 はフレーム 1 から先でポーズでなく終わる最初のフレームで、操作のときの状態はそこまで運ばれます
  （`Run.pipeKeep₁`）。3 行目の走りは最初のフレームでポーズします。その数えるフレーム 1 より前のフレームは 17 バイトを変えません。これらの走りでは、数えるフレーム 32 までの
  全部のフレームを 1 命令ずつも動かします（7,728 フレーム）。どの命令も `Clean`（`lags.clean`）で、数えないフレームが添字やポインタでポーズのバイトを書くことはありません
  （`lags.keeps`。いまは数えるフレーム 1 より前のフレームも含みます）。
* これらの走りの、操作できない状態で終わる最初のフレームまでの全部のフレームで、タイマーの段が動くのはポーズでなく終わるときだけです（81,931 フレームで例外なし）。
  3 行目の走りのうち 13 回はあとで操作できなくなります（死ぬ。再開した入力がゲームに合わない）。そのあとは、数えないフレームがポーズでなく終わります。そういう走りは
  定理の外です（`lags.ctl`）。

## 前提（Lean では証明していない）

* `Real` のフィールド: `cleanK`、`spare`、`st`、`spring`、`page`、`longer`、`after`、`flat`、`jump`。1 フレームごと、その命令ごと、その始まりの状態ごとの
  条件です。`after` は、スクロールの処理からあと何も彼を動かさず、当たりのルーチンが何も見つけないこと（壁も画面の端もない）です。項目 1-1-a-5-6 の横の半分です。
  `flat` はその縦の半分です（地面から落ちない）。`jump` は項目 1-1-a-5-7 です。
* もう仮定しないこと: 各フレームがモデルの 1 歩であること（`hstep`、`16·v` の移動、モデルの入力、`valid`）、列 `air`。各数えるフレームがポーズでなく終わることは
  定理です（`PipeFrames.Lags.unpaused`）。数えるフレームはポーズでなく終わるフレームで、`dP` フレームの中で見つかります（`lags.resume`）。
* **証明していないこと:** フレーム 368 で入れること（前と同じ）。

**ファイル.** `Theorems/OpenFrames.lean`、`Theorems/PipeFrames.lean`、`Theorems/LagFrames.lean`、`Theorems/StartRun.lean`、`Theorems/Route.lean`、非公開の
`Proof/OpenFrames.lean`、`Proof/LagPause.lean`、`Proof/Opening.lean`。

**再現.**
```
.lake/build/bin/smbrta open-real-check FM2 300      # Real のフィールドを TAS と自分の入力で、タイトルの確認、数えないフレームの歩き、約 1 分
.lake/build/bin/smbrta open-frames-check FM2 300    # 最初の 32 フレームをモデルの 1 歩として
.lake/build/bin/smbrta open-check 32 9744           # モデルの上限（true）
```
