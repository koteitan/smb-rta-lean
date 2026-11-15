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
* `longer`（移動のあいだにフレームは終わらない）は定理です。どの命令も `CleanK.time` を満たすので、歩きのフレームは移動のあとで終わります
  （`FrameModel.trace_inFrame`。パート e と同じやり方）。
* `page` は数えるフレーム 1 から `N + 1` のどの始まりでも求めていました。いまは数えるフレーム `N + 1` の始まりだけで求めます。その前のフレームの終わりでは、
  モデルの 2 つの探索で位置がちょうどになります。右は [出だし](a-3-Opening-ja.md)、左は [出だしの左への上限](a-5-4-3-3-2-OpenLeft-ja.md) が抑えます。

`N = 32`、`D = 9744`（1/256 px）、`v_top` は走りの最高速（2.5 px/フレーム）です。`fm(t)` は数えるフレーム `t` が始まるときの機械、`inp(t)` はその入力、
`b(t) = frame(fm t, inp t)` はその終わりの機械、`tr(t, k)` はその `k` 命令あとの機械です。`n₀(t) = arrAt(fm t, inp t)` は、そのフレームが初めてプレイヤーのルーチンに来る命令、
`in(t) = readIn(tr(t, n₀(t)))` はそのルーチンが読む入力です。`hs(m) = startHS(m)` は横の状態（速さ、端数、向き、動く向き、走りの速さ）、`P(m)` は位置、`v(m)` は符号つきの速さ、
`st(m)` はプレイヤーの状態、`ab(m)` は覚えている速さ、`bits(m)` は当たりのビットです。`ground(t)` は `st(fm t) = 0` です。`E` は入るフレームです。
`lens(|v|) = (L_tap, L_hold)` は、ジャンプの始まりから着地のフレームまでの長さで、A を 1 フレームだけ押したときと押し続けたときのものです。跳ぶときの速さごとに
エミュレータで測りました。`Zb = 128` はどの長さよりも大きい数です。`V(m)` は高さ、その上位バイト、縦の速さ、その端数、`Q` はプレイヤーのルーチンの中で
当たり判定のルーチンから戻るところ、`GroundAt(m)` は `V(m)` が地面のもの（`m₀` の高さ、1、0、0）であることです。`VS(m)` は `vstep` の縦のバイト、`hi(m)` は
高さの上位バイト、`a(t)` はプレイヤーのルーチンが読む数えるフレーム `t` の A、`vstepO` と `ground0` は [出だしのジャンプ](a-5-7-OpenJump-ja.md) の出だしの縦の
モデルです。

```
OpenRun(air)  :  air(1) = 0,  そして t ∈ [1, N],  t < E  の各 t で  ∃ i ∈ inputsN:
                   valid(air t, i)  ∧  air(t + 1) ∈ modes(lens, hs t, air t, i)
                   ∧  hs(fm(t + 1)) = hstep(hs(fm t), i)  ∧  P(fm(t + 1)) = P(fm t) + 16·v(hs(fm(t + 1)))
OpenRunM(air) :  OpenRun(air) の移動を  (P(fm(t + 1)) − P(fm t) − 16·v(hs(fm(t + 1)))) mod 2²⁴ = 0  にしたもの

Real  （t ∈ [1, N],  t < E  の各 t で）:
  cleanK    :  ∀ k,  CleanK_E(tr(t, k))                   （PipeWrites.Clean に城の旗、位置の端数、ポーズのバイト、エリアの種類、泳ぎのフラグ、大きさの変化、
                                                          A と B、前のフレームの A と B、動く向き、走る速さ、覚えている速さの保護を足したもの。ただし移動の
                                                          ルーチン自身の書き込みは除く: FrameKeep.guardE）
  noStore   :  ∀ k,  tr(t, k) でルーチン、モード、タスクに番地で書かない
  after     :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = PlayerSubs  →  b(t) の hs と P の 8 バイトは tr(t, k) のもの,  ab(b t) = |v(b t)|,  bits(b t) = FF
  afterV    :  ∀ k ≥ n₀(t),  pc(tr(t, k)) = Q  →  b(t) の vsA の 11 バイトは tr(t, k) のもの
                                                          （当たり判定から戻る Q からあと、高さ、その上位バイト、縦の速さ、その端数、高さの端数、2 つの力、
                                                          ジャンプの始まりの高さ、状態、A と B、止める値は変わらない）
そして 1 回だけ:
  page      :  N < E  →  page(fm(N + 1)) ≠ 255
1 ≤ n ≤ ix(N)、n < ix(E) の各フレーム n（数えるものも数えないものも）の各命令で（OpenMap）:
  map       :  MapOK(tr_n(k))                             （添字やポインタでの書き込みが、プレイヤーの状態、ジャンプ台のバイト、ブロックバッファ、当たりの
                                                          ルーチンを止める旗を書かない。ブロックバッファのルーチンの読み出しは最初のバッファの中）

Real.stSpring :  確認,  Real,  FrameStart(seq 1),  MapAt(seq 1)   →   st(fm t) ∈ {0, 1, 2}  ∧  JumpspringAnimCtrl(fm t) = 0     （前のフィールド st、spring）
Real.flat     :  確認,  Real,  FrameStart(seq 1),  MapAt(seq 1),  Held(fm t),  ground(t),  GroundAt(fm t),  ¬jump(in t)
                 →   ground(t + 1)  ∧  GroundAt(fm(t + 1))                                                （前のフィールド flat。OpenFlat）
Real.vertOK   :  確認,  Real,  Held,  StSpring,  PrevOK(fm 1)   →   VertOK: N までの跳ぶフレームと空中のフレームは vstepO の 1 歩     （前のフィールド vert。
                                                                                                          OpenAir、a-5-7-2）
Real.jumpV    :  確認,  VertOK,  t ∈ [1, N],  t < E,  Held(fm t),  |v(fm t)| ≤ top,  ground(t),  GroundAt(fm t),  jump(in t)
                 →   (∃ n ≥ 1,  t + n ≤ H,  L_tap ≤ n ≤ L_hold,  1 ≤ d < n で ¬ground(t + d),  ground(t + n),  GroundAt(fm(t + n)))
                     ∨  (t + d ≤ H で ¬ground(t + d)  ∧  H − t < L_hold)                        （前のフィールド jump。OpenJump）
Real.ground_all: 確認,  Real,  各 t の Held(fm t)、StSpring、|v(fm t)| ≤ top,  ground(1),  GroundAt(fm 1)   →   ground(t)  →  GroundAt(fm t)
                                                                                                          （前のフィールド ground。OpenFlat、OpenJump）

air(t)        :=  airT(t):  地面では 0;  t − 1 で跳んだあと:  地面の上の最初の数えるフレーム j が H = min(N + 1, E) までに来れば  j − t、
                  来なければ  max(L_tap − 1, H − t);  空中のあとの空中では  air(t − 1) − 1
Held(m)       :=  ab(m) = |v(m)|  ∧  bits(m) = FF  ∧  AreaType(m) = v₀  ∧  SwimmingFlag(m) = 0  ∧  PlayerChangeSizeFlag(m) = 0

hopt           :  ∀ k ≤ N,  Reach(start, k, u)  →  dist(u) ≤ D                   （Opening、非公開の opening）
hlow           :  ∀ k < N,  Reach(start, k, u)  →  −P(m₀) ≤ dist(u)              （OpenLeft、非公開の open_left）
htop           :  P(m₀) + D < 2²⁴                                                 （非公開の open_left）

move_mod       :  modelOK,  AtCtrl(tr n₀),  n₀ まで 8 バイトは変わらない,  frame(tr n₀) = frame(m),  CleanK.time,  アイドルループ,  PlayerSubs から 8 バイトは変わらない
                  →   hs(frame m i) = hstep(hs m, readIn(tr n₀))  ∧  (P(frame m i) − P(m) − 16·v(frame m i)) mod 2²⁴ = 0
Real.frame_step:  Checks,  Real,  t ∈ [1, N],  t < E,  StartK(fm t),  Held(fm t)
                  →   hs(b t) = hstep(hs(fm t), in t)  ∧  (P(b t) − P(fm t) − 16·v(b t)) mod 2²⁴ = 0  ∧  Held(b t)  ∧  st(tr(t, n₀)) = st(fm t)
lags_keepI     :  数えないフレームは 28 バイトを変えない。その中に hs、P、ab、bits、st、エリアの 3 バイト、VS、上位バイト、両方のフレームの A と B、
                  止める値がある      （LagFrames）
Real.toRunM    :  lagCheck, walkCheck, pauseCheck,  Checks,  FrameStart(seq 1),  Held(fm 1),  ground(1),  GroundAt(fm 1),  t ≤ E で |v(fm t)| ≤ top,  Real,
                  PrevOK(fm 1)
                  →   OpenRunM(air)
OpenRunM.next  :  OpenRunM(air),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page,  k < N,  1 + k < E,  Reach(start, k, st(1 + k))
                  →   P(fm(k + 2)) = P(fm(k + 1)) + 16·v(fm(k + 2))  ∧  Reach(start, k + 1, st(k + 2))
OpenRunM.toRun :  OpenRunM(air),  hs(fm 1) = hs(m₀),  P(fm 1) = P(m₀),  hopt,  hlow,  htop,  page   →   OpenRun(air)
Real.toRun     :  Real.toRunM のあと OpenRunM.toRun
Run.pipeHeld   :  Held(fm 1)  ∧  ground(1)  ∧  GroundAt(fm 1)   （title_check、title_pos_check、m₀ がそれを満たす: open_checks。fm 1 の前のフレームが変えない: Run.pipeKeep₁）
Run.pipeSpeed  :  ∀ t ∈ [1, E],  |v(fm t)| ≤ top                （PipeFrames.speed_of_reads。Pipe.reads と Run.still から）
Run.pipeOpening:  OpenRun(air)                                 （フィールド opening と確認から）
Run.pipeOpenB  :  N < E  →  fr(N).P' ≤ P(m₀) + D              （Run.pipeOpening と非公開の opening から）
```

`st(t)` は数えるフレーム `t` が始まるときのモデルの状態 `((hs(fm t), air(t)), P(fm t) − P(fm 1))` です。

`Checks` は ROM での確認です。`modelOK`（移動）、`ctrlCheck`（プレイヤーのルーチンまでの歩き）、`afterCheck`（1 フレーム全体の歩き。エリアの種類は `m₀` の `v₀`）、
`normIdem`、`lens` のどの長さも `Zb` より小さいこと、`Held(m₀) ∧ st(m₀) = 0`、NMI が見るポーズのバイトが `g` であること、アイドルループが自分への `JMP` であること、
地面の上のフレームの歩き（`OpenFlat.flatCheck`、非公開の `open_flat_check`、ネイティブで約 3 秒）、`16 ≤ top`、出だしの縦のモデルのジャンプの探索
（`OpenJump.arcCheck`、非公開の `open_jump_check`、ネイティブで約 2.4 秒）です。
非公開の `open_checks` がこれを出します。はじめの 3 つとアイドルループはパート e の確認（`pole_numbers`）で、地上のエリアの種類は `m₀` のものと同じです。`m₀` は地面の高さにいます（`GroundAt(m₀)`、`start` の中）。`title_pos_check` は、操作のときの `ab`、`bits`、`st`、
エリアの 3 バイト、`V` の 4 バイト、A と B、前のフレームの A と B の 12 バイトも `m₀` の値かを確かめます（ネイティブで約 2.2 秒）。`lag_check` は 28 バイトを追うようになりました（ネイティブで約 7 秒）。ROM のない定理が使う公理は `propext`、
`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/OpenFrames.lean`、`Theorems/OpenLeft.lean`、`Theorems/OpenMap.lean`（`Real.stSpring` が使う）、`Theorems/OpenFlat.lean`（`Real.flat` が使う）、`Theorems/OpenJump.lean`（`Real.jumpV` が使う）、`Theorems/PipeFrames.lean` の `lags_keepI`、`Theorems/LagFrames.lean` の `moreI`、`lagI`、`Theorems/StartRun.lean` の `stI`、
`titlePosCheck`、`Begin.bytesAll₁`、`Theorems/Route.lean` の `Pipe.opening`、`Run.pipeKeep₁`、`Run.pipeHeld`、`Run.pipeOpening`、`Run.pipeOpenB`、非公開の `Proof/OpenFrames.lean`（`open_checks`、`open_left`）、
`Proof/OpenFlat.lean`、`Proof/LagPause.lean`、`Proof/Opening.lean`、`Proof/PipeWrites.lean`。

## しくみ

* **移動.** `FrameModel.move_model`: プレイヤーのルーチンからスクロールの処理まで、横の状態はそこで読んだ入力での `hstep` のとおりで、`P` は `2²⁴` を法として `16·v` だけ
  動きます（`move_mod`）。移動のあいだにフレームは終わりません。ルーチンにはそのフレームのうちに来て（`CtrlKeep.arrive_at`）、アイドルループ以外のどの命令も
  ドット `dotsPerFrame − 64` 以下で動き（`CleanK.time`）、アイドルループは自分への `JMP` です。なので `FrameModel.trace_inFrame` が歩きの各ステップをフレームの中で
  たどります。これがフィールド `longer` でした。
* **ちょうどの位置.** パート e はここで `2048 ≤ P`（`far`）を求めます。これは左へ歩く出だしの本物のフレームで成り立ちません（下を見てください）。代わりに数えるフレームの
  帰納法で、数えるフレーム `1 + k` が始まるときの状態は、モデルが最初から `k` 歩で着く状態です（`OpenRunM.reachAll`）。モデルの次の状態 `u'` には `k + 1` 歩で着き、
  `P(fm(1 + k)) + 16·v' = P(m₀) + dist(u')` です。`k + 1 < N` なら 2 つの探索がこれを `[0, P(m₀) + D] ⊂ [0, 2²⁴)` に入れるので、移動はちょうどです（`exact_of_mod`）。
  `k + 1 = N` でも右の上限は成り立ちます。和が 0 より小さければ、終わりの位置は `P + 16·v' + 2²⁴ ≥ 2²⁴ − 2048` でページ 255 になります。これを `page` が除きます
  （`exact_of_page`）。
* **プレイヤーのルーチンでの状態.** フレームはアイドルループで操作できる状態で始まります（`Lags.starts`。`CtrlKeep` の歩きのガードは、アイドルループ、スタックポインタ、
  わかっているバイトが同じです）。ポーズでなく終わる（`Lags.unpaused`: 数えるフレームはポーズでなく終わるフレーム）ので、プレイヤーのルーチンに来ます（`CtrlKeep.arrive_at`）。そこで `keepA` の 25 バイトは始まりの値です
  （`CtrlKeep.ctrl_keep`）。`Real.stSpring` のプレイヤーの状態とジャンプ台のバイト、`Held` と合わせて `FrameModel.AtCtrl` になります。入力の状態とジャンプのビットは `st(fm t)` から出ます。
* **フレームからフレームへ.** `after` がフレームの終わりの `ab` と `bits` を出します。1 フレーム全体の歩きと `cleanK` がエリアのバイトを出します（`SurfaceFrames.area_endF`）。
  数えないフレームはこれらのバイトと `hs`、`P` を変えません（`lags_keepI`: `LagFrames` の歩きが 13 バイト多く追います）。なので、操作のときからの帰納法で、どの数えるフレームでも
  `Held` が成り立ちます。
* **空中.** `air(t) = 0` は `ground(t)` のときだけです。空中では定義から `air(t + 1) = air(t) − 1` です。地面で跳び始めなければ、`Real.flat`（[出だしの平らな地面](a-5-4-3-4-1-OpenFlat-ja.md)）から `air(t + 1) = 0` です。
  これには `GroundAt(fm t)` が要ります。これは地面の上のどの数えるフレームでも成り立ちます（`Real.ground_all`）: `GroundAt(fm 1)`、`Real.flat` そのもの、着地のあとの
  `Real.jumpV` からの帰納法です。
  跳び始めでは、`Real.jumpV` が `H` までの着地 `t + n` を出すので `air(t + 1) = n − 1 ∈ [L_tap − 1, L_hold − 1]` です。`H` までに着地しなければ `H − t < L_hold`
  なので `air(t + 1) = max(L_tap − 1, H − t − 1)` もそのあいだです。これは `Real.vertOK` とモデルのジャンプの探索から出ます（[出だしのジャンプ](a-5-7-OpenJump-ja.md)）。跳ぶときの速さは最高速以下です（`Run.pipeSpeed`）。モデルの入力は `norm(in t)` です。状態とジャンプのビットは同じで、
  それでの `hstep` も同じです（`normIdem`）。
* **操作のとき.** `title_pos_check` は、タイトルの集合の近い状態のどれからもどの入力でもフレーム 0 を追います。操作できる終わりのそれぞれで、位置、横の状態、`stI` の
  12 バイトが `m₀` の値でわかっていることを確かめます。

## 本物のフレームで確かめたこと

プログラムです（`open-real-check`）。操作のときの機械から最初の 32 の数えるフレームを動かします（インターバルタイマーの段が動かないフレームは数えません）。各フレームを
1 命令ずつ動かし、`Real` の各フィールド、証明が出すこと（フレームの始まりの `Held`、プレイヤーのルーチンでの `keepA`、フレームの終わりと次の数えるフレームでの `hstep` と
`16·v`）、数えないフレームが 28 バイトを変えないことを確かめます。

| 走り | 数えるフレーム | そのあいだの数えないフレーム | 跳び始め | `Real` のフィールドが成り立たない | モデルの 1 歩でない |
|---|---|---|---|---|---|
| TAS | 32 | 0 | 2 | 0 | 0 |
| 操作のときからの自分の入力、Start あり（300 回） | 9,600 | 9,600 | 528 | 0 | 0 |
| 操作できる最初の 4 フレームのどれかで 43〜82 フレームのポーズ、そのあと TAS の入力（60 回、ポーズが終わるのは 58 回） | 1,856 | 5,814 | 116 | 0 | 0 |

* TAS では、操作のときの `stI` の 12 バイト、位置、横の状態は `m₀` のものです。
* 縦のモデルの 1 歩（`VStep`）は、`N` までの空中かジャンプを読むどの数えるフレームでも確かめます。11 バイトの `afterV`、`noStore`、`guardE` の `CleanK` も
  どの数えるフレームでも確かめ、証明が各数えるフレームの始まりで出す関係（前のフレームの A と B、止める値の関係、当たりの旗 0）も確かめます。数は
  [本物のフレームの上の縦のモデル](a-5-7-2-OpenAir-ja.md) にあります。
* **パート e の `far` はここでは成り立ちません**: 最初のフレームで A と B と左を押し、そのあと B と左を押し続ける自分の走りは、数えるフレーム 33 を `P = 320`（1.25 px）で
  始めます。画面の端には触りません。`page` はどれでも成り立ちます。
* **操作できる最初のフレームで Start**: そのフレームはポーズで終わり、タイマーの段は動かないので、時計はそれを数えません。12 回目の前は `PipeFrames.Lags` が走りの
  フレーム 1 を数えるフレーム 1 にしていたので、そういう走りでは `t = 1` で `unpaused` が成り立たず、扱えていませんでした。いまは数えるフレームをポーズのバイトから読みます
  （`PipeFrames.ixP`、[LagPause](a-5-5-3-3-LagPause-ja.md)）。数えるフレーム 1 はフレーム 1 から先でポーズでなく終わる最初のフレームで、操作のときの状態はそこまで運ばれます
  （`Run.pipeKeep₁`）。3 行目の走りは最初のフレームでポーズします。その数えるフレーム 1 より前のフレームは 28 バイトを変えません。これらの走りでは、数えるフレーム 32 までの
  全部のフレームを 1 命令ずつも動かします（7,728 フレーム）。どの命令も `Clean`（`lags.clean`）で、数えないフレームが添字やポインタでポーズのバイトを書くことはありません
  （`lags.keeps`。いまは数えるフレーム 1 より前のフレームも含みます）。
* これらの走りの、操作できない状態で終わる最初のフレームまでの全部のフレームで、タイマーの段が動くのはポーズでなく終わるときだけです（81,931 フレームで例外なし）。
  3 行目の走りのうち 13 回はあとで操作できなくなります（死ぬ。再開した入力がゲームに合わない）。そのあとは、数えないフレームがポーズでなく終わります。そういう走りは
  定理の外です（`lags.ctl`）。

## 前提（Lean では証明していない）

* `Real` のフィールド: `cleanK`、`noStore`、`map`、`after`、`afterV`、それに数えるフレーム `N + 1` の始まりだけの `page`。1 フレームごと、その命令ごと、
  その始まりの状態ごとの条件です。`after` は、スクロールの処理からあと何も彼を動かさず、当たりのルーチンが何も見つけないこと（壁も画面の端もない）です。項目 1-1-a-5-6 の横の半分です。
  `afterV` は、当たり判定から戻るところからあと縦のモデルの 11 バイトが変わらないことです。
* 13 回目: `vert` はもう仮定しません（[本物のフレームの上の縦のモデル](a-5-7-2-OpenAir-ja.md)、`Real.vertOK`）。数えるフレーム `N` のあとでも求めません。新しい:
  `noStore`。広げた: `cleanK`（`guardE`: 守るバイトが 5 つ増える）、`afterV`（11 バイト、前は 4）、`map`（当たりの旗も守る）。
* もう仮定でないもの（12 回目）: `ground`（`Real.ground_all`: 数えるフレーム 1 ではタイトルから、ジャンプのない地面の上の数えるフレームのあとでは
  [出だしの平らな地面](a-5-4-3-4-1-OpenFlat-ja.md) の歩きから、着地のあとでは `Real.jumpV` から）。当たり判定から戻るところまでの歩きはそこで `V` を確かめます。
  そのあとの歩きは `V` を追えないので、新しいフィールド `afterV` を求めます。
* もう仮定でないもの（12 回目）: `jump`（項目 1-1-a-5-7、多くのフレームについての条件）。`Real.vertOK` と、モデルのどのジャンプも調べる探索から定理に
  なりました（`Real.jumpV`）。
* もう仮定でないもの（11 回目）: `flat`（地面から落ちない）。[出だしの平らな地面](a-5-4-3-4-1-OpenFlat-ja.md) の歩きと、新しいフィールド `ground` から定理になりました
  （`Real.flat`）。`map` の読み出しは最初のブロックバッファの中にあると求め、`map` は数えるフレーム `N` のフレームも含みます。
* 前の回から仮定しないこと: `longer`、数えるフレーム 1 から `N` の始まりでの `page`。
* もう仮定でないもの（前の回）: `st` と `spring`。[最初のフレームのブロックバッファ、ジャンプ台、プレイヤーの状態](a-5-4-3-3-3-OpenMap-ja.md) の歩きと、各命令の
  新しいフィールド `map` から定理になりました（`Real.stSpring`）。`spare` は `cleanK` の一部になりました（そのバイトは `cleanK` のガード `FrameKeep.guardF` が
  守ります。パート f と同じです）。
* もう仮定しないこと: 各フレームがモデルの 1 歩であること（`hstep`、`16·v` の移動、モデルの入力、`valid`）、列 `air`。各数えるフレームがポーズでなく終わることは
  定理です（`PipeFrames.Lags.unpaused`）。数えるフレームはポーズでなく終わるフレームで、`dP` フレームの中で見つかります（`lags.resume`）。
* **証明していないこと:** フレーム 368 で入れること（前と同じ）。

**ファイル.** `Theorems/OpenFrames.lean`、`Theorems/OpenLeft.lean`、`Theorems/OpenMap.lean`、`Theorems/OpenFlat.lean`、`Theorems/OpenJump.lean`、`Theorems/PipeFrames.lean`、`Theorems/LagFrames.lean`、`Theorems/StartRun.lean`、`Theorems/Route.lean`、非公開の
`Proof/OpenFrames.lean`、`Proof/OpenFlat.lean`、`Proof/LagPause.lean`、`Proof/Opening.lean`。

**再現.**
```
.lake/build/bin/smbrta open-real-check FM2 300      # Real のフィールドを TAS と自分の入力で、タイトルの確認、数えないフレームの歩き、約 1 分
.lake/build/bin/smbrta open-frames-check FM2 300    # 最初の 32 フレームをモデルの 1 歩として
.lake/build/bin/smbrta open-check 32 9744           # モデルの上限（true）
.lake/build/bin/smbrta open-left-check 31 10240     # モデルの左への上限（true）
```
