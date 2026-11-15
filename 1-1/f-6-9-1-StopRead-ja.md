[← Back](README-ja.md) | [English](f-6-9-1-StopRead.md) | [Japanese](f-6-9-1-StopRead-ja.md)

# 速いジャンプの前の覚えている速さを機械から読む

**主張.** `keep` のフレームで、触る前の数えるフレーム `j`（`1 ≤ j < g`）をとります。`frames` の条件があり、触るのは操作できてから `farN` フレーム以内とします。すると:

* 速さ 0 で始まるフレームは、覚えている速さ `|v₂|` で終わるか、前のフレームの覚えている速さと進む向きを保ちます（`Run.stop_step`）。
* 地面で始まり、プレイヤーのルーチンがジャンプを読まないフレームは、覚えている速さ `|v₂|` で終わります（`Run.ground_step`）。

なので `PoleJoin.ApproachCases` のフィールド `stopped` はなくなりました。フィールド `onGround` は、1 つの状態の条件 2 つのフィールド `ground` に置きかえました。

`abs(j)`、`md(j)`、`st(j)` は `seq j`（数えるフレーム `j` の終わりの機械）の覚えている速さ、進む向き、プレイヤーの状態です。`v(j)` は始まりの速さ（`seq(j − 1)` の速さ）です。`v₂(j)` は移動の終わり（`PlayerSubs`）の速さです。`jump(j)` はフレームのプレイヤーのルーチンが読むジャンプです。地面にいて、A を押し、前のフレームで A を押していないときです。`tr(k)` はフレームの `k` 命令目の機械、`n₀` は最初にプレイヤーのルーチンに来る命令、`Q = PlayerSubs` です。`c` はプレイヤーのルーチンでの場合（`FrameModel.caseOf`）です。`st(c)` はモデルの状態（地面からジャンプすると 1）、`lr(c)` は移動のルーチンが読む左右です。

```
frameE_move  :  ReadE,  Same   →   ∃ k ≥ n₀,  pc(tr(k)) = Q  ∧  v₂ = v(tr(k))  ∧  f₂ = f(tr(k))  ∧  P₂ = P(tr(k))
stored_c4N   :  AtFrame(R)   →   ∃ k,  R_k は移動のルーチンの入口  ∧  (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(R_k) = |v(R_k)|)
                                     ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(R_k) = v(R)  ∧  abs(R_k) = abs(R)  ∧  md(R_k) = md(R))
stored_subs  :  AtFrame(tr(n₀)),  n₀ のあと Q に 1 回   →   ∀ k ≥ n₀,  pc(tr(k)) = Q   →
                   (st(c) = 0  ∨  lr(c) ≠ 0   →   abs(tr(k)) = |v(tr(k))|)
                   ∧  (st(c) ≠ 0  ∧  lr(c) = 0   →   v(tr(k)) = v(tr(n₀))  ∧  abs(tr(k)) = abs(tr(n₀))  ∧  (v(tr(n₀)) = 0  →  md(tr(k)) = md(tr(n₀))))
stop_step    :  1 ≤ j < g,  v(j) = 0   →   abs(j) = |v₂(j)|  ∨  (abs(j) = abs(j − 1)  ∧  md(j) = md(j − 1))
ground_step  :  1 ≤ j < g,  st(j − 1) = 0,  jump(j) = false   →   abs(j) = |v₂(j)|
ground       :  fast,  L + 1 < T'   →   st(T' − 2) = 0  ∧  jump(T' − 1) = false                  （ApproachCases のフィールド）
```

走りのトラック（`PoleJoin.trackOf`）は、いまは機械から読みます。`abs`、`md`、`st`、`jump` は上のとおりです。フィールド `direct` が与えるのは縦の状態 `u` だけです。前はフィールド `direct` がトラック全体を与え、その覚えている速さと進む向きは機械と結びついていませんでした。

## 証明の流れ

`SurfaceRead.frame_readE` は、移動の終わりの命令 `k` も与えるようになりました。`v₂`、`f₂`、`P₂` はそこのバイトです。前の結論はそのままです。なのでフレームの `v₂` は、`Q` に来たときの速さです（`frameE_move`）。

`stored_c4N` は、`FrameModel.stored_c4` から「プレイヤーのルーチンで覚えている速さは `|v|`」という仮定を除いたものです。同じ歩きを使います。地面と、空中で左右を押すときは、フレームは `ImposeFriction` を動かし、覚えている速さに `|v|` を書きます（`fric_abs`、`TopSpeed.frictionCheck` から）。空中で左右を押さないときは、移動のルーチンまでの歩きが、速さ、覚えている速さ、進む向きを保ちます。`stored_c4` がその仮定を使うのは、この場合だけでした。

`stored_subs` は移動のルーチンから `Q` まで 2 つの歩きで進みます。`FrameModel.storedOK` の歩きは速さと覚えている速さを保ちます。移動のルーチンの歩き（`FrameModel.tail_spec`）は、速さから進む向きを決め、速さが 0 なら保ちます。フレームはプレイヤーのルーチンのあと `Q` に 1 回だけ来る（`GuardE.subs_onceE`）ので、2 つの歩きは同じ命令で終わります。

`stored_end` は数えるフレームでこれらをつなぎます。プレイヤーのルーチンまでは、`CtrlKeep` の歩きと、その前のポーズで終わるフレームが、速さ、覚えている速さ、進む向き、プレイヤーの状態を保ちます（`CtrlKeep.keepA`、`OnFrames.lagKeep`）。`Q` からフレームの終わりまでは、`GuardE.keepHE` が覚えている速さと進む向きを保ちます。`stop_step` はその 2 つの場合です。`ground_step`: 状態 0 でジャンプを読まなければ、プレイヤーのルーチンでの場合は地面です（`stOf_ground`）。

`ground` がジャンプも聞くわけ。`st(T' − 2) = 0` だけでは足りません。地面で始まりジャンプを読むフレームは、場合としては空中です（`st(c) = 1`）。左右を押さなければ覚えている速さを保つので、その `|v₂|` は覚えている速さではありません。本物の走りでは、`T'` のジャンプは A を押し、前のフレームで押していないことを読みます。なので `T' − 1` では A を押しておらず、`T' − 1` はジャンプを読みません。

## 本物のフレームで

`stop-read-check`（exit 0、27 秒）。触る前の数えるフレームのすべてで、速さ 0 で始まるときに `stop_step` を、地面で始まりジャンプを読まないときに `ground_step` を調べます。着地 `L` のあとの踏み切り `T` で `L + 1 < T` のもののすべてで、フィールド `ground` を調べます。`v₂` は `Q` での速さです。どのフレームもプレイヤーのルーチンのあと `Q` にちょうど 1 回来ました。

| 走り | 回数 | フレーム | 速さ 0 から（保つ、`|v₂|` でない） | 地面、ジャンプなし | 着地のあとの踏み切り `L + 1 < T`（`ground` あり） | 悪いもの |
|---|---|---|---|---|---|---|
| ムービー、操作から触るまで | 1 | 239 | 5 (1) | 48 | 3 (3) | 0 |
| 操作からランダムな入力 | 100 | 29,055 | 9,766 (404) | 14,549 | 348 (348) | 0 |
| ムービーのフレームからランダムな入力 | 100 | 15,777 | 3,385 (97) | 7,526 | 201 (201) | 0 |
| ホップ: A を押して離す、右ありとなし | 33 | 5,750 | 2,636 (0) | 1,203 | 157 (157) | 0 |

本物の直接つかみは速いジャンプからは来ません（`fast_short`）。なので本物の走りでは、フィールド `ground` を前提つきで使うことはありません。表は、着地のあとの本物の踏み切りのすべてで、それが言うことを調べたものです。

## 証明していないこと

* フィールド `ground`: それぞれ 1 つの状態の条件 2 つ（数えるフレーム `T' − 2` の終わりの機械と、フレーム `T' − 1` のプレイヤーのルーチンの機械）。モデルの踏み切り `T'` が機械の読むジャンプと結びつき、A をプレイヤーのルーチンからフレームの終わりまで追う歩きがあれば、`T'` のジャンプから出ます。どちらもしていません。
* フィールド `reads`: モデルの速いジャンプは、`seq(T' − 1)` で空中のしきい値以上の覚えている速さを読む。
* `Run.stop_step` と `Run.ground_step` は、`Run.reads` と同じく、`frames` の条件（`state`、`collide`、`spareV`）、`keep` の条件（`cleanE`、`noStore`）、触るのは操作できてから `farN` フレーム以内であることを使います。

ROM の新しいチェックはありません。歩きは `SurfaceFrames.numbersCheck` のもの（`FrameModel.modelOK`、`storedOK`、`CtrlKeep.ctrlCheck`、`AfterKeep.hCheck`）です。非公開の `pole_keep`（`keepCheck`、`keepCases` での移動のルーチン）はなくなりました。

**ファイル.** `Theorems/StopRead.lean`。`Theorems/SurfaceRead.lean` の `frame_readE`、`frameE_move`。`Theorems/PoleJoin.lean` の `trackOf`、`ApproachCases.ground`、`Run.stop_step`、`Run.ground_step`。

**再現.**
```
.lake/build/bin/smbrta stop-read-check FM2 100     # 上の表（約 30 秒）
```
