[← Back](../README-ja.md) | [English](Reach.md) | [Japanese](Reach-ja.md)

# 進める距離の上限

**命題.** 1-1 の最初（止まっている）から:

1. [最高速の上限](TopSpeed-ja.md) と同じ条件（壁やブロックがあってもよい）で、`n` フレームで
   マリオが右へ進めるのは多くても `reach(n)`。`n ≥ 22` では `2.5·n − 23.25` ピクセル。
2. 開けた場所（何にも触れない）では、多くても `dbound(n)`。`n ≥ 28` では `2.5·n − 38.375` ピクセル。

TAS の加速（32 フレーム）のあと右 + B で走ると、`2.5·n − 41.94` ピクセル進む（`n = 52` で確かめた）。
2 つ目の上限との差は 3.56 ピクセル（最高速で 1.4 フレーム）。ジャンプの長さを入れると、
[出だしの最適性](Opening-ja.md) でこの差はなくなる: TAS より遠くへは行けない。

位置 `P` は 1/256 ピクセル単位。`V = 256·v + subspeed`。`a_max` は加速の量の表の最大値。

```
adv(w)        =  max(16·min(v_top, ⌊(w + a_max)/256⌋), 256)
reach(w, 0)   =  0
reach(w, n+1) =  adv(w) + reach(w + a_max, n)

Frame.adv_le :  max(V, 0) ≤ w  →  P' − P ≤ adv(w)
chain_reach  :  max(V(0), 0) ≤ w  →  P(n) − P(0) ≤ reach(w, n)
reach_closed :  256·v_top ≤ w + a_max·K + a_max  →  reach(w, K + m) = reach(w, K) + 16·v_top·m
reach_11     :  1-1 の最初から（w = 0）: P(n) − P(0) ≤ reach(0, n)、
                reach(0, 22 + m) = 16·v_top·(22 + m) − 5952、
                TAS の入力: P(52) − P(0) = 16·v_top·52 − 10736
```

Lean: `Theorems/Reach.lean`（`chain_reach`、`reach_from`、`reach_closed`。計算を使わずに証明）、
`Theorems/TopSpeed.lean`（`Frame.adv_le`、`Frame.gain`）、非公開の `reach_11`（数は `native_decide`）。
開けた場所の上限は下の節。

## しくみ

1 フレームで `V' ≤ max(V, 0) + a_max`（`Frame.gain`）なので、`k` フレーム後は
`max(V, 0) ≤ w + a_max·k`。そのフレームで動く速さは `⌊(w + a_max)/256⌋` 以下で、`v_top` 以下。
速さによらずに右へ動くのは、壁から押し出されるとき（`ImpedePlayerMove`、+256 = 1 ピクセル）だけで、
それは速さが 0 以下のときだけ。なので 1 フレームの移動は `max(16·v, 256)` 以下。これを足すと `reach`
になる。

## 前提（Lean では証明していない）

* [最高速の上限](TopSpeed-ja.md) の前提: 速さ、subspeed、位置を書き換えるのは 5 つの処理だけで、
  それぞれ確かめたバイトだけで決まること。
* `X_Physics` は加速の量を表から取る（そこで確かめた）ので、`a_max` 以下。

## 開けた場所: 向きのポテンシャル

1 つ目の上限は、TAS の入力より 18.7 ピクセル多い。毎フレーム最大の加速の量 `a_max` を使えると
しているから。ゲームでは、加速の量が 2 倍になるのは、向きと進む向きが違うときだけで、向きを
変えるフレーム（左右同時押しか左）は加速の量が小さい。これをポテンシャルで数える。

```
Φ = |V| + w(向き, 進む向き)
w = 0    向き = 進む向き                c = 2·a₀ − 2·a₁   （a₀, a₁: 加速の量の表の最初の 2 つ）
    c    向き ≠ 進む向き ∈ {1, 2}
    c    進む向き = 0（まだ決まっていない: 1-1 の最初）
    2·c  進む向き = 3（滑りが止まると、向きの左右同時押しが写される）

potCheck  :  Φ' ≤ Φ + g_fast。遅いあいだは Φ' ≤ Φ + g_slow
             （g_slow = 2·a₁、g_fast = a_max。遅い: RunningSpeed = 0 かつ |v| < v_air）
next(p)   =  p + (p < θ なら g_slow、そうでなければ g_fast)      θ = 256·v_air − 255
dist_le   :  Σ_フレーム 16·v ≤ dbound(Φ₀, n)、 dbound(p, n+1) = 16·min(v_top, ⌊next(p)/256⌋) + dbound(next(p), n)
reach_open:  1-1 の最初から、dbound(Φ₀, 28 + m) = 16·v_top·(28 + m) − 9824
```

`v_air` は、`X_Physics` が空中で走りの加速の量を使い始める速さ（コードから読む）。`p < θ` の
あいだ、`Φ ≤ p` の状態はどれも `|v| < v_air` で、`RunningSpeed` はまだ 0（走りのしきい値以上の
速さでしか設定されず、それは `v_air` より大きい）。

`hstep` は 1 フレームの横の部分: `X_Physics`。地面では `GetPlayerAnimSpeed`、左右のボタンからの
向きの設定、`ImposeFriction`。空中では左か右を押しているとき `ImposeFriction`。最後に速さの符号から
進む向き。処理はゲームのコードのまま動かし、順番と 2 つの向きの書き込みは解析済みコードから。
`potCheck` は `hstep` を、全部の状態（`|v| ≤ v_top` の速さ、全部の subspeed、向き、速さに合う進む向き、
`RunningSpeed` が 0 かどうか）と全部の入力（地面、ジャンプの開始、空中。右、左、下、上、B の全部の
組み合わせ。ダッシュのタイマーが 0 かどうか）で動かす。`hstep` は最初に、そのフレームが読まない入力を
消す（`norm`: 空中では左右だけ、ジャンプの開始では下も。地面では B を押しているときのタイマー、ほかの
ボタンを押しているときの上）。残る入力は 38 通りで、約 490 万回、約 11 秒のファイル 3 つ。`check_of` は、
これが範囲の全部を含むことを証明する。

Lean: `Theorems/Potential.lean`（`hstep`、`potCheck`、`step_J`、`dist_le`、`dbound_closed`、
`check_of`。計算を使わずに証明）、非公開の `reach_open`（`potCheck` と数は `native_decide`）。

前提（Lean では証明していない）: `hstep` が 1 フレームで横の状態にすることであること（順番、向きの
書き込み、`norm` が消す入力。fast accel の探索の 340 万ステップで緩めたモデルと比べ、違いはなかった）。開けた場所
（`Player_CollisionBits` は最初と同じで、横の当たり判定がないので、`P` は `16·v` 動く）。
`X_Physics` は `RunningSpeed`、`RunningTimer`、`AreaType` を 0 かどうかでしか読まないこと。
Start と Select を押さないこと。

**ファイル.** `Theorems/Reach.lean`、`Theorems/Potential.lean`、非公開の `Proof/Reach.lean`、
`Proof/ReachOpen*.lean`。

**再現.**
```
.lake/build/bin/smbrta reach-check     # 上限と、いくつかの入力列で進んだ距離をプログラムとして比べる
.lake/build/bin/smbrta pot-check       # potCheck をプログラムとして実行
.lake/build/bin/smbrta hstep-validate lr 31   # hstep と緩めたモデルを比べる
```
