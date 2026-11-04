[← Back](../README-ja.md) | [English](TasFastAccel.md) | [Japanese](TasFastAccel-ja.md)

# TAS fast accel

**命題.** [fast accel](FastAccel-ja.md) の条件（小さいマリオが陸のステージの最初のように地面で
止まっていて、周りに何もない）で、左右同時押しを許すと（TAS のルール）、マリオは **32 フレーム**で
走りの最高速に達することができ、31 フレーム以下では達することができない。
（ほかの条件は [fast accel](FastAccel-ja.md) と同じ。）

```
upper :  ∃ w ∈ LRA^32,  v(Full(ctx, w)) ≥ v_top          （定理）
lower :  ∀ σ ∈ (LRA × {着地する, しない})^{≤ 30},  v(Relax(ctx, σ)) < v_top   （定理）
31 フレーム: 無理                                         （全探索。Lean ではない）
```

Lean: `tas_fast_accel : (∀ a ∈ landAreas, GainBound …) → FastAccel.BoundsAllAreas sy ctx lrInputsA relaxInputsLR 30 32`
（陸のステージの種類ごと。間引いた探索で、ステージの種類ごとに約 30 秒）。`prove.py --full` では、
`GainBound` を使わない `tas_fast_accel_full`（全探索）も証明します。

**入力.** HappyLee さんの TAS（tasvideos 公開 1715M）の出だしです。

| フレーム | 入力 |
|---|---|
| 1 | 左 + 右（向きが「両方」になり、すぐに向きと進む方向がずれる） |
| 2 | A + 右（ジャンプ） |
| 3–21 | 右 |
| 22–23 | 何も押さない、B + 右（着地） |
| 24 | 左 |
| 25 | A + 右（2 回目の後ろ向きジャンプ） |
| 26–32 | 右 |

左右同時押しなら、加速 2 倍の状態に 1 フレームで入れます（左 → 下 の 2 フレームの代わり）。
これで [fast accel](FastAccel-ja.md) より 2 フレーム縮みます。

**31 が無理な理由.** 緩めたモデルでは 31 ができてしまうので、緩めたモデルだけでは 31 で
止まります。そこで、正確なジャンプのモデル（引き継がれるバイトを全部持つ）で 31 フレームを
探しました。緩めたモデルに写して「まだ間に合う」状態だけを残すので、本物の入力列は
見落としません。どの枝も 21 フレーム目までに行き止まりでした。正確なモデルは、TAS の出だしの
32 フレーム全部で本物のエミュレータと一致します。この入力での縦の値の確認: 変えたステップ
134,209,152 回で違い 0。（この入力では、位置の確認はまだしていません。）

**ファイル.** `Theorems/TasFastAccel.lean`、非公開の `Proof/TasFastAccel.lean`。

**再現.**
```
.lake/build/bin/smbrta relax-layers 50 lr       # 緩めたモデルの最短: 31
.lake/build/bin/smbrta realize 31 lr            # 入力列なし（約 50 分）
lake build Proof.TasFastAccel   # 非公開のプロジェクトで、約 20 分
```
