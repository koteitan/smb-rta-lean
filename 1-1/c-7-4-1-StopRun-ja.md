[← Back](README-ja.md) | [English](c-7-4-1-StopRun.md) | [Japanese](c-7-4-1-StopRun-ja.md)

# 左の壁が止めるしくみ: 測ったことと、狭めた `stop_run`、`late`

[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) の項目 1-1-c-7-4 には、`hstep` に従わないフレームについての 3 つのフィールドがあります。このラウンドでは 3 つとも本物の走りで測り、`stop_run` と `late` を、それを使う定理が要るフレームだけに狭めました。

## 命題

`P(n)` はフレーム `n` の終わりの位置（1/256 px）、`rs(n)` はそこでの `RunningSpeed`（0 かそうでないか）、`Follow(n)` はフレーム `n + 1` が `hstep` に従うことです。`wallP = 3968`（15.5 px）、`c_P = 13056` はかたまりの角、`top = 40`。部屋の数は `fall = 34`、`hitF = 37`、`runF = 40` です。

```
wall（フィールド、変えていない）:
  C ≤ n,  n + 1 < C + 37,  ¬Follow(n)   →   P(n) ≤ wallP ∧ P(n + 1) ≤ wallP ∧ rs(n + 1) = 0

late（フィールド、狭めた）:
  C + 37 ≤ n + 1,  n ≤ C + 40,  (∃ h, C ≤ h < n ∧ h + 1 < C + 37 ∧ ¬Follow(h)),  ¬Follow(n)
    →   (P(n) ≤ wallP ∧ P(n + 1) ≤ wallP ∧ rs(n + 1) = 0) ∨ c_P ≤ P(n) + 16·top
  （前は 3 つ目の前提なしで同じもの）

stop_run（フィールド、狭めた）:
  C + 34 ≤ n,  n < C + 40,  rs(n) = 0,  ¬Follow(n)   →   rs(n + 1) = 0
  （前は C ≤ n,  n < C + 40,  ¬Follow(n)  →  rs(n + 1) = 0）
```

`stop_run` を使うのは `rs_of_safe` と `no_wall_back` だけです。どちらも落下の終わりからのフレーム（`C + fall + d`）で使い、どちらもそこでフレームの始めの `RunningSpeed` が 0 だと知っています（`rs_of_safe` の 1 つ前の段）。なのでこのフィールドは、落下のあとで `hstep` に従わないフレームは `RunningSpeed` を立てない、と求めます。

`late` を使うのは `anchor_at` だけです。`anchor_at` は、`hstep` に従わない最初のフレーム `h`（`h + 1 < C + 37`）のあとのフレームをたどります。なので `late` はそのようなフレームのあとだけで求めます。`C + 36` までに壁に当たらない走り（たとえば床の上で角に当たるもの）はフィールドの外です。

## 測ったこと

`room-approach-check FM2 300 1` と `… 300 0`（このラウンド。TAS と自分の走り 2,701 本ずつ。大きいプレイヤーと、大きさがそのままのもの）:

- `wall`: `C + 37` より前で `hstep` に従わないフレームは 8,123 と 8,154。すべて `WallAt` です。フレームの前のいちばん大きい `P` は 3888 と 3904、あとは 3824 で、`wallP = 3968` です。
- `late`: `C + 37` から `C + 41` で `hstep` に従わないフレームは 3,215 と 3,226（前のフィールド）で、成り立たないものはありません。狭めたフィールドに入るのはそのうち 1,479 と 1,490（`C + 36` までに `hstep` から外れるフレームがあるあと）で、成り立たないものはありません。
- `stop_run`: `C + 40` までで `hstep` に従わないフレームは 10,627 と 10,675（前のフィールド）で、成り立たないものはありません。狭めたフィールドに入るのはそのうち 3,132 と 3,153（`C + 34` から、始めの `RunningSpeed` が 0）で、成り立たないものはありません。

## 残ること（証明していない）

- `wall`: `C + 37` より前で `hstep` に従わないフレームは、左の壁に止められている。証明には、フレームが `hstep` に従わないわけ（壁での横の押し戻しや立ち、そのあとの古い保存された速さ、隠された向き）と、それぞれでの位置が要ります。
- `late`（狭めた）: 壁に当たったあと、`C + 37` から `C + 41` で同じこと、または角にいること。
- `stop_run`（狭めた）: `RunningSpeed` を書くのは地面での `GetPlayerAnimSpeed` だけで、保存された速さから書きます。証明には、`RunningSpeed` を追うフレームの歩きと、フレームの始めで保存された速さが走りのしきい値より下であることが要ります。ラウンド 31 でこれをしました: `stop_run` は証明されフィールドではなくなり、残るのはもっと小さいフィールド `ab_run` です（[部屋のフレームの `RunningSpeed`: `stop_run` を証明する](c-7-4-2-RunWalk-ja.md)、項目 1-1-c-7-4-2）。

**ファイル。** `Theorems/RoomJoin.lean`: `RoomFields.stop_run`、`RoomFields.late`、`RoomCore.rs_of_safe`、`RoomCore.no_wall_back`、`RoomCore.anchor_at`、`RoomRun.anchor_atR`。プログラム `room-approach-check`（数え 46 から 51、55 から 58）。
