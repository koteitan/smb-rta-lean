[← Back](README-ja.md) | [English](c-7-13-4-StandHit.md) | [Japanese](c-7-13-4-StandHit-ja.md)

# 最初の立ちの前の位置を証明する

このラウンドまで、[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `stand_P` は、落下（`C + 34` より前）の最初の立ちの 1 つ前のフレームで、位置が `standP = 3712`（14.5 px）かそれより左だ、と言っていました。これを使う定理は 2 つでした。

- `stand_first` は、最初の立ちが `hstep` に従わないことを示します。`hstep` に従うフレームで `stand_P` を使っていました（背理法です）。
- `wall_turn` は、最初の立ちのフレームが `hstep` に従わない最初のフレームのとき、それを使っていました。

このラウンドでは両方の使い方を証明し、`stand_P` はなくなりました。

- `stand_first` は、新しい定理 `RoomRun.fall_left`（最初の立ちより前では、かたまりの角より 1 ピクセルより多く左にいる）と、移動の終わりからの 2 つの歩きから位置を得ます。x が 13 からなら、どちらの足も固いマスにありません（`WallF`）。x が 12 までなら前と同じ議論です（`WallQ`）。
- `wall_turn` は、新しく証明した事実 `RoomCore.stand_hit`（`RoomRun.stand_hit_of`）を使います。移動の終わりで x が 12 まで（`WallX`）であることと、摩擦の下の上限（`FrameModel.frame_readQL`）からです。

フィールド `stand_fast` は狭めました。そのフレームが `hstep` に従う立ち（`stand_first`）か、前に立ちがあるあとの立ち（`stand_gap`）だけで求めます。`stand_hit` の証明はこれを使いません。

## 命題

`P(n)` はフレーム `n` の終わりの位置（1/256 px）、`st(n)` はそこでのプレイヤーの状態、`V(n) = 256·v + f` はそこでの速さと端数です。`Q` はフレーム `n + 1` の移動の終わり（`PlayerSubs` での機械）で、`x(Q)`、`y(Q)`、`page(Q)`、`high(Q)`、`st(Q)`、`vy(Q)` はそこでのバイトです。`Follow(n)` はフレーム `n + 1` が `hstep` に従うことです。`Φ₀ = 152` は最初に操作できるときの状態のポテンシャル、`c_P = 13056`（51 px）はかたまりの角、`cornerX = 51` です。`ysFall` は、最初の落下の最後のフレームより前の、移動の終わりの 33 個の高さの並びです（`fallLayer` の状態からの `vstepR`）。

```
WallX(Q)  :=  high(Q) = 1 ∧ page(Q) = 0 ∧ 13 ≤ x(Q) < 17 ∧ 32 ≤ y(Q) < groundY ∧ st(Q) ∈ {1, 2} ∧ vy(Q) ≥ 0
WallF(Q)  :=  high(Q) = 1 ∧ page(Q) = 0 ∧ 13 ≤ x(Q) < cornerX ∧ y(Q) ∈ ysFall ∧ st(Q) = 2 ∧ vy(Q) ≥ 0

RoomWall.wall_frameX、RoomWall.wall_frameF（歩き、証明）:
  移動の終わり Q で WallX(Q)（または WallF(Q)）を満たし、プレイヤーのルーチンで終わる部屋のフレームは、st ≠ 0 で終わる

InRoom.wall（新しい 3 つの部分。Route.Run.roomWall が証明）:
  空中のフレームの移動の終わり Q は、そのフレームのただ 1 つの PlayerSubs  （RoomVert.after_Q）
  WallX(Q)  →  st(n + 1) ≠ 0
  WallF(Q)  →  st(n + 1) ≠ 0

FrameModel.frame_readQL（証明。ROM の確認 frictionLowCheck を使う）:
  TopSpeed.Frame であるフレームは  min(V₁, 0) − amax ≤ V₂
  （V₁ = 256·v₁ + f₁ はアニメーションのルーチンのあと、V₂ = 256·v₂ + f₂ は Q でのもの、amax = 456）

RoomRun.fall_left（証明）:
  C ≤ k < C + 34,  (∀ j, C < j < k → st(j) ≠ 0)   →   P(k) + 256 < c_P

RoomCore.stand_hit（新しい事実。RoomRun.stand_hit_of が証明）:
  C ≤ n,  n + 1 < C + 34,  n < C + 15,  (∀ j, C ≤ j < n → Follow(j)),  ¬Follow(n),
  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0     →   P(n) ≤ standP

stand_P（フィールド）: なくなった
  （前は C ≤ n,  n + 1 < C + 34,  (∀ j, C < j ≤ n → st(j) ≠ 0),  st(n + 1) = 0  →  P(n) ≤ standP）

stand_fast（フィールド、狭めた）:
  C ≤ n,  n + 1 < C + 34,  (Follow(n) ∨ ∃ j, C < j ≤ n ∧ st(j) = 0),  st(n + 1) = 0   →   standV ≤ −V(n)
  （前は 3 つ目の前提なしで同じもの）
```

## 証明

**`fall_left`。** 最初の立ちより前のフレームでの `RoomCore.corner_late` です。`corner_late` は `RoomCore` の定理で、`RoomCore` を作るのに `stand_first` を使うので、そこでは使えません。`k` より前に `hstep` から外れるフレームがなければ、フレームは空中のフレームで（`air_in_of` と立ちより前の状態）、落下のポテンシャルが位置を押さえます（`fall_runR`）: `P(k) ≤ P1 + airDist(Φ₀, 34)`。`hstep` から外れるフレームがあれば、最後の壁のフレームと、そこからの止まったときのポテンシャルです（`anchor_atR`、`anchor_PR`）: `P(k) ≤ wallP + dbound(stopPhi, 34 − 15)`。確認 `WallFacts.fallQ` が、どちらも `c_P` より 256 より多く下だと言います。

**`stand_first`。** `Follow(n)` のもとで、フレームの終わりは `c_P − 256` より左（`fall_left`）で、`Q` はそれより多くて 1 px 右です（`q_le_end`）。ページ 0 で `x(Q) < cornerX` です。`Q` での縦のバイトは最初の落下のものです（`fall_mem`）。状態 2、`vy ≥ 0`、縦のページ 1、`ysFall` の高さ。`x(Q) ≥ 13` なら `WallF(Q)` で、フレームは `st ≠ 0` で終わり、`st(n + 1) = 0` に合いません。`x(Q) ≤ 12` なら前と同じく `WallQ(Q)` で（終わりの速さは `hstep` のもので、`stand_fast` で負）、フレームは `st ≠ 0`、床の上、速さ 0 のどれかで終わります。どれも成り立ちません。

**`stand_hit`。**

1. フレーム `n + 1` は `hstep` に従わないので、モデルのフレーム（`CleanW`）ではありません。`TopSpeed.Frame` であり、`frame_readQL` が移動の終わり `Q` を摩擦の下の上限とともに与えます。空中のフレームが `PlayerSubs` に来るのは 1 回なので、`Q` は `InRoom.wall` の移動の終わりです。
2. フレーム `n + 1` より前のフレームはすべて `hstep` に従うので、`|V(n)| ≤ Φ(n) ≤ iterN(Φ₀, n − C) = 152 + 304·(n − C) ≤ 4408` です（`J_runR`）。
3. フィールド `wall` から `P(n) ≤ wallP = 3968`。なので `V₂ ≤ max(V₁, 0) + amax ≤ 4408 + 456` で、`P(Q) = P(n) + 16·v₂ ≤ 3968 + 304 = 4272 < 4352` です。ページ 0 で `x(Q) < 17` です（確認 `standX` の 1 つ目の部分）。
4. `Q` での縦のバイトは最初の落下のものです。状態 2、`vy ≥ 0`、縦のページ 1、`32 ≤ y < groundY`（`wallYCheck` と新しい確認 `wallYCheckX`）。`13 ≤ x(Q)` なら `WallX(Q)` で、フレームは `st ≠ 0` で終わります。`st(n + 1) = 0` に合いません。なので `x(Q) ≤ 12` で、`P(Q) ≤ 3327` です。
5. `frame_readQL` から `V₂ ≥ −4408 − 456` で、`16·P(n) = 16·P(Q) − 256·v₂ ≤ 16·3327 + 4408 + 456 + 255`。なので `P(n) ≤ 3646 ≤ standP` です（`standX` の 2 つ目の部分。`n − C < 15` のそれぞれで）。

`stand_hit` の証明はフィールド `wall` と `clean` を使います。`stand_fast`、`stand_wall` は使いません。これで `wall_turn` は、前と同じく `left_far` と `stand_far` で、そのような立ちが `C + 16` より前でないことを得ます。

## ROM での確認（新しいもの）

- `RoomWall.familyX` と `cellsX`（`RoomWall.Checks` のフィールド。非公開の `room_wall`）: `Q` での切り口から衝突のルーチンの戻りまでの歩き `check1X` を、`x` が 13 から 16、高さが 32 から床の高さの 1 つ上まで、状態 1 と 2 で（1,152 本）。床の行（高さ 176 から 180 と 192 から 196）では歩きは通りません。そこでは足が床の中にあるからです。なので高さは床の高さの下で止めます。
- `RoomWall.FChecks`（非公開の `room_wall_f`）: 状態 2 での `check1X` を、`x` が 13 から 50、`ysFall` の 33 個の高さで（1,254 本）。そのマスも。`x = 51 = cornerX` では歩きもマスも通りません。そこでは右の横の判定がかたまりの列にあるからです。
- `FrameModel.frictionLowCheck`（非公開の `Proof/RoomFricLow.lean`、`room_fric_low`。ネイティブで約 60 秒）: `TopSpeed.frictionCheck` と同じ機械（−40 から 40 のすべての速さ、端数、足す値、上限、向き、衝突のビット）で、`ImposeFriction` は `V' ≥ min(V, 0) − 足す値` で終わる。
- `WallFacts.standX`、`yX`、`fallQ`（非公開の `room_stand_w`）。

## 測ったこと

`room-approach-check FM2 300 1` と `… 300 0`（このラウンド、最後のプログラムで。TAS と自分の走り 2,701 本ずつ、部屋のフレーム 764,248 と 769,213。大きいプレイヤーと、大きさがそのままのもの）:

- `C + 34` より前の立ち: 44 回と 50 回。すべて最初の立ちで（前に立ちがあるあとの立ちはない）、どれも `hstep` に従いません。なので狭めた `stand_fast` のフィールドに入る測ったフレームはありません（前のフィールドには 44 と 50 のすべてが入っていました）。それぞれの立ちの 1 つ前のフレームで `−V ≥ 3952` と `4256`（`standV = 3584`）、`P ≤ 3632`（前の `standP = 3712`）。
- `C + 15` までの最初の立ちで、`hstep` から外れる最初のフレームであるもの（`stand_hit` の場合）: 0 と 0。測った立ちはフレーム 18 から 30 です。
- `C + 34` より前の空中のフレームで、移動の終わりで `WallX` を満たし、状態 0 で終わるもの: 0（あればバグ）。
- 1-1-c-7-4 のフィールド（測っただけ）: `wall` は `C + 37` より前の `hstep` から外れるフレームが 8,123 と 8,154 で、すべて `WallAt`（前のいちばん大きい `P` は 3888 と 3904、あとは 3824。`wallP = 3968`）。`late` は 3,215 と 3,226 フレームで、成り立たないものはない。`stop_run` は 10,627 と 10,675 フレームで、成り立たないものはない。

## 残ること

- `stand_fast`（狭めた）: そのフレームが `hstep` に従う立ちの前、または前に立ちがあるあとの立ちの前で `−V ≥ standV`。測った走りには、このフィールドに入るフレームはありません（上のとおり）。証明には、あとの立ちでの速さが要ります。
- `stand_wall` と、1-1-c-7-4 のフィールド `wall`、`late`、`stop_run`（上で測った。証明はしていない。`late` と `stop_run` は狭めた: [左の壁が止めるしくみ: 測ったことと、狭めた `stop_run`、`late`](c-7-4-1-StopRun-ja.md)）。

**ファイル。** `Theorems/RoomWall.lean`: `endX`、`check1X`、`xsX`、`ysX`、`familyX`、`familyF`、`xsF`、`endX_spec`、`check1X_eq`、`mem_xsX`、`mem_ysX`、`mem_xsF`、`Checks.familyX`、`Checks.cellsX`、`FChecks`、`wall_atX`、`wall_atF`、`wall_frameX`、`wall_frameF`。`Theorems/RoomJoin.lean`: `FrameModel.frictionLowCheck`、`lowOK`、`fric_readL`、`frame_pathL`、`frame_readQL`。`WallX`、`WallF`、`ysFall`、`mem_ysFall`。`InRoom.wall`。`wallYCheckX`、`wallYCheckX_spec`。`WallFacts.standX`、`yX`、`fallQ`。`Checks.fricLow`。`RoomCore.stand_hit`。`RoomFields.stand_fast`（狭めた）、`stand_P`（なくなった）。`RoomRun.start_fallR`、`psiP_startR`、`fall_runR`、`anchor_PR`、`left_farR`、`wall_firstR`、`anchor_atR`、`fall_left`、`J_runR`、`hitQ_arith`、`hitP_arith`、`pos_lt_of`、`stand_hit_of`。`stand_first`、`stand_gap`、`wall_turn`、`toCore`。`Theorems/Route.lean`: `Run.roomWall`、`Run.inRoom`。非公開の `Proof/RoomFricLow.lean`（`room_fric_low`）、`Proof/RoomWall.lean`（`room_wall`、`room_wall_f`）、`Proof/RoomJoin.lean`（`room_stand_w`、`room_checks`）。
