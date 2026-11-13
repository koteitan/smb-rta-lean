[← Back](README-ja.md) | [English](c-7-1-3-RoomFar.md) | [Japanese](c-7-1-3-RoomFar-ja.md)

# 部屋のフレーム: 位置は 8 px 以上のまま

**主張.** ボーナス部屋の `t₀` までの各フレームの始まりで、位置は 2048（8 px）以上です。これは [部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `far` でした（前の `Clean.far` の下の半分、項目 1-1-c-7-1-1）。今はもっと弱いフィールド `farNear` からの定理です。8 px から右に `16·top + 256`（3.5 px）以内で始まるフレームだけに、8 px 以上で終わることを求めます。もっと右で始まるフレームは、どのみちそこで終わります。1 つのフレームで左に動くのは多くて最高速（2.5 px）で、当たり判定のルーチンが押すのは多くて 1 px だからです。

`P(n)` は部屋のフレーム `n` の終わり（フレーム `n + 1` の始まり）の位置、`hs(n)` は横の状態、`D` はモデルの範囲（`inD`）、`top` は最高速です。`C` は最初の操作、`t₀` はかたまりを越えた最初のフレームです。

```
farNear          :  C ≤ n,  n + 1 < t₀,  2048 ≤ P(n) < 2048 + 16·top + 256  →  2048 ≤ P(n + 1)        (フィールド、1 フレーム)
start_far        :  2048 ≤ 256·x_start                                                               (数、検査済み)
frame_readR_low  :  ReadR(M, n₀),  frame_readR の条件  →  P(M) − 16·top − 256 ≤ P(end)
step_far         :  C ≤ n < t₀,  2048 ≤ P(n),  hs(n) ∈ D
                    →  (Follow(n) ∨ Stop(n + 1))  ∧  P(n) − 16·top − 256 ≤ P(n + 1)  ∧  hs(n + 1) ∈ D
far_inD          :  C + d < t₀  →  2048 ≤ P(C + d)  ∧  hs(C + d) ∈ D
far_of           :  C ≤ n < t₀  →  2048 ≤ P(n)  ∧  P(n) + 2048 < 2²⁴
```

Lean: `Theorems/FrameTime.lean`（`frame_readR_low`）、`Theorems/RoomJoin.lean`（`RoomRun.farNear`、`NumFacts.start_far`、`far_up`、`follow_of_far`、`step_far`、`far_inD`、`far_of`、`inD_of`、`follow_of_clean`、`frames_of`、`move_top_of`）。非公開の `Proof/RoomJoin.lean`（`room_nums`）。

## 方法

**1 つのフレームの動き.** モデルに従うフレームは `P + 16·v'` で終わり（`clean_frameR`）、`v'` は範囲の中なので `|v'| ≤ top` です（`FastTakeoff.step_facts`）。止まった状態にするフレームは `TopSpeed.Frame` です。`16·v₂`（`|v₂| ≤ top`）動き、スクロールの処理のあとで位置はそのままか、左右に 256 動きます（`Collide`）。`frame_readR` は 3 つ目の場合に上の限りだけを残します。`frame_readR_low` はその写しで、下の限りを出します。なので各フレームで左に動くのは多くて `16·top + 256` です。

**帰納法.** 最初の操作で位置は `256·x_start`（始まりのピクセル、`StartAt.P0`）以上で、それは 2048 以上です（`start_far`、部屋の数の事実、`native_decide` で検査）。状態は部屋の始まりで、`D` の中です。フレームが 8 px 以上で、状態が `D` の中で始まるなら、`step_far` がその動きと、終わりの状態が `D` の中であることを出します。`2048 + 16·top + 256` 以上で始まったなら 2048 以上で終わります。そうでなければ `farNear` がそう言います。`clean_frameR` も `frame_readR` もフレームの始まりで `2048 ≤ P` を求めるので、位置と範囲を 1 つの帰納法でいっしょに進めます（`far_inD`）。

範囲は、`ReadR` が求めるプレイヤーのルーチンでの速さの範囲も出します（`speed_of`、[部屋のフレーム: プレイヤーのルーチンでの状態](c-7-1-2-RoomCut-ja.md)）。`inD_of`、`follow_of_clean`、`frames_of`、`move_top_of` は今は、`toCore` が渡す最初の操作の状態（`StartAt`）を取ります。

## 本物のフレームでの確認

`room-ctrl-check FM2 200`（映像と自分の走りの 150,111 フレーム、項目 1-1-c-7-1-2）: `2048 + 16·top + 256` より下で始まるフレームはありません。なので `farNear` の前提はそこで一度も成り立たず、2048 より下で終わるフレームもありません。部屋での位置の最小は 3552 でした（`room-pair-check`、前のラウンド）。

## 仮定（Lean で証明していない）

* `farNear`（1 フレーム、新しい）: `t₀` までのフレームで、8 px と 11.5 px の間で始まるものは 8 px 以上で終わる。左の壁が彼をそこに保ちます。証明には、壁のブロック（地図の 1 のビット）での当たり判定のルーチンが要ります。[ブロックの地図](c-7-12-RoomMap-ja.md) はそれを証明していません。

フィールド `far` はなくなりました。

**ファイル.** `Theorems/FrameTime.lean`、`Theorems/RoomJoin.lean`、非公開の `Proof/RoomJoin.lean`。
