[← Back](README-ja.md) | [English](c-7-1-1-FrameTime.md) | [Japanese](c-7-1-1-FrameTime-ja.md)

# 部屋のフレーム: `before`、`longer`、`far` の半分を歩きから

**主張.** [部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `clean` は、部屋の `t₀` までの各フレームが `FrameModel.Clean` か、止まった状態にして `FrameModel.ReadFrame` であると言います（[本物のフレームと横のモデル](../0-0/0-3-2-FrameModel-ja.md)）。その 3 つの部分はもう仮定ではありません。
* `before`: フレームの始まりからプレイヤーのルーチンまで、横のバイトに何も書かない。[RoomVert](c-7-5-1-RoomVert-ja.md) のプレイヤーのルーチンへの歩きが、今はそれらも保ちます（`hbytes_at_R`）。
* `longer`: プレイヤーのルーチンに来てから 728 命令の間にフレームが終わらない。今はフレームの時間から出ます。`SiteOK`（すでに仮定、`chg.roomSites`）は、アイドルループ以外のすべての命令をフレームの終わりの 6000 ドット前に置きます。移動の歩きは、そのときそれぞれのステップがフレームを保つことを示します。
* `far` の上の半分: `P + 2048 < 2²⁴`。`t₀` より前はゴールより左にいて（`first`）、ゴールは口より左で（`slow_mouth`、`air_pos`）、ページ 0 にあります。

`far` の下の半分は、`RoomRun` の 1 つの機械のフィールドとして残っていました。`t₀` までの各フレームの始まりで `2048 ≤ P` です。今はもっと弱いフィールド `farNear` からの定理です（[部屋のフレーム: 位置は 8 px 以上のまま](c-7-1-3-RoomFar-ja.md)、項目 1-1-c-7-1-3）。`CleanR` と `ReadR` のプレイヤーのルーチンでの状態も、どちらかを決める値のほかは今は証明しています（[部屋のフレーム: プレイヤーのルーチンでの状態](c-7-1-2-RoomCut-ja.md)、項目 1-1-c-7-1-2）。

`R` はプレイヤーのルーチン、`tr(j)` は `M` からフレームの `j` 命令目の機械、`idle` は部屋のアイドルループ（自分への `JMP`）、`dot` はフレームの中のドットです。

```
InTime(M, n₀)  :=  idleAt(idle)  ∧  frame(tr(n₀)) = frame(M)  ∧  ∀ n,  pc(tr(n)) ≠ idle → dot(tr(n)) ≤ dotsPerFrame − 64

hbytes_at_R  :  RoomCond(M),  各命令が SiteOK,  pc(tr(j)) = R  →  H(tr(j)) = H(M)        (H: 横の 8 バイト)
clean_frameR :  modelOK,  CleanR(M, n₀),  H(tr(n₀)) = H(M),  InTime(M, n₀),  2048 ≤ P(M),  P(M) + 2048 < 2²⁴
                →  hs(end) = hstep(hs(M), in),   P(end) = P(M) + 16·v(end)
frame_readR  :  modelOK,  frictionCheck,  ReadR(M, n₀),  H(tr(n₀)) = H(M),  InTime(M, n₀),  同じ範囲
                →  フレームは TopSpeed.Frame
far_of       :  C ≤ n < t₀  →  2048 ≤ P(fm(n))  ∧  P(fm(n)) + 2048 < 2²⁴
t0_le_E      :  t₀ ≤ E
inTime_of    :  C ≤ n < t₀,  pc(tr(arr(n))) = R  →  InTime(fm(n), arr(n))
```

`CleanR` と `ReadR` は、`Clean` と `ReadFrame` から `before`、`longer`、`far` を除いたものです。

Lean: `Theorems/FrameTime.lean`（`InTime`、`CleanR`、`ReadR`、`clean_frameR`、`fric_readI`、`frame_pathI`、`frame_readR`）、`Theorems/RoomJoin.lean`（`RoomRun.clean`、`InRoom.le`、`InRoom.time`、`InRoom.arrive`、`InRoom.before`、`goal_mouth`、`before_of`、`goal_small`、`t0_le_E`、`far_of`、`inTime_of`、`follow_of_clean`、`move_top_of`）、`Theorems/RoomVert.lean`（`vKeepA`、`finR`、`finA`、`before_R`、`hbytes_at_R`、`air_frame`、`air_arc`）、`Theorems/VertAir.lean`（`vert_air`）、`Theorems/Route.lean`（`late_of`、`Run.roomTime`、`Run.roomArrive`、`Run.roomBefore`、`Run.roomVert`、`Run.inRoom`）。非公開の `Proof/RoomVert.lean`（`room_vert_idle`）。

## 方法

**フレームの時間.** 移動の歩きのステップは、フレームの終わりより 64 ドット以上前に走るならフレームを保ちます。それほど長くかかる命令はありません（`FrameModel.InFrame`）。`move_model`、`frame_path`、`fric_read`、`tail_spec`、`vert_air` の歩きは、それぞれのステップでこれを示します（`InFrameN`）。すると `FrameModel.trace_inFrame`（パート e）から次が出ます。フレームが終わる前に `R` に来て、アイドルループ以外のすべての命令が終わりより 64 ドット以上前に走るなら、歩きのステップはフレームのステップです。`FrameModel` は `frame_path` と `fric_read` から `InFrameN` を落としています。`frame_pathI` と `fric_readI` はそれを残した写しです。証明は同じです。

**部屋での時間.** `SiteOK` は、アイドルループ以外の命令が高々 `late = dotsPerFrame − 6000` のドットで走ると言います（`late_of`）。アイドルループは自分への `JMP` です（`room_vert_idle`、ROM の確認）。

**到着と `before`.** [RoomVert](c-7-5-1-RoomVert-ja.md) のプレイヤーのルーチンへの歩きは、今はフレームの終わりの状態が `R` にないことを求めます（`finR`）。ですから `tr(j)` が `R` にあれば、フレームはそこで終わっていません（`before_R`）。歩きは `R` まで横の 8 バイトも保ちます（今は `vKeepA` に入っています）。フレームが `R` に来るのは 1 回なので、`tr(j)` が `R` にあるどの `j` でも、それらは `M` のものです（`hbytes_at_R`）。歩きの確認は真です（6.4 秒）。`room-vert-check` は、本物の 24,111 フレーム（ムービーと 200 回）で、`R` より前に `vKeepA` のバイトに書くステップを見ませんでした。

**部屋のフレームで.** `InRoom.time`、`InRoom.arrive`、`InRoom.before` は、入るフレーム `E` より前の各フレームで成り立ちます（`Route.Run.roomTime`、`Route.Run.roomArrive`、`Route.Run.roomBefore`: 部屋のフレーム `n + 1` は `base` のフレーム `b₁ + ix(n + 1 − C) − 1` で始まり、`a₂` より前です: `Route.Run.roomIdx`）。`clean` は `t₀` までのフレームについて述べ、`t₀ ≤ E` です（`t0_le_E`）。入るフレームで口にいて、`t₀` より前はゴールより左で、ゴールは口より左だからです。`InRoom.le` は `C ≤ E` です（`Route.Run.room_le`）。`RoomVert.air_frame` も引数 `hl` の代わりに同じ時間を使います。

## 本物のフレームで確かめたこと

`room-pair-check FM2 50`: 部屋のフレームの終わりの位置の最小は、ムービーで 5920、最初の操作からの自分の入力の 200 回（30,000 フレーム）で 3552 でした。フィールド `far` が求めるのは 2048 です。`longer` は前に本物のフレームで確かめました。今は定理です。

## 仮定（Lean で証明していないこと）

* `far` はもうフィールドではありません。8 px から右に 3.5 px 以内で始まるフレームだけの条件 `farNear` から証明します（[部屋のフレーム: 位置は 8 px 以上のまま](c-7-1-3-RoomFar-ja.md)）。
* 部屋のフレームの各命令の `SiteOK`（`chg.roomSites`、項目 1-1-d-2-4-2）。前と同じです。
* `CleanR` と `ReadR` の残り: プレイヤーのルーチンで、フレームがモデルに従うかを決める値（覚えている速さ、塞ぎ、当たりのビット）、スクロールの処理からあとのフレームのすること（`after`、`collide`）。そこでのほかの状態と、そこに来ることは今は証明しています。部屋のフレームの定義から出ます。部屋のフレームは止まっていない状態で終わります（フィールド `unpaused` はなくなりました: [部屋で一時停止する走り](c-7-1-4-RoomLag-ja.md)。[部屋のフレーム: プレイヤーのルーチンでの状態](c-7-1-2-RoomCut-ja.md)）。

**ファイル.** `Theorems/FrameTime.lean` と上のファイル。

**再現.**
```
.lake/build/bin/smbrta room-vert-check FM2 [N]    # finR つきのプレイヤーのルーチンへの歩き
.lake/build/bin/smbrta room-pair-check FM2 [N]    # アイドルループと、本物のフレームでの位置の最小
```
