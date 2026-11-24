[← Back](README-ja.md) | [English](c-7-8-6-AirMove.md) | [Japanese](c-7-8-6-AirMove-ja.md)

# `t0` のあとの空中の速さの上限: 遅いジャンプのフレーム

ラウンド 36 まで、[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `offSlow` は次を言っていました。かたまりの右端を越えた最初のフレーム `t0` から入るフレーム `E` まで、かたまりの上からの遅いジャンプで始まるフレームは、彼を右へ高々 `16·(A − 1)`（1/16 px 単位）動かす。`A` は空中のしきい値（`AirFastSpeed`、25）で、`16·(A − 1)` は 384、1.5 px です。[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md) はこれを 1 つの場合に使います。`t0 − 1` から `aboveS = 12` フレームあとに入る遅いジャンプは、口に届きません。

ラウンド 37 で `offSlow` はなくなりました。それらのフレームの動きのルーチンの部分は証明し、移動の終わりのあとの速さも証明しました。残るのは、同じフレームについての、移動の終わりのあとの位置だけのフィールド `offCollide` です。

## 証明したこと

`R` はフレームのプレイヤーのルーチン、`Q` は移動の終わり（`PlayerSubs`）、`F` はフレームの終わりです。`v` は速さ、`s` は覚えている速さ（`Player_XSpeedAbsolute`）、`P` は 1/256 px 単位の位置です。`SlowAt(M)` は機械 `M` で `s ≤ A − 1 ∧ |v| ≤ A − 1` であることです。

**1 フレーム、ROM から**（`FrameModel.air_pathA`、`air_pathB`、ファイル `Theorems/AirMove.lean`）: `R` で機械が `AtV` で、空中にいるかそこでジャンプが始まり（`stOf ≠ 0`）、`s < A` かつ `|v| ≤ A − 1` とします。すると

```
air_pathA :  ∃ k,  Q = stepN k R は PlayerSubs  ∧  |v(Q)| ≤ A − 1  ∧  P(Q) ≡ P(R) + 16·v(Q)  (mod 2²⁴)
air_pathB :  ∃ k,  Q = stepN k R は PlayerSubs  ∧  s(Q) ≤ A − 1
```

当たりのビットについての条件はなく、覚えている速さが `|v|` だという条件もありません（`room-off-slow FM2 400` が測った `t0 − 1` からの遅いジャンプのフレームのうち 2,160 で、当たったあとにそうではありません）。チェック（`FrameModel.airOK`、非公開の `Proof/RoomJoin.lean` で `native_decide`、ネイティブで約 5 秒）:

* `physAirOK`: `FrameModel` の場合のうち空中で Left か Right のものそれぞれで、`X_Physics` をその切れ目から歩きます。覚えている速さ `s < A` を 1 つずつわかっているものとして歩きます。戻るところで上限は右へ `A − 1`、左へ `−(A − 1)` で、足す量は表の値です（`capsAir`）。
* `fricAirOK`: 本物の機械の `ImposeFriction` をモデルの機械と並べて歩きます。当たりのビットは下の 2 ビットだけわかっているものとします。`ImposeFriction` はそれを Left/Right との `and` でだけ読みます。
* `fricCapCheck`: これらの上限での `ImposeFriction` は、`|v| ≤ A − 1` のどの速さ、どの端数、どの足す量、どちら側、下の 2 ビットのどの値からも、`|v| ≤ A − 1` で、覚えている速さ `|v|` で終わります。
* `17 ≤ A ≤ 128`。

Left も Right もないとき、速さと覚えている速さは `R` から移す処理まで変わりません（`FrameModel.caseOK` の歩き）。移す処理からは、歩き `tail_spec` が動きを与え、歩き `storedTailOK` が覚えている速さを保ちます。

**部屋の本物のフレームの上で**（`RoomJoin.lean`）:

```
air_frame :  C ≤ n < E  ∧  (st(fm n) ≠ 0 ∨ R でジャンプ)  ∧  SlowAt(fm n)  ∧  CollideP(Q, F)  →
               (16·(A − 1) ≤ P(fm n)  →  P(F) ≤ P(fm n) + 16·(A − 1))
             ∧ (P(fm n) + 16·(A − 1) < 2²⁴  →  P(fm n) − 16·(A − 1) − 256 ≤ P(F))
             ∧ (n + 1 < E  →  SlowAt(F))
slow_start :  T + 1 < t0、T + 1 で遅い飛び上がり、そのあと t0 までのフレームは空中  →  ∀ i,  T + i ≤ t0 − 1  →  SlowAt(fm(T + i))
slow_run   :  D + 1 = t0,  D + aboveS = E,  SlowAt(fm D),  D からのどのフレームも遅いジャンプ  →
               ∀ i < aboveS,  P(D + i + 1) ≤ P(D + i) + 16·(A − 1)
```

`CollideP(Q, F)`（`FrameModel.Collide` の位置の部分）: `P(F) = P(Q) ∨ P(F) = P(Q) − 256 ∨ (P(F) = P(Q) + 256 ∧ v(Q) ≤ 0)`。

**移動の終わりのあとの速さ**（`RoomSpeedKeep`、`InRoom` の新しい事実 `speedAfter`、ラウンド 37）:

```
InRoom.speedAfter :  C ≤ n  ∧  n + 1 < E  ∧  pc(k) = PlayerSubs  →  v(F) = v(trace k)  ∨  v(F) = 0
```

部屋のフレーム全体の歩き（`RoomMap` の抽象機械。`RoomAbsKeep` の覚えている速さの歩きと同じ）が `PlayerSubs` でビットを立てます。ビットのある状態で、その一歩が速さを書くかもしれないものは、ビットを落としてしるしをつけます。しるしのついた状態は、プレイヤーのルーチンの外でフレームを終わるか、速さが 0 とわかっている状態で終わらなければなりません（`finV`）。当たりのルーチン（`ImpedePlayerMove`）と画面の端の押さえは 0 しか書きません。チェック `checkV`（非公開の `Proof/RoomSpeedKeep.lean` で `native_decide`）はネイティブで約 9 秒です。フレームの終わりの状態は 56、そのうちしるしのついたものは 20 で、断られるものはありません。`Route.Run.roomSpeed` がこの事実を本物の機械で与えます。`roomAbs` が `absAfter` を与えるのと同じです。

* `air_frame`: フレームは移動の終わりに 1 度だけ来る（`InRoom.absAfter`）ので、`air_pathA` と `air_pathB` の終わりは同じ命令です。そのあとの一歩は覚えている速さを書かず、速さはそのままか 0 です（`speedAfter`）。だから `|v| ≤ A − 1` が保たれます。`CollideP` は彼を高々 1 px 動かします。前へ 1 px は `v ≤ 0` からだけなので、高々 256 ≤ `16·(A − 1)` です。
* `slow_start`: `T` での立ちは `SlowAt` で終わります。飛び上がりの覚えている速さは立ちの終わりのもので、`A` より小さいです（チェック `slowAbs`: 遅い飛び上がりの落ちる力（`slowF`）を持つ、かたまりの上からの飛び上がりは、`A` より小さい覚えている速さを読んだ）。`t0` より前のフレームの終わりでは、覚えている速さは `|v|` か、速さが 0 です（`absOr0`、ラウンド 33）。だから `|v| ≤ s ≤ A − 1` です。飛び上がりと `t0 − 1` までの空中のフレームは `SlowAt` を保ちます（`air_frame`、移動の終わりのあとは `clean`）。
* `slow_run`: フレーム `t0` は `clean` のフレームで、そのあとのフレームはフィールド `offCollide` のフレームです。位置は 8 px 以上で、範囲の終わりからは遠いままです（`NumFacts.slow_low`、`slow_hi`）。だから動き `16·v` は回り込みません。

`off_arc`（遅い場合）は `offSlow` のかわりに `slow_run` を使います。その結論と `off_gap_of` の結論（`t0 < E ∧ t0 + aboveF ≤ E + 1`）は変わりません。`off_arc` と `off_gap_of` は、`absOr0` のために最初の操作での状態（`StartAt`）を受け取るようになりました。

## フィールド

なくなったもの:

```
offSlow :  ∀ n,  t0 ≤ n + 1  ∧  n < E  ∧  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  P(n + 1) ≤ P(n) + 16·(A − 1)
```

加えたもの（`RoomRun` のフィールド、1 フレーム）:

```
offCollide :  ∀ n,  t0 ≤ n  ∧  n < E  ∧  st(vE n) = 1  ∧  vfd(vE n) ∈ F_slow  →  ∀ j ≥ arr n,  pc(j) = PlayerSubs  →  CollideP(trace j, F)
```

`offCollide` はどの点でも `offSlow` より弱いわけではありません。1 フレーム少なく求め（フレーム `t0` は `clean` のフレーム）、動きのルーチンにも速さにも何も求めません。しかし、移動の終わりのあとの位置だけについて、どちらへも高々 1 px と求めます。だから、フレームの残りが彼を 1 px より多く左へ動かさないことも求めます。これは `offSlow` が求めなかったことです。`t0` より前では、フィールド `clean` がどのフレームにもこれとそれ以上を求めます（`ReadW.collide`、`CleanW.after`）。

新しい ROM のチェック（`Checks`）: `airM`（`FrameModel.airOK`）と `slowAbs`（`OffDrop.slowAbs`）。歩き `RoomSpeedKeep.checkV`（`Route.Run.inRoom` が受け取る）。新しい数（`NumFacts`）: `slow_low : 2288·aboveS + 2048 ≤ goal`、`slow_hi : goal + 2032·aboveS + 4096 < 2²⁴`。`InRoom` の新しい事実: `speedAfter`。

## 測ったこと

`room-air-move FM2 400`（`PLACE/git` から）: 映像の部屋のフレームと、部屋の最初の操作からの自分の入力の 225 回の走り（`room-off-slow` と同じ: かたまりの上へ、`t0` まで右へ、その半分はかたまりの上からジャンプ、そのあと行ったり来たり）。

| | |
|---|---|
| 走り | 226（映像と自分の 225） |
| 空中かジャンプで、`s < A` かつ `\|v\| ≤ A − 1` でプレイヤーのルーチンに来るフレーム | 46,800 |
| そのうち `\|v(Q)\| > A − 1`、`s(Q) > A − 1`、または `16·v(Q)` でない動き（`air_pathA`、`air_pathB` に反する） | 0 |
| `t0 + 1` から遅いジャンプで始まるフレーム（`offCollide` のフレーム） | 20,881 |
| そのうち移動の終わりのあとで位置が変わるもの | 2,200 |
| そのうち移動の終わりが 2 つ以上あるもの | 0 |
| そのうち移動の終わりで `CollideP` でないもの、またはフレームの終わりの速さが移動の終わりのものでも 0 でもないもの | 0 |
| 遅い飛び上がりから着地までのジャンプのフレーム | 34,689 |
| そのうちプレイヤーのルーチンで `SlowAt` でないもの | 0 |
| `t0` からのフレームで、始まりで `s = \|v\|` でも `v = 0` でもないもの | 43,319 のうち 0 |

映像のかたまりの上からのジャンプは速いので、`offCollide` のフレームはありません。

## 残っていること（証明していない）

* `offCollide`: `t0` のあとのフレームでの、移動の終わりのあとの位置。`ImpedePlayerMove` は彼を 1 px 動かします。スクロール処理の押さえ（`KeepOnscr`）は位置を画面の端にします。バイトを追うだけの歩きでは足りません。測ったフレームのうち 2,200 で、移動の終わりのあとに位置が変わります。証明には、部屋のフレームを移動の終わりから歩き、これらの書き込みを通して位置を追うものが要ります（パート e には地上のフレームのための両方のルーチンのまとめ `ImpedePosition.routine_return`、`ScreenClamp.clamp_return` があります）。
* `offTop`（[かたまりの上から: 床までのフレーム](c-7-8-2-OffDrop-ja.md)）: 変えていません。

**ファイル。** `Theorems/AirMove.lean`（新しい: チェックと `air_c4`、`air_pathA`、`air_pathB`）。`Theorems/RoomSpeedKeep.lean`（新しい: 歩き `checkV`、`after_QV`、`speed_frame`）。`Theorems/Route.lean`（`Run.roomSpeed`、`Run.inRoom`）。`Theorems/OffDrop.lean`（`slowAbs`、`slowAbs_spec`）。`Theorems/RoomJoin.lean`（`CollideP`、`SlowAt`、`offCollide`、`InRoom.speedAfter`、`air_frame`、`slow_start`、`slow_run`、`off_arc`、チェック `airM`、`slowAbs`、数 `slow_low`、`slow_hi`）。`Main.lean`: `room-air-move`、`room-speed-keep`、非公開の `Proof/RoomSpeedKeep.lean` を書くもの。非公開の `Proof/RoomJoin.lean` は新しいチェックと数を持ち、`Proof/Route.lean` は歩きのチェックを `Run.inRoom` に渡します。

**再現。**
```
.lake/build/bin/smbrta room-air-move FM2 400     # チェック airOK と slowAbs、そしてこのページの事実を本物のフレームで（約 2 分）
.lake/build/bin/smbrta room-speed-keep           # 歩き RoomSpeedKeep.checkV（約 15 秒）
```
