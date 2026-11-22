[← Back](README-ja.md) | [English](c-7-4-3-AbsKeep.md) | [Japanese](c-7-4-3-AbsKeep-ja.md)

# 止まったあとの保存された速さ: `ab_run` を狭める

[ボーナス部屋をつなぐ](c-5-RoomJoin-ja.md) のフィールド `ab_run`（項目 1-1-c-7-4。ラウンド 31 で作った: [部屋のフレームの `RunningSpeed`](c-7-4-2-RunWalk-ja.md)）は、`C + 37` から `C + 40` の地面のフレームが読む古い保存された速さが走りのしきい値より下である、というものです。このラウンドでは、保存された速さを、それを書くフレームから読むフレームまで追います。1 つ前のフレームが止まり、そのプレイヤーのルーチンに、保存された速さが `|v|` で押している向きが隠されていない状態で来るとき、読まれる保存された速さは、その前の状態からの `hstep` の速さの大きさです。すると `safeFrom` がそれをしきい値より下にします。`ab_run` はほかのフレームだけで求めます。

## 命題

`fm(n)` はフレーム `n + 1` が始まる機械、`fe(n)` はフレーム `n` の終わりの機械、`T_k` はフレーム `n + 1` の（`fm(n)` からの）`k` 命令あとの機械、`end(n)` はその終わりの機械です。`xa` は保存された速さ `Player_XSpeedAbsolute` です。`PlayerSubs` は移動の終わりです。`R = RunSpeedMin` は走りのしきい値（1 フレームに 1.75 px）です。

数の側では: `hs(n)`、`v(n)`、`rs(n)`、`st(n)` はフレーム `n` の終わりの横の状態、速さ、`RunningSpeed`、状態です。`inp(n)` はフレーム `n` の入力、`ab(n)` はフレーム `n + 1` がプレイヤーのルーチンで読む保存された速さ、`Follow(n)` はフレーム `n + 1` が `hstep` に従うことです。`AtCtrl(n)`: フレーム `n + 1` はプレイヤーのルーチンに `FrameModel.AtCtrl` の状態で来る（そこで `xa = |v|` で、押している向きが当たりのビットで隠されていない）。`CleanW(n)`、`ReadW(n)`: フレーム `n + 1` についてのフィールド `clean` の 2 つの場合（モデルに従う、止まる）。部屋の数は `fall = 34`、`hitF = 37`、`runF = 40` です。

```
abs_frame（証明、RoomAbsKeep）:
  フレームは部屋の条件で始まり、各命令は SiteOK を満たす:
  PlayerSubs に来るのは多くて 1 回で、プレイヤーのルーチンの中で終わるなら、
  T_k.pc = PlayerSubs,  T_k.frame = fm(n).frame   →   xa(end) = xa(T_k)

InRoom.absAfter（本物の機械で証明: Route.Run.roomAbs）:  C ≤ n, n + 1 < E で同じこと
InRoom.absBefore（証明: Route.Run.roomAbsBefore）:  C ≤ n < E,  T_k.pc = PlayerCtrlRoutine   →   xa(T_k) = xa(fm(n))
InRoom.absKeep（証明: Route.Run.roomKeepA）:  C ≤ n < E   →   xa(fm(n)) = xa(fe(n))

RoomRun.ab_fresh（証明）:
  C ≤ n,  n + 1 < t0,  ReadW(n),  AtCtrl(n)   →   ab(n + 1) = |hstep(hs(n), inp(n + 1)).v|

RoomCore.stop_run（証明: RoomRun.stop_run_of。前提が 1 つ増えた）:
  C + 34 ≤ n < C + 40,  rs(n) = 0,  |v(n)| < R,
  (n = C + 34  ∨  ∀ i ∈ inputs, |hstep(hs(n − 1), i).v| < R),  ¬Follow(n)   →   rs(n + 1) = 0

ab_run（フィールド。いまは RoomRun のもの。狭めた）:
  C + 37 ≤ n + 1,  n < C + 40,  rs(n) = 0,  ¬Follow(n),  st(n) = 0,  inp(n + 1).jump = false,  ab(n) ≠ |v(n)|,
  (CleanW(n − 1)  ∨  ¬AtCtrl(n − 1))   →   ab(n) < R
```

前の `ab_run`（ラウンド 31）は、最後の前提のほかは同じでした。なので新しいフィールドが求めるフレームは少なくなります: フレーム `n` が止まり（`ReadW(n − 1)`）、プレイヤーのルーチンに `AtCtrl` の状態で来るときは求めません。

`ab_fresh` の筋道。フレーム `n + 1` はプレイヤーのルーチンに `k₀` で `AtCtrl` の状態で来て、`ReadW` はそこでの当たりのビットが `TopSpeed.collBits` のどれかだと言います。なので状態は `FrameModel.AtFrame` です。すると `FrameModel.stored_path` は `PlayerSubs` での `xa = |v|` の命令を、`FrameModel.move_model` は `PlayerSubs` での横の状態が `hstep(hs(n), inp(n + 1))` の命令をくれます。フレームが `PlayerSubs` に来るのは 1 回なので（`InRoom.absAfter`）、2 つは同じ命令です。そこからフレームの終わりまで `xa` を書く手はありません（`InRoom.absAfter`）。フレーム `n + 2` の前の一時停止で終わるフレームも `xa` を保ち（`InRoom.absKeep`）、フレーム `n + 2` もプレイヤーのルーチンまで保ちます（`InRoom.absBefore`）。そこで `read_ab` が `ab(n + 1)` を読みます。

いまの `stop_run_of` の筋道。ラウンド 31 と同じですが、`C + 37` から、地面でジャンプがなく、保存された速さが古いとき: フレーム `n` についてのフィールド `clean` は `CleanW(n − 1)` か `ReadW(n − 1)` です。`ReadW(n − 1)` で `AtCtrl(n − 1)` なら、`ab_fresh` で `ab(n) = |hstep(hs(n − 1), inp(n)).v|` です。機械から読んだ入力は `inputs` のどれかなので（`readIn_mem`）、`stop_run` の新しい前提がそれを `R` より下にします。ほかの場合はフィールド `ab_run` です。

`RoomCore.stop_run` の新しい前提は `safeFrom` から来ます: `rs_of_safe3` は、`1 ≤ d` の各フレーム `C + 34 + d` で、フレーム `C + 34 + d − 1` の終わりの状態からのモデルのどの入力も速さを `R` より下に保つことを運びます（そこでの `safeFrom` から `safe_step`）。`n = C + 34` では求めません。新しい数の事実 `NumFacts.hit_two`（`fall + 2 ≤ hitF`）は、`C + 37` からは `n` が `C + 34` でないと言います。同じ前提は、狭めた `ab_early`（[`ab_early` は落下の終わりからだけ](c-7-6-1-EarlyFall-ja.md)）の `n = C + 35` でも使います。

## 歩きのしくみ

歩きは `RoomVert` の、部屋の 1 フレーム全体の歩き（`RoomMap` の抽象機械）に 1 ビットをつけたもので、`RoomVert` のスクロールの処理からの歩き（`after_QP`）と同じ形です:

1. `PlayerSubs` で、どの状態にもビットをつけます（`phX`）。
2. ビットつきの状態で、その手が `xa` を書くかもしれないもの（`mayWriteX`: その 1 バイトについての `StepWrites.keepOK`）はビットを落とし、`[1]` の印をつけます。コインを消す手はかたまりのバッファに書きます。`apartX` は `xa` がそこにないと言います。
3. フレームの終わりで、`[1]` の印の状態はルーチンのバイトを知っていて、それが参照のものでないこと（`RoomVert.finB`）: フレームはプレイヤーのルーチンを出ています。
4. なので `PlayerSubs` に来て、プレイヤーのルーチンの中で終わるフレームは、`PlayerSubs` の `xa` で終わります（`after_QX`）。

通るわけ（決めるのはチェックで、これはコードの読みにすぎません）: `xa` を書くのは `ImposeFriction` の終わりだけで、プレイヤーの状態のルーチンが移動の終わりより前に呼びます。

保存された速さは `RoomVert.vKeepA` にも入れました。プレイヤーのルーチンへの歩きが保つバイト（`RoomVert.before_R`）で、一時停止で終わるフレームが保つバイト（`RoomVert.paused_R`）です。なので前からの歩きのチェックは 1 バイト多く求めます。

チェックは `room_abs_keep : RoomAbsKeep.checkX sy screenNames ctx = true` と `room_abs_apart` で、新しい非公開の `Proof/RoomAbsKeep.lean` で `native_decide` によります。それと `room_checks.stored`（`FrameModel.storedOK`）です。プログラム（`room-abs-check`）では探索に失敗はありません。フレームの終わりの状態は 40 で、`[1]` の印のものはなく、`finB` が退けるものもありません。探索を表示して約 7 s です。

## 測ったこと

`room-approach-check FM2 300 1`（大きい。作った状態）と `… 300 0`（小さい）。TAS と自分の走り 2,701 本ずつ:

| | 大きい | 小さい |
|---|---|---|
| ラウンド 31 のフィールド `ab_run` のフレーム | 457 | 479 |
| そのうち、1 つ前のフレームがプレイヤーのルーチンに `AtCtrl` の状態で来て、移動のあとで押し戻される（`CleanW` でない）もの: `ab_fresh` で証明 | 457 | 479 |
| そのうち、保存された速さが `|hstep(hs(n − 1), inp(n)).v|` でないもの（`ab_fresh` のまちがい） | 0 | 0 |
| 狭めたフィールド `ab_run` のフレーム | 0 | 0 |
| `RoomCore.stop_run` のフレーム（`C + 34` から） | 3,132 | 3,153 |
| そのうち終わりで `rs ≠ 0`（`stop_run_of` のまちがい） | 0 | 0 |
| そのうち `C + 37` から（新しい前提を求める） | 2,504 | 2,521 |
| そのうち、前の状態からのモデルの入力で `R` に届くものがある（前提が成り立たない） | 0 | 0 |

なので、前のフィールドの測ったどのフレームでも、1 つ前のフレームは止まり、プレイヤーのルーチンに保存された速さ `|v|`、隠されていない向きで来ていました。狭めたフィールドが求めるのは、1 つ前のフレームがモデルに従うか、古い保存された速さか隠された向きでプレイヤーのルーチンに来るフレームだけで、測ったものはありません。

## 残ること（証明していない）

- `ab_run` のうち、フレーム `n` がモデルに従う（`CleanW`）か、古い保存された速さか隠された向きでプレイヤーのルーチンに来るフレーム。モデルに従うフレームでも `stored_path` は移動の終わりで `xa = |v|` をくれるはずですが、そこでの当たりのビットが `TopSpeed.collBits` のどれかであることが要り、それをくれるのは `ReadW` だけです。古いか隠されたフレーム `n` では、`ImposeFriction` のあとの速さは `hstep` のものではありません。`FrameModel.frame_readQL` はそれを `|V(n − 1)|` と摩擦の足し算 1 回で抑えますが、それを `safeFrom` は抑えません。
- `wall`、`late`（変えていない）。

**ファイル。** 新しい `Theorems/RoomAbsKeep.lean`（`mayWriteX`、`phX`、`apartX`、`checkX`、`searchX`、`keepX_step`、`after_QX`、`abs_frame`）。`Theorems/RoomVert.lean`: `vKeepA` が保存された速さを持つ。`Theorems/RoomJoin.lean`: `InRoom.absBefore`、`InRoom.absKeep`、`InRoom.absAfter`（新しい事実）、`Checks.stored`、`NumFacts.hit_two`、`RoomFields.ab_run` はなくした、`RoomRun.ab_run`（狭めたフィールド）、`RoomCore.stop_run`（前提が 1 つ増えた）、`rs_of_safe3`、`safe_v`、`RoomRun.ab_fresh`。`stop_run_of`、`rs_of_safe`、`no_wall_back`、`toCore`。`Theorems/Route.lean`: `Run.roomAbsBefore`、`Run.roomAbs`。`Run.inRoom` は 2 つのチェックを取る。非公開の `Proof/RoomAbsKeep.lean`: `room_abs_keep`、`room_abs_apart`。プログラム: `room-abs-check`、`room-approach-check`（数え 73 から 81）。
