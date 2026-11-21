[← Back](README-ja.md) | [English](f-6-18-2-SubsOnce.md) | [Japanese](f-6-18-2-SubsOnce-ja.md)

# 操作中のフレームは移動の終わりに多くても 1 回来る

**主張.** 操作中のフレームは、移動の終わり（`PlayerSubs`。プレイヤーのルーチンがスクロールの処理を呼ぶところ）に、多くても 1 つの命令でしか来ません。フレームは操作中の待ちのループで始まり（`StartK`）、各命令は `guardK` の `CleanK` を満たします。ルーチン、モード、タスクへの書き込みについての条件はありません。ですから旗に触るフレームでも成り立ちます。このフレームは旗のルーチンを書きます。

ですから `PoleJoin.Run` のフィールド `moved` はなくなりました。パート e は、触るフレームの `P₂(g)` が、そのフレームが移動の終わりに来たときの位置であることを示します（`OnFrames.touchMove`）。来るのは 1 回だけです。ですから `P₂(g)` は、フレームが移動の終わりにいるどの命令での位置とも同じです。これが `moved` です（`Run.moved`）。

`tr(j)` はフレームの `j` 命令あとの機械です。`tr_g` は `keep` のフレーム `g` です（`fm g` から入力 `pad g` で動きます）。`Q = PlayerSubs` です。`idle` は待ちのループです。`CleanK_K` は `guardK` の `CleanK` です。移動のルーチンの端数の書き込みは除きます（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）。

```
subs_once   :  StartK(m)  ∧  (∀ n,  CleanK_K(tr(n)))   →   ∀ k k',  pc(tr(k)) = Q  →  pc(tr(k')) = Q  →  k = k'

touchMove   :  ∃ k,  arrAt ≤ k  ∧  pc(tr_g(k)) = Q  ∧  P₂(g) = posP(tr_g(k))                     （パート e）
Run.moved   :  ∀ j,  pc(tr_g(j)) = Q   →   P₂(g) = posP(tr_g(j))                                   （フィールド moved だった。書き込みまでの j について）
Run.inRange :  P₀ ≤ P₂(g)                                                                       （触るフレームの歩きと Run.moved から）
```

## 歩き

`TaintRun` の抽象機械の 2 つの歩きがフレームを追います。ステップは `FrameKeep` のもの（`kstep`、ガード `guardK`）です。どの道も切りません。

* 1 つ目の歩き（`walkS1`）はフレームの始まりから始めます。`FrameKeep` の 2 つの始まりの状態で、見張るビットはありません。どの道も、`Q` に来るか、フレームの始まりでフレームを終える（`endOK`）か、表の状態に来るまで続けます。`Q` では、その状態から 2 つ目の歩きが成り立つことを求めます。
* 2 つ目の歩き（`walkS2`）はそこから、どの道も、フレームの始まりでフレームを終えるか、表の状態に来るまで続けます。道が `Q` に来たら失敗します。

`run_S1`: 1 つ目の歩きが覆う状態からは、フレームは最初の命令 `k₁` で `Q` に来て、そこで 2 つ目の歩きが成り立ちます。または `Q` に来ません。`run_S2`: 2 つ目の歩きが覆う状態からは、フレームはもう `Q` に来ません。フレームの終わりのあと、機械は待ちのループにとどまります。`Q ≠ idle` です。フレームの始まりも待ちのループです。ですから来るのは 1 回か 0 回です。

`AfterKeep.subs_once`（パート e）は、プレイヤーのルーチンのあとについての同じ事実です。その歩きは、ルーチン、モード、タスクに番地で書くところで道を切ります。ですからフレームのどの命令もそれをしないことを求めます（`noStore`）。触るフレームにはそれがあります。旗のルーチンの書き込みです。書き込みまでに限った形は役に立ちません。`frOf g` が読む到着は `SurfaceRead.read_move` の中で選ばれていて、それが書き込みより前だとはどこにも書かれていません。ここの歩きは書き込みを切りません。`FrameKeep` の歩きも、それを含むフレーム全体をもう追っています。

## ROM での確認

`subsCheck` をプログラムで（`subs-once-check`、終了コード 0）:

| 歩き | 探索のステップ | 表 | 失敗 | `Q` での状態 |
|---|---|---|---|---|
| 1 つ目、フレームの始まりから `Q` まで | 4,382 | 378 | 0 | 2 |
| 2 つ目、`Q` からフレームの終わりまで | 709,326 | 46,413 | 0 | 0（もう一度 `Q` に来るものはない） |

確認はネイティブで 2.7 秒です。`PoleFrame.poleFrameCheck` の一部で、22 回目からは `PoleTileRead.poleCheckU`（23 回目からは `PoleTileHeight.poleCheckH`）の一部なので、非公開の `pole_check_h`（`native_decide`）がこれも確認します。

本物の触り（`touch-move-check`）で: 移動の終わりに 2 回以上来る触るフレームはありません。これは定理を確かめるだけで、証明は使いません。

## 証明されていないこと

新しいものはありません。`subs_once` が求めるのは `StartK` と `CleanK_K` だけです。触るまでのどのフレームもこれを満たします（`FrameKeep.Frames.start`、`Frames.cleanAt`）。`Run.moved` はパート e の `OnFrames.touchMove` を、その条件ごと使います（`frames`、それと触るのが操作から `farN` フレームより後でないこと）。もっと後で触る場合は `SurfaceLate` の場合で、`Run.inRange` を使いません。

**ファイル.** `Theorems/SubsOnce.lean`、`Theorems/PoleJoin.lean` の `Run.moved` と `Run.inRange`、`Theorems/PoleFrame.lean` の `PoleFrame.poleFrameCheck`、非公開の `Proof/PoleTiles.lean`（`pole_check_h`、23 回目から。22 回目は `pole_check_u`。21 回目までは `Proof/PoleFrame.lean` の `pole_frame_check`）。
