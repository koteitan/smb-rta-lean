[← Back](README-ja.md) | [English](d-2-4-1-ScreenStart.md) | [Japanese](d-2-4-1-ScreenStart-ja.md)

# 部屋で最初に操作できる状態の条件 `Room`

**主張.** [部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md) は、部屋で最初に操作できる状態についての条件 `Room` を仮定していました。`Room` は 82 バイトのビットと、フレームの終わり方（アイドルループ、ドット、フラグ）です。これは本物の機械で証明しました。[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md) の時間の段から出ます。条件はその切り替えの条件、出口で時間が切れていないこと（`chg.time₁`）、`b₁` が入ったあと最初の操作であること（`chg.ctlFirst₁`）です。フィールド `chg.roomRest`（操作のときの 5 バイト）はなくなりました。

## 文

`r` は `Room` の参照の機械（横の土管に入る前のフレームの機械）、`K` は `Room` が知るビットのリストです。`InRowsT(m)` は、`m` が時間の段のどれかの状態に覆われることです（[b-3-2](b-3-2-PipeChangeEnd-ja.md)）。

```
roomCheck     :  K のマスクが正しい ∧ 2 つの環境の ROM が同じ ∧
                 時間の段のどの状態 S も操作のバイトを知り、
                 操作できるなら S ≤ startR(r, K, low) となる low がある

room_of_rows    :  roomCheck ∧ InRowsT(m) ∧ ctl(m)  →  Room(m)
PipeRun.inRowsT :  EndStatement ∧ PipeRun ∧ time ∧ ctlFirst  →  InRowsT(seq b)       （b-3-2）
Route.Changes.roomAt :  RoomChecks ∧ Changes  →  Room(seq b₁)
```

`startR(r, K, low)` は `Room` の始まりの抽象状態で、`K` のビットを `r` の値で知り、ドットは 0（`low`）か 1〜9 です。`S ≤ startR` なら、`S` が覆う機械は `startR` も覆います（`sim_le`）。すると `Room` が出ます（`ScreenPage.room_of_sim`）。

`Changes.run₂` は `Changes.roomAt` を `ScreenPage.entry_long` に渡します。`RoomChecks` のフィールドは `pipe`（`pipe_end`）と `start`（`screen_start`）です。

## 5 バイトはどこから来るか

前は、切り替えの段では、操作のときに `K` の 5 バイトが参照と同じには知られていませんでした。いまは、どれも時間の段から出ます。

| バイト | 時間の段が参照と同じに知るわけ |
|---|---|
| `WorldNumber` | 出口の条件に入れました。その条件は、土管のフレームの歩きが入るときの条件から出します |
| `PlayerStatus`（ビット 1〜7） | 同じです。入るときの条件はもとからこのビットを知っていました |
| `AreaMusicBuffer_Alt`（ビット 2 を除く全部） | 同じです |
| `SecondaryHardMode` | 面の準備がこれを 0 にし、`PrimaryHardMode` と `WorldNumber` によってビット 0 を立てるか決めます。どちらも出口の条件に入れました |
| `AreaMusicQueue` | 時間の段では音のポーズのフラグが 0 なので、音のルーチンが動き、キューを参照と同じに取ります。フラグが 0 でないとキューに別の値が残ります。その場合は `rowsB` の段にあり、時間の段にはありません |

`LevelNumber` は要りません。`WorldNumber` と `PrimaryHardMode` が知られていれば、面の準備はこれを読みません。

## 確認

`screen_start`（非公開、`native_decide`）。プログラムで約 4 秒です。時間の段は 44 段、状態は 8118 個、操作できる状態は 2 個です。どちらも `K` 全体について `startR` の下にあります。

## 本物の走り

プログラム `room-start-check FM2 [N]` です。入る状態は、参照の入る状態、TAS の入る状態、13 個の本物の入る状態です。「出口の条件」は `quiet₁`、「時間」は出口の `TimeOK`（`time₁`）です。

| 入力 | 走り | 操作のときに `Room` でない | 出口の条件を満たす | そのうち時間でない | そのうち `Room` でない |
|---|---|---|---|---|---|
| TAS（フレーム 653 で操作） | 1 | 0 | 1 | 0 | 0 |
| 入力なし | 15 | 0 | 15 | 0 | 0 |
| ランダム、Start なし | 300 | 0 | 300 | 0 | 0 |
| ランダム、土管のフレームだけ Start あり | 300 | 41 | 167 | 0 | 0 |

`Room` でない 41 回は、どれも `AreaMusicQueue` だけが違い、どれも出口の条件（`chg.quiet₁`）を満たしません。なのでこれらの走りは定理の外です。

## 前提（Lean では証明していない）

* **`chg.time₁`、`chg.ctlFirst₁`.** 出口で時間が切れていない。`b₁` は最初の操作。[b-3-2](b-3-2-PipeChangeEnd-ja.md) を見てください。
* **切り替えの条件**（入るときの条件 `Run.entry₁`: `chg.entryRest₁`、`upStart₁`、`upClean₁` と `title`。`places₁`、`quiet₁`、`noStart₁`）。入るときの条件は、 `WorldNumber`、`PrimaryHardMode`、`AreaMusicBuffer_Alt` のビットも求めるようになりました。ファイアマリオ（`PlayerStatus` が 2）は `chg.entry₁` を満たしません。

**ファイル.** `Theorems/ScreenStart.lean`、`Theorems/PipeChangeEnd.lean`（`timeRows`、`PipeRun.inRowsT`）、`Theorems/Route.lean`（`RoomChecks`、`Changes.roomAt`）、非公開の `Proof/ScreenStart.lean`。
