[← Back](README-ja.md) | [English](d-2-4-1-ScreenStart.md) | [Japanese](d-2-4-1-ScreenStart-ja.md)

# 部屋で最初に操作できる状態の条件 `Room`

**主張.** [部屋の画面のページと、横の土管の長いタイマー](d-2-4-ScreenPage-ja.md) は、部屋で最初に操作できる状態についての条件 `Room` を仮定していました（`chg.roomStart`）。`Room` は 73 バイトのビットと、フレームの終わり方（アイドルループ、ドット、フラグ）です。これは本物の機械で証明しました。ただし 5 バイトは残ります（`chg.roomRest`）。[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md) の段から出ます。条件はその切り替えの条件、操作の前に `left₁` が 0 にならないこと（`chg.first₁`）、5 バイトです。

## 文

`r` は `Room` の参照の機械（横の土管に入る前のフレームの機械）、`K` は `Room` が知るビットのリストです。`R₅` は次の 5 バイトです。

```
R₅ = { SecondaryHardMode, PlayerStatus, WorldNumber, AreaMusicBuffer_Alt, AreaMusicQueue }
K' = K から R₅ のバイトを除いたもの

RestAt(m)     :  ∀ (b, k) ∈ K,  b ∈ R₅  →  m[b] & k = r[b] & k

roomCheck     :  K' のマスクが正しい ∧ 2 つの環境の ROM が同じ ∧
                 切り替えの 2 つの場合の段のどの状態 S も操作のバイトを知り、
                 操作できるなら S ≤ startR(r, K', low) となる low がある

room_of_rows  :  roomCheck ∧ InRows(m) ∧ ctl(m) ∧ RestAt(m)  →  Room(m)
Route.Changes.roomAt :  RoomChecks ∧ Changes  →  Room(seq b₁)
```

`startR(r, K', low)` は `Room` の始まりの抽象状態で、`K'` のビットを `r` の値で知り、ドットは 0（`low`）か 1〜9 です。`S ≤ startR` なら、`S` が覆う機械は `startR` も覆います（`sim_le`）。すると `Room` の `K'` の部分が出ます（`ScreenPage.room_of_sim`）。残りの `R₅` は `RestAt` から足します。

`Changes.roomAt` は、[部屋で最初に操作できる状態](c-7-2-RoomStart-ja.md) の `PipeRun.inRows` を使います。`Changes.run₂` は `chg.roomStart` のかわりに `Changes.roomAt` を `ScreenPage.entry_long` に渡します。`RoomChecks` には `pipe`（`pipe_end`）と `start`（`screen_start`）が加わりました。

## 確認

`screen_start`（非公開、`native_decide`）。プログラムで 3.8 秒です。段の操作できる状態は 4 個です。どれも `K'` について `startR` の下にあり、`R₅` の 5 バイトだけが参照と同じには知られていません（下の表）。

## 5 バイトが残るわけ

段の操作できる 4 個の状態で、`R₅` のバイトはこうなっています（プログラムで見ました）。

| バイト | 段が知るビット | 知るビットの値 |
|---|---|---|
| `SecondaryHardMode` | ビット 0 を除く全部 | 参照と同じ |
| `PlayerStatus` | なし | |
| `WorldNumber` | なし | |
| `AreaMusicBuffer_Alt` | なし | |
| `AreaMusicQueue` | 全部 | 2 個は参照と同じ、2 個は違う |

* `PlayerStatus`、`WorldNumber`、`AreaMusicBuffer_Alt` は、土管の出口の条件（`PipeChangeEnd.exitNames`）にないので、段の始まりで知られていません。段のフレームも、これらに知られた値を書きません。
* `SecondaryHardMode` のビット 0 は面の準備が立てることがあります（`inc`）。`PrimaryHardMode`、`WorldNumber`、`LevelNumber` によります。段は `WorldNumber` を知りません。
* `AreaMusicQueue` は、音のポーズのフラグが 0 の場合の段では参照と同じ 0、0 でない場合の段では 0 でない値です。0 でない場合は音のルーチンが動かないので、キューの値が残ります。

出口の条件に `PlayerStatus`、`WorldNumber`、`AreaMusicBuffer_Alt`、`PrimaryHardMode`、`LevelNumber` を足せば、残りは `AreaMusicQueue` だけになるはずです（試していません）。その条件は入るときの条件から出るので、入るときの条件もこれらを知る必要があります。`PipeChangeEnd` は変えていません。

## 本物の走り

プログラム `room-start-check FM2 [N]` です。

| 入力 | 走り | 操作のときに `Room` でない | そのうち出口の条件を満たす | `RestAt` でない |
|---|---|---|---|---|
| TAS | 1 | 0 | 0 | 0 |
| 入力なし | 15 | 0 | 0 | 0 |
| ランダム、Start なし | 300 | 0 | 0 | 0 |
| ランダム、土管のフレームだけ Start あり | 300 | 41 | 0 | 41 |

`Room` でない 41 回は、どれも `AreaMusicQueue` だけが違い、どれも出口の条件（`chg.quiet₁`）を満たしません。なのでこれらの走りは定理の外です。前の仮定 `chg.roomStart` も、この 41 回では成り立っていませんでした。

## 前提（Lean では証明していない）

* **`chg.roomRest`.** 部屋で最初に操作できる状態の `R₅` の 5 バイトのビットが参照と同じ。ファイアマリオ（`PlayerStatus` が 2）では成り立ちません。
* **`chg.first₁`**、**切り替えの条件.** [部屋で最初に操作できる状態](c-7-2-RoomStart-ja.md) と同じです。

**ファイル.** `Theorems/ScreenStart.lean`、`Theorems/Route.lean`（`roomRest`、`RoomChecks`、`Changes.roomAt`）、非公開の `Proof/ScreenStart.lean`。
