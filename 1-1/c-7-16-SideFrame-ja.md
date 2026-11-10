[← Back](README-ja.md) | [English](c-7-16-SideFrame.md) | [Japanese](c-7-16-SideFrame-ja.md)

# 横の土管に入るフレーム: 1 フレーム全部

**主張.** 抽象機械が、待ちのループからフレームの終わりまで、1 フレームを追います。フレームのある命令がルーチンのバイトを横の土管のものにするなら、その書き込みより前の移動の終わり（`PlayerSubs`）で、位置は口の左端より左ではありません。ですから `RoomRun` の仮定が 2 つなくなります。`pass`（書き込みは横の判定の 1 回の通過の終わり）と `pos`（`P(E)` は横の判定がページを読むときの位置）です。

抽象機械には 1 つの状態についての条件がいります。縦の土管と同じ条件です（[1 フレーム全部](a-5-2-PipeWrites-ja.md)、[移動の終わりの位置](a-5-9-MoveEnd-ja.md)）。そのうち 3 つは、[部屋のブロックの地図](c-7-12-RoomMap-ja.md) の抽象機械から、走りの本物の機械の上で証明します。フレーム `E` が操作できる状態で始まること（`StartE`）、書き込みまでの各命令が `Clean` であること（`CleanE`）、読みでは横の土管のタイルが土管の列にしかないこと（`TilesE`）です。縦の土管と同じく、2 つは仮定のままです。`edgeE` と `movedE` です。

名前は [横の土管に入るフレームを本物のフレームで](c-7-3-SideEntryRule-ja.md) と、縦の土管の 2 つのページと同じです。`tr(j)` は、`fm(E − 1)` から入力 `pad(E)` で始まるフレーム `E` の、`j` 命令あとの機械です。`x₀` は右側が口に入る最初の `x`、`P₀ = 256·x₀` は口の左端です。`posP(m) = 256·(256·page(m) + x(m)) + 小数部(m)` です。

```
FrameStart, Clean      1 フレーム全部 のとおり（縦の土管のガード。どちらもルーチンの番号によらない）
w_edge, h              移動の終わりの位置 のとおり: スクロールのルーチンが位置を書く命令、頭がブロックに当たったときのルーチン
HypF(m)        :=  (pc(m) = PlayerSubs  →  px(m) < x₀)  ∧  (AtRead(m) → TilesOK(m))  ∧  pc(m) ∉ {w_edge, h}

no_write_frame       :  frameCheck,  s(j + 1) = step(s(j)) (j ≤ n),  frame(s(j)) ≤ frame(s(0)) (j ≤ n),  FrameStart(s(0)),
                        (∀ j ≤ n,  Clean(s(j)) ∧ HypF(s(j)))                                 →  rt(s(n + 1)) ≠ e_s
entry_right_of_left  :  sideFrameCheck,  Enters(m, i),  FrameStart(m),
                        (∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j)) ∧ (AtRead(tr(j)) → TilesOK(tr(j))) ∧ pc(tr(j)) ≠ w_edge ∧ pc(tr(j)) ≠ h)
                        →  ∃ n j,  WriteStep(n) ∧ j ≤ n ∧ pc(tr(j)) = PlayerSubs ∧ x₀ ≤ px(tr(j))
mouth_of_frame       :  同じ条件,  (∀ n j,  WriteStep(n) → j ≤ n → pc(tr(j)) = PlayerSubs → P = posP(tr(j)))   →  P₀ ≤ P
StartE     :=  FrameStart(fm(E − 1))
CleanE     :=  ∀ n,  WriteStep(n) → ∀ j ≤ n,  Clean(tr(j))
TilesE     :=  ∀ n j,  WriteStep(n) → j ≤ n → AtRead(tr(j)) → TilesOK(tr(j))
InRoom     :=  TilesE ∧ StartE ∧ CleanE
RoomRun.mouth_of     :  Checks,  RoomRun,  InRoom                                                    →  P₀ ≤ P(E)
Route.Run.inRoom     :  部屋の確認,  Run                                                             →  InRoom
side_frame_check（非公開） :  sideFrameCheck(sy, m₀) = true（native_decide）
```

`sideFrameCheck` は `PlayerSubs ≠ 0` と、抽象機械の確認です。`Route.Run.inRoom` は [部屋のブロックの地図](c-7-12-RoomMap-ja.md) にあります。

ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。

Lean: `Theorems/SideFrame.lean`、`Theorems/RoomJoin.lean` の `RoomRun`、非公開の `Proof/SideFrame.lean`（`side_frame_check`）。

## しくみ

**抽象機械.** [1 フレーム全部](a-5-2-PipeWrites-ja.md) の抽象機械です。行き先を知らない書き込みと読みの手順があります（`Clean`）。始めにわかっているのは、ルーチンのバイト、ゲームのモードのバイト、`PPUCTRL` のビット 7、スタックポインタだけです。

**分けるところ.** どれも機械を変えません。

* 移動の終わりで、`px < x₀` の仮定のもとに: ページは 0 で、`x` は `[0, x₀)` のいくつかの片のどれかに入ります。`x₀` の 1 のビットごとに片が 1 つあります。そのビットより上は `x₀` のとおり、そのビットは 0、下のビットはわかりません。`x₀` の 1 のビットは 4 つなので、片は 4 つです。`posCover` が 256 バイト全部を確かめます。
* ブロックバッファのルーチンが `x` を足すところで、横の判定のとき: `x` を、わかっているビットに合う値ごとに分けます。仮定はいりません。
* 高さと足す数の和をマスクするところで、横の判定のとき: `A` の上の 4 ビットで分けます（16 個、仮定はいりません）。すると読む行がわかります。ですから `RowOK` はいりません。
* 読むところで、横の判定のとき: 読む場所がわかっています。それがブロックバッファの中で土管の列でなければ、`TilesOK` から [横の土管に入るフレームを本物のフレームで](c-7-3-SideEntryRule-ja.md) の 8 個の片が出ます。そのバイトはどちらのタイルでもありません。
* 横の判定かどうかは、ルーチンが保存する番号でわかります。足し算の番号の値は 3 つあります。大きいマリオ、水の中の大きいマリオ、小さいかしゃがんだマリオです。`Start` の 2 つだけにすると、抽象機械は 94,639 回失敗します。水の番号での読みです。
* `w_edge` と `h` は切ります。[移動の終わりの位置](a-5-9-MoveEnd-ja.md) と同じです。

**確かめること.** どの道でも、ルーチンのバイトは横の土管のものではありません。`ChkPBtm` の比較が見るバイトはどちらのタイルでもないので、書き込み `w` に来る道はありません。

**探索（証明の一部ではない）.** 移動の終わりから横の判定まで、位置の片を覚えています。読む列がわかったあとは、位置をその片に戻します。だから `x` の値だけが違う状態はまとまります。横の判定の始めでは、位置と `Clean` のバイトのほかは忘れます。

**大きさ.** 7,109,418 歩、分かれ 753,191、失敗 0、表 233,700。プログラムで探索が約 15 秒、確認が約 26 秒です。非公開の証明のビルドで 26 秒です。位置を 195 個の値に 1 つずつ分けた最初の抽象機械は、43,422,222 歩、表 2,810,791 個（17 GB）で、大きすぎました。

## 本物のフレームで確かめたこと

プログラム（`side-frame-check`）です。走りは [横の土管に入るフレームを本物のフレームで](c-7-3-SideEntryRule-ja.md) の `side-rule-check` と同じです。

| 走り | フレーム | 操作できる | 命令 | 読み | 入る |
|---|---|---|---|---|---|
| TAS の部屋（最初の操作から入ったあと 3 フレームまで） | 113 | 111 | 431,592 | 728 | 1 |
| TAS の部屋のフレームから、右に寄せた乱数の入力（200 回） | 45,123 | 45,123 | 174,974,667 | 309,608 | 67 |
| 入る 12、8、5、3 フレーム前から、左、右、A、B のすべての入力を 5 フレーム | 11,072 | 11,072 | 43,110,571 | 76,496 | 352 |
| 口の近くで、高さ、位置、状態、向きごとに 1 フレーム（書きかえ） | 38,400 | 38,400 | 144,438,759 | 191,144 | 1,295 |

* どの行でも、操作できるフレームは全部 `FrameStart` を満たし、その命令は全部 `Clean` を満たし、ブロックバッファのルーチンの読みは全部 `TilesOK` を満たします。`w_edge` にも `h` にも来る操作中のフレームはありません。
* 入る 1,715 回は全部 `w` で書きます。どれも書き込みの前に移動の終わりに 1 回だけ来ます。そこでの位置は 195〜216 px で、`x₀`（195）より左はありません。それはフレームの終わりの位置で（`movedE` は `read_P` と合う）、横の判定がページを読むどの時の位置とも同じです。

## `RoomRun` の欄

* なくなった: `pass`、`pos`（と `tiles`。[部屋のブロックの地図](c-7-12-RoomMap-ja.md) を見てください）。`Checks.sideRule` は `Checks.sideFrame` になりました。
* 増えた: `edgeE`（書き込みまでに `w_edge` にも `h` にも来ない）と `movedE`（`P(E)` は書き込みより前の移動の終わりの `posP`）。どちらもフレーム `E` だけのことです。
* 欄でないもの: `StartE`、`CleanE`、`TilesE`。`Route.Run.inRoom` が、部屋のフレームの抽象機械と `Route.Run` のつなぎ `roomEnter` から証明します。

## 仮定（Lean で証明していない）

* **`edgeE`.** 書き込みまでに、フレーム `E` は `w_edge` にも `h` にも来ません。
* **`movedE`.** `P(E)` は移動の終わりの位置です。`t0` までのフレームは `P(n)` をフレームの終わりで読みます（`read_P`）。フレーム `E` は `t0` よりあとで、まだ機械から読んでいません。本物のフレームでは 2 つは同じです（上）。
* **つなぎ `roomEnter`**（項目 1-1-0-4）: `RoomRun` のフレーム `E` は、部屋の中の `Route.Changes` のフレームの 1 つです。`StartE`、`CleanE`、`TilesE` はこれの上に立ちます。
* **口の右端.** 出てくるのは左端だけです。`RoomJoin` は左端だけを使います。

**ファイル.** `Theorems/SideFrame.lean`、`Theorems/RoomJoin.lean`、非公開の `Proof/SideFrame.lean`。

**再現.**
```
.lake/build/bin/smbrta side-frame-search          # 抽象機械の探索と確認、約 45 秒
.lake/build/bin/smbrta side-frame-check FM2 [N]   # 本物のフレームでの条件。自分の入力の走りを N 回
```
