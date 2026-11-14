[← Back](README-ja.md) | [English](b-3-10-PauseBits.md) | [Japanese](b-3-10-PauseBits-ja.md)

# 部屋で最初に操作できるときのポーズのバイト

**主張.** 部屋で最初に操作できるとき、ポーズのバイトのビット 0〜6 は 0 です。これを部屋への切り替えの段から、段がすでに持つ ROM の確認で証明しました。ですからフィールド `chg.pauseBits₂`（部屋で最初に操作できるときのポーズのバイトのビット 1〜6、項目 1-1-d-3-4）はなくなりました。`ChangesK.pauseBits₂` は同じ命題の定理です。名前の確認が 1 つ新しく要ります（`RoomChecks.pauseG`）。横の土管の名前のポーズのバイトが、縦の土管のデータのポーズのバイトと同じことです。

`m[i]` は `m` の RAM のバイト `i` です。`seq n` はフレーム `n` が始まるときの機械です。`a₁` は縦の土管に入るとき、`b₁` は部屋で最初に操作できるときです。`g` は縦の土管のデータが名づけるポーズのバイト（`GamePauseStatus`）、`g₂` は横の土管の名前が名づけるものです。`Entry`、`During`、`ExitAt` は[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)、`InRowsK`、`InRowsT` は[音のバイトを表で運ぶ、部屋への切り替え](b-3-7-1-SoundRows-ja.md)、`PipeRunK` は[縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md)と同じです。

## 命題

```
EndStatement.bitsK  :  InRowsK(m)  →  m[g] & 0x7F = 0                                        （確認の goOK から）
PipeRunK.pauseBits  :  (∀ n, a ≤ n < b → ¬ctl(seq n))  →  seq(b)[g] & 0x7F = 0
ChangesK.pauseBits₂ :  seq(b₁)[g₂] & 0x7E = 0                                                 （定理。フィールド pauseBits₂ だった）
RoomChecks.pauseG   :  g₂ = g                                                                 （新しい。非公開の確認 pause_index）
```

`PipeRunK.pauseBits` は `PipeRunK.way` から出ます。`b` の機械は操作できるので、表を持つ段にあります。`ChangesK.pauseBits₂` は、`ChangesK.pause₂` と同じく、最初の切り替えの走りを `ChangesK.run₁` から、入るときを `Run.entry₁` からとります。

## しくみ

**ポーズのルーチンはビット 1〜6 を保つ.** ルーチンがポーズのバイトを書くのは 2 通りだけです。ビット 0 を反転してビット 7 を立てる（Start を押し、ポーズのタイマーが 0 で、ビット 7 が 0）か、ビット 7 を消す（タイマーが 0 で Start を押していない）かです。ですからビット 1〜6 は変わりません。歩きがこのバイトについて知っているビットは、これらの書き込みのあとも知ったままです。

**入るときはそれを知っている.** `Entry` は、ポーズのバイトのビット 1〜6 が基準の値、つまり 0 であることを求めます（`entryMasks` の `GamePauseStatus` のマスク `0x7E`）。11 回目から、これも入るときに証明しています。`TitleStart` の近い状態がポーズのバイトを知り、操作できるときからのフレームがこのビットを保つからです（[1-1-b-3-4](b-3-4-EntryKeep-ja.md)）。前は `Rest`（`chg.entryRest₁`）の一部でした。土管のフレームの始まりの状態はこれを知り、土管にとどまるフレームの各終わりは始まりの状態の下になければならないので、土管のフレームの歩きはこれを保ちます。

**出口の状態がこれを知るようになった.** 前は、表を持つ段の出口の状態（`baseK`、`SideChangeEnd.exitStarts` から）はポーズのバイトのビット 0 しか知りませんでした。いまはビット 0〜6 を出口の基準の値で知っています（`exitBitsK`）。土管のフレームの 2 つの歩き、前の歩き（`zcheck`）とクラスを横に運ぶ歩き（`pipeCheckV`）は、どちらもまだその下で終わります。表を持つ段はこの状態から始まり、確認 `goOK` は段のすべての状態がビット 0〜6 が 0 だと知っていることを新しく求めます（`low7K`）。

**名前.** 段は縦の土管のデータでポーズのバイトを名づけ、部屋の確認は横の土管の名前で名づけます。2 つの一覧は同じ名前の別の表です。`RoomChecks.pauseG` は、どちらも同じ RAM の番号を与えると言います。非公開のファイルがこれを確かめます（`Proof/ScreenStart.lean` の `pause_index`）。

**段を読む確認.** 時間の段は表を持つ段から作るので、それを読む確認はどれも新しい段で動きます。`ScreenStart.roomCheck`、`RoomStart.startCheck`、`RoomMap.startCheckT`、`RoomPause.startCheck`、`RoomPair.rowsCheck`、`HurryStart.rowsCheck₁` です。すべて通りました（非公開のビルド、exit 0）。`left` が 0 の段は、表とあわせて今も 14,224 状態で、すべて操作できます。

**大きさ.** プログラムで、前の歩きの確認は 6.0 秒、クラスを横に運ぶ歩きは 11.4 秒、`soundCheck` は 180 秒です。`Proof/PipeChangeEnd.lean` の非公開のビルドは 250 秒でした（前は約 232 秒。ほかのビルドと同時に測りました）。

## ルートで変わったこと

* `chg.pauseBits₂` をなくしました。`ChangesK.pauseBits₂` は定理で、`ChangesK.pause₂` がそれを使います。
* `RoomChecks.pauseG` が新しくなりました。名前から出る 2 つの RAM の番号が等しいことです。`RoomChecks` はルートと急ぎの音楽の非公開のファイルで作ります（`pause_index`）。
* `PipeChangeEnd.EndStatement` に新しいフィールド `bitsK` があります。

## 仮定（Lean で証明していないもの）

* 新しいものはありません。縦の土管に入るときのポーズのバイトのビット 1〜6 は、タイトルで Start を押したことと操作できるときからのフレームから、`upClean₁` のもとで証明しています（[1-1-b-3-4](b-3-4-EntryKeep-ja.md)）。今回の前は `chg.entryRest₁` にありました。

**ファイル.** `Theorems/PipeChangeEnd.lean`（`low7K`、`low7_of`、`exitBitsK`、`baseK`、`goOK`、`EndStatement.bitsK`、`PipeRunK.pauseBits`）、`Theorems/Route.lean`（`RoomChecks.pauseG`、`low6_of_low7`、`ChangesK.pauseBits₂`、`ChangesK.pause₂`）。非公開の確認は前と同じ `Proof/PipeChangeEnd.lean` の `pipe_end_checks` と、`Proof/ScreenStart.lean` の `pause_index` です。公開のファイルにゲームのデータはありません。

**再現.**
```
.lake/build/bin/smbrta pipe-pause-check old   # 新しい出口の状態で、土管のフレームの 2 つの歩き。約 55 秒
.lake/build/bin/smbrta pipe-sound-rows -c     # 表を持つ段と soundCheck。約 6 分
.lake/build/bin/smbrta pipe-sound-rows -r     # 段での部屋の確認
```
