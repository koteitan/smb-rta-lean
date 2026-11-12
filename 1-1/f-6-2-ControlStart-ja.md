[← Back](README-ja.md) | [English](f-6-2-ControlStart.md) | [Japanese](f-6-2-ControlStart-ja.md)

# 地上で操作できるときの機械

**主張.** 横の土管から出る切り替えの本物の走りで、地上で操作できるときの機械は城の旗が立っておらず、1 フレーム全体の歩きが要る形の、操作中のフレームの始まりです（[操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ](f-6-19-FrameKeep-ja.md)）。条件は、切り替えが操作できるときの横の状態を出すとき（`SurfaceFrames.EndRun.start`）と同じです。

ですから `PoleJoin.Run` のフィールド `noCastle`（触るまで城の旗は立たない）はなくなりました。フィールド `keep.start`（触るまでの各フレームは操作中に始まる）もなくなりました。どちらも定理になりました。

`seq` は切り替えの機械（`SideChangeEnd.EndRun`）、`a` は入るとき、`b` は最初の操作です。`castle(m)` は `StarFlagTaskControl` が 0 でないことです。

```
AtCtl(m)         :=  FrameStart_K(m)  ∧  castle(m) = false
FrameStart_K(m)  :=  待ちのループ  ∧  S = S₀  ∧  ドットの窓  ∧  NMI がオン  ∧  ストローブがオフ  ∧  controllable(m)

ctlCheck         :  入るときの機械は m0 のプログラムを持ち、段の状態のうち操作できるものはどれも:
                    城のバイトが 0 とわかる、endOK                                    （side_ctl、native_decide）
ctl_of_rows      :  ctlCheck,  InRows(m),  controllable(m)   →   AtCtl(m)
EndRun.inRows    :  Statement,  EndStatement,  startCheck,  EndRun,  (∀ n,  a ≤ n < b  →  left(seq n) ≠ 0)   →   InRows(seq b)
EndRun.atCtl     :  同じもの,  ctlCheck   →   AtCtl(seq b)
Route.Run.atCtl₀ :  切り替えのチェック,  startCheck,  ctlCheck,  Route.Run   →   AtCtl(pole.seq 0)
```

`InRows(m)` は、段のある状態が `m` を覆うことです。`EndRun.inRows` は `EndRun.start` の帰納法です。土管の中か段の中かを、フレームごとに `b` まで追います。`startCheck` は土管の中の機械は操作できないと言うので、`seq b` は段の中にあります。`left` の条件は、`Run.start` と同じく、出口での時間から出ます（`EndRun.first`）。

`ctl_of_rows` は、`m` を覆う状態 `S` から `AtCtl` を読みます。城の旗は `S` のわかっているバイトです。`controllable(m)` がルーチン、モード、タスクを出します。残りは `FrameKeep.start_of_sim` が `endOK(S)` から出します。

## チェック

| 段 | 段の数 | 状態 | 城の旗が立っていないとわかる状態 | 操作できる状態 | そのうち `rowCtl` のとおりのもの |
|---|---|---|---|---|---|
| ポーズのフラグ 0 | 123 | 2,152 | 2,150 | 2 | 2 |
| ポーズのフラグ 0 でない | 123 | 1,022 | 1,020 | 2 | 2 |

操作できる 4 つの状態は、ルーチン（操作）、モード、タスク、城の旗（0）を知っています。待ちのループにいて `S = S₀` で、ドットの 2 つの窓のどちらかにいて、`ppuCtrl` のビット 7 が 1 とわかり、ストローブはオフです。それぞれの場合で城の旗を知らない 2 つの状態は最初の段、出口にあります。チェックはプログラムで 3.2 秒、非公開のビルド（`Proof.ControlStart`）で 4.4 秒です。

## 本物の走りで

最後の変更のあとの `ctl-start-check FM2` です（終了コード 0、悪いもの 0）:

* ムービー: ムービーのフレーム 1046 のあとに地上で操作できます。そこでの機械は `FrameStart_K` で、城の旗は立っていません。
* 本物の 44 の入るとき（基準、ムービーのもの、土管へ歩く 42 個）を、それぞれ入力なし、Start のないランダムな入力、最初の 80 フレームに Start、で走らせました: 132 の走りがどれも操作できるようになり、操作できるときの機械はどれも `FrameStart_K` で城の旗は立っていません。

## 仮定（Lean で証明していないもの）

ここだけの仮定はありません。`Run.atCtl₀` は `Run.start` と同じ切り替えの条件を使います。`chg` のフィールド（入るとき、Start なし、出口での音、出口での時間、最初の操作）です。[道筋のページ](0-1-Route-ja.md)に挙げてあります。

仮定でなくなったもの: `PoleJoin.Run` の `noCastle`、`FrameKeep.Frames` の `keep.start`。新しいもの: ROM のチェック `ctlCheck`、`keep` のフィールド `ctl`（触る前の各フレームは操作中に終わる。そのあとルーチンとタスクだけになり、いまは定理です。代わりの仮定は、触る前のフレームがルーチン、モード、タスクを番地で書かないこと `noStore`、[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）と `lagStart`。そのあと `lagStart` はまたなくなりました。`keep` は数えるかどうかによらず全部のフレームを持ち、歩きが `lag` のフレームも覆います（[操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ](f-6-19-FrameKeep-ja.md)）。

**ファイル.** `Theorems/ControlStart.lean`、`Theorems/Route.lean`（`Run.atCtl₀`）、非公開の `Proof/ControlStart.lean`（`side_ctl`）。

**確かめ方.**
```
.lake/build/bin/smbrta ctl-start-check FM2       # チェック、段、本物の走り（約 20 秒）
```
