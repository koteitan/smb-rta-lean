[← Back](README-ja.md) | [English](c-7-2-RoomStart.md) | [Japanese](c-7-2-RoomStart-ja.md)

# 部屋で最初に操作できる状態

**主張.** [地下の部屋をつなぐ](c-5-RoomJoin-ja.md) は、最初の操作での横の状態、位置、縦の状態、覚えている速さを仮定していました（`start`、`startP0`、`startP1`、`v_start`、`ab_start`）。これは本物の機械で証明しました。[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md) の段から出ます。条件はその切り替えの条件と、操作の前に `left₁` が 0 にならないこと（`chg.first₁`）です。部屋の機械と切り替えの機械が同じであること（`roomCtl`）と、最初の操作の縦の状態と覚えている速さを機械から読むこと（`vs_C`、`ab_C`）は、つなぎのフィールドです。

## 文

`s₀`、`P₀`、`P₁`、`Y_s`、`W_s`、`f_s` は部屋の数（`RoomJoin.room`、`Nums`）です。`s₀` は (速さ, 端数, 向き, 動く向き, 走りの速さ) = (0, 0, 1, 0, 0) の状態です。止まっていて右を向いています。`P₀ = 256·x_s`、`P₁ = 256·x_s + 255` で、`x_s` は部屋の最初の `x` です。`Y_s` は上から 50 ピクセル、`W_s` は 1 フレームに 2.375 ピクセル、`f_s` は機械の最初の落下の力です。

`hs(m)` は機械の横の状態（`FrameModel.readHS`）、`P(m)` は位置（`posP`）、`pix(m) = 256·page + x`、`vs(m)` は縦の状態（`SurfaceFrames.vsOf`）、`ab(m)` は覚えている速さです。`VY(s) = 256·y + 端数`、`VW(s) = 256·vy + 端数` です。

```
StartAt(m)       :  hs(m) = s₀  ∧  P₀ ≤ P(m) ≤ P₁
                    ∧  vs(m).st = 2  ∧  VY(vs m) ≤ Y_s  ∧  VW(vs m) ≤ W_s  ∧  vs(m).vfd = f_s
                    ∧  ab(m) = 0

startCheck       :  切り替えの 2 つの場合の段（rowsA、rowsB）のどの状態 S も
                    操作のバイト（OperMode、OperMode_Task、GameEngineSubroutine）を知り、
                    操作できるなら、横の状態、page、x、縦の状態、覚えている速さのバイトを知り、
                    hs(S) = s₀  ∧  P₀ ≤ 256·pix(S)  ∧  256·pix(S) + 255 ≤ P₁  ∧  縦の状態と ab が上のとおり

start_of_rows    :  startCheck ∧ InRows(m) ∧ ctl(m)  →  StartAt(m)
left_during      :  During(m)  →  left(m) ≠ 0
PipeRun.inRows   :  EndStatement ∧ PipeRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  InRows(seq b)
PipeRun.start    :  EndStatement ∧ startCheck ∧ PipeRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  StartAt(seq b)
Route.Run.roomStart :  pipe_end ∧ room_start ∧ Run  →  StartAt(room.fm room.C)
```

`PipeRun.inRows` は、入るときから操作までのどの機械も、土管のフレームの状態（`During`）か段の中（`InRows`）にあることを、フレームごとの帰納法で示します。土管のフレームは `step`、段のフレームは `rows` です。`rows` は「`left` がもう 0」か「次も段の中」を返します。前のほうを `first₁` が除きます。最後の機械は操作できるので `left = 0`（`atControl`）です。土管のフレームの状態では `left = timer + 43 > 0` なので、段の中です。

`RoomRun.toCore` と `RoomRun.entry_ge` は `StartAt(fm C)` を引数に取ります。`read_hs`、`read_P`、`vs_C`、`ab_C` で `start`、`startP0`、`startP1`、`v_start`、`ab_start` になります。

## 確認

`room_start`（非公開、`native_decide`）。段を計算して、その状態を見るだけです。プログラムで約 3 秒、証明のビルドで約 4 秒です。段は 2 つの場合とも 44 段、状態は 8122 個と 1924 個です。操作できる状態はそれぞれ 2 個です。どれも `s₀` で、位置は部屋の最初の位置、状態は落下、高さは上から 48 + 104/256 ピクセル、下向きの速さは 1 フレームに 2 + 88/256 ピクセル、落下の力は機械の最初の値、覚えている速さは 0 です。

## 本物の走り

プログラム `room-start-check FM2 [N]` です。入る状態は、参照の入る状態、TAS の入る状態、13 個の本物の入る状態です。

| 入力 | 走り | 操作できない | 操作の前に `left₁ = 0` | 操作のときに `StartAt` でない |
|---|---|---|---|---|
| TAS（フレーム 653 で操作） | 1 | 0 | 0 | 0 |
| 入力なし | 15 | 0 | 0 | 0 |
| ランダム、Start なし | 300 | 0 | 0 | 0 |
| ランダム、土管のフレームだけ Start あり | 300 | 0 | 0 | 0 |

## 前提（Lean では証明していない）

* **`chg.first₁`.** 操作の前に `left₁` は 0 にならない。時間切れで死ぬ走りでは成り立ちません。その走りはこの部屋では操作できません。
* **`roomCtl`.** `room.fm room.C = chg.seq chg.b₁`。部屋の最初の機械は切り替えの最後の機械です。列の作り方から来ます。
* **`vs_C`、`ab_C`.** `fr.vs C = vs(fm C)`、`fr.ab C = ab(fm C)`。`read_hs`、`read_P` と同じ、機械から読むことです。`C` のフレームだけです。
* 切り替えの条件（`chg.entry₁`、`places₁`、`quiet₁`、`noStart₁`）。[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md) の前提です。

**ファイル.** `Theorems/RoomStart.lean`、`Theorems/RoomJoin.lean`（`StartAt`、`vs_C`、`ab_C`）、`Theorems/Route.lean`（`first₁`、`roomCtl`、`Run.roomStart`）、非公開の `Proof/RoomStart.lean`。
