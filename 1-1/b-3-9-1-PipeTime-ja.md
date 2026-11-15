[← Back](README-ja.md) | [English](b-3-9-1-PipeTime.md) | [Japanese](b-3-9-1-PipeTime-ja.md)

# 縦の土管でのゲームタイマー

**主張.** 縦の土管のフレームは、ゲームタイマーの桁を変えません。なので縦の土管の入口でタイマーが 000 でなければ、出口でも 000 ではありません。これは ROM の確認つきで証明しました。[縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md) の歩きがこれを運びます。なので道筋は「タイマーが 000 でない」を、出口ではなく入口 `seq(a₁)` で求めます（`chg.time₁`、項目 1-1-b-3-9。このページは 1-1-b-3-9-1）。仮定を `entryRest₁` と同じ状態へ移しただけで、なくしてはいません。横の土管では第 12 回に同じことをしました（[横の土管でのゲームタイマー](d-3-5-1-SideTime-ja.md)）。

このページには、`time₁` をなくすことについて測ったことも書きます。操作から入口までのフレームの 1 フレームごとの条件からは出ません。操作中の走りが、タイマー 000 で入口に来られるからです。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` の入力 `i` での 1 フレームです。`trace(m, i, j)` はそのフレームの `j` 歩あとの機械です。`seq(n)` はフレーム `n` が始まるときの機械です。`a₁` は縦の土管の入口、`b₁` はそのあとの最初の操作です（`Route.Base.a₁`、`Route.Base.b₁`）。`digits` は `GameTimerDisplay` の 3 バイトです。`During`、`ExitAt`、`Places`、`classesV`、`SIn`、`QuietV`、`QuietP`、`SongAt`、`shape`、`InRowsK` は [縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md) と [音のバイトを表で運ぶ部屋への切り替え](b-3-7-1-SoundRows-ja.md) のものです。

## 命題

```
TimerOK(m)  :=  ∃ i ∈ digits,  m[i] ≠ 0
DuringV(m)  :=  During(m)  ∧  ( ∃ t ∈ classesV,  SIn(t, m) )  ∧  TimerOK(m)

pauseStep   :  ∀ m, DuringV(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                 DuringV(frame(m, i))
               ∨ ( ExitAt(frame(m, i))  ∧  QuietV(frame(m, i))  ∧  TimerOK(frame(m, i))  ∧
                   ( frame(m, i) で QuietP ∧ SongAt(shape)  →  InRowsK(frame(m, i)) ) )

PipeRunK.time :  TimerOK(seq a)                         （フィールド。前は  ∀ n ∈ [a, b],  ExitAt(seq n) → TimerOK(seq n)）
chg.time₁     :  TimerOK(seq a₁)                        （フィールド。前は  ∀ n ∈ [a₁, b₁],  ExitAt(seq n) → TimerOK(seq n)）
```

前は `DuringV` に `TimerOK` がなく、`pauseStep` は出口での `TimerOK` を `InRowsK` の前提として求めていました。いまは `pauseStep` が前提なしに出口での `TimerOK` を出します。`PipeRunK.atEntry` は、入口での `Entry`、`PauseV`、`TimerOK` から `DuringV(seq a)` を出します。`PipeRunK.bound`、`PipeRunK.first`、`PipeRunK.inRowsT`、`PipeRunK.pauseBits` は前と同じで、引数も同じです。

Lean: `Theorems/PipeChangeEnd.lean`（`withT`、`startsPT`、`baseKT`、`cfgRqT`、`cfgOqT`、`dgOff`、`pipeCheckV`、`DuringV`、`EndStatement.pauseStep`、`timerOK_of_simT`、`sim_of_simT`、`simT_of_sim`、`toOne_withT`、`invT_of`、`of_invT`、`PipeRunK.time`、`PipeRunK.stepD`、`PipeRunK.atEntry`）、`Theorems/Route.lean`（`ChangesK.time₁`）、`Theorems/HurryStart.lean`（`Chg₁.time₁`）。非公開の確認はこれまでどおり `Proof/PipeChangeEnd.lean` の `pipe_end_checks` です。公開のファイルにゲームのデータはありません。

## しくみ

ポーズのクラスを横に運ぶ土管のフレームの歩き（`pcheck`、[b-3-7-2](b-3-7-2-PipePause-ja.md)）を、環境 `timeEnv` で動かします。そのバイト `D` は 3 つの桁です。どの始まりの状態にも、出口のどの状態にも `dg` があります（`startsPT`、`baseKT`）。抽象機械では `D` のバイトへの書き込みは `dg` を消します。フレームの終わりの状態は始まりの状態（または出口の状態）の下になければならず、`A ≤ B` は `B` が `dg` を持つとき `A` にも `dg` を求めます。なので確認が通るのは、土管のフレームのどの道も桁に書かないときだけです。確認は通ります。ゲームタイマーを減らすのは `RunGameTimer` だけで、ルーチンが縦の土管のもの（プレイヤーの操作より小さいルーチンの番号）のあいだは、すぐに抜けます。

2 つの小さな補題が、土管のフレームの 2 つの歩きをつなぎます。前の歩き（`zcheck`、桁なし）は、これまでどおり `left` とポーズのフレームを出します（`EndStatement.step`、`EndStatement.paused`）。`HurryStart` は前と同じくそれを使います。

```
invT_of  :  During(m) ∧ TimerOK(m)  →  m は dg を持つ歩きの始まりの状態に覆われる          （ROM なし）
of_invT  :  m は dg を持つ歩きの始まりの状態に覆われる  →  During(m) ∧ TimerOK(m)           （withT の前の始まりの状態は dg を持たない: dgOff）
```

**大きさ.** 表は 58,850 と 43,229 の状態で、桁なしと同じです。プログラムでは探索が 7.4 秒と 4.2 秒、確認が 10.5 秒です（`pipe-time-check`）。`Proof/PipeChangeEnd.lean` の非公開のビルドは 226 秒でした（前は 232 秒）。新しい確認は足していません。同じ確認に知識を足しただけです。

## 本物のフレームで

`pipe-time-real FM2 3 7 0 0`: `pipe-pause-real` の 334 の入口（基準、TAS、土管の上に立つ本物の入口、ポーズのある基準の道の入口、Start をでたらめに押して立ったあとの入口）。それぞれから、でたらめな入力で土管のフレームを進めます。Start はおよそ 3、9、40 フレームに 1 回です。

| 入口 | 入口でタイマーが 000 でない | 土管のフレーム | 入口の桁のまま | 出口 | 出口で入口の桁のまま | 出口でタイマーが 000 でない |
|---|---|---|---|---|---|---|
| 334 | 334（いちばん小さいのは 368） | 88,769 | 88,769 | 1,002 | 1,002 | 1,002 |

## 測ったこと: `time₁` が操作からのフレームから出ない理由

プログラムで、定理ではありません（`pipe-time-real FM2 0 7 9160 9186`）。

* **操作からの歩きは `dg` を保てない.** 操作中のフレームでは `RunGameTimer` が桁を減らします（`DigitsMathRoutine`）。桁への書き込みは `dg` を消します。[入口の状態](b-3-4-EntryKeep-ja.md) の歩きは桁をどれも知りません。
* **タイマーを 000 にするフレームは時間切れに行かない.** そのフレームはタイマーの制御のバイトを 24 にします（`ResGTCtrl`）。時間切れ（`TimeUpOn`）は、そのバイトが 0 になったあとのフレームでだけ来ます。`m0` から立ったままでいると、フレーム 9,600 のあとで桁が 000 になり、操作はできたままです。フレーム 9,624 のあとで操作できなくなります（死のルーチン）。なので 24 フレームのあいだ、タイマー 000 で操作できます。
* **そのような走りはタイマー 000 で土管に入る.** `m0` から `k` フレーム立ってから基準の道を進みます。`k` は 9,160 から 9,185 です。12 回の走りがタイマー 000 で土管に入ります（フレーム 9,602 から 9,624 のあと）。12 回とも、入口の前のどのフレームも操作中で、[b-3-4](b-3-4-EntryKeep-ja.md) の保つバイトを持ち、入口で `PauseV` が成り立ちます。なので操作からの 1 フレームごとの条件は、入口での `TimerOK` を出しません。入ったあと 100 フレームのうちに操作はなく、フレーム 91 のルーチンは死のものです。
* **これらの走りは `Entry` を 1 バイトで満たさない.** 12 回とも、`Entry` のバイトで基準と違うのは、とっておいた曲（`AreaMusicBuffer_Alt`）だけです。これは `Rest`（`entryRest₁`）にあります。タイマー 100 での急ぎの音楽が変えました。なので道筋の仮定はこれらの走りをすでに除きますが、仮定したバイトを通してです。入口での `TimerOK` を証明するには、歩きがタイマーの値ととっておいた曲を結ぶか、フレーム 0（タイマーは 400、`Route.Run.read₀`）からのフレームを数える必要があります。どちらもしていません。

## 道筋で変わったこと

* `chg.time₁` は `TimerOK(seq a₁)` を入口で求めます。前は、`a₁` から `b₁` までの、出口のバイトを持つどの状態でも `TimerOK` を求めていました。
* `ChangesK.run₁` は `PipeRunK.time := chg.time₁` とします。`HurryStart.Chg₁.time₁` も同じように変えました。

## 仮定（Lean では証明していない）

* `chg.time₁`: 縦の土管の入口でゲームタイマーが 000 でない（1-1-b-3-9）。上の本物の走りではどれでも成り立ちます。

**ファイル.** `Theorems/PipeChangeEnd.lean`、`Theorems/Route.lean`、`Theorems/HurryStart.lean`。非公開の確認は `Proof/PipeChangeEnd.lean`（変えていない）。

**再現.**
```
.lake/build/bin/smbrta pipe-time-check                          # 桁を持つ歩きをプログラムで、場所の表と合わせて約 65 秒
.lake/build/bin/smbrta pipe-time-real FM2 3 7 0 0               # 本物の 334 の入口と土管の中のタイマー、約 1 分 30 秒
.lake/build/bin/smbrta pipe-time-real FM2 0 7 9160 9186         # タイマー 000 まで立ってから基準の道、数分
```
