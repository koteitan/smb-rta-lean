[← Back](README-ja.md) | [English](d-3-5-1-SideTime.md) | [Japanese](d-3-5-1-SideTime-ja.md)

# 横の土管でのゲームタイマー

**主張.** 横の土管のフレームは、ゲームタイマーの桁を変えません。なので横の土管の入口でタイマーが 000 でなければ、出口でも 000 ではありません。これは ROM の確認つきで証明しました。[横の土管のフレームを通るポーズ](d-3-4-3-SidePause-ja.md) の歩きがこれを運びます。なので道筋は「タイマーが 000 でない」を、出口ではなく入口 `seq(a₂)` で求めます（`chg.time₂`、1-1-d-3-5。このページは 1-1-d-3-5-1）。仮定を `entry₂` と同じ状態へ移しただけで、なくしてはいません。

このページには、`time₂` をなくすことについて測ったことも書きます。部屋のフレームからは出ません。部屋への切り替えの行は、部屋で最初に操作できるときのタイマーを知らず、部屋のフレームはタイマーを減らすからです。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` の入力 `i` での 1 フレームです。`seq(n)` はフレーム `n` が始まるときの機械です。`a₂` は横の土管の入口、`b₂` はそのあとの最初の操作です（`Route.Base.a₂`、`Route.Base.b₂`）。`digits` は `GameTimerDisplay` の 3 バイトです。`Entry2`、`Exit`、`PauseE`、`QuietK`、`InRowsK`、`During2C` は [横の土管のフレームを通るポーズ](d-3-4-3-SidePause-ja.md) のものです。

## 命題

```
TimerOK(m)    :=  ∃ i ∈ digits,  m[i] ≠ 0

PipeQ.during  :  Entry2(M) ∧ PauseE(M) ∧ TimerOK(M)  →  During2C(M)
PipeQ.step    :  During2C(m)  →  During2C(frame(m, i))  ∨  ( Exit(frame(m, i)) ∧ QuietK(frame(m, i)) ∧ InRowsK(frame(m, i)) )
EndRunQ.timeE :  TimerOK(seq a)                                         （フィールド。前は  time : ∀ n ∈ [a, b],  Exit(seq n) → TimerOK(seq n)）

chg.time₂     :  TimerOK(seq a₂)                                        （フィールド。前は  ∀ n ∈ [a₂, b₂],  Exit(seq n) → TimerOK(seq n)）
```

`During2C(m)` は今は `TimerOK(m)` を含みます。その始めの状態は `dg` を持ちます。`dg` は抽象機械のフラグで、`D` のバイトがすべて 0 ではないことを言います。`D` は `digits` です。出口の `InRowsK` にはそこでの `TimerOK` が要ります（[切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) の時間の行）。`step` は今はそれを前提なしに出します。

Lean：`Theorems/SidePause.lean`（`sideEnvT`、`withT`、`startsCT`、`baseXT`、`During2C`、`pipeCheck`、`sim_withT`、`any_of_timerOK`、`timerOK_of_sim`、`sim_of_simT`、`toOne_dg`、`PipeQ`、`pipeQ_of_check`、`EndRunQ.timeE`）、`Theorems/Route.lean`（`ChangesBase.time₂`、`ChangesK.run₂`）、private の `side_pause_check`（`Proof/SidePause.lean`）。公開のファイルにゲームのデータはありません。

## しくみ

`SidePause.pipeCheck` の土管のフレームの歩きは、3 つの桁を `D` のバイトにします（`sideEnvT`）。始めの状態と出口の状態はすべて `dg` を持ちます（`withT`）。抽象機械では `D` のバイトへの書き込みは `dg` を消します。フレームの終わりの状態は始めの状態（か出口の状態）の下にないといけません。`B` が `dg` を持つなら、`A ≤ B` には `A` の `dg` が要ります。なので、土管のフレームのどの道も桁に書き込まないときだけ確認が通ります。確認は通ります。ゲームタイマーを減らすのは `RunGameTimer` だけで、ルーチンが横の土管のもの（操作のルーチンより小さい番号）の間はすぐ抜けます。確認はプログラムで約 66 秒です（桁なしでは 62 秒）。前と同じ確認に知っていることを足しただけで、新しい確認は加えていません。

## 実際のフレームで

`room-music-real FM2 5 20`（[部屋のフレームを通る音楽のバイト](d-2-5-1-RoomMusic-ja.md) の走り）：縦の土管への 13 の実際の入りからの部屋の最初の操作、Start をでたらめに押すでたらめな入力、横の土管の近くの 42 の状態からの歩き。各入口のあと、土管のフレームを操作できるまで、でたらめな入力（Start も）で進めます。

| 横の土管の入口 | 入口でタイマーが 000 でない | 入口から操作の前のフレームまで、どのフレームも同じ桁 |
|---|---|---|
| 210 | 210 | 210 |

TAS：入口（TAS のフレーム 764）でタイマーは 380 で、操作できるまで（TAS のフレーム 1046）どのフレームも同じ桁です。

## 測ったこと：なぜ `time₂` は部屋から出ないか

プログラムで、定理ではありません（`entry-bytes-check`）。

* **部屋で最初に操作できるときのタイマー.** 部屋への切り替えの時間の行には、操作できる状態が 14,224 あります。どれも 3 つの桁のどのビットも知らず、どれも `dg` を持ちません。行は縦の土管の出口で `dg` を持って始まります。しかし切り替えの最後のフレームでプレイヤーのルーチンが始まり、`RunGameTimer` が動きます。これが桁を減らし（`ResGTCtrl`、`DigitsMathRoutine`）、桁への書き込みは `dg` を消します。14,224 のすべての状態で、タイマーの制御のバイト `GameTimerCtrlTimer` は `ResGTCtrl` が書く値です。これがそのしるしです。なので部屋で最初に操作できるとき、縦の土管の出口で 000 でなくても（`chg.time₁`）、タイマーは 000 かもしれません。
* **部屋のフレームはタイマーを減らす.** 部屋の歩き（[部屋での画面のページ](d-2-4-ScreenPage-ja.md)）のフレームの終わりは 14 あります。2 つは横の土管のルーチン、6 つは操作のルーチン、2 つは命を失うルーチン（穴に落ちる）、4 つはけがか死のルーチンで `GameTimerExpiredFlag` が立っています。このフラグを立てるのは時間切れのコード（`TimeUpOn`）だけです。なので部屋のフレームはタイマーを 000 まで減らし、それで部屋を終えられます。1 フレームの条件では、部屋を通してタイマーの下限を運べません。下限には、タイマーを知っているフレーム 0（`Route.Run.read₀`、タイトルで Start を押したとき）からのフレームの数が要ります。
* **出口でタイマーが 000 のとき.** 出口のあとの操作を与えるはずのフレームで、入場のルーチンがプレイヤーのルーチンに渡し、同じフレームで `RunGameTimer` が動きます（コードから読みました）。桁が 000 なら `TimeUpOn` へ行き、プレイヤーは死にます。なのでそのフレームは操作できないで終わります。これは [切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) で走らせました。入口でタイマーを 000 に書き換えると、フレーム 282 で操作できません（ルーチンは死）。このような走りには死があり、道筋は扱いません（1-1-0-6-3）。実際の走りでは、タイマーはプレイのフレーム 24 ごとに 1 減るので、これには約 9,600 フレームかかります（機械については証明していません）。

* **14 回目: 部屋の最初の操作のタイマーから入口のタイマーは出ない.** 本物の機械で測りました（`side-time-low FM2`、[縦の土管から横の土管までのレベルの番号](d-2-5-3-AreaKeep-ja.md) を見てください）。ムービーの部屋の最初の操作でタイマーを 004（制御タイマー 15 … 24）か 005（制御タイマー 0 … 14）にすると、ムービーの入力は 111 フレームのあとにタイマー 000 で横の土管に入ります（150 の始まりのうち 25）。だから部屋のフレームで `dg` を運んでも、時間切れの道があってもなくても、`time₂` は出ません。

## 道筋で変わったこと

* `chg.time₂` は入口で `TimerOK(seq a₂)` を求めます。前は、`a₂` から `b₂` までの出口のバイトを持つ各状態で `TimerOK` を求めました。
* `ChangesK.run₂` は `EndRunQ.timeE := chg.time₂` とします。`SidePause.PipeQ` の名前は同じです。`HurryStart` と `HurryMusic` は前と同じに使います。

## 仮定（Lean で証明していない）

* `chg.time₂`：横の土管の入口でゲームタイマーが 000 でない（1-1-d-3-5）。上のすべての実際の走りで成り立ちます。

**ファイル.** `Theorems/SidePause.lean`、`Theorems/Route.lean`。private の確認は `Proof/SidePause.lean`（`Main.lean` の `genSidePause`、変えていません）。

**再現.**
```
.lake/build/bin/smbrta side-pause-check              # 確認をプログラムで、約 66 秒
.lake/build/bin/smbrta side-time-check               # 同じ歩きをプログラムの中で組んだもの、約 66 秒
.lake/build/bin/smbrta room-music-real FM2 5 20      # 実際の入口と土管を通るタイマー、約 2 分 20 秒
.lake/build/bin/smbrta entry-bytes-check             # 部屋で最初に操作できるときのタイマーと、部屋のフレームの終わり、約 51 秒
```
