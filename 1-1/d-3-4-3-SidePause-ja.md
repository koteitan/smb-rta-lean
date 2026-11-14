[← Back](README-ja.md) | [English](d-3-4-3-SidePause.md) | [Japanese](d-3-4-3-SidePause-ja.md)

# 横の土管のフレームを通るポーズ

**主張.** 横の土管の入口で、ポーズの音が鳴っていない、またはポーズを解く音が鳴っていてポーズのタイマーがその数より 1 多い、またはそのフレームでポーズを解いた、とします（`PauseE`）。すると土管のフレームでは、Start も含めてどの入力でも、ポーズの 6 つのバイトは 90 のクラスのどれかにとどまり、出口ではポーズの音は `QuietK` のとおりです。これは ROM の確認つきで証明しました。なので道筋はもう出口の `QuietK` を仮定しません。`chg.quiet₂` はなくなり、`chg.pause₂`（入口の条件 `PauseE`）が新しく入りました（1-1-d-3-4）。Start をでたらめに押す実際の走りでは、636 の入口すべてで `PauseE` が成り立ち、土管の 205,016 フレームはすべてクラスに入り（90 のクラスのうち 89 が現れました）、636 の出口すべてで `QuietK` が成り立ちました。入口の `PauseE` は、いまは部屋で最初に操作できるときから証明しています（[部屋のフレームを通るポーズ](d-3-4-4-RoomPause-ja.md)）。`chg.pause₂` は定理になり、道筋はそこでポーズのバイトのビット 1 から 6 が 0 であることだけを求めます（`chg.pauseBits₂`）。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` の入力 `i` での 1 フレームです。`Entry2`、`During2`、`Exit`、`TimerOK` は [地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) のものです。`QuietK`、`InRowsK`、`EndStatementK`、`EndRunK` は [地上への切り替えを、音のバイトを表にして](d-3-4-2-SideChangeSound-ja.md) のものです。

## ポーズの 6 つのバイト

`q`、`b`、`f`、`c` はポーズの音のキュー、バッファ、フラグ、数です（`PauseSoundQueue`、`PauseSoundBuffer`、`PauseModeFlag`、`Squ1_SfxLenCounter`）。`t` はポーズのタイマー（`GamePauseTimer`）、`g` はポーズのバイト（`GamePauseStatus`）です。`U` はポーズを解く音の値、`P` はポーズの音の値、`L` は音の長さです。ROM から記号で読みます。

ゲームの中心のフレームでのはたらき：

* Start は `t = 0` で `g` のビット 7 が 0 のときだけ効きます。押すと `g` のビット 0（ポーズ中かどうか）が反転し、`g` のビット 7 が立ち、`q` に `P`（ポーズ）か `U`（ポーズを解く）が入り、`t = L + 1` になります。
* `t ≠ 0` の間、毎フレーム `t` から 1 引きます。`t = 0` で Start を押していないと、`g` のビット 7 が消えます。
* 次のフレームで音のルーチンが `q` を `b` と `f` に入れ、`c = L` で音を始め、すぐ 1 引きます。毎フレーム `c` から 1 引きます。`c` が 0 になると `b` は 0 になります。ポーズを解く音のあとは `f` も 0 になります。

なのでポーズの音が鳴っている間は `t = c + 1` で、Start は効きません。

## クラス

| クラス | `g` | `q` | `b` | `f` | `c` | `t` | 数 |
|---|---|---|---|---|---|---|---|
| 鳴っていない | 0 かビット 7 | 0 | 0 | 何でも | 何でも | 何でも | 2 |
| ポーズを解く音 | ビット 7 | 0 | `U` | `U` | `k` | `k + 1` | `k` = 1 … `L`：42 |
| ポーズを解いた | ビット 7 | `U` | 0 | `P` | 何でも | `L + 1` | 1 |
| ポーズした（ポーズ中） | ビット 0 と 7 | `P` | 0 | 何でも | 何でも | `L + 1` | 1 |
| ポーズの音（ポーズ中） | ビット 0 と 7 | 0 | `P` | `P` | `k` | `k + 1` | `k` = 1 … `L − 1`：41 |
| ポーズの音が終わった（ポーズ中） | ビット 0 と 7 | 0 | 0 | `P` | 0 | 1 | 1 |
| | ビット 0、ビット 7 はあってもなくても | 0 | 0 | `P` | 0 | 0 | 2 |

`g` の書いていないビットは 0 です。`PauseE(m)` は `m` が最初の 3 行のどれかにあることです：

```
PauseE(m)  :=  ( m[g] ∈ {0, 0x80}  ∧  m[q] = 0  ∧  m[b] = 0 )
            ∨  ( m[g] = 0x80  ∧  m[q] = 0  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] ≤ L  ∧  m[t] = m[c] + 1 )
            ∨  ( m[g] = 0x80  ∧  m[q] = U  ∧  m[b] = 0  ∧  m[f] = P  ∧  m[t] = L + 1 )
```

出口のフレームはポーズ中ではないので、機械は最初の 3 行のどれかにあります。これらから `QuietK` が出ます（`quietK_of_kind`。出口の参照の `q` と `b` は 0）。

## 命題

`During2C(m)`：`m` は、土管のフレームの始めの状態に、あるクラスの 6 つのバイトを入れたもので覆われます（`During2` と同じく土管のタイマーを追います）。`PipeQ` は次のフィールドを持ちます。確認 `pipeCheck` と行の確認 `endCheckK` がそれを出します（`pipeQ_of_check`）。

```
during    :  ∀ M,  Entry2(M) ∧ PauseE(M) → During2C(M)
toDuring2 :  ∀ m,  During2C(m) → During2(m)
step      :  ∀ m, During2C(m) → ∀ i :  During2C(frame(m, i))
               ∨  ( Exit(frame(m, i))  ∧  QuietK(frame(m, i))  ∧  ( TimerOK(frame(m, i)) → InRowsK(frame(m, i)) ) )
```

**走り.** `EndRunQ` は `EndRunK` のフィールドで、出口の `quiet` のかわりに入口の `pause : PauseE(seq a)` を持ちます。`b` は入口 `a` のあとの最初の操作です（`hc`）。定理は `EndRunK` のものに、引数 `PipeQ` を 1 つ加えたものです：

```
EndRunQ.bound  :  cnt(a) + 282 ≤ cnt(b)
EndRunQ.first  :  hc  →  ∀ n ∈ [a, b),  left(seq n) ≠ 0
EndRunQ.inRows :  hc  →  InRowsK(seq b)
EndRunQ.start  :  hc  ∧  startCheckK  →  Start(PA, seq b)
EndRunQ.atCtl' :  hc  ∧  ctlCheckK    →  AtCtl(seq b)
EndRunQ.last   :  hc  →  a + 1 ≤ b  ∧  seq(b − 1) は行にある  ∧  left(seq(b − 1)) = 1
```

Lean：`Theorems/SidePause.lean`（`PauseBytes`、`pauseBytesOf`、`classesP`、`PauseE`、`kindsX`、`withClass`、`pauseKeep`、`startsC`、`baseX`、`During2C`、`pipeCheck`、`class_of_pauseE`、`quietK_of_kind`、`sim_withClass`、`PipeQ`、`inRows_of_base`、`pipeQ_of_check`、`EndRunQ`、`StQ`、`st_stepQ`、`st_step_pausedQ`、`EndRunQ.bound`、`EndRunQ.way`、`EndRunQ.first`、`EndRunQ.inRows`、`EndRunQ.last`、`EndRunQ.start`、`EndRunQ.atCtl'`）、private の `side_pause_check`（`native_decide`、`Proof/SidePause.lean`）、`side_pause`（`Proof/Route.lean`）。公開のファイルにゲームのデータはありません。

## しくみ

**クラスを始めの状態にする.** `SideChangeEnd` の土管のフレームは 4 つの状態（参照の機械 2 つ、ドットの 2 種類）から始まります。ここではその各々に、各クラスの 6 つのバイトを入れます。始めの状態は 360 です。探索は 6 つのバイトを分けておきます。`SideChangeEnd` の確認 `duringCheck` をそのまま使います。始めの状態からの各フレームは始めの状態で終わるか、土管のタイマーが切れるフレームでは出口で終わります。出口の状態は `QuietK` の 44 の種類で分けます（`kindsX`）。なので出口で歩きが終わると、ある種類のバイトを持ちます。クラスや種類は状態に知っているバイトを足すだけです（`withClass(t, S) ≤ S`、確認つき）。なので `During2C` から `During2` が出て、`SideChangeEnd` と `SideChangeSound` が `During2` について証明したことはそのまま使えます。

**なぜタイマーをクラスに入れるか.** `t` がないと、ポーズを解く音が鳴っている間に Start が効く道が歩きに入ります。すると `b = U` の間にポーズし、ポーズの音は始まらず、ポーズを解く音が終わるとき、ポーズ中なのに `f` が 0 になります。ポーズ中に曲が進んでしまいます。クラスで `t = c + 1` とすれば、これは起きません。

**なぜ `g` のビット 7 を知っておくか.** 押すと `q` に `g + 1` が入ります。`g` のビット 7 を知らないと、抽象機械は足し算のあと `q` を知りません。最初の試みはこうなっていて、鳴っていないクラスが閉じませんでした。今は各クラスでビット 7 を知っています。ビット 1 から 6 は 0 です。

**なぜ表でなくクラスか.** [`StepWrites`](d-3-4-1-StepWrites-ja.md) の表は、抽象状態のビット `spent` を使います。土管のフレームは同じビットで土管のタイマーを追います（`rk`）。なのでここでは 6 つのバイトを状態の知っているバイトにします。

**確認の大きさ.** クラス 90、始めの状態 360、フレームの表の状態 211,898 です。確認 `pipeCheck` はプログラムで約 45 秒かかります。数秒より長いです。

## 測ったこと（定理ではない）

プログラム：`side-pause-real FM2 5 R`。部屋の 42 の状態（ブロックの上か床の上、0 から 20 フレームのあと）から横の土管まで、状態ごとに 5 回歩きます。Start はおよそ `R` フレームに 1 回、でたらめに押します。そのあと土管のフレームを、でたらめな入力と、およそ `R` フレームに 1 回の Start で進めます。参照の入口と、TAS の入口も加えます。

| `R` | 入口 | `Entry2` | `PauseE` | 入口で 鳴っていない / ポーズを解く音 / ポーズを解いた | 土管のフレーム | クラスに入る | 現れたクラス | `QuietK` の出口 |
|---|---|---|---|---|---|---|---|---|
| 7 | 212 | 212 | 212 | 66 / 136 / 10 | 66,541 | 66,541 | 89 | 212 |
| 20 | 212 | 212 | 212 | 135 / 67 / 10 | 69,051 | 69,051 | 89 | 212 |
| 60 | 212 | 212 | 212 | 162 / 49 / 1 | 69,424 | 69,424 | 89 | 212 |

TAS（`changes-check FM2`、および 380、416、450、545、575、730、845 に 60 フレームのポーズを入れたもの）では、横の土管の入口で毎回 `PauseE` が成り立ちました。380 と 416 のポーズは、この変更の前と同じく、最初の切り替えの `quiet₁` を満たしません。

## しないこと：土管のあとの Start

`chg.noStart₂`（1-1-d-3-3）は残ります。ポーズ中の行を試して測りましたが、Lean の結果はありません。ポーズするフレームは、同じ `left` のポーズ中の行へ行き、その行は自分自身と次の行へ行きます。タイマーは表に入れる必要があるので、表のルーチンを、音のルーチン、パッドの読み取り、ポーズのルーチンをまとめたものにし、タイマーとポーズのバイトを表のバイトにしました。すると、ゲームの中心までの行は 1 つ約 0.7 秒かかりました（前は 0.13 秒）。最初のポーズ中の行の探索は 10 分で終わりませんでした。その表は、曲とほかの効果音の約 255 の状態の各々に、ポーズの音とタイマーの 44 の状態をかけたものです。ポーズのあとは曲が遅れるので、そのあとの行は何フレームでも遅れた曲を持つ必要があります。これには、ポーズと曲を分けた別の形の表が要ります。

## 仮定（Lean で証明していない）

* 入口の `PauseE` はもう仮定しません。[部屋のフレームを通るポーズ](d-3-4-4-RoomPause-ja.md) が部屋で最初に操作できるときから証明します。そこでポーズのバイトのビット 1 から 6 が 0 であることは定理です（`ChangesK.pauseBits₂`、1-1-b-3-10）。
* ほかは [地上への切り替えを、音のバイトを表にして](d-3-4-2-SideChangeSound-ja.md) のとおりです：`Entry2`、`lagPaused`、土管のあとの `NoStart`、`TimerOK`。

**ファイル.** `Theorems/SidePause.lean`。private の確認は `Proof/SidePause.lean`（`Main.lean` の `genSidePause`）、`side_pause` は `Proof/Route.lean` にあります。名前 `GamePauseTimer` を `SideChangeEnd.namesOf` に加えました。

**再現.**
```
.lake/build/bin/smbrta side-pause-check            # 確認をプログラムで、約 47 秒
.lake/build/bin/smbrta side-pause-real FM2 5 20    # 実際の走りのクラス、約 30 秒（7 と 60 でも）
```
