[← Back](README-ja.md) | [English](d-3-4-4-RoomPause.md) | [Japanese](d-3-4-4-RoomPause-ja.md)

# 部屋のフレームを通るポーズ

**主張.** 部屋で最初に操作できるとき、ポーズのバイトのビット 1 から 6 が 0 だとします。すると横の土管の入口で、ポーズの音が鳴っていないか、ポーズのタイマーがその数より 1 多い状態でポーズを解く音が鳴っているか、そのフレームでポーズを解いたところです（`PauseE`）。これは部屋でのどの入力でも、Start を含めて成り立ちます。ROM の 2 つの確認つきで証明しました。そこで道筋は入口の `PauseE` をもう仮定しません。`chg.pause₂` をなくし、`chg.pauseBits₂`（部屋で最初に操作できるときの 6 ビット）が新しい仮定です（1-1-d-3-4-4）。Start を無作為に押す本物の走りで、最初の操作 195 回のすべてで 6 ビットは 0、部屋のフレーム 203,345 個のすべての始まりでポーズの 6 バイトはクラスに入り、入口 630 回のすべてで `PauseE` が成り立ちました。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は入力 `i` での `m` の 1 フレーム、`tr(j)` はその `j` 命令目の機械です。`seq(n)` はフレーム `n` が始まるときの機械です。`rt(m)` はルーチンのバイト（`GameEngineSubroutine`）、`r` は部屋の基準の機械です。`Room` と `SiteOK` は [部屋の画面のページと横の土管の長いタイマー](d-2-4-ScreenPage-ja.md) のものです。`InRowsT` は [部屋への切り替えを、音のバイトを表にして](b-3-7-1-SoundRows-ja.md) の時間の行です。ポーズの 6 バイト、90 のクラス、`PauseE` は [横の土管のフレームを通るポーズ](d-3-4-3-SidePause-ja.md) のものです。`q`、`b`、`f`、`c` はポーズの音の待ち、バッファ、フラグ、数、`t` はポーズのタイマー、`g` はポーズのバイトです。

```
InCls(m)  :=  ∃ t ∈ クラス,  m の 6 バイトは t のとおり
```

## 定理

```
pause_step      :  Room(m) ∧ (∀ j, SiteOK(tr(j))) ∧ InCls(m)
                     →  InCls(frame(m, i))  ∧  ( Room(frame(m, i))  ∨  ( rt(frame(m, i)) ≠ rt(r)  ∧  g(frame(m, i)) & 1 = 0 ) )
pause_run       :  Room(seq c) ∧ InCls(seq c),   ∀ n ∈ [c, e):  (∀ j, SiteOK(trₙ(j))) ∧ rt(seq n) = rt(r),   rt(seq e) ≠ rt(r)
                     →  InCls(seq e)  ∧  g(seq e) & 1 = 0
class_of_rows   :  InRowsT(m) ∧ ctl(m) ∧ g(m) & 0x7E = 0  →  InCls(m)
pauseE_of_class :  t ∈ クラス,  m の 6 バイトは t のとおり,  g(m) & 1 = 0  →  PauseE(m)
pauseE_run      :  c = b₁ から e = a₂ までこれらすべて  →  PauseE(seq a₂)
```

`pause_step` と `pause_run` は確認 `roomCheck`（`PauseOK`）から、`class_of_rows` は確認 `startCheck` から出ます。`pauseE_of_class` に確認は要りません。`g & 1 = 0` のクラスは `PauseE` の 3 つの種類です。

道筋では（`Route.ChangesK.pause₂`）:

```
pauseBits₂ : g(seq b₁) & 0x7E = 0                    （新しいフィールド）
Room(seq b₁)                                            （ChangesK.roomAt、前と同じ）
InRowsT(seq b₁), ctl(seq b₁)                            （最初の切り替えの行、前と同じ）
∀ n ∈ [b₁, a₂):  ∀ j, SiteOK(trₙ(j))                    （chg.roomSites、前と同じ）
∀ n ∈ [b₁, a₂):  rt(seq n) = rt(r)                       （ChangesK.roomStay: a₂ の定義）
rt(seq a₂) = e_s ≠ rt(r)                                 （ChangesK.rt₂: chg.entry₂ と確認 RoomChecks.rt）
ChangesK.pause₂ : PauseE(seq a₂)                        （定理。フィールド pause₂ だった）
```

Lean: `Theorems/RoomPause.lean`（`Reg`、`keep0`、`baseS`、`eraseKeeps`、`keepP`、`inP`、`pstep`、`Ph`、`finP`、`walkP`、`walkCheck`、`regOf`、`cfgR`、`roomCheck`、`rowP`、`startCheck`、`mem_low`、`low_of_mem`、`sim_keep0`、`s_baseS`、`keepP_ok`、`s_pstep`、`LiveP`、`cover_liveP`、`live_stepP`、`frame_of_walkP`、`InCls`、`PauseOK`、`pauseOK_of_check`、`pause_step`、`pause_run`、`pauseE_of_class`、`class_of_silent`、`class_of_rows`、`Facts`、`factsOf`、`pauseE_run`）、`Theorems/Route.lean`（`ChangesK.pauseBits₂`、`RoomChecks.pause`、`ChangesK.rt₂`、`ChangesK.pause₂`）、非公開の `room_pause_walk`、`room_pause_start`、`room_pause`（`Proof/RoomPause.lean`）。公開のファイルにゲームのデータはありません。

## しくみ

**6 バイトを書く場所.** 書くのは音のルーチン（ポーズの音と、1 つ目の矩形波の効果音による数）とポーズのルーチンだけです。割り込みの処理は、音のルーチン、パッドの読み取り、ポーズのルーチンを続けて呼びます。この 3 つの呼び出しが歩きの区間です。音のルーチンの呼び出しから、3 つ目の呼び出しのあとの場所までです。場所は ROM から読みます。`NonMaskableInterrupt` からの最初の `SoundEngine` の呼び出しと、その 9 バイトあとです。

**1 フレーム.** 歩きは [画面のページ](d-2-4-ScreenPage-ja.md) の部屋の 1 フレームの歩きに、抽象状態の外に持つ表を加えたものです。表は 90 のクラスです（`pstep`）。

* 区間の外では、どのステップも 6 バイトを保たなければなりません（`keepP`）。そのステップの抽象状態が、書き込みは 6 バイトに届かないと言える（`StepWrites.keepOK`）か、コインを消す書き込みです。コインを消す書き込みは `SiteOK` によってブロックのバッファに入り、6 バイトはそこにありません（確認ずみ）。
* 音のルーチンの呼び出しで、状態をそれと矛盾しないクラスごとの断片に分けます。断片には印をつけます（`spent`: 区間の中）。
* 区間の中のステップは部屋の歩きのステップです。各断片では 6 バイトがわかっています。
* 区間のあとの場所で、6 バイトはどれかのクラスに入らなければなりません。そのあと 6 バイトを忘れますが、ポーズのバイトのビット 0（ポーズ中かどうか）は残します（`keep0`）。印もはずします。

`Ph(A, m) := spent(A) ∨ InCls(m)`。各ステップは機械に従い、`Ph` を保ちます（`s_pstep`）。フレームの終わりで歩きは、状態が区間の外にあり、`Room` の始めの状態の下にあるか、ルーチンがわかっていて基準のものと違い、ポーズのバイトのビット 0 が 0 とわかっていることを求めます（`finP`）。

**ポーズのバイトのビット 0 を残すわけ.** 横の土管に入るフレームはゲームのルーチンを動かしたので、ポーズ中ではありません。歩きがこれを知るのは、区間のあとでこのビットがわかっているときだけです。そうすれば入口のクラスはポーズ中でない 3 つのどれかで、それが `PauseE` です。

**最初の操作.** 最初の切り替えの行は、操作できるときに次を知っています。ポーズの音の待ち、バッファ、フラグは 0 で、ポーズのバイトのビット 0 は 0 です。タイマーと、ポーズのバイトのビット 1 から 7 は知りません（状態の種類は 2 つ、操作できる状態は 14,224 個）。ポーズのバイトのビット 1 から 6 が 0 なら、ポーズのバイトは 0 か `0x80` で、機械は鳴っていない 2 つのクラスのどちらかに入ります（`class_of_silent`）。

**探索.** 表を作るのはプログラムで、確認は探索によりません。部屋の歩きの探索を 3 か所変えました。6 バイトを鍵のバイトに入れたので、違うクラスの断片は合わせません。待つ状態は鍵全体の順に並べます。[画面のページ](d-2-4-ScreenPage-ja.md) の探索は鍵を 2^200 で割った余りを使います。6 バイトを入れると場所とレジスタはビット 200 より上に来るので、違う場所の待つ状態が互いを置き換え、歩かれない状態がありました（そのとき表の歩きは終わりなく伸びました）。`Nat` は下位 64 ビットでハッシュされるので、鍵のすべてのビットをそこに混ぜます（`keyP`）。これがないと探索に 57 秒かかりました。

**確認の大きさ.** クラスは 90。探索は 529,736 ステップ、分岐 25,753、失敗 0、表は 25,264 状態です。プログラムで探索は約 3.7 秒、確認 `roomCheck` 全体は約 6.5 秒です。`startCheck` は時間の行を作り直し、プログラムで約 24 秒です。どちらも数秒を超えます。

## 測ったもの（定理ではない）

プログラム: `room-pause-real FM2 5 R`。部屋の最初の操作: 縦の土管への本物の入口 13 か所から 5 回ずつ（1 回目は入力なし、ほかは土管のフレームで `R` フレームに 1 回 Start を無作為に押す）、そのあと操作まで入力なし。各最初の操作から、Start を無作為に押す無作為な入力で 600 フレーム。横の土管の近くの 42 の状態（ブロックの上か床）から、Start を無作為に押して土管へ 5 回ずつ歩く。そのほか手本の部屋。

| `R` | 最初の操作 | 6 ビットが 0 | クラスに入る | 部屋のフレームの始まり | ポーズ中 | クラスに入る | 見たクラス | 入口 | `PauseE` | `g` のビット 0 が 0 |
|---|---|---|---|---|---|---|---|---|---|---|
| 7 | 65 | 65 | 65 | 70,253 | 38,366 | 70,253 | 89 | 210 | 210 | 210 |
| 20 | 65 | 65 | 65 | 67,505 | 34,707 | 67,505 | 89 | 210 | 210 | 210 |
| 60 | 65 | 65 | 65 | 65,587 | 32,474 | 65,587 | 89 | 210 | 210 | 210 |

最初の操作でのポーズのバイトは 0 か `0x80` でした。手本では、部屋の最初の操作で 6 ビットは 0、部屋のどのフレームもクラスに入り、入口（手本のフレーム 764）で `PauseE` が成り立ちます。

## 道筋で変わったこと

* `chg.pause₂` をなくしました。`ChangesK.pause₂` は同じ命題の定理で、`ChangesK.run₂` がそれを使います。
* `chg.pauseBits₂` が新しい: `g(seq b₁) & 0x7E = 0`。
* `RoomChecks` に新しいフィールド `pause : RoomPause.Facts`（2 つの確認）があります。`RoomChecks` は道筋と急ぎの音楽の非公開のファイルで作ります。

## 仮定（Lean で証明していないもの）

* **部屋で最初に操作できるときのポーズのバイトのビット 1 から 6**（`chg.pauseBits₂`、1-1-d-3-4-4）。新しい仮定です。ポーズのルーチンはポーズのバイトを、ビット 0 を反転してビット 7 を立てた値か、ビット 7 を消した値でしか書かないので、これらのビットはゲームの始まりのあと変わりません。これは証明していません。縦の土管の入口の条件はこれらのビットを知っています（`PipeChangeEnd.entryMasks`）が、出口の状態はポーズのバイトのビット 0 しか残しません（`SideChangeEnd.exitStarts`）。そのため部屋への切り替えの行はこれらを知りません。出口の状態がこれらを残せば、確認 `startCheck` がそれを求められ、このフィールドはなくなります。
* 部屋の各命令の `SiteOK`（`chg.roomSites`）と、最初の切り替えの行の条件（パート b）は前と同じです。

**ファイル.** `Theorems/RoomPause.lean`。非公開の確認は `Proof/RoomPause.lean`（`Main.lean` の `genRoomPause`）。

**再現.**
```
.lake/build/bin/smbrta room-pause-check -r                # 歩きの確認、行の操作できる状態の 6 バイト、startCheck。約 35 秒
.lake/build/bin/smbrta room-pause-real FM2 5 20           # 本物の走りでのクラス。約 22 秒（7 と 60 でも）
.lake/build/bin/smbrta room-pause-walks 20000             # 表の各状態からの歩きを、ステップの上限つきで
```
