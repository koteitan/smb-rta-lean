[← Back](README-ja.md) | [English](d-2-3-SideChangeEnd.md) | [Japanese](d-2-3-SideChangeEnd-ja.md)

# 地上への切り替えの最後のフレーム

**主張.** これは部分的な結果です。出口の 1 つの状態についての条件を満たす機械は、次の 121 フレームのあいだ操作できません。入力は、ゲームコアのフレームで Start を押さないものなら何でもかまいません。切り替えのはじめのフレームと合わせると、仮定 `fallAfter` がなくなります。そのような入力の走りは、入ってから操作できるまで、数えるフレームで 282 以上かかります。

`m₀`、`run`、`ctl`、`0^k`、`E`、`T = run(E, 0^160)` は[地上への切り替えの長さを決めるもの](d-2-1-SideTransitionAll-ja.md)と同じです。`EntryCond`、`During`、`left`、`frame(m, i)` は[地上への切り替えのはじめのフレーム](d-2-2-SideChangeBound-ja.md)と同じです。`m[b]` は `m` のバイト `b` です。

**出口の条件.** `ExitCond(m)` は、フレームの終わりの状態 `m` についての条件です。

* フレームは待ちの繰り返しの中で終わっています。プログラムカウンタとスタックポインタは `T` と同じです。ドットは 9 以下です。vblank と NMI のフラグはドットに合っています。スプライト 0 のフラグは立っています。PPU 制御で NMI はオンです。コントローラはストローブ中ではありません。
* 29 バイトの `Kx` は `T` と同じ値です。下に挙げます。
* ゲームはポーズしていません。`GamePauseStatus` の下のビットは 0 です。

ほかのバイトは何でもかまいません。マリオの `x`、大きさ、状態、速さ、コイン、スコア、ゲームタイマーの数字、フレームカウンタ、インターバルタイマー、乱数、音のポーズのフラグ `PauseModeFlag`、音の状態の残り、スプライト、一時的なバイトです。

**リスト `Kx`**（名前）:

| まとまり | バイト |
|---|---|
| モード | `OperMode`、`OperMode_Task`、`GameEngineSubroutine`、`ScreenRoutineTask`、`DisableScreenFlag`、`Sprite0HitDetectFlag` |
| 面 | `WorldNumber`、`AreaNumber`、`AreaPointer`、`EntrancePage`、`AltEntranceControl`、`PrimaryHardMode`、`CurrentPlayer`、`JoypadOverride`、`GameTimerExpiredFlag` |
| 画面 | `VRAM_Buffer1`、`VRAM_Buffer_AddrCtrl` |
| 音 | `NoiseSoundBuffer`、`AreaMusicBuffer`、`EventMusicBuffer`、`MusicData`（2）、`MusicOffset_Square1`、`NoteLengthTblAdder`、`AreaMusicQueue`、`EventMusicQueue`、`NoiseSoundQueue` |
| 音のポーズ | `PauseSoundBuffer`、`PauseSoundQueue` |

**`During` の終わりがこの条件にどうつながるか.** `Entry2(M)` は `EntryCond(M)` と、さらに 8 バイト `X` が `E` と同じ値であることです。`AreaPointer`、`EntrancePage`、`CurrentPlayer`、`JoypadOverride`、`GameTimerExpiredFlag`、`AreaNumber`、`PrimaryHardMode`、`NoteLengthTblAdder` です。`During2(m)` は、これらのバイトも知っている `During(m)` です。土管のフレームがこれらを変えないことは確認が示します。タイマーが切れるフレームは、音のポーズの 2 バイトを除く `Kx` の全部と、`GamePauseStatus` の下のビットを出します。`Quiet(m)` は、その 2 バイトが `T` の値（0）であることです。Start を押すと、ポーズの音が鳴るあいだこれらは変わります。`Quiet` は証明していません。出口の状態についての仮定です。

`NoStart(m, i)` は、`m` がゲームコアで土管以外のルーチンなら入力 `i` に Start がないことです。`InRows(m)` は、`m` が下の段の抽象状態のどれかに含まれることです。

```
entry      :  ∀ M,  Entry2(M) → EntryCond(M)
during     :  ∀ M,  Entry2(M) → During2(M)
toDuring   :  ∀ m,  During2(m) → During(m)
step       :  ∀ m, During2(m) → ∀ i :  During2(frame(m, i))  ∨  ( Exit(frame(m, i))  ∧  ( Quiet(frame(m, i)) → InRows(frame(m, i)) ) )
atExit     :  ∀ m,  ExitCond(m) → InRows(m)
leftExit   :  ∀ m,  ExitCond(m) → left(m) = 122
rows       :  ∀ m, InRows(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRows(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
no_control_exit :  ExitCond(s₀)  ∧  (∀ n, s₍ₙ₊₁₎ = frame(sₙ, iₙ)  ∧  NoStart(sₙ, iₙ))  →  ∀ j < 122, ¬ctl(sⱼ)
EndRun.fall     :  `EndRun` のフィールドを持つ走りの、はじめて left = 0 になるより前のフレームで :  left(seq n) ≤ left(seq (n+1)) + 1
EndRun.bound    :  `EndRun` のフィールドを持つ走りについて :  cnt(a) + 282 ≤ cnt(b)
```

`Exit(m)` は、はじめのフレームのページと同じです。`EndRun` のフィールドは `ChangeRun` のフィールドから `fallAfter` を除いたものです。入るときの条件は `Entry2` です。`noStart` と `quiet` が増えます。`lagKeeps` は残ります。

Lean: `Theorems/SideChangeEnd.lean`（`s_xtick`、`s_xbr`、`s_xstep1`、`xframe_of_walk`、`link_frame`、`chain_step`、`exit_cover`、`during_step`、`EndStatement`、`endStatement_of_check`、`no_control_exit`、`EndRun`、`EndRun.fall`、`EndRun.bound`）、非公開の `side_end_checks`（`native_decide`）、`side_end`、`side_exit_no_control`、`side_change_end`。

## しくみ

**フレームの終わりをまたぐ時間.** 土管のあとのフレームは RAM を消し、その繰り返しの中でフレームが終わります。[はじめのフレーム](d-2-2-SideChangeBound-ja.md)の抽象機械はここで失敗します。`xtick` は時間の進め方に 3 つの場合を足します。フレームの最初のドット、フレームの終わり、ドットの区間が vblank フラグの消える時刻の両側にあるときです。フレームの終わりでは状態は 3 つまでに分かれます。フレームが続く、ドット 0 で終わる、もっと先のドットで終わる、です。分岐命令もまたぐことがあります（`xbr`）。`xtick` と `xbr` は `tick` と `branch` に対して証明してあります（`s_xtick`、`s_xbr`）。

**RAM を消すフレーム.** 出口の状態からは、消す繰り返しに着くときのドットは区間でしかわかりません。音のルーチンの時間が、わからないバイトで変わるからです。ですから、フレームが終わる場所は繰り返しの中に 1,904 か所あります（フラグが 0 でなければ 774 か所）。どの場所でも `left` のキーはその段の値です。繰り返しは `ScreenRoutineTask` を消し終え、`GameEngineSubroutine` にはまだ着いていません。次のフレームはこれらすべての場所から始まります。探索は繰り返しの回の順に進むので、道は 1 つにまとまります。このフレームは 6,905 ステップです。

**段.** 消したあとは 2,048 バイトのうち 1,769 バイトがわかっています。消されないバイトは `ExitCond` から来るか、自由です。1 フレームは 1 つの段の状態から次の段の状態へ進みます。全部で 123 段で、`left` は 122 から 0 まで減ります。最後の段には、操作できる状態と、タイムアップの道の状態があります。ゲームタイマーの数字が自由だからです。どちらも `left` は 0 です。

**音のポーズのフラグの 2 つの場合.** RAM を消しても `PauseModeFlag` は変わりません。0 でなければ、次に Start を押すまで音のルーチンは動かず、曲も始まりません。ですから段は 2 組あります。2 組目は、フラグが 0 でないという事実（`dg`）を使います。

**確認の大きさ.**

| フレーム | 抽象ステップ |
|---|---|
| 土管の 1 フレーム、タイマー ≥ 2 | 106,156 |
| 土管の 1 フレーム、タイマー = 1 | 90,308 |
| 段、フラグ 0 | 682,944 |
| 段、フラグ 0 でない | 691,797 |

プログラムで約 5 秒、非公開の証明のビルドで約 13 秒です。

## Start を除く理由

ゲームコアのフレームで Start を押すとゲームはポーズします。ポーズの音が鳴るあいだ曲は止まり、ゲームは止まりません。ですからポーズのあと、曲はゲームから何フレームでも遅れます。段と遅れの組ごとに状態が要ります。その段にとどまるフレームと先へ進むフレームをまとめると、曲のポインタと位置がわからなくなります。Start を許すと、確認はゲームコアの最初のフレームで失敗します。音楽のルーチンで 4 回の失敗です（23,695 ステップ）。ですから、これは証明していません。

## 測ったけれど定理にしていないこと

`Entry2` を満たす入る状態です。`E`、TAS の入る状態、`side-all-real` の本物の 42 個、乱数の走り 21 個、大きいマリオで始めた乱数の走り 7 個です。それぞれから 5 種類の入力で動かしました。

| 入力 | 走り | フレーム | 出口で `Quiet` が成り立たない | `ExitCond` が成り立つ | 出口のあとで `left` がちょうど 1 減らないフレーム | `left` が 2 以上減るフレーム | いちばん短い切り替え |
|---|---|---|---|---|---|---|---|
| なし | 72 | 20,304 | 0 | 72 | 0 | 0 | 282 |
| 乱数、Start なし | 72 | 20,304 | 0 | 72 | 0 | 0 | 282 |
| 乱数、Start ははじめの 80 フレームだけ | 72 | 23,774 | 0 | 72 | 0 | 0 | 327 |
| 乱数、Start は土管のフレームだけ | 72 | 34,132 | 71 | 1 | 0 | 0 | 424 |
| 乱数、Start はすべてのフレーム | 72 | 40,994 | 72 | 0 | 数えていない | 0 | 519 |

* `T` の自由なバイトをすべて乱数で書き換えた状態を 300 個、半分は Start なしの乱数入力で動かしました。すべて `ExitCond` を満たし、すべてちょうど 122 フレームで操作できます。ほとんどは音のポーズのフラグが 0 ではありません。`Quiet` を満たす本物の走りで、このフラグが 0 でないものはありませんでした。
* ゲームタイマーの数字を 100 の近くに書き換えた乱数の走りでは、5 個のうち 4 個が `EntryCond` を満たし、`Entry2` を満たすものはありません。急ぎの音楽が `NoteLengthTblAdder` を変えています。そのような走りは 1748 フレームよりずっと多く使っています（タイマーの計算で、Lean にしていません）。
* `ChangeRun` の `fallAfter` は成り立たない状態があります。`E` でゲームタイマーを 000 に書き換えると `EntryCond` は成り立ち、フレーム 800 で操作できるまでに、`left` が 2 以上減るフレームが 4 個あります（たとえば 116 から 0）。ですから `EndRun.fall` ははじめての `left = 0` までで止まり、`EndRun.bound` はそのあとのフレームを使いません。
* 出口のあとでタイマーが動かないフレームは、RAM を消すフレームの次のフレームだけです。`Frames` の `setup` のフレームです。これは 1 つの走りで 1 個という数からの読みです。

**縦の土管の最後のフレーム.** 同じ道具で地下への切り替えを測りました。

| 始まり | 知っているバイト | 結果 |
|---|---|---|
| 出口、フレーム 48 | 横の土管のリスト `Kx` と `X`、その出口の値 | RAM を消すフレームで失敗します。149 回の失敗です。曲が鳴っていて、そのポインタがわかりません。ここは走りによって違います |
| 同じ、フラグ 0 でない | 同じ | RAM を消すフレームは通ります（21,781 ステップ）。次のフレームは失敗します。まとめた状態のドットが 0 から 10,254 までになり、時間の進め方にこの場合の規則がありません |
| フレーム 50 | 消されるバイトの全部と、消されないバイトの全部 | フラグの 2 つの場合とも通ります。41 段、約 148,000 ステップ、プログラムで 100 ミリ秒です |

ですから、段はフレーム 50 からの最後の 41 フレームに使えます。フレーム 50 の状態と RAM を消す 2 フレームには、曲についての事実が要ります。

## 前提（Lean では証明していない）

* 本物の走りの入る状態での `Entry2`、または出口での `ExitCond`。バイト `X` はコードから読みました。部屋が準備されたあと、部屋の中で書くものはありません。`NoteLengthTblAdder` は急ぎの音楽のあとは成り立ちません。項目 1-1-d-2-5 です。
* `Quiet`。出口でポーズの音が鳴っていないことです。測った走りでは、土管の最後のほうのフレームで Start を押すと成り立ちません。そのような走りでも `left` はちょうど 1 ずつ減ります。これは測っただけです。
* `NoStart`。土管のあとのゲームコアのフレームで Start を押さないことです。
* `lagKeeps`。`lag` のフレームが `left` を減らさないことです。段ではどのフレームも次の段へ進みます。ですから `lagKeeps` は、段のフレームが `lag` でないことを言います。`lag` と本物のフレームのつながりは `Route` にあります。項目 1-1-d-3-2 です。
* [1-1 全体](0-1-Route-ja.md) はこの定理を使います。`Changes.run₂` は `EndRun` です。

**ファイル.** `Theorems/SideChangeEnd.lean`、非公開の `Proof/SideChangeEnd.lean`。

**再現.**
```
.lake/build/bin/smbrta side-end-check FM2    # 確認、本物の入る状態と出口での条件、本物のフレームでの left、約 20 秒
```
