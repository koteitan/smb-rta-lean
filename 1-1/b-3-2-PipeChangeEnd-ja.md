[← Back](README-ja.md) | [English](b-3-2-PipeChangeEnd.md) | [Japanese](b-3-2-PipeChangeEnd-ja.md)

# `fall` なしの部屋への切り替え

**主張.** これは部分的な結果です。走りが、入るときの状態についての条件、土管のフレームのいくつかの場所での条件、出口での条件を満たすとします。さらに、土管のあとのゲームコアのフレームで Start を押さないとします。すると、入ってから操作できるまで、数えるフレームで 91 以上かかります。これで[ルート全体](0-1-Route-ja.md)から仮定 `fall₁` がなくなります。`Changes` には代わりにフィールド `places₁`、`quiet₁`、`noStart₁` が入ります。入るときの条件 `Entry` は、いまはその一部をタイトルで Start を押したことと操作できるときからのフレームから出します。[縦の土管に入るときの状態を、タイトルから出す](b-3-4-EntryKeep-ja.md)を見てください。`keep₁` もなくなりました。[部屋への切り替えの `lag` のフレーム](b-3-3-LagPaused-ja.md)を見てください。さらに出口で時間が切れておらず（`TimeOK`）、`b` が入ったあと最初の操作なら、操作の前に `left` は 0 になりません（`PipeRun.first`）。操作のときの機械は時間の段の中にあります（`PipeRun.inRowsT`）。これでルートから `first₁` がなくなります。`Changes` には代わりに `time₁` と `ctlFirst₁` が入ります（項目 1-1-b-3-9）。ルートはいま、音のバイトを表で運ぶ段を使い、出口でもっと弱い条件を求めます。[音のバイトを表で運ぶ、部屋への切り替え](b-3-7-1-SoundRows-ja.md)を見てください。そこでは、このページの時間の段を `InRowsTO` と呼び、`InRowsT` は表を運ぶ段で `left` が 0 のものです。

`m₀`、`run`、`ctl`、`0^k`、`E` は[地下への切り替えの長さを決めるもの](b-2-1-PipeTransitionAll-ja.md)と同じです。`left` は[1 フレームずつの事実から出す下限](b-2-2-PipeChangeBound-ja.md)と同じです。土管のルーチンが動くあいだは `timer + 43` で、そのあとは 43 行の表から読みます。`frame(m, i)` は `m` から入力 `i` で進む 1 フレームです。`trace(m, i, j)` はそのフレームを `j` ステップ進めた機械です。`T = run(E, 0^48)` は出口の基準です。`m[b]` は `m` のバイト `b` です。`+k` のついた名前は、その名前の `k` バイトあとのバイトです。`Paused(m)` は、`GamePauseStatus` の最下位ビットが立っていることです。`m[GamePauseStatus] & 1 = 1` です。`TimeOK(m)` は時間が切れていないことです。`m[PauseModeFlag] = 0 ∧ (m[GameTimerDisplay], m[GameTimerDisplay+1], m[GameTimerDisplay+2]) ≠ (0, 0, 0)` です。

**入るときの条件.** `Entry(M)` は、入るフレームの終わりの状態 `M` についての条件です。

* フレームは待ちの繰り返しの中で終わっています。[地上への切り替えのはじめのフレーム](d-2-2-SideChangeBound-ja.md)と同じです。プログラムカウンタとスタックポインタは `E` と同じです。ドットは 9 以下です。vblank と NMI のフラグはドットに合っています。スプライト 0 のフラグは立っています。PPU 制御で NMI はオンです。コントローラはストローブ中ではありません。
* 97 バイトの `K` は `E` と同じ値です。下に挙げます。
* 12 バイトは、マスクのビットが `E` と同じです。下に挙げます。

12 回目: 19 バイトが `K` とマスクから出ました（前は 115 と 13）。土管のフレームの歩きがそれらを使わないからです（`PipeChangeEnd.entryDropped`）。[縦の土管に入るときの状態を、タイトルから出す](b-3-4-EntryKeep-ja.md)を見てください。
* `timer(M) ≥ 48`。

ほかのバイトは何でもかまいません。マリオの位置、速さ、大きさ、スコア、コイン、ゲームタイマーの数字、フレームカウンタ、乱数、曲、スプライト、画面のバッファ、面のパーサー、スロットにいる敵です。

**リスト `K`**（名前）:

| まとまり | バイト |
|---|---|
| ゲーム | `WorldNumber`、`PrimaryHardMode` |
| モード | `OperMode`、`OperMode_Task`、`GameEngineSubroutine`、`ScreenRoutineTask`、`DisableScreenFlag`、`JoypadOverride` |
| 面 | `AreaPointer`、`EntrancePage`、`AltEntranceControl`、`HalfwayPage`、`WarpZoneControl`、`CurrentPlayer`、`AreaType`、`CloudTypeOverride`、`ScrollThirtyTwo+1`、`VerticalScroll` |
| タイマー | `GameTimerExpiredFlag`、`StarInvincibleTimer`、`WorldEndTimer` |
| 入力 | `Left_Right_Buttons` |
| 空のままのスロット | `Enemy_Flag+4` … `+6`、`Enemy_ID+3` … `+6`、`Enemy_State+4`、`Fireball_State`（2）、`Block_State`（4）、`Block_RepFlag`（2）、`Misc_State`（9）、`Misc_Y_Position+7`、`Misc_Collision_Flag+10` … `+12`、`FloateyNum_Control`（7）、`FirebarSpinSpeed+14`、`+15`、`MaximumRightSpeed+18`、`+19`、`SprDataOffset_Ctrl+1`、`Cannon_PageLoc`（6）、`Cannon_X_Position`（6）、`Cannon_Y_Position`（5）、`FireballCounter`、`VineFlagOffset`、`FlagpoleFNum_YMFDummy`、`FlagpoleScore` |
| 敵のデータ | `EnemyData`、`EnemyDataHigh`、`EnemyObjectPageSel`、`EnemyFrenzyBuffer`、`EnemyFrenzyQueue`、`SecondaryHardMode` |
| 音 | `NoiseSoundBuffer`、`AreaMusicBuffer`、`EventMusicBuffer`、`AreaMusicQueue`、`EventMusicQueue`、`NoiseSoundQueue`、`Square1SoundQueue+1` |

**マスクつきのバイト.**

| バイト | 自由なビット | 許すもの |
|---|---|---|
| `Enemy_ID`（はじめの 3 スロット） | ビット 1、2 | いくつかの敵の種類 |
| `Enemy_State`（はじめの 4 スロット） | ビット 0 | |
| `Square1SoundQueue` | ビット 4 | 1 つの音 |
| `SprDataOffset_Ctrl` | ビット 0 | |
| `PlayerStatus` | ビット 0 | 小さいマリオか大きいマリオ。ファイアマリオは `Entry` を満たしません |
| `GamePauseStatus` | ビット 0、7 | |
| `AreaMusicBuffer_Alt` | ビット 2 | 覚えている曲のうち地下の曲 |

**場所.** `Places(t)` はこう言います。`t` のプログラムカウンタが下の場所のどれかなら、`t` のドットはその上限以下で、`t` はその場所の行のどれか 1 つと同じ値を持ちます。

| 場所 | 行 | ドットの上限 |
|---|---|---|
| `NonMaskableInterrupt` | 画面のバッファの形 1,061 個。各レコードの最初のバイトと長さ | なし |
| `MusicHandler` | 曲の行 1,607 個 | なし |
| `EnemyGfxHandler`、`PlayerGfxHandler` | スプライトの位置の行 3 個 | なし |
| `UpdScrollVar` | 面のパーサーの行 67 個 | 50,000 |
| `ColorRotation` | `VRAM_Buffer1_Offset` の 256 の値すべて | 上限なし |
| `HandleEToBGCollision` のブロックのバッファへの書き込み | なし。着かない | |
| `PositionEnemyObj` の最初の `BCS` のあと | なし。着かない | |
| `CheckRightExtBounds` の最初の `BCC` のあと | なし。着かない | |

つまり土管のフレームでは、突き上げられているブロックの上に敵は立っていません。面のデータの次の敵は読み込まれません。フレームはドット 50,000 より前にパーサーの場所に着きます。曲、画面のバッファ、スプライトの位置、面のパーサーは行のどれかにあります。1 フレームは 89,342 ドットです。

**出口の条件.** `ExitAt(m)` は、`OperMode_Task`、`ScreenRoutineTask`、`GameEngineSubroutine`、`DisableScreenFlag` が `T` と同じ値であることです。そのような状態で、走りは次を満たします。

* `Quiet(m)`: `PauseSoundBuffer`、`PauseSoundQueue`、`Square1SoundBuffer`、`Square2SoundBuffer` は `T` と同じ値です。`NoiseSoundBuffer` と `VRAM_Buffer_AddrCtrl` も同じ値ですが、走りがそれを言う必要はありません。確認が出口のフレームでそれを証明します。`NoiseSoundBuffer` は `K` にあり、土管のフレームはこれを変えません。NMI は `VRAM_Buffer_AddrCtrl` を 0 にし、出口のフレームは土管のルーチンのあとでゲームエンジンを動かしません。
* `Song(m)`: 曲の 12 バイト（`MusicData`（2）、4 つの位置、`NoiseDataLoopbackOfs`、音符のカウンタとバッファ）は 1,607 行のどれかと同じ値です。曲の部分が終わるフレームでは `GroundMusicHeaderOfs` も行に入ります。
* `Shape(m)`: 1 つ目の画面のバッファは空か、パレットの 4 バイトのレコードを 1 つだけ持ちます。

`Exit(m)` は、[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md)の `ExitCond(m)` に出口の 21 バイトと 6 バイト `PauseSoundBuffer`、`PauseSoundQueue`、`Square1SoundBuffer`、`Square2SoundBuffer`、`NoiseSoundBuffer`、`VRAM_Buffer_AddrCtrl` を `T` の値で入れたものと、`PlayerStatus`（ビット 1〜7）と `AreaMusicBuffer_Alt`（ビット 2 を除く全部）のビットが `T` と同じであることと、`Song(m) ∧ Shape(m)` です。出口の 21 バイトは `OperMode`、`OperMode_Task`、`GameEngineSubroutine`、`ScreenRoutineTask`、`DisableScreenFlag`、`AreaPointer`、`EntrancePage`、`AltEntranceControl`、`HalfwayPage`、`CurrentPlayer`、`JoypadOverride`、`GameTimerExpiredFlag`、`AreaMusicBuffer`、`EventMusicBuffer`、`AreaMusicQueue`、`EventMusicQueue`、`Square1SoundQueue`、`Square2SoundQueue`、`NoiseSoundQueue`、`WorldNumber`、`PrimaryHardMode` です。`Quiet`、`Song`、`Shape` のほかは、土管のフレームの歩みが `Entry` から出します。

`NoStart(m, i)` は、`m` がゲームコアで土管以外のルーチンなら入力 `i` に Start がないことです。

**主張の形.** `During(m)` は、`m` が土管のフレームの抽象的な始まりの状態のどれかに含まれることです。`InRows(m)` は、`m` が下の段のどれかの状態に含まれることです。`InRowsTO(m)` は、時間の段について同じことです。

```
during     :  ∀ M,  Entry(M) → During(M)
atEntry    :  ∀ M,  Entry(M) → 91 ≤ left(M)
inRoutine  :  ∀ m,  During(m) → m では土管のルーチンが動く
step       :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                left(m) ≤ left(frame(m, i)) + 1  ∧
                ( During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( frame(m, i) で Quiet ∧ Song ∧ Shape  →  InRows(frame(m, i)) ) ) )
atExit     :  ∀ m,  Exit(m) → InRows(m)
leftExit   :  ∀ m,  Exit(m) → left(m) = 43
rows       :  ∀ m, InRows(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRows(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
atControl  :  ∀ m,  ctl(m) → left(m) = 0
paused     :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) → Paused(frame(m, i)) → left(m) ≤ left(frame(m, i))
rowsGo     :  ∀ m,  InRows(m) → ¬Paused(m)
stepT      :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
                During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( frame(m, i) で Quiet ∧ Song ∧ Shape ∧ TimeOK  →  InRowsTO(frame(m, i)) ) )
rowsT      :  ∀ m, InRowsTO(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  InRowsTO(frame(m, i))
zeroT      :  ∀ m,  InRowsTO(m) → left(m) = 0 → ctl(m)

no_control_exit :  Exit(s₀)  ∧  (∀ n, s₍ₙ₊₁₎ = frame(sₙ, iₙ)  ∧  NoStart(sₙ, iₙ))  →  ∀ j < 43, ¬ctl(sⱼ)
PipeRun.bound   :  下のフィールドを持つ走り  →  cnt(a) + 91 ≤ cnt(b)
Changes.bound₁  :  e₁ + 91 ≤ c₂
PipeRun.first   :  下のフィールドを持つ走り  ∧  time  ∧  ctlFirst  →  ∀ n, a ≤ n < b,  left(seq n) ≠ 0
PipeRun.inRowsT :  同じ  →  InRowsTO(seq b)
ChangesK.first₁ :  ∀ n, a₁ ≤ n < b₁,  left(seq n) ≠ 0        （Changes.ctlFirst₁ での b-3-7-1 の PipeRunK.first）
```

`PipeRun` のフィールドです。`Changes` の 1 つ目の切り替えのフィールドも同じです（ただし `atCtl` は定理 `Changes.ctl₁` です）。

```
entry    :  Entry(seq a)
atCtl    :  ctl(seq b)
lagPaused:  ∀ n, a ≤ n < b,  lag(n)  →  Paused(seq (n+1))
places   :  ∀ n, a ≤ n < b,  seq n で土管のルーチンが動く  →  ∀ j, Places(trace(seq n, inp n, j))
quiet    :  ∀ n, a ≤ n ≤ b,  ExitAt(seq n)  →  Quiet(seq n) ∧ Song(seq n) ∧ Shape(seq n)
noStart  :  ∀ n, a ≤ n < b,  NoStart(seq n, inp n)
```

`PipeRun.first` にはさらに次が要ります（`Changes` ではフィールド `time₁` と定理 `Changes.ctlFirst₁`）。

```
time     :  ∀ n, a ≤ n ≤ b,  ExitAt(seq n)  →  TimeOK(seq n)
ctlFirst :  ∀ n, a ≤ n < b,  ¬ctl(seq n)
```

`cnt` は `lag` でないフレームを数えます。`left` は入ってから操作できるまで、どのフレームでも高々 1 しか減らず、操作できるときは 0 です。`lag` のフレームはポーズの状態で終わり、そのとき `left` は減りません（[b-3-3](b-3-3-LagPaused-ja.md)）。ですから `91 ≤ left(seq a) ≤ cnt(b) − cnt(a)` です。`PipeRun.first` では、帰納法で、入ってから `b` までのどの機械も土管のフレームか時間の段の中にあります。その段で `left` が 0 になるのは操作できるときだけで（`zeroT`）、`b` より前に操作はありません。

Lean: `Theorems/PipeChangeEnd.lean`（`cov_place`、`cov_zsplit`、`s_zsuccs`、`zlive_step`、`zframe_run`、`zframe_of_walk`、`z_step`、`in_rows`、`in_rowsT`、`exit_base`、`EndStatement`、`endStatement_of_check`、`PipeRun`、`PipeRun.bound`、`during_left`、`PipeRun.timeWay`、`PipeRun.first`、`PipeRun.inRowsT`、`no_control_exit`）、`Theorems/Route.lean`（`Changes.run₁`、`Changes.bound₁`、`Changes.first₁`）、非公開の `pipe_end_checks`（`native_decide`）、`pipe_end`、`pipe_exit_no_control`、`pipe_change_end`。ROM なしの定理は `propext`、`Classical.choice`、`Quot.sound` だけを使います。

## しくみ

**土管のフレーム.** 曲、画面のバッファ、スプライトの位置、面のパーサーが自由だと、[地上への切り替えのはじめのフレーム](d-2-2-SideChangeBound-ja.md)の抽象機械はここで失敗します。道が多すぎるからです。そこで主張は `Places` を求め、抽象機械はそれを使います。場所に着いた状態は、行ごとに 1 つの状態に分かれます（`placeSplit`）。どの行にも合わない状態は先へ進みません。本物の機械はそこでどれかの行に合うので、これは正しいです（`cov_place`）。わからないビットが 4 つ以下の値を通して読み書きする命令は、そのビットの値ごとに状態を分けます（`zsplit`）。`JumpEngine` でのアキュムレータ、間接の読み書きでのポインタの下のバイト、添字つきの書き込みでの `X` か `Y` です。`s_zsuccs` はこれらのステップを本物のステップに対して証明します。`zframe_run` は本物のフレームを `trace` で 1 ステップずつ追います。どのステップでも、歩みの状態のどれかが機械を含みます。

**フレームの確認.** `Entry` の始まりの状態から、探索が状態の表を作ります。確認は表の各状態から歩きます。表の場所で着いた状態は、表のどれかの状態に含まれます。フレームの終わりは、また始まりの状態のどれかに含まれるか、出口です。

| フレーム | 探索のステップ | 表の状態 |
|---|---|---|
| タイマー ≥ 2 | 902,238 | 36,062 |
| タイマー = 1 | 527,799 | 23,135 |

探索は、いくつかの場所で状態をほかが終わるまで待たせ、そこでいくつかのバイトを忘れます。これは表を小さくするだけです。確認はこれに頼りません。`GamePauseStatus` の最下位ビットは探索のキーに入ります（[b-3-3](b-3-3-LagPaused-ja.md)）。

**出口のあと.** フレーム 48 が出口です。フレーム 49 と 50 は RAM を消し、消す途中でフレーム 49 が終わります。そのあと 41 フレームで操作できます。これらのフレームには[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md)の段を使います。`PauseModeFlag` の 2 つの場合があります。

* フラグ 0: 画面のバッファの形と曲の行の組ごとに 1 つの状態で、6,428 個です。どれも 1 つずつ、音のルーチンのあとの場所まで進みます。そこで 32 個に 1 個を、曲のバイトを除いてまとめ、そこから探索を続けます。確認は 6,428 個すべてから歩きます。
* フラグ 0 でない: 音のルーチンは動きません。形ごとに 1 つの状態で、1 つずつ同じ場所まで進みます。

どちらの場合も 44 段で、`left` は 43 から 0 まで減ります。

**時間の段.** フラグ 0 の場合の最後の段には、操作できる状態と、時間が切れた状態があります。そこではゲームのタイマーの数字が自由だからです。時間の段は、この場合の段で、`dg` が 3 つの数字は全部 0 ではないことを表すものです。[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md)と同じです。数字にビット 1 を知る状態は、フレームの終わりで `dg` を取り戻します（`normD`）。`dg` のある状態とない状態はまとめません。入口の準備は `FetchNewGameTimerFlag` でタイマーを読み込むことがあるので、探索はこのフラグを分けておきます。44 段、8,118 個の状態です。最後の段の状態は 2 個で、どちらも操作できます（`zeroCtl`）。この 2 個では、部屋の条件 `Room` のビットがすべて参照と同じに知られています（[d-2-4-1](d-2-4-1-ScreenStart-ja.md)）。

**場所の行.** 行は基準の走りのフレームから作ります。`E` を入力なしで 47 フレーム、`E` で `Player_X_Scroll` を 3、タイマーを 230 にして 225 フレーム、[b-2-1](b-2-1-PipeTransitionAll-ja.md) の本物の 13 個の入る状態をそれぞれ 47 フレーム、それに `m₀` から `E` までの道のフレームです。道のフレームからは、`E` の近くのパーサーの列の始まりだけを使います。列の始まりでは、パーサーはメタタイルのバッファを読む前に消します。ですから、その行ではメタタイルのバッファは自由です。画面のバッファの形には、見えたレコードの最初のバイトと長さ 1 から 8 で作った、レコード 2 つまでのすべての形を足します。曲の行は、`m₀` から入力なしで 5,327 フレーム鳴らした曲です。曲は始めの 143 フレームのあと、5,184 フレームの周期です。

**確認の大きさ.** 負荷のある機械のプログラムで約 49 秒です。そこで時間の段のない同じ確認は 36 秒でした。非公開の証明のビルドでは 57 秒 です。

## 正しくない事実

* `fall₁` は、[1 フレームずつの事実から出す下限](b-2-2-PipeChangeBound-ja.md)の条件を満たす状態で正しくないことがあります。`E` で `HalfwayPage` を 1 にすると、75 フレームで操作でき、フレーム 73 で `left` は 18 から 0 になります。`WarpZoneControl` を 1 にすると 228 フレームで操作でき、フレーム 55 で `left` は 36 から 0 になります。`GameTimerExpiredFlag` を 1 にすると 229 フレームで操作でき、フレーム 54 で `left` は 37 から 0 になります。これらのバイトは `K` にあるので、これらの状態は `Entry` を満たしません。入力なしで測りました。
* 土管のフレームで Start を押すと、本物の走りで `Quiet` は正しくありません。下では、土管のフレームで乱数の Start を使った 437 の走りのうち 129 で成り立ちません。この走りでは 6 バイトを求めていました。いまの 4 バイトでも `pipe-end-check` は同じで、土管のフレームで Start を押す 15 の走りのうち 6 で成り立たず、Start なしでは 0 です。

## 測ったけれど定理にしていないこと

**出口の時間.** `pipe-end-check` では、`E`、TAS の入る状態、本物の 13 個から 3 種類の入力で、出口の条件を満たす出口はどれも `TimeOK` で、操作の前に `left` が 0 になるフレームはありません。`room-start-check` の 615 回の走りと、`changes-check` の TAS でも同じです。`E` でゲームのタイマーを 000 に書いて入力なしで動かすと、出口で `TimeOK` は成り立ちません。フレーム 91 で `left` が 0 になり、そこでのルーチンは死ぬルーチンで、操作できません。001 なら、フレーム 91 で操作できます。だから `time₁` が要ります。

**入る状態.** 下の表は、`WorldNumber`、`PrimaryHardMode`、`AreaMusicBuffer_Alt` のビットを `Entry` に足す前に測りました。足したあと、`Entry` は `pipe-end-check` の 15 個の入る状態と TAS（`changes-check`）で成り立ちます。

入る状態は、`E`、TAS の入る状態、本物の 13 個、それに `m₀` からの自分の走りの 422 個です。自分の走りは、土管まで乱数で遊ぶものです。ふつう、踏みつけあり、大きいマリオで始める、大きいマリオで踏みつけあり、1,000、2,500、4,000 フレーム待ってから、`x` = 980 を越えてから戻る、です。種の違う 2 組があります。それぞれの入る状態から、3 種類の入力で操作できるまで動かしました。

| 入力 | 走り | `Entry` が成り立つ | 土管のフレーム | `Places` に反するフレーム | 出口で `Quiet ∧ Song ∧ Shape` | `left` が 2 以上減るフレーム | 操作できるまでの最少フレーム |
|---|---|---|---|---|---|---|---|
| なし | 437 | 437 | 20,976 | 0 | 437 | 0 | 91 |
| 乱数、Start なし | 437 | 437 | 20,976 | 0 | 437 | 0 | 91 |
| 乱数、土管のフレームでだけ Start | 437 | 437 | 48,044 | 0 | 308 | 0 | 136 |

`Song ∧ Shape` は、どの種類でも 437 の出口すべてで成り立ちました。成り立たなかったのは `Quiet` だけで、Start のあるときだけです。この走りでは、そのときの `Quiet` の 6 バイトを求めていました。いま求める 4 バイトは、6 バイトが成り立つところでは成り立ちます。パーサーの列の始まりの行を足す前は、ふつうの走りの 1,920 フレームのうち 11 フレームが `Places` に反していました。

## 仮定（Lean では証明していない）

* 本物の走りの入る状態で `Entry`。項目 1-1-b-3-4。もうフィールドではありません。`Run.entry₁` が、タイトルで Start を押したこと、操作できるときから入るまでのフレーム（`upClean₁`。各フレームが操作中に始まることは証明、`Run.upStart₁`）、`Rest`（`entryRest₁`: 12 回目から 109 バイトのうち 36。土管のタイマーは証明）から出します。[縦の土管に入るときの状態を、タイトルから出す](b-3-4-EntryKeep-ja.md)を見てください。
* 土管のフレームのすべてのステップで `Places`（`chg.places₁`）。行は少しの走りのフレームから作りました。敵が読み込まれる走りや、行にない列をパーサーが扱う走りは外れます。項目 1-1-b-3-5:
  * `ColorRotation` の場所は `VRAM_Buffer1_Offset` の 256 の値すべてを許し、上限もないので、走りに何も求めません。状態はそこでこのオフセットで分かれ、確認にはそれが要ります。
  * `ProcELoop`、`FlagpoleRoutine`、`BlockObjMT_Updater`、`ColorRotation` にはドットの上限 50,000 がありました。これらはなくなりました。5 つの上限（`UpdScrollVar` とこの 4 つ）のうちどの 4 つを外しても確認は成り立ち、5 つすべてを外すと成り立ちません。だから上限は 1 つ、パーサーの場所に残します。14 個の入る状態と 3 種類の入力では、土管の 1,974 フレームは、どれもドット 37,603 以下でパーサーの場所に着きます。
* ルートは出口で `QuietRest ∧ Shape` を（`chg.quiet₁`）、入るときに `PauseV` を（`chg.pause₁`）求めます。[b-3-7-2](b-3-7-2-PipePause-ja.md) を見てください。前は `QuietP ∧ Shape` を求めました。`Quiet ∧ Song ∧ Shape` と `TimeOK` のフラグ 0 より弱い条件です。[b-3-7-1](b-3-7-1-SoundRows-ja.md) を見てください。前の条件は、土管のフレームで Start を押すと成り立たないことがあります。`Shape` と `Song` は出口のフレームの歩みからは出ません。その歩みの出口での終わりの状態 36 個のどれも、1 つめの画面のバッファの形も曲のバイトも知りません。出口のフレームの NMI が 2 つめのバッファから書くとき、1 つめのバッファには前のフレームが書いたものが残ります。1 フレームの歩みはそれを知りません。CPU の 1 ステップは命令が書く場所にしか書きません（[CPU の 1 ステップが RAM を書く場所](d-3-4-1-StepWrites-ja.md)）。これを使えば音のバイトを段の状態の外に持てて、`Quiet` をポーズの音の種類の列にできます。これは [b-3-7-1](b-3-7-1-SoundRows-ja.md) でしました。
* 土管のあとのゲームコアのフレームで `NoStart`（`chg.noStart₁`）。
* 出口で `TimeOK`。ルートはいま、ゲームのタイマーが 000 でないことだけを求めます（`chg.time₁`、`TimerOK`）。音のポーズのフラグは `QuietP` に入ります。項目 1-1-b-3-9。`b` が入ったあと最初の操作であることは、もうフィールドではありません（フィールド `ctlFirst₁` はなくなりました）。`b₁` は、入るときから `dB` フレームの中で最初に操作できるフレームです（定義 `Base.b₁`: `b₁ = firstCtl(seq, a₁, dB)`）。さらに `ctlBy₁ : ctl(seq (a₁ + dB))`。すると `Changes.order₁ : a₁ ≤ b₁`、`Changes.ctl₁ : ctl(seq b₁)`、`Changes.ctlFirst₁ : ∀ n, a₁ ≤ n < b₁ → ¬ctl(seq n)` は定理です。`b₂` と同じです。土管の中でポーズすると `TimeOK` は成り立ちません（`changes-check FM2 pause 380 60` と `pause 416 60`）。そのときは同じ出口で `Quiet` も成り立ちません。
* `lagPaused`（`chg.paused₁`）: `lag` のフレームはポーズの状態で終わる。[b-3-3](b-3-3-LagPaused-ja.md) を見てください。

**ファイル.** `Theorems/PipeChangeEnd.lean`、非公開の `Proof/PipeChangeEnd.lean`。

**再現.**
```
.lake/build/bin/smbrta pipe-end-check FM2    # 確認と、E、TAS の入る状態、本物の 13 個での 3 種類の入力による条件と出口の時間の確認。約 2 分
.lake/build/bin/smbrta changes-check FM2     # TAS の走りでの Changes のフィールド
```
