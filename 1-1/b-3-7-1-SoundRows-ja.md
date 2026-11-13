[← Back](README-ja.md) | [English](b-3-7-1-SoundRows.md) | [Japanese](b-3-7-1-SoundRows-ja.md)

# 音のバイトを表で運ぶ、部屋への切り替え

**主張.** 縦の土管の出口のあとのフレームの段は、音のルーチンの外では音の 38 バイトを忘れてかまいません。段の横に、これらのバイトの状態の表を運びます。[横の土管から出る切り替え](d-3-4-2-SideChangeSound-ja.md)と同じやり方です。これは ROM の確認つきで証明しました。この段では出口の条件が弱くなります。ポーズの音は鳴っていないか、ポーズを解く音が鳴っていてかまいません（`QuietP`）。前は、鳴っておらず、音のポーズのフラグが 0 で、2 つの矩形波の効果音が基準と同じでなければなりませんでした。ルートはいま `QuietP`（`chg.quiet₁`、項目 1-1-b-3-7）と、ゲームのタイマーが 000 でないことだけ（`chg.time₁`、`TimerOK`）を求めます。土管のフレームで Start を乱数で押す本物の走り 1,100 回で、`QuietP` は 1,014 の出口で成り立ち、前の条件は 557 で成り立ちました。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` から入力 `i` で進む 1 フレームです。`x = run(E, 0^48)` は出口の基準の機械です。`left`、`During`、`ExitAt`、`Places`、`NoStart` は[`fall` なしの部屋への切り替え](b-3-2-PipeChangeEnd-ja.md)と同じです。`SongAt(rows, m)` は、`m` が行のどれか 1 つのバイトを持つことです。`song` は曲の 1,607 行、`shape` は出口での画面のバッファの形です。

## 出口の条件

`q`、`b`、`f`、`c`、`s₁`、`s₂` はバイト `PauseSoundQueue`、`PauseSoundBuffer`、`PauseModeFlag`、`Squ1_SfxLenCounter`、`Square1SoundBuffer`、`Square2SoundBuffer` です。`U` はポーズを解く音の値、`L` はポーズの音の長さです。シンボル（`UnpauseSfxValue`、`PauseSfxLength`）を通して ROM から読みます。

```
QuietP(m)  :=  ( m[q] = x[q]  ∧  m[b] = x[b]  ∧  m[f] = 0  ∧  m[s₁] = x[s₁]  ∧  m[s₂] = x[s₂]  ∧  SongAt(song, m) )     鳴っていない
            ∨  ( m[q] = x[q]  ∧  m[b] = U  ∧  m[f] = U  ∧  1 ≤ m[c] < L )                                          解く音が鳴っている
```

前の条件は `Quiet(m) ∧ SongAt(song, m)` で、`Quiet` は `q`、`b`、`s₁`、`s₂` についてのもの、`m[f] = 0` は `TimeOK` からでした。ですから `Quiet(m) ∧ SongAt(song, m) ∧ m[f] = 0 → QuietP(m)` です（`quietP_of_quiet`）。`Changes.toK` は前のフィールドを新しいフィールドにします。数は `L` より小さいです。音は数を `L` にして、同じフレームで 1 減らすからです。

## 段

段 `r` は、1 フレームの状態 `R(r)`、段の `left`、音のバイトの表 2 つを持ちます。音のルーチンを呼ぶ前の `T₀(r)` と、戻ったあとの `T₁(r)` です（`SoundRows.SRow`）。`Sim(S, m)` は抽象状態 `S` が `m` を含むことです。`Ph(S, m)` は、`m` の音のバイトが `T₀(r)` の状態のどれかに含まれること、戻ったあとなら `T₁(r)` のどれかに含まれることです。

```
InRowsK(m)  :=  ∃ r ∈ rowsK, ∃ S ∈ R(r),  Sim(S, m) ∧ Ph(S, m)
InRowsT(m)  :=  ∃ r ∈ rowsK, left(r) = 0, ∃ S ∈ R(r), ∃ t ∈ T₀(r),  Sim(S + t, m)
```

`S + t` は、`S` に `t` のバイトを入れた状態です。`InRowsT` は部屋の確認が読むものです（`ScreenStart.roomCheck`、`RoomStart.startCheck`、`RoomMap.startCheckT`）。段は、出口の状態から、音のバイトを忘れ、タイマーが 000 でない（`dg`）として始まります。最初の表は `QuietP` の種類を持ちます。曲の行ごとに 1 つ、1 から `L − 1` までの数ごとに 1 つです。どれにも、土管のフレームの歩きが出口で出す音のバイトが入ります。

## 主張の形

`EndStatement` に新しいフィールドが 5 つ入ります。確認 `endCheck` が、前のフィールドといっしょに出します（`endStatement_of_check`）。

```
stepK :  ∀ m, During(m) → ∀ i, (∀ j, Places(trace(m, i, j))) →
           During(frame(m, i))  ∨  ( ExitAt(frame(m, i))  ∧  ( frame(m, i) で QuietP ∧ SongAt(shape) ∧ TimerOK  →  InRowsK(frame(m, i)) ) )
rowsK :  ∀ m, InRowsK(m) → ∀ i, NoStart(m, i) →  left(m) = 0  ∨  ( InRowsK(frame(m, i))  ∧  left(m) ≤ left(frame(m, i)) + 1 )
zeroK :  ∀ m, InRowsK(m) ∧ left(m) = 0 → ctl(m)
goK   :  ∀ m, InRowsK(m) → ¬Paused(m)
ctlK  :  ∀ m, InRowsK(m) ∧ left(m) = 0 → InRowsT(m)
```

**走り.** `PipeRunK` は `PipeRun` のフィールドに、出口での `QuietP ∧ SongAt(shape)`（`quiet`）と出口での `TimerOK`（`time`）を持ちます。`b` が入ったあと最初の操作なら（`hc`）:

```
PipeRunK.bound   :  cnt(a) + 91 ≤ cnt(b)
PipeRunK.first   :  hc  →  ∀ n, a ≤ n < b,  left(seq n) ≠ 0
PipeRunK.inRowsT :  hc  →  InRowsT(seq b)
PipeRunK.start   :  hc  ∧  startCheck  →  seq b で部屋の始まり          （RoomStart）
```

`Route` は最初の切り替えを `ChangesK.run₁ : PipeRunK` からとります。`ChangesK.bound₁`、`ChangesK.first₁`、`ChangesK.roomAt`、`Run.roomStart`、`InRowsT` を読む部屋の定理です。

Lean: `Theorems/SoundRows.lean`（`SRow`、`scan`、`rowsFromS`、`incl`、`finS`、`linkS`、`chainS`、`CoveredS`、`link_frameS`、`InvS`、`chain_stepS`、`ctl_of_zeroS`、`inv_headS`、`refineRow`、`zeroRows`、`covered_refine`、`invL_zero`）、`Theorems/PipeChangeEnd.lean`（`rtOf`、`QuietP`、`kindsP`、`baseK`、`tableP`、`startsK`、`grpP`、`rowsKc`、`InRowsK`、`timeRows`、`InRowsT`、`soundCheck`、`baseIncl`、`base_of_K`、`kinds_of_quietP`、`quietP_of_quiet`、`inRowsK_of_exit`、`PipeRunK`、`PipeRunK.bound`、`PipeRunK.way`、`PipeRunK.first`、`PipeRunK.inRowsT`）、`Theorems/RoomStart.lean`（`startCheck`、`start_of_rowsT`、`PipeRunK.start`）、`Theorems/Route.lean`（`ChangesK.run₁`、`ChangesK.bound₁`、`ChangesK.first₁`、`ChangesK.roomAt`、`Changes.toK`）。これらのファイルにゲームのデータはありません。

## しくみ

**出口.** 土管のフレームの歩きは、いま出口で状態 `baseK` に着きます。出口のバイト、ノイズの効果音のバッファ、画面のバッファの制御を知っていて、前の `Quiet` の 4 バイトは知りません。前の状態 `baseOf` は、これに `Quiet` のバイトを足すと出ます（`baseIncl`、`base_of_K`）。ですから前の主張も同じ歩きから証明されます。

**1 フレーム.** 歩きは[CPU の 1 ステップが RAM のどこに書くか](d-3-4-1-StepWrites-ja.md)の `twalk` です。音のルーチンを呼ぶところで状態を `T₀(r)` で分け、音のバイトを知ったままルーチンを歩き、戻るところでバイトが `T₁(r)` に入ることを確かめて忘れます。呼ぶ場所と戻る場所は ROM から読みます。`NonMaskableInterrupt` から最初に `SoundEngine` を呼ぶところです（`rtOf`）。

**表.** 出口のあと最初のフレームでは、2 つめの表のうちポーズの音のバイトが同じ状態をまとめます（`grpP`）。そのフレームと次のフレームはページ 0 の音のバイトを消し、曲のほかのバイトは新しい曲が書くまで読まれません。それが成り立つかは確認が決めます。ほかのフレームでは、表は探索が見つけたとおりです。

**探索.** 探索は歩きの表を作ります。確認は探索によりません。待ちの繰り返しにある始まりの状態は、音のルーチンを呼ぶところまで 1 つずつ進みます。画面のバッファの形がまとまらないようにするためです。呼ぶところで状態をまとめ、最初の表の状態ごとに、まとめずに戻るところまで進みます。戻るところで、レジスタを忘れてまとめます（次の `ReadJoypads` がレジスタを書きます）。RAM を消す途中の始まりの状態はほかとまとめます。消す繰り返しの回ごとにまとまるようにするためです。

**確認の大きさ.** 44 段、1,906 個の状態、歩きの表で約 10,000 個の状態、最初の表は 1,648 個、いちばん大きい表は 3,557 個です（最後のフレームで、新しい曲と長さの違う解く音がまざるところ）。プログラムで、段は約 24 秒、段の歩きは約 65 秒です。数秒を超えます。部屋の確認は `left` が 0 の段を表といっしょに読みます。14,228 個の状態で、プログラムでそれぞれ約 26 秒です。

## 正しくない事実

* **出口のフレームでポーズを解いた場合は入れられません.** 下の 1,100 回のうち 86 回は、出口のフレームでポーズを解いていました（`m[q] = U`、`m[b] = x[b]`、`m[f]` はポーズの音の値）。86 回すべてで、操作できるときに部屋の条件 `Room`（d-2-4-1）が成り立ちません。新しい曲が始まっておらず、`AreaMusicQueue` が 0 でないからです。ですから `Room` が曲のキューを許さないかぎり、`QuietP` にこの場合は入れられません。
* 解く音の数 `L` を最初の表に入れると、`ScreenStart.roomCheck` は操作できる 4 個の状態で成り立ちません（`AreaMusicQueue` が 4）。本物の出口で数が `L` のものはありません。

## 測ったけれど定理にしていないこと

プログラム: `pipe-sound-real FM2 10`。入る状態 55 個（基準の入る状態、ムービーの入る状態、土管の窓に立って下を押す本物の 53 個）から、それぞれ 10 回、土管のフレームで 2 とおりの割合で Start を乱数で押し、そのあと操作できるまで Start を押しません。

| 出口での種類 | 出口 | 前の `quiet₁` | 曲 | 画面のバッファ | `s₁`、`s₂` が `x` と同じ | タイマーが 000 でない | 操作のときの `Room` |
|---|---|---|---|---|---|---|---|
| 鳴っていない、フラグ 0 | 557 | 557 | 557 | 557 | 557 | 557 | 557 |
| 解く音、数 1 から 41 | 457 | 0 | 457 | 457 | 457 | 457 | 457 |
| 出口のフレームで解いた | 86 | 0 | 86 | 86 | 86 | 86 | 0 |

出口から操作まではいつも 44 フレームで、出口のあとは各フレームで `left` がちょうど 1 減りました。

## 仮定（Lean では証明していない）

* 出口でルートはいま `QuietRest ∧ SongAt(shape)` だけを求めます（`chg.quiet₁`）。`QuietP` のポーズの部分は、入るときの条件 `PauseV`（`chg.pause₁`）から、ポーズをクラスに入れた土管のフレームで出ます。[縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md)を見てください。ポーズの音のキュー、鳴っていない場合の曲の行と 2 つの効果音、画面のバッファの形はまだ求めます。
* 出口での `TimerOK`（`chg.time₁`）。
* 土管のあとのゲームコアのフレームで Start を押さないこと（`chg.noStart₁`、1-1-b-3-6）。操作の前の最後の 18 フレームです。ポーズしたフレームは `left` を減らさず、段は `left` の値ごとに 1 つです。していません。

**ファイル.** `Theorems/SoundRows.lean`、`Theorems/PipeChangeEnd.lean`。非公開の確認は `Proof/PipeChangeEnd.lean` の `pipe_end_checks` です。

**再現.**
```
.lake/build/bin/smbrta pipe-sound-rows -c        # 段をフレームごとに、chainS と soundCheck
.lake/build/bin/smbrta pipe-sound-rows -r        # left が 0 の段で部屋の確認
.lake/build/bin/smbrta pipe-sound-real FM2 10    # 本物の走り 1,100 回で出口の種類と操作のときの Room、約 3 分
```
