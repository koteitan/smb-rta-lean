[← Back](README-ja.md) | [English](b-3-7-3-EntryPause.md) | [Japanese](b-3-7-3-EntryPause-ja.md)

# 縦の土管に入るときのポーズを、タイトルから出す

**主張.** タイトルで `TitleStart` のとおり Start を押し、操作できるときから縦の土管に入るまでのフレームの各命令が、[入るときの状態](b-3-4-EntryKeep-ja.md)の守りについて `Clean` だとします。守りの一覧には、ポーズの 6 バイトも加えました。すると入るとき、ポーズの音は鳴っていないか、解く音が鳴っていてポーズのタイマーがその数より 1 大きいか、そのフレームで解くボタンが押されています（`PauseV`）。これらのどのフレームで Start を押してもかまいません。これは ROM の確認 2 つつきで証明しました。ですからフィールド `chg.pause₁` はなくなりました（項目 1-1-b-3-7-3）。`upClean₁` は、添字やポインタを通した書き込みが 6 バイトにも触れないことを新しく求めます。本物のフレームでは、そういう書き込みは 6 バイトに触れません。

`m[i]` は `m` の RAM のバイト `i` です。`frame(m, i)` は `m` から入力 `i` で進む 1 フレーム、`trace(m, i, j)` はその `j` 歩あとの機械です。`seq n` はフレーム `n` が始まるときの機械で、`a` は `a₁`、入るフレームのあとの機械です。`FrameStart`、`Watched(kept, m)`、`Clean_G`、`Rest`、`rt(m)`、`Begin` は[入るときの状態](b-3-4-EntryKeep-ja.md)と同じです。6 バイト `q`、`b`、`f`、`c`、`t`、`g`（ポーズの音のキュー、バッファ、フラグ、数、ポーズのタイマー、ポーズのバイト）、88 のクラス `classesV`、`PauseV` は[縦の土管のフレームを通るポーズ](b-3-7-2-PipePause-ja.md)と同じです。`SIn(t, m)` は、`m` のバイトがクラス `t` のとおりであることです。

```
InCls(m)  :=  ∃ t ∈ classesV,  SIn(t, m)
```

## 命題

```
Begin.pauseClass :  Begin(seq, inp)  →  InCls(seq 1)                                                  （確認 nearPauseCheck）
pause_frame      :  FrameStart(m) ∧ Watched(kept, m) ∧ (∀ j, Clean_G(trace(m, i, j))) ∧ InCls(m)
                      →  InCls(frame(m, i))  ∧  ( rt(frame(m, i)) = pipe  →  frame(m, i)[g] & 1 = 0 )     （確認 pauseCheck）
class_up         :  ∀ n, 1 ≤ n ≤ a  →  InCls(seq n)                                                   （帰納法）
pauseV_of_class  :  t ∈ classesV ∧ SIn(t, m) ∧ m[g] & 1 = 0  →  PauseV(m)                             （ROM なし。L + 1 < 256）
pause_entry      :  2 ≤ a ∧ rt(seq a) = pipe  →  PauseV(seq a)
entryV_of_title  :  entry_of_title の仮定  →  Entry(seq a) ∧ PauseV(seq a)                             （EntryV）
```

`class_up` と `pause_entry` は、`1 ≤ n < a` で `FrameStart(seq n)`、`Watched(kept, seq n)`、フレーム `n` の `Clean_G` をとります（`entry_of_title` と同じく `starts_of_title` と `watched_up` から）。`L` はポーズの音の長さです。

ルートでは、`Run.entry₁` が前と同じ仮定から `EntryV`（`Entry ∧ PauseV`）を出し、`ChangesK.run₁` はそこからポーズをとります。

```
chg.pause₁   :  PauseV(seq a₁)                                                     （なくした。Run.entry₁ から）
chg.upClean₁ :  1 ≤ n < a₁  →  ∀ j, Clean_G(trace(seq n, inp n, j))               （G は 6 バイトも守る）
```

`Route` で `Entry(seq a₁)` をとっていた定理は `EntryV(seq a₁)` をとります。`HurryStart.Chg₁` にもフィールド `pause₁` はもうありません。

## しくみ

**フレーム 0.** フレーム 0 は `TitleStart` の近い状態か止まった状態で始まります。この 10 個の状態は 6 バイトを知っています。押したときの条件がポーズのバイトとポーズの音のバッファを知り、ほかはフレーム 0 までにゲームが知っている値で書くからです。`nearPauseCheck` はこれらからフレーム 0 を、Start を含むどの入力でも歩きます（`TitleStart.frame0Check`）。そして操作できる各終わりで、状態が 6 バイトをどれかのクラスのとおりに知っていることを求めます。そういう終わりは 40 あります。鳴っていない 16、解く音 16、解くボタン 8 です。

**操作できるときからの 1 フレーム.** 歩きは[入るときの状態](b-3-4-EntryKeep-ja.md)の歩きで、クラスを[土管のフレーム](b-3-7-2-PipePause-ja.md)と同じく横に運びます（`vsuccs`）。

* フレームの割り込みが音のルーチンを呼ぶところで、状態を、合うクラスごとの 1 つずつに分けます。
* その区間（音のルーチン、パッドの読み取り、ポーズのルーチン）では、各歩は歩きの 1 歩です。ポーズのルーチンを呼ぶところで、`g` のビット 7 で分けます。戻りでは 6 バイトがどれかのクラスにあることを求め、`g` のビット 0〜6 のほかは忘れます。
* 区間の外では、各歩は 6 バイトを保たなければなりません。書き込みが 6 バイトに届かない（`StepWrites.keepOK`）か、状態に合う各クラスについて、そのクラスのバイトを入れた状態の歩がどれも 6 バイトをクラスのとおりに知っている（`outOK`）かです。2 つめは、行き先のわからない、添字やポインタを通した書き込みです。そういう歩は守りのバイトのほかをすべて忘れ、6 バイトはいま守りにあります。ですから証明に要るのは、歩きの 1 歩が機械を追うこと（`FrameKeep.s_kstep`）だけです。
* フレームの終わりは区間の外で、`EntryKeep` の歩きの終わりを満たします。そこでルーチンが土管のものなら、状態は `g` のビット 0 が 0 だと知っています（`finV`）。

`Ph(A, m) := inR(A) ∨ InCls(m)` は、機械 `m` を覆う歩きの各状態 `A` で成り立ちます（`s_vsuccs`）。フレームの終わりで状態は区間の外なので、そこでは `InCls` が成り立ちます（`frame_of_walkV`）。

**入るフレームがポーズしていないわけ.** ポーズのルーチンは、同じフレームのゲームのルーチンより先に動きます。それがポーズすると、フレームはゲームのルーチンを飛ばすので、ルーチンのバイトは変わりません。土管に入るフレームはプレイヤーのルーチンを動かし、それが土管のルーチンを書きました。歩きは区間のあとで `g` のビット 0 を保つので、これを知っています。

**入るとき.** `seq a` のクラスは、`g` のビット 0 が 0 です。そういうクラスは、鳴っていないか、数が 1 から `L − 1` の解く音か、解くボタンです。これは `PauseV` の 3 つの場合です（`pauseV_of_class`）。

**縦の土管のクラスを使うわけ.** `PauseV` は、鳴っていないときフラグが 0 であることと、解く音の数が `L` より小さいことを求めます。[横の土管](d-3-4-3-SidePause-ja.md)の 90 のクラスは、鳴っていないときのフラグを知らず、数 `L` も許します。縦の土管の 88 のクラスは両方を言います。

**守り.** `EntryKeep.guardOf` は、行き先のわからない書き込みが触れないバイトに 6 バイトを加えます（`pauseSix`）。`EntryKeep` の歩きはほとんど変わりません。表は 53,438 状態（前は 53,437）で、`keepCheck` はプログラムで 4.8 秒です。

**確認の大きさ.** 88 のクラスです。プログラムで、探索は 2,131,805 歩、201,762 の分かれ、失敗 0、表は 95,044 状態です（11〜13 秒）。`pauseCheck` は探索込みで 14〜16 秒、`nearPauseCheck` は約 1.8 秒です。数秒より長いです。`Proof/EntryKeep.lean` の非公開のビルドは 28〜35 秒です（前は約 7 秒）。確認は非公開の `Proof/EntryKeep.lean` の `entry_pause` と `entry_pause_near` で、`EntryKeep.Checks` にフィールドが 2 つ加わりました（`pauseNear`、`pause`）。

## 測ったこと

新しい守りで `entry-keep-check FM2`（exit 0）。添字やポインタを通した書き込みは、どれも守りのバイトに触れませんでした。TAS の操作から入るまで（368 フレーム）、基準の入り方（440 フレーム）、操作できるときからの乱数の入力 300 回（127,841 フレーム、うち 5,390 はポーズ）、TAS のフレームからの乱数の入力 300 回（75,241 フレーム、うち 4,746 はポーズ）、立ち止まる 0〜39 フレームを加えた基準（17,600 フレーム）です。

`title-pause-near`（exit 0）。`TitleStart` の近い状態 8 と止まった状態 2 は、`q`、`b`、`f`、`t`、`g` を知り、`c` は一部で知っています。フレーム 0 の操作できる 40 の終わりは 6 バイトをすべて知っています。ただし鳴っていない 16 の終わりでは `c` を知りません。そのクラスは `c` を求めません。

## 仮定（Lean で証明していないもの）

* `upClean₁`: 操作できるときから入るまでのフレームの各命令が `Clean` であること。添字やポインタを通した書き込みは、ポーズの 6 バイトにも触れません。
* `entryRest₁`: 入るときの `Rest`。11 回目は 55 バイトでした（操作できるときからのフレームがポーズのバイトのビット 1〜6 を保つので、それは一覧から出ました）。12 回目から 36 バイトです（土管のフレームが使わない 19 バイトが `Entry` から出ました）（[1-1-b-3-4](b-3-4-EntryKeep-ja.md)）。

**ファイル.** `Theorems/EntryKeep.lean`（`pauseSix`、`guardOf`、`outOK`、`vsuccs`、`coverV`、`walkV`、`keyV`、`routeV`、`runV`、`searchV`、`finV`、`cfgV`、`pauseCheck`、`nearPauseCheck`、`Checks`、`tab_of`、`keep_of_outOK`、`s_vsuccs`、`LiveV`、`cover_liveV`、`live_stepV`、`frame_of_walkV`、`PauseOK`、`pauseOK_of_check`、`pause_frame`、`low7_all`、`low7_cases`、`pauseV_of_class`、`Begin.pauseClass`、`class_up`、`pause_entry`、`entryV_of_title`）、`Theorems/PipeChangeEnd.lean`（`EntryV`）、`Theorems/Route.lean`（`ChangesK.run₁`、`Run.entry₁`）、`Theorems/HurryStart.lean`（`Chg₁`）。非公開の確認は `Proof/EntryKeep.lean` の `entry_pause_near` と `entry_pause` です。公開のファイルにゲームのデータはありません。

**再現.**
```
.lake/build/bin/smbrta entry-pause-check     # 探索、pauseCheck、nearPauseCheck。約 50 秒
.lake/build/bin/smbrta title-pause-near      # フレーム 0 が 6 バイトについて知っていること。約 2 秒
.lake/build/bin/smbrta entry-walk-check      # EntryKeep の歩きとフレーム 0。約 30 秒
.lake/build/bin/smbrta entry-keep-check FM2  # 本物のフレームでの書き込み。約 4 分
```
