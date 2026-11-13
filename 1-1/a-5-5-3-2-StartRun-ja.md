[← Back](README-ja.md) | [English](a-5-5-3-2-StartRun.md) | [Japanese](a-5-5-3-2-StartRun-ja.md)

# 操作から土管までの各フレームはアイドルループで始まる

**主張.** タイトルで Start を押したことから、操作できるときの機械は、アイドルループで、操作できる状態でフレームを始めます。そこから縦の土管に入るまでの各フレームも、
数えるフレームでも数えないフレームでも、同じように始まります。ただし、数えるフレームが操作できる状態で終わり、各命令が `Clean` を満たす（数えないフレームでは、
添字やポインタを通ってポーズのバイトを書かない）ときです。数えないフレームは、数えるフレームの定義からポーズで終わります（[LagPause](a-5-5-3-3-LagPause-ja.md)）。数えないフレームはモードのルーチンを呼ばないので
（[ポーズで終わるフレームはモードのルーチンを呼ばない](a-5-5-3-3-LagPause-ja.md)）、操作できる状態で終わることは [土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md) の確認から出ます。なので次のものは、もう仮定しません。

* `Pipe.start`（項目 1-1-a-5-2-1）: 入るフレームはアイドルループで、操作できる状態で始まる。
* `lags.start`（項目 1-1-a-5-5-3-2）: 数えないフレームはアイドルループで始まる。

前の `lags.clean`（モードのルーチンの呼び出しまで、`V` の 5 バイトも守る `Clean`）は前の回に 2 つに分けました。5 バイトについての部分（`lags.store`）は、
いまは `LagFrames` の確認が証明します。残りは、操作から入るまでのどのフレームにも、その全部の命令について求めます（`lags.clean`）。

記号. `seq(n)` は全部のフレームを数えたときのフレーム `n` の始まりの機械、`sin(n)` はその入力で、`seq(n + 1) = frame(seq n, sin n)` です。数えるフレーム `t` はフレーム `ix(t)` で、
`fm(t) = seq(ix t)` です。`ix(t + 1)` は `ix(t)` のあとでポーズでなく終わる最初のフレーム、`ix(0) = 0` です。`tr_n(k)` はフレーム `n` の `k` 命令あとの機械です。`c` はモードのルーチンの呼び出しです。`V = (v, f, P)` は速さ、端数、位置で、`vfp` はその 5 バイトです。

```
ctl(m)            :=  OperMode(m) = ゲーム  ∧  OperMode_Task(m) = ゲームコア  ∧  GameEngineSubroutine(m) = PlayerCtrl
FrameStart_G(m)   :=  pc(m) = EndlessLoop  ∧  スタックポインタはそこの値  ∧  m はフレームの始まり（dot の 2 つの窓）
                      ∧  NMI が有効  ∧  パッドのストローブが off  ∧  G.known のバイトはその値
FrameStart(m)     :=  G = guardOf の FrameStart_G(m): ルーチン、モード、タスクは操作できるときの値
Clean(m)          :=  guardOf の PipeWrites.Clean（store、read、jump、time）
CleanK_G(q, m)    :=  Clean_G(m)。ただし q で X = 0 のときの書き込みは問わない（FrameKeep）
```

```
starts         :  keepCheck(S, G, W),  FrameStart_G(seq a),  W(seq a),
                  ∀ n ∈ [a, b),  ∀ j,  CleanK_G(S.store, tr_n(j)),
                  ∀ n ∈ [a, b),  seq(n + 1) で G.known のバイトはその値
                  →   ∀ n ∈ [a, b],  FrameStart_G(seq n)  ∧  W(seq n)
starts_dep     :  同じもの。ただしフレーム n の終わりのわかっているバイトは、FrameStart_G(seq n) のときだけ求める
starts_clean, starts_clean_dep :  見張るビットなし（W = []）で、CleanK_G のかわりに Clean_G のもの
Begin.start₁   :  check（TitleStart）,  titleCheck(c, G, m₀),  Begin,  seq 1 = frame(seq 0, inp 0),  seq 1 で G.known のバイト   →   FrameStart_G(seq 1)
Begin.start₁G  :  G = guardOf のもの。わかっているバイトは ctl(seq 1)（フィールド Begin.ctl）から
Begin.pos₁     :  check,  titlePosCheck(c, m₀),  Begin,  seq 1 = frame(seq 0, inp 0)   →   P(seq 1) = P(m₀)          （この回）
Begin.hs₁      :  同じ前提   →   startHS(seq 1) = startHS(m₀)       （速さ、端数、向き、動く向き、走りの速さ。この回）

Lags           :  ix t < ix(t + 1),  fm t = seq(ix t),  そして
                    ctl   :  ∀ t ∈ [1, E),  ctl(seq(ix t + 1))                      （数えるフレーム）
                    clean :  ∀ n ∈ [1, ix E),  ∀ k,  Clean_P(tr_n(k))      （ポーズのバイトも守る Clean: LagPause.guardP。前の clean と keeps）
Lags.cleanG    :  Lags   →   ∀ n ∈ [1, ix E),  ∀ k,  Clean(tr_n(k))
Lags.keepsP    :  Lags   →   数えないフレームは添字やポインタを通ってポーズのバイトを書かない   （LagPause。ポーズで終わることは定義から）
Lags.known_end :  lagCheck,  pauseCheck,  Lags,  n ∈ [1, ix E),  FrameStart(seq n)   →   ctl(seq(n + 1))
Lags.starts    :  lagCheck,  walkCheck,  pauseCheck,  Lags,  FrameStart(seq 1)   →   ∀ n ∈ [1, ix E],  FrameStart(seq n)
Lags.lagStart  :  同じもの   →   数えないフレームで FrameStart(seq n)          （前のフィールド lags.start）
Pipe.startE    :  lagCheck,  walkCheck,  pauseCheck,  1 ≤ E,  FrameStart(seq 1)   →   FrameStart(fm E)    （前のフィールド Pipe.start）
Run.pipeStart₁ :  title_check,  title_ctl_check   →   FrameStart(seq 1)            （Run のフィールド title を使う）
Run.pipeKeep₁  :  確認,  1 ≤ E   →   fm 1 の LagFrames.lagI の 17 バイトは seq 1 のもの     （数えるフレーム 1 の前のフレームはポーズで終わる）
Run.pipePos    :  確認,  title_pos_check,  1 ≤ E   →   P(pipe.fm 1) = P(m₀)
Run.pipeHS     :  確認,  title_pos_check,  1 ≤ E   →   startHS(pipe.fm 1) = startHS(m₀)
```

`walkCheck` と `titleCheck` は ROM での確認で、非公開の `walk_check` と `title_ctl_check` が `native_decide` で示します（証明のビルドで 2 つ合わせて約 4 秒）。
`titlePosCheck` は `titleCheck` と同じようにフレーム 0 を追い、操作できる終わりのそれぞれで、位置、横の状態のバイト、`stI` の 6 バイトが `m₀` の値で
わかっていることを確かめます（非公開の `title_pos_check`、ネイティブで約 2.2 秒）。
`lagCheck` は [土管までの数えないフレーム](a-5-5-3-LagFrames-ja.md) の確認で、非公開の `lag_check` が示します。
ROM のない定理が使う公理は `propext`、`Classical.choice`、`Quot.sound` だけです。`#print axioms route_1_1` に `sorryAx` はありません。

Lean: `Theorems/StartRun.lean`、`Theorems/PipeFrames.lean` の `Lags`、`Lags.known_end`、`Lags.starts`、`Lags.lagStart`、`Lags.startE`、`Theorems/Route.lean` の `Pipe.one_le`、`Pipe.startE`、
`Pipe.reads`、`Run.pipeStart₁`、`Theorems/PipeWrites.lean` の `rule_on_frameS`、非公開の `Proof/StartRun.lean`。

## しくみ

* **1 フレーム全部.** 歩きは `FrameKeep`（[パート f](f-6-19-FrameKeep-ja.md)）のものです。`TaintRun` の抽象機械が `FrameStart` からフレームを追い、各命令が `CleanK` を満たせば、
  どの道も次のフレームの始まり（アイドルループ、そのスタックポインタ、dot の窓、NMI が有効、ストローブが off）で終わります。終わりの `G.known` のバイトは歩きにはわかりません。
  それは、数えるフレームでは終わりの `ctl` から、数えないフレームでは `LagFrames` の確認から来ます。数えないフレームはモードのルーチンを呼びません（`Lags.no_call`、`Lags.known_end`）。
  最後のものには、そのフレームが操作できる状態で始まることが要ります。なので帰納法は、フレーム `n` の終わりのわかっているバイトを、フレーム `n` がそう始まるときだけ求めます
  （`starts_dep`）。ここでは歩きのガードを `PipeWrites` のもの（`guardOf`）にし、見張るビットも移動のルーチンの場所もなしにしました（`walkCheck`）。なので 1 命令の条件は
  `Clean` そのものです。641,723 段、分かれ 65,610、失敗 0、表は 43,259 状態です。ネイティブで探索 1.5 秒、確認 2.2 秒です。
* **数えないフレーム.** 歩きはポーズのバイトを知りません。なのでポーズのフレームは歩きの道の 1 つです。帰納法はフレーム 1 から `ix E` までの `seq` の全部のフレームを、
  数えるものも数えないものもたどります。数えるフレーム 1 より前のフレームも数えないフレームです。
* **操作できるときの機械.** `TitleStart` は、フレーム 0 がその集合の近い状態か止まった状態で始まることを示します。`titleCheck`（`TitleStart.frame0Check`）はその状態からフレーム 0 を
  Start も含めてどの入力でももう一度追い、操作できる終わりはフレームの始まりであることを確かめます。`Run.pipeStart₁` はこれを `base` のフレーム 1 で読みます。帰納法がそれを `pipe.fm 1` まで運びます。
* **`one_le`.** 入るフレームはフレーム 1 以降でなければなりません。これはいまは定理です（`Pipe.one_le`、`Route.Run.pipeOne`）。`fm 0` は走りのフレーム 0 で、フレーム 0 は操作できる状態で終わり（`title`）、入るフレームは土管のルーチンで終わります（`Enters`）。2 つのルーチンは違います（`EntryKeep.KeepOK.ne`）。

## 本物のフレームで確かめたこと

プログラムです（`start-check`）。操作できるときの機械から、入るまで、または操作できない状態で終わる最初のフレームまで走らせます。各フレームで `FrameStart`、各命令の `Clean`、
数えないフレーム（インターバルタイマーが動かない）では `c` より前の書き込み（前のフィールド `lags.store`。いまは証明）を調べます。入るフレームでは `FrameStart` を調べます。
どのフレームも操作できる状態で終わることを調べるので、新しい `lags.ctl`（数えるフレーム）も確かめています。

| 走り | フレーム | 数えない | 入る | 操作できない状態で止まった走り | `FrameStart` でない | `Clean` でない | `c` より前の `vfp` への書き込み | `FrameStart` でない入るフレーム |
|---|---|---|---|---|---|---|---|---|
| TAS の操作から入るまで | 367 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| Start のある自分の入力、小さい・大きい（240 回） | 150,299 | 76,542 | 0 | 51 | 0 | 0 | 0 | 0 |
| 入る前にポーズ、そのあと TAS の入力（200 回） | 15,580 | 14,140 | 40 | 0 | 0 | 0 | 0 | 0 |
| 入る前の TAS の機械から B と右、そのあと下（480 回） | 26,903 | 0 | 93 | 0 | 0 | 0 | 0 | 0 |

* 止まった 51 回は、死ぬ、大きくなる、けがをするで、操作できない状態で終わります。`lags.ctl` により、そういう走りは定理の外です。[1-1 全体](0-1-Route-ja.md) は、パワーアップのある走りを
  もう外としています。
* モードのルーチンを呼ぶ数えないフレームはありませんでした。全部ポーズです。
* タイトルで押したあとの操作できるときの機械がフレームを始めることは、押したときの条件のどの機械についても `title_ctl_check` が示します。TAS でも成り立ちます。

## 前提（Lean では証明していない）

* **`lags.ctl`**: 操作から入るまでの数えるフレームは、どれも操作できる状態で終わる。各フレームの 1 つの状態についての条件です。大きくなる、けが、死ぬでは成り立ちません。
  数えないフレームが操作できる状態で終わることは確認から出ます。ポーズで終わる（`ix` の定義から）ので、モードのルーチンを呼ばないからです。
* **`lags.clean`**: そのフレームの各命令は `Clean` で、ポーズのバイトも守る（添字やポインタを通った書き込みがそれを書かない）。同じフレームについての
  `chg.upClean₁`（パート b）と同じ種類の条件で、守るバイトは少ないです。地上の `FrameKeep.Frames.cleanF` とも同じ種類です。下と同じ走りでポーズのバイトも守って
  確かめました（`start-check FM2 240 pause`）。成り立たない命令は 0 です。
* **`lags.keeps` はもうフィールドではありません**（この回）。数えないフレームでの `Clean` のポーズのバイトの部分だったもので、いまは `lags.clean` に入っています
  （`Lags.keepsP`）。
* **`lags.game` はもう仮定しません**: かわりに `lags.clean` で守るポーズのバイトと数えるフレームの定義です（[ポーズで終わるフレームはモードのルーチンを呼ばない](a-5-5-3-3-LagPause-ja.md)）。
* `lags.store` はもう仮定しません。`LagFrames` の確認が証明します。
* `one_le` はもう仮定ではありません。`Pipe.one_le` が証明します。
* **`Run.pipeAt` はなくなりました.** `pipe` の数えるフレーム 1 は、もう定義からフレーム 1 ではありません。フレーム 1 から先でポーズでなく終わる最初のフレームです。
  操作のときの値はフレーム 1 で読み、その前のフレームが変えないことで運びます（`Run.pipeKeep₁`）。

`StartRun.starts` と `Begin.start₁` はガードについて一般です。パート b の `Run.upStart₁` は同じ帰納法を `base.seq` で `EntryKeep` の中で行います。2 つは 1 つの補題にまとめられます。

**ファイル.** `Theorems/StartRun.lean`、`Theorems/PipeFrames.lean`、`Theorems/Route.lean`、`Theorems/PipeWrites.lean`、非公開の `Proof/StartRun.lean`。

**再現.**
```
.lake/build/bin/smbrta start-check FM2 240    # 2 つの確認と、本物のフレームでのフィールド、約 4 分
```
