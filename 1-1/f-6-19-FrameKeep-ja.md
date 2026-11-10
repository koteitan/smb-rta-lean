[← Back](README-ja.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# 操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ

**主張.** 操作中に始まる 1 フレーム全体は 2 つのことを保ちます。城の旗は立ちません。位置の端数は 1/16 ピクセルの倍数のままです。またフレームは、歩きに見える範囲で、操作中の次のフレームの始まりで終わります。待ちのループにいて、スタックポインタ、ドット、PPU がフレームの始まりのものです。これはどの機械、どの入力についても成り立つ定理です。条件はフレームの始まりの 1 つの状態と、フレームの各命令の 1 つの条件です。証明は [`PipeWrites`](a-5-2-PipeWrites-ja.md) と同じように、`TaintRun.lean` の抽象機械でフレーム全体を追います。

ですから `PoleJoin.Run` の仮定 `fracStep` はなくなりました。定理 `Run.fracP` です。走りのフレーム（フィールド `keep`）と ROM のチェックから出ます。フィールド `noCastle` もなくなりました。操作できるときの機械から出る定理 `Run.noCastle_of` です（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。フィールド `keep.start`（各フレームは操作中に始まる）もなくなりました。定理 `Frames.start` です。それにはもっと小さいフィールド `keep.ctl` が要ります。触る前の各フレームは操作中に終わる、というものです。

この回、フィールド `keep.ends`、`keep.lag`、`keep.lagStart` がなくなりました。`keep` は、操作できるときからの全部のフレームを、数えるものも数えないものも、本物のフレームの列として持ちます（`all`、`inp`、`next`）。数えるフレームがどこで終わるかも持ちます（`ix`）。`lag` のフレームに専用の規則は要りません。歩きは、操作中に始まるどのフレームも覆います。ポーズ中かどうかは関係ありません。ですから `lag` のフレームも、数えるフレームと同じ定理（`Frames.all_start`）で、城の旗、端数の下のビット、操作中のフレームの始まりを保ちます。条件も同じ 2 つです。`ctl` と `clean` は、`lag` のフレームにもそれを聞くようになりました。

`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` はその中で `n` 命令あとの機械です。`all n` は、数えるかどうかによらず、フレーム `n` が始まるときの機械です。`all 0` は地上で操作できるときの機械です。`seq j` は数えるフレーム `j` の終わりの機械で、`seq 0 = all 0` です。

```
castle(m)        :=  StarFlagTaskControl(m) ≠ 0
f(m)             :=  SprObject_X_MoveForce(m)                         位置の端数（1/256 ピクセル単位）
Watched(m)       :=  castle(m) = false  ∧  f(m) mod 16 = 0
q                :=  MoveObjectHorizontally の最初の STA abs,X        端数を書く命令
Prot_K           :=  PipeWrites の Prot  ∪  {StarFlagTaskControl, SprObject_X_MoveForce}
Known_K(m)       :=  GameEngineSubroutine(m) = 操作  ∧  OperMode(m) = ゲーム  ∧  OperMode_Task(m) = コア
                  =  controllable(m)                                                     （known_of_ctl）
FrameStart_K(m)  :=  PipeWrites の FrameStart（待ちのループ、スタック、ドット、PPU、ストローブ）  ∧  Known_K(m)          （StartK）
CleanK(m)        :=  store:  添え字かポインタを通して書く命令、書く先 t:   ¬(pc(m) = q ∧ X(m) = 0)  →  Plain(Prot_K, t)
                     read, jump, time:  PipeWrites の `Clean` と同じ
```

`Plain(Prot_K, t)` は、その書き込みが `Prot_K` のバイトを変えないことです。`q` で `X = 0` の書き込みはプレイヤー自身の端数の書き込みなので、聞きません。

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))
keep_frame_start  :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n))),  Known_K(frame(m, i))
                       →   FrameStart_K(frame(m, i))  ∧  Watched(frame(m, i))

Frames (keep)     :  all n, inp n                      フレーム n が始まる機械（数えるかどうかによらない）と、その入力
                     next    :  all(n + 1) = frame(all n, inp n)
                     ix      :  ix 0 = 0,   j < g → ix j < ix(j + 1),   j ≤ g → seq j = all(ix j)      数えるフレーム j は all(ix j) で終わる
                     ctl     :  n + 1 < ix g  →  controllable(all(n + 1))
                     clean   :  n < ix g  →  ∀ k,  CleanK(tr_n(k))                 tr_n:  all n からのフレームの命令
fm j  :=  all(ix j − 1),   pad j  :=  inp(ix j − 1)                       数えるフレーム j が始まる機械と、その入力
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 操作できるときの機械
Frames.ends       :  keep  →  ∀ j,  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
Frames.all_start  :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ n < ix g,  FrameStart_K(all n)  ∧  Watched(all n)
Frames.all_watched:  同じもの   →   ∀ n ≤ ix g,  Watched(all n)
Frames.run        :  同じもの   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  同じもの   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  同じもの   →   ∀ j ≤ g,  Watched(seq j)

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  同じもの  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  同じもの  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` は機械から読んだ `posP(seq(j − 1))` です（`frames.reads`）。`AtCtl(seq 0)` は本物の走りの上の定理 `ControlStart.EndRun.atCtl` です。横の土管から出る切り替えの段から出ます（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。

`Frames.all_start` は `n` についての帰納法です。数えるかどうかによらず、全部のフレームをたどります。フレーム `n` は `all n` で `FrameStart_K` と `Watched` で始まります。`all(n + 1)` で終わります（`next`）。`keep_frame_start` が `FrameStart_K(all(n + 1))` と `Watched(all(n + 1))` を出します。`Known_K(all(n + 1))` は `ctl` からです。触るフレームは最後のフレーム（`n = ix g − 1`）で、操作中に終わることを聞きません。そこでルーチンが変わるからです。`keep_frame` はそれなしで `Watched(all(ix g))` を出します（`Frames.all_watched`）。数えるフレームについての定理は、これを `seq j = all(ix j)` と `fm j = all(ix j − 1)` で読みます。`ix` は増えるので `ix j ≤ ix g` です（`Frames.ix_mono`）。

## 抽象機械の歩き

`PipeWrites` の歩きと同じです。書く先がわからない書き込みは `Prot_K` の外のバイトを全部忘れます。ジャンプのルーチンでは添え字を表の項目に分けます。時間には上限をつけます。始まりは `PipeWrites` の状態に、城のバイトが 0 で端数の下 4 ビットが 0 とわかっていることを足したものです。どの道もフレームの終わりで、`Watched` がわかっていることと、フレームの始まりの状態であること（`endOK`）を確かめて終わります:

```
endOK(B)  :=  pc(B) = 待ちのループ  ∧  S(B) = S₀  ∧  ((lo = hi = 0  ∧  ¬vblank  ∧  ¬nmi)  ∨  (1 ≤ lo  ∧  hi ≤ 9  ∧  vblank  ∧  nmi))
              ∧  ppuCtrl(B) のビット 7 が 1 とわかる  ∧  ¬strobe(B)
```

`start_of_sim` は、`endOK(B)` と、`B` が覆う機械と、その機械の `Known_K` から `FrameStart_K` を出します。歩きはフレームの終わりで `Known_K` を知りません。表のキーにはルーチンのバイトがありますが、モードとタスクはありません。ですから表はモードとタスクについて状態をまとめてしまいます。表の 46,573 の状態のうち 45,808 は、モードとタスクを知りません。`GameCoreRoutine` が `GameRoutines`（ルーチンのバイトのルーチン）から戻るところと、`PlayerSubs` が当たり判定のルーチンから戻るところで、まとめるときに失われます。ですから `Known_K` はフレームの終わりの条件（`ctl`）として残ります。

**`ctl` を 1 バイト（ルーチン）にできるか.** できません。モードとタスクをキーに入れると（試しのプログラムで、証明の一部ではありません）、表は 46,576 の状態、歩きは 3.3 秒で、フレームのどの終わりでも 3 つのバイトがわかります。終わりは 34 個で、3 つのバイトの組は 17 種類です。そのうち 4 個は、ルーチンが操作のもので、タスクが 0 です。2 個はモードがゲーム、2 個はモードが 2 です。歩きはこれらを `ChgAreaMode`（面の切り替え: タスク 0）と `HandleAxeMetatile`（斧: タスク 0 とモード 2）で書きます。どちらもルーチンのバイトは書きません。ですから、フレームの終わりでルーチンが操作のものでも、操作中とは言えません。タスクがゲームのコアのものである終わりでは、どれもモードはゲームのものです。ですから `ctl` から外せるのはモードだけです。`ctl` は 3 つのバイトのままにしました。

この歩きだけのステップが 2 つあります。

* **下のビットの足し算.** `A` の下 4 ビット、バイトの下 4 ビット、キャリーがわかっている `ADC zp` は、和の下 4 ビットがわかります: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16`（`s_adcL`、`adc` に対して証明）。移動のルーチンはこうして `16·v` を足します。速さを 4 回左にずらしたものは下 4 ビットが 0 です。
* **移動のルーチンの添え字.** その入り口で、わからない添え字 `X` を 9 つに分けます: `X = 0`、または `X` の一番下の 1 のビットがビット `b`（`b = 0, …, 7`）。`X = 0` なら書く先がわかります。`X ≠ 0` なら `PipeWrites` のいつもの書き込みで、`CleanK` がその書く先は `Plain` だと言います。プレイヤーの移動は `X` をジャンプ台の制御からとります。9 つに分けるので、そのバイトに条件は要りません。

チェック `keepCheck`（非公開の証明では `keep_check`）。フレームの終わりの状態は 10 種類で、どれも `endOK` です。

| 歩き | ステップ | 分かれ | 失敗 | 表 | 時間 |
|---|---|---|---|---|---|
| 城の旗と端数、9 つに分ける、終わりで `endOK` | 707,685 | 69,404 | 0 | 46,573 | プログラムでチェック 3.8 秒、`Proof.FrameKeep` 5.0 秒 |
| 同じもので、ジャンプ台の制御が始まりで 0 とわかり `Prot_K` にある（前の回） | 1,044,377 | 101,574 | 0 | 79,266 | プログラムでチェック 4.9 秒 |
| 城の旗だけ、分けない | 907,094 | 92,482 | 0 | 72,016 | チェック 4.5 秒 |
| 城の旗と端数、`X` を 256 の値に分ける | 9,779,840 | 767,686 | 0 | 355,602 | チェック 32 秒 |

## 本物のフレームで

最後の変更のあとの `keep-frames-check FM2 100` です（終了コード 0、悪いもの 0）。地上で操作できるときから触るまでの全部のフレーム（触るフレームも入れて、数えるかどうかによらず）です。はじめの 4 種類の走りは Start がないので `lag` のフレームはありません。5 番目は 1 つのフレームで Start を押し、10〜49 フレームあとにもう一度押します。これは旗まで行きません。最後のものはムービーのフレーム 1002〜1091 から始め、1 つのフレームで Start を押し、ポーズのタイマーのあと、44〜73 フレームあとにもう一度押します。ゲームは続きます。この走りのうち 241 が旗に触り、触る前にポーズ中のフレームが 12,671 あります。

| 走り | 走りの数 | フレーム | 命令 | 触り |
|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 1,203,506 | 1 |
| 操作からランダムな入力 | 100 | 29,102 | 150,058,083 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力 | 400 | 46,025 | 183,000,496 | 216 |
| 画面の左端へ入ってからランダム | 120 | 35,945 | 193,591,853 | 0 |
| 操作からポーズのあるランダムな入力 | 100 | 37,395（ポーズ中 26,341） | 107,816,920 | 0 |
| ムービーのフレーム 1002〜1091 からポーズのあるランダムな入力 | 400 | 76,106（ポーズ中 24,517） | 250,174,812 | 241 |

* どのフレームも `FrameStart_K` を満たし、`Watched` で始まります。どの命令も `CleanK` を満たします。どのフレームも `Watched` で終わります。
* 操作のルーチンで終わるフレームはどれも、`controllable` で終わります。旗に触る走りでは、触るフレームの前のどのフレームも、ポーズ中のものも、操作のルーチンで終わります。ですからこれらの走りで `ctl` が成り立ちます。
* `q` で `X = 0` の書き込みは、ポーズ中でないどのフレームにも 1 回あります。プレイヤーの移動です。添え字かポインタを通すほかの書き込みは `Prot_K` に触れません。
* 命令の一番遅いドットは 66,674 で、上限 `dotsPerFrame − 64` より下です。

## 仮定（Lean で証明していないもの）

* **`keep.clean`: 触るまでの各フレーム（数えるかどうかによらず）の各命令の `CleanK`.** `PipeWrites` の条件に、3 つのバイトを `Prot_K` に足し、プレイヤーの書き込みを聞かないことにしたものです。上の本物のフレームで確かめました。
* **`keep.ctl`: 触るフレームの前の各フレーム（数えるかどうかによらず）は操作中に終わる.** 1 つの状態の 3 つのバイト（ルーチン、モード、タスク）です。歩きはフレームの終わりでこれらを知りません。ルーチンのバイトだけでは足りません（上）。
* **`keep.all`、`keep.inp`、`keep.next`、`keep.ix`: フレームは操作できるときから続く本物のフレームで、数えるフレーム `j` は `seq j` で終わる.** 走りがどの機械でできているかを言うものです。

仮定でなくなったもの: `fracStep`（各フレームは位置を 1/16 ピクセルの倍数だけ動かす）、そのあと `noCastle` と `keep.start`、そのあと `keep.ends`（`Frames.ends`）、`keep.lag` と `keep.lagStart`（`Frames.all_start`）。`CleanK` と `FrameStart_K` はもうジャンプ台の制御を名指ししません。新しいもの: `keep`（`all`、`inp`、`next`、`ix`、`ctl`、`clean`）と ROM のチェック `keepCheck`、`ControlStart.ctlCheck`。

**変えたことで多く聞くもの.** `ctl` と `clean` は、数えるフレームに聞くことを `lag` のフレームにも聞くようになりました。操作中に終わらない `lag` のフレームは `ctl` の外です。コードによると、大きいマリオがダメージを受けたあとの、タイマーを止める制御のフレームがそうです。ダメージはダメージのルーチンとタイマーを止める制御を一緒に書きます。前の `lag` と `lagStart` は、城の旗、端数の下のビット、操作中のフレームの始まりが `lag` のフレームを通って保たれることだけを聞いていました。ですからそういう走りでも成り立ちえました。ポーズ中のフレームは操作中に終わります。

**ファイル.** `Theorems/FrameKeep.lean`、`Theorems/ControlStart.lean`、`Theorems/PoleJoin.lean`、非公開の `Proof/FrameKeep.lean`、`Proof/ControlStart.lean`。

**確かめ方.**
```
.lake/build/bin/smbrta keep-check                     # 歩きをプログラムで（約 10 秒）
.lake/build/bin/smbrta keep-frames-check FM2 100      # 本物のフレームで条件を（約 4 分）
```
