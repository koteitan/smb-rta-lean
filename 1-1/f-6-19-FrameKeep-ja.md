[← Back](README-ja.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# 操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ

**主張.** 操作中に始まる 1 フレーム全体は 2 つのことを保ちます。城の旗は立ちません。位置の端数は 1/16 ピクセルの倍数のままです。またフレームは、歩きに見える範囲で、操作中の次のフレームの始まりで終わります。待ちのループにいて、スタックポインタ、ドット、PPU がフレームの始まりのものです。これはどの機械、どの入力についても成り立つ定理です。条件はフレームの始まりの 1 つの状態と、フレームの各命令の 1 つの条件です。証明は [`PipeWrites`](a-5-2-PipeWrites-ja.md) と同じように、`TaintRun.lean` の抽象機械でフレーム全体を追います。

ですから `PoleJoin.Run` の仮定 `fracStep` はなくなりました。定理 `Run.fracP` です。走りのフレーム（フィールド `keep`）と ROM のチェックから出ます。フィールド `noCastle` もなくなりました。操作できるときの機械から出る定理 `Run.noCastle_of` です（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。フィールド `keep.start`（各フレームは操作中に始まる）もなくなりました。定理 `Frames.start` です。それにはもっと小さいフィールド `keep.ctl` が要ります。触る前の各フレームは操作中に終わる、というものです。

`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` はその中で `n` 命令あとの機械です。`seq j` は数えるフレーム `j` の終わりの機械で、`seq 0` は地上で操作できるときの機械です。

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

Frames (keep)     :  fm j, pad j                       数えるフレーム j が始まる機械と、その入力
                     ends    :  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
                     ctl     :  1 ≤ j < g  →  controllable(seq j)
                     clean   :  1 ≤ j ≤ g  →  ∀ n,  CleanK(tr_j(n))
                     lag     :  1 ≤ j ≤ g  →  Watched(seq(j − 1))  →  Watched(fm j)
                     lagStart:  1 ≤ j ≤ g  →  FrameStart_K(seq(j − 1))  →  FrameStart_K(fm j)
AtCtl(m)          :=  FrameStart_K(m)  ∧  castle(m) = false                 操作できるときの機械
Frames.run        :  keepCheck,  keep,  FrameStart_K(seq 0),  Watched(seq 0)   →   ∀ j < g,  FrameStart_K(seq j)  ∧  Watched(seq j)
Frames.start      :  同じもの   →   ∀ j,  1 ≤ j ≤ g  →  FrameStart_K(fm j)
Frames.watched    :  同じもの   →   ∀ j ≤ g,  Watched(seq j)

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  AtCtl(seq 0),  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  同じもの  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  同じもの  →  ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` は機械から読んだ `posP(seq(j − 1))` です（`frames.reads`）。`AtCtl(seq 0)` は本物の走りの上の定理 `ControlStart.EndRun.atCtl` です。横の土管から出る切り替えの段から出ます（[地上で操作できるときの機械](f-6-2-ControlStart-ja.md)）。

`Frames.run` は `j` についての帰納法です。フレーム `j + 1` は `fm(j + 1)` で始まります。`lagStart` と `lag` が `seq j` の `FrameStart_K` と `Watched` をそこへ運びます。フレームは `seq(j + 1)` で終わります。`keep_frame_start` が `FrameStart_K(seq(j + 1))` を出します。`Known_K(seq(j + 1))` は `ctl` からです。触るフレーム `g` には、操作中に終わることを聞きません。そこでルーチンが変わるからです。

## 抽象機械の歩き

`PipeWrites` の歩きと同じです。書く先がわからない書き込みは `Prot_K` の外のバイトを全部忘れます。ジャンプのルーチンでは添え字を表の項目に分けます。時間には上限をつけます。始まりは `PipeWrites` の状態に、城のバイトが 0 で端数の下 4 ビットが 0 とわかっていることを足したものです。どの道もフレームの終わりで、`Watched` がわかっていることと、フレームの始まりの状態であること（`endOK`）を確かめて終わります:

```
endOK(B)  :=  pc(B) = 待ちのループ  ∧  S(B) = S₀  ∧  ((lo = hi = 0  ∧  ¬vblank  ∧  ¬nmi)  ∨  (1 ≤ lo  ∧  hi ≤ 9  ∧  vblank  ∧  nmi))
              ∧  ppuCtrl(B) のビット 7 が 1 とわかる  ∧  ¬strobe(B)
```

`start_of_sim` は、`endOK(B)` と、`B` が覆う機械と、その機械の `Known_K` から `FrameStart_K` を出します。歩きはフレームの終わりで `Known_K` を知りません。表は待ちのループの状態を、ルーチン、モード、タスクについてまとめてしまいます。ですから `Known_K` はフレームの終わりの条件（`ctl`）として残ります。この歩きだけのステップが 2 つあります。

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

最後の変更のあとの `keep-frames-check FM2 100` です（終了コード 0、悪いもの 0）。地上で操作できるときから触るまでの全部のフレーム（触るフレームも入れて）です。はじめの 4 種類の走りは Start がないので `lag` のフレームはありません。最後のものは 1 つのフレームで Start を押し、10〜49 フレームあとにもう一度押します。

| 走り | 走りの数 | フレーム | 命令 | 触り |
|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 1,203,506 | 1 |
| 操作からランダムな入力 | 100 | 29,102 | 150,058,083 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力 | 400 | 46,025 | 183,000,496 | 216 |
| 画面の左端へ入ってからランダム | 120 | 35,945 | 193,591,853 | 0 |
| 操作からポーズのあるランダムな入力 | 100 | 37,395（ポーズ中 26,341） | 107,816,920 | 0 |

* どのフレームも `FrameStart_K` を満たし、`Watched` で始まります。どの命令も `CleanK` を満たします。どのフレームも `Watched` で終わります。
* 操作のルーチンで終わるフレームはどれも、`controllable` で終わります（`ctl`）。
* `q` で `X = 0` の書き込みは、ポーズ中でないどのフレームにも 1 回あります。プレイヤーの移動です。添え字かポインタを通すほかの書き込みは `Prot_K` に触れません。
* 命令の一番遅いドットは 66,674 で、上限 `dotsPerFrame − 64` より下です。

## 仮定（Lean で証明していないもの）

* **`keep.clean`: 触るまでの各フレームの各命令の `CleanK`.** `PipeWrites` の条件に、3 つのバイトを `Prot_K` に足し、プレイヤーの書き込みを聞かないことにしたものです。上の本物のフレームで確かめました。
* **`keep.ctl`: 触る前の各フレームは操作中に終わる.** 1 つの状態の 3 つのバイト（ルーチン、モード、タスク）です。歩きはフレームの終わりでこれらを知りません。
* **`keep.ends`: 数えるフレーム `j` は `seq j` で終わる.** `fm j` は `seq(j − 1)` か、`lag` のフレームのあとです。
* **`keep.lag`、`keep.lagStart`: 数えるフレームの前の `lag` のフレームは、城の旗、端数の下 4 ビット、操作中のフレームの始まりを保つ.** 上のポーズのある走りでは保ちます。

仮定でなくなったもの: `fracStep`（各フレームは位置を 1/16 ピクセルの倍数だけ動かす）、そのあと `noCastle` と `keep.start`。`CleanK` と `FrameStart_K` はもうジャンプ台の制御を名指ししません。新しいもの: `keep`（`ends`、`ctl`、`clean`、`lag`、`lagStart`）と ROM のチェック `keepCheck`、`ControlStart.ctlCheck`。

**ファイル.** `Theorems/FrameKeep.lean`、`Theorems/ControlStart.lean`、`Theorems/PoleJoin.lean`、非公開の `Proof/FrameKeep.lean`、`Proof/ControlStart.lean`。

**確かめ方.**
```
.lake/build/bin/smbrta keep-check                     # 歩きをプログラムで（約 10 秒）
.lake/build/bin/smbrta keep-frames-check FM2 100      # 本物のフレームで条件を（約 3 分）
```
