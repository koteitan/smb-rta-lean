[← Back](README-ja.md) | [English](f-6-19-FrameKeep.md) | [Japanese](f-6-19-FrameKeep-ja.md)

# 操作中の 1 フレーム全体は城の旗と端数の下のビットを保つ

**主張.** 操作中に始まる 1 フレーム全体は 2 つのことを保ちます。城の旗は立ちません。位置の端数は 1/16 ピクセルの倍数のままです。これはどの機械、どの入力についても成り立つ定理です。条件はフレームの始まりの 1 つの状態と、フレームの各命令の 1 つの条件です。証明は [`PipeWrites`](a-5-2-PipeWrites-ja.md) と同じように、`TaintRun.lean` の抽象機械でフレーム全体を追います。

ですから `PoleJoin.Run` の仮定 `fracStep` はなくなりました。定理 `Run.fracP` になりました。走りのフレーム（新しいフィールド `keep`）と ROM のチェックから出ます。`noCastle` も、その最初の状態から出ます（`Run.noCastle_of`）。ただしこの回はフィールドのままです。`Route` はチェックをとらない `Run.afterTouch` を使うからです。

`frame(m, i)` は入力 `i` の本物の 1 フレームです。`tr(n)` はその中で `n` 命令あとの機械です。`seq j` は数えるフレーム `j` の終わりの機械で、`seq 0` は地上で操作できるときの機械です。

```
castle(m)        :=  StarFlagTaskControl(m) ≠ 0
f(m)             :=  SprObject_X_MoveForce(m)                         位置の端数（1/256 ピクセル単位）
Watched(m)       :=  castle(m) = false  ∧  f(m) mod 16 = 0
q                :=  MoveObjectHorizontally の最初の STA abs,X        端数を書く命令
Prot_K           :=  PipeWrites の Prot  ∪  {StarFlagTaskControl, SprObject_X_MoveForce, JumpspringAnimCtrl}
FrameStart_K(m)  :=  PipeWrites の FrameStart（待ちのループ、スタック、ドット、PPU、ルーチン = 操作、OperMode、OperMode_Task）  ∧  JumpspringAnimCtrl(m) = 0
CleanK(m)        :=  store:  添え字かポインタを通して書く命令、書く先 t:   ¬(pc(m) = q ∧ X(m) = 0)  →  Plain(Prot_K, t)
                     read, jump, time:  PipeWrites の `Clean` と同じ
```

`Plain(Prot_K, t)` は、その書き込みが `Prot_K` のバイトを変えないことです。`q` で `X = 0` の書き込みはプレイヤー自身の端数の書き込みなので、聞きません。

```
keep_frame        :  keepCheck,  FrameStart_K(m),  Watched(m),  (∀ n,  CleanK(tr(n)))   →   Watched(frame(m, i))

Frames (keep)     :  fm j, pad j                       数えるフレーム j が始まる機械と、その入力
                     ends :  1 ≤ j ≤ g  →  seq j = frame(fm j, pad j)
                     start:  1 ≤ j ≤ g  →  FrameStart_K(fm j)
                     clean:  1 ≤ j ≤ g  →  ∀ n,  CleanK(tr_j(n))
                     lag  :  1 ≤ j ≤ g  →  Watched(seq(j − 1))  →  Watched(fm j)
Frames.watched    :  keepCheck,  keep,  Watched(seq 0)   →   ∀ j ≤ g,  Watched(seq j)

Run.watched₀      :  Start(seq 0),  fracCheck,  castle(seq 0) = false   →   Watched(seq 0)
Run.fracP         :  Start(seq 0),  fracCheck,  keepCheck,  Run   →   ∀ j,  1 ≤ j ≤ g  →  P(j) mod 16 = 0
Run.frac          :  同じもの  →  P₂(g) mod 16 = 0
Run.noCastle_of   :  Start(seq 0),  fracCheck,  keepCheck,  castle(seq 0) = false,  Run   →   ∀ j ≤ g,  castle(seq j) = false
```

`P(j)` は機械から読んだ `posP(seq(j − 1))` です（`frames.reads`）。`Run.fracP` は `castle(seq 0) = false` をフィールド `noCastle` の `j = 0` だけからとります。

## 抽象機械の歩き

`PipeWrites` の歩きと同じです。書く先がわからない書き込みは `Prot_K` の外のバイトを全部忘れます。ジャンプのルーチンでは添え字を表の項目に分けます。時間には上限をつけます。始まりは `PipeWrites` の状態に、城のバイトが 0 で端数の下 4 ビットが 0 とわかっていることを足したものです。どの道もフレームの終わりで `Watched` がわかっていることを確かめて終わります。この歩きだけのステップが 2 つあります。

* **下のビットの足し算.** `A` の下 4 ビット、バイトの下 4 ビット、キャリーがわかっている `ADC zp` は、和の下 4 ビットがわかります: `(a + b + c) mod 16 = (a mod 16 + b mod 16 + c) mod 16`（`s_adcL`、`adc` に対して証明）。移動のルーチンはこうして `16·v` を足します。速さを 4 回左にずらしたものは下 4 ビットが 0 です。
* **移動のルーチンの添え字.** その入り口で、わからない添え字 `X` を 9 つに分けます: `X = 0`、または `X` の一番下の 1 のビットがビット `b`（`b = 0, …, 7`）。`X = 0` なら書く先がわかります。`X ≠ 0` なら `PipeWrites` のいつもの書き込みで、`CleanK` がその書く先は `Plain` だと言います。ジャンプ台の制御が始まりで 0 なので、プレイヤーの移動では `X = 0` がわかっています。

チェック `keepCheck`（非公開の証明では `keep_check`）:

| 歩き | ステップ | 分かれ | 失敗 | 表 | 時間 |
|---|---|---|---|---|---|
| 城の旗と端数、9 つに分ける | 1,044,377 | 101,574 | 0 | 79,266 | プログラムでチェック 5.3 秒、`Proof.FrameKeep` 5.5 秒 |
| 城の旗だけ、分けない | 907,094 | 92,482 | 0 | 72,016 | チェック 4.5 秒 |
| 城の旗と端数、`X` を 256 の値に分ける | 9,779,840 | 767,686 | 0 | 355,602 | チェック 32 秒 |

## 本物のフレームで

最後の変更のあとの `keep-frames-check FM2 100` です。地上で操作できるときから触るまでの全部のフレーム（触るフレームも入れて）です。入力に Start がないので `lag` のフレームはありません。

| 走り | 走りの数 | フレーム | 命令 | 触り |
|---|---|---|---|---|
| ムービーの、操作から触るまで | 1 | 240 | 1,203,506 | 1 |
| 操作からランダムな入力 | 100 | 29,102 | 150,058,083 | 0 |
| ムービーのフレーム 1002〜1091 からランダムな入力 | 400 | 46,025 | 183,000,496 | 216 |
| 画面の左端へ入ってからランダム | 120 | 35,945 | 193,591,853 | 0 |

* どのフレームも `FrameStart_K` を満たし、`Watched` で始まります。どの命令も `CleanK` を満たします。どのフレームも `Watched` で終わります。
* `q` で `X = 0` の書き込みはどのフレームにも 1 回あります。プレイヤーの移動です。添え字かポインタを通すほかの書き込みは `Prot_K` に触れません。
* 命令の一番遅いドットは 65,975 で、上限 `dotsPerFrame − 64` より下です。

## 仮定（Lean で証明していないもの）

* **`keep.clean`: 触るまでの各フレームの各命令の `CleanK`.** `PipeWrites` の条件に、3 つのバイトを `Prot_K` に足し、プレイヤーの書き込みを聞かないことにしたものです。上の本物のフレームで確かめました。
* **`keep.start`: 数える各フレームが始まるときの `FrameStart_K`.** とくにフレームは操作中に始まり、ジャンプ台の制御は 0 です。
* **`keep.ends`: 数えるフレーム `j` は `seq j` で終わる.** `fm j` は `seq(j − 1)` か、`lag` のフレームのあとです。
* **`keep.lag`: 数えるフレームの前の `lag` のフレームは城の旗と端数の下 4 ビットを保つ.**
* **`noCastle` はフィールドのまま.** `keep` とチェックがあれば、`castle(seq 0) = false` だけで足ります（`Run.noCastle_of`）。残りを消すには、`Route` が `Run.afterTouch` にチェックを渡す必要があります。

仮定でなくなったもの: `fracStep`（各フレームは位置を 1/16 ピクセルの倍数だけ動かす）。新しいもの: `keep`（`ends`、`start`、`clean`、`lag`）と ROM のチェック `keepCheck`。

**ファイル.** `Theorems/FrameKeep.lean`、`Theorems/PoleJoin.lean`、非公開の `Proof/FrameKeep.lean`。

**確かめ方.**
```
.lake/build/bin/smbrta keep-check                     # 歩きをプログラムで（約 10 秒）
.lake/build/bin/smbrta keep-frames-check FM2 100      # 本物のフレームで条件を（約 2 分）
```
