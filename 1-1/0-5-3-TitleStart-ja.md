[← Back](README-ja.md) | [English](0-5-3-TitleStart.md) | [Japanese](0-5-3-TitleStart-ja.md)

# タイトルの Start から操作できるまで

**命題.** タイトル画面で Start を押したところからの走りを考えます。押したフレームのあとの機械が 1 つの条件を満たし、操作できるまでのゲームコアのフレームで Start を押さないとします。すると、最初に操作できるフレームの前のフレーム（道筋のフレーム 0）は、タイマー 401、インターバルタイマーの位相 2、急ぎの音楽なしで始まります。操作できるときの速さは 0 です。

**これは仮定つきの定理です.** 仮定は `TitleStart.Begin` のフィールドで、下に全部挙げます。押したときの条件は 1 つの状態の条件です。本物の 301 通りで確かめましたが、全部の走りについては証明していません。

これまで `Route.Run` にはフィールド `zero`（フレーム 0 が始まるときのタイマーと位相）、`Route.Pipe` には `still`（操作できるときの速さ）、`HurryMusic.Run` には `zero` と `quiet₀` がありました。これらは定理になりました: `Route.Run.zero`、`Route.Run.still`、`HurryMusic.Run.zero`、`HurryMusic.Run.quiet₀`。

## ゲームがすること

押したあと、ゲームは RAM を消し、「WORLD 1-1」の画面を描きます。そして画面のタイマー `ScreenTimer` が切れるまで待ちます。このタイマーは、インターバルタイマーの位相が一回りするとき（21 フレームごと）にだけ進みます。なので、押したときの位相が何でも、待ちは同じ位相で終わります。そのあとレベルを描き、ゲームコアが 2 フレーム動き（タイマーはレベルのヘッダーから読みます）、操作できるようになります。押してからフレーム 0 までは、押したときの位相によって 153 から 173 フレームです。

## 定理

`tm n` は押してから `n` フレームあとの機械、`ti n` はその入力です。`seq`、`inp` はフレーム 0 からの道筋の機械と入力です（`chg.seq`、`chg.inp`）。`x` は基準の機械です。電源を入れ、39 フレームは何も押さず、フレーム 39 で Start を押し、そのフレームのあとの機械です。

```
Press(m)  :  m はフレームの始まりで何もしないループにいる（x のプログラムカウンタとスタックポインタ、ドット < 10、NMI はフレームの始まりのとおり）、
             ポーズしていない、そして  ∀ i ∈ K,  m[i] = x[i]
K         =  x から何も押さずに走るとき、操作できるまでに書く前に読むバイト  から  自由なバイトを除いたもの
自由      =  FrameCounter、IntervalTimerControl、PseudoRandomBitReg（7）、NumberOfPlayers、TopScoreDisplay（6）、点数のあとの 3 バイト、
             Timers（36）、JoypadBitMask（2）、HorizontalScroll、VerticalScroll、SprShuffleAmtOffset、SprDataOffset（15）、Mirror_PPU_CTRL_REG1
```

`K` は 52 バイトです。音のキューとバッファ、画面のバッファの頭、ワールドとレベルとエリア、プレイヤーの大きさと状態、タイマーのフラグ、モードとタスク、ポーズのバイト、点数です。ほかのバイトは全部自由です。

`TitleStart.Begin` のフィールドです。

```
next      tm(n + 1) = frame(tm n, ti n)
press     Press(tm 0)                                                          （1 つの状態）
atZero    tm(pre) = seq 0,  ti(pre) = inp 0
noPause   n ≤ pre,  OperMode_Task(tm n) = ゲームコア  ⟹  ti n に Start がない        （2 フレーム）
first     n ≤ pre  ⟹  ¬ctl(tm n)
ctl       ctl(seq 1)
```

定理です（`title_check` は ROM での確かめで、`native_decide` によります）。

```
Begin.zero     :  seq 1 = frame(seq 0, inp 0)  ⟹  timer(seq 0) = 401,  phase(seq 0) = 2,  EventMusicQueue = EventMusicBuffer = NoteLengthTblAdder = 0
Begin.timer    :  timer(seq 0) = t0  ∧  phase(seq 0) = 2
Begin.still    :  v(seq 1) = 0
Route.Run.zero, Route.Run.still              Run.title と Run.pipeAt（pipe.fm 1 = chg.seq 1）から
HurryMusic.Run.zero, HurryMusic.Run.quiet₀   Run.title から
```

## 証明

抽象機械が多くの機械を一度に追います。いくつかのビットは分かっていて、ほかは分かりません。分からないビットでの分かれ道は両方に進みます（`TaintRun`。RAM を消すフレームはルーチンの途中で終わるので、`SideChangeEnd` のフレームの終わりをまたぐ進め方を使います）。探索で、1 フレームで閉じたフレームの始まりの状態の集まりを見つけます。

* 始まりの状態（`Press` から）は集まりの中にある。
* 遠い状態（404 個）: フレームの終わりは全部、集まりの状態で、操作できない。
* 近い状態（4 個）: フレームの終わりは全部、操作できて、速さ 0 を知っている。タイマーの数字 4、0、1、位相 2、音楽の 3 バイト 0 を知っている。

ゲームコアの中（遠い状態の 2 個と近い状態）では、`noPause` のとおり入力に Start がありません。

探索は証明の一部ではありません。`check` が集まりのすべての状態と、表のすべての状態（13,221 個）を歩きます。ネイティブで約 4 秒です。そこから帰納法で、`n ≤ pre` の `tm n` は全部集まりの中にあります（`Begin.inSet`）。近い状態ならフレーム 1 より前に操作できてしまいます（`first`）。`tm pre` は遠い状態ではありません。そのフレームで操作できるからです（`ctl`）。なので近い状態です（`Begin.near`）。

## 本物の走りで

`title-check FM2`、終了コード 0 です。押し方: タイトルの 30 から 624 フレームのあとの Start（100 通り）、A と Start（10 通り）、タイトルで乱数のボタンと、操作できるまで乱数のボタン、ただしゲームコアでは Start なし（200 通り）、動画の 150 フレームごとにリセットしてから Start（12 通り）。

```
走り                                     322
600 フレームで操作できない               21   （フレーム 30 の Start か、デモ中: 押したことにならない）
押したあとが Press を満たす              301 のうち 301
フレーム 0 か操作のときが確かめと違う    0
押してからフレーム 0 まで                153 から 173 フレーム
動画そのものの押し方                     Press を満たす。フレーム 0 はタイマー 401、位相 2、音楽なし。操作できるとき速さ 0
```

## 証明していないこと

* `press` は 1 つの状態の仮定です。上の 301 通りでは全部成り立ちます。タイトルが別のワールドを示す走り（ゲームオーバーのあとの A と Start）や、`K` のバイトが別の値の走りは外です。
* `noPause` は 2 フレームの入力の条件です。そこで Start を押すとポーズします。ポーズは操作を遅らせるだけですが、Lean にはありません。探索はポーズした状態で音楽のコードで失敗します。
* `atZero`、`first`、`ctl`、`pipeAt` はどの機械がフレーム 0 かと、2 つの列が合っていることです。列の作り方から成り立ちます。

**ファイル.** `Theorems/TitleStart.lean`、`Theorems/Route.lean`（`Run.title`、`Run.pipeAt`、`Run.zero`、`Run.still`）、`Theorems/HurryMusic.lean`、非公開の `Proof/TitleStart.lean`。

**再現.**
```
.lake/build/bin/smbrta title-check FM2
```
