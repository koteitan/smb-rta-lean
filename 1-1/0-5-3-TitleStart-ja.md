[← Back](README-ja.md) | [English](0-5-3-TitleStart.md) | [Japanese](0-5-3-TitleStart-ja.md)

# タイトルの Start から操作できるまで

**命題.** タイトル画面で Start を押したところからの走りを考えます。各フレームの入力は何でもよく、Start も押してよいです。押したフレームのあとの機械が 1 つの条件を満たすとします。すると、最初に操作できるフレームの前のフレーム（道筋のフレーム 0）は、タイマー 401、インターバルタイマーの位相 2、急ぎの音楽なしで始まります。操作できるときの速さは 0 です。

**これは仮定つきの定理です.** 仮定は `TitleStart.Begin` のフィールドで、下に全部挙げます。押したときの条件は 1 つの状態の条件です。これは [電源から Start を押すまで](0-5-4-TitleBoot-ja.md) の電源からの走りについては定理になりました（`Begin.press`）。ウォームブートの印がないか 2 バイトが 0 の RAM、押す前に Start も Select もない、フレーム 32 から 508 で Start、という走りです。ほかの走りでは、まだ仮定です（`boot` の 2 つ目の場合）。本物の 339 通りで確かめました。Start がないことを求めるフィールドはありません。フレーム 0 も含めて、どのフレームでも Start を押してよいです。フレーム 0 を操作まで歩くほかのファイルの確かめ（`StartRun`、`EntryKeep`、`HurryMusic`）は、近い状態と止まった状態からどの入力でも歩きます（`frame0Check`、`Begin.frame0`）。

これまで `Route.Run` にはフィールド `zero`（フレーム 0 が始まるときのタイマーと位相）、`Route.Pipe` には `still`（操作できるときの速さ）、`HurryMusic.Run` には `zero` と `quiet₀` がありました。これらは定理になりました: `Route.Run.zero`、`Route.Run.still`、`HurryMusic.Run.zero`、`HurryMusic.Run.quiet₀`。

## ゲームがすること

押したあと、ゲームは RAM を消し、「WORLD 1-1」の画面を描きます。そして画面のタイマー `ScreenTimer` が切れるまで待ちます。このタイマーは、インターバルタイマーの位相が一回りするとき（21 フレームごと）にだけ進みます。なので、押したときの位相が何でも、待ちは同じ位相で終わります。そのあとレベルを描き、ゲームコアが 2 フレーム動き（タイマーはレベルのヘッダーから読みます）、操作できるようになります。押してからフレーム 0 までは、押したときの位相によって 153 から 173 フレームです。

ゲームコアのフレームで Start を押すとポーズします（`PauseRoutine`。フレームの中でコアのルーチンより前）。ポーズしたフレームは音、パッドの読み取り、ポーズのルーチンを動かし、タイマー、フレームカウンタ、モードのルーチンを飛ばします。なのでコアの 2 フレーム、位相、タイマーは待ちます。ポーズの音が `PauseModeFlag` を立て、そのあいだ音楽は鳴りません。43 フレーム以上あと（`GamePauseTimer`）にもう一度 Start を押すとポーズが終わり、ポーズの音がまた 42 フレーム鳴ります。なのでポーズは操作を遅らせるだけです。フレーム 0 はあとに来て、タイマー、位相、音楽のバイトは同じです。

## 定理

`tm n` は押してから `n` フレームあとの機械、`ti n` はその入力です。`seq`、`inp` はフレーム 0 からの道筋の機械と入力です（`base.seq`、`base.inp`）。`x` は基準の機械です。電源を入れ、39 フレームは何も押さず、フレーム 39 で Start を押し、そのフレームのあとの機械です。

```
Press(m)  :  m はフレームの始まりで何もしないループにいる（x のプログラムカウンタとスタックポインタ、ドット < 10、NMI はフレームの始まりのとおり）、
             ポーズしていない、そして  ∀ i ∈ K,  m[i] = x[i]
K         =  x から何も押さずに走るとき、操作できるまでに書く前に読むバイト  から  自由なバイトを除いたもの、
             と PauseSoundBuffer
自由      =  FrameCounter、IntervalTimerControl、PseudoRandomBitReg（7）、NumberOfPlayers、TopScoreDisplay（6）、点数のあとの 3 バイト、
             Timers（36）、JoypadBitMask（2）、HorizontalScroll、VerticalScroll、SprShuffleAmtOffset、SprDataOffset（15）、Mirror_PPU_CTRL_REG1
```

`K` は 54 バイトです。音のキューとバッファ、画面のバッファの頭、ワールドとレベルとエリア、プレイヤーの大きさと状態、タイマーのフラグ、モードとタスク、ポーズのバイト、点数、レベルの番号です（`AreaNumber`。15 回目に加えた。走りは操作までにこれを読みませんが、縦の土管の入口がその値を使います。1-1-b-3-4-5）。ほかのバイトは全部自由です。

`PauseSoundBuffer`（鳴っているポーズの音）は `K` に新しく入れました。何も押さない走りはこれを読みませんが、ポーズする走りはポーズの次のフレームで読みます。分からないままだと、抽象機械はポーズの音が `PauseModeFlag` を立てない道を通れます。すると音楽がどんなに長いポーズのあいだも鳴り、探索が終わりません。本物の走りではタイトル画面でいつも 0 です。音のエンジンが各ポーズの音の終わりに消し、電源とリセットも消します。`GamePauseStatus` はもとから `K` にあります。始まりの状態は、いまはそのビットを全部知っています（前はビット 0 だけでした）。

`TitleStart.Begin` のフィールドです。

```
next      tm(n + 1) = frame(tm n, ti n)
boot      TitleBoot.Start(tm 0)  =  power(TitleBoot.Run(tm 0))  |  press(Press(tm 0))
              power: 1 つの状態（電源を入れたときの機械）と、押すまでの 1 つずつの入力。 press: 前と同じ 1 つの状態
atZero    tm(pre) = seq 0,  ti(pre) = inp 0
first     n ≤ pre  ⟹  ¬ctl(tm n)
ctl       ctl(seq 1)
```

定理です（`title_check` は ROM での確かめで、`native_decide` によります）。

```
Begin.press    :  Press(tm 0)                                                       （前はフィールド press。boot から、TitleBoot の段で）
Begin.zero     :  seq 1 = frame(seq 0, inp 0)  ⟹  timer(seq 0) = 401,  phase(seq 0) = 2,  EventMusicQueue = EventMusicBuffer = NoteLengthTblAdder = 0
Begin.timer    :  timer(seq 0) = t0  ∧  phase(seq 0) = 2
Begin.still    :  v(seq 1) = 0
Begin.anyNear  :  seq 0 は近い状態か止まった状態にある,  v(seq 1) = 0               （どの入力でも）
Begin.frame0   :  frame0Check(fin)  ⟹  フレーム 0 の終わりは fin を満たす          （どの入力でも。StartRun、EntryKeep、HurryMusic が使う）
Route.Run.zero, Route.Run.still              Run.title と定理 Run.pipeAt（pipe.fm 1 = base.seq 1）から
HurryMusic.Run.zero, HurryMusic.Run.quiet₀   Run.title から
```

## 証明

抽象機械が多くの機械を一度に追います。いくつかのビットは分かっていて、ほかは分かりません。分からないビットでの分かれ道は両方に進みます（`TaintRun`。RAM を消すフレームはルーチンの途中で終わるので、`SideChangeEnd` のフレームの終わりをまたぐ進め方を使います）。探索で、1 フレームで閉じたフレームの始まりの状態の集まりを見つけます。

* 始まりの状態（`Press` から）は集まりの中にある。
* 遠い状態（582 個）: どの入力でも、フレームの終わりは全部、集まりの状態で、操作できない。
* 近い状態（8 個）と止まった状態（2 個）: どの入力でも、フレームの終わりは全部、操作できて速さ 0 を知っているか、操作できない集まりの状態。タイマーの数字 4、0、1、位相 2、音楽の 3 バイト 0 を知っている。

近い状態は、ポーズなしの 4 個と、ポーズが終わった直後の 4 個（`GamePauseStatus` = 128、`GamePauseTimer` = 43: 次の 43 フレームは Start が効かない）です。止まった状態は、プレイヤーの登場のルーチンでポーズしている状態です。Start でポーズが終わり、同じフレームで操作できます。Start がなければ、近い状態のフレームは操作できて終わり、止まった状態のフレームはポーズのまま操作できずに終わります（2 つの歩き。いまはどの定理も使いません）。

探索は証明の一部ではありません。`check` が集まりのすべての状態と、表のすべての状態（17,591 個）を歩きます。ネイティブで約 4 秒です（探索 1.8 秒、歩き 2.5 秒）。`check` にはいまは `TitleBoot` の段も入っています（約 4 秒増えて、全部で約 8 秒です）。そこから帰納法で、入力が何でも、`n ≤ pre` の `tm n` は全部集まりの中にあります（`Begin.inSet`）。フレーム 0 より前に操作できて終わるフレームは `first` が除きます。`tm pre` は遠い状態ではありません。そのフレームで操作できるからです（`ctl`）。なので近い状態か止まった状態で（`Begin.anyNear`）、バイトと速さが出ます。

前に探索が終わらなかったわけ: 前の回、Start を許すと集まりは 6,852 個を超えても閉じませんでした。始まりの状態は `GamePauseStatus` のビット 0 しか知らず、`PauseSoundBuffer` は何も知りませんでした。するとポーズで `PauseModeFlag` が 0 のままの道を通れて、ポーズのあいだ音楽が鳴り、曲の各フレームが新しい状態を作りました。

## 本物の走りで

`title-check FM2`、終了コード 0 です。押し方: タイトルの 30 から 624 フレームのあとの Start（100 通り）、A と Start（10 通り）、タイトルで乱数のボタンと、操作できるまで Start も含む乱数のボタン（200 通り）、ゲームコアの 1 つ目か 2 つ目のフレームで 43 から 200 フレームのポーズ、押す時を 8 通り（64 通り）、ゲームオーバーのあとのタイトル。何も押さないか、ゲームの最初の 3000 フレームでポーズする（6 通り）、動画の 150 フレームごとにリセットしてから Start（12 通り）。フレーム 0 では、ゲームコアの Start は、なくても操作できるなら外します。そこで Start が要るとき（ポーズを終わらせるとき）は残します。

```
走り                                         392
3000 フレームで操作できない                  53   （フレーム 30 の Start か、デモ中。乱数の Start でポーズし続ける）
押したあとが Press を満たす                  339 のうち 339
フレーム 0 か操作のときが確かめと違う        0
フレーム 0 より前にポーズしたフレームがある  117  （ポーズしたフレームは最大 200）
フレーム 0 に Start がある                   60   （バイトと速さは確かめのとおり）
押してからフレーム 0 まで                    ポーズなしで 153 から 173 フレーム、ポーズありで最大 373
動画そのものの押し方                         Press を満たす。フレーム 0 はタイマー 401、位相 2、音楽なし。操作できるとき速さ 0
```

## 証明していないこと

* `press` は、[電源から Start を押すまで](0-5-4-TitleBoot-ja.md) の電源からの走りについては証明しました。押したときの `PauseSoundBuffer` = 0 もその一部です。ほかの走り（押す前の Select や Start、最初のデモのあとに押す、ゲームオーバーやリセットのあとのタイトル）では、まだ 1 つの状態の仮定です（`boot` の場合 `press`）。上の 339 通りでは全部成り立ちます。タイトルが別のワールドを示す走り（ゲームオーバーのあとの A と Start）や、`K` のバイトが別の値の走りは外です。電源からフレーム 31 で押す走りも外です。ゲームは `FetchNewGameTimerFlag` = 2 で始まり、`Press` は 1 を求めます。その走りでもフレーム 0 と操作は定理のとおりです。
* フィールド `noPause`（フレーム 0 で Start を押さない）がありましたが、なくしました。`StartRun.titleCheck` と `EntryKeep.nearCheck` を、`HurryMusic.nearCheck` と同じく `frame0Check`（近い状態と止まった状態からどの入力でも、フレーム 0 の終わりは全部、その条件を満たすか遠い状態）にし、`Begin.near` の代わりに `Begin.frame0` を使います。どちらの確かめも証明のビルドで通ります。
* `atZero`、`first`、`ctl` はどの機械がフレーム 0 かです。列の作り方から成り立ちます。`pipeAt` はもう欄ではありません。`pipe` は機械を `base` からとり、数えるフレーム 1 はフレーム 1 です（定理 `Run.pipeAt`）。

**ファイル.** `Theorems/TitleStart.lean`、`Theorems/TitleBoot.lean`、`Theorems/Route.lean`（`Run.title`、`Run.pipeAt`、`Run.zero`、`Run.still`）、`Theorems/HurryMusic.lean`、非公開の `Proof/TitleStart.lean`。

**再現.**
```
.lake/build/bin/smbrta title-check FM2
```
