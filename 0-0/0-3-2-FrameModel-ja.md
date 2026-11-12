[← Back](../README-ja.md) | [English](0-3-2-FrameModel.md) | [Japanese](0-3-2-FrameModel-ja.md)

# 本物のフレームと横と縦のモデル

**主張.** `hstep` は 1 フレームの横の部分、`vstep` は縦の部分です。本物の機械の 1 フレーム `frame(M, i)` について、次のことを Lean で証明します。プレイヤーのルーチンに来てからスクロールの処理に行くまで、機械のバイトは `hstep` のとおりに変わり、位置は `16·v'` だけ動きます。縦のバイトは `vstep` のとおりに変わります（`vert_model`）。押している側がふさがれていると、フレームは `hstep` のとおりか、速さを 0 にします（`move_masked`）。ルーチンに来るまでとスクロールの処理のあとは、1 フレームについての前提です。

`tr(n)` は `frame(M, i)` の `n` 命令あとの機械です。`HS(m)` は機械 `m` から読んだ横の状態（速さ、subspeed、向き、動く向き、`RunningSpeed` が 0 かどうか）です。`P(m)` は位置です。`In(m)` はプレイヤーのルーチンに来た機械から読んだ入力です。`v'` は `HS(frame(M, i))` の速さです。

```
move_model  :  modelOK,  AtCtrl(R)
               →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs  ∧  HS(stepN(k, R)) = hstep(HS(R), In(R))
                              ∧  P(stepN(k, R)) ≡ P(R) + 16·v'  (mod 2²⁴)
clean_frame :  modelOK,  Clean(M, i, n₀)
               →  HS(frame(M, i)) = hstep(HS(M), In(tr(n₀)))  ∧  P(frame(M, i)) = P(M) + 16·v'
frame_read  :  modelOK,  frictionCheck,  ReadFrame(M, i, n₀)
               →  ∃ f : TopSpeed.Frame,  f は M と frame(M, i) の速さ、subspeed、位置を持つ
```

`frame_read` と `TopSpeed` の `Frame.bound` から、`|v| ≤ v_top` のとき `|v'| ≤ v_top`、`P' − P ≤ 16·v_top` です。`RoomJoin` の `move_top` はこれで定理になりました。

Lean: `Theorems/FrameWalk.lean`（2 台の機械の歩き。`tstep_spec`、`walkT_spec`、`piece_spec`、`leaf_spec`。回り道つき: `lk_detour`、`walkD_spec`、`leafD_spec`）、`Theorems/FrameModel.lean`（`move_model`、`move_masked`、`clean_frame`、`frame_read`）、`Theorems/VertModel.lean`（`vert_model`）、非公開の `frame_model`（`modelOK`、`native_decide`）。`vertOK` と `maskOK` は `SurfaceFrames.numbersCheck` の一部です。どのファイルにもゲームの値はありません。チェックはネイティブで約 2 秒、0.1 秒、0.1 秒です。

## 2 台の機械の歩き

命令は同じ場所にいる 2 台の機械の上で同時に進めます。各レジスタと各バイトについて、歩きが知っているのは次の 4 つのどれかだけです。何も知らない、2 台で同じ、2 台とも 0 か 2 台とも 0 でない、それぞれの既知のビット。値を列挙しないので、速さと subspeed は 256 × 256 通りを調べなくて済みます。命令は、読むアドレスと書くアドレスが歩きに分かるものだけ進みます。時間は見ません。ここの命令は時計を読まないからです。

* 使う命令ごとに 1 回証明します（`tstep_spec`）。ROM はチェックのときだけ見ます。
* 本物の機械と `runSub` の機械を並べると、ルーチンが両方で同じことをすると分かります（`leaf_spec`）。スタックポインタと時間が違っていても構いません。
* 同じ機械を 2 回渡すと、コードの区間がどのバイトを書かないか、どこに着くかが分かります（`piece_spec`）。

## しばらく別々に進む 2 台の機械

コードが 2 台で違うバイトを読み、そこで書くものは要らない、という場所があります。回り道（`Detour`）は次のことを言います。切れ目 `c` から、それぞれの機械が 1 台で（1 台の機械の歩きで）切れ目 `c'` に着き、`keep` のバイトを書きません。`walkD` は 2 台を上と同じに進め、回り道の始まりでは、それぞれの機械を自分の道で進めます。そのあと 2 台の命令の数は違ってよいです。

```
lk_detour  :  Detour.ok(d),  d.c での歩きの状態が m, n で成り立つ
              →  ∃ k₁ k₂ ≤ fuel(d),  d のあとの状態が stepN(k₁, m), stepN(k₂, n) で成り立つ
walkD_spec :  walkD(f, Q) = true,  Q が m, n で成り立つ
              →  ∃ k₁ k₂ ≤ f,  stop ∧ goal で、終わりの状態が stepN(k₁, m), stepN(k₂, n) で成り立つ
leafD_spec :  ルーチンの入口からの walkD、スタックポインタは 2 台で同じ
              →  ルーチンが戻るところで、タグが本物の機械と runSub の結果をつなぐ
```

`leaf_spec` はほかのルーチンを呼ばないルーチンにしか使えません。`leafD_spec` は呼んでもよいです。スタックポインタが分かっているからです。`runSub2` は同じやり方で 2 台の機械の `runSub` の結果をつなぎます。

## 縦のモデル

`vstepV(s, A, abs)` は機械 `vmach` の上の `Jump.vstep` です。`vmach` は `m0` で、スタックポインタをプレイヤーのルーチンの `S` にし、`DiffToHaltJump = 1` にしたものです。`A(R)` は `R` での `SavedJoypadBits` の 7 ビット目です。`vs(m)` は機械から読んだ縦の状態です。

```
vert_model :  vertOK,  AtCtrl0(R),  (st(R) = 1 → DTHJ(R) = 1),  PrevA(R) & 80 = A_B(R) & 80
              →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs  ∧  vs(stepN(k, R)) = vstepV(vs(R), A(R), abs(R))
                             ∧  stepN(k, R) で (st = 1 → DTHJ = 1)
```

`DTHJ` は `DiffToHaltJump`、`PrevA` は `PreviousA_B_Buttons`、`A_B` は `A_B_Buttons` です。チェック `vertOK` の中身です。

* プレイヤーのルーチンから `PlayerMovementSubs` まで: 1 台の機械、4608 の場合（`Player_State` 3、`AreaType` 3、ボタン 256、前のフレームの A 2）。
* `PlayerMovementSubs`: 本物の機械と `vstep` の機械を並べて、24 の場合（状態 3、A と B の 4 通り、前の A 2）。回り道は 6 つです。しゃがみの判定（`PlayerSize` を読む）、`X_Physics`、ジャンプの音（`PlayerSize`）、地面の処理、空中の左右、縦の移動の最初の判定（`TimerControl`）。
* ルーチンが戻ってからスクロールの処理まで: 1 台の機械。

2 つの条件がある理由です。`DiffToHaltJump` は地上で操作できるときは 0 で、ジャンプのあとは 1 です。レベルの最初の `m0` では 0 です。ルーチンはジャンプ中にこれと比べるので、歩きでは 2 台で同じでないといけません。`vstep` は前のフレームの A を `s.prevA` から書きます。`s.prevA` は `A_B_Buttons` を読みます。本物のルーチンは `PreviousA_B_Buttons` を読みます。ゲームはゲームエンジンの最後で前者を後者に写します（`SaveAB`）。

チェックをまずプログラムとして動かして分かったことです。ボタンの一部のビットだけが分かっていると、1 台の機械の歩きはほかのビットで分かれられません。なのでボタンは 256 通りにしました。`MovePlayerHorizontally` は `JumpspringAnimCtrl` から読んだレジスタで番地を決めるので、2 つの回り道の始まりでそのバイトが 0 と分かっていることにしました。地面の処理と空中の左右は、ルーチン自身のスタックの高さからほかのルーチンを呼ぶので、そのすぐ下の 2 バイトを書きます。

## 押している側がふさがれたフレーム

`ImposeFriction` はまず左右のボタンを当たり判定のビットでふさぎます。`hstep` はそれを `m0` のビットで動かし、そこでは何もふさがれていません。左がふさがれていて（`noLeft`）左を押すと、本物のルーチンは別の道を通ることがあります。

```
move_masked :  modelOK,  maskOK,  AtCtrl0(R),  bits(R) = noLeft,  noLeft & lr ≠ lr,  0 < v(R) < 128
               →  ∃ k ≤ 728,  stepN(k, R).pc = PlayerSubs
                              ∧  ( HS(stepN(k, R)) = hstep(HS(R), In(R))  ∨  v(stepN(k, R)) = 0 )
                              ∧  P(stepN(k, R)) ≡ P(R) + 16·v'  (mod 2²⁴)
```

`lr` は `hstep` が `In(R)` から読む左右です。`AtCtrl0` は `AtCtrl` からふさぎの条件を除いたものです。証明は次のとおりです。

* `N` は、`ImposeFriction` でのモデルの機械に本物のビットを入れたものです。本物の摩擦と `runSub(N)` は同じ道を通ります（`fric_stage`、2 台の機械の歩き。4608 の場合のうち 1920 がふさがれた場合）。
* `runSub(N)` と、モデルの機械 `C` の `runSub(C)` を並べます（`runSub2`、`runSub` の 2 台の機械の歩き）。
  * 左と右: 2 台は同じ道を通ります。
  * 左だけで速さ `v` が 1 から 127: 始まりが 2 つの回り道です。`ImposeFriction` から、それぞれの機械が 1 台で `RghtFrict` に着き、途中で何も書きません。`v` ごとに 1 つの歩きです。
  * 左だけで速さ 0: `runSub(N)` は速さを 0 のままにし、モデルの速さは負になります。これが止まるフレーム（`MaskStop`）です。
* `ImposeFriction` での速さは `v(R)` か 0 です。`X_Physics` は速さを書かず、`GetPlayerAnimSpeed` は 0 だけを書きます（`gpasOK`）。

`maskOK` はこれらのチェックで、ネイティブで約 0.1 秒です。`SurfaceFrames.numbersCheck` の一部です。回り道は、2 台目の機械に別の始まりを持たせられるようになりました（`Detour.c₂`）。`ImposeFriction` では 2 台の当たり判定のビットが違い、ビットが道を決めるからです。

## 分け方

| 区間 | 結果 |
|---|---|
| (1) フレームの最初からプレイヤーのルーチンまで | 地上: 操作中のフレームの始まりから証明（`SurfaceFrames.Moves.toAt`、`CtrlKeep` の歩き）。部屋: 前提（`at_ctrl`、`before`） |
| (2) プレイヤーのルーチンからスクロールの処理まで | 証明。`move_model` |
| (3) スクロールの処理からフレームの最後まで | 前提（`after` または `collide`） |

(2) の中身です。`Player_State` 3 通り、ボタン 256 通り、前のフレームの A 2 通り、`AreaType` 3 通りの 4608 の場合ごとに、次の歩きが通ります。

* プレイヤーのルーチンから `X_Physics` まで: 既知のバイトで 1 台の歩き。ボタンのバイトを既知にします。
* `X_Physics`、`GetPlayerAnimSpeed`、`ImposeFriction`: `hstepN` の `runSub` と 2 台で歩きます。
* それぞれのあいだ: 1 台の歩きで、横のバイトを書かないことを見ます。向きの書き込みもここです。
* `MoveObjectHorizontally`: 速さから 3 桁（256 通り）、端数の足し算（65536 通り）、`x` の足し算と page の足し算（131072 通りずつ）を既知の値で歩き、足すと `P' ≡ P + 16·v` です（`pos_digits`）。page に制限はありません。
* 動く向きの設定: 速さの 256 通り。

`hstep` の入力は機械から読みます。A は押したばかりのときだけ、`st = 0` のときのジャンプです。Select と Start はボタンの 1 つとしてだけ読まれるので、Up と同じに扱います（`joyOf`）。

## 前提（Lean では証明していない）

`Clean(M, i, n₀)` のフィールドです。どれも 1 フレームについてのものです。

* `at_ctrl`（`AtCtrl`）: 命令 `n₀` でプレイヤーのルーチンに来ます。スタックポインタは決まった値、ルーチンの番号はプレイヤーの操作、`AreaType` は水でない、`Player_State` は 0、1、2、ジャンプ台なし、泳ぎなし、大きさの変化なし、NMI なし。覚えている速さは `|v|` です。押した向きはマスクされていません。後の 2 つはぶつかった直後に成り立ちません。
* `before`: そこまで横のバイトと位置のバイトを誰も書きません。
* `longer`: 移動のあいだ（728 命令）にフレームは終わりません。
* `after`: スクロールの処理からフレームの最後まで、横のバイトと位置のバイトを誰も書きません。
* `far`: 位置は範囲の両端から 8 ピクセル以上離れています。

`ReadFrame(M, i, n₀)` のフィールドです。

* `at_frame`（`AtFrame`）: `AtCtrl` から覚えている速さとマスクの条件を除き、マスクは `TopSpeed.collBits` のどれか、`|v| ≤ v_top` を足したものです。
* `before`、`longer`、`far`: `Clean` と同じです。
* `collide`（`Collide`）: スクロールの処理からフレームの最後までに、速さはそのままか 0、subspeed はそのまま、`P` はそのままか −256 か +256 で、+256 は `v ≤ 0` のときだけです。

`modelOK` と `frictionCheck` は ROM のチェックで、`native_decide` で通ります。

## 測ったこと

抽象機械（`TaintRun` のもの）で、各区間を横のバイト 8 個のそれぞれを見張って歩きました（TAS のフレーム 500 の状態、`rkI`）。

| 区間 | 既知のバイト | ステップ | 失敗 |
|---|---|---|---|
| NMI の最初から画面の更新まで | 4 | 5 | 1（NMI の 10 バイト目。PPU の制御レジスタの前の値が分からない） |
| 画面の更新から音まで | 1 | 3 | 1（`UpdateScreen+5`、ポインタ） |
| 音からパッドの読み取りまで | 0 | 1,780,102 | 693（`HandleSquare2Music+9` などポインタ） |
| パッドの読み取りからモードの処理まで | 1 | 2,188 | 0。8 個とも書かない |
| モードの処理からプレイヤーのルーチンまで | 3 | 49 | 0。8 個とも書かない |
| プレイヤーのルーチンからスクロールの処理まで | 8 | 390 | 0（既知が 4 だと `UseAdder+8` で 8） |
| スクロールの処理から当たり判定まで | 5 | 821 | `KeepOnscr` で速さ、`x`、page を書く。画面の端の処理です |
| 当たり判定 | 5 | 547 | 8（`BlockBufferCollision+43`、ポインタ） |
| 当たり判定のあとからゲームエンジンまで | 1 | 99 | 0。8 個とも書かない |
| ゲームエンジンからフレームの最後まで | 3 | 899,031 | 4383（敵、スプライト。添字が分からない） |

2 台の機械の歩きでは、(2) の全部の場合でルーチンのステップは少なく（`X_Physics` 2,896、`GetPlayerAnimSpeed` 14,776、`ImposeFriction` 133）、失敗はありません。

## 本物のフレームで確かめたこと

`frame-model-check` で確かめました。

| 走り | フレーム | `Clean` | `Stop` かつ `ReadFrame` | どちらでもない | `Clean` なのにモデルと違う |
|---|---|---|---|---|---|
| TAS の部屋 | 98 | 98 | 0 | 0 | 0 |
| 部屋、ランダムな入力 300 回 | 56,573 | 48,437 | 8,136 | 0 | 0 |
| 部屋、ほかの 3 種類の入力 700 回ずつ（このリポジトリにないプログラム） | 377,372 | 333,282 | 44,090 | 0 | 0 |

TAS の操作できる 3442 フレームでは、`Clean` は 3404 で、モデルと違うものは 0 です。`Clean` でないのは、マスク 17、当たりのあとの書き込み 25、覚えている速さ 23 です（重なりあり）。`ReadFrame` は 3440 で、残りの 2 つは旗をつかむフレームです。`ReadFrame` のフレームで `|v'| ≤ v_top`、`P' − P ≤ 16·v_top`、`V' ≤ max(V, 0) + a_max` が破れたものは 0 です。移動の一番長いものは 255 命令で、許した 728 より短いです。

`RoomRun` のほかのフィールドも、入力を機械から読んで試し直しました（このリポジトリにないプログラム）。TAS では全部成り立ち `E` = `C` + 111、4 種類の入力 100 回ずつで成り立たないものは 0 でした。

スクロールの処理のあとで横のバイトを書いたのは次の場所です。TAS の 3442 フレームとランダムな入力で見ました。`ImpedePlayerMove`（`NXSpd`、`PlatF`）、旗と `PutPlayerOnVine`、`KillPlayer`。部屋ではランダムな入力でも `ImpedePlayerMove` だけです。スクロールの処理の中の `KeepOnscr` は書きうる場所ですが、これらのフレームでは起きていません。

## まだ証明していないこと

* `before`、部屋で: パッドの読み取りからプレイヤーのルーチンまでは、上の表のとおり歩きが閉じます。そこでは定理にはしていません。地上では定理です: 各命令の条件 `FrameKeep.CleanK`（ポインタや添字での書き込みは守るバイトに触れず、ポインタでの読み込みはレジスタを読まない）のもとで、`CtrlKeep` の歩きはフレームの始まりから、画面の更新と音も含めて、プレイヤーのルーチンまで閉じます（[地上: 操作できてからのフレーム](../1-1/e-2-SurfaceFrames-ja.md)）。
* `vert_model` について: スクロールの処理のあとも縦のバイトが変わらないこと（`SurfaceFrames.OnFrames.vAfter`）。プレイヤーのルーチンまで縦のバイトが前のフレームのものであることと、そこでの 2 つの条件は、地上では定理です（`SurfaceFrames.Moves.vBefore`）。数えないフレーム（`lagPaused` と `spare` のもとで定理 `OnFrames.lagKeep`）と前のフレームの A の 7 ビット目（`CtlState.prevA`）から出ます。
* `after`、`collide`: 当たり判定とゲームエンジンの中は閉じません。`after` は当たりがなかったことを言います。
* `at_ctrl` のうちスタックポインタ、NMI なし、`AreaType` など: 部屋ではフレームが始まる状態から導いていません。地上ではスタックポインタ、NMI なし、ルーチンは歩きから、`AreaType`、泳ぎなし、大きさの変化なしは 1 フレーム全体の歩きから操作のときからの帰納法で（`SurfaceFrames.OnFrames.areaAll`）、`Player_State` とジャンプ台は前のフレームの終わりの値（`SurfaceFrames.CtlState`）から出ます。
* フレームがあふれる走り（1 フレームで処理が終わらない）。`clean` はそのフレームでは成り立ちません。部屋では見ていません。一番短いフレームでも来てから 1469 命令ありました。
* エミュレータが本物の機械と同じこと。

**ファイル.** `Theorems/FrameWalk.lean`、`Theorems/FrameModel.lean`、`Theorems/VertModel.lean`、非公開の `Proof/FrameModel.lean`。

**再現.**
```
.lake/build/bin/smbrta frame-model-check FM2 300
.lake/build/bin/smbrta vert-model-check          # vertOK と各場合、約 0.1 秒
.lake/build/bin/smbrta mask-model-check          # maskOK とその部分、約 0.1 秒
```
