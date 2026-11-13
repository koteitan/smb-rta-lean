[← Back](README-ja.md) | [English](e-2-SurfaceFrames.md) | [Japanese](e-2-SurfaceFrames-ja.md)

# 地上: 操作できてからのフレームを 1 つずつ

**主張.** [操作から城まで](f-5-PoleJoin-ja.md) は走り全体についての文 `model`、`hit`、`stop`、`box`、`off`、`next`、`startP`、`startV` を仮定していました。これらは定理になりました。残る仮定は 1 フレームについての文です。1〜8 フレーム目の縦の一歩（`vstep`）も本物の機械で定理になりました。そこで残るのは、スクロールの処理からあとが縦のバイトを変えないことです。各フレームの始まりからプレイヤーのルーチンまでの部分は定理になりました。その部分の歩き（[`CtrlKeep`](#プレイヤーのルーチンまでのフレーム)）が、25 バイトを保ち、移動の要る状態でルーチンに来ることを示します。なのでフィールド `vBefore`、`Moves.at_ctrl`、`Moves.before`、`Moves.bits` はなくなりました。フレームの両端も、1 つの機械か 1 つのフレームの条件から定理になりました。数えるフレームはポーズでない状態で終わるので、プレイヤーのルーチンに来ます（`Moves.arrive` をなくし、新しく `unpaused`）。数えないフレームはプレイヤーのルーチンに来ないので、25 バイトを保ちます（`Moves.lag` をなくしました）。フレームの残り、プレイヤーのルーチンからフレームの終わりまでの歩き（[下](#フレーム全体-プレイヤーのルーチンから終わりまで)）が、ルーチンに来たフレームはポーズでない状態で終わることと、操作中のどのフレームもエリアの種類、泳ぎのフラグ、大きさの変化を保つことを示すようになりました。なので数えないフレームがルーチンに来ないことは定理です（`OnFrames.lagNo`。新しく `lagPaused`: 数えないフレームはポーズで終わる）。`state` の値のうち 3 つも定理です。各命令の新しい条件は `spare` です: 添字かポインタでの書き込みは、これらの 4 バイトを書きません。フレームは `Run` のフィールド `keep`（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）のものと同じなので、フィールド `ends` もなくなりました。押している側がふさがれたフレームも定理になり、フィールド `masked` はなくなりました。`moves` の条件があと 2 つ定理になりました（[フレームの時間と位置の範囲](#フレームの時間と位置の範囲)）。移動のあいだにフレームが終わらないこと（`Moves.longer` をなくしました。移動の歩きと `CleanK` の条件 `time` から出ます）と、位置が範囲の端から遠いこと（`Moves.far` をなくしました。操作のときの位置と、`hstep` のとおりの前のフレームから出ます）です。`startP`、`startV` は本物の機械で証明しました。[地上への切り替えの最後のフレーム](d-2-3-SideChangeEnd-ja.md) の最後の段から出ます。条件はその切り替えの条件と、`left` が操作の前に 0 にならないことだけです。

単位は 1/256 ピクセルです。`seq j` は数えるフレーム `j` の終わりの機械です。`seq 0` は操作できるときの機械です。`B.m` は非公開の証明が持つ、操作できるときの機械です。

## 1 フレームの形

入力 `i` でのフレーム `a → b` について読みます。`hs(m)` は横方向の状態、`P(m)` は位置、`v(m)` は速さ、`abs(m)` は覚えている速さ、`bits(m)` は当たり判定のビット、`vs(m)` は縦のバイトです。

```
inAt(M, x, n)     : M のフレームをパッド x で動かしたときの n 命令目で、プレイヤーのルーチンが読む入力
                    （FrameModel.readIn）。Select と Start は上ボタンと同じに読む
inAt_mem          : inAt(M, x, n) ∈ inputs                       modelOK から、どの機械でも

t = hstep(hs a, i)     v₂ = v(t)     P₂ = P(a) + 16·v₂

Clean(m)          : inD(hs m) ∧ abs(m) = |v(m)| ∧ (bits(m) = FF ∨ (bits(m) = noLeft ∧ 0 < v(m)))
Pre(i, a, b)      : hs(b) は v を除いて t と同じ ∧ abs(b) = |v₂|
Hit(i, a, b)      : v(b) ≤ 0 ∧ (P(b) ≤ P₂ − 256 ∨ P(b) ≤ P(a) + 256)
Coll(i, a, b)     : (P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = FF)
                  ∨ (0 < v₂ ∧ P(b) = P₂ ∧ v(b) = v₂ ∧ bits(b) = noLeft)
                  ∨ Hit(i, a, b)
MaskStop(a, b)    : bits(a) = noLeft ∧ v(b) ≤ 0 ∧ P(b) ≤ P(a) + 256
OneFrame(i, a, b) : MaskStop(a, b) ∨ (Pre(i, a, b) ∧ Coll(i, a, b))
```

`Follow(i, a, b)` は [地下の部屋](c-5-RoomJoin-ja.md) の `RoomJoin.Follow` と同じ形です。`fr.hs n = hs(seq n)`、`fr.P n = P(seq n)` です。数えるフレーム `j` の入力は `inp(j) = inAt(fm j, pad j, arr j)` です。`arr j` はフレームが初めてプレイヤーのルーチンにいる命令です（次の節）。前はフレームの両端から読む `readIn(a, b)` で、フィールド `input` が 2 つは同じと言っていました。今はルーチンが読む入力そのものなので、そのフィールドはなくなりました。

## 本物の機械の 1 フレーム

[`FrameModel.move_model`](../0-0/0-3-2-FrameModel-ja.md) は本物のフレームの移動を証明しています。プレイヤーのルーチンからスクロールの処理まで、`hs` は `hstep` のとおりで、`P` は `16·v₂` 動きます。なので `OneFrame` は、フレームの移動の外の部分から出る定理です。

`fm j` は数えるフレーム `j` が始まるときの機械です。`seq (j − 1)` か、そのあとの `lag` のフレームのあとです。`pad j` はその入力です。どちらも `Run` のフィールド `keep`（`FrameKeep.Frames`）のものです。`arr j = arrAt(fm j, pad j)` はフレームが初めてプレイヤーのルーチンにいる命令の番号です（`CtrlKeep.arrAt`: `pc(trM(n)) = PlayerCtrlRoutine` となる最初の `n ≤ fuelPerFrame`。前は `OnFrames` のデータでしたが、今は定義です）。`R` はそこでの機械、`Q` はスクロールの処理に来たときの機械です。`b = frame(M, i)` はフレームの終わりの機械です。

```
Masked(i, a)       : bits(a) & lr ≠ lr            lr は hstep が i から読む左右

After(a, Q, b)     : b の f, fd, md は Q のもの ∧ (RunningSpeed(b) = 0 ⟺ RunningSpeed(Q) = 0) ∧ abs(b) = |v(Q)|
                     ∧ ( (P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = FF)
                       ∨ (0 < v(Q) ∧ P(b) = P(Q) ∧ v(b) = v(Q) ∧ bits(b) = noLeft)
                       ∨ (v(b) ≤ 0 ∧ (P(b) ≤ P(Q) − 256 ∨ P(b) ≤ P(a) + 256)) )

MovesAt(a, M, x, n₀) : AtCtrl0(R)                                  プレイヤーのルーチンでの状態。FrameModel が要るもの（ふさぎは除く）
                       ∧ R の横の 8 バイトは a のもの                  a から R まで書かれない
                       ∧ bits(R) = bits(a)                             当たり判定のビットも書かれない
                       ∧ frame(R) = frame(M)                           ルーチンは M のフレームの中で来る（Arrive）
                       ∧ ∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64     CleanK の条件 time
                       ∧ idleAt(idle) ∧ far(a) ∧ after                 アイドルループは自分への JMP。far、after は下

CtlState(a)        : Player_State(a) ∈ {0, 1, 2} ∧ JumpspringAnimCtrl(a) = 0 ∧ PrevA(a) & 80 = A_B(a) & 80
AreaOK(v, a)       : AreaType(a) = v ∧ SwimmingFlag(a) = 0 ∧ PlayerChangeSizeFlag(a) = 0      どのフレームでも定理（OnFrames.areaAll）
AreaRun(v)         : v = AreaType(B.m) ∈ {1, 2, 3} ∧ afterCheck(v) ∧ ∀ n < ix g, AreaOK(v, all n)

Arrive(M, x, n₀)   : pc(trM(n₀)) = PlayerCtrlRoutine で M のフレームの中、n₀ より前の命令はそこにない

Moves(a, M, x, n₀) : state    CtlState(a)
                     after    スクロールの処理に来るどの Q でも After(a, Q, b)
far(a)             : 2048 ≤ P(a) ∧ P(a) + 2048 < 2²⁴

Moves.toAt    : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Clean(a) ∧ Arrive(M, x, n₀) ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ AreaOK(v, a) ∧ v ∈ {1, 2, 3}
                ∧ far(a) ∧ idleAt(idle) ∧ Moves  →  MovesAt
at_subs       : modelOK ∧ MovesAt ∧ ¬Masked  →  スクロールの処理に来る Q があって hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_moves  : modelOK ∧ MovesAt ∧ ¬Masked  →  Pre(inAt(M, x, n₀), a, b) ∧ Coll(inAt(M, x, n₀), a, b)
at_subsM      : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  スクロールの処理に来る Q があって (hs(Q) = hstep(hs a, inAt(M, x, n₀)) ∨ v(Q) = 0)
                                                                  ∧ P(Q) = P(a) + 16·v(Q) ∧ After(a, Q, b)
one_of_movesM : modelOK ∧ maskOK ∧ MovesAt ∧ Clean(a) ∧ Masked  →  OneFrame(inAt(M, x, n₀), a, b)
one_of_frames : OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaRun(v) ∧ Clean(seq (j − 1)) ∧ far(seq (j − 1)) ∧ idleAt(idle)  →  OneFrame(inp j, seq (j − 1), seq j)
```

`keepA` と `StartK`、`CleanK`、`ctrlCheck` は次の節にあります。`all n` は `keep` のフレームで、数えるものも数えないものも入ります。`ix g` は触るフレームです。`StartK(all n)` は操作できるときの機械から出る定理 `FrameKeep.Frames.all_start` です。各命令の `CleanK` はフィールド `keep.clean` です。`Moves.toAt` のほかの 2 つの条件は定理です（`OnFrames.arrive`、`OnFrames.lagKeep`、次の節）。

`idle` はアイドルループ（`EndlessLoop`）で、`idleAt(idle)` はそれが自分への `JMP` だと言います。`numbersCheck` の中の ROM の確認です。`modelOK` は `FrameModel` の ROM の確認です。これは `numbersCheck` の一部になったので、非公開の証明が `native_decide` で計算します（約 3 秒増えます）。`move_model` は押している側がふさがれていないことを要ります。`bits(R) = bits(a)` があれば、これは `¬Masked` です。

**ふさがれたフレーム.** 押している側がふさがれたフレーム（`Masked`）では、摩擦の処理がふさぎを読み、`hstep` は読みません。[`FrameModel.move_masked`](../0-0/0-3-2-FrameModel-ja.md) は、それでもフレームが `hstep` のとおりになるか、速さを 0 にすることを証明します。押している側がふさがれた Clean な状態は、左をふさぐビットを持ち、右へ動いています（`masked_clean`）。スクロールの処理で速さが 0 なら、`After` から `MaskStop` が出ます。`maskOK` は `move_masked` の ROM の確認で（約 0.1 秒）、`numbersCheck` の一部です。

仮定のフィールドです（`OnFrames`）。全部 `Run` の `frames` に入ります。`fm`、`pad` は `keep` のものです。

```
reads    : 1 ≤ j ≤ g   →  fr j の始まりの v, f, P は seq (j − 1) のもの
           1 ≤ j < g   →  fr j の終わりの v', f', P' は seq j のもの
moves    : 1 ≤ j ≤ T, j < g, Clean(seq (j − 1))  →  Moves(seq (j − 1), fm j, pad j, arr j)
vAfter   : 1 ≤ j < J, j < g、Q はスクロールの処理  →  seq j での縦のバイトと A は Q のもの
box      : 1 ≤ j < J, j < g, Q はスクロールの処理  →  Q から seq j まで、当たり判定のルーチンは B.m で
           (pix P(Q), y, w, vy, st) を動かしたときと同じ        (y, vy, st) は vstep の結果、w は速さの符号の代表
```

`pause` はポーズのバイト（`GamePauseStatus`）で、ROM から読みます。NMI がモードのルーチンを呼ぶ直前の読み込みの番地です（`CtrlKeep.pauseA`）。ゲームがポーズしているあいだ、その最下位ビットは 1 です。ポーズの処理がこれを立て、消します。

フィールド `unpaused`、`lagPaused`、`spare` はなくなりました。`keep` のフレームは、`pause & 1 = 0` で終わるとき数えます。これがいまの `ix` の定義です（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）。なので数えるフレームはポーズでない状態で終わり（`Frames.up`、前の `unpaused`）、数えないフレームはポーズで終わります（`Frames.down`、前の `lagPaused`）。前の `spare` は `keep.clean` の一部です。そのガード `FrameKeep.guardF` は `spareI` の 4 バイトも守ります。

フレームの終わりは `Run` のフィールド `keep.ends` です: `1 ≤ j ≤ g → seq j = frame(fm j, pad j)`（`OnFrames.ends`、定理）。縦のバイトは `y, mf, vy, dummy, vf, vfd, origin, st, DTHJ` です。`DTHJ` は `DiffToHaltJump`、`A` は `A_B_Buttons` の 7 ビット目、`PrevA` は `PreviousA_B_Buttons` です。

**縦の一歩は定理.** [`VertModel.vert_model`](../0-0/0-3-2-FrameModel-ja.md) は、プレイヤーのルーチンからスクロールの処理まで、縦のバイトが `vstepV` のとおりになることを証明します。`vstepV` は、スタックポインタをプレイヤーのルーチンのものにし `DTHJ = 1` にした機械の上の `vstep` です。

```
HaltOK(m)  : st(m) = 1 → DTHJ(m) = 1
vNext(a, b) = vstepV(vs(a), A(b), abs(a))
Moves.vBefore : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ Arrive ∧ (∀ y ∈ keepA, y(M) = y(a)) ∧ Moves  →  R での縦のバイトと A は a のもの、
                かつ PrevA(R) & 80 = A_B(R) & 80                       （前のフィールド vBefore）
vert_of    : vertOK ∧ ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ far(seq (j − 1)) ∧ idleAt(idle) ∧ HaltOK(seq (j − 1))
               →  vs(seq j) = vNext(seq (j − 1), seq j) ∧ HaltOK(seq j)
```

操作できるときの状態はジャンプ中ではないので（`numbersCheck` の中）、`HaltOK(seq 0)` が成り立ちます。なので `quiet_upto` は、ほかの事実といっしょに、`j < J` のすべてで `vs(seq j) = vNext(...)` と `HaltOK(seq j)` を帰納法で証明します。`vertOK` は `numbersCheck` の一部です（約 0.1 秒増えます）。

| 前のフィールド | 今 |
|---|---|
| `step`: Clean なフレームは全部 `OneFrame` | `moves`（移動の外の部分）、`ends` |
| `masked`: 押している側がふさがれたフレームは `OneFrame` | 定理 `one_of_movesM`（`moves` と `FrameModel.move_masked` から）。新しく `Moves.bits`。`Moves.at_ctrl` は `AtCtrl0` で、ふさぎの条件はない |
| `reads`: `v₂(fr j) = v₂` | なくなった。`box` が本物の機械 `Q` と `seq j` の文なので、フレームの `v₂` は要らない |
| `fr j` についての `box` | 本物の機械についての `box`、スクロールの処理から |
| `Moves.input`: ルーチンは `readIn(a, b)` を読む | なくなった。モデルの入力はルーチンが読むものそのもの |
| `vert`: 1〜8 フレーム目は `vstep` のとおり | 定理 `vert_of`。新しく `vBefore`、`vAfter`（移動のルーチンの外は縦のバイトを変えない） |
| `vBefore`: プレイヤーのルーチンまで縦のバイトと A は前のフレームのもので、PrevA は A | 定理 `Moves.vBefore`。`CtrlKeep` の歩きから。`OnFrames.lagKeep` と `CtlState.prevA` を使う |
| `Moves.at_ctrl`: プレイヤーのルーチンで `AtCtrl0` | 定理 `Moves.toAt`。歩きから。新しく `Moves.state`（前のフレームの終わりで `CtlState`） |
| `Moves.before`、`Moves.bits`: ルーチンまで横のバイトと当たり判定のビットを書かない | 定理 `Moves.toAt`。歩きから |
| `Moves.arrive`: フレームは終わる前に `arr j` で初めてルーチンに来る | 定理 `OnFrames.arrive`。ポーズのビットを追う歩きと `Frames.up`（数えるフレームはポーズのバイトの最下位ビットが 0 で終わる。数えるフレームの定義から）から |
| `Moves.lag`: `seq (j − 1)` と `fm j` の間の数えないフレームは `keepA` の 25 バイトを保つ | 定理 `OnFrames.lagKeep`。歩きから、1 フレームずつ。新しく `lagNo`（数えないフレームはプレイヤーのルーチンに来ない） |
| `lagNo`: 数えないフレームはプレイヤーのルーチンに来ない | 定理 `OnFrames.lagNo`。フレーム全体の歩き（`area_endF`）と `Frames.down`（数えないフレームはポーズで終わる。定義から）から |
| `state`: 前のフレームの終わりのエリアの種類、泳ぎのフラグ、大きさの変化 | 定理 `OnFrames.areaAll`。フレーム全体の歩きと、操作のときからの `keep` のフレームの帰納法から。`keep.clean` を使う。`Start` はこの 3 バイトを段から持ち、`numbersCheck` が `B.m` での値を確かめる |
| `arr`: データ、ルーチンに来る命令 | 定義 `CtrlKeep.arrAt`: ルーチンにいる最初の命令 |
| `ends` と、データ `fm`、`pad` | `Run` の `keep.ends`、`keep.fm`、`keep.pad`。両方で同じフレームの組を使う |
| `Moves.longer`: プレイヤーのルーチンから 728 命令のうちにフレームが終わらない | 定理 `FrameModel.trace_inFrame`。移動の歩き（`InFrameN`）と `CleanK` の条件 `time`（`keep.clean`）から。新しく `idleAt(idle)`、`numbersCheck` の中の ROM の確認 |
| `Moves.far`: フレームの始まりの位置は範囲の両端から 8 ピクセル以上 | 定理 `far_of_follow`。`Start` と、`hstep` のとおりの前のフレームから。新しく `SurfaceRun.allCheck` の確認 `far`（`B.m` について） |

## フレームの時間と位置の範囲

**時間.** 移動の歩き（[`FrameModel`](../0-0/0-3-2-FrameModel-ja.md#歩いた命令の時間)）は、途中の各ステップが `InFrame` を満たすと言うようになりました。機械は止まっておらず、アイドルループにおらず、フレームに 64 ドット以上残っていればそのステップでフレームは変わりません。`keep` のフレームの各命令は `CleanK` を満たし、その条件 `time` は、アイドルループにいない命令はドット `dotsPerFrame − 64` 以下で動くと言います。なので移動のあいだにフレームは終わらず、プレイヤーのルーチンからの命令は歩きのステップです（`trace_inFrame`）。縦の歩き（`vert_model`）とふさがれたフレーム（`move_masked`）も同じです。

```
trace_inFrame : idleAt(idle) ∧ frame(R) = frame(M) ∧ InFrameN(R, k) ∧ (∀ n, pc(trM(n)) ≠ idle → fdot(trM(n)) ≤ dotsPerFrame − 64)
                →  ∀ j ≤ k,  trM(n₀ + j) = stepN(j, R)
```

**範囲.** `far(a)` が要るのは `one_of_frames` を使うところです。`hstep` のとおりに clean な状態へ進まない最初のフレーム `h` と、`J` より前のフレーム（`quiet_upto`）です。どちらでも前のフレームは `hstep` のとおりなので、`w` をその入力として `P(seq (j − 1)) = P(B.m) + d(w)` です。`hstep` の 1 フレームはどちら向きにも `16·v_top` 以下しか動かず（`hdist_abs`）、`j − 1 ≤ T` です。`SurfaceRun.allCheck` の確認 `far` が `2048 + 16·v_top·T ≤ P(B.m)` と `P(B.m) + 16·v_top·T + 2048 < 2²⁴` を与えます。

```
hdist_abs      : inD(s), w ∈ I*  →  −16·v_top·|w| ≤ d(s, w) ≤ 16·v_top·|w|
far_of_follow  : numbersCheck ∧ Start(B, seq 0) ∧ SurfaceRun.far ∧ d ≤ T ∧ 1..d のフレームは hstep のとおり  →  far(seq d)
```

非公開の証明が `T = 233` で `B.m` の `far` を確かめます（`surface_checks`）。

## プレイヤーのルーチンまでのフレーム

操作中のフレームは、画面の更新、音、パッド、ポーズ、タイマーを動かし、それからモードのルーチンを呼び、それがプレイヤーのルーチンを呼びます。`CtrlKeep` はこの部分を `TaintRun` の抽象機械で追います。[数えないフレーム](a-5-5-3-LagFrames-ja.md) がモードのルーチンの呼び出しまでフレームを追うのと同じです。1 つのバイトを `TaintRun` のカウンタ（`Env.rkI`）として追います。歩きはそのバイトへのどの書き込みでも失敗します。歩きはフレームが初めてプレイヤーのルーチンに来たところ（切れ目）で止まり、そこでバイトがまだ追えていることを確かめます。`keepA` の 25 バイトのそれぞれに 1 つの歩きがあります。

```
keepA      = 横の 8 バイト（FrameModel.hBytes）、Player_CollisionBits、Player_XSpeedAbsolute、AreaType、JumpspringAnimCtrl、
             SwimmingFlag、PlayerChangeSizeFlag、縦の 9 バイト（vKeep）、A_B_Buttons、PreviousA_B_Buttons
StartK(m)  : m は操作中のフレームの始まりのアイドルループにいる（FrameKeep: スタック、ドット、PPU、ルーチン、モード、タスク）
CleanK(m)  : FrameKeep の 1 命令についての条件
trM(n)     : M のフレームの n 命令目の機械

ctrl_keep  : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pc(trM(k)) = PlayerCtrlRoutine ∧ trM(k) は M のフレームの中 ∧ (∀ j < k, pc(trM(j)) ≠ PlayerCtrlRoutine)
             →  ∀ y ∈ keepA, y(trM(k)) = y(M)
                ∧ S(trM(k)) はプレイヤーのルーチンのスタック ∧ NMI が来ていない ∧ NMI が切ってある ∧ GameEngineSubroutine(trM(k)) は操作
```

切れ目では、スタックポインタ、NMI が来ていないこと、PPU の制御の 7 ビット目が 0 であること、ルーチンのバイトも確かめます。これらで `ctrl_keep` は `R` での `AtCtrl0` を出します。ただし `AreaType`、`Player_State`、ジャンプ台、泳ぎ、大きさの変化の値と、覚えている速さは別です。これらは `OnFrames.lagKeep` と `Moves.state` から、覚えている速さは `Clean(a)` から出ます（`Moves.toAt`）。

**ルーチンに来ないときのフレームの終わり.** 切れ目に来ない道では、歩きはフレームの終わりまで進みます。これはポーズのフレームです（NMI がモードのルーチンを飛ばします）。そこでも、追っているバイトがまだ追えていることを確かめます。もう 1 つの歩きはポーズのバイトの最下位ビットを追います。そのビットを知った状態から始め（両方の値から歩きます）、切れ目に来なかったフレームの終わりで、そのビットが 1 と分かっていることを確かめます。ポーズの処理はそのビットを `EOR` で反転するか保ち、NMI はそのビットで分岐するので、どの道でもビットは分かっています。その歩きの探索は、ポーズのバイトの値が違う状態をまとめません。

```
cut_or_end    : ctrlCheck1 ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)))
                →  (∃ k ≤ fuelPerFrame, pc(trM(k)) = PlayerCtrlRoutine で M のフレームの中、初めて)
                   ∨ フレームの終わりは、バイトを追えている（ポーズのビットが 1 の）状態で覆われる
arrive_at     : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ pause(frame(M, x)) & 1 = 0  →  Arrive(M, x, arrAt(M, x))
keep_of_noCut : ctrlCheck ∧ StartK(M) ∧ (∀ n, CleanK(trM(n))) ∧ （M のフレームのどの命令も PlayerCtrlRoutine にいない）
                →  ∀ y ∈ keepA, y(frame(M, x)) = y(M)
OnFrames.arrive  : ctrlCheck ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)), 1 ≤ j ≤ T, j < g  →  Arrive(fm j, pad j, arr j)        Frames.up と keep.ends から
OnFrames.lagKeep : 同じ  →  ∀ y ∈ keepA, y(fm j) = y(seq (j − 1))                                                          OnFrames.lagNo（定理）から、フレーム ix (j − 1) … ix j − 2 の帰納法
```

* **各命令の条件.** `CleanK` で、フィールド `keep.clean` です。移動のルーチンの書き込みは切れ目の前にありません（歩きが `pc` を確かめます）。行き先の分からない書き込みがあると、歩きは追っているバイトを忘れ、切れ目で失敗します。なので歩きは、切れ目の前のすべての書き込みが行き先を知っていることも示します。
* **探索.** 証明の一部ではありません。確認は表の全部の状態から歩きます。`LagFrames` の探索は `prot` の外のバイトを忘れ、ループの周回をまとめます。するとタイマーのループ（`DEC abs,X`）、乱数のビット（`ROR abs,X`）、トップスコア（`STA abs,Y`）が分からない添字で書き込み、追っているバイトを失います。`CtrlKeep` の探索は RAM のバイトを忘れず、2 つの添字レジスタをキーに入れます。1 つの表が全部のバイトに使えます。
* **数.** 25 バイトの探索: 108,736 歩、7,157 分岐、失敗 0、表は 7,852 状態、切れ目に来るのは 2、フレームの終わりは 6（ポーズのフレーム）、0.2 秒。ポーズのビットの探索: 221,415 歩、14,528 分岐、失敗 0、表は 16,729 状態、切れ目に来るのは 6、フレームの終わりは 12、0.5 秒。25 バイトとポーズのビットの確認（`ctrlCheck`）: ネイティブで 2.8 秒（ポーズのビットの前は 2.3 秒）。`numbersCheck` の一部です（`Numbers.ctrl`）。

`surface_of_frames` とその前の定理は、触るフレームより前の `keep` の各フレーム（数えるものも数えないものも）の `StartK(all n)` を受け取ります。`PoleJoin` では、操作できるときの機械（`FrameKeep.AtCtl`）、歩きの確認 `keepCheckOf`、`fracCheck` から出る `FrameKeep.Frames.all_start` です。

## フレーム全体: プレイヤーのルーチンから終わりまで

ポーズのビットの歩きは、プレイヤーのルーチン（切れ目）で止まります。いまは切れ目で `FrameKeep` の歩き（`FrameKeep.walkK`）に引き継ぎ、そこからフレームの終わりまで追います。この歩きは、[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md) の歩きと同じく、守るバイトの外を忘れます。その守り（`guardP`）は 4 バイト多く守ります（`spareI`）: ポーズのバイト、`AreaType`、`SwimmingFlag`、`PlayerChangeSizeFlag` です。切れ目では、ポーズのバイトのうち最下位ビットだけを残します。そこでは 0 と分かっています（NMI がちょうどそのビットを調べたからです）。ほかの 3 つはフレームの始まりの値（`v`、0、0）にします。切れ目でもまだその値です（`ctrl_keep`）。フレームの終わりで 4 つの値をまた確かめます（`afterCheck`）。

```
Spare(m)        : m の添字かポインタでの書き込みは、行き先 t < 2000h なら spareI のバイトを書かない
AreaOK(v, m)    : AreaType(m) = v ∧ SwimmingFlag(m) = 0 ∧ PlayerChangeSizeFlag(m) = 0

area_end        : ctrlCheck ∧ afterCheck(v) ∧ StartK(M) ∧ (∀ n, CleanK(trM(n)) ∧ Spare(trM(n))) ∧ AreaOK(v, M)
                  →  AreaOK(v, frame(M, x)) ∧ ((∃ k, M のフレームの中で pc(trM(k)) = PlayerCtrlRoutine) → pause(frame(M, x)) & 1 = 0)
noCut_of_paused : 同じ ∧ pause(frame(M, x)) & 1 = 1  →  M のフレームのどの命令も PlayerCtrlRoutine にいない
area_endF, noCut_of_pausedF : 同じもので、CleanK(trM(n)) ∧ Spare(trM(n)) の代わりに ∀ n, CleanK_F(trM(n))       CleanK_F: FrameKeep.guardF の CleanK
OnFrames.areaAll : ctrlCheck ∧ afterCheck(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n)) ∧ AreaOK(v, seq 0)  →  ∀ n < ix g, AreaOK(v, all n)
OnFrames.lagNo   : ctrlCheck ∧ AreaRun(v) ∧ OnFrames ∧ (∀ n < ix g, StartK(all n))  →  前のフィールド lagNo
```

ルーチンに来ないフレームは、前からの歩きのとおりです: ポーズで終わり、`keepA` を保ちます。`keepA` には 3 バイトが入っています。なので操作中のどのフレームも 3 バイトを保ち、フレームがポーズでない状態で終わるのは、ちょうどプレイヤーのルーチンに来たときです。

* **バイトを守る理由.** プレイヤーのルーチンのあと、ゲームエンジンは歩きの知らない添字で書き込みます（物の処理）。そういう書き込みのあと、歩きは守るバイトの外をすべて忘れます。`CleanK` が守るのは `FrameKeep.guardK` のバイトだけです。なので `keep.clean` は `FrameKeep.guardF` の `CleanK` を聞きます。これは 4 バイトも守ります。`area_endF` はこれを使う `area_end` です。切れ目のあとの歩きはプレイヤー自身の端数の書き込みで `Spare` を聞かないので、その書き込みでの前の `Spare` は要りません。本物のフレームでは、添字かポインタでの書き込みがこれらのバイトを書くことはありません（下の「測ったもの」）。
* **帰納法.** `seq 0` は `B.m` の 3 バイトを持ちます（`Start`、切り替えの段から）。`numbersCheck` は `AreaType(B.m) ∈ {1, 2, 3}`、`SwimmingFlag(B.m) = 0`、`PlayerChangeSizeFlag(B.m) = 0` を確かめます。触るフレームより前の `keep` の各フレームはそれらを保つので（`area_endF`）、どの `all n` もそれらを持ち、`seq (j − 1)` も持ちます。
* **大きさの変化.** `PlayerChangeSizeFlag` を立てるのは大きさを変えるルーチンだけで、それは操作のルーチンではありません。パワーアップはルーチンのバイトを変えます。フラグが立つのはあとのフレームで、それは操作中ではありません。
* **数.** ポーズのビットの歩きは 3 つの状態で切れ目に来ます。切れ目からの探索: 1,633,803 歩、154,366 分岐、失敗 0、表は 75,196 状態。`afterCheck`（切れ目までのポーズのビットの歩きをもう一度と、切れ目からの歩き）: プログラムで 5.9 秒。`numbersCheck` の一部です（`Numbers.after`）。ポーズのビットだけを見ると表は 46,644 状態、ポーズのビット、エリアの種類、泳ぎのフラグでは 44,924 状態です。切れ目でポーズのバイト全体を残すと、切れ目の 3 つの状態が 3 つのキーになり、表は 139,987 状態です。
* **ジャンプ台.** `JumpspringAnimCtrl` も守って見ると、探索は終わりませんでした: 9 分、6.8 GB で止めました。ジャンプ台の物の処理は、乗ったときにこれを書くので、どのみち歩きでは保てません。
* **`unpaused` と `lagPaused` はなくなった.** どのフレームを数えるかは `keep` の `ix` です。歩きから、フレームがポーズでない状態で終わるのは、ちょうどプレイヤーのルーチンに来たときです。なので `ix` を、ポーズでない状態で終わるフレームとして定義しました。2 つのフィールドは定義から成り立ちます。

## 走り全体の文は定理

```
step_of_one       : Clean(a) ∧ OneFrame(a, b)  →  (Follow(a, b) ∧ Clean(b)) ∨ Hit(a, b)
next_of_reads     : reads  →  ∀ j ∈ [1, g), Next(fr j, fr (j + 1))
quiet_upto        : 1 ≤ j < J, j < g  →  フレーム 1..j は Follow ∧ seq 0..j は Clean ∧ bits(seq j) = FF
                                         ∧ フレーム 1..j は vNext ∧ seq 0..j は HaltOK
surface_of_frames : OnFrames ∧ Start(B, seq 0) ∧ (∀ n < ix g, StartK(all n)) ∧ noHitCheck ∧ numbersCheck ∧ J ≤ T
                    →  ∃ w h, Surface(w, h)
Run.next, Run.startP, Run.startV                                 PoleJoin
```

| 前の仮定 | 今 | どこから |
|---|---|---|
| `model`: `j < h` で `P'(j) ≤ P_A + d(w)` | 定理 | `one_of_frames`。`w` は `inp j` の列、`h` は `Follow ∧ Clean` でない最初のフレーム |
| `hit`、`stop` | 定理 | `OneFrame` の `Hit` |
| `box`、`off`: `J` の前にぶつからない | 定理（`Surface.first : J ≤ h`） | `box`、`vert_of`、`moves`、距離の上限（`dist_abs`）、高さの探索（`vCheck`） |
| `next` | 定理 | `reads`。両方の端を同じ機械から読む |
| `startP`、`startV` | 定理 | `Start`。下の節 |
| `mem`、`long` | 定理 | `inAt_mem`、`w` の作り方 |

**箱の中.** 1〜8 フレーム目の `x` は仮定ではありません。`|d(w)|` の上限から 4 ピクセル以内です（`dl`、左へは速さのバイトが 1 大きくなるので `dbound` より少し大きい）。高さも仮定ではありません。`vCheck` は `vs(B.m)` から A の有無と 0 から最高速までの覚えている速さの全部で 8 フレーム `vstepV` を動かし、全部が箱の中であることを確かめます。

## 操作できるときの状態

`Start(B, m)` は 1 つの機械についての文です。

```
Start(B, m) : hs(m) = hs(B.m) ∧ P(m) = P(B.m) ∧ abs(m) = abs(B.m) ∧ bits(m) = bits(B.m) ∧ vs(m) = vs(B.m)
              ∧ AreaType(m) = AreaType(B.m) ∧ SwimmingFlag(m) = SwimmingFlag(B.m) ∧ PlayerChangeSizeFlag(m) = PlayerChangeSizeFlag(B.m)
```

切り替えの最後の段の操作できる状態は、2,048 バイトのうち 1,763 か 1,776 を知っています。`startCheck` は、全部の段の全部の状態について、操作できるかどうかが読めて、操作できるなら `Start` のバイトを知っていて `B.m` と同じであることを確かめます。

```
start_of_rows : startCheck ∧ InRows(m) ∧ ctl(m)  →  Start(B, m)
EndRun.start  : Statement ∧ EndStatement ∧ startCheck ∧ EndRun ∧ (∀ n ∈ [a, b), left(seq n) ≠ 0)  →  Start(B, seq b)
Run.start     : 同じ条件で、Route の走りについて  Start(B, pole.seq 0)
```

段の中で `left` が 0 なのは最後の段だけです。最後の段には 6 つの状態があり、操作できるのは 2 つです。ほかの 4 つは時間切れです。段は `left` が 0 のところで終わるので、`left` が操作の前に 0 にならないことが要ります（`EndRun.first`。`chg.time₂` と `chg.ctlFirst₂` から証明）。`Route.Run.atCtl : pole.seq 0 = base.seq b₂` は定理です。`keep` のフレームは `base` のフレーム `b₂` からのものです。`chg` の条件 `entry₂`、`noStart₂`、`quiet₂` は `Run.change₂` と同じものを使います。

最後の段からは縦のバイトと、A のボタン、当たり判定のビットも出ます。知らない主なものは `PlayerSize` と `EventMusicQueue` です。

## 画面の左端

マリオが画面の左端のピクセルにいるとき、右ボタンだけを押していなければ、スクロールの処理が速さを 0 にします。左端より左に出ると、位置をそのピクセルに戻します。順番は、移動、スクロールの処理、当たり判定です。

* 前の `Frame.impedeP` は本物のフレームで成り立ちません。左へ走って左端を越えるフレームは `v₂ = −v_top`、`P' − P₂ = 512` です。左端へ走る 53,398 フレームのうち 13 フレームがこれです。
* なので `impedeP` の 3 番目を `P' = P₂ + 256 ∧ v₂ ≤ 0` から `P' ≤ P + 256 ∧ v₂ ≤ 0` にしました。`Frame.bound`、`Frame.adv_le`、`chain_reach` はそのままです。
* 1 フレームの文では、これは `Hit` の 2 番目です。`v₂ > 0` でも止まることがあります（測った最大は 4）。そのとき `P(b) = P₂ ≤ P(a) + 256` です。左端のピクセルを速く離れることはないので、これで足ります。この「速くない」は証明していません。`After` の中（`moves` の中）の仮定です。

## 測ったもの

プログラム `surface-frames-check FM2 N`、`N = 200`、終了コード 0、CPU で約 9 分です。全部の行で、`OneFrame`、`Moves`、`ends`、`reads` の `v₂`、`Frame` の `move`、`gain`、`impedeV`、`impedeF`、`impedeP` が成り立たないフレームは 0 です。

| 走り | フレーム | Clean でない | `lag` | 何もしない | 左をふさぐ | `Hit` | 左端で戻す | 1〜8 フレーム目 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| TAS の 852 から | 240 | 5 | 0 | 233 | 0 | 1 | 0 | 8 |
| 1089 のあとの遅い触り、A を長く押す | 34 | 3 | 0 | 30 | 0 | 0 | 0 | 0 |
| 操作からランダム | 36,308 | 4,048 | 0 | 30,705 | 2 | 1,463 | 1 | 1,600 |
| TAS のフレームからランダム | 15,019 | 571 | 0 | 14,087 | 0 | 327 | 0 | 0 |
| Select あり | 10,520 | 571 | 0 | 9,724 | 0 | 180 | 1 | 800 |
| Start あり | 20,311 | 761 | 8,070 | 11,161 | 0 | 284 | 2 | 786 |
| 左端へ走る | 53,398 | 3,804 | 0 | 47,629 | 0 | 1,835 | 13 | 0 |
| 階段のまわりを書き換えた状態 | 103,680 | 5,908 | 0 | 88,917 | 2,653 | 6,202 | 0 | 0 |

* 1〜8 フレーム目（3,194 フレーム）では `vs(seq j) = vNext(seq (j − 1), seq j)`、前の `vBefore`、`vAfter`、両端の `HaltOK`、`box`、当たり判定に入るときの `(y, vy, st)` が `vstepV` の結果であることも確かめました。違いは 0 です。
* `Moves` を確かめる全部のフレームで、`state`（前のフレームの終わりで `PrevA & 80 = A_B & 80` を含む）、`OnFrames.lagKeep` が証明すること（`fm j` の 25 バイトは `seq (j − 1)` のもの）、ルーチンに来ること、`ctrl_keep` が証明すること（ルーチンでの `keepA` の 25 バイトは `fm j` のもの）も確かめました。Start ありの `lag` のフレーム 8,070 も含めて、違いは 0 です。
* 前のフィールド `unpaused`、`lagPaused`、`spare`: ポーズで終わる操作中の数えるフレーム、ポーズでなく終わる `lag` のフレーム、`spareI` の 4 バイトへの添字かポインタでの書き込みのあるフレームは、どれもありません。プレイヤーのルーチンに来る `lag` のフレーム（`OnFrames.lagNo` が証明すること）と、エリアの種類、泳ぎのフラグ、大きさの変化を変える操作中のフレーム（`OnFrames.areaAll` が証明すること）もありません。Start ありの `lag` のフレーム 8,070 も含めて、どの走りでもすべて 0 です。証明の機械はエリアの種類 1、泳ぎのフラグ 0、大きさの変化 0 です。
* 全部のフレームで、プレイヤーのルーチンが読む入力は両端から読む `readIn(a, b)` と同じです（前のフィールド `input`）。違いは 0 です。
* 1〜8 フレーム目の 3,194 フレームのうち 2,375 で、スクロールの処理からフレームの終わりまでのあいだに縦のバイトが別の値になり、終わりには戻っています。地面の上では当たり判定のルーチンが `Player_State` を 2 にして、また着地させます。なので `vAfter` は、これらのバイトへの書き込みを許さない歩きからは出ません。
* 押している側がふさがれたフレームは 329 です（操作から 3、階段のまわり 326）。全部 `OneFrame` で、全部 `Moves` を満たします。移動の処理に来たとき、182 はモデルの速さで、147 はモデルの速さが 0 でないのに速さ 0 です（`move_masked` の 2 番目の場合。種類の列では `Hit` に数えます）。この 147 は `Pre ∧ Coll` でなく、`MaskStop` が要ります。前にこのページは要るものは 0 と書いていましたが、それは誤りでした。`bits(R) = bits(a)` が成り立たないフレームはありません。
* `lag` のフレーム 8,070 では、ここで読むバイトは変わりません。なので `seq j` のあとに `lag` のフレームがあっても読む値は同じです。はみ出すフレームはこれらの走りにありません。
* 切り替え: TAS の入る状態と `E` から、Start なしのランダムな入力で 201 回。全部 282 フレーム以上で操作でき、操作の前に `left` が 0 になることはなく、操作のときの状態は全部 `Start` を満たします。
* 測り方: 操作できない機械で終わるフレーム（死ぬ、旗に触る）はフィールドの外なので数えません。そこで `Follow` と `Hit` は成り立ちません。そういう走りは `Run` ではありません。

## 最初のフレームを抽象機械で

最後の段の操作できる状態から 1 フレームを歩いてみました（Lean には入れていません）。

| 知っていること | 歩数 | 失敗 |
|---|---:|---:|
| パッドが不明 | 27,292 | 5（`FindEventMusicHeader+2`） |
| `EventMusicQueue = 0`、パッドが不明 | 2,288 | 4（`JumpEngine+18`） |
| `EventMusicQueue = 0`、パッドは Start なしの 128 通りのそれぞれ | 739,183 | A なしの 64 通りで 1 回（`BlockBufferCollision+43`） |
| さらに `PlayerSize` を場合分け | 1 つの場合に約 840,000 | 0、4 つの場合で約 3 秒 |

なのでフレーム 1 だけなら閉じます。これは 233 フレームのうちの 1 つで、次のフレームの状態の数は増えるので、入れていません。

## 前提（Lean では証明していない）

* `moves`: 移動の外の部分。プレイヤーのルーチンまでは、操作中のフレームの始まりと `CleanK` から証明です（`ctrl_keep`）。ルーチンに来ることと、数えないフレームが 25 バイトを保つことも証明です。移動のあいだにフレームが終わらないこと（`CleanK` から）と、位置が端から遠いこと（前のフレームから）も証明です。残るのは、前のフレームの終わりの値（`state`）と `After` です。移動そのものは、押している側がふさがれていても証明です（[`FrameModel`](../0-0/0-3-2-FrameModel-ja.md)）。
* `unpaused`、`lagPaused`、`spare` はここではもう仮定しません。数えるフレームはポーズでない状態で終わるフレームで、4 バイトは `keep.clean` のガードに入っています（[操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md)）。
* `state`: 残るのは `Player_State` ∈ {0, 1, 2}、ジャンプ台なし、`PrevA & 80 = A_B & 80` です。これらは地図と物のコードが書きます（ジャンプ台に乗ったときのジャンプ台、当たり判定のルーチンの `Player_State`、ゲームエンジンの終わりの `PreviousA_B_Buttons`）。操作中のフレームの歩きは地図も物も知らないので、これらを保つことは示せません。`AreaType`、`SwimmingFlag`、`PlayerChangeSizeFlag` は証明です（`OnFrames.areaAll`）。
  `PrevA` については、この回に切れ目からの歩きを試しました（プログラム `ctrl-prev-check`）。プレイヤーのルーチンは `A_B_Buttons` を `SavedJoypadBits` からしか書かず、`SaveAB` がそれを写します。歩きは切れ目で `SavedJoypadBits` の 7 ビット目を決め（両方の値）、`SavedJoypadBits`、`A_B_Buttons`、`PreviousA_B_Buttons` を `spareI` のバイトと同じように守り、フレームの終わりで今のフレームと前のフレームの A の 7 ビット目がそのビットであることを確かめます。探索は終わります（74,910 状態、約 5 秒）が、26 のフレームの終わりで失敗します。そこでは `PreviousA_B_Buttons` が分からないので、探索には `SaveAB` を通らない道があります。どの道かはまだ見つけていません。歩きが閉じても、この 3 バイトには、プレイヤーのルーチンからあとの各命令に `spare` のような条件が要ります（パッドの処理はその前に添字で `SavedJoypadBits` に書きます）。
* `vAfter`: 1〜8 フレーム目で、スクロールの処理からあとが縦のバイトを変えないこと。ルーチンが `vstep` のとおりなのは証明（`vert_of`）、その前の部分も証明（`Moves.vBefore`）です。`vAfter` は前の部分と同じ歩きでは出ません。測った 1〜8 フレーム目の 3,194 のうち 2,375 で、縦のバイトがスクロールの処理のあとで別の値になり、フレームの終わりに戻ります（当たり判定のルーチンが `Player_State` を 2 にして、また着地させます）。当たり判定のあとは敵の処理が縦の速さを書くことがあり（踏みつけ）、歩きは敵を知りません。
* [操作中の 1 フレーム全体](f-6-19-FrameKeep-ja.md) の `keep.ends`、`keep.clean` と定理 `keep.start`: フレームは同じなので、`ends` はここのフィールドではなくなりました。
* `box`: 1〜8 フレーム目で、当たり判定が操作のときの機械と同じ結果になること。
* `reads`: `fr` を機械から読むこと。`Frame` であること自体は [最高速の上限](../0-0/0-1-TopSpeed-ja.md) の前提のままです。
* `chg.time₂`、`chg.ctlFirst₂`、定理 `Run.atCtl`。

**ファイル.** `Theorems/SurfaceFrames.lean`、`Theorems/CtrlKeep.lean`、`Theorems/VertModel.lean`、`Theorems/FrameModel.lean`（`move_masked`、`trace_inFrame`）、`Theorems/FrameWalk.lean`（`InFrame`）、`Theorems/SurfaceRun.lean`（`far`）、非公開の `Proof/SurfaceFrames.lean`（`side_start`）、`Proof/PoleJoin.lean`（`pole_numbers`。`ctrlCheck` と `afterCheck` を含む）。

**再現.**
```
.lake/build/bin/smbrta surface-frames-check FM2 200    # 上の表、CPU で約 9 分
.lake/build/bin/smbrta vert-model-check                # vertOK とその各場合、約 0.1 秒
.lake/build/bin/smbrta mask-model-check                # maskOK とその部分、約 0.1 秒
.lake/build/bin/smbrta ctrl-keep-check                 # プレイヤーのルーチンまでの歩き: 25 バイトのそれぞれとポーズのビット、約 4 秒
.lake/build/bin/smbrta ctrl-after-check size           # 切れ目からの歩き（afterCheck）、約 20 秒。`pause` と `area` は見るバイトが少ない
.lake/build/bin/smbrta ctrl-prev-check                 # PrevA の切れ目からの探索（証明には入らない）、約 10 秒。exit 1（26 のフレームの終わりで失敗）
```
